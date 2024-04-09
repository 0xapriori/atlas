//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

import { SafeTransferLib, ERC20 } from "solmate/utils/SafeTransferLib.sol";

import { IAtlasVerification } from "src/contracts/interfaces/IAtlasVerification.sol";

import { Escrow } from "./Escrow.sol";
import { Factory } from "./Factory.sol";

import "src/contracts/types/SolverCallTypes.sol";
import "src/contracts/types/UserCallTypes.sol";
import "src/contracts/types/LockTypes.sol";
import "src/contracts/types/DAppApprovalTypes.sol";
import "src/contracts/types/ValidCallsTypes.sol";

import { CallBits } from "src/contracts/libraries/CallBits.sol";
import { SafetyBits } from "src/contracts/libraries/SafetyBits.sol";

/// @title Atlas V1
/// @author FastLane Labs
/// @notice The Execution Abstraction protocol.
contract Atlas is Escrow, Factory {
    using CallBits for uint32;
    using SafetyBits for EscrowKey;

    constructor(
        uint256 _escrowDuration,
        address _verification,
        address _simulator,
        address _surchargeRecipient,
        address _executionTemplate
    )
        Escrow(_escrowDuration, _verification, _simulator, _surchargeRecipient)
        Factory(_executionTemplate)
    { }

    /// @notice metacall is the entrypoint function for the Atlas transactions.
    /// @param userOp The UserOperation struct containing the user's transaction data.
    /// @param solverOps The SolverOperation array containing the solvers' transaction data.
    /// @param dAppOp The DAppOperation struct containing the DApp's transaction data.
    function metacall(
        UserOperation calldata userOp, // set by user
        SolverOperation[] calldata solverOps, // supplied by ops relay
        DAppOperation calldata dAppOp // supplied by front end via atlas SDK
    )
        external
        payable
        returns (bool auctionWon)
    {
        uint256 gasMarker = gasleft(); // + 21_000 + (msg.data.length * _CALLDATA_LENGTH_PREMIUM);
        bool isSimulation = msg.sender == SIMULATOR;

        (address executionEnvironment, DAppConfig memory dConfig) = _getOrCreateExecutionEnvironment(userOp);

        // Gracefully return if not valid. This allows signature data to be stored, which helps prevent
        // replay attacks.
        // NOTE: Currently reverting instead of graceful return to help w/ testing. TODO - still reverting?
        (bytes32 userOpHash, ValidCallsResult validCallsResult) = IAtlasVerification(VERIFICATION).validateCalls(
            dConfig, userOp, solverOps, dAppOp, msg.value, msg.sender, isSimulation
        );
        if (validCallsResult != ValidCallsResult.Valid) {
            if (isSimulation) revert VerificationSimFail(uint256(validCallsResult));
            else revert ValidCalls(validCallsResult);
        }

        // Initialize the lock
        _setAtlasLock(executionEnvironment, gasMarker, userOp.value);

        try this.execute{ value: msg.value }(dConfig, userOp, solverOps, executionEnvironment, msg.sender, userOpHash)
        returns (bool _auctionWon, uint256 winningSolverIndex) {
            auctionWon = _auctionWon;
            // Gas Refund to sender only if execution is successful
            (uint256 ethPaidToBundler, uint256 netGasSurcharge) = _settle({
                winningSolver: auctionWon ? solverOps[winningSolverIndex].from : msg.sender,
                bundler: msg.sender
            });

            emit MetacallResult(
                msg.sender,
                userOp.from,
                auctionWon ? solverOps[winningSolverIndex].from : address(0),
                ethPaidToBundler,
                netGasSurcharge
            );
        } catch (bytes memory revertData) {
            // Bubble up some specific errors
            _handleErrors(revertData, dConfig.callConfig);

            // Refund the msg.value to sender if it errored
            if (msg.value != 0) SafeTransferLib.safeTransferETH(msg.sender, msg.value);
        }

        // Release the lock
        _releaseAtlasLock();
    }

    /// @notice execute is called above, in a try-catch block in metacall.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp UserOperation struct of the current metacall tx.
    /// @param solverOps SolverOperation array of the current metacall tx.
    /// @param executionEnvironment Address of the execution environment contract of the current metacall tx.
    /// @param bundler Address of the bundler of the current metacall tx.
    /// @param userOpHash Hash of the userOp struct of the current metacall tx.
    /// @return auctionWon Boolean indicating whether the auction was won
    /// @return uint256 The solver outcome bitmap
    function execute(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        address executionEnvironment,
        address bundler,
        bytes32 userOpHash
    )
        external
        payable
        returns (bool auctionWon, uint256)
    {
        // This is a self.call made externally so that it can be used with try/catch
        if (msg.sender != address(this)) revert InvalidAccess();

        (bytes memory returnData, EscrowKey memory key) =
            _preOpsUserExecutionIteration(dConfig, userOp, solverOps, executionEnvironment, bundler, userOpHash);

        if (dConfig.callConfig.exPostBids()) {
            (auctionWon, key) = _bidFindingIteration(dConfig, userOp, solverOps, returnData, key);
        } else {
            (auctionWon, key) = _bidKnownIteration(dConfig, userOp, solverOps, returnData, key);
        }

        // If no solver was successful, handle revert decision
        if (!auctionWon) {
            if (key.isSimulation) revert SolverSimFail(uint256(key.solverOutcome));
            if (dConfig.callConfig.needsFulfillment()) {
                revert UserNotFulfilled();
            }
        }

        if (dConfig.callConfig.needsPostOpsCall()) {
            // NOTE: key.addressPointer currently points at address(0) if all solvers fail.
            // TODO: point key.addressPointer at bundler if all fail.
            key = key.holdPostOpsLock(); // preserves addressPointer of winning solver

            bool callSuccessful = _executePostOpsCall(auctionWon, returnData, key);
            if (!callSuccessful) {
                if (key.isSimulation) revert PostOpsSimFail();
                else revert PostOpsFail();
            }
        }
        return (auctionWon, uint256(key.solverOutcome));
    }

    /// @notice Called above in `execute`, this function executes the preOps and userOp calls.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp UserOperation struct of the current metacall tx.
    /// @param solverOps SolverOperation array of the current metacall tx.
    /// @param executionEnvironment Address of the execution environment contract of the current metacall tx.
    /// @param bundler Address of the bundler of the current metacall tx.
    /// @param userOpHash Hash of the userOp struct of the current metacall tx.
    /// @return bytes returnData returned from the preOps and/or userOp calls.
    /// @return EscrowKey struct containing the current state of the escrow lock.
    function _preOpsUserExecutionIteration(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        address executionEnvironment,
        address bundler,
        bytes32 userOpHash
    )
        internal
        returns (bytes memory, EscrowKey memory)
    {
        bool callSuccessful;
        bool usePreOpsReturnData;
        bytes memory returnData;

        // Build the memory lock
        EscrowKey memory key = _buildEscrowLock(
            dConfig, executionEnvironment, userOpHash, bundler, uint8(solverOps.length), bundler == SIMULATOR
        );

        if (dConfig.callConfig.needsPreOpsCall()) {
            // CASE: Need PreOps Call
            key = key.holdPreOpsLock(dConfig.to);

            if (dConfig.callConfig.needsPreOpsReturnData()) {
                // CASE: Need PreOps return data
                usePreOpsReturnData = true;
                (callSuccessful, returnData) = _executePreOpsCall(userOp, executionEnvironment, key.pack());
            } else {
                // CASE: Ignore PreOps return data
                (callSuccessful,) = _executePreOpsCall(userOp, executionEnvironment, key.pack());
            }

            if (!callSuccessful) {
                if (key.isSimulation) revert PreOpsSimFail();
                else revert PreOpsFail();
            }
        }

        key = key.holdUserLock(userOp.dapp);

        if (dConfig.callConfig.needsUserReturnData()) {
            // CASE: Need User return data

            if (usePreOpsReturnData) {
                // CASE: Need PreOps return Data, Need User return data
                bytes memory userReturnData;
                (callSuccessful, userReturnData) = _executeUserOperation(userOp, executionEnvironment, key.pack());
                returnData = bytes.concat(returnData, userReturnData);
            } else {
                // CASE: Ignore PreOps return data, Need User return data
                (callSuccessful, returnData) = _executeUserOperation(userOp, executionEnvironment, key.pack());
            }
        } else {
            // CASE: Ignore User return data
            (callSuccessful,) = _executeUserOperation(userOp, executionEnvironment, key.pack());
        }

        if (!callSuccessful) {
            if (key.isSimulation) revert UserOpSimFail();
            else revert UserOpFail();
        }

        return (returnData, key);
    }

    /// @notice Called above in `execute` if the DAppConfig requires ex post bids. Sorts solverOps by bid amount and
    /// executes them in descending order until a successful winner is found.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp UserOperation struct of the current metacall tx.
    /// @param solverOps SolverOperation array of the current metacall tx.
    /// @param returnData Return data from the preOps and userOp calls.
    /// @param key EscrowKey struct containing the current state of the escrow lock.
    /// @return auctionWon bool indicating whether a winning solver was found or not.
    /// @return EscrowKey struct containing the current state of the escrow lock.
    function _bidFindingIteration(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        bytes memory returnData,
        EscrowKey memory key
    )
        internal
        returns (bool auctionWon, EscrowKey memory)
    {
        key.bidFind = true;

        uint256[] memory sortedOps = new uint256[](solverOps.length);
        uint256[] memory bidAmounts = new uint256[](solverOps.length);
        uint256 j;
        uint256 bidPlaceholder;

        for (uint256 i; i < solverOps.length; i++) {
            bidPlaceholder = _getBidAmount(dConfig, userOp, solverOps[i], returnData, key);

            if (bidPlaceholder == 0) {
                unchecked {
                    ++j;
                }
                continue;
            } else {
                bidAmounts[i] = bidPlaceholder;

                for (uint256 k = i - j + 1; k > 0; k--) {
                    if (bidPlaceholder > bidAmounts[sortedOps[k - 1]]) {
                        sortedOps[k] = sortedOps[k - 1];
                        sortedOps[k - 1] = i;
                    } else {
                        sortedOps[k] = i;
                        break;
                    }
                }
            }
        }

        key.bidFind = false;
        j = solverOps.length - j;

        for (uint256 i; i < j; i++) {
            bidPlaceholder = sortedOps[i];

            (auctionWon, key) = _executeSolverOperation(
                dConfig, userOp, solverOps[bidPlaceholder], returnData, bidAmounts[bidPlaceholder], true, key
            );

            if (auctionWon) {
                key = _allocateValue(dConfig, solverOps[bidPlaceholder], bidAmounts[bidPlaceholder], returnData, key);
                key.solverOutcome = uint24(bidPlaceholder);
                return (auctionWon, key);
            }
        }

        return (auctionWon, key);
    }

    /// @notice Called above in `execute` as an alternative to `_bidFindingIteration`, if solverOps have already been
    /// reliably sorted. Executes solverOps in order until a successful winner is found.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp UserOperation struct of the current metacall tx.
    /// @param solverOps SolverOperation array of the current metacall tx.
    /// @param returnData Return data from the preOps and userOp calls.
    /// @param key EscrowKey struct containing the current state of the escrow lock.
    /// @return auctionWon bool indicating whether a winning solver was found or not.
    /// @return EscrowKey struct containing the current state of the escrow lock.
    function _bidKnownIteration(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        bytes memory returnData,
        EscrowKey memory key
    )
        internal
        returns (bool auctionWon, EscrowKey memory)
    {
        uint256 k = solverOps.length;
        uint256 i;

        for (; i < k;) {
            // valid solverOps are packed from left of array - break at first invalid solverOp

            SolverOperation calldata solverOp = solverOps[i];

            (auctionWon, key) =
                _executeSolverOperation(dConfig, userOp, solverOp, returnData, solverOp.bidAmount, false, key);

            if (auctionWon) {
                key = _allocateValue(dConfig, solverOp, solverOp.bidAmount, returnData, key);

                key.solverOutcome = uint24(i);

                return (auctionWon, key);
            }

            unchecked {
                ++i;
            }
        }

        return (auctionWon, key);
    }

    /// @notice Called at the end of `metacall` to bubble up specific error info in a revert.
    /// @param revertData Revert data from a failure during the execution of the metacall.
    /// @param callConfig The CallConfig of the current metacall tx.
    function _handleErrors(bytes memory revertData, uint32 callConfig) internal view {
        bytes4 errorSwitch = bytes4(revertData);
        if (msg.sender == SIMULATOR) {
            // Simulation
            if (errorSwitch == PreOpsSimFail.selector) {
                revert PreOpsSimFail();
            } else if (errorSwitch == UserOpSimFail.selector) {
                revert UserOpSimFail();
            } else if (errorSwitch == SolverSimFail.selector) {
                // Expects revertData in form [bytes4, uint256]
                uint256 solverOutcomeResult;
                assembly {
                    let dataLocation := add(revertData, 0x20)
                    solverOutcomeResult := mload(add(dataLocation, sub(mload(revertData), 32)))
                }
                revert SolverSimFail(solverOutcomeResult);
            } else if (errorSwitch == PostOpsSimFail.selector) {
                revert PostOpsSimFail();
            }
        }
        if (errorSwitch == UserNotFulfilled.selector) {
            revert UserNotFulfilled();
        }
        if (callConfig.allowsReuseUserOps()) {
            assembly {
                mstore(0, errorSwitch)
                revert(0, 4)
            }
        }
    }

    /// @notice Reverts if the caller is not the execution environment address expected from the set of inputs.
    /// @param user User address
    /// @param controller DAppControl contract address
    /// @param callConfig CallConfig of the current metacall tx.
    function _verifyCallerIsExecutionEnv(address user, address controller, uint32 callConfig) internal view override {
        if (msg.sender != _getExecutionEnvironmentCustom(user, controller.codehash, controller, callConfig)) {
            revert EnvironmentMismatch();
        }
    }
}
