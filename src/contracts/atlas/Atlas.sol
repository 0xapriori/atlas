//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

import { IExecutionEnvironment } from "../interfaces/IExecutionEnvironment.sol";
import { IDAppControl } from "../interfaces/IDAppControl.sol";
import { IAtlasVerification } from "../interfaces/IAtlasVerification.sol";

import { SafeTransferLib, ERC20 } from "solmate/utils/SafeTransferLib.sol";

import { Escrow } from "./Escrow.sol";
import { Factory } from "./Factory.sol";

import { AtlasEvents } from "src/contracts/types/AtlasEvents.sol";
import { AtlasErrors } from "src/contracts/types/AtlasErrors.sol";

import "../types/SolverCallTypes.sol";
import "../types/UserCallTypes.sol";
import "../types/LockTypes.sol";
import "../types/DAppApprovalTypes.sol";
import "../types/ValidCallsTypes.sol";

import { CALLDATA_LENGTH_PREMIUM } from "../types/EscrowTypes.sol";

import { CallBits } from "../libraries/CallBits.sol";
import { SafetyBits } from "../libraries/SafetyBits.sol";

import "forge-std/Test.sol";

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

    function metacall( // <- Entrypoint Function
        UserOperation calldata userOp, // set by user
        SolverOperation[] calldata solverOps, // supplied by ops relay
        DAppOperation calldata dAppOp // supplied by front end via atlas SDK
    )
        external
        payable
        returns (bool auctionWon)
    {
        uint256 gasMarker = gasleft(); // + 21_000 + (msg.data.length * CALLDATA_LENGTH_PREMIUM);

        // Get or create the execution environment
        (address executionEnvironment, DAppConfig memory dConfig) = _getOrCreateExecutionEnvironment(userOp);

        // Initialize the lock
        _initializeEscrowLock(executionEnvironment, gasMarker, userOp.value);

        try this.execute{ value: msg.value }(dConfig, userOp, solverOps, dAppOp, executionEnvironment, msg.sender)
        returns (bool _auctionWon, uint256 winningSolverIndex) {
            auctionWon = _auctionWon;
            // Gas Refund to sender only if execution is successful
            _settle({ winningSolver: auctionWon ? solverOps[winningSolverIndex].from : msg.sender, bundler: msg.sender });

            emit MetacallResult(msg.sender, userOp.from, auctionWon ? solverOps[winningSolverIndex].from : address(0));
        } catch (bytes memory revertData) {
            // Bubble up some specific errors
            _handleErrors(dConfig, userOp, solverOps, dAppOp, bytes4(revertData), dConfig.callConfig);

            // Refund the msg.value to sender if it errored
            if (msg.value != 0) SafeTransferLib.safeTransferETH(msg.sender, msg.value);
        }

        // Release the lock
        _releaseEscrowLock();

        console.log("total gas used", gasMarker - gasleft());
    }

    function execute(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        DAppOperation calldata dAppOp,
        address executionEnvironment,
        address bundler
    )
        external
        payable
        returns (bool auctionWon, uint256 winningSearcherIndex)
    {
        // This is a self.call made externally so that it can be used with try/catch
        if (msg.sender != address(this)) revert InvalidAccess();

        // Gracefully return if not valid. This allows signature data to be stored, which helps prevent
        // replay attacks. Revert occurs in a try / catch. 
        (bytes32 userOpHash, ValidCallsResult validCallsResult) = IAtlasVerification(VERIFICATION).validateCalls(
            dConfig, userOp, solverOps, dAppOp, msg.value, bundler, bundler == SIMULATOR
        );

        if (validCallsResult != ValidCallsResult.Valid) revert ValidCalls(validCallsResult);

        (bytes memory returnData, EscrowKey memory key) =
            _preOpsUserExecutionIteration(dConfig, userOp, solverOps, executionEnvironment, bundler);


        bool isUserReplay = _checkIfUserOpReplay(dConfig, userOpHash);

        for (; winningSearcherIndex < solverOps.length;) {
            // valid solverOps are packed from left of array - break at first invalid solverOp

            SolverOperation calldata solverOp = solverOps[winningSearcherIndex];
            // if (solverOp.from == address(0)) break;

            (auctionWon, key) = _solverExecutionIteration(
                dConfig, userOp, solverOp, returnData, executionEnvironment, bundler, userOpHash, isUserReplay, key
            );
            emit SolverExecution(solverOp.from, winningSearcherIndex, auctionWon);
            if (auctionWon) break;

            unchecked {
                ++winningSearcherIndex;
            }
        }

        // If no solver was successful, handle revert decision
        if (!auctionWon) {
            if (key.isSimulation) revert SolverSimFail();
            if (dConfig.callConfig.needsFulfillment()) {
                revert UserNotFulfilled(); // revert("ERR-E003 SolverFulfillmentFailure");
            }
        }

        if (dConfig.callConfig.needsPostOpsCall()) {
            // NOTE: key.addressPointer currently points at address(0) if all solvers fail.
            // TODO: point key.addressPointer at bundler if all fail.
            key = key.holdPostOpsLock(); // preserves addressPointer of winning solver

            bool callSuccessful = _executePostOpsCall(auctionWon, returnData, executionEnvironment, key.pack());
            if (!callSuccessful) {
                if (key.isSimulation) revert PostOpsSimFail();
                else revert PostOpsFail();
            }
        }
        return (auctionWon, winningSearcherIndex);
    }

    function _preOpsUserExecutionIteration(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        address executionEnvironment,
        address bundler
    )
        internal
        returns (bytes memory, EscrowKey memory)
    {
        bool callSuccessful;
        bool usePreOpsReturnData;
        bytes memory returnData;

        // Build the memory lock
        EscrowKey memory key =
            _buildEscrowLock(dConfig, executionEnvironment, uint8(solverOps.length), bundler == SIMULATOR);

        if (dConfig.callConfig.needsPreOpsCall()) {
            // CASE: Need PreOps Call
            key = key.holdPreOpsLock(dConfig.to);

            if (CallBits.needsPreOpsReturnData(dConfig.callConfig)) {
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

        if (CallBits.needsUserReturnData(dConfig.callConfig)) {
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

    function _solverExecutionIteration(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation calldata solverOp,
        bytes memory dAppReturnData,
        address executionEnvironment,
        address bundler,
        bytes32 userOpHash,
        bool isUserReplay,
        EscrowKey memory key
    )
        internal
        returns (bool auctionWon, EscrowKey memory)
    {
        (auctionWon, key) = _executeSolverOperation(
            dConfig, userOp, solverOp, dAppReturnData, executionEnvironment, bundler, userOpHash, isUserReplay, key
        );

        if (auctionWon) {
            key = key.holdAllocateValueLock(solverOp.from);

            key.paymentsSuccessful =
                _allocateValue(dConfig, solverOp.bidAmount, dAppReturnData, executionEnvironment, key.pack());
        }
        return (auctionWon, key);
    }

    function _handleErrors(
        DAppConfig memory dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        DAppOperation calldata dAppOp,
        bytes4 errorSwitch, 
        uint32 callConfig
    ) 
        internal 
    {
        if (msg.sender == SIMULATOR) {
            // Simulation
            if (errorSwitch == ValidCalls.selector) {
                revert VerificationSimFail();
            } else if (errorSwitch == PreOpsSimFail.selector) {
                revert PreOpsSimFail();
            } else if (errorSwitch == UserOpSimFail.selector) {
                revert UserOpSimFail();
            } else if (errorSwitch == SolverSimFail.selector) {
                revert SolverSimFail();
            } else if (errorSwitch == PostOpsSimFail.selector) {
                revert PostOpsSimFail();
            }
        }

        // No replay protection needed on invalid userop / dappOp / auctioneer
        // NOTE: These won't be executed. Replay protection on unauthorized txs
        // would lead to censorship.
        if (errorSwitch == ValidCalls.selector) {
            revert ValidCalls(ValidCallsResult.Invalid);
        }

        bytes32 userOpHash = IAtlasVerification(VERIFICATION).replayProtectionOnRevert(
            dConfig, userOp, dAppOp, msg.sender
        );
       
        // If UserOps are allowed to be reused, block solverOp replay
        // NOTE: The UserOp hash is effectively the SolverOp nonce. 
        if (callConfig.allowsReuseUserOps()) {

            _usedOpHashes[userOpHash] = true;

            for (uint256 i; i < solverOps.length; i++) {
                if (IAtlasVerification(VERIFICATION).verifySolverOp(solverOps[i], userOpHash, msg.sender) == 0) {
                    _preventOpHashReplay(userOp, solverOps[i]);
                }
            }
        }
    }

    function _verifyCallerIsExecutionEnv(address user, address controller, uint32 callConfig) internal view override {
        if (msg.sender != _getExecutionEnvironmentCustom(user, controller.codehash, controller, callConfig)) {
            revert EnvironmentMismatch();
        }
    }
}
