//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.25;

import { IExecutionEnvironment } from "../interfaces/IExecutionEnvironment.sol";

// import "openzeppelin-contracts/contracts/utils/cryptography/ECDSA.sol";

import { IAtlasVerification } from "../interfaces/IAtlasVerification.sol";
import { AtlETH } from "./AtlETH.sol";

import "../types/SolverCallTypes.sol";
import "../types/UserCallTypes.sol";
import { DAppConfig } from "../types/DAppApprovalTypes.sol";
import "../types/EscrowTypes.sol";
import "../types/LockTypes.sol";

import { EscrowBits } from "../libraries/EscrowBits.sol";
import { CallBits } from "../libraries/CallBits.sol";
import { SafetyBits } from "../libraries/SafetyBits.sol";

// import "forge-std/Test.sol";

abstract contract Escrow is AtlETH {
    using EscrowBits for uint256;
    using CallBits for uint32;
    using SafetyBits for EscrowKey;

    uint256 private constant _SOLVER_GAS_LIMIT = 1_000_000;
    uint256 private constant _VALIDATION_GAS_LIMIT = 500_000;
    uint256 private constant _SOLVER_GAS_BUFFER = 5; // out of 100
    uint256 private constant _FASTLANE_GAS_BUFFER = 125_000; // integer amount

    constructor(
        uint256 _escrowDuration,
        address _verification,
        address _simulator,
        address _surchargeRecipient
    )
        AtlETH(_escrowDuration, _verification, _simulator, _surchargeRecipient)
    { }

    function _executePreOpsCall(
        UserOperation calldata userOp,
        address environment,
        bytes32 lockBytes
    )
        internal
        returns (bool success, bytes memory preOpsData)
    {
        preOpsData = abi.encodeWithSelector(IExecutionEnvironment.preOpsWrapper.selector, userOp);
        preOpsData = abi.encodePacked(preOpsData, lockBytes);
        (success, preOpsData) = environment.call(preOpsData);
        if (success) {
            preOpsData = abi.decode(preOpsData, (bytes));
        }
        emit PreOpsCall(environment, success, preOpsData);
    }

    function _executeUserOperation(
        UserOperation calldata userOp,
        address environment,
        bytes32 lockBytes
    )
        internal
        returns (bool success, bytes memory userData)
    {
        userData = abi.encodeWithSelector(IExecutionEnvironment.userWrapper.selector, userOp);
        userData = abi.encodePacked(userData, lockBytes);

        (success, userData) = environment.call{ value: userOp.value }(userData);

        // require(success, "ERR-E002 UserFail");
        if (success) {
            userData = abi.decode(userData, (bytes));
        }

        emit UserCall(environment, success, userData);
    }

    // Returns (bool auctionWon, EscrowKey key)
    function _executeSolverOperation(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation calldata solverOp,
        bytes memory dAppReturnData,
        uint256 bidAmount,
        bool prevalidated,
        EscrowKey memory key
    )
        internal
        returns (bool, EscrowKey memory)
    {
        // Set the gas baseline
        uint256 gasWaterMark = gasleft();
        uint256 result;
        if (!prevalidated) {
            result = IAtlasVerification(VERIFICATION).verifySolverOp(
                solverOp, key.userOpHash, userOp.maxFeePerGas, key.bundler
            );
        }

        // Verify the transaction.
        if (result.canExecute()) {
            uint256 gasLimit;
            // Verify gasLimit again
            (result, gasLimit) = _validateSolverOperation(dConfig, solverOp, gasWaterMark, result);

            if (dConfig.callConfig.allowsTrustedOpHash()) {
                if (!prevalidated && !_handleAltOpHash(userOp, solverOp)) {
                    key.solverOutcome = uint24(result);
                    return (false, key);
                }
            }

            // If there are no errors, attempt to execute
            if (result.canExecute() && _trySolverLock(solverOp)) {
                // Open the solver lock
                key = key.holdSolverLock(solverOp.solver);

                // Execute the solver call
                // _solverOpsWrapper returns a SolverOutcome enum value
                result |= _solverOpWrapper(
                    bidAmount, gasLimit, key.executionEnvironment, solverOp, dAppReturnData, key.pack()
                );

                key.solverOutcome = uint24(result);

                if (result.executionSuccessful()) {
                    // first successful solver call that paid what it bid

                    emit SolverTxResult(solverOp.solver, solverOp.from, true, true, result);

                    key.solverSuccessful = true;
                    // auctionWon = true
                    return (true, key);
                }
            }
        }

        key.solverOutcome = uint24(result);

        _releaseSolverLock(solverOp, gasWaterMark, result, false, !prevalidated);

        unchecked {
            ++key.callIndex;
        }
        // emit event
        emit SolverTxResult(solverOp.solver, solverOp.from, result.executedWithError(), false, result);

        // auctionWon = false
        return (false, key);
    }

    // (Note that balances are held in the execution environment, meaning
    // that payment failure is typically a result of a flaw in the
    // DAppControl contract)
    function _allocateValue(
        DAppConfig calldata dConfig,
        SolverOperation calldata solverOp,
        uint256 winningBidAmount,
        bytes memory returnData,
        EscrowKey memory key
    )
        internal
        returns (EscrowKey memory)
    {
        // process dApp payments
        key = key.holdAllocateValueLock(solverOp.from);

        bytes memory data = abi.encodeWithSelector(
            IExecutionEnvironment.allocateValue.selector, dConfig.bidToken, winningBidAmount, returnData
        );
        data = abi.encodePacked(data, key.pack());
        (bool success,) = key.executionEnvironment.call(data);
        if (!success) {
            emit MEVPaymentFailure(dConfig.to, dConfig.callConfig, dConfig.bidToken, winningBidAmount);
        } else {
            key.paymentsSuccessful = true;
        }

        return key;
    }

    function _executePostOpsCall(
        bool solved,
        bytes memory returnData,
        EscrowKey memory key
    )
        internal
        returns (bool success)
    {
        bytes memory postOpsData =
            abi.encodeWithSelector(IExecutionEnvironment.postOpsWrapper.selector, solved, returnData);
        postOpsData = abi.encodePacked(postOpsData, key.pack());
        (success,) = key.executionEnvironment.call(postOpsData);
        emit PostOpsCall(key.executionEnvironment, success);
    }

    // TODO Revisit the EscrowAccountBalance memory solverEscrow arg. Needs to be passed through from Atlas, through
    // callstack
    function _validateSolverOperation(
        DAppConfig calldata dConfig,
        SolverOperation calldata solverOp,
        uint256 gasWaterMark,
        uint256 result
    )
        internal
        view
        returns (uint256, uint256 gasLimit)
    {
        if (gasWaterMark < _VALIDATION_GAS_LIMIT + _SOLVER_GAS_LIMIT) {
            // Make sure to leave enough gas for dApp validation calls
            return (result | 1 << uint256(SolverOutcome.UserOutOfGas), gasLimit);
        }

        if (block.number > solverOp.deadline) {
            return (
                result
                    | 1
                        << uint256(
                            dConfig.callConfig.allowsTrustedOpHash()
                                ? uint256(SolverOutcome.DeadlinePassedAlt)
                                : uint256(SolverOutcome.DeadlinePassed)
                        ),
                0
            );
        }

        gasLimit = (100) * (solverOp.gas < _SOLVER_GAS_LIMIT ? solverOp.gas : _SOLVER_GAS_LIMIT)
            / (100 + _SOLVER_GAS_BUFFER) + _FASTLANE_GAS_BUFFER;

        uint256 gasCost = (tx.gasprice * gasLimit) + _getCalldataCost(solverOp.data.length);

        // Verify that we can lend the solver their tx value
        if (
            solverOp.value
                > address(this).balance - (gasLimit * tx.gasprice > address(this).balance ? 0 : gasLimit * tx.gasprice)
        ) {
            return (result |= 1 << uint256(SolverOutcome.CallValueTooHigh), gasLimit);
        }

        // subtract out the gas buffer since the solver's metaTx won't use it
        gasLimit -= _FASTLANE_GAS_BUFFER;

        EscrowAccountAccessData memory aData = accessData[solverOp.from];

        uint256 solverBalance = aData.bonded;
        uint256 lastAccessedBlock = aData.lastAccessedBlock;

        // NOTE: Turn this into time stamp check for FCFS L2s?
        if (lastAccessedBlock == block.number) {
            result |= 1 << uint256(SolverOutcome.PerBlockLimit);
        }

        // see if solver's escrow can afford tx gascost
        if (gasCost > solverBalance) {
            // charge solver for calldata so that we can avoid vampire attacks from solver onto user
            result |= 1 << uint256(SolverOutcome.InsufficientEscrow);
        }

        return (result, gasLimit);
    }

    function _getBidAmount(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation calldata solverOp,
        bytes memory data,
        EscrowKey memory key
    )
        internal
        returns (uint256 bidAmount)
    {
        // NOTE: To prevent a malicious bundler from aggressively collecting storage refunds,
        // solvers should not be on the hook for any 'on chain bid finding' gas usage.

        bool success;
        uint256 gasWaterMark = gasleft();
        uint256 result =
            IAtlasVerification(VERIFICATION).verifySolverOp(solverOp, key.userOpHash, userOp.maxFeePerGas, key.bundler);

        // Verify the transaction.
        if (!result.canExecute()) return 0;

        uint256 gasLimit;
        (result, gasLimit) = _validateSolverOperation(dConfig, solverOp, gasWaterMark, result);

        if (dConfig.callConfig.allowsTrustedOpHash()) {
            if (!_handleAltOpHash(userOp, solverOp)) {
                return (0);
            }
        }

        // If there are no errors, attempt to execute
        if (!result.canExecute() || !_trySolverLock(solverOp)) return 0;

        data = abi.encodeWithSelector(
            IExecutionEnvironment(key.executionEnvironment).solverMetaTryCatch.selector,
            solverOp.bidAmount,
            gasLimit,
            solverOp,
            data
        );

        data = abi.encodePacked(data, key.holdSolverLock(solverOp.solver).pack());

        (success, data) = key.executionEnvironment.call{ value: solverOp.value }(data);

        _releaseSolverLock(solverOp, gasWaterMark, result, true, true);

        if (success) {
            revert();
        }

        if (bytes4(data) == BidFindSuccessful.selector) {
            // Get the uint256 from the memory array
            assembly {
                let dataLocation := add(data, 0x20)
                bidAmount :=
                    mload(
                        add(
                            dataLocation,
                            sub(mload(data), 32) // TODO: make sure a full uint256 is safe from overflow
                        )
                    )
            }
            return bidAmount;
        } else {
            return 0;
        }
    }

    function _handleAltOpHash(
        UserOperation calldata userOp,
        SolverOperation calldata solverOp
    )
        internal
        returns (bool)
    {
        // These failures should be attributed to bundler maliciousness
        if (solverOp.deadline != userOp.deadline || solverOp.control != userOp.control) {
            return false;
        }
        bytes32 hashId = keccak256(abi.encodePacked(solverOp.userOpHash, solverOp.from, solverOp.deadline));
        if (_solverOpHashes[hashId]) {
            return false;
        }
        _solverOpHashes[hashId] = true;
        return true;
    }

    // Returns a SolverOutcome enum value
    function _solverOpWrapper(
        uint256 bidAmount,
        uint256 gasLimit,
        address environment,
        SolverOperation calldata solverOp,
        bytes memory dAppReturnData,
        bytes32 lockBytes
    )
        internal
        returns (uint256)
    {
        // address(this) = Atlas/Escrow
        // msg.sender = tx.origin

        bool success;

        bytes memory data = abi.encodeWithSelector(
            IExecutionEnvironment(environment).solverMetaTryCatch.selector,
            bidAmount,
            gasLimit,
            solverOp,
            dAppReturnData
        );

        data = abi.encodePacked(data, lockBytes);

        (success, data) = environment.call{ value: solverOp.value }(data);

        if (success) {
            return uint256(0);
        }
        bytes4 errorSwitch = bytes4(data);

        if (errorSwitch == AlteredControl.selector) {
            return 1 << uint256(SolverOutcome.AlteredControl);
        } else if (errorSwitch == PreSolverFailed.selector) {
            return 1 << uint256(SolverOutcome.PreSolverFailed);
        } else if (errorSwitch == SolverOperationReverted.selector) {
            return 1 << uint256(SolverOutcome.SolverOpReverted);
        } else if (errorSwitch == PostSolverFailed.selector) {
            return 1 << uint256(SolverOutcome.PostSolverFailed);
        } else if (errorSwitch == IntentUnfulfilled.selector) {
            return 1 << uint256(SolverOutcome.IntentUnfulfilled);
        } else if (errorSwitch == SolverBidUnpaid.selector) {
            return 1 << uint256(SolverOutcome.BidNotPaid);
        } else if (errorSwitch == BalanceNotReconciled.selector) {
            return 1 << uint256(SolverOutcome.BalanceNotReconciled);
        } else {
            return 1 << uint256(SolverOutcome.EVMError);
        }
    }

    receive() external payable { }

    fallback() external payable {
        revert(); // no untracked balance transfers plz. (not that this fully stops it)
    }
}
