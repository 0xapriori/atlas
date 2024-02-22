//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

import { IDAppControl } from "../interfaces/IDAppControl.sol";

import "../types/SolverCallTypes.sol";
import "../types/UserCallTypes.sol";
import "../types/DAppApprovalTypes.sol";

library CallVerification {
    function getUserOperationHash(UserOperation memory userOp) internal pure returns (bytes32 userOpHash) {
        userOpHash = keccak256(abi.encode(userOp));
    }

    function getAltOperationHash(UserOperation memory userOp) internal pure returns (bytes32 altOpHash) {
        altOpHash = keccak256(abi.encodePacked(userOp.from, userOp.to, userOp.dapp, userOp.control, userOp.sessionKey));
    }

    function getSolverHash(SolverOperation calldata solverOp) internal pure returns (bytes32 solverHash) {
        return keccak256(
            abi.encode(
                SOLVER_TYPE_HASH,
                solverOp.from,
                solverOp.to,
                solverOp.value,
                solverOp.gas,
                solverOp.maxFeePerGas,
                solverOp.deadline,
                solverOp.solver,
                solverOp.control,
                solverOp.userOpHash,
                solverOp.bidToken,
                solverOp.bidAmount,
                keccak256(solverOp.data)
            )
        );
    }

    function getCallChainHash(
        DAppConfig memory dConfig,
        UserOperation memory userOp,
        SolverOperation[] memory solverOps
    )
        internal
        pure
        returns (bytes32 callSequenceHash)
    {
        uint256 i;
        if (dConfig.callConfig & 1 << uint32(CallConfigIndex.RequirePreOps) != 0) {
            // Start with preOps call if preOps is needed
            callSequenceHash = keccak256(
                abi.encodePacked(
                    callSequenceHash, // initial hash = null
                    dConfig.to,
                    abi.encodeWithSelector(IDAppControl.preOpsCall.selector, userOp),
                    i++
                )
            );
        }

        // then user call
        callSequenceHash = keccak256(
            abi.encodePacked(
                callSequenceHash, // always reference previous hash
                abi.encode(userOp),
                i++
            )
        );

        // then solver calls
        uint256 count = solverOps.length;
        uint256 n;
        for (; n < count;) {
            callSequenceHash = keccak256(
                abi.encodePacked(
                    callSequenceHash, // reference previous hash
                    abi.encode(solverOps[n]), // solver op
                    i++
                )
            );
            unchecked {
                ++n;
            }
        }
    }
}
