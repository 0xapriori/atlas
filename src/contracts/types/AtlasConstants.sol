//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

// NOTE: Internal constants that are defined but not used in the logic of a smart contract, will NOT be included in the
// bytecode of the smart contract when compiled. However, public constants will be included in every inheriting contract
// as they are part of the ABI. As such, only internal constants are defined in this shared contract.

contract AtlasConstants {
    // ------------------------------------------------------- //
    //                      ATLAS CONSTANTS                    //
    // ------------------------------------------------------- //

    // Atlas constants
    uint256 internal constant _GAS_USED_DECIMALS_TO_DROP = 1000;
    address internal constant _UNLOCKED = address(1);
    uint256 internal constant _UNLOCKED_UINT = 1;

    // Atlas constants used in `_bidFindingIteration()`
    uint256 internal constant _BITS_FOR_INDEX = 16;

    // Escrow constants
    uint256 internal constant _VALIDATION_GAS_LIMIT = 500_000;
    uint256 internal constant _SOLVER_GAS_LIMIT_BUFFER_PERCENTAGE = 5; // out of 100 = 5%
    uint256 internal constant _SOLVER_GAS_LIMIT_SCALE = 100; // out of 100 = 100%
    uint256 internal constant _FASTLANE_GAS_BUFFER = 125_000; // integer amount

    // Gas Accounting constants
    uint256 internal constant _CALLDATA_LENGTH_PREMIUM = 32; // 16 (default) * 2
    uint256 internal constant _SOLVER_OP_BASE_CALLDATA = 608; // SolverOperation calldata length excluding solverOp.data
    uint256 internal constant _SOLVER_LOCK_GAS_BUFFER = 5000; // Base gas charged to solver in `_releaseSolverLock()`

    // First 160 bits of _solverLock are the address of the current solver.
    // The 161st bit represents whether the solver has called back via `reconcile`.
    // The 162nd bit represents whether the solver's outstanding debt has been repaid via `reconcile`.
    uint256 internal constant _SOLVER_CALLED_BACK_MASK = 1 << 161;
    uint256 internal constant _SOLVER_FULFILLED_MASK = 1 << 162;

    // ------------------------------------------------------- //
    //               ATLAS VERIFICATION CONSTANTS              //
    // ------------------------------------------------------- //

    uint256 internal constant _FULL_BITMAP = _FIRST_240_BITS_TRUE_MASK;
    uint256 internal constant _NONCES_PER_BITMAP = 240;
    uint8 internal constant _MAX_SOLVERS = type(uint8).max - _CALL_COUNT_EXCL_SOLVER_CALLS;

    // ------------------------------------------------------- //
    //                     SHARED CONSTANTS                    //
    // ------------------------------------------------------- //

    uint256 internal constant _FIRST_240_BITS_TRUE_MASK =
        uint256(0x0000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
    uint256 internal constant _FIRST_16_BITS_TRUE_MASK = uint256(0xFFFF);
    uint256 internal constant _FIRST_4_BITS_TRUE_MASK = uint256(0xF);
    uint8 internal constant _CALL_COUNT_EXCL_SOLVER_CALLS = 4;
}
