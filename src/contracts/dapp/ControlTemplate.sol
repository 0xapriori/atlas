//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

import "../types/SolverCallTypes.sol";
import "../types/UserCallTypes.sol";
import "../types/DAppApprovalTypes.sol";
import { AtlasErrors } from "src/contracts/types/AtlasErrors.sol";

import "forge-std/Test.sol";

abstract contract DAppControlTemplate {
    uint32 internal constant DEFAULT_SOLVER_GAS_LIMIT = 1_000_000;

    constructor() { }

    // Virtual functions to be overridden by participating dApp governance
    // (not FastLane) prior to deploying contract. Note that dApp governance
    // will "own" this contract but that it should be immutable.

    /////////////////////////////////////////////////////////
    //                  PRE OPS                            //
    /////////////////////////////////////////////////////////
    //
    // PreOps:
    // Data should be decoded as:
    //
    //     bytes calldata userOpData
    //

    // _preOpsCall
    // Details:
    //  preOps/delegate =
    //      Inputs: User's calldata
    //      Function: Executing the function set by DAppControl
    //      Container: Inside of the FastLane ExecutionEnvironment
    //      Access: With storage access (read + write) only to the ExecutionEnvironment
    //
    // DApp exposure: Trustless
    // User exposure: Trustless
    function _preOpsCall(UserOperation calldata userOp) internal virtual returns (bytes memory) {
        revert AtlasErrors.NotImplemented();
    }

    /////////////////////////////////////////////////////////
    //                MEV ALLOCATION                       //
    /////////////////////////////////////////////////////////
    //
    // _allocateValueCall
    // Details:
    //  allocate/delegate =
    //      Inputs: MEV Profits (ERC20 balances)
    //      Function: Executing the function set by DAppControl / MEVAllocator
    //      Container: Inside of the FastLane ExecutionEnvironment
    //      Access: With storage access (read + write) only to the ExecutionEnvironment
    //
    // DApp exposure: Trustless
    // User exposure: Trustless
    function _allocateValueCall(
        UserOperation calldata userOp,
        address bidToken,
        uint256 bidAmount,
        bytes calldata data
    )
        internal
        virtual;

    /////////////////////////////////////////////////////////
    //              INTENT FULFILLMENT                     //
    /////////////////////////////////////////////////////////
    //

    // _preSolverCall
    //
    // Details:
    //  Data should be decoded as:
    //
    //    address solverTo, bytes memory returnData
    //
    //  fulfillment(preOps)/delegatecall =
    //      Inputs: preOps call's returnData, winning solver to address
    //      Function: Executing the function set by DAppControl
    //      Container: Inside of the FastLane ExecutionEnvironment
    //      Access: Storage access (read+write) to the ExecutionEnvironment contract
    //      NOTE: This happens *inside* of the solver's try/catch wrapper
    //      and is designed to give the solver everything they need to fulfill
    //      the user's 'intent.'

    function _preSolverCall(
        UserOperation calldata userOp,
        SolverOperation calldata solverOp,
        bytes calldata returnData
    )
        internal
        virtual
        returns (bool)
    {
        revert AtlasErrors.NotImplemented();
    }

    // _postSolverCall
    //
    // Details:
    //
    //  Data should be decoded as:
    //
    //    address solverTo, bytes memory returnData
    //

    //  fulfillment(verification)/delegatecall =
    //      Inputs: preOps call's returnData, winning solver to address
    //      Function: Executing the function set by DAppControl
    //      Container: Inside of the FastLane ExecutionEnvironment
    //      Access: Storage access (read+write) to the ExecutionEnvironment contract
    //      NOTE: This happens *inside* of the solver's try/catch wrapper
    //      and is designed to make sure that the solver is fulfilling
    //      the user's 'intent.'

    function _postSolverCall(
        UserOperation calldata userOp,
        SolverOperation calldata solverOp,
        bytes calldata returnData
    )
        internal
        virtual
        returns (bool)
    {
        revert AtlasErrors.NotImplemented();
    }

    /////////////////////////////////////////////////////////
    //                  VERIFICATION                       //
    /////////////////////////////////////////////////////////
    //
    // Data should be decoded as:
    //
    //    bytes memory returnData
    //

    // _postOpsCall
    // Details:
    //  verification/delegatecall =
    //      Inputs: User's return data + preOps call's returnData
    //      Function: Executing the function set by DAppControl
    //      Container: Inside of the FastLane ExecutionEnvironment
    //      Access: Storage access (read+write) to the ExecutionEnvironment contract
    function _postOpsCall(
        UserOperation calldata userOp,
        bool solved,
        bytes calldata data
    )
        internal
        virtual
        returns (bool)
    {
        revert AtlasErrors.NotImplemented();
    }

    /////////////////////////////////////////////////////////
    //                 GETTERS & HELPERS                   //
    /////////////////////////////////////////////////////////
    //
    // View functions used by the backend to verify bid format
    // and by the factory and DAppVerification to verify the
    // backend.
    function getBidFormat(UserOperation calldata userOp) public view virtual returns (address bidToken);

    function getBidValue(SolverOperation calldata solverOp) public view virtual returns (uint256);

    function getSolverGasLimit() public view virtual returns (uint32) {
        return DEFAULT_SOLVER_GAS_LIMIT;
    }
}
