//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

import { SafeTransferLib, ERC20 } from "solmate/utils/SafeTransferLib.sol";
import { Base } from "src/contracts/common/ExecutionBase.sol";

import { ISolverContract } from "src/contracts/interfaces/ISolverContract.sol";
import { ISafetyLocks } from "src/contracts/interfaces/ISafetyLocks.sol";
import { IDAppControl } from "src/contracts/interfaces/IDAppControl.sol";
import { IEscrow } from "src/contracts/interfaces/IEscrow.sol";

import { AtlasErrors } from "src/contracts/types/AtlasErrors.sol";
import { CallBits } from "src/contracts/libraries/CallBits.sol";
import { ExecutionPhase } from "src/contracts/types/LockTypes.sol";
import "src/contracts/types/SolverCallTypes.sol";
import "src/contracts/types/UserCallTypes.sol";
import "src/contracts/types/DAppApprovalTypes.sol";

/// @title ExecutionEnvironment
/// @author FastLane Labs
/// @notice An Execution Environment contract is deployed for each unique combination of User address x DAppControl
/// address that interacts with the Atlas protocol via a metacall transaction.
contract ExecutionEnvironment is Base {
    using CallBits for uint32;

    uint8 private constant _ENVIRONMENT_DEPTH = 1 << 1;

    constructor(address _atlas) Base(_atlas) { }

    modifier validUser(UserOperation calldata userOp) {
        if (userOp.from != _user()) {
            revert("ERR-CE02 InvalidUser");
        }
        if (userOp.to != atlas || userOp.dapp == atlas) {
            revert("ERR-EV007 InvalidTo");
        }
        _;
    }

    modifier validControlHash() {
        if (_control().codehash != _controlCodeHash()) {
            revert("ERR-EV008 InvalidCodeHash");
        }
        _;
    }

    modifier contributeSurplus() {
        _;
        {
            uint256 balance = address(this).balance;
            if (balance > 0) {
                IEscrow(atlas).contribute{ value: balance }();
            }
        }
    }

    //////////////////////////////////
    ///    CORE CALL FUNCTIONS     ///
    //////////////////////////////////

    /// @notice The preOpsWrapper function may be called by Atlas before the UserOperation is executed.
    /// @dev This contract is called by the Atlas contract, and delegatecalls the DAppControl contract via the
    /// corresponding `preOpsCall` function.
    /// @param userOp The UserOperation struct.
    /// @return preOpsData Data to be passed to the next call phase.
    function preOpsWrapper(UserOperation calldata userOp)
        external
        validUser(userOp)
        onlyAtlasEnvironment(ExecutionPhase.PreOps, _ENVIRONMENT_DEPTH)
        returns (bytes memory)
    {
        bytes memory preOpsData = forward(abi.encodeWithSelector(IDAppControl.preOpsCall.selector, userOp));

        bool success;
        (success, preOpsData) = _control().delegatecall(preOpsData);

        require(success, "ERR-EC02 DelegateRevert");

        preOpsData = abi.decode(preOpsData, (bytes));
        return preOpsData;
    }

    /// @notice The userWrapper function is called by Atlas to execute the UserOperation.
    /// @dev This contract is called by the Atlas contract, and either delegatecalls or calls the DAppControl contract
    /// with `userOp.data` as calldata, depending on the the needsDelegateUser flag.
    /// @param userOp The UserOperation struct.
    /// @return returnData Data to be passed to the next call phase.
    function userWrapper(UserOperation calldata userOp)
        external
        payable
        validUser(userOp)
        onlyAtlasEnvironment(ExecutionPhase.UserOperation, _ENVIRONMENT_DEPTH)
        validControlHash
        contributeSurplus
        returns (bytes memory returnData)
    {
        uint32 config = _config();

        require(address(this).balance >= userOp.value, "ERR-CE01 ValueExceedsBalance");

        bool success;

        if (config.needsDelegateUser()) {
            (success, returnData) = userOp.dapp.delegatecall(forward(userOp.data));
            require(success, "ERR-EC02 DelegateRevert");
        } else {
            // regular user call - executed at regular destination and not performed locally
            (success, returnData) = userOp.dapp.call{ value: userOp.value }(forward(userOp.data));
            require(success, "ERR-EC04a CallRevert");
        }
    }

    /// @notice The postOpsWrapper function may be called by Atlas as the last phase of a `metacall` transaction.
    /// @dev This contract is called by the Atlas contract, and delegatecalls the DAppControl contract via the
    /// corresponding `postOpsCall` function.
    /// @param solved Boolean indicating whether a winning SolverOperation was executed successfully.
    /// @param returnData Data returned from the previous call phase.
    function postOpsWrapper(
        bool solved,
        bytes calldata returnData
    )
        external
        onlyAtlasEnvironment(ExecutionPhase.PostOps, _ENVIRONMENT_DEPTH)
    {
        bytes memory data = forward(abi.encodeWithSelector(IDAppControl.postOpsCall.selector, solved, returnData));

        bool success;
        (success, data) = _control().delegatecall(data);

        require(success, "ERR-EC02 DelegateRevert");
        require(abi.decode(data, (bool)), "ERR-EC03a DelegateUnsuccessful");
    }

    /// @notice The solverMetaTryCatch function is called by Atlas to execute the SolverOperation, as well as any
    /// preSolver or postSolver hooks that the DAppControl contract may require.
    /// @dev This contract is called by the Atlas contract, delegatecalls the preSolver and postSolver hooks if
    /// required, and executes the SolverOperation by calling the `solverOp.solver` address.
    /// @param bidAmount The Solver's bid amount.
    /// @param gasLimit The gas limit for the SolverOperation.
    /// @param solverOp The SolverOperation struct.
    /// @param returnData Data returned from the previous call phase.
    function solverMetaTryCatch(
        uint256 bidAmount,
        uint256 gasLimit,
        SolverOperation calldata solverOp,
        bytes calldata returnData
    )
        external
        payable
        onlyAtlasEnvironment(ExecutionPhase.SolverOperations, _ENVIRONMENT_DEPTH)
    {
        require(address(this).balance == solverOp.value, "ERR-CE05 IncorrectValue");

        uint32 config = _config();
        address control = _control();

        // Track token balance to measure if the bid amount is paid.
        bool etherIsBidToken;
        uint256 startBalance;

        // Set the startBalance to use later for bid accounting
        if (solverOp.bidToken == address(0)) {
            startBalance = 0; // address(this).balance - solverOp.value;
            etherIsBidToken = true;
            // ERC20 balance
        } else {
            startBalance = ERC20(solverOp.bidToken).balanceOf(address(this));
        }

        ////////////////////////////
        // SOLVER SAFETY CHECKS //
        ////////////////////////////

        // Verify that the DAppControl contract matches the solver's expectations
        if (solverOp.control != control) {
            revert AtlasErrors.AlteredControl();
        }

        bool success;

        // Handle any solver preOps, if necessary
        if (config.needsPreSolver()) {
            bytes memory data = forwardSpecial(
                abi.encodeWithSelector(IDAppControl.preSolverCall.selector, solverOp, returnData),
                ExecutionPhase.PreSolver
            );

            (success, data) = control.delegatecall(data);

            if (!success) {
                revert AtlasErrors.PreSolverFailed();
            }

            success = abi.decode(data, (bool));
            if (!success) {
                revert AtlasErrors.PreSolverFailed();
            }

            // Verify that the hook didn't illegally enter the Solver contract
            // success = "calledBack"
            (, success,) = IEscrow(atlas).solverLockData();
            if (success) revert AtlasErrors.InvalidEntry();
        }

        // Execute the solver call.
        bytes memory solverCallData = abi.encodeWithSelector(
            ISolverContract.atlasSolverCall.selector,
            solverOp.from,
            solverOp.bidToken,
            bidAmount,
            solverOp.data,
            config.forwardReturnData() ? returnData : new bytes(0)
        );
        (success,) = solverOp.solver.call{ gas: gasLimit, value: solverOp.value }(solverCallData);

        // Verify that it was successful
        if (!success) {
            revert AtlasErrors.SolverOperationReverted();
        }

        // If this was a user intent, handle and verify fulfillment
        if (config.needsSolverPostCall()) {
            // Verify that the solver contract hit the callback before handing over to PostSolver hook
            // NOTE The balance may still be unfulfilled and handled by the PostSolver hook.
            (, success,) = IEscrow(atlas).solverLockData();
            if (!success) revert AtlasErrors.CallbackNotCalled();

            bytes memory data = forwardSpecial(
                abi.encodeWithSelector(IDAppControl.postSolverCall.selector, solverOp, returnData),
                ExecutionPhase.PostSolver
            );

            (success, data) = control.delegatecall(data);

            if (!success) {
                revert AtlasErrors.PostSolverFailed();
            }

            success = abi.decode(data, (bool));
            if (!success) {
                revert AtlasErrors.IntentUnfulfilled();
            }
        }

        // Set the endBalance to use for bid accounting
        uint256 endBalance = etherIsBidToken ? address(this).balance : ERC20(solverOp.bidToken).balanceOf(address(this));

        // Check if this is the bid finding iteration (first step) of a two-step on-chain, ex post bid search. 
        // If so, calculate what the bid would have been assuming that the amount received is the bid, and then
        // revert afterwards with the bidAmount as the argument for the error.
        // NOTE: For ex post bidding, the solverOp.bidAmount is the solver's MAX or MIN bid depending on whether 
        // or not bids are inverted.  A solverOp.bidAmount of zero corresponds with there being no maximum or 
        // minimum specified.
        if (_bidFind()) {
            // netBid track's the calculated bid for the solver for this bid finding iteration.
            uint256 netBid;

            // If invertsBidValue is true, the solver with the smallest bid will win. This is useful
            // when solvers are competing to see which takes the least amount of tokens from a user.
            // CASE: Largest bid wins
            if (!config.invertsBidValue()) {
                // Calculate the bid received
                netBid = endBalance - startBalance; // intentionally underflow on fail

                // CASE: Solver specified a maxBid and the actual bid exceeded the maxBid.
                if (solverOp.bidAmount != 0 && netBid > solverOp.bidAmount) {
                    // Set the netBid to be the max bid. 
                    netBid = solverOp.bidAmount;

                    // We reuse the endBalance variable to hold the surplus ETH balance that can
                    // be contributed back to the Atlas gas accounting system.  If etherIsBidToken,
                    // we avoid contributing the bid amount. 
                    endBalance = etherIsBidToken ? netBid - solverOp.bidAmount : address(this).balance;
                
                // CASE: Solver's netBid is their actual bid. 
                } else {
                    // TODO: This can be endBalance = etherIsBidToken ? 0 : address(this).balance;
                    endBalance = 0;
                }

            // CASE: Smallest bid wins
            } else {
                // Calculate the bid received
                // NOTE: For inverted bid amounts, the startBalance is greater than the endBalance
                // because the solvers compete to take the least. 
                netBid = startBalance - endBalance; // intentionally underflow on fail

                // CASE: Solver specified a minimum bid and the actual bid was less than the minimum bid.
                if (solverOp.bidAmount != 0 && netBid < solverOp.bidAmount) {
                    // Set the netBid to be the min bid. 
                    netBid = solverOp.bidAmount;

                    // We reuse the endBalance variable to hold the surplus ETH balance that can
                    // be contributed back to the Atlas gas accounting system.  If etherIsBidToken,
                    // we avoid contributing the bid amount.
                    // NOTE: Because the solvers compete to take the least, if we increase netBid to 
                    // equal solverOp.bidAmount then solverOp.bidAmount - netBid should represent any 
                    // requested-but-not-used ETH, which can be contributed. Here we set it to zero to 
                    // allow for the possibility that the solver contributed it directly via reconcile()
                    endBalance = etherIsBidToken ? 0 : address(this).balance;
                } else {
                    // TODO: Could be endBalance = etherIsBidToken ? 0 : address(this).balance;
                    endBalance = 0;
                }
            }

            // Contribute any surplus balance
            if (endBalance > 0) {
                IEscrow(atlas).contribute{ value: endBalance }();
            }

            // Verify payback
            (, success) = IEscrow(atlas).validateBalances();
            if (!success) revert AtlasErrors.BalanceNotReconciled();

            // Solver bid was successful, revert with the bid amount as the arg.
            revert AtlasErrors.BidFindSuccessful(netBid);
        }

        // This is either the only iteration of a non-ex post bid transaction, or the second
        // iteration of an ex post bid transaction. We verify that the solver paid what they bid
        // CASE: Largest bid wins,  endBalance > startBalance
        if (!config.invertsBidValue()) {

            // When the largest bid wins, the bid amount is the amount transferred in by the solver. 
            // The endBalance must be greater than or equal to the startBalance plus the bid amount.
            // NOTE: Use bidAmount arg instead of solverOp element to ensure that any ex ante bid results
            // from a bidFinding iteration aren't tampered with or otherwise altered.
            if (endBalance < startBalance + bidAmount) {
                revert AtlasErrors.SolverBidUnpaid();
            }

            // We reuse the endBalance variable to hold the surplus ETH balance that can
            // be contributed back to the Atlas gas accounting system.  If etherIsBidToken,
            // we avoid contributing the bid amount.
            endBalance = etherIsBidToken ? endBalance - bidAmount : address(this).balance;

        // CASE: Smallest bid wins,  startBalance > endBalance
        } else {

            // When the smallest bid wins, the bid amount is the amount transferred out by the solver.
            // The endBalance must be greater than or equal to the startBalance less the bid amount.
            // In other words, we verify that the solver didn't take more than they said they'd take.
            // NOTE: Use bidAmount arg instead of solverOp element to ensure that any ex ante bid results
            // from a bidFinding iteration aren't tampered with or otherwise altered.
            if (endBalance < startBalance - bidAmount) {
                // underflow -> revert = intended
                revert AtlasErrors.SolverBidUnpaid();
            }

            // We reuse the endBalance variable to hold the surplus ETH balance that can
            // be contributed back to the Atlas gas accounting system.  If etherIsBidToken,
            // we avoid contributing the bid amount.  Because the Solver already took what
            // they need from the contract, we assume any remaining balance can be contributed. 
            endBalance = etherIsBidToken ? endBalance : address(this).balance; 
        }

        // Contribute any surplus back - this may be used to validate balance.
        if (endBalance > 0) {
            IEscrow(atlas).contribute{ value: endBalance }();
        }

        // Verify that the solver repaid their msg.value
        (, success) = IEscrow(atlas).validateBalances();
        if (!success) {
            revert AtlasErrors.BalanceNotReconciled();
        }
    }

    /// @notice The allocateValue function is called by Atlas after a successful SolverOperation.
    /// @dev This contract is called by the Atlas contract, and delegatecalls the DAppControl contract via the
    /// corresponding `allocateValueCall` function.
    /// @param bidToken The address of the token used for the winning SolverOperation's bid.
    /// @param bidAmount The winning bid amount.
    /// @param allocateData Data returned from the previous call phase.
    function allocateValue(
        address bidToken,
        uint256 bidAmount,
        bytes memory allocateData
    )
        external
        onlyAtlasEnvironment(ExecutionPhase.HandlingPayments, _ENVIRONMENT_DEPTH)
        contributeSurplus
    {
        allocateData =
            forward(abi.encodeWithSelector(IDAppControl.allocateValueCall.selector, bidToken, bidAmount, allocateData));

        (bool success,) = _control().delegatecall(allocateData);
        require(success, "ERR-EC02 DelegateRevert");
    }

    ///////////////////////////////////////
    //  USER SUPPORT / ACCESS FUNCTIONS  //
    ///////////////////////////////////////

    /// @notice The withdrawERC20 function allows the environment owner to withdraw ERC20 tokens from this Execution
    /// Environment.
    /// @dev This function is only callable by the environment owner and only when Atlas is in an unlocked state.
    /// @param token The address of the ERC20 token to withdraw.
    /// @param amount The amount of the ERC20 token to withdraw.
    function withdrawERC20(address token, uint256 amount) external {
        require(msg.sender == _user(), "ERR-EC01 NotEnvironmentOwner");
        require(ISafetyLocks(atlas).isUnlocked(), "ERR-EC15 EscrowLocked");

        if (ERC20(token).balanceOf(address(this)) >= amount) {
            SafeTransferLib.safeTransfer(ERC20(token), msg.sender, amount);
        } else {
            revert("ERR-EC02 BalanceTooLow");
        }
    }

    /// @notice The factoryWithdrawERC20 function allows Atlas to withdraw ERC20 tokens from this Execution Environment,
    /// to the original user of this environment.
    /// @dev This function is only callable by the Atlas contract and only when Atlas is in an unlocked state.
    /// @param msgSender The address of the original user of this environment.
    /// @param token The address of the ERC20 token to withdraw.
    /// @param amount The amount of the ERC20 token to withdraw.
    function factoryWithdrawERC20(address msgSender, address token, uint256 amount) external {
        require(msg.sender == atlas, "ERR-EC10 NotFactory");
        require(msgSender == _user(), "ERR-EC11 NotEnvironmentOwner");
        require(ISafetyLocks(atlas).isUnlocked(), "ERR-EC15 EscrowLocked");

        if (ERC20(token).balanceOf(address(this)) >= amount) {
            SafeTransferLib.safeTransfer(ERC20(token), _user(), amount);
        } else {
            revert("ERR-EC02 BalanceTooLow");
        }
    }

    /// @notice The withdrawEther function allows the environment owner to withdraw Ether from this Execution
    /// Environment.
    /// @dev This function is only callable by the environment owner and only when Atlas is in an unlocked state.
    /// @param amount The amount of Ether to withdraw.
    function withdrawEther(uint256 amount) external {
        require(msg.sender == _user(), "ERR-EC01 NotEnvironmentOwner");
        require(ISafetyLocks(atlas).isUnlocked(), "ERR-EC15 EscrowLocked");

        if (address(this).balance >= amount) {
            SafeTransferLib.safeTransferETH(msg.sender, amount);
        } else {
            revert("ERR-EC03 BalanceTooLow");
        }
    }

    /// @notice The factoryWithdrawEther function allows Atlas to withdraw Ether from this Execution Environment, to the
    /// original user of this environment.
    /// @dev This function is only callable by the Atlas contract and only when Atlas is in an unlocked state.
    /// @param msgSender The address of the original user of this environment.
    /// @param amount The amount of Ether to withdraw.
    function factoryWithdrawEther(address msgSender, uint256 amount) external {
        require(msg.sender == atlas, "ERR-EC10 NotFactory");
        require(msgSender == _user(), "ERR-EC11 NotEnvironmentOwner");
        require(ISafetyLocks(atlas).isUnlocked(), "ERR-EC15 EscrowLocked");

        if (address(this).balance >= amount) {
            SafeTransferLib.safeTransferETH(_user(), amount);
        } else {
            revert("ERR-EC03 BalanceTooLow");
        }
    }

    /// @notice The getUser function returns the address of the user of this Execution Environment.
    /// @return user The address of the user of this Execution Environment.
    function getUser() external pure returns (address user) {
        user = _user();
    }

    /// @notice The getControl function returns the address of the DAppControl contract of the current metacall
    /// transaction.
    /// @return control The address of the DAppControl contract of the current metacall transaction.
    function getControl() external pure returns (address control) {
        control = _control();
    }

    /// @notice The getConfig function returns the CallConfig of the current metacall transaction.
    /// @return config The CallConfig in uint32 form of the current metacall transaction.
    function getConfig() external pure returns (uint32 config) {
        config = _config();
    }

    /// @notice The getEscrow function returns the address of the Atlas/Escrow contract.
    /// @return escrow The address of the Atlas/Escrow contract.
    function getEscrow() external view returns (address escrow) {
        escrow = atlas;
    }

    receive() external payable { }

    fallback() external payable { }
}
