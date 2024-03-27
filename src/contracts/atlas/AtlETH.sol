// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity 0.8.25;

import { SafeTransferLib } from "solmate/utils/SafeTransferLib.sol";

import "../types/EscrowTypes.sol";
import { Permit69 } from "../common/Permit69.sol";

/// @notice Modified Solmate ERC20 with some Atlas-specific modifications.
/// @author FastLane Labs
/// @author Modified from Solmate (https://github.com/transmissions11/solmate/blob/main/src/tokens/ERC20.sol)
/// @dev Do not manually set balances without updating totalSupply, as the sum of all user balances must not exceed it.
abstract contract AtlETH is Permit69 {
    constructor(
        uint256 _escrowDuration,
        address _verification,
        address _simulator,
        address _surchargeRecipient
    )
        Permit69(_escrowDuration, _verification, _simulator, _surchargeRecipient)
    { }

    /*//////////////////////////////////////////////////////////////
                                ATLETH
    //////////////////////////////////////////////////////////////*/

    function balanceOf(address account) external view returns (uint256) {
        return uint256(_balanceOf[account].balance);
    }

    function balanceOfBonded(address account) external view returns (uint256) {
        return uint256(accessData[account].bonded);
    }

    function balanceOfUnbonding(address account) external view returns (uint256) {
        return uint256(_balanceOf[account].unbonding);
    }

    function accountLastActiveBlock(address account) external view returns (uint256) {
        return uint256(accessData[account].lastAccessedBlock);
    }

    function unbondingCompleteBlock(address account) external view returns (uint256) {
        uint256 lastAccessedBlock = uint256(accessData[account].lastAccessedBlock);
        if (lastAccessedBlock == 0) return 0;
        return lastAccessedBlock + ESCROW_DURATION;
    }

    // Deposit ETH and get atlETH in return.
    function deposit() external payable {
        _mint(msg.sender, msg.value);
    }

    // Redeem atlETH for ETH.
    function withdraw(uint256 amount) external {
        _burn(msg.sender, amount);
        SafeTransferLib.safeTransferETH(msg.sender, amount);
    }

    /*//////////////////////////////////////////////////////////////
                               ERC20 LOGIC
    //////////////////////////////////////////////////////////////*/

    function approve(address spender, uint256 amount) public returns (bool) {
        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    function transfer(address to, uint256 amount) public returns (bool) {
        _deduct(msg.sender, amount);
        _balanceOf[to].balance += uint112(amount);

        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) public returns (bool) {
        uint256 allowed = allowance[from][msg.sender]; // Saves gas for limited approvals.
        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;
        _deduct(from, amount);
        _balanceOf[to].balance += uint112(amount);
        emit Transfer(from, to, amount);
        return true;
    }

    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    )
        public
    {
        if (deadline < block.timestamp) revert PermitDeadlineExpired();
        // Unchecked because the only math done is incrementing
        // the owner's nonce which cannot realistically overflow.
        unchecked {
            address recoveredAddress = ecrecover(
                keccak256(
                    abi.encodePacked(
                        "\x19\x01",
                        DOMAIN_SEPARATOR(),
                        keccak256(
                            abi.encode(
                                keccak256(
                                    "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"
                                ),
                                owner,
                                spender,
                                value,
                                nonces[owner]++,
                                deadline
                            )
                        )
                    )
                ),
                v,
                r,
                s
            );
            if (recoveredAddress == address(0) || recoveredAddress != owner) revert InvalidSigner();
            allowance[recoveredAddress][spender] = value;
        }
        emit Approval(owner, spender, value);
    }

    function DOMAIN_SEPARATOR() public view returns (bytes32) {
        return block.chainid == INITIAL_CHAIN_ID ? INITIAL_DOMAIN_SEPARATOR : _computeDomainSeparator();
    }

    function _computeDomainSeparator() internal view override returns (bytes32) {
        return keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256(bytes(name)),
                keccak256("1"),
                block.chainid,
                address(this)
            )
        );
    }

    /*//////////////////////////////////////////////////////////////
                        INTERNAL MINT/BURN LOGIC
    //////////////////////////////////////////////////////////////*/

    function _mint(address to, uint256 amount) internal {
        totalSupply += amount;
        _balanceOf[to].balance += uint112(amount);
        emit Transfer(address(0), to, amount);
    }

    function _burn(address from, uint256 amount) internal {
        _deduct(from, amount);
        totalSupply -= amount;
        emit Transfer(from, address(0), amount);
    }

    // NOTE: This does not change total supply.
    function _deduct(address account, uint256 amount) internal {
        uint112 amt = uint112(amount);

        EscrowAccountBalance memory aData = _balanceOf[account];

        uint112 balance = aData.balance;

        if (amt <= balance) {
            _balanceOf[account].balance = balance - amt;
        } else if (block.number > accessData[account].lastAccessedBlock + ESCROW_DURATION) {
            uint112 _shortfall = amt - balance;
            aData.balance = 0;
            aData.unbonding -= _shortfall; // underflow here to revert if insufficient balance
            _balanceOf[account] = aData;

            uint256 shortfall256 = uint256(_shortfall);
            totalSupply += shortfall256; // add the released supply back to atleth.
            bondedTotalSupply -= shortfall256; // subtract the unbonded, freed amount
        } else {
            // Reverts because amount > account's balance
            revert InsufficientBalanceForDeduction(_balanceOf[account].balance, amount);
        }
    }

    /*//////////////////////////////////////////////////////////////
                    EXTERNAL BOND/UNBOND LOGIC
    //////////////////////////////////////////////////////////////*/

    // Puts a "hold" on a solver's AtlETH, enabling it to be used in Atlas transactions
    // Bonded AtlETH must first be unbonded to become transferrable or withdrawable
    function bond(uint256 amount) external {
        // TODO: consider allowing msg.sender to bond another account holder via allowance
        _bond(msg.sender, amount);
    }

    // Deposits the sender's full msg.value and converts to AtlETH
    // Then bonds the sender's amountToBond of AtlETH
    function depositAndBond(uint256 amountToBond) external payable {
        _mint(msg.sender, msg.value);
        _bond(msg.sender, amountToBond);
    }

    // Starts the unbonding wait time.
    // Unbonding AtlETH can still be used be solvers while unbonding,
    // but adjustments may be made at withdrawal to ensure solvency
    function unbond(uint256 amount) external {
        _unbond(msg.sender, amount);
    }

    function redeem(uint256 amount) external {
        _redeem(msg.sender, amount);
    }

    /*//////////////////////////////////////////////////////////////
                    INTERNAL BOND/UNBOND LOGIC
    //////////////////////////////////////////////////////////////*/

    function _bond(address owner, uint256 amount) internal {
        uint112 amt = uint112(amount);

        _balanceOf[owner].balance -= amt;
        totalSupply -= amount;

        accessData[owner].bonded += amt;
        bondedTotalSupply += amount;

        emit Bond(owner, amount);
    }

    function _unbond(address owner, uint256 amount) internal {
        uint112 amt = uint112(amount);

        // totalSupply and totalBondedSupply are unaffected; continue to count the
        // unbonding amount as bonded total supply since it is still inaccessible
        // for atomic xfer.

        EscrowAccountAccessData memory aData = accessData[owner];

        aData.bonded -= amt;
        aData.lastAccessedBlock = uint32(block.number);
        accessData[owner] = aData;

        _balanceOf[owner].unbonding += amt;

        emit Unbond(owner, amount, block.number + ESCROW_DURATION + 1);
    }

    function _redeem(address owner, uint256 amount) internal {
        if (block.number <= uint256(accessData[owner].lastAccessedBlock) + ESCROW_DURATION) {
            revert EscrowLockActive();
        }

        uint112 amt = uint112(amount);

        EscrowAccountBalance memory bData = _balanceOf[owner];

        bData.unbonding -= amt;
        bondedTotalSupply -= amount;

        bData.balance += amt;
        totalSupply += amount;

        _balanceOf[owner] = bData;

        emit Redeem(owner, amount);
    }

    // Surcharge withdrawals
    function withdrawSurcharge() external {
        if (msg.sender != surchargeRecipient) {
            revert InvalidAccess();
        }

        uint256 paymentAmount = surcharge;
        surcharge = 0; // Clear before transfer to prevent reentrancy
        SafeTransferLib.safeTransferETH(msg.sender, paymentAmount);
        emit SurchargeWithdrawn(msg.sender, paymentAmount);
    }

    // Transfers the surcharge recipient to a new address
    // Only callable by the current surcharge recipient
    // The new recipient must call becomeSurchargeRecipient() for transfer to take effect
    function transferSurchargeRecipient(address newRecipient) external {
        if (msg.sender != surchargeRecipient) {
            revert InvalidAccess();
        }

        pendingSurchargeRecipient = newRecipient;
        emit SurchargeRecipientTransferStarted(surchargeRecipient, newRecipient);
    }

    // Finalizes the transfer of surcharge recipient to a new address
    // Only callable by the pending surcharge recipient
    function becomeSurchargeRecipient() external {
        if (msg.sender != pendingSurchargeRecipient) {
            revert InvalidAccess();
        }

        surchargeRecipient = pendingSurchargeRecipient;
        pendingSurchargeRecipient = address(0);
        emit SurchargeRecipientTransferred(surchargeRecipient);
    }
}
