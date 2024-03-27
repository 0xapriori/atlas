//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.25;

import "../types/EscrowTypes.sol";
import "../types/LockTypes.sol";

import { AtlasEvents } from "src/contracts/types/AtlasEvents.sol";
import { AtlasErrors } from "src/contracts/types/AtlasErrors.sol";

contract Storage is AtlasEvents, AtlasErrors {
    // Atlas constants
    uint256 internal constant GAS_USED_DECIMALS_TO_DROP = 1000;

    uint256 public immutable ESCROW_DURATION;
    address public immutable VERIFICATION;
    address public immutable SIMULATOR;

    // AtlETH ERC-20 constants
    string public constant name = "Atlas ETH";
    string public constant symbol = "atlETH";
    uint8 public constant decimals = 18;

    // AtlETH EIP-2612 constants
    uint256 internal immutable INITIAL_CHAIN_ID;
    bytes32 internal immutable INITIAL_DOMAIN_SEPARATOR;

    // AtlETH ERC-20 storage
    uint256 public totalSupply;
    uint256 public bondedTotalSupply;

    mapping(address => uint256) public nonces;
    mapping(address => EscrowAccountBalance) internal _balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    mapping(address => EscrowAccountAccessData) public accessData;
    mapping(bytes32 => bool) internal _solverOpHashes; // NOTE: Only used for when allowTrustedOpHash is enabled

    // Gas Accounting constants
    uint256 public constant SURCHARGE = 1_000_000; // Out of 10_000_000
    uint256 internal constant _CALLDATA_LENGTH_PREMIUM = 32; // 16 (default) * 2

    // atlETH GasAccounting storage

    uint256 public surcharge; // Atlas gas surcharges
    address public surchargeRecipient; // Fastlane surcharge recipient
    address public pendingSurchargeRecipient; // For 2-step transfer process

    address internal constant _UNLOCKED = address(0);

    // Atlas SafetyLocks (transient storage)
    /*
    address public lock; // transient storage
    uint256 internal _solverLock; // transient storage
    uint256 public claims; // transient storage
    uint256 public withdrawals; // transient storage
    uint256 public deposits; // transient storage
    */

    uint256 internal constant _LOCK = 0x0000000000000000000000000000000000000000000000000000000000000100;
    uint256 internal constant _SOLVER_LOCK = 0x0000000000000000000000000000000000000000000000000000000000000120;
    uint256 internal constant _CLAIMS = 0x0000000000000000000000000000000000000000000000000000000000000140;
    uint256 internal constant _WITHDRAWALS = 0x0000000000000000000000000000000000000000000000000000000000000160;
    uint256 internal constant _DEPOSITS = 0x0000000000000000000000000000000000000000000000000000000000000180;

    uint256 internal _solverCalledBack = 1 << 161;
    uint256 internal _solverFulfilled = 1 << 162;

    constructor(
        uint256 _escrowDuration,
        address _verification,
        address _simulator,
        address _surchargeRecipient
    )
        payable
    {
        ESCROW_DURATION = _escrowDuration;
        VERIFICATION = _verification;
        SIMULATOR = _simulator;
        INITIAL_CHAIN_ID = block.chainid;
        INITIAL_DOMAIN_SEPARATOR = _computeDomainSeparator();

        // Gas Accounting
        // Initialized with msg.value to seed flash loan liquidity
        surcharge = msg.value;
        surchargeRecipient = _surchargeRecipient;

        // Gas Accounting - transient storage (delete this from constructor post dencun)

        emit SurchargeRecipientTransferred(_surchargeRecipient);
    }

    function solverLockData() public view returns (address currentSolver, bool calledBack, bool fulfilled) {
        uint256 solverLock = tRead(_SOLVER_LOCK);
        currentSolver = address(uint160(solverLock));
        calledBack = solverLock & _solverCalledBack != 0;
        fulfilled = solverLock & _solverFulfilled != 0;
    }

    function solver() public view returns (address) {
        return address(uint160(uint256(tRead(_SOLVER_LOCK))));
    }

    function tRead(uint256 loc) internal view returns (uint256 data) {
        assembly {
            data := tload(loc)
        }
    }

    function tWrite(uint256 loc, uint256 data) internal {
        assembly {
            tstore(loc, data)
        }
    }

    function lock() public view returns (address) {
        return address(uint160(tRead(_LOCK)));
    }

    function deposits() external returns (uint256 _deposits) {
        _deposits = tRead(_DEPOSITS);
    }

    function claims() external returns (uint256 _claims) {
        _claims = tRead(_CLAIMS);
    }

    function withdrawals() external returns (uint256 _withdrawals) {
        _withdrawals = tRead(_WITHDRAWALS);
    }

    function _computeDomainSeparator() internal view virtual returns (bytes32) { }
}
