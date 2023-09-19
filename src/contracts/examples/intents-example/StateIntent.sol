//SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.16;

// Base Imports
import {SafeTransferLib, ERC20} from "solmate/utils/SafeTransferLib.sol";

// Atlas Base Imports
import {ISafetyLocks} from "../../interfaces/ISafetyLocks.sol";
import {IExecutionEnvironment} from "../../interfaces/IExecutionEnvironment.sol";
import {IEscrow} from "../../interfaces/IEscrow.sol";

import {SafetyBits} from "../../libraries/SafetyBits.sol";

import "../../types/CallTypes.sol";
import "../../types/LockTypes.sol";

// Atlas DApp-Control Imports
import {DAppControl} from "../../dapp/DAppControl.sol";

import "forge-std/Test.sol";

// under construction

enum TimingPath {
    EarliestBlock,
    LatestBlock,
    ExactBlock,
    EarliestTime,
    LatestTime,
    ExactTime
}

struct Timing {
    TimingPath path;
    uint256 value;
}

enum StatePath {
    PriorAbsolute,
    PostAbsolute,
    PositiveDelta,
    NegativeDelta
}

struct StateExpression {
    StatePath path;
    uint8 offset;
    uint8 size;
    bytes32 slot;
    uint256 value;
}

struct StatePreference {
    address src;
    StateExpression[] exp;
}

struct Payment {
    address token;
    uint256 amount;
}

struct Intent {
    StatePreference[] preferences;
    Timing time;
    Payment pmt;
    address from;
}


