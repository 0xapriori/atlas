//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

enum ValidCallsResult {
    Valid,
    GasPriceHigherThanMax,
    TxValueLowerThanCallValue,
    DAppSignatureInvalid,
    UserSignatureInvalid,
    TooManySolverOps,
    UserDeadlineReached,
    DAppDeadlineReached,
    ExecutionEnvEmpty,
    NoSolverOp,
    UnknownAuctioneerNotAllowed,
    InvalidSequence,
    InvalidAuctioneer,
    InvalidBundler,
    OpHashMismatch,
    DeadlineMismatch,
    InvalidControl,
    InvalidSolverGasLimit,
    InvalidDAppNonce,
    CallConfigMismatch,
    DAppToInvalid,
    UserFromInvalid,
    UserSmartWalletInvalid,
    ControlMismatch,
    UserNonceInvalid,
    InvalidCallChainHash
}
