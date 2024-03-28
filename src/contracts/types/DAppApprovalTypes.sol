//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.25;

bytes32 constant DAPP_TYPE_HASH = keccak256(
    "DAppApproval(address from,address to,uint256 value,uint256 gas,uint256 nonce,uint256 deadline,address control,address bundler,bytes32 userOpHash,bytes32 callChainHash)"
);

struct DAppOperation {
    address from; // signor address
    address to; // Atlas address
    uint256 value;
    uint256 gas;
    uint256 nonce;
    uint256 deadline;
    address control; // control
    address bundler; // msg.sender
    bytes32 userOpHash; // keccak256 of userOp.to, userOp.data
    bytes32 callChainHash; // keccak256 of the solvers' txs
    bytes signature;
}

struct DAppConfig {
    address to;
    uint32 callConfig;
    address bidToken;
    uint32 solverGasLimit;
}

struct CallConfig {
    bool userNoncesSequenced;
    bool dappNoncesSequenced;
    bool requirePreOps;
    bool trackPreOpsReturnData;
    bool trackUserReturnData;
    bool delegateUser;
    bool preSolver;
    bool postSolver;
    bool requirePostOps;
    bool zeroSolvers;
    bool reuseUserOp;
    bool userAuctioneer;
    bool solverAuctioneer;
    bool unknownAuctioneer;
    bool verifyCallChainHash;
    bool forwardReturnData;
    bool requireFulfillment;
    bool trustedOpHash;
    bool invertBidValue;
    bool exPostBids;
}

enum CallConfigIndex {
    UserNoncesSequenced,
    DAppNoncesSequenced,
    RequirePreOps,
    TrackPreOpsReturnData,
    TrackUserReturnData,
    DelegateUser,
    PreSolver,
    PostSolver,
    RequirePostOpsCall,
    ZeroSolvers,
    ReuseUserOp,
    UserAuctioneer,
    SolverAuctioneer,
    UnknownAuctioneer,
    // Default = DAppAuctioneer
    VerifyCallChainHash,
    ForwardReturnData,
    RequireFulfillment,
    TrustedOpHash,
    InvertBidValue,
    ExPostBids
}
