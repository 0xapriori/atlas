//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.25;

contract AtlasEvents {
    // Metacall events
    event MetacallResult(address indexed bundler, address indexed user, address indexed winningSolver);
    event SolverExecution(address indexed solver, uint256 index, bool isWin);

    // AtlETH
    event Bond(address indexed owner, uint256 amount);
    event Unbond(address indexed owner, uint256 amount, uint256 earliestAvailable);
    event Redeem(address indexed owner, uint256 amount);
    event Transfer(address indexed from, address indexed to, uint256 amount);
    event Approval(address indexed owner, address indexed spender, uint256 amount);

    // Escrow call step events
    event PreOpsCall(address environment, bool success, bytes returnData);
    event UserCall(address environment, bool success, bytes returnData);
    event PostOpsCall(address environment, bool success); // No return data tracking for post ops?

    // Factory
    event ExecutionEnvironmentCreated(address indexed user, address indexed executionEnvironment);

    // Gas accounting
    event GasRefundSettled(address indexed bundler, uint256 refundedETH);

    // Surcharge events
    event SurchargeWithdrawn(address to, uint256 amount);
    event SurchargeRecipientTransferStarted(address currentRecipient, address newRecipient);
    event SurchargeRecipientTransferred(address newRecipient);

    event SolverTxResult(
        address indexed solverTo, address indexed solverFrom, bool executed, bool success, uint256 result
    );
    event UserTxResult(address indexed user, uint256 valueReturned, uint256 gasRefunded);
    event MEVPaymentFailure(address indexed controller, uint32 callConfig, address bidToken, uint256 bidAmount);
}
