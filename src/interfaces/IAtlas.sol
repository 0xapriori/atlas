//SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.16;

import {
    ProtocolCall,
    UserCall,
    PayeeData,
    SearcherCall,
    Verification
} from "../libraries/DataTypes.sol";

interface IAtlas {
    function metacall(
        ProtocolCall calldata protocolCall, 
        UserCall calldata userCall,
        PayeeData[] calldata payeeData, 
        SearcherCall[] calldata searcherCalls,
        Verification calldata verification 
    ) external payable;

    function getExecutionEnvironment(
        address protocolControl
    ) external view returns (
        address executionEnvironment
    );

    function untrustedVerifyProtocol(
        address userCallTo,
        uint256 searcherCallsLength,
        ProtocolCall calldata protocolCall,
        Verification calldata verification
    ) external returns (bool);

    function untrustedReleaseLock(bytes32 key) external;
}