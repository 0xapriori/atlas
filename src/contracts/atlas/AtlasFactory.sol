//SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.18;

import {IDAppControl} from "../interfaces/IDAppControl.sol";
import {Mimic} from "./Mimic.sol";

// NOTE: Experimental - Splitting contracts into [AtlETH, Atlas, AtlasFactory]

// AtlasFactory needs:
// Factory - everything for creating new Execution Environments
// Exec Env template deployed separately, no internal deploy functions

contract AtlasFactory {
    event NewExecutionEnvironment(
        address indexed environment,
        address indexed user,
        address indexed controller,
        uint32 callConfig
    );

    bytes32 public immutable salt;
    address public immutable executionTemplate;

    constructor(address _executionTemplate) {
        salt = keccak256(abi.encodePacked(block.chainid, address(this), "AtlasFactory 1.0"));
        executionTemplate = _executionTemplate;
    }

    // ------------------ //
    // EXTERNAL FUNCTIONS //
    // ------------------ //

    function createExecutionEnvironment(address dAppControl) external returns (address executionEnvironment) {
        executionEnvironment = _setExecutionEnvironment(dAppControl, msg.sender, dAppControl.codehash);
        // _initializeNonce(msg.sender); // NOTE: called separately by Atlas after calling createExecEnv
    }

    function getMimicCreationCode(address controller, uint32 callConfig, address user, bytes32 controlCodeHash)
        external
        view
        returns (bytes memory creationCode)
    {
        creationCode = _getMimicCreationCode(controller, callConfig, user, controlCodeHash);
    }

    // ------------------ //
    // INTERNAL FUNCTIONS //
    // ------------------ //

    function _setExecutionEnvironment(address dAppControl, address user, bytes32 controlCodeHash)
        internal
        returns (address executionEnvironment)
    {
        uint32 callConfig = IDAppControl(dAppControl).callConfig();

        bytes memory creationCode = _getMimicCreationCode(dAppControl, callConfig, user, controlCodeHash);

        executionEnvironment = address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(bytes1(0xff), address(this), salt, keccak256(abi.encodePacked(creationCode)))
                    )
                )
            )
        );

        if (executionEnvironment.codehash == bytes32(0)) {
            bytes32 memSalt = salt;
            assembly {
                executionEnvironment := create2(0, add(creationCode, 32), mload(creationCode), memSalt)
            }

            emit NewExecutionEnvironment(executionEnvironment, user, dAppControl, callConfig);
        }
    }


    function _getMimicCreationCode(address controller, uint32 callConfig, address user, bytes32 controlCodeHash)
        internal
        view
        returns (bytes memory creationCode)
    {
        address executionLib = executionTemplate;
        // NOTE: Changing compiler settings or solidity versions can break this.
        creationCode = type(Mimic).creationCode;

        // TODO: unpack the SHL and reorient 
        assembly {
            mstore(
                add(creationCode, 85), 
                or(
                    and(
                        mload(add(creationCode, 85)),
                        not(shl(96, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
                    ),
                    shl(96, executionLib)
                )
            )           
            
            mstore(
                add(creationCode, 118), 
                or(
                    and(
                        mload(add(creationCode, 118)),
                        not(shl(96, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
                    ),
                    shl(96, user)
                )
            )    
            
            mstore(
                add(creationCode, 139),
                or(
                    and(
                        mload(add(creationCode, 139)),
                        not(shl(56, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFF))
                    ),
                    add(shl(96, controller), add(shl(88, 0x63), shl(56, callConfig)))
                )
            )

            mstore(add(creationCode, 165), controlCodeHash)
        }
    }

}