//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.22;

import "openzeppelin-contracts/contracts/utils/cryptography/EIP712.sol";
import { DAppIntegration } from "./DAppIntegration.sol";

import { EscrowBits } from "src/contracts/libraries/EscrowBits.sol";
import { CallBits } from "src/contracts/libraries/CallBits.sol";
import { CallVerification } from "src/contracts/libraries/CallVerification.sol";
import { AtlasErrors } from "src/contracts/types/AtlasErrors.sol";
import "src/contracts/types/SolverCallTypes.sol";
import "src/contracts/types/UserCallTypes.sol";
import "src/contracts/types/DAppApprovalTypes.sol";
import "src/contracts/types/EscrowTypes.sol";
import "src/contracts/types/ValidCallsTypes.sol";

/// @title AtlasVerification
/// @author FastLane Labs
/// @notice AtlasVerification handles the verification of DAppConfigs, UserOperations, SolverOperations, and
/// DAppOperations within a metacall to ensure that calldata sourced from various parties is safe and valid.
contract AtlasVerification is EIP712, DAppIntegration {
    using ECDSA for bytes32;
    using CallBits for uint32;
    using CallVerification for UserOperation;

    uint256 internal constant FULL_BITMAP = uint256(0x0000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
    uint256 internal constant FIRST_16_BITS_FULL = uint256(0xFFFF);
    uint256 internal constant FIRST_4_BITS_FULL = uint256(0xF);
    uint8 internal constant MAX_SOLVERS = type(uint8).max - 2;

    constructor(address _atlas) EIP712("AtlasVerification", "1.0") DAppIntegration(_atlas) { }

    /// @notice The validateCalls function verifies the validity of the metacall calldata components.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp The UserOperation struct of the metacall.
    /// @param solverOps An array of SolverOperation structs.
    /// @param dAppOp The DAppOperation struct of the metacall.
    /// @param msgValue The ETH value sent with the metacall transaction.
    /// @param msgSender The forwarded msg.sender of the original metacall transaction in the Atlas contract.
    /// @param isSimulation A boolean indicating if the call is a simulation.
    /// @return userOpHash The hash of the UserOperation struct.
    /// @return The result of the ValidCalls check, in enum ValidCallsResult form.
    function validateCalls(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        DAppOperation calldata dAppOp,
        uint256 msgValue,
        address msgSender,
        bool isSimulation
    )
        external
        returns (bytes32 userOpHash, ValidCallsResult)
    {
        if (msg.sender != ATLAS) revert AtlasErrors.InvalidCaller();
        return _validCalls(dConfig, userOp, solverOps, dAppOp, msgValue, msgSender, isSimulation);
    }

    /// @notice The internal _validCalls function verifies the validity of the metacall calldata components, and is
    /// called by validateCalls.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp The UserOperation struct of the metacall.
    /// @param solverOps An array of SolverOperation structs.
    /// @param dAppOp The DAppOperation struct of the metacall.
    /// @param msgValue The ETH value sent with the metacall transaction.
    /// @param msgSender The forwarded msg.sender of the original metacall transaction in the Atlas contract.
    /// @param isSimulation A boolean indicating if the call is a simulation.
    /// @return userOpHash The hash of the UserOperation struct.
    /// @return The result of the ValidCalls check, in enum ValidCallsResult form.
    function _validCalls(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        DAppOperation calldata dAppOp,
        uint256 msgValue,
        address msgSender,
        bool isSimulation
    )
        internal
        returns (bytes32 userOpHash, ValidCallsResult)
    {
        // Verify that the calldata injection came from the dApp frontend
        // and that the signatures are valid.

        // CASE: Solvers trust app to update content of UserOp after submission of solverOp
        if (dConfig.callConfig.allowsTrustedOpHash()) {
            userOpHash = userOp.getAltOperationHash();

            // SessionKey must match explicitly - cannot be skipped
            if (userOp.sessionKey != dAppOp.from && !isSimulation) {
                return (userOpHash, ValidCallsResult.InvalidAuctioneer);
            }

            // msgSender (the bundler) must be userOp.from, userOp.sessionKey / dappOp.from, or dappOp.bundler
            if (!(msgSender == dAppOp.from || msgSender == dAppOp.bundler || msgSender == userOp.from) && !isSimulation)
            {
                return (userOpHash, ValidCallsResult.InvalidBundler);
            }
        } else {
            userOpHash = userOp.getUserOperationHash();
        }

        uint256 solverOpCount = solverOps.length;

        {
            // bypassSignatoryApproval still verifies signature match, but does not check
            // if dApp approved the signor.
            (bool validAuctioneer, bool bypassSignatoryApproval) = _verifyAuctioneer(dConfig, userOp, solverOps, dAppOp);

            if (!validAuctioneer && !isSimulation) {
                return (userOpHash, ValidCallsResult.InvalidAuctioneer);
            }

            // Check dapp signature
            (bool validDAppOp, ValidCallsResult result) =
                _verifyDApp(dConfig, dAppOp, msgSender, bypassSignatoryApproval, isSimulation);
            if (!validDAppOp) {
                return (userOpHash, result);
            }

            // Check user signature
            if (!_verifyUser(dConfig, userOp, msgSender, isSimulation)) {
                return (userOpHash, ValidCallsResult.UserSignatureInvalid);
            }

            // Check solvers not over the max (253)
            if (solverOpCount > MAX_SOLVERS) {
                return (userOpHash, ValidCallsResult.TooManySolverOps);
            }

            // Check if past user's deadline
            if (block.number > userOp.deadline) {
                if (userOp.deadline != 0 && !isSimulation) {
                    return (userOpHash, ValidCallsResult.UserDeadlineReached);
                }
            }

            // Check if past dapp's deadline
            if (block.number > dAppOp.deadline) {
                if (dAppOp.deadline != 0 && !isSimulation) {
                    return (userOpHash, ValidCallsResult.DAppDeadlineReached);
                }
            }

            // Check gas price is within user's limit
            if (tx.gasprice > userOp.maxFeePerGas) {
                return (userOpHash, ValidCallsResult.GasPriceHigherThanMax);
            }

            // Check that the value of the tx is greater than or equal to the value specified
            if (msgValue < userOp.value) {
                return (userOpHash, ValidCallsResult.TxValueLowerThanCallValue);
            }
        }

        // Some checks are only needed when call is not a simulation
        if (isSimulation) {
            // Add all solver ops if simulation
            return (userOpHash, ValidCallsResult.Valid);
        }

        // Verify a solver was successfully verified.
        if (solverOpCount == 0) {
            if (!dConfig.callConfig.allowsZeroSolvers()) {
                return (userOpHash, ValidCallsResult.NoSolverOp);
            }

            if (dConfig.callConfig.needsFulfillment()) {
                return (userOpHash, ValidCallsResult.NoSolverOp);
            }
        }

        if (userOpHash != dAppOp.userOpHash) {
            return (userOpHash, ValidCallsResult.OpHashMismatch);
        }

        return (userOpHash, ValidCallsResult.Valid);
    }

    /// @notice The verifySolverOp function verifies the validity of a SolverOperation.
    /// @param solverOp The SolverOperation struct to verify.
    /// @param userOpHash The hash of the associated UserOperation struct.
    /// @param userMaxFeePerGas The maximum fee per gas the user is willing to pay.
    /// @param bundler The address of the bundler.
    /// @return result The result of the SolverOperation verification, containing SolverOutcome info in a bitmap.
    function verifySolverOp(
        SolverOperation calldata solverOp,
        bytes32 userOpHash,
        uint256 userMaxFeePerGas,
        address bundler
    )
        external
        view
        returns (uint256 result)
    {
        if (bundler == solverOp.from || _verifySolverSignature(solverOp)) {
            // Validate solver signature
            // NOTE: First two failures are the bundler's fault - solver does not
            // owe a gas refund to the bundler.
            if (solverOp.userOpHash != userOpHash) {
                result |= (1 << uint256(SolverOutcome.InvalidUserHash));
            }

            if (solverOp.to != ATLAS) result |= (1 << uint256(SolverOutcome.InvalidTo));

            // NOTE: The next three failures below here are the solver's fault, and as a result
            // they are on the hook for their own gas cost.
            if (tx.gasprice > solverOp.maxFeePerGas) result |= (1 << uint256(SolverOutcome.GasPriceOverCap));

            if (solverOp.maxFeePerGas < userMaxFeePerGas) {
                result |= (1 << uint256(SolverOutcome.GasPriceBelowUsers));
            }

            if (solverOp.solver == ATLAS || solverOp.solver == address(this)) {
                result |= (1 << uint256(SolverOutcome.InvalidSolver));
            }
            // NOTE: If result is not set above, result stays 0, therefore result is `canExecute == true`
        } else {
            // No refund
            result |= (1 << uint256(SolverOutcome.InvalidSignature));
        }
    }

    /// @notice The _verifyAuctioneer internal function is called by _validCalls to verify that the auctioneer of the
    /// metacall is valid according to the rules set in the DAppConfig.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp The UserOperation struct of the metacall.
    /// @param solverOps An array of SolverOperation structs.
    /// @param dAppOp The DAppOperation struct of the metacall.
    /// @return valid A boolean indicating if the auctioneer is valid.
    /// @return bypassSignatoryApproval A boolean indicating if the signatory approval check should be bypassed.
    function _verifyAuctioneer(
        DAppConfig calldata dConfig,
        UserOperation calldata userOp,
        SolverOperation[] calldata solverOps,
        DAppOperation calldata dAppOp
    )
        internal
        pure
        returns (bool valid, bool bypassSignatoryApproval)
    {
        if (
            dConfig.callConfig.verifyCallChainHash()
                && dAppOp.callChainHash != CallVerification.getCallChainHash(dConfig, userOp, solverOps)
        ) return (false, false);

        if (dConfig.callConfig.allowsUserAuctioneer() && dAppOp.from == userOp.sessionKey) return (true, true);

        if (dConfig.callConfig.allowsSolverAuctioneer() && dAppOp.from == solverOps[0].from) return (true, true);

        if (dConfig.callConfig.allowsUnknownAuctioneer()) return (true, true);

        return (true, false);
    }

    /// @notice The getSolverPayload function returns the hash of a SolverOperation struct.
    /// @param solverOp The SolverOperation struct to hash.
    function getSolverPayload(SolverOperation calldata solverOp) external view returns (bytes32 payload) {
        payload = _hashTypedDataV4(_getSolverHash(solverOp));
    }

    /// @notice The internal _verifySolverSignature function verifies the signature of a SolverOperation.
    /// @param solverOp The SolverOperation struct to verify.
    /// @return A boolean indicating if the signature is valid.
    function _verifySolverSignature(SolverOperation calldata solverOp) internal view returns (bool) {
        if (solverOp.signature.length == 0) return false;
        address signer = _hashTypedDataV4(_getSolverHash(solverOp)).recover(solverOp.signature);
        return signer == solverOp.from;
    }

    /// @notice The _getSolverHash internal function returns the hash of a SolverOperation struct.
    /// @param solverOp The SolverOperation struct to hash.
    /// @return solverHash The hash of the SolverOperation struct.
    function _getSolverHash(SolverOperation calldata solverOp) internal pure returns (bytes32 solverHash) {
        return keccak256(
            abi.encode(
                SOLVER_TYPE_HASH,
                solverOp.from,
                solverOp.to,
                solverOp.value,
                solverOp.gas,
                solverOp.maxFeePerGas,
                solverOp.deadline,
                solverOp.solver,
                solverOp.control,
                solverOp.userOpHash,
                solverOp.bidToken,
                solverOp.bidAmount,
                keccak256(solverOp.data)
            )
        );
    }

    //
    // DAPP VERIFICATION
    //

    /// @notice Verifies that the dapp's data matches the data submitted by the user and solvers. NOTE: The dapp's front
    /// end is the last party in the supply chain to submit data.  If any other party (user, solver, FastLane,  or a
    /// collusion between all of them) attempts to alter it, this check will fail.
    /// @param dConfig The DAppConfig containing configuration details.
    /// @param dAppOp The DAppOperation struct of the metacall.
    /// @param msgSender The forwarded msg.sender of the original metacall transaction in the Atlas contract.
    /// @param bypassSignatoryApproval Boolean indicating whether to bypass signatory approval.
    /// @param isSimulation Boolean indicating whether the execution is a simulation.
    /// @return A boolean indicating if the DAppOperation is valid.
    /// @return The result of the ValidCalls check, in enum ValidCallsResult form.
    function _verifyDApp(
        DAppConfig memory dConfig,
        DAppOperation calldata dAppOp,
        address msgSender,
        bool bypassSignatoryApproval,
        bool isSimulation
    )
        internal
        returns (bool, ValidCallsResult)
    {
        // Verify the signature before storing any data to avoid
        // spoof transactions clogging up dapp nonces

        bool bypassSignature = msgSender == dAppOp.from || (isSimulation && dAppOp.signature.length == 0);

        if (!bypassSignature && !_verifyDAppSignature(dAppOp)) {
            return (false, ValidCallsResult.DAppSignatureInvalid);
        }

        if (bypassSignatoryApproval) return (true, ValidCallsResult.Valid); // If bypass, return true after signature
            // verification

        // NOTE: to avoid replay attacks arising from key management errors,
        // the state changes below must be *saved* even if they render the
        // transaction invalid.
        // TODO: consider dapp-owned gas escrow.  Enshrined account
        // abstraction may render that redundant at a large scale, but
        // allocating different parts of the tx to different parties
        // will allow for optimized trustlessness. This could lead to
        // users not having to trust the front end at all - a huge
        // improvement over the current experience.

        // Check bundler matches dAppOp bundler
        if (dAppOp.bundler != address(0) && msgSender != dAppOp.bundler) {
            if (!signatories[keccak256(abi.encodePacked(dAppOp.control, msgSender))]) {
                bool bypassSignatoryCheck = isSimulation && dAppOp.from == address(0);
                if (!isSimulation) {
                    return (false, ValidCallsResult.InvalidBundler);
                }
            }
        }

        // Make sure the signer is currently enabled by dapp owner
        if (!signatories[keccak256(abi.encodePacked(dAppOp.control, dAppOp.from))]) {
            bool bypassSignatoryCheck = isSimulation && dAppOp.from == address(0);
            if (!bypassSignatoryCheck) {
                return (false, ValidCallsResult.DAppSignatureInvalid);
            }
        }

        if (dAppOp.control != dConfig.to) {
            return (false, ValidCallsResult.InvalidControl);
        }

        // If dAppOp.from is left blank and sim = true,
        // implies a simUserOp call, so dapp nonce check is skipped.
        if (dAppOp.from == address(0) && isSimulation) {
            return (true, ValidCallsResult.Valid);
        }

        // If the dapp indicated that they only accept sequenced nonces
        // (IE for FCFS execution), check and make sure the order is correct
        // NOTE: allowing only sequenced nonces could create a scenario in
        // which builders or validators may be able to profit via censorship.
        // DApps are encouraged to rely on the deadline parameter.
        if (!_handleNonces(dAppOp.from, dAppOp.nonce, !dConfig.callConfig.needsSequencedDAppNonces(), isSimulation)) {
            return (false, ValidCallsResult.InvalidDAppNonce);
        }

        return (true, ValidCallsResult.Valid);
    }

    /// @notice The _handleNonces internal function handles the verification of nonces for both sequenced and async
    /// nonce systems.
    /// @param account The address of the account to verify the nonce for.
    /// @param nonce The nonce to verify.
    /// @param async A boolean indicating if the nonce is async (true) or sequential (false).
    /// @param isSimulation A boolean indicating if the execution is a simulation.
    /// @return A boolean indicating if the nonce is valid.
    function _handleNonces(address account, uint256 nonce, bool async, bool isSimulation) internal returns (bool) {
        if (nonce > type(uint128).max - 1) {
            return false;
        }

        // 0 Nonces are not allowed. Nonces start at 1 for both sequenced and async.
        if (nonce == 0) return false;

        NonceTracker memory nonceTracker = nonceTrackers[account];

        if (!async) {
            // SEQUENTIAL NONCES

            // Nonces must increase by 1 if sequential
            if (nonce != nonceTracker.lastUsedSeqNonce + 1) return false;

            // Return true here if simulation to avoid storing nonce updates
            if (isSimulation) return true;

            ++nonceTracker.lastUsedSeqNonce;
        } else {
            // ASYNC NONCES

            uint256 bitmapIndex = ((nonce - 1) / 240) + 1; // +1 because highestFullBitmap initializes at 0
            uint256 bitmapNonce = ((nonce - 1) % 240); // 1 -> 0, 240 -> 239. Needed for shifts in bitmap.

            bytes32 bitmapKey = keccak256(abi.encode(account, bitmapIndex));
            NonceBitmap memory nonceBitmap = nonceBitmaps[bitmapKey];
            uint256 bitmap = uint256(nonceBitmap.bitmap);

            // Check if nonce has already been used
            if (_nonceUsedInBitmap(bitmap, bitmapNonce)) {
                return false;
            }

            // Return true here if simulation to avoid storing nonce updates
            if (isSimulation) return true;

            // Mark nonce as used in bitmap
            bitmap |= 1 << bitmapNonce;
            nonceBitmap.bitmap = uint240(bitmap);

            // Update highestUsedNonce if necessary.
            // Add 1 back to bitmapNonce: 1 -> 1, 240 -> 240. As opposed to the shift form used above.
            if (bitmapNonce + 1 > uint256(nonceBitmap.highestUsedNonce)) {
                nonceBitmap.highestUsedNonce = uint8(bitmapNonce + 1);
            }

            // Mark bitmap as full if necessary
            if (bitmap == FULL_BITMAP) {
                // Update highestFullAsyncBitmap if necessary
                if (bitmapIndex == nonceTracker.highestFullAsyncBitmap + 1) {
                    nonceTracker = _incrementHighestFullAsyncBitmap(nonceTracker, account);
                }
            }

            nonceBitmaps[bitmapKey] = nonceBitmap;
        }

        nonceTrackers[account] = nonceTracker;
        return true;
    }

    /// @notice Increments the `highestFullAsyncBitmap` of a given `nonceTracker` for the specified `account` until a
    /// non-fully utilized bitmap is found.
    /// @param nonceTracker The `NonceTracker` memory structure representing the current state of nonce tracking for a
    /// specific account.
    /// @param account The address of the account for which the nonce tracking is being updated. This is used to
    /// generate a unique key for accessing the correct bitmap from a mapping.
    /// @return nonceTracker The updated `NonceTracker` structure with the `highestFullAsyncBitmap` field modified to
    /// reflect the highest index of a bitmap that is not fully utilized.
    function _incrementHighestFullAsyncBitmap(
        NonceTracker memory nonceTracker,
        address account
    )
        internal
        view
        returns (NonceTracker memory)
    {
        uint256 bitmap;
        do {
            unchecked {
                ++nonceTracker.highestFullAsyncBitmap;
            }
            uint256 bitmapIndex = uint256(nonceTracker.highestFullAsyncBitmap) + 1;
            bytes32 bitmapKey = keccak256(abi.encode(account, bitmapIndex));
            bitmap = uint256(nonceBitmaps[bitmapKey].bitmap);
        } while (bitmap == FULL_BITMAP);

        return nonceTracker;
    }

    /// @notice Generates the hash of a DAppOperation struct.
    /// @param approval The DAppOperation struct to hash.
    /// @return proofHash The hash of the DAppOperation struct.
    function _getProofHash(DAppOperation memory approval) internal pure returns (bytes32 proofHash) {
        proofHash = keccak256(
            abi.encode(
                DAPP_TYPE_HASH,
                approval.from,
                approval.to,
                approval.value,
                approval.gas,
                approval.nonce,
                approval.deadline,
                approval.control,
                approval.bundler,
                approval.userOpHash,
                approval.callChainHash
            )
        );
    }

    /// @notice Verifies the signature of a DAppOperation struct.
    /// @param dAppOp The DAppOperation struct to verify.
    /// @return A boolean indicating if the signature is valid.
    function _verifyDAppSignature(DAppOperation calldata dAppOp) internal view returns (bool) {
        if (dAppOp.signature.length == 0) return false;
        address signer = _hashTypedDataV4(_getProofHash(dAppOp)).recover(dAppOp.signature);

        return signer == dAppOp.from;
    }

    /// @notice Generates the hash of a DAppOperation struct.
    /// @param dAppOp The DAppOperation struct to hash.
    /// @return payload The hash of the DAppOperation struct.
    function getDAppOperationPayload(DAppOperation memory dAppOp) public view returns (bytes32 payload) {
        payload = _hashTypedDataV4(_getProofHash(dAppOp));
    }

    /// @notice Returns the domain separator for the EIP712 signature scheme.
    /// @return domainSeparator The domain separator for the EIP712 signature scheme.
    function getDomainSeparator() external view returns (bytes32 domainSeparator) {
        domainSeparator = _domainSeparatorV4();
    }

    //
    // USER VERIFICATION
    //

    /// @notice Verifies the validity of a UserOperation struct.
    /// @param dConfig Configuration data for the DApp involved, containing execution parameters and settings.
    /// @param userOp The UserOperation struct to verify.
    /// @param msgSender The forwarded msg.sender of the original metacall transaction in the Atlas contract.
    /// @param isSimulation A boolean indicating if the call is a simulation.
    /// @return A boolean indicating if the UserOperation is valid.
    function _verifyUser(
        DAppConfig memory dConfig,
        UserOperation calldata userOp,
        address msgSender,
        bool isSimulation
    )
        internal
        returns (bool)
    {
        // Verify the signature before storing any data to avoid
        // spoof transactions clogging up dapp userNonces

        if (userOp.from.code.length > 0) {
            // TODO: not sure if 30k gas limit is accurate
            if (userOp.from == address(this) || userOp.from == ATLAS || userOp.from == userOp.control) {
                return false;
            }
            bool validSmartWallet =
                IAccount(userOp.from).validateUserOp{ gas: 30_000 }(userOp, _getProofHash(userOp), 0) == 0;
            return (isSimulation || validSmartWallet);
        }

        bool bypassSignature = msgSender == userOp.from || (isSimulation && userOp.signature.length == 0);

        if (!bypassSignature && !_verifyUserSignature(userOp)) {
            return false;
        }

        if (userOp.control != dConfig.to) {
            return false;
        }

        // If the dapp indicated that they only accept sequenced userNonces
        // (IE for FCFS execution), check and make sure the order is correct
        // NOTE: allowing only sequenced userNonces could create a scenario in
        // which builders or validators may be able to profit via censorship.
        // DApps are encouraged to rely on the deadline parameter
        // to prevent replay attacks.
        if (!_handleNonces(userOp.from, userOp.nonce, !dConfig.callConfig.needsSequencedUserNonces(), isSimulation)) {
            return false;
        }

        return true;
    }

    /// @notice Generates the hash of a UserOperation struct.
    /// @param userOp The UserOperation struct to hash.
    /// @return proofHash The hash of the UserOperation struct.
    function _getProofHash(UserOperation memory userOp) internal pure returns (bytes32 proofHash) {
        proofHash = keccak256(
            abi.encode(
                USER_TYPE_HASH,
                userOp.from,
                userOp.to,
                userOp.value,
                userOp.gas,
                userOp.maxFeePerGas,
                userOp.nonce,
                userOp.deadline,
                userOp.dapp,
                userOp.control,
                userOp.sessionKey,
                keccak256(userOp.data)
            )
        );
    }

    /// @notice Verifies the signature of a UserOperation struct.
    /// @param userOp The UserOperation struct to verify.
    /// @return A boolean indicating if the signature is valid.
    function _verifyUserSignature(UserOperation calldata userOp) internal view returns (bool) {
        if (userOp.signature.length == 0) return false;
        address signer = _hashTypedDataV4(_getProofHash(userOp)).recover(userOp.signature);

        return signer == userOp.from;
    }

    /// @notice Generates the hash of a UserOperation struct.
    /// @param userOp The UserOperation struct to hash.
    /// @return payload The hash of the UserOperation struct.
    function getUserOperationPayload(UserOperation memory userOp) public view returns (bytes32 payload) {
        payload = _hashTypedDataV4(_getProofHash(userOp));
    }

    /// @notice Returns the next nonce for the given account, in sequential or async mode.
    /// @param account The address of the account for which to retrieve the next nonce.
    /// @param sequenced A boolean indicating if the nonce should be sequential (true) or async (false).
    /// @return The next nonce for the given account.
    function getNextNonce(address account, bool sequenced) external view returns (uint256) {
        NonceTracker memory nonceTracker = nonceTrackers[account];

        if (sequenced) {
            return nonceTracker.lastUsedSeqNonce + 1;
        } else {
            uint256 n;
            uint256 bitmap256;
            do {
                unchecked {
                    ++n;
                }
                // Async bitmaps start at index 1. I.e. accounts start with bitmap 0 = HighestFullAsyncBitmap
                bytes32 bitmapKey = keccak256(abi.encode(account, nonceTracker.highestFullAsyncBitmap + n));
                NonceBitmap memory nonceBitmap = nonceBitmaps[bitmapKey];
                bitmap256 = uint256(nonceBitmap.bitmap);
            } while (bitmap256 == FULL_BITMAP);

            uint256 remainder = _getFirstUnusedNonceInBitmap(bitmap256);
            return ((nonceTracker.highestFullAsyncBitmap + n - 1) * 240) + remainder;
        }
    }

    /// @notice Manually updates the highestFullAsyncBitmap of an account to reflect the real full bitmap.
    /// @dev Only the owner of the account whose nonce tracker is being updated can call this function.
    /// @param account The address of the account for which to update the highestFullAsyncBitmap.
    function manuallyUpdateNonceTracker(address account) external {
        if (msg.sender != account) revert AtlasErrors.OnlyAccount();

        NonceTracker memory nonceTracker = nonceTrackers[account];
        NonceBitmap memory nonceBitmap;

        // Checks the next 10 bitmaps for a higher full bitmap
        uint128 nonceIndexToCheck = nonceTracker.highestFullAsyncBitmap + 10;
        for (; nonceIndexToCheck > nonceTracker.highestFullAsyncBitmap; nonceIndexToCheck--) {
            bytes32 bitmapKey = keccak256(abi.encode(account, nonceIndexToCheck));
            nonceBitmap = nonceBitmaps[bitmapKey];

            if (nonceBitmap.bitmap == FULL_BITMAP) {
                nonceTracker.highestFullAsyncBitmap = nonceIndexToCheck;
                break;
            }
        }

        nonceTrackers[account] = nonceTracker;
    }

    /// @notice Checks if a nonce is used in a 256-bit bitmap.
    /// @dev Only accurate for nonces 1 - 240 within a 256-bit bitmap.
    /// @param bitmap The 256-bit bitmap to check.
    /// @param nonce The nonce to check.
    /// @return A boolean indicating if the nonce is used in the bitmap.
    function _nonceUsedInBitmap(uint256 bitmap, uint256 nonce) internal pure returns (bool) {
        return (bitmap & (1 << nonce)) != 0;
    }

    /// @notice Returns the first unused nonce in a 256-bit bitmap.
    /// @dev Finds the first unused nonce within a given 240-bit bitmap, checking 16 bits and then 4 bits at a time for
    /// efficiency.
    /// @param bitmap A uint256 where the first 240 bits are used to represent the used/unused status of nonces.
    /// @return The 1-indexed position of the first unused nonce within the bitmap, or 0 if all nonces represented by
    /// the bitmap are used.
    function _getFirstUnusedNonceInBitmap(uint256 bitmap) internal pure returns (uint256) {
        // Check the 240-bit bitmap, 16 bits at a time, if a 16 bit chunk is not full.
        // Then check the located 16-bit chunk, 4 bits at a time, for an unused 4-bit chunk.
        // Then loop normally from the start of the 4-bit chunk to find the first unused bit.

        for (uint256 i = 0; i < 240; i += 16) {
            // Isolate the next 16 bits to check
            uint256 chunk16 = (bitmap >> i) & FIRST_16_BITS_FULL;
            // Find non-full 16-bit chunk
            if (chunk16 != FIRST_16_BITS_FULL) {
                for (uint256 j = 0; j < 16; j += 4) {
                    // Isolate the next 4 bits within the 16-bit chunk to check
                    uint256 chunk4 = (chunk16 >> j) & FIRST_4_BITS_FULL;
                    // Find non-full 4-bit chunk
                    if (chunk4 != FIRST_4_BITS_FULL) {
                        for (uint256 k = 0; k < 4; k++) {
                            // Find first unused bit
                            if ((chunk4 >> k) & 0x1 == 0) {
                                // Returns 1-indexed nonce
                                return i + j + k + 1;
                            }
                        }
                    }
                }
            }
        }

        return 0;
    }
}

// FROM ETH-INFINITISM REPO:
// https://github.com/eth-infinitism/account-abstraction/blob/develop/contracts/interfaces/IAccount.sol

interface IAccount {
    /**
     * Validate user's signature and nonce
     * the entryPoint will make the call to the recipient only if this validation call returns successfully.
     * signature failure should be reported by returning SIG_VALIDATION_FAILED (1).
     * This allows making a "simulation call" without a valid signature
     * Other failures (e.g. nonce mismatch, or invalid signature format) should still revert to signal failure.
     *
     * @dev Must validate caller is the entryPoint.
     *      Must validate the signature and nonce
     * @param userOp              - The operation that is about to be executed.
     * @param userOpHash          - Hash of the user's request data. can be used as the basis for signature.
     * @param missingAccountFunds - Missing funds on the account's deposit in the entrypoint.
     *                              This is the minimum amount to transfer to the sender(entryPoint) to be
     *                              able to make the call. The excess is left as a deposit in the entrypoint
     *                              for future calls. Can be withdrawn anytime using "entryPoint.withdrawTo()".
     *                              In case there is a paymaster in the request (or the current deposit is high
     *                              enough), this value will be zero.
     * @return validationData       - Packaged ValidationData structure. use `_packValidationData` and
     *                              `_unpackValidationData` to encode and decode.
     *                              <20-byte> sigAuthorizer - 0 for valid signature, 1 to mark signature failure,
     *                                 otherwise, an address of an "authorizer" contract.
     *                              <6-byte> validUntil - Last timestamp this operation is valid. 0 for "indefinite"
     *                              <6-byte> validAfter - First timestamp this operation is valid
     *                                                    If an account doesn't use time-range, it is enough to
     *                                                    return SIG_VALIDATION_FAILED value (1) for signature failure.
     *                              Note that the validation code cannot use block.timestamp (or block.number) directly.
     */
    function validateUserOp(
        UserOperation calldata userOp,
        bytes32 userOpHash,
        uint256 missingAccountFunds
    )
        external
        returns (uint256 validationData);
}
