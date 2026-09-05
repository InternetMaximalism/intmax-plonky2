// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleVerifierConfiguration} from "./MleProofErrors.sol";
import {
    CANONICAL_WHIR_PROFILE_TABLE_V2,
    CANONICAL_WHIR_SESSION_ID_V2,
    MAX_WHIR_PROFILE_VARIABLES_V2,
    MIN_WHIR_PROFILE_VARIABLES_V2,
    WHIR_PROFILE_ENTRY_BYTES_V2
} from "./generated/WhirProfilesV2.sol";

/// @title CanonicalWhirProfileV2
/// @notice Deployment-time allowlist for the Rust `WhirPCS::for_constituents` profiles.
/// @dev Kept as an externally linked library so the 21-profile table is not
/// copied into `MleVerifierV2` runtime bytecode. Each table row contains the
/// exact `keccak256(abi.encode(WhirParams))` digest followed by both halves of
/// the native WHIR protocol ID.
library CanonicalWhirProfileV2 {
    function validateCanonical(
        uint256 numVariables,
        bytes32 parametersDigest,
        bytes32[2] memory protocolId,
        bytes32 sessionId
    ) external pure {
        if (
            numVariables < MIN_WHIR_PROFILE_VARIABLES_V2 || numVariables > MAX_WHIR_PROFILE_VARIABLES_V2
                || sessionId != CANONICAL_WHIR_SESSION_ID_V2
        ) revert InvalidMleVerifierConfiguration();

        bytes memory table = CANONICAL_WHIR_PROFILE_TABLE_V2;
        uint256 offset = (numVariables - MIN_WHIR_PROFILE_VARIABLES_V2) * WHIR_PROFILE_ENTRY_BYTES_V2;
        bytes32 expectedDigest;
        bytes32 expectedProtocolIdFirst;
        bytes32 expectedProtocolIdSecond;
        assembly ("memory-safe") {
            let entry := add(add(table, 0x20), offset)
            expectedDigest := mload(entry)
            expectedProtocolIdFirst := mload(add(entry, 0x20))
            expectedProtocolIdSecond := mload(add(entry, 0x40))
        }
        if (
            parametersDigest != expectedDigest || protocolId[0] != expectedProtocolIdFirst
                || protocolId[1] != expectedProtocolIdSecond
        ) revert InvalidMleVerifierConfiguration();
    }
}
