// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof} from "./MleProofErrors.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {
    BASE_FIELD_MODULUS_V2,
    DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2,
    DOMAIN_OUTER_SUMCHECK_ROUND_V2,
    DOMAIN_WHIR_PROTOCOL_ID_V2,
    DOMAIN_WHIR_SESSION_ID_V2,
    OUTER_TRANSCRIPT_PROTOCOL_V2,
    TAG_BYTES_V2,
    TAG_DOMAIN_V2,
    TAG_EXT3_VEC_V2,
    TAG_EXT3_V2,
    TAG_FIELD_VEC_V2,
    TAG_FIELD_V2,
    TRANSCRIPT_CHALLENGE_PREFIX_V2,
    TRANSCRIPT_FRAME_PREFIX_V2
} from "./generated/MleWhirV2.sol";

/// @title TranscriptV2
/// @notice Constant-state Keccak Fiat--Shamir transcript for MLE/WHIR v2.
/// @dev This is byte-for-byte compatible with `mle/src/transcript_v2.rs`.
///      Every absorbed message is committed as
///      `FRAME_PREFIX || old_digest || tag || payload_len_u64_le || payload`.
///      A challenge hashes
///      `CHALLENGE_PREFIX || digest || squeeze_counter_u64_le` and reduces the
///      256-bit little-endian digest modulo the Goldilocks prime.
library TranscriptV2 {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;

    struct Transcript {
        bytes32 state;
        uint64 squeezeCounter;
    }

    struct CoupledOuterRoundChallenges {
        GoldilocksExt3.Ext3 log;
        GoldilocksExt3.Ext3 gate;
    }

    /// @notice Initialize a transcript with the mandatory v2 protocol domain.
    function init(Transcript memory transcript) internal pure {
        transcript.state = bytes32(0);
        transcript.squeezeCounter = 0;
        domainSeparate(transcript, OUTER_TRANSCRIPT_PROTOCOL_V2);
    }

    /// @notice Return an initialized transcript value.
    function create() internal pure returns (Transcript memory transcript) {
        init(transcript);
    }

    function domainSeparate(Transcript memory transcript, string memory label) internal pure {
        _absorbFrame(transcript, TAG_DOMAIN_V2, bytes(label));
    }

    function absorbBytes(Transcript memory transcript, bytes memory value) internal pure {
        _absorbFrame(transcript, TAG_BYTES_V2, value);
    }

    function absorbField(Transcript memory transcript, uint256 value) internal pure {
        if (value >= P) revert InvalidMleProof();
        bytes memory payload = new bytes(8);
        _writeU64Le(payload, 0, uint64(value));
        _absorbFrame(transcript, TAG_FIELD_V2, payload);
    }

    function absorbFieldVec(Transcript memory transcript, uint256[] memory values) internal pure {
        uint256 count = values.length;
        if (count > type(uint64).max) revert InvalidMleProof();
        for (uint256 i = 0; i < count; ++i) {
            if (values[i] >= P) revert InvalidMleProof();
        }

        _absorbFieldVecUnchecked(transcript, values);
    }

    /// @dev Internal-only fast path after the atomic proof preflight has
    /// checked every supplied base-field element for canonical encoding.
    function absorbFieldVecPrevalidated(Transcript memory transcript, uint256[] memory values) internal pure {
        _absorbFieldVecUnchecked(transcript, values);
    }

    function _absorbFieldVecUnchecked(Transcript memory transcript, uint256[] memory values) private pure {
        uint256 count = values.length;
        bytes memory payload = new bytes(8 + 8 * count);
        _writeU64Le(payload, 0, uint64(count));
        for (uint256 i = 0; i < count; ++i) {
            _writeU64Le(payload, 8 + 8 * i, uint64(values[i]));
        }
        _absorbFrame(transcript, TAG_FIELD_VEC_V2, payload);
    }

    function absorbExt3(Transcript memory transcript, GoldilocksExt3.Ext3 memory value) internal pure {
        _checkCanonical(value);
        bytes memory payload = new bytes(24);
        _writeExt3(payload, 0, value);
        _absorbFrame(transcript, TAG_EXT3_V2, payload);
    }

    function absorbExt3Vec(Transcript memory transcript, GoldilocksExt3.Ext3[] memory values) internal pure {
        uint256 count = values.length;
        if (count > type(uint64).max) revert InvalidMleProof();
        for (uint256 i = 0; i < count; ++i) {
            _checkCanonical(values[i]);
        }

        _absorbExt3VecUnchecked(transcript, values);
    }

    /// @dev Internal-only fast path after the atomic proof preflight has
    /// checked every Ext3 limb. The exact typed frame is unchanged.
    function absorbExt3VecPrevalidated(
        Transcript memory transcript,
        GoldilocksExt3.Ext3[] memory values
    ) internal pure {
        _absorbExt3VecUnchecked(transcript, values);
    }

    function _absorbExt3VecUnchecked(
        Transcript memory transcript,
        GoldilocksExt3.Ext3[] memory values
    ) private pure {
        uint256 count = values.length;
        bytes memory payload = new bytes(8 + 24 * count);
        _writeU64Le(payload, 0, uint64(count));
        for (uint256 i = 0; i < count; ++i) {
            _writeExt3(payload, 8 + 24 * i, values[i]);
        }
        _absorbFrame(transcript, TAG_EXT3_VEC_V2, payload);
    }

    /// @notice Bind canonical-config-derived WHIR identifiers before PCS roots.
    /// @dev The caller must re-derive both values from the canonical WHIR config
    ///      and compare them with its VK before calling this helper. Rust absorbs
    ///      the 64-byte protocol ID and 32-byte session ID in this exact order.
    function bindWhirIdentifiers(Transcript memory transcript, bytes memory protocolId, bytes memory sessionId)
        internal
        pure
    {
        if (protocolId.length != 64 || sessionId.length != 32) revert InvalidMleProof();
        domainSeparate(transcript, DOMAIN_WHIR_PROTOCOL_ID_V2);
        absorbBytes(transcript, protocolId);
        domainSeparate(transcript, DOMAIN_WHIR_SESSION_ID_V2);
        absorbBytes(transcript, sessionId);
    }

    /// @notice Squeeze one canonical Goldilocks base-field challenge.
    function squeezeChallenge(Transcript memory transcript) internal pure returns (uint256 challenge) {
        bytes32 digest = keccak256(
            abi.encodePacked(TRANSCRIPT_CHALLENGE_PREFIX_V2, transcript.state, _u64Le(transcript.squeezeCounter))
        );
        ++transcript.squeezeCounter;
        uint256 hashValue = uint256(digest);
        uint256 limb0 = _swap64(uint64(hashValue >> 192));
        uint256 limb1 = _swap64(uint64(hashValue >> 128));
        uint256 limb2 = _swap64(uint64(hashValue >> 64));
        uint256 limb3 = _swap64(uint64(hashValue));
        uint256 radix = 0xFFFFFFFF;
        uint256 reduced = addmod(mulmod(limb3, radix, P), limb2, P);
        reduced = addmod(mulmod(reduced, radix, P), limb1, P);
        challenge = addmod(mulmod(reduced, radix, P), limb0, P);
    }

    /// @notice Squeeze one Ext3 challenge as three consecutive base squeezes.
    function squeezeExt3(Transcript memory transcript) internal pure returns (GoldilocksExt3.Ext3 memory value) {
        value.c0 = uint64(squeezeChallenge(transcript));
        value.c1 = uint64(squeezeChallenge(transcript));
        value.c2 = uint64(squeezeChallenge(transcript));
    }

    /// @notice Commit both Ext3 outer-sumcheck messages before sampling either challenge.
    /// @dev Matches Rust `TranscriptV2::commit_coupled_outer_round`. The returned
    ///      tuple consumes counters 0..5: three limbs for log, then three limbs
    ///      for gate. Each sumcheck gets Fp3 entropy; lockstep ordering prevents
    ///      adaptive bridging but is not itself a soundness-amplification claim.
    function commitCoupledOuterRound(
        Transcript memory transcript,
        uint256 roundIndex,
        GoldilocksExt3.Ext3[] memory logNonConstant,
        GoldilocksExt3.Ext3[] memory gateNonConstant
    ) internal pure returns (CoupledOuterRoundChallenges memory challenges) {
        if (roundIndex > type(uint64).max) revert InvalidMleProof();
        domainSeparate(transcript, DOMAIN_OUTER_SUMCHECK_ROUND_V2);
        absorbBytes(transcript, abi.encodePacked(_u64Le(uint64(roundIndex))));
        absorbExt3Vec(transcript, logNonConstant);
        absorbExt3Vec(transcript, gateNonConstant);
        domainSeparate(transcript, DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2);
        challenges.log = squeezeExt3(transcript);
        challenges.gate = squeezeExt3(transcript);
    }

    function _absorbFrame(Transcript memory transcript, uint8 tag, bytes memory payload) private pure {
        if (payload.length > type(uint64).max) revert InvalidMleProof();
        transcript.state = keccak256(
            abi.encodePacked(
                TRANSCRIPT_FRAME_PREFIX_V2, transcript.state, bytes1(tag), _u64Le(uint64(payload.length)), payload
            )
        );
        transcript.squeezeCounter = 0;
    }

    function _writeExt3(bytes memory destination, uint256 offset, GoldilocksExt3.Ext3 memory value) private pure {
        if (offset > destination.length || 24 > destination.length - offset) revert InvalidMleProof();
        assembly ("memory-safe") {
            function writeLe(ptr, x) {
                mstore8(ptr, x)
                mstore8(add(ptr, 1), shr(8, x))
                mstore8(add(ptr, 2), shr(16, x))
                mstore8(add(ptr, 3), shr(24, x))
                mstore8(add(ptr, 4), shr(32, x))
                mstore8(add(ptr, 5), shr(40, x))
                mstore8(add(ptr, 6), shr(48, x))
                mstore8(add(ptr, 7), shr(56, x))
            }
            let ptr := add(add(destination, 0x20), offset)
            writeLe(ptr, mload(value))
            writeLe(add(ptr, 8), mload(add(value, 0x20)))
            writeLe(add(ptr, 16), mload(add(value, 0x40)))
        }
    }

    function _writeU64Le(bytes memory destination, uint256 offset, uint64 value) private pure {
        if (offset > destination.length || 8 > destination.length - offset) revert InvalidMleProof();
        assembly ("memory-safe") {
            let ptr := add(add(destination, 0x20), offset)
            mstore8(ptr, value)
            mstore8(add(ptr, 1), shr(8, value))
            mstore8(add(ptr, 2), shr(16, value))
            mstore8(add(ptr, 3), shr(24, value))
            mstore8(add(ptr, 4), shr(32, value))
            mstore8(add(ptr, 5), shr(40, value))
            mstore8(add(ptr, 6), shr(48, value))
            mstore8(add(ptr, 7), shr(56, value))
        }
    }

    function _u64Le(uint64 value) private pure returns (bytes8 encoded) {
        uint64 swapped = ((value & 0x00000000FFFFFFFF) << 32) | ((value & 0xFFFFFFFF00000000) >> 32);
        swapped = ((swapped & 0x0000FFFF0000FFFF) << 16) | ((swapped & 0xFFFF0000FFFF0000) >> 16);
        swapped = ((swapped & 0x00FF00FF00FF00FF) << 8) | ((swapped & 0xFF00FF00FF00FF00) >> 8);
        encoded = bytes8(swapped);
    }

    function _swap64(uint64 value) private pure returns (uint64) {
        value = ((value & 0x00000000FFFFFFFF) << 32) | ((value & 0xFFFFFFFF00000000) >> 32);
        value = ((value & 0x0000FFFF0000FFFF) << 16) | ((value & 0xFFFF0000FFFF0000) >> 16);
        return ((value & 0x00FF00FF00FF00FF) << 8) | ((value & 0xFF00FF00FF00FF00) >> 8);
    }

    function _checkCanonical(GoldilocksExt3.Ext3 memory value) private pure {
        if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
            revert InvalidMleProof();
        }
    }
}
