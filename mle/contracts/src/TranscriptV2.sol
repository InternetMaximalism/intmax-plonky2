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
    TAG_FIELD_V2
} from "./generated/MleWhirV2.sol";

/// @title TranscriptV2
/// @notice Constant-state Keccak Fiat--Shamir transcript for MLE/WHIR v2.
/// @dev This is byte-for-byte compatible with `mle/src/transcript_v2.rs`.
///      Every absorbed message is committed as
///      `FRAME_PREFIX || old_digest || tag || payload_len_u64_le || payload`.
///      A challenge hashes
///      `CHALLENGE_PREFIX || digest || squeeze_counter_u64_le` and reduces the
///      256-bit little-endian digest modulo the Goldilocks prime.
///
///      Every frame is assembled in temporary memory at the free-memory pointer
///      (never allocated, never read after the keccak) and every challenge in
///      the 64-byte scratch space, so a complete verification allocates no
///      transcript buffers at all.
library TranscriptV2 {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;

    /// @dev `TRANSCRIPT_FRAME_PREFIX_V2` ("plonky2-mle-v3-frame", 20 bytes) as a
    /// left-aligned word, and `TRANSCRIPT_CHALLENGE_PREFIX_V2`
    /// ("plonky2-mle-v3-challenge", 24 bytes). `TranscriptV2.t.sol` pins both
    /// against the generated string constants; the frame header below is
    /// `prefix(20) || state(32) || tag(1) || len_le(8)` = 61 bytes.
    uint256 internal constant FRAME_PREFIX_WORD = 0x706c6f6e6b79322d6d6c652d76332d6672616d65000000000000000000000000;
    uint256 internal constant FRAME_PREFIX_LENGTH = 20;
    uint256 internal constant FRAME_HEADER_LENGTH = 61;
    uint256 internal constant CHALLENGE_PREFIX_WORD = 0x706c6f6e6b79322d6d6c652d76332d6368616c6c656e67650000000000000000;
    uint256 internal constant CHALLENGE_PREFIX_LENGTH = 24;

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
        _absorbMemoryBytes(transcript, TAG_DOMAIN_V2, bytes(label));
    }

    function absorbBytes(Transcript memory transcript, bytes memory value) internal pure {
        _absorbMemoryBytes(transcript, TAG_BYTES_V2, value);
    }

    function absorbField(Transcript memory transcript, uint256 value) internal pure {
        if (value >= P) revert InvalidMleProof();
        _absorbScalarLimbs(transcript, TAG_FIELD_V2, value, 0, 0, 8);
    }

    function absorbFieldVec(Transcript memory transcript, uint256[] memory values) internal pure {
        uint256 count = values.length;
        if (count > type(uint64).max) revert InvalidMleProof();
        for (uint256 i = 0; i < count; ++i) {
            if (values[i] >= P) revert InvalidMleProof();
        }
        _absorbVecMemory(transcript, TAG_FIELD_VEC_V2, count, 8, 0, values);
    }

    /// @dev Internal-only fast path after the atomic proof preflight has
    /// checked every supplied base-field element for canonical encoding.
    function absorbFieldVecPrevalidated(Transcript memory transcript, uint256[] memory values) internal pure {
        _absorbVecMemory(transcript, TAG_FIELD_VEC_V2, values.length, 8, 0, values);
    }

    function absorbExt3(Transcript memory transcript, GoldilocksExt3.Ext3 memory value) internal pure {
        _checkCanonical(value);
        _absorbScalarLimbs(transcript, TAG_EXT3_V2, value.c0, value.c1, value.c2, 24);
    }

    function absorbExt3Vec(Transcript memory transcript, GoldilocksExt3.Ext3[] memory values) internal pure {
        uint256 count = values.length;
        if (count > type(uint64).max) revert InvalidMleProof();
        for (uint256 i = 0; i < count; ++i) {
            _checkCanonical(values[i]);
        }
        _absorbVecMemory(transcript, TAG_EXT3_VEC_V2, count, 24, 1, _asWords(values));
    }

    /// @dev Internal-only fast path after the atomic proof preflight has
    /// checked every Ext3 limb. The exact typed frame is unchanged.
    function absorbExt3VecPrevalidated(Transcript memory transcript, GoldilocksExt3.Ext3[] memory values)
        internal
        pure
    {
        _absorbVecMemory(transcript, TAG_EXT3_VEC_V2, values.length, 24, 1, _asWords(values));
    }

    /// @notice Absorb an Ext3 vector held as a flat limb buffer (three canonical
    /// words per element, `c0, c1, c2`), producing exactly the frame of
    /// `absorbExt3Vec` over the same elements.
    /// @dev Internal-only: the caller has already checked every limb.
    function absorbExt3VecFlatPrevalidated(Transcript memory transcript, uint256[] memory flatLimbs) internal pure {
        if (flatLimbs.length % 3 != 0) revert InvalidMleProof();
        _absorbVecMemory(transcript, TAG_EXT3_VEC_V2, flatLimbs.length / 3, 24, 2, flatLimbs);
    }

    /// @notice Absorb `count` Ext3 elements that already sit in calldata in the
    /// wire encoding (24 little-endian bytes per element), producing exactly the
    /// frame of `absorbExt3Vec` over the decoded elements.
    /// @dev Internal-only: the caller has already decoded and checked every limb
    /// of the same calldata range, and guarantees `[offset, offset + 24 * count)`
    /// lies inside the authenticated proof bytes.
    function absorbExt3VecCalldataPrevalidated(Transcript memory transcript, uint256 calldataOffset, uint256 count)
        internal
        pure
    {
        if (count > type(uint64).max) revert InvalidMleProof();
        assembly ("memory-safe") {
            let payloadLength := add(8, mul(count, 24))
            let frame := mload(0x40)
            let payload := add(frame, FRAME_HEADER_LENGTH)
            // header: prefix || state || tag || len_le
            mstore(frame, FRAME_PREFIX_WORD)
            mstore(add(frame, FRAME_PREFIX_LENGTH), mload(transcript))
            mstore8(add(frame, 52), TAG_EXT3_VEC_V2)
            mstore(add(frame, 53), shl(192, bswap64(payloadLength)))
            // payload: count_le || raw little-endian records straight from calldata
            mstore(payload, shl(192, bswap64(count)))
            calldatacopy(add(payload, 8), calldataOffset, mul(count, 24))
            mstore(transcript, keccak256(frame, add(FRAME_HEADER_LENGTH, payloadLength)))
            mstore(add(transcript, 0x20), 0)

            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
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
        assembly ("memory-safe") {
            challenge := squeeze(transcript)

            // keccak(CHALLENGE_PREFIX(24) || state(32) || counter_le(8)) in the scratch space,
            // then the 256-bit little-endian digest reduced modulo p with 2^64 = 2^32 - 1.
            function squeeze(t) -> value {
                let state := mload(t)
                let counter := mload(add(t, 0x20))
                mstore(0x00, or(CHALLENGE_PREFIX_WORD, shr(192, state)))
                mstore(0x20, or(shl(64, state), bswap64(counter)))
                let digest := keccak256(0x00, 0x40)
                mstore(add(t, 0x20), add(counter, 1))
                let p := 0xFFFFFFFF00000001
                // Byte-reverse every 8-byte lane at once: the four little-endian
                // digest limbs become big-endian lanes of `w`.
                let w := digest
                w := or(shl(8, and(w, 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF)), and(shr(8, w), 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF))
                w := or(shl(16, and(w, 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF)), and(shr(16, w), 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF))
                w := or(shl(32, and(w, 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF)), and(shr(32, w), 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF))
                let radix := 0xFFFFFFFF
                value := addmod(mulmod(and(w, 0xFFFFFFFFFFFFFFFF), radix, p), and(shr(64, w), 0xFFFFFFFFFFFFFFFF), p)
                value := addmod(mulmod(value, radix, p), and(shr(128, w), 0xFFFFFFFFFFFFFFFF), p)
                value := addmod(mulmod(value, radix, p), shr(192, w), p)
            }
            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
    }

    /// @notice Squeeze one Ext3 challenge as three consecutive base squeezes.
    function squeezeExt3(Transcript memory transcript) internal pure returns (GoldilocksExt3.Ext3 memory value) {
        squeezeExt3Into(transcript, value);
    }

    /// @notice Squeeze one Ext3 challenge into caller-owned memory (three words).
    /// @dev Three consecutive base squeezes (counters `c`, `c + 1`, `c + 2`), each
    /// `keccak(CHALLENGE_PREFIX || state || counter_le)` reduced as in `squeezeChallenge`;
    /// the state is loaded once and the three hashes share the scratch-space preimage.
    function squeezeExt3Into(Transcript memory transcript, GoldilocksExt3.Ext3 memory destination) internal pure {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let state := mload(transcript)
            let counter := mload(add(transcript, 0x20))
            mstore(0x00, or(CHALLENGE_PREFIX_WORD, shr(192, state)))
            let high := shl(64, state)
            for { let k := 0 } lt(k, 3) { k := add(k, 1) } {
                let c := counter
                c := or(shl(32, and(c, 0xFFFFFFFF)), shr(32, and(c, 0xFFFFFFFF00000000)))
                c := or(shl(16, and(c, 0x0000FFFF0000FFFF)), shr(16, and(c, 0xFFFF0000FFFF0000)))
                c := or(shl(8, and(c, 0x00FF00FF00FF00FF)), shr(8, and(c, 0xFF00FF00FF00FF00)))
                mstore(0x20, or(high, c))
                let w := keccak256(0x00, 0x40)
                counter := add(counter, 1)
                // Byte-reverse every 8-byte lane at once: the four little-endian digest
                // limbs become big-endian lanes of `w`.
                w := or(shl(8, and(w, 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF)), and(shr(8, w), 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF))
                w := or(shl(16, and(w, 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF)), and(shr(16, w), 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF))
                w := or(shl(32, and(w, 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF)), and(shr(32, w), 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF))
                let value := addmod(mulmod(and(w, 0xFFFFFFFFFFFFFFFF), 0xFFFFFFFF, p), and(shr(64, w), 0xFFFFFFFFFFFFFFFF), p)
                value := addmod(mulmod(value, 0xFFFFFFFF, p), and(shr(128, w), 0xFFFFFFFFFFFFFFFF), p)
                mstore(add(destination, shl(5, k)), addmod(mulmod(value, 0xFFFFFFFF, p), shr(192, w), p))
            }
            mstore(add(transcript, 0x20), counter)
        }
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
        _absorbScalarLimbs(transcript, TAG_BYTES_V2, roundIndex, 0, 0, 8);
        absorbExt3Vec(transcript, logNonConstant);
        absorbExt3Vec(transcript, gateNonConstant);
        domainSeparate(transcript, DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2);
        squeezeExt3Into(transcript, challenges.log);
        squeezeExt3Into(transcript, challenges.gate);
    }

    /// @dev Commit `FRAME_PREFIX || state || tag || len_le || payload` where the
    /// payload is an in-memory byte string.
    function _absorbMemoryBytes(Transcript memory transcript, uint8 tag, bytes memory payload) private pure {
        uint256 payloadLength = payload.length;
        if (payloadLength > type(uint64).max) revert InvalidMleProof();
        assembly ("memory-safe") {
            let frame := mload(0x40)
            mstore(frame, FRAME_PREFIX_WORD)
            mstore(add(frame, FRAME_PREFIX_LENGTH), mload(transcript))
            mstore8(add(frame, 52), tag)
            mstore(add(frame, 53), shl(192, bswap64(payloadLength)))
            let dst := add(frame, FRAME_HEADER_LENGTH)
            let src := add(payload, 0x20)
            for { let off := 0 } lt(off, payloadLength) { off := add(off, 0x20) } {
                mstore(add(dst, off), mload(add(src, off)))
            }
            mstore(transcript, keccak256(frame, add(FRAME_HEADER_LENGTH, payloadLength)))
            mstore(add(transcript, 0x20), 0)

            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
    }

    /// @dev Commit a frame whose payload is one, or three, little-endian u64 limbs
    /// (`payloadLength` 8 or 24). Used for `TAG_FIELD`, `TAG_EXT3` and the
    /// round-index `TAG_BYTES` message of the coupled outer round.
    function _absorbScalarLimbs(
        Transcript memory transcript,
        uint8 tag,
        uint256 limb0,
        uint256 limb1,
        uint256 limb2,
        uint256 payloadLength
    ) private pure {
        assembly ("memory-safe") {
            let frame := mload(0x40)
            mstore(frame, FRAME_PREFIX_WORD)
            mstore(add(frame, FRAME_PREFIX_LENGTH), mload(transcript))
            mstore8(add(frame, 52), tag)
            mstore(add(frame, 53), shl(192, bswap64(payloadLength)))
            let payload := add(frame, FRAME_HEADER_LENGTH)
            mstore(
                payload,
                or(or(shl(192, bswap64(limb0)), shl(128, bswap64(limb1))), shl(64, bswap64(limb2)))
            )
            mstore(transcript, keccak256(frame, add(FRAME_HEADER_LENGTH, payloadLength)))
            mstore(add(transcript, 0x20), 0)

            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
    }

    /// @dev Commit a vector frame `count_le || elements` where every element is
    /// `elementBytes` little-endian bytes (8 for base-field words, 24 for Ext3)
    /// read from memory in one of three layouts:
    ///   mode 0: `uint256[]` of base-field words (8 bytes each);
    ///   mode 1: `Ext3[]` pointer table, each record three words (24 bytes each);
    ///   mode 2: flat `uint256[]` of limbs, three words per element (24 bytes each).
    /// Little-endian writes spill zero bytes past the element; the next element
    /// overwrites them and the final spill lands in unhashed temporary memory.
    function _absorbVecMemory(
        Transcript memory transcript,
        uint8 tag,
        uint256 count,
        uint256 elementBytes,
        uint256 mode,
        uint256[] memory source
    ) private pure {
        assembly ("memory-safe") {
            let payloadLength := add(8, mul(count, elementBytes))
            let frame := mload(0x40)
            mstore(frame, FRAME_PREFIX_WORD)
            mstore(add(frame, FRAME_PREFIX_LENGTH), mload(transcript))
            mstore8(add(frame, 52), tag)
            mstore(add(frame, 53), shl(192, bswap64(payloadLength)))
            let payload := add(frame, FRAME_HEADER_LENGTH)
            mstore(payload, shl(192, bswap64(count)))
            let dst := add(payload, 8)
            let src := add(source, 0x20)
            switch mode
            case 0 {
                for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                    mstore(dst, shl(192, bswap64(mload(add(src, shl(5, i))))))
                    dst := add(dst, 8)
                }
            }
            case 1 {
                for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                    let record := mload(add(src, shl(5, i)))
                    mstore(
                        dst,
                        or(
                            or(shl(192, bswap64(mload(record))), shl(128, bswap64(mload(add(record, 0x20))))),
                            shl(64, bswap64(mload(add(record, 0x40))))
                        )
                    )
                    dst := add(dst, 24)
                }
            }
            default {
                for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                    let record := add(src, mul(i, 0x60))
                    mstore(
                        dst,
                        or(
                            or(shl(192, bswap64(mload(record))), shl(128, bswap64(mload(add(record, 0x20))))),
                            shl(64, bswap64(mload(add(record, 0x40))))
                        )
                    )
                    dst := add(dst, 24)
                }
            }
            mstore(transcript, keccak256(frame, add(FRAME_HEADER_LENGTH, payloadLength)))
            mstore(add(transcript, 0x20), 0)

            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
    }

    /// @dev Reinterpret an `Ext3[]` (length word followed by record pointers) as
    /// the word array its pointer table is; only `_absorbVecMemory` mode 1 reads it.
    function _asWords(GoldilocksExt3.Ext3[] memory values) private pure returns (uint256[] memory words) {
        assembly ("memory-safe") {
            words := values
        }
    }

    function _checkCanonical(GoldilocksExt3.Ext3 memory value) private pure {
        if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
            revert InvalidMleProof();
        }
    }
}
