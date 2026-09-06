// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {CircuitConfigV2} from "./CircuitConfigV2.sol";
import {InvalidMleProof} from "./MleProofErrors.sol";
import {MleVerifierV2} from "./MleVerifierV2.sol";
import {OuterLogupExt3Verifier} from "./OuterLogupExt3Verifier.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {
    BASE_FIELD_MODULUS_V2,
    CIRCUIT_DIGEST_LENGTH_V2,
    COMPACT_MAGIC_V2,
    LOG_ROUND_DEGREE_V2,
    MAX_COMPACT_PROOF_BYTES_V2,
    MAX_WHIR_HINT_BYTES_V2,
    MAX_WHIR_NARG_BYTES_V2,
    MLE_PROTOCOL_VERSION_CURRENT
} from "./generated/MleWhirV2.sol";

/// @title CompactMleProofV2
/// @notice Strict decoder for the schema-generated `MLEWHIR3` DA encoding.
/// @dev Every vector length is derived from the constructor-pinned circuit;
/// only the two opaque WHIR streams carry a length prefix. All integers are
/// little-endian. The standalone decoder checks every Goldilocks limb; the
/// production core-bound decoder defers only that duplicate comparison to the
/// core's fused canonical-copy boundary. There are no aliases, ignored tails,
/// optional fields, or padding.
library CompactMleProofV2 {
    struct Cursor {
        uint256 offset;
    }

    /// @notice Decode one canonical compact proof using trusted circuit dimensions.
    /// @dev Any malformed or non-canonical authenticated byte stream is an invalid
    /// proof. Configuration validity remains the responsibility of the pinned core.
    function decode(bytes calldata encoded, CircuitConfigV2.Parameters memory circuit)
        internal
        pure
        returns (MleVerifierV2.MleProof memory proof)
    {
        return _decode(encoded, circuit, true);
    }

    /// @notice Decode for an immediate call to `MleVerifierV2.verify`.
    /// @dev The core verifier validates every decoded field limb before its
    /// first use.  Its canonical copy therefore makes repeating the same limb
    /// comparisons in this adapter frame unnecessary.  All compact framing,
    /// magic/version, trusted lengths, stream caps and exact-consumption checks
    /// remain enforced here.  This entry MUST NOT be used by a path which can
    /// consume or return the decoded proof without first invoking the core.
    function decodeForCoreVerification(bytes calldata encoded, CircuitConfigV2.Parameters memory circuit)
        internal
        pure
        returns (MleVerifierV2.MleProof memory proof)
    {
        return _decode(encoded, circuit, false);
    }

    function _decode(bytes calldata encoded, CircuitConfigV2.Parameters memory circuit, bool requireCanonicalLimbs)
        private
        pure
        returns (MleVerifierV2.MleProof memory proof)
    {
        if (encoded.length > MAX_COMPACT_PROOF_BYTES_V2 || encoded.length < 8) revert InvalidMleProof();

        bytes8 magic;
        assembly ("memory-safe") {
            magic := calldataload(encoded.offset)
        }
        if (magic != COMPACT_MAGIC_V2) revert InvalidMleProof();

        Cursor memory cursor = Cursor({offset: 8});
        proof.protocolVersion = _readU64(encoded, cursor, false);
        if (proof.protocolVersion != MLE_PROTOCOL_VERSION_CURRENT) revert InvalidMleProof();

        proof.constituentWidth = _readU32(encoded, cursor);
        uint256 expectedWidth = circuit.numConstants + circuit.numRoutedWires;
        if (circuit.numWires > expectedWidth) expectedWidth = circuit.numWires;
        uint256 normInverseLength = 2 * circuit.numRoutedWires;
        if (normInverseLength > expectedWidth) expectedWidth = normInverseLength;
        if (proof.constituentWidth != expectedWidth) revert InvalidMleProof();

        proof.circuitDigest = _readBaseVector(encoded, cursor, CIRCUIT_DIGEST_LENGTH_V2, requireCanonicalLimbs);
        proof.publicInputs = _readBaseVector(encoded, cursor, circuit.numPublicInputs, requireCanonicalLimbs);
        proof.preprocessedRoot = _readBytes32(encoded, cursor);
        proof.witnessRoot = _readBytes32(encoded, cursor);
        proof.normInverseRoot = _readBytes32(encoded, cursor);
        proof.whirTranscript = _readBlob(encoded, cursor, MAX_WHIR_NARG_BYTES_V2);
        proof.whirHints = _readBlob(encoded, cursor, MAX_WHIR_HINT_BYTES_V2);

        proof.logProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.logProof.rounds[round].nonConstant =
                _readExt3Vector(encoded, cursor, LOG_ROUND_DEGREE_V2, requireCanonicalLimbs);
        }

        uint256 preprocessedLength = circuit.numConstants + circuit.numRoutedWires;
        proof.logPreprocessed = _readExt3Vector(encoded, cursor, preprocessedLength, requireCanonicalLimbs);
        proof.logWitness = _readExt3Vector(encoded, cursor, circuit.numWires, requireCanonicalLimbs);
        proof.logNormInverse = _readExt3Vector(encoded, cursor, normInverseLength, requireCanonicalLimbs);

        proof.gateProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        uint256 gateDegree = circuit.quotientDegreeFactor + 2;
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.gateProof.rounds[round].nonConstant =
                _readExt3Vector(encoded, cursor, gateDegree, requireCanonicalLimbs);
        }
        proof.gatePreprocessed = _readExt3Vector(encoded, cursor, preprocessedLength, requireCanonicalLimbs);
        proof.gateWitness = _readExt3Vector(encoded, cursor, circuit.numWires, requireCanonicalLimbs);

        if (cursor.offset != encoded.length) revert InvalidMleProof();
    }

    function _readBaseVector(bytes calldata encoded, Cursor memory cursor, uint256 count, bool canonical)
        private
        pure
        returns (uint256[] memory values)
    {
        uint256 start = cursor.offset;
        // Check by division before either `count * 8` below. Together with the
        // global compact-proof cap this proves both calldata reads and memory
        // pointer arithmetic bounded even for a hostile standalone decoder
        // call whose circuit shape was not constructor-pinned.
        if (start > encoded.length || count > (encoded.length - start) / 8) revert InvalidMleProof();
        assembly ("memory-safe") {
            function bswap64(x) -> y {
                y := or(and(shr(8, x), 0x00FF00FF00FF00FF), and(shl(8, x), 0xFF00FF00FF00FF00))
                y := or(and(shr(16, y), 0x0000FFFF0000FFFF), and(shl(16, y), 0xFFFF0000FFFF0000))
                y := and(or(shr(32, y), shl(32, y)), 0xFFFFFFFFFFFFFFFF)
            }

            let p := 0xFFFFFFFF00000001
            values := mload(0x40)
            let output := add(values, 0x20)
            let input := add(encoded.offset, start)
            mstore(values, count)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let value := bswap64(shr(192, calldataload(add(input, mul(i, 8)))))
                if and(canonical, iszero(lt(value, p))) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                mstore(add(output, mul(i, 0x20)), value)
            }
            mstore(0x40, add(output, mul(count, 0x20)))
        }
        cursor.offset = start + count * 8;
    }

    function _readExt3Vector(bytes calldata encoded, Cursor memory cursor, uint256 count, bool canonical)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        uint256 start = cursor.offset;
        // Divide the remaining byte count before multiplying so an adversarial
        // dimension can never wrap `count * 24`. Production dimensions are
        // constructor-pinned, but the compact grammar remains independently
        // fail-closed here.
        if (start > encoded.length || count > (encoded.length - start) / 24) {
            revert InvalidMleProof();
        }
        uint256 byteLength = count * 24;

        // Solidity represents an array of three-word structs as a length word,
        // a table of record pointers, then separately allocated 96-byte
        // records. Allocate the exact same representation contiguously instead
        // of growing free memory once per limb tuple. The division check above
        // and global input cap prove `count * (0x20 + 0x60)` cannot overflow;
        // every 24-byte source read lies in calldata. This preserves ordinary
        // ABI encoding and indexing while avoiding hundreds of allocator calls.
        assembly ("memory-safe") {
            function bswap64(x) -> y {
                y := or(and(shr(8, x), 0x00FF00FF00FF00FF), and(shl(8, x), 0xFF00FF00FF00FF00))
                y := or(and(shr(16, y), 0x0000FFFF0000FFFF), and(shl(16, y), 0xFFFF0000FFFF0000))
                y := and(or(shr(32, y), shl(32, y)), 0xFFFFFFFFFFFFFFFF)
            }

            let p := 0xFFFFFFFF00000001
            let arrayPtr := mload(0x40)
            let pointerTable := add(arrayPtr, 0x20)
            let records := add(pointerTable, mul(count, 0x20))
            let source := add(encoded.offset, start)
            mstore(arrayPtr, count)

            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let record := add(records, mul(i, 0x60))
                let input := add(source, mul(i, 24))
                let c0 := bswap64(shr(192, calldataload(input)))
                let c1 := bswap64(shr(192, calldataload(add(input, 8))))
                let c2 := bswap64(shr(192, calldataload(add(input, 16))))
                if and(canonical, iszero(and(and(lt(c0, p), lt(c1, p)), lt(c2, p)))) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                mstore(add(pointerTable, mul(i, 0x20)), record)
                mstore(record, c0)
                mstore(add(record, 0x20), c1)
                mstore(add(record, 0x40), c2)
            }

            mstore(0x40, add(records, mul(count, 0x60)))
            values := arrayPtr
        }
        cursor.offset = start + byteLength;
    }

    function _readBlob(bytes calldata encoded, Cursor memory cursor, uint256 maximum)
        private
        pure
        returns (bytes memory value)
    {
        uint256 length = _readU32(encoded, cursor);
        if (length > maximum) revert InvalidMleProof();
        _requireAvailable(encoded, cursor.offset, length);
        value = new bytes(length);
        uint256 source = cursor.offset;
        assembly ("memory-safe") {
            calldatacopy(add(value, 0x20), add(encoded.offset, source), length)
        }
        cursor.offset += length;
    }

    function _readBytes32(bytes calldata encoded, Cursor memory cursor) private pure returns (bytes32 value) {
        _requireAvailable(encoded, cursor.offset, 32);
        uint256 offset = cursor.offset;
        assembly ("memory-safe") {
            value := calldataload(add(encoded.offset, offset))
        }
        cursor.offset = offset + 32;
    }

    function _readU32(bytes calldata encoded, Cursor memory cursor) private pure returns (uint256 value) {
        _requireAvailable(encoded, cursor.offset, 4);
        uint256 offset = cursor.offset;
        uint256 word;
        assembly ("memory-safe") {
            word := calldataload(add(encoded.offset, offset))
            value := or(or(byte(0, word), shl(8, byte(1, word))), or(shl(16, byte(2, word)), shl(24, byte(3, word))))
        }
        cursor.offset = offset + 4;
    }

    function _readU64(bytes calldata encoded, Cursor memory cursor, bool canonical)
        private
        pure
        returns (uint256 value)
    {
        _requireAvailable(encoded, cursor.offset, 8);
        value = _readU64Unchecked(encoded, cursor, canonical);
    }

    function _readU64Unchecked(bytes calldata encoded, Cursor memory cursor, bool canonical)
        private
        pure
        returns (uint256 value)
    {
        uint256 offset = cursor.offset;
        uint256 word;
        assembly ("memory-safe") {
            word := calldataload(add(encoded.offset, offset))
            value := or(
                or(or(byte(0, word), shl(8, byte(1, word))), or(shl(16, byte(2, word)), shl(24, byte(3, word)))),
                or(
                    or(shl(32, byte(4, word)), shl(40, byte(5, word))),
                    or(shl(48, byte(6, word)), shl(56, byte(7, word)))
                )
            )
        }
        cursor.offset = offset + 8;
        if (canonical && value >= BASE_FIELD_MODULUS_V2) revert InvalidMleProof();
    }

    function _requireAvailable(bytes calldata encoded, uint256 offset, uint256 count) private pure {
        // All schema dimensions and the complete input are tightly capped, so
        // subtraction is safe after the explicit offset check.
        if (offset > encoded.length || count > encoded.length - offset) revert InvalidMleProof();
    }
}
