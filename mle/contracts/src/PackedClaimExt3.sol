// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof} from "./MleProofErrors.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {
    BASE_FIELD_MODULUS_V2,
    MAX_CONSTITUENT_INDEX_BITS_V2,
    MAX_CONSTITUENT_WIDTH_V2,
    MAX_ROUTED_WIRES_V2,
    NUM_PCS_CLAIMS_V2,
    NUM_PCS_GROUPS_V2,
    NUM_PCS_TERMINAL_POINTS_V2,
    PACKED_BOUND_CLAIM_MASK_V2
} from "./generated/MleWhirV2.sol";

/// @title PackedClaimExt3
/// @notice Canonical Ext3 constituent folding for the grouped MLE/WHIR v2 statement.
/// @dev The packed dense-table order is row variables first, followed by
/// constituent-index variables in LSB-first order. Missing constituent slots are
/// zero padded to the next power of two. This library deliberately lives behind an
/// external-library boundary so a production verifier can link it without absorbing
/// the implementation into its own EIP-170 bytecode budget.
library PackedClaimExt3 {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;
    uint256 internal constant MAX_CONSTITUENT_WIDTH = MAX_CONSTITUENT_WIDTH_V2;
    uint256 internal constant MAX_INDEX_BITS = MAX_CONSTITUENT_INDEX_BITS_V2;
    uint256 internal constant MAX_ROUTED_WIRES = MAX_ROUTED_WIRES_V2;

    uint256 internal constant NUM_GROUPS = NUM_PCS_GROUPS_V2;
    uint256 internal constant NUM_POINTS = NUM_PCS_TERMINAL_POINTS_V2;
    uint256 internal constant NUM_CELLS = NUM_PCS_CLAIMS_V2;
    bytes1 internal constant USED_CELL_MASK = PACKED_BOUND_CLAIM_MASK_V2;

    /// @dev These dimensions are circuit/VK data in the complete verifier. `width`
    /// must equal `max(numConstants + numRoutedWires, numWires, 2*numRoutedWires)`.
    struct Schema {
        uint256 width;
        uint256 numConstants;
        uint256 numRoutedWires;
        uint256 numWires;
    }

    /// @dev Exact five terminal-used cells in point-major/group-major order:
    /// `(log, preprocessed)`, `(log, witness)`, `(log, norm-inverse)`,
    /// `(gate, preprocessed)`, `(gate, witness)`. The sixth Cartesian cell,
    /// `(gate, norm-inverse)`, is unused and is represented by a zero output.
    struct UsedClaims {
        GoldilocksExt3.Ext3[] logPreprocessed;
        GoldilocksExt3.Ext3[] logWitness;
        GoldilocksExt3.Ext3[] logNormInverse;
        GoldilocksExt3.Ext3[] gatePreprocessed;
        GoldilocksExt3.Ext3[] gateWitness;
    }

    /// @notice Fold one Ext3 constituent vector at its Ext3 index point.
    /// @dev All limbs are checked for canonical Goldilocks representation before
    /// arithmetic. `values` may occupy a strict prefix of `width`; the suffix up to
    /// `width.next_power_of_two()` is exactly zero.
    function fold(GoldilocksExt3.Ext3[] memory values, uint256 width, GoldilocksExt3.Ext3[] memory indexPoint)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory result)
    {
        (uint256 capacity,) = _validateFoldInputs(values, width, indexPoint);
        result = _foldUnchecked(values, capacity, indexPoint);
    }

    /// @notice Fold the exact five v2 terminal-used point/group cells.
    /// @return evaluations Six point-major/group-major evaluations. Slots `0..4`
    /// are populated and slot `5` is the canonical zero for the unused cell.
    /// @return evalMask Exactly one byte, `0x1f`, authenticating slots `0..4` only.
    function foldV2UsedCells(UsedClaims memory claims, Schema memory schema, GoldilocksExt3.Ext3[][] memory indexPoints)
        external
        pure
        returns (GoldilocksExt3.Ext3[] memory evaluations, bytes memory evalMask)
    {
        return foldV2UsedCellsInternal(claims, schema, indexPoints);
    }

    /// @dev Identical specialized fold for callers that can afford inlining.
    /// The atomic verifier uses this path to avoid ABI-encoding roughly six
    /// hundred Ext3 claim records into a delegatecall to this library.
    function foldV2UsedCellsInternal(
        UsedClaims memory claims,
        Schema memory schema,
        GoldilocksExt3.Ext3[][] memory indexPoints
    ) internal pure returns (GoldilocksExt3.Ext3[] memory evaluations, bytes memory evalMask) {
        uint256 capacity = _validateV2Inputs(claims, schema, indexPoints);

        return _foldV2UsedCellsUnchecked(claims, capacity, indexPoints);
    }

    /// @dev Specialized path for the atomic verifier after its calldata
    /// preflight has checked the exact five vector lengths and every Ext3 limb,
    /// and after transcript squeezing has produced two canonical index points
    /// of the deployment-pinned length. Keeping this entry internal prevents an
    /// untrusted caller from bypassing those checks at an ABI boundary.
    function foldV2UsedCellsPrevalidatedInternal(
        UsedClaims memory claims,
        uint256 capacity,
        GoldilocksExt3.Ext3[][] memory indexPoints
    ) internal pure returns (GoldilocksExt3.Ext3[] memory evaluations, bytes memory evalMask) {
        return _foldV2UsedCellsUnchecked(claims, capacity, indexPoints);
    }

    function _foldV2UsedCellsUnchecked(
        UsedClaims memory claims,
        uint256 capacity,
        GoldilocksExt3.Ext3[][] memory indexPoints
    ) private pure returns (GoldilocksExt3.Ext3[] memory evaluations, bytes memory evalMask) {
        evaluations = new GoldilocksExt3.Ext3[](NUM_CELLS);
        // One flat limb buffer (three words per slot) shared by all five folds. Every fold
        // overwrites the prefix it uses, so no per-fold allocation or zeroing is needed.
        uint256[] memory scratch = new uint256[](3 * capacity);
        _foldFlat(claims.logPreprocessed, indexPoints[0], scratch, evaluations[0]);
        _foldFlat(claims.logWitness, indexPoints[0], scratch, evaluations[1]);
        _foldFlat(claims.logNormInverse, indexPoints[0], scratch, evaluations[2]);
        _foldFlat(claims.gatePreprocessed, indexPoints[1], scratch, evaluations[3]);
        _foldFlat(claims.gateWitness, indexPoints[1], scratch, evaluations[4]);
        // evaluations[5] remains the canonical Ext3 zero.

        evalMask = new bytes(1);
        evalMask[0] = USED_CELL_MASK;
    }

    /// @notice Return the protocol-fixed v2 used-cell mask.
    function usedCellMask() external pure returns (bytes memory mask) {
        mask = new bytes(1);
        mask[0] = USED_CELL_MASK;
    }

    function _validateV2Inputs(
        UsedClaims memory claims,
        Schema memory schema,
        GoldilocksExt3.Ext3[][] memory indexPoints
    ) private pure returns (uint256 capacity) {
        // Cap each dimension before additions/multiplication so even adversarial
        // direct callers cannot trigger an arithmetic panic in schema derivation.
        if (
            schema.numConstants > MAX_CONSTITUENT_WIDTH || schema.numRoutedWires > MAX_ROUTED_WIRES
                || schema.numWires > MAX_CONSTITUENT_WIDTH
        ) revert InvalidMleProof();

        uint256 preprocessedLength = schema.numConstants + schema.numRoutedWires;
        uint256 normInverseLength = 2 * schema.numRoutedWires;
        uint256 expectedWidth = preprocessedLength;
        if (schema.numWires > expectedWidth) expectedWidth = schema.numWires;
        if (normInverseLength > expectedWidth) expectedWidth = normInverseLength;
        if (schema.width != expectedWidth) revert InvalidMleProof();

        uint256 indexBits;
        (capacity, indexBits) = _widthShape(schema.width);
        if (indexPoints.length != NUM_POINTS) revert InvalidMleProof();
        for (uint256 point = 0; point < NUM_POINTS; ++point) {
            if (indexPoints[point].length != indexBits) revert InvalidMleProof();
            _validateCanonical(indexPoints[point]);
        }

        if (
            claims.logPreprocessed.length != preprocessedLength || claims.logWitness.length != schema.numWires
                || claims.logNormInverse.length != normInverseLength
                || claims.gatePreprocessed.length != preprocessedLength || claims.gateWitness.length != schema.numWires
        ) revert InvalidMleProof();

        // Complete the preflight before doing any field arithmetic or allocating
        // fold layers. In particular, inactive/late cells cannot hide a bad limb.
        _validateCanonical(claims.logPreprocessed);
        _validateCanonical(claims.logWitness);
        _validateCanonical(claims.logNormInverse);
        _validateCanonical(claims.gatePreprocessed);
        _validateCanonical(claims.gateWitness);
    }

    function _validateFoldInputs(
        GoldilocksExt3.Ext3[] memory values,
        uint256 width,
        GoldilocksExt3.Ext3[] memory indexPoint
    ) private pure returns (uint256 capacity, uint256 indexBits) {
        (capacity, indexBits) = _widthShape(width);
        if (values.length > width || indexPoint.length != indexBits) revert InvalidMleProof();
        _validateCanonical(values);
        _validateCanonical(indexPoint);
    }

    function _widthShape(uint256 width) private pure returns (uint256 capacity, uint256 indexBits) {
        if (width == 0 || width > MAX_CONSTITUENT_WIDTH) revert InvalidMleProof();
        capacity = 1;
        while (capacity < width) {
            capacity <<= 1;
            ++indexBits;
        }
        // Keep the reviewed zero-padding envelope explicit. For width <= 160 the
        // next power of two is at most 256 and therefore needs at most eight bits.
        if (indexBits > MAX_INDEX_BITS || capacity > (uint256(1) << MAX_INDEX_BITS)) {
            revert InvalidMleProof();
        }
    }

    function _validateCanonical(GoldilocksExt3.Ext3[] memory values) private pure {
        for (uint256 i = 0; i < values.length; ++i) {
            GoldilocksExt3.Ext3 memory value = values[i];
            if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
                revert InvalidMleProof();
            }
        }
    }

    function _foldUnchecked(
        GoldilocksExt3.Ext3[] memory values,
        uint256 capacity,
        GoldilocksExt3.Ext3[] memory indexPoint
    ) private pure returns (GoldilocksExt3.Ext3 memory result) {
        uint256[] memory scratch = new uint256[](3 * capacity);
        _foldFlat(values, indexPoint, scratch, result);
    }

    /// @dev Multilinear fold of `values` (a strict prefix of the zero-padded slot
    /// table) at `indexPoint`, LSB-first, computed in a flat limb buffer.
    ///
    /// Algebraically identical to the reviewed record-based fold: every butterfly is
    /// `even + r * (odd - even)`, an absent (zero-padded) odd partner contributes
    /// `even + r * (0 - even)`, and pairs that lie wholly inside the zero suffix are
    /// never evaluated because they cannot change the result. The buffer holds three
    /// words per slot; slot `i` of the next layer is written only after pair `i` was
    /// consumed (slot `0` is read before it is written, every other slot `j` was read
    /// by pair `j / 2 < j`), so the in-place update never aliases a live input.
    function _foldFlat(
        GoldilocksExt3.Ext3[] memory values,
        GoldilocksExt3.Ext3[] memory indexPoint,
        uint256[] memory scratch,
        GoldilocksExt3.Ext3 memory result
    ) private pure {
        uint256 count = values.length;
        if (count == 0) return;
        if (3 * count > scratch.length) revert InvalidMleProof();
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let buf := add(scratch, 0x20)
            let table := add(values, 0x20)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let record := mload(add(table, shl(5, i)))
                let dst := add(buf, mul(i, 0x60))
                mstore(dst, mload(record))
                mstore(add(dst, 0x20), mload(add(record, 0x20)))
                mstore(add(dst, 0x40), mload(add(record, 0x40)))
            }
            let active := count
            let bits := mload(indexPoint)
            let points := add(indexPoint, 0x20)
            for { let bit := 0 } lt(bit, bits) { bit := add(bit, 1) } {
                let challenge := mload(add(points, shl(5, bit)))
                let r0 := mload(challenge)
                let r1 := mload(add(challenge, 0x20))
                let r2 := mload(add(challenge, 0x40))
                let next := shr(1, add(active, 1))
                for { let i := 0 } lt(i, next) { i := add(i, 1) } {
                    let even := add(buf, mul(shl(1, i), 0x60))
                    let e0 := mload(even)
                    let e1 := mload(add(even, 0x20))
                    let e2 := mload(add(even, 0x40))
                    // d = odd - even, with odd = 0 for the sole element of an odd prefix.
                    let d0 := sub(p, e0)
                    let d1 := sub(p, e1)
                    let d2 := sub(p, e2)
                    if lt(add(shl(1, i), 1), active) {
                        let odd := add(even, 0x60)
                        d0 := addmod(mload(odd), d0, p)
                        d1 := addmod(mload(add(odd, 0x20)), d1, p)
                        d2 := addmod(mload(add(odd, 0x40)), d2, p)
                    }
                    let t0 := addmod(mulmod(r1, d2, p), mulmod(r2, d1, p), p)
                    let product0 := addmod(mulmod(r0, d0, p), mulmod(2, t0, p), p)
                    let t1 := addmod(mulmod(r0, d1, p), mulmod(r1, d0, p), p)
                    let product1 := addmod(t1, mulmod(2, mulmod(r2, d2, p), p), p)
                    let product2 := addmod(addmod(mulmod(r0, d2, p), mulmod(r1, d1, p), p), mulmod(r2, d0, p), p)
                    let dst := add(buf, mul(i, 0x60))
                    mstore(dst, addmod(e0, product0, p))
                    mstore(add(dst, 0x20), addmod(e1, product1, p))
                    mstore(add(dst, 0x40), addmod(e2, product2, p))
                }
                active := next
            }
            mstore(result, mload(buf))
            mstore(add(result, 0x20), mload(add(buf, 0x20)))
            mstore(add(result, 0x40), mload(add(buf, 0x40)))
        }
    }
}
