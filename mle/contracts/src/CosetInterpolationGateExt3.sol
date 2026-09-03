// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {CosetInterpolationConstants} from "./CosetInterpolationConstants.sol";
import {InvalidMleProof} from "./MleProofErrors.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {BASE_FIELD_MODULUS_V2, INNER_EXTENSION_NON_RESIDUE_V2} from "./generated/MleWhirV2.sol";

/// @title CosetInterpolationGateExt3
/// @notice Exact Plonky2 coset-interpolation constraints over the Goldilocks cubic extension.
/// @dev Plonky2's inner quadratic extension is represented by `(c0, c1)` over Fp3, with
///      `t^2 = 7`. This external-library boundary mirrors
///      `mle/src/gate_ext3.rs::eval_coset_interpolation` without projecting any Fp3 limb.
library CosetInterpolationGateExt3 {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;
    uint256 private constant INNER_EXTENSION_NONRESIDUE = INNER_EXTENSION_NON_RESIDUE_V2;

    struct Ext2 {
        GoldilocksExt3.Ext3 c0;
        GoldilocksExt3.Ext3 c1;
    }

    struct CosetState {
        Ext2 evaluation;
        Ext2 product;
        Ext2 point;
    }

    struct Layout {
        uint256 points;
        uint256 intermediates;
        uint256 startIntermediates;
        uint256 shiftedPointIndex;
    }

    /// @notice Evaluate gate id 13 over Ext3-valued wire openings.
    /// @dev Wire layout, for `N = 2^subgroupBits` and
    ///      `m = (N - 2) / (degree - 1)`:
    ///
    ///      - `wires[0]`: shift (an Fp3 scalar)
    ///      - `wires[1 + 2*i .. +2]`: value `i`, as an Ext2 pair, for `i < N`
    ///      - the next two pairs: evaluation point and claimed evaluation value
    ///      - `m` intermediate evaluation pairs, then `m` intermediate product pairs
    ///      - the final pair: shifted evaluation point
    ///
    ///      The input length must be exactly `7 + 2*N + 4*m`; the caller must slice a
    ///      circuit-wide wire vector to this gate-local prefix. Every Fp3 limb must be
    ///      canonical. Supported subgroup sizes are the checked-in table range 1..=5.
    /// @return output The `4 + 4*m` unfiltered constraints in canonical Plonky2 order.
    function evalCoset(GoldilocksExt3.Ext3[] memory wires, uint256 subgroupBits, uint256 degree)
        external
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        Layout memory layout = _validateAndLayout(wires, subgroupBits, degree);
        output = new GoldilocksExt3.Ext3[](4 + 4 * layout.intermediates);

        Ext2 memory evaluationPoint = _readExt2(wires, 1 + 2 * layout.points);
        Ext2 memory shiftedPoint = _readExt2(wires, layout.shiftedPointIndex);

        uint256 outputIndex = _writePair(output, 0, _sub(evaluationPoint, _scalarMul(shiftedPoint, wires[0])));

        CosetState memory state;
        state.product = _one();
        state.point = shiftedPoint;
        _runChunk(state, wires, subgroupBits, 0, degree);

        for (uint256 i = 0; i < layout.intermediates; ++i) {
            Ext2 memory intermediateEvaluation = _readExt2(wires, layout.startIntermediates + 2 * i);
            Ext2 memory intermediateProduct =
                _readExt2(wires, layout.startIntermediates + 2 * layout.intermediates + 2 * i);

            outputIndex = _writePair(output, outputIndex, _sub(intermediateEvaluation, state.evaluation));
            outputIndex = _writePair(output, outputIndex, _sub(intermediateProduct, state.product));

            state.evaluation = intermediateEvaluation;
            state.product = intermediateProduct;

            uint256 start = 1 + (degree - 1) * (i + 1);
            uint256 end = start + degree - 1;
            if (end > layout.points) end = layout.points;
            _runChunk(state, wires, subgroupBits, start, end);
        }

        Ext2 memory claimedEvaluation = _readExt2(wires, 1 + 2 * (layout.points + 1));
        outputIndex = _writePair(output, outputIndex, _sub(claimedEvaluation, state.evaluation));
        assert(outputIndex == output.length);
    }

    function _validateAndLayout(GoldilocksExt3.Ext3[] memory wires, uint256 subgroupBits, uint256 degree)
        private
        pure
        returns (Layout memory layout)
    {
        if (subgroupBits < 1 || subgroupBits > 5) revert InvalidMleProof();

        layout.points = uint256(1) << subgroupBits;
        if (degree < 2 || degree > layout.points) revert InvalidMleProof();

        layout.intermediates = (layout.points - 2) / (degree - 1);
        layout.startIntermediates = 2 * layout.points + 5;
        layout.shiftedPointIndex = layout.startIntermediates + 4 * layout.intermediates;
        if (wires.length != layout.shiftedPointIndex + 2) revert InvalidMleProof();

        for (uint256 i = 0; i < wires.length; ++i) {
            GoldilocksExt3.Ext3 memory value = wires[i];
            if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
                revert InvalidMleProof();
            }
        }

        // Eagerly touch the canonical table as a defense against the supported-range
        // guard drifting away from the checked-in constants.
        if (CosetInterpolationConstants.weight(subgroupBits, 0) >= P) revert InvalidMleProof();
    }

    /// @dev Run Rust's `coset_partial_interpolate` over `[start, end)` and mutate `state`.
    function _runChunk(
        CosetState memory state,
        GoldilocksExt3.Ext3[] memory wires,
        uint256 subgroupBits,
        uint256 start,
        uint256 end
    ) private pure {
        for (uint256 j = start; j < end; ++j) {
            Ext2 memory term =
                _sub(state.point, _fromBase(CosetInterpolationConstants.subgroupElement(subgroupBits, j)));
            Ext2 memory weightedValue =
                _scalarMul(_readExt2(wires, 1 + 2 * j), _base(CosetInterpolationConstants.weight(subgroupBits, j)));

            // Evaluation must use the old product, exactly as in the Rust recurrence.
            Ext2 memory nextEvaluation = _add(_mul(state.evaluation, term), _mul(weightedValue, state.product));
            Ext2 memory nextProduct = _mul(state.product, term);
            state.evaluation = nextEvaluation;
            state.product = nextProduct;
        }
    }

    function _readExt2(GoldilocksExt3.Ext3[] memory wires, uint256 start) private pure returns (Ext2 memory result) {
        result.c0 = wires[start];
        result.c1 = wires[start + 1];
    }

    function _writePair(GoldilocksExt3.Ext3[] memory output, uint256 start, Ext2 memory value)
        private
        pure
        returns (uint256)
    {
        output[start] = value.c0;
        output[start + 1] = value.c1;
        return start + 2;
    }

    function _fromBase(uint256 value) private pure returns (Ext2 memory result) {
        result.c0 = _base(value);
    }

    function _base(uint256 value) private pure returns (GoldilocksExt3.Ext3 memory result) {
        if (value >= P) revert InvalidMleProof();
        // `P < 2^64`, so the canonical-field check makes this narrowing exact.
        // forge-lint: disable-next-line(unsafe-typecast)
        result.c0 = uint64(value);
    }

    function _one() private pure returns (Ext2 memory result) {
        result.c0 = GoldilocksExt3.one();
    }

    function _add(Ext2 memory left, Ext2 memory right) private pure returns (Ext2 memory result) {
        result.c0 = GoldilocksExt3.add(left.c0, right.c0);
        result.c1 = GoldilocksExt3.add(left.c1, right.c1);
    }

    function _sub(Ext2 memory left, Ext2 memory right) private pure returns (Ext2 memory result) {
        result.c0 = GoldilocksExt3.sub(left.c0, right.c0);
        result.c1 = GoldilocksExt3.sub(left.c1, right.c1);
    }

    function _scalarMul(Ext2 memory value, GoldilocksExt3.Ext3 memory scalar)
        private
        pure
        returns (Ext2 memory result)
    {
        result.c0 = GoldilocksExt3.mul(value.c0, scalar);
        result.c1 = GoldilocksExt3.mul(value.c1, scalar);
    }

    function _mul(Ext2 memory left, Ext2 memory right) private pure returns (Ext2 memory result) {
        result.c0 = GoldilocksExt3.add(
            GoldilocksExt3.mul(left.c0, right.c0),
            GoldilocksExt3.mulScalarU256(GoldilocksExt3.mul(left.c1, right.c1), INNER_EXTENSION_NONRESIDUE)
        );
        result.c1 = GoldilocksExt3.add(GoldilocksExt3.mul(left.c0, right.c1), GoldilocksExt3.mul(left.c1, right.c0));
    }
}
