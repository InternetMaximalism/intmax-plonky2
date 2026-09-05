// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof, InvalidMleVerifierConfiguration} from "./MleProofErrors.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {PoseidonGateExt3} from "./PoseidonGateExt3.sol";
import {CosetInterpolationGateExt3} from "./CosetInterpolationGateExt3.sol";
import {
    BASE_FIELD_MODULUS_V2,
    MAX_CONSTITUENT_WIDTH_V2,
    MAX_GATE_CONSTRAINTS_V2,
    MAX_GATE_ROUND_DEGREE_V2
} from "./generated/MleWhirV2.sol";

/// @title Plonky2GateEvaluatorExt3
/// @notice Exact Plonky2 gate aggregation over Goldilocks Fp3 for MLE/WHIR v2.
/// @dev Wires and constants are Fp3 evaluations at an off-cube point. They MUST
///      remain Fp3 throughout every nonlinear gate operation; projecting limbs
///      to the base field would be unsound. Plonky2's inner degree-two algebra
///      is represented as a pair of Fp3 values with t^2=7.
library Plonky2GateEvaluatorExt3 {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;
    uint256 internal constant UNUSED_SELECTOR = 0xFFFFFFFF;
    uint256 internal constant MAX_GATE_CONSTRAINTS = MAX_GATE_CONSTRAINTS_V2;
    uint256 internal constant MAX_CONSTITUENT_WIDTH = MAX_CONSTITUENT_WIDTH_V2;

    uint8 internal constant GATE_NOOP = 0;
    uint8 internal constant GATE_CONSTANT = 1;
    uint8 internal constant GATE_PUBLIC_INPUT = 2;
    uint8 internal constant GATE_ARITHMETIC = 3;
    uint8 internal constant GATE_POSEIDON = 4;
    uint8 internal constant GATE_POSEIDON_MDS = 5;
    uint8 internal constant GATE_ARITHMETIC_EXT = 6;
    uint8 internal constant GATE_MUL_EXT = 7;
    uint8 internal constant GATE_EXPONENTIATION = 8;
    uint8 internal constant GATE_BASE_SUM = 9;
    uint8 internal constant GATE_REDUCING = 10;
    uint8 internal constant GATE_REDUCING_EXT = 11;
    uint8 internal constant GATE_RANDOM_ACCESS = 12;
    uint8 internal constant GATE_COSET_INTERPOLATION = 13;

    /// @dev Byte-for-byte field widths match Rust `GateInfoV2` and its config digest.
    struct GateInfoV2 {
        uint8 gateId;
        uint8 selectorIndex;
        uint8 groupStart;
        uint8 groupEnd;
        uint8 gateRowIndex;
        uint16 numConstraints;
        uint16 numOrConsts;
        uint16 param2;
        uint16 param3;
    }

    struct Ext2 {
        GoldilocksExt3.Ext3 c0;
        GoldilocksExt3.Ext3 c1;
    }

    struct RandomAccessLayout {
        uint256 bits;
        uint256 vectorSize;
        uint256 copyWidth;
        uint256 routedWires;
    }

    /// @notice Validate, evaluate, filter, and aggregate all configured gates.
    /// @dev Computes `sum_i alpha^i * sum_gate(filter_gate*c_gate[i])` via the
    ///      distributively equivalent per-gate reduction. Every gate descriptor
    ///      is validated before dispatch, so an unknown gate fails even if its
    ///      selector happens to evaluate to zero.
    function evalCombined(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256[4] memory publicInputsHash,
        GoldilocksExt3.Ext3 memory alpha,
        GateInfoV2[] calldata gates,
        uint256 numSelectors,
        uint256 numConstants,
        uint256 numGateConstraints,
        uint256 numWires,
        uint256 quotientDegreeFactor
    ) external pure returns (GoldilocksExt3.Ext3 memory combined) {
        if (wires.length != numWires || constants.length != numConstants) {
            revert InvalidMleProof();
        }
        _validateConfiguration(gates, numSelectors, numConstants, numGateConstraints, numWires, quotientDegreeFactor);
        _validateCanonical(wires);
        _validateCanonical(constants);
        _checkCanonical(alpha);
        for (uint256 i = 0; i < 4; ++i) {
            if (publicInputsHash[i] >= P) revert InvalidMleProof();
        }

        return _evalCombinedUnchecked(wires, constants, publicInputsHash, alpha, gates, numSelectors);
    }

    /// @notice Evaluate a deployment-pinned gate table after the atomic
    /// verifier's complete proof/configuration preflight.
    /// @dev `wires` and `constants` were already checked as canonical proof
    /// limbs, `publicInputsHash` and `alpha` are verifier-derived canonical
    /// values, and the constructor validated every gate descriptor. This is
    /// not a safe standalone entry for untrusted inputs.
    function evalCombinedPrevalidated(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256[4] memory publicInputsHash,
        GoldilocksExt3.Ext3 memory alpha,
        GateInfoV2[] calldata gates,
        uint256 numSelectors
    ) external pure returns (GoldilocksExt3.Ext3 memory combined) {
        return _evalCombinedUnchecked(wires, constants, publicInputsHash, alpha, gates, numSelectors);
    }

    function _evalCombinedUnchecked(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256[4] memory publicHash,
        GoldilocksExt3.Ext3 memory alpha,
        GateInfoV2[] calldata gates,
        uint256 numSelectors
    ) private pure returns (GoldilocksExt3.Ext3 memory combined) {
        combined = GoldilocksExt3.zero();
        for (uint256 row = 0; row < gates.length; ++row) {
            GateInfoV2 calldata info = gates[row];
            GoldilocksExt3.Ext3 memory filter =
                _computeFilter(info, constants[uint256(info.selectorIndex)], numSelectors > 1);
            // Metadata for every gate was validated above. A zero selector filter
            // therefore makes this gate's entire contribution identically zero;
            // avoid evaluating expensive inactive Poseidon/coset constraints.
            if (GoldilocksExt3.isZero(filter)) continue;
            GoldilocksExt3.Ext3 memory reduced;
            // Poseidon is by far the largest Plonky2 gate. Reduce its constraints
            // inside the linked library so 123/24 Ext3 values are never ABI-copied
            // back into this evaluator, and pass the already validated wire vector
            // directly instead of allocating another struct array prefix.
            if (info.gateId == GATE_POSEIDON) {
                reduced = PoseidonGateExt3.evalPoseidonReduced(wires, alpha);
            } else if (info.gateId == GATE_POSEIDON_MDS) {
                reduced = PoseidonGateExt3.evalPoseidonMdsReduced(wires, alpha);
            } else {
                GoldilocksExt3.Ext3[] memory unfiltered =
                    _evaluateUnfiltered(info, wires, constants, publicHash, numSelectors);
                if (unfiltered.length != uint256(info.numConstraints)) revert InvalidMleVerifierConfiguration();
                reduced = GoldilocksExt3.reduceWithPowers(unfiltered, alpha);
            }
            combined = GoldilocksExt3.add(combined, GoldilocksExt3.mul(filter, reduced));
        }
    }

    /// @notice Validate all gate-dispatch metadata and the exact degree bound
    /// independently of prover-supplied terminal values.
    function validateConfiguration(
        GateInfoV2[] calldata gates,
        uint256 numSelectors,
        uint256 numConstants,
        uint256 numGateConstraints,
        uint256 numWires,
        uint256 quotientDegreeFactor
    ) external pure {
        _validateConfiguration(gates, numSelectors, numConstants, numGateConstraints, numWires, quotientDegreeFactor);
    }

    function _validateConfiguration(
        GateInfoV2[] calldata gates,
        uint256 numSelectors,
        uint256 numConstants,
        uint256 numGateConstraints,
        uint256 numWires,
        uint256 quotientDegreeFactor
    ) private pure {
        if (
            numWires > MAX_CONSTITUENT_WIDTH || numConstants > MAX_CONSTITUENT_WIDTH
                || numGateConstraints > MAX_GATE_CONSTRAINTS || numSelectors == 0 || numSelectors > numConstants
                || gates.length == 0 || gates.length > type(uint8).max || numSelectors > gates.length
                || quotientDegreeFactor == 0 || quotientDegreeFactor > MAX_GATE_ROUND_DEGREE_V2 - 2
        ) revert InvalidMleVerifierConfiguration();

        uint256 exactMaximum;
        for (uint256 row = 0; row < gates.length; ++row) {
            uint256 constraints = _validateGate(gates[row], row, gates.length, numSelectors, numConstants, numWires);
            if (constraints > exactMaximum) exactMaximum = constraints;
            uint256 filterDegree = uint256(gates[row].groupEnd) - uint256(gates[row].groupStart) - 1;
            if (numSelectors > 1) ++filterDegree;
            if (_unfilteredDegree(gates[row]) + filterDegree > quotientDegreeFactor + 1) {
                revert InvalidMleVerifierConfiguration();
            }
        }
        if (exactMaximum != numGateConstraints) revert InvalidMleVerifierConfiguration();
    }

    /// @dev Exact Plonky2 gate degree used by selector-filter degree accounting.
    /// Multiplication by the row equality polynomial adds one further degree in
    /// the outer sumcheck, so the public entry point enforces
    /// `gateDegree + filterDegree <= quotientDegreeFactor + 1`.
    function _unfilteredDegree(GateInfoV2 calldata info) private pure returns (uint256) {
        if (info.gateId == GATE_NOOP) return 0;
        if (info.gateId == GATE_CONSTANT || info.gateId == GATE_PUBLIC_INPUT || info.gateId == GATE_POSEIDON_MDS) {
            return 1;
        }
        if (info.gateId == GATE_ARITHMETIC || info.gateId == GATE_ARITHMETIC_EXT || info.gateId == GATE_MUL_EXT) {
            return 3;
        }
        if (info.gateId == GATE_POSEIDON) return 7;
        if (info.gateId == GATE_EXPONENTIATION) return 4;
        if (info.gateId == GATE_BASE_SUM || info.gateId == GATE_COSET_INTERPOLATION) {
            return uint256(info.param2);
        }
        if (info.gateId == GATE_REDUCING || info.gateId == GATE_REDUCING_EXT) return 2;
        if (info.gateId == GATE_RANDOM_ACCESS) return uint256(info.numOrConsts) + 1;
        revert InvalidMleVerifierConfiguration();
    }

    function _evaluateUnfiltered(
        GateInfoV2 calldata info,
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256[4] memory publicHash,
        uint256 numSelectors
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        uint256 count = uint256(info.numOrConsts);
        if (info.gateId == GATE_NOOP) return new GoldilocksExt3.Ext3[](0);
        if (info.gateId == GATE_CONSTANT) return _evalConstant(wires, constants, numSelectors, count);
        if (info.gateId == GATE_PUBLIC_INPUT) return _evalPublicInput(wires, publicHash);
        if (info.gateId == GATE_ARITHMETIC) return _evalArithmetic(wires, constants, numSelectors, count);
        if (info.gateId == GATE_ARITHMETIC_EXT) {
            return _evalArithmeticExtension(wires, constants, numSelectors, count);
        }
        if (info.gateId == GATE_MUL_EXT) return _evalMulExtension(wires, constants, numSelectors, count);
        if (info.gateId == GATE_EXPONENTIATION) return _evalExponentiation(wires, count);
        if (info.gateId == GATE_BASE_SUM) return _evalBaseSum(wires, count, uint256(info.param2));
        if (info.gateId == GATE_REDUCING) return _evalReducing(wires, count, false);
        if (info.gateId == GATE_REDUCING_EXT) return _evalReducing(wires, count, true);
        if (info.gateId == GATE_RANDOM_ACCESS) {
            return _evalRandomAccess(wires, constants, numSelectors, count, uint256(info.param2), uint256(info.param3));
        }
        if (info.gateId == GATE_COSET_INTERPOLATION) {
            uint256 points = uint256(1) << count;
            uint256 intermediates = (points - 2) / (uint256(info.param2) - 1);
            return CosetInterpolationGateExt3.evalCoset(
                _prefix(wires, 7 + 2 * points + 4 * intermediates), count, uint256(info.param2)
            );
        }
        revert InvalidMleVerifierConfiguration();
    }

    function _validateGate(
        GateInfoV2 calldata info,
        uint256 row,
        uint256 gateCount,
        uint256 numSelectors,
        uint256 numConstants,
        uint256 numWires
    ) private pure returns (uint256 expectedConstraints) {
        if (
            uint256(info.gateRowIndex) != row || uint256(info.selectorIndex) >= numSelectors
                || info.groupStart >= info.groupEnd || uint256(info.groupEnd) > gateCount
                || row < uint256(info.groupStart) || row >= uint256(info.groupEnd)
        ) revert InvalidMleVerifierConfiguration();

        uint256 n = uint256(info.numOrConsts);
        uint256 requiredWires;
        uint256 requiredLocalConstants;
        if (info.gateId == GATE_NOOP) {
            _requireZeroParams(info);
        } else if (info.gateId == GATE_CONSTANT) {
            _requireAuxZero(info);
            expectedConstraints = n;
            requiredWires = n;
            requiredLocalConstants = n;
        } else if (info.gateId == GATE_PUBLIC_INPUT) {
            _requireZeroParams(info);
            expectedConstraints = 4;
            requiredWires = 4;
        } else if (info.gateId == GATE_ARITHMETIC) {
            _requireAuxZero(info);
            expectedConstraints = n;
            requiredWires = 4 * n;
            requiredLocalConstants = 2;
        } else if (info.gateId == GATE_POSEIDON) {
            _requireZeroParams(info);
            expectedConstraints = 123;
            requiredWires = 135;
        } else if (info.gateId == GATE_POSEIDON_MDS) {
            _requireZeroParams(info);
            expectedConstraints = 24;
            requiredWires = 48;
        } else if (info.gateId == GATE_ARITHMETIC_EXT) {
            _requireAuxZero(info);
            expectedConstraints = 2 * n;
            requiredWires = 8 * n;
            requiredLocalConstants = 2;
        } else if (info.gateId == GATE_MUL_EXT) {
            _requireAuxZero(info);
            expectedConstraints = 2 * n;
            requiredWires = 6 * n;
            requiredLocalConstants = 1;
        } else if (info.gateId == GATE_EXPONENTIATION) {
            _requireAuxZero(info);
            if (n == 0) revert InvalidMleVerifierConfiguration();
            expectedConstraints = n + 1;
            requiredWires = 2 * n + 2;
        } else if (info.gateId == GATE_BASE_SUM) {
            if (info.param3 != 0 || !_supportedBase(uint256(info.param2))) {
                revert InvalidMleVerifierConfiguration();
            }
            expectedConstraints = n + 1;
            requiredWires = n + 1;
        } else if (info.gateId == GATE_REDUCING) {
            _requireAuxZero(info);
            if (n == 0) revert InvalidMleVerifierConfiguration();
            expectedConstraints = 2 * n;
            requiredWires = 4 + 3 * n;
        } else if (info.gateId == GATE_REDUCING_EXT) {
            _requireAuxZero(info);
            if (n == 0) revert InvalidMleVerifierConfiguration();
            expectedConstraints = 2 * n;
            requiredWires = 4 + 4 * n;
        } else if (info.gateId == GATE_RANDOM_ACCESS) {
            uint256 copies = uint256(info.param2);
            uint256 extra = uint256(info.param3);
            if (n == 0 || n > 7 || copies == 0) revert InvalidMleVerifierConfiguration();
            uint256 vectorSize = uint256(1) << n;
            uint256 copyWidth = 2 + vectorSize;
            requiredWires = copyWidth * copies + extra + copies * n;
            requiredLocalConstants = extra;
            expectedConstraints = copies * (n + 2) + extra;
        } else if (info.gateId == GATE_COSET_INTERPOLATION) {
            if (info.param3 != 0 || n == 0 || n > 5) revert InvalidMleVerifierConfiguration();
            uint256 degree = uint256(info.param2);
            uint256 points = uint256(1) << n;
            if (degree < 2 || degree > points) revert InvalidMleVerifierConfiguration();
            uint256 intermediates = (points - 2) / (degree - 1);
            expectedConstraints = 4 + 4 * intermediates;
            requiredWires = 7 + 2 * points + 4 * intermediates;
        } else {
            revert InvalidMleVerifierConfiguration();
        }

        if (
            uint256(info.numConstraints) != expectedConstraints || requiredWires > numWires
                || requiredLocalConstants > numConstants - numSelectors
        ) revert InvalidMleVerifierConfiguration();
    }

    function _computeFilter(GateInfoV2 calldata info, GoldilocksExt3.Ext3 memory selector, bool manySelectors)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory filter)
    {
        filter = GoldilocksExt3.one();
        for (uint256 other = uint256(info.groupStart); other < uint256(info.groupEnd); ++other) {
            if (other != uint256(info.gateRowIndex)) {
                filter = GoldilocksExt3.mul(filter, GoldilocksExt3.sub(_base(other), selector));
            }
        }
        if (manySelectors) {
            filter = GoldilocksExt3.mul(filter, GoldilocksExt3.sub(_base(UNUSED_SELECTOR), selector));
        }
    }

    function _evalConstant(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 count
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        output = new GoldilocksExt3.Ext3[](count);
        for (uint256 i = 0; i < count; ++i) {
            output[i] = GoldilocksExt3.sub(constants[constantOffset + i], wires[i]);
        }
    }

    function _evalPublicInput(GoldilocksExt3.Ext3[] memory wires, uint256[4] memory publicHash)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        output = new GoldilocksExt3.Ext3[](4);
        for (uint256 i = 0; i < 4; ++i) {
            output[i] = GoldilocksExt3.sub(wires[i], _base(publicHash[i]));
        }
    }

    function _evalArithmetic(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 count
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        output = new GoldilocksExt3.Ext3[](count);
        GoldilocksExt3.Ext3 memory c0 = constants[constantOffset];
        GoldilocksExt3.Ext3 memory c1 = constants[constantOffset + 1];
        for (uint256 i = 0; i < count; ++i) {
            uint256 start = 4 * i;
            GoldilocksExt3.Ext3 memory computed = GoldilocksExt3.add(
                GoldilocksExt3.mul(c0, GoldilocksExt3.mul(wires[start], wires[start + 1])),
                GoldilocksExt3.mul(c1, wires[start + 2])
            );
            output[i] = GoldilocksExt3.sub(wires[start + 3], computed);
        }
    }

    function _evalArithmeticExtension(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 count
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        output = new GoldilocksExt3.Ext3[](2 * count);
        for (uint256 i = 0; i < count; ++i) {
            uint256 start = 8 * i;
            Ext2 memory computed = _ext2Add(
                _ext2ScalarMul(
                    _ext2Mul(_readExt2(wires, start), _readExt2(wires, start + 2)), constants[constantOffset]
                ),
                _ext2ScalarMul(_readExt2(wires, start + 4), constants[constantOffset + 1])
            );
            _writeExt2(output, 2 * i, _ext2Sub(_readExt2(wires, start + 6), computed));
        }
    }

    function _evalMulExtension(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 count
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        output = new GoldilocksExt3.Ext3[](2 * count);
        for (uint256 i = 0; i < count; ++i) {
            uint256 start = 6 * i;
            Ext2 memory computed = _ext2ScalarMul(
                _ext2Mul(_readExt2(wires, start), _readExt2(wires, start + 2)), constants[constantOffset]
            );
            _writeExt2(output, 2 * i, _ext2Sub(_readExt2(wires, start + 4), computed));
        }
    }

    function _evalExponentiation(GoldilocksExt3.Ext3[] memory wires, uint256 bits)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        output = new GoldilocksExt3.Ext3[](bits + 1);
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        uint256 intermediateStart = 2 + bits;
        for (uint256 i = 0; i < bits; ++i) {
            GoldilocksExt3.Ext3 memory previous = i == 0 ? one : GoldilocksExt3.square(wires[intermediateStart + i - 1]);
            GoldilocksExt3.Ext3 memory bit = wires[bits - i];
            GoldilocksExt3.Ext3 memory multiplier =
                GoldilocksExt3.add(GoldilocksExt3.mul(bit, wires[0]), GoldilocksExt3.sub(one, bit));
            output[i] = GoldilocksExt3.sub(GoldilocksExt3.mul(previous, multiplier), wires[intermediateStart + i]);
        }
        output[bits] = GoldilocksExt3.sub(wires[1 + bits], wires[intermediateStart + bits - 1]);
    }

    function _evalBaseSum(GoldilocksExt3.Ext3[] memory wires, uint256 limbs, uint256 base)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        output = new GoldilocksExt3.Ext3[](limbs + 1);
        GoldilocksExt3.Ext3 memory computed = GoldilocksExt3.zero();
        for (uint256 i = limbs; i > 0; --i) {
            computed = GoldilocksExt3.add(GoldilocksExt3.mul(computed, _base(base)), wires[i]);
        }
        output[0] = GoldilocksExt3.sub(computed, wires[0]);
        for (uint256 i = 0; i < limbs; ++i) {
            GoldilocksExt3.Ext3 memory rangeCheck = GoldilocksExt3.one();
            for (uint256 value = 0; value < base; ++value) {
                rangeCheck = GoldilocksExt3.mul(rangeCheck, GoldilocksExt3.sub(wires[i + 1], _base(value)));
            }
            output[i + 1] = rangeCheck;
        }
    }

    function _evalReducing(GoldilocksExt3.Ext3[] memory wires, uint256 count, bool extensionCoefficients)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        output = new GoldilocksExt3.Ext3[](2 * count);
        Ext2 memory alpha = _readExt2(wires, 2);
        Ext2 memory accumulator = _readExt2(wires, 4);
        uint256 coefficientWidth = extensionCoefficients ? 2 : 1;
        uint256 coefficientStart = 6;
        uint256 accumulatorStart = coefficientStart + coefficientWidth * count;
        for (uint256 i = 0; i < count; ++i) {
            Ext2 memory coefficient = extensionCoefficients
                ? _readExt2(wires, coefficientStart + 2 * i)
                : Ext2({c0: wires[coefficientStart + i], c1: GoldilocksExt3.zero()});
            Ext2 memory next = i + 1 == count ? _readExt2(wires, 0) : _readExt2(wires, accumulatorStart + 2 * i);
            _writeExt2(output, 2 * i, _ext2Sub(_ext2Add(_ext2Mul(accumulator, alpha), coefficient), next));
            accumulator = next;
        }
    }

    function _evalRandomAccess(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 bits,
        uint256 copies,
        uint256 extraConstants
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        RandomAccessLayout memory layout = RandomAccessLayout({
            bits: bits,
            vectorSize: uint256(1) << bits,
            copyWidth: 2 + (uint256(1) << bits),
            routedWires: (2 + (uint256(1) << bits)) * copies + extraConstants
        });
        output = new GoldilocksExt3.Ext3[](copies * (bits + 2) + extraConstants);
        uint256 outputIndex;
        for (uint256 copy = 0; copy < copies; ++copy) {
            GoldilocksExt3.Ext3[] memory copyConstraints = _evalRandomAccessCopy(wires, layout, copy);
            for (uint256 i = 0; i < copyConstraints.length; ++i) {
                output[outputIndex++] = copyConstraints[i];
            }
        }
        for (uint256 i = 0; i < extraConstants; ++i) {
            output[outputIndex++] =
                GoldilocksExt3.sub(constants[constantOffset + i], wires[layout.copyWidth * copies + i]);
        }
    }

    function _evalRandomAccessCopy(GoldilocksExt3.Ext3[] memory wires, RandomAccessLayout memory layout, uint256 copy)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        output = new GoldilocksExt3.Ext3[](layout.bits + 2);
        uint256 copyStart = layout.copyWidth * copy;
        uint256 bitStart = layout.routedWires + copy * layout.bits;
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 bitIndex = 0; bitIndex < layout.bits; ++bitIndex) {
            GoldilocksExt3.Ext3 memory bit = wires[bitStart + bitIndex];
            output[bitIndex] = GoldilocksExt3.mul(bit, GoldilocksExt3.sub(bit, one));
        }

        GoldilocksExt3.Ext3 memory reconstructed = GoldilocksExt3.zero();
        for (uint256 bitIndex = layout.bits; bitIndex > 0; --bitIndex) {
            reconstructed = GoldilocksExt3.add(GoldilocksExt3.double_(reconstructed), wires[bitStart + bitIndex - 1]);
        }
        output[layout.bits] = GoldilocksExt3.sub(reconstructed, wires[copyStart]);

        GoldilocksExt3.Ext3[] memory list = new GoldilocksExt3.Ext3[](layout.vectorSize);
        for (uint256 i = 0; i < layout.vectorSize; ++i) {
            list[i] = wires[copyStart + 2 + i];
        }
        uint256 currentLength = layout.vectorSize;
        for (uint256 bitIndex = 0; bitIndex < layout.bits; ++bitIndex) {
            GoldilocksExt3.Ext3 memory bit = wires[bitStart + bitIndex];
            uint256 half = currentLength / 2;
            for (uint256 i = 0; i < half; ++i) {
                list[i] = GoldilocksExt3.add(
                    list[2 * i], GoldilocksExt3.mul(bit, GoldilocksExt3.sub(list[2 * i + 1], list[2 * i]))
                );
            }
            currentLength = half;
        }
        output[layout.bits + 1] = GoldilocksExt3.sub(list[0], wires[copyStart + 1]);
    }

    function _readExt2(GoldilocksExt3.Ext3[] memory values, uint256 start) private pure returns (Ext2 memory value) {
        value.c0 = values[start];
        value.c1 = values[start + 1];
    }

    function _writeExt2(GoldilocksExt3.Ext3[] memory values, uint256 start, Ext2 memory value) private pure {
        values[start] = value.c0;
        values[start + 1] = value.c1;
    }

    function _ext2Add(Ext2 memory left, Ext2 memory right) private pure returns (Ext2 memory result) {
        result.c0 = GoldilocksExt3.add(left.c0, right.c0);
        result.c1 = GoldilocksExt3.add(left.c1, right.c1);
    }

    function _ext2Sub(Ext2 memory left, Ext2 memory right) private pure returns (Ext2 memory result) {
        result.c0 = GoldilocksExt3.sub(left.c0, right.c0);
        result.c1 = GoldilocksExt3.sub(left.c1, right.c1);
    }

    function _ext2ScalarMul(Ext2 memory value, GoldilocksExt3.Ext3 memory scalar)
        private
        pure
        returns (Ext2 memory result)
    {
        result.c0 = GoldilocksExt3.mul(value.c0, scalar);
        result.c1 = GoldilocksExt3.mul(value.c1, scalar);
    }

    function _ext2Mul(Ext2 memory left, Ext2 memory right) private pure returns (Ext2 memory result) {
        result.c0 = GoldilocksExt3.add(
            GoldilocksExt3.mul(left.c0, right.c0),
            GoldilocksExt3.mulScalarU256(GoldilocksExt3.mul(left.c1, right.c1), 7)
        );
        result.c1 = GoldilocksExt3.add(GoldilocksExt3.mul(left.c0, right.c1), GoldilocksExt3.mul(left.c1, right.c0));
    }

    function _validateCanonical(GoldilocksExt3.Ext3[] memory values) private pure {
        for (uint256 i = 0; i < values.length; ++i) {
            _checkCanonical(values[i]);
        }
    }

    function _prefix(GoldilocksExt3.Ext3[] memory source, uint256 length)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory result)
    {
        if (length > source.length) revert InvalidMleVerifierConfiguration();
        result = new GoldilocksExt3.Ext3[](length);
        for (uint256 i = 0; i < length; ++i) {
            result[i] = source[i];
        }
    }

    function _checkCanonical(GoldilocksExt3.Ext3 memory value) private pure {
        if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
            revert InvalidMleProof();
        }
    }

    function _base(uint256 value) private pure returns (GoldilocksExt3.Ext3 memory result) {
        if (value >= P) revert InvalidMleProof();
        result.c0 = uint64(value);
    }

    function _requireZeroParams(GateInfoV2 calldata info) private pure {
        if (info.numOrConsts != 0 || info.param2 != 0 || info.param3 != 0) {
            revert InvalidMleVerifierConfiguration();
        }
    }

    function _requireAuxZero(GateInfoV2 calldata info) private pure {
        if (info.param2 != 0 || info.param3 != 0) revert InvalidMleVerifierConfiguration();
    }

    function _supportedBase(uint256 value) private pure returns (bool) {
        return value >= 2 && value <= 8 || value == 16 || value == 32 || value == 64 || value == 128 || value == 256;
    }
}
