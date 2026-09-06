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

    /// @dev Plonky2 `ArithmeticGate`: `w[4i+3] - (c0 * w[4i] * w[4i+1] + c1 * w[4i+2])`.
    function _evalArithmetic(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 count
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        if (wires.length < 4 * count || constants.length < constantOffset + 2) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](count);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                r0 := addmod(mulmod(a0, b0, p), mulmod(2, t0, p), p)
                let t1 := addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p)
                r1 := addmod(t1, mulmod(2, mulmod(a2, b2, p), p), p)
                r2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            }
            function add3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                r0 := addmod(a0, b0, p)
                r1 := addmod(a1, b1, p)
                r2 := addmod(a2, b2, p)
            }
            function sub3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                r0 := addmod(a0, sub(p, b0), p)
                r1 := addmod(a1, sub(p, b1), p)
                r2 := addmod(a2, sub(p, b2), p)
            }
            function ld(table, i) -> x0, x1, x2 {
                let r := mload(add(table, shl(5, i)))
                x0 := mload(r)
                x1 := mload(add(r, 0x20))
                x2 := mload(add(r, 0x40))
            }
            function st(table, i, x0, x1, x2) {
                let r := mload(add(table, shl(5, i)))
                mstore(r, x0)
                mstore(add(r, 0x20), x1)
                mstore(add(r, 0x40), x2)
            }
            let w := add(wires, 0x20)
            let out := add(output, 0x20)
            let c00, c01, c02 := ld(add(constants, 0x20), constantOffset)
            let c10, c11, c12 := ld(add(constants, 0x20), add(constantOffset, 1))
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let sIdx := shl(2, i)
                let a0, a1, a2 := ld(w, sIdx)
                let b0, b1, b2 := ld(w, add(sIdx, 1))
                let m0, m1, m2 := mul3(a0, a1, a2, b0, b1, b2)
                let x0, x1, x2 := mul3(c00, c01, c02, m0, m1, m2)
                let d0, d1, d2 := ld(w, add(sIdx, 2))
                let y0, y1, y2 := mul3(c10, c11, c12, d0, d1, d2)
                let e0, e1, e2 := add3(x0, x1, x2, y0, y1, y2)
                let f0, f1, f2 := ld(w, add(sIdx, 3))
                let o0, o1, o2 := sub3(f0, f1, f2, e0, e1, e2)
                st(out, i, o0, o1, o2)
            }
        }
    }

    /// @dev Plonky2 `ArithmeticExtensionGate` over the quadratic extension (W = 7) whose
    /// coefficients are Ext3 evaluations: `D - (c0 * (A ⊗ B) + c1 * C)` per operation.
    function _evalArithmeticExtension(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 count
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        if (wires.length < 8 * count || constants.length < constantOffset + 2) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](2 * count);
        uint256[24] memory scratch;
        assembly ("memory-safe") {
            function rp(table, i) -> r {
                r := mload(add(table, shl(5, i)))
            }
            function mul3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                let a0 := mload(a)
                let a1 := mload(add(a, 0x20))
                let a2 := mload(add(a, 0x40))
                let b0 := mload(b)
                let b1 := mload(add(b, 0x20))
                let b2 := mload(add(b, 0x40))
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                let r0 := addmod(mulmod(a0, b0, p), mulmod(2, t0, p), p)
                let t1 := addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p)
                let r1 := addmod(t1, mulmod(2, mulmod(a2, b2, p), p), p)
                let r2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
                mstore(o, r0)
                mstore(add(o, 0x20), r1)
                mstore(add(o, 0x40), r2)
            }
            function add3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), mload(b), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), mload(add(b, 0x20)), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), mload(add(b, 0x40)), p))
            }
            function sub3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), sub(p, mload(b)), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), sub(p, mload(add(b, 0x20))), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), sub(p, mload(add(b, 0x40))), p))
            }
            function mul7p(a, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, mulmod(mload(a), 7, p))
                mstore(add(o, 0x20), mulmod(mload(add(a, 0x20)), 7, p))
                mstore(add(o, 0x40), mulmod(mload(add(a, 0x40)), 7, p))
            }
            // (a0 + a1 X) * (b0 + b1 X) with X^2 = 7: o0 = a0 b0 + 7 a1 b1, o1 = a0 b1 + a1 b0.
            // `t` is a scratch pointer with room for three Ext3 records.
            function q2mul(a0, a1, b0, b1, o0, o1, t) {
                mul3p(a1, b1, t)
                mul7p(t, add(t, 0x60))
                mul3p(a0, b0, t)
                add3p(t, add(t, 0x60), o0)
                mul3p(a0, b1, t)
                mul3p(a1, b0, add(t, 0x60))
                add3p(t, add(t, 0x60), o1)
            }
            let w := add(wires, 0x20)
            let out := add(output, 0x20)
            let c0 := rp(add(constants, 0x20), constantOffset)
            let c1 := rp(add(constants, 0x20), add(constantOffset, 1))
            let m0 := scratch
            let m1 := add(scratch, 0x60)
            let x0 := add(scratch, 0xc0)
            let x1 := add(scratch, 0x120)
            let t := add(scratch, 0x180)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let sIdx := shl(3, i)
                q2mul(rp(w, sIdx), rp(w, add(sIdx, 1)), rp(w, add(sIdx, 2)), rp(w, add(sIdx, 3)), m0, m1, t)
                mul3p(m0, c0, x0)
                mul3p(m1, c0, x1)
                mul3p(rp(w, add(sIdx, 4)), c1, t)
                add3p(x0, t, x0)
                mul3p(rp(w, add(sIdx, 5)), c1, t)
                add3p(x1, t, x1)
                sub3p(rp(w, add(sIdx, 6)), x0, rp(out, shl(1, i)))
                sub3p(rp(w, add(sIdx, 7)), x1, rp(out, add(shl(1, i), 1)))
            }
        }
    }

    /// @dev Plonky2 `MulExtensionGate`: `D - c0 * (A ⊗ B)` per operation (quadratic extension, W = 7).
    function _evalMulExtension(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 count
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        if (wires.length < 6 * count || constants.length < constantOffset + 1) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](2 * count);
        uint256[24] memory scratch;
        assembly ("memory-safe") {
            function rp(table, i) -> r {
                r := mload(add(table, shl(5, i)))
            }
            function mul3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                let a0 := mload(a)
                let a1 := mload(add(a, 0x20))
                let a2 := mload(add(a, 0x40))
                let b0 := mload(b)
                let b1 := mload(add(b, 0x20))
                let b2 := mload(add(b, 0x40))
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                let r0 := addmod(mulmod(a0, b0, p), mulmod(2, t0, p), p)
                let t1 := addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p)
                let r1 := addmod(t1, mulmod(2, mulmod(a2, b2, p), p), p)
                let r2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
                mstore(o, r0)
                mstore(add(o, 0x20), r1)
                mstore(add(o, 0x40), r2)
            }
            function add3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), mload(b), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), mload(add(b, 0x20)), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), mload(add(b, 0x40)), p))
            }
            function sub3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), sub(p, mload(b)), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), sub(p, mload(add(b, 0x20))), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), sub(p, mload(add(b, 0x40))), p))
            }
            function mul7p(a, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, mulmod(mload(a), 7, p))
                mstore(add(o, 0x20), mulmod(mload(add(a, 0x20)), 7, p))
                mstore(add(o, 0x40), mulmod(mload(add(a, 0x40)), 7, p))
            }
            // (a0 + a1 X) * (b0 + b1 X) with X^2 = 7: o0 = a0 b0 + 7 a1 b1, o1 = a0 b1 + a1 b0.
            // `t` is a scratch pointer with room for three Ext3 records.
            function q2mul(a0, a1, b0, b1, o0, o1, t) {
                mul3p(a1, b1, t)
                mul7p(t, add(t, 0x60))
                mul3p(a0, b0, t)
                add3p(t, add(t, 0x60), o0)
                mul3p(a0, b1, t)
                mul3p(a1, b0, add(t, 0x60))
                add3p(t, add(t, 0x60), o1)
            }
            let w := add(wires, 0x20)
            let out := add(output, 0x20)
            let c0 := rp(add(constants, 0x20), constantOffset)
            let m0 := scratch
            let m1 := add(scratch, 0x60)
            let x0 := add(scratch, 0xc0)
            let x1 := add(scratch, 0x120)
            let t := add(scratch, 0x180)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let sIdx := mul(6, i)
                q2mul(rp(w, sIdx), rp(w, add(sIdx, 1)), rp(w, add(sIdx, 2)), rp(w, add(sIdx, 3)), m0, m1, t)
                mul3p(m0, c0, x0)
                mul3p(m1, c0, x1)
                sub3p(rp(w, add(sIdx, 4)), x0, rp(out, shl(1, i)))
                sub3p(rp(w, add(sIdx, 5)), x1, rp(out, add(shl(1, i), 1)))
            }
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

    /// @dev Plonky2 `BaseSumGate<base>`: `sum_i w[i+1] base^i - w[0]`, then one range product
    /// `prod_{v<base} (w[i+1] - v)` per limb.
    function _evalBaseSum(GoldilocksExt3.Ext3[] memory wires, uint256 limbs, uint256 base)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        if (wires.length < limbs + 1 || base == 0 || base >= P) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](limbs + 1);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                r0 := addmod(mulmod(a0, b0, p), mulmod(2, t0, p), p)
                let t1 := addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p)
                r1 := addmod(t1, mulmod(2, mulmod(a2, b2, p), p), p)
                r2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            }
            function add3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                r0 := addmod(a0, b0, p)
                r1 := addmod(a1, b1, p)
                r2 := addmod(a2, b2, p)
            }
            function sub3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                r0 := addmod(a0, sub(p, b0), p)
                r1 := addmod(a1, sub(p, b1), p)
                r2 := addmod(a2, sub(p, b2), p)
            }
            function ld(table, i) -> x0, x1, x2 {
                let r := mload(add(table, shl(5, i)))
                x0 := mload(r)
                x1 := mload(add(r, 0x20))
                x2 := mload(add(r, 0x40))
            }
            function st(table, i, x0, x1, x2) {
                let r := mload(add(table, shl(5, i)))
                mstore(r, x0)
                mstore(add(r, 0x20), x1)
                mstore(add(r, 0x40), x2)
            }
            let p := 0xFFFFFFFF00000001
            let w := add(wires, 0x20)
            let out := add(output, 0x20)
            let s0 := 0
            let s1 := 0
            let s2 := 0
            for { let i := limbs } gt(i, 0) { i := sub(i, 1) } {
                let l0, l1, l2 := ld(w, i)
                s0 := addmod(mulmod(s0, base, p), l0, p)
                s1 := addmod(mulmod(s1, base, p), l1, p)
                s2 := addmod(mulmod(s2, base, p), l2, p)
            }
            let w00, w01, w02 := ld(w, 0)
            let o0, o1, o2 := sub3(s0, s1, s2, w00, w01, w02)
            st(out, 0, o0, o1, o2)
            for { let i := 0 } lt(i, limbs) { i := add(i, 1) } {
                let l0, l1, l2 := ld(w, add(i, 1))
                let r0 := 1
                let r1 := 0
                let r2 := 0
                for { let v := 0 } lt(v, base) { v := add(v, 1) } {
                    // (w - v) subtracts the base scalar from limb 0 only
                    let d0 := addmod(l0, sub(p, v), p)
                    r0, r1, r2 := mul3(r0, r1, r2, d0, l1, l2)
                }
                st(out, add(i, 1), r0, r1, r2)
            }
        }
    }

    /// @dev Plonky2 `ReducingGate` / `ReducingExtensionGate`: `acc_{i+1} = acc_i * alpha + c_i` over the
    /// quadratic extension (W = 7); wires are `[out(2), alpha(2), acc0(2), coeffs, accs(2 per step)]`.
    function _evalReducing(GoldilocksExt3.Ext3[] memory wires, uint256 count, bool extensionCoefficients)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory output)
    {
        uint256 coefficientWidth = extensionCoefficients ? 2 : 1;
        uint256 accumulatorStart = 6 + coefficientWidth * count;
        // The last accumulator is wire[0..2]; every earlier one is read from `accumulatorStart`.
        if (count == 0 || wires.length < accumulatorStart + 2 * (count - 1)) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](2 * count);
        uint256[24] memory scratch;
        assembly ("memory-safe") {
            function rp(table, i) -> r {
                r := mload(add(table, shl(5, i)))
            }
            function mul3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                let a0 := mload(a)
                let a1 := mload(add(a, 0x20))
                let a2 := mload(add(a, 0x40))
                let b0 := mload(b)
                let b1 := mload(add(b, 0x20))
                let b2 := mload(add(b, 0x40))
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                let r0 := addmod(mulmod(a0, b0, p), mulmod(2, t0, p), p)
                let t1 := addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p)
                let r1 := addmod(t1, mulmod(2, mulmod(a2, b2, p), p), p)
                let r2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
                mstore(o, r0)
                mstore(add(o, 0x20), r1)
                mstore(add(o, 0x40), r2)
            }
            function add3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), mload(b), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), mload(add(b, 0x20)), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), mload(add(b, 0x40)), p))
            }
            function sub3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), sub(p, mload(b)), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), sub(p, mload(add(b, 0x20))), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), sub(p, mload(add(b, 0x40))), p))
            }
            function mul7p(a, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, mulmod(mload(a), 7, p))
                mstore(add(o, 0x20), mulmod(mload(add(a, 0x20)), 7, p))
                mstore(add(o, 0x40), mulmod(mload(add(a, 0x40)), 7, p))
            }
            // (a0 + a1 X) * (b0 + b1 X) with X^2 = 7: o0 = a0 b0 + 7 a1 b1, o1 = a0 b1 + a1 b0.
            // `t` is a scratch pointer with room for three Ext3 records.
            function q2mul(a0, a1, b0, b1, o0, o1, t) {
                mul3p(a1, b1, t)
                mul7p(t, add(t, 0x60))
                mul3p(a0, b0, t)
                add3p(t, add(t, 0x60), o0)
                mul3p(a0, b1, t)
                mul3p(a1, b0, add(t, 0x60))
                add3p(t, add(t, 0x60), o1)
            }
            let w := add(wires, 0x20)
            let out := add(output, 0x20)
            let alpha0 := rp(w, 2)
            let alpha1 := rp(w, 3)
            let acc0 := rp(w, 4)
            let acc1 := rp(w, 5)
            let m0 := scratch
            let m1 := add(scratch, 0x60)
            let zero := add(scratch, 0xc0)
            let t := add(scratch, 0x120)
            mstore(zero, 0)
            mstore(add(zero, 0x20), 0)
            mstore(add(zero, 0x40), 0)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                q2mul(acc0, acc1, alpha0, alpha1, m0, m1, t)
                // + coefficient
                switch coefficientWidth
                case 2 {
                    add3p(m0, rp(w, add(6, shl(1, i))), m0)
                    add3p(m1, rp(w, add(7, shl(1, i))), m1)
                }
                default { add3p(m0, rp(w, add(6, i)), m0) }
                // - next accumulator (the final one is the gate output at wire 0..2)
                let next0 := rp(w, add(accumulatorStart, shl(1, i)))
                let next1 := rp(w, add(add(accumulatorStart, shl(1, i)), 1))
                if eq(add(i, 1), count) {
                    next0 := rp(w, 0)
                    next1 := rp(w, 1)
                }
                sub3p(m0, next0, rp(out, shl(1, i)))
                sub3p(m1, next1, rp(out, add(shl(1, i), 1)))
                acc0 := next0
                acc1 := next1
            }
        }
    }

    /// @dev Plonky2 `RandomAccessGate`: per copy, `bits` booleanity constraints, the index
    /// reconstruction `sum_j bit_j 2^j - index`, and the multilinear selection of the claimed element,
    /// followed by the gate's extra constant constraints.
    function _evalRandomAccess(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256 constantOffset,
        uint256 bits,
        uint256 copies,
        uint256 extraConstants
    ) private pure returns (GoldilocksExt3.Ext3[] memory output) {
        // The scratch list holds 2^bits Ext3 slots; the gate validator already bounds `bits`.
        if (bits > 16) revert InvalidMleVerifierConfiguration();
        if (
            wires.length < (2 + (uint256(1) << bits)) * copies + extraConstants + copies * bits
                || constants.length < constantOffset + extraConstants
        ) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](copies * (bits + 2) + extraConstants);
        uint256[] memory scratch = new uint256[](3 * (uint256(1) << bits) + 6);
        assembly ("memory-safe") {
            function rp(table, i) -> r {
                r := mload(add(table, shl(5, i)))
            }
            function mul3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                let a0 := mload(a)
                let a1 := mload(add(a, 0x20))
                let a2 := mload(add(a, 0x40))
                let b0 := mload(b)
                let b1 := mload(add(b, 0x20))
                let b2 := mload(add(b, 0x40))
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                let r0 := addmod(mulmod(a0, b0, p), mulmod(2, t0, p), p)
                let t1 := addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p)
                let r1 := addmod(t1, mulmod(2, mulmod(a2, b2, p), p), p)
                let r2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
                mstore(o, r0)
                mstore(add(o, 0x20), r1)
                mstore(add(o, 0x40), r2)
            }
            function add3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), mload(b), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), mload(add(b, 0x20)), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), mload(add(b, 0x40)), p))
            }
            function sub3p(a, b, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), sub(p, mload(b)), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), sub(p, mload(add(b, 0x20))), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), sub(p, mload(add(b, 0x40))), p))
            }
            function mul7p(a, o) {
                let p := 0xFFFFFFFF00000001
                mstore(o, mulmod(mload(a), 7, p))
                mstore(add(o, 0x20), mulmod(mload(add(a, 0x20)), 7, p))
                mstore(add(o, 0x40), mulmod(mload(add(a, 0x40)), 7, p))
            }
            let p := 0xFFFFFFFF00000001
            let w := add(wires, 0x20)
            let out := add(output, 0x20)
            let buf := add(scratch, 0x20)
            let vectorSize := shl(bits, 1)
            let copyWidth := add(2, vectorSize)
            let routedWires := add(mul(copyWidth, copies), extraConstants)
            // two Ext3 temporaries after the list slots
            let acc := add(buf, mul(vectorSize, 0x60))
            let tmp := add(acc, 0x60)
            let outputIndex := 0
            for { let copy := 0 } lt(copy, copies) { copy := add(copy, 1) } {
                let copyStart := mul(copyWidth, copy)
                let bitStart := add(routedWires, mul(copy, bits))
                // booleanity: bit * (bit - 1)
                for { let b := 0 } lt(b, bits) { b := add(b, 1) } {
                    let x := rp(w, add(bitStart, b))
                    mstore(tmp, addmod(mload(x), sub(p, 1), p))
                    mstore(add(tmp, 0x20), mload(add(x, 0x20)))
                    mstore(add(tmp, 0x40), mload(add(x, 0x40)))
                    mul3p(x, tmp, rp(out, outputIndex))
                    outputIndex := add(outputIndex, 1)
                }
                // reconstructed index: Horner from the most significant bit
                mstore(acc, 0)
                mstore(add(acc, 0x20), 0)
                mstore(add(acc, 0x40), 0)
                for { let b := bits } gt(b, 0) { b := sub(b, 1) } {
                    add3p(acc, acc, acc)
                    add3p(acc, rp(w, add(bitStart, sub(b, 1))), acc)
                }
                sub3p(acc, rp(w, copyStart), rp(out, outputIndex))
                outputIndex := add(outputIndex, 1)
                // multilinear selection over the list
                for { let k := 0 } lt(k, vectorSize) { k := add(k, 1) } {
                    let x := rp(w, add(add(copyStart, 2), k))
                    let dst := add(buf, mul(k, 0x60))
                    mstore(dst, mload(x))
                    mstore(add(dst, 0x20), mload(add(x, 0x20)))
                    mstore(add(dst, 0x40), mload(add(x, 0x40)))
                }
                let currentLength := vectorSize
                for { let b := 0 } lt(b, bits) { b := add(b, 1) } {
                    let bit := rp(w, add(bitStart, b))
                    let half := shr(1, currentLength)
                    for { let k := 0 } lt(k, half) { k := add(k, 1) } {
                        let even := add(buf, mul(shl(1, k), 0x60))
                        sub3p(add(even, 0x60), even, tmp)
                        mul3p(bit, tmp, tmp)
                        add3p(even, tmp, add(buf, mul(k, 0x60)))
                    }
                    currentLength := half
                }
                sub3p(buf, rp(w, add(copyStart, 1)), rp(out, outputIndex))
                outputIndex := add(outputIndex, 1)
            }
            for { let e := 0 } lt(e, extraConstants) { e := add(e, 1) } {
                sub3p(rp(add(constants, 0x20), add(constantOffset, e)), rp(w, add(mul(copyWidth, copies), e)), rp(out, outputIndex))
                outputIndex := add(outputIndex, 1)
            }
        }
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
