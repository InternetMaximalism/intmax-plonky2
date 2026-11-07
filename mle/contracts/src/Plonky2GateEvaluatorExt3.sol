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
///
///      Evaluation strategy: the validated wire and constant vectors are copied once
///      into flat limb buffers (three words per Fp3 value). Every gate body then runs
///      in one assembly block over those buffers, writes its constraints in canonical
///      Plonky2 order into a shared constraint buffer and reduces them by Horner's rule
///      with `alpha`. The two large gates live in linked libraries that receive the flat
///      wire buffer as calldata bytes and return the already reduced Fp3 value.
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

    /// @dev Evaluation state shared by the assembly gate bodies. Pointers are memory
    /// addresses of the first limb word; the field offsets below are used by the
    /// assembly and must match the declaration order.
    struct Frame {
        uint256 wires; // 0x00: flat wire limbs
        uint256 constants; // 0x20: flat constant limbs
        uint256 constraints; // 0x40: constraint buffer
        uint256 publicHash; // 0x60: publicInputsHash[4]
        uint256 alpha; // 0x80: alpha limbs
        uint256 localConstants; // 0xa0: flat constants after the selector columns
        uint256 gateId; // 0xc0
        uint256 n; // 0xe0: numOrConsts
        uint256 p2; // 0x100
        uint256 p3; // 0x120
        uint256 count; // 0x140: constraints produced by the current gate
        uint256 f0; // 0x160: selector filter
        uint256 f1; // 0x180
        uint256 f2; // 0x1a0
        uint256 r0; // 0x1c0: alpha-reduced gate value
        uint256 r1; // 0x1e0
        uint256 r2; // 0x200
        uint256 acc0; // 0x220: running sum of filter * reduced
        uint256 acc1; // 0x240
        uint256 acc2; // 0x260
        uint256 flatWires; // 0x280: the flat wire buffer as a `bytes` object (for library calls)
        uint256 numSelectors; // 0x2a0
        uint256 numWires; // 0x2c0
        uint256 numConstants; // 0x2e0
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

    /// @notice `evalCombinedPrevalidated` over flat limb buffers: `wires` and `constants`
    /// hold three canonical words per Fp3 value (`c0, c1, c2`) and no pointer table, so the
    /// atomic verifier's buffers cross the library boundary as plain word copies.
    /// @dev Same caller contract as `evalCombinedPrevalidated` (every limb canonical,
    /// deployment-validated gate table); not a safe standalone entry for untrusted inputs.
    function evalCombinedPrevalidatedFlat(
        uint256[] memory wires,
        uint256[] memory constants,
        uint256[4] memory publicInputsHash,
        GoldilocksExt3.Ext3 memory alpha,
        GateInfoV2[] calldata gates,
        uint256 numSelectors
    ) external pure returns (GoldilocksExt3.Ext3 memory combined) {
        if (wires.length % 3 != 0 || constants.length % 3 != 0) revert InvalidMleProof();
        // A `uint256[]` of 3n limb words has the layout of a `bytes` of 0x60 * n bytes up to
        // its length word; rewrite the length in place to present the same buffer as bytes.
        bytes memory flatWires;
        bytes memory flatConstants;
        assembly ("memory-safe") {
            flatWires := wires
            mstore(flatWires, shl(5, mload(wires)))
            flatConstants := constants
            mstore(flatConstants, shl(5, mload(constants)))
        }
        return _evalFlatUnchecked(flatWires, flatConstants, publicInputsHash, alpha, gates, numSelectors);
    }

    function _evalCombinedUnchecked(
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256[4] memory publicHash,
        GoldilocksExt3.Ext3 memory alpha,
        GateInfoV2[] calldata gates,
        uint256 numSelectors
    ) private pure returns (GoldilocksExt3.Ext3 memory combined) {
        return _evalFlatUnchecked(_flatten(wires), _flatten(constants), publicHash, alpha, gates, numSelectors);
    }

    /// @dev Evaluate over flat limb buffers (`0x60` bytes per Fp3 value).
    function _evalFlatUnchecked(
        bytes memory flatWires,
        bytes memory flatConstants,
        uint256[4] memory publicHash,
        GoldilocksExt3.Ext3 memory alpha,
        GateInfoV2[] calldata gates,
        uint256 numSelectors
    ) private pure returns (GoldilocksExt3.Ext3 memory combined) {
        uint256 maxConstraints;
        for (uint256 row = 0; row < gates.length; ++row) {
            if (uint256(gates[row].numConstraints) > maxConstraints) {
                maxConstraints = uint256(gates[row].numConstraints);
            }
        }
        bytes memory constraintBuffer = new bytes(maxConstraints * 0x60);

        Frame memory fr;
        assembly ("memory-safe") {
            mstore(fr, add(flatWires, 0x20))
            mstore(add(fr, 0x20), add(flatConstants, 0x20))
            mstore(add(fr, 0x40), add(constraintBuffer, 0x20))
            mstore(add(fr, 0x60), publicHash)
            mstore(add(fr, 0x80), alpha)
            mstore(add(fr, 0xa0), add(add(flatConstants, 0x20), mul(numSelectors, 0x60)))
            mstore(add(fr, 0x280), flatWires)
        }
        fr.numSelectors = numSelectors;
        fr.numWires = flatWires.length / 0x60;
        fr.numConstants = flatConstants.length / 0x60;
        _evalRows(fr, gates);
        combined.c0 = uint64(fr.acc0);
        combined.c1 = uint64(fr.acc1);
        combined.c2 = uint64(fr.acc2);
    }

    /// @dev Filter, evaluate, reduce and accumulate every gate row into `fr.acc`.
    function _evalRows(Frame memory fr, GateInfoV2[] calldata gates) private pure {
        for (uint256 row = 0; row < gates.length; ++row) {
            GateInfoV2 calldata info = gates[row];
            if (uint256(info.selectorIndex) >= fr.numConstants) revert InvalidMleProof();
            _computeFilter(fr, info, fr.numSelectors > 1);
            // Metadata for every gate was validated above. A zero selector filter
            // therefore makes this gate's entire contribution identically zero;
            // avoid evaluating expensive inactive Poseidon/coset constraints.
            if ((fr.f0 | fr.f1 | fr.f2) == 0) continue;

            uint256 gateId = uint256(info.gateId);
            fr.gateId = gateId;
            fr.n = uint256(info.numOrConsts);
            fr.p2 = uint256(info.param2);
            fr.p3 = uint256(info.param3);
            (uint256 count, uint256 requiredWires) =
                _gateBounds(gateId, fr.n, fr.p2, fr.p3, fr.numWires, fr.numConstants, fr.numSelectors);
            if (count != uint256(info.numConstraints)) revert InvalidMleVerifierConfiguration();
            fr.count = count;

            // The two large gates are evaluated and reduced inside their linked
            // libraries, which receive the flat wire limbs as calldata bytes; the
            // accumulation step then only applies the filter to `fr.r`.
            if (gateId == GATE_POSEIDON || gateId == GATE_COSET_INTERPOLATION) {
                (bytes memory flatWires, uint256 a0, uint256 a1, uint256 a2) = _libraryArguments(fr);
                if (gateId == GATE_POSEIDON) {
                    (fr.r0, fr.r1, fr.r2) = PoseidonGateExt3.evalPoseidonReduced(flatWires, a0, a1, a2);
                } else {
                    // Present the library with exactly the gate-local wire prefix (the
                    // bound against the full vector was enforced in `_gateBounds`) by
                    // temporarily shortening the flat buffer's length word.
                    uint256 fullLength = flatWires.length;
                    uint256 prefixLength = requiredWires * 0x60;
                    assembly ("memory-safe") {
                        mstore(flatWires, prefixLength)
                    }
                    (fr.r0, fr.r1, fr.r2) =
                        CosetInterpolationGateExt3.evalCosetReduced(flatWires, fr.n, fr.p2, a0, a1, a2);
                    assembly ("memory-safe") {
                        mstore(flatWires, fullLength)
                    }
                }
                _evalAndAccumulate(fr);
            } else {
                _evalAndAccumulate(fr);
            }
        }
    }

    function _libraryArguments(Frame memory fr)
        private
        pure
        returns (bytes memory flatWires, uint256 a0, uint256 a1, uint256 a2)
    {
        assembly ("memory-safe") {
            flatWires := mload(add(fr, 0x280))
            let ap := mload(add(fr, 0x80))
            a0 := mload(ap)
            a1 := mload(add(ap, 0x20))
            a2 := mload(add(ap, 0x40))
        }
    }

    /// @dev Copy an Fp3 vector into three contiguous words per element.
    function _flatten(GoldilocksExt3.Ext3[] memory values) private pure returns (bytes memory flat) {
        uint256 count = values.length;
        assembly ("memory-safe") {
            flat := mload(0x40)
            let dst := add(flat, 0x20)
            mstore(flat, mul(count, 0x60))
            let src := add(values, 0x20)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let e := mload(add(src, shl(5, i)))
                mstore(dst, mload(e))
                mstore(add(dst, 0x20), mload(add(e, 0x20)))
                mstore(add(dst, 0x40), mload(add(e, 0x40)))
                dst := add(dst, 0x60)
            }
            mstore(0x40, dst)
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

    /// @dev Per-gate wire/constant bounds for the dispatch, and the exact number of
    /// constraints the gate produces. Short inputs fail with `InvalidMleProof` exactly as
    /// the per-gate evaluators did (reads that previously surfaced as a Solidity
    /// out-of-bounds panic now fail the same way); descriptor-shape faults remain
    /// `InvalidMleVerifierConfiguration`. Both are unreachable after
    /// `_validateConfiguration`, which bounds every requirement by the circuit widths.
    function _gateBounds(
        uint256 gateId,
        uint256 n,
        uint256 p2,
        uint256 p3,
        uint256 numWires,
        uint256 numConstants,
        uint256 constantOffset
    ) private pure returns (uint256 count, uint256 requiredWires) {
        uint256 requiredConstants;
        if (gateId == GATE_NOOP) {
            return (0, 0);
        } else if (gateId == GATE_CONSTANT) {
            count = n;
            requiredWires = n;
            requiredConstants = constantOffset + n;
        } else if (gateId == GATE_PUBLIC_INPUT) {
            count = 4;
            requiredWires = 4;
        } else if (gateId == GATE_ARITHMETIC) {
            count = n;
            requiredWires = 4 * n;
            requiredConstants = constantOffset + 2;
        } else if (gateId == GATE_POSEIDON) {
            count = PoseidonGateExt3.POSEIDON_CONSTRAINTS;
            requiredWires = PoseidonGateExt3.POSEIDON_WIRES;
        } else if (gateId == GATE_POSEIDON_MDS) {
            count = 24;
            requiredWires = 48;
        } else if (gateId == GATE_ARITHMETIC_EXT) {
            count = 2 * n;
            requiredWires = 8 * n;
            requiredConstants = constantOffset + 2;
        } else if (gateId == GATE_MUL_EXT) {
            count = 2 * n;
            requiredWires = 6 * n;
            requiredConstants = constantOffset + 1;
        } else if (gateId == GATE_EXPONENTIATION) {
            count = n + 1;
            requiredWires = 2 * n + 2;
        } else if (gateId == GATE_BASE_SUM) {
            if (p2 == 0 || p2 >= P) revert InvalidMleProof();
            count = n + 1;
            requiredWires = n + 1;
        } else if (gateId == GATE_REDUCING) {
            if (n == 0) revert InvalidMleProof();
            count = 2 * n;
            requiredWires = 4 + 3 * n;
        } else if (gateId == GATE_REDUCING_EXT) {
            if (n == 0) revert InvalidMleProof();
            count = 2 * n;
            requiredWires = 4 + 4 * n;
        } else if (gateId == GATE_RANDOM_ACCESS) {
            // The list scratch holds 2^bits Ext3 slots; the gate validator already bounds `bits`.
            if (n > 16) revert InvalidMleVerifierConfiguration();
            uint256 vectorSize = uint256(1) << n;
            requiredWires = (2 + vectorSize) * p2 + p3 + p2 * n;
            requiredConstants = constantOffset + p3;
            count = p2 * (n + 2) + p3;
        } else if (gateId == GATE_COSET_INTERPOLATION) {
            uint256 points = uint256(1) << n;
            uint256 intermediates = (points - 2) / (p2 - 1);
            requiredWires = 7 + 2 * points + 4 * intermediates;
            // The gate-local prefix must exist; the library checks its exact shape.
            if (requiredWires > numWires) revert InvalidMleVerifierConfiguration();
            return (4 + 4 * intermediates, requiredWires);
        } else {
            revert InvalidMleVerifierConfiguration();
        }
        if (requiredWires > numWires || requiredConstants > numConstants) revert InvalidMleProof();
    }

    /// @dev Selector filter `prod_{other in group, other != row} (other - s) * (UNUSED - s)?`
    /// into `fr.f0..f2`, where `s` is the gate's selector constant.
    function _computeFilter(Frame memory fr, GateInfoV2 calldata info, bool manySelectors) private pure {
        uint256 groupStart = uint256(info.groupStart);
        uint256 groupEnd = uint256(info.groupEnd);
        uint256 rowIndex = uint256(info.gateRowIndex);
        uint256 selectorIndex = uint256(info.selectorIndex);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                // Operands are below 2^64 (canonical limbs, or p for a negated zero), so every
                // limb sum of products is below 2^131 and is reduced exactly once.
                let p := 0xFFFFFFFF00000001
                r0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), p)
                r1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), p)
                r2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), p)
            }
            let p := 0xFFFFFFFF00000001
            let sp := add(mload(add(fr, 0x20)), mul(selectorIndex, 0x60))
            // Negated selector limbs, parked in the (not yet used) fr.r slots; `p` stands
            // for zero and every use below is an operand of mulmod/addmod, which reduce it.
            let np := add(fr, 0x1c0)
            mstore(np, sub(p, mload(sp)))
            mstore(add(np, 0x20), sub(p, mload(add(sp, 0x20))))
            mstore(add(np, 0x40), sub(p, mload(add(sp, 0x40))))
            let f0 := 1
            let f1 := 0
            let f2 := 0
            for { let other := groupStart } lt(other, groupEnd) { other := add(other, 1) } {
                if iszero(eq(other, rowIndex)) {
                    f0, f1, f2 :=
                        mul3(f0, f1, f2, addmod(other, mload(np), p), mload(add(np, 0x20)), mload(add(np, 0x40)))
                }
            }
            if manySelectors {
                f0, f1, f2 :=
                    mul3(f0, f1, f2, addmod(0xFFFFFFFF, mload(np), p), mload(add(np, 0x20)), mload(add(np, 0x40)))
            }
            mstore(add(fr, 0x160), f0)
            mstore(add(fr, 0x180), f1)
            mstore(add(fr, 0x1a0), f2)
        }
    }

    /// @dev Evaluate the current gate of `fr` (unless it is a no-op or was already reduced by
    /// a linked library), reduce its constraints with alpha, and accumulate
    /// `filter * reduced` into `fr.acc`.
    function _evalAndAccumulate(Frame memory fr) private pure {
        uint256 invalidProofSelector = uint32(InvalidMleProof.selector);
        uint256 invalidConfigurationSelector = uint32(InvalidMleVerifierConfiguration.selector);
        assembly ("memory-safe") {
            // ------------------------------------------------------------ Fp3 helpers
            function ld(a) -> x0, x1, x2 {
                x0 := mload(a)
                x1 := mload(add(a, 0x20))
                x2 := mload(add(a, 0x40))
            }
            function st(a, x0, x1, x2) {
                mstore(a, x0)
                mstore(add(a, 0x20), x1)
                mstore(add(a, 0x40), x2)
            }
            function mul3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                // Operands are below 2^64 (canonical limbs, or p for a negated zero), so every
                // limb sum of products is below 2^131 and is reduced exactly once.
                let p := 0xFFFFFFFF00000001
                r0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), p)
                r1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), p)
                r2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), p)
            }
            function sq3(a0, a1, a2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                r0 := mod(add(mul(a0, a0), shl(2, mul(a1, a2))), p)
                r1 := mod(shl(1, add(mul(a0, a1), mul(a2, a2))), p)
                r2 := mod(add(shl(1, mul(a0, a2)), mul(a1, a1)), p)
            }
            // mem[a] * mem[b]
            function mul3p(a, b) -> r0, r1, r2 {
                let a0, a1, a2 := ld(a)
                let b0, b1, b2 := ld(b)
                r0, r1, r2 := mul3(a0, a1, a2, b0, b1, b2)
            }
            // mem[o] := mem[a] - mem[b]
            function subp(o, a, b) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), sub(p, mload(b)), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), sub(p, mload(add(b, 0x20))), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), sub(p, mload(add(b, 0x40))), p))
            }
            // mem[o] := (a0, a1, a2) - mem[b]
            function subst(o, a0, a1, a2, b) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(a0, sub(p, mload(b)), p))
                mstore(add(o, 0x20), addmod(a1, sub(p, mload(add(b, 0x20))), p))
                mstore(add(o, 0x40), addmod(a2, sub(p, mload(add(b, 0x40))), p))
            }
            // mem[o] += mem[b]
            function addp(o, b) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(o), mload(b), p))
                mstore(add(o, 0x20), addmod(mload(add(o, 0x20)), mload(add(b, 0x20)), p))
                mstore(add(o, 0x40), addmod(mload(add(o, 0x40)), mload(add(b, 0x40)), p))
            }
            // Quadratic-extension product (t^2 = 7) of two Ext2 records of six words:
            // (a0 + a1 t)(b0 + b1 t) = (a0 b0 + 7 a1 b1) + (a0 b1 + a1 b0) t, computed with
            // Karatsuba's three Fp3 products: m0 = a0 b0, m1 = a1 b1, m2 = (a0 + a1)(b0 + b1),
            // c0 = m0 + 7 m1, c1 = m2 - m0 - m1 (an identity in the ring, so the field values
            // are the same as the four-product form). `o` must not alias `a` or `b`.
            function q2mul(a, b, o) {
                let p := 0xFFFFFFFF00000001
                let x0, x1, x2 := mul3p(a, b)
                let y0, y1, y2 := mul3p(add(a, 0x60), add(b, 0x60))
                mstore(o, addmod(x0, mulmod(y0, 7, p), p))
                mstore(add(o, 0x20), addmod(x1, mulmod(y1, 7, p), p))
                mstore(add(o, 0x40), addmod(x2, mulmod(y2, 7, p), p))
                // park m0 + m1 in the c1 slot
                mstore(add(o, 0x60), addmod(x0, y0, p))
                mstore(add(o, 0x80), addmod(x1, y1, p))
                mstore(add(o, 0xa0), addmod(x2, y2, p))
                x0, x1, x2 :=
                    mul3(
                    addmod(mload(a), mload(add(a, 0x60)), p),
                    addmod(mload(add(a, 0x20)), mload(add(a, 0x80)), p),
                    addmod(mload(add(a, 0x40)), mload(add(a, 0xa0)), p),
                    addmod(mload(b), mload(add(b, 0x60)), p),
                    addmod(mload(add(b, 0x20)), mload(add(b, 0x80)), p),
                    addmod(mload(add(b, 0x40)), mload(add(b, 0xa0)), p)
                )
                mstore(add(o, 0x60), addmod(x0, sub(p, mload(add(o, 0x60))), p))
                mstore(add(o, 0x80), addmod(x1, sub(p, mload(add(o, 0x80))), p))
                mstore(add(o, 0xa0), addmod(x2, sub(p, mload(add(o, 0xa0))), p))
            }
            function alloc(size) -> ptr {
                ptr := mload(0x40)
                mstore(0x40, add(ptr, size))
            }
            function fail(selector) {
                mstore(0, shl(224, selector))
                revert(0, 4)
            }

            // ------------------------------------------------------------ gate bodies
            // `w`: flat wire limbs, `c`: flat local constants (after the selector
            // columns), `k`: constraint buffer. Every body writes exactly `count`
            // constraints in canonical Plonky2 order.

            // Plonky2 `ConstantGate`: constants[i] - wires[i].
            function gConstant(w, c, k, n) {
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    subp(k, c, w)
                    w := add(w, 0x60)
                    c := add(c, 0x60)
                    k := add(k, 0x60)
                }
            }

            // Plonky2 `PublicInputGate`: wires[i] - hash[i] with the hash limb embedded in c0.
            function gPublicInput(w, k, h, sel) {
                let p := 0xFFFFFFFF00000001
                for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                    let hv := mload(add(h, shl(5, i)))
                    if iszero(lt(hv, p)) { fail(sel) }
                    mstore(k, addmod(mload(w), sub(p, hv), p))
                    mstore(add(k, 0x20), mload(add(w, 0x20)))
                    mstore(add(k, 0x40), mload(add(w, 0x40)))
                    w := add(w, 0x60)
                    k := add(k, 0x60)
                }
            }

            // Plonky2 `ArithmeticGate`: w[4i+3] - (c0 * w[4i] * w[4i+1] + c1 * w[4i+2]).
            function gArithmetic(w, c, k, n) {
                let p := 0xFFFFFFFF00000001
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    let m0, m1, m2 := mul3p(w, add(w, 0x60))
                    let c0, c1, c2 := ld(c)
                    m0, m1, m2 := mul3(c0, c1, c2, m0, m1, m2)
                    let y0, y1, y2 := mul3p(add(c, 0x60), add(w, 0xc0))
                    let dp := add(w, 0x120)
                    mstore(k, addmod(mload(dp), sub(p, addmod(m0, y0, p)), p))
                    mstore(add(k, 0x20), addmod(mload(add(dp, 0x20)), sub(p, addmod(m1, y1, p)), p))
                    mstore(add(k, 0x40), addmod(mload(add(dp, 0x40)), sub(p, addmod(m2, y2, p)), p))
                    w := add(w, 0x180)
                    k := add(k, 0x60)
                }
            }

            // Plonky2 `ArithmeticExtensionGate` over the quadratic extension (W = 7):
            // D - (c0 * (A (x) B) + c1 * C) per operation, with A, B, C, D Ext2 records.
            function gArithmeticExt(w, c, k, n) {
                let p := 0xFFFFFFFF00000001
                let t := alloc(0xc0)
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    q2mul(w, add(w, 0xc0), t)
                    for { let j := 0 } lt(j, 0xc0) { j := add(j, 0x60) } {
                        let m0, m1, m2 := mul3p(add(t, j), c)
                        let y0, y1, y2 := mul3p(add(add(w, 0x180), j), add(c, 0x60))
                        let dp := add(add(w, 0x240), j)
                        let o := add(k, j)
                        mstore(o, addmod(mload(dp), sub(p, addmod(m0, y0, p)), p))
                        mstore(add(o, 0x20), addmod(mload(add(dp, 0x20)), sub(p, addmod(m1, y1, p)), p))
                        mstore(add(o, 0x40), addmod(mload(add(dp, 0x40)), sub(p, addmod(m2, y2, p)), p))
                    }
                    w := add(w, 0x300)
                    k := add(k, 0xc0)
                }
            }

            // Plonky2 `MulExtensionGate`: D - c0 * (A (x) B) per operation.
            function gMulExt(w, c, k, n) {
                let p := 0xFFFFFFFF00000001
                let t := alloc(0xc0)
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    q2mul(w, add(w, 0xc0), t)
                    for { let j := 0 } lt(j, 0xc0) { j := add(j, 0x60) } {
                        let m0, m1, m2 := mul3p(add(t, j), c)
                        let dp := add(add(w, 0x180), j)
                        let o := add(k, j)
                        mstore(o, addmod(mload(dp), sub(p, m0), p))
                        mstore(add(o, 0x20), addmod(mload(add(dp, 0x20)), sub(p, m1), p))
                        mstore(add(o, 0x40), addmod(mload(add(dp, 0x40)), sub(p, m2), p))
                    }
                    w := add(w, 0x240)
                    k := add(k, 0xc0)
                }
            }

            // Plonky2 `ExponentiationGate`: wires are [base, bits (MSB first at 1..bits),
            // claimed output at 1 + bits, intermediates from 2 + bits].
            function gExponentiation(w, k, bits) {
                let p := 0xFFFFFFFF00000001
                let b0, b1, b2 := ld(w)
                let interm := add(w, mul(add(2, bits), 0x60))
                for { let i := 0 } lt(i, bits) { i := add(i, 1) } {
                    // previous = i == 0 ? 1 : intermediate[i-1]^2
                    let v0 := 1
                    let v1 := 0
                    let v2 := 0
                    if i {
                        v0, v1, v2 := ld(add(interm, mul(sub(i, 1), 0x60)))
                        v0, v1, v2 := sq3(v0, v1, v2)
                    }
                    // multiplier = bit * base + (1 - bit)
                    let t0, t1, t2 := ld(add(w, mul(sub(bits, i), 0x60)))
                    let m0, m1, m2 := mul3(t0, t1, t2, b0, b1, b2)
                    m0 := addmod(m0, addmod(1, sub(p, t0), p), p)
                    m1 := addmod(m1, sub(p, t1), p)
                    m2 := addmod(m2, sub(p, t2), p)
                    v0, v1, v2 := mul3(v0, v1, v2, m0, m1, m2)
                    subst(add(k, mul(i, 0x60)), v0, v1, v2, add(interm, mul(i, 0x60)))
                }
                // claimed output (wire 1 + bits) - last intermediate (wire 2 + bits + bits - 1)
                subp(add(k, mul(bits, 0x60)), add(w, mul(add(1, bits), 0x60)), add(w, mul(add(1, shl(1, bits)), 0x60)))
            }

            // Plonky2 `BaseSumGate<base>`: sum_i w[i+1] base^i - w[0], then one range product
            // prod_{v<base} (w[i+1] - v) per limb.
            function gBaseSum(w, k, limbs, base) {
                let p := 0xFFFFFFFF00000001
                let s0 := 0
                let s1 := 0
                let s2 := 0
                for { let i := limbs } gt(i, 0) { i := sub(i, 1) } {
                    let lp := add(w, mul(i, 0x60))
                    s0 := addmod(mulmod(s0, base, p), mload(lp), p)
                    s1 := addmod(mulmod(s1, base, p), mload(add(lp, 0x20)), p)
                    s2 := addmod(mulmod(s2, base, p), mload(add(lp, 0x40)), p)
                }
                subst(k, s0, s1, s2, w)
                for { let i := 1 } iszero(gt(i, limbs)) { i := add(i, 1) } {
                    // (w - v) subtracts the base scalar from limb 0 only. The product
                    // starts at 1 * (w - 0) = w exactly, so the loop begins at v = 1.
                    let l0, l1, l2 := ld(add(w, mul(i, 0x60)))
                    let r0 := l0
                    let r1 := l1
                    let r2 := l2
                    for { let v := 1 } lt(v, base) { v := add(v, 1) } {
                        r0, r1, r2 := mul3(r0, r1, r2, addmod(l0, sub(p, v), p), l1, l2)
                    }
                    st(add(k, mul(i, 0x60)), r0, r1, r2)
                }
            }

            // Plonky2 `ReducingGate` / `ReducingExtensionGate`: acc_{i+1} = acc_i * alpha + c_i
            // over the quadratic extension; wires are [out(2), alpha(2), acc0(2), coeffs, accs].
            function gReducing(w, k, n, ext) {
                let t := alloc(0xc0)
                let acc := add(w, 0x180)
                let coeff := add(w, 0x240)
                let next := add(coeff, mul(n, mul(add(1, ext), 0x60)))
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    // alpha is the Ext2 record at wires 2..4
                    q2mul(acc, add(w, 0xc0), t)
                    addp(t, coeff)
                    if ext { addp(add(t, 0x60), add(coeff, 0x60)) }
                    // The final accumulator is the gate output at wires 0..2.
                    if eq(add(i, 1), n) { next := w }
                    subp(k, t, next)
                    subp(add(k, 0x60), add(t, 0x60), add(next, 0x60))
                    acc := next
                    next := add(next, 0xc0)
                    coeff := add(coeff, mul(add(1, ext), 0x60))
                    k := add(k, 0xc0)
                }
            }

            // Plonky2 `RandomAccessGate`: per copy, `bits` booleanity constraints, the index
            // reconstruction sum_j bit_j 2^j - index, and the multilinear selection of the
            // claimed element, followed by the gate's extra constant constraints.
            function gRandomAccess(w, c, k, bits, copies, extra) {
                let p := 0xFFFFFFFF00000001
                let vectorSize := shl(bits, 1)
                // Extra constant constraints come last in the output; write them first so
                // that `c` and `extra` are dead during the copy loop.
                {
                    let kx := add(k, mul(mul(copies, add(bits, 2)), 0x60))
                    let ep := add(w, mul(mul(add(2, vectorSize), copies), 0x60))
                    for { let e := 0 } lt(e, extra) { e := add(e, 1) } {
                        subp(kx, c, ep)
                        c := add(c, 0x60)
                        ep := add(ep, 0x60)
                        kx := add(kx, 0x60)
                    }
                }
                // bit wires start after the routed wires: (2 + vectorSize) * copies + extra
                let bs := add(w, mul(add(mul(add(2, vectorSize), copies), extra), 0x60))
                let buf := alloc(mul(vectorSize, 0x60))
                for { let copy := 0 } lt(copy, copies) { copy := add(copy, 1) } {
                    let cs := add(w, mul(mul(add(2, vectorSize), copy), 0x60))
                    // booleanity: bit * (bit - 1)
                    for { let b := 0 } lt(b, bits) { b := add(b, 1) } {
                        let x0, x1, x2 := ld(add(bs, mul(b, 0x60)))
                        x0, x1, x2 := mul3(x0, x1, x2, addmod(x0, sub(p, 1), p), x1, x2)
                        st(k, x0, x1, x2)
                        k := add(k, 0x60)
                    }
                    // reconstructed index: Horner from the most significant bit
                    let a0 := 0
                    let a1 := 0
                    let a2 := 0
                    for { let b := bits } gt(b, 0) { b := sub(b, 1) } {
                        let bp := add(bs, mul(sub(b, 1), 0x60))
                        a0 := addmod(addmod(a0, a0, p), mload(bp), p)
                        a1 := addmod(addmod(a1, a1, p), mload(add(bp, 0x20)), p)
                        a2 := addmod(addmod(a2, a2, p), mload(add(bp, 0x40)), p)
                    }
                    subst(k, a0, a1, a2, cs)
                    k := add(k, 0x60)
                    // multilinear selection over the list
                    mcopy(buf, add(cs, 0xc0), mul(vectorSize, 0x60))
                    let len := vectorSize
                    for { let b := 0 } lt(b, bits) { b := add(b, 1) } {
                        let t0, t1, t2 := ld(add(bs, mul(b, 0x60)))
                        let half := shr(1, len)
                        for { let j := 0 } lt(j, half) { j := add(j, 1) } {
                            let even := add(buf, mul(j, 0xc0))
                            let odd := add(even, 0x60)
                            let d0 := addmod(mload(odd), sub(p, mload(even)), p)
                            let d1 := addmod(mload(add(odd, 0x20)), sub(p, mload(add(even, 0x20))), p)
                            let d2 := addmod(mload(add(odd, 0x40)), sub(p, mload(add(even, 0x40))), p)
                            d0, d1, d2 := mul3(t0, t1, t2, d0, d1, d2)
                            let dst := add(buf, mul(j, 0x60))
                            mstore(dst, addmod(mload(even), d0, p))
                            mstore(add(dst, 0x20), addmod(mload(add(even, 0x20)), d1, p))
                            mstore(add(dst, 0x40), addmod(mload(add(even, 0x40)), d2, p))
                        }
                        len := half
                    }
                    subp(k, buf, add(cs, 0x60))
                    k := add(k, 0x60)
                    bs := add(bs, mul(bits, 0x60))
                }
            }

            // Dense Poseidon MDS on one 12-word limb plane `sp`, using Plonky2's exact
            // integer-FFT factorization of the fixed circulant CIRC =
            // [17,15,41,16,2,28,13,13,39,18,34,20] plus the diagonal coefficient 8 on row 0.
            // Identical to `PoseidonGate._mdsLayerInline`; `t` is a 12-word scratch area.
            function mdsPlane(sp, t) {
                let p := 0xFFFFFFFF00000001
                for { let g := 0 } lt(g, 3) { g := add(g, 1) } {
                    let a := mload(add(sp, mul(g, 0x20)))
                    let b := mload(add(sp, mul(add(g, 3), 0x20)))
                    let c := mload(add(sp, mul(add(g, 6), 0x20)))
                    let d := mload(add(sp, mul(add(g, 9), 0x20)))
                    let base := add(t, mul(g, 0x80))
                    mstore(base, addmod(addmod(a, b, p), addmod(c, d, p), p))
                    mstore(add(base, 0x20), addmod(a, sub(p, c), p))
                    mstore(add(base, 0x40), addmod(d, sub(p, b), p))
                    mstore(add(base, 0x60), addmod(addmod(a, sub(p, b), p), addmod(c, sub(p, d), p), p))
                }
                {
                    let x0 := mload(t)
                    let x1 := mload(add(t, 0x80))
                    let x2 := mload(add(t, 0x100))
                    mstore(t, mod(add(add(shl(4, x0), shl(4, x1)), shl(5, x2)), p))
                    mstore(add(t, 0x80), mod(add(add(shl(5, x0), shl(4, x1)), shl(4, x2)), p))
                    mstore(add(t, 0x100), mod(add(add(shl(4, x0), shl(5, x1)), shl(4, x2)), p))
                }
                {
                    let a := mload(add(t, 0x20))
                    let b := mload(add(t, 0x40))
                    let c := mload(add(t, 0xa0))
                    let d := mload(add(t, 0xc0))
                    let e := mload(add(t, 0x120))
                    let f := mload(add(t, 0x140))
                    mstore(
                        add(t, 0x20),
                        mod(add(add(add(add(add(shl(1, a), b), c), shl(4, d)), e), sub(shl(2, p), shl(2, f))), p)
                    )
                    mstore(
                        add(t, 0x40),
                        mod(sub(add(add(add(shl(1, b), d), shl(2, e)), add(f, mul(17, p))), add(a, shl(4, c))), p)
                    )
                    mstore(
                        add(t, 0xa0),
                        mod(add(add(add(add(shl(1, c), d), e), shl(4, f)), sub(mul(5, p), add(shl(2, a), b))), p)
                    )
                    mstore(
                        add(t, 0xc0),
                        mod(sub(add(add(add(a, shl(1, d)), f), mul(21, p)), add(add(shl(2, b), c), shl(4, e))), p)
                    )
                    mstore(
                        add(t, 0x120),
                        mod(add(add(add(shl(4, a), shl(1, e)), f), sub(mul(6, p), add(add(b, shl(2, c)), d))), p)
                    )
                    mstore(
                        add(t, 0x140),
                        mod(add(add(add(add(a, shl(4, b)), c), shl(1, f)), sub(mul(5, p), add(shl(2, d), e))), p)
                    )
                }
                {
                    let x0 := mload(add(t, 0x60))
                    let x1 := mload(add(t, 0xe0))
                    let x2 := mload(add(t, 0x160))
                    mstore(add(t, 0x60), mod(add(shl(3, x2), sub(mul(3, p), add(x0, shl(1, x1)))), p))
                    mstore(add(t, 0xe0), mod(sub(mul(11, p), add(add(shl(3, x0), x1), shl(1, x2))), p))
                    mstore(add(t, 0x160), mod(add(shl(1, x0), sub(mul(9, p), add(shl(3, x1), x2))), p))
                }
                for { let g := 0 } lt(g, 3) { g := add(g, 1) } {
                    let base := add(t, mul(g, 0x80))
                    let v0 := mload(base)
                    let v1r := mload(add(base, 0x20))
                    let v1i := mload(add(base, 0x40))
                    let v2 := mload(add(base, 0x60))
                    let z0 := addmod(v0, v2, p)
                    let z1 := addmod(v0, sub(p, v2), p)
                    let out0 := addmod(z0, v1r, p)
                    if iszero(g) { out0 := addmod(out0, mulmod(mload(sp), 8, p), p) }
                    mstore(add(sp, mul(g, 0x20)), out0)
                    mstore(add(sp, mul(add(g, 3), 0x20)), addmod(z1, sub(p, v1i), p))
                    mstore(add(sp, mul(add(g, 6), 0x20)), addmod(z0, sub(p, v1r), p))
                    mstore(add(sp, mul(add(g, 9), 0x20)), addmod(z1, v1i, p))
                }
            }

            // Plonky2 `PoseidonMdsGate`: twelve Ext2 inputs (wires 0..24), twelve Ext2 outputs
            // (wires 24..48); constraint pair r is output_r - (MDS * input)_r. The matrix has
            // base-field coefficients, so it acts on each of the six limb planes separately.
            function gPoseidonMds(w, k) {
                let p := 0xFFFFFFFF00000001
                let planes := alloc(0xa80)
                let t := add(planes, 0x900)
                for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                    let wp := add(w, mul(i, 0xc0))
                    let dst := add(planes, shl(5, i))
                    for { let q := 0 } lt(q, 6) { q := add(q, 1) } {
                        mstore(add(dst, mul(q, 0x180)), mload(add(wp, mul(q, 0x20))))
                    }
                }
                for { let q := 0 } lt(q, 6) { q := add(q, 1) } { mdsPlane(add(planes, mul(q, 0x180)), t) }
                let op := add(w, mul(24, 0x60))
                for { let r := 0 } lt(r, 12) { r := add(r, 1) } {
                    let src := add(planes, shl(5, r))
                    for { let q := 0 } lt(q, 6) { q := add(q, 1) } {
                        let off := mul(q, 0x20)
                        mstore(add(k, off), addmod(mload(add(op, off)), sub(p, mload(add(src, mul(q, 0x180)))), p))
                    }
                    op := add(op, 0xc0)
                    k := add(k, 0xc0)
                }
            }

            // Horner over the `count` constraints at `k`:
            // terms[0] + alpha*(terms[1] + alpha*(terms[2] + ...)), alpha read from `ap`.
            function horner(k, count, ap) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                if count {
                    let kp := add(k, mul(sub(count, 1), 0x60))
                    r0, r1, r2 := ld(kp)
                    for {} gt(kp, k) {} {
                        kp := sub(kp, 0x60)
                        // r * alpha + term, with the term folded into the unreduced limb sums
                        // (everything below 2^64, sums below 2^132).
                        let a0 := mload(ap)
                        let a1 := mload(add(ap, 0x20))
                        let a2 := mload(add(ap, 0x40))
                        let n0 := mod(add(add(mul(r0, a0), shl(1, add(mul(r1, a2), mul(r2, a1)))), mload(kp)), p)
                        let n1 :=
                            mod(add(add(add(mul(r0, a1), mul(r1, a0)), shl(1, mul(r2, a2))), mload(add(kp, 0x20))), p)
                        r2 := mod(add(add(add(mul(r0, a2), mul(r1, a1)), mul(r2, a0)), mload(add(kp, 0x40))), p)
                        r0 := n0
                        r1 := n1
                    }
                }
            }
            // fr.acc += fr.filter * (r0, r1, r2)
            function accumulate(fr_, r0, r1, r2) {
                let p := 0xFFFFFFFF00000001
                r0, r1, r2 := mul3(mload(add(fr_, 0x160)), mload(add(fr_, 0x180)), mload(add(fr_, 0x1a0)), r0, r1, r2)
                mstore(add(fr_, 0x220), addmod(mload(add(fr_, 0x220)), r0, p))
                mstore(add(fr_, 0x240), addmod(mload(add(fr_, 0x240)), r1, p))
                mstore(add(fr_, 0x260), addmod(mload(add(fr_, 0x260)), r2, p))
            }

            // ------------------------------------------------------------ dispatch
            // Gates 0 (no constraints), 4 and 13 (reduced by their libraries into fr.r)
            // produce nothing here. Only `w`, `k`, `gateId`, `n` stay live across a body.
            {
                let w := mload(fr)
                let k := mload(add(fr, 0x40))
                let gateId := mload(add(fr, 0xc0))
                let n := mload(add(fr, 0xe0))
                switch gateId
                case 0 {}
                case 1 { gConstant(w, mload(add(fr, 0xa0)), k, n) }
                case 2 { gPublicInput(w, k, mload(add(fr, 0x60)), invalidProofSelector) }
                case 3 { gArithmetic(w, mload(add(fr, 0xa0)), k, n) }
                case 4 {}
                case 5 { gPoseidonMds(w, k) }
                case 6 { gArithmeticExt(w, mload(add(fr, 0xa0)), k, n) }
                case 7 { gMulExt(w, mload(add(fr, 0xa0)), k, n) }
                case 8 { gExponentiation(w, k, n) }
                case 9 { gBaseSum(w, k, n, mload(add(fr, 0x100))) }
                case 10 { gReducing(w, k, n, 0) }
                case 11 { gReducing(w, k, n, 1) }
                case 12 { gRandomAccess(w, mload(add(fr, 0xa0)), k, n, mload(add(fr, 0x100)), mload(add(fr, 0x120))) }
                case 13 {}
                default { fail(invalidConfigurationSelector) }
            }
            // reduced value: zero for the no-op gate, the library result for 4 and 13,
            // otherwise Horner over the constraints just written.
            let r0 := 0
            let r1 := 0
            let r2 := 0
            switch mload(add(fr, 0xc0))
            case 0 {}
            case 4 {
                r0 := mload(add(fr, 0x1c0))
                r1 := mload(add(fr, 0x1e0))
                r2 := mload(add(fr, 0x200))
            }
            case 13 {
                r0 := mload(add(fr, 0x1c0))
                r1 := mload(add(fr, 0x1e0))
                r2 := mload(add(fr, 0x200))
            }
            default { r0, r1, r2 := horner(mload(add(fr, 0x40)), mload(add(fr, 0x140)), mload(add(fr, 0x80))) }
            accumulate(fr, r0, r1, r2)
        }
    }

    function _validateCanonical(GoldilocksExt3.Ext3[] memory values) private pure {
        for (uint256 i = 0; i < values.length; ++i) {
            _checkCanonical(values[i]);
        }
    }

    function _checkCanonical(GoldilocksExt3.Ext3 memory value) private pure {
        if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
            revert InvalidMleProof();
        }
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
