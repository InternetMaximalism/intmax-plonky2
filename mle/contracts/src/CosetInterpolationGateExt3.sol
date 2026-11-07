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
///      Both entry points share one assembly core over a flat limb buffer (three words per
///      Fp3 value, six per Ext2 value) and the gate-local barycentric tables loaded once.
library CosetInterpolationGateExt3 {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;
    uint256 private constant INNER_EXTENSION_NONRESIDUE = INNER_EXTENSION_NON_RESIDUE_V2;

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
        Layout memory layout = _validateLayout(wires.length, subgroupBits, degree);
        for (uint256 i = 0; i < wires.length; ++i) {
            GoldilocksExt3.Ext3 memory value = wires[i];
            if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
                revert InvalidMleProof();
            }
        }
        uint256 count = 4 + 4 * layout.intermediates;
        bytes memory flat = new bytes(wires.length * 0x60);
        bytes memory constraints = new bytes(count * 0x60);
        assembly ("memory-safe") {
            let dst := add(flat, 0x20)
            let src := add(wires, 0x20)
            for { let i := 0 } lt(i, mload(wires)) { i := add(i, 1) } {
                let e := mload(add(src, shl(5, i)))
                mstore(dst, mload(e))
                mstore(add(dst, 0x20), mload(add(e, 0x20)))
                mstore(add(dst, 0x40), mload(add(e, 0x40)))
                dst := add(dst, 0x60)
            }
        }
        _evalFlat(flat, constraints, layout, subgroupBits, degree);
        output = new GoldilocksExt3.Ext3[](count);
        for (uint256 i = 0; i < count; ++i) {
            GoldilocksExt3.Ext3 memory value = output[i];
            assembly ("memory-safe") {
                let src := add(add(constraints, 0x20), mul(i, 0x60))
                mstore(value, mload(src))
                mstore(add(value, 0x20), mload(add(src, 0x20)))
                mstore(add(value, 0x40), mload(add(src, 0x40)))
            }
        }
    }

    /// @notice Evaluate gate id 13 on the gate-local wire prefix given as flat canonical Fp3
    ///         limbs (exactly `7 + 2*N + 4*m` wires of three 32-byte words) and return
    ///         `sum_i alpha^i * constraint_i` over its `4 + 4*m` constraints.
    /// @dev Called by `Plonky2GateEvaluatorExt3` through a DELEGATECALL; applies the same
    ///      shape, canonical-limb and constant-table checks as `evalCoset`.
    function evalCosetReduced(
        bytes calldata wires,
        uint256 subgroupBits,
        uint256 degree,
        uint256 alpha0,
        uint256 alpha1,
        uint256 alpha2
    ) external pure returns (uint256 red0, uint256 red1, uint256 red2) {
        if (wires.length % 0x60 != 0) revert InvalidMleProof();
        Layout memory layout = _validateLayout(wires.length / 0x60, subgroupBits, degree);
        bytes memory flat = wires;
        uint256 count = 4 + 4 * layout.intermediates;
        bytes memory constraints = new bytes(count * 0x60);
        bool canonical = true;
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let end := add(add(flat, 0x20), mload(flat))
            for { let ptr := add(flat, 0x20) } lt(ptr, end) { ptr := add(ptr, 0x20) } {
                if iszero(lt(mload(ptr), p)) { canonical := 0 }
            }
        }
        if (!canonical) revert InvalidMleProof();
        _evalFlat(flat, constraints, layout, subgroupBits, degree);
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let k := add(constraints, 0x20)
            let kp := add(k, mul(sub(count, 1), 0x60))
            red0 := mload(kp)
            red1 := mload(add(kp, 0x20))
            red2 := mload(add(kp, 0x40))
            for {} gt(kp, k) {} {
                kp := sub(kp, 0x60)
                // r * alpha + term with the term folded into the unreduced limb sums
                // (everything below 2^64, sums below 2^132).
                let n0 :=
                    mod(add(add(mul(red0, alpha0), shl(1, add(mul(red1, alpha2), mul(red2, alpha1)))), mload(kp)), p)
                let n1 :=
                    mod(
                        add(
                            add(add(mul(red0, alpha1), mul(red1, alpha0)), shl(1, mul(red2, alpha2))),
                            mload(add(kp, 0x20))
                        ),
                        p
                    )
                red2 := mod(
                    add(add(add(mul(red0, alpha2), mul(red1, alpha1)), mul(red2, alpha0)), mload(add(kp, 0x40))),
                    p
                )
                red0 := n0
                red1 := n1
            }
        }
    }

    function _validateLayout(uint256 wireCount, uint256 subgroupBits, uint256 degree)
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
        if (wireCount != layout.shiftedPointIndex + 2) revert InvalidMleProof();

        // Eagerly touch the canonical table as a defense against the supported-range
        // guard drifting away from the checked-in constants.
        if (CosetInterpolationConstants.weight(subgroupBits, 0) >= P) revert InvalidMleProof();
    }

    function _subgroup(uint256 subgroupBits) private pure returns (bytes memory) {
        if (subgroupBits == 1) return CosetInterpolationConstants.SUBGROUP_1;
        if (subgroupBits == 2) return CosetInterpolationConstants.SUBGROUP_2;
        if (subgroupBits == 3) return CosetInterpolationConstants.SUBGROUP_3;
        if (subgroupBits == 4) return CosetInterpolationConstants.SUBGROUP_4;
        if (subgroupBits == 5) return CosetInterpolationConstants.SUBGROUP_5;
        revert InvalidMleProof();
    }

    function _weights(uint256 subgroupBits) private pure returns (bytes memory) {
        if (subgroupBits == 1) return CosetInterpolationConstants.WEIGHTS_1;
        if (subgroupBits == 2) return CosetInterpolationConstants.WEIGHTS_2;
        if (subgroupBits == 3) return CosetInterpolationConstants.WEIGHTS_3;
        if (subgroupBits == 4) return CosetInterpolationConstants.WEIGHTS_4;
        if (subgroupBits == 5) return CosetInterpolationConstants.WEIGHTS_5;
        revert InvalidMleProof();
    }

    /// @dev Rust `eval_coset_interpolation` over flat limbs: `flat` holds the gate-local
    /// wires, `constraints` receives the `4 + 4*m` constraints in canonical order.
    function _evalFlat(
        bytes memory flat,
        bytes memory constraints,
        Layout memory layout,
        uint256 subgroupBits,
        uint256 degree
    ) private pure {
        bytes memory domain = _subgroup(subgroupBits);
        bytes memory weights = _weights(subgroupBits);
        uint256 points = layout.points;
        // Every index read below is `< points`; the tables hold exactly `points` entries
        // (the bounds check of `CosetInterpolationConstants.readU64`).
        if (domain.length != 8 * points || weights.length != 8 * points) revert InvalidMleProof();
        // The assembly below hard-codes the inner non-residue 7.
        if (INNER_EXTENSION_NONRESIDUE != 7) revert InvalidMleProof();
        uint256 intermediates = layout.intermediates;
        uint256 startIntermediates = layout.startIntermediates;
        uint256 shiftedPointIndex = layout.shiftedPointIndex;
        assembly ("memory-safe") {
            function ld(a) -> x0, x1, x2 {
                x0 := mload(a)
                x1 := mload(add(a, 0x20))
                x2 := mload(add(a, 0x40))
            }
            function mul3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                // Operands are below 2^64 (canonical limbs, or p for a negated zero), so every
                // limb sum of products is below 2^131 and is reduced exactly once.
                let p := 0xFFFFFFFF00000001
                r0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), p)
                r1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), p)
                r2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), p)
            }
            function mul3p(a, b) -> r0, r1, r2 {
                let a0, a1, a2 := ld(a)
                let b0, b1, b2 := ld(b)
                r0, r1, r2 := mul3(a0, a1, a2, b0, b1, b2)
            }
            // mem[o] := mem[a] - mem[b] over one Ext2 record (six words).
            function sub2(o, a, b) {
                let p := 0xFFFFFFFF00000001
                mstore(o, addmod(mload(a), sub(p, mload(b)), p))
                mstore(add(o, 0x20), addmod(mload(add(a, 0x20)), sub(p, mload(add(b, 0x20))), p))
                mstore(add(o, 0x40), addmod(mload(add(a, 0x40)), sub(p, mload(add(b, 0x40))), p))
                mstore(add(o, 0x60), addmod(mload(add(a, 0x60)), sub(p, mload(add(b, 0x60))), p))
                mstore(add(o, 0x80), addmod(mload(add(a, 0x80)), sub(p, mload(add(b, 0x80))), p))
                mstore(add(o, 0xa0), addmod(mload(add(a, 0xa0)), sub(p, mload(add(b, 0xa0))), p))
            }
            // Quadratic-extension product (t^2 = 7) of two Ext2 records with Karatsuba's three
            // Fp3 products: m0 = a0 b0, m1 = a1 b1, m2 = (a0 + a1)(b0 + b1), c0 = m0 + 7 m1,
            // c1 = m2 - m0 - m1 (a ring identity, so the values equal the four-product form).
            // `o` must not alias `a` or `b`.
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
            // State record `sc`:
            //   0x000 term (Ext2)   0x0c0 weighted (Ext2)   0x180 scratch n0 (Ext2)
            //   0x240 scratch n1    0x300 evaluation (Ext2) 0x3c0 product (Ext2)
            //   0x480 shifted point pointer   0x4a0 domain table   0x4c0 weight table
            // Rust `coset_partial_interpolate` over domain indices [start, end):
            //   term       = point - domain[j]
            //   weighted   = value[j] * weight[j]
            //   evaluation = evaluation * term + weighted * product   (old product)
            //   product    = product * term
            function chunk(w, sc, start, end) {
                let p := 0xFFFFFFFF00000001
                for { let j := start } lt(j, end) { j := add(j, 1) } {
                    // term = (pt.c0 - d_j, pt.c1): the base-field point only touches limb 0.
                    {
                        let pt := mload(add(sc, 0x480))
                        mstore(sc, addmod(mload(pt), sub(p, shr(192, mload(add(mload(add(sc, 0x4a0)), mul(j, 8))))), p))
                        mcopy(add(sc, 0x20), add(pt, 0x20), 0xa0)
                    }
                    {
                        let wj := shr(192, mload(add(mload(add(sc, 0x4c0)), mul(j, 8))))
                        let vp := add(w, mul(add(1, shl(1, j)), 0x60))
                        mstore(add(sc, 0xc0), mulmod(mload(vp), wj, p))
                        mstore(add(sc, 0xe0), mulmod(mload(add(vp, 0x20)), wj, p))
                        mstore(add(sc, 0x100), mulmod(mload(add(vp, 0x40)), wj, p))
                        mstore(add(sc, 0x120), mulmod(mload(add(vp, 0x60)), wj, p))
                        mstore(add(sc, 0x140), mulmod(mload(add(vp, 0x80)), wj, p))
                        mstore(add(sc, 0x160), mulmod(mload(add(vp, 0xa0)), wj, p))
                    }
                    q2mul(add(sc, 0x300), sc, add(sc, 0x180))
                    q2mul(add(sc, 0xc0), add(sc, 0x3c0), add(sc, 0x240))
                    {
                        let ev := add(sc, 0x300)
                        mstore(ev, addmod(mload(add(sc, 0x180)), mload(add(sc, 0x240)), p))
                        mstore(add(ev, 0x20), addmod(mload(add(sc, 0x1a0)), mload(add(sc, 0x260)), p))
                        mstore(add(ev, 0x40), addmod(mload(add(sc, 0x1c0)), mload(add(sc, 0x280)), p))
                        mstore(add(ev, 0x60), addmod(mload(add(sc, 0x1e0)), mload(add(sc, 0x2a0)), p))
                        mstore(add(ev, 0x80), addmod(mload(add(sc, 0x200)), mload(add(sc, 0x2c0)), p))
                        mstore(add(ev, 0xa0), addmod(mload(add(sc, 0x220)), mload(add(sc, 0x2e0)), p))
                    }
                    q2mul(add(sc, 0x3c0), sc, add(sc, 0x180))
                    mcopy(add(sc, 0x3c0), add(sc, 0x180), 0xc0)
                }
            }

            let p := 0xFFFFFFFF00000001
            let w := add(flat, 0x20)
            let k := add(constraints, 0x20)
            let sc := mload(0x40)
            mstore(0x40, add(sc, 0x4e0))
            let ev := add(sc, 0x300)
            let pr := add(sc, 0x3c0)
            let shifted := add(w, mul(shiftedPointIndex, 0x60))
            mstore(add(sc, 0x480), shifted)
            mstore(add(sc, 0x4a0), add(domain, 0x20))
            mstore(add(sc, 0x4c0), add(weights, 0x20))

            // Constraint pair 0: evaluation_point - shifted_point * shift.
            {
                let ep := add(w, mul(add(1, shl(1, points)), 0x60))
                for { let j := 0 } lt(j, 0xc0) { j := add(j, 0x60) } {
                    let m0, m1, m2 := mul3p(add(shifted, j), w)
                    let o := add(k, j)
                    mstore(o, addmod(mload(add(ep, j)), sub(p, m0), p))
                    mstore(add(o, 0x20), addmod(mload(add(add(ep, j), 0x20)), sub(p, m1), p))
                    mstore(add(o, 0x40), addmod(mload(add(add(ep, j), 0x40)), sub(p, m2), p))
                }
            }
            // State: evaluation = 0, product = 1, point = shifted.
            for { let l := 0 } lt(l, 0xc0) { l := add(l, 0x20) } {
                mstore(add(ev, l), 0)
                mstore(add(pr, l), 0)
            }
            mstore(pr, 1)
            chunk(w, sc, 0, degree)

            let kp := add(k, 0xc0)
            for { let i := 0 } lt(i, intermediates) { i := add(i, 1) } {
                let ie := add(w, mul(add(startIntermediates, shl(1, i)), 0x60))
                let ip := add(ie, mul(intermediates, 0xc0))
                sub2(kp, ie, ev)
                sub2(add(kp, 0xc0), ip, pr)
                kp := add(kp, 0x180)
                mcopy(ev, ie, 0xc0)
                mcopy(pr, ip, 0xc0)
                let start := add(1, mul(sub(degree, 1), add(i, 1)))
                let end := add(start, sub(degree, 1))
                if gt(end, points) { end := points }
                chunk(w, sc, start, end)
            }
            // Final pair: claimed evaluation - evaluation.
            sub2(kp, add(w, mul(add(1, shl(1, add(points, 1))), 0x60)), ev)
        }
    }
}
