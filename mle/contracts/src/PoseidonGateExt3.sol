// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof} from "./MleProofErrors.sol";
import {PoseidonConstants} from "./PoseidonConstants.sol";

/// @title PoseidonGateExt3
/// @notice Exact Plonky2 Poseidon gate (id 4) constraints over the Goldilocks cubic extension,
///         alpha-reduced in canonical constraint order. Mirrors
///         `mle/src/gate_ext3.rs::eval_poseidon` followed by the Horner reduction of its 123
///         constraints.
/// @dev Called by `Plonky2GateEvaluatorExt3` through a DELEGATECALL. The wires arrive as a flat
///      calldata byte string holding three canonical 32-byte limbs per Fp3 wire, so the
///      boundary copies no struct array and the body reads limbs with `calldataload`.
///
///      Layout and arithmetic:
///       - The 12-element Fp3 state is kept as three 12-word limb planes. Every linear layer of
///         Poseidon has base-field coefficients, so it acts on each plane independently.
///       - The dense MDS layer is Plonky2's exact integer-FFT factorization of the fixed
///         circulant (ported from `PoseidonGate._mdsLayerInline`), applied once per plane. The
///         sparse partial-round matrices and the partial initial matrix accumulate products of
///         canonical 64-bit values unreduced (sums stay far below 2^256) and reduce once.
///       - The S-box `x^7` is two Fp3 squarings and two Fp3 products in registers.
///       - All constraints are written to one contiguous buffer and reduced by Horner's rule.
///
///      Callers must pass canonical limbs (the evaluator validates them, or receives them
///      already validated from the core); subtraction uses `p - x` without re-normalisation.
library PoseidonGateExt3 {
    uint256 internal constant P = 0xFFFFFFFF00000001;
    uint256 internal constant SPONGE_WIDTH = 12;
    uint256 internal constant HALF_N_FULL_ROUNDS = 4;
    uint256 internal constant N_PARTIAL_ROUNDS = 22;

    uint256 internal constant POSEIDON_WIRES = 135;
    uint256 internal constant POSEIDON_CONSTRAINTS = 123;

    uint256 private constant WIRE_SWAP = 24;
    uint256 private constant START_DELTA = 25;
    uint256 private constant START_FULL_0 = 29;
    uint256 private constant START_PARTIAL = 65;
    uint256 private constant START_FULL_1 = 87;

    /// @dev Byte size of one Fp3 wire (three words) and of one limb plane (twelve words).
    uint256 private constant WIRE = 0x60;
    uint256 private constant PLANE = 0x180;

    /// @notice Evaluate gate id 4 on `wires` (flat canonical Fp3 limbs, at least 135 wires) and
    ///         return `sum_i alpha^i * constraint_i` over the 123 constraints.
    function evalPoseidonReduced(bytes calldata wires, uint256 alpha0, uint256 alpha1, uint256 alpha2)
        external
        pure
        returns (uint256 red0, uint256 red1, uint256 red2)
    {
        if (wires.length < POSEIDON_WIRES * WIRE) revert InvalidMleProof();

        bytes memory roundConstants = PoseidonConstants.ALL_ROUND_CONSTANTS;
        bytes memory pfrc = PoseidonConstants.FAST_PARTIAL_FIRST_ROUND_CONSTANT;
        bytes memory prc = PoseidonConstants.FAST_PARTIAL_ROUND_CONSTANTS;
        bytes memory prvs = PoseidonConstants.FAST_PARTIAL_ROUND_VS;
        bytes memory prwh = PoseidonConstants.FAST_PARTIAL_ROUND_W_HATS;
        bytes memory pim = PoseidonConstants.FAST_PARTIAL_ROUND_INITIAL_MATRIX;

        // s: state planes (36 words), r: ping-pong planes (36), t: MDS scratch (12),
        // k: 123 constraints (369 words).
        uint256 w;
        uint256 s;
        uint256 r;
        uint256 t;
        uint256 k;
        assembly ("memory-safe") {
            w := wires.offset
            s := mload(0x40)
            r := add(s, 0x480)
            t := add(r, 0x480)
            k := add(t, 0x180)
            mstore(0x40, add(k, mul(123, 0x60)))
        }

        _swapDelta(w, s, k, t);
        uint256 next = _fullRounds(w, s, t, k, roundConstants, 0, 5);
        s = _partialInit(s, r, pfrc, pim);
        next = _partialRounds(w, s, k, prc, prvs, prwh, next);
        next = _fullRounds(w, s, t, k, roundConstants, 1, next);
        _outputConstraints(w, s, k, next);
        (red0, red1, red2) = _reduce(k, alpha0, alpha1, alpha2);
    }

    /// @dev Constraint 0: swap * (swap - 1). Constraints 1..4: swap * (w[i+4] - w[i]) - delta_i.
    /// State: s[i] = w[i] + delta_i, s[i+4] = w[i+4] - delta_i, s[8..12] = w[8..12].
    function _swapDelta(uint256 w, uint256 s, uint256 k, uint256 t) private pure {
        assembly ("memory-safe") {
            function ext3Mul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                // Operands are below 2^64 (canonical limbs, or p for a negated zero), so every
                // limb sum of products is below 2^131 and is reduced exactly once.
                let p := 0xFFFFFFFF00000001
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), p)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), p)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), p)
            }
            let p := 0xFFFFFFFF00000001
            let sp := add(w, mul(24, 0x60))
            let s0 := calldataload(sp)
            let s1 := calldataload(add(sp, 0x20))
            let s2 := calldataload(add(sp, 0x40))
            let c0, c1, c2 := ext3Mul(s0, s1, s2, addmod(s0, sub(p, 1), p), s1, s2)
            mstore(k, c0)
            mstore(add(k, 0x20), c1)
            mstore(add(k, 0x40), c2)
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                let lp := add(w, mul(i, 0x60))
                let rp := add(lp, 0x180)
                let dp := add(w, mul(add(25, i), 0x60))
                let kp := add(k, mul(add(i, 1), 0x60))
                let lo := add(s, shl(5, i))
                let hi := add(lo, 0x80)
                for { let limb := 0 } lt(limb, 0x60) { limb := add(limb, 0x20) } {
                    let l := calldataload(add(lp, limb))
                    let h := calldataload(add(rp, limb))
                    let d := calldataload(add(dp, limb))
                    let plane := mul(limb, 12)
                    mstore(add(lo, plane), addmod(l, d, p))
                    mstore(add(hi, plane), addmod(h, sub(p, d), p))
                    // (w[i+4] - w[i]) for this limb, consumed by the Fp3 product below.
                    mstore(add(t, limb), addmod(h, sub(p, l), p))
                }
                c0, c1, c2 := ext3Mul(s0, s1, s2, mload(t), mload(add(t, 0x20)), mload(add(t, 0x40)))
                mstore(kp, addmod(c0, sub(p, calldataload(dp)), p))
                mstore(add(kp, 0x20), addmod(c1, sub(p, calldataload(add(dp, 0x20))), p))
                mstore(add(kp, 0x40), addmod(c2, sub(p, calldataload(add(dp, 0x40))), p))
            }
            for { let i := 8 } lt(i, 12) { i := add(i, 1) } {
                let sp2 := add(w, mul(i, 0x60))
                let a := add(s, shl(5, i))
                mstore(a, calldataload(sp2))
                mstore(add(a, 0x180), calldataload(add(sp2, 0x20)))
                mstore(add(a, 0x300), calldataload(add(sp2, 0x40)))
            }
        }
    }

    /// @dev Four full rounds. `half == 0`: round constants 0..3, rounds 1..3 consume the
    /// explicit S-box input wires from 29. `half == 1`: round constants 26..29, every round
    /// consumes the wires from 87. Returns the next constraint index.
    function _fullRounds(
        uint256 w,
        uint256 s,
        uint256 t,
        uint256 k,
        bytes memory roundConstants,
        uint256 half,
        uint256 next
    ) private pure returns (uint256) {
        assembly ("memory-safe") {
            function ext3Mul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                // Operands are below 2^64 (canonical limbs, or p for a negated zero), so every
                // limb sum of products is below 2^131 and is reduced exactly once.
                let p := 0xFFFFFFFF00000001
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), p)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), p)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), p)
            }
            function ext3Sq(a0, a1, a2) -> c0, c1, c2 {
                let p := 0xFFFFFFFF00000001
                c0 := mod(add(mul(a0, a0), shl(2, mul(a1, a2))), p)
                c1 := mod(shl(1, add(mul(a0, a1), mul(a2, a2))), p)
                c2 := mod(add(shl(1, mul(a0, a2)), mul(a1, a1)), p)
            }
            // x^7 = (x * x^2) * x^4, exactly as the Rust `pow7`.
            function pow7(x0, x1, x2) -> r0, r1, r2 {
                let q0, q1, q2 := ext3Sq(x0, x1, x2)
                let f0, f1, f2 := ext3Sq(q0, q1, q2)
                r0, r1, r2 := ext3Mul(x0, x1, x2, q0, q1, q2)
                r0, r1, r2 := ext3Mul(r0, r1, r2, f0, f1, f2)
            }
            // state[i].c0 += rc[i] for the twelve base-field round constants at `rcBase`.
            function constantLayer(s_, rcBase) {
                let p := 0xFFFFFFFF00000001
                for { let i := 0 } lt(i, 0x180) { i := add(i, 0x20) } {
                    let a := add(s_, i)
                    mstore(a, addmod(mload(a), shr(192, mload(rcBase)), p))
                    rcBase := add(rcBase, 8)
                }
            }
            // Write twelve constraints `state[i] - wire` at `kp` and load the wires into the
            // state (the Rust `state[i] = sbox_input` step of a full round).
            function consumeWires(s_, wp, kp) {
                let p := 0xFFFFFFFF00000001
                for { let i := 0 } lt(i, 0x180) { i := add(i, 0x20) } {
                    let a := add(s_, i)
                    let x0 := calldataload(wp)
                    let x1 := calldataload(add(wp, 0x20))
                    let x2 := calldataload(add(wp, 0x40))
                    mstore(kp, addmod(mload(a), sub(p, x0), p))
                    mstore(add(kp, 0x20), addmod(mload(add(a, 0x180)), sub(p, x1), p))
                    mstore(add(kp, 0x40), addmod(mload(add(a, 0x300)), sub(p, x2), p))
                    mstore(a, x0)
                    mstore(add(a, 0x180), x1)
                    mstore(add(a, 0x300), x2)
                    wp := add(wp, 0x60)
                    kp := add(kp, 0x60)
                }
            }
            // state[i] := state[i]^7 for every element.
            function sboxLayer(s_) {
                for { let i := 0 } lt(i, 0x180) { i := add(i, 0x20) } {
                    let a := add(s_, i)
                    let r0, r1, r2 := pow7(mload(a), mload(add(a, 0x180)), mload(add(a, 0x300)))
                    mstore(a, r0)
                    mstore(add(a, 0x180), r1)
                    mstore(add(a, 0x300), r2)
                }
            }
            // Dense MDS on one limb plane `sp` (12 words), using Plonky2's exact integer-FFT
            // factorization of the fixed circulant CIRC = [17,15,41,16,2,28,13,13,39,18,34,20]
            // plus the single diagonal coefficient 8 on row 0. `t_` is a 12-word scratch area.
            // Identical to `PoseidonGate._mdsLayerInline`; every value stays a canonical
            // representative and the bounded multiples of p keep all subtractions positive.
            function mdsPlane(sp, t_) {
                let p := 0xFFFFFFFF00000001
                for { let g := 0 } lt(g, 3) { g := add(g, 1) } {
                    let a := mload(add(sp, mul(g, 0x20)))
                    let b := mload(add(sp, mul(add(g, 3), 0x20)))
                    let c := mload(add(sp, mul(add(g, 6), 0x20)))
                    let d := mload(add(sp, mul(add(g, 9), 0x20)))
                    let base := add(t_, mul(g, 0x80))
                    mstore(base, addmod(addmod(a, b, p), addmod(c, d, p), p))
                    mstore(add(base, 0x20), addmod(a, sub(p, c), p))
                    mstore(add(base, 0x40), addmod(d, sub(p, b), p))
                    mstore(add(base, 0x60), addmod(addmod(a, sub(p, b), p), addmod(c, sub(p, d), p), p))
                }
                {
                    let x0 := mload(t_)
                    let x1 := mload(add(t_, 0x80))
                    let x2 := mload(add(t_, 0x100))
                    mstore(t_, mod(add(add(shl(4, x0), shl(4, x1)), shl(5, x2)), p))
                    mstore(add(t_, 0x80), mod(add(add(shl(5, x0), shl(4, x1)), shl(4, x2)), p))
                    mstore(add(t_, 0x100), mod(add(add(shl(4, x0), shl(5, x1)), shl(4, x2)), p))
                }
                {
                    let a := mload(add(t_, 0x20))
                    let b := mload(add(t_, 0x40))
                    let c := mload(add(t_, 0xa0))
                    let d := mload(add(t_, 0xc0))
                    let e := mload(add(t_, 0x120))
                    let f := mload(add(t_, 0x140))
                    mstore(
                        add(t_, 0x20),
                        mod(add(add(add(add(add(shl(1, a), b), c), shl(4, d)), e), sub(shl(2, p), shl(2, f))), p)
                    )
                    mstore(
                        add(t_, 0x40),
                        mod(sub(add(add(add(shl(1, b), d), shl(2, e)), add(f, mul(17, p))), add(a, shl(4, c))), p)
                    )
                    mstore(
                        add(t_, 0xa0),
                        mod(add(add(add(add(shl(1, c), d), e), shl(4, f)), sub(mul(5, p), add(shl(2, a), b))), p)
                    )
                    mstore(
                        add(t_, 0xc0),
                        mod(sub(add(add(add(a, shl(1, d)), f), mul(21, p)), add(add(shl(2, b), c), shl(4, e))), p)
                    )
                    mstore(
                        add(t_, 0x120),
                        mod(add(add(add(shl(4, a), shl(1, e)), f), sub(mul(6, p), add(add(b, shl(2, c)), d))), p)
                    )
                    mstore(
                        add(t_, 0x140),
                        mod(add(add(add(add(a, shl(4, b)), c), shl(1, f)), sub(mul(5, p), add(shl(2, d), e))), p)
                    )
                }
                {
                    let x0 := mload(add(t_, 0x60))
                    let x1 := mload(add(t_, 0xe0))
                    let x2 := mload(add(t_, 0x160))
                    mstore(add(t_, 0x60), mod(add(shl(3, x2), sub(mul(3, p), add(x0, shl(1, x1)))), p))
                    mstore(add(t_, 0xe0), mod(sub(mul(11, p), add(add(shl(3, x0), x1), shl(1, x2))), p))
                    mstore(add(t_, 0x160), mod(add(shl(1, x0), sub(mul(9, p), add(shl(3, x1), x2))), p))
                }
                for { let g := 0 } lt(g, 3) { g := add(g, 1) } {
                    let base := add(t_, mul(g, 0x80))
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

            let rc := add(roundConstants, 0x20)
            for { let round := 0 } lt(round, 4) { round := add(round, 1) } {
                switch half
                case 0 {
                    constantLayer(s, add(rc, mul(round, 96)))
                    if round {
                        consumeWires(s, add(w, mul(add(29, mul(12, sub(round, 1))), 0x60)), add(k, mul(next, 0x60)))
                        next := add(next, 12)
                    }
                }
                default {
                    constantLayer(s, add(rc, mul(add(26, round), 96)))
                    consumeWires(s, add(w, mul(add(87, mul(12, round)), 0x60)), add(k, mul(next, 0x60)))
                    next := add(next, 12)
                }
                sboxLayer(s)
                mdsPlane(s, t)
                mdsPlane(add(s, 0x180), t)
                mdsPlane(add(s, 0x300), t)
            }
        }
        return next;
    }

    /// @dev Partial first constant layer followed by the partial initial matrix,
    /// `result[0] = state[0]; result[c] = sum_{r=1..11} state[r] * M[r-1][c-1]`, written to the
    /// planes at `r`. Eleven products of canonical 64-bit values stay below 2^132, so each
    /// column is reduced once. Returns the pointer holding the new state (`r`).
    function _partialInit(uint256 s, uint256 r, bytes memory pfrc, bytes memory pim) private pure returns (uint256) {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            {
                let rcBase := add(pfrc, 0x20)
                for { let i := 0 } lt(i, 0x180) { i := add(i, 0x20) } {
                    let a := add(s, i)
                    mstore(a, addmod(mload(a), shr(192, mload(rcBase)), p))
                    rcBase := add(rcBase, 8)
                }
            }
            mstore(r, mload(s))
            mstore(add(r, 0x180), mload(add(s, 0x180)))
            mstore(add(r, 0x300), mload(add(s, 0x300)))
            let matrix := add(pim, 0x20)
            for { let c := 0x20 } lt(c, 0x180) { c := add(c, 0x20) } {
                let acc0 := 0
                let acc1 := 0
                let acc2 := 0
                // M[0][c-1], then one 88-byte row stride per state row.
                let mp := add(matrix, sub(shr(2, c), 8))
                for { let row := 0x20 } lt(row, 0x180) { row := add(row, 0x20) } {
                    let m := shr(192, mload(mp))
                    let a := add(s, row)
                    acc0 := add(acc0, mul(mload(a), m))
                    acc1 := add(acc1, mul(mload(add(a, 0x180)), m))
                    acc2 := add(acc2, mul(mload(add(a, 0x300)), m))
                    mp := add(mp, 88)
                }
                let o := add(r, c)
                mstore(o, mod(acc0, p))
                mstore(add(o, 0x180), mod(acc1, p))
                mstore(add(o, 0x300), mod(acc2, p))
            }
        }
        return r;
    }

    /// @dev The 22 partial rounds: constraint `state[0] - wire`, `state[0] = wire^7 + rc`, then
    /// the sparse matrix in place:
    ///   d        = state[0] * (CIRC[0] + DIAG[0]) + sum_{i>=1} state[i] * W_HAT[i-1]
    ///   state[i] = state[0] * V[i-1] + state[i]          (i >= 1)
    ///   state[0] = d
    /// Products of canonical 64-bit values are accumulated unreduced (below 2^132).
    function _partialRounds(
        uint256 w,
        uint256 s,
        uint256 k,
        bytes memory prc,
        bytes memory prvs,
        bytes memory prwh,
        uint256 next
    ) private pure returns (uint256) {
        assembly ("memory-safe") {
            function ext3Mul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                // Operands are below 2^64 (canonical limbs, or p for a negated zero), so every
                // limb sum of products is below 2^131 and is reduced exactly once.
                let p := 0xFFFFFFFF00000001
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), p)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), p)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), p)
            }
            function ext3Sq(a0, a1, a2) -> c0, c1, c2 {
                let p := 0xFFFFFFFF00000001
                c0 := mod(add(mul(a0, a0), shl(2, mul(a1, a2))), p)
                c1 := mod(shl(1, add(mul(a0, a1), mul(a2, a2))), p)
                c2 := mod(add(shl(1, mul(a0, a2)), mul(a1, a1)), p)
            }
            function pow7(x0, x1, x2) -> r0, r1, r2 {
                let q0, q1, q2 := ext3Sq(x0, x1, x2)
                let f0, f1, f2 := ext3Sq(q0, q1, q2)
                r0, r1, r2 := ext3Mul(x0, x1, x2, q0, q1, q2)
                r0, r1, r2 := ext3Mul(r0, r1, r2, f0, f1, f2)
            }
            function mdsPartialFast(s_, whp, vsp) {
                let p := 0xFFFFFFFF00000001
                let d0 := mul(mload(s_), 25)
                let d1 := mul(mload(add(s_, 0x180)), 25)
                let d2 := mul(mload(add(s_, 0x300)), 25)
                for { let i := 0x20 } lt(i, 0x180) { i := add(i, 0x20) } {
                    let wh := shr(192, mload(whp))
                    let v := shr(192, mload(vsp))
                    whp := add(whp, 8)
                    vsp := add(vsp, 8)
                    let a := add(s_, i)
                    let x := mload(a)
                    d0 := add(d0, mul(x, wh))
                    mstore(a, mod(add(mul(mload(s_), v), x), p))
                    a := add(a, 0x180)
                    x := mload(a)
                    d1 := add(d1, mul(x, wh))
                    mstore(a, mod(add(mul(mload(add(s_, 0x180)), v), x), p))
                    a := add(a, 0x180)
                    x := mload(a)
                    d2 := add(d2, mul(x, wh))
                    mstore(a, mod(add(mul(mload(add(s_, 0x300)), v), x), p))
                }
                mstore(s_, mod(d0, p))
                mstore(add(s_, 0x180), mod(d1, p))
                mstore(add(s_, 0x300), mod(d2, p))
            }

            let p := 0xFFFFFFFF00000001
            let whp := add(prwh, 0x20)
            let vsp := add(prvs, 0x20)
            let rcp := add(prc, 0x20)
            let wp := add(w, mul(65, 0x60))
            let kp := add(k, mul(next, 0x60))
            for { let round := 0 } lt(round, 22) { round := add(round, 1) } {
                let x0 := calldataload(wp)
                let x1 := calldataload(add(wp, 0x20))
                let x2 := calldataload(add(wp, 0x40))
                mstore(kp, addmod(mload(s), sub(p, x0), p))
                mstore(add(kp, 0x20), addmod(mload(add(s, 0x180)), sub(p, x1), p))
                mstore(add(kp, 0x40), addmod(mload(add(s, 0x300)), sub(p, x2), p))
                let y0, y1, y2 := pow7(x0, x1, x2)
                // The Rust reference adds FAST_PARTIAL_ROUND_CONSTANTS[round] for every
                // round; the table's last entry is zero.
                mstore(s, addmod(y0, shr(192, mload(rcp)), p))
                mstore(add(s, 0x180), y1)
                mstore(add(s, 0x300), y2)
                mdsPartialFast(s, whp, vsp)
                whp := add(whp, 88)
                vsp := add(vsp, 88)
                rcp := add(rcp, 8)
                wp := add(wp, 0x60)
                kp := add(kp, 0x60)
            }
            next := add(next, 22)
        }
        return next;
    }

    /// @dev Output constraints: state[i] - w[12 + i].
    function _outputConstraints(uint256 w, uint256 s, uint256 k, uint256 next) private pure {
        assert(next + SPONGE_WIDTH == POSEIDON_CONSTRAINTS);
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let wp := add(w, mul(12, 0x60))
            let kp := add(k, mul(next, 0x60))
            for { let i := 0 } lt(i, 0x180) { i := add(i, 0x20) } {
                let a := add(s, i)
                mstore(kp, addmod(mload(a), sub(p, calldataload(wp)), p))
                mstore(add(kp, 0x20), addmod(mload(add(a, 0x180)), sub(p, calldataload(add(wp, 0x20))), p))
                mstore(add(kp, 0x40), addmod(mload(add(a, 0x300)), sub(p, calldataload(add(wp, 0x40))), p))
                wp := add(wp, 0x60)
                kp := add(kp, 0x60)
            }
        }
    }

    /// @dev Horner: r = k[122]; r = r * alpha + k[i] for i = 121 .. 0.
    function _reduce(uint256 k, uint256 alpha0, uint256 alpha1, uint256 alpha2)
        private
        pure
        returns (uint256 red0, uint256 red1, uint256 red2)
    {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let kp := add(k, mul(122, 0x60))
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
}
