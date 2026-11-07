// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {GoldilocksExt3} from "./GoldilocksExt3.sol";
import {InvalidMleProof} from "../MleProofErrors.sol";

/// @title WhirLinearAlgebra
/// @notice Linear algebra utilities for WHIR verification.
///         All hot-path functions use inline assembly to avoid Ext3 memory allocation.
library WhirLinearAlgebra {
    using GoldilocksExt3 for GoldilocksExt3.Ext3;

    uint256 private constant P = 0xFFFFFFFF00000001;

    // =====================================================================
    // Inline assembly helpers for Ext3 arithmetic on stack
    // =====================================================================
    // All Ext3 values are kept as 3 stack variables (c0, c1, c2).
    // Ext3 mul: c0 = a0*b0 + 2*(a1*b2 + a2*b1)
    //           c1 = a0*b1 + a1*b0 + 2*a2*b2
    //           c2 = a0*b2 + a1*b1 + a2*b0

    /// @dev mleEvaluateUnivariateFrom — full assembly, zero intermediate Ext3 allocs.
    ///      Computes Π_i ((1 - r_i) + r_i * x^(2^i)) for i in [start..point.length), iterated in reverse.
    ///
    /// SECURITY: Points are paired in REVERSE order (point[len-1] → x^1, ..., point[start] → x^(2^{n-1})).
    /// This matches the prover's bit-reversal convention for WHIR univariate MLE evaluation.
    /// If the prover uses the forward convention, this would evaluate a different polynomial.
    function mleEvaluateUnivariateFrom(
        GoldilocksExt3.Ext3 memory x,
        GoldilocksExt3.Ext3[] memory point,
        uint256 start
    ) internal pure returns (GoldilocksExt3.Ext3 memory result) {
        assembly {
            let p := P

            // result = 1
            let res0 := 1
            let res1 := 0
            let res2 := 0

            // x2i = x (will be squared each iteration)
            let x0 := mload(x)
            let x1 := mload(add(x, 0x20))
            let x2 := mload(add(x, 0x40))

            let pData := add(point, 0x20)
            let len := mload(point)

            for { let i := len } gt(i, start) { i := sub(i, 1) } {
                let rPtr := mload(add(pData, mul(sub(i, 1), 0x20)))
                let r0 := mload(rPtr)
                let r1 := mload(add(rPtr, 0x20))
                let r2 := mload(add(rPtr, 0x40))

                // term = (1 - r) + r * x2i
                // SECURITY: Normalize r components before negating. Non-canonical r (r >= p)
                // causes sub(p, r) to wrap in 256-bit: sub(p, p+k) = 2^256-k, and since
                // 2^256 mod p != 0, the subsequent addmod produces an incorrect field value.
                r0 := mod(r0, p)
                r1 := mod(r1, p)
                r2 := mod(r2, p)
                // oneMinusR = (1-r0, -r1, -r2) mod p
                let omr0 := addmod(1, sub(p, r0), p)
                let omr1 := sub(p, r1)
                let omr2 := sub(p, r2)

                // r * x2i (Ext3 mul). In-domain evaluation points are base-field elements
                // (x1 = x2 = 0 for every square), so the scalar product is used whenever the
                // extension limbs are zero; the two formulas agree exactly in that case.
                let rx0 := 0
                let rx1 := 0
                let rx2 := 0
                switch or(x1, x2)
                case 0 {
                    rx0 := mulmod(r0, x0, p)
                    rx1 := mulmod(r1, x0, p)
                    rx2 := mulmod(r2, x0, p)
                }
                default {
                    let t1 := addmod(mulmod(r1, x2, p), mulmod(r2, x1, p), p)
                    rx0 := addmod(mulmod(r0, x0, p), mulmod(2, t1, p), p)
                    rx1 := addmod(addmod(mulmod(r0, x1, p), mulmod(r1, x0, p), p), mulmod(2, mulmod(r2, x2, p), p), p)
                    rx2 := addmod(addmod(mulmod(r0, x2, p), mulmod(r1, x1, p), p), mulmod(r2, x0, p), p)
                }

                // term = oneMinusR + rx
                let term0 := addmod(omr0, rx0, p)
                let term1 := addmod(omr1, rx1, p)
                let term2 := addmod(omr2, rx2, p)

                // result *= term (Ext3 mul)
                let mt1 := addmod(mulmod(res1, term2, p), mulmod(res2, term1, p), p)
                let nr0 := addmod(mulmod(res0, term0, p), mulmod(2, mt1, p), p)
                let nr1 := addmod(addmod(mulmod(res0, term1, p), mulmod(res1, term0, p), p), mulmod(2, mulmod(res2, term2, p), p), p)
                let nr2 := addmod(addmod(mulmod(res0, term2, p), mulmod(res1, term1, p), p), mulmod(res2, term0, p), p)
                res0 := nr0
                res1 := nr1
                res2 := nr2

                // x2i = x2i^2 (Ext3 square = mul(x2i, x2i)); a base-field point stays base-field.
                switch or(x1, x2)
                case 0 { x0 := mulmod(x0, x0, p) }
                default {
                    let st1 := addmod(mulmod(x1, x2, p), mulmod(x2, x1, p), p)
                    let sx0 := addmod(mulmod(x0, x0, p), mulmod(2, st1, p), p)
                    let sx1 := addmod(addmod(mulmod(x0, x1, p), mulmod(x1, x0, p), p), mulmod(2, mulmod(x2, x2, p), p), p)
                    let sx2 := addmod(addmod(mulmod(x0, x2, p), mulmod(x1, x1, p), p), mulmod(x2, x0, p), p)
                    x0 := sx0
                    x1 := sx1
                    x2 := sx2
                }
            }

            mstore(result, res0)
            mstore(add(result, 0x20), res1)
            mstore(add(result, 0x40), res2)
        }
    }

    /// @dev mleEvaluateUnivariate — same as above but start=0.
    function mleEvaluateUnivariate(
        GoldilocksExt3.Ext3 memory x,
        GoldilocksExt3.Ext3[] memory point
    ) internal pure returns (GoldilocksExt3.Ext3 memory result) {
        return mleEvaluateUnivariateFrom(x, point, 0);
    }

    /// @dev Evaluate eq((1, 2, ..., numVariables), evalPoint) — full assembly.
    ///      eq(l, r) = Π_i (l_i * r_i + (1 - l_i) * (1 - r_i))
    ///      where l_i = i+1 (base field constant).
    function mleEvaluateEqCanonical(
        uint256 numVariables,
        GoldilocksExt3.Ext3[] memory evalPoint
    ) internal pure returns (GoldilocksExt3.Ext3 memory result) {
        // SECURITY: require length equality — silent truncation allows a prover to supply
        // a shorter evalPoint, making the verifier evaluate over fewer variables and
        // accepting constraints that only hold on a proper subset of the required domain.
        if (numVariables != evalPoint.length) revert InvalidMleProof();
        assembly {
            let p := P
            let res0 := 1
            let res1 := 0
            let res2 := 0

            let epLen := mload(evalPoint)
            let n := numVariables
            // Length equality is enforced above; the min is kept only as defensive fallback.
            if lt(epLen, n) { n := epLen }
            let epData := add(evalPoint, 0x20)

            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let li := add(i, 1) // base field: l = i+1, so l0=li, l1=0, l2=0

                let rPtr := mload(add(epData, mul(i, 0x20)))
                let r0 := mload(rPtr)
                let r1 := mload(add(rPtr, 0x20))
                let r2 := mload(add(rPtr, 0x40))

                // SECURITY: Normalize r components before negating.
                r0 := mod(r0, p)
                r1 := mod(r1, p)
                r2 := mod(r2, p)

                // lr = l * r = (li*r0, li*r1, li*r2) (scalar mul)
                let lr0 := mulmod(li, r0, p)
                let lr1 := mulmod(li, r1, p)
                let lr2 := mulmod(li, r2, p)

                // oneMinusL = (1 - li, 0, 0) = (p+1-li, 0, 0) mod p
                let oml := addmod(1, sub(p, li), p)

                // oneMinusR = (1-r0, -r1, -r2)
                let omr0 := addmod(1, sub(p, r0), p)
                let omr1 := sub(p, r1)
                let omr2 := sub(p, r2)

                // (1-l)*(1-r): scalar oml * (omr0, omr1, omr2)
                let pr0 := mulmod(oml, omr0, p)
                let pr1 := mulmod(oml, omr1, p)
                let pr2 := mulmod(oml, omr2, p)

                // term = lr + (1-l)*(1-r)
                let t0 := addmod(lr0, pr0, p)
                let t1 := addmod(lr1, pr1, p)
                let t2 := addmod(lr2, pr2, p)

                // result *= term
                let mt := addmod(mulmod(res1, t2, p), mulmod(res2, t1, p), p)
                let nr0 := addmod(mulmod(res0, t0, p), mulmod(2, mt, p), p)
                let nr1 := addmod(addmod(mulmod(res0, t1, p), mulmod(res1, t0, p), p), mulmod(2, mulmod(res2, t2, p), p), p)
                let nr2 := addmod(addmod(mulmod(res0, t2, p), mulmod(res1, t1, p), p), mulmod(res2, t0, p), p)
                res0 := nr0
                res1 := nr1
                res2 := nr2
            }

            mstore(result, res0)
            mstore(add(result, 0x20), res1)
            mstore(add(result, 0x40), res2)
        }
    }

    /// @dev mleEvaluateEq — full assembly version.
    function mleEvaluateEq(
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3[] memory evalPoint
    ) internal pure returns (GoldilocksExt3.Ext3 memory result) {
        // SECURITY: require length equality — silent truncation allows a prover to supply
        // a shorter array, causing the verifier to evaluate over fewer variables and
        // potentially accepting constraints that only hold on a subset of the domain.
        if (point.length != evalPoint.length) revert InvalidMleProof();
        assembly {
            let p := P
            let res0 := 1
            let res1 := 0
            let res2 := 0

            let pLen := mload(point)
            let epLen := mload(evalPoint)
            let n := pLen
            // Length equality is enforced above; the min is kept only as defensive fallback.
            if lt(epLen, n) { n := epLen }

            let pData := add(point, 0x20)
            let epData := add(evalPoint, 0x20)

            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let lPtr := mload(add(pData, mul(i, 0x20)))
                let l0 := mload(lPtr)
                let l1 := mload(add(lPtr, 0x20))
                let l2 := mload(add(lPtr, 0x40))

                let rPtr := mload(add(epData, mul(i, 0x20)))
                let r0 := mload(rPtr)
                let r1 := mload(add(rPtr, 0x20))
                let r2 := mload(add(rPtr, 0x40))

                // SECURITY: Normalize l and r components before negating.
                l0 := mod(l0, p)
                l1 := mod(l1, p)
                l2 := mod(l2, p)
                r0 := mod(r0, p)
                r1 := mod(r1, p)
                r2 := mod(r2, p)

                // lr = l * r (Ext3 mul)
                let lrt := addmod(mulmod(l1, r2, p), mulmod(l2, r1, p), p)
                let lr0 := addmod(mulmod(l0, r0, p), mulmod(2, lrt, p), p)
                let lr1 := addmod(addmod(mulmod(l0, r1, p), mulmod(l1, r0, p), p), mulmod(2, mulmod(l2, r2, p), p), p)
                let lr2 := addmod(addmod(mulmod(l0, r2, p), mulmod(l1, r1, p), p), mulmod(l2, r0, p), p)

                // oneMinusL
                let oml0 := addmod(1, sub(p, l0), p)
                let oml1 := sub(p, l1)
                let oml2 := sub(p, l2)
                // oneMinusR
                let omr0 := addmod(1, sub(p, r0), p)
                let omr1 := sub(p, r1)
                let omr2 := sub(p, r2)

                // (1-l)*(1-r) (Ext3 mul)
                let pt := addmod(mulmod(oml1, omr2, p), mulmod(oml2, omr1, p), p)
                let pr0 := addmod(mulmod(oml0, omr0, p), mulmod(2, pt, p), p)
                let pr1 := addmod(addmod(mulmod(oml0, omr1, p), mulmod(oml1, omr0, p), p), mulmod(2, mulmod(oml2, omr2, p), p), p)
                let pr2 := addmod(addmod(mulmod(oml0, omr2, p), mulmod(oml1, omr1, p), p), mulmod(oml2, omr0, p), p)

                // term = lr + (1-l)*(1-r)
                let t0 := addmod(lr0, pr0, p)
                let t1 := addmod(lr1, pr1, p)
                let t2 := addmod(lr2, pr2, p)

                // result *= term
                let mt := addmod(mulmod(res1, t2, p), mulmod(res2, t1, p), p)
                let nr0 := addmod(mulmod(res0, t0, p), mulmod(2, mt, p), p)
                let nr1 := addmod(addmod(mulmod(res0, t1, p), mulmod(res1, t0, p), p), mulmod(2, mulmod(res2, t2, p), p), p)
                let nr2 := addmod(addmod(mulmod(res0, t2, p), mulmod(res1, t1, p), p), mulmod(res2, t0, p), p)
                res0 := nr0
                res1 := nr1
                res2 := nr2
            }

            mstore(result, res0)
            mstore(add(result, 0x20), res1)
            mstore(add(result, 0x40), res2)
        }
    }

    /// @dev Compute eq_weights from a slice of a larger array — full assembly.
    ///      Result array elements are Ext3 structs written directly.
    function eqWeightsFrom(
        GoldilocksExt3.Ext3[] memory arr,
        uint256 start,
        uint256 count
    ) internal pure returns (GoldilocksExt3.Ext3[] memory weights) {
        // SECURITY: Bounds check — without this, the assembly loop reads arr[start+idx]
        // for idx in [0, count), which accesses beyond arr.length when start+count > arr.length.
        // Out-of-bounds reads return garbage from adjacent EVM memory, corrupting eq_weights
        // and thus the polynomial commitment check: dotProduct(eqWeights, evaluations).
        if (start > arr.length || count > arr.length - start) revert InvalidMleProof();
        uint256 size = 1 << count;
        weights = new GoldilocksExt3.Ext3[](size);
        // Allocate all Ext3 structs upfront
        for (uint256 i = 0; i < size; i++) {
            weights[i] = GoldilocksExt3.zero();
        }
        // Set weights[0] = 1
        weights[0].c0 = 1;

        assembly {
            let p := P
            let wData := add(weights, 0x20)
            let aData := add(arr, 0x20)

            let half := 1
            for { let idx := 0 } lt(idx, count) { idx := add(idx, 1) } {
                let riPtr := mload(add(aData, mul(add(start, idx), 0x20)))
                let ri0 := mload(riPtr)
                let ri1 := mload(add(riPtr, 0x20))
                let ri2 := mload(add(riPtr, 0x40))
                // SECURITY: Normalize ri components before negating.
                ri0 := mod(ri0, p)
                ri1 := mod(ri1, p)
                ri2 := mod(ri2, p)
                // oneMinusRi
                let omr0 := addmod(1, sub(p, ri0), p)
                let omr1 := sub(p, ri1)
                let omr2 := sub(p, ri2)

                // Process in reverse to avoid overwriting
                for { let j := half } gt(j, 0) { j := sub(j, 1) } {
                    let srcPtr := mload(add(wData, mul(sub(j, 1), 0x20)))
                    let s0 := mload(srcPtr)
                    let s1 := mload(add(srcPtr, 0x20))
                    let s2 := mload(add(srcPtr, 0x40))

                    // weights[2*(j-1)+1] = src * ri (Ext3 mul)
                    let hiPtr := mload(add(wData, mul(add(mul(sub(j, 1), 2), 1), 0x20)))
                    let mt1 := addmod(mulmod(s1, ri2, p), mulmod(s2, ri1, p), p)
                    mstore(hiPtr, addmod(mulmod(s0, ri0, p), mulmod(2, mt1, p), p))
                    mstore(add(hiPtr, 0x20), addmod(addmod(mulmod(s0, ri1, p), mulmod(s1, ri0, p), p), mulmod(2, mulmod(s2, ri2, p), p), p))
                    mstore(add(hiPtr, 0x40), addmod(addmod(mulmod(s0, ri2, p), mulmod(s1, ri1, p), p), mulmod(s2, ri0, p), p))

                    // weights[2*(j-1)] = src * oneMinusRi (Ext3 mul)
                    let loPtr := mload(add(wData, mul(mul(sub(j, 1), 2), 0x20)))
                    let mt2 := addmod(mulmod(s1, omr2, p), mulmod(s2, omr1, p), p)
                    mstore(loPtr, addmod(mulmod(s0, omr0, p), mulmod(2, mt2, p), p))
                    mstore(add(loPtr, 0x20), addmod(addmod(mulmod(s0, omr1, p), mulmod(s1, omr0, p), p), mulmod(2, mulmod(s2, omr2, p), p), p))
                    mstore(add(loPtr, 0x40), addmod(addmod(mulmod(s0, omr2, p), mulmod(s1, omr1, p), p), mulmod(s2, omr0, p), p))
                }
                half := shl(1, half)
            }
        }
    }

    /// @dev Compute eq_weights: same as eqWeightsFrom with start=0.
    function eqWeights(
        GoldilocksExt3.Ext3[] memory point
    ) internal pure returns (GoldilocksExt3.Ext3[] memory weights) {
        // Reimplement directly to avoid extra indirection
        uint256 n = point.length;
        uint256 size = 1 << n;
        weights = new GoldilocksExt3.Ext3[](size);
        for (uint256 i = 0; i < size; i++) {
            weights[i] = GoldilocksExt3.zero();
        }
        weights[0].c0 = 1;

        assembly {
            let p := P
            let wData := add(weights, 0x20)
            let pData := add(point, 0x20)

            let half := 1
            for { let idx := 0 } lt(idx, n) { idx := add(idx, 1) } {
                let riPtr := mload(add(pData, mul(idx, 0x20)))
                let ri0 := mload(riPtr)
                let ri1 := mload(add(riPtr, 0x20))
                let ri2 := mload(add(riPtr, 0x40))
                // SECURITY: Normalize ri components before negating.
                ri0 := mod(ri0, p)
                ri1 := mod(ri1, p)
                ri2 := mod(ri2, p)
                let omr0 := addmod(1, sub(p, ri0), p)
                let omr1 := sub(p, ri1)
                let omr2 := sub(p, ri2)

                for { let j := half } gt(j, 0) { j := sub(j, 1) } {
                    let srcPtr := mload(add(wData, mul(sub(j, 1), 0x20)))
                    let s0 := mload(srcPtr)
                    let s1 := mload(add(srcPtr, 0x20))
                    let s2 := mload(add(srcPtr, 0x40))

                    let hiPtr := mload(add(wData, mul(add(mul(sub(j, 1), 2), 1), 0x20)))
                    let mt1 := addmod(mulmod(s1, ri2, p), mulmod(s2, ri1, p), p)
                    mstore(hiPtr, addmod(mulmod(s0, ri0, p), mulmod(2, mt1, p), p))
                    mstore(add(hiPtr, 0x20), addmod(addmod(mulmod(s0, ri1, p), mulmod(s1, ri0, p), p), mulmod(2, mulmod(s2, ri2, p), p), p))
                    mstore(add(hiPtr, 0x40), addmod(addmod(mulmod(s0, ri2, p), mulmod(s1, ri1, p), p), mulmod(s2, ri0, p), p))

                    let loPtr := mload(add(wData, mul(mul(sub(j, 1), 2), 0x20)))
                    let mt2 := addmod(mulmod(s1, omr2, p), mulmod(s2, omr1, p), p)
                    mstore(loPtr, addmod(mulmod(s0, omr0, p), mulmod(2, mt2, p), p))
                    mstore(add(loPtr, 0x20), addmod(addmod(mulmod(s0, omr1, p), mulmod(s1, omr0, p), p), mulmod(2, mulmod(s2, omr2, p), p), p))
                    mstore(add(loPtr, 0x40), addmod(addmod(mulmod(s0, omr2, p), mulmod(s1, omr1, p), p), mulmod(s2, omr0, p), p))
                }
                half := shl(1, half)
            }
        }
    }

    // =====================================================================
    // Flat-limb variants used by the verifier hot paths.
    // A "flat" Ext3 vector is a uint256[] holding 3 canonical limbs (c0, c1, c2) per element.
    // Products use lazy reduction: with every input < 2^64 the 256-bit sums of products cannot
    // wrap, and one `mod` per limb yields the same canonical value as the mulmod/addmod form.
    // =====================================================================

    /// @dev eq weights over the folding randomness slice r[start..start+count) in flat layout:
    ///      weights[idx] = prod_k (bit_k(idx) ? r_(start+count-1-k) : 1 - r_(start+count-1-k)),
    ///      identical to `eqWeightsFrom` (last randomness <-> lowest index bit).
    function eqWeightsFlat(uint256[] memory r, uint256 start, uint256 count)
        internal
        pure
        returns (uint256[] memory weights)
    {
        // SECURITY: Bounds check the randomness slice (see eqWeightsFrom).
        uint256 len = r.length / 3;
        if (start > len || count > len - start) revert InvalidMleProof();
        uint256 size = 1 << count;
        weights = new uint256[](3 * size);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let p := P
            let wData := add(weights, 0x20)
            mstore(wData, 1)
            let rp := add(add(r, 0x20), mul(start, 0x60))
            let half := 1
            for { let idx := 0 } lt(idx, count) { idx := add(idx, 1) } {
                // SECURITY: Normalize ri components before negating.
                let ri0 := mod(mload(rp), p)
                let ri1 := mod(mload(add(rp, 0x20)), p)
                let ri2 := mod(mload(add(rp, 0x40)), p)
                rp := add(rp, 0x60)
                let omr0 := addmod(1, sub(p, ri0), p)
                let omr1 := sub(p, ri1)
                let omr2 := sub(p, ri2)
                // Process in reverse to avoid overwriting
                for { let j := half } j { j := sub(j, 1) } {
                    let sp := add(wData, mul(sub(j, 1), 0x60))
                    let s0 := mload(sp)
                    let s1 := mload(add(sp, 0x20))
                    let s2 := mload(add(sp, 0x40))
                    let lo := add(wData, mul(sub(j, 1), 0xc0))
                    let h0, h1, h2 := mul3(s0, s1, s2, ri0, ri1, ri2)
                    mstore(add(lo, 0x60), h0)
                    mstore(add(lo, 0x80), h1)
                    mstore(add(lo, 0xa0), h2)
                    let l0, l1, l2 := mul3(s0, s1, s2, omr0, omr1, omr2)
                    mstore(lo, l0)
                    mstore(add(lo, 0x20), l1)
                    mstore(add(lo, 0x40), l2)
                }
                half := shl(1, half)
            }
        }
    }

    /// @dev Tensor product of the flat slice a[aOff..aOff+aLen) with the flat vector b:
    ///      result[i * |b| + j] = a[aOff + i] * b[j] (same layout as `tensorProduct`).
    ///      A one-element slice equal to 1 returns `b` itself (multiplication by one is exact).
    function tensorFlat(uint256[] memory a, uint256 aOff, uint256 aLen, uint256[] memory b)
        internal
        pure
        returns (uint256[] memory result)
    {
        if (aOff > a.length / 3 || aLen > a.length / 3 - aOff) revert InvalidMleProof();
        if (aLen == 1 && a[3 * aOff] == 1 && a[3 * aOff + 1] == 0 && a[3 * aOff + 2] == 0) return b;
        uint256 bLen = b.length / 3;
        result = new uint256[](3 * aLen * bLen);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let bData := add(b, 0x20)
            let bEnd := add(bData, mul(bLen, 0x60))
            let rp := add(result, 0x20)
            let ap := add(add(a, 0x20), mul(aOff, 0x60))
            let aEnd := add(ap, mul(aLen, 0x60))
            for {} lt(ap, aEnd) { ap := add(ap, 0x60) } {
                let a0 := mload(ap)
                let a1 := mload(add(ap, 0x20))
                let a2 := mload(add(ap, 0x40))
                for { let bp := bData } lt(bp, bEnd) { bp := add(bp, 0x60) } {
                    let c0, c1, c2 := mul3(a0, a1, a2, mload(bp), mload(add(bp, 0x20)), mload(add(bp, 0x40)))
                    mstore(rp, c0)
                    mstore(add(rp, 0x20), c1)
                    mstore(add(rp, 0x40), c2)
                    rp := add(rp, 0x60)
                }
            }
        }
    }

    /// @dev eq(point, r) with `r` in flat layout; identical to `mleEvaluateEq`.
    function mleEvaluateEqFlat(GoldilocksExt3.Ext3[] memory point, uint256[] memory r)
        internal
        pure
        returns (uint256 res0, uint256 res1, uint256 res2)
    {
        // SECURITY: require length equality (see mleEvaluateEq).
        if (3 * point.length != r.length) revert InvalidMleProof();
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let p := P
            res0 := 1
            let n := mload(point)
            let pData := add(point, 0x20)
            let rp := add(r, 0x20)
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let lPtr := mload(add(pData, shl(5, i)))
                // SECURITY: Normalize l and r components before negating.
                let l0 := mod(mload(lPtr), p)
                let l1 := mod(mload(add(lPtr, 0x20)), p)
                let l2 := mod(mload(add(lPtr, 0x40)), p)
                let r0 := mod(mload(rp), p)
                let r1 := mod(mload(add(rp, 0x20)), p)
                let r2 := mod(mload(add(rp, 0x40)), p)
                rp := add(rp, 0x60)
                // term = l*r + (1-l)*(1-r)
                let t0, t1, t2 := mul3(l0, l1, l2, r0, r1, r2)
                let q0, q1, q2 :=
                    mul3(addmod(1, sub(p, l0), p), sub(p, l1), sub(p, l2), addmod(1, sub(p, r0), p), sub(p, r1), sub(p, r2))
                t0 := addmod(t0, q0, p)
                t1 := addmod(t1, q1, p)
                t2 := addmod(t2, q2, p)
                res0, res1, res2 := mul3(res0, res1, res2, t0, t1, t2)
            }
        }
    }

    /// @dev Dot product of two Ext3 arrays — full assembly.
    function dotProduct(
        GoldilocksExt3.Ext3[] memory a,
        GoldilocksExt3.Ext3[] memory b
    ) internal pure returns (GoldilocksExt3.Ext3 memory result) {
        // SECURITY: require length equality. Silent truncation to min(len_a, len_b) allows a
        // prover to supply a shorter evaluations array, making the verifier sum fewer terms and
        // treating the missing ones as zero. This breaks the polynomial commitment check.
        if (a.length != b.length) revert InvalidMleProof();
        assembly {
            let p := P
            let aLen := mload(a)
            let bLen := mload(b)
            let n := aLen
            // Length equality enforced above; keep min as defensive fallback.
            if lt(bLen, aLen) { n := bLen }

            let r0 := 0
            let r1 := 0
            let r2 := 0
            let aPtr := add(a, 0x20)
            let bPtr := add(b, 0x20)

            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let ae := mload(add(aPtr, mul(i, 0x20)))
                let be := mload(add(bPtr, mul(i, 0x20)))
                let a0 := mload(ae)
                let a1 := mload(add(ae, 0x20))
                let a2 := mload(add(ae, 0x40))
                let b0 := mload(be)
                let b1 := mload(add(be, 0x20))
                let b2 := mload(add(be, 0x40))

                let t := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                r0 := addmod(r0, addmod(mulmod(a0, b0, p), mulmod(2, t, p), p), p)
                r1 := addmod(r1, addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p), p)
                r2 := addmod(r2, addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p), p)
            }

            mstore(result, r0)
            mstore(add(result, 0x20), r1)
            mstore(add(result, 0x40), r2)
        }
    }

    /// @dev Geometric sequence: [1, x, x^2, ..., x^(n-1)] — inline assembly.
    function geometricSequence(
        GoldilocksExt3.Ext3 memory x,
        uint256 n
    ) internal pure returns (GoldilocksExt3.Ext3[] memory result) {
        result = new GoldilocksExt3.Ext3[](n);
        if (n == 0) return result;
        assembly {
            let p := 0xFFFFFFFF00000001
            let x0 := mload(x)
            let x1 := mload(add(x, 0x20))
            let x2 := mload(add(x, 0x40))

            // result[0] = 1
            let dataPtr := add(result, 0x20) // skip length slot
            let elem0 := mload(dataPtr)      // pointer to first Ext3 struct
            mstore(elem0, 1)
            mstore(add(elem0, 0x20), 0)
            mstore(add(elem0, 0x40), 0)

            // result[i] = result[i-1] * x  (inline Ext3 mul)
            let prev0 := 1
            let prev1 := 0
            let prev2 := 0
            for { let i := 1 } lt(i, n) { i := add(i, 1) } {
                // Ext3 mul: (prev) * (x)
                let t1 := addmod(mulmod(prev1, x2, p), mulmod(prev2, x1, p), p)
                let c0 := addmod(mulmod(prev0, x0, p), mulmod(2, t1, p), p)
                let t2 := addmod(mulmod(prev0, x1, p), mulmod(prev1, x0, p), p)
                let c1 := addmod(t2, mulmod(2, mulmod(prev2, x2, p), p), p)
                let c2 := addmod(addmod(mulmod(prev0, x2, p), mulmod(prev1, x1, p), p), mulmod(prev2, x0, p), p)

                let elemPtr := mload(add(dataPtr, mul(i, 0x20)))
                mstore(elemPtr, c0)
                mstore(add(elemPtr, 0x20), c1)
                mstore(add(elemPtr, 0x40), c2)

                prev0 := c0
                prev1 := c1
                prev2 := c2
            }
        }
    }

    /// @dev Tensor product of two vectors — inline assembly.
    function tensorProduct(
        GoldilocksExt3.Ext3[] memory a,
        GoldilocksExt3.Ext3[] memory b
    ) internal pure returns (GoldilocksExt3.Ext3[] memory result) {
        uint256 aLen = a.length;
        uint256 bLen = b.length;
        result = new GoldilocksExt3.Ext3[](aLen * bLen);
        assembly {
            let p := 0xFFFFFFFF00000001
            let aData := add(a, 0x20)
            let bData := add(b, 0x20)
            let rData := add(result, 0x20)

            for { let i := 0 } lt(i, aLen) { i := add(i, 1) } {
                let aPtr := mload(add(aData, mul(i, 0x20)))
                let a0 := mload(aPtr)
                let a1 := mload(add(aPtr, 0x20))
                let a2 := mload(add(aPtr, 0x40))

                for { let j := 0 } lt(j, bLen) { j := add(j, 1) } {
                    let bPtr := mload(add(bData, mul(j, 0x20)))
                    let b0 := mload(bPtr)
                    let b1 := mload(add(bPtr, 0x20))
                    let b2 := mload(add(bPtr, 0x40))

                    // Ext3 mul inline
                    let t1 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
                    let c0 := addmod(mulmod(a0, b0, p), mulmod(2, t1, p), p)
                    let t2 := addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p)
                    let c1 := addmod(t2, mulmod(2, mulmod(a2, b2, p), p), p)
                    let c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)

                    let idx := add(mul(i, bLen), j)
                    let rPtr := mload(add(rData, mul(idx, 0x20)))
                    mstore(rPtr, c0)
                    mstore(add(rPtr, 0x20), c1)
                    mstore(add(rPtr, 0x40), c2)
                }
            }
        }
    }
}
