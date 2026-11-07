// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {PoseidonConstants} from "./PoseidonConstants.sol";
import {InvalidMleProof} from "./MleProofErrors.sol";

/// @title PoseidonGate — Plonky2 Poseidon-12 gate constraints (Yul-optimized).
/// @notice Mirrors `plonky2::gates::poseidon::PoseidonGate::eval_unfiltered` for
/// the Goldilocks field. Produces 123 base-field constraint values at a random
/// point `r_gate_v2`, accumulating `filter * constraint_i` into the caller's
/// accumulator slot `acc[i]`.
///
/// Optimizations vs. the naïve port:
///  - State kept in contiguous memory (12 × 32-byte slots) instead of solidity
///    uint256[12] with copy-back-and-forth on every layer.
///  - The fixed circulant MDS is evaluated with Plonky2's exact integer-FFT
///    factorization; its only diagonal coefficient and sparse M00 are 8 and 25.
///  - Round constants for the current round loaded in a single 12-value block
///    per round instead of 12 separate library calls.
///  - S-box `x^7` inlined as 4 mulmod ops inside tight assembly loops.
///  - Constraint accumulation writes `acc[i]` directly in assembly (skip
///    Solidity bounds check + wrapper mulmod/addmod).
///  - `_mdsPartialLayerFast` and `_mdsPartialLayerInit` unrolled + in-place.
///
/// All uint64 Poseidon constants live in `PoseidonConstants.sol` as packed
/// big-endian `bytes` blobs. The gate evaluator takes a direct memory pointer
/// to each blob's data region at function entry and reads via
/// `shr(192, mload(ptr+offset))`.
///
/// The public-input hash (`hashNoPad`) shares the field, the constants and the
/// MDS factorization with the gate evaluator but runs its own permutation
/// (`_permute`): lazy modular reduction and every constant inlined as a
/// literal. See its doc comment for the bounds and the code-shape constraints.
library PoseidonGate {
    uint256 internal constant P = 0xFFFFFFFF00000001;
    uint256 internal constant SPONGE_WIDTH = 12;
    uint256 internal constant HALF_N_FULL_ROUNDS = 4;
    uint256 internal constant N_PARTIAL_ROUNDS = 22;

    // Wire layout (matches plonky2/src/gates/poseidon.rs).
    uint256 internal constant WIRE_SWAP = 24;
    uint256 internal constant START_DELTA = 25;
    uint256 internal constant START_FULL_0 = 29;
    uint256 internal constant START_PARTIAL = 65;
    uint256 internal constant START_FULL_1 = 87;

    /// @dev Plonky2's Poseidon `hash_no_pad` over the Goldilocks field.
    /// The sponge rate is eight, the state width is twelve, and the first four
    /// rate elements are returned.  A final short chunk overwrites only its
    /// occupied rate slots, exactly matching `PlonkyPermutation::set_from_slice`.
    function hashNoPad(uint256[] calldata inputs) internal pure returns (uint256[4] memory digest) {
        uint256[12] memory state;
        uint256 invalidProofSelector = uint32(InvalidMleProof.selector);

        for (uint256 offset = 0; offset < inputs.length; offset += 8) {
            uint256 remaining = inputs.length - offset;
            uint256 chunkLength = remaining < 8 ? remaining : 8;
            assembly ("memory-safe") {
                let source := add(inputs.offset, shl(5, offset))
                let end := add(source, shl(5, chunkLength))
                for { let slot := state } lt(source, end) {
                    source := add(source, 0x20)
                    slot := add(slot, 0x20)
                } {
                    let value := calldataload(source)
                    if iszero(lt(value, P)) {
                        mstore(0x00, shl(224, invalidProofSelector))
                        revert(0x00, 0x04)
                    }
                    mstore(slot, value)
                }
            }
            _permute(state);
        }

        digest[0] = state[0];
        digest[1] = state[1];
        digest[2] = state[2];
        digest[3] = state[3];
    }

    /// @dev Exact Plonky2 Poseidon-12 permutation of `state` (canonical in, canonical out),
    /// following `plonky2::hash::poseidon::Poseidon::poseidon` with `partial_rounds_fast`.
    /// Every constant is an inline literal taken from the `PoseidonConstants` blobs, so no
    /// round pays for blob pointer arithmetic; the MDS layer is the integer 3x4 FFT
    /// factorization of `_mdsLayerInline`, evaluated without intermediate reductions.
    ///
    /// The permutation is a set of short Yul functions over the twelve `state` words (plus
    /// scratch word 0x20 for the S-boxed s0). Keeping every function at a dozen locals or
    /// fewer is deliberate: the via-IR stack layout generator cannot keep long straight-line
    /// Yul with many temporaries on the stack, and a spilled word is re-expanded into an
    /// exponentially growing expression, which made a fully unrolled version uncompilable.
    ///
    /// Modular reduction is lazy: an unreduced word is only ever consumed by `mulmod`
    /// (which reduces its 256-bit operands exactly) or by another unreduced sum, and the
    /// twelve words are reduced once at the end.  Magnitude bounds, with p < 2^64:
    ///  - MDS input is canonical (S-box output); its exact integer circulant product is
    ///    < 264 * 2^64 < 2^73, so a full-round input never exceeds 2^73 + 2^64. The FFT
    ///    intermediates are signed and may wrap modulo 2^256, which is harmless because the
    ///    output rows are exact non-negative integers below 2^73.
    ///  - The initial partial matrix sums eleven products of such words by u64 entries:
    ///    < 11 * 2^74 * 2^64 < 2^142.
    ///  - Each partial round adds s0' * v < 2^65 * 2^64 to s1..s11 (< 2^142 after 22
    ///    rounds) and sets s0 to a twelve-term dot product < 2^70 + 11 * 2^142 * 2^64 < 2^210.
    /// Every bound is far below 2^256, so no addition overflows.
    function _permute(uint256[12] memory state) private pure {
        assembly ("memory-safe") {
            // state[p], state[p + 32] := x0^7, x1^7 over Goldilocks. The inputs may be any 256-bit
            // values (`mulmod` reduces its operands exactly); the results are canonical.
            function sbox2(p, x0, x1) {
                let x2 := mulmod(x0, x0, P)
                let x3 := mulmod(x0, x2, P)
                mstore(p, mulmod(x3, mulmod(x2, x2, P), P))
                let y2 := mulmod(x1, x1, P)
                let y3 := mulmod(x1, y2, P)
                mstore(add(p, 0x20), mulmod(y3, mulmod(y2, y2, P), P))
            }
            // Forward real 4-FFT of the group at `p` = state + 32*g, in place:
            // [a, b, c, d] = state[g, g+3, g+6, g+9]  ->  state[g] = a - c, state[g+3] = d - b,
            // state[g+6] = a + b + c + d, state[g+9] = a - b + c - d  (signed, wrapping mod 2^256).
            function forward(p) {
                let a := mload(p)
                let c := mload(add(p, 0xc0))
                let u1r := sub(a, c)
                let ac := add(a, c)
                let b := mload(add(p, 0x60))
                let d := mload(add(p, 0x120))
                let u1i := sub(d, b)
                let bd := add(b, d)
                mstore(p, u1r)
                mstore(add(p, 0x60), u1i)
                mstore(add(p, 0xc0), add(ac, bd))
                mstore(add(p, 0x120), sub(ac, bd))
            }
            // Frequency block two: the 3-point complex convolution of (state[g], state[g+3]) for
            // g = 0..2 with the kernel of `_mdsLayerInline`, written back in place.
            function blockTwo(st) {
                let a := mload(st)
                let b := mload(add(st, 0x60))
                let c := mload(add(st, 0x20))
                let d := mload(add(st, 0x80))
                let e := mload(add(st, 0x40))
                let f := mload(add(st, 0xa0))
                mstore(st, sub(add(add(add(add(shl(1, a), b), c), shl(4, d)), e), shl(2, f)))
                mstore(add(st, 0x60), sub(add(add(add(shl(1, b), d), shl(2, e)), f), add(a, shl(4, c))))
                mstore(add(st, 0x20), sub(add(add(add(shl(1, c), d), e), shl(4, f)), add(shl(2, a), b)))
                mstore(add(st, 0x80), sub(add(add(a, shl(1, d)), f), add(add(shl(2, b), c), shl(4, e))))
                mstore(add(st, 0x40), sub(add(add(shl(4, a), shl(1, e)), f), add(add(b, shl(2, c)), d)))
                mstore(add(st, 0xa0), sub(add(add(add(a, shl(4, b)), c), shl(1, f)), add(shl(2, d), e)))
            }
            // Frequency block one (coefficients [16, 32, 16]) on state[6..8], in place.
            function blockOne(st) {
                let x0 := mload(add(st, 0xc0))
                let x1 := mload(add(st, 0xe0))
                let x2 := mload(add(st, 0x100))
                let t := shl(4, add(add(x0, x1), x2))
                mstore(add(st, 0xc0), add(t, shl(4, x2)))
                mstore(add(st, 0xe0), add(t, shl(4, x0)))
                mstore(add(st, 0x100), add(t, shl(4, x1)))
            }
            // Frequency block three (coefficients [-1, -8, 2]) on state[9..11], in place.
            function blockThree(st) {
                let x0 := mload(add(st, 0x120))
                let x1 := mload(add(st, 0x140))
                let x2 := mload(add(st, 0x160))
                mstore(add(st, 0x120), sub(shl(3, x2), add(x0, shl(1, x1))))
                mstore(add(st, 0x140), sub(0, add(add(shl(3, x0), x1), shl(1, x2))))
                mstore(add(st, 0x160), sub(shl(1, x0), add(shl(3, x1), x2)))
            }
            // Inverse real 4-FFT of the group at `p`: state[g] = y + w + re + diag, state[g+3] =
            // y - w - im, state[g+6] = y + w - re, state[g+9] = y - w + im, where (re, im) is the
            // block-two output in state[g, g+3] and (y, w) the block one/three output in state[g+6, g+9].
            function inverse(p, diag) {
                let y := mload(add(p, 0xc0))
                let wv := mload(add(p, 0x120))
                let z0 := add(y, wv)
                let z1 := sub(y, wv)
                let re := mload(p)
                let im := mload(add(p, 0x60))
                mstore(p, add(add(z0, re), diag))
                mstore(add(p, 0x60), sub(z1, im))
                mstore(add(p, 0xc0), sub(z0, re))
                mstore(add(p, 0x120), add(z1, im))
            }
            // Full round 0: ALL_ROUND_CONSTANTS[0..12), S-box, lazy MDS (rows < 2^73).
            function fullRound0(st) {
                sbox2(st, add(mload(st), 0xb585f766f2144405), add(mload(add(st, 0x20)), 0x7746a55f43921ad7))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0xb2fb0d31cee799b4),
                    add(mload(add(st, 0x60)), 0x0f6760a4803427d7)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0xe10d666650f4e012),
                    add(mload(add(st, 0xa0)), 0x8cae14cb07d09bf1)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0xd438539c95f63e9f),
                    add(mload(add(st, 0xe0)), 0xef781c7ce35b4c3d)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0xcdc4a239b0c44426),
                    add(mload(add(st, 0x120)), 0x277fa208bf337bff)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0xe17653a29da578a1),
                    add(mload(add(st, 0x160)), 0xc54302f225db2c76)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // Full round 1: ALL_ROUND_CONSTANTS[12..24), S-box, lazy MDS (rows < 2^73).
            function fullRound1(st) {
                sbox2(st, add(mload(st), 0x86287821f722c881), add(mload(add(st, 0x20)), 0x59cd1a8a41c18e55))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0xc3b919ad495dc574),
                    add(mload(add(st, 0x60)), 0xa484c4c5ef6a0781)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0x308bbd23dc5416cc),
                    add(mload(add(st, 0xa0)), 0x6e4a40c18f30c09c)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0x9a2eedb70d8f8cfa),
                    add(mload(add(st, 0xe0)), 0xe360c6e0ae486f38)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0xd5c7718fbfc647fb),
                    add(mload(add(st, 0x120)), 0xc35eae071903ff0b)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0x849c2656969c4be7),
                    add(mload(add(st, 0x160)), 0xc0572c8c08cbbbad)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // Full round 2: ALL_ROUND_CONSTANTS[24..36), S-box, lazy MDS (rows < 2^73).
            function fullRound2(st) {
                sbox2(st, add(mload(st), 0xe9fa634a21de0082), add(mload(add(st, 0x20)), 0xf56f6d48959a600d))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0xf7d713e806391165),
                    add(mload(add(st, 0x60)), 0x8297132b32825daf)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0xad6805e0e30b2c8a),
                    add(mload(add(st, 0xa0)), 0xac51d9f5fcf8535e)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0x502ad7dc18c2ad87),
                    add(mload(add(st, 0xe0)), 0x57a1550c110b3041)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0x66bbd30e6ce0e583),
                    add(mload(add(st, 0x120)), 0x0da2abef589d644e)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0xf061274fdb150d61),
                    add(mload(add(st, 0x160)), 0x28b8ec3ae9c29633)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // Full round 3: ALL_ROUND_CONSTANTS[36..48), S-box, lazy MDS (rows < 2^73).
            function fullRound3(st) {
                sbox2(st, add(mload(st), 0x92a756e67e2b9413), add(mload(add(st, 0x20)), 0x70e741ebfee96586))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0x019d5ee2af82ec1c),
                    add(mload(add(st, 0x60)), 0x6f6f2ed772466352)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0x7cf416cfe7e14ca1),
                    add(mload(add(st, 0xa0)), 0x61df517b86a46439)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0x85dc499b11d77b75),
                    add(mload(add(st, 0xe0)), 0x4b959b48b9c10733)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0xe8be3e5da8043e57),
                    add(mload(add(st, 0x120)), 0xf5c0bc1de6da8699)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0x40b12cbf09ef74bf),
                    add(mload(add(st, 0x160)), 0xa637093ecb2ad631)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // Full round 26: ALL_ROUND_CONSTANTS[312..324), S-box, lazy MDS (rows < 2^73).
            function fullRound26(st) {
                sbox2(st, add(mload(st), 0x475cd3205a3bdcde), add(mload(add(st, 0x20)), 0x18a42105c31b7e88))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0x023e7414af663068),
                    add(mload(add(st, 0x60)), 0x15147108121967d7)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0xe4a3dff1d7d6fef9),
                    add(mload(add(st, 0xa0)), 0x01a8d1a588085737)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0x11b4c74eda62beef),
                    add(mload(add(st, 0xe0)), 0xe587cc0d69a73346)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0x1ff7327017aa2a6e),
                    add(mload(add(st, 0x120)), 0x594e29c42473d06b)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0xf6f31db1899b12d5),
                    add(mload(add(st, 0x160)), 0xc02ac5e47312d3ca)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // Full round 27: ALL_ROUND_CONSTANTS[324..336), S-box, lazy MDS (rows < 2^73).
            function fullRound27(st) {
                sbox2(st, add(mload(st), 0xe70201e960cb78b8), add(mload(add(st, 0x20)), 0x6f90ff3b6a65f108))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0x42747a7245e7fa84),
                    add(mload(add(st, 0x60)), 0xd1f507e43ab749b2)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0x1c86d265f15750cd),
                    add(mload(add(st, 0xa0)), 0x3996ce73dd832c1c)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0x8e7fba02983224bd),
                    add(mload(add(st, 0xe0)), 0xba0dec7103255dd4)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0x9e9cbd781628fc5b),
                    add(mload(add(st, 0x120)), 0xdae8645996edd6a5)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0xdebe0853b1a1d378),
                    add(mload(add(st, 0x160)), 0xa49229d24d014343)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // Full round 28: ALL_ROUND_CONSTANTS[336..348), S-box, lazy MDS (rows < 2^73).
            function fullRound28(st) {
                sbox2(st, add(mload(st), 0x7be5b9ffda905e1c), add(mload(add(st, 0x20)), 0xa3c95eaec244aa30))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0x0230bca8f4df0544),
                    add(mload(add(st, 0x60)), 0x4135c2bebfe148c6)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0x166fc0cc438a3c72),
                    add(mload(add(st, 0xa0)), 0x3762b59a8ae83efa)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0xe8928a4c89114750),
                    add(mload(add(st, 0xe0)), 0x2a440b51a4945ee5)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0x80cefd2b7d99ff83),
                    add(mload(add(st, 0x120)), 0xbb9879c6e61fd62a)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0x6e7c8f1a84265034),
                    add(mload(add(st, 0x160)), 0x164bb2de1bbeddc8)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // Full round 29: ALL_ROUND_CONSTANTS[348..360), S-box, lazy MDS (rows < 2^73).
            function fullRound29(st) {
                sbox2(st, add(mload(st), 0xf3c12fe54d5c653b), add(mload(add(st, 0x20)), 0x40b9e922ed9771e2))
                sbox2(
                    add(st, 0x40),
                    add(mload(add(st, 0x40)), 0x551f5b0fbe7b1840),
                    add(mload(add(st, 0x60)), 0x25032aa7c4cb1811)
                )
                sbox2(
                    add(st, 0x80),
                    add(mload(add(st, 0x80)), 0xaaed34074b164346),
                    add(mload(add(st, 0xa0)), 0x8ffd96bbf9c9c81d)
                )
                sbox2(
                    add(st, 0xc0),
                    add(mload(add(st, 0xc0)), 0x70fc91eb5937085c),
                    add(mload(add(st, 0xe0)), 0x7f795e2a5f915440)
                )
                sbox2(
                    add(st, 0x100),
                    add(mload(add(st, 0x100)), 0x4543d9df5476d3cb),
                    add(mload(add(st, 0x120)), 0xf172d73e004fc90d)
                )
                sbox2(
                    add(st, 0x140),
                    add(mload(add(st, 0x140)), 0xdfd1c4febcc81238),
                    add(mload(add(st, 0x160)), 0xbc8dfb627fe558fc)
                )
                mstore(0x20, mload(st)) // S-boxed s0 for the diagonal term
                forward(st)
                forward(add(st, 0x20))
                forward(add(st, 0x40))
                blockTwo(st)
                blockOne(st)
                blockThree(st)
                inverse(st, shl(3, mload(0x20)))
                inverse(add(st, 0x20), 0)
                inverse(add(st, 0x40), 0)
            }
            // `partial_first_constant_layer` then `mds_partial_layer_init`: state[0] is only offset
            // by its constant, state[c] := sum_r s_r * M[r-1][c-1] (r, c in 1..11; row-major literals).
            function partialInit(st) {
                mstore(st, add(mload(st), 0x3cc3f892184df408))
                let s1 := add(mload(add(st, 0x20)), 0xe993fd841e7e97f1)
                let s2 := add(mload(add(st, 0x40)), 0xf2831d3575f0f3af)
                let s3 := add(mload(add(st, 0x60)), 0xd2500e0a350994ca)
                let s4 := add(mload(add(st, 0x80)), 0xc5571f35d7288633)
                let s5 := add(mload(add(st, 0xa0)), 0x91d89c5184109a02)
                let s6 := add(mload(add(st, 0xc0)), 0xf37f925d04e5667b)
                let s7 := add(mload(add(st, 0xe0)), 0x2d6e448371955a69)
                let s8 := add(mload(add(st, 0x100)), 0x740ef19ce01398a1)
                let s9 := add(mload(add(st, 0x120)), 0x694d24c0752fdf45)
                let s10 := add(mload(add(st, 0x140)), 0x60936af96ee2f148)
                let s11 := add(mload(add(st, 0x160)), 0xc33448feadc78f0c)
                {
                    let acc := mul(s1, 0x80772dc2645b280b)
                    acc := add(acc, mul(s2, 0xe796d293a47a64cb))
                    acc := add(acc, mul(s3, 0xdcedab70f40718ba))
                    acc := add(acc, mul(s4, 0xf4a437f2888ae909))
                    acc := add(acc, mul(s5, 0xf97abba0dffb6c50))
                    acc := add(acc, mul(s6, 0x7f8e41e0b0a6cdff))
                    acc := add(acc, mul(s7, 0x726af914971c1374))
                    acc := add(acc, mul(s8, 0x64dd936da878404d))
                    acc := add(acc, mul(s9, 0x85418a9fef8a9890))
                    acc := add(acc, mul(s10, 0x156048ee7a738154))
                    acc := add(acc, mul(s11, 0xd841e8ef9dde8ba0))
                    mstore(add(st, 0x20), acc)
                }
                {
                    let acc := mul(s1, 0xdc927721da922cf8)
                    acc := add(acc, mul(s2, 0xb124c33152a2421a))
                    acc := add(acc, mul(s3, 0x14a4a64da0b2668f))
                    acc := add(acc, mul(s4, 0xc537d44dc2875403))
                    acc := add(acc, mul(s5, 0x5e40f0c9bb82aab5))
                    acc := add(acc, mul(s6, 0x4b1ba8d40afca97d))
                    acc := add(acc, mul(s7, 0x1d7f8a2cce1a9d00))
                    acc := add(acc, mul(s8, 0x4db9a2ead2bd7262))
                    acc := add(acc, mul(s9, 0xd8a2eb7ef5e707ad))
                    acc := add(acc, mul(s10, 0x91f7562377e81df5))
                    acc := add(acc, mul(s11, 0x156048ee7a738154))
                    mstore(add(st, 0x40), acc)
                }
                {
                    let acc := mul(s1, 0xc1978156516879ad)
                    acc := add(acc, mul(s2, 0x0ee5dc0ce131268a))
                    acc := add(acc, mul(s3, 0x4715b8e5ab34653b))
                    acc := add(acc, mul(s4, 0x7f68007619fd8ba9))
                    acc := add(acc, mul(s5, 0x5996a80497e24a6b))
                    acc := add(acc, mul(s6, 0x623708f28fca70e8))
                    acc := add(acc, mul(s7, 0x18737784700c75cd))
                    acc := add(acc, mul(s8, 0xbe2e19f6d07f1a83))
                    acc := add(acc, mul(s9, 0xbfe85ababed2d882))
                    acc := add(acc, mul(s10, 0xd8a2eb7ef5e707ad))
                    acc := add(acc, mul(s11, 0x85418a9fef8a9890))
                    mstore(add(st, 0x60), acc)
                }
                {
                    let acc := mul(s1, 0x90e80c591f48b603)
                    acc := add(acc, mul(s2, 0xa9032a52f930fae6))
                    acc := add(acc, mul(s3, 0x1e8916a99c93a88e))
                    acc := add(acc, mul(s4, 0xa4911db6a32612da))
                    acc := add(acc, mul(s5, 0x07084430a7307c9a))
                    acc := add(acc, mul(s6, 0xbf150dc4914d380f))
                    acc := add(acc, mul(s7, 0x7fb45d605dd82838))
                    acc := add(acc, mul(s8, 0x02290fe23c20351a))
                    acc := add(acc, mul(s9, 0xbe2e19f6d07f1a83))
                    acc := add(acc, mul(s10, 0x4db9a2ead2bd7262))
                    acc := add(acc, mul(s11, 0x64dd936da878404d))
                    mstore(add(st, 0x80), acc)
                }
                {
                    let acc := mul(s1, 0x3a2432625475e3ae)
                    acc := add(acc, mul(s2, 0x7e33ca8c814280de))
                    acc := add(acc, mul(s3, 0xbba4b5d86b9a3b2c))
                    acc := add(acc, mul(s4, 0x2f7e9aade3fdaec1))
                    acc := add(acc, mul(s5, 0xad2f570a5b8545aa))
                    acc := add(acc, mul(s6, 0xc26a083554767106))
                    acc := add(acc, mul(s7, 0x862361aeab0f9b6e))
                    acc := add(acc, mul(s8, 0x7fb45d605dd82838))
                    acc := add(acc, mul(s9, 0x18737784700c75cd))
                    acc := add(acc, mul(s10, 0x1d7f8a2cce1a9d00))
                    acc := add(acc, mul(s11, 0x726af914971c1374))
                    mstore(add(st, 0xa0), acc)
                }
                {
                    let acc := mul(s1, 0x00a2d4321cca94fe)
                    acc := add(acc, mul(s2, 0xad11180f69a8c29e))
                    acc := add(acc, mul(s3, 0xe76649f9bd5d5c2e))
                    acc := add(acc, mul(s4, 0xe7ffd578da4ea43d))
                    acc := add(acc, mul(s5, 0xab7f81fef4274770))
                    acc := add(acc, mul(s6, 0x753b8b1126665c22))
                    acc := add(acc, mul(s7, 0xc26a083554767106))
                    acc := add(acc, mul(s8, 0xbf150dc4914d380f))
                    acc := add(acc, mul(s9, 0x623708f28fca70e8))
                    acc := add(acc, mul(s10, 0x4b1ba8d40afca97d))
                    acc := add(acc, mul(s11, 0x7f8e41e0b0a6cdff))
                    mstore(add(st, 0xc0), acc)
                }
                {
                    let acc := mul(s1, 0x77736f524010c932)
                    acc := add(acc, mul(s2, 0xc75ac6d5b5a10ff3))
                    acc := add(acc, mul(s3, 0xaf8e2518a1ece54d))
                    acc := add(acc, mul(s4, 0x43a608e7afa6b5c2))
                    acc := add(acc, mul(s5, 0xcb81f535cf98c9e9))
                    acc := add(acc, mul(s6, 0xab7f81fef4274770))
                    acc := add(acc, mul(s7, 0xad2f570a5b8545aa))
                    acc := add(acc, mul(s8, 0x07084430a7307c9a))
                    acc := add(acc, mul(s9, 0x5996a80497e24a6b))
                    acc := add(acc, mul(s10, 0x5e40f0c9bb82aab5))
                    acc := add(acc, mul(s11, 0xf97abba0dffb6c50))
                    mstore(add(st, 0xe0), acc)
                }
                {
                    let acc := mul(s1, 0x904d3f2804a36c54)
                    acc := add(acc, mul(s2, 0xf0674a8dc5a387ec))
                    acc := add(acc, mul(s3, 0xdcda1344cdca873f))
                    acc := add(acc, mul(s4, 0xca46546aa99e1575))
                    acc := add(acc, mul(s5, 0x43a608e7afa6b5c2))
                    acc := add(acc, mul(s6, 0xe7ffd578da4ea43d))
                    acc := add(acc, mul(s7, 0x2f7e9aade3fdaec1))
                    acc := add(acc, mul(s8, 0xa4911db6a32612da))
                    acc := add(acc, mul(s9, 0x7f68007619fd8ba9))
                    acc := add(acc, mul(s10, 0xc537d44dc2875403))
                    acc := add(acc, mul(s11, 0xf4a437f2888ae909))
                    mstore(add(st, 0x100), acc)
                }
                {
                    let acc := mul(s1, 0xbf9b39e28a16f354)
                    acc := add(acc, mul(s2, 0xb36d43120eaa5e2b))
                    acc := add(acc, mul(s3, 0xcd080204256088e5))
                    acc := add(acc, mul(s4, 0xdcda1344cdca873f))
                    acc := add(acc, mul(s5, 0xaf8e2518a1ece54d))
                    acc := add(acc, mul(s6, 0xe76649f9bd5d5c2e))
                    acc := add(acc, mul(s7, 0xbba4b5d86b9a3b2c))
                    acc := add(acc, mul(s8, 0x1e8916a99c93a88e))
                    acc := add(acc, mul(s9, 0x4715b8e5ab34653b))
                    acc := add(acc, mul(s10, 0x14a4a64da0b2668f))
                    acc := add(acc, mul(s11, 0xdcedab70f40718ba))
                    mstore(add(st, 0x120), acc)
                }
                {
                    let acc := mul(s1, 0x3a1ded54a6cd058b)
                    acc := add(acc, mul(s2, 0x6f232aab4b533a25))
                    acc := add(acc, mul(s3, 0xb36d43120eaa5e2b))
                    acc := add(acc, mul(s4, 0xf0674a8dc5a387ec))
                    acc := add(acc, mul(s5, 0xc75ac6d5b5a10ff3))
                    acc := add(acc, mul(s6, 0xad11180f69a8c29e))
                    acc := add(acc, mul(s7, 0x7e33ca8c814280de))
                    acc := add(acc, mul(s8, 0xa9032a52f930fae6))
                    acc := add(acc, mul(s9, 0x0ee5dc0ce131268a))
                    acc := add(acc, mul(s10, 0xb124c33152a2421a))
                    acc := add(acc, mul(s11, 0xe796d293a47a64cb))
                    mstore(add(st, 0x140), acc)
                }
                {
                    let acc := mul(s1, 0x42392870da5737cf)
                    acc := add(acc, mul(s2, 0x3a1ded54a6cd058b))
                    acc := add(acc, mul(s3, 0xbf9b39e28a16f354))
                    acc := add(acc, mul(s4, 0x904d3f2804a36c54))
                    acc := add(acc, mul(s5, 0x77736f524010c932))
                    acc := add(acc, mul(s6, 0x00a2d4321cca94fe))
                    acc := add(acc, mul(s7, 0x3a2432625475e3ae))
                    acc := add(acc, mul(s8, 0x90e80c591f48b603))
                    acc := add(acc, mul(s9, 0xc1978156516879ad))
                    acc := add(acc, mul(s10, 0xdc927721da922cf8))
                    acc := add(acc, mul(s11, 0x80772dc2645b280b))
                    mstore(add(st, 0x160), acc)
                }
            }
            // Partial round 0: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[0], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[0] and VS[0] as literals (lazy sums).
            function partialRound0(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x74cb2e819ae421ab)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x3d999c961b7c63b0))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x94877900674181c3)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x814e82efcd172529))
                    mstore(add(st, 0x40), add(s, mul(s0, 0xc6c67cc37a2a2bbd)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x2421e5d236704588))
                    mstore(add(st, 0x60), add(s, mul(s0, 0xd667c2055387940f)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x887af7d4dd482328))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x0ba63a63e94b5ff0)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0xa5e9c291f6119b27))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x99460cc41b8f079f)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xbdc52b2676a4b4aa))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x7ff02375ed524bb3)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x64832009d29bcf57))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0xea0870b47a8caf0e)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x09c4155174a552cc))
                    mstore(add(st, 0x100), add(s, mul(s0, 0xabcad82633b7bc9d)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x463f9ee03d290810))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x3b8d135261052241)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0xc810936e64982542))
                    mstore(add(st, 0x140), add(s, mul(s0, 0xfb4515f5e5b0d539)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x043b1c289f7bc3ac))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x3ee8011c2b37f77c)))
                }
                mstore(st, d)
            }
            // Partial round 1: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[1], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[1] and VS[1] as literals (lazy sums).
            function partialRound1(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xd2559d2370e7f663)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x673655aae8be5a8b))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x0adef3740e71c726)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xd510fe714f39fa10))
                    mstore(add(st, 0x40), add(s, mul(s0, 0xa37bf67c6f986559)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x2c68a099b51c9e73))
                    mstore(add(st, 0x60), add(s, mul(s0, 0xc6b16f7ed4fa1b00)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0xa667bfa9aa96999d))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x6a065da88d8bfc3c)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x4d67e72f063e2108))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x4cabc0916844b46f)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xf84dde3e6acda179))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x407faac0f02e78d1)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x40f9cc8c08f80981))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x07a786d9cf0852cf)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x5ead032050097142))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x42433fb6949a629a)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x6591b02092d671bb))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x891682a147ce43b0)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x00e18c71963dd1b7))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x26cfd58e7b003b55)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x8a21bcd24a14218a))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x2bbf0ed7b657acb3)))
                }
                mstore(st, d)
            }
            // Partial round 2: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[2], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[2] and VS[2] as literals (lazy sums).
            function partialRound2(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x62bf78acf843d17c)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x202800f4addbdc87))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x481ac7746b159c67)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xe4b5bdb1cc3504ff))
                    mstore(add(st, 0x40), add(s, mul(s0, 0xe367de32f108e278)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xbe32b32a825596e7))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x73f260087ad28bec)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x8e0f68c5dc223b9a))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x5cfc82216bc1bdca)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x58022d9e1c256ce3))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0xcaccc870a2663a0e)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x584d29227aa073ac))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xdb69cd7b4298c45d)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x8b9352ad04bef9e7))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x7bc9e0c57243e62d)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xaead42a3f445ecbf))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x3cc51c5d368693ae)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x3c667a1d833a3cca))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x366b4e8cc068895b)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0xda6f61838efa1ffe))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x2bd18715cdabbca4)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xe8f749470bd7c446))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xa752061c4f33b8cf)))
                }
                mstore(st, d)
            }
            // Partial round 3: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[3], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[3] and VS[3] as literals (lazy sums).
            function partialRound3(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xd5ab7b67e14d1fb4)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xc5b85bab9e5b3869))
                    mstore(add(st, 0x20), add(s, mul(s0, 0xb22d2432b72d5098)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x45245258aec51cf7))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x9e18a487f44d2fe4)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x16e6b8e68b931830))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x4b39e14ce22abd3c)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0xe2ae0f051418112c))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x9e77fde2eb315e0d)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x0470e26a0093a65b))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0xca5e0385fe67014d)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x6bef71973a8146ed))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x0c2cb99bf1b6bddb)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x119265be51812daf))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x99ec1cd2a4460bfe)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xb0be7356254bea2e))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x8577a815a2ff843f)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x8584defff7589bd7))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x7d80a6b4fd6518a5)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x3c5fe4aeb1fb52ba))
                    mstore(add(st, 0x140), add(s, mul(s0, 0xeb6c67123eab62cb)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x9e7cd88acf543a5e))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x8f7851650eca21a5)))
                }
                mstore(st, d)
            }
            // Partial round 4: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[4], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[4] and VS[4] as literals (lazy sums).
            function partialRound4(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xb9fe2ae6e0969bdc)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x179be4bba87f0a8c))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x11ba9a1b81718c2a)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xacf63d95d8887355))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x9f7d798a3323410c)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x6696670196b0074f))
                    mstore(add(st, 0x60), add(s, mul(s0, 0xa821855c8c1cf5e5)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0xd99ddf1fe75085f9))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x535e8d6fac0031b2)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0xc2597881fef0283b))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x404e7c751b634320)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xcf48395ee6c54f14))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xa729353f6e55d354)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x15226a8e4cd8d3b6))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x4db97d92e58bb831)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xc053297389af5d3b))
                    mstore(add(st, 0x100), add(s, mul(s0, 0xb53926c27897bf7d)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x2c08893f0d1580e2))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x965040d52fe115c5)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x0ed3cbcff6fcc5ba))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x9565fa41ebd31fd7)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xc82f510ecf81f6d0))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xaae4438c877ea8f4)))
                }
                mstore(st, d)
            }
            // Partial round 5: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[5], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[5] and VS[5] as literals (lazy sums).
            function partialRound5(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xe33fdf79f92a10e8)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x94b06183acb715cc))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x37f4e36af6073c6e)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x500392ed0d431137))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x4edc0918210800e9)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x861cc95ad5c86323))
                    mstore(add(st, 0x60), add(s, mul(s0, 0xc44998e99eae4188)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x05830a443f86c4ac))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x9f4310d05d068338)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x3b68225874a20a7c))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x9ec7fe4350680f29)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x10b3309838e236fb))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xc5b2c1fdc0b50874)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x9b77fc8bcd559e2c))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0xa01920c5ef8b2ebe)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xbdecf5e0cb9cb213))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x59fa6f8bd91d58ba)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x30276f1221ace5fa))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x8bfc9eb89b515a82)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x7935dd342764a144))
                    mstore(add(st, 0x140), add(s, mul(s0, 0xbe86a7a2555ae775)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xeac6db520bb03708))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xcbb8bbaa3810babf)))
                }
                mstore(st, d)
            }
            // Partial round 6: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[6], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[6] and VS[6] as literals (lazy sums).
            function partialRound6(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x0ea2bb4c2b25989b)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x7186a80551025f8f))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x577f9a9e7ee3f9c2)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x622247557e9b5371))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x88c522b949ace7b1)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xc4cbe326d1ad9742))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x82f07007c8b72106)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x55f1523ac6a23ea2))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x8283d37c6675b50e)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0xa13dfe77a3d52f53))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x98b074d9bbac1123)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xe30750b6301c0452))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x75c56fb7758317c1)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x08bd488070a3a32b))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0xfed24e206052bc72)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xcd800caef5b72ae3))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x26d7c3d1bc07dae5)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x83329c90f04233ce))
                    mstore(add(st, 0x120), add(s, mul(s0, 0xf88c5e441e28dbb4)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0xb5b99e6664a0a3ee))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x4fe27f9f96615270)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x6b0731849e200a7f))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x514d4ba49c2b14fe)))
                }
                mstore(st, d)
            }
            // Partial round 7: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[7], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[7] and VS[7] as literals (lazy sums).
            function partialRound7(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xca9121fbf9d38f06)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xec3fabc192b01799))
                    mstore(add(st, 0x20), add(s, mul(s0, 0xf02a3ac068ee110b)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x382b38cee8ee5375))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x0a3630dafb8ae2d7)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x3bfb6c3f0e616572))
                    mstore(add(st, 0x60), add(s, mul(s0, 0xce0dc874eaf9b55c)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x514abd0cf6c7bc86))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x9a95f6cff5b55c7e)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x47521b1361dcc546))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x626d76abfed00c7b)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x178093843f863d14))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xa0c1cf1251c204ad)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xad1003c5d28918e7))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0xdaebd3006321052c)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x738450e42495bc81))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x3d4bd48b625a8065)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xaf947c59af5e4047))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x7f1e584e071f6ed2)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x4653fb0685084ef2))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x720574f0501caed3)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x057fde2062ae35bf))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xe3260ba93d23540a)))
                }
                mstore(st, d)
            }
            // Partial round 8: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[8], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[8] and VS[8] as literals (lazy sums).
            function partialRound8(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xbdd9b0aa81f58fa4)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xe376678d843ce55e))
                    mstore(add(st, 0x20), add(s, mul(s0, 0xab1cbd41d8c1e335)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x66f3860d7514e7fc))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x9322ed4c0bc2df01)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x7817f3dfff8b4ffa))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x51c3c0983d4284e5)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x3929624a9def725b))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x94178e291145c231)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x0126ca37f215a80a))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0xfd0f1a973d6b2085)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xfce2f5d02762a303))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xd427ad96e2b39719)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x1bc927375febbad7))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x8a52437fecaac06b)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x85b481e5243f60bf))
                    mstore(add(st, 0x100), add(s, mul(s0, 0xdc20ee4b8c4c9a80)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x2d3c5f42a39c91a0))
                    mstore(add(st, 0x120), add(s, mul(s0, 0xa2c98e9549da2100)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x0811719919351ae8))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x1603fe12613db5b6)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xf669de0add993131))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x0e174929433c5505)))
                }
                mstore(st, d)
            }
            // Partial round 9: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[9], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[9] and VS[9] as literals (lazy sums).
            function partialRound9(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x83079fa4ecf20d7e)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x7de38bae084da92d))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x3d4eab2b8ef5f796)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x5b848442237e8a9b))
                    mstore(add(st, 0x40), add(s, mul(s0, 0xcfff421583896e22)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xf6c705da84d57310))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x4143cb32d39ac3d9)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x31e6a4bdb6a49017))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x22365051b78a5b65)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x889489706e5c5c0f))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x6f7fd010d027c9b6)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x0e4a205459692a1b))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xd9dd36fba77522ab)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xbac3fa75ee26f299))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0xa44cf1cb33e37165)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x5f5894f4057d755e))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x3fc83d3038c86417)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xb0dc3ecd724bb076))
                    mstore(add(st, 0x120), add(s, mul(s0, 0xc4588d418e88d270)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x5e34d8554a6452ba))
                    mstore(add(st, 0x140), add(s, mul(s0, 0xce1320f10ab80fe2)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x04f78fd8c1fdcc5f))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xdb5eadbbec18de5d)))
                }
                mstore(st, d)
            }
            // Partial round 10: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[10], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[10] and VS[10] as literals (lazy sums).
            function partialRound10(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x650b838edfcc4ad3)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x4dd19c38779512ea))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x1183dfce7c454afd)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xdb79ba02704620e9))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x21cea4aa3d3ed949)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x92a29a3675a5d2be))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x0fce6f70303f2304)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0xd5177029fe495166))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x19557d34b55551be)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0xd32b3298a13330c1))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x4c56f689afc5bbc9)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x251c4a3eb2c5f8fd))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xa1e920844334f944)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xe1c48b26e0d98825))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0xbad66d423d2ec861)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x3301d3362a4ffccb))
                    mstore(add(st, 0x100), add(s, mul(s0, 0xf318c785dc9e0479)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x09bb6c88de8cd178))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x99e2032e765ddd81)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0xdc05b676564f538a))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x400ccc9906d66f45)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x60192d883e473fee))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xe1197454db2e0dd9)))
                }
                mstore(st, d)
            }
            // Partial round 11: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[11], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[11] and VS[11] as literals (lazy sums).
            function partialRound11(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x77180c88583c76ac)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x16b9774801ac44a0))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x84d1ecc4d53d2ff1)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x3cb8411e786d3c8e))
                    mstore(add(st, 0x40), add(s, mul(s0, 0xd8af8b9ceb4e11b6)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xa86e9cf505072491))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x335856bb527b52f4)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x0178928152e109ae))
                    mstore(add(st, 0x80), add(s, mul(s0, 0xc756f17fb59be595)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x5317b905a6e1ab7b))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0xc0654e4ea5553a78)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xda20b3be7f53d59f))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x9e9a46b61f2ea942)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xcb97dedecebee9ad))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x14fc8b5b3b809127)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x4bd545218c59f58d))
                    mstore(add(st, 0x100), add(s, mul(s0, 0xd7009f0f103be413)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x77dc8d856c05a44a))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x3e0ee7b7a9fb4601)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x87948589e4f243fd))
                    mstore(add(st, 0x140), add(s, mul(s0, 0xa74e888922085ed7)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x7e5217af969952c2))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xe80a7cde3d4ac526)))
                }
                mstore(st, d)
            }
            // Partial round 12: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[12], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[12] and VS[12] as literals (lazy sums).
            function partialRound12(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xaf8c20753143a180)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xbc58987d06a84e4d))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x238aa6daa612186d)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x0b5d420244c9cae3))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x9137a5c630bad4b4)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xa3c4711b938c02c0))
                    mstore(add(st, 0x60), add(s, mul(s0, 0xc7db3817870c5eda)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x3aace640a3e03990))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x217e4f04e5718dc9)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x865a0f3249aacd8a))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0xcae814e2817bd99d)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x8d00b2a7dbed06c7))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0xe3292e7ab770a8ba)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x6eacb905beb7e2f8))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x7bb36ef70b6b9482)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x045322b216ec3ec7))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x3c7835fb85bca2d3)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xeb9de00d594828e6))
                    mstore(add(st, 0x120), add(s, mul(s0, 0xfe2cdf8ee3c25e86)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x088c5f20df9e5c26))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x61b3915ad7274b20)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xf555f4112b19781f))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xeab75ca7c918e4ef)))
                }
                mstore(st, d)
            }
            // Partial round 13: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[13], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[13] and VS[13] as literals (lazy sums).
            function partialRound13(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xb8ccfe9989a39175)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xa8cedbff1813d3a7))
                    mstore(add(st, 0x20), add(s, mul(s0, 0xd6e15ffc055e154e)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x50dcaee0fd27d164))
                    mstore(add(st, 0x40), add(s, mul(s0, 0xec67881f381a32bf)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xf1cb02417e23bd82))
                    mstore(add(st, 0x60), add(s, mul(s0, 0xfbb1196092bf409c)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0xfaf322786e2abe8b))
                    mstore(add(st, 0x80), add(s, mul(s0, 0xdc9d2e07830ba226)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x937a4315beb5d9b6))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x0698ef3245ff7988)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x1b18992921a11d85))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x194fae2974f8b576)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x7d66c4368b3c497b))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x7a5d9bea6ca4910e)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x0e7946317a6b4e99))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x7aebfea95ccdd1c9)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xbe4430134182978b))
                    mstore(add(st, 0x120), add(s, mul(s0, 0xf9bd38a67d5f0e86)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x3771e82493ab262d))
                    mstore(add(st, 0x140), add(s, mul(s0, 0xfa65539de65492d8)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xa671690d8095ce82))
                    mstore(add(st, 0x160), add(s, mul(s0, 0xf0dfcbe7653ff787)))
                }
                mstore(st, d)
            }
            // Partial round 14: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[14], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[14] and VS[14] as literals (lazy sums).
            function partialRound14(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x954a1729f60cc9c5)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xb035585f6e929d9d))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x0bd87ad390420258)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xba1579c7e219b954))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x0ad8617bca9e33c8)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xcb201cf846db4ba3))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x0c00ad377a1e2666)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x287bf9177372cf45))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x0ac6fc58b3f0518f)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0xa350e4f61147d0a6))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x0c0cc8a892cc4173)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xd5d0ecfb50bcff99))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x0c210accb117bc21)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x2e166aa6c776ed21))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x0b73630dbb46ca18)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xe1e66c991990e282))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x0c8be4920cbd4a54)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x662b329b01e7bb38))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x0bfe877a21be1690)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x8aa674b36144d9a9))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x0ae790559b0ded81)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xcbabf78f97f95e65))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x0bf50db2f8d6ce31)))
                }
                mstore(st, d)
            }
            // Partial round 15: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[15], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[15] and VS[15] as literals (lazy sums).
            function partialRound15(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xdeb5b550c4dca53b)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xeec24b15a06b53fe))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x000cf29427ff7c58)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xc8a7aa07c5633533))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x000bd9b3cf49eec8)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xefe9c6fa4311ad51))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x000d1dc8aa81fb26)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0xb9173f13977109a1))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x000bc792d5c394ef)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x69ce43c9cc94aedc))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x000d2ae0b2266453)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xecf623c9cd118815))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x000d413f12c496c1)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x28625def198c33c7))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x000c84128cfed618)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xccfc5f7de5c3636a))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x000db5ebd48fc0d4)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xf5e6c40f1621c299))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x000d1b77326dcb90)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0xcec0e58c34cb64b1))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x000beb0ccc145421)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xa868ea113387939f))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x000d10e5b22b11d1)))
                }
                mstore(st, d)
            }
            // Partial round 16: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[16], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[16] and VS[16] as literals (lazy sums).
            function partialRound16(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xf01bb0b00f77011e)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xd8dddbdc5ce4ef45))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x00000e24c99adad8)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xacfc51de8131458c))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x00000cf389ed4bc8)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x146bb3c0fe499ac0))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x00000e580cbf6966)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x9e65309f15943903))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x00000cde5fd7e04f)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x80d0ad980773aa70))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x00000e63628041b3)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0xf97817d4ddbf0607))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x00000e7e81a87361)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xe4626620a75ba276))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x00000dabe78f6d98)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x0dfdc7fd6fc74f66))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x00000efb14cac554)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xf464864ad6f2bb93))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x00000e5574743b10)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x02d55e52a5d44414))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x00000d05709f42c1)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xdd8de62487c40925))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x00000e4690c96af1)))
                }
                mstore(st, d)
            }
            // Partial round 17: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[17], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[17] and VS[17] as literals (lazy sums).
            function partialRound17(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0xa1ebb404b676afd9)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0xc15acf44759545a3))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x0000000f7157bc98)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xcbfdcf39869719d4))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x0000000e3006d948)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x33f62042e2f80225))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x0000000fa65811e6)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x2599c5ead81d8fa3))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x0000000e0d127e2f)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x0b306cb6c1d7c8d0))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x0000000fc18bfe53)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x658c80d3df3729b1))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x0000000fd002d901)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xe8d1b2b21b41429c))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x0000000eed6461d8)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xa1b67f09d4b3ccb8))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x0000001068562754)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x0e1adf8b84437180))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x0000000fa0236f50)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x0d593a5e584af47b))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x0000000e3af13ee1)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xa023d94c56e151c7))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x0000000fa460f6d1)))
                }
                mstore(st, d)
            }
            // Partial round 18: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[18], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[18] and VS[18] as literals (lazy sums).
            function partialRound18(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x860b6e1597a0173e)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x49026cc3a4afc5a6))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x0000000011131738)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xe06dff00ab25b91b))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x000000000f56d588)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x0ab38c561e8850ff))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x0000000011050f86)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x92c3c8275e105eeb))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x000000000f848f4f)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0xb65256e546889bd0))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x00000000111527d3)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x3c0468236ea142f6))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x00000000114369a1)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xee61766b889e18f2))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x00000000106f2f38)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xa206f41b12c30415))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x0000000011e2ca94)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0x02fe9d756c9f12d1))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x00000000110a29f0)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0xe9633210630cbf12))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x000000000fa9f5c1)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x1ffea9fe85a0b0b1))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x0000000010f625d1)))
                }
                mstore(st, d)
            }
            // Partial round 19: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[19], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[19] and VS[19] as literals (lazy sums).
            function partialRound19(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x308bb65a036acbce)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x81d1ae8cc50240f3))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x000000000011f718)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0xf4c77a079a4607d7))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x000000000010b6c8)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xed446b2315e3efc1))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x0000000000134a96)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x0b0a6b70915178c3))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x000000000010cf7f)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0xb11ff3e089f15d9a))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x0000000000124d03)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x1d4dba0b7ae9cc18))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x000000000013f8a1)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x65d74e2f43b48d05))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x0000000000117c58)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xa2df8c6b8ae0804a))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x0000000000132c94)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xa4e6f0a8c33348a6))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x0000000000134fc0)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0xc0a26efc7be5669b))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x000000000010a091)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0xa6b6582c547d0d60))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x0000000000128961)))
                }
                mstore(st, d)
            }
            // Partial round 20: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[20], then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[20] and VS[20] as literals (lazy sums).
            function partialRound20(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := add(mulmod(x3, mulmod(x2, x2, P), P), 0x1aca78f31c97c876)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x84afc741f1c13213))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x0000000000001300)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x2f8f43734fc906f3))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x0000000000001750)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0xde682d72da0a02d9))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x000000000000114e)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x0bb005236adb9ef2))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x000000000000131f)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x5bdf35c10a8b5624))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x000000000000167b)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x0739a8a343950010))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x0000000000001371)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0x52f515f44785cfbc))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x0000000000001230)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0xcbaf4e5d82856c60))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x000000000000182c)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xac9ea09074e3e150))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x0000000000001368)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x8f0fa011a2035fb0))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x0000000000000f31)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x1a37905d8450904a))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x00000000000015c9)))
                }
                mstore(st, d)
            }
            // Partial round 21: S-box on state[0], add FAST_PARTIAL_ROUND_CONSTANTS[21] (zero, omitted), then
            // `mds_partial_layer_fast` with M_00 = 25, W_HATS[21] and VS[21] as literals (lazy sums).
            function partialRound21(st) {
                let x := mload(st)
                let x2 := mulmod(x, x, P)
                let x3 := mulmod(x, x2, P)
                let s0 := mulmod(x3, mulmod(x2, x2, P), P)
                let d := mul(s0, 25)
                {
                    let s := mload(add(st, 0x20))
                    d := add(d, mul(s, 0x3abeb80def61cc85))
                    mstore(add(st, 0x20), add(s, mul(s0, 0x0000000000000014)))
                }
                {
                    let s := mload(add(st, 0x40))
                    d := add(d, mul(s, 0x9d19c9dd4eac4133))
                    mstore(add(st, 0x40), add(s, mul(s0, 0x0000000000000022)))
                }
                {
                    let s := mload(add(st, 0x60))
                    d := add(d, mul(s, 0x075a652d9641a985))
                    mstore(add(st, 0x60), add(s, mul(s0, 0x0000000000000012)))
                }
                {
                    let s := mload(add(st, 0x80))
                    d := add(d, mul(s, 0x9daf69ae1b67e667))
                    mstore(add(st, 0x80), add(s, mul(s0, 0x0000000000000027)))
                }
                {
                    let s := mload(add(st, 0xa0))
                    d := add(d, mul(s, 0x364f71da77920a18))
                    mstore(add(st, 0xa0), add(s, mul(s0, 0x000000000000000d)))
                }
                {
                    let s := mload(add(st, 0xc0))
                    d := add(d, mul(s, 0x50bd769f745c95b1))
                    mstore(add(st, 0xc0), add(s, mul(s0, 0x000000000000000d)))
                }
                {
                    let s := mload(add(st, 0xe0))
                    d := add(d, mul(s, 0xf223d1180dbbf3fc))
                    mstore(add(st, 0xe0), add(s, mul(s0, 0x000000000000001c)))
                }
                {
                    let s := mload(add(st, 0x100))
                    d := add(d, mul(s, 0x2f885e584e04aa99))
                    mstore(add(st, 0x100), add(s, mul(s0, 0x0000000000000002)))
                }
                {
                    let s := mload(add(st, 0x120))
                    d := add(d, mul(s, 0xb69a0fa70aea684a))
                    mstore(add(st, 0x120), add(s, mul(s0, 0x0000000000000010)))
                }
                {
                    let s := mload(add(st, 0x140))
                    d := add(d, mul(s, 0x09584acaa6e062a0))
                    mstore(add(st, 0x140), add(s, mul(s0, 0x0000000000000029)))
                }
                {
                    let s := mload(add(st, 0x160))
                    d := add(d, mul(s, 0x0bc051640145b19b))
                    mstore(add(st, 0x160), add(s, mul(s0, 0x000000000000000f)))
                }
                mstore(st, d)
            }
            // 4 full rounds, 22 partial rounds, 4 full rounds (ALL_ROUND_CONSTANTS rows 0..3, 26..29).
            fullRound0(state)
            fullRound1(state)
            fullRound2(state)
            fullRound3(state)
            partialInit(state)
            partialRound0(state)
            partialRound1(state)
            partialRound2(state)
            partialRound3(state)
            partialRound4(state)
            partialRound5(state)
            partialRound6(state)
            partialRound7(state)
            partialRound8(state)
            partialRound9(state)
            partialRound10(state)
            partialRound11(state)
            partialRound12(state)
            partialRound13(state)
            partialRound14(state)
            partialRound15(state)
            partialRound16(state)
            partialRound17(state)
            partialRound18(state)
            partialRound19(state)
            partialRound20(state)
            partialRound21(state)
            fullRound26(state)
            fullRound27(state)
            fullRound28(state)
            fullRound29(state)
            // Reduce once; every word is an exact circulant row below 2^73 here.
            mstore(state, mod(mload(state), P))
            mstore(add(state, 0x20), mod(mload(add(state, 0x20)), P))
            mstore(add(state, 0x40), mod(mload(add(state, 0x40)), P))
            mstore(add(state, 0x60), mod(mload(add(state, 0x60)), P))
            mstore(add(state, 0x80), mod(mload(add(state, 0x80)), P))
            mstore(add(state, 0xa0), mod(mload(add(state, 0xa0)), P))
            mstore(add(state, 0xc0), mod(mload(add(state, 0xc0)), P))
            mstore(add(state, 0xe0), mod(mload(add(state, 0xe0)), P))
            mstore(add(state, 0x100), mod(mload(add(state, 0x100)), P))
            mstore(add(state, 0x120), mod(mload(add(state, 0x120)), P))
            mstore(add(state, 0x140), mod(mload(add(state, 0x140)), P))
            mstore(add(state, 0x160), mod(mload(add(state, 0x160)), P))
            // Never executed: the public inputs are calldata, so `calldatasize()` is not zero
            // here. The block only gives every round function a second call site: with a
            // memory-safe block the via-IR inliner would otherwise inline each single-use round
            // into one straight-line body, the stack layout generator then spills its words to
            // memory, and the spilled words get re-expanded into exponentially growing
            // expressions (the compile does not terminate).
            if iszero(calldatasize()) {
                partialInit(state)
                partialRound0(state)
                partialRound1(state)
                partialRound2(state)
                partialRound3(state)
                partialRound4(state)
                partialRound5(state)
                partialRound6(state)
                partialRound7(state)
                partialRound8(state)
                partialRound9(state)
                partialRound10(state)
                partialRound11(state)
                partialRound12(state)
                partialRound13(state)
                partialRound14(state)
                partialRound15(state)
                partialRound16(state)
                partialRound17(state)
                partialRound18(state)
                partialRound19(state)
                partialRound20(state)
                partialRound21(state)
                fullRound0(state)
                fullRound1(state)
                fullRound2(state)
                fullRound3(state)
                fullRound26(state)
                fullRound27(state)
                fullRound28(state)
                fullRound29(state)
            }
        }
    }

    /// @dev 123 constraints total. Layout:
    ///   [0]           swap binary check
    ///   [1..5)        delta consistency (4)
    ///   [5..41)       first-set full-round S-box input consistency (36 = 12×3)
    ///   [41..63)      partial-round S-box input consistency (22)
    ///   [63..111)     second-set full-round S-box input consistency (48 = 12×4)
    ///   [111..123)    output consistency (12)
    function evalConstraints(uint256[] memory w, uint256 filter, uint256[] memory acc) internal pure {
        // Pull direct memory pointers to the packed big-endian blobs so inner
        // loops can `mload(ptr+offset)` without function-call or bounds-check
        // overhead. Each blob is `bytes memory`: 32-byte length prefix then
        // the payload we want.
        bytes memory allRC = PoseidonConstants.ALL_ROUND_CONSTANTS;
        bytes memory pfrc = PoseidonConstants.FAST_PARTIAL_FIRST_ROUND_CONSTANT;
        bytes memory prc = PoseidonConstants.FAST_PARTIAL_ROUND_CONSTANTS;
        bytes memory prvs = PoseidonConstants.FAST_PARTIAL_ROUND_VS;
        bytes memory prwh = PoseidonConstants.FAST_PARTIAL_ROUND_W_HATS;
        bytes memory pim = PoseidonConstants.FAST_PARTIAL_ROUND_INITIAL_MATRIX;

        // Allocate a contiguous 12-slot scratch for the Poseidon state.
        // Layout: state[i] at offset 0x20*i (i ∈ 0..12).
        uint256[] memory stateArr = new uint256[](12);
        uint256 statePtr;
        assembly {
            statePtr := add(stateArr, 0x20)
        }

        // Also need a second 12-slot buffer for MDS output accumulators.
        uint256[] memory scratchArr = new uint256[](12);
        uint256 scratchPtr;
        assembly {
            scratchPtr := add(scratchArr, 0x20)
        }

        // 0..5: swap + delta constraints, also build initial state.
        _evalSwapDelta(w, filter, acc, statePtr);

        // Phase structure delegated to helpers to keep stack usage bounded.
        uint256 nextIdx = _firstFullRounds(w, filter, acc, statePtr, scratchPtr, allRC);
        _partialFirstConstantLayer(statePtr, pfrc);
        _mdsPartialLayerInit(statePtr, scratchPtr, pim);
        nextIdx = _partialRounds(w, filter, acc, statePtr, scratchPtr, prc, prvs, prwh, nextIdx);
        nextIdx = _secondFullRounds(w, filter, acc, statePtr, scratchPtr, allRC, nextIdx);
        _outputConstraints(w, filter, acc, statePtr, nextIdx);
    }

    /// @dev First HALF_N_FULL_ROUNDS full rounds with S-box input constraints
    /// starting from round 1.
    function _firstFullRounds(
        uint256[] memory w,
        uint256 filter,
        uint256[] memory acc,
        uint256 statePtr,
        uint256 scratchPtr,
        bytes memory allRC
    ) private pure returns (uint256 nextIdx) {
        uint256 wPtr;
        uint256 accPtr;
        assembly {
            wPtr := add(w, 0x20)
            accPtr := add(acc, 0x20)
        }
        nextIdx = 5;
        uint256 roundCtr = 0;
        for (uint256 r = 0; r < HALF_N_FULL_ROUNDS; r++) {
            _addConstantLayer(statePtr, allRC, roundCtr);
            if (r != 0) {
                uint256 startSbox = START_FULL_0 + 12 * (r - 1);
                nextIdx = _pushConsumeSboxInputs(statePtr, wPtr, startSbox, filter, accPtr, nextIdx);
            }
            _sboxLayer(statePtr);
            _mdsLayerInline(statePtr, scratchPtr);
            roundCtr++;
        }
    }

    /// @dev N_PARTIAL_ROUNDS partial rounds with a constraint per round.
    function _partialRounds(
        uint256[] memory w,
        uint256 filter,
        uint256[] memory acc,
        uint256 statePtr,
        uint256 scratchPtr,
        bytes memory prc,
        bytes memory prvs,
        bytes memory prwh,
        uint256 nextIdx
    ) private pure returns (uint256) {
        uint256 accPtr;
        assembly {
            accPtr := add(acc, 0x20)
        }
        // MDS_CIRC[0] + MDS_DIAG[0] = 17 + 8.
        uint256 m00 = 25;
        for (uint256 r = 0; r < N_PARTIAL_ROUNDS - 1; r++) {
            uint256 sboxIn = w[START_PARTIAL + r];
            nextIdx = _pushPartialConstraint(statePtr, sboxIn, filter, accPtr, nextIdx);
            // state[0] = sbox_monomial(sboxIn) + FAST_PARTIAL_ROUND_CONSTANTS[r]
            assembly {
                let x := sboxIn
                let x2 := mulmod(x, x, P)
                let x4 := mulmod(x2, x2, P)
                let x7 := mulmod(mulmod(x, x2, P), x4, P)
                let rc := shr(192, mload(add(add(prc, 0x20), mul(r, 8))))
                mstore(statePtr, addmod(x7, rc, P))
            }
            _mdsPartialLayerFast(statePtr, scratchPtr, prvs, prwh, r, m00);
        }
        // Final partial round (no following round constant add).
        uint256 sboxInFinal = w[START_PARTIAL + N_PARTIAL_ROUNDS - 1];
        nextIdx = _pushPartialConstraint(statePtr, sboxInFinal, filter, accPtr, nextIdx);
        assembly {
            let x := sboxInFinal
            let x2 := mulmod(x, x, P)
            let x4 := mulmod(x2, x2, P)
            let x7 := mulmod(mulmod(x, x2, P), x4, P)
            mstore(statePtr, x7)
        }
        _mdsPartialLayerFast(statePtr, scratchPtr, prvs, prwh, N_PARTIAL_ROUNDS - 1, m00);
        return nextIdx;
    }

    /// @dev Second set of full rounds (with S-box input constraints at every round).
    function _secondFullRounds(
        uint256[] memory w,
        uint256 filter,
        uint256[] memory acc,
        uint256 statePtr,
        uint256 scratchPtr,
        bytes memory allRC,
        uint256 nextIdx
    ) private pure returns (uint256) {
        uint256 wPtr;
        uint256 accPtr;
        assembly {
            wPtr := add(w, 0x20)
            accPtr := add(acc, 0x20)
        }
        uint256 roundCtr = HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS;
        for (uint256 r = 0; r < HALF_N_FULL_ROUNDS; r++) {
            _addConstantLayer(statePtr, allRC, roundCtr);
            uint256 startSbox = START_FULL_1 + 12 * r;
            nextIdx = _pushConsumeSboxInputs(statePtr, wPtr, startSbox, filter, accPtr, nextIdx);
            _sboxLayer(statePtr);
            _mdsLayerInline(statePtr, scratchPtr);
            roundCtr++;
        }
        return nextIdx;
    }

    /// @dev Output consistency: state[i] - wire_output(i) for i ∈ 0..12.
    function _outputConstraints(
        uint256[] memory w,
        uint256 filter,
        uint256[] memory acc,
        uint256 statePtr,
        uint256 nextIdx
    ) private pure {
        assembly {
            let p := P
            let wPtr := add(w, 0x20)
            let accPtr := add(acc, 0x20)
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let stI := mload(add(statePtr, mul(i, 0x20)))
                let outI := mload(add(wPtr, mul(add(i, 12), 0x20)))
                // SECURITY (C2): self-reduce `outI` (prover-supplied wire)
                // before negation — see phase3_c2_threat_model.md §6.2.
                let diff := addmod(stI, sub(p, mod(outI, p)), p)
                let slot := add(accPtr, mul(add(nextIdx, i), 0x20))
                mstore(slot, addmod(mload(slot), mulmod(filter, diff, p), p))
            }
        }
    }

    /// @dev Constraints 0..5 (swap binary + 4 delta) and initial state load.
    function _evalSwapDelta(uint256[] memory w, uint256 filter, uint256[] memory acc, uint256 statePtr) private pure {
        uint256 swap = w[WIRE_SWAP];
        assembly {
            let p := P
            let accPtr := add(acc, 0x20)
            let wPtr := add(w, 0x20)
            // Constraint 0: swap * (swap - 1)
            let s1 := addmod(swap, sub(p, 1), p)
            let v0 := mulmod(swap, s1, p)
            mstore(accPtr, addmod(mload(accPtr), mulmod(filter, v0, p), p))
            // Constraints 1..5: swap*(rhs-lhs) - delta_i
            // Also write state[0..8] = [input[i] + delta_i, input[i+4] - delta_i].
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                let lhs := mload(add(wPtr, mul(i, 0x20)))
                let rhs := mload(add(wPtr, mul(add(i, 4), 0x20)))
                let deltaI := mload(add(wPtr, mul(add(i, START_DELTA), 0x20)))
                // SECURITY (C2): reduce each prover wire before it enters any
                // `sub(P, X)` context. Canonical representatives are forced,
                // and downstream addmod/mulmod remain correct.
                let lhsR := mod(lhs, p)
                let rhsR := mod(rhs, p)
                let deltaR := mod(deltaI, p)
                let rmL := addmod(rhsR, sub(p, lhsR), p)
                let tmp := mulmod(swap, rmL, p)
                let diff := addmod(tmp, sub(p, deltaR), p)
                let slot := add(accPtr, mul(add(i, 1), 0x20))
                mstore(slot, addmod(mload(slot), mulmod(filter, diff, p), p))
                mstore(add(statePtr, mul(i, 0x20)), addmod(lhsR, deltaR, p))
                mstore(add(statePtr, mul(add(i, 4), 0x20)), addmod(rhsR, sub(p, deltaR), p))
            }
            // state[8..12] = wire_input(8..12)
            for { let i := 8 } lt(i, 12) { i := add(i, 1) } {
                mstore(add(statePtr, mul(i, 0x20)), mload(add(wPtr, mul(i, 0x20))))
            }
        }
    }

    /// @dev Push 12 constraints `state[i] - sbox_in_i`, overwriting
    /// state[i] with sbox_in_i on the way out.
    function _pushConsumeSboxInputs(
        uint256 statePtr,
        uint256 wPtr,
        uint256 startSbox,
        uint256 filter,
        uint256 accPtr,
        uint256 nextIdx
    ) private pure returns (uint256) {
        assembly {
            let p := P
            let f := filter
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let stSlot := add(statePtr, mul(i, 0x20))
                let stV := mload(stSlot)
                let sboxIn := mload(add(wPtr, mul(add(startSbox, i), 0x20)))
                // SECURITY (C2): reduce the prover-supplied sbox-input before
                // using it in sub(P, X). Also write the canonical form into
                // state so future reads are stable (even though downstream
                // mulmod would self-reduce, this keeps state invariants clean).
                let sboxInR := mod(sboxIn, p)
                let diff := addmod(stV, sub(p, sboxInR), p)
                let contribute := mulmod(f, diff, p)
                let accSlot := add(accPtr, mul(add(nextIdx, i), 0x20))
                mstore(accSlot, addmod(mload(accSlot), contribute, p))
                // state[i] = sbox_in (canonical)
                mstore(stSlot, sboxInR)
            }
        }
        unchecked {
            return nextIdx + 12;
        }
    }

    /// @dev Single partial-round sbox-input constraint: state[0] - sbox_in.
    function _pushPartialConstraint(uint256 statePtr, uint256 sboxIn, uint256 filter, uint256 accPtr, uint256 nextIdx)
        private
        pure
        returns (uint256)
    {
        assembly {
            let p := P
            let st0 := mload(statePtr)
            // SECURITY (C2): reduce `sboxIn` before sub(P, X). `sboxIn` is a
            // single wire value (not looped), so one `mod` is enough.
            let diff := addmod(st0, sub(p, mod(sboxIn, p)), p)
            let contribute := mulmod(filter, diff, p)
            let slot := add(accPtr, mul(nextIdx, 0x20))
            mstore(slot, addmod(mload(slot), contribute, p))
        }
        unchecked {
            return nextIdx + 1;
        }
    }

    /// @dev state[i] += ALL_ROUND_CONSTANTS[12*round_ctr + i] for i ∈ 0..12.
    function _addConstantLayer(uint256 statePtr, bytes memory allRC, uint256 roundCtr) private pure {
        assembly {
            let base := add(add(allRC, 0x20), mul(roundCtr, 96)) // 12*8 bytes per round
            let p := P
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let rc := shr(192, mload(add(base, mul(i, 8))))
                let slot := add(statePtr, mul(i, 0x20))
                mstore(slot, addmod(mload(slot), rc, p))
            }
        }
    }

    /// @dev state[i] := state[i]^7 for i ∈ 0..12. In-place.
    function _sboxLayer(uint256 statePtr) private pure {
        assembly {
            let p := P
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let slot := add(statePtr, mul(i, 0x20))
                let x := mload(slot)
                let x2 := mulmod(x, x, p)
                let x4 := mulmod(x2, x2, p)
                let x7 := mulmod(mulmod(x, x2, p), x4, p)
                mstore(slot, x7)
            }
        }
    }

    /// @dev MDS layer using the exact 3x4 integer-FFT factorization from
    /// `plonky2::hash::poseidon_goldilocks::poseidon12_mds`.
    ///
    /// This is algebraically identical to
    /// `result[r] = Σ_i state[(i+r) % 12] * CIRC[i]`, for the fixed
    /// `CIRC = [17,15,41,16,2,28,13,13,39,18,34,20]`. The only diagonal
    /// coefficient is then added to result[0]. Every transform value is kept as
    /// a canonical Goldilocks representative. Weighted integer sums are below
    /// 2^70 and are reduced exactly once; subtraction uses an explicit bounded
    /// multiple of P, avoiding any signed-EVM interpretation.
    ///
    /// Keeping this factorization here (rather than a second hash-only MDS)
    /// means both the gate evaluator and public-input hasher exercise the same
    /// reviewed linear layer.
    function _mdsLayerInline(uint256 statePtr, uint256 scratchPtr) internal pure {
        assembly {
            let p := P

            // Three independent real 4-FFTs. Each group [a,b,c,d] maps to
            // [a+b+c+d, (a-c)+i(d-b), a-b+c-d]. Store the twelve scalar
            // components in scratch as
            // [u0,u1r,u1i,u2, u4,u5r,u5i,u6, u8,u9r,u9i,u10].
            for { let g := 0 } lt(g, 3) { g := add(g, 1) } {
                let a := mload(add(statePtr, mul(g, 0x20)))
                let b := mload(add(statePtr, mul(add(g, 3), 0x20)))
                let c := mload(add(statePtr, mul(add(g, 6), 0x20)))
                let d := mload(add(statePtr, mul(add(g, 9), 0x20)))
                let base := add(scratchPtr, mul(g, 0x80))
                mstore(base, addmod(addmod(a, b, p), addmod(c, d, p), p))
                mstore(add(base, 0x20), addmod(a, sub(p, c), p))
                mstore(add(base, 0x40), addmod(d, sub(p, b), p))
                mstore(add(base, 0x60), addmod(addmod(a, sub(p, b), p), addmod(c, sub(p, d), p), p))
            }

            // Frequency block one, with coefficients [16,32,16].
            {
                let x0 := mload(scratchPtr)
                let x1 := mload(add(scratchPtr, 0x80))
                let x2 := mload(add(scratchPtr, 0x100))
                mstore(scratchPtr, mod(add(add(shl(4, x0), shl(4, x1)), shl(5, x2)), p))
                mstore(add(scratchPtr, 0x80), mod(add(add(shl(5, x0), shl(4, x1)), shl(4, x2)), p))
                mstore(add(scratchPtr, 0x100), mod(add(add(shl(4, x0), shl(5, x1)), shl(4, x2)), p))
            }

            // Frequency block two. This is the source implementation's
            // complex Karatsuba block specialized for constants
            // [(2,-1),(-4,1),(16,1)], simplified symbolically.
            {
                let a := mload(add(scratchPtr, 0x20))
                let b := mload(add(scratchPtr, 0x40))
                let c := mload(add(scratchPtr, 0xa0))
                let d := mload(add(scratchPtr, 0xc0))
                let e := mload(add(scratchPtr, 0x120))
                let f := mload(add(scratchPtr, 0x140))

                mstore(
                    add(scratchPtr, 0x20),
                    mod(add(add(add(add(add(shl(1, a), b), c), shl(4, d)), e), sub(shl(2, p), shl(2, f))), p)
                )
                mstore(
                    add(scratchPtr, 0x40),
                    mod(sub(add(add(add(shl(1, b), d), shl(2, e)), add(f, mul(17, p))), add(a, shl(4, c))), p)
                )
                mstore(
                    add(scratchPtr, 0xa0),
                    mod(add(add(add(add(shl(1, c), d), e), shl(4, f)), sub(mul(5, p), add(shl(2, a), b))), p)
                )
                mstore(
                    add(scratchPtr, 0xc0),
                    mod(sub(add(add(add(a, shl(1, d)), f), mul(21, p)), add(add(shl(2, b), c), shl(4, e))), p)
                )
                mstore(
                    add(scratchPtr, 0x120),
                    mod(add(add(add(shl(4, a), shl(1, e)), f), sub(mul(6, p), add(add(b, shl(2, c)), d))), p)
                )
                mstore(
                    add(scratchPtr, 0x140),
                    mod(add(add(add(add(a, shl(4, b)), c), shl(1, f)), sub(mul(5, p), add(shl(2, d), e))), p)
                )
            }

            // Frequency block three, with coefficients [-1,-8,2].
            {
                let x0 := mload(add(scratchPtr, 0x60))
                let x1 := mload(add(scratchPtr, 0xe0))
                let x2 := mload(add(scratchPtr, 0x160))
                mstore(add(scratchPtr, 0x60), mod(add(shl(3, x2), sub(mul(3, p), add(x0, shl(1, x1)))), p))
                mstore(add(scratchPtr, 0xe0), mod(sub(mul(11, p), add(add(shl(3, x0), x1), shl(1, x2))), p))
                mstore(add(scratchPtr, 0x160), mod(add(shl(1, x0), sub(mul(9, p), add(shl(3, x1), x2))), p))
            }

            // Three real inverse 4-FFTs (without the cancelling /4 factor).
            // The output is the exact positive circulant product; reduce each
            // row once, matching Plonky2's Goldilocks result.
            for { let g := 0 } lt(g, 3) { g := add(g, 1) } {
                let base := add(scratchPtr, mul(g, 0x80))
                let v0 := mload(base)
                let v1r := mload(add(base, 0x20))
                let v1i := mload(add(base, 0x40))
                let v2 := mload(add(base, 0x60))
                let z0 := addmod(v0, v2, p)
                let z1 := addmod(v0, sub(p, v2), p)
                let out0 := addmod(z0, v1r, p)
                if iszero(g) {
                    out0 := addmod(out0, mulmod(mload(statePtr), 8, p), p)
                }
                mstore(add(statePtr, mul(g, 0x20)), out0)
                mstore(add(statePtr, mul(add(g, 3), 0x20)), addmod(z1, sub(p, v1i), p))
                mstore(add(statePtr, mul(add(g, 6), 0x20)), addmod(z0, sub(p, v1r), p))
                mstore(add(statePtr, mul(add(g, 9), 0x20)), addmod(z1, v1i, p))
            }
        }
    }

    /// @dev state[i] += FAST_PARTIAL_FIRST_ROUND_CONSTANT[i] for i ∈ 0..12.
    function _partialFirstConstantLayer(uint256 statePtr, bytes memory pfrc) private pure {
        assembly {
            let p := P
            let base := add(pfrc, 0x20)
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let c := shr(192, mload(add(base, mul(i, 8))))
                let slot := add(statePtr, mul(i, 0x20))
                mstore(slot, addmod(mload(slot), c, p))
            }
        }
    }

    /// @dev result[0] = state[0]; result[c] = Σ_r state[r] * M[r-1][c-1].
    function _mdsPartialLayerInit(uint256 statePtr, uint256 scratchPtr, bytes memory pim) private pure {
        assembly {
            let p := P
            // Zero scratch.
            mstore(scratchPtr, mload(statePtr)) // result[0] = state[0]
            for { let i := 1 } lt(i, 12) { i := add(i, 1) } {
                mstore(add(scratchPtr, mul(i, 0x20)), 0)
            }
            let matBase := add(pim, 0x20)
            // For r ∈ [1,12): for c ∈ [1,12): scratch[c] += state[r] * M[r-1][c-1]
            for { let r := 1 } lt(r, 12) { r := add(r, 1) } {
                let stR := mload(add(statePtr, mul(r, 0x20)))
                if stR {
                    let rowBase := add(matBase, mul(sub(r, 1), 88)) // 11 entries × 8 bytes
                    for { let c := 1 } lt(c, 12) { c := add(c, 1) } {
                        let t := shr(192, mload(add(rowBase, mul(sub(c, 1), 8))))
                        let sl := add(scratchPtr, mul(c, 0x20))
                        // 11 products of two canonical u64 values sum to < 2^132.
                        mstore(sl, add(mload(sl), mul(stR, t)))
                    }
                }
            }
            // Copy scratch back to state.
            mstore(statePtr, mload(scratchPtr))
            for { let i := 1 } lt(i, 12) { i := add(i, 1) } {
                mstore(add(statePtr, mul(i, 0x20)), mod(mload(add(scratchPtr, mul(i, 0x20))), p))
            }
        }
    }

    /// @dev Fast partial MDS layer for partial round `r`.
    ///   d = state[0] * M_00 + Σ_{i=1..12} state[i] * W_HATS[r][i-1]
    ///   result[0] = d
    ///   result[i] = state[0] * VS[r][i-1] + state[i]  for i ∈ [1,12)
    function _mdsPartialLayerFast(
        uint256 statePtr,
        uint256 scratchPtr,
        bytes memory prvs,
        bytes memory prwh,
        uint256 r,
        uint256 m00
    ) private pure {
        assembly {
            let p := P
            let s0 := mload(statePtr)
            let d := mul(s0, m00)
            let whBase := add(add(prwh, 0x20), mul(r, 88))
            for { let i := 1 } lt(i, 12) { i := add(i, 1) } {
                let t := shr(192, mload(add(whBase, mul(sub(i, 1), 8))))
                let stI := mload(add(statePtr, mul(i, 0x20)))
                // Twelve u64*u64 products sum to < 2^132.
                d := add(d, mul(stI, t))
            }
            mstore(scratchPtr, mod(d, p))
            let vsBase := add(add(prvs, 0x20), mul(r, 88))
            for { let i := 1 } lt(i, 12) { i := add(i, 1) } {
                let t := shr(192, mload(add(vsBase, mul(sub(i, 1), 8))))
                let stI := mload(add(statePtr, mul(i, 0x20)))
                mstore(add(scratchPtr, mul(i, 0x20)), mod(add(mul(s0, t), stI), p))
            }
            // Copy scratch back.
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                mstore(add(statePtr, mul(i, 0x20)), mload(add(scratchPtr, mul(i, 0x20))))
            }
        }
    }
}
