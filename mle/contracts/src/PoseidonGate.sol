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
/// big-endian `bytes` blobs. We take a direct memory pointer to each blob's
/// data region at function entry and read via `shr(192, mload(ptr+offset))`.
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

    /// @dev Packed constants shared by every sponge permutation in one `hashNoPad` call. A
    /// 103-element production statement needs 13 permutations, so these blobs are materialized
    /// once rather than once per rate chunk.
    struct HashContext {
        bytes allRoundConstants;
        bytes partialFirstConstants;
        bytes partialRoundConstants;
        bytes partialRoundVs;
        bytes partialRoundWHats;
        bytes partialInitialMatrix;
    }

    /// @dev Plonky2's Poseidon `hash_no_pad` over the Goldilocks field.
    /// The sponge rate is eight, the state width is twelve, and the first four
    /// rate elements are returned.  A final short chunk overwrites only its
    /// occupied rate slots, exactly matching `PlonkyPermutation::set_from_slice`.
    function hashNoPad(uint256[] calldata inputs) internal pure returns (uint256[4] memory digest) {
        uint256[] memory state = new uint256[](SPONGE_WIDTH);
        uint256[] memory scratch = new uint256[](SPONGE_WIDTH);
        uint256 statePtr;
        uint256 scratchPtr;
        assembly {
            statePtr := add(state, 0x20)
            scratchPtr := add(scratch, 0x20)
        }

        HashContext memory context = _hashContext();
        uint256 invalidProofSelector = uint32(InvalidMleProof.selector);

        for (uint256 offset = 0; offset < inputs.length; offset += 8) {
            uint256 remaining = inputs.length - offset;
            uint256 chunkLength = remaining < 8 ? remaining : 8;
            assembly ("memory-safe") {
                let source := add(inputs.offset, mul(offset, 0x20))
                for { let i := 0 } lt(i, chunkLength) { i := add(i, 1) } {
                    let value := calldataload(add(source, mul(i, 0x20)))
                    if iszero(lt(value, P)) {
                        mstore(0x00, shl(224, invalidProofSelector))
                        revert(0x00, 0x04)
                    }
                    mstore(add(statePtr, mul(i, 0x20)), value)
                }
            }
            _permuteHashState(statePtr, scratchPtr, context);
        }

        for (uint256 i = 0; i < 4; i++) {
            digest[i] = state[i];
        }
    }

    /// @dev Build the immutable permutation context once per public-input vector. The pointers
    /// refer to memory owned by this call frame and remain live for the complete hash operation.
    function _hashContext() private pure returns (HashContext memory context) {
        context.allRoundConstants = PoseidonConstants.ALL_ROUND_CONSTANTS;
        context.partialFirstConstants = PoseidonConstants.FAST_PARTIAL_FIRST_ROUND_CONSTANT;
        context.partialRoundConstants = PoseidonConstants.FAST_PARTIAL_ROUND_CONSTANTS;
        context.partialRoundVs = PoseidonConstants.FAST_PARTIAL_ROUND_VS;
        context.partialRoundWHats = PoseidonConstants.FAST_PARTIAL_ROUND_W_HATS;
        context.partialInitialMatrix = PoseidonConstants.FAST_PARTIAL_ROUND_INITIAL_MATRIX;
    }

    /// @dev Exact Plonky2 Poseidon permutation using its equivalent fast-partial
    /// decomposition. This preserves the byte-for-byte hash while replacing each of the 22
    /// partial rounds' dense 12x12 MDS products with the audited sparse factorization used by
    /// Plonky2 itself and by `evalConstraints` below.
    function _permuteHashState(uint256 statePtr, uint256 scratchPtr, HashContext memory context) private pure {
        for (uint256 round = 0; round < HALF_N_FULL_ROUNDS; ++round) {
            _addConstantLayer(statePtr, context.allRoundConstants, round);
            _sboxLayer(statePtr);
            _mdsLayerInline(statePtr, scratchPtr);
        }

        _partialFirstConstantLayer(statePtr, context.partialFirstConstants);
        _mdsPartialLayerInit(statePtr, scratchPtr, context.partialInitialMatrix);
        _partialRoundsHash(statePtr, context);

        for (
            uint256 round = HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS;
            round < 2 * HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS;
            ++round
        ) {
            _addConstantLayer(statePtr, context.allRoundConstants, round);
            _sboxLayer(statePtr);
            _mdsLayerInline(statePtr, scratchPtr);
        }
    }

    /// @dev Hash-only fast partial rounds. The gate evaluator needs to stop at
    /// every round to compare an explicit S-box wire, while hashing does not.
    /// Keeping all 22 rounds in one assembly loop avoids 22 internal-call
    /// boundaries per permutation. The sparse matrix update is in-place: its
    /// row-zero dot product is computed before any of state[1..11] changes.
    function _partialRoundsHash(uint256 statePtr, HashContext memory context) private pure {
        assembly ("memory-safe") {
            let p := P
            let rcPtr := add(mload(add(context, 0x40)), 0x20)
            let vsPtr := add(mload(add(context, 0x60)), 0x20)
            let whPtr := add(mload(add(context, 0x80)), 0x20)
            let m00 := 25

            for { let round := 0 } lt(round, N_PARTIAL_ROUNDS) { round := add(round, 1) } {
                let x := mload(statePtr)
                let x2 := mulmod(x, x, p)
                let x4 := mulmod(x2, x2, p)
                let s0 := addmod(mulmod(mulmod(x, x2, p), x4, p), shr(192, mload(rcPtr)), p)

                // d = s0*M00 + sum(state[i]*W_HAT[i]). Each operand is a
                // canonical u64 and the twelve-product sum is < 2^132.
                let d := mul(s0, m00)
                for { let i := 1 } lt(i, 12) { i := add(i, 1) } {
                    d := add(d, mul(mload(add(statePtr, mul(i, 0x20))), shr(192, mload(add(whPtr, mul(sub(i, 1), 8))))))
                }

                // Rows 1..11 are independent sparse updates from the same
                // old state and s0, so they can overwrite their source slots.
                for { let i := 1 } lt(i, 12) { i := add(i, 1) } {
                    let slot := add(statePtr, mul(i, 0x20))
                    let coefficient := shr(192, mload(add(vsPtr, mul(sub(i, 1), 8))))
                    mstore(slot, mod(add(mul(s0, coefficient), mload(slot)), p))
                }
                mstore(statePtr, mod(d, p))

                rcPtr := add(rcPtr, 8)
                vsPtr := add(vsPtr, 88)
                whPtr := add(whPtr, 88)
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
