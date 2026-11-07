// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof} from "./MleProofErrors.sol";
import {TranscriptV2} from "./TranscriptV2.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {
    BASE_FIELD_MODULUS_V2,
    LOG_ROUND_DEGREE_V2,
    MAX_CONSTITUENT_WIDTH_V2,
    MAX_GATE_ROUND_DEGREE_V2,
    MAX_ROUTED_WIRES_V2,
    MAX_ROW_VARIABLES_V2
} from "./generated/MleWhirV2.sol";

/// @title OuterLogupExt3Verifier
/// @notice Coupled Ext3 sumchecks and formal norm/logUp terminal for MLE wire v3.
/// @dev The public functions deliberately form an external-library boundary: a future
///      production verifier can link this bulk implementation without consuming its own
///      EIP-170 bytecode budget. The terminal uses formal coordinate polynomials at the
///      off-cube Ext3 point. It never takes an actual Ext3 inverse there.
///
///      Internally every Ext3 vector is a flat `uint256[]` of canonical limbs, three words
///      per element in `(c0, c1, c2)` order (`verifyPrevalidatedFlat` consumes that layout
///      directly; the `Ext3[]`-based entries flatten their inputs once). All field algebra
///      lives in `("memory-safe")` Yul: an element is three words, products are small Yul
///      helpers over stack triples or scratch records (every load precedes every store, so
///      an output may alias an input), and long-lived accumulators sit in fixed scratch so
///      nothing is allocated per round or per wire. Field products use lazy reduction: all
///      operands are canonical limbs (< 2^64), so integer sums of limb products stay below
///      2^133 and every output limb is reduced exactly once with `mod` (subtractions first add
///      2^68 * p, which exceeds every unreduced minuend, so nothing wraps). Every limb written
///      back is therefore canonical and bit-identical to the reference Ext3 library sequence
///      it replaces.
library OuterLogupExt3Verifier {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;
    uint256 internal constant MAX_DEGREE = LOG_ROUND_DEGREE_V2;
    uint256 internal constant MAX_ROW_VARIABLES = MAX_ROW_VARIABLES_V2;
    uint256 internal constant MAX_GATE_DEGREE = MAX_GATE_ROUND_DEGREE_V2;
    uint256 internal constant MAX_ROUTED_WIRES = MAX_ROUTED_WIRES_V2;
    uint256 internal constant MAX_CONSTITUENT_WIDTH = MAX_CONSTITUENT_WIDTH_V2;

    // Yul literals (assembly cannot read these constants): the Goldilocks prime
    // 0xFFFFFFFF00000001, `2p` = 0x1FFFFFFFE00000002, `p - 1` = 0xFFFFFFFF00000000,
    // `2^-1 mod p` = 0x7FFFFFFF80000001 and the `InvalidMleProof()` selector 0xf0783a66.

    struct CoefficientRound {
        /// @dev Monomial coefficients `[a1, a2, a3, a4, a5]` in this exact order.
        GoldilocksExt3.Ext3[] nonConstant;
    }

    struct SumcheckProof {
        CoefficientRound[] rounds;
    }

    /// @dev All fields are verifier-derived Fiat--Shamir values, never proof echoes.
    struct Challenges {
        GoldilocksExt3.Ext3 beta;
        GoldilocksExt3.Ext3 gamma;
        GoldilocksExt3.Ext3 lambda;
        GoldilocksExt3.Ext3 rho;
        GoldilocksExt3.Ext3 kappa;
        GoldilocksExt3.Ext3 eta;
        GoldilocksExt3.Ext3 xi;
        GoldilocksExt3.Ext3[] tau;
    }

    struct VerificationKey {
        uint256 numVars;
        /// @dev Must be the canonical circuit's `quotient_degree_factor + 2`.
        uint256 gateDegree;
        uint256 numConstants;
        uint256 numRoutedWires;
        uint256 numWires;
        uint256[] kIs;
        uint256[] subgroupGenPowers;
        /// @dev Ordered `row_u16_le || routed_column_u8`, exactly 3 bytes/PI.
        bytes publicInputWireMap;
    }

    /// @dev Ordered PCS-bound constituent evaluations at the Ext3 logUp point.
    struct TerminalEvaluations {
        /// `[constants..., sigma_0, ..., sigma_(numRoutedWires-1)]`.
        GoldilocksExt3.Ext3[] preprocessed;
        /// All witness-wire constituents, not only the routed prefix.
        GoldilocksExt3.Ext3[] witness;
        /// `[T_id,0.., T_id,m-1, T_sigma,0.., T_sigma,m-1]`.
        GoldilocksExt3.Ext3[] normInverse;
        /// Raw statement PIs, in the exact order used by `publicInputWireMap`.
        uint256[] publicInputs;
    }

    // ---------------------------------------------------------------- external entries

    /// @notice Verify both lockstep Ext3 sumchecks and a norm/logUp terminal evaluation.
    /// @dev This verifies only the outer algebra. Before accepting a proof, the caller MUST
    ///      authenticate every member of `terminal` with grouped WHIR openings at the returned
    ///      points and check the Ext3 gate terminal equation. Supplying this function with
    ///      unauthenticated evaluations is not a complete proof verification.
    /// @param transcript Transcript snapshot after all earlier wire-v3 messages and challenges.
    /// @return logPoint Ext3 row point produced by the norm/logUp sumcheck.
    /// @return gatePoint Ext3 gate point produced in the same coupled rounds.
    /// @return gateFinalClaim Gate claim to be checked by a linked Ext3 gate evaluator.
    /// @return nextTranscript Transcript after all coupled sumcheck rounds.
    function verify(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        _validateAll(logProof, gateProof, vk, challenges, terminal);
        (logPoint, gatePoint, gateFinalClaim) = _verifyFlatUnchecked(
            _flattenRounds(logProof, vk.numVars, MAX_DEGREE),
            _flattenRounds(gateProof, vk.numVars, vk.gateDegree),
            _flattenExt3(terminal.preprocessed),
            _flattenExt3(terminal.witness),
            _flattenExt3(terminal.normInverse),
            terminal.publicInputs,
            vk,
            challenges,
            transcript
        );
        nextTranscript = transcript;
    }

    /// @notice Verify the coupled sumchecks and terminal after a complete
    /// caller-side proof/VK preflight.
    /// @dev This entry is intentionally limited to the atomic verifier, which
    /// checks every proof coefficient and terminal limb in calldata before
    /// deriving canonical transcript challenges, and pins the VK by digest.
    /// It is not a standalone proof verifier and its return value must never be
    /// trusted without that preflight and the subsequent PCS/gate checks.
    /// The vector shapes the caller guarantees are re-checked against `vk` while
    /// the inputs are flattened; any mismatch reverts with `InvalidMleProof`.
    function verifyPrevalidated(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        uint256[] memory logRounds = _flattenRounds(logProof, vk.numVars, MAX_DEGREE);
        uint256[] memory gateRounds = _flattenRounds(gateProof, vk.numVars, vk.gateDegree);
        (logPoint, gatePoint, gateFinalClaim) = _verifyFlatUnchecked(
            logRounds,
            gateRounds,
            _flattenExt3(terminal.preprocessed),
            _flattenExt3(terminal.witness),
            _flattenExt3(terminal.normInverse),
            terminal.publicInputs,
            vk,
            challenges,
            transcript
        );
        nextTranscript = transcript;
    }

    /// @notice Same semantics as `verifyPrevalidated`, but every Ext3 vector is supplied as a flat
    /// `uint256[]` of canonical limbs, three words per element in (c0, c1, c2) order, no pointer tables.
    /// The caller guarantees exact lengths and canonical limbs, exactly as for `verifyPrevalidated`.
    /// @param logRounds numVars * 5 * 3 words: round-major, then coefficients a1..a5, then limbs.
    /// @param gateRounds numVars * gateDegree * 3 words, same ordering.
    /// @param preprocessed (numConstants + numRoutedWires) * 3 words: constants..., sigma_0..sigma_{m-1}.
    /// @param witness numWires * 3 words.
    /// @param normInverse 2 * numRoutedWires * 3 words.
    /// @param publicInputs numPublicInputs canonical base-field words.
    function verifyPrevalidatedFlat(
        uint256[] memory logRounds,
        uint256[] memory gateRounds,
        uint256[] memory preprocessed,
        uint256[] memory witness,
        uint256[] memory normInverse,
        uint256[] memory publicInputs,
        VerificationKey memory vk,
        Challenges memory challenges,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        (logPoint, gatePoint, gateFinalClaim) = _verifyFlatUnchecked(
            logRounds, gateRounds, preprocessed, witness, normInverse, publicInputs, vk, challenges, transcript
        );
        nextTranscript = transcript;
    }

    /// @notice `verifyPrevalidatedFlat` with the six flat vectors packed in one byte string:
    /// `blob` is the concatenation, in this order, of six length-prefixed word arrays
    /// `[len_words][word_0 .. word_{len-1}]` (each exactly the memory image of a `uint256[]`):
    /// publicInputs, logRounds, gateRounds, preprocessed, witness, normInverse.
    /// @dev The blob is copied to memory once and the six `uint256[]` views point into that copy
    /// (no further copies). Any array running past the blob, or trailing bytes after the sixth,
    /// revert with `InvalidMleProof`; every length is then re-checked against `vk` exactly as in
    /// `verifyPrevalidatedFlat`.
    function verifyPrevalidatedBlob(
        bytes calldata blob,
        VerificationKey memory vk,
        Challenges memory challenges,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        bytes memory copy = blob;
        uint256 cursor;
        uint256[] memory publicInputs;
        uint256[] memory logRounds;
        uint256[] memory gateRounds;
        uint256[] memory preprocessed;
        uint256[] memory witness;
        uint256[] memory normInverse;
        (publicInputs, cursor) = _blobArray(copy, cursor);
        (logRounds, cursor) = _blobArray(copy, cursor);
        (gateRounds, cursor) = _blobArray(copy, cursor);
        (preprocessed, cursor) = _blobArray(copy, cursor);
        (witness, cursor) = _blobArray(copy, cursor);
        (normInverse, cursor) = _blobArray(copy, cursor);
        if (cursor != copy.length) revert InvalidMleProof();
        (logPoint, gatePoint, gateFinalClaim) = _verifyFlatUnchecked(
            logRounds, gateRounds, preprocessed, witness, normInverse, publicInputs, vk, challenges, transcript
        );
        nextTranscript = transcript;
    }

    /// @dev `uint256[]` view (no copy) of the length-prefixed word array starting at byte `offset`
    /// of `copy`, and the offset just past it. Reverts with `InvalidMleProof` when the length word
    /// or the words it announces run past the end of `copy`.
    function _blobArray(bytes memory copy, uint256 offset)
        private
        pure
        returns (uint256[] memory view_, uint256 next)
    {
        uint256 end = copy.length;
        if (offset + 0x20 > end) revert InvalidMleProof();
        assembly ("memory-safe") {
            view_ := add(add(copy, 0x20), offset)
        }
        uint256 length = view_.length;
        if (length > (end - offset - 0x20) >> 5) revert InvalidMleProof();
        next = offset + 0x20 + (length << 5);
    }

    /// @notice Verify all coefficient rounds without evaluating either terminal family.
    /// @dev There is intentionally no log-only or gate-only transcript API: every round
    ///      commits both Ext3 messages before either challenge is available.
    function verifyCoupledSumchecks(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        uint256 gateDegree,
        uint256 numVars,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3 memory logFinalClaim,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        _validateProofs(logProof, gateProof, numVars, gateDegree);
        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) = _coupledSumchecksFlat(
            _flattenRounds(logProof, numVars, MAX_DEGREE),
            _flattenRounds(gateProof, numVars, gateDegree),
            numVars,
            gateDegree,
            transcript
        );
        nextTranscript = transcript;
    }

    /// @notice Check one already-verified sumcheck claim against authenticated terminal values.
    /// @dev The caller is responsible for authenticating `terminal` with the PCS first.
    function verifyTerminal(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3 memory finalClaim
    ) external pure {
        _validateTerminalInputs(vk, challenges, terminal, point);
        _checkCanonical(finalClaim);
        GoldilocksExt3.Ext3 memory terminalValue = _terminalFlat(
            vk,
            challenges,
            _flattenExt3(terminal.preprocessed),
            _flattenExt3(terminal.witness),
            _flattenExt3(terminal.normInverse),
            terminal.publicInputs,
            point
        );
        if (!GoldilocksExt3.eq(finalClaim, terminalValue)) revert InvalidMleProof();
    }

    /// @notice Evaluate the formal terminal polynomial without performing an inverse.
    function evaluateTerminal(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) external pure returns (GoldilocksExt3.Ext3 memory value) {
        _validateTerminalInputs(vk, challenges, terminal, point);
        value = _terminalFlat(
            vk,
            challenges,
            _flattenExt3(terminal.preprocessed),
            _flattenExt3(terminal.witness),
            _flattenExt3(terminal.normInverse),
            terminal.publicInputs,
            point
        );
    }

    /// @notice Check the Ext3 gate sumcheck terminal after its constituent
    /// values have been authenticated by grouped WHIR.
    function verifyGateTerminal(
        GoldilocksExt3.Ext3[] memory tau,
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3 memory gateEvaluation,
        GoldilocksExt3.Ext3 memory finalClaim
    ) external pure {
        if (tau.length == 0 || tau.length != point.length || tau.length > MAX_ROW_VARIABLES) {
            revert InvalidMleProof();
        }
        for (uint256 i = 0; i < tau.length; ++i) {
            _checkCanonical(tau[i]);
            _checkCanonical(point[i]);
        }
        _checkCanonical(gateEvaluation);
        _checkCanonical(finalClaim);
        GoldilocksExt3.Ext3 memory expected = _eqEvaluation(tau, point);
        _mulInPlace(expected, gateEvaluation);
        if (!GoldilocksExt3.eq(expected, finalClaim)) revert InvalidMleProof();
    }

    /// @notice Evaluate formal adjugate coordinates over Ext3-valued coordinate polynomials.
    function formalAdjugate(GoldilocksExt3.Ext3[3] memory coordinates)
        external
        pure
        returns (GoldilocksExt3.Ext3[3] memory adjugate)
    {
        for (uint256 i = 0; i < 3; ++i) {
            _checkCanonical(coordinates[i]);
        }
        GoldilocksExt3.Ext3 memory norm;
        _formalTerms(coordinates, adjugate, norm);
    }

    /// @notice Evaluate the formal cubic norm over Ext3-valued coordinate polynomials.
    function formalNorm(GoldilocksExt3.Ext3[3] memory coordinates)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory norm)
    {
        for (uint256 i = 0; i < 3; ++i) {
            _checkCanonical(coordinates[i]);
        }
        GoldilocksExt3.Ext3[3] memory adjugate;
        _formalTerms(coordinates, adjugate, norm);
    }

    // ---------------------------------------------------------------- flat core

    /// @dev Shared body of `verify`, `verifyPrevalidated` and `verifyPrevalidatedFlat` over the
    /// flat limb layout. The structural shape of every vector is re-checked against `vk` so no
    /// Yul read can leave its buffer; canonical limbs are the caller's responsibility (or were
    /// established by `_validateAll`).
    function _verifyFlatUnchecked(
        uint256[] memory logRounds,
        uint256[] memory gateRounds,
        uint256[] memory preprocessed,
        uint256[] memory witness,
        uint256[] memory normInverse,
        uint256[] memory publicInputs,
        VerificationKey memory vk,
        Challenges memory challenges,
        TranscriptV2.Transcript memory transcript
    )
        private
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim
        )
    {
        _requireFlatShapes(logRounds, gateRounds, preprocessed, witness, normInverse, publicInputs, vk, challenges);
        GoldilocksExt3.Ext3 memory logFinalClaim;
        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _coupledSumchecksFlat(logRounds, gateRounds, vk.numVars, vk.gateDegree, transcript);
        GoldilocksExt3.Ext3 memory terminalValue =
            _terminalFlat(vk, challenges, preprocessed, witness, normInverse, publicInputs, logPoint);
        if (!GoldilocksExt3.eq(logFinalClaim, terminalValue)) revert InvalidMleProof();
    }

    function _requireFlatShapes(
        uint256[] memory logRounds,
        uint256[] memory gateRounds,
        uint256[] memory preprocessed,
        uint256[] memory witness,
        uint256[] memory normInverse,
        uint256[] memory publicInputs,
        VerificationKey memory vk,
        Challenges memory challenges
    ) private pure {
        uint256 numVars = vk.numVars;
        uint256 numRoutedWires = vk.numRoutedWires;
        if (
            numVars > MAX_ROW_VARIABLES || vk.gateDegree > MAX_GATE_DEGREE
                || logRounds.length != numVars * MAX_DEGREE * 3 || gateRounds.length != numVars * vk.gateDegree * 3
                || preprocessed.length != 3 * (vk.numConstants + numRoutedWires) || witness.length != 3 * vk.numWires
                || normInverse.length != 6 * numRoutedWires || vk.kIs.length != numRoutedWires
                || vk.subgroupGenPowers.length != numVars || challenges.tau.length != numVars
                || publicInputs.length > type(uint256).max / 3
                || vk.publicInputWireMap.length != 3 * publicInputs.length
        ) revert InvalidMleProof();
    }

    /// @dev Both coupled sumchecks over flat coefficient buffers. The transcript still receives
    /// ordinary `Ext3[]` arguments: two pointer tables, reused every round, whose entries point
    /// straight into the flat buffers. The zero-initialised return records are the running claims.
    function _coupledSumchecksFlat(
        uint256[] memory logRounds,
        uint256[] memory gateRounds,
        uint256 numVars,
        uint256 gateDegree,
        TranscriptV2.Transcript memory transcript
    )
        private
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3 memory logFinalClaim,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim
        )
    {
        logPoint = new GoldilocksExt3.Ext3[](numVars);
        gatePoint = new GoldilocksExt3.Ext3[](numVars);
        GoldilocksExt3.Ext3[] memory logCoefficients = new GoldilocksExt3.Ext3[](MAX_DEGREE);
        GoldilocksExt3.Ext3[] memory gateCoefficients = new GoldilocksExt3.Ext3[](gateDegree);
        // Loop-invariant context read from memory inside the Yul: 0x00 log data, 0x20 gate data,
        // 0x40 gate round stride, 0x60 log table, 0x80 gate table, 0xa0 log point table,
        // 0xc0 gate point table, 0xe0 log claim, 0x100 gate claim.
        uint256[9] memory ctx;
        assembly ("memory-safe") {
            mstore(ctx, add(logRounds, 0x20))
            mstore(add(ctx, 0x20), add(gateRounds, 0x20))
            mstore(add(ctx, 0x40), mul(gateDegree, 0x60))
            mstore(add(ctx, 0x60), add(logCoefficients, 0x20))
            mstore(add(ctx, 0x80), add(gateCoefficients, 0x20))
            mstore(add(ctx, 0xa0), add(logPoint, 0x20))
            mstore(add(ctx, 0xc0), add(gatePoint, 0x20))
            mstore(add(ctx, 0xe0), logFinalClaim)
            mstore(add(ctx, 0x100), gateFinalClaim)
        }

        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            assembly ("memory-safe") {
                let base := add(mload(ctx), mul(roundIndex, 0x1e0))
                let table := mload(add(ctx, 0x60))
                for { let j := 0 } lt(j, 5) { j := add(j, 1) } {
                    mstore(add(table, shl(5, j)), add(base, mul(j, 0x60)))
                }
                let stride := mload(add(ctx, 0x40))
                base := add(mload(add(ctx, 0x20)), mul(roundIndex, stride))
                table := mload(add(ctx, 0x80))
                for { let offset := 0 } lt(offset, stride) { offset := add(offset, 0x60) } {
                    mstore(table, add(base, offset))
                    table := add(table, 0x20)
                }
            }
            TranscriptV2.CoupledOuterRoundChallenges memory roundChallenges =
                TranscriptV2.commitCoupledOuterRound(transcript, roundIndex, logCoefficients, gateCoefficients);
            // Round polynomial evaluation: a0 = (claim - sum a_j) / 2, then Horner at the challenge.
            assembly ("memory-safe") {
                // record x times stack triple b (canonical limbs; one `mod` per output limb)
                function mulRecord(x, b0, b1, b2) -> c0, c1, c2 {
                    let p := 0xFFFFFFFF00000001
                    c0 := mod(add(mul(mload(x), b0), shl(1, add(mul(mload(add(x, 0x20)), b2), mul(mload(add(x, 0x40)), b1)))), p)
                    c1 := mod(add(add(mul(mload(x), b1), mul(mload(add(x, 0x20)), b0)), shl(1, mul(mload(add(x, 0x40)), b2))), p)
                    c2 := mod(add(add(mul(mload(x), b2), mul(mload(add(x, 0x20)), b1)), mul(mload(add(x, 0x40)), b0)), p)
                }
                // claim <- a0 + x * (a1 + x * (... + x * a_degree)) with a0 = (claim - sum a_j) * 2^-1.
                // One pass: Horner from a_degree down to a_1 while summing the coefficients; the sum of at
                // most ten canonical limbs (< 2^68) is reduced once at the end.
                function evaluateRound(claim, base, end, x) {
                    let p := 0xFFFFFFFF00000001
                    let s0 := 0
                    let s1 := 0
                    let s2 := 0
                    let e0 := 0
                    let e1 := 0
                    let e2 := 0
                    if gt(end, base) {
                        let c := sub(end, 0x60)
                        e0 := mload(c)
                        e1 := mload(add(c, 0x20))
                        e2 := mload(add(c, 0x40))
                        s0 := e0
                        s1 := e1
                        s2 := e2
                        for {} gt(c, base) {} {
                            c := sub(c, 0x60)
                            e0, e1, e2 := mulRecord(x, e0, e1, e2)
                            e0 := mod(add(e0, mload(c)), p)
                            e1 := mod(add(e1, mload(add(c, 0x20))), p)
                            e2 := mod(add(e2, mload(add(c, 0x40))), p)
                            s0 := add(s0, mload(c))
                            s1 := add(s1, mload(add(c, 0x20)))
                            s2 := add(s2, mload(add(c, 0x40)))
                        }
                        e0, e1, e2 := mulRecord(x, e0, e1, e2)
                    }
                    mstore(claim, mod(add(e0, mulmod(add(mload(claim), sub(p, mod(s0, p))), 0x7FFFFFFF80000001, p)), p))
                    mstore(
                        add(claim, 0x20),
                        mod(add(e1, mulmod(add(mload(add(claim, 0x20)), sub(p, mod(s1, p))), 0x7FFFFFFF80000001, p)), p)
                    )
                    mstore(
                        add(claim, 0x40),
                        mod(add(e2, mulmod(add(mload(add(claim, 0x40)), sub(p, mod(s2, p))), 0x7FFFFFFF80000001, p)), p)
                    )
                }

                let challenge := mload(roundChallenges)
                let record := mload(add(mload(add(ctx, 0xa0)), shl(5, roundIndex)))
                mstore(record, mload(challenge))
                mstore(add(record, 0x20), mload(add(challenge, 0x20)))
                mstore(add(record, 0x40), mload(add(challenge, 0x40)))
                record := add(mload(ctx), mul(roundIndex, 0x1e0))
                evaluateRound(mload(add(ctx, 0xe0)), record, add(record, 0x1e0), challenge)

                challenge := mload(add(roundChallenges, 0x20))
                record := mload(add(mload(add(ctx, 0xc0)), shl(5, roundIndex)))
                mstore(record, mload(challenge))
                mstore(add(record, 0x20), mload(add(challenge, 0x20)))
                mstore(add(record, 0x40), mload(add(challenge, 0x40)))
                record := add(mload(add(ctx, 0x20)), mul(roundIndex, mload(add(ctx, 0x40))))
                evaluateRound(mload(add(ctx, 0x100)), record, add(record, mload(add(ctx, 0x40))), challenge)
            }
        }
    }

    /// @dev Full terminal: norm/logUp permutation value plus `xi` times the direct-PI binding.
    function _terminalFlat(
        VerificationKey memory vk,
        Challenges memory challenges,
        uint256[] memory preprocessed,
        uint256[] memory witness,
        uint256[] memory normInverse,
        uint256[] memory publicInputs,
        GoldilocksExt3.Ext3[] memory point
    ) private pure returns (GoldilocksExt3.Ext3 memory value) {
        value = _permutationTerminalFlat(vk, challenges, preprocessed, witness, normInverse, point);
        GoldilocksExt3.Ext3 memory binding =
            _publicInputBindingFlat(vk.publicInputWireMap, witness, publicInputs, point, challenges.eta);
        _mulAddInPlace(value, challenges.xi, binding);
    }

    /// @dev Degree-five norm/logUp terminal over the routed wires:
    ///   eq(tau, point) * sum_i lambda^i (Z_id,i + rho * Z_sigma,i) + kappa * sum_i (T_id,i * R_id,i - T_sigma,i * R_sigma,i)
    /// with Z = T * N - 1, N the formal norm and R the recomposed formal adjugate of the
    /// denominator coordinates. The lambda-weighted sum is accumulated by Horner from the last
    /// routed wire down, which is the same field element as the power-by-power sum.
    function _permutationTerminalFlat(
        VerificationKey memory vk,
        Challenges memory challenges,
        uint256[] memory preprocessed,
        uint256[] memory witness,
        uint256[] memory normInverse,
        GoldilocksExt3.Ext3[] memory point
    ) private pure returns (GoldilocksExt3.Ext3 memory permutationValue) {
        GoldilocksExt3.Ext3 memory eqValue = _eqEvaluation(challenges.tau, point);
        GoldilocksExt3.Ext3 memory subgroup = _subgroupEvaluation(vk.subgroupGenPowers, point);
        // Scratch block (byte offsets): 0x000 subgroup, 0x060 beta, 0x0c0 gamma, 0x120 rho,
        // 0x180 lambda, 0x1e0 helper-zero accumulator, 0x240 logUp sum, 0x2a0 identity position,
        // 0x300 Z_id, 0x360/0x3c0/0x420 coordinates a/b/c, 0x480/0x4e0/0x540 adjugate s0/s1/s2,
        // 0x5a0 norm, 0x600 recomposed adjugate, 0x660 temporary, 0x6c0 unused, 0x720 witness data,
        // 0x740 sigma data, 0x760 T_id data, 0x780 T_sigma data, 0x7a0 k_i data.
        uint256[62] memory w;
        assembly ("memory-safe") {
            // Lazy reduction: operands are canonical (< 2^64) limbs, so every product is < 2^128 and the
            // integer sums below stay far below 2^256; each limb is reduced once with `mod`. Subtractions
            // add 2^68 * p = 0xffffffff0000000100000000000000000 (> 2^132 - 2^100, larger than any
            // unreduced minuend here, all < 10 * 2^128 + 2^64) before subtracting, so they never wrap.
            // out <- x * y (records; every load precedes the stores, so out may alias x or y)
            function mulInto(out, x, y) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                let y0 := mload(y)
                let y1 := mload(add(y, 0x20))
                let y2 := mload(add(y, 0x40))
                mstore(out, mod(add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1)))), p))
                mstore(add(out, 0x20), mod(add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2))), p))
                mstore(add(out, 0x40), mod(add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0)), p))
            }
            // out <- out + x * y (sum < 2^64 + 5 * 2^128)
            function mulAddInto(out, x, y) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                let y0 := mload(y)
                let y1 := mload(add(y, 0x20))
                let y2 := mload(add(y, 0x40))
                mstore(out, mod(add(mload(out), add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1))))), p))
                mstore(
                    add(out, 0x20),
                    mod(add(mload(add(out, 0x20)), add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2)))), p)
                )
                mstore(add(out, 0x40), mod(add(mload(add(out, 0x40)), add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0))), p))
            }
            // out <- out - x * y, as (out + 2^68 p - x * y) mod p with 2^68 p > 5 * 2^128 > x * y limbs
            function mulSubInto(out, x, y) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                let y0 := mload(y)
                let y1 := mload(add(y, 0x20))
                let y2 := mload(add(y, 0x40))
                mstore(
                    out,
                    mod(
                        sub(
                            add(mload(out), 0xffffffff0000000100000000000000000),
                            add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1))))
                        ),
                        p
                    )
                )
                mstore(
                    add(out, 0x20),
                    mod(
                        sub(
                            add(mload(add(out, 0x20)), 0xffffffff0000000100000000000000000),
                            add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2)))
                        ),
                        p
                    )
                )
                mstore(
                    add(out, 0x40),
                    mod(
                        sub(
                            add(mload(add(out, 0x40)), 0xffffffff0000000100000000000000000),
                            add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0))
                        ),
                        p
                    )
                )
            }
            // out <- out + 2 * x * y (sum < 2^64 + 10 * 2^128)
            function mulDoubleAddInto(out, x, y) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                let y0 := mload(y)
                let y1 := mload(add(y, 0x20))
                let y2 := mload(add(y, 0x40))
                mstore(out, mod(add(mload(out), shl(1, add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1)))))), p))
                mstore(
                    add(out, 0x20),
                    mod(add(mload(add(out, 0x20)), shl(1, add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2))))), p)
                )
                mstore(
                    add(out, 0x40),
                    mod(add(mload(add(out, 0x40)), shl(1, add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0)))), p)
                )
            }
            // out <- a^2 - 2 * b * c (unreduced a^2 limbs < 5 * 2^128, 2bc limbs < 10 * 2^128)
            function squareMinusDoubleProductInto(out, a, b, c) {
                let p := 0xFFFFFFFF00000001
                let q0 := 0
                let q1 := 0
                let q2 := 0
                {
                    let a0 := mload(a)
                    let a1 := mload(add(a, 0x20))
                    let a2 := mload(add(a, 0x40))
                    q0 := add(mul(a0, a0), shl(2, mul(a1, a2)))
                    q1 := shl(1, add(mul(a0, a1), mul(a2, a2)))
                    q2 := add(shl(1, mul(a0, a2)), mul(a1, a1))
                }
                let x0 := mload(b)
                let x1 := mload(add(b, 0x20))
                let x2 := mload(add(b, 0x40))
                let y0 := mload(c)
                let y1 := mload(add(c, 0x20))
                let y2 := mload(add(c, 0x40))
                mstore(out, mod(sub(add(q0, 0xffffffff0000000100000000000000000), shl(1, add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1)))))), p))
                mstore(add(out, 0x20), mod(sub(add(q1, 0xffffffff0000000100000000000000000), shl(1, add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2))))), p))
                mstore(add(out, 0x40), mod(sub(add(q2, 0xffffffff0000000100000000000000000), shl(1, add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0)))), p))
            }
            // out <- 2 * a^2 - b * c (unreduced 2a^2 limbs < 10 * 2^128)
            function doubleSquareMinusProductInto(out, a, b, c) {
                let p := 0xFFFFFFFF00000001
                let q0 := 0
                let q1 := 0
                let q2 := 0
                {
                    let a0 := mload(a)
                    let a1 := mload(add(a, 0x20))
                    let a2 := mload(add(a, 0x40))
                    q0 := shl(1, add(mul(a0, a0), shl(2, mul(a1, a2))))
                    q1 := shl(1, shl(1, add(mul(a0, a1), mul(a2, a2))))
                    q2 := shl(1, add(shl(1, mul(a0, a2)), mul(a1, a1)))
                }
                let x0 := mload(b)
                let x1 := mload(add(b, 0x20))
                let x2 := mload(add(b, 0x40))
                let y0 := mload(c)
                let y1 := mload(add(c, 0x20))
                let y2 := mload(add(c, 0x40))
                mstore(out, mod(sub(add(q0, 0xffffffff0000000100000000000000000), add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1))))), p))
                mstore(add(out, 0x20), mod(sub(add(q1, 0xffffffff0000000100000000000000000), add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2)))), p))
                mstore(add(out, 0x40), mod(sub(add(q2, 0xffffffff0000000100000000000000000), add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0))), p))
            }
            // out <- a^2 - b * c (unreduced a^2 limbs < 5 * 2^128)
            function squareMinusProductInto(out, a, b, c) {
                let p := 0xFFFFFFFF00000001
                let q0 := 0
                let q1 := 0
                let q2 := 0
                {
                    let a0 := mload(a)
                    let a1 := mload(add(a, 0x20))
                    let a2 := mload(add(a, 0x40))
                    q0 := add(mul(a0, a0), shl(2, mul(a1, a2)))
                    q1 := shl(1, add(mul(a0, a1), mul(a2, a2)))
                    q2 := add(shl(1, mul(a0, a2)), mul(a1, a1))
                }
                let x0 := mload(b)
                let x1 := mload(add(b, 0x20))
                let x2 := mload(add(b, 0x40))
                let y0 := mload(c)
                let y1 := mload(add(c, 0x20))
                let y2 := mload(add(c, 0x40))
                mstore(out, mod(sub(add(q0, 0xffffffff0000000100000000000000000), add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1))))), p))
                mstore(add(out, 0x20), mod(sub(add(q1, 0xffffffff0000000100000000000000000), add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2)))), p))
                mstore(add(out, 0x40), mod(sub(add(q2, 0xffffffff0000000100000000000000000), add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0))), p))
            }
            // Formal norm (-> 0x5a0) and recomposed adjugate (-> 0x600) of the denominator coordinates
            //   a = wire + beta_0 + gamma_0 * pos, b = beta_1 + gamma_1 * pos, c = beta_2 + gamma_2 * pos,
            //   (s0, s1, s2) = (a^2 - 2bc, 2c^2 - ab, b^2 - ac), norm = a*s0 + 2*(c*s1 + b*s2),
            //   recomposed = s0 + theta*s1 + theta^2*s2 with theta^3 = 2.
            function denominator(s, wire, pos) {
                let p := 0xFFFFFFFF00000001
                {
                    let p0 := mload(pos)
                    let p1 := mload(add(pos, 0x20))
                    let p2 := mload(add(pos, 0x40))
                    let g := mload(add(s, 0xc0))
                    mstore(add(s, 0x360), mod(add(add(mload(wire), mload(add(s, 0x60))), mul(p0, g)), p))
                    mstore(add(s, 0x380), mod(add(mload(add(wire, 0x20)), mul(p1, g)), p))
                    mstore(add(s, 0x3a0), mod(add(mload(add(wire, 0x40)), mul(p2, g)), p))
                    g := mload(add(s, 0xe0))
                    mstore(add(s, 0x3c0), mod(add(mload(add(s, 0x80)), mul(p0, g)), p))
                    mstore(add(s, 0x3e0), mod(mul(p1, g), p))
                    mstore(add(s, 0x400), mod(mul(p2, g), p))
                    g := mload(add(s, 0x100))
                    mstore(add(s, 0x420), mod(add(mload(add(s, 0xa0)), mul(p0, g)), p))
                    mstore(add(s, 0x440), mod(mul(p1, g), p))
                    mstore(add(s, 0x460), mod(mul(p2, g), p))
                }
                squareMinusDoubleProductInto(add(s, 0x480), add(s, 0x360), add(s, 0x3c0), add(s, 0x420))
                doubleSquareMinusProductInto(add(s, 0x4e0), add(s, 0x420), add(s, 0x360), add(s, 0x3c0))
                squareMinusProductInto(add(s, 0x540), add(s, 0x3c0), add(s, 0x360), add(s, 0x420))
                mulInto(add(s, 0x5a0), add(s, 0x360), add(s, 0x480))
                mulDoubleAddInto(add(s, 0x5a0), add(s, 0x420), add(s, 0x4e0))
                mulDoubleAddInto(add(s, 0x5a0), add(s, 0x3c0), add(s, 0x540))
                mstore(add(s, 0x600), mod(add(mload(add(s, 0x480)), shl(1, add(mload(add(s, 0x520)), mload(add(s, 0x560))))), p))
                mstore(add(s, 0x620), mod(add(mload(add(s, 0x4a0)), add(mload(add(s, 0x4e0)), shl(1, mload(add(s, 0x580))))), p))
                mstore(add(s, 0x640), mod(add(mload(add(s, 0x4c0)), add(mload(add(s, 0x500)), mload(add(s, 0x540)))), p))
            }
            function wireStep(s, i) {
                let p := 0xFFFFFFFF00000001
                let wire := add(mload(add(s, 0x720)), mul(i, 0x60))
                {
                    // identity position = k_i * subgroup(point): an Ext3 times a base scalar
                    let k := mload(add(mload(add(s, 0x7a0)), shl(5, i)))
                    mstore(add(s, 0x2a0), mod(mul(mload(s), k), p))
                    mstore(add(s, 0x2c0), mod(mul(mload(add(s, 0x20)), k), p))
                    mstore(add(s, 0x2e0), mod(mul(mload(add(s, 0x40)), k), p))
                }
                denominator(s, wire, add(s, 0x2a0))
                let helper := add(mload(add(s, 0x760)), mul(i, 0x60))
                // Z_id = T_id * N_id - 1
                mulInto(add(s, 0x300), helper, add(s, 0x5a0))
                mstore(add(s, 0x300), mod(add(mload(add(s, 0x300)), 0xFFFFFFFF00000000), p))
                // logUp += T_id * R_id
                mulAddInto(add(s, 0x240), helper, add(s, 0x600))

                denominator(s, wire, add(mload(add(s, 0x740)), mul(i, 0x60)))
                helper := add(mload(add(s, 0x780)), mul(i, 0x60))
                // logUp -= T_sigma * R_sigma
                mulSubInto(add(s, 0x240), helper, add(s, 0x600))
                // Z_sigma = T_sigma * N_sigma - 1, then Z_id += rho * Z_sigma
                mulInto(add(s, 0x660), helper, add(s, 0x5a0))
                mstore(add(s, 0x660), mod(add(mload(add(s, 0x660)), 0xFFFFFFFF00000000), p))
                mulAddInto(add(s, 0x300), add(s, 0x120), add(s, 0x660))
                // accumulator = accumulator * lambda + (Z_id + rho * Z_sigma) (Horner over the routed wires)
                mulInto(add(s, 0x1e0), add(s, 0x1e0), add(s, 0x180))
                mstore(add(s, 0x1e0), mod(add(mload(add(s, 0x1e0)), mload(add(s, 0x300))), p))
                mstore(add(s, 0x200), mod(add(mload(add(s, 0x200)), mload(add(s, 0x320))), p))
                mstore(add(s, 0x220), mod(add(mload(add(s, 0x220)), mload(add(s, 0x340))), p))
            }

            mstore(w, mload(subgroup))
            mstore(add(w, 0x20), mload(add(subgroup, 0x20)))
            mstore(add(w, 0x40), mload(add(subgroup, 0x40)))
            let source := mload(challenges) // beta
            mstore(add(w, 0x60), mload(source))
            mstore(add(w, 0x80), mload(add(source, 0x20)))
            mstore(add(w, 0xa0), mload(add(source, 0x40)))
            source := mload(add(challenges, 0x20)) // gamma
            mstore(add(w, 0xc0), mload(source))
            mstore(add(w, 0xe0), mload(add(source, 0x20)))
            mstore(add(w, 0x100), mload(add(source, 0x40)))
            source := mload(add(challenges, 0x60)) // rho
            mstore(add(w, 0x120), mload(source))
            mstore(add(w, 0x140), mload(add(source, 0x20)))
            mstore(add(w, 0x160), mload(add(source, 0x40)))
            source := mload(add(challenges, 0x40)) // lambda
            mstore(add(w, 0x180), mload(source))
            mstore(add(w, 0x1a0), mload(add(source, 0x20)))
            mstore(add(w, 0x1c0), mload(add(source, 0x40)))
            let numRoutedWires := mload(add(vk, 0x60))
            mstore(add(w, 0x720), add(witness, 0x20))
            mstore(add(w, 0x740), add(add(preprocessed, 0x20), mul(mload(add(vk, 0x40)), 0x60)))
            mstore(add(w, 0x760), add(normInverse, 0x20))
            mstore(add(w, 0x780), add(add(normInverse, 0x20), mul(numRoutedWires, 0x60)))
            mstore(add(w, 0x7a0), add(mload(add(vk, 0xa0)), 0x20))

            for { let i := numRoutedWires } i {} {
                i := sub(i, 1)
                wireStep(w, i)
            }
        }
        // permutationValue = eq(tau, point) * helperZeroChecks + kappa * logUpSum
        assembly ("memory-safe") {
            mstore(permutationValue, 0)
            mstore(add(permutationValue, 0x20), 0)
            mstore(add(permutationValue, 0x40), 0)
        }
        _mulAddInPlace(permutationValue, eqValue, _recordAt(w, 0x1e0));
        _mulAddInPlace(permutationValue, challenges.kappa, _recordAt(w, 0x240));
    }

    /// @dev View three consecutive scratch words as an Ext3 record (no copy).
    function _recordAt(uint256[62] memory w, uint256 offset) private pure returns (GoldilocksExt3.Ext3 memory record) {
        assembly ("memory-safe") {
            record := add(w, offset)
        }
    }

    /// @dev Evaluate sum_i eta^i eq(row_i, point) (W_col_i(point) - PI_i). Duplicate map entries
    /// and PI order are intentionally retained. The sum is taken by Horner from the last public
    /// input down, one run of consecutive same-row entries (at most eight) at a time:
    ///   acc <- acc * eta^L + eq(row) * sum_{t in run} eta^(t - first) D_t,
    /// so a run costs one product per entry plus two, and eta^1..eta^8 are built once on demand.
    /// Coordinates shared by every row are multiplied once; each unique row then adds only its
    /// genuinely varying coordinates and is memoised, so an `eq(row, point)` is never repeated.
    /// Every intermediate is reduced, so the result is the same field element as the direct sum.
    function _publicInputBindingFlat(
        bytes memory publicInputWireMap,
        uint256[] memory witness,
        uint256[] memory publicInputs,
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3 memory eta
    ) private pure returns (GoldilocksExt3.Ext3 memory binding) {
        uint256 count = publicInputs.length;
        if (count == 0) return binding;
        // Scratch (byte offsets): 0x00 map data, 0x20 point table, 0x40 numVars, 0x60 witness data,
        // 0x80 numWires, 0xa0 public input data, 0xc0 varying-row-bit mask, 0xe0 eta record,
        // 0x100 shared-coordinate eq (3 words), 0x160 eta-power table base, 0x180 powers built,
        // 0x1a0 unique-row memo base, 0x1c0 memo entries used, 0x1e0 accumulator (3 words).
        uint256[18] memory w;
        assembly ("memory-safe") {
            // record x times stack triple b (canonical limbs; one `mod` per output limb)
            function mulRecord(x, b0, b1, b2) -> c0, c1, c2 {
                let p := 0xFFFFFFFF00000001
                c0 := mod(add(mul(mload(x), b0), shl(1, add(mul(mload(add(x, 0x20)), b2), mul(mload(add(x, 0x40)), b1)))), p)
                c1 := mod(add(add(mul(mload(x), b1), mul(mload(add(x, 0x20)), b0)), shl(1, mul(mload(add(x, 0x40)), b2))), p)
                c2 := mod(add(add(mul(mload(x), b2), mul(mload(add(x, 0x20)), b1)), mul(mload(add(x, 0x40)), b0)), p)
            }
            // out <- out * (x when bit = 1, 1 - x otherwise) for coordinate record x
            function mulFactorInto(out, x, bit) {
                let p := 0xFFFFFFFF00000001
                let f0 := mload(x)
                let f1 := mload(add(x, 0x20))
                let f2 := mload(add(x, 0x40))
                if iszero(bit) {
                    f0 := mod(add(1, sub(p, f0)), p)
                    f1 := mod(sub(p, f1), p)
                    f2 := mod(sub(p, f2), p)
                }
                let c0, c1, c2 := mulRecord(out, f0, f1, f2)
                mstore(out, c0)
                mstore(add(out, 0x20), c1)
                mstore(add(out, 0x40), c2)
            }
            // out <- out * prod of the equality factors of `row` over the coordinates selected by `mask`
            function selectedEqInto(out, row, mask, pointTable, numVars) {
                for { let v := 0 } lt(v, numVars) { v := add(v, 1) } {
                    if and(shr(v, mask), 1) {
                        mulFactorInto(out, mload(add(pointTable, shl(5, v))), and(shr(v, row), 1))
                    }
                }
            }
            // `row_u16_le` of map entry i (`row_u16_le || routed_column_u8` at byte offset 3*i)
            function rowOf(mapData, i) -> row {
                let word := mload(add(mapData, mul(i, 3)))
                row := or(byte(0, word), shl(8, byte(1, word)))
            }
            // eq(row, point) record from the unique-row memo, computed and memoised on first use
            function eqRow(s, row) -> e {
                let memo := mload(add(s, 0x1a0))
                let used := mload(add(s, 0x1c0))
                for { let j := used } j {} {
                    j := sub(j, 1)
                    let entry := add(memo, shl(7, j))
                    if eq(mload(entry), row) {
                        e := add(entry, 0x20)
                        leave
                    }
                }
                e := add(memo, shl(7, used))
                mstore(e, row)
                e := add(e, 0x20)
                mstore(e, mload(add(s, 0x100)))
                mstore(add(e, 0x20), mload(add(s, 0x120)))
                mstore(add(e, 0x40), mload(add(s, 0x140)))
                selectedEqInto(e, row, mload(add(s, 0xc0)), mload(add(s, 0x20)), mload(add(s, 0x40)))
                mstore(add(s, 0x1c0), add(used, 1))
            }
            // record of eta^length (1 <= length <= 8), extending the power table as needed
            function etaPower(s, length) -> e {
                let base := mload(add(s, 0x160))
                for { let have := mload(add(s, 0x180)) } lt(have, length) { have := add(have, 1) } {
                    let dst := add(base, mul(have, 0x60))
                    switch have
                    case 0 { mcopy(dst, mload(add(s, 0xe0)), 0x60) }
                    default {
                        let prev := sub(dst, 0x60)
                        let c0, c1, c2 :=
                            mulRecord(mload(add(s, 0xe0)), mload(prev), mload(add(prev, 0x20)), mload(add(prev, 0x40)))
                        mstore(dst, c0)
                        mstore(add(dst, 0x20), c1)
                        mstore(add(dst, 0x40), c2)
                    }
                    mstore(add(s, 0x180), add(have, 1))
                }
                e := add(base, mul(sub(length, 1), 0x60))
            }
            // accumulator (-> 0x1e0..0x220) <- accumulator * eta^length + eq(row) * run
            function flush(s, row, length, r0, r1, r2) {
                let p := 0xFFFFFFFF00000001
                let a0 := mload(add(s, 0x1e0))
                let a1 := mload(add(s, 0x200))
                let a2 := mload(add(s, 0x220))
                if or(a0, or(a1, a2)) { a0, a1, a2 := mulRecord(etaPower(s, length), a0, a1, a2) }
                r0, r1, r2 := mulRecord(eqRow(s, row), r0, r1, r2)
                mstore(add(s, 0x1e0), mod(add(a0, r0), p))
                mstore(add(s, 0x200), mod(add(a1, r1), p))
                mstore(add(s, 0x220), mod(add(a2, r2), p))
            }

            let p := 0xFFFFFFFF00000001
            mstore(w, add(publicInputWireMap, 0x20))
            mstore(add(w, 0x20), add(point, 0x20))
            mstore(add(w, 0x40), mload(point))
            mstore(add(w, 0x60), add(witness, 0x20))
            mstore(add(w, 0x80), div(mload(witness), 3))
            mstore(add(w, 0xa0), add(publicInputs, 0x20))
            mstore(add(w, 0xe0), eta)
            {
                let row0 := rowOf(mload(w), 0)
                let varying := 0
                for { let i := 1 } lt(i, count) { i := add(i, 1) } {
                    varying := or(varying, xor(row0, rowOf(mload(w), i)))
                }
                mstore(add(w, 0xc0), varying)
                // eq over the coordinates every row shares, evaluated once
                mstore(add(w, 0x100), 1)
                selectedEqInto(add(w, 0x100), row0, not(varying), mload(add(w, 0x20)), mload(add(w, 0x40)))
            }
            // temporary memory past the free pointer: eta^1..eta^8, then the memo `(row, eq0, eq1, eq2)`
            mstore(add(w, 0x160), mload(0x40))
            mstore(add(w, 0x1a0), add(mload(0x40), 0x300))
            // walk the public inputs from the last one down, one same-row run (at most eight) at a time
            let runRow := 0
            let length := 0
            let r0 := 0
            let r1 := 0
            let r2 := 0
            for { let i := count } i {} {
                i := sub(i, 1)
                let word := mload(add(mload(w), mul(i, 3)))
                let row := or(byte(0, word), shl(8, byte(1, word)))
                if iszero(and(eq(row, runRow), lt(length, 8))) {
                    if length { flush(w, runRow, length, r0, r1, r2) }
                    runRow := row
                    length := 0
                    r0 := 0
                    r1 := 0
                    r2 := 0
                }
                // run <- run * eta + (W_column - PI_i)
                if length { r0, r1, r2 := mulRecord(mload(add(w, 0xe0)), r0, r1, r2) }
                word := byte(2, word)
                if iszero(lt(word, mload(add(w, 0x80)))) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                word := add(mload(add(w, 0x60)), mul(word, 0x60))
                r0 := mod(add(r0, add(mload(word), sub(p, mload(add(mload(add(w, 0xa0)), shl(5, i)))))), p)
                r1 := mod(add(r1, mload(add(word, 0x20))), p)
                r2 := mod(add(r2, mload(add(word, 0x40))), p)
                length := add(length, 1)
            }
            flush(w, runRow, length, r0, r1, r2)
            mstore(binding, mload(add(w, 0x1e0)))
            mstore(add(binding, 0x20), mload(add(w, 0x200)))
            mstore(add(binding, 0x40), mload(add(w, 0x220)))
        }
    }

    /// @dev eq(tau, point) = prod_i (1 - tau_i - x_i + 2 tau_i x_i).
    function _eqEvaluation(GoldilocksExt3.Ext3[] memory tau, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        GoldilocksExt3.Ext3 memory factor;
        value.c0 = 1;
        uint256 n = point.length;
        for (uint256 i = 0; i < n; ++i) {
            GoldilocksExt3.Ext3 memory t = tau[i];
            GoldilocksExt3.Ext3 memory x = point[i];
            assembly ("memory-safe") {
                let p := 0xFFFFFFFF00000001
                let t0 := mload(t)
                let t1 := mload(add(t, 0x20))
                let t2 := mload(add(t, 0x40))
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                // factor = 1 - tau - x + 2 * tau * x, lazily: 2p - (tau + x) >= 2 and the doubled
                // unreduced product limbs are < 10 * 2^128, reduced once per limb
                mstore(
                    factor,
                    mod(
                        add(
                            add(1, sub(0x1FFFFFFFE00000002, add(t0, x0))),
                            shl(1, add(mul(t0, x0), shl(1, add(mul(t1, x2), mul(t2, x1)))))
                        ),
                        p
                    )
                )
                mstore(
                    add(factor, 0x20),
                    mod(
                        add(
                            sub(0x1FFFFFFFE00000002, add(t1, x1)),
                            shl(1, add(add(mul(t0, x1), mul(t1, x0)), shl(1, mul(t2, x2))))
                        ),
                        p
                    )
                )
                mstore(
                    add(factor, 0x40),
                    mod(
                        add(sub(0x1FFFFFFFE00000002, add(t2, x2)), shl(1, add(add(mul(t0, x2), mul(t1, x1)), mul(t2, x0)))),
                        p
                    )
                )
            }
            _mulInPlace(value, factor);
        }
    }

    /// @dev subgroup(point) = prod_i (1 + x_i * (g_i - 1)) with base-field generator powers.
    function _subgroupEvaluation(uint256[] memory subgroupGenPowers, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        GoldilocksExt3.Ext3 memory factor;
        value.c0 = 1;
        uint256 n = point.length;
        for (uint256 i = 0; i < n; ++i) {
            uint256 generator = subgroupGenPowers[i];
            GoldilocksExt3.Ext3 memory x = point[i];
            assembly ("memory-safe") {
                let p := 0xFFFFFFFF00000001
                let g := mod(add(generator, 0xFFFFFFFF00000000), p)
                mstore(factor, mod(add(1, mul(mload(x), g)), p))
                mstore(add(factor, 0x20), mod(mul(mload(add(x, 0x20)), g), p))
                mstore(add(factor, 0x40), mod(mul(mload(add(x, 0x40)), g), p))
            }
            _mulInPlace(value, factor);
        }
    }

    /// @dev destination *= multiplier (all loads precede the stores, so aliasing is fine).
    function _mulInPlace(GoldilocksExt3.Ext3 memory destination, GoldilocksExt3.Ext3 memory multiplier)
        private
        pure
    {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let a0 := mload(destination)
            let a1 := mload(add(destination, 0x20))
            let a2 := mload(add(destination, 0x40))
            let b0 := mload(multiplier)
            let b1 := mload(add(multiplier, 0x20))
            let b2 := mload(add(multiplier, 0x40))
            // lazy reduction over canonical limbs: integer sums < 5 * 2^128, one `mod` per limb
            mstore(destination, mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), p))
            mstore(add(destination, 0x20), mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), p))
            mstore(add(destination, 0x40), mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), p))
        }
    }

    /// @dev destination += x * y.
    function _mulAddInPlace(
        GoldilocksExt3.Ext3 memory destination,
        GoldilocksExt3.Ext3 memory x,
        GoldilocksExt3.Ext3 memory y
    ) private pure {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let x0 := mload(x)
            let x1 := mload(add(x, 0x20))
            let x2 := mload(add(x, 0x40))
            let y0 := mload(y)
            let y1 := mload(add(y, 0x20))
            let y2 := mload(add(y, 0x40))
            // lazy reduction over canonical limbs: integer sums < 2^64 + 5 * 2^128, one `mod` per limb
            mstore(destination, mod(add(mload(destination), add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1))))), p))
            mstore(
                add(destination, 0x20),
                mod(add(mload(add(destination, 0x20)), add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2)))), p)
            )
            mstore(
                add(destination, 0x40),
                mod(add(mload(add(destination, 0x40)), add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0))), p)
            )
        }
    }

    /// @dev Formal adjugate `(a^2 - 2bc, 2c^2 - ab, b^2 - ac)` and formal norm
    /// `a*s0 + 2*(c*s1 + b*s2)` of Ext3-valued coordinate polynomials, written into the
    /// caller-allocated records.
    function _formalTerms(
        GoldilocksExt3.Ext3[3] memory coordinates,
        GoldilocksExt3.Ext3[3] memory adjugate,
        GoldilocksExt3.Ext3 memory norm
    ) private pure {
        GoldilocksExt3.Ext3 memory product;
        assembly ("memory-safe") {
            function mulInto(out, x, y) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                let y0 := mload(y)
                let y1 := mload(add(y, 0x20))
                let y2 := mload(add(y, 0x40))
                mstore(out, mod(add(mul(x0, y0), shl(1, add(mul(x1, y2), mul(x2, y1)))), p))
                mstore(add(out, 0x20), mod(add(add(mul(x0, y1), mul(x1, y0)), shl(1, mul(x2, y2))), p))
                mstore(add(out, 0x40), mod(add(add(mul(x0, y2), mul(x1, y1)), mul(x2, y0)), p))
            }
            function squareInto(out, x) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                mstore(out, mod(add(mul(x0, x0), shl(2, mul(x1, x2))), p))
                mstore(add(out, 0x20), mod(shl(1, add(mul(x0, x1), mul(x2, x2))), p))
                mstore(add(out, 0x40), mod(add(shl(1, mul(x0, x2)), mul(x1, x1)), p))
            }
            // lazy reduction: every operand below is a canonical limb (< 2^64), so each integer sum is
            // < 2^67 and is reduced once; 2p - 2x and p - x are non-negative for canonical x
            let p := 0xFFFFFFFF00000001
            let a := mload(coordinates)
            let b := mload(add(coordinates, 0x20))
            let c := mload(add(coordinates, 0x40))
            // s0 = a^2 - 2bc
            let s := mload(adjugate)
            squareInto(s, a)
            mulInto(product, b, c)
            mstore(s, mod(add(mload(s), sub(0x1FFFFFFFE00000002, shl(1, mload(product)))), p))
            mstore(add(s, 0x20), mod(add(mload(add(s, 0x20)), sub(0x1FFFFFFFE00000002, shl(1, mload(add(product, 0x20))))), p))
            mstore(add(s, 0x40), mod(add(mload(add(s, 0x40)), sub(0x1FFFFFFFE00000002, shl(1, mload(add(product, 0x40))))), p))
            // s1 = 2c^2 - ab
            s := mload(add(adjugate, 0x20))
            squareInto(s, c)
            mulInto(product, a, b)
            mstore(s, mod(add(shl(1, mload(s)), sub(p, mload(product))), p))
            mstore(add(s, 0x20), mod(add(shl(1, mload(add(s, 0x20))), sub(p, mload(add(product, 0x20)))), p))
            mstore(add(s, 0x40), mod(add(shl(1, mload(add(s, 0x40))), sub(p, mload(add(product, 0x40)))), p))
            // s2 = b^2 - ac
            s := mload(add(adjugate, 0x40))
            squareInto(s, b)
            mulInto(product, a, c)
            mstore(s, mod(add(mload(s), sub(p, mload(product))), p))
            mstore(add(s, 0x20), mod(add(mload(add(s, 0x20)), sub(p, mload(add(product, 0x20)))), p))
            mstore(add(s, 0x40), mod(add(mload(add(s, 0x40)), sub(p, mload(add(product, 0x40)))), p))
            // norm = a*s0 + 2*(c*s1 + b*s2)
            mulInto(norm, a, mload(adjugate))
            mulInto(product, c, mload(add(adjugate, 0x20)))
            mstore(norm, mod(add(mload(norm), shl(1, mload(product))), p))
            mstore(add(norm, 0x20), mod(add(mload(add(norm, 0x20)), shl(1, mload(add(product, 0x20)))), p))
            mstore(add(norm, 0x40), mod(add(mload(add(norm, 0x40)), shl(1, mload(add(product, 0x40)))), p))
            mulInto(product, b, mload(add(adjugate, 0x40)))
            mstore(norm, mod(add(mload(norm), shl(1, mload(product))), p))
            mstore(add(norm, 0x20), mod(add(mload(add(norm, 0x20)), shl(1, mload(add(product, 0x20)))), p))
            mstore(add(norm, 0x40), mod(add(mload(add(norm, 0x40)), shl(1, mload(add(product, 0x40)))), p))
        }
    }

    // ---------------------------------------------------------------- layout conversion

    /// @dev Flatten `numVars` rounds of exactly `degree` coefficients each into the round-major
    /// limb layout. Any other shape reverts with `InvalidMleProof`.
    function _flattenRounds(SumcheckProof memory proof, uint256 numVars, uint256 degree)
        private
        pure
        returns (uint256[] memory flat)
    {
        CoefficientRound[] memory rounds = proof.rounds;
        if (rounds.length != numVars || numVars > MAX_ROW_VARIABLES || degree > MAX_GATE_DEGREE) {
            revert InvalidMleProof();
        }
        uint256 words = numVars * degree * 3;
        assembly ("memory-safe") {
            flat := mload(0x40)
            mstore(flat, words)
            let destination := add(flat, 0x20)
            mstore(0x40, add(destination, shl(5, words)))
            for { let r := 0 } lt(r, numVars) { r := add(r, 1) } {
                let coefficients := mload(mload(add(add(rounds, 0x20), shl(5, r))))
                if iszero(eq(mload(coefficients), degree)) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                for { let j := 0 } lt(j, degree) { j := add(j, 1) } {
                    mcopy(destination, mload(add(add(coefficients, 0x20), shl(5, j))), 0x60)
                    destination := add(destination, 0x60)
                }
            }
        }
    }

    /// @dev Copy an `Ext3[]` into the flat three-words-per-element layout.
    function _flattenExt3(GoldilocksExt3.Ext3[] memory values) private pure returns (uint256[] memory flat) {
        assembly ("memory-safe") {
            let count := mload(values)
            flat := mload(0x40)
            mstore(flat, mul(count, 3))
            let destination := add(flat, 0x20)
            mstore(0x40, add(destination, mul(count, 0x60)))
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                mcopy(destination, mload(add(add(values, 0x20), shl(5, i))), 0x60)
                destination := add(destination, 0x60)
            }
        }
    }

    // ---------------------------------------------------------------- validation

    function _validateAll(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal
    ) private pure {
        _validateProofs(logProof, gateProof, vk.numVars, vk.gateDegree);
        // The actual point is generated canonically by TranscriptV2 after this
        // preflight, so do not allocate a proof-sized placeholder here.
        _validateTerminalShapeAndCanonical(vk, challenges, terminal);
    }

    function _validateProofs(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        uint256 numVars,
        uint256 gateDegree
    ) private pure {
        if (
            numVars == 0 || numVars > MAX_ROW_VARIABLES || gateDegree == 0 || gateDegree > MAX_GATE_DEGREE
                || logProof.rounds.length != numVars || gateProof.rounds.length != numVars
        ) {
            revert InvalidMleProof();
        }
        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            GoldilocksExt3.Ext3[] memory coefficients = logProof.rounds[roundIndex].nonConstant;
            if (coefficients.length != MAX_DEGREE) revert InvalidMleProof();
            for (uint256 coefficientIndex = 0; coefficientIndex < MAX_DEGREE; ++coefficientIndex) {
                _checkCanonical(coefficients[coefficientIndex]);
            }
            GoldilocksExt3.Ext3[] memory gateCoefficients = gateProof.rounds[roundIndex].nonConstant;
            if (gateCoefficients.length != gateDegree) revert InvalidMleProof();
            for (uint256 coefficientIndex = 0; coefficientIndex < gateDegree; ++coefficientIndex) {
                _checkCanonical(gateCoefficients[coefficientIndex]);
            }
        }
    }

    function _validateTerminalInputs(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) private pure {
        _validateTerminalShapeAndCanonical(vk, challenges, terminal);
        if (point.length != vk.numVars) revert InvalidMleProof();
        for (uint256 i = 0; i < point.length; ++i) {
            _checkCanonical(point[i]);
        }
    }

    function _validateTerminalShapeAndCanonical(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal
    ) private pure {
        if (
            vk.numVars > MAX_ROW_VARIABLES || vk.numRoutedWires > MAX_ROUTED_WIRES
                || vk.numWires > MAX_CONSTITUENT_WIDTH || vk.numRoutedWires > vk.numWires
                || vk.numConstants > MAX_CONSTITUENT_WIDTH - vk.numRoutedWires || vk.kIs.length != vk.numRoutedWires
                || vk.subgroupGenPowers.length != vk.numVars || challenges.tau.length != vk.numVars
                || terminal.preprocessed.length != vk.numConstants + vk.numRoutedWires
                || terminal.witness.length != vk.numWires || terminal.normInverse.length != 2 * vk.numRoutedWires
                || terminal.publicInputs.length > type(uint256).max / 3
                || vk.publicInputWireMap.length != 3 * terminal.publicInputs.length
        ) revert InvalidMleProof();

        _checkCanonical(challenges.beta);
        _checkCanonical(challenges.gamma);
        _checkCanonical(challenges.lambda);
        _checkCanonical(challenges.rho);
        _checkCanonical(challenges.kappa);
        _checkCanonical(challenges.eta);
        _checkCanonical(challenges.xi);
        for (uint256 i = 0; i < challenges.tau.length; ++i) {
            _checkCanonical(challenges.tau[i]);
        }
        for (uint256 i = 0; i < vk.kIs.length; ++i) {
            if (vk.kIs[i] >= P) revert InvalidMleProof();
        }
        for (uint256 i = 0; i < vk.subgroupGenPowers.length; ++i) {
            if (vk.subgroupGenPowers[i] >= P) revert InvalidMleProof();
        }
        for (uint256 i = 0; i < terminal.preprocessed.length; ++i) {
            _checkCanonical(terminal.preprocessed[i]);
        }
        for (uint256 i = 0; i < terminal.witness.length; ++i) {
            _checkCanonical(terminal.witness[i]);
        }
        for (uint256 i = 0; i < terminal.normInverse.length; ++i) {
            _checkCanonical(terminal.normInverse[i]);
        }
        uint256 degree = uint256(1) << vk.numVars;
        for (uint256 i = 0; i < terminal.publicInputs.length; ++i) {
            if (terminal.publicInputs[i] >= P) revert InvalidMleProof();
            uint256 offset = 3 * i;
            uint256 row =
                uint8(vk.publicInputWireMap[offset]) | (uint256(uint8(vk.publicInputWireMap[offset + 1])) << 8);
            uint256 column = uint8(vk.publicInputWireMap[offset + 2]);
            if (row >= degree || column >= vk.numRoutedWires) revert InvalidMleProof();
        }
    }

    function _checkCanonical(GoldilocksExt3.Ext3 memory value) private pure {
        if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
            revert InvalidMleProof();
        }
    }
}
