// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SpongefishWhir} from "./SpongefishWhir.sol";
import {SpongefishMerkle} from "./SpongefishMerkle.sol";
import {GoldilocksExt3} from "./GoldilocksExt3.sol";
import {WhirLinearAlgebra} from "./WhirLinearAlgebra.sol";
import {Keccak256Chain} from "./Keccak256Chain.sol";
import {InvalidMleProof} from "../MleProofErrors.sol";

/// @title SpongefishWhirVerify
/// @notice Full WHIR verification matching WizardOfMenlo/whir verifier.rs
/// @dev Internal Ext3 vectors are kept in "flat" layout: a uint256[] holding three canonical
///      Goldilocks limbs (c0, c1, c2) per element. Hot loops multiply with lazy reduction
///      (plain `mul`/`add` over < 2^64 limbs, one `mod` per output limb), which yields exactly
///      the same canonical values as the mulmod/addmod formulation.
library SpongefishWhirVerify {
    using GoldilocksExt3 for GoldilocksExt3.Ext3;
    using Keccak256Chain for Keccak256Chain.Sponge;
    using SpongefishWhir for SpongefishWhir.TranscriptState;

    uint64 constant GL_P = 0xFFFFFFFF00000001;
    uint256 private constant P = 0xFFFFFFFF00000001;

    error DuplicateLeafMismatch();
    error FinalOpeningMismatch();
    error FinalClaimMismatch();
    error InvalidHints();
    error InvalidParameters();
    error TranscriptNotConsumed();
    error ZeroPolynomialEvaluation();

    struct RoundParams {
        uint256 codewordLength;
        uint256 merkleDepth;
        uint64 domainGenerator;
        uint256 inDomainSamples;
        uint256 outDomainSamples;
        uint256 sumcheckRounds;
        uint256 interleavingDepth;
        uint256 cosetSize;
        uint256 numCosets;
        uint256 numVariables;
        uint64 powThreshold;
        uint64 sumcheckPowThreshold;
    }

    struct WhirParams {
        uint256 numVariables;
        uint256 foldingFactor;
        uint256 numVectors;
        /// Number of separate split-commit calls (1 = standard, 2 = split-commit).
        /// Total effective vectors = numCommitments * numVectors.
        uint256 numCommitments;
        uint256 outDomainSamples;
        uint256 inDomainSamples;
        uint256 initialSumcheckRounds;
        uint256 numRounds;
        uint256 finalSumcheckRounds;
        uint256 finalSize;
        uint256 initialCodewordLength;
        uint256 initialMerkleDepth;
        uint64 initialDomainGenerator;
        uint256 initialInterleavingDepth;
        // FinalClaim params
        uint256 initialNumVariables;
        uint256 initialCosetSize;
        uint256 initialNumCosets;
        uint64 initialSumcheckPowThreshold;
        uint64 finalPowThreshold;
        uint64 finalSumcheckPowThreshold;
        // Evaluation point(s) for FinalClaim. Grouped v1 requires every point
        // explicitly and with exactly `numVariables` canonical Ext3 entries.
        GoldilocksExt3.Ext3[] evaluationPoint;
        // Second evaluation point (for dual-point / gζ bridge).
        // If empty, single-point mode (numLinearForms = 1).
        // With dual bridge, this is the sumcheck-derived point r₂ for gζ.
        GoldilocksExt3.Ext3[] evaluationPoint2;
        // Additional evaluation points (multi-point support beyond 2).
        // Used for the v2 logUp soundness fix which opens at 3 points
        // (r_gate, r_inv, r_h). Each entry is an evaluation point of
        // length numVariables. Empty for legacy 1- or 2-point usage.
        GoldilocksExt3.Ext3[][] additionalEvaluationPoints;
        // Per-round params (array of length numRounds)
        RoundParams[] rounds;
    }

    /// @notice One entry in round_constraints: RLC coefficients + evaluation points for UnivariateEvaluation
    struct RoundConstraintEntry {
        uint256[] rlcCoeffs; // flat Ext3 limbs, 3 words per coefficient
        uint256[] points; // flat Ext3 limbs: OOD points ++ in-domain points (base field: c1 = c2 = 0)
        uint256 numVariables; // for eval_point slice
    }

    struct VerifyState {
        GoldilocksExt3.Ext3 theSum;
        uint256[] foldR; // flat folding randomness, 3 words per element
        uint256 foldIdx;
        uint256 totalFoldingLen;
        bytes32 prevRoot;
        // Split-commit: per-commitment roots for round-0 Merkle verification
        bytes32[] initialRoots;
        // Vector RLC coefficients (from initial phase, needed for split in-domain eval), flat
        uint256[] vectorRlc;
        // Initial phase, flat
        uint256[] initialConstraintRlc;
        uint256 numLinearForms;
        // Round constraints for FinalClaim subtraction
        // Entry 0: initial OOD constraints
        // Entry 1+: intermediate round constraints (OOD + in-domain)
        RoundConstraintEntry[] roundConstraints;
    }

    // =====================================================================
    // Main entry point
    // =====================================================================
    /// @notice Verify the v1 grouped-constituent statement.
    /// @dev `evaluationMask` is a little-endian bitset. A set bit requires the
    /// transcript-bound Ext3 claim to equal `evaluations[i]`; unset entries are
    /// still verified by WHIR but are not consumed by an MLE terminal equation.
    /// All evaluation claims are read before WHIR samples its vector RLC.
    function verifyWhirProofBound(
        bytes memory protocolId,
        bytes memory sessionId,
        bytes memory instance,
        bytes memory transcript,
        bytes calldata hints,
        GoldilocksExt3.Ext3[] memory evaluations,
        bytes memory evaluationMask,
        bytes32[] memory expectedRoots,
        WhirParams memory params
    ) external pure returns (bool) {
        if (params.numCommitments == 0 || params.numVectors == 0) {
            revert InvalidParameters();
        }
        if (evaluationMask.length != (evaluations.length + 7) / 8) revert InvalidParameters();
        if (expectedRoots.length != params.numCommitments) revert InvalidParameters();
        uint256 totalVectors = params.numCommitments * params.numVectors;
        if (evaluations.length == 0 || evaluations.length % totalVectors != 0) {
            revert InvalidParameters();
        }
        _validateParameters(params, evaluations.length / totalVectors);
        SpongefishMerkle.CalldataBytes memory hintsView =
            SpongefishMerkle.CalldataBytes({offset: 0, length: hints.length});
        assembly ("memory-safe") {
            mstore(hintsView, hints.offset)
        }
        return _verifyWhirProof(
            protocolId, sessionId, instance, transcript, hintsView, evaluations, evaluationMask, expectedRoots, params
        );
    }

    /// @notice Validate a deployment-time WHIR configuration without reading
    /// any prover bytes. Production MLE v2 deployment uses this before pinning
    /// the configuration digest, so malformed VK parameters remain
    /// UNEVALUABLE rather than becoming proof-fraud evidence.
    function validateParameters(WhirParams memory params, uint256 numLinearForms) external pure {
        if (numLinearForms == 0) revert InvalidParameters();
        _validateParameters(params, numLinearForms);
    }

    /// @dev Reject inconsistent or tailed verifier configuration before any
    /// proof bytes are consumed. `InvalidParameters` deliberately remains
    /// distinct from `InvalidMleProof`: WhirParams belongs to the stored VK,
    /// so a broken deployment must be UNEVALUABLE rather than slashable.
    function _validateParameters(WhirParams memory params, uint256 numLinearForms) private pure {
        if (
            params.numVariables == 0 || params.numVariables >= 256 || params.initialNumVariables != params.numVariables
                || params.foldingFactor == 0 || params.initialSumcheckRounds == 0
                || params.initialSumcheckRounds > params.numVariables || params.initialSumcheckRounds >= 256
                || params.initialInterleavingDepth != (uint256(1) << params.initialSumcheckRounds)
                || params.rounds.length != params.numRounds
        ) revert InvalidParameters();
        _validateDomain(
            params.initialCodewordLength,
            params.initialMerkleDepth,
            params.initialCosetSize,
            params.initialNumCosets,
            params.initialDomainGenerator
        );

        uint256 remainingVariables = params.numVariables - params.initialSumcheckRounds;
        for (uint256 round = 0; round < params.rounds.length; round++) {
            RoundParams memory rp = params.rounds[round];
            if (
                rp.numVariables != remainingVariables || rp.sumcheckRounds != params.foldingFactor
                    || rp.sumcheckRounds > remainingVariables || rp.sumcheckRounds >= 256
                    || rp.interleavingDepth != (uint256(1) << rp.sumcheckRounds)
            ) revert InvalidParameters();
            _validateDomain(rp.codewordLength, rp.merkleDepth, rp.cosetSize, rp.numCosets, rp.domainGenerator);
            remainingVariables -= rp.sumcheckRounds;
        }
        if (
            remainingVariables != params.finalSumcheckRounds || params.finalSumcheckRounds >= 256
                || params.finalSize != (uint256(1) << params.finalSumcheckRounds)
        ) revert InvalidParameters();

        // Grouped-v1 supplies every linear-form point explicitly. Exact
        // lengths avoid the historical optional/ignored point tails.
        if (params.evaluationPoint.length != params.numVariables) revert InvalidParameters();
        _validateEvaluationPoint(params.evaluationPoint);
        if (numLinearForms == 1) {
            if (params.evaluationPoint2.length != 0 || params.additionalEvaluationPoints.length != 0) {
                revert InvalidParameters();
            }
            return;
        }
        if (
            params.evaluationPoint2.length != params.numVariables
                || params.additionalEvaluationPoints.length != numLinearForms - 2
        ) revert InvalidParameters();
        _validateEvaluationPoint(params.evaluationPoint2);
        for (uint256 i = 0; i < params.additionalEvaluationPoints.length; i++) {
            if (params.additionalEvaluationPoints[i].length != params.numVariables) {
                revert InvalidParameters();
            }
            _validateEvaluationPoint(params.additionalEvaluationPoints[i]);
        }
    }

    function _validateEvaluationPoint(GoldilocksExt3.Ext3[] memory point) private pure {
        for (uint256 i = 0; i < point.length; i++) {
            GoldilocksExt3.Ext3 memory coordinate = point[i];
            if (coordinate.c0 >= GL_P || coordinate.c1 >= GL_P || coordinate.c2 >= GL_P) {
                revert InvalidParameters();
            }
        }
    }

    function _validateDomain(
        uint256 codewordLength,
        uint256 merkleDepth,
        uint256 cosetSize,
        uint256 numCosets,
        uint64 domainGenerator
    ) private pure {
        if (
            codewordLength == 0 || (codewordLength & (codewordLength - 1)) != 0 || merkleDepth >= 256
                || codewordLength != (uint256(1) << merkleDepth) || cosetSize == 0 || numCosets == 0
                || codewordLength % cosetSize != 0 || codewordLength / cosetSize != numCosets || domainGenerator == 0
                || domainGenerator >= GL_P
        ) revert InvalidParameters();
    }

    function _verifyWhirProof(
        bytes memory protocolId,
        bytes memory sessionId,
        bytes memory instance,
        bytes memory transcript,
        SpongefishMerkle.CalldataBytes memory hints,
        GoldilocksExt3.Ext3[] memory evaluations,
        bytes memory evaluationMask,
        bytes32[] memory expectedRoots,
        WhirParams memory params
    ) private pure returns (bool) {
        SpongefishWhir.TranscriptState memory ts = SpongefishWhir.initTranscript(protocolId, sessionId, instance);

        VerifyState memory vs;
        // Parameter validation proves that the initial, intermediate and final
        // folding rounds partition the original variable count exactly.
        vs.totalFoldingLen = params.numVariables;
        vs.foldR = new uint256[](3 * vs.totalFoldingLen);
        vs.roundConstraints = new RoundConstraintEntry[](1 + params.numRounds);

        // Phase 1: Initial commitment + OOD + RLC + compute "the sum"
        _phaseInitial(ts, transcript, evaluations, evaluationMask, expectedRoots, params, vs);

        // Phase 2: Initial sumcheck
        _phaseSumcheck(ts, transcript, params.initialSumcheckRounds, params.initialSumcheckPowThreshold, vs);

        // Phase 3: Intermediate rounds
        for (uint256 round = 0; round < params.numRounds; round++) {
            _doIntermediateRound(ts, transcript, hints, params, vs, round);
        }

        // Phase 4: Final vector + final Merkle open
        uint256[] memory finalVector = _phaseFinalVectorAndMerkle(ts, transcript, hints, params, vs);

        // Phase 5: Final sumcheck
        _phaseSumcheck(ts, transcript, params.finalSumcheckRounds, params.finalSumcheckPowThreshold, vs);

        // Phase 6: FinalClaim verification
        _phaseFinalClaim(params, vs, finalVector);

        if (ts.transcriptPos != transcript.length) revert InvalidMleProof();
        if (ts.hintPos != hints.length) revert InvalidMleProof();
        return true;
    }

    // =====================================================================
    // Phase 1: Initial commitment + OOD + RLC + sum
    // Supports split-commit mode: numCommitments separate Merkle roots,
    // each with their own OOD cycle, followed by cross-term evaluations.
    // =====================================================================
    function _phaseInitial(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        GoldilocksExt3.Ext3[] memory evaluations,
        bytes memory evaluationMask,
        bytes32[] memory expectedRoots,
        WhirParams memory params,
        VerifyState memory vs
    ) private pure {
        uint256 totalVectors = params.numCommitments * params.numVectors;
        uint256 totalOodPoints = params.numCommitments * params.outDomainSamples;

        // Phase 1a: Receive per-commitment roots and OOD data
        (uint256[] memory perCommitOod, uint256[] memory allOodPoints) =
            _receiveCommitmentsAndOod(ts, transcript, expectedRoots, params, vs);

        // In v1 the complete public evaluation statement precedes the vector
        // RLC challenge. Unchecked entries are copied from the transcript into
        // the matrix; checked entries must match the MLE terminal claims.
        uint256[] memory evalsFlat = _readEvaluationStatement(ts, transcript, evaluations, evaluationMask);

        // Cross-commitment OOD terms are emitted by WHIR prove() only after
        // the v1 bound evaluation statement (legacy proofs reach this point
        // immediately). Keep this read on the corresponding side of the
        // pre-RLC statement boundary.
        uint256[] memory oodMatrix = _completeOodMatrix(ts, transcript, perCommitOod, params);

        // Phase 1b: RLC and sum computation
        vs.vectorRlc = SpongefishWhir.geometricChallengeFlat(ts, totalVectors);
        vs.numLinearForms = evaluations.length / totalVectors;
        vs.initialConstraintRlc = SpongefishWhir.geometricChallengeFlat(ts, totalOodPoints + vs.numLinearForms);

        // Store initial OOD round_constraints entry (entry 0)
        uint256[] memory oodRlcCoeffs = new uint256[](3 * totalOodPoints);
        for (uint256 i = 0; i < 3 * totalOodPoints; i++) {
            oodRlcCoeffs[i] = vs.initialConstraintRlc[3 * vs.numLinearForms + i];
        }
        vs.roundConstraints[0] = RoundConstraintEntry({
            rlcCoeffs: oodRlcCoeffs, points: allOodPoints, numVariables: params.initialNumVariables
        });

        // Compute "the sum"
        vs.theSum = GoldilocksExt3.zero();
        _accumulateTheSum(
            vs.theSum, evalsFlat, vs.vectorRlc, vs.initialConstraintRlc, 0, vs.numLinearForms, totalVectors
        );
        _accumulateTheSum(
            vs.theSum, oodMatrix, vs.vectorRlc, vs.initialConstraintRlc, vs.numLinearForms, totalOodPoints, totalVectors
        );
    }

    /// @dev Receive commitment roots and OOD data for split-commit mode.
    /// Returns the per-commitment OOD answers ([c][oodIdx * nv + v], flat) and the OOD points
    /// (flat). Cross terms are read separately because v1 inserts its bound evaluation
    /// statement first.
    function _receiveCommitmentsAndOod(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        bytes32[] memory expectedRoots,
        WhirParams memory params,
        VerifyState memory vs
    ) private pure returns (uint256[] memory perCommitOod, uint256[] memory allOodPoints) {
        uint256 nc = params.numCommitments;
        uint256 nv = params.numVectors;
        uint256 K = params.outDomainSamples;

        vs.initialRoots = new bytes32[](nc);
        allOodPoints = new uint256[](3 * nc * K);
        perCommitOod = new uint256[](3 * nc * K * nv);

        for (uint256 c = 0; c < nc; c++) {
            bytes32 root = SpongefishWhir.proverMessageHash(ts, transcript);
            vs.initialRoots[c] = root;
            for (uint256 i = 0; i < K; i++) {
                _squeezeInto(ts, allOodPoints, c * K + i);
            }
            for (uint256 i = 0; i < K * nv; i++) {
                _readInto(ts, transcript, perCommitOod, c * K * nv + i);
            }
            bytes32 boundRoot = SpongefishWhir.proverMessageHash(ts, transcript);
            if (boundRoot != expectedRoots[c] || boundRoot != root) {
                revert InvalidMleProof();
            }
        }

        vs.prevRoot = vs.initialRoots[0];
    }

    /// @dev Read the bound evaluation statement: every claim is absorbed; masked claims must
    ///      equal the MLE terminal values. Returns the claims in flat layout.
    function _readEvaluationStatement(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        GoldilocksExt3.Ext3[] memory evaluations,
        bytes memory evaluationMask
    ) private pure returns (uint256[] memory evalsFlat) {
        evalsFlat = new uint256[](3 * evaluations.length);
        for (uint256 i = 0; i < evaluations.length; i++) {
            (uint64 e0, uint64 e1, uint64 e2) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            bool checked = (uint8(evaluationMask[i >> 3]) & uint8(1 << (i & 7))) != 0;
            if (checked) {
                GoldilocksExt3.Ext3 memory expected = evaluations[i];
                if (expected.c0 != e0 || expected.c1 != e1 || expected.c2 != e2) {
                    revert InvalidMleProof();
                }
            }
            evalsFlat[3 * i] = e0;
            evalsFlat[3 * i + 1] = e1;
            evalsFlat[3 * i + 2] = e2;
        }
    }

    /// @dev Squeeze one Ext3 challenge into flat slot `idx` of `buf`.
    function _squeezeInto(SpongefishWhir.TranscriptState memory ts, uint256[] memory buf, uint256 idx) private pure {
        (uint64 c0, uint64 c1, uint64 c2) = SpongefishWhir.verifierMessageField64x3(ts);
        buf[3 * idx] = c0;
        buf[3 * idx + 1] = c1;
        buf[3 * idx + 2] = c2;
    }

    /// @dev Read one canonical Ext3 prover message into flat slot `idx` of `buf`.
    function _readInto(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        uint256[] memory buf,
        uint256 idx
    ) private pure {
        (uint64 c0, uint64 c1, uint64 c2) = SpongefishWhir.proverMessageField64x3(ts, transcript);
        buf[3 * idx] = c0;
        buf[3 * idx + 1] = c1;
        buf[3 * idx + 2] = c2;
    }

    function _completeOodMatrix(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        uint256[] memory perCommitOod,
        WhirParams memory params
    ) private pure returns (uint256[] memory oodMatrix) {
        uint256 nc = params.numCommitments;
        uint256 nv = params.numVectors;
        uint256 K = params.outDomainSamples;
        uint256 totalVectors = nc * nv;
        oodMatrix = new uint256[](3 * nc * K * totalVectors);
        for (uint256 c = 0; c < nc; c++) {
            uint256 vOff = c * nv;
            for (uint256 oodIdx = 0; oodIdx < K; oodIdx++) {
                uint256 row = c * K + oodIdx;
                for (uint256 j = 0; j < totalVectors; j++) {
                    uint256 dst = row * totalVectors + j;
                    if (j >= vOff && j < vOff + nv) {
                        uint256 src = 3 * (c * K * nv + oodIdx * nv + (j - vOff));
                        oodMatrix[3 * dst] = perCommitOod[src];
                        oodMatrix[3 * dst + 1] = perCommitOod[src + 1];
                        oodMatrix[3 * dst + 2] = perCommitOod[src + 2];
                    } else {
                        _readInto(ts, transcript, oodMatrix, dst);
                    }
                }
            }
        }
    }

    /// @dev Accumulate theSum += Σ_i (dot(matrix[i*nv..(i+1)*nv], vectorRlc) * constraintRlc[rlcOff+i]),
    ///      all vectors in flat layout.
    function _accumulateTheSum(
        GoldilocksExt3.Ext3 memory theSum,
        uint256[] memory matrix,
        uint256[] memory vectorRlc,
        uint256[] memory constraintRlc,
        uint256 rlcOffset,
        uint256 count,
        uint256 numVectors
    ) private pure {
        if (
            matrix.length != 3 * count * numVectors || vectorRlc.length != 3 * numVectors
                || constraintRlc.length < 3 * (rlcOffset + count)
        ) revert InvalidMleProof();
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let p := 0xFFFFFFFF00000001
            let mp := add(matrix, 0x20)
            let vData := add(vectorRlc, 0x20)
            let vEnd := add(vData, mul(numVectors, 0x60))
            let cp := add(add(constraintRlc, 0x20), mul(rlcOffset, 0x60))
            let s0 := mload(theSum)
            let s1 := mload(add(theSum, 0x20))
            let s2 := mload(add(theSum, 0x40))
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                // dot = Σ_j matrix[i*nv+j] * vectorRlc[j] (lazy sums of < 2^131 terms)
                let d0 := 0
                let d1 := 0
                let d2 := 0
                for { let vp := vData } lt(vp, vEnd) { vp := add(vp, 0x60) } {
                    let a0 := mload(mp)
                    let a1 := mload(add(mp, 0x20))
                    let a2 := mload(add(mp, 0x40))
                    let b0 := mload(vp)
                    let b1 := mload(add(vp, 0x20))
                    let b2 := mload(add(vp, 0x40))
                    d0 := add(d0, add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))))
                    d1 := add(d1, add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))))
                    d2 := add(d2, add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)))
                    mp := add(mp, 0x60)
                }
                // term = dot * constraintRlc[rlcOffset + i]; theSum += term
                let r0, r1, r2 :=
                    mul3(mod(d0, p), mod(d1, p), mod(d2, p), mload(cp), mload(add(cp, 0x20)), mload(add(cp, 0x40)))
                cp := add(cp, 0x60)
                s0 := addmod(s0, r0, p)
                s1 := addmod(s1, r1, p)
                s2 := addmod(s2, r2, p)
            }
            mstore(theSum, s0)
            mstore(add(theSum, 0x20), s1)
            mstore(add(theSum, 0x40), s2)
        }
    }

    // =====================================================================
    // Phase 2/5: Sumcheck
    // =====================================================================
    function _phaseSumcheck(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        uint256 numRounds,
        uint64 powThreshold,
        VerifyState memory vs
    ) private pure {
        // Round coefficients c0 (slot 0) and c2 (slot 1), flat.
        uint256[] memory coeffs = new uint256[](6);
        uint256[] memory foldR = vs.foldR;
        for (uint256 i = 0; i < numRounds; i++) {
            (uint64 c0a, uint64 c0b, uint64 c0c) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            (uint64 c2a, uint64 c2b, uint64 c2c) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            assembly ("memory-safe") {
                mstore(add(coeffs, 0x20), c0a)
                mstore(add(coeffs, 0x40), c0b)
                mstore(add(coeffs, 0x60), c0c)
                mstore(add(coeffs, 0x80), c2a)
                mstore(add(coeffs, 0xa0), c2b)
                mstore(add(coeffs, 0xc0), c2c)
            }

            _verifyPow(ts, transcript, powThreshold);

            // Squeeze r into the flat folding randomness
            uint256 fi = vs.foldIdx++;
            _squeezeInto(ts, foldR, fi);

            // Compute c1 = theSum - 2*c0 - c2, then theSum = ((c2 * r) + c1) * r + c0
            assembly ("memory-safe") {
                function mul3(a0, a1, a2, b0, b1, b2) -> x0, x1, x2 {
                    x0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                    x1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                    x2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
                }
                let p := 0xFFFFFFFF00000001
                let sp := mload(vs) // vs.theSum is first field
                let cp := add(coeffs, 0x20) // c0 at cp, c2 at cp + 0x60
                let rp := add(add(foldR, 0x20), mul(fi, 0x60))

                // c1 = theSum - 2*c0 - c2
                let c1_0 :=
                    addmod(mload(sp), sub(p, addmod(addmod(mload(cp), mload(cp), p), mload(add(cp, 0x60)), p)), p)
                let c1_1 :=
                    addmod(
                        mload(add(sp, 0x20)),
                        sub(p, addmod(addmod(mload(add(cp, 0x20)), mload(add(cp, 0x20)), p), mload(add(cp, 0x80)), p)),
                        p
                    )
                let c1_2 :=
                    addmod(
                        mload(add(sp, 0x40)),
                        sub(p, addmod(addmod(mload(add(cp, 0x40)), mload(add(cp, 0x40)), p), mload(add(cp, 0xa0)), p)),
                        p
                    )

                // tmp = c2 * r + c1
                let t0, t1, t2 :=
                    mul3(
                        mload(add(cp, 0x60)),
                        mload(add(cp, 0x80)),
                        mload(add(cp, 0xa0)),
                        mload(rp),
                        mload(add(rp, 0x20)),
                        mload(add(rp, 0x40))
                    )
                t0 := addmod(t0, c1_0, p)
                t1 := addmod(t1, c1_1, p)
                t2 := addmod(t2, c1_2, p)

                // theSum = tmp * r + c0
                let n0, n1, n2 := mul3(t0, t1, t2, mload(rp), mload(add(rp, 0x20)), mload(add(rp, 0x40)))
                mstore(sp, addmod(n0, mload(cp), p))
                mstore(add(sp, 0x20), addmod(n1, mload(add(cp, 0x20)), p))
                mstore(add(sp, 0x40), addmod(n2, mload(add(cp, 0x40)), p))
            }
        }
    }

    /// @dev Verify WHIR's optional Keccak proof of work. Rust first squeezes a
    /// 32-byte challenge, then absorbs an LE u64 nonce. The PoW input is
    /// challenge || nonce_le || 24 zero bytes, and the first digest limb is
    /// interpreted as LE u64.
    function _verifyPow(SpongefishWhir.TranscriptState memory ts, bytes memory transcript, uint64 threshold)
        private
        pure
    {
        if (threshold == type(uint64).max) return;
        bytes32 challenge = ts.sponge.squeezeWord();
        uint256 pos = ts.transcriptPos;
        if (pos > transcript.length || 8 > transcript.length - pos) {
            revert InvalidMleProof();
        }
        uint256 value;
        assembly ("memory-safe") {
            mstore(0x00, challenge)
            // Keep exactly the leading eight nonce bytes and explicitly zero the remainder.
            mstore(0x20, shl(192, shr(192, mload(add(add(transcript, 0x20), pos)))))
            let w := shr(192, keccak256(0x00, 0x40))
            w := or(and(shr(8, w), 0x00FF00FF00FF00FF), and(shl(8, w), 0xFF00FF00FF00FF00))
            w := or(and(shr(16, w), 0x0000FFFF0000FFFF), and(shl(16, w), 0xFFFF0000FFFF0000))
            w := or(shr(32, w), shl(32, w))
            value := and(w, 0xFFFFFFFFFFFFFFFF)
        }
        ts.sponge.absorbSlice(transcript, pos, 8);
        ts.transcriptPos = pos + 8;
        if (value > threshold) revert InvalidMleProof();
    }

    // =====================================================================
    // Phase 3: Intermediate rounds
    // =====================================================================
    function _doIntermediateRound(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        SpongefishMerkle.CalldataBytes memory hints,
        WhirParams memory params,
        VerifyState memory vs,
        uint256 round
    ) private pure {
        RoundParams memory rp = params.rounds[round];

        // Receive new commitment
        bytes32 roundRoot = SpongefishWhir.proverMessageHash(ts, transcript);

        // OOD for this round: ALL points squeezed first, then ALL answers absorbed
        // (matches Rust irs_commit::receive_commitment order)
        uint256[] memory roundOodPoints = new uint256[](3 * rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            _squeezeInto(ts, roundOodPoints, i);
        }
        uint256[] memory roundOodAnswers = new uint256[](3 * rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            _readInto(ts, transcript, roundOodAnswers, i);
        }

        _verifyPow(ts, transcript, rp.powThreshold);

        // Open previous commitment with Merkle verification
        _openAndVerifyCommitment(ts, hints, params, vs, round, roundOodAnswers, roundOodPoints);

        // Sumcheck
        _phaseSumcheck(ts, transcript, rp.sumcheckRounds, rp.sumcheckPowThreshold, vs);

        vs.prevRoot = roundRoot;
    }

    struct OpenParams {
        uint256 cl;
        uint256 md;
        uint256 rowBytes;
        uint64 domainGen;
        uint256 numCosets;
        uint256 cosetSize;
        uint256 inDomainSamples;
        uint256 numCols;
        bool isBaseField;
    }

    function _getOpenParams(WhirParams memory params, uint256 round) private pure returns (OpenParams memory o) {
        if (round == 0) {
            o.cl = params.initialCodewordLength;
            o.md = params.initialMerkleDepth;
            // SECURITY: In split-commit mode, each commitment has its own Merkle tree
            // with interleaving_depth × numVectors columns (numVectors=1 per commit).
            // Row bytes per commitment = interleaving_depth × numVectors × 8.
            o.rowBytes = params.initialInterleavingDepth * params.numVectors * 8;
            o.domainGen = params.initialDomainGenerator;
            o.numCosets = params.initialNumCosets;
            o.cosetSize = params.initialCosetSize;
            o.inDomainSamples = params.inDomainSamples;
            o.numCols = params.initialInterleavingDepth * params.numVectors;
            o.isBaseField = true;
        } else {
            // Opening the commitment from round (round-1)
            RoundParams memory rp = params.rounds[round - 1];
            o.cl = rp.codewordLength;
            o.md = rp.merkleDepth;
            o.rowBytes = rp.interleavingDepth * 24;
            o.domainGen = rp.domainGenerator;
            o.numCosets = rp.numCosets;
            o.cosetSize = rp.cosetSize;
            o.inDomainSamples = rp.inDomainSamples;
            o.numCols = rp.interleavingDepth;
            o.isBaseField = false;
        }
    }

    /// @dev Open the commitment of round `round - 1` (the initial commitment(s) for round 0) at
    ///      the challenge indices, authenticate every opened row, evaluate the opened rows with
    ///      the eq weights of the fold just completed and fold OOD + in-domain constraints into
    ///      theSum with a fresh geometric RLC. Records the round constraints for FinalClaim.
    function _openAndVerifyCommitment(
        SpongefishWhir.TranscriptState memory ts,
        SpongefishMerkle.CalldataBytes memory hints,
        WhirParams memory params,
        VerifyState memory vs,
        uint256 round,
        uint256[] memory roundOodAnswers,
        uint256[] memory roundOodPoints
    ) private pure {
        OpenParams memory o = _getOpenParams(params, round);
        RoundParams memory rp = params.rounds[round];

        uint256[] memory rawIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        uint256 rawCount = rawIndices.length;

        // eq_weights from the folding randomness of the fold just completed
        uint256 ff = (round == 0) ? params.initialSumcheckRounds : params.rounds[round - 1].sumcheckRounds;
        uint256[] memory eqW = WhirLinearAlgebra.eqWeightsFlat(vs.foldR, vs.foldIdx - ff, ff);
        uint256[] memory inDomainEvalPoints = _computeEvalPoints(rawIndices, o);
        uint256[] memory rowValues = new uint256[](3 * rawCount);

        if (round == 0) {
            // Round 0 rows are vector-major over the commitment's `numVectors` constituents:
            // weights = tensor_product(vectorRlc[c * nv ..], eqW) (Rust's grouped statement).
            // In split-commit mode every commitment has its own Merkle tree; the opened
            // rows of all commitments are summed per query.
            for (uint256 c = 0; c < params.numCommitments; c++) {
                uint256[] memory w =
                    WhirLinearAlgebra.tensorFlat(vs.vectorRlc, c * params.numVectors, params.numVectors, eqW);
                _openRows(ts, hints, o, rawIndices, vs.initialRoots[c], w, rowValues);
            }
        } else {
            _openRows(ts, hints, o, rawIndices, vs.prevRoot, eqW, rowValues);
        }

        // Constraint RLC and accumulation into theSum (OOD values, then in-domain values)
        uint256 constraintCount = rp.outDomainSamples + rawCount;
        uint256[] memory roundRlc = SpongefishWhir.geometricChallengeFlat(ts, constraintCount);
        _mulAddFlat(vs.theSum, roundOodAnswers, roundRlc, 0, rp.outDomainSamples);
        _mulAddFlat(vs.theSum, rowValues, roundRlc, rp.outDomainSamples, rawCount);

        // Build evaluation points for FinalClaim: OOD points ++ base-field in-domain points
        uint256[] memory allEvalPoints = new uint256[](3 * constraintCount);
        if (roundOodPoints.length != 3 * rp.outDomainSamples || inDomainEvalPoints.length != rawCount) {
            revert InvalidMleProof();
        }
        assembly ("memory-safe") {
            let dst := add(allEvalPoints, 0x20)
            let src := add(roundOodPoints, 0x20)
            for { let end := add(src, shl(5, mload(roundOodPoints))) } lt(src, end) { src := add(src, 0x20) } {
                mstore(dst, mload(src))
                dst := add(dst, 0x20)
            }
            src := add(inDomainEvalPoints, 0x20)
            for { let end := add(src, shl(5, rawCount)) } lt(src, end) { src := add(src, 0x20) } {
                mstore(dst, mload(src))
                dst := add(dst, 0x60)
            }
        }
        vs.roundConstraints[1 + round] =
            RoundConstraintEntry({rlcCoeffs: roundRlc, points: allEvalPoints, numVariables: rp.numVariables});
    }

    /// @dev Consume one commitment's opening: Arkworks vec prefix, `rawIndices.length` rows,
    ///      then the Merkle decommitment against `root`. Afterwards `rowValues[i] += dot(w, row_i)`.
    function _openRows(
        SpongefishWhir.TranscriptState memory ts,
        SpongefishMerkle.CalldataBytes memory hints,
        OpenParams memory o,
        uint256[] memory rawIndices,
        bytes32 root,
        uint256[] memory w,
        uint256[] memory rowValues
    ) private pure {
        uint256 rawCount = rawIndices.length;
        _consumeVecPrefix(ts, hints, rawCount * o.numCols);
        uint256 rowsStart = ts.hintPos;
        bytes32[] memory leafHashes = _hashRows(hints, rowsStart, o.rowBytes, rawCount);
        // SpongefishMerkle.verify packs the (index, hash) pairs into its own buffer, so the
        // query list survives for the later commitments / the eval points.
        ts.hintPos =
            SpongefishMerkle.verify(root, o.md, rawIndices, leafHashes, hints, rowsStart + rawCount * o.rowBytes);
        _accumulateRowDots(rowValues, w, o.numCols, hints, rowsStart, o.rowBytes, rawCount, o.isBaseField);
    }

    // =====================================================================
    // Phase 4: Final vector + Merkle
    // =====================================================================
    function _phaseFinalVectorAndMerkle(
        SpongefishWhir.TranscriptState memory ts,
        bytes memory transcript,
        SpongefishMerkle.CalldataBytes memory hints,
        WhirParams memory params,
        VerifyState memory vs
    ) private pure returns (uint256[] memory finalVector) {
        // `_validateParameters` has already bound finalSize exactly to the
        // final sumcheck-round count before any proof bytes are consumed.
        finalVector = new uint256[](3 * params.finalSize);
        for (uint256 i = 0; i < params.finalSize; i++) {
            _readInto(ts, transcript, finalVector, i);
        }

        _verifyPow(ts, transcript, params.finalPowThreshold);

        // The final opening is the same IRS commitment that the next intermediate round would
        // open: the initial commitment(s) when numRounds == 0, otherwise the last round commitment.
        OpenParams memory o = _getOpenParams(params, params.numRounds);
        uint256[] memory rawFinalIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        uint256 foldingRounds =
            params.numRounds == 0 ? params.initialSumcheckRounds : params.rounds[params.numRounds - 1].sumcheckRounds;
        uint256[] memory finalWeights =
            WhirLinearAlgebra.eqWeightsFlat(vs.foldR, vs.foldIdx - foldingRounds, foldingRounds);
        uint256[] memory finalEvalPoints = _computeEvalPoints(rawFinalIndices, o);
        uint256[] memory openedValues = new uint256[](3 * rawFinalIndices.length);

        if (params.numRounds == 0) {
            // Initial commitment(s): rows are vector-major, weights = tensor(vectorRlc[c*nv..], eqW);
            // split-commit sums the opened rows of every commitment per query (Rust applies the
            // same vector RLC before its final check).
            for (uint256 c = 0; c < params.numCommitments; c++) {
                uint256[] memory w =
                    WhirLinearAlgebra.tensorFlat(vs.vectorRlc, c * params.numVectors, params.numVectors, finalWeights);
                _openRows(ts, hints, o, rawFinalIndices, vs.initialRoots[c], w, openedValues);
            }
        } else {
            _openRows(ts, hints, o, rawFinalIndices, vs.prevRoot, finalWeights, openedValues);
        }

        _requireFinalOpenings(finalVector, finalEvalPoints, openedValues);
    }

    /// @dev Rust WHIR's final round checks every opened row against the explicit final vector:
    ///      Σ_k finalVector[k] * x_i^k == openedValues[i] for every query point x_i (base field).
    ///      Omitting this equality leaves the last commitment disconnected from finalVector.
    function _requireFinalOpenings(uint256[] memory finalVector, uint256[] memory xs, uint256[] memory openedValues)
        private
        pure
    {
        uint256 count = xs.length;
        if (openedValues.length != 3 * count) revert InvalidMleProof();
        bool ok = true;
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let n := div(mload(finalVector), 3)
            let fv := add(finalVector, 0x20)
            let vp := add(openedValues, 0x20)
            let xp := add(xs, 0x20)
            let xEnd := add(xp, shl(5, count))
            for {} lt(xp, xEnd) { xp := add(xp, 0x20) } {
                let x := mload(xp)
                // Horner: result = terms[0] + x*(terms[1] + x*(...))
                let a0 := 0
                let a1 := 0
                let a2 := 0
                for { let k := n } k { k := sub(k, 1) } {
                    let tp := add(fv, mul(sub(k, 1), 0x60))
                    a0 := addmod(mulmod(a0, x, p), mload(tp), p)
                    a1 := addmod(mulmod(a1, x, p), mload(add(tp, 0x20)), p)
                    a2 := addmod(mulmod(a2, x, p), mload(add(tp, 0x40)), p)
                }
                // Field equality (compare modulo p)
                let same :=
                    and(
                        and(eq(a0, mod(mload(vp), p)), eq(a1, mod(mload(add(vp, 0x20)), p))),
                        eq(a2, mod(mload(add(vp, 0x40)), p))
                    )
                ok := and(ok, same)
                vp := add(vp, 0x60)
            }
        }
        if (!ok) revert InvalidMleProof();
    }

    // =====================================================================
    // Phase 6: FinalClaim verification
    // =====================================================================
    function _phaseFinalClaim(WhirParams memory params, VerifyState memory vs, uint256[] memory finalVector)
        private
        pure
    {
        // poly_eval = dot(eq_weights(final_sumcheck_r), finalVector)
        // Use in-place fold: v'[i] = v[2i]*(1-r) + v[2i+1]*r, repeated for each randomness
        uint256 foldStart = vs.foldIdx - params.finalSumcheckRounds;
        GoldilocksExt3.Ext3 memory polyEval = _foldEval(finalVector, vs.foldR, foldStart, params.finalSumcheckRounds);
        if (GoldilocksExt3.isZero(polyEval)) revert InvalidMleProof();

        // linear_form_rlc = theSum / polyEval
        GoldilocksExt3.Ext3 memory linearFormRlc = vs.theSum.mul(GoldilocksExt3.inv(polyEval));

        // Subtract ALL round constraints (matching Rust's round_constraints loop)
        for (uint256 rc = 0; rc < vs.roundConstraints.length; rc++) {
            RoundConstraintEntry memory entry = vs.roundConstraints[rc];
            if (entry.rlcCoeffs.length == 0) continue;
            _subtractRoundConstraints(linearFormRlc, entry, vs.foldR, vs.totalFoldingLen - entry.numVariables);
        }

        // Compute expectedRlc = Σ rlc[i] * eq(point_i, foldingRandomness)
        // For single-point: expectedRlc = rlc[0] * eq(point1, folding)
        // For dual-point:   expectedRlc = rlc[0] * eq(point1, folding) + rlc[1] * eq(point2, folding)
        GoldilocksExt3.Ext3 memory expectedRlc = GoldilocksExt3.zero();
        _addRlcTimesEq(expectedRlc, vs.initialConstraintRlc, 0, params.evaluationPoint, vs.foldR);
        if (vs.numLinearForms != 1) {
            // Multi-point mode: each linear form has its own evaluation point
            _addRlcTimesEq(expectedRlc, vs.initialConstraintRlc, 1, params.evaluationPoint2, vs.foldR);
            // Multi-point linear forms beyond 2 — used by v2 logUp fix
            // (r_gate, r_inv, r_h ⇒ numLinearForms = 3, additional point at index 0).
            for (uint256 i = 2; i < vs.numLinearForms; i++) {
                _addRlcTimesEq(
                    expectedRlc, vs.initialConstraintRlc, i, params.additionalEvaluationPoints[i - 2], vs.foldR
                );
            }
        }

        if (!GoldilocksExt3.eq(linearFormRlc, expectedRlc)) revert InvalidMleProof();
    }

    /// @dev acc += rlc[idx] * eq(point, r)
    function _addRlcTimesEq(
        GoldilocksExt3.Ext3 memory acc,
        uint256[] memory rlc,
        uint256 idx,
        GoldilocksExt3.Ext3[] memory point,
        uint256[] memory r
    ) private pure {
        (uint256 e0, uint256 e1, uint256 e2) = WhirLinearAlgebra.mleEvaluateEqFlat(point, r);
        uint256 c0 = rlc[3 * idx];
        uint256 c1 = rlc[3 * idx + 1];
        uint256 c2 = rlc[3 * idx + 2];
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let m0 := mod(add(mul(c0, e0), shl(1, add(mul(c1, e2), mul(c2, e1)))), p)
            let m1 := mod(add(add(mul(c0, e1), mul(c1, e0)), shl(1, mul(c2, e2))), p)
            let m2 := mod(add(add(mul(c0, e2), mul(c1, e1)), mul(c2, e0)), p)
            mstore(acc, addmod(mload(acc), m0, p))
            mstore(add(acc, 0x20), addmod(mload(add(acc, 0x20)), m1, p))
            mstore(add(acc, 0x40), addmod(mload(add(acc, 0x40)), m2, p))
        }
    }

    /// @dev acc -= Σ_i coeff_i * Π_{k = len-1 .. start} ((1 - r_k) + r_k * x_i^(2^(len-1-k)))
    ///      for every (point x_i, coefficient) of the entry, with r the flat folding randomness
    ///      of length `len` and the pairing in REVERSE order (r[len-1] <-> x^1), exactly like
    ///      `WhirLinearAlgebra.mleEvaluateUnivariateFrom`.
    ///
    ///      (1 - r) + r * X is evaluated as 1 + r * (X - 1). In-domain points are base-field
    ///      elements (x1 = x2 = 0, preserved by squaring), so they take the scalar path.
    function _subtractRoundConstraints(
        GoldilocksExt3.Ext3 memory acc,
        RoundConstraintEntry memory entry,
        uint256[] memory r,
        uint256 start
    ) private pure {
        uint256[] memory coeffs = entry.rlcCoeffs;
        uint256[] memory pts = entry.points;
        if (pts.length != coeffs.length) revert InvalidMleProof();
        uint256 rLow; // address of r[start]
        uint256 rTop; // one past r[len-1]
        assembly ("memory-safe") {
            rLow := add(add(r, 0x20), mul(start, 0x60))
            rTop := add(add(r, 0x20), mul(div(mload(r), 3), 0x60))
        }
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            // Base-field point x: s = prod_{rp from rTop down to rLow} (1 + r*d), d = X - 1, X <- X^2.
            // Term limbs stay lazy (< 2^129); every product sum is far below 2^256.
            function evalBase(x0, rp, rLow_) -> s0, s1, s2 {
                s0 := 1
                for {} gt(rp, rLow_) {} {
                    rp := sub(rp, 0x60)
                    let d := addmod(x0, 0xFFFFFFFF00000000, 0xFFFFFFFF00000001)
                    let t0 := add(1, mul(mload(rp), d))
                    let t1 := mul(mload(add(rp, 0x20)), d)
                    let t2 := mul(mload(add(rp, 0x40)), d)
                    let n0 := mod(add(mul(s0, t0), shl(1, add(mul(s1, t2), mul(s2, t1)))), 0xFFFFFFFF00000001)
                    let n1 := mod(add(add(mul(s0, t1), mul(s1, t0)), shl(1, mul(s2, t2))), 0xFFFFFFFF00000001)
                    s2 := mod(add(add(mul(s0, t2), mul(s1, t1)), mul(s2, t0)), 0xFFFFFFFF00000001)
                    s0 := n0
                    s1 := n1
                    x0 := mulmod(x0, x0, 0xFFFFFFFF00000001)
                }
            }
            // Extension point X: s = prod (1 + r*(X - 1)), X <- X^2, everything on the stack.
            function evalExt(x0, x1, x2, rp, rLow_) -> s0, s1, s2 {
                s0 := 1
                for {} gt(rp, rLow_) {} {
                    rp := sub(rp, 0x60)
                    let t0, t1, t2 :=
                        mul3(
                            mload(rp),
                            mload(add(rp, 0x20)),
                            mload(add(rp, 0x40)),
                            addmod(x0, 0xFFFFFFFF00000000, 0xFFFFFFFF00000001),
                            x1,
                            x2
                        )
                    s0, s1, s2 := mul3(s0, s1, s2, add(t0, 1), t1, t2)
                    x0, x1, x2 := mul3(x0, x1, x2, x0, x1, x2)
                }
            }
            let cp := add(coeffs, 0x20)
            let cEnd := add(cp, shl(5, mload(coeffs)))
            let pp := add(pts, 0x20)
            for {} lt(cp, cEnd) {} {
                // Running product kept in temporary memory after the free pointer (not retained).
                let tmp := mload(0x40)
                let s0 := 0
                let s1 := 0
                let s2 := 0
                switch or(mload(add(pp, 0x20)), mload(add(pp, 0x40)))
                case 0 { s0, s1, s2 := evalBase(mload(pp), rTop, rLow) }
                default { s0, s1, s2 := evalExt(mload(pp), mload(add(pp, 0x20)), mload(add(pp, 0x40)), rTop, rLow) }
                mstore(tmp, s0)
                mstore(add(tmp, 0x20), s1)
                mstore(add(tmp, 0x40), s2)
                pp := add(pp, 0x60)
                // acc -= s * coeff
                let m0, m1, m2 :=
                    mul3(
                        mload(tmp),
                        mload(add(tmp, 0x20)),
                        mload(add(tmp, 0x40)),
                        mload(cp),
                        mload(add(cp, 0x20)),
                        mload(add(cp, 0x40))
                    )
                cp := add(cp, 0x60)
                mstore(acc, addmod(mload(acc), sub(0xFFFFFFFF00000001, m0), 0xFFFFFFFF00000001))
                mstore(add(acc, 0x20), addmod(mload(add(acc, 0x20)), sub(0xFFFFFFFF00000001, m1), 0xFFFFFFFF00000001))
                mstore(add(acc, 0x40), addmod(mload(add(acc, 0x40)), sub(0xFFFFFFFF00000001, m2), 0xFFFFFFFF00000001))
            }
        }
    }

    // =====================================================================
    // Helpers
    // =====================================================================

    function _challengeIndices(SpongefishWhir.TranscriptState memory ts, uint256 numLeaves, uint256 count)
        internal
        pure
        returns (uint256[] memory indices)
    {
        if (count == 0) return new uint256[](0);
        if (numLeaves == 1) {
            indices = new uint256[](1);
            return indices;
        }

        // `_validateDomain` has already established that every codeword length
        // is a nonzero power of two, so this mask samples uniformly.
        uint256 mask = numLeaves - 1; // safe bitmask for power-of-2

        uint256 sizeBytes = _ceilDiv(_log2(numLeaves), 8);
        uint256 totalBytes = count * sizeBytes;
        indices = new uint256[](count);
        uint256 counter = uint256(ts.sponge.squeezeCounter);
        if (totalBytes > type(uint64).max - counter) revert InvalidMleProof();
        bytes32 spongeState = ts.sponge.state;
        uint256 nextCounter;
        assembly ("memory-safe") {
            // One Rust `verifier_message::<u8>()` hashes state || "squeeze" || counter_be
            // (state already at 0x00) and consumes its first byte; `n` bytes form one query.
            function squeezeIndex(ctr, n) -> value, next {
                next := ctr
                for {} n { n := sub(n, 1) } {
                    mstore(0x20, or(shl(200, 0x73717565657a65), shl(136, next)))
                    value := or(shl(8, value), shr(248, keccak256(0x00, 47)))
                    next := add(next, 1)
                }
            }
            // Rust's `challenge_indices(..., deduplicate=true)` sorts and compacts before any
            // row is serialized: insertion sort (count is small) followed by in-place dedup.
            function sortDedup(out, n) -> write {
                let end := add(out, shl(5, n))
                for { let q := add(out, 0x20) } lt(q, end) { q := add(q, 0x20) } {
                    let v := mload(q)
                    let r := q
                    for {} gt(r, out) {} {
                        let prev := mload(sub(r, 0x20))
                        if iszero(gt(prev, v)) { break }
                        mstore(r, prev)
                        r := sub(r, 0x20)
                    }
                    mstore(r, v)
                }
                // Compact equal neighbours in place; out[0] always stays (n >= 1 here).
                let w := add(out, 0x20)
                for { let q := add(out, 0x20) } lt(q, end) { q := add(q, 0x20) } {
                    let cur := mload(q)
                    if iszero(eq(cur, mload(sub(w, 0x20)))) {
                        mstore(w, cur)
                        w := add(w, 0x20)
                    }
                }
                write := shr(5, sub(w, out))
            }
            let out := add(indices, 0x20)
            nextCounter := counter
            mstore(0x00, spongeState)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let value := 0
                value, nextCounter := squeezeIndex(nextCounter, sizeBytes)
                mstore(add(out, shl(5, i)), and(value, mask))
            }
            mstore(indices, sortDedup(out, count))
        }
        ts.sponge.squeezeCounter = uint64(nextCounter);
    }

    /// @dev theSum += Σ_i a[i] * rlc[rlcOffset + i] over flat vectors.
    function _mulAddFlat(
        GoldilocksExt3.Ext3 memory s,
        uint256[] memory a,
        uint256[] memory rlc,
        uint256 rlcOffset,
        uint256 count
    ) private pure {
        if (a.length < 3 * count || rlc.length < 3 * (rlcOffset + count)) revert InvalidMleProof();
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let p := 0xFFFFFFFF00000001
            let ap := add(a, 0x20)
            let aEnd := add(ap, mul(count, 0x60))
            let cp := add(add(rlc, 0x20), mul(rlcOffset, 0x60))
            let s0 := mload(s)
            let s1 := mload(add(s, 0x20))
            let s2 := mload(add(s, 0x40))
            for {} lt(ap, aEnd) {} {
                let m0, m1, m2 :=
                    mul3(
                        mload(ap),
                        mload(add(ap, 0x20)),
                        mload(add(ap, 0x40)),
                        mload(cp),
                        mload(add(cp, 0x20)),
                        mload(add(cp, 0x40))
                    )
                ap := add(ap, 0x60)
                cp := add(cp, 0x60)
                s0 := addmod(s0, m0, p)
                s1 := addmod(s1, m1, p)
                s2 := addmod(s2, m2, p)
            }
            mstore(s, s0)
            mstore(add(s, 0x20), s1)
            mstore(add(s, 0x40), s2)
        }
    }

    /// @dev keccak256 of `count` consecutive rows of `rowBytes` bytes starting at `start` in hints.
    function _hashRows(SpongefishMerkle.CalldataBytes memory hints, uint256 start, uint256 rowBytes, uint256 count)
        private
        pure
        returns (bytes32[] memory hashes)
    {
        if (start > hints.length || count * rowBytes > hints.length - start) revert InvalidMleProof();
        hashes = new bytes32[](count);
        assembly ("memory-safe") {
            // KECCAK256 only reads memory. Use ephemeral free-memory scratch;
            // no Solidity allocation can occur between the copy and hash.
            let scratch := mload(0x40)
            let src := add(mload(hints), start)
            let dst := add(hashes, 0x20)
            let dEnd := add(dst, shl(5, count))
            for {} lt(dst, dEnd) { dst := add(dst, 0x20) } {
                calldatacopy(scratch, src, rowBytes)
                mstore(dst, keccak256(scratch, rowBytes))
                src := add(src, rowBytes)
            }
        }
    }

    /// @dev Read a u64 LE from a bytes buffer at a given offset (zero-copy).
    ///      Uses efficient byte-swap: load BE word, extract top 8 bytes, reverse.
    function _readU64LEAt(SpongefishMerkle.CalldataBytes memory buf, uint256 baseOff)
        private
        pure
        returns (uint64 val)
    {
        assembly ("memory-safe") {
            let w := shr(192, calldataload(add(mload(buf), baseOff))) // top 8 bytes as BE u64

            // Byte-swap 64-bit BE → LE using parallel swap
            // Swap bytes in pairs of 1, then 2, then 4
            w := or(and(shr(8, w), 0x00FF00FF00FF00FF), and(shl(8, w), 0xFF00FF00FF00FF00))
            w := or(and(shr(16, w), 0x0000FFFF0000FFFF), and(shl(16, w), 0xFFFF0000FFFF0000))
            w := or(shr(32, w), shl(32, w))
            val := and(w, 0xFFFFFFFFFFFFFFFF)
        }
    }

    /// @dev Consume Arkworks' compressed Vec length and bind the serialized shape to the
    ///      transcript-derived query count. Blindly skipping this prefix accepts encodings the
    ///      pinned Rust verifier rejects and can shift all later Merkle hints.
    function _consumeVecPrefix(
        SpongefishWhir.TranscriptState memory ts,
        SpongefishMerkle.CalldataBytes memory hints,
        uint256 expectedElements
    ) private pure {
        if (ts.hintPos > hints.length || hints.length - ts.hintPos < 8) {
            revert InvalidMleProof();
        }
        if (uint256(_readU64LEAt(hints, ts.hintPos)) != expectedElements) revert InvalidMleProof();
        ts.hintPos += 8;
    }

    /// @dev In-domain evaluation points: x_i = domainGen^(row_i + col_i * numCosets) with
    ///      row_i = idx_i / cosetSize and col_i = idx_i % cosetSize, as base-field words.
    ///      Uses the table g^(2^k): every exponent is < codewordLength = 2^merkleDepth
    ///      (idx < codewordLength by construction, cosetSize * numCosets == codewordLength).
    function _computeEvalPoints(uint256[] memory rawIndices, OpenParams memory o)
        private
        pure
        returns (uint256[] memory pts)
    {
        uint256 count = rawIndices.length;
        pts = new uint256[](count);
        uint256 depth = o.md;
        uint256 cosetSize = o.cosetSize;
        uint256 numCosets = o.numCosets;
        uint64 gen = o.domainGen;
        if (cosetSize == 0) revert InvalidMleProof();
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            // Temporary nibble table after the free memory pointer (not retained):
            // group j (15 words at table + j*0x1e0) holds gen^(m * 16^j) for m = 1..15, for every
            // nibble position j of an exponent below 2^depth.
            let table := mload(0x40)
            let g := and(gen, 0xFFFFFFFFFFFFFFFF)
            for {
                let t := table
                let tEnd := add(table, mul(shr(2, add(depth, 3)), 0x1e0))
            } lt(t, tEnd) {} {
                let acc := g
                for { let m := 0 } lt(m, 15) { m := add(m, 1) } {
                    mstore(t, acc)
                    acc := mulmod(acc, g, p)
                    t := add(t, 0x20)
                }
                // acc = g^16 is the base of the next nibble position
                g := acc
            }
            // gen^e from the nibble table: one mulmod per nonzero nibble of e.
            function pow(e, t) -> result {
                result := 1
                for {} e { t := add(t, 0x1e0) } {
                    let m := and(e, 15)
                    if m { result := mulmod(result, mload(add(t, shl(5, sub(m, 1)))), 0xFFFFFFFF00000001) }
                    e := shr(4, e)
                }
            }
            let src := add(rawIndices, 0x20)
            let dst := add(pts, 0x20)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let idx := mload(add(src, shl(5, i)))
                mstore(add(dst, shl(5, i)), pow(add(div(idx, cosetSize), mul(mod(idx, cosetSize), numCosets)), table))
            }
        }
    }

    /// @dev For every row i: rowValues[i] += dot(w, row_i), where row_i is the `numCols`-column
    ///      hint row at `rowsStart + i * rowBytes` (base field: 8-byte LE limbs; extension: three
    ///      8-byte LE limbs per column). Every limb is decoded once and checked canonical.
    ///      `w` is a flat Ext3 vector with at least `numCols` entries.
    function _accumulateRowDots(
        uint256[] memory rowValues,
        uint256[] memory w,
        uint256 numCols,
        SpongefishMerkle.CalldataBytes memory hints,
        uint256 rowsStart,
        uint256 rowBytes,
        uint256 count,
        bool isBaseField
    ) private pure {
        uint256 limbsPerCol = isBaseField ? 1 : 3;
        // The descriptor bounds the exact hints byte slice. Never allow calldataload to reach
        // a later ABI argument: every decoded limb lies inside [rowsStart, rowsStart + count*rowBytes).
        if (
            rowsStart > hints.length || count * rowBytes > hints.length - rowsStart
                || numCols * limbsPerCol * 8 > rowBytes || w.length < 3 * numCols || rowValues.length < 3 * count
        ) revert InvalidMleProof();
        assembly ("memory-safe") {
            // Hot loops are Yul functions with few arguments so that only their own locals are
            // reachable on the EVM stack; limb decoding and accumulation are fused per calldata
            // word (four LE u64 limbs). Products are lazily reduced: every weight and limb is
            // < 2^64, so the 256-bit sums of products cannot wrap before the final mod.

            // Reverse the bytes inside every 64-bit lane of a word (four LE u64 limbs at once).
            function lanes(x) -> y {
                y := or(
                    and(shr(8, x), 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF),
                    and(shl(8, x), 0xFF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00)
                )
                y := or(
                    and(shr(16, y), 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF),
                    and(shl(16, y), 0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000)
                )
                y := or(
                    and(shr(32, y), 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF),
                    and(shl(32, y), 0xFFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000)
                )
            }
            // Nonzero iff some 64-bit lane of a lane-swapped word is >= p. Arkworks
            // CanonicalDeserialize rejects raw >= p: the Merkle tree commits the raw bytes, so
            // reducing a non-canonical encoding here would otherwise give the same field oracle
            // multiple Fiat-Shamir commitment roots.
            function badLanes(y) -> b {
                b := or(
                    or(
                        gt(shr(192, y), 0xFFFFFFFF00000000),
                        gt(and(shr(128, y), 0xFFFFFFFFFFFFFFFF), 0xFFFFFFFF00000000)
                    ),
                    or(
                        gt(and(shr(64, y), 0xFFFFFFFFFFFFFFFF), 0xFFFFFFFF00000000),
                        gt(and(y, 0xFFFFFFFFFFFFFFFF), 0xFFFFFFFF00000000)
                    )
                )
            }
            // r += w[wp] * b for one base-field limb b.
            function accBase(r0, r1, r2, wp, b) -> n0, n1, n2 {
                n0 := add(r0, mul(mload(wp), b))
                n1 := add(r1, mul(mload(add(wp, 0x20)), b))
                n2 := add(r2, mul(mload(add(wp, 0x40)), b))
            }
            // acc[0..3) += w[wp] * (b0, b1, b2) (Ext3 product), accumulators in memory.
            function accExt(acc, wp, b0, b1, b2) {
                // c0 = w0*b0 + 2*(w1*b2 + w2*b1)
                mstore(
                    acc,
                    add(
                        mload(acc),
                        add(
                            mul(mload(wp), b0),
                            shl(1, add(mul(mload(add(wp, 0x20)), b2), mul(mload(add(wp, 0x40)), b1)))
                        )
                    )
                )
                // c1 = w0*b1 + w1*b0 + 2*w2*b2
                mstore(
                    add(acc, 0x20),
                    add(
                        mload(add(acc, 0x20)),
                        add(
                            add(mul(mload(wp), b1), mul(mload(add(wp, 0x20)), b0)),
                            shl(1, mul(mload(add(wp, 0x40)), b2))
                        )
                    )
                )
                // c2 = w0*b2 + w1*b1 + w2*b0
                mstore(
                    add(acc, 0x40),
                    add(
                        mload(add(acc, 0x40)),
                        add(add(mul(mload(wp), b2), mul(mload(add(wp, 0x20)), b1)), mul(mload(add(wp, 0x40)), b0))
                    )
                )
            }
            // dot(w, row) for a base-field row of numCols 8-byte limbs at calldata cd.
            function dotBaseRow(cd, cols, wp) -> r0, r1, r2, bad {
                for { let end := add(wp, mul(and(cols, not(3)), 0x60)) } lt(wp, end) { wp := add(wp, 0x180) } {
                    let y := lanes(calldataload(cd))
                    cd := add(cd, 32)
                    bad := or(bad, badLanes(y))
                    r0, r1, r2 := accBase(r0, r1, r2, wp, shr(192, y))
                    r0, r1, r2 := accBase(r0, r1, r2, add(wp, 0x60), and(shr(128, y), 0xFFFFFFFFFFFFFFFF))
                    r0, r1, r2 := accBase(r0, r1, r2, add(wp, 0xc0), and(shr(64, y), 0xFFFFFFFFFFFFFFFF))
                    r0, r1, r2 := accBase(r0, r1, r2, add(wp, 0x120), and(y, 0xFFFFFFFFFFFFFFFF))
                }
                // 0..3 trailing columns, one limb at a time
                for { let n := and(cols, 3) } n { n := sub(n, 1) } {
                    let b := shr(192, lanes(calldataload(cd)))
                    cd := add(cd, 8)
                    bad := or(bad, gt(b, 0xFFFFFFFF00000000))
                    r0, r1, r2 := accBase(r0, r1, r2, wp, b)
                    wp := add(wp, 0x60)
                }
            }
            // dot(w, row) for an extension row of numCols columns of three 8-byte limbs each;
            // the accumulators live at acc (three words).
            function dotExtRow(cd, cols, wp, acc) -> bad {
                // four columns = twelve limbs = three calldata words
                for { let end := add(wp, mul(and(cols, not(3)), 0x60)) } lt(wp, end) { wp := add(wp, 0x180) } {
                    let y0 := lanes(calldataload(cd))
                    let y1 := lanes(calldataload(add(cd, 32)))
                    bad := or(bad, or(badLanes(y0), badLanes(y1)))
                    accExt(
                        acc,
                        wp,
                        shr(192, y0),
                        and(shr(128, y0), 0xFFFFFFFFFFFFFFFF),
                        and(shr(64, y0), 0xFFFFFFFFFFFFFFFF)
                    )
                    accExt(
                        acc,
                        add(wp, 0x60),
                        and(y0, 0xFFFFFFFFFFFFFFFF),
                        shr(192, y1),
                        and(shr(128, y1), 0xFFFFFFFFFFFFFFFF)
                    )
                    y0 := lanes(calldataload(add(cd, 64)))
                    cd := add(cd, 96)
                    bad := or(bad, badLanes(y0))
                    accExt(
                        acc,
                        add(wp, 0xc0),
                        and(shr(64, y1), 0xFFFFFFFFFFFFFFFF),
                        and(y1, 0xFFFFFFFFFFFFFFFF),
                        shr(192, y0)
                    )
                    accExt(
                        acc,
                        add(wp, 0x120),
                        and(shr(128, y0), 0xFFFFFFFFFFFFFFFF),
                        and(shr(64, y0), 0xFFFFFFFFFFFFFFFF),
                        and(y0, 0xFFFFFFFFFFFFFFFF)
                    )
                }
                // 0..3 trailing columns, one limb at a time
                for { let n := and(cols, 3) } n { n := sub(n, 1) } {
                    let b0 := shr(192, lanes(calldataload(cd)))
                    let b1 := shr(192, lanes(calldataload(add(cd, 8))))
                    let b2 := shr(192, lanes(calldataload(add(cd, 16))))
                    cd := add(cd, 24)
                    bad := or(
                        bad,
                        or(or(gt(b0, 0xFFFFFFFF00000000), gt(b1, 0xFFFFFFFF00000000)), gt(b2, 0xFFFFFFFF00000000))
                    )
                    accExt(acc, wp, b0, b1, b2)
                    wp := add(wp, 0x60)
                }
            }
            let p := 0xFFFFFFFF00000001
            // Extension accumulators live in temporary memory after the free pointer (not retained).
            let acc := mload(0x40)
            let src := add(mload(hints), rowsStart)
            let vEnd := add(add(rowValues, 0x20), mul(count, 0x60))
            for { let vp := add(rowValues, 0x20) } lt(vp, vEnd) { vp := add(vp, 0x60) } {
                let r0 := 0
                let r1 := 0
                let r2 := 0
                let bad := 0
                switch isBaseField
                case 1 { r0, r1, r2, bad := dotBaseRow(src, numCols, add(w, 0x20)) }
                default {
                    mstore(acc, 0)
                    mstore(add(acc, 0x20), 0)
                    mstore(add(acc, 0x40), 0)
                    bad := dotExtRow(src, numCols, add(w, 0x20), acc)
                    r0 := mload(acc)
                    r1 := mload(add(acc, 0x20))
                    r2 := mload(add(acc, 0x40))
                }
                if bad {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                src := add(src, rowBytes)
                mstore(vp, addmod(mload(vp), mod(r0, p), p))
                mstore(add(vp, 0x20), addmod(mload(add(vp, 0x20)), mod(r1, p), p))
                mstore(add(vp, 0x40), addmod(mload(add(vp, 0x40)), mod(r2, p), p))
            }
        }
    }

    /// @dev Compute dot(eqW, row) by reading row fields directly from hints (no row alloc).
    ///      Reads the first `numCols` element pointers of `eqW` (the hint slice is bounds
    ///      checked exactly as before) and evaluates through `_accumulateRowDots`.
    function _dotEqWithRow(
        GoldilocksExt3.Ext3[] memory eqW,
        SpongefishMerkle.CalldataBytes memory hints,
        uint256 rowOff,
        uint256 numCols,
        bool isBaseField
    ) internal pure returns (GoldilocksExt3.Ext3 memory acc) {
        uint256 elementBytes = isBaseField ? 8 : 24;
        if (rowOff > hints.length || numCols > (hints.length - rowOff) / elementBytes) {
            revert InvalidMleProof();
        }
        uint256[] memory w = new uint256[](3 * numCols);
        assembly ("memory-safe") {
            let eqPtr := add(eqW, 0x20) // pointer to first element pointer
            let wp := add(w, 0x20)
            for { let j := 0 } lt(j, numCols) { j := add(j, 1) } {
                let eqElem := mload(add(eqPtr, shl(5, j)))
                mstore(wp, mload(eqElem))
                mstore(add(wp, 0x20), mload(add(eqElem, 0x20)))
                mstore(add(wp, 0x40), mload(add(eqElem, 0x40)))
                wp := add(wp, 0x60)
            }
        }
        uint256[] memory value = new uint256[](3);
        _accumulateRowDots(value, w, numCols, hints, rowOff, numCols * elementBytes, 1, isBaseField);
        acc.c0 = uint64(value[0]);
        acc.c1 = uint64(value[1]);
        acc.c2 = uint64(value[2]);
    }

    /// @dev Evaluate dot(eq_weights(r), vector) by in-place folding (no eqWeights alloc).
    ///      Fold in REVERSE order: last randomness first (matching eqWeights bit convention).
    ///      Mutates `vec` (flat) in place.
    function _foldEval(uint256[] memory vec, uint256[] memory r, uint256 rStart, uint256 numRounds)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory result)
    {
        if (rStart > r.length / 3 || numRounds > r.length / 3 - rStart) revert InvalidMleProof();
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let p := 0xFFFFFFFF00000001
            let size := div(mload(vec), 3)
            let vData := add(vec, 0x20)
            let rData := add(r, 0x20)

            for { let round := numRounds } round { round := sub(round, 1) } {
                let rp := add(rData, mul(add(rStart, sub(round, 1)), 0x60))
                let rr0 := mload(rp)
                let rr1 := mload(add(rp, 0x20))
                let rr2 := mload(add(rp, 0x40))
                // oneMinusR
                let omr0 := addmod(1, sub(p, rr0), p)
                let omr1 := sub(p, rr1)
                let omr2 := sub(p, rr2)

                let half := shr(1, size)
                for { let i := 0 } lt(i, half) { i := add(i, 1) } {
                    let ep := add(vData, mul(i, 0xc0)) // even = vec[2i], odd = vec[2i+1]
                    let e0, e1, e2 := mul3(mload(ep), mload(add(ep, 0x20)), mload(add(ep, 0x40)), omr0, omr1, omr2)
                    let o0, o1, o2 :=
                        mul3(mload(add(ep, 0x60)), mload(add(ep, 0x80)), mload(add(ep, 0xa0)), rr0, rr1, rr2)
                    let dp := add(vData, mul(i, 0x60))
                    mstore(dp, addmod(e0, o0, p))
                    mstore(add(dp, 0x20), addmod(e1, o1, p))
                    mstore(add(dp, 0x40), addmod(e2, o2, p))
                }
                size := half
            }

            // result = vec[0]
            mstore(result, mload(vData))
            mstore(add(result, 0x20), mload(add(vData, 0x20)))
            mstore(add(result, 0x40), mload(add(vData, 0x40)))
        }
    }

    function _ceilDiv(uint256 a, uint256 b) private pure returns (uint256) {
        return (a + b - 1) / b;
    }

    function _log2(uint256 x) private pure returns (uint256 n) {
        while (x > 1) {
            x >>= 1;
            n++;
        }
    }
}
