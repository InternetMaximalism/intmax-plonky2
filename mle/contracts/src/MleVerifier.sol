// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {GoldilocksField as F} from "./GoldilocksField.sol";
import {TranscriptLib} from "./TranscriptLib.sol";
import {SumcheckVerifier} from "./SumcheckVerifier.sol";
import {EqPolyLib} from "./EqPolyLib.sol";
import {SpongefishWhirVerify} from "./spongefish/SpongefishWhirVerify.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {Plonky2GateEvaluator} from "./Plonky2GateEvaluator.sol";
import {PoseidonPublicInputsHash} from "./PoseidonPublicInputsHash.sol";
import {PackedClaimLib} from "./PackedClaimLib.sol";
import {InvalidMleProof, InvalidMleVerifierChainId, MleProofEngineUnavailable} from "./MleProofErrors.sol";
import {
    EXTENSION_FIELD_LIMBS,
    GROUP_AUXILIARY,
    GROUP_INVERSE_HELPERS,
    GROUP_PREPROCESSED,
    GROUP_WITNESS,
    MLE_PROTOCOL_VERSION,
    NUM_PACKED_VECTORS_PER_GROUP,
    NUM_PCS_CLAIMS,
    NUM_PCS_GROUPS,
    NUM_PCS_TERMINAL_POINTS,
    PACKED_BOUND_CLAIM_MASK,
    PACKED_PCS_SCHEMA_DOMAIN,
    PACKED_VARIABLE_ORDER_CODE,
    POINT_COMBINED,
    POINT_GATE,
    POINT_H,
    POINT_INVERSE
} from "./generated/MleWhirV1.sol";

/// @title MleVerifier — abstract legacy conformance implementation
/// @notice Every terminal constituent is opened directly from an ordered
/// commitment made before its aggregation/query challenges. The immutable
/// chain pin remains as release containment pending independent review.
/// @dev This legacy protocol is not a production fallback. Keep the checked
/// implementation abstract so it has no deployable artifact; only test-local
/// harnesses may instantiate it. Production integrations use the wire-v3
/// MleVerifierV2/PinnedMleVerifierV2 entry points.
abstract contract MleVerifier {
    using F for uint256;
    uint256 constant P = 0xFFFFFFFF00000001;

    /// @notice The only chain on which this verifier may execute.
    /// @dev Immutable by design: a setter would let an already-populated
    ///      verifier deployment become usable after a cross-chain state/code
    ///      migration. The constructor also requires this value to equal the
    ///      deployment chain so a wrong-network deployment fails atomically.
    uint256 public immutable allowedChainId;

    // Encoded-proof verdicts consumed by IntmaxRollup.  Keep 0..3 aligned
    // with the rollup's existing typed-verifier tri-state; PI_MISMATCH is a
    // failed accusation precondition, never proof fraud.
    uint8 internal constant ENCODED_INVALID = 0;
    uint8 internal constant ENCODED_VALID = 1;
    uint8 internal constant ENCODED_UNEVALUABLE = 2;
    uint8 internal constant ENCODED_STARVED = 3;
    uint8 internal constant ENCODED_PI_MISMATCH = 4;

    /// @dev Deployment and execution are both guarded.  The runtime check is
    /// still required because code can be installed by genesis configuration,
    /// state migration, or test cheatcodes without running this initcode.
    constructor(uint256 allowedChainId_) {
        if (allowedChainId_ == 0 || block.chainid != allowedChainId_) {
            revert InvalidMleVerifierChainId(allowedChainId_, block.chainid);
        }
        allowedChainId = allowedChainId_;
    }

    struct MleProof {
        uint256 protocolVersion;
        uint256 constituentWidth;
        uint256[] circuitDigest;
        bytes whirTranscript;
        bytes whirHints;
        bytes32 preprocessedRoot;
        bytes32 witnessRoot;
        bytes32 auxCommitmentRoot;
        uint256 preprocessedEvalValue;
        uint256 preprocessedBatchR;
        uint256[] preprocessedIndividualEvals;
        uint256 witnessEvalValue;
        uint256 witnessBatchR;
        uint256[] witnessIndividualEvals;
        uint256 auxBatchR;
        uint256 auxConstraintEval;
        uint256 auxPermEval;
        uint256 auxEvalValue;
        SumcheckVerifier.SumcheckProof combinedProof;
        uint256[] publicInputs;
        uint256 alpha;
        uint256 beta;
        uint256 gamma;
        uint256 mu;
        // SECURITY note (Issue #5): tau and tauPerm are NOT carried
        // in the proof struct — they are deterministically re-derived from the
        // transcript inside verify(). Including a prover-supplied tau would be a
        // dead field at best and a footgun (an unchecked field used as if authoritative).
        //
        // ── v2 logUp soundness fix (Issue R2-#2, paper §4.2) ────────────
        // Inverse helpers A_j(b) = 1/D_j^id(b), B_j(b) = 1/D_j^σ(b) committed
        // as the third ordered packed group in the grouped WHIR session.
        // Bound by Φ_inv (zero-check) and Φ_h (linear sumcheck), both of
        // which produce their own terminal points r_inv, r_h.
        bytes32 inverseHelpersCommitmentRoot;
        uint256 inverseHelpersBatchR;
        SumcheckVerifier.SumcheckProof invSumcheckProof;
        SumcheckVerifier.SumcheckProof hSumcheckProof;
        uint256 lambdaInv;
        uint256 muInv;
        // Goldilocks individual evals at r_inv:
        // - witnessIndividualEvalsAtRInv  : length = numWires
        // - preprocessedIndividualEvalsAtRInv : length = numConstants + numRoutedWires,
        //                                        layout [const_0..const_C, sigma_0..sigma_R].
        //                                        Sigma subset feeds Φ_inv terminal;
        //                                        const subset only enters batch consistency.
        // - inverseHelpersEvalsAtRInv     : length = 2 · numRoutedWires
        //                                   layout [a_0, …, a_{R-1}, b_0, …, b_{R-1}]
        uint256[] witnessIndividualEvalsAtRInv;
        uint256[] preprocessedIndividualEvalsAtRInv;
        uint256[] inverseHelpersEvalsAtRInv;
        // Inverse-helpers individual evals at r_h (same layout as above)
        uint256[] inverseHelpersEvalsAtRH;
        // Verifier-recomputable g_sub(r_inv) — enclosed in proof for a hard
        // cross-check against subgroupGenPowers.
        uint256 gSubEvalAtRInv;
        // Batched Goldilocks evals at r_inv (for batch consistency vs WHIR)
        uint256 witnessEvalValueAtRInv;
        uint256 preprocessedEvalValueAtRInv;
        // ── v2 gate binding fix (Issue R2-#1, paper §7.3) ─────────────
        // Additional sumcheck Φ_gate whose terminal check runs the actual
        // Plonky2 gate-constraint formula at a random point r_gate_v2,
        // closing the MLE-commutativity gap for gates of degree ≥ 2.
        uint256 extChallenge;
        SumcheckVerifier.SumcheckProof gateSumcheckProof;
        // Individual evals at r_gate_v2 (PCS-bound via WHIR 4th point):
        //  - witnessIndividualEvalsAtRGateV2  : length = numWires
        //  - preprocessedIndividualEvalsAtRGateV2 : length = numConstants + numRoutedWires
        uint256[] witnessIndividualEvalsAtRGateV2;
        uint256[] preprocessedIndividualEvalsAtRGateV2;
        uint256 witnessEvalValueAtRGateV2;
        uint256 preprocessedEvalValueAtRGateV2;
        // Circuit metadata needed by Plonky2GateEvaluator.
        uint256 quotientDegreeFactor;
        uint256 numSelectors;
        uint256 numGateConstraints;
        Plonky2GateEvaluator.GateInfo[] gates;
        uint256[4] publicInputsHash;
    }

    /// @dev Wrap call args into a struct to drastically reduce stack pressure.
    /// Without this, verify() crosses Solc's 16-slot stack limit even with
    /// via_ir + heavy helper extraction (Yul optimizer issue with calldata-derived
    /// memory pointers).
    struct VerifyParams {
        uint256 degreeBits;
        bytes32 preprocessedCommitmentRoot;
        uint256 numConstants;
        uint256 numRoutedWires;
        bytes protocolId;
        bytes sessionId;
        // Issue #2: VK-bound permutation context. These determine the identity
        // permutation MLE id_col(b) = k_is[col] · subgroup[b], whose evaluation at
        // the sumcheck point r is needed to verify h̃(r) is actually the logUp
        // permutation numerator and not an arbitrary polynomial summing to 0.
        // SECURITY: kIs and subgroupGenPowers MUST be the values consistent with
        // the circuit's VK (caller-supplied; they are not transcript-bound here
        // because they are public per-circuit constants).
        uint256[] kIs; // length = numRoutedWires
        uint256[] subgroupGenPowers; // length = degreeBits, [g, g^2, g^4, ..., g^{2^(n-1)}]
    }

    struct TerminalPoints {
        uint256[] combined;
        uint256[] inverse;
        uint256[] h;
        uint256[] gate;
    }

    /// @dev Version byte for the gatesDigest encoding. Bump when the
    /// GateInfo struct layout or the list of hashed fields changes.
    uint8 internal constant GATES_DIGEST_VERSION = 2;

    // NOTE on `gatesDigest`:
    // The VK-bound digest that pins gate-layout metadata was intentionally
    // added as a standalone verify() parameter rather than a field of
    // VerifyParams. Growing the struct triggers a Yul-optimizer stack-too-deep
    // failure in this already-tight function; an external parameter is
    // API-cleaner and keeps the Yul layout stable.
    // Digest formula (MUST match the off-chain deployer):
    //   keccak256(abi.encode(
    //       uint8(GATES_DIGEST_VERSION),
    //       proof.circuitDigest,
    //       proof.publicInputs.length,
    //       proof.witnessIndividualEvalsAtRGateV2.length,   // numWires
    //       proof.numSelectors,
    //       proof.numGateConstraints,
    //       proof.quotientDegreeFactor,
    //       proof.gates                                     // Plonky2GateEvaluator.GateInfo[]
    //   ))

    /// @notice Verify a versioned, VK-bound MLE/WHIR proof on the
    /// constructor-selected chain.
    /// @dev The chain guard MUST be the first branch. In particular, malformed
    /// proof data after a chain-id migration must not be classified as
    /// `InvalidMleProof` while the verifier is unavailable on that chain.
    function verify(
        MleProof calldata proof,
        VerifyParams memory vp,
        SpongefishWhirVerify.WhirParams memory whirParams,
        bytes32 gatesDigest
    ) external view returns (bool) {
        if (block.chainid != allowedChainId) {
            revert MleProofEngineUnavailable(block.chainid);
        }
        // The four packed evaluation points are derived below from the
        // authenticated sumcheck transcript. Caller-supplied point arrays
        // would otherwise be silently overwritten, leaving non-canonical
        // verifier configurations with ignored tails. This is configuration
        // invalidity (UNEVALUABLE in the fraud path), not proof fraud.
        require(
            whirParams.evaluationPoint.length == 0 && whirParams.evaluationPoint2.length == 0
                && whirParams.additionalEvaluationPoints.length == 0,
            "WHIR derived point config"
        );
        _requireValidVkInputs(vp);
        _requireGatesDigest(proof, gatesDigest);
        _requireCanonicalProofInputs(proof);
        _requireCanonicalSumchecks(proof);
        if (proof.protocolVersion != MLE_PROTOCOL_VERSION) revert InvalidMleProof();
        if (!_canonicalScalars(proof)) revert InvalidMleProof();
        uint256 numWires = proof.witnessIndividualEvalsAtRGateV2.length;
        uint256 preLen = vp.numConstants + vp.numRoutedWires;
        uint256 inverseLen = 2 * vp.numRoutedWires;
        uint256 expectedWidth = preLen;
        if (numWires > expectedWidth) expectedWidth = numWires;
        if (inverseLen > expectedWidth) expectedWidth = inverseLen;
        if (expectedWidth < 2) expectedWidth = 2;
        if (proof.constituentWidth != expectedWidth) revert InvalidMleProof();
        // These values belong to the caller's stored VK/configuration. A stale
        // deployment is UNEVALUABLE, never authenticated proof fraud.
        require(whirParams.numCommitments == NUM_PCS_GROUPS, "WHIR commitment config");
        require(whirParams.numVectors == NUM_PACKED_VECTORS_PER_GROUP, "WHIR vector config");
        require(
            whirParams.numVariables == vp.degreeBits + _constituentIndexBits(expectedWidth),
            "WHIR packed variable config"
        );
        // Unlike the witness width, the preprocessed width is not part of
        // `gatesDigest`: it is fixed by the VK (`numConstants +
        // numRoutedWires`).  Validate it before `Plonky2GateEvaluator`
        // indexes selector/constant entries.  Otherwise a prover can submit
        // an empty/short array and turn an invalid proof into Panic(0x32),
        // which the rollup correctly classifies as verifier-unevaluable
        // rather than fraud.
        if (
            proof.preprocessedIndividualEvals.length != preLen
                || proof.preprocessedIndividualEvalsAtRInv.length != preLen
                || proof.preprocessedIndividualEvalsAtRGateV2.length != preLen
                || proof.witnessIndividualEvals.length != numWires
                || proof.witnessIndividualEvalsAtRInv.length != numWires
                || proof.inverseHelpersEvalsAtRInv.length != inverseLen
                || proof.inverseHelpersEvalsAtRH.length != inverseLen
        ) {
            revert InvalidMleProof();
        }
        return _verifyCore(proof, vp, whirParams);
    }

    /// @notice Classify an authenticated raw proof encoding for the rollup fraud path.
    /// @dev The caller MUST authenticate `rawProof` against the submission's blob commitment
    /// before consuming an INVALID result.  This function deliberately separates:
    ///   - malformed/non-canonical ABI or InvalidMleProof(): INVALID;
    ///   - a public-input preimage mismatch: PI_MISMATCH (failed accusation);
    ///   - verifier/config/unknown failures: UNEVALUABLE; and
    ///   - gas exhaustion: STARVED.
    ///
    /// Decoding is isolated in an external self-call.  A deterministic empty revert from that
    /// decode-only routine means the authenticated bytes are not an ABI MleProof; the same empty
    /// revert after burning the explicit budget is OOG and remains non-convicting.
    function fraudVerdictEncoded(
        bytes calldata rawProof,
        bytes32 expectedPiHash,
        bytes4 verifierCallback
    ) external view returns (uint8) {
        // This MUST precede even canonical decoding. Otherwise malformed bytes
        // observed after a chain-id migration could return INVALID rather than
        // making the whole unreleased engine UNEVALUABLE to its caller.
        if (block.chainid != allowedChainId) return ENCODED_UNEVALUABLE;
        MleProof memory proof;
        bool canonical;
        {
            uint256 decodeReserve = gasleft() / 64;
            uint256 decodeBudget = gasleft() - decodeReserve;
            try this.decodeCanonicalMleProof{gas: decodeBudget}(rawProof) returns (
                MleProof memory decoded, bool isCanonical
            ) {
                proof = decoded;
                canonical = isCanonical;
            } catch (bytes memory reason) {
                if (gasleft() < decodeReserve + decodeBudget / 8) return ENCODED_STARVED;
                // Solidity's ABI decoder uses an empty revert for malformed offsets/lengths.
                // Panic(0x41) is its excessive-memory-allocation form (e.g. an authenticated
                // tiny buffer claiming an impossible dynamic-array length).  No other selector
                // is proof fraud: an unexpected decoder/compiler failure stays unevaluable.
                if (reason.length == 0 || _isMemoryAllocationPanic(reason)) {
                    return ENCODED_INVALID;
                }
                return ENCODED_UNEVALUABLE;
            }
        }

        if (!canonical) return ENCODED_INVALID;
        bool piMatches = _publicInputsMatch(proof.publicInputs, expectedPiHash);

        // Re-enter the pinned rollup through its existing typed verification trampoline.  This
        // deliberately keeps the large VK/WHIR storage-to-memory copy in exactly one rollup
        // routine instead of duplicating it in the EIP-170-constrained runtime.  The rollup passes
        // the selector itself; arbitrary callers can only influence their own view result.
        uint256 verifyReserve = gasleft() / 64;
        uint256 verifyBudget = gasleft() - verifyReserve;
        (bool ok, bytes memory result) =
            msg.sender.staticcall{gas: verifyBudget}(abi.encodeWithSelector(verifierCallback, proof));
        if (ok) {
            // The production callback is true-or-revert.  Reject malformed/false return data as
            // unevaluable; neither is authenticated proof-rejection evidence.
            if (result.length == 32) {
                uint256 returned;
                assembly ("memory-safe") {
                    returned := mload(add(result, 0x20))
                }
                if (returned == 1) {
                    // An invalid authenticated proof is slashable regardless of whether an
                    // accuser knows a public-input preimage for its embedded limbs.  The PI
                    // precondition is consulted only after the proof itself verifies, so a
                    // malicious producer cannot hide an invalid proof behind arbitrary PIs.
                    return piMatches ? ENCODED_VALID : ENCODED_PI_MISMATCH;
                }
            }
            return ENCODED_UNEVALUABLE;
        }
        if (_isInvalidMleProof(result)) return ENCODED_INVALID;
        if (gasleft() < verifyReserve + verifyBudget / 8) return ENCODED_STARVED;
        return ENCODED_UNEVALUABLE;
    }

    /// @notice Decode a raw ABI MleProof and report whether its encoding is canonical.
    /// @dev External solely to give `fraudVerdictEncoded` a catchable decode frame.  The routine
    /// has no verifier/config branches: a non-starved empty/Panic(0x41) revert is attributable to
    /// the authenticated raw encoding, while every unexpected selector remains unevaluable.
    function decodeCanonicalMleProof(bytes calldata rawProof)
        external
        pure
        returns (MleProof memory proof, bool canonical)
    {
        proof = abi.decode(rawProof, (MleProof));
        bytes memory encoded = abi.encode(proof);
        canonical = encoded.length == rawProof.length && keccak256(encoded) == keccak256(rawProof);
    }

    function _publicInputsMatch(uint256[] memory publicInputs, bytes32 piHash) private pure returns (bool) {
        if (publicInputs.length != 8) return false;
        uint256 h = uint256(piHash);
        for (uint256 i = 0; i < 8; i++) {
            if (publicInputs[i] != ((h >> (224 - i * 32)) & 0xFFFFFFFF)) return false;
        }
        return true;
    }

    function _isInvalidMleProof(bytes memory reason) private pure returns (bool yes) {
        assembly ("memory-safe") {
            yes := and(eq(mload(reason), 4), eq(mload(add(reason, 0x20)), shl(224, 0xf0783a66)))
        }
    }

    function _isMemoryAllocationPanic(bytes memory reason) private pure returns (bool yes) {
        assembly ("memory-safe") {
            yes := and(
                eq(mload(reason), 36),
                and(eq(mload(add(reason, 0x20)), shl(224, 0x4e487b71)), eq(mload(add(reason, 0x24)), 0x41))
            )
        }
    }

    function _verifyCore(
        MleProof calldata proof,
        VerifyParams memory vp,
        SpongefishWhirVerify.WhirParams memory whirParams
    ) internal pure returns (bool) {
        if (proof.circuitDigest.length != 4) revert InvalidMleProof();
        if (proof.preprocessedRoot != vp.preprocessedCommitmentRoot) revert InvalidMleProof();
        if (_derivePreprocessedBatchR(proof.circuitDigest, proof.preprocessedRoot) != proof.preprocessedBatchR) {
            revert InvalidMleProof();
        }

        TranscriptLib.Transcript memory ts;
        (uint256[] memory tau, uint256[] memory tauInv) = _initTranscriptAndChallenges(ts, proof, vp);

        // Combined sumcheck (eq(τ,b)·C̃(b) + μ·h̃(b)): max round-poly degree = 2.
        SumcheckVerifier.SumcheckProof memory sc = _copySumcheckProof(proof.combinedProof);
        (uint256[] memory rGate, uint256 gateFinal) = SumcheckVerifier.verify(sc, 0, vp.degreeBits, 2, ts);

        // ── v2 logUp: Φ_inv zero-check sumcheck (round-poly degree ≤ 3) ──
        TranscriptLib.domainSeparate(ts, "v2-inv-zerocheck");
        SumcheckVerifier.SumcheckProof memory invSc = _copySumcheckProof(proof.invSumcheckProof);
        (uint256[] memory rInv, uint256 invFinal) = SumcheckVerifier.verify(invSc, 0, vp.degreeBits, 3, ts);

        // ── v2 logUp: Φ_h linear sumcheck (round-poly degree = 1) ──
        TranscriptLib.domainSeparate(ts, "v2-h-linear");
        SumcheckVerifier.SumcheckProof memory hSc = _copySumcheckProof(proof.hSumcheckProof);
        (uint256[] memory rH, uint256 hFinal) = SumcheckVerifier.verify(hSc, 0, vp.degreeBits, 1, ts);

        // ── R2-#1: Φ_gate zero-check sumcheck + terminal check. Returns
        // `rGateV2` (needed for the WHIR binding below). `tauGate` and
        // `gateFinalV2` are scoped inside the helper so they do not occupy
        // stack slots alongside `rGateV2` during `_runBatchAndWhir`. Without
        // this split, adding the C1/C2 boundary checks overflows the Yul
        // optimizer's 16-slot stack limit.
        uint256[] memory rGateV2 = _runGateSumcheckAndTerminal(proof, vp, ts);

        TerminalPoints memory terminalPoints = TerminalPoints({combined: rGate, inverse: rInv, h: rH, gate: rGateV2});
        _runBatchAndWhir(proof, whirParams, vp, ts, terminalPoints);

        // ── Terminal check: combined sumcheck. Packed v1 PCS-binds both C̃(r)
        //    and h̃(r). The dedicated Φ_inv + Φ_h checks below remain the
        //    algebraic soundness anchors for the phased logUp relation; this
        //    combined equality alone is not a proof of that relation.
        if (EqPolyLib.eqEval(tau, rGate).mul(proof.auxConstraintEval).add(proof.mu.mul(proof.auxPermEval)) != gateFinal)
        {
            revert InvalidMleProof();
        }

        // ── v2 logUp: g_sub(r_inv) consistency (subgroup MLE from VK powers)
        // `subgroupGenPowers` is VK/configuration data, not prover data.  A
        // short table must remain an unevaluable verifier configuration
        // error; without this guard the assembly evaluator reads adjacent
        // memory and can misclassify the resulting mismatch as proof fraud.
        require(vp.subgroupGenPowers.length == rInv.length, "subgroup powers len");
        if (_evalSubgroupMle(rInv, vp.subgroupGenPowers) != proof.gSubEvalAtRInv) {
            revert InvalidMleProof();
        }

        // ── v2 logUp: batch consistency at r_inv (witness + preprocessed)
        if (
            _computeBatchedEval(proof.witnessIndividualEvalsAtRInv, proof.witnessBatchR) != proof.witnessEvalValueAtRInv
        ) revert InvalidMleProof();

        // ── v2 logUp: terminal checks for Φ_inv and Φ_h
        _checkInvTerminal(proof, vp, tauInv, rInv, invFinal);
        _checkHTerminal(proof, vp, hFinal);

        return true;
    }

    /// @dev Φ_inv terminal check (paper §4.2.2):
    /// eq(τ_inv,r_inv) · Σ_j λ_inv^j · ( a_j·D_id − 1 + μ_inv·(b_j·D_σ − 1) ) ?= invFinal
    /// where D_id = β + w_j(r_inv) + γ·k_j·g_sub(r_inv),
    ///       D_σ  = β + w_j(r_inv) + γ·σ_j(r_inv).
    function _checkInvTerminal(
        MleProof calldata proof,
        VerifyParams memory vp,
        uint256[] memory tauInv,
        uint256[] memory rInv,
        uint256 invFinal
    ) private pure {
        uint256 nr = vp.numRoutedWires;
        if (proof.witnessIndividualEvalsAtRInv.length != proof.witnessIndividualEvals.length) {
            revert InvalidMleProof();
        }
        if (proof.preprocessedIndividualEvalsAtRInv.length != vp.numConstants + nr) {
            revert InvalidMleProof();
        }
        if (proof.inverseHelpersEvalsAtRInv.length != 2 * nr) revert InvalidMleProof();
        require(vp.kIs.length == nr, "kIs len");

        uint256 inner = _invInner(proof, vp, nr);
        uint256 eqAtRInv = EqPolyLib.eqEval(tauInv, rInv);
        if (eqAtRInv.mul(inner) != invFinal) revert InvalidMleProof();
    }

    /// @dev Φ_gate terminal check (Issue R2-#1, paper §7.3):
    ///   gateFinal ?= eq(τ_gate, r_gate_v2) · flatten_ext(
    ///       Σ_j α^j · filter_j · gate_j.eval( w(r_gate_v2), c(r_gate_v2) ),
    ///       ext_challenge
    ///   )
    ///
    /// SECURITY: All inputs to Plonky2GateEvaluator are WHIR-bound (wire +
    /// const evals at r_gate_v2 via the 4th WHIR point opening) or
    /// Fiat-Shamir-derived (α, ext_challenge, τ_gate). No prover oracle is
    /// trusted for the formula result — the verifier runs the same gate
    /// evaluator the Rust prover uses.
    function _checkGateTerminal(
        MleProof calldata proof,
        uint256[] memory tauGate,
        uint256[] memory rGateV2,
        uint256 gateFinal
    ) private pure {
        uint256 flat = Plonky2GateEvaluator.evalCombinedFlat(
            proof.witnessIndividualEvalsAtRGateV2,
            proof.preprocessedIndividualEvalsAtRGateV2,
            proof.alpha,
            proof.extChallenge,
            proof.publicInputsHash,
            proof.gates,
            proof.numSelectors,
            0, // numConstants: computed inside the evaluator from preprocessed length if needed
            proof.numGateConstraints
        );
        uint256 eqAtRGateV2 = EqPolyLib.eqEval(tauGate, rGateV2);
        if (eqAtRGateV2.mul(flat) != gateFinal) revert InvalidMleProof();
    }

    /// @dev Inner sum of the Φ_inv terminal predicate. Extracted so we can
    /// use the direct calldata arrays as typed parameters (allowing `.offset`
    /// access inside assembly).
    function _invInner(MleProof calldata proof, VerifyParams memory vp, uint256 nr)
        private
        pure
        returns (uint256 inner)
    {
        uint256[] calldata w_ = proof.witnessIndividualEvalsAtRInv;
        uint256[] calldata pre_ = proof.preprocessedIndividualEvalsAtRInv;
        uint256[] calldata ih_ = proof.inverseHelpersEvalsAtRInv;
        // vp.kIs lives in memory: take its data-pointer so inner-loop reads
        // go through a single `mload` too.
        uint256 kPtr;
        {
            uint256[] memory kArr = vp.kIs;
            assembly { kPtr := add(kArr, 0x20) }
        }
        uint256 gSub = proof.gSubEvalAtRInv;
        uint256 beta = proof.beta;
        uint256 gamma = proof.gamma;
        uint256 muInv = proof.muInv;
        uint256 lambdaInv = proof.lambdaInv;
        uint256 numConsts = vp.numConstants;
        assembly {
            let p := 0xFFFFFFFF00000001
            let wOff := w_.offset
            let pOff := pre_.offset
            let aOff := ih_.offset
            let acc := 0
            let lambdaPow := 1
            for { let j := 0 } lt(j, nr) { j := add(j, 1) } {
                let wv := calldataload(add(wOff, mul(j, 0x20)))
                let sv := calldataload(add(pOff, mul(add(j, numConsts), 0x20)))
                let aVal := calldataload(add(aOff, mul(j, 0x20)))
                let bVal := calldataload(add(aOff, mul(add(j, nr), 0x20)))
                let kj := mload(add(kPtr, mul(j, 0x20)))
                let idJ := mulmod(kj, gSub, p)
                let sum_bw := addmod(beta, wv, p)
                let denomId := addmod(sum_bw, mulmod(gamma, idJ, p), p)
                let denomSigma := addmod(sum_bw, mulmod(gamma, sv, p), p)
                let zId := mulmod(aVal, denomId, p)
                switch zId
                case 0 { zId := sub(p, 1) }
                default { zId := sub(zId, 1) }
                let zSigma := mulmod(bVal, denomSigma, p)
                switch zSigma
                case 0 { zSigma := sub(p, 1) }
                default { zSigma := sub(zSigma, 1) }
                let combined := addmod(zId, mulmod(muInv, zSigma, p), p)
                acc := addmod(acc, mulmod(lambdaPow, combined, p), p)
                lambdaPow := mulmod(lambdaPow, lambdaInv, p)
            }
            inner := acc
        }
    }

    /// @dev Φ_h terminal check (paper §4.2.3):
    /// h_final ?= Σ_j (a_j(r_h) − b_j(r_h))
    /// (unweighted — only the unweighted Σ_j (A_j − B_j) telescopes via logUp).
    function _checkHTerminal(MleProof calldata proof, VerifyParams memory vp, uint256 hFinal) private pure {
        uint256 nr = vp.numRoutedWires;
        if (proof.inverseHelpersEvalsAtRH.length != 2 * nr) revert InvalidMleProof();
        uint256 acc;
        {
            uint256[] calldata ih_ = proof.inverseHelpersEvalsAtRH;
            assembly {
                let p := 0xFFFFFFFF00000001
                let aOff := ih_.offset
                let sum := 0
                for { let j := 0 } lt(j, nr) { j := add(j, 1) } {
                    let aVal := calldataload(add(aOff, mul(j, 0x20)))
                    let bVal := calldataload(add(aOff, mul(add(j, nr), 0x20)))
                    // SECURITY (C2): self-reduce `bVal` before sub(P, bVal).
                    // `inverseHelpersEvalsAtRH` is prover-supplied uint256 with
                    // no canonical check before reaching here; a non-canonical
                    // `bVal = v + k·P` would otherwise inject K = 2^256 mod P
                    // into the sum. Caller-side canonicalization (added in
                    // verify() entry) also covers this; belt-and-suspenders.
                    sum := addmod(sum, addmod(aVal, sub(p, mod(bVal, p)), p), p)
                }
                acc := sum
            }
        }
        if (acc != hFinal) revert InvalidMleProof();
    }

    /// @dev Evaluate g_sub MLE at r using VK-bound subgroup generator powers.
    /// result = Π_i ((1-r_i) + r_i·g^{2^i}).
    function _evalSubgroupMle(uint256[] memory r, uint256[] memory gPow) internal pure returns (uint256 result) {
        assembly {
            let p := 0xFFFFFFFF00000001
            result := 1
            let rLen := mload(r)
            let rPtr := add(r, 0x20)
            let gPtr := add(gPow, 0x20)
            for { let i := 0 } lt(i, rLen) { i := add(i, 1) } {
                let ri := mload(add(rPtr, mul(i, 0x20)))
                let gi := mload(add(gPtr, mul(i, 0x20)))
                let oneMinusR := addmod(1, sub(p, ri), p)
                let rTimesG := mulmod(ri, gi, p)
                let factor := addmod(oneMinusR, rTimesG, p)
                result := mulmod(result, factor, p)
            }
        }
    }

    /// @dev Initialize transcript, absorb commitments, squeeze and check Fiat-Shamir
    /// challenges. Mirrors the Rust prover transcript order, including the v2
    /// logUp inverse-helpers commit + new challenges.
    /// Returns the transcript-derived (tau, tauInv) used in terminal checks.
    function _initTranscriptAndChallenges(
        TranscriptLib.Transcript memory ts,
        MleProof calldata proof,
        VerifyParams memory vp
    ) private pure returns (uint256[] memory tau, uint256[] memory tauInv) {
        TranscriptLib.init(ts);
        TranscriptLib.domainSeparate(ts, "circuit");
        TranscriptLib.absorbFieldVec(ts, proof.circuitDigest);
        TranscriptLib.absorbFieldVec(ts, proof.publicInputs);
        TranscriptLib.domainSeparate(ts, PACKED_PCS_SCHEMA_DOMAIN);
        TranscriptLib.absorbU64Bytes(ts, proof.protocolVersion);
        TranscriptLib.absorbU64Bytes(ts, NUM_PCS_GROUPS);
        TranscriptLib.absorbU64Bytes(ts, vp.numConstants);
        TranscriptLib.absorbU64Bytes(ts, vp.numRoutedWires);
        TranscriptLib.absorbU64Bytes(ts, proof.witnessIndividualEvals.length);
        TranscriptLib.absorbU64Bytes(ts, proof.constituentWidth);
        TranscriptLib.absorbU64Bytes(ts, _constituentIndexBits(proof.constituentWidth));
        TranscriptLib.absorbU64Bytes(ts, NUM_PACKED_VECTORS_PER_GROUP);
        TranscriptLib.absorbU64Bytes(ts, EXTENSION_FIELD_LIMBS);
        TranscriptLib.absorbU64Bytes(ts, PACKED_VARIABLE_ORDER_CODE);
        TranscriptLib.domainSeparate(ts, "pcs-group-preprocessed");
        TranscriptLib.absorbBytes(ts, abi.encodePacked(proof.preprocessedRoot));
        TranscriptLib.domainSeparate(ts, "pcs-group-witness");
        TranscriptLib.absorbBytes(ts, abi.encodePacked(proof.witnessRoot));

        TranscriptLib.domainSeparate(ts, "batch-commit-witness");
        if (TranscriptLib.squeezeChallenge(ts) != proof.witnessBatchR) revert InvalidMleProof();

        TranscriptLib.domainSeparate(ts, "challenges");
        if (TranscriptLib.squeezeChallenge(ts) != proof.beta) revert InvalidMleProof();
        if (TranscriptLib.squeezeChallenge(ts) != proof.gamma) revert InvalidMleProof();

        // ── v2 logUp: inverse-helpers commit absorbed AFTER β,γ. ─────────
        TranscriptLib.domainSeparate(ts, "pcs-group-inverse-helpers");
        TranscriptLib.absorbBytes(ts, abi.encodePacked(proof.inverseHelpersCommitmentRoot));
        TranscriptLib.domainSeparate(ts, "inverse-helpers-batch-r");
        if (TranscriptLib.squeezeChallenge(ts) != proof.inverseHelpersBatchR) {
            revert InvalidMleProof();
        }

        if (TranscriptLib.squeezeChallenge(ts) != proof.alpha) revert InvalidMleProof();
        TranscriptLib.domainSeparate(ts, "extension-combine");
        if (TranscriptLib.squeezeChallenge(ts) != proof.extChallenge) revert InvalidMleProof();

        // Aux commit
        TranscriptLib.domainSeparate(ts, "pcs-group-auxiliary");
        TranscriptLib.absorbBytes(ts, abi.encodePacked(proof.auxCommitmentRoot));
        TranscriptLib.domainSeparate(ts, "aux-batch-r");
        if (TranscriptLib.squeezeChallenge(ts) != proof.auxBatchR) revert InvalidMleProof();
        if (proof.auxConstraintEval.add(proof.auxBatchR.mul(proof.auxPermEval)) != proof.auxEvalValue) {
            revert InvalidMleProof();
        }

        TranscriptLib.domainSeparate(ts, "post-auxiliary-challenges-v1");
        tau = TranscriptLib.squeezeChallenges(ts, vp.degreeBits);
        TranscriptLib.squeezeChallenges(ts, vp.degreeBits); // tauPerm sync (unused)
        TranscriptLib.domainSeparate(ts, "v2-logup-challenges");
        if (TranscriptLib.squeezeChallenge(ts) != proof.lambdaInv) revert InvalidMleProof();
        if (TranscriptLib.squeezeChallenge(ts) != proof.muInv) revert InvalidMleProof();
        tauInv = TranscriptLib.squeezeChallenges(ts, vp.degreeBits);

        // Combined sumcheck
        TranscriptLib.domainSeparate(ts, "combined-sumcheck");
        if (TranscriptLib.squeezeChallenge(ts) != proof.mu) revert InvalidMleProof();
    }

    /// @dev Run redundant batch-evaluation consistency checks, build the exact
    /// constituent opening matrix, and invoke WHIR with every terminal value
    /// fixed before WHIR samples its vector-RLC challenge.
    function _runBatchAndWhir(
        MleProof calldata proof,
        SpongefishWhirVerify.WhirParams memory whirParams,
        VerifyParams memory vp,
        TranscriptLib.Transcript memory ts,
        TerminalPoints memory terminalPoints
    ) private pure {
        TranscriptLib.domainSeparate(ts, "pcs-eval");
        if (
            _computeBatchedEval(proof.preprocessedIndividualEvals, proof.preprocessedBatchR)
                != proof.preprocessedEvalValue
        ) revert InvalidMleProof();
        if (proof.preprocessedIndividualEvals.length != vp.numConstants + vp.numRoutedWires) {
            revert InvalidMleProof();
        }
        if (_computeBatchedEval(proof.witnessIndividualEvals, proof.witnessBatchR) != proof.witnessEvalValue) {
            revert InvalidMleProof();
        }

        // ── v2 logUp: also bind preprocessed batch eval at r_inv. ────────
        if (
            _computeBatchedEval(proof.preprocessedIndividualEvalsAtRInv, proof.preprocessedBatchR)
                != proof.preprocessedEvalValueAtRInv
        ) revert InvalidMleProof();

        uint256 indexBits = _constituentIndexBits(proof.constituentWidth);
        GoldilocksExt3.Ext3[][] memory indexPoints = _absorbClaimsAndSampleIndexPoints(ts, proof, indexBits);
        // WHIR consumes the reverse of the full dense-LSB point
        // `[row_0..row_n-1,index_0..index_l-1]`.
        whirParams.evaluationPoint = _derivePackedEvalPoint(terminalPoints.combined, indexPoints[POINT_COMBINED]);
        whirParams.evaluationPoint2 = _derivePackedEvalPoint(terminalPoints.inverse, indexPoints[POINT_INVERSE]);
        whirParams.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](2);
        whirParams.additionalEvaluationPoints[0] = _derivePackedEvalPoint(terminalPoints.h, indexPoints[POINT_H]);
        whirParams.additionalEvaluationPoints[1] = _derivePackedEvalPoint(terminalPoints.gate, indexPoints[POINT_GATE]);

        // One packed scalar opening per point/group. The mask fixes precisely
        // the nine pairs consumed by terminal equations; WHIR authenticates the
        // remaining Cartesian openings against the same four roots as well.
        uint256 width = proof.constituentWidth;
        GoldilocksExt3.Ext3[] memory whirEvals = new GoldilocksExt3.Ext3[](NUM_PCS_CLAIMS);
        bytes memory evalMask = abi.encodePacked(PACKED_BOUND_CLAIM_MASK);

        _bindPackedClaim(
            whirEvals,
            proof.preprocessedIndividualEvals,
            POINT_COMBINED,
            GROUP_PREPROCESSED,
            width,
            indexPoints[POINT_COMBINED]
        );
        _bindPackedClaim(
            whirEvals, proof.witnessIndividualEvals, POINT_COMBINED, GROUP_WITNESS, width, indexPoints[POINT_COMBINED]
        );
        uint256[] memory auxClaims = new uint256[](2);
        auxClaims[0] = proof.auxConstraintEval;
        auxClaims[1] = proof.auxPermEval;
        _bindPackedClaim(whirEvals, auxClaims, POINT_COMBINED, GROUP_AUXILIARY, width, indexPoints[POINT_COMBINED]);

        _bindPackedClaim(
            whirEvals,
            proof.preprocessedIndividualEvalsAtRInv,
            POINT_INVERSE,
            GROUP_PREPROCESSED,
            width,
            indexPoints[POINT_INVERSE]
        );
        _bindPackedClaim(
            whirEvals,
            proof.witnessIndividualEvalsAtRInv,
            POINT_INVERSE,
            GROUP_WITNESS,
            width,
            indexPoints[POINT_INVERSE]
        );
        _bindPackedClaim(
            whirEvals,
            proof.inverseHelpersEvalsAtRInv,
            POINT_INVERSE,
            GROUP_INVERSE_HELPERS,
            width,
            indexPoints[POINT_INVERSE]
        );

        _bindPackedClaim(
            whirEvals, proof.inverseHelpersEvalsAtRH, POINT_H, GROUP_INVERSE_HELPERS, width, indexPoints[POINT_H]
        );

        _bindPackedClaim(
            whirEvals,
            proof.preprocessedIndividualEvalsAtRGateV2,
            POINT_GATE,
            GROUP_PREPROCESSED,
            width,
            indexPoints[POINT_GATE]
        );
        _bindPackedClaim(
            whirEvals, proof.witnessIndividualEvalsAtRGateV2, POINT_GATE, GROUP_WITNESS, width, indexPoints[POINT_GATE]
        );
        bytes32[] memory expectedRoots = new bytes32[](NUM_PCS_GROUPS);
        expectedRoots[GROUP_PREPROCESSED] = proof.preprocessedRoot;
        expectedRoots[GROUP_WITNESS] = proof.witnessRoot;
        expectedRoots[GROUP_INVERSE_HELPERS] = proof.inverseHelpersCommitmentRoot;
        expectedRoots[GROUP_AUXILIARY] = proof.auxCommitmentRoot;

        // Batch consistency at r_gate_v2 (witness + full preprocessed)
        if (
            _computeBatchedEval(proof.witnessIndividualEvalsAtRGateV2, proof.witnessBatchR)
                != proof.witnessEvalValueAtRGateV2
        ) revert InvalidMleProof();
        if (
            _computeBatchedEval(proof.preprocessedIndividualEvalsAtRGateV2, proof.preprocessedBatchR)
                != proof.preprocessedEvalValueAtRGateV2
        ) revert InvalidMleProof();

        if (!SpongefishWhirVerify.verifyWhirProofBound(
                vp.protocolId,
                vp.sessionId,
                "",
                proof.whirTranscript,
                proof.whirHints,
                whirEvals,
                evalMask,
                expectedRoots,
                whirParams
            )) revert InvalidMleProof();
    }

    function _bindPackedClaim(
        GoldilocksExt3.Ext3[] memory evals,
        uint256[] memory values,
        uint256 point,
        uint256 group,
        uint256 width,
        GoldilocksExt3.Ext3[] memory indexPoint
    ) private pure {
        uint256 slot = point * NUM_PCS_GROUPS + group;
        evals[slot] = PackedClaimLib.fold(values, width, indexPoint);
    }

    function _absorbClaimsAndSampleIndexPoints(
        TranscriptLib.Transcript memory ts,
        MleProof calldata proof,
        uint256 indexBits
    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        uint256[] memory empty = new uint256[](0);
        uint256[] memory aux = new uint256[](2);
        aux[0] = proof.auxConstraintEval;
        aux[1] = proof.auxPermEval;
        TranscriptLib.domainSeparate(ts, "pcs-constituent-claims-v1");
        // Exact point-major, group-major layout. Empty vectors are explicit
        // length-zero messages, not omitted transcript entries.
        TranscriptLib.absorbFieldVec(ts, proof.preprocessedIndividualEvals);
        TranscriptLib.absorbFieldVec(ts, proof.witnessIndividualEvals);
        TranscriptLib.absorbFieldVec(ts, empty);
        TranscriptLib.absorbFieldVec(ts, aux);
        TranscriptLib.absorbFieldVec(ts, proof.preprocessedIndividualEvalsAtRInv);
        TranscriptLib.absorbFieldVec(ts, proof.witnessIndividualEvalsAtRInv);
        TranscriptLib.absorbFieldVec(ts, proof.inverseHelpersEvalsAtRInv);
        TranscriptLib.absorbFieldVec(ts, empty);
        TranscriptLib.absorbFieldVec(ts, empty);
        TranscriptLib.absorbFieldVec(ts, empty);
        TranscriptLib.absorbFieldVec(ts, proof.inverseHelpersEvalsAtRH);
        TranscriptLib.absorbFieldVec(ts, empty);
        TranscriptLib.absorbFieldVec(ts, proof.preprocessedIndividualEvalsAtRGateV2);
        TranscriptLib.absorbFieldVec(ts, proof.witnessIndividualEvalsAtRGateV2);
        TranscriptLib.absorbFieldVec(ts, empty);
        TranscriptLib.absorbFieldVec(ts, empty);

        TranscriptLib.domainSeparate(ts, "pcs-constituent-index-v1");
        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS);
        for (uint256 point = 0; point < NUM_PCS_TERMINAL_POINTS; point++) {
            points[point] = new GoldilocksExt3.Ext3[](indexBits);
            for (uint256 bit = 0; bit < indexBits; bit++) {
                points[point][bit] = GoldilocksExt3.Ext3(
                    uint64(TranscriptLib.squeezeChallenge(ts)),
                    uint64(TranscriptLib.squeezeChallenge(ts)),
                    uint64(TranscriptLib.squeezeChallenge(ts))
                );
            }
        }
    }

    /// @dev Run the Φ_gate sumcheck and its terminal check in a single scope
    /// so that `tauGate` and `gateFinalV2` don't live in `_verifyCore`'s stack
    /// frame during the subsequent WHIR batching. Returns `rGateV2` which is
    /// still needed for the WHIR evaluation-point binding.
    function _runGateSumcheckAndTerminal(
        MleProof calldata proof,
        VerifyParams memory vp,
        TranscriptLib.Transcript memory ts
    ) private pure returns (uint256[] memory rGateV2) {
        TranscriptLib.domainSeparate(ts, "v2-gate-challenges");
        uint256[] memory tauGate = TranscriptLib.squeezeChallenges(ts, vp.degreeBits);
        TranscriptLib.domainSeparate(ts, "v2-gate-zerocheck");
        SumcheckVerifier.SumcheckProof memory gateSc = _copySumcheckProof(proof.gateSumcheckProof);
        uint256 gateFinalV2;
        (rGateV2, gateFinalV2) = SumcheckVerifier.verify(gateSc, 0, vp.degreeBits, 2 + proof.quotientDegreeFactor, ts);
        // Terminal check uses proof.gates / wire+const evals at r_gate_v2 —
        // all bound directly by the grouped WHIR opening statement.
        _checkGateTerminal(proof, tauGate, rGateV2, gateFinalV2);
    }

    /// @notice Public helper: compute the VK-bound gate-layout digest.
    ///
    /// The digest protects against the gate-reinterpretation forgery
    /// described in phase3_c1_threat_model.md. The on-chain verifier
    /// (`_requireGatesDigest` inside `verify`) re-computes this value and
    /// compares against the `gatesDigest` passed by the caller; a mismatch
    /// reverts with `"gatesDigest"`.
    ///
    /// Deployers and test harnesses MUST invoke this function (or emit the
    /// identical byte layout off-chain) to pin a circuit's expected digest.
    ///
    /// Hashed layout (deterministic):
    ///   [0x00] version       (32 bytes)
    ///   [0x20] piLength      (32 bytes)
    ///   [0x40] circuitDigest[0]
    ///   [0x60] circuitDigest[1]
    ///   [0x80] circuitDigest[2]
    ///   [0xa0] circuitDigest[3]
    ///   [0xc0] numWires      (32 bytes)
    ///   [0xe0] numSelectors  (32 bytes)
    ///   [0x100] numGateConstr (32 bytes)
    ///   [0x120] qdf           (32 bytes)
    ///   [0x140] gatesLen      (32 bytes)
    ///   [0x160] gates data    (gatesLen × 288 bytes, raw calldata copy)
    ///
    /// Each GateInfo element occupies 9 × 32 = 288 bytes in calldata because
    /// uint8/uint16 fields are individually padded to the 32-byte word
    /// boundary; this matches the layout `calldatacopy` would produce.
    function computeGatesDigest(
        Plonky2GateEvaluator.GateInfo[] calldata gates,
        uint256[] calldata circuitDigest,
        uint256 numPublicInputs,
        uint256 numWires,
        uint256 numSelectors,
        uint256 numGateConstraints,
        uint256 quotientDegreeFactor
    ) public pure returns (bytes32 computed) {
        if (circuitDigest.length != 4) revert InvalidMleProof();
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, GATES_DIGEST_VERSION)
            mstore(add(ptr, 0x20), numPublicInputs)
            calldatacopy(add(ptr, 0x40), circuitDigest.offset, 0x80)
            mstore(add(ptr, 0xc0), numWires)
            mstore(add(ptr, 0xe0), numSelectors)
            mstore(add(ptr, 0x100), numGateConstraints)
            mstore(add(ptr, 0x120), quotientDegreeFactor)
            let gatesLen := gates.length
            mstore(add(ptr, 0x140), gatesLen)
            let gatesBytes := mul(gatesLen, 288)
            calldatacopy(add(ptr, 0x160), gates.offset, gatesBytes)
            computed := keccak256(ptr, add(0x160, gatesBytes))
        }
    }

    /// @dev C1 VK-binding check. Delegates to `computeGatesDigest` so the
    /// on-chain and off-chain hashes stay in lockstep.
    function _requireGatesDigest(MleProof calldata proof, bytes32 expected) private pure {
        bytes32 computed = computeGatesDigest(
            proof.gates,
            proof.circuitDigest,
            proof.publicInputs.length,
            proof.witnessIndividualEvalsAtRGateV2.length,
            proof.numSelectors,
            proof.numGateConstraints,
            proof.quotientDegreeFactor
        );
        if (computed != expected) revert InvalidMleProof();
    }

    /// @dev C2 boundary canonicalization — fully Yul-ified.
    ///
    /// Every prover-supplied `uint256` array consumed by inline-assembly
    /// `sub(P, X)` (directly or via MleProof fields reaching
    /// `Plonky2GateEvaluator` / `PoseidonGate`) must be `< P` to prevent the
    /// K = 2^32 − 1 injection attack documented in phase2_c2_poc_report.md.
    ///
    /// The entire check runs in a single assembly block so the per-array
    /// function-call overhead is amortized and the `P` constant lives in one
    /// stack slot. On a medium_mul fixture this saves ~40k gas over the
    /// previous `_requireCanonicalArray` helper-per-array structure.
    function _requireCanonicalProofInputs(MleProof calldata proof) private pure {
        // Split into two halves to stay under the Yul stack limit (each half
        // has 5 calldata array offset+length pairs = 10 stack slots, plus
        // locals = ~14, well within budget).
        _canonHalfA(
            proof.preprocessedIndividualEvals,
            proof.witnessIndividualEvals,
            proof.preprocessedIndividualEvalsAtRInv,
            proof.witnessIndividualEvalsAtRInv,
            proof.inverseHelpersEvalsAtRInv
        );
        _canonHalfB(
            proof.inverseHelpersEvalsAtRH,
            proof.witnessIndividualEvalsAtRGateV2,
            proof.preprocessedIndividualEvalsAtRGateV2,
            proof.circuitDigest,
            proof.publicInputs
        );
        _canonPih(proof.publicInputsHash);
        uint256[4] memory expectedPublicInputsHash = PoseidonPublicInputsHash.hashNoPad(proof.publicInputs);
        for (uint256 i = 0; i < 4; i++) {
            if (proof.publicInputsHash[i] != expectedPublicInputsHash[i]) {
                revert InvalidMleProof();
            }
        }
    }

    function _requireValidVkInputs(VerifyParams memory vp) private pure {
        require(vp.kIs.length == vp.numRoutedWires, "kIs len");
        require(vp.subgroupGenPowers.length == vp.degreeBits, "subgroup powers len");
        for (uint256 i = 0; i < vp.kIs.length; i++) {
            require(vp.kIs[i] < P, "kIs canonical");
        }
        for (uint256 i = 0; i < vp.subgroupGenPowers.length; i++) {
            require(vp.subgroupGenPowers[i] < P, "subgroup powers canonical");
        }
    }

    function _canonicalScalars(MleProof calldata proof) private pure returns (bool) {
        if (
            proof.preprocessedEvalValue >= P || proof.preprocessedBatchR >= P || proof.witnessEvalValue >= P
                || proof.witnessBatchR >= P || proof.auxBatchR >= P || proof.auxConstraintEval >= P
        ) return false;
        if (
            proof.auxPermEval >= P || proof.auxEvalValue >= P || proof.alpha >= P || proof.beta >= P || proof.gamma >= P
                || proof.mu >= P
        ) return false;
        if (
            proof.inverseHelpersBatchR >= P || proof.lambdaInv >= P || proof.muInv >= P || proof.gSubEvalAtRInv >= P
                || proof.witnessEvalValueAtRInv >= P
        ) return false;
        return proof.preprocessedEvalValueAtRInv < P && proof.extChallenge < P && proof.witnessEvalValueAtRGateV2 < P
            && proof.preprocessedEvalValueAtRGateV2 < P;
    }

    function _requireCanonicalSumchecks(MleProof calldata proof) private pure {
        _requireCanonicalSumcheck(proof.combinedProof);
        _requireCanonicalSumcheck(proof.invSumcheckProof);
        _requireCanonicalSumcheck(proof.hSumcheckProof);
        _requireCanonicalSumcheck(proof.gateSumcheckProof);
    }

    function _requireCanonicalSumcheck(SumcheckVerifier.SumcheckProof calldata proof) private pure {
        for (uint256 i = 0; i < proof.roundPolys.length; i++) {
            uint256[] calldata evals = proof.roundPolys[i].evals;
            for (uint256 j = 0; j < evals.length; j++) {
                if (evals[j] >= P) revert InvalidMleProof();
            }
        }
    }

    /// @dev Five-array canonicalization — first half. Single Yul block,
    /// shared revert path, one `P` constant on the stack.
    function _canonHalfA(
        uint256[] calldata a0,
        uint256[] calldata a1,
        uint256[] calldata a2,
        uint256[] calldata a3,
        uint256[] calldata a4
    ) private pure {
        assembly {
            function checkArr(off, n, p) {
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    let v := calldataload(add(off, mul(i, 0x20)))
                    if iszero(lt(v, p)) {
                        mstore(0x00, shl(224, 0xf0783a66))
                        revert(0x00, 0x04)
                    }
                }
            }
            let P_ := 0xFFFFFFFF00000001
            checkArr(a0.offset, a0.length, P_)
            checkArr(a1.offset, a1.length, P_)
            checkArr(a2.offset, a2.length, P_)
            checkArr(a3.offset, a3.length, P_)
            checkArr(a4.offset, a4.length, P_)
        }
    }

    function _canonHalfB(
        uint256[] calldata a0,
        uint256[] calldata a1,
        uint256[] calldata a2,
        uint256[] calldata a3,
        uint256[] calldata a4
    ) private pure {
        assembly {
            function checkArr(off, n, p) {
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    let v := calldataload(add(off, mul(i, 0x20)))
                    if iszero(lt(v, p)) {
                        mstore(0x00, shl(224, 0xf0783a66))
                        revert(0x00, 0x04)
                    }
                }
            }
            let P_ := 0xFFFFFFFF00000001
            checkArr(a0.offset, a0.length, P_)
            checkArr(a1.offset, a1.length, P_)
            checkArr(a2.offset, a2.length, P_)
            checkArr(a3.offset, a3.length, P_)
            checkArr(a4.offset, a4.length, P_)
        }
    }

    /// @dev Fixed-size 4-element publicInputsHash canonicalization. Unrolled.
    function _canonPih(uint256[4] calldata pih) private pure {
        assembly {
            let P_ := 0xFFFFFFFF00000001
            let h0 := calldataload(pih)
            let h1 := calldataload(add(pih, 0x20))
            let h2 := calldataload(add(pih, 0x40))
            let h3 := calldataload(add(pih, 0x60))
            if or(or(iszero(lt(h0, P_)), iszero(lt(h1, P_))), or(iszero(lt(h2, P_)), iszero(lt(h3, P_)))) {
                mstore(0x00, shl(224, 0xf0783a66))
                revert(0x00, 0x04)
            }
        }
    }

    /// @dev Yul-optimized: replaces the per-element calldata→memory loop with
    /// a single `calldatacopy`.
    function _derivePreprocessedBatchR(uint256[] calldata cd, bytes32 preprocessedRoot) private pure returns (uint256) {
        TranscriptLib.Transcript memory t;
        TranscriptLib.init(t);
        TranscriptLib.domainSeparate(t, "preprocessed-batch-r");
        uint256 n = cd.length;
        uint256[] memory m = new uint256[](n);
        assembly {
            calldatacopy(add(m, 0x20), cd.offset, mul(n, 0x20))
        }
        TranscriptLib.absorbFieldVec(t, m);
        TranscriptLib.absorbBytes(t, abi.encodePacked(preprocessedRoot));
        return TranscriptLib.squeezeChallenge(t);
    }

    function _computeBatchedEval(uint256[] calldata evals, uint256 batchR) private pure returns (uint256 result) {
        assembly {
            let p := 0xFFFFFFFF00000001
            result := 0
            let rPow := 1
            let n := evals.length
            let off := evals.offset
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let v := calldataload(add(off, mul(i, 0x20)))
                result := addmod(result, mulmod(rPow, v, p), p)
                rPow := mulmod(rPow, batchR, p)
            }
        }
    }

    /// @dev Reverse the complete dense-LSB packed point
    /// `[row_0..row_n-1,index_0..index_l-1]` into WHIR order.
    function _derivePackedEvalPoint(uint256[] memory rowPoint, GoldilocksExt3.Ext3[] memory indexPoint)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory pt)
    {
        pt = new GoldilocksExt3.Ext3[](rowPoint.length + indexPoint.length);
        for (uint256 i = 0; i < indexPoint.length; i++) {
            GoldilocksExt3.Ext3 memory value = indexPoint[indexPoint.length - 1 - i];
            pt[i] = GoldilocksExt3.Ext3(value.c0, value.c1, value.c2);
        }
        for (uint256 i = 0; i < rowPoint.length; i++) {
            pt[indexPoint.length + i] = GoldilocksExt3.Ext3(uint64(rowPoint[rowPoint.length - 1 - i]), 0, 0);
        }
    }

    function _constituentIndexBits(uint256 width) private pure returns (uint256 bits) {
        if (width == 0) revert InvalidMleProof();
        uint256 capacity = 1;
        while (capacity < width) {
            capacity <<= 1;
            bits++;
        }
    }

    /// @dev Copy a sumcheck proof from calldata to memory using `calldatacopy`
    /// for the inner `uint256[] evals` arrays (instead of an element-wise
    /// Solidity loop). Called 4× per verify — on a 16-round fixture this
    /// saves ~5 × 16 × #rounds gas vs the naïve loop.
    function _copySumcheckProof(SumcheckVerifier.SumcheckProof calldata src)
        private
        pure
        returns (SumcheckVerifier.SumcheckProof memory dst)
    {
        uint256 nRounds = src.roundPolys.length;
        dst.roundPolys = new SumcheckVerifier.RoundPoly[](nRounds);
        for (uint256 i = 0; i < nRounds; i++) {
            uint256[] calldata srcEvals = src.roundPolys[i].evals;
            uint256 n = srcEvals.length;
            uint256[] memory dstEvals = new uint256[](n);
            assembly {
                // Copy n · 32 bytes from calldata into memory starting at
                // the `uint256[]` payload (skipping the 0x20 length prefix).
                calldatacopy(add(dstEvals, 0x20), srcEvals.offset, mul(n, 0x20))
            }
            dst.roundPolys[i].evals = dstEvals;
        }
    }
}
