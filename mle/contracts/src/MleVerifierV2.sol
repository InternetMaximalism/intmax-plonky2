// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {
    InvalidMleProof,
    InvalidMleVerifierChainId,
    InvalidMleVerifierConfiguration,
    MleProofEngineUnavailable
} from "./MleProofErrors.sol";
import {CanonicalWhirProfileV2} from "./CanonicalWhirProfileV2.sol";
import {CircuitConfigV2} from "./CircuitConfigV2.sol";
import {OuterLogupExt3Verifier} from "./OuterLogupExt3Verifier.sol";
import {PackedClaimExt3} from "./PackedClaimExt3.sol";
import {Plonky2GateEvaluatorExt3} from "./Plonky2GateEvaluatorExt3.sol";
import {PoseidonPublicInputsHash} from "./PoseidonPublicInputsHash.sol";
import {TranscriptV2} from "./TranscriptV2.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {SpongefishWhirVerify} from "./spongefish/SpongefishWhirVerify.sol";
import {
    BASE_FIELD_MULTIPLICATIVE_GENERATOR_V2,
    BASE_FIELD_MODULUS_V2,
    BASE_FIELD_POWER_OF_TWO_GENERATOR_V2,
    BASE_FIELD_TWO_ADICITY_V2,
    CIRCUIT_DIGEST_LENGTH_V2,
    COMPACT_MAGIC_V2,
    DOMAIN_CIRCUIT_CONFIG_DIGEST_V2,
    DOMAIN_CIRCUIT_STATEMENT_V2,
    DOMAIN_CONSTITUENT_CLAIMS_V2,
    DOMAIN_CONSTITUENT_INDEX_V2,
    DOMAIN_GROUP_NORM_INVERSE_V2,
    DOMAIN_GROUP_PREPROCESSED_V2,
    DOMAIN_GROUP_WITNESS_V2,
    DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2,
    DOMAIN_OUTER_RELATION_CHALLENGES_V2,
    DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2,
    DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2,
    EXTENSION_FIELD_LIMBS_V2,
    GATE_SUMCHECK_COUNT_V2,
    LOG_ROUND_DEGREE_V2,
    MAX_COMPACT_PROOF_BYTES_V2,
    MAX_CONSTITUENT_INDEX_BITS_V2,
    MAX_CONSTITUENT_WIDTH_V2,
    MAX_GATE_CONSTRAINTS_V2,
    MAX_GATE_ROUND_DEGREE_V2,
    MAX_GATE_ROWS_V2,
    MAX_PUBLIC_INPUTS_V2,
    MAX_ROUTED_WIRES_V2,
    MAX_ROW_VARIABLES_V2,
    MAX_WHIR_HINT_BYTES_V2,
    MAX_WHIR_NARG_BYTES_V2,
    MLE_PROTOCOL_VERSION_CURRENT,
    NUM_PACKED_VECTORS_PER_GROUP_V2,
    NUM_PCS_CLAIMS_V2,
    NUM_PCS_GROUPS_V2,
    NUM_PCS_TERMINAL_POINTS_V2,
    PACKED_BOUND_CLAIM_MASK_V2,
    PACKED_PCS_SCHEMA_DOMAIN_V2,
    PACKED_VARIABLE_ORDER_CODE_V2
} from "./generated/MleWhirV2.sol";

/// @title MleVerifierV2
/// @notice Atomic security-amplified MLE/WHIR verification.
/// @dev No public partial-verification result is accepted here. A successful
/// call has checked the two Ext3 outer sumchecks, all five terminal-used
/// constituent vectors against one three-group/two-point WHIR statement, the
/// formal norm/logUp terminal, and the exact Plonky2 gate terminal.
///
/// Two entry points share one verification pipeline over a `ProofView`:
/// `verifyCompactWithConfig` reads the canonical `MLEWHIR3` byte string
/// directly from calldata (the production path used by `PinnedMleVerifierV2`),
/// and `verify` accepts the typed ABI proof. Both materialize every Ext3
/// vector exactly once, as flat canonical limb buffers, and keep the WHIR hint
/// stream in calldata until its single consumer.
contract MleVerifierV2 {
    // Raw-proof verdicts consumed by fraud classifiers. Keep these values
    // aligned with the parent rollup: only INVALID is proof-dependent fraud;
    // every decoder/configuration/availability failure is non-convicting.
    uint8 internal constant ENCODED_INVALID = 0;
    uint8 internal constant ENCODED_VALID = 1;
    uint8 internal constant ENCODED_UNEVALUABLE = 2;
    uint8 internal constant ENCODED_STARVED = 3;
    uint8 internal constant ENCODED_PI_MISMATCH = 4;

    uint256 public immutable allowedChainId;
    bytes32 public immutable preprocessedCommitmentRoot;
    bytes32 public immutable verificationConfigDigest;
    bytes32 public immutable circuitConfigDigest;
    bytes32 public immutable whirParametersDigest;
    bytes32 public immutable whirProtocolIdFirst;
    bytes32 public immutable whirProtocolIdSecond;
    bytes32 public immutable whirSessionId;
    uint64 public immutable circuitDigest0;
    uint64 public immutable circuitDigest1;
    uint64 public immutable circuitDigest2;
    uint64 public immutable circuitDigest3;

    struct MleProof {
        uint256 protocolVersion;
        uint256 constituentWidth;
        uint256[] circuitDigest;
        uint256[] publicInputs;
        bytes32 preprocessedRoot;
        bytes32 witnessRoot;
        bytes32 normInverseRoot;
        bytes whirTranscript;
        bytes whirHints;
        OuterLogupExt3Verifier.SumcheckProof logProof;
        GoldilocksExt3.Ext3[] logPreprocessed;
        GoldilocksExt3.Ext3[] logWitness;
        GoldilocksExt3.Ext3[] logNormInverse;
        OuterLogupExt3Verifier.SumcheckProof gateProof;
        GoldilocksExt3.Ext3[] gatePreprocessed;
        GoldilocksExt3.Ext3[] gateWitness;
    }

    /// @dev The dynamic VK is supplied on each call only to avoid expensive
    /// contract storage. Its two complete digests are computed and pinned by
    /// the constructor; callers cannot select another circuit or WHIR config.
    struct VerificationConfig {
        CircuitConfigV2.Parameters circuit;
        /// @dev Ordered `row_u16_le || routed_column_u8`, exactly 3 bytes/PI.
        bytes publicInputWireMap;
        uint256[] kIs;
        uint256[] subgroupGenPowers;
        Plonky2GateEvaluatorExt3.GateInfoV2[] gates;
        SpongefishWhirVerify.WhirParams whir;
    }

    /// @dev One proof, fully shape-checked and canonicalized, in the form the
    /// pipeline consumes. Every Ext3 vector is a flat limb buffer with three
    /// canonical words per element (`c0, c1, c2`); sumcheck rounds are
    /// round-major then coefficient-major. The WHIR hint stream stays in
    /// calldata (`hintsOffset`, `hintsLength`). When the proof came from the
    /// compact encoding, `logClaimsOffset`/`gateClaimsOffset` point at the raw
    /// little-endian records of the five terminal-used vectors so the
    /// transcript can absorb them without re-serializing; both are zero for a
    /// typed ABI proof.
    struct ProofView {
        uint256[] publicInputs;
        bytes32 preprocessedRoot;
        bytes32 witnessRoot;
        bytes32 normInverseRoot;
        bytes whirTranscript;
        uint256 hintsOffset;
        uint256 hintsLength;
        uint256[] logRounds;
        uint256[] gateRounds;
        uint256[] logPreprocessed;
        uint256[] logWitness;
        uint256[] logNormInverse;
        uint256[] gatePreprocessed;
        uint256[] gateWitness;
        uint256 logClaimsOffset;
        uint256 gateClaimsOffset;
    }

    struct DerivedState {
        TranscriptV2.Transcript transcript;
        OuterLogupExt3Verifier.Challenges logChallenges;
        GoldilocksExt3.Ext3 gateAlpha;
        GoldilocksExt3.Ext3[] gateTau;
    }

    constructor(
        uint256 allowedChainId_,
        bytes32 preprocessedCommitmentRoot_,
        bytes32[2] memory whirProtocolId_,
        bytes32 whirSessionId_,
        uint64[4] memory circuitDigest_,
        VerificationConfig memory config_
    ) {
        if (allowedChainId_ == 0 || block.chainid != allowedChainId_) {
            revert InvalidMleVerifierChainId(allowedChainId_, block.chainid);
        }
        if (
            preprocessedCommitmentRoot_ == bytes32(0)
                || (whirProtocolId_[0] == bytes32(0) && whirProtocolId_[1] == bytes32(0))
                || whirSessionId_ == bytes32(0)
        ) revert InvalidMleVerifierConfiguration();

        _validateConfiguration(config_, circuitDigest_);
        // A memory-to-memory assignment of a struct containing dynamic arrays
        // aliases those arrays. Pin the caller's canonical empty-point config
        // before constructing the temporary two-point validation view below.
        bytes32 computedVerificationConfigDigest = keccak256(abi.encode(config_));
        bytes32 computedWhirParametersDigest = keccak256(abi.encode(config_.whir));
        CanonicalWhirProfileV2.validateCanonical(
            config_.whir.numVariables, computedWhirParametersDigest, whirProtocolId_, whirSessionId_
        );
        Plonky2GateEvaluatorExt3.validateConfiguration(
            config_.gates,
            config_.circuit.numSelectors,
            config_.circuit.numConstants,
            config_.circuit.numGateConstraints,
            config_.circuit.numWires,
            config_.circuit.quotientDegreeFactor
        );
        SpongefishWhirVerify.WhirParams memory whirForValidation = config_.whir;
        whirForValidation.evaluationPoint = new GoldilocksExt3.Ext3[](config_.whir.numVariables);
        whirForValidation.evaluationPoint2 = new GoldilocksExt3.Ext3[](config_.whir.numVariables);
        whirForValidation.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        SpongefishWhirVerify.validateParameters(whirForValidation, NUM_PCS_TERMINAL_POINTS_V2);

        uint256[] memory digestVector = _digestVector(circuitDigest_);
        bytes32 computedCircuitConfig = CircuitConfigV2.digest(
            config_.circuit,
            digestVector,
            config_.kIs,
            config_.subgroupGenPowers,
            config_.gates,
            config_.publicInputWireMap
        );

        allowedChainId = allowedChainId_;
        preprocessedCommitmentRoot = preprocessedCommitmentRoot_;
        verificationConfigDigest = computedVerificationConfigDigest;
        circuitConfigDigest = computedCircuitConfig;
        whirParametersDigest = computedWhirParametersDigest;
        whirProtocolIdFirst = whirProtocolId_[0];
        whirProtocolIdSecond = whirProtocolId_[1];
        whirSessionId = whirSessionId_;
        circuitDigest0 = circuitDigest_[0];
        circuitDigest1 = circuitDigest_[1];
        circuitDigest2 = circuitDigest_[2];
        circuitDigest3 = circuitDigest_[3];
    }

    /// @notice Verify the complete v2 statement on the constructor-pinned chain.
    /// @dev The chain guard is deliberately the first branch. Configuration
    /// failures use `InvalidMleVerifierConfiguration`; only proof-dependent
    /// negative results use `InvalidMleProof`.
    function verify(MleProof calldata proof, VerificationConfig calldata config) external view returns (bool) {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);

        _requirePinnedConfiguration(config);
        _requireCanonicalProof(proof, config.circuit);

        ProofView memory view_ = _viewFromAbi(proof, config.circuit);
        _verifyView(view_, config);
        return true;
    }

    /// @notice Verify the canonical `MLEWHIR3` compact encoding against the
    /// pinned configuration supplied as its exact ABI encoding.
    /// @dev `encodedConfig` must be `abi.encode(config)` for the constructor-pinned
    /// configuration: its keccak is compared with `verificationConfigDigest`
    /// before any field is read, after which the bytes are interpreted in place
    /// as the calldata struct. Every compact framing rule (magic, protocol
    /// version, constituent width, trusted vector lengths, stream caps, exact
    /// consumption, canonical limbs, pinned circuit digest and preprocessed
    /// root) is enforced here with `InvalidMleProof`, so a caller that only
    /// authenticates these bytes needs no separate decoder.
    function verifyCompactWithConfig(bytes calldata compactProof, bytes calldata encodedConfig)
        external
        view
        returns (bool)
    {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        if (keccak256(encodedConfig) != verificationConfigDigest) revert InvalidMleVerifierConfiguration();

        // `abi.encode(struct)` is `0x20 || tuple`; a calldata struct pointer
        // addresses the tuple. The digest equality above proves the bytes are
        // exactly the canonical encoding the constructor validated, so every
        // nested offset is well-formed and lies inside `encodedConfig`.
        VerificationConfig calldata config;
        assembly ("memory-safe") {
            config := add(encodedConfig.offset, 0x20)
        }

        ProofView memory view_ = _parseCompact(compactProof, config.circuit);
        _verifyView(view_, config);
        return true;
    }

    /// @notice Classify authenticated canonical ABI proof bytes without letting
    /// malformed decoding, configuration failures, or gas exhaustion convict.
    /// @dev The caller must first authenticate `rawProof` against the submitted
    /// blob. `verifierCallback` must decode `MleProof` and run this
    /// verifier with its own pinned VerificationConfig. Arbitrary callers can
    /// only affect the view result returned to themselves.
    function fraudVerdictEncoded(
        bytes calldata rawProof,
        bytes32 expectedPiHash,
        bytes4 verifierCallback
    ) external view returns (uint8) {
        // Availability containment precedes proof decoding so migrated code or
        // a chain mismatch can never turn malformed bytes into fraud evidence.
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
                // Solidity's decoder emits empty data for malformed offsets and
                // Panic(0x41) for impossible allocations. Both are properties
                // of the authenticated proof bytes, not verifier configuration.
                if (reason.length == 0 || _isMemoryAllocationPanic(reason)) return ENCODED_INVALID;
                return ENCODED_UNEVALUABLE;
            }
        }

        // A canonical old-version tuple is still an invalid v2 proof.
        if (!canonical || proof.protocolVersion != MLE_PROTOCOL_VERSION_CURRENT) return ENCODED_INVALID;
        bool piMatches = _publicInputsMatch(proof.publicInputs, expectedPiHash);

        uint256 verifyReserve = gasleft() / 64;
        uint256 verifyBudget = gasleft() - verifyReserve;
        (bool ok, bytes memory result) =
            msg.sender.staticcall{gas: verifyBudget}(abi.encodeWithSelector(verifierCallback, proof));
        if (ok) {
            if (result.length == 32) {
                uint256 returned;
                assembly ("memory-safe") {
                    returned := mload(add(result, 0x20))
                }
                if (returned == 1) return piMatches ? ENCODED_VALID : ENCODED_PI_MISMATCH;
            }
            return ENCODED_UNEVALUABLE;
        }
        if (_isInvalidMleProof(result)) return ENCODED_INVALID;
        if (gasleft() < verifyReserve + verifyBudget / 8) return ENCODED_STARVED;
        return ENCODED_UNEVALUABLE;
    }

    /// @notice Decode a raw ABI-encoded MleProof and test its unique canonical
    /// encoding. External only so the classifier can catch decoder failures.
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
        uint256 hash = uint256(piHash);
        for (uint256 i = 0; i < 8; ++i) {
            if (publicInputs[i] != ((hash >> (224 - i * 32)) & 0xffffffff)) return false;
        }
        return true;
    }

    function _isInvalidMleProof(bytes memory reason) private pure returns (bool yes) {
        if (reason.length != 4) return false;
        bytes4 selector;
        assembly ("memory-safe") {
            selector := mload(add(reason, 0x20))
        }
        return selector == InvalidMleProof.selector;
    }

    function _isMemoryAllocationPanic(bytes memory reason) private pure returns (bool yes) {
        assembly ("memory-safe") {
            yes := and(
                eq(mload(reason), 36),
                and(eq(mload(add(reason, 0x20)), shl(224, 0x4e487b71)), eq(mload(add(reason, 0x24)), 0x41))
            )
        }
    }

    // ------------------------------------------------------------------ pipeline

    /// @dev The complete atomic statement over one shape-checked, canonical view.
    function _verifyView(ProofView memory view_, VerificationConfig calldata config) private view {
        CircuitConfigV2.Parameters calldata circuit = config.circuit;
        uint256 width = _constituentWidth(circuit);
        uint256 indexBits = _constituentIndexBits(width);
        DerivedState memory derived = _deriveInitialTranscript(view_, config, width, indexBits);

        OuterLogupExt3Verifier.VerificationKey memory outerVk = OuterLogupExt3Verifier.VerificationKey({
            numVars: circuit.degreeBits,
            gateDegree: circuit.quotientDegreeFactor + 2,
            numConstants: circuit.numConstants,
            numRoutedWires: circuit.numRoutedWires,
            numWires: circuit.numWires,
            kIs: config.kIs,
            subgroupGenPowers: config.subgroupGenPowers,
            publicInputWireMap: config.publicInputWireMap
        });

        GoldilocksExt3.Ext3[] memory logPoint;
        GoldilocksExt3.Ext3[] memory gatePoint;
        GoldilocksExt3.Ext3 memory gateFinalClaim;
        (logPoint, gatePoint, gateFinalClaim) = _runOuter(view_, outerVk, derived);

        GoldilocksExt3.Ext3[][] memory indexPoints = _absorbClaimsAndSampleIndices(derived.transcript, view_, indexBits);
        (GoldilocksExt3.Ext3[] memory evaluations, bytes memory evaluationMask) = PackedClaimExt3
            .foldV2UsedCellsFlatPrevalidatedInternal(
            view_.logPreprocessed,
            view_.logWitness,
            view_.logNormInverse,
            view_.gatePreprocessed,
            view_.gateWitness,
            uint256(1) << indexBits,
            indexPoints
        );
        if (
            evaluations.length != NUM_PCS_CLAIMS_V2 || evaluationMask.length != 1
                || evaluationMask[0] != PACKED_BOUND_CLAIM_MASK_V2
        ) revert InvalidMleVerifierConfiguration();

        SpongefishWhirVerify.WhirParams memory whir = config.whir;
        whir.evaluationPoint = _packedPoint(logPoint, indexPoints[0]);
        whir.evaluationPoint2 = _packedPoint(gatePoint, indexPoints[1]);
        whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        bytes32[] memory roots = new bytes32[](NUM_PCS_GROUPS_V2);
        roots[0] = view_.preprocessedRoot;
        roots[1] = view_.witnessRoot;
        roots[2] = view_.normInverseRoot;
        bytes calldata hints = _hintsSlice(view_);
        bool whirAccepted = SpongefishWhirVerify.verifyWhirProofBound(
            _protocolId(),
            abi.encodePacked(whirSessionId),
            "",
            view_.whirTranscript,
            hints,
            evaluations,
            evaluationMask,
            roots,
            whir
        );
        if (!whirAccepted) revert InvalidMleProof();

        uint256[4] memory publicInputsHash = PoseidonPublicInputsHash.hashNoPad(view_.publicInputs);
        GoldilocksExt3.Ext3 memory gateEvaluation = Plonky2GateEvaluatorExt3.evalCombinedPrevalidated(
            _pointerTable(view_.gateWitness, circuit.numWires),
            _pointerTable(view_.gatePreprocessed, circuit.numConstants),
            publicInputsHash,
            derived.gateAlpha,
            config.gates,
            circuit.numSelectors
        );
        OuterLogupExt3Verifier.verifyGateTerminal(derived.gateTau, gatePoint, gateEvaluation, gateFinalClaim);
    }

    /// @dev Coupled outer sumchecks and the norm/logUp terminal over the flat
    /// buffers. TEMPORARY ADAPTER: builds pointer-table views for the current
    /// `verifyPrevalidated` entry; replaced by `verifyPrevalidatedFlat`.
    function _runOuter(
        ProofView memory view_,
        OuterLogupExt3Verifier.VerificationKey memory outerVk,
        DerivedState memory derived
    )
        private
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim
        )
    {
        OuterLogupExt3Verifier.SumcheckProof memory logProof =
            _sumcheckView(view_.logRounds, outerVk.numVars, LOG_ROUND_DEGREE_V2);
        OuterLogupExt3Verifier.SumcheckProof memory gateProof =
            _sumcheckView(view_.gateRounds, outerVk.numVars, outerVk.gateDegree);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = OuterLogupExt3Verifier.TerminalEvaluations({
            preprocessed: _pointerTable(view_.logPreprocessed, view_.logPreprocessed.length / 3),
            witness: _pointerTable(view_.logWitness, view_.logWitness.length / 3),
            normInverse: _pointerTable(view_.logNormInverse, view_.logNormInverse.length / 3),
            publicInputs: view_.publicInputs
        });
        (logPoint, gatePoint, gateFinalClaim, derived.transcript) = OuterLogupExt3Verifier.verifyPrevalidated(
            logProof, gateProof, outerVk, derived.logChallenges, terminal, derived.transcript
        );
    }

    function _sumcheckView(uint256[] memory limbs, uint256 rounds, uint256 degree)
        private
        pure
        returns (OuterLogupExt3Verifier.SumcheckProof memory proof)
    {
        if (limbs.length != 3 * rounds * degree) revert InvalidMleProof();
        proof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](rounds);
        for (uint256 round = 0; round < rounds; ++round) {
            GoldilocksExt3.Ext3[] memory table;
            assembly ("memory-safe") {
                table := mload(0x40)
                mstore(table, degree)
                let entries := add(table, 0x20)
                let record := add(add(limbs, 0x20), mul(mul(round, degree), 0x60))
                for { let i := 0 } lt(i, degree) { i := add(i, 1) } {
                    mstore(add(entries, shl(5, i)), record)
                    record := add(record, 0x60)
                }
                mstore(0x40, add(entries, shl(5, degree)))
            }
            proof.rounds[round].nonConstant = table;
        }
    }

    function _deriveInitialTranscript(
        ProofView memory view_,
        VerificationConfig calldata config,
        uint256 width,
        uint256 indexBits
    ) private view returns (DerivedState memory derived) {
        TranscriptV2.Transcript memory transcript = derived.transcript;
        TranscriptV2.init(transcript);
        TranscriptV2.domainSeparate(transcript, DOMAIN_CIRCUIT_STATEMENT_V2);
        // The view's digest was compared against the pinned one, so the pinned
        // values are the exact absorbed statement.
        TranscriptV2.absorbFieldVecPrevalidated(
            transcript, _digestVector([circuitDigest0, circuitDigest1, circuitDigest2, circuitDigest3])
        );
        TranscriptV2.absorbFieldVecPrevalidated(transcript, view_.publicInputs);

        TranscriptV2.domainSeparate(transcript, PACKED_PCS_SCHEMA_DOMAIN_V2);
        TranscriptV2.absorbBytes(transcript, _schemaMetadata(config.circuit, width, indexBits));

        TranscriptV2.domainSeparate(transcript, DOMAIN_CIRCUIT_CONFIG_DIGEST_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(circuitConfigDigest));
        TranscriptV2.bindWhirIdentifiers(transcript, _protocolId(), abi.encodePacked(whirSessionId));
        TranscriptV2.domainSeparate(transcript, DOMAIN_GROUP_PREPROCESSED_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(view_.preprocessedRoot));
        TranscriptV2.domainSeparate(transcript, DOMAIN_GROUP_WITNESS_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(view_.witnessRoot));

        TranscriptV2.domainSeparate(transcript, DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.eta);

        TranscriptV2.domainSeparate(transcript, DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.beta);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.gamma);
        TranscriptV2.domainSeparate(transcript, DOMAIN_GROUP_NORM_INVERSE_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(view_.normInverseRoot));

        TranscriptV2.domainSeparate(transcript, DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.xi);

        TranscriptV2.domainSeparate(transcript, DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.lambda);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.rho);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.kappa);
        derived.logChallenges.tau = _squeezeExt3Vector(transcript, config.circuit.degreeBits);
        TranscriptV2.squeezeExt3Into(transcript, derived.gateAlpha);
        derived.gateTau = _squeezeExt3Vector(transcript, config.circuit.degreeBits);
    }

    /// @dev The fifteen little-endian u64 schema fields absorbed under
    /// `PACKED_PCS_SCHEMA_DOMAIN_V2`, in the reviewed wire-v3 order.
    function _schemaMetadata(CircuitConfigV2.Parameters calldata circuit, uint256 width, uint256 indexBits)
        private
        pure
        returns (bytes memory metadata)
    {
        uint256[15] memory fields = [
            MLE_PROTOCOL_VERSION_CURRENT,
            NUM_PCS_GROUPS_V2,
            NUM_PCS_TERMINAL_POINTS_V2,
            NUM_PCS_CLAIMS_V2,
            circuit.numConstants,
            circuit.numRoutedWires,
            circuit.numWires,
            circuit.degreeBits,
            width,
            indexBits,
            NUM_PACKED_VECTORS_PER_GROUP_V2,
            EXTENSION_FIELD_LIMBS_V2,
            PACKED_VARIABLE_ORDER_CODE_V2,
            GATE_SUMCHECK_COUNT_V2,
            LOG_ROUND_DEGREE_V2
        ];
        metadata = new bytes(15 * 8 + 24);
        assembly ("memory-safe") {
            mstore(metadata, 120)
            let dst := add(metadata, 0x20)
            for { let i := 0 } lt(i, 15) { i := add(i, 1) } {
                let value := mload(add(fields, shl(5, i)))
                if gt(value, 0xFFFFFFFFFFFFFFFF) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                // 8 little-endian bytes; the 24 trailing zero bytes of each store
                // are overwritten by the next field or land in the slack region.
                mstore(add(dst, mul(i, 8)), shl(192, bswap64(value)))
            }
            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
    }

    function _absorbClaimsAndSampleIndices(
        TranscriptV2.Transcript memory transcript,
        ProofView memory view_,
        uint256 indexBits
    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_CLAIMS_V2);
        if (view_.logClaimsOffset != 0) {
            // Compact path: the five vectors are exactly the little-endian wire
            // records whose decoded, canonical limbs fill the flat buffers below.
            uint256 offset = view_.logClaimsOffset;
            uint256 count = view_.logPreprocessed.length / 3;
            TranscriptV2.absorbExt3VecCalldataPrevalidated(transcript, offset, count);
            offset += 24 * count;
            count = view_.logWitness.length / 3;
            TranscriptV2.absorbExt3VecCalldataPrevalidated(transcript, offset, count);
            offset += 24 * count;
            TranscriptV2.absorbExt3VecCalldataPrevalidated(transcript, offset, view_.logNormInverse.length / 3);
            offset = view_.gateClaimsOffset;
            count = view_.gatePreprocessed.length / 3;
            TranscriptV2.absorbExt3VecCalldataPrevalidated(transcript, offset, count);
            offset += 24 * count;
            TranscriptV2.absorbExt3VecCalldataPrevalidated(transcript, offset, view_.gateWitness.length / 3);
        } else {
            TranscriptV2.absorbExt3VecFlatPrevalidated(transcript, view_.logPreprocessed);
            TranscriptV2.absorbExt3VecFlatPrevalidated(transcript, view_.logWitness);
            TranscriptV2.absorbExt3VecFlatPrevalidated(transcript, view_.logNormInverse);
            TranscriptV2.absorbExt3VecFlatPrevalidated(transcript, view_.gatePreprocessed);
            TranscriptV2.absorbExt3VecFlatPrevalidated(transcript, view_.gateWitness);
        }
        TranscriptV2.absorbExt3Vec(transcript, new GoldilocksExt3.Ext3[](0));
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_INDEX_V2);

        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < points.length; ++point) {
            points[point] = _squeezeExt3Vector(transcript, indexBits);
        }
    }

    // ------------------------------------------------------------------ compact parsing

    /// @dev Parse the canonical `MLEWHIR3` encoding into a `ProofView`. Every
    /// vector length is derived from the pinned circuit; only the two opaque
    /// WHIR streams carry a length prefix. All integers are little-endian. Any
    /// framing, cap, pin or canonical-limb violation is `InvalidMleProof`.
    function _parseCompact(bytes calldata compact, CircuitConfigV2.Parameters calldata circuit)
        private
        view
        returns (ProofView memory view_)
    {
        uint256 length = compact.length;
        if (length > MAX_COMPACT_PROOF_BYTES_V2 || length < 8 + 8 + 4 + 32) revert InvalidMleProof();
        uint256 base;
        bytes8 magic;
        uint256 protocolVersion;
        uint256 constituentWidth;
        assembly ("memory-safe") {
            base := compact.offset
            magic := calldataload(base)
            protocolVersion := bswap64(shr(192, calldataload(add(base, 8))))
            constituentWidth := and(bswap64(shr(192, calldataload(add(base, 16)))), 0xFFFFFFFF)
            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
        if (magic != COMPACT_MAGIC_V2 || protocolVersion != MLE_PROTOCOL_VERSION_CURRENT) revert InvalidMleProof();
        if (constituentWidth != _constituentWidth(circuit)) revert InvalidMleProof();

        // Circuit digest: four little-endian limbs that must equal the pinned
        // (canonical) digest exactly.
        uint256[] memory digest = _readBaseVectorLe(base + 20, CIRCUIT_DIGEST_LENGTH_V2, false);
        if (
            digest[0] != circuitDigest0 || digest[1] != circuitDigest1 || digest[2] != circuitDigest2
                || digest[3] != circuitDigest3
        ) revert InvalidMleProof();

        uint256 numPublicInputs = circuit.numPublicInputs;
        if (numPublicInputs > MAX_PUBLIC_INPUTS_V2) revert InvalidMleVerifierConfiguration();
        uint256 position = 52;
        if (length - position < 8 * numPublicInputs + 96 + 8) revert InvalidMleProof();
        view_.publicInputs = _readBaseVectorLe(base + position, numPublicInputs, true);
        position += 8 * numPublicInputs;

        bytes32 preprocessedRoot;
        bytes32 witnessRoot;
        bytes32 normInverseRoot;
        uint256 transcriptLength;
        assembly ("memory-safe") {
            let p := add(base, position)
            preprocessedRoot := calldataload(p)
            witnessRoot := calldataload(add(p, 32))
            normInverseRoot := calldataload(add(p, 64))
            transcriptLength := readU32(add(p, 96))
            function readU32(ptr) -> v {
                let w := calldataload(ptr)
                v := or(or(byte(0, w), shl(8, byte(1, w))), or(shl(16, byte(2, w)), shl(24, byte(3, w))))
            }
        }
        if (preprocessedRoot != preprocessedCommitmentRoot) revert InvalidMleProof();
        view_.preprocessedRoot = preprocessedRoot;
        view_.witnessRoot = witnessRoot;
        view_.normInverseRoot = normInverseRoot;
        position += 100;

        if (transcriptLength > MAX_WHIR_NARG_BYTES_V2 || length - position < transcriptLength + 4) {
            revert InvalidMleProof();
        }
        bytes memory whirTranscript = new bytes(transcriptLength);
        uint256 hintsLength;
        assembly ("memory-safe") {
            calldatacopy(add(whirTranscript, 0x20), add(base, position), transcriptLength)
            let w := calldataload(add(base, add(position, transcriptLength)))
            hintsLength := or(or(byte(0, w), shl(8, byte(1, w))), or(shl(16, byte(2, w)), shl(24, byte(3, w))))
        }
        view_.whirTranscript = whirTranscript;
        position += transcriptLength + 4;
        if (hintsLength > MAX_WHIR_HINT_BYTES_V2 || length - position < hintsLength) revert InvalidMleProof();
        view_.hintsOffset = base + position;
        view_.hintsLength = hintsLength;
        position += hintsLength;

        // Fixed-length Ext3 vectors: every count comes from the pinned circuit and
        // the remaining byte count must be consumed exactly.
        uint256 degreeBits = circuit.degreeBits;
        uint256 preprocessedLength = circuit.numConstants + circuit.numRoutedWires;
        uint256 numWires = circuit.numWires;
        uint256 normInverseLength = 2 * circuit.numRoutedWires;
        uint256 gateDegree = circuit.quotientDegreeFactor + 2;
        uint256 totalRecords = degreeBits * LOG_ROUND_DEGREE_V2 + 2 * preprocessedLength + 2 * numWires
            + normInverseLength + degreeBits * gateDegree;
        if (length - position != 24 * totalRecords) revert InvalidMleProof();

        uint256 cursor = base + position;
        view_.logRounds = _readExt3VectorLe(cursor, degreeBits * LOG_ROUND_DEGREE_V2);
        cursor += 24 * degreeBits * LOG_ROUND_DEGREE_V2;
        view_.logClaimsOffset = cursor;
        view_.logPreprocessed = _readExt3VectorLe(cursor, preprocessedLength);
        cursor += 24 * preprocessedLength;
        view_.logWitness = _readExt3VectorLe(cursor, numWires);
        cursor += 24 * numWires;
        view_.logNormInverse = _readExt3VectorLe(cursor, normInverseLength);
        cursor += 24 * normInverseLength;
        view_.gateRounds = _readExt3VectorLe(cursor, degreeBits * gateDegree);
        cursor += 24 * degreeBits * gateDegree;
        view_.gateClaimsOffset = cursor;
        view_.gatePreprocessed = _readExt3VectorLe(cursor, preprocessedLength);
        cursor += 24 * preprocessedLength;
        view_.gateWitness = _readExt3VectorLe(cursor, numWires);
    }

    /// @dev Read `count` little-endian u64 base-field elements from calldata into
    /// a word array, rejecting any limb `>= p` when `canonical` is set. The
    /// caller has bounded `[offset, offset + 8 * count)` inside the proof bytes.
    function _readBaseVectorLe(uint256 offset, uint256 count, bool canonical)
        private
        pure
        returns (uint256[] memory values)
    {
        assembly ("memory-safe") {
            values := mload(0x40)
            mstore(values, count)
            let output := add(values, 0x20)
            let p := 0xFFFFFFFF00000001
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let value := bswap64(shr(192, calldataload(add(offset, mul(i, 8)))))
                if and(canonical, iszero(lt(value, p))) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                mstore(add(output, shl(5, i)), value)
            }
            mstore(0x40, add(output, shl(5, count)))
            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
    }

    /// @dev Read `count` Ext3 wire records (24 little-endian bytes each) from
    /// calldata into a flat limb buffer of `3 * count` canonical words,
    /// rejecting any limb `>= p`. The caller has bounded the calldata range and
    /// `count <= MAX_CONSTITUENT_WIDTH_V2 * MAX_GATE_ROUND_DEGREE_V2`-scale
    /// dimensions, so `0x20 + 0x60 * count` cannot overflow.
    function _readExt3VectorLe(uint256 offset, uint256 count) private pure returns (uint256[] memory limbs) {
        assembly ("memory-safe") {
            limbs := mload(0x40)
            mstore(limbs, mul(count, 3))
            let output := add(limbs, 0x20)
            let p := 0xFFFFFFFF00000001
            let end := add(offset, mul(count, 24))
            for {} lt(offset, end) { offset := add(offset, 24) } {
                // One 32-byte load covers the whole record; the last 8 bytes are
                // the next record's first limb and are ignored here.
                let word := calldataload(offset)
                let c0 := bswap64(shr(192, word))
                let c1 := bswap64(and(shr(128, word), 0xFFFFFFFFFFFFFFFF))
                let c2 := bswap64(and(shr(64, word), 0xFFFFFFFFFFFFFFFF))
                if iszero(and(and(lt(c0, p), lt(c1, p)), lt(c2, p))) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                mstore(output, c0)
                mstore(add(output, 0x20), c1)
                mstore(add(output, 0x40), c2)
                output := add(output, 0x60)
            }
            mstore(0x40, output)
            function bswap64(x) -> y {
                y := or(shl(32, and(x, 0xFFFFFFFF)), shr(32, and(x, 0xFFFFFFFF00000000)))
                y := or(shl(16, and(y, 0x0000FFFF0000FFFF)), shr(16, and(y, 0xFFFF0000FFFF0000)))
                y := or(shl(8, and(y, 0x00FF00FF00FF00FF)), shr(8, and(y, 0xFF00FF00FF00FF00)))
            }
        }
    }

    // ------------------------------------------------------------------ typed ABI proof

    function _requirePinnedConfiguration(VerificationConfig calldata config) private view {
        // The constructor performed the complete cap, circuit/VK, gate and
        // WHIR validation before pinning this canonical typed encoding. A
        // single full-struct digest therefore proves that every runtime field
        // is exactly the already-reviewed deployment value; re-running the
        // nested validation and two partial digests on every proof only burns
        // gas and cannot strengthen that equality check.
        if (keccak256(abi.encode(config)) != verificationConfigDigest) {
            revert InvalidMleVerifierConfiguration();
        }
    }

    function _requireCanonicalProof(MleProof calldata proof, CircuitConfigV2.Parameters calldata circuit)
        private
        view
    {
        if (proof.protocolVersion != MLE_PROTOCOL_VERSION_CURRENT) revert InvalidMleProof();
        if (proof.circuitDigest.length != CIRCUIT_DIGEST_LENGTH_V2) revert InvalidMleProof();
        if (
            proof.circuitDigest[0] != circuitDigest0 || proof.circuitDigest[1] != circuitDigest1
                || proof.circuitDigest[2] != circuitDigest2 || proof.circuitDigest[3] != circuitDigest3
        ) revert InvalidMleProof();
        if (proof.publicInputs.length != circuit.numPublicInputs) revert InvalidMleProof();
        if (proof.preprocessedRoot != preprocessedCommitmentRoot) revert InvalidMleProof();
        if (proof.whirTranscript.length > MAX_WHIR_NARG_BYTES_V2 || proof.whirHints.length > MAX_WHIR_HINT_BYTES_V2) {
            revert InvalidMleProof();
        }
        if (proof.constituentWidth != _constituentWidth(circuit)) revert InvalidMleProof();

        uint256 preprocessedLength = circuit.numConstants + circuit.numRoutedWires;
        uint256 normInverseLength = 2 * circuit.numRoutedWires;
        if (
            proof.logPreprocessed.length != preprocessedLength || proof.logWitness.length != circuit.numWires
                || proof.logNormInverse.length != normInverseLength
                || proof.gatePreprocessed.length != preprocessedLength || proof.gateWitness.length != circuit.numWires
        ) revert InvalidMleProof();
        if (proof.logProof.rounds.length != circuit.degreeBits || proof.gateProof.rounds.length != circuit.degreeBits) {
            revert InvalidMleProof();
        }
        uint256 gateDegree = circuit.quotientDegreeFactor + 2;
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            if (
                proof.logProof.rounds[round].nonConstant.length != LOG_ROUND_DEGREE_V2
                    || proof.gateProof.rounds[round].nonConstant.length != gateDegree
            ) revert InvalidMleProof();
        }
    }

    /// @dev Build the pipeline view of a shape-checked typed proof, canonicalizing
    /// every limb while flattening it.
    function _viewFromAbi(MleProof calldata proof, CircuitConfigV2.Parameters calldata circuit)
        private
        pure
        returns (ProofView memory view_)
    {
        view_.publicInputs = _copyCanonicalBase(proof.publicInputs);
        view_.preprocessedRoot = proof.preprocessedRoot;
        view_.witnessRoot = proof.witnessRoot;
        view_.normInverseRoot = proof.normInverseRoot;
        view_.whirTranscript = proof.whirTranscript;
        bytes calldata hints = proof.whirHints;
        uint256 hintsOffset;
        assembly ("memory-safe") {
            hintsOffset := hints.offset
        }
        view_.hintsOffset = hintsOffset;
        view_.hintsLength = hints.length;
        view_.logRounds = _flattenSumcheck(proof.logProof, LOG_ROUND_DEGREE_V2);
        view_.gateRounds = _flattenSumcheck(proof.gateProof, circuit.quotientDegreeFactor + 2);
        view_.logPreprocessed = _flattenCanonicalExt3(proof.logPreprocessed);
        view_.logWitness = _flattenCanonicalExt3(proof.logWitness);
        view_.logNormInverse = _flattenCanonicalExt3(proof.logNormInverse);
        view_.gatePreprocessed = _flattenCanonicalExt3(proof.gatePreprocessed);
        view_.gateWitness = _flattenCanonicalExt3(proof.gateWitness);
    }

    /// @dev Fuse the proof-boundary canonical check with the unavoidable
    /// calldata-to-memory copy into a flat limb buffer.
    function _flattenCanonicalExt3(GoldilocksExt3.Ext3[] calldata source)
        private
        pure
        returns (uint256[] memory limbs)
    {
        uint256 count = source.length;
        // Every caller reaches this helper only after `_requireCanonicalProof`
        // has matched an exact protocol vector length. Keep the independent cap
        // here as a local proof for the Yul arithmetic below.
        if (count > MAX_CONSTITUENT_WIDTH_V2) revert InvalidMleProof();
        assembly ("memory-safe") {
            limbs := mload(0x40)
            mstore(limbs, mul(count, 3))
            let output := add(limbs, 0x20)
            let input := source.offset
            let end := add(input, mul(count, 0x60))
            let p := 0xFFFFFFFF00000001
            for {} lt(input, end) {
                input := add(input, 0x60)
                output := add(output, 0x60)
            } {
                let c0 := calldataload(input)
                let c1 := calldataload(add(input, 0x20))
                let c2 := calldataload(add(input, 0x40))
                if iszero(and(and(lt(c0, p), lt(c1, p)), lt(c2, p))) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                mstore(output, c0)
                mstore(add(output, 0x20), c1)
                mstore(add(output, 0x40), c2)
            }
            mstore(0x40, output)
        }
    }

    /// @dev Concatenate the per-round coefficient vectors (each exactly `degree`
    /// records, as established by `_requireCanonicalProof`) into one canonical
    /// flat buffer, round-major then coefficient-major.
    function _flattenSumcheck(OuterLogupExt3Verifier.SumcheckProof calldata source, uint256 degree)
        private
        pure
        returns (uint256[] memory limbs)
    {
        uint256 rounds = source.rounds.length;
        if (rounds > MAX_ROW_VARIABLES_V2 || degree > MAX_GATE_ROUND_DEGREE_V2) revert InvalidMleProof();
        limbs = new uint256[](3 * rounds * degree);
        uint256 write;
        for (uint256 round = 0; round < rounds; ++round) {
            GoldilocksExt3.Ext3[] calldata coefficients = source.rounds[round].nonConstant;
            if (coefficients.length != degree) revert InvalidMleProof();
            assembly ("memory-safe") {
                let output := add(add(limbs, 0x20), write)
                let input := coefficients.offset
                let end := add(input, mul(degree, 0x60))
                let p := 0xFFFFFFFF00000001
                for {} lt(input, end) {
                    input := add(input, 0x60)
                    output := add(output, 0x60)
                } {
                    let c0 := calldataload(input)
                    let c1 := calldataload(add(input, 0x20))
                    let c2 := calldataload(add(input, 0x40))
                    if iszero(and(and(lt(c0, p), lt(c1, p)), lt(c2, p))) {
                        mstore(0x00, shl(224, 0xf0783a66))
                        revert(0x00, 0x04)
                    }
                    mstore(output, c0)
                    mstore(add(output, 0x20), c1)
                    mstore(add(output, 0x40), c2)
                }
            }
            write += degree * 0x60;
        }
    }

    function _copyCanonicalBase(uint256[] calldata source) private pure returns (uint256[] memory values) {
        uint256 count = source.length;
        // The pinned circuit already imposes this bound; repeat it next to the
        // pointer arithmetic so a future private call site cannot invalidate
        // the allocation/read proof.
        if (count > MAX_PUBLIC_INPUTS_V2) revert InvalidMleProof();
        values = new uint256[](count);
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let input := source.offset
            let output := add(values, 0x20)
            let end := add(input, mul(count, 0x20))
            for {} lt(input, end) {
                input := add(input, 0x20)
                output := add(output, 0x20)
            } {
                let value := calldataload(input)
                if iszero(lt(value, p)) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                mstore(output, value)
            }
        }
    }

    // ------------------------------------------------------------------ helpers

    /// @dev View the first `count` elements of a flat limb buffer as an ordinary
    /// `Ext3[]` (a pointer table whose entries address three consecutive words
    /// of the buffer). No limb is copied.
    function _pointerTable(uint256[] memory limbs, uint256 count)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory table)
    {
        if (3 * count > limbs.length) revert InvalidMleProof();
        assembly ("memory-safe") {
            table := mload(0x40)
            mstore(table, count)
            let entries := add(table, 0x20)
            let record := add(limbs, 0x20)
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                mstore(add(entries, shl(5, i)), record)
                record := add(record, 0x60)
            }
            mstore(0x40, add(entries, shl(5, count)))
        }
    }

    function _hintsSlice(ProofView memory view_) private pure returns (bytes calldata hints) {
        uint256 offset = view_.hintsOffset;
        uint256 length = view_.hintsLength;
        assembly ("memory-safe") {
            hints.offset := offset
            hints.length := length
        }
    }

    function _squeezeExt3Vector(TranscriptV2.Transcript memory transcript, uint256 length)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        values = new GoldilocksExt3.Ext3[](length);
        for (uint256 i = 0; i < length; ++i) {
            TranscriptV2.squeezeExt3Into(transcript, values[i]);
        }
    }

    function _packedPoint(GoldilocksExt3.Ext3[] memory row, GoldilocksExt3.Ext3[] memory index)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory point)
    {
        point = new GoldilocksExt3.Ext3[](row.length + index.length);
        // Dense MLEs bind variables LSB-first as `[row, index]`, while WHIR's
        // `MultilinearExtension` consumes the complete point in the opposite
        // coordinate order. Reverse the full concatenation here; the separate
        // PackedClaimExt3 fold above deliberately keeps `index` LSB-first.
        for (uint256 i = 0; i < index.length; ++i) {
            point[i] = index[index.length - 1 - i];
        }
        for (uint256 i = 0; i < row.length; ++i) {
            point[index.length + i] = row[row.length - 1 - i];
        }
    }

    function _validateConfiguration(VerificationConfig memory config, uint64[4] memory digest) private pure {
        CircuitConfigV2.Parameters memory circuit = config.circuit;
        if (
            circuit.degreeBits == 0 || circuit.degreeBits > MAX_ROW_VARIABLES_V2
                || circuit.numPublicInputs > MAX_PUBLIC_INPUTS_V2 || circuit.numConstants > MAX_CONSTITUENT_WIDTH_V2
                || circuit.numRoutedWires > MAX_ROUTED_WIRES_V2 || circuit.numWires > MAX_CONSTITUENT_WIDTH_V2
                || circuit.numRoutedWires > circuit.numWires
                || circuit.numConstants > MAX_CONSTITUENT_WIDTH_V2 - circuit.numRoutedWires || circuit.numSelectors == 0
                || circuit.numSelectors > circuit.numConstants || circuit.numGateConstraints > MAX_GATE_CONSTRAINTS_V2
                || circuit.quotientDegreeFactor == 0 || circuit.quotientDegreeFactor > MAX_GATE_ROUND_DEGREE_V2 - 2
                || config.kIs.length != circuit.numRoutedWires || config.subgroupGenPowers.length != circuit.degreeBits
                || config.gates.length == 0 || config.gates.length > MAX_GATE_ROWS_V2
        ) revert InvalidMleVerifierConfiguration();
        if (
            circuit.numPublicInputs > type(uint256).max / 3
                || config.publicInputWireMap.length != 3 * circuit.numPublicInputs
        ) revert InvalidMleVerifierConfiguration();
        uint256 degree = uint256(1) << circuit.degreeBits;
        for (uint256 offset = 0; offset < config.publicInputWireMap.length; offset += 3) {
            uint256 row = uint8(config.publicInputWireMap[offset])
                | (uint256(uint8(config.publicInputWireMap[offset + 1])) << 8);
            uint256 column = uint8(config.publicInputWireMap[offset + 2]);
            if (row >= degree || column >= circuit.numRoutedWires) revert InvalidMleVerifierConfiguration();
        }
        for (uint256 i = 0; i < digest.length; ++i) {
            if (uint256(digest[i]) >= BASE_FIELD_MODULUS_V2) revert InvalidMleVerifierConfiguration();
        }
        if (
            config.whir.numCommitments != NUM_PCS_GROUPS_V2 || config.whir.numVectors != NUM_PACKED_VECTORS_PER_GROUP_V2
                || config.whir.evaluationPoint.length != 0 || config.whir.evaluationPoint2.length != 0
                || config.whir.additionalEvaluationPoints.length != 0
                || config.whir.rounds.length > MAX_ROW_VARIABLES_V2
        ) revert InvalidMleVerifierConfiguration();
        uint256 width = _constituentWidthMemory(circuit);
        if (config.whir.numVariables != circuit.degreeBits + _constituentIndexBits(width)) {
            revert InvalidMleVerifierConfiguration();
        }
        uint256 expectedCosetShift = 1;
        for (uint256 i = 0; i < config.kIs.length; ++i) {
            if (config.kIs[i] != expectedCosetShift) revert InvalidMleVerifierConfiguration();
            expectedCosetShift =
                mulmod(expectedCosetShift, BASE_FIELD_MULTIPLICATIVE_GENERATOR_V2, BASE_FIELD_MODULUS_V2);
        }

        uint256 expectedSubgroupGenerator = BASE_FIELD_POWER_OF_TWO_GENERATOR_V2;
        for (uint256 bits = circuit.degreeBits; bits < BASE_FIELD_TWO_ADICITY_V2; ++bits) {
            expectedSubgroupGenerator =
                mulmod(expectedSubgroupGenerator, expectedSubgroupGenerator, BASE_FIELD_MODULUS_V2);
        }
        for (uint256 i = 0; i < config.subgroupGenPowers.length; ++i) {
            if (config.subgroupGenPowers[i] != expectedSubgroupGenerator) {
                revert InvalidMleVerifierConfiguration();
            }
            expectedSubgroupGenerator =
                mulmod(expectedSubgroupGenerator, expectedSubgroupGenerator, BASE_FIELD_MODULUS_V2);
        }
        if (config.subgroupGenPowers[config.subgroupGenPowers.length - 1] != BASE_FIELD_MODULUS_V2 - 1) {
            revert InvalidMleVerifierConfiguration();
        }
    }

    function _constituentWidth(CircuitConfigV2.Parameters calldata circuit) private pure returns (uint256 width) {
        width = circuit.numConstants + circuit.numRoutedWires;
        if (circuit.numWires > width) width = circuit.numWires;
        uint256 normInverseLength = 2 * circuit.numRoutedWires;
        if (normInverseLength > width) width = normInverseLength;
    }

    function _constituentWidthMemory(CircuitConfigV2.Parameters memory circuit) private pure returns (uint256 width) {
        width = circuit.numConstants + circuit.numRoutedWires;
        if (circuit.numWires > width) width = circuit.numWires;
        uint256 normInverseLength = 2 * circuit.numRoutedWires;
        if (normInverseLength > width) width = normInverseLength;
    }

    function _constituentIndexBits(uint256 width) private pure returns (uint256 bits) {
        if (width == 0 || width > MAX_CONSTITUENT_WIDTH_V2) revert InvalidMleVerifierConfiguration();
        uint256 capacity = 1;
        while (capacity < width) {
            capacity <<= 1;
            ++bits;
        }
        if (bits > MAX_CONSTITUENT_INDEX_BITS_V2) revert InvalidMleVerifierConfiguration();
    }

    function _digestVector(uint64[4] memory digest) private pure returns (uint256[] memory values) {
        values = new uint256[](CIRCUIT_DIGEST_LENGTH_V2);
        for (uint256 i = 0; i < values.length; ++i) {
            values[i] = digest[i];
        }
    }

    function _protocolId() private view returns (bytes memory) {
        return abi.encodePacked(whirProtocolIdFirst, whirProtocolIdSecond);
    }
}
