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

    struct DerivedState {
        TranscriptV2.Transcript transcript;
        OuterLogupExt3Verifier.Challenges logChallenges;
        GoldilocksExt3.Ext3 gateAlpha;
        GoldilocksExt3.Ext3[] gateTau;
        uint256[] publicInputs;
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
        uint256 width = _requireCanonicalProof(proof, config.circuit);

        _verifyAtomic(proof, config, width);
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

    function _verifyAtomic(MleProof calldata proof, VerificationConfig calldata config, uint256 width) private view {
        uint256 indexBits = _constituentIndexBits(width);
        DerivedState memory derived = _deriveInitialTranscript(proof, config, width, indexBits);

        // Only the five vectors used by both the packed fold and later
        // terminal/gate checks need a persistent memory representation. Keep
        // the large WHIR byte strings and sumcheck records in calldata until
        // their single consumer instead of deep-copying the entire proof.
        PackedClaimExt3.UsedClaims memory usedClaims = PackedClaimExt3.UsedClaims({
            logPreprocessed: _copyCanonicalExt3(proof.logPreprocessed),
            logWitness: _copyCanonicalExt3(proof.logWitness),
            logNormInverse: _copyCanonicalExt3(proof.logNormInverse),
            gatePreprocessed: _copyCanonicalExt3(proof.gatePreprocessed),
            gateWitness: _copyCanonicalExt3(proof.gateWitness)
        });
        uint256[] memory kIs = config.kIs;
        uint256[] memory subgroupGenPowers = config.subgroupGenPowers;

        OuterLogupExt3Verifier.VerificationKey memory outerVk = OuterLogupExt3Verifier.VerificationKey({
            numVars: config.circuit.degreeBits,
            gateDegree: config.circuit.quotientDegreeFactor + 2,
            numConstants: config.circuit.numConstants,
            numRoutedWires: config.circuit.numRoutedWires,
            numWires: config.circuit.numWires,
            kIs: kIs,
            subgroupGenPowers: subgroupGenPowers,
            publicInputWireMap: config.publicInputWireMap
        });
        OuterLogupExt3Verifier.TerminalEvaluations memory logTerminal = OuterLogupExt3Verifier.TerminalEvaluations({
            preprocessed: usedClaims.logPreprocessed,
            witness: usedClaims.logWitness,
            normInverse: usedClaims.logNormInverse,
            publicInputs: derived.publicInputs
        });

        OuterLogupExt3Verifier.SumcheckProof memory logProof = _copyCanonicalSumcheck(proof.logProof);
        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _copyCanonicalSumcheck(proof.gateProof);

        GoldilocksExt3.Ext3[] memory logPoint;
        GoldilocksExt3.Ext3[] memory gatePoint;
        GoldilocksExt3.Ext3 memory gateFinalClaim;
        (logPoint, gatePoint, gateFinalClaim, derived.transcript) = OuterLogupExt3Verifier.verifyPrevalidated(
            logProof, gateProof, outerVk, derived.logChallenges, logTerminal, derived.transcript
        );

        GoldilocksExt3.Ext3[][] memory indexPoints =
            _absorbClaimsAndSampleIndices(derived.transcript, usedClaims, indexBits);
        (GoldilocksExt3.Ext3[] memory evaluations, bytes memory evaluationMask) =
            PackedClaimExt3.foldV2UsedCellsPrevalidatedInternal(usedClaims, uint256(1) << indexBits, indexPoints);
        if (
            evaluations.length != NUM_PCS_CLAIMS_V2 || evaluationMask.length != 1
                || evaluationMask[0] != PACKED_BOUND_CLAIM_MASK_V2
        ) revert InvalidMleVerifierConfiguration();

        SpongefishWhirVerify.WhirParams memory whir = config.whir;
        whir.evaluationPoint = _packedPoint(logPoint, indexPoints[0]);
        whir.evaluationPoint2 = _packedPoint(gatePoint, indexPoints[1]);
        whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        bytes32[] memory roots = new bytes32[](NUM_PCS_GROUPS_V2);
        roots[0] = proof.preprocessedRoot;
        roots[1] = proof.witnessRoot;
        roots[2] = proof.normInverseRoot;
        bool whirAccepted = SpongefishWhirVerify.verifyWhirProofBound(
            _protocolId(),
            abi.encodePacked(whirSessionId),
            "",
            proof.whirTranscript,
            proof.whirHints,
            evaluations,
            evaluationMask,
            roots,
            whir
        );
        if (!whirAccepted) revert InvalidMleProof();

        GoldilocksExt3.Ext3[] memory constants = new GoldilocksExt3.Ext3[](config.circuit.numConstants);
        for (uint256 i = 0; i < constants.length; ++i) {
            constants[i] = usedClaims.gatePreprocessed[i];
        }
        uint256[4] memory publicInputsHash = PoseidonPublicInputsHash.hashNoPad(proof.publicInputs);
        GoldilocksExt3.Ext3 memory gateEvaluation = Plonky2GateEvaluatorExt3.evalCombinedPrevalidated(
            usedClaims.gateWitness,
            constants,
            publicInputsHash,
            derived.gateAlpha,
            config.gates,
            config.circuit.numSelectors
        );
        OuterLogupExt3Verifier.verifyGateTerminal(derived.gateTau, gatePoint, gateEvaluation, gateFinalClaim);
    }

    function _deriveInitialTranscript(
        MleProof calldata proof,
        VerificationConfig calldata config,
        uint256 width,
        uint256 indexBits
    ) private view returns (DerivedState memory derived) {
        derived.transcript = TranscriptV2.create();
        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_CIRCUIT_STATEMENT_V2);
        uint256[] memory circuitDigest = proof.circuitDigest;
        uint256[] memory publicInputs = _copyCanonicalBase(proof.publicInputs);
        derived.publicInputs = publicInputs;
        TranscriptV2.absorbFieldVecPrevalidated(derived.transcript, circuitDigest);
        TranscriptV2.absorbFieldVecPrevalidated(derived.transcript, publicInputs);

        TranscriptV2.domainSeparate(derived.transcript, PACKED_PCS_SCHEMA_DOMAIN_V2);
        bytes memory metadata = new bytes(15 * 8);
        uint256 offset;
        offset = _writeU64Le(metadata, offset, MLE_PROTOCOL_VERSION_CURRENT);
        offset = _writeU64Le(metadata, offset, NUM_PCS_GROUPS_V2);
        offset = _writeU64Le(metadata, offset, NUM_PCS_TERMINAL_POINTS_V2);
        offset = _writeU64Le(metadata, offset, NUM_PCS_CLAIMS_V2);
        offset = _writeU64Le(metadata, offset, config.circuit.numConstants);
        offset = _writeU64Le(metadata, offset, config.circuit.numRoutedWires);
        offset = _writeU64Le(metadata, offset, config.circuit.numWires);
        offset = _writeU64Le(metadata, offset, config.circuit.degreeBits);
        offset = _writeU64Le(metadata, offset, width);
        offset = _writeU64Le(metadata, offset, indexBits);
        offset = _writeU64Le(metadata, offset, NUM_PACKED_VECTORS_PER_GROUP_V2);
        offset = _writeU64Le(metadata, offset, EXTENSION_FIELD_LIMBS_V2);
        offset = _writeU64Le(metadata, offset, PACKED_VARIABLE_ORDER_CODE_V2);
        offset = _writeU64Le(metadata, offset, GATE_SUMCHECK_COUNT_V2);
        offset = _writeU64Le(metadata, offset, LOG_ROUND_DEGREE_V2);
        if (offset != metadata.length) revert InvalidMleVerifierConfiguration();
        TranscriptV2.absorbBytes(derived.transcript, metadata);

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_CIRCUIT_CONFIG_DIGEST_V2);
        TranscriptV2.absorbBytes(derived.transcript, abi.encodePacked(circuitConfigDigest));
        TranscriptV2.bindWhirIdentifiers(derived.transcript, _protocolId(), abi.encodePacked(whirSessionId));
        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_GROUP_PREPROCESSED_V2);
        TranscriptV2.absorbBytes(derived.transcript, abi.encodePacked(proof.preprocessedRoot));
        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_GROUP_WITNESS_V2);
        TranscriptV2.absorbBytes(derived.transcript, abi.encodePacked(proof.witnessRoot));

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
        derived.logChallenges.eta = TranscriptV2.squeezeExt3(derived.transcript);

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2);
        derived.logChallenges.beta = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.gamma = TranscriptV2.squeezeExt3(derived.transcript);
        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_GROUP_NORM_INVERSE_V2);
        TranscriptV2.absorbBytes(derived.transcript, abi.encodePacked(proof.normInverseRoot));

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2);
        derived.logChallenges.xi = TranscriptV2.squeezeExt3(derived.transcript);

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        derived.logChallenges.lambda = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.rho = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.kappa = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.tau = _squeezeExt3Vector(derived.transcript, config.circuit.degreeBits);
        derived.gateAlpha = TranscriptV2.squeezeExt3(derived.transcript);
        derived.gateTau = _squeezeExt3Vector(derived.transcript, config.circuit.degreeBits);
    }

    function _absorbClaimsAndSampleIndices(
        TranscriptV2.Transcript memory transcript,
        PackedClaimExt3.UsedClaims memory claims,
        uint256 indexBits
    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_CLAIMS_V2);
        TranscriptV2.absorbExt3VecPrevalidated(transcript, claims.logPreprocessed);
        TranscriptV2.absorbExt3VecPrevalidated(transcript, claims.logWitness);
        TranscriptV2.absorbExt3VecPrevalidated(transcript, claims.logNormInverse);
        TranscriptV2.absorbExt3VecPrevalidated(transcript, claims.gatePreprocessed);
        TranscriptV2.absorbExt3VecPrevalidated(transcript, claims.gateWitness);
        TranscriptV2.absorbExt3Vec(transcript, new GoldilocksExt3.Ext3[](0));
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_INDEX_V2);

        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < points.length; ++point) {
            points[point] = _squeezeExt3Vector(transcript, indexBits);
        }
    }

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

    function _requireCanonicalProof(MleProof calldata proof, CircuitConfigV2.Parameters calldata circuit)
        private
        view
        returns (uint256 width)
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
        width = _constituentWidth(circuit);
        if (proof.constituentWidth != width) revert InvalidMleProof();

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

    /// @dev Fuse the proof-boundary canonical check with the unavoidable
    /// calldata-to-memory copy.  Downstream helpers receive the same ordinary
    /// Solidity memory layout as before, but no longer require an earlier full
    /// scan of these large vectors.
    function _copyCanonicalExt3(GoldilocksExt3.Ext3[] calldata source)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        uint256 count = source.length;
        // Every caller reaches this helper only after `_requireCanonicalProof`
        // has matched an exact protocol vector length. Keep the independent cap
        // here as a local proof for the Yul arithmetic below: at most 160
        // records means `0x20 + count * (0x20 + 0x60)` cannot overflow and the
        // loop reads exactly the ABI-decoder-bounds-checked calldata elements.
        if (count > MAX_CONSTITUENT_WIDTH_V2) revert InvalidMleProof();
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let arrayPtr := mload(0x40)
            let pointerTable := add(arrayPtr, 0x20)
            let records := add(pointerTable, mul(count, 0x20))
            let input := source.offset
            mstore(arrayPtr, count)

            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let record := add(records, mul(i, 0x60))
                let c0 := calldataload(input)
                let c1 := calldataload(add(input, 0x20))
                let c2 := calldataload(add(input, 0x40))
                if iszero(and(and(lt(c0, p), lt(c1, p)), lt(c2, p))) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                mstore(add(pointerTable, mul(i, 0x20)), record)
                mstore(record, c0)
                mstore(add(record, 0x20), c1)
                mstore(add(record, 0x40), c2)
                input := add(input, 0x60)
            }

            mstore(0x40, add(records, mul(count, 0x60)))
            values := arrayPtr
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

    function _copyCanonicalSumcheck(OuterLogupExt3Verifier.SumcheckProof calldata source)
        private
        pure
        returns (OuterLogupExt3Verifier.SumcheckProof memory proof)
    {
        // `_requireCanonicalProof` has established both the circuit-capped
        // number of rounds and each exact coefficient count. The per-round
        // helper repeats its 160-record allocation cap and canonicalizes every
        // limb while copying it.
        proof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](source.rounds.length);
        for (uint256 round = 0; round < source.rounds.length; ++round) {
            proof.rounds[round].nonConstant = _copyCanonicalExt3(source.rounds[round].nonConstant);
        }
    }

    function _squeezeExt3Vector(TranscriptV2.Transcript memory transcript, uint256 length)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        values = new GoldilocksExt3.Ext3[](length);
        for (uint256 i = 0; i < length; ++i) {
            values[i] = TranscriptV2.squeezeExt3(transcript);
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

    function _writeU64Le(bytes memory destination, uint256 offset, uint256 value) private pure returns (uint256) {
        if (value > type(uint64).max || offset > destination.length || 8 > destination.length - offset) {
            revert InvalidMleVerifierConfiguration();
        }
        assembly ("memory-safe") {
            let ptr := add(add(destination, 0x20), offset)
            mstore8(ptr, value)
            mstore8(add(ptr, 1), shr(8, value))
            mstore8(add(ptr, 2), shr(16, value))
            mstore8(add(ptr, 3), shr(24, value))
            mstore8(add(ptr, 4), shr(32, value))
            mstore8(add(ptr, 5), shr(40, value))
            mstore8(add(ptr, 6), shr(48, value))
            mstore8(add(ptr, 7), shr(56, value))
        }
        return offset + 8;
    }
}
