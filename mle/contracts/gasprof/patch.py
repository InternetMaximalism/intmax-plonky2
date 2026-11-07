#!/usr/bin/env python3
"""Instrument a SCRATCH COPY of mle/contracts/src with GasProbe marks/counters.

usage: patch.py <scratch>/contracts/src          apply the marks to a scratch copy
       patch.py --check <any>/src               only verify that every anchor matches

Every replacement must match exactly once against the current tracked sources;
the script aborts without writing anything otherwise. Never point it at the
tracked mle/contracts/src without --check: the marks change bytecode and gas and
must not be committed. The tracked sources are guarded by a refusal below.
"""
import sys, pathlib

args = sys.argv[1:]
CHECK_ONLY = "--check" in args
args = [a for a in args if a != "--check"]
if len(args) != 1:
    print(__doc__, file=sys.stderr)
    sys.exit(2)
ROOT = pathlib.Path(args[0]).resolve()
TRACKED = (pathlib.Path(__file__).resolve().parent.parent / "src").resolve()
if ROOT == TRACKED and not CHECK_ONLY:
    print(f"refusing to instrument the tracked sources at {TRACKED} (use --check)", file=sys.stderr)
    sys.exit(2)
if not (ROOT / "PinnedMleVerifierV2.sol").is_file():
    print(f"{ROOT} does not look like a copy of mle/contracts/src", file=sys.stderr)
    sys.exit(2)
IMPORT_ROOT = 'import {GasProbe} from "./GasProbe.sol";\n'
IMPORT_SUB = 'import {GasProbe} from "../GasProbe.sol";\n'

patches = []  # (relpath, old, new)

def P(path, old, new):
    patches.append((path, old, new))

# ---------------------------------------------------------------- PinnedMleVerifierV2
f = "PinnedMleVerifierV2.sol"
P(f, 'import {MLE_PROTOCOL_VERSION_CURRENT} from "./generated/MleWhirV2.sol";\n',
     'import {MLE_PROTOCOL_VERSION_CURRENT} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """    function verifyCompact(bytes calldata compactProof) external view returns (bool) {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        return core.verifyCompactWithConfig(compactProof, _loadEncodedConfiguration());
    }
""", """    function verifyCompact(bytes calldata compactProof) external view returns (bool) {
        GasProbe.mark(10);
        GasProbe.mark(9001);
        GasProbe.mark(9002);
        GasProbe.mark(9003);
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        bytes memory encodedConfig = _loadEncodedConfiguration();
        GasProbe.mark(11);
        GasProbe.mark(12);
        bool ok = core.verifyCompactWithConfig(compactProof, encodedConfig);
        GasProbe.mark(13);
        GasProbe.mark(9004);
        GasProbe.mark(9005);
        return ok;
    }
""")
P(f, """        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        if (!core.verifyCompactWithConfig(compactProof, _loadEncodedConfiguration())) {
            revert InvalidMleVerifierConfiguration();
        }
        publicInputs = _compactPublicInputs(compactProof, _numPublicInputs);
""", """        GasProbe.mark(10);
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        bytes memory encodedConfig = _loadEncodedConfiguration();
        GasProbe.mark(11);
        GasProbe.mark(12);
        if (!core.verifyCompactWithConfig(compactProof, encodedConfig)) {
            revert InvalidMleVerifierConfiguration();
        }
        GasProbe.mark(13);
        publicInputs = _compactPublicInputs(compactProof, _numPublicInputs);
""")
P(f, """    function _loadEncodedConfiguration() private view returns (bytes memory encodedConfig) {
        address store = _configStore;
""", """    function _loadEncodedConfiguration() private view returns (bytes memory encodedConfig) {
        GasProbe.mark(110);
        address store = _configStore;
""")
P(f, """        encodedConfig = new bytes(length);
        assembly ("memory-safe") {
            extcodecopy(store, add(encodedConfig, 0x20), 1, length)
        }
    }
""", """        encodedConfig = new bytes(length);
        assembly ("memory-safe") {
            extcodecopy(store, add(encodedConfig, 0x20), 1, length)
        }
        GasProbe.mark(111);
    }
""")

# ---------------------------------------------------------------- MleVerifierV2
f = "MleVerifierV2.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """    {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        if (keccak256(encodedConfig) != verificationConfigDigest) revert InvalidMleVerifierConfiguration();
""", """    {
        GasProbe.mark(20);
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        if (keccak256(encodedConfig) != verificationConfigDigest) revert InvalidMleVerifierConfiguration();
        GasProbe.mark(21);
""")
P(f, """        ProofView memory view_ = _parseCompact(compactProof, config.circuit);
        _verifyView(view_, config);
        return true;
""", """        ProofView memory view_ = _parseCompact(compactProof, config.circuit);
        _verifyView(view_, config);
        GasProbe.mark(55);
        return true;
""")
# _parseCompact
P(f, """        uint256 length = compact.length;
        if (length > MAX_COMPACT_PROOF_BYTES_V2 || length < 8 + 8 + 4 + 32) revert InvalidMleProof();
""", """        GasProbe.mark(120);
        uint256 length = compact.length;
        if (length > MAX_COMPACT_PROOF_BYTES_V2 || length < 8 + 8 + 4 + 32) revert InvalidMleProof();
""")
P(f, """        view_.normInverseRoot = normInverseRoot;
        position += 100;
""", """        view_.normInverseRoot = normInverseRoot;
        position += 100;
        GasProbe.mark(121);
""")
P(f, """        view_.whirTranscript = whirTranscript;
        position += transcriptLength + 4;
""", """        view_.whirTranscript = whirTranscript;
        position += transcriptLength + 4;
        GasProbe.mark(122);
""")
P(f, """        view_.hintsLength = hintsLength;
        position += hintsLength;
""", """        view_.hintsLength = hintsLength;
        position += hintsLength;
        GasProbe.mark(123);
""")
P(f, """        view_.logRounds = _readExt3VectorLe(cursor, degreeBits * LOG_ROUND_DEGREE_V2);
        cursor += 24 * degreeBits * LOG_ROUND_DEGREE_V2;
""", """        view_.logRounds = _readExt3VectorLe(cursor, degreeBits * LOG_ROUND_DEGREE_V2);
        cursor += 24 * degreeBits * LOG_ROUND_DEGREE_V2;
        GasProbe.mark(124);
""")
P(f, """        view_.logNormInverse = _readExt3VectorLe(cursor, normInverseLength);
        cursor += 24 * normInverseLength;
""", """        view_.logNormInverse = _readExt3VectorLe(cursor, normInverseLength);
        cursor += 24 * normInverseLength;
        GasProbe.mark(125);
""")
P(f, """        view_.gateRounds = _readExt3VectorLe(cursor, degreeBits * gateDegree);
        cursor += 24 * degreeBits * gateDegree;
""", """        view_.gateRounds = _readExt3VectorLe(cursor, degreeBits * gateDegree);
        cursor += 24 * degreeBits * gateDegree;
        GasProbe.mark(126);
""")
P(f, """        view_.gateWitness = _readExt3VectorLe(cursor, numWires);
    }
""", """        view_.gateWitness = _readExt3VectorLe(cursor, numWires);
        GasProbe.mark(127);
    }
""")
# _verifyView
P(f, """    function _verifyView(ProofView memory view_, VerificationConfig calldata config) private view {
        CircuitConfigV2.Parameters calldata circuit = config.circuit;
""", """    function _verifyView(ProofView memory view_, VerificationConfig calldata config) private view {
        GasProbe.mark(22);
        CircuitConfigV2.Parameters calldata circuit = config.circuit;
""")
P(f, """        DerivedState memory derived = _deriveInitialTranscript(view_, config, width, indexBits);

        OuterLogupExt3Verifier.VerificationKey memory outerVk""", """        DerivedState memory derived = _deriveInitialTranscript(view_, config, width, indexBits);
        GasProbe.mark(23);

        OuterLogupExt3Verifier.VerificationKey memory outerVk""")
P(f, """        (logPoint, gatePoint, gateFinalClaim, derived.transcript) = OuterLogupExt3Verifier.verifyPrevalidatedFlat(
            view_.logRounds,
""", """        GasProbe.mark(24);
        GasProbe.mark(25);
        (logPoint, gatePoint, gateFinalClaim, derived.transcript) = OuterLogupExt3Verifier.verifyPrevalidatedFlat(
            view_.logRounds,
""")
P(f, """            derived.logChallenges,
            derived.transcript
        );

        GoldilocksExt3.Ext3[][] memory indexPoints""", """            derived.logChallenges,
            derived.transcript
        );
        GasProbe.mark(26);

        GoldilocksExt3.Ext3[][] memory indexPoints""")
P(f, """        GoldilocksExt3.Ext3[][] memory indexPoints = _absorbClaimsAndSampleIndices(derived.transcript, view_, indexBits);
""", """        GoldilocksExt3.Ext3[][] memory indexPoints = _absorbClaimsAndSampleIndices(derived.transcript, view_, indexBits);
        GasProbe.mark(27);
""")
P(f, """        if (
            evaluations.length != NUM_PCS_CLAIMS_V2 || evaluationMask.length != 1
                || evaluationMask[0] != PACKED_BOUND_CLAIM_MASK_V2
        ) revert InvalidMleVerifierConfiguration();

        SpongefishWhirVerify.WhirParams memory whir = config.whir;
""", """        GasProbe.mark(28);
        if (
            evaluations.length != NUM_PCS_CLAIMS_V2 || evaluationMask.length != 1
                || evaluationMask[0] != PACKED_BOUND_CLAIM_MASK_V2
        ) revert InvalidMleVerifierConfiguration();

        SpongefishWhirVerify.WhirParams memory whir = config.whir;
""")
P(f, """        bytes calldata hints = _hintsSlice(view_);
        bool whirAccepted = SpongefishWhirVerify.verifyWhirProofBound(
""", """        bytes calldata hints = _hintsSlice(view_);
        GasProbe.mark(29);
        bool whirAccepted = SpongefishWhirVerify.verifyWhirProofBound(
""")
P(f, """        if (!whirAccepted) revert InvalidMleProof();

        uint256[4] memory publicInputsHash = PoseidonPublicInputsHash.hashNoPad(view_.publicInputs);
        GoldilocksExt3.Ext3 memory gateEvaluation = Plonky2GateEvaluatorExt3.evalCombinedPrevalidated(
""", """        GasProbe.mark(50);
        if (!whirAccepted) revert InvalidMleProof();

        GasProbe.mark(51);
        uint256[4] memory publicInputsHash = PoseidonPublicInputsHash.hashNoPad(view_.publicInputs);
        GasProbe.mark(52);
        GoldilocksExt3.Ext3 memory gateEvaluation = Plonky2GateEvaluatorExt3.evalCombinedPrevalidated(
""")
P(f, """        _requireGateTerminal(derived.gateTau, gatePoint, gateEvaluation, gateFinalClaim);
    }
""", """        GasProbe.mark(53);
        _requireGateTerminal(derived.gateTau, gatePoint, gateEvaluation, gateFinalClaim);
        GasProbe.mark(54);
    }
""")
# _deriveInitialTranscript
P(f, """        TranscriptV2.Transcript memory transcript = derived.transcript;
        TranscriptV2.init(transcript);
""", """        GasProbe.mark(30);
        TranscriptV2.Transcript memory transcript = derived.transcript;
        TranscriptV2.init(transcript);
""")
P(f, """        TranscriptV2.domainSeparate(transcript, DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.eta);
""", """        GasProbe.mark(31);
        TranscriptV2.domainSeparate(transcript, DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.eta);
""")
P(f, """        TranscriptV2.domainSeparate(transcript, DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.lambda);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.rho);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.kappa);
        derived.logChallenges.tau = _squeezeExt3Vector(transcript, config.circuit.degreeBits);
        TranscriptV2.squeezeExt3Into(transcript, derived.gateAlpha);
        derived.gateTau = _squeezeExt3Vector(transcript, config.circuit.degreeBits);
    }
""", """        GasProbe.mark(32);
        TranscriptV2.domainSeparate(transcript, DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.lambda);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.rho);
        TranscriptV2.squeezeExt3Into(transcript, derived.logChallenges.kappa);
        GasProbe.mark(33);
        derived.logChallenges.tau = _squeezeExt3Vector(transcript, config.circuit.degreeBits);
        GasProbe.mark(34);
        TranscriptV2.squeezeExt3Into(transcript, derived.gateAlpha);
        GasProbe.mark(35);
        derived.gateTau = _squeezeExt3Vector(transcript, config.circuit.degreeBits);
        GasProbe.mark(36);
    }
""")
# _absorbClaimsAndSampleIndices
P(f, """    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_CLAIMS_V2);
""", """    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        GasProbe.mark(40);
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_CLAIMS_V2);
""")
P(f, """        TranscriptV2.absorbExt3Vec(transcript, new GoldilocksExt3.Ext3[](0));
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_INDEX_V2);

        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < points.length; ++point) {
            points[point] = _squeezeExt3Vector(transcript, indexBits);
        }
    }
""", """        TranscriptV2.absorbExt3Vec(transcript, new GoldilocksExt3.Ext3[](0));
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_INDEX_V2);
        GasProbe.mark(41);

        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < points.length; ++point) {
            points[point] = _squeezeExt3Vector(transcript, indexBits);
        }
        GasProbe.mark(42);
    }
""")

# ---------------------------------------------------------------- TranscriptV2
f = "TranscriptV2.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """        if (count > type(uint64).max) revert InvalidMleProof();
        assembly ("memory-safe") {
            let payloadLength := add(8, mul(count, 24))
            let frame := mload(0x40)
            let payload := add(frame, FRAME_HEADER_LENGTH)
""", """        if (count > type(uint64).max) revert InvalidMleProof();
        GasProbe.keccakCount(11, 1, FRAME_HEADER_LENGTH + 8 + 24 * count);
        assembly ("memory-safe") {
            let payloadLength := add(8, mul(count, 24))
            let frame := mload(0x40)
            let payload := add(frame, FRAME_HEADER_LENGTH)
""")
P(f, """    function squeezeChallenge(Transcript memory transcript) internal pure returns (uint256 challenge) {
        assembly ("memory-safe") {
""", """    function squeezeChallenge(Transcript memory transcript) internal pure returns (uint256 challenge) {
        GasProbe.keccakCount(12, 1, 64);
        assembly ("memory-safe") {
""")
P(f, """    function squeezeExt3Into(Transcript memory transcript, GoldilocksExt3.Ext3 memory destination) internal pure {
        assembly ("memory-safe") {
""", """    function squeezeExt3Into(Transcript memory transcript, GoldilocksExt3.Ext3 memory destination) internal pure {
        GasProbe.keccakCount(12, 3, 64);
        assembly ("memory-safe") {
""")
P(f, """        uint256 payloadLength = payload.length;
        if (payloadLength > type(uint64).max) revert InvalidMleProof();
        assembly ("memory-safe") {
""", """        uint256 payloadLength = payload.length;
        if (payloadLength > type(uint64).max) revert InvalidMleProof();
        GasProbe.keccakCount(10, 1, FRAME_HEADER_LENGTH + payloadLength);
        assembly ("memory-safe") {
""")
P(f, """        uint256 payloadLength
    ) private pure {
        assembly ("memory-safe") {
""", """        uint256 payloadLength
    ) private pure {
        GasProbe.keccakCount(10, 1, FRAME_HEADER_LENGTH + payloadLength);
        assembly ("memory-safe") {
""")
P(f, """        uint256[] memory source
    ) private pure {
        assembly ("memory-safe") {
""", """        uint256[] memory source
    ) private pure {
        GasProbe.keccakCount(11, 1, FRAME_HEADER_LENGTH + 8 + count * elementBytes);
        assembly ("memory-safe") {
""")

# ---------------------------------------------------------------- OuterLogupExt3Verifier
f = "OuterLogupExt3Verifier.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
# mark 60: entry of verifyPrevalidated (the flattening of the Ext3[] inputs is inside the frame)
P(f, """    {
        uint256[] memory logRounds = _flattenRounds(logProof, vk.numVars, MAX_DEGREE);
        uint256[] memory gateRounds = _flattenRounds(gateProof, vk.numVars, vk.gateDegree);
""", """    {
        GasProbe.mark(60);
        uint256[] memory logRounds = _flattenRounds(logProof, vk.numVars, MAX_DEGREE);
        uint256[] memory gateRounds = _flattenRounds(gateProof, vk.numVars, vk.gateDegree);
""")
# marks 63/64: after the coupled sumchecks / after the terminal equality
P(f, """        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _coupledSumchecksFlat(logRounds, gateRounds, vk.numVars, vk.gateDegree, transcript);
        GoldilocksExt3.Ext3 memory terminalValue =
            _terminalFlat(vk, challenges, preprocessed, witness, normInverse, publicInputs, logPoint);
        if (!GoldilocksExt3.eq(logFinalClaim, terminalValue)) revert InvalidMleProof();
    }
""", """        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _coupledSumchecksFlat(logRounds, gateRounds, vk.numVars, vk.gateDegree, transcript);
        GasProbe.mark(63);
        GoldilocksExt3.Ext3 memory terminalValue =
            _terminalFlat(vk, challenges, preprocessed, witness, normInverse, publicInputs, logPoint);
        if (!GoldilocksExt3.eq(logFinalClaim, terminalValue)) revert InvalidMleProof();
        GasProbe.mark(64);
    }
""")
# per-round marks: 1000+10r loop entry, 1001+10r after the transcript commit, 1002+10r after both evaluations
P(f, """        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            assembly ("memory-safe") {
                let base := add(mload(ctx), mul(roundIndex, 0x1e0))
""", """        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            GasProbe.mark(1000 + 10 * roundIndex);
            assembly ("memory-safe") {
                let base := add(mload(ctx), mul(roundIndex, 0x1e0))
""")
P(f, """            TranscriptV2.CoupledOuterRoundChallenges memory roundChallenges =
                TranscriptV2.commitCoupledOuterRound(transcript, roundIndex, logCoefficients, gateCoefficients);
            // Round polynomial evaluation: a0 = (claim - sum a_j) / 2, then Horner at the challenge.
""", """            TranscriptV2.CoupledOuterRoundChallenges memory roundChallenges =
                TranscriptV2.commitCoupledOuterRound(transcript, roundIndex, logCoefficients, gateCoefficients);
            GasProbe.mark(1001 + 10 * roundIndex);
            GasProbe.ext3Count(20, MAX_DEGREE);
            GasProbe.ext3Count(21, gateDegree);
            // Round polynomial evaluation: a0 = (claim - sum a_j) / 2, then Horner at the challenge.
""")
P(f, """                record := add(mload(add(ctx, 0x20)), mul(roundIndex, mload(add(ctx, 0x40))))
                evaluateRound(mload(add(ctx, 0x100)), record, add(record, mload(add(ctx, 0x40))), challenge)
            }
        }
    }
""", """                record := add(mload(add(ctx, 0x20)), mul(roundIndex, mload(add(ctx, 0x40))))
                evaluateRound(mload(add(ctx, 0x100)), record, add(record, mload(add(ctx, 0x40))), challenge)
            }
            GasProbe.mark(1002 + 10 * roundIndex);
        }
    }
""")
# norm/logUp terminal: 70 entry, 71 after eq(tau, point), 72 after subgroup(point), 73 after the wire loop, 74 after combine
P(f, """    ) private pure returns (GoldilocksExt3.Ext3 memory permutationValue) {
        GoldilocksExt3.Ext3 memory eqValue = _eqEvaluation(challenges.tau, point);
        GoldilocksExt3.Ext3 memory subgroup = _subgroupEvaluation(vk.subgroupGenPowers, point);
""", """    ) private pure returns (GoldilocksExt3.Ext3 memory permutationValue) {
        GasProbe.mark(70);
        GoldilocksExt3.Ext3 memory eqValue = _eqEvaluation(challenges.tau, point);
        GasProbe.mark(71);
        GoldilocksExt3.Ext3 memory subgroup = _subgroupEvaluation(vk.subgroupGenPowers, point);
        GasProbe.mark(72);
""")
P(f, """            for { let i := numRoutedWires } i {} {
                i := sub(i, 1)
                wireStep(w, i)
            }
        }
        // permutationValue = eq(tau, point) * helperZeroChecks + kappa * logUpSum
""", """            for { let i := numRoutedWires } i {} {
                i := sub(i, 1)
                wireStep(w, i)
            }
        }
        GasProbe.ext3Count(23, 24 * vk.numRoutedWires);
        GasProbe.scalarCount(24, vk.numRoutedWires);
        GasProbe.mark(73);
        // permutationValue = eq(tau, point) * helperZeroChecks + kappa * logUpSum
""")
P(f, """        _mulAddInPlace(permutationValue, eqValue, _recordAt(w, 0x1e0));
        _mulAddInPlace(permutationValue, challenges.kappa, _recordAt(w, 0x240));
    }
""", """        _mulAddInPlace(permutationValue, eqValue, _recordAt(w, 0x1e0));
        _mulAddInPlace(permutationValue, challenges.kappa, _recordAt(w, 0x240));
        GasProbe.mark(74);
    }
""")
# direct-PI binding: 75 entry, 76/77 after the Horner loop (eq rows are memoised inside the same loop)
P(f, """        uint256 count = publicInputs.length;
        if (count == 0) return binding;
        // Scratch (byte offsets): 0x00 map data, 0x20 point table, 0x40 numVars, 0x60 witness data,
""", """        GasProbe.mark(75);
        uint256 count = publicInputs.length;
        if (count == 0) return binding;
        // Scratch (byte offsets): 0x00 map data, 0x20 point table, 0x40 numVars, 0x60 witness data,
""")
P(f, """            mstore(binding, mload(add(w, 0x1e0)))
            mstore(add(binding, 0x20), mload(add(w, 0x200)))
            mstore(add(binding, 0x40), mload(add(w, 0x220)))
        }
    }
""", """            mstore(binding, mload(add(w, 0x1e0)))
            mstore(add(binding, 0x20), mload(add(w, 0x200)))
            mstore(add(binding, 0x40), mload(add(w, 0x220)))
        }
        GasProbe.ext3Count(28, 2 * count);
        GasProbe.mark(76);
        GasProbe.mark(77);
    }
""")
P(f, """    function _eqEvaluation(GoldilocksExt3.Ext3[] memory tau, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        GoldilocksExt3.Ext3 memory factor;
""", """    function _eqEvaluation(GoldilocksExt3.Ext3[] memory tau, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        GasProbe.ext3Count(25, 2 * point.length);
        GoldilocksExt3.Ext3 memory factor;
""")
P(f, """    function _subgroupEvaluation(uint256[] memory subgroupGenPowers, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        GoldilocksExt3.Ext3 memory factor;
""", """    function _subgroupEvaluation(uint256[] memory subgroupGenPowers, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        GasProbe.ext3Count(26, point.length);
        GasProbe.scalarCount(26, point.length);
        GoldilocksExt3.Ext3 memory factor;
""")
P(f, """        if (tau.length == 0 || tau.length != point.length || tau.length > MAX_ROW_VARIABLES) {
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
""", """        GasProbe.mark(800);
        if (tau.length == 0 || tau.length != point.length || tau.length > MAX_ROW_VARIABLES) {
            revert InvalidMleProof();
        }
        for (uint256 i = 0; i < tau.length; ++i) {
            _checkCanonical(tau[i]);
            _checkCanonical(point[i]);
        }
        _checkCanonical(gateEvaluation);
        _checkCanonical(finalClaim);
        GasProbe.mark(801);
        GoldilocksExt3.Ext3 memory expected = _eqEvaluation(tau, point);
        _mulInPlace(expected, gateEvaluation);
        GasProbe.ext3Count(27, 1);
        if (!GoldilocksExt3.eq(expected, finalClaim)) revert InvalidMleProof();
        GasProbe.mark(802);
    }
""")

# ---------------------------------------------------------------- PackedClaimExt3
f = "PackedClaimExt3.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """        uint256 count = values.length;
        if (count == 0) return;
        if (3 * count > scratch.length) revert InvalidMleProof();
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let buf := add(scratch, 0x20)
""", """        uint256 count = values.length;
        if (count == 0) return;
        if (3 * count > scratch.length) revert InvalidMleProof();
        if (GasProbe.COUNTING) {
            uint256 active = count;
            uint256 total;
            for (uint256 bit = 0; bit < indexPoint.length; ++bit) {
                uint256 next = (active + 1) >> 1;
                total += next;
                active = next;
            }
            GasProbe.ext3Count(40, total);
        }
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let buf := add(scratch, 0x20)
""")

# ---------------------------------------------------------------- GoldilocksExt3
f = "spongefish/GoldilocksExt3.sol"
P(f, "library GoldilocksExt3 {\n", IMPORT_SUB + "\nlibrary GoldilocksExt3 {\n")
P(f, """    function mul(Ext3 memory a, Ext3 memory b) internal pure returns (Ext3 memory r) {
        assembly {
""", """    function mul(Ext3 memory a, Ext3 memory b) internal pure returns (Ext3 memory r) {
        GasProbe.ext3Count(1, 1);
        assembly {
""")
P(f, """    function mulScalar(Ext3 memory a, uint64 s) internal pure returns (Ext3 memory r) {
        assembly {
""", """    function mulScalar(Ext3 memory a, uint64 s) internal pure returns (Ext3 memory r) {
        GasProbe.scalarCount(4, 1);
        assembly {
""")
P(f, """    function square(Ext3 memory a) internal pure returns (Ext3 memory r) {
        assembly {
""", """    function square(Ext3 memory a) internal pure returns (Ext3 memory r) {
        GasProbe.ext3Count(2, 1);
        assembly {
""")
P(f, """    function inv(Ext3 memory a) internal pure returns (Ext3 memory r) {
        assembly {
""", """    function inv(Ext3 memory a) internal pure returns (Ext3 memory r) {
        GasProbe.ext3Count(3, 1);
        GasProbe.baseCount(3, 96 + 9);
        assembly {
""")
P(f, """    function dot(Ext3[] memory a, Ext3[] memory b) internal pure returns (Ext3 memory result) {
        assembly {
""", """    function dot(Ext3[] memory a, Ext3[] memory b) internal pure returns (Ext3 memory result) {
        GasProbe.ext3Count(5, a.length < b.length ? a.length : b.length);
        assembly {
""")

# ---------------------------------------------------------------- Keccak256Chain
f = "spongefish/Keccak256Chain.sol"
P(f, "library Keccak256Chain {\n", IMPORT_SUB + "\nlibrary Keccak256Chain {\n")
P(f, """    function absorb(Sponge memory s, bytes memory input) internal pure {
        bytes32 st = s.state;
""", """    function absorb(Sponge memory s, bytes memory input) internal pure {
        GasProbe.keccakCount(34, 1, 32 + input.length);
        bytes32 st = s.state;
""")
P(f, """    function absorbSlice(Sponge memory s, bytes memory data, uint256 offset, uint256 len) internal pure {
        assembly ("memory-safe") {
""", """    function absorbSlice(Sponge memory s, bytes memory data, uint256 offset, uint256 len) internal pure {
        GasProbe.keccakCount(34, 1, 32 + len);
        assembly ("memory-safe") {
""")
P(f, """        uint256 blocksNeeded = (n + 31) / 32;
        require(counter + blocksNeeded <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
""", """        uint256 blocksNeeded = (n + 31) / 32;
        GasProbe.keccakCount(35, blocksNeeded, 47);
        require(counter + blocksNeeded <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
""")
P(f, """        require(counter < type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        assembly {
""", """        require(counter < type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        GasProbe.keccakCount(36, 1, 47);
        assembly {
""")
P(f, """        require(counter + 1 <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        bytes32 st = s.state;
""", """        require(counter + 1 <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        GasProbe.keccakCount(35, 1, 47);
        bytes32 st = s.state;
""")
P(f, """        require(counter + 4 <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        bytes32 st = s.state;
""", """        require(counter + 4 <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        GasProbe.keccakCount(35, 4, 47);
        bytes32 st = s.state;
""")
P(f, """    function ratchet(Sponge memory s) internal pure {
        bytes32 st = s.state;
""", """    function ratchet(Sponge memory s) internal pure {
        GasProbe.keccakCount(37, 1, 39);
        bytes32 st = s.state;
""")

# ---------------------------------------------------------------- SpongefishMerkle
f = "spongefish/SpongefishMerkle.sol"
P(f, 'import {InvalidMleProof} from "../MleProofErrors.sol";\n',
     'import {InvalidMleProof} from "../MleProofErrors.sol";\n' + IMPORT_SUB)
P(f, """            nextLen := shr(6, sub(wp, pairs))
            newHc := hcOut
        }
    }
""", """            nextLen := shr(6, sub(wp, pairs))
            newHc := hcOut
        }
        GasProbe.keccakCount(33, nextLen, 64);
    }
""")

# ---------------------------------------------------------------- SpongefishWhir
f = "spongefish/SpongefishWhir.sol"
P(f, 'import {InvalidMleProof} from "../MleProofErrors.sol";\n',
     'import {InvalidMleProof} from "../MleProofErrors.sol";\n' + IMPORT_SUB)
P(f, """        (uint64 c0, uint64 c1, uint64 c2) = verifierMessageField64x3(ts);
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let x0 := c0
""", """        (uint64 c0, uint64 c1, uint64 c2) = verifierMessageField64x3(ts);
        GasProbe.ext3Count(52, count - 1);
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let x0 := c0
""")

# ---------------------------------------------------------------- WhirLinearAlgebra
f = "spongefish/WhirLinearAlgebra.sol"
P(f, 'import {InvalidMleProof} from "../MleProofErrors.sol";\n',
     'import {InvalidMleProof} from "../MleProofErrors.sol";\n' + IMPORT_SUB)
P(f, """        if (3 * point.length != r.length) revert InvalidMleProof();
        assembly ("memory-safe") {
""", """        if (3 * point.length != r.length) revert InvalidMleProof();
        GasProbe.ext3Count(63, 3 * point.length);
        assembly ("memory-safe") {
""")
P(f, """        uint256 len = r.length / 3;
        if (start > len || count > len - start) revert InvalidMleProof();
        uint256 size = 1 << count;
        weights = new uint256[](3 * size);
""", """        uint256 len = r.length / 3;
        if (start > len || count > len - start) revert InvalidMleProof();
        uint256 size = 1 << count;
        GasProbe.ext3Count(53, 2 * (size - 1));
        weights = new uint256[](3 * size);
""")
P(f, """        uint256 bLen = b.length / 3;
        result = new uint256[](3 * aLen * bLen);
""", """        uint256 bLen = b.length / 3;
        GasProbe.ext3Count(64, aLen * bLen);
        result = new uint256[](3 * aLen * bLen);
""")

# ---------------------------------------------------------------- SpongefishWhirVerify
f = "spongefish/SpongefishWhirVerify.sol"
P(f, 'import {InvalidMleProof} from "../MleProofErrors.sol";\n',
     'import {InvalidMleProof} from "../MleProofErrors.sol";\n' + IMPORT_SUB)
P(f, """    ) external pure returns (bool) {
        if (params.numCommitments == 0 || params.numVectors == 0) {
            revert InvalidParameters();
        }
""", """    ) external pure returns (bool) {
        GasProbe.mark(200);
        if (params.numCommitments == 0 || params.numVectors == 0) {
            revert InvalidParameters();
        }
""")
P(f, """        _validateParameters(params, evaluations.length / totalVectors);
        SpongefishMerkle.CalldataBytes memory hintsView =
""", """        _validateParameters(params, evaluations.length / totalVectors);
        GasProbe.mark(201);
        SpongefishMerkle.CalldataBytes memory hintsView =
""")
P(f, """        vs.roundConstraints = new RoundConstraintEntry[](1 + params.numRounds);

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
""", """        vs.roundConstraints = new RoundConstraintEntry[](1 + params.numRounds);
        GasProbe.mark(202);

        // Phase 1: Initial commitment + OOD + RLC + compute "the sum"
        _phaseInitial(ts, transcript, evaluations, evaluationMask, expectedRoots, params, vs);
        GasProbe.mark(203);

        // Phase 2: Initial sumcheck
        _phaseSumcheck(ts, transcript, params.initialSumcheckRounds, params.initialSumcheckPowThreshold, vs);
        GasProbe.mark(204);

        // Phase 3: Intermediate rounds
        for (uint256 round = 0; round < params.numRounds; round++) {
            _doIntermediateRound(ts, transcript, hints, params, vs, round);
        }

        // Phase 4: Final vector + final Merkle open
        uint256[] memory finalVector = _phaseFinalVectorAndMerkle(ts, transcript, hints, params, vs);
        GasProbe.mark(205);

        // Phase 5: Final sumcheck
        _phaseSumcheck(ts, transcript, params.finalSumcheckRounds, params.finalSumcheckPowThreshold, vs);
        GasProbe.mark(206);

        // Phase 6: FinalClaim verification
        _phaseFinalClaim(params, vs, finalVector);
        GasProbe.mark(207);

        if (ts.transcriptPos != transcript.length) revert InvalidMleProof();
        if (ts.hintPos != hints.length) revert InvalidMleProof();
        GasProbe.mark(208);
        return true;
""")
P(f, """        // Phase 1a: Receive per-commitment roots and OOD data
        (uint256[] memory perCommitOod, uint256[] memory allOodPoints) =
            _receiveCommitmentsAndOod(ts, transcript, expectedRoots, params, vs);
""", """        GasProbe.mark(210);
        // Phase 1a: Receive per-commitment roots and OOD data
        (uint256[] memory perCommitOod, uint256[] memory allOodPoints) =
            _receiveCommitmentsAndOod(ts, transcript, expectedRoots, params, vs);
        GasProbe.mark(211);
""")
P(f, """        uint256[] memory evalsFlat = _readEvaluationStatement(ts, transcript, evaluations, evaluationMask);
""", """        uint256[] memory evalsFlat = _readEvaluationStatement(ts, transcript, evaluations, evaluationMask);
        GasProbe.mark(212);
""")
P(f, """        uint256[] memory oodMatrix = _completeOodMatrix(ts, transcript, perCommitOod, params);

        // Phase 1b: RLC and sum computation
        vs.vectorRlc = SpongefishWhir.geometricChallengeFlat(ts, totalVectors);
        vs.numLinearForms = evaluations.length / totalVectors;
        vs.initialConstraintRlc = SpongefishWhir.geometricChallengeFlat(ts, totalOodPoints + vs.numLinearForms);
""", """        uint256[] memory oodMatrix = _completeOodMatrix(ts, transcript, perCommitOod, params);
        GasProbe.mark(213);

        // Phase 1b: RLC and sum computation
        vs.vectorRlc = SpongefishWhir.geometricChallengeFlat(ts, totalVectors);
        vs.numLinearForms = evaluations.length / totalVectors;
        vs.initialConstraintRlc = SpongefishWhir.geometricChallengeFlat(ts, totalOodPoints + vs.numLinearForms);
        GasProbe.mark(214);
""")
P(f, """        _accumulateTheSum(
            vs.theSum, oodMatrix, vs.vectorRlc, vs.initialConstraintRlc, vs.numLinearForms, totalOodPoints, totalVectors
        );
    }
""", """        _accumulateTheSum(
            vs.theSum, oodMatrix, vs.vectorRlc, vs.initialConstraintRlc, vs.numLinearForms, totalOodPoints, totalVectors
        );
        GasProbe.mark(215);
    }
""")
P(f, """        ) revert InvalidMleProof();
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let p := 0xFFFFFFFF00000001
            let mp := add(matrix, 0x20)
""", """        ) revert InvalidMleProof();
        GasProbe.ext3Count(51, count * numVectors + count);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                c0 := mod(add(mul(a0, b0), shl(1, add(mul(a1, b2), mul(a2, b1)))), 0xFFFFFFFF00000001)
                c1 := mod(add(add(mul(a0, b1), mul(a1, b0)), shl(1, mul(a2, b2))), 0xFFFFFFFF00000001)
                c2 := mod(add(add(mul(a0, b2), mul(a1, b1)), mul(a2, b0)), 0xFFFFFFFF00000001)
            }
            let p := 0xFFFFFFFF00000001
            let mp := add(matrix, 0x20)
""")
P(f, """        for (uint256 i = 0; i < numRounds; i++) {
            _readInto(ts, transcript, coeffs, 0);
            _readInto(ts, transcript, coeffs, 1);
""", """        for (uint256 i = 0; i < numRounds; i++) {
            GasProbe.ext3Count(50, 2);
            _readInto(ts, transcript, coeffs, 0);
            _readInto(ts, transcript, coeffs, 1);
""")
P(f, """        if (threshold == type(uint64).max) return;
        bytes32 challenge = ts.sponge.squeezeWord();
""", """        if (threshold == type(uint64).max) return;
        GasProbe.keccakCount(32, 1, 64);
        bytes32 challenge = ts.sponge.squeezeWord();
""")
P(f, """        RoundParams memory rp = params.rounds[round];

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
""", """        RoundParams memory rp = params.rounds[round];
        GasProbe.mark(300 + 20 * round);

        // Receive new commitment
        bytes32 roundRoot = SpongefishWhir.proverMessageHash(ts, transcript);
        GasProbe.mark(301 + 20 * round);

        // OOD for this round: ALL points squeezed first, then ALL answers absorbed
        // (matches Rust irs_commit::receive_commitment order)
        uint256[] memory roundOodPoints = new uint256[](3 * rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            _squeezeInto(ts, roundOodPoints, i);
        }
        GasProbe.mark(302 + 20 * round);
        uint256[] memory roundOodAnswers = new uint256[](3 * rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            _readInto(ts, transcript, roundOodAnswers, i);
        }
        GasProbe.mark(303 + 20 * round);

        _verifyPow(ts, transcript, rp.powThreshold);
        GasProbe.mark(304 + 20 * round);

        // Open previous commitment with Merkle verification
        _openAndVerifyCommitment(ts, hints, params, vs, round, roundOodAnswers, roundOodPoints);
        GasProbe.mark(309 + 20 * round);

        // Sumcheck
        _phaseSumcheck(ts, transcript, rp.sumcheckRounds, rp.sumcheckPowThreshold, vs);
        GasProbe.mark(310 + 20 * round);

        vs.prevRoot = roundRoot;
    }
""")
# Round openings. Marks inside `_openRows` are parameterised (patch-only extra arguments):
# mA starts the "vec prefix + leaf row hashing" span, mB the Merkle span, mC the row-dot span.
P(f, """        uint256[] memory rawIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        uint256 rawCount = rawIndices.length;

        // eq_weights from the folding randomness of the fold just completed
        uint256 ff = (round == 0) ? params.initialSumcheckRounds : params.rounds[round - 1].sumcheckRounds;
        uint256[] memory eqW = WhirLinearAlgebra.eqWeightsFlat(vs.foldR, vs.foldIdx - ff, ff);
        uint256[] memory inDomainEvalPoints = _computeEvalPoints(rawIndices, o);
        uint256[] memory rowValues = new uint256[](3 * rawCount);
""", """        uint256[] memory rawIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        uint256 rawCount = rawIndices.length;
        GasProbe.mark(305 + 20 * round);

        // eq_weights from the folding randomness of the fold just completed
        uint256 ff = (round == 0) ? params.initialSumcheckRounds : params.rounds[round - 1].sumcheckRounds;
        GasProbe.mark(420);
        uint256[] memory eqW = WhirLinearAlgebra.eqWeightsFlat(vs.foldR, vs.foldIdx - ff, ff);
        GasProbe.mark(421);
        GasProbe.mark(306 + 20 * round);
        uint256[] memory inDomainEvalPoints = _computeEvalPoints(rawIndices, o);
        uint256[] memory rowValues = new uint256[](3 * rawCount);
""")
P(f, """                _openRows(ts, hints, o, rawIndices, vs.initialRoots[c], w, rowValues);
            }
        } else {
            _openRows(ts, hints, o, rawIndices, vs.prevRoot, eqW, rowValues);
        }

        // Constraint RLC and accumulation into theSum (OOD values, then in-domain values)
        uint256 constraintCount = rp.outDomainSamples + rawCount;
        uint256[] memory roundRlc = SpongefishWhir.geometricChallengeFlat(ts, constraintCount);
        _mulAddFlat(vs.theSum, roundOodAnswers, roundRlc, 0, rp.outDomainSamples);
        _mulAddFlat(vs.theSum, rowValues, roundRlc, rp.outDomainSamples, rawCount);
""", """                _openRows(ts, hints, o, rawIndices, vs.initialRoots[c], w, rowValues, 305 + 20 * round, 307 + 20 * round, 422);
            }
        } else {
            _openRows(ts, hints, o, rawIndices, vs.prevRoot, eqW, rowValues, 305 + 20 * round, 307 + 20 * round, 422);
        }
        GasProbe.mark(421);

        // Constraint RLC and accumulation into theSum (OOD values, then in-domain values)
        uint256 constraintCount = rp.outDomainSamples + rawCount;
        uint256[] memory roundRlc = SpongefishWhir.geometricChallengeFlat(ts, constraintCount);
        GasProbe.mark(422);
        _mulAddFlat(vs.theSum, roundOodAnswers, roundRlc, 0, rp.outDomainSamples);
        _mulAddFlat(vs.theSum, rowValues, roundRlc, rp.outDomainSamples, rawCount);
        GasProbe.ext3Count(57, rp.outDomainSamples + rawCount);
        GasProbe.mark(423);
""")
P(f, """        vs.roundConstraints[1 + round] =
            RoundConstraintEntry({rlcCoeffs: roundRlc, points: allEvalPoints, numVariables: rp.numVariables});
    }
""", """        vs.roundConstraints[1 + round] =
            RoundConstraintEntry({rlcCoeffs: roundRlc, points: allEvalPoints, numVariables: rp.numVariables});
        GasProbe.mark(424);
    }
""")
P(f, """        uint256[] memory w,
        uint256[] memory rowValues
    ) private pure {
        uint256 rawCount = rawIndices.length;
        _consumeVecPrefix(ts, hints, rawCount * o.numCols);
        uint256 rowsStart = ts.hintPos;
        bytes32[] memory leafHashes = _hashRows(hints, rowsStart, o.rowBytes, rawCount);
""", """        uint256[] memory w,
        uint256[] memory rowValues,
        uint256 mA,
        uint256 mB,
        uint256 mC
    ) private pure {
        uint256 rawCount = rawIndices.length;
        GasProbe.mark(mA);
        _consumeVecPrefix(ts, hints, rawCount * o.numCols);
        uint256 rowsStart = ts.hintPos;
        bytes32[] memory leafHashes = _hashRows(hints, rowsStart, o.rowBytes, rawCount);
        GasProbe.mark(mB);
""")
P(f, """        ts.hintPos = SpongefishMerkle.verify(root, o.md, idxCopy, leafHashes, hints, rowsStart + rawCount * o.rowBytes);
        _accumulateRowDots(rowValues, w, o.numCols, hints, rowsStart, o.rowBytes, rawCount, o.isBaseField);
    }
""", """        ts.hintPos = SpongefishMerkle.verify(root, o.md, idxCopy, leafHashes, hints, rowsStart + rawCount * o.rowBytes);
        GasProbe.mark(mC);
        _accumulateRowDots(rowValues, w, o.numCols, hints, rowsStart, o.rowBytes, rawCount, o.isBaseField);
    }
""")
P(f, """        finalVector = new uint256[](3 * params.finalSize);
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
""", """        GasProbe.mark(500);
        finalVector = new uint256[](3 * params.finalSize);
        for (uint256 i = 0; i < params.finalSize; i++) {
            _readInto(ts, transcript, finalVector, i);
        }
        GasProbe.mark(501);

        _verifyPow(ts, transcript, params.finalPowThreshold);
        GasProbe.mark(502);

        // The final opening is the same IRS commitment that the next intermediate round would
        // open: the initial commitment(s) when numRounds == 0, otherwise the last round commitment.
        OpenParams memory o = _getOpenParams(params, params.numRounds);
        uint256[] memory rawFinalIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        GasProbe.mark(503);
        uint256 foldingRounds =
            params.numRounds == 0 ? params.initialSumcheckRounds : params.rounds[params.numRounds - 1].sumcheckRounds;
        uint256[] memory finalWeights =
            WhirLinearAlgebra.eqWeightsFlat(vs.foldR, vs.foldIdx - foldingRounds, foldingRounds);
        GasProbe.mark(504);
        uint256[] memory finalEvalPoints = _computeEvalPoints(rawFinalIndices, o);
        uint256[] memory openedValues = new uint256[](3 * rawFinalIndices.length);
""")
P(f, """                _openRows(ts, hints, o, rawFinalIndices, vs.initialRoots[c], w, openedValues);
            }
        } else {
            _openRows(ts, hints, o, rawFinalIndices, vs.prevRoot, finalWeights, openedValues);
        }

        _requireFinalOpenings(finalVector, finalEvalPoints, openedValues);
""", """                _openRows(ts, hints, o, rawFinalIndices, vs.initialRoots[c], w, openedValues, 505, 506, 507);
            }
        } else {
            _openRows(ts, hints, o, rawFinalIndices, vs.prevRoot, finalWeights, openedValues, 505, 506, 507);
        }
        GasProbe.mark(508);

        _requireFinalOpenings(finalVector, finalEvalPoints, openedValues);
""")
P(f, """        uint256 foldStart = vs.foldIdx - params.finalSumcheckRounds;
        GoldilocksExt3.Ext3 memory polyEval = _foldEval(finalVector, vs.foldR, foldStart, params.finalSumcheckRounds);
        if (GoldilocksExt3.isZero(polyEval)) revert InvalidMleProof();

        // linear_form_rlc = theSum / polyEval
        GoldilocksExt3.Ext3 memory linearFormRlc = vs.theSum.mul(GoldilocksExt3.inv(polyEval));
""", """        GasProbe.mark(520);
        uint256 foldStart = vs.foldIdx - params.finalSumcheckRounds;
        GoldilocksExt3.Ext3 memory polyEval = _foldEval(finalVector, vs.foldR, foldStart, params.finalSumcheckRounds);
        if (GoldilocksExt3.isZero(polyEval)) revert InvalidMleProof();
        GasProbe.mark(521);

        // linear_form_rlc = theSum / polyEval
        GoldilocksExt3.Ext3 memory linearFormRlc = vs.theSum.mul(GoldilocksExt3.inv(polyEval));
        GasProbe.mark(522);
""")
P(f, """            if (entry.rlcCoeffs.length == 0) continue;
            _subtractRoundConstraints(linearFormRlc, entry, vs.foldR, vs.totalFoldingLen - entry.numVariables);
""", """            if (entry.rlcCoeffs.length == 0) continue;
            GasProbe.ext3Count(65, entry.rlcCoeffs.length / 3);
            if (GasProbe.COUNTING) {
                uint256 iterations = entry.numVariables * (entry.rlcCoeffs.length / 3);
                GasProbe.ext3Count(60, iterations);
                GasProbe.scalarCount(61, iterations);
                GasProbe.baseCount(61, iterations);
            }
            _subtractRoundConstraints(linearFormRlc, entry, vs.foldR, vs.totalFoldingLen - entry.numVariables);
""")
P(f, """        // Compute expectedRlc = Σ rlc[i] * eq(point_i, foldingRandomness)
        // For single-point: expectedRlc = rlc[0] * eq(point1, folding)
        // For dual-point:   expectedRlc = rlc[0] * eq(point1, folding) + rlc[1] * eq(point2, folding)
        GoldilocksExt3.Ext3 memory expectedRlc = GoldilocksExt3.zero();
""", """        GasProbe.mark(523);
        // Compute expectedRlc = Σ rlc[i] * eq(point_i, foldingRandomness)
        // For single-point: expectedRlc = rlc[0] * eq(point1, folding)
        // For dual-point:   expectedRlc = rlc[0] * eq(point1, folding) + rlc[1] * eq(point2, folding)
        GoldilocksExt3.Ext3 memory expectedRlc = GoldilocksExt3.zero();
""")
P(f, """        if (!GoldilocksExt3.eq(linearFormRlc, expectedRlc)) revert InvalidMleProof();
    }
""", """        GasProbe.mark(524);
        if (!GoldilocksExt3.eq(linearFormRlc, expectedRlc)) revert InvalidMleProof();
    }
""")
P(f, """        uint256 sizeBytes = _ceilDiv(_log2(numLeaves), 8);
        uint256 totalBytes = count * sizeBytes;
        indices = new uint256[](count);
        uint256 counter = uint256(ts.sponge.squeezeCounter);
""", """        uint256 sizeBytes = _ceilDiv(_log2(numLeaves), 8);
        uint256 totalBytes = count * sizeBytes;
        GasProbe.keccakCount(30, totalBytes, 47);
        indices = new uint256[](count);
        uint256 counter = uint256(ts.sponge.squeezeCounter);
""")
P(f, """        if (start > hints.length || count * rowBytes > hints.length - start) revert InvalidMleProof();
        hashes = new bytes32[](count);
""", """        if (start > hints.length || count * rowBytes > hints.length - start) revert InvalidMleProof();
        GasProbe.keccakCount(31, count, rowBytes);
        hashes = new bytes32[](count);
""")
P(f, """        uint256 count = rawIndices.length;
        pts = new uint256[](count);
        uint256 depth = o.md;
""", """        uint256 count = rawIndices.length;
        pts = new uint256[](count);
        GasProbe.baseCount(58, count);
        uint256 depth = o.md;
""")
P(f, """                || numCols * limbsPerCol * 8 > rowBytes || w.length < 3 * numCols || rowValues.length < 3 * count
        ) revert InvalidMleProof();
""", """                || numCols * limbsPerCol * 8 > rowBytes || w.length < 3 * numCols || rowValues.length < 3 * count
        ) revert InvalidMleProof();
        if (isBaseField) GasProbe.scalarCount(54, numCols * count);
        else GasProbe.ext3Count(55, numCols * count);
""")
P(f, """        if (rStart > r.length / 3 || numRounds > r.length / 3 - rStart) revert InvalidMleProof();
        assembly ("memory-safe") {
""", """        if (rStart > r.length / 3 || numRounds > r.length / 3 - rStart) revert InvalidMleProof();
        GasProbe.ext3Count(59, vec.length > 3 ? 2 * (vec.length / 3 - 1) : 0);
        assembly ("memory-safe") {
""")

# ---------------------------------------------------------------- Plonky2GateEvaluatorExt3
f = "Plonky2GateEvaluatorExt3.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """    ) external pure returns (GoldilocksExt3.Ext3 memory combined) {
        return _evalCombinedUnchecked(wires, constants, publicInputsHash, alpha, gates, numSelectors);
    }
""", """    ) external pure returns (GoldilocksExt3.Ext3 memory combined) {
        GasProbe.mark(600);
        combined = _evalCombinedUnchecked(wires, constants, publicInputsHash, alpha, gates, numSelectors);
        GasProbe.mark(601);
    }
""")
P(f, """        for (uint256 row = 0; row < gates.length; ++row) {
            GateInfoV2 calldata info = gates[row];
            if (uint256(info.selectorIndex) >= fr.numConstants) revert InvalidMleProof();
            _computeFilter(fr, info, fr.numSelectors > 1);
            // Metadata for every gate was validated above. A zero selector filter
            // therefore makes this gate's entire contribution identically zero;
            // avoid evaluating expensive inactive Poseidon/coset constraints.
            if ((fr.f0 | fr.f1 | fr.f2) == 0) continue;
""", """        for (uint256 row = 0; row < gates.length; ++row) {
            GasProbe.mark(2010 + 10 * row);
            GateInfoV2 calldata info = gates[row];
            if (uint256(info.selectorIndex) >= fr.numConstants) revert InvalidMleProof();
            _computeFilter(fr, info, fr.numSelectors > 1);
            GasProbe.mark(2011 + 10 * row);
            // Metadata for every gate was validated above. A zero selector filter
            // therefore makes this gate's entire contribution identically zero;
            // avoid evaluating expensive inactive Poseidon/coset constraints.
            if ((fr.f0 | fr.f1 | fr.f2) == 0) continue;
""")
P(f, """                if (gateId == GATE_POSEIDON) {
                    (fr.r0, fr.r1, fr.r2) = PoseidonGateExt3.evalPoseidonReduced(flatWires, a0, a1, a2);
                } else {
""", """                if (gateId == GATE_POSEIDON) {
                    (fr.r0, fr.r1, fr.r2) = PoseidonGateExt3.evalPoseidonReduced(flatWires, a0, a1, a2);
                    GasProbe.mark(2013 + 10 * row);
                } else {
""")
P(f, """                    assembly ("memory-safe") {
                        mstore(flatWires, fullLength)
                    }
                }
                _evalAndAccumulate(fr);
            } else {
                _evalAndAccumulate(fr);
            }
        }
""", """                    assembly ("memory-safe") {
                        mstore(flatWires, fullLength)
                    }
                    GasProbe.mark(2012 + 10 * row);
                }
                _evalAndAccumulate(fr);
                if (gateId != GATE_POSEIDON) GasProbe.mark(2013 + 10 * row);
            } else {
                GasProbe.mark(2012 + 10 * row);
                _evalAndAccumulate(fr);
                GasProbe.mark(2013 + 10 * row);
            }
            GasProbe.mark(2014 + 10 * row);
        }
""")

# ---------------------------------------------------------------- PoseidonGateExt3
f = "PoseidonGateExt3.sol"
P(f, 'import {PoseidonConstants} from "./PoseidonConstants.sol";\n',
     'import {PoseidonConstants} from "./PoseidonConstants.sol";\n' + IMPORT_ROOT)
P(f, """        if (wires.length < POSEIDON_WIRES * WIRE) revert InvalidMleProof();

        bytes memory roundConstants = PoseidonConstants.ALL_ROUND_CONSTANTS;
""", """        GasProbe.mark(700);
        if (wires.length < POSEIDON_WIRES * WIRE) revert InvalidMleProof();

        bytes memory roundConstants = PoseidonConstants.ALL_ROUND_CONSTANTS;
""")
P(f, """        _swapDelta(w, s, k, t);
        uint256 next = _fullRounds(w, s, t, k, roundConstants, 0, 5);
        s = _partialInit(s, r, pfrc, pim);
        next = _partialRounds(w, s, k, prc, prvs, prwh, next);
        next = _fullRounds(w, s, t, k, roundConstants, 1, next);
        _outputConstraints(w, s, k, next);
        (red0, red1, red2) = _reduce(k, alpha0, alpha1, alpha2);
    }
""", """        GasProbe.mark(701);
        _swapDelta(w, s, k, t);
        GasProbe.ext3Count(83, 5);
        GasProbe.mark(702);
        uint256 next = _fullRounds(w, s, t, k, roundConstants, 0, 5);
        GasProbe.ext3Count(80, 192);
        GasProbe.mark(703);
        s = _partialInit(s, r, pfrc, pim);
        GasProbe.scalarCount(84, 121);
        GasProbe.mark(704);
        next = _partialRounds(w, s, k, prc, prvs, prwh, next);
        GasProbe.ext3Count(80, 88);
        GasProbe.mark(705);
        next = _fullRounds(w, s, t, k, roundConstants, 1, next);
        GasProbe.ext3Count(80, 192);
        GasProbe.mark(706);
        _outputConstraints(w, s, k, next);
        GasProbe.mark(707);
        (red0, red1, red2) = _reduce(k, alpha0, alpha1, alpha2);
        GasProbe.ext3Count(82, 123);
        GasProbe.mark(708);
    }
""")

# ---------------------------------------------------------------- PoseidonPublicInputsHash
f = "PoseidonPublicInputsHash.sol"
P(f, 'import {PoseidonGate} from "./PoseidonGate.sol";\n',
     'import {PoseidonGate} from "./PoseidonGate.sol";\n' + IMPORT_ROOT)
P(f, """    function hashNoPad(uint256[] calldata inputs) external pure returns (uint256[4] memory) {
        return PoseidonGate.hashNoPad(inputs);
    }
""", """    function hashNoPad(uint256[] calldata inputs) external pure returns (uint256[4] memory digest) {
        GasProbe.mark(850);
        digest = PoseidonGate.hashNoPad(inputs);
        GasProbe.mark(851);
    }
""")


def main():
    touched = {}
    for rel, old, new in patches:
        path = ROOT / rel
        text = touched.get(path)
        if text is None:
            text = path.read_text()
        n = text.count(old)
        if n != 1:
            print(f"FAIL {rel}: expected 1 match, found {n} for:\n{old[:200]}", file=sys.stderr)
            sys.exit(1)
        touched[path] = text.replace(old, new)
    if CHECK_ONLY:
        print(f"all {len(patches)} anchors match exactly once in {len(touched)} files under {ROOT}")
        return
    if not (ROOT / "GasProbe.sol").is_file():
        print(f"FAIL: {ROOT}/GasProbe.sol missing (copy gasprof/GasProbe.sol there first)", file=sys.stderr)
        sys.exit(1)
    for path, text in touched.items():
        path.write_text(text)
    print(f"applied {len(patches)} patches to {len(touched)} files under {ROOT}")

if __name__ == "__main__":
    main()
