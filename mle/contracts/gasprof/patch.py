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
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decodeForCoreVerification(compactProof, config.circuit);
        return core.verify(proof, config);
    }
""", """    function verifyCompact(bytes calldata compactProof) external view returns (bool) {
        GasProbe.mark(10);
        GasProbe.mark(9001);
        GasProbe.mark(9002);
        GasProbe.mark(9003);
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        GasProbe.mark(11);
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decodeForCoreVerification(compactProof, config.circuit);
        GasProbe.mark(12);
        bool ok = core.verify(proof, config);
        GasProbe.mark(13);
        GasProbe.mark(9004);
        GasProbe.mark(9005);
        return ok;
    }
""")
P(f, """        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decodeForCoreVerification(compactProof, config.circuit);
        if (!core.verify(proof, config)) revert InvalidMleVerifierConfiguration();
        publicInputs = proof.publicInputs;
    }
""", """        GasProbe.mark(10);
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        GasProbe.mark(11);
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decodeForCoreVerification(compactProof, config.circuit);
        GasProbe.mark(12);
        if (!core.verify(proof, config)) revert InvalidMleVerifierConfiguration();
        GasProbe.mark(13);
        publicInputs = proof.publicInputs;
    }
""")
P(f, """        address store = _configStore;
        uint256 length = _configLength;
        if (store.code.length != length + 1) revert InvalidMleVerifierConfiguration();
        bytes memory encodedConfig = new bytes(length);
        assembly ("memory-safe") {
            extcodecopy(store, add(encodedConfig, 0x20), 1, length)
        }
        config = abi.decode(encodedConfig, (MleVerifierV2.VerificationConfig));
""", """        GasProbe.mark(110);
        address store = _configStore;
        uint256 length = _configLength;
        if (store.code.length != length + 1) revert InvalidMleVerifierConfiguration();
        bytes memory encodedConfig = new bytes(length);
        assembly ("memory-safe") {
            extcodecopy(store, add(encodedConfig, 0x20), 1, length)
        }
        GasProbe.mark(111);
        config = abi.decode(encodedConfig, (MleVerifierV2.VerificationConfig));
        GasProbe.mark(112);
""")

# ---------------------------------------------------------------- CompactMleProofV2
f = "CompactMleProofV2.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """        if (encoded.length > MAX_COMPACT_PROOF_BYTES_V2 || encoded.length < 8) revert InvalidMleProof();

        bytes8 magic;
""", """        GasProbe.mark(120);
        if (encoded.length > MAX_COMPACT_PROOF_BYTES_V2 || encoded.length < 8) revert InvalidMleProof();

        bytes8 magic;
""")
P(f, """        proof.normInverseRoot = _readBytes32(encoded, cursor);
        proof.whirTranscript = _readBlob(encoded, cursor, MAX_WHIR_NARG_BYTES_V2);
        proof.whirHints = _readBlob(encoded, cursor, MAX_WHIR_HINT_BYTES_V2);

        proof.logProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.logProof.rounds[round].nonConstant =
                _readExt3Vector(encoded, cursor, LOG_ROUND_DEGREE_V2, requireCanonicalLimbs);
        }

        uint256 preprocessedLength = circuit.numConstants + circuit.numRoutedWires;
        proof.logPreprocessed = _readExt3Vector(encoded, cursor, preprocessedLength, requireCanonicalLimbs);
        proof.logWitness = _readExt3Vector(encoded, cursor, circuit.numWires, requireCanonicalLimbs);
        proof.logNormInverse = _readExt3Vector(encoded, cursor, normInverseLength, requireCanonicalLimbs);

        proof.gateProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        uint256 gateDegree = circuit.quotientDegreeFactor + 2;
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.gateProof.rounds[round].nonConstant =
                _readExt3Vector(encoded, cursor, gateDegree, requireCanonicalLimbs);
        }
        proof.gatePreprocessed = _readExt3Vector(encoded, cursor, preprocessedLength, requireCanonicalLimbs);
        proof.gateWitness = _readExt3Vector(encoded, cursor, circuit.numWires, requireCanonicalLimbs);

        if (cursor.offset != encoded.length) revert InvalidMleProof();
""", """        proof.normInverseRoot = _readBytes32(encoded, cursor);
        GasProbe.mark(121);
        proof.whirTranscript = _readBlob(encoded, cursor, MAX_WHIR_NARG_BYTES_V2);
        GasProbe.mark(122);
        proof.whirHints = _readBlob(encoded, cursor, MAX_WHIR_HINT_BYTES_V2);
        GasProbe.mark(123);

        proof.logProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.logProof.rounds[round].nonConstant =
                _readExt3Vector(encoded, cursor, LOG_ROUND_DEGREE_V2, requireCanonicalLimbs);
        }
        GasProbe.mark(124);

        uint256 preprocessedLength = circuit.numConstants + circuit.numRoutedWires;
        proof.logPreprocessed = _readExt3Vector(encoded, cursor, preprocessedLength, requireCanonicalLimbs);
        proof.logWitness = _readExt3Vector(encoded, cursor, circuit.numWires, requireCanonicalLimbs);
        proof.logNormInverse = _readExt3Vector(encoded, cursor, normInverseLength, requireCanonicalLimbs);
        GasProbe.mark(125);

        proof.gateProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        uint256 gateDegree = circuit.quotientDegreeFactor + 2;
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.gateProof.rounds[round].nonConstant =
                _readExt3Vector(encoded, cursor, gateDegree, requireCanonicalLimbs);
        }
        GasProbe.mark(126);
        proof.gatePreprocessed = _readExt3Vector(encoded, cursor, preprocessedLength, requireCanonicalLimbs);
        proof.gateWitness = _readExt3Vector(encoded, cursor, circuit.numWires, requireCanonicalLimbs);

        if (cursor.offset != encoded.length) revert InvalidMleProof();
        GasProbe.mark(127);
""")

# ---------------------------------------------------------------- MleVerifierV2
f = "MleVerifierV2.sol"
P(f, 'import {SpongefishWhirVerify} from "./spongefish/SpongefishWhirVerify.sol";\n',
     'import {SpongefishWhirVerify} from "./spongefish/SpongefishWhirVerify.sol";\n' + IMPORT_ROOT)
P(f, """    function verify(MleProof calldata proof, VerificationConfig calldata config) external view returns (bool) {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);

        _requirePinnedConfiguration(config);
        uint256 width = _requireCanonicalProof(proof, config.circuit);

        _verifyAtomic(proof, config, width);
        return true;
    }
""", """    function verify(MleProof calldata proof, VerificationConfig calldata config) external view returns (bool) {
        GasProbe.mark(20);
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);

        _requirePinnedConfiguration(config);
        GasProbe.mark(21);
        uint256 width = _requireCanonicalProof(proof, config.circuit);
        GasProbe.mark(22);

        _verifyAtomic(proof, config, width);
        GasProbe.mark(55);
        return true;
    }
""")
P(f, """        uint256 indexBits = _constituentIndexBits(width);
        DerivedState memory derived = _deriveInitialTranscript(proof, config, width, indexBits);
""", """        uint256 indexBits = _constituentIndexBits(width);
        DerivedState memory derived = _deriveInitialTranscript(proof, config, width, indexBits);
        GasProbe.mark(23);
""")
P(f, """            gateWitness: _copyCanonicalExt3(proof.gateWitness)
        });
        uint256[] memory kIs = config.kIs;
""", """            gateWitness: _copyCanonicalExt3(proof.gateWitness)
        });
        GasProbe.mark(24);
        uint256[] memory kIs = config.kIs;
""")
P(f, """        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _copyCanonicalSumcheck(proof.gateProof);

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
""", """        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _copyCanonicalSumcheck(proof.gateProof);
        GasProbe.mark(25);

        GoldilocksExt3.Ext3[] memory logPoint;
        GoldilocksExt3.Ext3[] memory gatePoint;
        GoldilocksExt3.Ext3 memory gateFinalClaim;
        (logPoint, gatePoint, gateFinalClaim, derived.transcript) = OuterLogupExt3Verifier.verifyPrevalidated(
            logProof, gateProof, outerVk, derived.logChallenges, logTerminal, derived.transcript
        );
        GasProbe.mark(26);

        GoldilocksExt3.Ext3[][] memory indexPoints =
            _absorbClaimsAndSampleIndices(derived.transcript, usedClaims, indexBits);
        GasProbe.mark(27);
        (GoldilocksExt3.Ext3[] memory evaluations, bytes memory evaluationMask) =
            PackedClaimExt3.foldV2UsedCellsPrevalidatedInternal(usedClaims, uint256(1) << indexBits, indexPoints);
        GasProbe.mark(28);
""")
P(f, """        roots[2] = proof.normInverseRoot;
        bool whirAccepted = SpongefishWhirVerify.verifyWhirProofBound(
""", """        roots[2] = proof.normInverseRoot;
        GasProbe.mark(29);
        bool whirAccepted = SpongefishWhirVerify.verifyWhirProofBound(
""")
P(f, """        if (!whirAccepted) revert InvalidMleProof();

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
""", """        GasProbe.mark(50);
        if (!whirAccepted) revert InvalidMleProof();

        GoldilocksExt3.Ext3[] memory constants = new GoldilocksExt3.Ext3[](config.circuit.numConstants);
        for (uint256 i = 0; i < constants.length; ++i) {
            constants[i] = usedClaims.gatePreprocessed[i];
        }
        GasProbe.mark(51);
        uint256[4] memory publicInputsHash = PoseidonPublicInputsHash.hashNoPad(proof.publicInputs);
        GasProbe.mark(52);
        GoldilocksExt3.Ext3 memory gateEvaluation = Plonky2GateEvaluatorExt3.evalCombinedPrevalidated(
            usedClaims.gateWitness,
            constants,
            publicInputsHash,
            derived.gateAlpha,
            config.gates,
            config.circuit.numSelectors
        );
        GasProbe.mark(53);
        OuterLogupExt3Verifier.verifyGateTerminal(derived.gateTau, gatePoint, gateEvaluation, gateFinalClaim);
        GasProbe.mark(54);
    }
""")
P(f, """    ) private view returns (DerivedState memory derived) {
        derived.transcript = TranscriptV2.create();
""", """    ) private view returns (DerivedState memory derived) {
        GasProbe.mark(30);
        derived.transcript = TranscriptV2.create();
""")
P(f, """        TranscriptV2.absorbBytes(derived.transcript, abi.encodePacked(proof.witnessRoot));

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
""", """        TranscriptV2.absorbBytes(derived.transcript, abi.encodePacked(proof.witnessRoot));
        GasProbe.mark(31);

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
""")
P(f, """        derived.logChallenges.xi = TranscriptV2.squeezeExt3(derived.transcript);

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        derived.logChallenges.lambda = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.rho = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.kappa = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.tau = _squeezeExt3Vector(derived.transcript, config.circuit.degreeBits);
        derived.gateAlpha = TranscriptV2.squeezeExt3(derived.transcript);
        derived.gateTau = _squeezeExt3Vector(derived.transcript, config.circuit.degreeBits);
    }
""", """        derived.logChallenges.xi = TranscriptV2.squeezeExt3(derived.transcript);
        GasProbe.mark(32);

        TranscriptV2.domainSeparate(derived.transcript, DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        derived.logChallenges.lambda = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.rho = TranscriptV2.squeezeExt3(derived.transcript);
        derived.logChallenges.kappa = TranscriptV2.squeezeExt3(derived.transcript);
        GasProbe.mark(33);
        derived.logChallenges.tau = _squeezeExt3Vector(derived.transcript, config.circuit.degreeBits);
        GasProbe.mark(34);
        derived.gateAlpha = TranscriptV2.squeezeExt3(derived.transcript);
        GasProbe.mark(35);
        derived.gateTau = _squeezeExt3Vector(derived.transcript, config.circuit.degreeBits);
        GasProbe.mark(36);
    }
""")
P(f, """    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_CLAIMS_V2);
""", """    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        GasProbe.mark(40);
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_CLAIMS_V2);
""")
P(f, """        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_INDEX_V2);

        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < points.length; ++point) {
            points[point] = _squeezeExt3Vector(transcript, indexBits);
        }
    }
""", """        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_INDEX_V2);
        GasProbe.mark(41);

        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < points.length; ++point) {
            points[point] = _squeezeExt3Vector(transcript, indexBits);
        }
        GasProbe.mark(42);
    }
""")
P(f, """        if (keccak256(abi.encode(config)) != verificationConfigDigest) {
            revert InvalidMleVerifierConfiguration();
        }
""", """        bytes memory encodedConfig = abi.encode(config);
        GasProbe.keccakCount(1, 1, encodedConfig.length);
        if (keccak256(encodedConfig) != verificationConfigDigest) {
            revert InvalidMleVerifierConfiguration();
        }
""")

# ---------------------------------------------------------------- TranscriptV2
f = "TranscriptV2.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """        if (payload.length > type(uint64).max) revert InvalidMleProof();
        transcript.state = keccak256(
            abi.encodePacked(
                TRANSCRIPT_FRAME_PREFIX_V2, transcript.state, bytes1(tag), _u64Le(uint64(payload.length)), payload
            )
        );
        transcript.squeezeCounter = 0;
""", """        if (payload.length > type(uint64).max) revert InvalidMleProof();
        bytes memory frame = abi.encodePacked(
            TRANSCRIPT_FRAME_PREFIX_V2, transcript.state, bytes1(tag), _u64Le(uint64(payload.length)), payload
        );
        GasProbe.keccakCount(10, 1, frame.length);
        transcript.state = keccak256(frame);
        transcript.squeezeCounter = 0;
""")
P(f, """    function _closeFrame(Transcript memory transcript, bytes memory frame) private pure {
        transcript.state = keccak256(frame);
""", """    function _closeFrame(Transcript memory transcript, bytes memory frame) private pure {
        GasProbe.keccakCount(11, 1, frame.length);
        transcript.state = keccak256(frame);
""")
P(f, """        bytes32 digest = keccak256(
            abi.encodePacked(TRANSCRIPT_CHALLENGE_PREFIX_V2, transcript.state, _u64Le(transcript.squeezeCounter))
        );
""", """        GasProbe.keccakCount(12, 1, 64);
        bytes32 digest = keccak256(
            abi.encodePacked(TRANSCRIPT_CHALLENGE_PREFIX_V2, transcript.state, _u64Le(transcript.squeezeCounter))
        );
""")

# ---------------------------------------------------------------- OuterLogupExt3Verifier
f = "OuterLogupExt3Verifier.sol"
P(f, '} from "./generated/MleWhirV2.sol";\n', '} from "./generated/MleWhirV2.sol";\n' + IMPORT_ROOT)
P(f, """    {
        GoldilocksExt3.Ext3 memory logFinalClaim;
        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _verifyCoupledSumchecksUnchecked(logProof, gateProof, vk.numVars, transcript);
        GoldilocksExt3.Ext3 memory terminalValue = _evaluateTerminalUnchecked(vk, challenges, terminal, logPoint);
        if (!GoldilocksExt3.eq(logFinalClaim, terminalValue)) revert InvalidMleProof();
        nextTranscript = transcript;
    }

    /// @notice Verify all coefficient rounds without evaluating either terminal family.
""", """    {
        GasProbe.mark(60);
        GoldilocksExt3.Ext3 memory logFinalClaim;
        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _verifyCoupledSumchecksUnchecked(logProof, gateProof, vk.numVars, transcript);
        GasProbe.mark(63);
        GoldilocksExt3.Ext3 memory terminalValue = _evaluateTerminalUnchecked(vk, challenges, terminal, logPoint);
        if (!GoldilocksExt3.eq(logFinalClaim, terminalValue)) revert InvalidMleProof();
        nextTranscript = transcript;
        GasProbe.mark(64);
    }

    /// @notice Verify all coefficient rounds without evaluating either terminal family.
""")
P(f, """        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            GoldilocksExt3.Ext3[] memory logCoefficients = logProof.rounds[roundIndex].nonConstant;
            GoldilocksExt3.Ext3[] memory gateCoefficients = gateProof.rounds[roundIndex].nonConstant;
            TranscriptV2.CoupledOuterRoundChallenges memory roundChallenges =
                TranscriptV2.commitCoupledOuterRound(transcript, roundIndex, logCoefficients, gateCoefficients);

            logPoint[roundIndex] = roundChallenges.log;
            logClaim = _evaluateExt3Round(logClaim, logCoefficients, roundChallenges.log);
            gatePoint[roundIndex] = roundChallenges.gate;
            gateClaim = _evaluateExt3RoundDynamic(gateClaim, gateCoefficients, roundChallenges.gate);
        }
""", """        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            GasProbe.mark(1000 + 10 * roundIndex);
            GoldilocksExt3.Ext3[] memory logCoefficients = logProof.rounds[roundIndex].nonConstant;
            GoldilocksExt3.Ext3[] memory gateCoefficients = gateProof.rounds[roundIndex].nonConstant;
            TranscriptV2.CoupledOuterRoundChallenges memory roundChallenges =
                TranscriptV2.commitCoupledOuterRound(transcript, roundIndex, logCoefficients, gateCoefficients);
            GasProbe.mark(1001 + 10 * roundIndex);

            logPoint[roundIndex] = roundChallenges.log;
            logClaim = _evaluateExt3Round(logClaim, logCoefficients, roundChallenges.log);
            gatePoint[roundIndex] = roundChallenges.gate;
            gateClaim = _evaluateExt3RoundDynamic(gateClaim, gateCoefficients, roundChallenges.gate);
            GasProbe.mark(1002 + 10 * roundIndex);
        }
""")
P(f, """        GoldilocksExt3.Ext3 memory coefficientSum = GoldilocksExt3.zero();
        for (uint256 i = 0; i < MAX_DEGREE; ++i) {
            coefficientSum = GoldilocksExt3.add(coefficientSum, coefficients[i]);
        }
""", """        GasProbe.ext3Count(20, MAX_DEGREE + 1);
        GoldilocksExt3.Ext3 memory coefficientSum = GoldilocksExt3.zero();
        for (uint256 i = 0; i < MAX_DEGREE; ++i) {
            coefficientSum = GoldilocksExt3.add(coefficientSum, coefficients[i]);
        }
""")
P(f, """        GoldilocksExt3.Ext3 memory coefficientSum = GoldilocksExt3.zero();
        for (uint256 i = 0; i < coefficients.length; ++i) {
            coefficientSum = GoldilocksExt3.add(coefficientSum, coefficients[i]);
        }
""", """        GasProbe.ext3Count(21, coefficients.length + 1);
        GoldilocksExt3.Ext3 memory coefficientSum = GoldilocksExt3.zero();
        for (uint256 i = 0; i < coefficients.length; ++i) {
            coefficientSum = GoldilocksExt3.add(coefficientSum, coefficients[i]);
        }
""")
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
P(f, """                challenges.lambda,
                scratch
            );
        }

        permutationValue = GoldilocksExt3.add(
            GoldilocksExt3.mul(eqValue, helperZeroChecks), GoldilocksExt3.mul(challenges.kappa, logupSum)
        );
    }
""", """                challenges.lambda,
                scratch
            );
        }
        GasProbe.ext3Count(23, 24 * vk.numRoutedWires);
        GasProbe.scalarCount(24, vk.numRoutedWires);
        GasProbe.mark(73);

        permutationValue = GoldilocksExt3.add(
            GoldilocksExt3.mul(eqValue, helperZeroChecks), GoldilocksExt3.mul(challenges.kappa, logupSum)
        );
        GasProbe.mark(74);
    }
""")
P(f, """        uint256 count = terminal.publicInputs.length;
        if (count == 0) return binding;
        PublicInputBindingScratch memory scratch;
""", """        GasProbe.mark(75);
        uint256 count = terminal.publicInputs.length;
        if (count == 0) return binding;
        PublicInputBindingScratch memory scratch;
""")
P(f, """            if (i + 1 < count) _mulExt3InPlace(scratch.etaPower, eta);
        }
        GoldilocksExt3.Ext3 memory commonEq = _eqBooleanRowSelectedBits(
""", """            if (i + 1 < count) _mulExt3InPlace(scratch.etaPower, eta);
        }
        GasProbe.ext3Count(28, 2 * count - 1);
        GasProbe.mark(76);
        GoldilocksExt3.Ext3 memory commonEq = _eqBooleanRowSelectedBits(
""")
P(f, """                GoldilocksExt3.add(scratch.binding, GoldilocksExt3.mul(eqRow, scratch.rowBindings[rowIndex]));
        }
        binding = scratch.binding;
    }
""", """                GoldilocksExt3.add(scratch.binding, GoldilocksExt3.mul(eqRow, scratch.rowBindings[rowIndex]));
        }
        binding = scratch.binding;
        GasProbe.mark(77);
    }
""")
P(f, """        value = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 i = 0; i < point.length; ++i) {
            // tau*x + (1-tau)*(1-x) = 1 - tau - x + 2*tau*x.
""", """        value = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        GasProbe.ext3Count(25, 0);
        for (uint256 i = 0; i < point.length; ++i) {
            // tau*x + (1-tau)*(1-x) = 1 - tau - x + 2*tau*x.
""")
P(f, """        value = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 i = 0; i < point.length; ++i) {
            // (1-x) + x*g = 1 + x*(g-1). Since g is base-field
""", """        value = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        GasProbe.ext3Count(26, 0);
        for (uint256 i = 0; i < point.length; ++i) {
            // (1-x) + x*g = 1 + x*(g-1). Since g is base-field
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
        GoldilocksExt3.Ext3 memory expected = GoldilocksExt3.mul(_eqEvaluation(tau, point), gateEvaluation);
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
        GoldilocksExt3.Ext3 memory expected = GoldilocksExt3.mul(_eqEvaluation(tau, point), gateEvaluation);
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
P(f, """                mstore(add(nextHashData, mul(nextLen, 0x20)), keccak256(0x00, 0x40))
                nextLen := add(nextLen, 1)
            }
        }
    }
""", """                mstore(add(nextHashData, mul(nextLen, 0x20)), keccak256(0x00, 0x40))
                nextLen := add(nextLen, 1)
            }
        }
        GasProbe.keccakCount(33, nextLen, 64);
    }
""")

# ---------------------------------------------------------------- SpongefishWhir
f = "spongefish/SpongefishWhir.sol"
P(f, 'import {InvalidMleProof} from "../MleProofErrors.sol";\n',
     'import {InvalidMleProof} from "../MleProofErrors.sol";\n' + IMPORT_SUB)
P(f, """        (uint64 c0, uint64 c1, uint64 c2) = verifierMessageField64x3(ts);
        coeffs = new GoldilocksExt3.Ext3[](count);
        coeffs[0] = GoldilocksExt3.one();
""", """        (uint64 c0, uint64 c1, uint64 c2) = verifierMessageField64x3(ts);
        GasProbe.ext3Count(52, count - 1);
        coeffs = new GoldilocksExt3.Ext3[](count);
        coeffs[0] = GoldilocksExt3.one();
""")

# ---------------------------------------------------------------- WhirLinearAlgebra
f = "spongefish/WhirLinearAlgebra.sol"
P(f, 'import {InvalidMleProof} from "../MleProofErrors.sol";\n',
     'import {InvalidMleProof} from "../MleProofErrors.sol";\n' + IMPORT_SUB)
P(f, """        uint256 start
    ) internal pure returns (GoldilocksExt3.Ext3 memory result) {
        assembly {
            let p := P

            // result = 1
""", """        uint256 start
    ) internal pure returns (GoldilocksExt3.Ext3 memory result) {
        if (GasProbe.COUNTING) {
            uint256 iterations = point.length > start ? point.length - start : 0;
            if (x.c1 == 0 && x.c2 == 0) {
                GasProbe.ext3Count(60, iterations);
                GasProbe.scalarCount(61, iterations);
                GasProbe.baseCount(61, iterations);
            } else {
                GasProbe.ext3Count(62, 3 * iterations);
            }
        }
        assembly {
            let p := P

            // result = 1
""")
P(f, """        if (point.length != evalPoint.length) revert InvalidMleProof();
        assembly {
            let p := P
            let res0 := 1
            let res1 := 0
            let res2 := 0

            let pLen := mload(point)
""", """        if (point.length != evalPoint.length) revert InvalidMleProof();
        GasProbe.ext3Count(63, 3 * point.length);
        assembly {
            let p := P
            let res0 := 1
            let res1 := 0
            let res2 := 0

            let pLen := mload(point)
""")
P(f, """        if (start > arr.length || count > arr.length - start) revert InvalidMleProof();
        uint256 size = 1 << count;
        weights = new GoldilocksExt3.Ext3[](size);
""", """        if (start > arr.length || count > arr.length - start) revert InvalidMleProof();
        uint256 size = 1 << count;
        GasProbe.ext3Count(53, 2 * (size - 1));
        weights = new GoldilocksExt3.Ext3[](size);
""")
P(f, """        uint256 aLen = a.length;
        uint256 bLen = b.length;
        result = new GoldilocksExt3.Ext3[](aLen * bLen);
""", """        uint256 aLen = a.length;
        uint256 bLen = b.length;
        GasProbe.ext3Count(64, aLen * bLen);
        result = new GoldilocksExt3.Ext3[](aLen * bLen);
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
        _phaseIntermediateRounds(ts, transcript, hints, params, vs);

        // Phase 4: Final vector + final Merkle open
        GoldilocksExt3.Ext3[] memory finalVector = _phaseFinalVectorAndMerkle(ts, transcript, hints, params, vs);

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
        _phaseIntermediateRounds(ts, transcript, hints, params, vs);

        // Phase 4: Final vector + final Merkle open
        GoldilocksExt3.Ext3[] memory finalVector = _phaseFinalVectorAndMerkle(ts, transcript, hints, params, vs);
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
        GoldilocksExt3.Ext3[] memory allOodPoints = new GoldilocksExt3.Ext3[](totalOodPoints);
        GoldilocksExt3.Ext3[][] memory perCommitOod;
        (perCommitOod, allOodPoints) = _receiveCommitmentsAndOod(ts, transcript, expectedRoots, params, vs);
""", """        GasProbe.mark(210);
        // Phase 1a: Receive per-commitment roots and OOD data
        GoldilocksExt3.Ext3[] memory allOodPoints = new GoldilocksExt3.Ext3[](totalOodPoints);
        GoldilocksExt3.Ext3[][] memory perCommitOod;
        (perCommitOod, allOodPoints) = _receiveCommitmentsAndOod(ts, transcript, expectedRoots, params, vs);
        GasProbe.mark(211);
""")
P(f, """            evaluations[i] = GoldilocksExt3.Ext3(e0, e1, e2);
        }

        // Cross-commitment OOD terms are emitted by WHIR prove() only after
""", """            evaluations[i] = GoldilocksExt3.Ext3(e0, e1, e2);
        }
        GasProbe.mark(212);

        // Cross-commitment OOD terms are emitted by WHIR prove() only after
""")
P(f, """        GoldilocksExt3.Ext3[] memory oodMatrix = _completeOodMatrix(ts, transcript, perCommitOod, params);

        // Phase 1b: RLC and sum computation
        GoldilocksExt3.Ext3[] memory vectorRlc = SpongefishWhir.geometricChallenge(ts, totalVectors);
        vs.vectorRlc = vectorRlc;
        vs.numLinearForms = evaluations.length / totalVectors;
        vs.initialConstraintRlc = SpongefishWhir.geometricChallenge(ts, totalOodPoints + vs.numLinearForms);
""", """        GoldilocksExt3.Ext3[] memory oodMatrix = _completeOodMatrix(ts, transcript, perCommitOod, params);
        GasProbe.mark(213);

        // Phase 1b: RLC and sum computation
        GoldilocksExt3.Ext3[] memory vectorRlc = SpongefishWhir.geometricChallenge(ts, totalVectors);
        vs.vectorRlc = vectorRlc;
        vs.numLinearForms = evaluations.length / totalVectors;
        vs.initialConstraintRlc = SpongefishWhir.geometricChallenge(ts, totalOodPoints + vs.numLinearForms);
        GasProbe.mark(214);
""")
P(f, """        _accumulateTheSum(
            vs.theSum, oodMatrix, vectorRlc, vs.initialConstraintRlc, vs.numLinearForms, totalOodPoints, totalVectors
        );
    }
""", """        _accumulateTheSum(
            vs.theSum, oodMatrix, vectorRlc, vs.initialConstraintRlc, vs.numLinearForms, totalOodPoints, totalVectors
        );
        GasProbe.mark(215);
    }
""")
P(f, """        for (uint256 i = 0; i < numRounds; i++) {
            (uint64 c0a, uint64 c0b, uint64 c0c) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            (uint64 c2a, uint64 c2b, uint64 c2c) = SpongefishWhir.proverMessageField64x3(ts, transcript);

            _verifyPow(ts, transcript, powThreshold);
""", """        for (uint256 i = 0; i < numRounds; i++) {
            GasProbe.ext3Count(50, 2);
            (uint64 c0a, uint64 c0b, uint64 c0c) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            (uint64 c2a, uint64 c2b, uint64 c2c) = SpongefishWhir.proverMessageField64x3(ts, transcript);

            _verifyPow(ts, transcript, powThreshold);
""")
P(f, """        RoundParams memory rp = params.rounds[round];

        // Receive new commitment
        bytes32 roundRoot = SpongefishWhir.proverMessageHash(ts, transcript);

        // OOD for this round: ALL points squeezed first, then ALL answers absorbed
        // (matches Rust irs_commit::receive_commitment order)
        GoldilocksExt3.Ext3[] memory roundOodPoints = new GoldilocksExt3.Ext3[](rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            (uint64 c0, uint64 c1, uint64 c2) = SpongefishWhir.verifierMessageField64x3(ts);
            roundOodPoints[i] = GoldilocksExt3.Ext3(c0, c1, c2);
        }
        GoldilocksExt3.Ext3[] memory roundOodAnswers = new GoldilocksExt3.Ext3[](rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            (uint64 a0, uint64 a1, uint64 a2) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            roundOodAnswers[i] = GoldilocksExt3.Ext3(a0, a1, a2);
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
        GoldilocksExt3.Ext3[] memory roundOodPoints = new GoldilocksExt3.Ext3[](rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            (uint64 c0, uint64 c1, uint64 c2) = SpongefishWhir.verifierMessageField64x3(ts);
            roundOodPoints[i] = GoldilocksExt3.Ext3(c0, c1, c2);
        }
        GasProbe.mark(302 + 20 * round);
        GoldilocksExt3.Ext3[] memory roundOodAnswers = new GoldilocksExt3.Ext3[](rp.outDomainSamples);
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            (uint64 a0, uint64 a1, uint64 a2) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            roundOodAnswers[i] = GoldilocksExt3.Ext3(a0, a1, a2);
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
P(f, """        finalVector = new GoldilocksExt3.Ext3[](params.finalSize);
        for (uint256 i = 0; i < params.finalSize; i++) {
            (uint64 c0, uint64 c1, uint64 c2) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            finalVector[i] = GoldilocksExt3.Ext3(c0, c1, c2);
        }

        _verifyPow(ts, transcript, params.finalPowThreshold);

        // The final opening is the same IRS commitment that the next intermediate round would
        // open: the initial commitment when numRounds == 0, otherwise the last round commitment.
        OpenParams memory o = _getOpenParams(params, params.numRounds);
        bool isSplitInitial = params.numRounds == 0 && params.numCommitments > 1;
        uint256[] memory rawFinalIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
""", """        GasProbe.mark(500);
        finalVector = new GoldilocksExt3.Ext3[](params.finalSize);
        for (uint256 i = 0; i < params.finalSize; i++) {
            (uint64 c0, uint64 c1, uint64 c2) = SpongefishWhir.proverMessageField64x3(ts, transcript);
            finalVector[i] = GoldilocksExt3.Ext3(c0, c1, c2);
        }
        GasProbe.mark(501);

        _verifyPow(ts, transcript, params.finalPowThreshold);
        GasProbe.mark(502);

        // The final opening is the same IRS commitment that the next intermediate round would
        // open: the initial commitment when numRounds == 0, otherwise the last round commitment.
        OpenParams memory o = _getOpenParams(params, params.numRounds);
        bool isSplitInitial = params.numRounds == 0 && params.numCommitments > 1;
        uint256[] memory rawFinalIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        GasProbe.mark(503);
""")
P(f, """            GoldilocksExt3.Ext3[] memory finalWeights =
                WhirLinearAlgebra.eqWeightsFrom(vs.allFoldingRandomness, vs.foldIdx - foldingRounds, foldingRounds);
            if (params.numRounds == 0) {
                finalWeights = WhirLinearAlgebra.tensorProduct(vs.vectorRlc, finalWeights);
            }
            GoldilocksExt3.Ext3[] memory finalEvalPoints =
                _computeEvalPoints(rawFinalIndices, rawFinalIndices.length, o.domainGen, o.numCosets, o.cosetSize);
            _consumeVecPrefix(ts, hints, rawFinalIndices.length * o.numCols);
            uint256 rowsStart = ts.hintPos;
            bytes32[] memory rawFinalHashes = new bytes32[](rawFinalIndices.length);
            for (uint256 i = 0; i < rawFinalIndices.length; i++) {
                rawFinalHashes[i] = _keccak256At(hints, ts.hintPos, o.rowBytes);
                ts.hintPos += o.rowBytes;
            }

            ts.hintPos = SpongefishMerkle.verify(vs.prevRoot, o.md, rawFinalIndices, rawFinalHashes, hints, ts.hintPos);
            for (uint256 i = 0; i < finalEvalPoints.length; i++) {
                _requireFinalOpening(
                    finalVector,
                    finalEvalPoints[i],
                    _dotEqWithRow(finalWeights, hints, rowsStart + i * o.rowBytes, o.numCols, o.isBaseField)
                );
            }
        }
    }
""", """            GoldilocksExt3.Ext3[] memory finalWeights =
                WhirLinearAlgebra.eqWeightsFrom(vs.allFoldingRandomness, vs.foldIdx - foldingRounds, foldingRounds);
            if (params.numRounds == 0) {
                finalWeights = WhirLinearAlgebra.tensorProduct(vs.vectorRlc, finalWeights);
            }
            GasProbe.mark(504);
            GoldilocksExt3.Ext3[] memory finalEvalPoints =
                _computeEvalPoints(rawFinalIndices, rawFinalIndices.length, o.domainGen, o.numCosets, o.cosetSize);
            GasProbe.mark(505);
            _consumeVecPrefix(ts, hints, rawFinalIndices.length * o.numCols);
            uint256 rowsStart = ts.hintPos;
            bytes32[] memory rawFinalHashes = new bytes32[](rawFinalIndices.length);
            for (uint256 i = 0; i < rawFinalIndices.length; i++) {
                rawFinalHashes[i] = _keccak256At(hints, ts.hintPos, o.rowBytes);
                ts.hintPos += o.rowBytes;
            }
            GasProbe.mark(506);

            ts.hintPos = SpongefishMerkle.verify(vs.prevRoot, o.md, rawFinalIndices, rawFinalHashes, hints, ts.hintPos);
            GasProbe.mark(507);
            for (uint256 i = 0; i < finalEvalPoints.length; i++) {
                _requireFinalOpening(
                    finalVector,
                    finalEvalPoints[i],
                    _dotEqWithRow(finalWeights, hints, rowsStart + i * o.rowBytes, o.numCols, o.isBaseField)
                );
            }
            GasProbe.mark(508);
        }
    }
""")
P(f, """        uint256 foldStart = vs.foldIdx - params.finalSumcheckRounds;
        GoldilocksExt3.Ext3 memory polyEval =
            _foldEval(finalVector, vs.allFoldingRandomness, foldStart, params.finalSumcheckRounds);
        if (GoldilocksExt3.isZero(polyEval)) revert InvalidMleProof();

        // linear_form_rlc = theSum / polyEval
        GoldilocksExt3.Ext3 memory linearFormRlc = vs.theSum.mul(GoldilocksExt3.inv(polyEval));
""", """        GasProbe.mark(520);
        uint256 foldStart = vs.foldIdx - params.finalSumcheckRounds;
        GoldilocksExt3.Ext3 memory polyEval =
            _foldEval(finalVector, vs.allFoldingRandomness, foldStart, params.finalSumcheckRounds);
        if (GoldilocksExt3.isZero(polyEval)) revert InvalidMleProof();
        GasProbe.mark(521);

        // linear_form_rlc = theSum / polyEval
        GoldilocksExt3.Ext3 memory linearFormRlc = vs.theSum.mul(GoldilocksExt3.inv(polyEval));
        GasProbe.mark(522);
""")
P(f, """            for (uint256 i = 0; i < entry.rlcCoeffs.length; i++) {
                GoldilocksExt3.Ext3 memory mleVal = WhirLinearAlgebra.mleEvaluateUnivariateFrom(
                    entry.univariatePoints[i], vs.allFoldingRandomness, start
                );
""", """            GasProbe.ext3Count(65, entry.rlcCoeffs.length);
            for (uint256 i = 0; i < entry.rlcCoeffs.length; i++) {
                GoldilocksExt3.Ext3 memory mleVal = WhirLinearAlgebra.mleEvaluateUnivariateFrom(
                    entry.univariatePoints[i], vs.allFoldingRandomness, start
                );
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
P(f, """        // In-domain values
        for (uint256 i = 0; i < rawCount; i++) {
            GoldilocksExt3.Ext3 memory val = _dotEqWithRow(eqW, hints, rowOffsets[i], numCols, isBaseField);
            _mulAddToSum(theSum_, val, roundRlc[oodSamples + i]);
        }
    }
""", """        // In-domain values
        for (uint256 i = 0; i < rawCount; i++) {
            GoldilocksExt3.Ext3 memory val = _dotEqWithRow(eqW, hints, rowOffsets[i], numCols, isBaseField);
            _mulAddToSum(theSum_, val, roundRlc[oodSamples + i]);
        }
        GasProbe.ext3Count(57, oodSamples + rawCount);
    }
""")
P(f, """    ) private pure {
        assembly {
            let p := 0xFFFFFFFF00000001
            let mData := add(matrix, 0x20)
            let vData := add(vectorRlc, 0x20)
            let cData := add(constraintRlc, 0x20)
""", """    ) private pure {
        GasProbe.ext3Count(51, count * numVectors + count);
        assembly {
            let p := 0xFFFFFFFF00000001
            let mData := add(matrix, 0x20)
            let vData := add(vectorRlc, 0x20)
            let cData := add(constraintRlc, 0x20)
""")
P(f, """        if (offset > buf.length || len > buf.length - offset) revert InvalidMleProof();
        assembly ("memory-safe") {
            // KECCAK256 only reads memory. Use ephemeral free-memory scratch;
""", """        if (offset > buf.length || len > buf.length - offset) revert InvalidMleProof();
        GasProbe.keccakCount(31, 1, len);
        assembly ("memory-safe") {
            // KECCAK256 only reads memory. Use ephemeral free-memory scratch;
""")
P(f, """        if (threshold == type(uint64).max) return;
        bytes memory challenge = SpongefishWhir.verifierMessage(ts, 32);
        bytes memory nonceBytes = SpongefishWhir.proverMessage(ts, transcript, 8);
""", """        if (threshold == type(uint64).max) return;
        GasProbe.keccakCount(32, 1, 64);
        bytes memory challenge = SpongefishWhir.verifierMessage(ts, 32);
        bytes memory nonceBytes = SpongefishWhir.proverMessage(ts, transcript, 8);
""")
P(f, """        OpenParams memory o = _getOpenParams(params, round);

        uint256[] memory rawIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        uint256 rawCount = rawIndices.length;

        if (round == 0 && params.numCommitments > 1) {
            _openSplitCommitments(ts, hints, params, vs, o, rawIndices, rawCount, roundOodAnswers, roundOodPoints);
        } else {
            // Standard mode (single commitment or round > 0)
            _consumeVecPrefix(ts, hints, rawCount * o.numCols);

            bytes32[] memory rawLeafHashes = new bytes32[](rawCount);
            uint256[] memory rowOffsets = new uint256[](rawCount);

            for (uint256 i = 0; i < rawCount; i++) {
                uint256 rowOff = ts.hintPos;
                rowOffsets[i] = rowOff;
                rawLeafHashes[i] = _keccak256At(hints, rowOff, o.rowBytes);
                ts.hintPos += o.rowBytes;
            }

            GoldilocksExt3.Ext3[] memory inDomainEvalPoints =
                _computeEvalPoints(rawIndices, rawCount, o.domainGen, o.numCosets, o.cosetSize);

            ts.hintPos = SpongefishMerkle.verify(vs.prevRoot, o.md, rawIndices, rawLeafHashes, hints, ts.hintPos);

            _addConstraintValues(
""", """        OpenParams memory o = _getOpenParams(params, round);

        uint256[] memory rawIndices = _challengeIndices(ts, o.cl, o.inDomainSamples);
        uint256 rawCount = rawIndices.length;
        GasProbe.mark(305 + 20 * round);

        if (round == 0 && params.numCommitments > 1) {
            _openSplitCommitments(ts, hints, params, vs, o, rawIndices, rawCount, roundOodAnswers, roundOodPoints);
        } else {
            // Standard mode (single commitment or round > 0)
            _consumeVecPrefix(ts, hints, rawCount * o.numCols);

            bytes32[] memory rawLeafHashes = new bytes32[](rawCount);
            uint256[] memory rowOffsets = new uint256[](rawCount);

            for (uint256 i = 0; i < rawCount; i++) {
                uint256 rowOff = ts.hintPos;
                rowOffsets[i] = rowOff;
                rawLeafHashes[i] = _keccak256At(hints, rowOff, o.rowBytes);
                ts.hintPos += o.rowBytes;
            }
            GasProbe.mark(306 + 20 * round);

            GoldilocksExt3.Ext3[] memory inDomainEvalPoints =
                _computeEvalPoints(rawIndices, rawCount, o.domainGen, o.numCosets, o.cosetSize);
            GasProbe.mark(307 + 20 * round);

            ts.hintPos = SpongefishMerkle.verify(vs.prevRoot, o.md, rawIndices, rawLeafHashes, hints, ts.hintPos);
            GasProbe.mark(308 + 20 * round);

            _addConstraintValues(
""")
P(f, """        for (uint256 c = 0; c < params.numCommitments; c++) {
            _consumeVecPrefix(ts, hints, rawCount * o.numCols);

            perCommitRowOffsets[c] = new uint256[](rawCount);
            bytes32[] memory rawLeafHashes = new bytes32[](rawCount);
            for (uint256 i = 0; i < rawCount; i++) {
                perCommitRowOffsets[c][i] = ts.hintPos;
                rawLeafHashes[i] = _keccak256At(hints, ts.hintPos, o.rowBytes);
                ts.hintPos += o.rowBytes;
            }

            // SpongefishMerkle uses the index array as alternating layer
            // scratch, so retain the canonical query list for later groups.
            uint256[] memory idxCopy = new uint256[](rawCount);
            for (uint256 i = 0; i < rawCount; i++) {
                idxCopy[i] = rawIndices[i];
            }

            ts.hintPos = SpongefishMerkle.verify(vs.initialRoots[c], o.md, idxCopy, rawLeafHashes, hints, ts.hintPos);
        }

        GoldilocksExt3.Ext3[] memory inDomainEvalPoints =
            _computeEvalPoints(rawIndices, rawCount, o.domainGen, o.numCosets, o.cosetSize);

        // Compute constraint values using per-commitment rows + vector RLC.
""", """        for (uint256 c = 0; c < params.numCommitments; c++) {
            _consumeVecPrefix(ts, hints, rawCount * o.numCols);

            perCommitRowOffsets[c] = new uint256[](rawCount);
            bytes32[] memory rawLeafHashes = new bytes32[](rawCount);
            for (uint256 i = 0; i < rawCount; i++) {
                perCommitRowOffsets[c][i] = ts.hintPos;
                rawLeafHashes[i] = _keccak256At(hints, ts.hintPos, o.rowBytes);
                ts.hintPos += o.rowBytes;
            }
            GasProbe.mark(450 + 10 * c);

            // SpongefishMerkle uses the index array as alternating layer
            // scratch, so retain the canonical query list for later groups.
            uint256[] memory idxCopy = new uint256[](rawCount);
            for (uint256 i = 0; i < rawCount; i++) {
                idxCopy[i] = rawIndices[i];
            }

            ts.hintPos = SpongefishMerkle.verify(vs.initialRoots[c], o.md, idxCopy, rawLeafHashes, hints, ts.hintPos);
            GasProbe.mark(451 + 10 * c);
        }
        GasProbe.mark(306);

        GoldilocksExt3.Ext3[] memory inDomainEvalPoints =
            _computeEvalPoints(rawIndices, rawCount, o.domainGen, o.numCosets, o.cosetSize);
        GasProbe.mark(307);

        // Compute constraint values using per-commitment rows + vector RLC.
""")
P(f, """        RoundParams memory rp = params.rounds[0];
        uint256 ff = params.initialSumcheckRounds;
        uint256 eqBase = vs.foldIdx - ff;
        GoldilocksExt3.Ext3[] memory eqW = WhirLinearAlgebra.eqWeightsFrom(vs.allFoldingRandomness, eqBase, ff);

        uint256 constraintCount = rp.outDomainSamples + rawCount;
        GoldilocksExt3.Ext3[] memory roundRlc = SpongefishWhir.geometricChallenge(ts, constraintCount);

        // OOD values
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            _mulAddToSum(vs.theSum, roundOodAnswers[i], roundRlc[i]);
        }

        // In-domain values: combine per-commitment rows with vector RLC
        for (uint256 i = 0; i < rawCount; i++) {
            // Each commitment row contains numVectors consecutive subvectors.
            GoldilocksExt3.Ext3 memory combined = GoldilocksExt3.zero();
            for (uint256 c = 0; c < params.numCommitments; c++) {
                GoldilocksExt3.Ext3 memory perCommitDot = _dotGroupedRow(
                    eqW,
                    vs.vectorRlc,
                    c * params.numVectors,
                    params.numVectors,
                    hints,
                    perCommitRowOffsets[c][i],
                    isBaseField
                );
                _addToExt3(combined, perCommitDot);
            }
            _mulAddToSum(vs.theSum, combined, roundRlc[rp.outDomainSamples + i]);
        }

        // Store round constraints for FinalClaim
""", """        RoundParams memory rp = params.rounds[0];
        uint256 ff = params.initialSumcheckRounds;
        uint256 eqBase = vs.foldIdx - ff;
        GasProbe.mark(420);
        GoldilocksExt3.Ext3[] memory eqW = WhirLinearAlgebra.eqWeightsFrom(vs.allFoldingRandomness, eqBase, ff);
        GasProbe.mark(421);

        uint256 constraintCount = rp.outDomainSamples + rawCount;
        GoldilocksExt3.Ext3[] memory roundRlc = SpongefishWhir.geometricChallenge(ts, constraintCount);
        GasProbe.mark(422);

        // OOD values
        for (uint256 i = 0; i < rp.outDomainSamples; i++) {
            _mulAddToSum(vs.theSum, roundOodAnswers[i], roundRlc[i]);
        }

        // In-domain values: combine per-commitment rows with vector RLC
        for (uint256 i = 0; i < rawCount; i++) {
            // Each commitment row contains numVectors consecutive subvectors.
            GoldilocksExt3.Ext3 memory combined = GoldilocksExt3.zero();
            for (uint256 c = 0; c < params.numCommitments; c++) {
                GoldilocksExt3.Ext3 memory perCommitDot = _dotGroupedRow(
                    eqW,
                    vs.vectorRlc,
                    c * params.numVectors,
                    params.numVectors,
                    hints,
                    perCommitRowOffsets[c][i],
                    isBaseField
                );
                _addToExt3(combined, perCommitDot);
            }
            _mulAddToSum(vs.theSum, combined, roundRlc[rp.outDomainSamples + i]);
        }
        GasProbe.ext3Count(57, rp.outDomainSamples + rawCount);
        GasProbe.mark(423);

        // Store round constraints for FinalClaim
""")
P(f, """        vs.roundConstraints[1] =
            RoundConstraintEntry({rlcCoeffs: roundRlc, univariatePoints: allEvalPoints, numVariables: rp.numVariables});
    }
""", """        vs.roundConstraints[1] =
            RoundConstraintEntry({rlcCoeffs: roundRlc, univariatePoints: allEvalPoints, numVariables: rp.numVariables});
        GasProbe.mark(424);
    }
""")
P(f, """        combined = GoldilocksExt3.zero();
        uint256 elementBytes = isBaseField ? 8 : 24;
        uint256 subvectorBytes = eqW.length * elementBytes;
""", """        combined = GoldilocksExt3.zero();
        uint256 elementBytes = isBaseField ? 8 : 24;
        uint256 subvectorBytes = eqW.length * elementBytes;
        GasProbe.ext3Count(56, numVectors);
""")
P(f, """        pts = new GoldilocksExt3.Ext3[](rawCount);
        for (uint256 i = 0; i < rawCount; i++) {
            uint256 idx = rawIndices[i];
""", """        pts = new GoldilocksExt3.Ext3[](rawCount);
        GasProbe.baseCount(58, rawCount);
        for (uint256 i = 0; i < rawCount; i++) {
            uint256 idx = rawIndices[i];
""")
P(f, """        RoundParams memory rp = params.rounds[round];

        // eq_weights from last folding randomness (read directly, no copy)
        uint256 ff = (round == 0) ? params.initialSumcheckRounds : params.rounds[round - 1].sumcheckRounds;
        uint256 eqBase = vs.foldIdx - ff;
        GoldilocksExt3.Ext3[] memory eqW = WhirLinearAlgebra.eqWeightsFrom(vs.allFoldingRandomness, eqBase, ff);

        // Constraint RLC
        uint256 constraintCount = rp.outDomainSamples + rawCount;
        GoldilocksExt3.Ext3[] memory roundRlc = SpongefishWhir.geometricChallenge(ts, constraintCount);

        // Add OOD + in-domain constraint values to theSum
        _addOodAndInDomainToSum(
            vs.theSum,
            roundOodAnswers,
            roundRlc,
            rp.outDomainSamples,
            eqW,
            hints,
            rowOffsets,
            rawCount,
            numCols,
            isBaseField
        );

        // Build evaluation points for FinalClaim
""", """        RoundParams memory rp = params.rounds[round];

        // eq_weights from last folding randomness (read directly, no copy)
        uint256 ff = (round == 0) ? params.initialSumcheckRounds : params.rounds[round - 1].sumcheckRounds;
        uint256 eqBase = vs.foldIdx - ff;
        GasProbe.mark(420);
        GoldilocksExt3.Ext3[] memory eqW = WhirLinearAlgebra.eqWeightsFrom(vs.allFoldingRandomness, eqBase, ff);
        GasProbe.mark(421);

        // Constraint RLC
        uint256 constraintCount = rp.outDomainSamples + rawCount;
        GoldilocksExt3.Ext3[] memory roundRlc = SpongefishWhir.geometricChallenge(ts, constraintCount);
        GasProbe.mark(422);

        // Add OOD + in-domain constraint values to theSum
        _addOodAndInDomainToSum(
            vs.theSum,
            roundOodAnswers,
            roundRlc,
            rp.outDomainSamples,
            eqW,
            hints,
            rowOffsets,
            rawCount,
            numCols,
            isBaseField
        );
        GasProbe.mark(423);

        // Build evaluation points for FinalClaim
""")
P(f, """        vs.roundConstraints[1 + round] =
            RoundConstraintEntry({rlcCoeffs: roundRlc, univariatePoints: allEvalPoints, numVariables: rp.numVariables});
    }
""", """        vs.roundConstraints[1 + round] =
            RoundConstraintEntry({rlcCoeffs: roundRlc, univariatePoints: allEvalPoints, numVariables: rp.numVariables});
        GasProbe.mark(424);
    }
""")
P(f, """    ) private pure returns (GoldilocksExt3.Ext3 memory result) {
        assembly {
            let p := 0xFFFFFFFF00000001
            let size := mload(vec)
            let vecData := add(vec, 0x20) // pointer to array of Ext3 pointers
""", """    ) private pure returns (GoldilocksExt3.Ext3 memory result) {
        GasProbe.ext3Count(59, vec.length > 0 ? 2 * (vec.length - 1) : 0);
        assembly {
            let p := 0xFFFFFFFF00000001
            let size := mload(vec)
            let vecData := add(vec, 0x20) // pointer to array of Ext3 pointers
""")
P(f, """        uint256 elementBytes = isBaseField ? 8 : 24;
        if (rowOff > hints.length || numCols > (hints.length - rowOff) / elementBytes) {
            revert InvalidMleProof();
        }
        assembly {
""", """        uint256 elementBytes = isBaseField ? 8 : 24;
        if (rowOff > hints.length || numCols > (hints.length - rowOff) / elementBytes) {
            revert InvalidMleProof();
        }
        if (isBaseField) GasProbe.scalarCount(54, numCols);
        else GasProbe.ext3Count(55, numCols);
        assembly {
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
P(f, """        combined = GoldilocksExt3.zero();
        for (uint256 row = 0; row < gates.length; ++row) {
            GateInfoV2 calldata info = gates[row];
            GoldilocksExt3.Ext3 memory filter =
                _computeFilter(info, constants[uint256(info.selectorIndex)], numSelectors > 1);
            // Metadata for every gate was validated above. A zero selector filter
            // therefore makes this gate's entire contribution identically zero;
            // avoid evaluating expensive inactive Poseidon/coset constraints.
            if (GoldilocksExt3.isZero(filter)) continue;
            GoldilocksExt3.Ext3 memory reduced;
            // Poseidon is by far the largest Plonky2 gate. Reduce its constraints
            // inside the linked library so 123/24 Ext3 values are never ABI-copied
            // back into this evaluator, and pass the already validated wire vector
            // directly instead of allocating another struct array prefix.
            if (info.gateId == GATE_POSEIDON) {
                reduced = PoseidonGateExt3.evalPoseidonReduced(wires, alpha);
            } else if (info.gateId == GATE_POSEIDON_MDS) {
                reduced = PoseidonGateExt3.evalPoseidonMdsReduced(wires, alpha);
            } else {
                GoldilocksExt3.Ext3[] memory unfiltered =
                    _evaluateUnfiltered(info, wires, constants, publicHash, numSelectors);
                if (unfiltered.length != uint256(info.numConstraints)) revert InvalidMleVerifierConfiguration();
                reduced = GoldilocksExt3.reduceWithPowers(unfiltered, alpha);
            }
            combined = GoldilocksExt3.add(combined, GoldilocksExt3.mul(filter, reduced));
        }
""", """        combined = GoldilocksExt3.zero();
        for (uint256 row = 0; row < gates.length; ++row) {
            GasProbe.mark(610 + 10 * row);
            GateInfoV2 calldata info = gates[row];
            GoldilocksExt3.Ext3 memory filter =
                _computeFilter(info, constants[uint256(info.selectorIndex)], numSelectors > 1);
            GasProbe.mark(611 + 10 * row);
            // Metadata for every gate was validated above. A zero selector filter
            // therefore makes this gate's entire contribution identically zero;
            // avoid evaluating expensive inactive Poseidon/coset constraints.
            if (GoldilocksExt3.isZero(filter)) continue;
            GoldilocksExt3.Ext3 memory reduced;
            // Poseidon is by far the largest Plonky2 gate. Reduce its constraints
            // inside the linked library so 123/24 Ext3 values are never ABI-copied
            // back into this evaluator, and pass the already validated wire vector
            // directly instead of allocating another struct array prefix.
            if (info.gateId == GATE_POSEIDON) {
                reduced = PoseidonGateExt3.evalPoseidonReduced(wires, alpha);
            } else if (info.gateId == GATE_POSEIDON_MDS) {
                reduced = PoseidonGateExt3.evalPoseidonMdsReduced(wires, alpha);
            } else {
                GoldilocksExt3.Ext3[] memory unfiltered =
                    _evaluateUnfiltered(info, wires, constants, publicHash, numSelectors);
                GasProbe.mark(612 + 10 * row);
                if (unfiltered.length != uint256(info.numConstraints)) revert InvalidMleVerifierConfiguration();
                reduced = GoldilocksExt3.reduceWithPowers(unfiltered, alpha);
            }
            GasProbe.mark(613 + 10 * row);
            combined = GoldilocksExt3.add(combined, GoldilocksExt3.mul(filter, reduced));
            GasProbe.mark(614 + 10 * row);
        }
""")
P(f, """        if (wires.length < 4 * count || constants.length < constantOffset + 2) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](count);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
""", """        if (wires.length < 4 * count || constants.length < constantOffset + 2) revert InvalidMleProof();
        output = new GoldilocksExt3.Ext3[](count);
        GasProbe.ext3Count(70, 3 * count);
        assembly ("memory-safe") {
            function mul3(a0, a1, a2, b0, b1, b2) -> r0, r1, r2 {
                let p := 0xFFFFFFFF00000001
                let t0 := addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p)
""")

# ---------------------------------------------------------------- PoseidonGateExt3
f = "PoseidonGateExt3.sol"
P(f, 'import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";\n',
     'import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";\n' + IMPORT_ROOT)
P(f, """        if (wires.length < POSEIDON_WIRES) revert InvalidMleProof();

        bytes memory allRC = PoseidonConstants.ALL_ROUND_CONSTANTS;
""", """        GasProbe.mark(700);
        if (wires.length < POSEIDON_WIRES) revert InvalidMleProof();

        bytes memory allRC = PoseidonConstants.ALL_ROUND_CONSTANTS;
""")
P(f, """        _evalSwapDelta(wires, statePtr, constraintsPtr);
        uint256 next = _firstFullRounds(wires, statePtr, scratchPtr, constraintsPtr, mdsPtr, allRC);
        _partialFirstConstantLayer(statePtr, pfrc);
        _mdsPartialLayerInit(statePtr, scratchPtr, pim);
        next = _partialRounds(wires, statePtr, scratchPtr, constraintsPtr, prc, prvs, prwh, next, mdsPtr);
        next = _secondFullRounds(wires, statePtr, scratchPtr, constraintsPtr, mdsPtr, allRC, next);
        _outputConstraints(wires, statePtr, constraintsPtr, next);
        reduced = _reduceRaw(constraintsPtr, POSEIDON_CONSTRAINTS, alpha);
    }
""", """        GasProbe.mark(701);
        _evalSwapDelta(wires, statePtr, constraintsPtr);
        GasProbe.ext3Count(83, 5);
        GasProbe.mark(702);
        uint256 next = _firstFullRounds(wires, statePtr, scratchPtr, constraintsPtr, mdsPtr, allRC);
        GasProbe.mark(703);
        _partialFirstConstantLayer(statePtr, pfrc);
        _mdsPartialLayerInit(statePtr, scratchPtr, pim);
        GasProbe.scalarCount(84, 121);
        GasProbe.mark(704);
        next = _partialRounds(wires, statePtr, scratchPtr, constraintsPtr, prc, prvs, prwh, next, mdsPtr);
        GasProbe.mark(705);
        next = _secondFullRounds(wires, statePtr, scratchPtr, constraintsPtr, mdsPtr, allRC, next);
        GasProbe.mark(706);
        _outputConstraints(wires, statePtr, constraintsPtr, next);
        GasProbe.mark(707);
        reduced = _reduceRaw(constraintsPtr, POSEIDON_CONSTRAINTS, alpha);
        GasProbe.mark(708);
    }
""")
P(f, """    function _sboxOne(uint256 valuePtr) private pure {
        assembly ("memory-safe") {
""", """    function _sboxOne(uint256 valuePtr) private pure {
        GasProbe.ext3Count(80, 4);
        assembly ("memory-safe") {
""")
P(f, """    function _mdsLayer(uint256 statePtr, uint256 scratchPtr, uint256 mdsPtr) private pure {
        assembly ("memory-safe") {
""", """    function _mdsLayer(uint256 statePtr, uint256 scratchPtr, uint256 mdsPtr) private pure {
        GasProbe.scalarCount(81, 145);
        assembly ("memory-safe") {
""")
P(f, """        uint256 m00
    ) private pure {
        assembly ("memory-safe") {
            let p := P
            let s0 := mload(statePtr)
""", """        uint256 m00
    ) private pure {
        GasProbe.scalarCount(85, 23);
        assembly ("memory-safe") {
            let p := P
            let s0 := mload(statePtr)
""")
P(f, """        returns (GoldilocksExt3.Ext3 memory reduced)
    {
        assembly ("memory-safe") {
            function extMul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                let p := P
                c0 := addmod(mulmod(a0, b0, p), mulmod(2, addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p), p), p)
                c1 := addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p)
                c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            }
            let p := P
            let alpha0 := mload(alpha)
""", """        returns (GoldilocksExt3.Ext3 memory reduced)
    {
        GasProbe.ext3Count(82, count);
        assembly ("memory-safe") {
            function extMul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                let p := P
                c0 := addmod(mulmod(a0, b0, p), mulmod(2, addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p), p), p)
                c1 := addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p)
                c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            }
            let p := P
            let alpha0 := mload(alpha)
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
