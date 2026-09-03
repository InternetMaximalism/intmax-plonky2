// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";
import {CompactMleProofV2} from "../src/CompactMleProofV2.sol";
import {CircuitConfigV2} from "../src/CircuitConfigV2.sol";
import {OuterLogupExt3Verifier} from "../src/OuterLogupExt3Verifier.sol";
import {PackedClaimExt3} from "../src/PackedClaimExt3.sol";
import {Plonky2GateEvaluatorExt3} from "../src/Plonky2GateEvaluatorExt3.sol";
import {PoseidonPublicInputsHash} from "../src/PoseidonPublicInputsHash.sol";
import {TranscriptV2} from "../src/TranscriptV2.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";
import {SpongefishWhir} from "../src/spongefish/SpongefishWhir.sol";
import {MAX_COMPACT_PROOF_BYTES_V2} from "../src/generated/MleWhirV2.sol";
import {
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
    MLE_PROTOCOL_VERSION_CURRENT,
    NUM_PACKED_VECTORS_PER_GROUP_V2,
    NUM_PCS_CLAIMS_V2,
    NUM_PCS_GROUPS_V2,
    NUM_PCS_TERMINAL_POINTS_V2,
    PACKED_BOUND_CLAIM_MASK_V2,
    PACKED_PCS_SCHEMA_DOMAIN_V2,
    PACKED_VARIABLE_ORDER_CODE_V2
} from "../src/generated/MleWhirV2.sol";

/// @notice Release gate for a sampled degree-13/max-width resource proof.
/// @dev This fixture reaches the row, wire and gate-constraint maxima but has one public input and
/// five configured gate rows. It is not evidence for every simultaneous combination of the wider
/// generic parser caps. Parent production profiles have separate explicit admission and real-proof
/// tests. The fixture is produced by the ignored, explicit Rust resource generator; no Solidity-
/// side reconstruction or hand-patched config is used.
contract V2ResourceEnvelopeTest is Test {
    string private constant FIXTURE = "test/fixtures/v2_max_resource.json";
    uint256 private constant MAX_PRODUCTION_VERIFY_GAS = 30_000_000;

    struct ResourceFixture {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes compact;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    /// @dev Diagnostic-only gas split. This deliberately has no envelope
    /// assertion so `forge test --flamegraph` can profile a successful run.
    function test_profileMaxResourceCoreAndCalldata() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);

        bytes memory coreCalldata = abi.encodeCall(MleVerifierV2.verify, (fixture.proof, fixture.config));
        emit log_named_uint("sampled max-row core calldata bytes", coreCalldata.length);
        emit log_named_uint("sampled max-row core calldata intrinsic gas", _calldataIntrinsicGas(coreCalldata));

        uint256 beforeGas = gasleft();
        assertTrue(core.verify(fixture.proof, fixture.config), "sampled max-row v2 proof");
        emit log_named_uint("sampled max-row core measured execution gas", beforeGas - gasleft());
    }

    function test_profileMaxResourceCompactCalldata() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);

        bytes memory compactCalldata = abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (fixture.compact));
        emit log_named_uint("sampled max-row compact calldata bytes", compactCalldata.length);
        emit log_named_uint("sampled max-row compact calldata intrinsic gas", _calldataIntrinsicGas(compactCalldata));

        uint256 beforeGas = gasleft();
        assertTrue(pinned.verifyCompact(fixture.compact), "sampled max-row compact v2 proof");
        emit log_named_uint("sampled max-row compact measured execution gas", beforeGas - gasleft());
    }

    function test_profileMaxResourceCompactDecoder() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);

        uint256 beforeGas = gasleft();
        MleVerifierV2.MleProof memory decoded = pinned.decodeCompactMleProof(fixture.compact);
        emit log_named_uint("profile compact decode plus ABI return gas", beforeGas - gasleft());
        assertEq(decoded.protocolVersion, MLE_PROTOCOL_VERSION_CURRENT);

        bytes32 piHash;
        beforeGas = gasleft();
        uint8 verdict = this.profileCompactClassifierDecodeOnly(fixture.compact, fixture.config.circuit, piHash);
        emit log_named_uint("profile compact classifier decode-only gas", beforeGas - gasleft());
        assertEq(verdict, 4);

        (uint256 bodyGas, bytes32 bodySink) = this.profileCompactDecodeBody(fixture.compact, fixture.config.circuit);
        emit log_named_uint("profile compact decoder body gas", bodyGas);
        assertTrue(bodySink != bytes32(0));

        bytes memory encodedExt3 = new bytes(24 * 793);
        (uint256 naiveGas, bytes32 naiveSink) = this.profileNaiveExt3VectorDecode(encodedExt3, 793);
        (uint256 bulkGas, bytes32 bulkSink) = this.profileBulkExt3VectorDecode(encodedExt3, 793);
        emit log_named_uint("profile naive 793 Ext3 allocation/fill gas", naiveGas);
        emit log_named_uint("profile bulk 793 Ext3 allocation/fill gas", bulkGas);
        assertEq(naiveSink, bulkSink);
    }

    function test_profileOneWhirPowCheck() external {
        (uint256 used, bytes32 sink) = this.profileOneWhirPowCheck();
        emit log_named_uint("profile one active WHIR PoW verifier check gas", used);
        assertTrue(sink != bytes32(0));
    }

    function profileOneWhirPowCheck() external view returns (uint256 gasUsed, bytes32 sink) {
        SpongefishWhir.TranscriptState memory ts = SpongefishWhir.initTranscript("protocol", "session", "instance");
        bytes memory transcript = hex"0102030405060708";
        uint256 beforeGas = gasleft();
        bytes memory challenge = SpongefishWhir.verifierMessage(ts, 32);
        bytes memory nonceBytes = SpongefishWhir.proverMessage(ts, transcript, 8);
        assembly ("memory-safe") {
            mstore(0x00, mload(add(challenge, 0x20)))
            mstore(0x20, shl(192, shr(192, mload(add(nonceBytes, 0x20)))))
            sink := keccak256(0x00, 0x40)
        }
        gasUsed = beforeGas - gasleft();
    }

    function profileCompactDecodeBody(bytes calldata compact, CircuitConfigV2.Parameters memory circuit)
        external
        view
        returns (uint256 gasUsed, bytes32 sink)
    {
        uint256 beforeGas = gasleft();
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decode(compact, circuit);
        sink = keccak256(
            abi.encode(
                proof.protocolVersion,
                proof.whirHints.length,
                proof.logPreprocessed[proof.logPreprocessed.length - 1],
                proof.gateWitness[proof.gateWitness.length - 1]
            )
        );
        gasUsed = beforeGas - gasleft();
    }

    /// @dev Test-only profiling harness for the compact decode/PI-classification prefix. Keeping
    /// this outside `PinnedMleVerifierV2` ensures deployed production bytecode has no path that
    /// can return a valid verdict without first executing the cryptographic verifier.
    function profileCompactClassifierDecodeOnly(
        bytes calldata compact,
        CircuitConfigV2.Parameters memory circuit,
        bytes32 expectedPiHash
    ) external pure returns (uint8) {
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decode(compact, circuit);
        if (proof.publicInputs.length != 8) return 4;
        uint256 hash = uint256(expectedPiHash);
        for (uint256 i = 0; i < 8; ++i) {
            if (proof.publicInputs[i] != ((hash >> (224 - i * 32)) & 0xffffffff)) return 4;
        }
        return 1;
    }

    function profileNaiveExt3VectorDecode(bytes calldata encoded, uint256 count)
        external
        view
        returns (uint256 gasUsed, bytes32 sink)
    {
        uint256 beforeGas = gasleft();
        GoldilocksExt3.Ext3[] memory values = new GoldilocksExt3.Ext3[](count);
        for (uint256 i = 0; i < count; ++i) {
            uint256 offset = 24 * i;
            values[i] = GoldilocksExt3.Ext3({
                c0: _profileReadU64Le(encoded, offset),
                c1: _profileReadU64Le(encoded, offset + 8),
                c2: _profileReadU64Le(encoded, offset + 16)
            });
        }
        sink = keccak256(abi.encode(values[values.length - 1]));
        gasUsed = beforeGas - gasleft();
    }

    function profileBulkExt3VectorDecode(bytes calldata encoded, uint256 count)
        external
        view
        returns (uint256 gasUsed, bytes32 sink)
    {
        require(encoded.length == count * 24);
        uint256 beforeGas = gasleft();
        GoldilocksExt3.Ext3[] memory values;
        assembly ("memory-safe") {
            function bswap64(x) -> y {
                y := or(and(shr(8, x), 0x00FF00FF00FF00FF), and(shl(8, x), 0xFF00FF00FF00FF00))
                y := or(and(shr(16, y), 0x0000FFFF0000FFFF), and(shl(16, y), 0xFFFF0000FFFF0000))
                y := and(or(shr(32, y), shl(32, y)), 0xFFFFFFFFFFFFFFFF)
            }
            values := mload(0x40)
            mstore(values, count)
            let table := add(values, 0x20)
            let records := add(table, mul(count, 0x20))
            let input := encoded.offset
            let p := 0xFFFFFFFF00000001
            for { let i := 0 } lt(i, count) { i := add(i, 1) } {
                let record := add(records, mul(i, 0x60))
                mstore(add(table, mul(i, 0x20)), record)
                let source := add(input, mul(i, 24))
                let c0 := bswap64(shr(192, calldataload(source)))
                let c1 := bswap64(shr(192, calldataload(add(source, 8))))
                let c2 := bswap64(shr(192, calldataload(add(source, 16))))
                if iszero(and(and(lt(c0, p), lt(c1, p)), lt(c2, p))) { revert(0, 0) }
                mstore(record, c0)
                mstore(add(record, 0x20), c1)
                mstore(add(record, 0x40), c2)
            }
            mstore(0x40, add(records, mul(count, 0x60)))
        }
        sink = keccak256(abi.encode(values[values.length - 1]));
        gasUsed = beforeGas - gasleft();
    }

    /// @dev Exact verifier-phase profile over the sampled max-row fixture. Inputs are
    /// already materialized in memory here, so the difference from core.verify
    /// is the calldata/config hashing/canonical-scan/copy envelope.
    function test_profileMaxResourceAtomicPhases() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        uint256 indexBits = 8;

        uint256 beforeGas = gasleft();
        bytes32 configHash = keccak256(abi.encode(fixture.config));
        emit log_named_uint("profile config abi encode plus keccak gas", beforeGas - gasleft());
        assertEq(configHash, core.verificationConfigDigest());

        TranscriptV2.Transcript memory transcript;
        OuterLogupExt3Verifier.Challenges memory challenges;
        GoldilocksExt3.Ext3 memory gateAlpha;
        GoldilocksExt3.Ext3[] memory gateTau;
        beforeGas = gasleft();
        (transcript, challenges, gateAlpha, gateTau) = _deriveProfileTranscript(fixture, core, indexBits);
        emit log_named_uint("profile initial transcript gas", beforeGas - gasleft());

        OuterLogupExt3Verifier.VerificationKey memory vk = OuterLogupExt3Verifier.VerificationKey({
            numVars: fixture.config.circuit.degreeBits,
            gateDegree: fixture.config.circuit.quotientDegreeFactor + 2,
            numConstants: fixture.config.circuit.numConstants,
            numRoutedWires: fixture.config.circuit.numRoutedWires,
            numWires: fixture.config.circuit.numWires,
            kIs: fixture.config.kIs,
            subgroupGenPowers: fixture.config.subgroupGenPowers,
            publicInputWireMap: fixture.config.publicInputWireMap
        });
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = OuterLogupExt3Verifier.TerminalEvaluations({
            preprocessed: fixture.proof.logPreprocessed,
            witness: fixture.proof.logWitness,
            normInverse: fixture.proof.logNormInverse,
            publicInputs: fixture.proof.publicInputs
        });
        GoldilocksExt3.Ext3[] memory logPoint;
        GoldilocksExt3.Ext3[] memory gatePoint;
        GoldilocksExt3.Ext3 memory gateFinalClaim;
        beforeGas = gasleft();
        (logPoint, gatePoint, gateFinalClaim, transcript) = OuterLogupExt3Verifier.verify(
            fixture.proof.logProof, fixture.proof.gateProof, vk, challenges, terminal, transcript
        );
        emit log_named_uint("profile outer coupled sumchecks plus log terminal gas", beforeGas - gasleft());

        GoldilocksExt3.Ext3[][] memory indexPoints;
        beforeGas = gasleft();
        indexPoints = _profileAbsorbClaimsAndSampleIndices(transcript, fixture.proof, indexBits);
        emit log_named_uint("profile claim transcript plus index challenges gas", beforeGas - gasleft());

        PackedClaimExt3.UsedClaims memory claims = PackedClaimExt3.UsedClaims({
            logPreprocessed: fixture.proof.logPreprocessed,
            logWitness: fixture.proof.logWitness,
            logNormInverse: fixture.proof.logNormInverse,
            gatePreprocessed: fixture.proof.gatePreprocessed,
            gateWitness: fixture.proof.gateWitness
        });
        PackedClaimExt3.Schema memory schema = PackedClaimExt3.Schema({
            width: fixture.proof.constituentWidth,
            numConstants: fixture.config.circuit.numConstants,
            numRoutedWires: fixture.config.circuit.numRoutedWires,
            numWires: fixture.config.circuit.numWires
        });
        GoldilocksExt3.Ext3[] memory evaluations;
        bytes memory evaluationMask;
        beforeGas = gasleft();
        (evaluations, evaluationMask) = PackedClaimExt3.foldV2UsedCells(claims, schema, indexPoints);
        emit log_named_uint("profile packed five-cell fold gas", beforeGas - gasleft());

        SpongefishWhirVerify.WhirParams memory whir = fixture.config.whir;
        whir.evaluationPoint = _profilePackedPoint(logPoint, indexPoints[0]);
        whir.evaluationPoint2 = _profilePackedPoint(gatePoint, indexPoints[1]);
        whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        bytes32[] memory roots = new bytes32[](NUM_PCS_GROUPS_V2);
        roots[0] = fixture.proof.preprocessedRoot;
        roots[1] = fixture.proof.witnessRoot;
        roots[2] = fixture.proof.normInverseRoot;
        beforeGas = gasleft();
        bool accepted = SpongefishWhirVerify.verifyWhirProofBound(
            abi.encodePacked(fixture.whirProtocolId[0], fixture.whirProtocolId[1]),
            abi.encodePacked(fixture.whirSessionId),
            "",
            fixture.proof.whirTranscript,
            fixture.proof.whirHints,
            evaluations,
            evaluationMask,
            roots,
            whir
        );
        emit log_named_uint("profile WHIR gas", beforeGas - gasleft());
        assertTrue(accepted);

        GoldilocksExt3.Ext3[] memory constants = new GoldilocksExt3.Ext3[](fixture.config.circuit.numConstants);
        for (uint256 i = 0; i < constants.length; ++i) {
            constants[i] = fixture.proof.gatePreprocessed[i];
        }
        beforeGas = gasleft();
        uint256[4] memory publicInputsHash = PoseidonPublicInputsHash.hashNoPad(fixture.proof.publicInputs);
        emit log_named_uint("profile public input Poseidon gas", beforeGas - gasleft());
        beforeGas = gasleft();
        GoldilocksExt3.Ext3 memory gateEvaluation = Plonky2GateEvaluatorExt3.evalCombined(
            fixture.proof.gateWitness,
            constants,
            publicInputsHash,
            gateAlpha,
            fixture.config.gates,
            fixture.config.circuit.numSelectors,
            fixture.config.circuit.numConstants,
            fixture.config.circuit.numGateConstraints,
            fixture.config.circuit.numWires,
            fixture.config.circuit.quotientDegreeFactor
        );
        emit log_named_uint("profile gate evaluation gas", beforeGas - gasleft());
        beforeGas = gasleft();
        GoldilocksExt3.Ext3 memory gateEvaluationPrevalidated = Plonky2GateEvaluatorExt3.evalCombinedPrevalidated(
            fixture.proof.gateWitness,
            constants,
            publicInputsHash,
            gateAlpha,
            fixture.config.gates,
            fixture.config.circuit.numSelectors
        );
        emit log_named_uint("profile gate evaluation prevalidated gas", beforeGas - gasleft());
        assertEq(gateEvaluationPrevalidated.c0, gateEvaluation.c0);
        assertEq(gateEvaluationPrevalidated.c1, gateEvaluation.c1);
        assertEq(gateEvaluationPrevalidated.c2, gateEvaluation.c2);
        beforeGas = gasleft();
        OuterLogupExt3Verifier.verifyGateTerminal(gateTau, gatePoint, gateEvaluation, gateFinalClaim);
        emit log_named_uint("profile gate terminal equality gas", beforeGas - gasleft());
    }

    function test_profileWhirFailureByHintOffset() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        uint256[8] memory offsets = [
            uint256(100),
            fixture.proof.whirHints.length / 8,
            fixture.proof.whirHints.length / 4,
            fixture.proof.whirHints.length * 3 / 8,
            fixture.proof.whirHints.length / 2,
            fixture.proof.whirHints.length * 5 / 8,
            fixture.proof.whirHints.length * 3 / 4,
            fixture.proof.whirHints.length - 1
        ];
        for (uint256 i = 0; i < offsets.length; ++i) {
            uint256 offset = offsets[i];
            fixture.proof.whirHints[offset] = bytes1(uint8(fixture.proof.whirHints[offset]) ^ 1);
            bytes memory callData = abi.encodeCall(MleVerifierV2.verify, (fixture.proof, fixture.config));
            uint256 beforeGas = gasleft();
            (bool ok,) = address(core).staticcall(callData);
            uint256 used = beforeGas - gasleft();
            fixture.proof.whirHints[offset] = bytes1(uint8(fixture.proof.whirHints[offset]) ^ 1);
            emit log_named_uint("profile mutated hint offset", offset);
            emit log_named_uint("profile cumulative reject gas", used);
            assertFalse(ok);
        }
    }

    function test_maxResourceCoreVerificationFitsProductionGasEnvelope() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        bytes memory callData = abi.encodeCall(MleVerifierV2.verify, (fixture.proof, fixture.config));
        uint256 intrinsicGas = _calldataIntrinsicGas(callData);

        uint256 beforeGas = gasleft();
        assertTrue(core.verify(fixture.proof, fixture.config), "sampled max-row v2 proof");
        uint256 used = beforeGas - gasleft();
        uint256 transactionGasUpperBound = used + intrinsicGas;
        emit log_named_uint("sampled max-row MleVerifierV2.verify gas", used);
        emit log_named_uint("sampled max-row core calldata intrinsic gas", intrinsicGas);
        emit log_named_uint("sampled max-row core transaction gas upper bound", transactionGasUpperBound);
        assertLt(
            transactionGasUpperBound,
            MAX_PRODUCTION_VERIFY_GAS,
            "sampled max-row core transaction exceeds production block envelope"
        );
        assertLt(address(core).code.length, 24_576, "v2 core exceeds EIP-170");
    }

    function test_maxResourceCompactPinnedPathFitsProductionGasEnvelope() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory callData = abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (fixture.compact));
        uint256 intrinsicGas = _calldataIntrinsicGas(callData);

        uint256 beforeGas = gasleft();
        assertTrue(pinned.verifyCompact(fixture.compact), "sampled max-row compact v2 proof");
        uint256 used = beforeGas - gasleft();
        uint256 transactionGasUpperBound = used + intrinsicGas;
        emit log_named_uint("sampled max-row PinnedMleVerifierV2.verifyCompact gas", used);
        emit log_named_uint("sampled max-row compact calldata intrinsic gas", intrinsicGas);
        emit log_named_uint("sampled max-row compact transaction gas upper bound", transactionGasUpperBound);
        assertLt(
            transactionGasUpperBound,
            MAX_PRODUCTION_VERIFY_GAS,
            "compact production transaction exceeds production block envelope"
        );
        assertLt(address(pinned).code.length, 24_576, "pinned compact adapter exceeds EIP-170");
    }

    /// @dev This is the exact adapter entry point used by parent application contracts: the
    /// returned public inputs are decoded by the caller only after the compact proof verifies.
    function test_maxResourceCompactPublicInputsPathFitsProductionGasEnvelope() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory callData = abi.encodeCall(PinnedMleVerifierV2.verifyCompactPublicInputs, (fixture.compact));
        uint256 intrinsicGas = _calldataIntrinsicGas(callData);

        uint256 beforeGas = gasleft();
        uint256[] memory publicInputs = pinned.verifyCompactPublicInputs(fixture.compact);
        uint256 used = beforeGas - gasleft();
        uint256 transactionGasUpperBound = used + intrinsicGas;
        emit log_named_uint("sampled max-row compact PI-return path gas", used);
        emit log_named_uint("sampled max-row compact PI-return calldata intrinsic gas", intrinsicGas);
        emit log_named_uint("sampled max-row compact PI-return transaction gas upper bound", transactionGasUpperBound);
        assertEq(publicInputs.length, fixture.proof.publicInputs.length, "authenticated public input length");
        assertLt(
            transactionGasUpperBound,
            MAX_PRODUCTION_VERIFY_GAS,
            "compact PI-return transaction exceeds production block envelope"
        );
        assertLt(address(pinned).code.length, 24_576, "pinned compact adapter exceeds EIP-170");
    }

    /// @dev The rollup fraud path calls this classifier over the same authenticated compact bytes.
    /// The sampled resource fixture has a non-rollup PI shape, so a valid proof returns PI_MISMATCH;
    /// the important release condition here is that classification reaches that exact verdict
    /// within one production transaction rather than degrading to STARVED.
    function test_maxResourceCompactFraudClassifierFitsProductionGasEnvelope() external {
        ResourceFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory callData = abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (fixture.compact, bytes32(0)));
        uint256 intrinsicGas = _calldataIntrinsicGas(callData);

        uint256 beforeGas = gasleft();
        uint8 verdict = pinned.fraudVerdictCompact(fixture.compact, bytes32(0));
        uint256 used = beforeGas - gasleft();
        uint256 transactionGasUpperBound = used + intrinsicGas;
        emit log_named_uint("sampled max-row compact fraud classifier gas", used);
        emit log_named_uint("sampled max-row compact fraud calldata intrinsic gas", intrinsicGas);
        emit log_named_uint("sampled max-row compact fraud transaction gas upper bound", transactionGasUpperBound);
        assertEq(verdict, 4, "valid generic fixture must reach PI_MISMATCH");
        assertLt(
            transactionGasUpperBound,
            MAX_PRODUCTION_VERIFY_GAS,
            "compact fraud-classifier transaction exceeds production block envelope"
        );
    }

    function test_maxResourceFixtureIsInsideStrictTwoBlobUpperBound() external view {
        string memory json = vm.readFile(FIXTURE);
        uint256 actual = vm.parseJsonUint(json, ".stats.compactBytes");
        uint256 maximum = vm.parseJsonUint(json, ".sizeUpperBound.maxCompactBytes");
        assertEq(vm.parseJsonBool(json, ".sizeUpperBound.fitsCompactCap"), true);
        assertLe(actual, maximum, "sampled proof exceeds grammar-theoretic maximum");
        assertLe(maximum, MAX_COMPACT_PROOF_BYTES_V2, "strict maximum exceeds two SimpleCoder blobs");
    }

    function _fixture() private view returns (ResourceFixture memory fixture) {
        string memory json = vm.readFile(FIXTURE);
        bytes memory proofAbi = vm.parseJsonBytes(json, ".solidityAbiProof.bytes");
        bytes memory configAbi = vm.parseJsonBytes(json, ".solidityAbiVerificationConfig.bytes");
        assertEq(proofAbi.length, vm.parseJsonUint(json, ".solidityAbiProof.byteLength"));
        assertEq(keccak256(proofAbi), vm.parseJsonBytes32(json, ".solidityAbiProof.keccak256"));
        assertEq(configAbi.length, vm.parseJsonUint(json, ".solidityAbiVerificationConfig.byteLength"));
        assertEq(keccak256(configAbi), vm.parseJsonBytes32(json, ".solidityAbiVerificationConfig.keccak256"));

        fixture.proof = abi.decode(proofAbi, (MleVerifierV2.MleProof));
        fixture.config = abi.decode(configAbi, (MleVerifierV2.VerificationConfig));
        fixture.compact = vm.parseJsonBytes(json, ".compactProof.bytes");
        assertEq(fixture.compact.length, vm.parseJsonUint(json, ".compactProof.byteLength"));
        assertEq(keccak256(fixture.compact), vm.parseJsonBytes32(json, ".compactProof.keccak256"));

        bytes memory protocolId = vm.parseJsonBytes(json, ".pinnedVerifier.whirProtocolId");
        assertEq(protocolId.length, 64, "WHIR protocol identifier length");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocolId, 0x20))
            second := mload(add(protocolId, 0x40))
        }
        fixture.whirProtocolId = [first, second];
        fixture.whirSessionId = vm.parseJsonBytes32(json, ".pinnedVerifier.whirSessionId");
        assertEq(fixture.proof.circuitDigest.length, 4, "circuit digest length");
        for (uint256 i = 0; i < 4; ++i) {
            fixture.circuitDigest[i] = uint64(fixture.proof.circuitDigest[i]);
        }
    }

    function _deployCore(ResourceFixture memory fixture) private returns (MleVerifierV2 core) {
        core = new MleVerifierV2(
            block.chainid,
            fixture.proof.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            fixture.config
        );
    }

    function _deriveProfileTranscript(ResourceFixture memory fixture, MleVerifierV2 core, uint256 indexBits)
        private
        view
        returns (
            TranscriptV2.Transcript memory transcript,
            OuterLogupExt3Verifier.Challenges memory challenges,
            GoldilocksExt3.Ext3 memory gateAlpha,
            GoldilocksExt3.Ext3[] memory gateTau
        )
    {
        transcript = TranscriptV2.create();
        TranscriptV2.domainSeparate(transcript, DOMAIN_CIRCUIT_STATEMENT_V2);
        TranscriptV2.absorbFieldVec(transcript, fixture.proof.circuitDigest);
        TranscriptV2.absorbFieldVec(transcript, fixture.proof.publicInputs);
        TranscriptV2.domainSeparate(transcript, PACKED_PCS_SCHEMA_DOMAIN_V2);
        bytes memory metadata = new bytes(15 * 8);
        uint256 offset;
        offset = _profileWriteU64Le(metadata, offset, MLE_PROTOCOL_VERSION_CURRENT);
        offset = _profileWriteU64Le(metadata, offset, NUM_PCS_GROUPS_V2);
        offset = _profileWriteU64Le(metadata, offset, NUM_PCS_TERMINAL_POINTS_V2);
        offset = _profileWriteU64Le(metadata, offset, NUM_PCS_CLAIMS_V2);
        offset = _profileWriteU64Le(metadata, offset, fixture.config.circuit.numConstants);
        offset = _profileWriteU64Le(metadata, offset, fixture.config.circuit.numRoutedWires);
        offset = _profileWriteU64Le(metadata, offset, fixture.config.circuit.numWires);
        offset = _profileWriteU64Le(metadata, offset, fixture.config.circuit.degreeBits);
        offset = _profileWriteU64Le(metadata, offset, fixture.proof.constituentWidth);
        offset = _profileWriteU64Le(metadata, offset, indexBits);
        offset = _profileWriteU64Le(metadata, offset, NUM_PACKED_VECTORS_PER_GROUP_V2);
        offset = _profileWriteU64Le(metadata, offset, EXTENSION_FIELD_LIMBS_V2);
        offset = _profileWriteU64Le(metadata, offset, PACKED_VARIABLE_ORDER_CODE_V2);
        offset = _profileWriteU64Le(metadata, offset, GATE_SUMCHECK_COUNT_V2);
        offset = _profileWriteU64Le(metadata, offset, LOG_ROUND_DEGREE_V2);
        assertEq(offset, metadata.length);
        TranscriptV2.absorbBytes(transcript, metadata);
        TranscriptV2.domainSeparate(transcript, DOMAIN_CIRCUIT_CONFIG_DIGEST_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(core.circuitConfigDigest()));
        TranscriptV2.bindWhirIdentifiers(
            transcript,
            abi.encodePacked(fixture.whirProtocolId[0], fixture.whirProtocolId[1]),
            abi.encodePacked(fixture.whirSessionId)
        );
        TranscriptV2.domainSeparate(transcript, DOMAIN_GROUP_PREPROCESSED_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(fixture.proof.preprocessedRoot));
        TranscriptV2.domainSeparate(transcript, DOMAIN_GROUP_WITNESS_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(fixture.proof.witnessRoot));
        TranscriptV2.domainSeparate(transcript, DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
        challenges.eta = TranscriptV2.squeezeExt3(transcript);
        TranscriptV2.domainSeparate(transcript, DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2);
        challenges.beta = TranscriptV2.squeezeExt3(transcript);
        challenges.gamma = TranscriptV2.squeezeExt3(transcript);
        TranscriptV2.domainSeparate(transcript, DOMAIN_GROUP_NORM_INVERSE_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(fixture.proof.normInverseRoot));
        TranscriptV2.domainSeparate(transcript, DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2);
        challenges.xi = TranscriptV2.squeezeExt3(transcript);
        TranscriptV2.domainSeparate(transcript, DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        challenges.lambda = TranscriptV2.squeezeExt3(transcript);
        challenges.rho = TranscriptV2.squeezeExt3(transcript);
        challenges.kappa = TranscriptV2.squeezeExt3(transcript);
        challenges.tau = _profileSqueezeExt3Vector(transcript, fixture.config.circuit.degreeBits);
        gateAlpha = TranscriptV2.squeezeExt3(transcript);
        gateTau = _profileSqueezeExt3Vector(transcript, fixture.config.circuit.degreeBits);
    }

    function _profileAbsorbClaimsAndSampleIndices(
        TranscriptV2.Transcript memory transcript,
        MleVerifierV2.MleProof memory proof,
        uint256 indexBits
    ) private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_CLAIMS_V2);
        TranscriptV2.absorbExt3Vec(transcript, proof.logPreprocessed);
        TranscriptV2.absorbExt3Vec(transcript, proof.logWitness);
        TranscriptV2.absorbExt3Vec(transcript, proof.logNormInverse);
        TranscriptV2.absorbExt3Vec(transcript, proof.gatePreprocessed);
        TranscriptV2.absorbExt3Vec(transcript, proof.gateWitness);
        TranscriptV2.absorbExt3Vec(transcript, new GoldilocksExt3.Ext3[](0));
        TranscriptV2.domainSeparate(transcript, DOMAIN_CONSTITUENT_INDEX_V2);
        points = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < points.length; ++point) {
            points[point] = _profileSqueezeExt3Vector(transcript, indexBits);
        }
    }

    function _profileSqueezeExt3Vector(TranscriptV2.Transcript memory transcript, uint256 length)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        values = new GoldilocksExt3.Ext3[](length);
        for (uint256 i = 0; i < length; ++i) {
            values[i] = TranscriptV2.squeezeExt3(transcript);
        }
    }

    function _profilePackedPoint(GoldilocksExt3.Ext3[] memory row, GoldilocksExt3.Ext3[] memory index)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory point)
    {
        point = new GoldilocksExt3.Ext3[](row.length + index.length);
        for (uint256 i = 0; i < index.length; ++i) {
            point[i] = index[index.length - 1 - i];
        }
        for (uint256 i = 0; i < row.length; ++i) {
            point[index.length + i] = row[row.length - 1 - i];
        }
    }

    function _profileWriteU64Le(bytes memory destination, uint256 offset, uint256 value)
        private
        pure
        returns (uint256)
    {
        for (uint256 byteIndex = 0; byteIndex < 8; ++byteIndex) {
            destination[offset + byteIndex] = bytes1(uint8(value >> (8 * byteIndex)));
        }
        return offset + 8;
    }

    function _profileReadU64Le(bytes calldata encoded, uint256 offset) private pure returns (uint64 value) {
        assembly ("memory-safe") {
            let raw := shr(192, calldataload(add(encoded.offset, offset)))
            raw := or(and(shr(8, raw), 0x00FF00FF00FF00FF), and(shl(8, raw), 0xFF00FF00FF00FF00))
            raw := or(and(shr(16, raw), 0x0000FFFF0000FFFF), and(shl(16, raw), 0xFFFF0000FFFF0000))
            value := and(or(shr(32, raw), shl(32, raw)), 0xFFFFFFFFFFFFFFFF)
        }
    }

    function _calldataIntrinsicGas(bytes memory data) private pure returns (uint256 gasCost) {
        gasCost = 21_000;
        for (uint256 i = 0; i < data.length; ++i) {
            gasCost += data[i] == 0 ? 4 : 16;
        }
    }
}
