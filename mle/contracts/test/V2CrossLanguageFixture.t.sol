// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {CircuitConfigV2} from "../src/CircuitConfigV2.sol";
import {CompactMleProofV2} from "../src/CompactMleProofV2.sol";
import {
    InvalidMleProof,
    InvalidMleVerifierChainId,
    InvalidMleVerifierConfiguration,
    MleProofEngineUnavailable
} from "../src/MleProofErrors.sol";
import {MleVerifier} from "../src/MleVerifier.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";
import {OuterLogupExt3Verifier} from "../src/OuterLogupExt3Verifier.sol";
import {PackedClaimExt3} from "../src/PackedClaimExt3.sol";
import {Plonky2GateEvaluatorExt3} from "../src/Plonky2GateEvaluatorExt3.sol";
import {PoseidonPublicInputsHash} from "../src/PoseidonPublicInputsHash.sol";
import {TranscriptV2} from "../src/TranscriptV2.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";
import {
    BASE_FIELD_MODULUS_V2,
    COMPACT_FIELD_COUNT_V2,
    COMPACT_LAYOUT_HASH_V2,
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
    DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2,
    DOMAIN_OUTER_SUMCHECK_ROUND_V2,
    DOMAIN_WHIR_PROTOCOL_ID_V2,
    DOMAIN_WHIR_SESSION_ID_V2,
    EXTENSION_FIELD_LIMBS_V2,
    GATE_SUMCHECK_COUNT_V2,
    GROUP_NORM_INVERSE_V2,
    GROUP_PREPROCESSED_V2,
    GROUP_WITNESS_V2,
    LOG_ROUND_DEGREE_V2,
    MAX_COMPACT_PROOF_BYTES_V2,
    MAX_WHIR_HINT_BYTES_V2,
    MAX_WHIR_NARG_BYTES_V2,
    MLE_PROTOCOL_VERSION_CURRENT,
    NUM_BOUND_PCS_CLAIMS_V2,
    NUM_PACKED_VECTORS_PER_GROUP_V2,
    NUM_PCS_CLAIMS_V2,
    NUM_PCS_GROUPS_V2,
    NUM_PCS_TERMINAL_POINTS_V2,
    OUTER_TRANSCRIPT_PROTOCOL_V2,
    PACKED_BOUND_CLAIM_MASK_V2,
    PACKED_PCS_SCHEMA_DOMAIN_V2,
    PACKED_VARIABLE_ORDER_CODE_V2,
    POINT_GATE_V2,
    POINT_LOG_V2,
    TAG_BYTES_V2,
    TAG_DOMAIN_V2,
    TAG_EXT3_VEC_V2,
    TAG_FIELD_VEC_V2
} from "../src/generated/MleWhirV2.sol";

contract CrossRevisionCompactHarness {
    function decode(bytes calldata encoded, CircuitConfigV2.Parameters calldata circuit)
        external
        pure
        returns (MleVerifierV2.MleProof memory proof)
    {
        CircuitConfigV2.Parameters memory trustedCircuit = circuit;
        return CompactMleProofV2.decode(encoded, trustedCircuit);
    }
}

/// @notice Byte-exact Solidity consumer for the Rust-generated MLE/WHIR v2 fixture.
/// @dev This deliberately replays the production TranscriptV2 primitives rather
/// than implementing a second transcript encoder. The fixed event-order checks
/// prevent a self-consistent but reordered JSON trace from being accepted.
contract V2CrossLanguageFixtureTest is Test {
    string internal constant FIXTURE = "test/fixtures/v2_cross_language.json";
    string internal constant HISTORICAL_WIRE_V2_FIXTURE = "../testdata/historical_wire_v2_compact.json";
    string internal constant CASE = ".cases[0]";
    uint256 internal constant EVENT_COUNT = 78;
    uint256 internal constant RUST_SOLIDITY_ABI_PROOF_BYTES = 118_528;
    bytes32 internal constant RUST_SOLIDITY_ABI_PROOF_KECCAK =
        0x388b52d7a548d08e51455df44faeb830a3eb7f59e1cee50830ef8e7812620e23;
    uint256 internal constant RUST_SOLIDITY_ABI_CONFIG_BYTES = 5_664;
    bytes32 internal constant RUST_SOLIDITY_ABI_CONFIG_KECCAK =
        0x61c7fcecfd5b6839926e2579bde990144cfcdc9b3e2f0f24f0f72b3aa2094c9f;
    MleVerifierV2 private encodedVerifier;

    struct AtomicFixture {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes32 preprocessedRoot;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    struct CompactCursor {
        bytes encoded;
        uint256 offset;
    }

    function test_genuineWireV2CannotCrossTheWireV3DecoderOrCryptographicBoundary() external {
        string memory historicalJson = vm.readFile(HISTORICAL_WIRE_V2_FIXTURE);
        assertEq(
            vm.parseJsonString(historicalJson, ".source.sourceFixtureSha256"),
            "0xe4bd26575fb6b101e8be487251689bc073511e1df7ba69996afccfbf14ac6af3",
            "historical source snapshot"
        );
        bytes memory legacy = vm.parseJsonBytes(historicalJson, ".compactProof.bytes");
        assertEq(legacy.length, 71_988, "historical compact length");
        assertEq(
            keccak256(legacy),
            0xd7eb1b018d6e33a8546436e05788ca9946cd994dd93ed9b8c689ac97f92e418a,
            "historical compact keccak"
        );

        string memory currentJson = vm.readFile(FIXTURE);
        AtomicFixture memory current = _parseAtomicFixture(currentJson);
        CrossRevisionCompactHarness decoder = new CrossRevisionCompactHarness();

        // The genuine old discriminator is rejected by the production strict
        // decoder before its body can be interpreted as the current protocol.
        (bool decoded, bytes memory reason) = address(decoder)
            .staticcall(abi.encodeCall(CrossRevisionCompactHarness.decode, (legacy, current.config.circuit)));
        assertFalse(decoded, "genuine wire-v2 unexpectedly decoded as wire-v3");
        assertEq(reason, abi.encodeWithSelector(InvalidMleProof.selector), "strict decoder selector");

        // Relabel exactly the magic/version bytes. The unchanged old body is
        // structurally canonical and therefore reaches cryptographic replay.
        bytes memory relabeled = bytes.concat(legacy);
        bytes memory currentMagic = abi.encodePacked(COMPACT_MAGIC_V2);
        for (uint256 i = 0; i < 8; ++i) {
            relabeled[i] = currentMagic[i];
        }
        _writeU64Le(relabeled, 8, MLE_PROTOCOL_VERSION_CURRENT);
        MleVerifierV2.MleProof memory oldBody = decoder.decode(relabeled, current.config.circuit);
        assertEq(oldBody.protocolVersion, MLE_PROTOCOL_VERSION_CURRENT, "relabeled version");
        assertEq(oldBody.preprocessedRoot, current.preprocessedRoot, "same-circuit preprocessed root");
        for (uint256 i = 0; i < 4; ++i) {
            assertEq(oldBody.circuitDigest[i], current.circuitDigest[i], "same-circuit digest");
        }

        // The current verifier is pinned to v3 domains/session/WHIR profile.
        // A non-empty InvalidMleProof selector also excludes an OOG false pass.
        MleVerifierV2 verifier = _deployAtomicVerifier(current);
        (bool verified, bytes memory verifyReason) = address(verifier).staticcall{gas: 30_000_000}(
            abi.encodeCall(MleVerifierV2.verify, (oldBody, current.config))
        );
        assertFalse(verified, "header-relabeled wire-v2 proof verified under wire-v3");
        assertEq(
            verifyReason, abi.encodeWithSelector(InvalidMleProof.selector), "wire-v3 transcript/WHIR rejection selector"
        );
    }

    function test_solidityAbiEncodingMatchesCanonicalRustExport() external view {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        bytes memory encoded = abi.encode(fixture.proof);
        assertEq(encoded.length, RUST_SOLIDITY_ABI_PROOF_BYTES, "Rust/Solidity ABI proof length");
        assertEq(keccak256(encoded), RUST_SOLIDITY_ABI_PROOF_KECCAK, "Rust/Solidity ABI proof hash");
    }

    function test_solidityVerificationConfigAbiEncodingMatchesCanonicalRustExport() external view {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        bytes memory encoded = abi.encode(fixture.config);
        assertEq(encoded.length, RUST_SOLIDITY_ABI_CONFIG_BYTES, "Rust/Solidity ABI config length");
        assertEq(keccak256(encoded), RUST_SOLIDITY_ABI_CONFIG_KECCAK, "Rust/Solidity ABI config hash");
    }

    function test_atomicMleVerifierV2AcceptsCanonicalRustProof() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);

        uint256 gasBefore = gasleft();
        assertTrue(verifier.verify(fixture.proof, fixture.config), "atomic v2 proof must verify");
        uint256 verifyGas = gasBefore - gasleft();
        emit log_named_uint("MleVerifierV2.verify gas", verifyGas);
        assertLt(verifyGas, 30_000_000, "atomic v2 verification must fit the 30m envelope");
        assertEq(verifier.allowedChainId(), block.chainid);
        assertEq(verifier.preprocessedCommitmentRoot(), fixture.preprocessedRoot);
        assertEq(
            verifier.whirParametersDigest(),
            keccak256(abi.encode(fixture.config.whir)),
            "constructor must pin the caller-visible empty-point WHIR config"
        );
        assertEq(
            verifier.circuitConfigDigest(),
            vm.parseJsonBytes32(vm.readFile(FIXTURE), string.concat(CASE, ".verificationKey.circuitConfigDigest"))
        );
    }

    function test_pinnedMleVerifierV2AcceptsCanonicalRustProofAndPreservesFraudSemantics() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(verifier, fixture.config);

        uint256 gasBefore = gasleft();
        assertTrue(pinned.verify(fixture.proof), "pinned atomic v2 proof must verify");
        uint256 verifyGas = gasBefore - gasleft();
        emit log_named_uint("PinnedMleVerifierV2.verify gas", verifyGas);
        emit log_named_uint("PinnedMleVerifierV2 runtime bytes", address(pinned).code.length);
        assertLt(verifyGas, 30_000_000, "pinned verification must fit the 30m envelope");
        assertLt(address(pinned).code.length, 24_576, "pinned adapter must fit EIP-170");

        // This generic fixture does not have the rollup's eight-limb PI digest, so a valid proof
        // reaches PI_MISMATCH rather than VALID. The adapter decodes once and calls core.verify once.
        gasBefore = gasleft();
        assertEq(pinned.fraudVerdictEncoded(abi.encode(fixture.proof), bytes32(0)), 4, "PI verdict");
        uint256 classifierGas = gasBefore - gasleft();
        emit log_named_uint("PinnedMleVerifierV2.fraudVerdictEncoded valid gas", classifierGas);
        MleVerifierV2.MleProof memory invalid = _cloneProof(fixture.proof);
        invalid.witnessRoot = bytes32(uint256(invalid.witnessRoot) ^ 1);
        gasBefore = gasleft();
        assertEq(pinned.fraudVerdictEncoded(abi.encode(invalid), bytes32(0)), 0, "fraud verdict");
        emit log_named_uint("PinnedMleVerifierV2.fraudVerdictEncoded invalid gas", gasBefore - gasleft());
    }

    function test_directWhirAcceptsCanonicalRustProofWithoutOuterClaimBindings() external {
        string memory json = vm.readFile(FIXTURE);
        AtomicFixture memory fixture = _parseAtomicFixture(json);
        GoldilocksExt3.Ext3[] memory evaluations = new GoldilocksExt3.Ext3[](NUM_PCS_CLAIMS_V2);
        bytes memory mask = new bytes(1);

        uint256 gasBefore = gasleft();
        assertTrue(_verifyDirectWhir(json, fixture, evaluations, mask), "canonical WHIR proof must verify");
        emit log_named_uint("SpongefishWhirVerify.verifyWhirProofBound gas", gasBefore - gasleft());
    }

    function test_directWhirAcceptsCanonicalRustProofWithFixtureClaimBindings() external view {
        string memory json = vm.readFile(FIXTURE);
        AtomicFixture memory fixture = _parseAtomicFixture(json);
        GoldilocksExt3.Ext3[] memory evaluations = new GoldilocksExt3.Ext3[](NUM_PCS_CLAIMS_V2);
        for (uint256 i = 0; i < NUM_BOUND_PCS_CLAIMS_V2; ++i) {
            evaluations[i] = _ext3(json, string.concat(CASE, ".packedClaims[", vm.toString(i), "].value"));
        }
        bytes memory mask = new bytes(1);
        mask[0] = bytes1(uint8(PACKED_BOUND_CLAIM_MASK_V2));

        assertTrue(_verifyDirectWhir(json, fixture, evaluations, mask), "fixture-bound WHIR proof must verify");
    }

    function test_whirBoundaryUsesReverseOfFullDenseLsbPackedPoint() external view {
        string memory json = vm.readFile(FIXTURE);
        for (uint256 point = 0; point < NUM_PCS_TERMINAL_POINTS_V2; ++point) {
            GoldilocksExt3.Ext3[] memory dense =
                _ext3Array(json, string.concat(CASE, ".packedPoints[", vm.toString(point), "].packedPoint"), 10);
            GoldilocksExt3.Ext3[] memory whirPoint = _reversePoint(dense);
            assertFalse(GoldilocksExt3.eq(whirPoint[0], dense[0]), "fixture must detect an omitted reversal");
            for (uint256 i = 0; i < dense.length; ++i) {
                _assertExt3Eq(whirPoint[i], dense[dense.length - 1 - i], "WHIR full-point reversal");
            }
        }
    }

    function test_atomicProofMutationMatrixUsesProofFraudError() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        for (uint256 mutation = 0; mutation < 15; ++mutation) {
            MleVerifierV2.MleProof memory invalidProof = _cloneProof(fixture.proof);
            _mutateProof(invalidProof, mutation);
            vm.expectRevert(InvalidMleProof.selector);
            verifier.verify(invalidProof, fixture.config);
        }
    }

    /// @notice Exhausts every scalar proof member, every digest/PI entry and
    /// every ordered commitment root. Each mutation is canonical, so rejection
    /// must come from the proof verifier rather than ABI decoding.
    function test_adversarialEveryScalarDigestPiAndRootMutationIsInvalidProof() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        MleVerifierV2.MleProof memory proof = _cloneProof(fixture.proof);

        uint256 original = proof.protocolVersion;
        proof.protocolVersion ^= 1;
        _assertInvalidProof(verifier, proof, fixture.config, "scalar.protocolVersion.bump");
        proof.protocolVersion = original;

        original = proof.constituentWidth;
        proof.constituentWidth ^= 1;
        _assertInvalidProof(verifier, proof, fixture.config, "scalar.constituentWidth.bump");
        proof.constituentWidth = original;

        for (uint256 i = 0; i < proof.circuitDigest.length; ++i) {
            original = proof.circuitDigest[i];
            proof.circuitDigest[i] = _bumpField(original);
            _assertInvalidProof(verifier, proof, fixture.config, _indexedLabel("circuitDigest.bump", i, 0, 0));
            proof.circuitDigest[i] = BASE_FIELD_MODULUS_V2;
            _assertInvalidProof(verifier, proof, fixture.config, _indexedLabel("circuitDigest.noncanonical", i, 0, 0));
            proof.circuitDigest[i] = original;
        }
        for (uint256 i = 0; i < proof.publicInputs.length; ++i) {
            original = proof.publicInputs[i];
            proof.publicInputs[i] = _bumpField(original);
            _assertInvalidProof(verifier, proof, fixture.config, _indexedLabel("publicInputs.bump", i, 0, 0));
            proof.publicInputs[i] = BASE_FIELD_MODULUS_V2;
            _assertInvalidProof(verifier, proof, fixture.config, _indexedLabel("publicInputs.noncanonical", i, 0, 0));
            proof.publicInputs[i] = original;
        }

        bytes32 originalRoot = proof.preprocessedRoot;
        proof.preprocessedRoot = bytes32(uint256(originalRoot) ^ 1);
        _assertInvalidProof(verifier, proof, fixture.config, "root.preprocessed.bump");
        proof.preprocessedRoot = originalRoot;
        originalRoot = proof.witnessRoot;
        proof.witnessRoot = bytes32(uint256(originalRoot) ^ 1);
        _assertInvalidProof(verifier, proof, fixture.config, "root.witness.bump");
        proof.witnessRoot = originalRoot;
        originalRoot = proof.normInverseRoot;
        proof.normInverseRoot = bytes32(uint256(originalRoot) ^ 1);
        _assertInvalidProof(verifier, proof, fixture.config, "root.normInverse.bump");
    }

    function test_adversarialEveryLogSumcheckCoefficientAndLimbIsInvalidProof() external {
        _runEverySumcheckCoefficientMutation(true, 0, type(uint256).max);
    }

    function test_adversarialEveryGateRound0CoefficientAndLimbIsInvalidProof() external {
        _runEverySumcheckCoefficientMutation(false, 0, 1);
    }

    function test_adversarialEveryGateRound1CoefficientAndLimbIsInvalidProof() external {
        _runEverySumcheckCoefficientMutation(false, 1, 2);
    }

    function test_adversarialLogPreprocessed0To59C0() external {
        _runTerminalVectorMutation(0, 0, 0, 60);
    }

    function test_adversarialLogPreprocessed60ToEndC0() external {
        _runTerminalVectorMutation(0, 0, 60, type(uint256).max);
    }

    function test_adversarialLogPreprocessed0To59C1() external {
        _runTerminalVectorMutation(0, 1, 0, 60);
    }

    function test_adversarialLogPreprocessed60ToEndC1() external {
        _runTerminalVectorMutation(0, 1, 60, type(uint256).max);
    }

    function test_adversarialLogPreprocessed0To59C2() external {
        _runTerminalVectorMutation(0, 2, 0, 60);
    }

    function test_adversarialLogPreprocessed60ToEndC2() external {
        _runTerminalVectorMutation(0, 2, 60, type(uint256).max);
    }

    function test_adversarialLogWitness0To59C0() external {
        _runTerminalVectorMutation(1, 0, 0, 60);
    }

    function test_adversarialLogWitness60To89C0() external {
        _runTerminalVectorMutation(1, 0, 60, 90);
    }

    function test_adversarialLogWitness90To119C0() external {
        _runTerminalVectorMutation(1, 0, 90, 120);
    }

    function test_adversarialLogWitness120ToEndC0() external {
        _runTerminalVectorMutation(1, 0, 120, type(uint256).max);
    }

    function test_adversarialLogWitness0To59C1() external {
        _runTerminalVectorMutation(1, 1, 0, 60);
    }

    function test_adversarialLogWitness60To89C1() external {
        _runTerminalVectorMutation(1, 1, 60, 90);
    }

    function test_adversarialLogWitness90To119C1() external {
        _runTerminalVectorMutation(1, 1, 90, 120);
    }

    function test_adversarialLogWitness120ToEndC1() external {
        _runTerminalVectorMutation(1, 1, 120, type(uint256).max);
    }

    function test_adversarialLogWitness0To59C2() external {
        _runTerminalVectorMutation(1, 2, 0, 60);
    }

    function test_adversarialLogWitness60To89C2() external {
        _runTerminalVectorMutation(1, 2, 60, 90);
    }

    function test_adversarialLogWitness90To119C2() external {
        _runTerminalVectorMutation(1, 2, 90, 120);
    }

    function test_adversarialLogWitness120ToEndC2() external {
        _runTerminalVectorMutation(1, 2, 120, type(uint256).max);
    }

    function test_adversarialLogNormInverse0To59C0() external {
        _runTerminalVectorMutation(2, 0, 0, 60);
    }

    function test_adversarialLogNormInverse60To119C0() external {
        _runTerminalVectorMutation(2, 0, 60, 120);
    }

    function test_adversarialLogNormInverse120ToEndC0() external {
        _runTerminalVectorMutation(2, 0, 120, type(uint256).max);
    }

    function test_adversarialLogNormInverse0To59C1() external {
        _runTerminalVectorMutation(2, 1, 0, 60);
    }

    function test_adversarialLogNormInverse60To119C1() external {
        _runTerminalVectorMutation(2, 1, 60, 120);
    }

    function test_adversarialLogNormInverse120ToEndC1() external {
        _runTerminalVectorMutation(2, 1, 120, type(uint256).max);
    }

    function test_adversarialLogNormInverse0To59C2() external {
        _runTerminalVectorMutation(2, 2, 0, 60);
    }

    function test_adversarialLogNormInverse60To119C2() external {
        _runTerminalVectorMutation(2, 2, 60, 120);
    }

    function test_adversarialLogNormInverse120ToEndC2() external {
        _runTerminalVectorMutation(2, 2, 120, type(uint256).max);
    }

    function test_adversarialEveryTerminalFamilyAndLimbRejectsNoncanonicalField() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        MleVerifierV2.MleProof memory proof = _cloneProof(fixture.proof);

        for (uint256 field = 0; field < 5; ++field) {
            GoldilocksExt3.Ext3[] memory values = _terminalVector(proof, field);
            uint256 element = values.length - 1;
            for (uint256 limb = 0; limb < 3; ++limb) {
                uint64 original = _ext3Limb(values[element], limb);
                _setExt3Limb(values[element], limb, uint64(BASE_FIELD_MODULUS_V2));
                _assertInvalidProof(
                    verifier,
                    proof,
                    fixture.config,
                    _indexedLabel(string.concat(_terminalVectorName(field), ".noncanonical"), element, limb, 0)
                );
                _setExt3Limb(values[element], limb, original);
            }
        }
    }

    // Gate terminal values are consumed after the full WHIR proof. Keep each
    // test below 30 honest-cost calls so the test transaction's gas limit does
    // not turn an expected proof rejection into an outer OOG.
    function test_adversarialGatePreprocessed0To29C0() external {
        _runTerminalVectorMutation(3, 0, 0, 30);
    }

    function test_adversarialGatePreprocessed30To59C0() external {
        _runTerminalVectorMutation(3, 0, 30, 60);
    }

    function test_adversarialGatePreprocessed60ToEndC0() external {
        _runTerminalVectorMutation(3, 0, 60, type(uint256).max);
    }

    function test_adversarialGatePreprocessed0To29C1() external {
        _runTerminalVectorMutation(3, 1, 0, 30);
    }

    function test_adversarialGatePreprocessed30To59C1() external {
        _runTerminalVectorMutation(3, 1, 30, 60);
    }

    function test_adversarialGatePreprocessed60ToEndC1() external {
        _runTerminalVectorMutation(3, 1, 60, type(uint256).max);
    }

    function test_adversarialGatePreprocessed0To29C2() external {
        _runTerminalVectorMutation(3, 2, 0, 30);
    }

    function test_adversarialGatePreprocessed30To59C2() external {
        _runTerminalVectorMutation(3, 2, 30, 60);
    }

    function test_adversarialGatePreprocessed60ToEndC2() external {
        _runTerminalVectorMutation(3, 2, 60, type(uint256).max);
    }

    function test_adversarialGateWitness0To29C0() external {
        _runTerminalVectorMutation(4, 0, 0, 30);
    }

    function test_adversarialGateWitness30To59C0() external {
        _runTerminalVectorMutation(4, 0, 30, 60);
    }

    function test_adversarialGateWitness60To89C0() external {
        _runTerminalVectorMutation(4, 0, 60, 90);
    }

    function test_adversarialGateWitness90To119C0() external {
        _runTerminalVectorMutation(4, 0, 90, 120);
    }

    function test_adversarialGateWitness120ToEndC0() external {
        _runTerminalVectorMutation(4, 0, 120, type(uint256).max);
    }

    function test_adversarialGateWitness0To29C1() external {
        _runTerminalVectorMutation(4, 1, 0, 30);
    }

    function test_adversarialGateWitness30To59C1() external {
        _runTerminalVectorMutation(4, 1, 30, 60);
    }

    function test_adversarialGateWitness60To89C1() external {
        _runTerminalVectorMutation(4, 1, 60, 90);
    }

    function test_adversarialGateWitness90To119C1() external {
        _runTerminalVectorMutation(4, 1, 90, 120);
    }

    function test_adversarialGateWitness120ToEndC1() external {
        _runTerminalVectorMutation(4, 1, 120, type(uint256).max);
    }

    function test_adversarialGateWitness0To29C2() external {
        _runTerminalVectorMutation(4, 2, 0, 30);
    }

    function test_adversarialGateWitness30To59C2() external {
        _runTerminalVectorMutation(4, 2, 30, 60);
    }

    function test_adversarialGateWitness60To89C2() external {
        _runTerminalVectorMutation(4, 2, 60, 90);
    }

    function test_adversarialGateWitness90To119C2() external {
        _runTerminalVectorMutation(4, 2, 90, 120);
    }

    function test_adversarialGateWitness120ToEndC2() external {
        _runTerminalVectorMutation(4, 2, 120, type(uint256).max);
    }

    /// @notice Covers every dynamic proof-array family on both sides of its
    /// canonical length. Stream changes are included here because their byte
    /// length is part of the proof shape even though it is checked by WHIR.
    function test_adversarialEveryDynamicProofArrayRejectsShortAndLongShapes() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        for (uint256 mutation = 0; mutation < 32; ++mutation) {
            MleVerifierV2.MleProof memory proof = _cloneProof(fixture.proof);
            _mutateProofShape(proof, mutation);
            _assertInvalidProof(verifier, proof, fixture.config, _shapeMutationLabel(mutation));
        }
    }

    // The canonical PoW-22 native trace has 49 distinct NARG reads. Mutate the first, middle,
    // and last byte of every read, with bounded shards so a late WHIR rejection
    // cannot exhaust the surrounding Foundry test transaction.
    function test_adversarialWhirNargRecords0To9InternalBytes() external {
        _runWhirRecordMutations(true, 0, 10, 3);
    }

    function test_adversarialWhirNargRecords10To19InternalBytes() external {
        _runWhirRecordMutations(true, 10, 20, 3);
    }

    function test_adversarialWhirNargRecords20To29InternalBytes() external {
        _runWhirRecordMutations(true, 20, 30, 3);
    }

    function test_adversarialWhirNargRecords30To39InternalBytes() external {
        _runWhirRecordMutations(true, 30, 40, 3);
    }

    function test_adversarialWhirNargRecords40To48InternalBytes() external {
        _runWhirRecordMutations(true, 40, 49, 3);
    }

    /// @notice Each large Merkle-hint record is sampled at its boundaries,
    /// quarters and midpoint. Cursor boundaries come from the Rust trace.
    function test_adversarialEveryWhirHintRecordInternalBytes() external {
        _runWhirRecordMutations(false, 0, 4, 5);
    }

    /// @notice Pin representative preflight, outer-sumcheck, WHIR and terminal
    /// failures to the fraud classifier's INVALID verdict. A STARVED verdict
    /// (or an outer OOG) is deliberately not accepted as proof invalidity.
    function test_adversarialPinnedClassifierReturnsInvalidAcrossVerificationStages() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 core = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);

        for (uint256 mutation = 0; mutation < 10; ++mutation) {
            MleVerifierV2.MleProof memory proof = _cloneProof(fixture.proof);
            string memory label;
            if (mutation == 0) {
                proof.protocolVersion ^= 1;
                label = "classifier.version";
            } else if (mutation == 1) {
                proof.constituentWidth ^= 1;
                label = "classifier.width";
            } else if (mutation == 2) {
                proof.circuitDigest[2] = _bumpField(proof.circuitDigest[2]);
                label = "classifier.digest";
            } else if (mutation == 3) {
                proof.publicInputs[0] = _bumpField(proof.publicInputs[0]);
                label = "classifier.publicInputs";
            } else if (mutation == 4) {
                proof.preprocessedRoot = bytes32(uint256(proof.preprocessedRoot) ^ 1);
                label = "classifier.root";
            } else if (mutation == 5) {
                _bumpExt3(proof.logProof.rounds[1].nonConstant[4]);
                label = "classifier.outerSumcheck";
            } else if (mutation == 6) {
                _bumpExt3(proof.gateWitness[proof.gateWitness.length - 1]);
                label = "classifier.terminal";
            } else if (mutation == 7) {
                proof.whirTranscript[proof.whirTranscript.length / 2] =
                    bytes1(uint8(proof.whirTranscript[proof.whirTranscript.length / 2]) ^ 1);
                label = "classifier.whirNarg";
            } else if (mutation == 8) {
                proof.whirHints[proof.whirHints.length / 2] =
                    bytes1(uint8(proof.whirHints[proof.whirHints.length / 2]) ^ 1);
                label = "classifier.whirHints";
            } else {
                proof.logNormInverse = _resizeExt3(proof.logNormInverse, proof.logNormInverse.length - 1);
                label = "classifier.shape";
            }
            _assertPinnedEncodedInvalid(pinned, proof, label);
        }
    }

    /// @notice Exercises malformed and non-unique ABI layouts through the
    /// pinned production classifier. Every case fails canonical decoding before
    /// proof verification, so this remains independent of proof-verification gas.
    function test_adversarialPinnedClassifierRejectsRawAbiTruncationTrailingAndOffsets() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 core = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory canonical = abi.encode(fixture.proof);

        uint256[7] memory truncatedLengths = [uint256(0), 1, 31, 32, 33, 543, canonical.length - 1];
        for (uint256 i = 0; i < truncatedLengths.length; ++i) {
            bytes memory truncated = _resizeBytes(canonical, truncatedLengths[i]);
            _assertRawDecodeFails(pinned, truncated, false, string.concat("raw.decode.truncated.", vm.toString(i)));
            _assertPinnedRawInvalid(
                pinned, truncated, string.concat("raw.truncated.", vm.toString(truncatedLengths[i]))
            );
        }
        bytes memory raw = bytes.concat(canonical, hex"00");
        _assertRawDecodesNoncanonical(pinned, raw, keccak256(canonical), "raw.decode.trailingByte");
        _assertPinnedRawInvalid(pinned, raw, "raw.trailing.byte");
        _assertPinnedRawInvalid(pinned, bytes.concat(canonical, new bytes(32)), "raw.trailing.word");

        // Move the complete tuple by one byte and point the outer head at the
        // unaligned copy. Solc accepts the decoded value, while the canonical
        // re-encoding check rejects this alternate representation.
        raw = _insertZeroBytes(canonical, 0x20, 1);
        _writeWord(raw, 0, 0x21);
        _assertRawDecodesNoncanonical(pinned, raw, keccak256(canonical), "raw.decode.outerUnaligned");
        _assertPinnedRawInvalid(pinned, raw, "raw.offset.outerUnaligned");

        // Insert a word between the 16-word tuple head and its tails, then
        // update every top-level dynamic pointer. The decoded value is unchanged
        // but the layout is not the unique abi.encode layout.
        raw = _insertZeroBytes(canonical, 0x220, 32);
        _shiftTopLevelDynamicPointers(raw, 32);
        _assertRawDecodesNoncanonical(pinned, raw, keccak256(canonical), "raw.decode.headTailGap");
        _assertPinnedRawInvalid(pinned, raw, "raw.offset.headTailGap");

        // Equal-length terminal arrays can be aliased without inducing a huge
        // attacker-controlled allocation. Canonical re-encoding must reject it.
        raw = _resizeBytes(canonical, canonical.length);
        _writeWord(raw, 0x1e0, _readWord(raw, 0x160));
        _assertRawDecodesNoncanonical(pinned, raw, bytes32(0), "raw.decode.aliasedTail");
        _assertPinnedRawInvalid(pinned, raw, "raw.offset.aliasedTail");

        // Alias the second element of the nested dynamic log-round array to
        // the first. This covers non-unique offsets below the top-level tuple.
        raw = _resizeBytes(canonical, canonical.length);
        uint256 tupleBase = _readWord(raw, 0);
        uint256 logProofBase = tupleBase + _readWord(raw, 0x140);
        uint256 roundsBase = logProofBase + _readWord(raw, logProofBase);
        uint256 firstRoundHead = roundsBase + 32;
        _writeWord(raw, firstRoundHead + 32, _readWord(raw, firstRoundHead));
        _assertRawDecodesNoncanonical(pinned, raw, bytes32(0), "raw.decode.nestedRoundAlias");
        _assertPinnedRawInvalid(pinned, raw, "raw.offset.nestedRoundAlias");

        // Point the hints array at a zeroed word inside the transcript payload.
        // The two decoded byte regions now partially overlap but remain bounded.
        raw = _resizeBytes(canonical, canonical.length);
        uint256 transcriptRelative = _readWord(raw, 0x100);
        uint256 transcriptBase = tupleBase + transcriptRelative;
        require(_readWord(raw, transcriptBase) >= 32, "raw transcript too short");
        _writeWord(raw, transcriptBase + 32, 0);
        _writeWord(raw, 0x120, transcriptRelative + 32);
        _assertRawDecodesNoncanonical(pinned, raw, bytes32(0), "raw.decode.partialOverlap");
        _assertPinnedRawInvalid(pinned, raw, "raw.offset.partialOverlap");

        raw = _insertZeroBytes(canonical, 0x220, 1);
        _shiftTopLevelDynamicPointers(raw, 1);
        _assertRawDecodesNoncanonical(pinned, raw, keccak256(canonical), "raw.decode.dynamicUnaligned");
        _assertPinnedRawInvalid(pinned, raw, "raw.offset.dynamicUnaligned");

        raw = _resizeBytes(canonical, canonical.length);
        _writeWord(raw, 0, canonical.length);
        _assertRawDecodeFails(pinned, raw, false, "raw.decode.outerOutOfBounds");
        _assertPinnedRawInvalid(pinned, raw, "raw.offset.outerOutOfBounds");

        // Force the first dynamic-array length to overflow memory allocation.
        // The production decoder must contain Panic(0x41) as INVALID, not OOG.
        raw = _resizeBytes(canonical, canonical.length);
        uint256 digestTail = 0x20 + _readWord(raw, 0x60);
        _writeWord(raw, digestTail, type(uint256).max);
        _assertRawDecodeFails(pinned, raw, true, "raw.decode.allocationOverflow");
        _assertPinnedRawInvalid(pinned, raw, "raw.length.allocationOverflow");

        // uint64 ABI words require zero upper padding. Flip the high bit of the
        // first log-preprocessed c0 limb to exercise strict typed decoding.
        raw = _resizeBytes(canonical, canonical.length);
        uint256 terminalTail = 0x20 + _readWord(raw, 0x160);
        _writeWord(raw, terminalTail + 32, _readWord(raw, terminalTail + 32) | (uint256(1) << 255));
        _assertRawDecodeFails(pinned, raw, false, "raw.decode.uint64HighBit");
        _assertPinnedRawInvalid(pinned, raw, "raw.padding.uint64HighBit");
    }

    function test_atomicConfigurationMutationIsUnevaluableNotFraud() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);

        MleVerifierV2.VerificationConfig memory badCircuit = _cloneConfig(fixture.config);
        badCircuit.kIs[0] = 2;
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        verifier.verify(fixture.proof, badCircuit);

        MleVerifierV2.VerificationConfig memory badWhir = _cloneConfig(fixture.config);
        ++badWhir.whir.inDomainSamples;
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        verifier.verify(fixture.proof, badWhir);
    }

    function test_atomicChainMismatchIsUnevaluableAndGuardRunsFirst() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        uint256 originalChain = block.chainid;
        uint256 otherChain = originalChain + 1;

        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierChainId.selector, otherChain, originalChain));
        new MleVerifierV2(
            otherChain,
            fixture.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            fixture.config
        );

        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        MleVerifierV2.MleProof memory alsoInvalidProof = _cloneProof(fixture.proof);
        alsoInvalidProof.protocolVersion = 2;
        MleVerifierV2.VerificationConfig memory alsoInvalidConfig = _cloneConfig(fixture.config);
        alsoInvalidConfig.kIs[0] = 2;
        vm.chainId(otherChain);
        vm.expectRevert(abi.encodeWithSelector(MleProofEngineUnavailable.selector, otherChain));
        verifier.verify(alsoInvalidProof, alsoInvalidConfig);
        vm.chainId(originalChain);
    }

    function test_encodedFraudVerdictSeparatesProofFraudPiAndUnevaluableFailures() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        encodedVerifier = _deployAtomicVerifier(fixture);
        bytes32 piHash;
        bytes4 callback = this.verifyEncodedV2Callback.selector;

        bytes memory canonical = abi.encode(fixture.proof);
        // The generic small_mul fixture has no eight-limb rollup PI digest, so
        // a cryptographically valid proof reaches the distinct PI-preimage result.
        assertEq(encodedVerifier.fraudVerdictEncoded(canonical, piHash, callback), 4, "PI verdict");

        MleVerifierV2.MleProof memory invalid = _cloneProof(fixture.proof);
        invalid.witnessRoot = bytes32(uint256(invalid.witnessRoot) ^ 1);
        assertEq(encodedVerifier.fraudVerdictEncoded(abi.encode(invalid), piHash, callback), 0, "fraud verdict");

        assertEq(
            encodedVerifier.fraudVerdictEncoded(canonical, piHash, this.verifyEncodedV2UnevaluableCallback.selector),
            2,
            "configuration failure must be unevaluable"
        );

        // Isolate the successful callback branch with a canonical 8-limb PI
        // tuple; production never uses this test callback in place of verify.
        MleVerifierV2.MleProof memory eightPi = _cloneProof(fixture.proof);
        eightPi.publicInputs = new uint256[](8);
        for (uint256 i = 0; i < 8; ++i) {
            eightPi.publicInputs[i] = i + 1;
        }
        bytes32 matchingPiHash = _publicInputsDigest(eightPi.publicInputs);
        bytes4 acceptingCallback = this.verifyEncodedV2AcceptingCallback.selector;
        assertEq(
            encodedVerifier.fraudVerdictEncoded(abi.encode(eightPi), matchingPiHash, acceptingCallback),
            1,
            "valid verdict"
        );
        assertEq(
            encodedVerifier.fraudVerdictEncoded(
                abi.encode(eightPi), bytes32(uint256(matchingPiHash) ^ 1), acceptingCallback
            ),
            4,
            "PI-preimage mismatch verdict"
        );
    }

    function test_encodedFraudVerdictRejectsNonCanonicalMalformedAndOldProofBytes() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        encodedVerifier = _deployAtomicVerifier(fixture);
        bytes32 piHash;
        bytes4 callback = this.verifyEncodedV2Callback.selector;
        bytes memory canonical = abi.encode(fixture.proof);

        assertEq(
            encodedVerifier.fraudVerdictEncoded(bytes.concat(canonical, hex"00"), piHash, callback),
            0,
            "trailing ABI bytes"
        );
        assertEq(encodedVerifier.fraudVerdictEncoded(hex"010203", piHash, callback), 0, "malformed ABI");

        MleVerifierV2.MleProof memory oldVersion = _cloneProof(fixture.proof);
        oldVersion.protocolVersion = 2;
        assertEq(
            encodedVerifier.fraudVerdictEncoded(abi.encode(oldVersion), piHash, callback),
            0,
            "old protocol version"
        );

        MleVerifier.MleProof memory v1Proof;
        v1Proof.protocolVersion = 1;
        assertEq(encodedVerifier.fraudVerdictEncoded(abi.encode(v1Proof), piHash, callback), 0, "v1 ABI bytes");
    }

    function test_encodedFraudVerdictChainGuardPrecedesMalformedProofClassification() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        encodedVerifier = _deployAtomicVerifier(fixture);
        uint256 originalChain = block.chainid;
        vm.chainId(originalChain + 1);
        assertEq(
            encodedVerifier.fraudVerdictEncoded(hex"010203", bytes32(0), bytes4(0)),
            2,
            "chain mismatch is unevaluable"
        );
        vm.chainId(originalChain);
    }

    function test_v2CoreHasNoLegacyVerificationBypassSelector() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        encodedVerifier = _deployAtomicVerifier(fixture);
        (bool ok,) = address(encodedVerifier).staticcall(
            abi.encodeWithSignature(
                "fraudVerdictEncoded(bytes,bytes32,bytes4,bool)", hex"", bytes32(0), bytes4(0), true
            )
        );
        assertFalse(ok, "legacy v2-core bypass selector remains callable");
    }

    function verifyEncodedV2Callback(MleVerifierV2.MleProof calldata proof) external view returns (bool) {
        require(msg.sender == address(encodedVerifier), "encoded callback caller");
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        return encodedVerifier.verify(proof, fixture.config);
    }

    function verifyEncodedV2UnevaluableCallback(MleVerifierV2.MleProof calldata) external pure returns (bool) {
        revert InvalidMleVerifierConfiguration();
    }

    function verifyEncodedV2AcceptingCallback(MleVerifierV2.MleProof calldata) external view returns (bool) {
        require(msg.sender == address(encodedVerifier), "encoded callback caller");
        return true;
    }

    function test_constructorRejectsStructurallyValidNonCanonicalWhirScalar() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2.VerificationConfig memory drifted = _cloneConfig(fixture.config);
        ++drifted.whir.inDomainSamples;

        // The generic WHIR shape validator deliberately permits this sampling
        // count. Deployment must still reject it because the exact Rust profile
        // digest, rather than structural plausibility, is the security boundary.
        _requireStructurallyValidWhir(drifted.whir);
        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierConfiguration.selector));
        new MleVerifierV2(
            block.chainid,
            fixture.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            drifted
        );
    }

    function test_constructorRejectsAlternativePermutationCosetRepresentatives() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2.VerificationConfig memory drifted = _cloneConfig(fixture.config);

        // Multiplying every canonical k_i by the same non-subgroup scalar
        // preserves non-zero/distinct-coset checks, but changes the identity
        // polynomials in the permutation relation. Rust's CommonCircuitData
        // never emits this sequence, so deployment must reject it.
        for (uint256 i = 0; i < drifted.kIs.length; ++i) {
            drifted.kIs[i] = mulmod(drifted.kIs[i], 2, BASE_FIELD_MODULUS_V2);
        }

        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierConfiguration.selector));
        new MleVerifierV2(
            block.chainid,
            fixture.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            drifted
        );
    }

    function test_constructorRejectsAlternativePrimitiveRowGenerator() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2.VerificationConfig memory drifted = _cloneConfig(fixture.config);

        // g^3 generates the same-order subgroup as g. Rebuilding the complete
        // square chain therefore passes the former structural checks and ends
        // at -1, but it permutes row identities relative to Rust/Plonky2.
        uint256 generator = drifted.subgroupGenPowers[0];
        generator = mulmod(mulmod(generator, generator, BASE_FIELD_MODULUS_V2), generator, BASE_FIELD_MODULUS_V2);
        for (uint256 i = 0; i < drifted.subgroupGenPowers.length; ++i) {
            drifted.subgroupGenPowers[i] = generator;
            generator = mulmod(generator, generator, BASE_FIELD_MODULUS_V2);
        }

        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierConfiguration.selector));
        new MleVerifierV2(
            block.chainid,
            fixture.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            drifted
        );
    }

    function test_constructorRejectsNonCanonicalWhirProtocolIdSecondHalf() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        bytes32[2] memory driftedProtocolId = fixture.whirProtocolId;
        driftedProtocolId[1] = bytes32(uint256(driftedProtocolId[1]) ^ 1);

        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierConfiguration.selector));
        new MleVerifierV2(
            block.chainid,
            fixture.preprocessedRoot,
            driftedProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            fixture.config
        );
    }

    function test_constructorRejectsNonCanonicalWhirSessionId() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        bytes32 driftedSessionId = bytes32(uint256(fixture.whirSessionId) ^ 1);

        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierConfiguration.selector));
        new MleVerifierV2(
            block.chainid,
            fixture.preprocessedRoot,
            fixture.whirProtocolId,
            driftedSessionId,
            fixture.circuitDigest,
            fixture.config
        );
    }

    function test_replaysAll78RustTranscriptCheckpointsByteExactly() external view {
        string memory json = vm.readFile(FIXTURE);
        _assertProtocolEventOrder(json);

        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        for (uint256 eventIndex = 0; eventIndex < EVENT_COUNT; ++eventIndex) {
            _replayEvent(json, transcript, eventIndex);
        }

        assertEq(transcript.squeezeCounter, 48, "final squeeze counter");
        _assertNoStringPath(json, _eventField(EVENT_COUNT, "kind"), "unexpected transcript tail");
    }

    function test_schemaMetadataIdentifiersAndCommitmentOrder() external view {
        string memory json = vm.readFile(FIXTURE);
        assertEq(vm.parseJsonString(json, ".schema"), "plonky2-mle-v3-cross-language");
        assertEq(vm.parseJsonUint(json, ".version"), MLE_PROTOCOL_VERSION_CURRENT);
        assertEq(vm.parseUint(vm.parseJsonString(json, ".field.modulus")), BASE_FIELD_MODULUS_V2);

        string[] memory limbs = vm.parseJsonStringArray(json, ".field.ext3LimbOrder");
        assertEq(limbs.length, EXTENSION_FIELD_LIMBS_V2);
        assertEq(limbs[0], "c0");
        assertEq(limbs[1], "c1");
        assertEq(limbs[2], "c2");
        assertEq(vm.parseJsonString(json, ".field.compactLimbByteOrder"), "little-endian");
        assertEq(vm.parseJsonUint(json, ".field.transcriptTags.domain"), TAG_DOMAIN_V2);
        assertEq(vm.parseJsonUint(json, ".field.transcriptTags.bytes"), TAG_BYTES_V2);
        assertEq(vm.parseJsonUint(json, ".field.transcriptTags.fieldVec"), TAG_FIELD_VEC_V2);
        assertEq(vm.parseJsonUint(json, ".field.transcriptTags.ext3Vec"), TAG_EXT3_VEC_V2);

        string[] memory groups = vm.parseJsonStringArray(json, ".groupOrder");
        assertEq(groups.length, NUM_PCS_GROUPS_V2);
        assertEq(groups[GROUP_PREPROCESSED_V2], "preprocessed");
        assertEq(groups[GROUP_WITNESS_V2], "witness");
        assertEq(groups[GROUP_NORM_INVERSE_V2], "norm_inverse");
        string[] memory points = vm.parseJsonStringArray(json, ".pointOrder");
        assertEq(points.length, NUM_PCS_TERMINAL_POINTS_V2);
        assertEq(points[POINT_LOG_V2], "log");
        assertEq(points[POINT_GATE_V2], "gate");

        bytes memory metadata = vm.parseJsonBytes(json, _eventField(5, "payload"));
        assertEq(metadata.length, 15 * 8, "schema metadata byte length");
        uint256[15] memory expected;
        expected[0] = MLE_PROTOCOL_VERSION_CURRENT;
        expected[1] = NUM_PCS_GROUPS_V2;
        expected[2] = NUM_PCS_TERMINAL_POINTS_V2;
        expected[3] = NUM_PCS_CLAIMS_V2;
        expected[4] = vm.parseJsonUint(json, string.concat(CASE, ".verificationKey.numConstants"));
        expected[5] = vm.parseJsonUint(json, string.concat(CASE, ".verificationKey.numRoutedWires"));
        expected[6] = vm.parseJsonUint(json, string.concat(CASE, ".verificationKey.numWires"));
        expected[7] = vm.parseJsonUint(json, string.concat(CASE, ".circuit.degreeBits"));
        expected[8] = vm.parseJsonUint(json, string.concat(CASE, ".verificationKey.constituentWidth"));
        expected[9] = 8;
        expected[10] = NUM_PACKED_VECTORS_PER_GROUP_V2;
        expected[11] = EXTENSION_FIELD_LIMBS_V2;
        expected[12] = PACKED_VARIABLE_ORDER_CODE_V2;
        expected[13] = GATE_SUMCHECK_COUNT_V2;
        expected[14] = LOG_ROUND_DEGREE_V2;
        for (uint256 i = 0; i < expected.length; ++i) {
            assertEq(_readU64Le(metadata, 8 * i), expected[i], string.concat("schema metadata[", vm.toString(i), "]"));
        }

        _assertEventPayloadEqualsJson(json, 7, string.concat(CASE, ".verificationKey.circuitConfigDigest"));
        _assertEventPayloadEqualsJson(json, 9, string.concat(CASE, ".verificationKey.whirProtocolId"));
        _assertEventPayloadEqualsJson(json, 11, string.concat(CASE, ".verificationKey.whirSessionId"));
        _assertEventPayloadEqualsJson(json, 13, string.concat(CASE, ".verificationKey.preprocessedCommitmentRoot"));
        assertEq(vm.parseJsonBytes(json, _eventField(9, "payload")).length, 64, "WHIR protocol id length");
        assertEq(vm.parseJsonBytes(json, _eventField(11, "payload")).length, 32, "WHIR session id length");
    }

    function test_twoPackedPointsAndSixClaimsMatchProductionExt3Fold() external view {
        string memory json = vm.readFile(FIXTURE);
        assertEq(_hexField(json, string.concat(CASE, ".packedClaimMask")), uint8(PACKED_BOUND_CLAIM_MASK_V2));
        assertEq(NUM_BOUND_PCS_CLAIMS_V2, 5);

        GoldilocksExt3.Ext3[][] memory indexPoints = new GoldilocksExt3.Ext3[][](NUM_PCS_TERMINAL_POINTS_V2);
        for (uint256 point = 0; point < NUM_PCS_TERMINAL_POINTS_V2; ++point) {
            _assertPackedPoint(json, point);
            indexPoints[point] = _ext3Array(
                json, string.concat(CASE, ".packedPoints[", vm.toString(point), "].constituentIndexPoint"), 8
            );
            assertEq(indexPoints[point].length, 8, "constituent index width");
        }
        _assertNoStringPath(json, string.concat(CASE, ".packedPoints[2].name"), "unexpected packed point tail");

        PackedClaimExt3.UsedClaims memory claims;
        claims.logPreprocessed = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(53, "payload")));
        claims.logWitness = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(54, "payload")));
        claims.logNormInverse = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(55, "payload")));
        claims.gatePreprocessed = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(56, "payload")));
        claims.gateWitness = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(57, "payload")));

        PackedClaimExt3.Schema memory schema = PackedClaimExt3.Schema({
            width: vm.parseJsonUint(json, string.concat(CASE, ".compactShape.constituentWidth")),
            numConstants: vm.parseJsonUint(json, string.concat(CASE, ".compactShape.numConstants")),
            numRoutedWires: vm.parseJsonUint(json, string.concat(CASE, ".compactShape.numRoutedWires")),
            numWires: vm.parseJsonUint(json, string.concat(CASE, ".compactShape.numWires"))
        });
        (GoldilocksExt3.Ext3[] memory folded, bytes memory mask) =
            PackedClaimExt3.foldV2UsedCells(claims, schema, indexPoints);
        assertEq(folded.length, NUM_PCS_CLAIMS_V2);
        assertEq(mask.length, 1);
        assertEq(uint8(mask[0]), uint8(PACKED_BOUND_CLAIM_MASK_V2));

        string[3] memory groupNames = [string("preprocessed"), "witness", "norm_inverse"];
        string[2] memory pointNames = [string("log"), "gate"];
        for (uint256 claim = 0; claim < NUM_PCS_CLAIMS_V2; ++claim) {
            string memory base = string.concat(CASE, ".packedClaims[", vm.toString(claim), "]");
            uint256 pointIndex = claim / NUM_PCS_GROUPS_V2;
            uint256 groupIndex = claim % NUM_PCS_GROUPS_V2;
            bool used = (uint8(PACKED_BOUND_CLAIM_MASK_V2) & (uint8(1) << uint8(claim))) != 0;
            assertEq(vm.parseJsonUint(json, string.concat(base, ".pointIndex")), pointIndex);
            assertEq(vm.parseJsonUint(json, string.concat(base, ".groupIndex")), groupIndex);
            assertEq(vm.parseJsonString(json, string.concat(base, ".point")), pointNames[pointIndex]);
            assertEq(vm.parseJsonString(json, string.concat(base, ".group")), groupNames[groupIndex]);
            assertEq(vm.parseJsonBool(json, string.concat(base, ".used")), used);
            if (used) {
                _assertExt3Eq(folded[claim], _ext3(json, string.concat(base, ".value")), "folded packed claim");
            } else {
                _assertExt3Eq(folded[claim], GoldilocksExt3.Ext3(0, 0, 0), "unused packed claim");
                _assertNoStringPath(json, string.concat(base, ".value[0]"), "unused claim unexpectedly has a value");
            }
        }
        _assertNoStringPath(json, string.concat(CASE, ".packedClaims[6].point"), "unexpected packed claim tail");
    }

    function test_compactProofHeaderRootsAndEveryOuterVectorAreBound() external view {
        string memory json = vm.readFile(FIXTURE);
        bytes memory compact = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));
        assertEq(compact.length, vm.parseJsonUint(json, string.concat(CASE, ".compactProof.byteLength")));
        assertLe(compact.length, MAX_COMPACT_PROOF_BYTES_V2);
        assertEq(keccak256(compact), vm.parseJsonBytes32(json, string.concat(CASE, ".compactProof.keccak256")));
        assertEq(
            vm.parseJsonString(json, string.concat(CASE, ".compactProof.encoding")),
            string(abi.encodePacked(COMPACT_MAGIC_V2))
        );
        assertEq(COMPACT_FIELD_COUNT_V2, 17);
        assertEq(COMPACT_LAYOUT_HASH_V2, 0xe3d01532fb72b31d049076afef24b96863866a91a0bb3f66ae90ee39a62e4b97);

        uint256 cursor;
        _assertRangeEqual(compact, cursor, abi.encodePacked(COMPACT_MAGIC_V2), 0, 8, "compact magic");
        cursor += 8;
        assertEq(_readU64Le(compact, cursor), MLE_PROTOCOL_VERSION_CURRENT, "compact protocol version");
        cursor += 8;
        assertEq(
            _readU32Le(compact, cursor),
            vm.parseJsonUint(json, string.concat(CASE, ".compactShape.constituentWidth")),
            "compact constituent width"
        );
        cursor += 4;

        uint256 digestLength = vm.parseJsonUint(json, string.concat(CASE, ".compactShape.circuitDigestLen"));
        for (uint256 i = 0; i < digestLength; ++i) {
            assertEq(
                _readCanonicalU64Le(compact, cursor),
                _hexField(json, string.concat(CASE, ".verificationKey.circuitDigest[", vm.toString(i), "]")),
                "compact circuit digest"
            );
            cursor += 8;
        }
        uint256 publicInputLength = vm.parseJsonUint(json, string.concat(CASE, ".compactShape.publicInputsLen"));
        for (uint256 i = 0; i < publicInputLength; ++i) {
            assertEq(
                _readCanonicalU64Le(compact, cursor),
                _hexField(json, string.concat(CASE, ".circuit.expectedPublicInputs[", vm.toString(i), "]")),
                "compact public input"
            );
            cursor += 8;
        }

        for (uint256 root = 0; root < NUM_PCS_GROUPS_V2; ++root) {
            uint256 eventIndex = root == 0 ? 13 : (root == 1 ? 15 : 22);
            bytes memory eventRoot = vm.parseJsonBytes(json, _eventField(eventIndex, "payload"));
            assertEq(eventRoot.length, 32);
            _assertRangeEqual(compact, cursor, eventRoot, 0, 32, "compact ordered root");
            cursor += 32;
        }

        uint256 nargLength = _readU32Le(compact, cursor);
        cursor += 4;
        assertLe(nargLength, MAX_WHIR_NARG_BYTES_V2);
        assertLe(cursor + nargLength, compact.length, "compact narg bounds");
        cursor += nargLength;
        uint256 hintLength = _readU32Le(compact, cursor);
        cursor += 4;
        assertLe(hintLength, MAX_WHIR_HINT_BYTES_V2);
        assertLe(cursor + hintLength, compact.length, "compact hint bounds");
        cursor += hintLength;

        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(37, "payload")), 5);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(46, "payload")), 5);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(53, "payload")), 84);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(54, "payload")), 135);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(55, "payload")), 160);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(38, "payload")), 10);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(47, "payload")), 10);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(56, "payload")), 84);
        cursor = _consumeExt3Payload(compact, cursor, vm.parseJsonBytes(json, _eventField(57, "payload")), 135);
        assertEq(cursor, compact.length, "compact trailing bytes or omitted field");

        assertEq(vm.parseJsonUint(json, string.concat(CASE, ".compactShape.maxWhirNargBytes")), MAX_WHIR_NARG_BYTES_V2);
        assertEq(vm.parseJsonUint(json, string.concat(CASE, ".compactShape.maxWhirHintBytes")), MAX_WHIR_HINT_BYTES_V2);
        assertEq(
            vm.parseJsonUint(json, string.concat(CASE, ".compactShape.maxEncodedBytes")), MAX_COMPACT_PROOF_BYTES_V2
        );
    }

    function test_pinnedCompactAcceptsCanonicalRustProofAndPreservesPiVerdict() external {
        string memory json = vm.readFile(FIXTURE);
        AtomicFixture memory fixture = _parseAtomicFixture(json);
        MleVerifierV2 core = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory compact = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));

        uint256 gasBefore = gasleft();
        assertTrue(pinned.verifyCompact(compact), "canonical compact proof");
        uint256 verifyGas = gasBefore - gasleft();
        emit log_named_uint("PinnedMleVerifierV2.verifyCompact gas", verifyGas);
        assertLt(verifyGas, 30_000_000, "compact verification must fit the 30m envelope");

        uint256[] memory authenticatedPublicInputs = pinned.verifyCompactPublicInputs(compact);
        assertEq(authenticatedPublicInputs.length, fixture.proof.publicInputs.length, "authenticated PI length");
        for (uint256 i = 0; i < authenticatedPublicInputs.length; ++i) {
            assertEq(authenticatedPublicInputs[i], fixture.proof.publicInputs[i], "authenticated PI value");
        }
        assertEq(
            pinned.fraudVerdictCompact(compact, bytes32(0)), 4, "valid generic fixture has a non-rollup PI shape"
        );
    }

    function test_adversarialPinnedCompactSyntaxAndWhirMutationVerdicts() external {
        string memory json = vm.readFile(FIXTURE);
        AtomicFixture memory fixture = _parseAtomicFixture(json);
        MleVerifierV2 core = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory canonical = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));
        bytes memory compact;

        compact = _resizeBytes(canonical, canonical.length);
        compact[0] = bytes1(uint8(compact[0]) ^ 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.magic");

        compact = _resizeBytes(canonical, canonical.length);
        compact[8] = bytes1(uint8(compact[8]) ^ 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.version");

        compact = _resizeBytes(canonical, canonical.length);
        compact[16] = bytes1(uint8(compact[16]) ^ 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.width");

        _assertPinnedCompactInvalid(pinned, _resizeBytes(canonical, canonical.length - 1), "compact.truncated");
        _assertPinnedCompactInvalid(pinned, bytes.concat(canonical, hex"00"), "compact.trailing");
        _assertPinnedCompactInvalid(
            pinned, _resizeBytes(canonical, MAX_COMPACT_PROOF_BYTES_V2 + 1), "compact.totalLengthCap"
        );

        compact = _resizeBytes(canonical, canonical.length);
        _writeU64Le(compact, 20, BASE_FIELD_MODULUS_V2);
        _assertPinnedCompactInvalid(pinned, compact, "compact.noncanonicalDigestLimb");

        uint256 cursor = 8 + 8 + 4 + 4 * 8 + fixture.config.circuit.numPublicInputs * 8 + 3 * 32;
        uint256 nargLength = _readU32Le(canonical, cursor);
        uint256 nargStart = cursor + 4;
        require(nargLength != 0 && nargStart + nargLength + 4 <= canonical.length, "compact NARG layout");
        uint256 hintLength = _readU32Le(canonical, nargStart + nargLength);
        uint256 hintStart = nargStart + nargLength + 4;
        require(hintLength != 0 && hintStart + hintLength <= canonical.length, "compact hint layout");

        compact = _resizeBytes(canonical, canonical.length);
        _writeU32Le(compact, cursor, MAX_WHIR_NARG_BYTES_V2 + 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirNargLengthCap");

        compact = _resizeBytes(canonical, canonical.length);
        _writeU32Le(compact, cursor, nargLength - 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirNargLengthShort");

        compact = _resizeBytes(canonical, canonical.length);
        _writeU32Le(compact, cursor, nargLength + 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirNargLengthLong");

        compact = _resizeBytes(canonical, canonical.length);
        _writeU32Le(compact, nargStart + nargLength, MAX_WHIR_HINT_BYTES_V2 + 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirHintLengthCap");

        compact = _resizeBytes(canonical, canonical.length);
        _writeU32Le(compact, nargStart + nargLength, hintLength - 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirHintLengthShort");

        compact = _resizeBytes(canonical, canonical.length);
        _writeU32Le(compact, nargStart + nargLength, hintLength + 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirHintLengthLong");

        compact = _resizeBytes(canonical, canonical.length);
        _writeU64Le(compact, hintStart + hintLength, BASE_FIELD_MODULUS_V2);
        _assertPinnedCompactInvalid(pinned, compact, "compact.noncanonicalExt3Limb");

        compact = _resizeBytes(canonical, canonical.length);
        uint256 nargOffset = nargStart + nargLength / 2;
        compact[nargOffset] = bytes1(uint8(compact[nargOffset]) ^ 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirNargInternal");

        compact = _resizeBytes(canonical, canonical.length);
        uint256 hintOffset = hintStart + hintLength / 2;
        compact[hintOffset] = bytes1(uint8(compact[hintOffset]) ^ 1);
        _assertPinnedCompactInvalid(pinned, compact, "compact.whirHintInternal");
    }

    function test_adversarialPinnedCompactLowGasIsStarvedNotInvalid() external {
        string memory json = vm.readFile(FIXTURE);
        AtomicFixture memory fixture = _parseAtomicFixture(json);
        MleVerifierV2 core = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory compact = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));
        bytes memory callData = abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (compact, bytes32(0)));

        // Keep enough gas for strict compact decoding and the classifier's
        // EIP-150 reserve, but less than an honest end-to-end verification.
        // This is a containment test, not a snapshot of verifier performance.
        (bool success, bytes memory result) = address(pinned).staticcall{gas: 10_000_000}(callData);
        assertTrue(success, "compact low-gas classifier must contain exhaustion");
        assertEq(result.length, 32, "compact low-gas verdict encoding");
        assertEq(uint256(abi.decode(result, (uint8))), 3, "compact low gas must be STARVED");
    }

    function test_adversarialPinnedCompactUnknownFailureIsUnevaluable() external {
        string memory json = vm.readFile(FIXTURE);
        AtomicFixture memory fixture = _parseAtomicFixture(json);
        MleVerifierV2 core = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        bytes memory compact = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));

        vm.mockCallRevert(address(core), MleVerifierV2.verify.selector, hex"deadbeef");
        assertEq(
            pinned.fraudVerdictCompact(compact, bytes32(0)),
            2,
            "unknown compact verification failure must be UNEVALUABLE"
        );
        vm.clearMockedCalls();
    }

    function test_adversarialPinnedCompactChainGuardPrecedesDecoding() external {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 core = _deployAtomicVerifier(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);
        uint256 originalChain = block.chainid;
        uint256 otherChain = originalChain + 1;

        vm.chainId(otherChain);
        assertEq(
            pinned.fraudVerdictCompact(hex"010203", bytes32(0)),
            2,
            "chain guard must classify before compact decoding"
        );
        vm.expectRevert(abi.encodeWithSelector(MleProofEngineUnavailable.selector, otherChain));
        pinned.verifyCompact(hex"010203");
        vm.chainId(originalChain);
    }

    function test_productionCoupledSumchecksAndTerminalRecordsConsumeSameFixture() external {
        string memory json = vm.readFile(FIXTURE);
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        for (uint256 eventIndex = 0; eventIndex < 34; ++eventIndex) {
            _replayEvent(json, transcript, eventIndex);
        }

        OuterLogupExt3Verifier.SumcheckProof memory logProof;
        OuterLogupExt3Verifier.SumcheckProof memory gateProof;
        logProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](2);
        gateProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](2);
        logProof.rounds[0].nonConstant = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(37, "payload")));
        gateProof.rounds[0].nonConstant = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(38, "payload")));
        logProof.rounds[1].nonConstant = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(46, "payload")));
        gateProof.rounds[1].nonConstant = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(47, "payload")));

        OuterLogupExt3Verifier.VerificationKey memory vk = OuterLogupExt3Verifier.VerificationKey({
            numVars: 2,
            gateDegree: vm.parseJsonUint(json, string.concat(CASE, ".compactShape.gateRoundDegree")),
            numConstants: vm.parseJsonUint(json, string.concat(CASE, ".verificationKey.numConstants")),
            numRoutedWires: vm.parseJsonUint(json, string.concat(CASE, ".verificationKey.numRoutedWires")),
            numWires: vm.parseJsonUint(json, string.concat(CASE, ".verificationKey.numWires")),
            kIs: _hexFieldArray(json, string.concat(CASE, ".verificationKey.kIs")),
            subgroupGenPowers: _hexFieldArray(json, string.concat(CASE, ".verificationKey.subgroupGenPowers")),
            publicInputWireMap: vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.publicInputWireMap"))
        });
        OuterLogupExt3Verifier.Challenges memory challenges;
        challenges.eta = _ext3(json, _eventField(17, "challenge"));
        challenges.beta = _ext3(json, _eventField(19, "challenge"));
        challenges.gamma = _ext3(json, _eventField(20, "challenge"));
        challenges.xi = _ext3(json, _eventField(24, "challenge"));
        challenges.lambda = _ext3(json, _eventField(26, "challenge"));
        challenges.rho = _ext3(json, _eventField(27, "challenge"));
        challenges.kappa = _ext3(json, _eventField(28, "challenge"));
        challenges.tau = new GoldilocksExt3.Ext3[](2);
        challenges.tau[0] = _ext3(json, _eventField(29, "challenge"));
        challenges.tau[1] = _ext3(json, _eventField(30, "challenge"));

        OuterLogupExt3Verifier.TerminalEvaluations memory terminal;
        terminal.preprocessed = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(53, "payload")));
        terminal.witness = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(54, "payload")));
        terminal.normInverse = _parseExt3VecPayload(vm.parseJsonBytes(json, _eventField(55, "payload")));
        terminal.publicInputs = _hexFieldArray(json, string.concat(CASE, ".circuit.expectedPublicInputs"));

        uint256 componentGasBefore = gasleft();
        (GoldilocksExt3.Ext3[] memory profiledLogPoint, GoldilocksExt3.Ext3 memory profiledLogClaim,,,) =
            OuterLogupExt3Verifier.verifyCoupledSumchecks(logProof, gateProof, vk.gateDegree, vk.numVars, transcript);
        emit log_named_uint("OuterLogupExt3Verifier.verifyCoupledSumchecks gas", componentGasBefore - gasleft());
        componentGasBefore = gasleft();
        GoldilocksExt3.Ext3 memory profiledTerminal =
            OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, profiledLogPoint);
        emit log_named_uint("OuterLogupExt3Verifier.evaluateTerminal gas", componentGasBefore - gasleft());
        _assertExt3Eq(profiledTerminal, profiledLogClaim, "profiled terminal");

        uint256 gasBefore = gasleft();
        (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        ) = OuterLogupExt3Verifier.verify(logProof, gateProof, vk, challenges, terminal, transcript);
        emit log_named_uint("OuterLogupExt3Verifier.verify gas", gasBefore - gasleft());
        assertEq(nextTranscript.state, vm.parseJsonBytes32(json, _eventField(51, "state")));
        assertEq(nextTranscript.squeezeCounter, vm.parseJsonUint(json, _eventField(51, "squeezeCounter")));
        for (uint256 round = 0; round < 2; ++round) {
            _assertExt3Eq(
                logPoint[round],
                _ext3(json, string.concat(CASE, ".packedPoints[0].rowPoint[", vm.toString(round), "]")),
                "production log point"
            );
            _assertExt3Eq(
                gatePoint[round],
                _ext3(json, string.concat(CASE, ".packedPoints[1].rowPoint[", vm.toString(round), "]")),
                "production gate point"
            );
        }

        GoldilocksExt3.Ext3 memory recordedLogFinal = _ext3(json, string.concat(CASE, ".terminals.logFinalClaim"));
        _assertExt3Eq(recordedLogFinal, _ext3(json, string.concat(CASE, ".terminals.logTerminal")), "log terminal");
        _assertExt3Eq(gateFinalClaim, _ext3(json, string.concat(CASE, ".terminals.gateFinalClaim")), "gate final claim");
        GoldilocksExt3.Ext3 memory gateAggregation =
            _ext3(json, string.concat(CASE, ".terminals.gateConstraintAggregation"));
        GoldilocksExt3.Ext3 memory gateEq = _ext3(json, string.concat(CASE, ".terminals.gateEqEvaluation"));
        GoldilocksExt3.Ext3 memory expectedGate = GoldilocksExt3.mul(gateEq, gateAggregation);
        _assertExt3Eq(
            expectedGate, _ext3(json, string.concat(CASE, ".terminals.gateExpectedFinalClaim")), "gate product"
        );
        _assertExt3Eq(expectedGate, gateFinalClaim, "gate terminal claim");
        GoldilocksExt3.Ext3[] memory gateTau = new GoldilocksExt3.Ext3[](2);
        gateTau[0] = _ext3(json, _eventField(32, "challenge"));
        gateTau[1] = _ext3(json, _eventField(33, "challenge"));
        OuterLogupExt3Verifier.verifyGateTerminal(gateTau, gatePoint, gateAggregation, gateFinalClaim);

        uint256[] memory publicInputs = _hexFieldArray(json, string.concat(CASE, ".circuit.expectedPublicInputs"));
        uint256[4] memory publicInputsHash = PoseidonPublicInputsHash.hashNoPad(publicInputs);
        uint256[] memory recordedHash = _hexFieldArray(json, string.concat(CASE, ".terminals.publicInputsHash"));
        assertEq(recordedHash.length, 4);
        for (uint256 i = 0; i < 4; ++i) {
            assertEq(publicInputsHash[i], recordedHash[i], "public-input hash");
        }
    }

    function _parseAtomicFixture(string memory json) private pure returns (AtomicFixture memory fixture) {
        fixture.config = _parseVerificationConfig(json);
        fixture.proof = _decodeCompactProof(
            vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes")), fixture.config.circuit
        );
        fixture.preprocessedRoot =
            vm.parseJsonBytes32(json, string.concat(CASE, ".verificationKey.preprocessedCommitmentRoot"));
        require(fixture.proof.preprocessedRoot == fixture.preprocessedRoot, "fixture preprocessed root drift");

        bytes memory protocolId = vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.whirProtocolId"));
        require(protocolId.length == 64, "fixture WHIR protocol id length");
        fixture.whirProtocolId[0] = _bytes32At(protocolId, 0);
        fixture.whirProtocolId[1] = _bytes32At(protocolId, 32);
        fixture.whirSessionId = vm.parseJsonBytes32(json, string.concat(CASE, ".verificationKey.whirSessionId"));
        for (uint256 i = 0; i < 4; ++i) {
            fixture.circuitDigest[i] = uint64(fixture.proof.circuitDigest[i]);
        }
    }

    function _cloneProof(MleVerifierV2.MleProof memory proof) private pure returns (MleVerifierV2.MleProof memory) {
        return abi.decode(abi.encode(proof), (MleVerifierV2.MleProof));
    }

    function _cloneConfig(MleVerifierV2.VerificationConfig memory config)
        private
        pure
        returns (MleVerifierV2.VerificationConfig memory)
    {
        return abi.decode(abi.encode(config), (MleVerifierV2.VerificationConfig));
    }

    function _requireStructurallyValidWhir(SpongefishWhirVerify.WhirParams memory whir) private pure {
        SpongefishWhirVerify.WhirParams memory validationCopy =
            abi.decode(abi.encode(whir), (SpongefishWhirVerify.WhirParams));
        validationCopy.evaluationPoint = new GoldilocksExt3.Ext3[](validationCopy.numVariables);
        validationCopy.evaluationPoint2 = new GoldilocksExt3.Ext3[](validationCopy.numVariables);
        validationCopy.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        SpongefishWhirVerify.validateParameters(validationCopy, NUM_PCS_TERMINAL_POINTS_V2);
    }

    function _mutateProofShape(MleVerifierV2.MleProof memory proof, uint256 mutation) private pure {
        if (mutation == 0) {
            proof.circuitDigest = _resizeUint256(proof.circuitDigest, proof.circuitDigest.length - 1);
        } else if (mutation == 1) {
            proof.circuitDigest = _resizeUint256(proof.circuitDigest, proof.circuitDigest.length + 1);
        } else if (mutation == 2) {
            proof.publicInputs = _resizeUint256(proof.publicInputs, proof.publicInputs.length - 1);
        } else if (mutation == 3) {
            proof.publicInputs = _resizeUint256(proof.publicInputs, proof.publicInputs.length + 1);
        } else if (mutation == 4) {
            proof.logProof.rounds = _resizeRounds(proof.logProof.rounds, proof.logProof.rounds.length - 1);
        } else if (mutation == 5) {
            proof.logProof.rounds = _resizeRounds(proof.logProof.rounds, proof.logProof.rounds.length + 1);
        } else if (mutation == 6) {
            proof.gateProof.rounds = _resizeRounds(proof.gateProof.rounds, proof.gateProof.rounds.length - 1);
        } else if (mutation == 7) {
            proof.gateProof.rounds = _resizeRounds(proof.gateProof.rounds, proof.gateProof.rounds.length + 1);
        } else if (mutation >= 8 && mutation < 12) {
            uint256 round = (mutation - 8) / 2;
            GoldilocksExt3.Ext3[] memory values = proof.logProof.rounds[round].nonConstant;
            proof.logProof.rounds[round].nonConstant =
                _resizeExt3(values, mutation % 2 == 0 ? values.length - 1 : values.length + 1);
        } else if (mutation >= 12 && mutation < 16) {
            uint256 round = (mutation - 12) / 2;
            GoldilocksExt3.Ext3[] memory values = proof.gateProof.rounds[round].nonConstant;
            proof.gateProof.rounds[round].nonConstant =
                _resizeExt3(values, mutation % 2 == 0 ? values.length - 1 : values.length + 1);
        } else if (mutation >= 16 && mutation < 26) {
            uint256 field = (mutation - 16) / 2;
            GoldilocksExt3.Ext3[] memory values = _terminalVector(proof, field);
            uint256 replacementLength = mutation % 2 == 0 ? values.length - 1 : values.length + 1;
            _setTerminalVector(proof, field, _resizeExt3(values, replacementLength));
        } else if (mutation == 26) {
            proof.whirTranscript = new bytes(0);
        } else if (mutation == 27) {
            proof.whirTranscript = _resizeBytes(proof.whirTranscript, proof.whirTranscript.length - 1);
        } else if (mutation == 28) {
            proof.whirTranscript = _resizeBytes(proof.whirTranscript, proof.whirTranscript.length + 1);
        } else if (mutation == 29) {
            proof.whirHints = new bytes(0);
        } else if (mutation == 30) {
            proof.whirHints = _resizeBytes(proof.whirHints, proof.whirHints.length - 1);
        } else if (mutation == 31) {
            proof.whirHints = _resizeBytes(proof.whirHints, proof.whirHints.length + 1);
        } else {
            revert("unknown shape mutation");
        }
    }

    function _shapeMutationLabel(uint256 mutation) private pure returns (string memory) {
        if (mutation == 0) return "shape.circuitDigest.short";
        if (mutation == 1) return "shape.circuitDigest.long";
        if (mutation == 2) return "shape.publicInputs.short";
        if (mutation == 3) return "shape.publicInputs.long";
        if (mutation == 4) return "shape.logRounds.short";
        if (mutation == 5) return "shape.logRounds.long";
        if (mutation == 6) return "shape.gateRounds.short";
        if (mutation == 7) return "shape.gateRounds.long";
        if (mutation >= 8 && mutation < 12) {
            return _indexedLabel(
                mutation % 2 == 0 ? "shape.logCoefficients.short" : "shape.logCoefficients.long",
                (mutation - 8) / 2,
                0,
                0
            );
        }
        if (mutation >= 12 && mutation < 16) {
            return _indexedLabel(
                mutation % 2 == 0 ? "shape.gateCoefficients.short" : "shape.gateCoefficients.long",
                (mutation - 12) / 2,
                0,
                0
            );
        }
        if (mutation >= 16 && mutation < 26) {
            return
                string.concat(
                    "shape.", _terminalVectorName((mutation - 16) / 2), mutation % 2 == 0 ? ".short" : ".long"
                );
        }
        if (mutation == 26) return "shape.whirTranscript.empty";
        if (mutation == 27) return "shape.whirTranscript.truncated";
        if (mutation == 28) return "shape.whirTranscript.trailing";
        if (mutation == 29) return "shape.whirHints.empty";
        if (mutation == 30) return "shape.whirHints.truncated";
        if (mutation == 31) return "shape.whirHints.trailing";
        revert("unknown shape mutation");
    }

    function _runWhirRecordMutations(bool narg, uint256 startRecord, uint256 endRecord, uint256 samples) private {
        require(samples >= 2, "WHIR mutation sample count");
        string memory json = vm.readFile(FIXTURE);
        AtomicFixture memory fixture = _parseAtomicFixture(json);
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        MleVerifierV2.MleProof memory proof = _cloneProof(fixture.proof);
        uint256[] memory positions = vm.parseJsonUintArray(
            json, string.concat(CASE, narg ? ".whirNative.nargPositions" : ".whirNative.hintPositions")
        );
        bytes memory stream = narg ? proof.whirTranscript : proof.whirHints;
        require(positions.length > 1 && positions[positions.length - 1] == stream.length, "WHIR trace cursor drift");

        uint256 record;
        for (uint256 eventIndex = 1; eventIndex < positions.length; ++eventIndex) {
            uint256 start = positions[eventIndex - 1];
            uint256 end = positions[eventIndex];
            if (end == start) continue;
            require(end > start && end <= stream.length, "WHIR trace cursor order");
            if (record >= startRecord && record < endRecord) {
                uint256 span = end - start;
                for (uint256 sample = 0; sample < samples; ++sample) {
                    uint256 offset = start + ((span - 1) * sample) / (samples - 1);
                    bytes1 original = stream[offset];
                    stream[offset] = bytes1(uint8(original) ^ 1);
                    _assertInvalidProof(
                        verifier,
                        proof,
                        fixture.config,
                        _indexedLabel(
                            narg ? "whir.narg.recordByte" : "whir.hints.recordByte", record, eventIndex, offset
                        )
                    );
                    stream[offset] = original;
                }
            }
            ++record;
        }
        require(record == (narg ? 49 : 4), "WHIR consumed-record count drift");
        require(startRecord < endRecord && endRecord <= record, "WHIR mutation record range");
    }

    function _assertPinnedEncodedInvalid(
        PinnedMleVerifierV2 pinned,
        MleVerifierV2.MleProof memory proof,
        string memory label
    ) private view {
        require(gasleft() > 50_000_000, string.concat(label, ": test harness gas too low"));
        uint8 verdict = pinned.fraudVerdictEncoded(abi.encode(proof), bytes32(0));
        assertEq(uint256(verdict), 0, string.concat(label, ": expected INVALID, not STARVED/UNEVALUABLE"));
    }

    function _assertPinnedRawInvalid(PinnedMleVerifierV2 pinned, bytes memory rawProof, string memory label)
        private
        view
    {
        require(gasleft() > 50_000_000, string.concat(label, ": test harness gas too low"));
        uint8 verdict = pinned.fraudVerdictEncoded(rawProof, bytes32(0));
        assertEq(uint256(verdict), 0, string.concat(label, ": malformed ABI was not INVALID"));
    }

    function _assertRawDecodesNoncanonical(
        PinnedMleVerifierV2 pinned,
        bytes memory rawProof,
        bytes32 expectedCanonicalHash,
        string memory label
    ) private pure {
        (MleVerifierV2.MleProof memory decoded, bool canonical) = pinned.decodeCanonicalMleProof(rawProof);
        assertFalse(canonical, string.concat(label, ": layout unexpectedly canonical"));
        if (expectedCanonicalHash != bytes32(0)) {
            assertEq(
                keccak256(abi.encode(decoded)),
                expectedCanonicalHash,
                string.concat(label, ": noncanonical layout changed decoded value")
            );
        }
    }

    function _assertRawDecodeFails(
        PinnedMleVerifierV2 pinned,
        bytes memory rawProof,
        bool expectAllocationPanic,
        string memory label
    ) private view {
        require(gasleft() > 50_000_000, string.concat(label, ": test harness gas too low"));
        uint256 gasBefore = gasleft();
        (bool success, bytes memory reason) = address(pinned).staticcall{gas: 30_000_000}(
            abi.encodeCall(PinnedMleVerifierV2.decodeCanonicalMleProof, (rawProof))
        );
        assertFalse(success, string.concat(label, ": malformed layout unexpectedly decoded"));
        assertLt(gasBefore - gasleft(), 25_000_000, string.concat(label, ": decoder failure may be OOG"));
        if (expectAllocationPanic) {
            assertEq(
                reason,
                abi.encodeWithSelector(bytes4(0x4e487b71), uint256(0x41)),
                string.concat(label, ": expected Panic(0x41)")
            );
        } else {
            assertEq(reason.length, 0, string.concat(label, ": unexpected decoder reason"));
        }
    }

    function _assertPinnedCompactInvalid(PinnedMleVerifierV2 pinned, bytes memory compactProof, string memory label)
        private
        view
    {
        require(gasleft() > 50_000_000, string.concat(label, ": test harness gas too low"));
        (bool success, bytes memory reason) =
            address(pinned).staticcall(abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (compactProof)));
        assertFalse(success, string.concat(label, ": unexpectedly accepted"));
        assertEq(
            reason,
            abi.encodeWithSelector(InvalidMleProof.selector),
            string.concat(label, ": wrong rejection selector (including empty OOG)")
        );
        uint8 verdict = pinned.fraudVerdictCompact(compactProof, bytes32(0));
        assertEq(uint256(verdict), 0, string.concat(label, ": expected INVALID, not STARVED/UNEVALUABLE"));
    }

    function _resizeUint256(uint256[] memory source, uint256 length) private pure returns (uint256[] memory resized) {
        resized = new uint256[](length);
        uint256 copied = length < source.length ? length : source.length;
        for (uint256 i = 0; i < copied; ++i) {
            resized[i] = source[i];
        }
    }

    function _resizeExt3(GoldilocksExt3.Ext3[] memory source, uint256 length)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory resized)
    {
        resized = new GoldilocksExt3.Ext3[](length);
        uint256 copied = length < source.length ? length : source.length;
        for (uint256 i = 0; i < copied; ++i) {
            resized[i] = source[i];
        }
    }

    function _resizeRounds(OuterLogupExt3Verifier.CoefficientRound[] memory source, uint256 length)
        private
        pure
        returns (OuterLogupExt3Verifier.CoefficientRound[] memory resized)
    {
        resized = new OuterLogupExt3Verifier.CoefficientRound[](length);
        uint256 copied = length < source.length ? length : source.length;
        for (uint256 i = 0; i < copied; ++i) {
            resized[i] = source[i];
        }
    }

    function _resizeBytes(bytes memory source, uint256 length) private pure returns (bytes memory resized) {
        resized = new bytes(length);
        uint256 copied = length < source.length ? length : source.length;
        for (uint256 i = 0; i < copied; ++i) {
            resized[i] = source[i];
        }
    }

    function _insertZeroBytes(bytes memory source, uint256 offset, uint256 count)
        private
        pure
        returns (bytes memory expanded)
    {
        require(offset <= source.length, "raw insertion bounds");
        expanded = new bytes(source.length + count);
        for (uint256 i = 0; i < offset; ++i) {
            expanded[i] = source[i];
        }
        for (uint256 i = offset; i < source.length; ++i) {
            expanded[i + count] = source[i];
        }
    }

    function _shiftTopLevelDynamicPointers(bytes memory raw, uint256 delta) private pure {
        uint256[11] memory pointerWords =
            [uint256(0x60), 0x80, 0x100, 0x120, 0x140, 0x160, 0x180, 0x1a0, 0x1c0, 0x1e0, 0x200];
        for (uint256 i = 0; i < pointerWords.length; ++i) {
            _writeWord(raw, pointerWords[i], _readWord(raw, pointerWords[i]) + delta);
        }
    }

    function _readWord(bytes memory raw, uint256 offset) private pure returns (uint256 value) {
        require(offset + 32 <= raw.length, "raw read bounds");
        assembly ("memory-safe") {
            value := mload(add(add(raw, 0x20), offset))
        }
    }

    function _writeWord(bytes memory raw, uint256 offset, uint256 value) private pure {
        require(offset + 32 <= raw.length, "raw write bounds");
        assembly ("memory-safe") {
            mstore(add(add(raw, 0x20), offset), value)
        }
    }

    function _writeU64Le(bytes memory encoded, uint256 offset, uint256 value) private pure {
        require(offset + 8 <= encoded.length && value <= type(uint64).max, "u64 write bounds");
        for (uint256 i = 0; i < 8; ++i) {
            encoded[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
    }

    function _writeU32Le(bytes memory encoded, uint256 offset, uint256 value) private pure {
        require(offset + 4 <= encoded.length && value <= type(uint32).max, "u32 write bounds");
        for (uint256 i = 0; i < 4; ++i) {
            encoded[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
    }

    function _runEverySumcheckCoefficientMutation(bool logProof, uint256 startRound, uint256 requestedEndRound)
        private
    {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        MleVerifierV2.MleProof memory proof = _cloneProof(fixture.proof);
        uint256 roundCount = logProof ? proof.logProof.rounds.length : proof.gateProof.rounds.length;
        string memory family = logProof ? "log.sumcheck" : "gate.sumcheck";

        uint256 endRound = requestedEndRound < roundCount ? requestedEndRound : roundCount;
        require(startRound < endRound, "empty sumcheck mutation chunk");
        for (uint256 round = startRound; round < endRound; ++round) {
            uint256 coefficientCount = logProof
                ? proof.logProof.rounds[round].nonConstant.length
                : proof.gateProof.rounds[round].nonConstant.length;
            for (uint256 coefficient = 0; coefficient < coefficientCount; ++coefficient) {
                for (uint256 limb = 0; limb < 3; ++limb) {
                    GoldilocksExt3.Ext3 memory target = logProof
                        ? proof.logProof.rounds[round].nonConstant[coefficient]
                        : proof.gateProof.rounds[round].nonConstant[coefficient];
                    uint64 original = _ext3Limb(target, limb);
                    _setExt3Limb(target, limb, uint64(_bumpField(original)));
                    _assertInvalidProof(
                        verifier,
                        proof,
                        fixture.config,
                        _indexedLabel(string.concat(family, ".bump"), round, coefficient, limb)
                    );
                    _setExt3Limb(target, limb, uint64(BASE_FIELD_MODULUS_V2));
                    _assertInvalidProof(
                        verifier,
                        proof,
                        fixture.config,
                        _indexedLabel(string.concat(family, ".noncanonical"), round, coefficient, limb)
                    );
                    _setExt3Limb(target, limb, original);
                }
            }
        }
    }

    function _runTerminalVectorMutation(uint256 field, uint256 limb, uint256 start, uint256 requestedEnd) private {
        AtomicFixture memory fixture = _parseAtomicFixture(vm.readFile(FIXTURE));
        MleVerifierV2 verifier = _deployAtomicVerifier(fixture);
        MleVerifierV2.MleProof memory proof = _cloneProof(fixture.proof);
        GoldilocksExt3.Ext3[] memory values = _terminalVector(proof, field);
        uint256 end = requestedEnd < values.length ? requestedEnd : values.length;
        require(start < end, "empty terminal mutation chunk");
        string memory family = _terminalVectorName(field);

        for (uint256 element = start; element < end; ++element) {
            uint64 original = _ext3Limb(values[element], limb);
            _setExt3Limb(values[element], limb, uint64(_bumpField(original)));
            _assertInvalidProof(
                verifier, proof, fixture.config, _indexedLabel(string.concat(family, ".bump"), element, limb, 0)
            );
            _setExt3Limb(values[element], limb, original);
        }
    }

    function _terminalVector(MleVerifierV2.MleProof memory proof, uint256 field)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        if (field == 0) return proof.logPreprocessed;
        if (field == 1) return proof.logWitness;
        if (field == 2) return proof.logNormInverse;
        if (field == 3) return proof.gatePreprocessed;
        if (field == 4) return proof.gateWitness;
        revert("unknown terminal vector");
    }

    function _setTerminalVector(MleVerifierV2.MleProof memory proof, uint256 field, GoldilocksExt3.Ext3[] memory values)
        private
        pure
    {
        if (field == 0) proof.logPreprocessed = values;
        else if (field == 1) proof.logWitness = values;
        else if (field == 2) proof.logNormInverse = values;
        else if (field == 3) proof.gatePreprocessed = values;
        else if (field == 4) proof.gateWitness = values;
        else revert("unknown terminal vector");
    }

    function _terminalVectorName(uint256 field) private pure returns (string memory) {
        if (field == 0) return "terminal.logPreprocessed";
        if (field == 1) return "terminal.logWitness";
        if (field == 2) return "terminal.logNormInverse";
        if (field == 3) return "terminal.gatePreprocessed";
        if (field == 4) return "terminal.gateWitness";
        revert("unknown terminal vector");
    }

    function _ext3Limb(GoldilocksExt3.Ext3 memory value, uint256 limb) private pure returns (uint64) {
        if (limb == 0) return value.c0;
        if (limb == 1) return value.c1;
        if (limb == 2) return value.c2;
        revert("unknown Ext3 limb");
    }

    function _setExt3Limb(GoldilocksExt3.Ext3 memory value, uint256 limb, uint64 replacement) private pure {
        if (limb == 0) value.c0 = replacement;
        else if (limb == 1) value.c1 = replacement;
        else if (limb == 2) value.c2 = replacement;
        else revert("unknown Ext3 limb");
    }

    function _assertInvalidProof(
        MleVerifierV2 verifier,
        MleVerifierV2.MleProof memory proof,
        MleVerifierV2.VerificationConfig memory config,
        string memory label
    ) private view {
        (bool success, bytes memory reason) =
            address(verifier).staticcall(abi.encodeCall(MleVerifierV2.verify, (proof, config)));
        assertFalse(success, string.concat(label, ": unexpectedly accepted"));
        assertEq(
            reason,
            abi.encodeWithSelector(InvalidMleProof.selector),
            string.concat(label, ": wrong rejection selector (including empty OOG)")
        );
    }

    function _indexedLabel(string memory family, uint256 first, uint256 second, uint256 third)
        private
        pure
        returns (string memory)
    {
        return string.concat(family, "[", vm.toString(first), "][", vm.toString(second), "][", vm.toString(third), "]");
    }

    /// @dev Fixed high-value matrix:
    /// 0 version; 1..3 ordered roots; 4..8 all five constituent families;
    /// 9..10 both coupled round families; 11 PI; 12 digest; 13..14 WHIR streams.
    function _mutateProof(MleVerifierV2.MleProof memory proof, uint256 mutation) private pure {
        if (mutation == 0) {
            proof.protocolVersion = 2;
        } else if (mutation == 1) {
            proof.preprocessedRoot = bytes32(uint256(proof.preprocessedRoot) ^ 1);
        } else if (mutation == 2) {
            proof.witnessRoot = bytes32(uint256(proof.witnessRoot) ^ 1);
        } else if (mutation == 3) {
            proof.normInverseRoot = bytes32(uint256(proof.normInverseRoot) ^ 1);
        } else if (mutation == 4) {
            _bumpExt3(proof.logPreprocessed[0]);
        } else if (mutation == 5) {
            _bumpExt3(proof.logWitness[0]);
        } else if (mutation == 6) {
            _bumpExt3(proof.logNormInverse[0]);
        } else if (mutation == 7) {
            _bumpExt3(proof.gatePreprocessed[0]);
        } else if (mutation == 8) {
            _bumpExt3(proof.gateWitness[0]);
        } else if (mutation == 9) {
            _bumpExt3(proof.logProof.rounds[0].nonConstant[0]);
        } else if (mutation == 10) {
            _bumpExt3(proof.gateProof.rounds[0].nonConstant[0]);
        } else if (mutation == 11) {
            proof.publicInputs[0] = _bumpField(proof.publicInputs[0]);
        } else if (mutation == 12) {
            proof.circuitDigest[0] = _bumpField(proof.circuitDigest[0]);
        } else if (mutation == 13) {
            require(proof.whirTranscript.length != 0, "empty WHIR transcript");
            proof.whirTranscript[0] = bytes1(uint8(proof.whirTranscript[0]) ^ 1);
        } else if (mutation == 14) {
            require(proof.whirHints.length != 0, "empty WHIR hints");
            proof.whirHints[0] = bytes1(uint8(proof.whirHints[0]) ^ 1);
        } else {
            revert("unknown proof mutation");
        }
    }

    function _bumpExt3(GoldilocksExt3.Ext3 memory value) private pure {
        value.c0 = uint64(_bumpField(value.c0));
    }

    function _bumpField(uint256 value) private pure returns (uint256) {
        return value + 1 == BASE_FIELD_MODULUS_V2 ? 0 : value + 1;
    }

    function _publicInputsDigest(uint256[] memory publicInputs) private pure returns (bytes32 digest) {
        require(publicInputs.length == 8, "fixture PI limb count");
        uint256 value;
        for (uint256 i = 0; i < 8; ++i) {
            require(publicInputs[i] <= type(uint32).max, "fixture PI limb width");
            value |= publicInputs[i] << (224 - 32 * i);
        }
        digest = bytes32(value);
    }

    function _deployAtomicVerifier(AtomicFixture memory fixture) private returns (MleVerifierV2 verifier) {
        verifier = new MleVerifierV2(
            block.chainid,
            fixture.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            fixture.config
        );
    }

    function _verifyDirectWhir(
        string memory json,
        AtomicFixture memory fixture,
        GoldilocksExt3.Ext3[] memory evaluations,
        bytes memory mask
    ) private pure returns (bool) {
        SpongefishWhirVerify.WhirParams memory whir = fixture.config.whir;
        whir.evaluationPoint =
            _reversePoint(_ext3Array(json, string.concat(CASE, ".packedPoints[0].packedPoint"), whir.numVariables));
        whir.evaluationPoint2 =
            _reversePoint(_ext3Array(json, string.concat(CASE, ".packedPoints[1].packedPoint"), whir.numVariables));
        whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);

        bytes32[] memory roots = new bytes32[](NUM_PCS_GROUPS_V2);
        roots[0] = fixture.proof.preprocessedRoot;
        roots[1] = fixture.proof.witnessRoot;
        roots[2] = fixture.proof.normInverseRoot;
        return SpongefishWhirVerify.verifyWhirProofBound(
            abi.encodePacked(fixture.whirProtocolId[0], fixture.whirProtocolId[1]),
            abi.encodePacked(fixture.whirSessionId),
            "",
            fixture.proof.whirTranscript,
            fixture.proof.whirHints,
            evaluations,
            mask,
            roots,
            whir
        );
    }

    function _reversePoint(GoldilocksExt3.Ext3[] memory dense)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory whirPoint)
    {
        whirPoint = new GoldilocksExt3.Ext3[](dense.length);
        for (uint256 i = 0; i < dense.length; ++i) {
            whirPoint[i] = dense[dense.length - 1 - i];
        }
    }

    function _parseVerificationConfig(string memory json)
        private
        pure
        returns (MleVerifierV2.VerificationConfig memory config)
    {
        string memory vk = string.concat(CASE, ".verificationKey");
        config.circuit = CircuitConfigV2.Parameters({
            degreeBits: vm.parseJsonUint(json, string.concat(CASE, ".circuit.degreeBits")),
            numPublicInputs: vm.parseJsonUint(json, string.concat(CASE, ".circuit.numPublicInputs")),
            numConstants: vm.parseJsonUint(json, string.concat(vk, ".numConstants")),
            numRoutedWires: vm.parseJsonUint(json, string.concat(vk, ".numRoutedWires")),
            numWires: vm.parseJsonUint(json, string.concat(vk, ".numWires")),
            numSelectors: vm.parseJsonUint(json, string.concat(vk, ".numSelectors")),
            numGateConstraints: vm.parseJsonUint(json, string.concat(vk, ".numGateConstraints")),
            quotientDegreeFactor: vm.parseJsonUint(json, string.concat(vk, ".quotientDegreeFactor"))
        });
        config.kIs = _hexFieldArray(json, string.concat(vk, ".kIs"));
        config.subgroupGenPowers = _hexFieldArray(json, string.concat(vk, ".subgroupGenPowers"));
        config.publicInputWireMap = vm.parseJsonBytes(json, string.concat(vk, ".publicInputWireMap"));

        uint256 gateCount = _countNumericObjects(json, string.concat(vk, ".gates"), ".gateId", 256);
        config.gates = new Plonky2GateEvaluatorExt3.GateInfoV2[](gateCount);
        for (uint256 i = 0; i < gateCount; ++i) {
            string memory gate = string.concat(vk, ".gates[", vm.toString(i), "]");
            config.gates[i] = Plonky2GateEvaluatorExt3.GateInfoV2({
                gateId: uint8(vm.parseJsonUint(json, string.concat(gate, ".gateId"))),
                selectorIndex: uint8(vm.parseJsonUint(json, string.concat(gate, ".selectorIndex"))),
                groupStart: uint8(vm.parseJsonUint(json, string.concat(gate, ".groupStart"))),
                groupEnd: uint8(vm.parseJsonUint(json, string.concat(gate, ".groupEnd"))),
                gateRowIndex: uint8(vm.parseJsonUint(json, string.concat(gate, ".gateRowIndex"))),
                numConstraints: uint16(vm.parseJsonUint(json, string.concat(gate, ".numConstraints"))),
                numOrConsts: uint16(vm.parseJsonUint(json, string.concat(gate, ".numOrConsts"))),
                param2: uint16(vm.parseJsonUint(json, string.concat(gate, ".param2"))),
                param3: uint16(vm.parseJsonUint(json, string.concat(gate, ".param3")))
            });
        }
        config.whir = _parseWhirParams(json);
    }

    function _parseWhirParams(string memory json) private pure returns (SpongefishWhirVerify.WhirParams memory whir) {
        string memory base = string.concat(CASE, ".whirParams");
        whir.numVariables = vm.parseJsonUint(json, string.concat(base, ".numVariables"));
        whir.foldingFactor = vm.parseJsonUint(json, string.concat(base, ".foldingFactor"));
        whir.numVectors = vm.parseJsonUint(json, string.concat(base, ".numVectors"));
        whir.numCommitments = vm.parseJsonUint(json, string.concat(base, ".numCommitments"));
        whir.outDomainSamples = vm.parseJsonUint(json, string.concat(base, ".outDomainSamples"));
        whir.inDomainSamples = vm.parseJsonUint(json, string.concat(base, ".inDomainSamples"));
        whir.initialSumcheckRounds = vm.parseJsonUint(json, string.concat(base, ".initialSumcheckRounds"));
        whir.numRounds = vm.parseJsonUint(json, string.concat(base, ".numRounds"));
        whir.finalSumcheckRounds = vm.parseJsonUint(json, string.concat(base, ".finalSumcheckRounds"));
        whir.finalSize = vm.parseJsonUint(json, string.concat(base, ".finalSize"));
        whir.initialCodewordLength = vm.parseJsonUint(json, string.concat(base, ".initialCodewordLength"));
        whir.initialMerkleDepth = vm.parseJsonUint(json, string.concat(base, ".initialMerkleDepth"));
        whir.initialDomainGenerator = uint64(_jsonStringUint(json, string.concat(base, ".initialDomainGenerator")));
        whir.initialInterleavingDepth = vm.parseJsonUint(json, string.concat(base, ".initialInterleavingDepth"));
        whir.initialNumVariables = vm.parseJsonUint(json, string.concat(base, ".initialNumVariables"));
        whir.initialCosetSize = vm.parseJsonUint(json, string.concat(base, ".initialCosetSize"));
        whir.initialNumCosets = vm.parseJsonUint(json, string.concat(base, ".initialNumCosets"));
        whir.initialSumcheckPowThreshold =
            uint64(_jsonStringUint(json, string.concat(base, ".initialSumcheckPowThreshold")));
        whir.finalPowThreshold = uint64(_jsonStringUint(json, string.concat(base, ".finalPowThreshold")));
        whir.finalSumcheckPowThreshold =
            uint64(_jsonStringUint(json, string.concat(base, ".finalSumcheckPowThreshold")));
        whir.evaluationPoint = new GoldilocksExt3.Ext3[](0);
        whir.evaluationPoint2 = new GoldilocksExt3.Ext3[](0);
        whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        whir.rounds = new SpongefishWhirVerify.RoundParams[](whir.numRounds);
        for (uint256 i = 0; i < whir.numRounds; ++i) {
            whir.rounds[i] = _parseWhirRound(json, base, i);
        }
        require(
            _countNumericObjects(json, string.concat(base, ".rounds"), ".codewordLength", 14) == whir.numRounds,
            "fixture WHIR round tail"
        );
    }

    function _parseWhirRound(string memory json, string memory base, uint256 index)
        private
        pure
        returns (SpongefishWhirVerify.RoundParams memory roundParams)
    {
        string memory round = string.concat(base, ".rounds[", vm.toString(index), "]");
        roundParams.codewordLength = vm.parseJsonUint(json, string.concat(round, ".codewordLength"));
        roundParams.merkleDepth = vm.parseJsonUint(json, string.concat(round, ".merkleDepth"));
        roundParams.domainGenerator = uint64(_jsonStringUint(json, string.concat(round, ".domainGenerator")));
        roundParams.inDomainSamples = vm.parseJsonUint(json, string.concat(round, ".inDomainSamples"));
        roundParams.outDomainSamples = vm.parseJsonUint(json, string.concat(round, ".outDomainSamples"));
        roundParams.sumcheckRounds = vm.parseJsonUint(json, string.concat(round, ".sumcheckRounds"));
        roundParams.interleavingDepth = vm.parseJsonUint(json, string.concat(round, ".interleavingDepth"));
        roundParams.cosetSize = vm.parseJsonUint(json, string.concat(round, ".cosetSize"));
        roundParams.numCosets = vm.parseJsonUint(json, string.concat(round, ".numCosets"));
        roundParams.numVariables = vm.parseJsonUint(json, string.concat(round, ".numVariables"));
        roundParams.powThreshold = uint64(_jsonStringUint(json, string.concat(round, ".powThreshold")));
        roundParams.sumcheckPowThreshold = uint64(_jsonStringUint(json, string.concat(round, ".sumcheckPowThreshold")));
    }

    function _decodeCompactProof(bytes memory encoded, CircuitConfigV2.Parameters memory circuit)
        private
        pure
        returns (MleVerifierV2.MleProof memory proof)
    {
        CompactCursor memory cursor = CompactCursor({encoded: encoded, offset: 0});
        require(keccak256(_takeCompactBytes(cursor, 8)) == keccak256(abi.encodePacked(COMPACT_MAGIC_V2)), "magic");
        proof.protocolVersion = _readCompactU64(cursor, false);
        proof.constituentWidth = _readCompactU32(cursor);
        proof.circuitDigest = _readCompactBaseVector(cursor, 4);
        proof.publicInputs = _readCompactBaseVector(cursor, circuit.numPublicInputs);
        proof.preprocessedRoot = _readCompactBytes32(cursor);
        proof.witnessRoot = _readCompactBytes32(cursor);
        proof.normInverseRoot = _readCompactBytes32(cursor);
        proof.whirTranscript = _readCompactBlob(cursor);
        proof.whirHints = _readCompactBlob(cursor);

        proof.logProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.logProof.rounds[round].nonConstant = _readCompactExt3Vector(cursor, LOG_ROUND_DEGREE_V2);
        }
        uint256 preprocessedLength = circuit.numConstants + circuit.numRoutedWires;
        proof.logPreprocessed = _readCompactExt3Vector(cursor, preprocessedLength);
        proof.logWitness = _readCompactExt3Vector(cursor, circuit.numWires);
        proof.logNormInverse = _readCompactExt3Vector(cursor, 2 * circuit.numRoutedWires);

        proof.gateProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](circuit.degreeBits);
        uint256 gateDegree = circuit.quotientDegreeFactor + 2;
        for (uint256 round = 0; round < circuit.degreeBits; ++round) {
            proof.gateProof.rounds[round].nonConstant = _readCompactExt3Vector(cursor, gateDegree);
        }
        proof.gatePreprocessed = _readCompactExt3Vector(cursor, preprocessedLength);
        proof.gateWitness = _readCompactExt3Vector(cursor, circuit.numWires);
        require(cursor.offset == encoded.length, "compact trailing bytes");
    }

    function _readCompactBaseVector(CompactCursor memory cursor, uint256 length)
        private
        pure
        returns (uint256[] memory values)
    {
        values = new uint256[](length);
        for (uint256 i = 0; i < length; ++i) {
            values[i] = _readCompactU64(cursor, true);
        }
    }

    function _readCompactExt3Vector(CompactCursor memory cursor, uint256 length)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        values = new GoldilocksExt3.Ext3[](length);
        for (uint256 i = 0; i < length; ++i) {
            values[i] = GoldilocksExt3.Ext3(
                uint64(_readCompactU64(cursor, true)),
                uint64(_readCompactU64(cursor, true)),
                uint64(_readCompactU64(cursor, true))
            );
        }
    }

    function _readCompactBlob(CompactCursor memory cursor) private pure returns (bytes memory) {
        return _takeCompactBytes(cursor, _readCompactU32(cursor));
    }

    function _readCompactBytes32(CompactCursor memory cursor) private pure returns (bytes32 value) {
        require(cursor.offset + 32 <= cursor.encoded.length, "compact bytes32 bounds");
        bytes memory encoded = cursor.encoded;
        uint256 offset = cursor.offset;
        assembly ("memory-safe") {
            value := mload(add(add(encoded, 0x20), offset))
        }
        cursor.offset += 32;
    }

    function _readCompactU32(CompactCursor memory cursor) private pure returns (uint256 value) {
        value = _readU32Le(cursor.encoded, cursor.offset);
        cursor.offset += 4;
    }

    function _readCompactU64(CompactCursor memory cursor, bool canonical) private pure returns (uint256 value) {
        value = _readU64Le(cursor.encoded, cursor.offset);
        cursor.offset += 8;
        if (canonical) require(value < BASE_FIELD_MODULUS_V2, "compact non-canonical field");
    }

    function _takeCompactBytes(CompactCursor memory cursor, uint256 length) private pure returns (bytes memory value) {
        require(cursor.offset + length <= cursor.encoded.length, "compact byte bounds");
        value = new bytes(length);
        for (uint256 i = 0; i < length; ++i) {
            value[i] = cursor.encoded[cursor.offset + i];
        }
        cursor.offset += length;
    }

    function _countNumericObjects(string memory json, string memory arrayPath, string memory field, uint256 cap)
        private
        pure
        returns (uint256 count)
    {
        while (count < cap) {
            string memory path = string.concat(arrayPath, "[", vm.toString(count), "]", field);
            try vm.parseJsonUint(json, path) returns (uint256) {
                ++count;
            } catch {
                return count;
            }
        }
        revert("fixture object array exceeds cap");
    }

    function _jsonStringUint(string memory json, string memory path) private pure returns (uint256) {
        return vm.parseUint(vm.parseJsonString(json, path));
    }

    function _bytes32At(bytes memory value, uint256 offset) private pure returns (bytes32 word) {
        require(offset + 32 <= value.length, "bytes32 slice bounds");
        assembly ("memory-safe") {
            word := mload(add(add(value, 0x20), offset))
        }
    }

    function _replayEvent(string memory json, TranscriptV2.Transcript memory transcript, uint256 eventIndex)
        private
        pure
    {
        string memory base = _event(eventIndex);
        string memory kind = vm.parseJsonString(json, string.concat(base, ".kind"));
        if (eventIndex == 0) {
            assertEq(kind, "domain");
            assertEq(vm.parseJsonUint(json, string.concat(base, ".tag")), TAG_DOMAIN_V2);
            string memory domain = vm.parseJsonString(json, string.concat(base, ".domain"));
            assertEq(domain, OUTER_TRANSCRIPT_PROTOCOL_V2);
            assertEq(vm.parseJsonBytes(json, string.concat(base, ".payload")), bytes(domain));
        } else if (_same(kind, "domain")) {
            assertEq(vm.parseJsonUint(json, string.concat(base, ".tag")), TAG_DOMAIN_V2);
            string memory domain = vm.parseJsonString(json, string.concat(base, ".domain"));
            assertEq(vm.parseJsonBytes(json, string.concat(base, ".payload")), bytes(domain));
            TranscriptV2.domainSeparate(transcript, domain);
        } else if (_same(kind, "absorbBytes")) {
            assertEq(vm.parseJsonUint(json, string.concat(base, ".tag")), TAG_BYTES_V2);
            TranscriptV2.absorbBytes(transcript, vm.parseJsonBytes(json, string.concat(base, ".payload")));
        } else if (_same(kind, "absorbFieldVec")) {
            assertEq(vm.parseJsonUint(json, string.concat(base, ".tag")), TAG_FIELD_VEC_V2);
            TranscriptV2.absorbFieldVec(
                transcript, _parseFieldVecPayload(vm.parseJsonBytes(json, string.concat(base, ".payload")))
            );
        } else if (_same(kind, "absorbExt3Vec")) {
            assertEq(vm.parseJsonUint(json, string.concat(base, ".tag")), TAG_EXT3_VEC_V2);
            TranscriptV2.absorbExt3Vec(
                transcript, _parseExt3VecPayload(vm.parseJsonBytes(json, string.concat(base, ".payload")))
            );
        } else if (_same(kind, "squeezeExt3")) {
            assertEq(
                transcript.squeezeCounter,
                vm.parseJsonUint(json, string.concat(base, ".squeezeCounterBefore")),
                "pre-squeeze counter"
            );
            GoldilocksExt3.Ext3 memory actual = TranscriptV2.squeezeExt3(transcript);
            _assertExt3Eq(actual, _ext3(json, string.concat(base, ".challenge")), "Ext3 challenge");
        } else {
            assertEq(kind, "checkpoint", "unknown transcript event kind");
        }

        assertEq(transcript.state, vm.parseJsonBytes32(json, string.concat(base, ".state")), "transcript state");
        assertEq(
            transcript.squeezeCounter,
            vm.parseJsonUint(json, string.concat(base, ".squeezeCounter")),
            "post-event squeeze counter"
        );
    }

    function _assertProtocolEventOrder(string memory json) private pure {
        _assertDomainEvent(json, 0, "protocol", OUTER_TRANSCRIPT_PROTOCOL_V2);
        _assertDomainEvent(json, 1, "statement", DOMAIN_CIRCUIT_STATEMENT_V2);
        _assertEvent(json, 2, "absorbFieldVec", "statement.circuitDigest");
        _assertEvent(json, 3, "absorbFieldVec", "statement.publicInputs");
        _assertDomainEvent(json, 4, "schema", PACKED_PCS_SCHEMA_DOMAIN_V2);
        _assertEvent(json, 5, "absorbBytes", "schema.metadata");
        _assertDomainEvent(json, 6, "circuitConfigDigest", DOMAIN_CIRCUIT_CONFIG_DIGEST_V2);
        _assertEvent(json, 7, "absorbBytes", "circuitConfigDigest.value");
        _assertDomainEvent(json, 8, "whirProtocolId", DOMAIN_WHIR_PROTOCOL_ID_V2);
        _assertEvent(json, 9, "absorbBytes", "whirProtocolId.value");
        _assertDomainEvent(json, 10, "whirSessionId", DOMAIN_WHIR_SESSION_ID_V2);
        _assertEvent(json, 11, "absorbBytes", "whirSessionId.value");
        _assertDomainEvent(json, 12, "preprocessedRoot", DOMAIN_GROUP_PREPROCESSED_V2);
        _assertEvent(json, 13, "absorbBytes", "preprocessedRoot.value");
        _assertDomainEvent(json, 14, "witnessRoot", DOMAIN_GROUP_WITNESS_V2);
        _assertEvent(json, 15, "absorbBytes", "witnessRoot.value");
        _assertDomainEvent(json, 16, "publicInputAggregationChallenge", DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
        _assertEvent(json, 17, "squeezeExt3", "etaPi");
        _assertDomainEvent(json, 18, "normDenominatorChallenges", DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2);
        _assertEvent(json, 19, "squeezeExt3", "beta");
        _assertEvent(json, 20, "squeezeExt3", "gamma");
        _assertDomainEvent(json, 21, "normInverseRoot", DOMAIN_GROUP_NORM_INVERSE_V2);
        _assertEvent(json, 22, "absorbBytes", "normInverseRoot.value");
        _assertDomainEvent(json, 23, "publicInputMixChallenge", DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2);
        _assertEvent(json, 24, "squeezeExt3", "xiPi");
        _assertDomainEvent(json, 25, "outerRelationChallenges", DOMAIN_OUTER_RELATION_CHALLENGES_V2);
        _assertEvent(json, 26, "squeezeExt3", "lambda");
        _assertEvent(json, 27, "squeezeExt3", "rho");
        _assertEvent(json, 28, "squeezeExt3", "kappa");
        _assertEvent(json, 29, "squeezeExt3", "tauLog[0]");
        _assertEvent(json, 30, "squeezeExt3", "tauLog[1]");
        _assertEvent(json, 31, "squeezeExt3", "gateAlpha");
        _assertEvent(json, 32, "squeezeExt3", "gateTau[0]");
        _assertEvent(json, 33, "squeezeExt3", "gateTau[1]");

        for (uint256 round = 0; round < 2; ++round) {
            uint256 base = 34 + 9 * round;
            string memory index = vm.toString(round);
            _assertEvent(json, base, "checkpoint", string.concat("round[", index, "].before"));
            _assertDomainEvent(
                json, base + 1, string.concat("round[", index, "].messages"), DOMAIN_OUTER_SUMCHECK_ROUND_V2
            );
            _assertEvent(json, base + 2, "absorbBytes", string.concat("round[", index, "].index"));
            _assertEvent(json, base + 3, "absorbExt3Vec", string.concat("round[", index, "].logNonConstant"));
            _assertEvent(json, base + 4, "absorbExt3Vec", string.concat("round[", index, "].gateNonConstant"));
            _assertDomainEvent(
                json, base + 5, string.concat("round[", index, "].challenges"), DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2
            );
            _assertEvent(json, base + 6, "squeezeExt3", string.concat("round[", index, "].log"));
            _assertEvent(json, base + 7, "squeezeExt3", string.concat("round[", index, "].gate"));
            _assertEvent(json, base + 8, "checkpoint", string.concat("round[", index, "].after"));
        }

        _assertDomainEvent(json, 52, "constituentClaims", DOMAIN_CONSTITUENT_CLAIMS_V2);
        _assertEvent(json, 53, "absorbExt3Vec", "claim[0].log.preprocessed");
        _assertEvent(json, 54, "absorbExt3Vec", "claim[1].log.witness");
        _assertEvent(json, 55, "absorbExt3Vec", "claim[2].log.normInverse");
        _assertEvent(json, 56, "absorbExt3Vec", "claim[3].gate.preprocessed");
        _assertEvent(json, 57, "absorbExt3Vec", "claim[4].gate.witness");
        _assertEvent(json, 58, "absorbExt3Vec", "claim[5].gate.normInverse.unused");
        _assertEvent(json, 59, "checkpoint", "constituentClaims.after");
        _assertDomainEvent(json, 60, "constituentIndices", DOMAIN_CONSTITUENT_INDEX_V2);
        for (uint256 point = 0; point < 2; ++point) {
            for (uint256 bit = 0; bit < 8; ++bit) {
                _assertEvent(
                    json,
                    61 + 8 * point + bit,
                    "squeezeExt3",
                    string.concat("index[", vm.toString(point), "][", vm.toString(bit), "]")
                );
            }
        }
        _assertEvent(json, 77, "checkpoint", "final");
    }

    function _assertPackedPoint(string memory json, uint256 point) private pure {
        string memory base = string.concat(CASE, ".packedPoints[", vm.toString(point), "]");
        assertEq(vm.parseJsonString(json, string.concat(base, ".name")), point == POINT_LOG_V2 ? "log" : "gate");
        GoldilocksExt3.Ext3[] memory row = _ext3Array(json, string.concat(base, ".rowPoint"), 2);
        GoldilocksExt3.Ext3[] memory index = _ext3Array(json, string.concat(base, ".constituentIndexPoint"), 8);
        GoldilocksExt3.Ext3[] memory packed = _ext3Array(json, string.concat(base, ".packedPoint"), 10);
        assertEq(row.length, 2);
        assertEq(index.length, 8);
        assertEq(packed.length, 10);
        for (uint256 round = 0; round < 2; ++round) {
            uint256 challengeEvent = 40 + 9 * round + point;
            _assertExt3Eq(row[round], _ext3(json, _eventField(challengeEvent, "challenge")), "row point order");
            _assertExt3Eq(packed[round], row[round], "packed row prefix");
        }
        for (uint256 bit = 0; bit < 8; ++bit) {
            _assertExt3Eq(index[bit], _ext3(json, _eventField(61 + 8 * point + bit, "challenge")), "index point order");
            _assertExt3Eq(packed[2 + bit], index[bit], "packed index suffix");
        }
    }

    function _assertEvent(string memory json, uint256 index, string memory kind, string memory label) private pure {
        assertEq(vm.parseJsonString(json, _eventField(index, "kind")), kind, "event kind/order");
        assertEq(vm.parseJsonString(json, _eventField(index, "label")), label, "event label/order");
    }

    function _assertDomainEvent(string memory json, uint256 index, string memory label, string memory domain)
        private
        pure
    {
        _assertEvent(json, index, "domain", label);
        assertEq(vm.parseJsonString(json, _eventField(index, "domain")), domain, "domain/order");
    }

    function _assertEventPayloadEqualsJson(string memory json, uint256 eventIndex, string memory valuePath)
        private
        pure
    {
        assertEq(vm.parseJsonBytes(json, _eventField(eventIndex, "payload")), vm.parseJsonBytes(json, valuePath));
    }

    function _parseFieldVecPayload(bytes memory payload) private pure returns (uint256[] memory values) {
        uint256 count = _readU64Le(payload, 0);
        assertEq(payload.length, 8 + 8 * count, "field-vector payload length");
        values = new uint256[](count);
        for (uint256 i = 0; i < count; ++i) {
            values[i] = _readCanonicalU64Le(payload, 8 + 8 * i);
        }
    }

    function _parseExt3VecPayload(bytes memory payload) private pure returns (GoldilocksExt3.Ext3[] memory values) {
        uint256 count = _readU64Le(payload, 0);
        assertEq(payload.length, 8 + 24 * count, "Ext3-vector payload length");
        values = new GoldilocksExt3.Ext3[](count);
        for (uint256 i = 0; i < count; ++i) {
            uint256 offset = 8 + 24 * i;
            values[i] = GoldilocksExt3.Ext3(
                uint64(_readCanonicalU64Le(payload, offset)),
                uint64(_readCanonicalU64Le(payload, offset + 8)),
                uint64(_readCanonicalU64Le(payload, offset + 16))
            );
        }
    }

    function _ext3Array(string memory json, string memory path, uint256 expectedLength)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        values = new GoldilocksExt3.Ext3[](expectedLength);
        for (uint256 i = 0; i < expectedLength; ++i) {
            values[i] = _ext3(json, string.concat(path, "[", vm.toString(i), "]"));
        }
        _assertNoStringPath(
            json, string.concat(path, "[", vm.toString(expectedLength), "][0]"), "unexpected Ext3 array tail"
        );
    }

    function _ext3(string memory json, string memory path) private pure returns (GoldilocksExt3.Ext3 memory value) {
        string[] memory encoded = vm.parseJsonStringArray(json, path);
        assertEq(encoded.length, 3, "Ext3 JSON limb count");
        value = GoldilocksExt3.Ext3(
            uint64(_canonicalHex(encoded[0])), uint64(_canonicalHex(encoded[1])), uint64(_canonicalHex(encoded[2]))
        );
    }

    function _consumeExt3Payload(bytes memory compact, uint256 cursor, bytes memory payload, uint256 expectedCount)
        private
        pure
        returns (uint256)
    {
        assertEq(_readU64Le(payload, 0), expectedCount, "compact-bound Ext3 vector count");
        assertEq(payload.length, 8 + 24 * expectedCount, "compact-bound Ext3 payload length");
        _assertRangeEqual(compact, cursor, payload, 8, 24 * expectedCount, "compact/transcript Ext3 bytes");
        for (uint256 i = 0; i < 3 * expectedCount; ++i) {
            _readCanonicalU64Le(compact, cursor + 8 * i);
        }
        return cursor + 24 * expectedCount;
    }

    function _assertRangeEqual(
        bytes memory left,
        uint256 leftOffset,
        bytes memory right,
        uint256 rightOffset,
        uint256 length,
        string memory message
    ) private pure {
        assertLe(leftOffset + length, left.length, "left byte range");
        assertLe(rightOffset + length, right.length, "right byte range");
        for (uint256 i = 0; i < length; ++i) {
            require(left[leftOffset + i] == right[rightOffset + i], message);
        }
    }

    function _readCanonicalU64Le(bytes memory encoded, uint256 offset) private pure returns (uint256 value) {
        value = _readU64Le(encoded, offset);
        assertLt(value, BASE_FIELD_MODULUS_V2, "non-canonical Goldilocks limb");
    }

    function _readU32Le(bytes memory encoded, uint256 offset) private pure returns (uint256 value) {
        assertLe(offset + 4, encoded.length, "u32 read bounds");
        for (uint256 i = 0; i < 4; ++i) {
            value |= uint256(uint8(encoded[offset + i])) << (8 * i);
        }
    }

    function _readU64Le(bytes memory encoded, uint256 offset) private pure returns (uint256 value) {
        assertLe(offset + 8, encoded.length, "u64 read bounds");
        for (uint256 i = 0; i < 8; ++i) {
            value |= uint256(uint8(encoded[offset + i])) << (8 * i);
        }
    }

    function _hexField(string memory json, string memory path) private pure returns (uint256) {
        return _canonicalHex(vm.parseJsonString(json, path));
    }

    function _hexFieldArray(string memory json, string memory path) private pure returns (uint256[] memory values) {
        string[] memory encoded = vm.parseJsonStringArray(json, path);
        values = new uint256[](encoded.length);
        for (uint256 i = 0; i < encoded.length; ++i) {
            values[i] = _canonicalHex(encoded[i]);
        }
    }

    function _canonicalHex(string memory encoded) private pure returns (uint256 value) {
        value = vm.parseUint(encoded);
        assertLt(value, BASE_FIELD_MODULUS_V2, "non-canonical fixture field");
    }

    function _assertExt3Eq(
        GoldilocksExt3.Ext3 memory actual,
        GoldilocksExt3.Ext3 memory expected,
        string memory message
    ) private pure {
        assertEq(actual.c0, expected.c0, message);
        assertEq(actual.c1, expected.c1, message);
        assertEq(actual.c2, expected.c2, message);
    }

    function _assertNoStringPath(string memory json, string memory path, string memory message) private pure {
        try vm.parseJsonString(json, path) returns (string memory) {
            require(false, message);
        } catch {}
    }

    function _event(uint256 eventIndex) private pure returns (string memory) {
        return string.concat(CASE, ".outerTranscript[", vm.toString(eventIndex), "]");
    }

    function _eventField(uint256 eventIndex, string memory field) private pure returns (string memory) {
        return string.concat(_event(eventIndex), ".", field);
    }

    function _same(string memory left, string memory right) private pure returns (bool) {
        return keccak256(bytes(left)) == keccak256(bytes(right));
    }
}
