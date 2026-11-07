// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {OuterLogupExt3Verifier} from "../src/OuterLogupExt3Verifier.sol";
import {TranscriptV2} from "../src/TranscriptV2.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {
    DOMAIN_CIRCUIT_CONFIG_DIGEST_V2,
    DOMAIN_CIRCUIT_STATEMENT_V2,
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
    PACKED_PCS_SCHEMA_DOMAIN_V2,
    PACKED_VARIABLE_ORDER_CODE_V2
} from "../src/generated/MleWhirV2.sol";

/// @notice `verifyPrevalidatedFlat` must be an exact drop-in for `verifyPrevalidated` (and `verify`):
/// same points, same gate claim, same transcript, on the real max-resource and production-shape
/// proofs, with the transcript and challenges derived exactly as `MleVerifierV2` derives them.
contract OuterLogupExt3VerifierFlatTest is Test {
    string private constant MAX_FIXTURE = "test/fixtures/v2_max_resource.json";
    string private constant PRODUCTION_FIXTURE = "test/fixtures/v2_production_shape.json";

    struct Fixture {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    /// @dev Everything the outer verifier consumes, in both layouts.
    struct OuterInputs {
        OuterLogupExt3Verifier.VerificationKey vk;
        OuterLogupExt3Verifier.Challenges challenges;
        OuterLogupExt3Verifier.TerminalEvaluations terminal;
        TranscriptV2.Transcript transcript;
        uint256[] logRounds;
        uint256[] gateRounds;
        uint256[] preprocessed;
        uint256[] witness;
        uint256[] normInverse;
    }

    struct Outcome {
        GoldilocksExt3.Ext3[] logPoint;
        GoldilocksExt3.Ext3[] gatePoint;
        GoldilocksExt3.Ext3 gateFinalClaim;
        TranscriptV2.Transcript transcript;
        uint256 gas;
    }

    function test_flatMatchesLegacyEntries_max() external {
        _assertFlatMatchesLegacy("max", _load(vm.readFile(MAX_FIXTURE)));
    }

    function test_flatMatchesLegacyEntries_production() external {
        _assertFlatMatchesLegacy("production", _load(vm.readFile(PRODUCTION_FIXTURE)));
    }

    function test_flatRejectsPerturbedWitnessLimb_max() external {
        _assertPerturbedWitnessRejected(_load(vm.readFile(MAX_FIXTURE)));
    }

    function test_flatRejectsPerturbedWitnessLimb_production() external {
        _assertPerturbedWitnessRejected(_load(vm.readFile(PRODUCTION_FIXTURE)));
    }

    function test_blobMatchesFlat_max() external {
        _assertBlobMatchesFlat("max", _load(vm.readFile(MAX_FIXTURE)));
    }

    function test_blobMatchesFlat_production() external {
        _assertBlobMatchesFlat("production", _load(vm.readFile(PRODUCTION_FIXTURE)));
    }

    function test_blobRejectsTrailingBytesAndShortArrays_max() external {
        OuterInputs memory inputs = _prepare(_load(vm.readFile(MAX_FIXTURE)));
        bytes memory blob = _pack(inputs);
        this.callBlob(blob, inputs);
        // one trailing byte
        vm.expectRevert(InvalidMleProof.selector);
        this.callBlob(bytes.concat(blob, hex"00"), inputs);
        // a seventh (empty) array
        vm.expectRevert(InvalidMleProof.selector);
        this.callBlob(bytes.concat(blob, new bytes(32)), inputs);
        // last word missing: the sixth array announces more words than remain
        bytes memory truncated = new bytes(blob.length - 32);
        for (uint256 i = 0; i < truncated.length; ++i) {
            truncated[i] = blob[i];
        }
        vm.expectRevert(InvalidMleProof.selector);
        this.callBlob(truncated, inputs);
        // a length word pointing past the end (first array claims the whole blob)
        bytes memory inflated = bytes.concat(abi.encodePacked(uint256(blob.length)), blob);
        vm.expectRevert(InvalidMleProof.selector);
        this.callBlob(inflated, inputs);
        // too short to hold even one length word
        vm.expectRevert(InvalidMleProof.selector);
        this.callBlob(hex"0102", inputs);
        // a length that would overflow the bound arithmetic in a naive multiplication
        bytes memory huge = bytes.concat(abi.encodePacked(type(uint256).max), blob);
        vm.expectRevert(InvalidMleProof.selector);
        this.callBlob(huge, inputs);
    }

    function _assertBlobMatchesFlat(string memory label, Fixture memory fixture) private {
        OuterInputs memory inputs = _prepare(fixture);
        Outcome memory flat = _runFlat(inputs);
        bytes memory blob = _pack(inputs);
        TranscriptV2.Transcript memory transcript = _copyTranscript(inputs.transcript);
        Outcome memory packed;
        uint256 before = gasleft();
        (packed.logPoint, packed.gatePoint, packed.gateFinalClaim, packed.transcript) =
            OuterLogupExt3Verifier.verifyPrevalidatedBlob(blob, inputs.vk, inputs.challenges, transcript);
        packed.gas = before - gasleft();
        _assertSameOutcome(flat, packed, "flat vs blob");
        emit log_named_uint(string.concat("gas/", label, "/verifyPrevalidatedBlob"), packed.gas);
        emit log_named_uint(string.concat("gas/", label, "/verifyPrevalidatedFlat"), flat.gas);
    }

    /// @dev Six length-prefixed word arrays in the documented order: the memory image of each `uint256[]`.
    function _pack(OuterInputs memory inputs) private pure returns (bytes memory) {
        return bytes.concat(
            abi.encodePacked(inputs.terminal.publicInputs.length, inputs.terminal.publicInputs),
            abi.encodePacked(inputs.logRounds.length, inputs.logRounds),
            abi.encodePacked(inputs.gateRounds.length, inputs.gateRounds),
            abi.encodePacked(inputs.preprocessed.length, inputs.preprocessed),
            abi.encodePacked(inputs.witness.length, inputs.witness),
            abi.encodePacked(inputs.normInverse.length, inputs.normInverse)
        );
    }

    /// @dev External so `vm.expectRevert` observes the library revert.
    function callBlob(bytes calldata blob, OuterInputs memory inputs) external view {
        OuterLogupExt3Verifier.verifyPrevalidatedBlob(blob, inputs.vk, inputs.challenges, _copyTranscript(inputs.transcript));
    }

    /// @dev The direct-PI binding is evaluated by run-grouped Horner with memoised rows and a lazily
    /// built eta-power table; this pins it to the plain definition
    /// sum_i eta^i eq(row_i, point) (W_col_i - PI_i) over run shapes of every length class
    /// (1, 2, 7, 8, 9, 10, mixed rows, production-like row sequences).
    function test_publicInputBindingMatchesPlainDefinition() external pure {
        uint256[48] memory productionRows = [
            uint256(4799), 4804, 4805, 4800, 4808, 4808, 4808, 4808, 4811, 4811, 4806, 4806, 4807, 4807, 4813, 4813,
            4813, 4813, 4808, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4808, 4799, 4804, 4805, 4813,
            4808, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4810, 4808, 4812, 4819
        ];
        uint256[8] memory runLengths = [uint256(1), 2, 7, 8, 9, 10, 17, 24];
        for (uint256 k = 0; k < runLengths.length; ++k) {
            uint256[] memory rows = new uint256[](runLengths[k]);
            for (uint256 i = 0; i < rows.length; ++i) {
                rows[i] = 4810;
            }
            _assertBindingMatchesDefinition(rows, string.concat("run of ", vm.toString(runLengths[k])));
        }
        for (uint256 n = 44; n <= 48; ++n) {
            uint256[] memory rows = new uint256[](n);
            for (uint256 i = 0; i < n; ++i) {
                rows[i] = productionRows[i];
            }
            _assertBindingMatchesDefinition(rows, string.concat("production rows prefix ", vm.toString(n)));
        }
    }

    function _assertBindingMatchesDefinition(uint256[] memory rows, string memory label) private pure {
        OuterLogupExt3Verifier.VerificationKey memory vk = _smallVk(rows);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _smallTerminal(rows.length);
        OuterLogupExt3Verifier.Challenges memory challenges = _smallChallenges();
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](13);
        for (uint64 i = 0; i < 13; ++i) {
            point[i] = GoldilocksExt3.Ext3(101 + i, 151 + i, 211 + i);
        }
        GoldilocksExt3.Ext3 memory withInputs =
            OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        // the same statement without public inputs isolates xi * binding
        vk.publicInputWireMap = new bytes(0);
        terminal.publicInputs = new uint256[](0);
        GoldilocksExt3.Ext3 memory without = OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        vk = _smallVk(rows);
        terminal = _smallTerminal(rows.length);
        GoldilocksExt3.Ext3 memory expected = GoldilocksExt3.add(
            without, GoldilocksExt3.mul(challenges.xi, _plainBinding(vk, terminal, point, challenges.eta))
        );
        assertTrue(GoldilocksExt3.eq(withInputs, expected), label);
    }

    /// @dev sum_i eta^i eq(row_i, point) (W_col_i - PI_i) with the plain Ext3 library, no grouping.
    function _plainBinding(
        OuterLogupExt3Verifier.VerificationKey memory vk,
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3 memory eta
    ) private pure returns (GoldilocksExt3.Ext3 memory binding) {
        GoldilocksExt3.Ext3 memory power = GoldilocksExt3.one();
        for (uint256 i = 0; i < terminal.publicInputs.length; ++i) {
            uint256 row =
                uint8(vk.publicInputWireMap[3 * i]) | (uint256(uint8(vk.publicInputWireMap[3 * i + 1])) << 8);
            uint256 column = uint8(vk.publicInputWireMap[3 * i + 2]);
            GoldilocksExt3.Ext3 memory eq = GoldilocksExt3.one();
            for (uint256 v = 0; v < point.length; ++v) {
                eq = GoldilocksExt3.mul(
                    eq, ((row >> v) & 1) == 1 ? point[v] : GoldilocksExt3.sub(GoldilocksExt3.one(), point[v])
                );
            }
            GoldilocksExt3.Ext3 memory difference = GoldilocksExt3.sub(
                terminal.witness[column], GoldilocksExt3.Ext3(uint64(terminal.publicInputs[i]), 0, 0)
            );
            binding = GoldilocksExt3.add(binding, GoldilocksExt3.mul(power, GoldilocksExt3.mul(eq, difference)));
            power = GoldilocksExt3.mul(power, eta);
        }
    }

    function _smallVk(uint256[] memory rows) private pure returns (OuterLogupExt3Verifier.VerificationKey memory vk) {
        vk.numVars = 13;
        vk.gateDegree = 2;
        vk.numRoutedWires = 8;
        vk.numWires = 8;
        vk.numConstants = 1;
        vk.kIs = new uint256[](8);
        vk.subgroupGenPowers = new uint256[](13);
        for (uint256 i = 0; i < 8; ++i) {
            vk.kIs[i] = i + 3;
        }
        for (uint256 i = 0; i < 13; ++i) {
            vk.subgroupGenPowers[i] = 7 + i;
        }
        vk.publicInputWireMap = new bytes(3 * rows.length);
        for (uint256 i = 0; i < rows.length; ++i) {
            vk.publicInputWireMap[3 * i] = bytes1(uint8(rows[i]));
            vk.publicInputWireMap[3 * i + 1] = bytes1(uint8(rows[i] >> 8));
            vk.publicInputWireMap[3 * i + 2] = bytes1(uint8((i * 5) % 8));
        }
    }

    function _smallTerminal(uint256 count)
        private
        pure
        returns (OuterLogupExt3Verifier.TerminalEvaluations memory terminal)
    {
        terminal.preprocessed = new GoldilocksExt3.Ext3[](9);
        terminal.witness = new GoldilocksExt3.Ext3[](8);
        terminal.normInverse = new GoldilocksExt3.Ext3[](16);
        for (uint64 i = 0; i < 8; ++i) {
            terminal.witness[i] = GoldilocksExt3.Ext3(73 + i, 89 + i, 101 + i);
        }
        terminal.publicInputs = new uint256[](count);
        for (uint256 i = 0; i < count; ++i) {
            terminal.publicInputs[i] = 3 * i + 1;
        }
    }

    function _smallChallenges() private pure returns (OuterLogupExt3Verifier.Challenges memory challenges) {
        challenges.beta = GoldilocksExt3.Ext3(1, 0, 0);
        challenges.lambda = GoldilocksExt3.Ext3(5, 7, 11);
        challenges.rho = GoldilocksExt3.Ext3(13, 17, 19);
        challenges.kappa = GoldilocksExt3.Ext3(23, 29, 31);
        challenges.eta = GoldilocksExt3.Ext3(13, 17, 19);
        challenges.xi = GoldilocksExt3.Ext3(23, 29, 31);
        challenges.tau = new GoldilocksExt3.Ext3[](13);
        for (uint256 i = 0; i < 13; ++i) {
            challenges.tau[i] = GoldilocksExt3.Ext3(uint64(37 + i), uint64(41 + i), uint64(43 + i));
        }
    }

    function test_flatRejectsShapeMismatch_max() external {
        OuterInputs memory inputs = _prepare(_load(vm.readFile(MAX_FIXTURE)));
        // one limb short in every flat vector family must fail closed rather than read past the buffer
        _assertShortVectorRejected(inputs, 0);
        _assertShortVectorRejected(inputs, 1);
        _assertShortVectorRejected(inputs, 2);
        _assertShortVectorRejected(inputs, 3);
        _assertShortVectorRejected(inputs, 4);
    }

    // ---------------------------------------------------------------- assertions

    function _assertFlatMatchesLegacy(string memory label, Fixture memory fixture) private {
        OuterInputs memory inputs = _prepare(fixture);

        Outcome memory validated = _runVerify(inputs);
        Outcome memory legacy = _runPrevalidated(inputs);
        Outcome memory flat = _runFlat(inputs);

        _assertSameOutcome(legacy, flat, "prevalidated vs flat");
        _assertSameOutcome(validated, flat, "verify vs flat");
        assertEq(flat.logPoint.length, fixture.config.circuit.degreeBits, "log point length");
        assertEq(flat.gatePoint.length, fixture.config.circuit.degreeBits, "gate point length");
        // every coupled round squeezes two Ext3 challenges and the counter restarts after each absorb
        assertEq(flat.transcript.squeezeCounter, 6, "squeeze counter after the last coupled round");

        emit log_named_uint(string.concat("gas/", label, "/verify"), validated.gas);
        emit log_named_uint(string.concat("gas/", label, "/verifyPrevalidated"), legacy.gas);
        emit log_named_uint(string.concat("gas/", label, "/verifyPrevalidatedFlat"), flat.gas);
    }

    function _assertPerturbedWitnessRejected(Fixture memory fixture) private {
        OuterInputs memory inputs = _prepare(fixture);
        // a routed wire's c1 limb; the honest proof must still pass just before
        _runFlat(inputs);
        uint256 index = 3 * (inputs.vk.numRoutedWires / 2) + 1;
        inputs.witness[index] = addmod(inputs.witness[index], 1, OuterLogupExt3Verifier.P);
        vm.expectRevert(InvalidMleProof.selector);
        this.callFlat(inputs);
        // a public-input column limb (c0) seen only through the direct-PI binding
        inputs = _prepare(fixture);
        uint256 column = uint8(inputs.vk.publicInputWireMap[2]);
        inputs.witness[3 * column] = addmod(inputs.witness[3 * column], 1, OuterLogupExt3Verifier.P);
        vm.expectRevert(InvalidMleProof.selector);
        this.callFlat(inputs);
    }

    function _assertShortVectorRejected(OuterInputs memory inputs, uint256 family) private {
        OuterInputs memory broken = inputs;
        if (family == 0) broken.logRounds = _dropLast(inputs.logRounds);
        else if (family == 1) broken.gateRounds = _dropLast(inputs.gateRounds);
        else if (family == 2) broken.preprocessed = _dropLast(inputs.preprocessed);
        else if (family == 3) broken.witness = _dropLast(inputs.witness);
        else broken.normInverse = _dropLast(inputs.normInverse);
        vm.expectRevert(InvalidMleProof.selector);
        this.callFlat(broken);
    }

    function _assertSameOutcome(Outcome memory expected, Outcome memory actual, string memory label) private pure {
        assertEq(actual.logPoint.length, expected.logPoint.length, string.concat(label, ": logPoint length"));
        assertEq(actual.gatePoint.length, expected.gatePoint.length, string.concat(label, ": gatePoint length"));
        for (uint256 i = 0; i < expected.logPoint.length; ++i) {
            _assertSameExt3(expected.logPoint[i], actual.logPoint[i], string.concat(label, ": logPoint"));
            _assertSameExt3(expected.gatePoint[i], actual.gatePoint[i], string.concat(label, ": gatePoint"));
        }
        _assertSameExt3(expected.gateFinalClaim, actual.gateFinalClaim, string.concat(label, ": gateFinalClaim"));
        assertEq(actual.transcript.state, expected.transcript.state, string.concat(label, ": transcript state"));
        assertEq(
            actual.transcript.squeezeCounter,
            expected.transcript.squeezeCounter,
            string.concat(label, ": transcript squeeze counter")
        );
    }

    function _assertSameExt3(GoldilocksExt3.Ext3 memory expected, GoldilocksExt3.Ext3 memory actual, string memory label)
        private
        pure
    {
        assertEq(actual.c0, expected.c0, string.concat(label, ".c0"));
        assertEq(actual.c1, expected.c1, string.concat(label, ".c1"));
        assertEq(actual.c2, expected.c2, string.concat(label, ".c2"));
    }

    // ---------------------------------------------------------------- entry wrappers

    function _runVerify(OuterInputs memory inputs) private view returns (Outcome memory outcome) {
        TranscriptV2.Transcript memory transcript = _copyTranscript(inputs.transcript);
        OuterLogupExt3Verifier.SumcheckProof memory logProof = _logProof(inputs);
        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _gateProof(inputs);
        uint256 before = gasleft();
        (outcome.logPoint, outcome.gatePoint, outcome.gateFinalClaim, outcome.transcript) = OuterLogupExt3Verifier
            .verify(logProof, gateProof, inputs.vk, inputs.challenges, inputs.terminal, transcript);
        outcome.gas = before - gasleft();
    }

    function _runPrevalidated(OuterInputs memory inputs) private view returns (Outcome memory outcome) {
        TranscriptV2.Transcript memory transcript = _copyTranscript(inputs.transcript);
        OuterLogupExt3Verifier.SumcheckProof memory logProof = _logProof(inputs);
        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _gateProof(inputs);
        uint256 before = gasleft();
        (outcome.logPoint, outcome.gatePoint, outcome.gateFinalClaim, outcome.transcript) = OuterLogupExt3Verifier
            .verifyPrevalidated(logProof, gateProof, inputs.vk, inputs.challenges, inputs.terminal, transcript);
        outcome.gas = before - gasleft();
    }

    function _runFlat(OuterInputs memory inputs) private view returns (Outcome memory outcome) {
        TranscriptV2.Transcript memory transcript = _copyTranscript(inputs.transcript);
        uint256 before = gasleft();
        (outcome.logPoint, outcome.gatePoint, outcome.gateFinalClaim, outcome.transcript) = OuterLogupExt3Verifier
            .verifyPrevalidatedFlat(
            inputs.logRounds,
            inputs.gateRounds,
            inputs.preprocessed,
            inputs.witness,
            inputs.normInverse,
            inputs.terminal.publicInputs,
            inputs.vk,
            inputs.challenges,
            transcript
        );
        outcome.gas = before - gasleft();
    }

    /// @dev External so `vm.expectRevert` observes the library revert.
    function callFlat(OuterInputs memory inputs) external view {
        _runFlat(inputs);
    }

    // ---------------------------------------------------------------- input preparation

    function _prepare(Fixture memory fixture) private returns (OuterInputs memory inputs) {
        MleVerifierV2 core = new MleVerifierV2(
            block.chainid,
            fixture.proof.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            fixture.config
        );
        uint256 indexBits = fixture.config.whir.numVariables - fixture.config.circuit.degreeBits;
        (inputs.transcript, inputs.challenges) = _deriveTranscript(fixture, core.circuitConfigDigest(), indexBits);

        inputs.vk = OuterLogupExt3Verifier.VerificationKey({
            numVars: fixture.config.circuit.degreeBits,
            gateDegree: fixture.config.circuit.quotientDegreeFactor + 2,
            numConstants: fixture.config.circuit.numConstants,
            numRoutedWires: fixture.config.circuit.numRoutedWires,
            numWires: fixture.config.circuit.numWires,
            kIs: fixture.config.kIs,
            subgroupGenPowers: fixture.config.subgroupGenPowers,
            publicInputWireMap: fixture.config.publicInputWireMap
        });
        inputs.terminal = OuterLogupExt3Verifier.TerminalEvaluations({
            preprocessed: fixture.proof.logPreprocessed,
            witness: fixture.proof.logWitness,
            normInverse: fixture.proof.logNormInverse,
            publicInputs: fixture.proof.publicInputs
        });
        inputs.logRounds = _flattenRounds(fixture.proof.logProof);
        inputs.gateRounds = _flattenRounds(fixture.proof.gateProof);
        inputs.preprocessed = _flatten(fixture.proof.logPreprocessed);
        inputs.witness = _flatten(fixture.proof.logWitness);
        inputs.normInverse = _flatten(fixture.proof.logNormInverse);
    }

    /// @dev The legacy entries read the same coefficient limbs the flat buffers were built from.
    function _logProof(OuterInputs memory inputs) private pure returns (OuterLogupExt3Verifier.SumcheckProof memory) {
        return _unflattenRounds(inputs.logRounds, inputs.vk.numVars, LOG_ROUND_DEGREE_V2);
    }

    function _gateProof(OuterInputs memory inputs) private pure returns (OuterLogupExt3Verifier.SumcheckProof memory) {
        return _unflattenRounds(inputs.gateRounds, inputs.vk.numVars, inputs.vk.gateDegree);
    }

    function _flattenRounds(OuterLogupExt3Verifier.SumcheckProof memory proof)
        private
        pure
        returns (uint256[] memory flat)
    {
        uint256 total;
        for (uint256 r = 0; r < proof.rounds.length; ++r) {
            total += proof.rounds[r].nonConstant.length;
        }
        flat = new uint256[](3 * total);
        uint256 cursor;
        for (uint256 r = 0; r < proof.rounds.length; ++r) {
            GoldilocksExt3.Ext3[] memory coefficients = proof.rounds[r].nonConstant;
            for (uint256 j = 0; j < coefficients.length; ++j) {
                flat[cursor++] = coefficients[j].c0;
                flat[cursor++] = coefficients[j].c1;
                flat[cursor++] = coefficients[j].c2;
            }
        }
    }

    function _unflattenRounds(uint256[] memory flat, uint256 numVars, uint256 degree)
        private
        pure
        returns (OuterLogupExt3Verifier.SumcheckProof memory proof)
    {
        proof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](numVars);
        uint256 cursor;
        for (uint256 r = 0; r < numVars; ++r) {
            proof.rounds[r].nonConstant = new GoldilocksExt3.Ext3[](degree);
            for (uint256 j = 0; j < degree; ++j) {
                proof.rounds[r].nonConstant[j] =
                    GoldilocksExt3.Ext3(uint64(flat[cursor]), uint64(flat[cursor + 1]), uint64(flat[cursor + 2]));
                cursor += 3;
            }
        }
    }

    function _flatten(GoldilocksExt3.Ext3[] memory values) private pure returns (uint256[] memory flat) {
        flat = new uint256[](3 * values.length);
        for (uint256 i = 0; i < values.length; ++i) {
            flat[3 * i] = values[i].c0;
            flat[3 * i + 1] = values[i].c1;
            flat[3 * i + 2] = values[i].c2;
        }
    }

    function _dropLast(uint256[] memory values) private pure returns (uint256[] memory shorter) {
        shorter = new uint256[](values.length - 1);
        for (uint256 i = 0; i < shorter.length; ++i) {
            shorter[i] = values[i];
        }
    }

    function _copyTranscript(TranscriptV2.Transcript memory source)
        private
        pure
        returns (TranscriptV2.Transcript memory copy)
    {
        copy.state = source.state;
        copy.squeezeCounter = source.squeezeCounter;
    }

    // ---------------------------------------------------------------- fixture + transcript derivation

    function _load(string memory json) private pure returns (Fixture memory fixture) {
        fixture.proof = abi.decode(vm.parseJsonBytes(json, ".solidityAbiProof.bytes"), (MleVerifierV2.MleProof));
        fixture.config = abi.decode(
            vm.parseJsonBytes(json, ".solidityAbiVerificationConfig.bytes"), (MleVerifierV2.VerificationConfig)
        );
        bytes memory protocolId = vm.parseJsonBytes(json, ".pinnedVerifier.whirProtocolId");
        require(protocolId.length == 64, "WHIR protocol identifier length");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocolId, 0x20))
            second := mload(add(protocolId, 0x40))
        }
        fixture.whirProtocolId = [first, second];
        fixture.whirSessionId = vm.parseJsonBytes32(json, ".pinnedVerifier.whirSessionId");
        require(fixture.proof.circuitDigest.length == 4, "circuit digest length");
        for (uint256 i = 0; i < 4; ++i) {
            fixture.circuitDigest[i] = uint64(fixture.proof.circuitDigest[i]);
        }
    }

    /// @dev Mirrors `MleVerifierV2._deriveInitialTranscript` up to (and including) the outer
    /// relation challenges; the gate alpha/tau squeezes that follow do not feed the outer verifier.
    function _deriveTranscript(Fixture memory fixture, bytes32 circuitConfigDigest, uint256 indexBits)
        private
        pure
        returns (TranscriptV2.Transcript memory transcript, OuterLogupExt3Verifier.Challenges memory challenges)
    {
        transcript = TranscriptV2.create();
        TranscriptV2.domainSeparate(transcript, DOMAIN_CIRCUIT_STATEMENT_V2);
        TranscriptV2.absorbFieldVec(transcript, fixture.proof.circuitDigest);
        TranscriptV2.absorbFieldVec(transcript, fixture.proof.publicInputs);
        TranscriptV2.domainSeparate(transcript, PACKED_PCS_SCHEMA_DOMAIN_V2);
        bytes memory metadata = new bytes(15 * 8);
        uint256 offset;
        offset = _writeU64Le(metadata, offset, MLE_PROTOCOL_VERSION_CURRENT);
        offset = _writeU64Le(metadata, offset, NUM_PCS_GROUPS_V2);
        offset = _writeU64Le(metadata, offset, NUM_PCS_TERMINAL_POINTS_V2);
        offset = _writeU64Le(metadata, offset, NUM_PCS_CLAIMS_V2);
        offset = _writeU64Le(metadata, offset, fixture.config.circuit.numConstants);
        offset = _writeU64Le(metadata, offset, fixture.config.circuit.numRoutedWires);
        offset = _writeU64Le(metadata, offset, fixture.config.circuit.numWires);
        offset = _writeU64Le(metadata, offset, fixture.config.circuit.degreeBits);
        offset = _writeU64Le(metadata, offset, fixture.proof.constituentWidth);
        offset = _writeU64Le(metadata, offset, indexBits);
        offset = _writeU64Le(metadata, offset, NUM_PACKED_VECTORS_PER_GROUP_V2);
        offset = _writeU64Le(metadata, offset, EXTENSION_FIELD_LIMBS_V2);
        offset = _writeU64Le(metadata, offset, PACKED_VARIABLE_ORDER_CODE_V2);
        offset = _writeU64Le(metadata, offset, GATE_SUMCHECK_COUNT_V2);
        offset = _writeU64Le(metadata, offset, LOG_ROUND_DEGREE_V2);
        require(offset == metadata.length, "metadata length");
        TranscriptV2.absorbBytes(transcript, metadata);
        TranscriptV2.domainSeparate(transcript, DOMAIN_CIRCUIT_CONFIG_DIGEST_V2);
        TranscriptV2.absorbBytes(transcript, abi.encodePacked(circuitConfigDigest));
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
        challenges.tau = new GoldilocksExt3.Ext3[](fixture.config.circuit.degreeBits);
        for (uint256 i = 0; i < challenges.tau.length; ++i) {
            challenges.tau[i] = TranscriptV2.squeezeExt3(transcript);
        }
        // gate alpha and gate tau are squeezed next by the core; they do not enter the outer verifier
        TranscriptV2.squeezeExt3(transcript);
        for (uint256 i = 0; i < fixture.config.circuit.degreeBits; ++i) {
            TranscriptV2.squeezeExt3(transcript);
        }
    }

    function _writeU64Le(bytes memory destination, uint256 offset, uint256 value) private pure returns (uint256) {
        for (uint256 byteIndex = 0; byteIndex < 8; ++byteIndex) {
            destination[offset + byteIndex] = bytes1(uint8(value >> (8 * byteIndex)));
        }
        return offset + 8;
    }
}
