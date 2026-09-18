// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {TranscriptLib} from "../src/TranscriptLib.sol";
import {PACKED_V1_GOLDEN_TERMINAL_DIGEST} from "./TranscriptV1Golden.sol";
import {
    EXTENSION_FIELD_LIMBS,
    MLE_PROTOCOL_VERSION,
    MLE_TRANSCRIPT_PROTOCOL,
    NUM_PACKED_VECTORS_PER_GROUP,
    NUM_PCS_GROUPS,
    NUM_PCS_TERMINAL_POINTS,
    PACKED_PCS_SCHEMA_DOMAIN,
    PACKED_VARIABLE_ORDER_CODE
} from "../src/generated/MleWhirV1.sol";

/// @notice Byte-exact Solidity replay of the packed-v1 outer transcript.
/// @dev The fixture test mirrors `mle/tests/transcript_e2e_trace.rs`. Every
/// MLE-owned absorb and squeeze is checked against a deliberately simple
/// independent encoder, while all exported outer challenges are also checked
/// against the Rust fixture. This catches drift in state bytes, counter resets,
/// or operation order at the exact checkpoint where it occurs.
contract TranscriptE2ETrace is Test {
    uint256 internal constant P = 0xFFFFFFFF00000001;
    uint256 internal constant RADIX = 0xFFFFFFFF;

    struct ReferenceTrace {
        bytes state;
        uint64 squeezeCounter;
        uint256 checkpoints;
        uint256[] goldenStateLengths;
        uint256[] goldenSqueezeCounters;
        bytes32[] goldenStateDigests;
        string[] goldenLabels;
        bytes[] goldenAbsorbedBytes;
        uint256[] goldenChallengeCheckpointIndices;
        uint256[] goldenSqueezedChallenges;
        uint256 goldenChallengeCursor;
    }

    /// @notice Pins the dedicated prover/verifier mini-transcript used to
    /// derive the exported preprocessed-column batching challenge after its
    /// constituent commitment root has been fixed.
    function test_preprocessed_batch_r_trace() external view {
        string memory fixtureJson = vm.readFile("test/fixtures/small_mul.json");
        TranscriptLib.Transcript memory transcript;
        ReferenceTrace memory refTrace;
        _loadGolden(refTrace, ".preprocessedBatch", 5);
        _init(transcript, refTrace);
        _domain(transcript, refTrace, "preprocessed-batch-r", "preprocessed.domain");
        _absorbFieldVec(
            transcript, refTrace, _fieldArrayChecked(fixtureJson, ".circuitDigest", 4), "preprocessed.circuit_digest"
        );
        _absorbBytes(
            transcript, refTrace, vm.parseJsonBytes(fixtureJson, ".preprocessedCommitmentRoot"), "preprocessed.root"
        );
        _squeezeExpected(transcript, refTrace, _field(fixtureJson, ".preprocessedBatchR"), "preprocessed.batch_r");
        require(refTrace.checkpoints == 5, "preprocessed checkpoint count");
        require(refTrace.goldenChallengeCursor == 1, "preprocessed challenge count");
    }

    /// @notice Pins the version/domain and the complete packed PCS schema.
    function test_v1_protocol_and_schema_prefix() external pure {
        TranscriptLib.Transcript memory transcript;
        ReferenceTrace memory refTrace;
        _init(transcript, refTrace);

        require(transcript.state.length == 22, "protocol prefix length");
        require(
            keccak256(transcript.state) == 0x757cbb63921c25fc0fd6177a08c19085e0a08fd85dbdde3c1f8d2f7505e8e023,
            "protocol prefix digest"
        );

        _domain(transcript, refTrace, PACKED_PCS_SCHEMA_DOMAIN, "pcs.schema.domain");
        uint256[10] memory schema;
        schema[0] = MLE_PROTOCOL_VERSION;
        schema[1] = NUM_PCS_GROUPS;
        schema[2] = 4; // constants
        schema[3] = 80; // routed wires
        schema[4] = 135; // total wires
        schema[5] = 160; // constituent width
        schema[6] = 8; // packed constituent-index bits
        schema[7] = NUM_PACKED_VECTORS_PER_GROUP;
        schema[8] = EXTENSION_FIELD_LIMBS;
        schema[9] = PACKED_VARIABLE_ORDER_CODE;
        for (uint256 i = 0; i < schema.length; i++) {
            _absorbU64(transcript, refTrace, schema[i], string.concat("pcs.schema[", vm.toString(i), "]"));
        }

        require(refTrace.checkpoints == 12, "schema checkpoint count");
        require(transcript.squeezeCounter == 0, "schema squeeze counter");
        // 22-byte protocol prefix + 28-byte packed-schema domain + ten
        // (8-byte length || 8-byte u64 payload) entries.
        require(transcript.state.length == 210, "packed schema byte length");
        require(
            keccak256(transcript.state) == 0x719dac2325c9887267cd2bb63282738b51c5f646f26750c2545643874c671c22,
            "packed schema digest"
        );
    }

    /// @notice Replays all 192 checkpoints in the canonical small fixture.
    function test_small_mul_fixture_full_outer_packed_v1_trace() external view {
        string memory json = vm.readFile("test/fixtures/small_mul.json");
        uint256 protocolVersion = vm.parseJsonUint(json, ".protocolVersion");
        uint256 degreeBits = vm.parseJsonUint(json, ".degreeBits");
        uint256 constituentWidth = vm.parseJsonUint(json, ".constituentWidth");
        uint256 numConstants = vm.parseJsonUint(json, ".numConstants");
        uint256 numRoutedWires = vm.parseJsonUint(json, ".numRoutedWires");
        uint256 numWires = vm.parseJsonUint(json, ".numWires");
        uint256 indexBits = _ceilLog2(constituentWidth);

        require(protocolVersion == MLE_PROTOCOL_VERSION, "protocol version");
        require(vm.parseJsonUint(json, ".whirParams.numCommitments") == NUM_PCS_GROUPS, "commitment groups");
        require(vm.parseJsonUint(json, ".whirParams.numVectors") == NUM_PACKED_VECTORS_PER_GROUP, "packed vector count");
        require(vm.parseJsonUint(json, ".whirParams.numVariables") == degreeBits + indexBits, "packed variable count");

        TranscriptLib.Transcript memory transcript;
        ReferenceTrace memory refTrace;
        _loadGolden(refTrace, ".outer", 192);
        _init(transcript, refTrace);

        _domain(transcript, refTrace, "circuit", "circuit.domain");
        _absorbFieldVec(transcript, refTrace, _fieldArrayChecked(json, ".circuitDigest", 4), "circuit.digest");
        _absorbFieldVec(transcript, refTrace, _fieldArray(json, ".publicInputs"), "circuit.public_inputs");

        _domain(transcript, refTrace, PACKED_PCS_SCHEMA_DOMAIN, "pcs.schema.domain");
        uint256[10] memory schema;
        schema[0] = protocolVersion;
        schema[1] = NUM_PCS_GROUPS;
        schema[2] = numConstants;
        schema[3] = numRoutedWires;
        schema[4] = numWires;
        schema[5] = constituentWidth;
        schema[6] = indexBits;
        schema[7] = NUM_PACKED_VECTORS_PER_GROUP;
        schema[8] = EXTENSION_FIELD_LIMBS;
        schema[9] = PACKED_VARIABLE_ORDER_CODE;
        for (uint256 i = 0; i < schema.length; i++) {
            _absorbU64(transcript, refTrace, schema[i], string.concat("pcs.schema[", vm.toString(i), "]"));
        }

        _domain(transcript, refTrace, "pcs-group-preprocessed", "pcs.preprocessed.domain");
        _absorbBytes(
            transcript, refTrace, vm.parseJsonBytes(json, ".preprocessedCommitmentRoot"), "pcs.root.preprocessed"
        );
        _domain(transcript, refTrace, "pcs-group-witness", "pcs.witness.domain");
        _absorbBytes(transcript, refTrace, vm.parseJsonBytes(json, ".witnessCommitmentRoot"), "pcs.root.witness");

        _domain(transcript, refTrace, "batch-commit-witness", "rho.witness.domain");
        _squeezeExpected(transcript, refTrace, _field(json, ".witnessBatchR"), "rho.witness");
        _domain(transcript, refTrace, "challenges", "base.domain");
        _squeezeExpected(transcript, refTrace, _field(json, ".beta"), "beta");
        _squeezeExpected(transcript, refTrace, _field(json, ".gamma"), "gamma");

        _domain(transcript, refTrace, "pcs-group-inverse-helpers", "pcs.inverse.domain");
        _absorbBytes(transcript, refTrace, vm.parseJsonBytes(json, ".inverseHelpersCommitmentRoot"), "pcs.root.inverse");
        _domain(transcript, refTrace, "inverse-helpers-batch-r", "rho.inverse.domain");
        _squeezeExpected(transcript, refTrace, _field(json, ".inverseHelpersBatchR"), "rho.inverse");
        _squeezeExpected(transcript, refTrace, _field(json, ".alpha"), "alpha");
        _domain(transcript, refTrace, "extension-combine", "extension.domain");
        _squeezeExpected(transcript, refTrace, _field(json, ".extChallenge"), "extension");

        _domain(transcript, refTrace, "pcs-group-auxiliary", "pcs.auxiliary.domain");
        _absorbBytes(transcript, refTrace, vm.parseJsonBytes(json, ".auxCommitmentRoot"), "pcs.root.auxiliary");
        _domain(transcript, refTrace, "aux-batch-r", "rho.auxiliary.domain");
        _squeezeExpected(transcript, refTrace, _field(json, ".auxBatchR"), "rho.auxiliary");

        _domain(transcript, refTrace, "post-auxiliary-challenges-v1", "post_auxiliary.domain");
        _squeezeArray(transcript, refTrace, _fieldArrayChecked(json, ".tau", degreeBits), "tau");
        _squeezeArray(transcript, refTrace, _fieldArrayChecked(json, ".tauPerm", degreeBits), "tau_perm");

        _domain(transcript, refTrace, "v2-logup-challenges", "logup.domain");
        _squeezeExpected(transcript, refTrace, _field(json, ".lambdaInv"), "lambda_inv");
        _squeezeExpected(transcript, refTrace, _field(json, ".muInv"), "mu_inv");
        _squeezeArray(transcript, refTrace, _fieldArrayChecked(json, ".tauInv", degreeBits), "tau_inv");

        _domain(transcript, refTrace, "combined-sumcheck", "combined.domain");
        _squeezeExpected(transcript, refTrace, _field(json, ".mu"), "mu");
        _replaySumcheck(transcript, refTrace, json, ".combinedProof", ".evaluationPoint", "combined", degreeBits, true);

        _domain(transcript, refTrace, "v2-inv-zerocheck", "inverse.domain");
        _replaySumcheck(
            transcript, refTrace, json, ".invSumcheckProof", ".invSumcheckChallenges", "inverse", degreeBits, false
        );
        _domain(transcript, refTrace, "v2-h-linear", "h.domain");
        _replaySumcheck(transcript, refTrace, json, ".hSumcheckProof", ".hSumcheckChallenges", "h", degreeBits, false);

        _domain(transcript, refTrace, "v2-gate-challenges", "gate.challenge.domain");
        _squeezeArray(transcript, refTrace, _fieldArrayChecked(json, ".tauGate", degreeBits), "tau_gate");
        _domain(transcript, refTrace, "v2-gate-zerocheck", "gate.domain");
        _replaySumcheck(
            transcript, refTrace, json, ".gateSumcheckProof", ".gateSumcheckChallenges", "gate", degreeBits, false
        );

        _domain(transcript, refTrace, "pcs-eval", "pcs.eval.domain");
        _replayPackedClaims(transcript, refTrace, json, numConstants + numRoutedWires, numWires, 2 * numRoutedWires);

        _domain(transcript, refTrace, "pcs-constituent-index-v1", "pcs.index.domain");
        for (uint256 pointIndex = 0; pointIndex < NUM_PCS_TERMINAL_POINTS; pointIndex++) {
            for (uint256 bit = 0; bit < indexBits; bit++) {
                for (uint256 limb = 0; limb < EXTENSION_FIELD_LIMBS; limb++) {
                    _squeeze(
                        transcript,
                        refTrace,
                        string.concat(
                            "pcs.index[", vm.toString(pointIndex), "][", vm.toString(bit), "].c", vm.toString(limb)
                        )
                    );
                }
            }
        }

        require(refTrace.checkpoints == 64 + 16 * degreeBits + 12 * indexBits, "trace formula");
        require(refTrace.checkpoints == 192, "small fixture checkpoint count");
        require(refTrace.checkpoints == refTrace.goldenStateDigests.length, "unconsumed golden checkpoints");
        require(
            refTrace.goldenChallengeCursor == refTrace.goldenSqueezedChallenges.length, "unconsumed golden challenges"
        );
        require(transcript.squeezeCounter == 12 * indexBits, "terminal squeeze count");
        require(
            keccak256(transcript.state) == PACKED_V1_GOLDEN_TERMINAL_DIGEST,
            "packed v1 golden terminal digest"
        );
    }

    function _replayPackedClaims(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        string memory json,
        uint256 preprocessedWidth,
        uint256 witnessWidth,
        uint256 inverseWidth
    ) internal pure {
        uint256[] memory empty = new uint256[](0);
        uint256[] memory auxiliary = new uint256[](2);
        auxiliary[0] = _field(json, ".auxConstraintEval");
        auxiliary[1] = _field(json, ".auxPermEval");

        _domain(transcript, refTrace, "pcs-constituent-claims-v1", "pcs.claims.domain");
        // Point-major, then canonical group order:
        // preprocessed, witness, inverse helpers, auxiliary.
        _absorbClaim(
            transcript, refTrace, _fieldArrayChecked(json, ".preprocessedIndividualEvals", preprocessedWidth), 0
        );
        _absorbClaim(transcript, refTrace, _fieldArrayChecked(json, ".witnessIndividualEvals", witnessWidth), 1);
        _absorbClaim(transcript, refTrace, empty, 2);
        _absorbClaim(transcript, refTrace, auxiliary, 3);

        _absorbClaim(
            transcript, refTrace, _fieldArrayChecked(json, ".preprocessedIndividualEvalsAtRInv", preprocessedWidth), 4
        );
        _absorbClaim(transcript, refTrace, _fieldArrayChecked(json, ".witnessIndividualEvalsAtRInv", witnessWidth), 5);
        _absorbClaim(transcript, refTrace, _fieldArrayChecked(json, ".inverseHelpersEvalsAtRInv", inverseWidth), 6);
        _absorbClaim(transcript, refTrace, empty, 7);

        _absorbClaim(transcript, refTrace, empty, 8);
        _absorbClaim(transcript, refTrace, empty, 9);
        _absorbClaim(transcript, refTrace, _fieldArrayChecked(json, ".inverseHelpersEvalsAtRH", inverseWidth), 10);
        _absorbClaim(transcript, refTrace, empty, 11);

        _absorbClaim(
            transcript,
            refTrace,
            _fieldArrayChecked(json, ".preprocessedIndividualEvalsAtRGateV2", preprocessedWidth),
            12
        );
        _absorbClaim(
            transcript, refTrace, _fieldArrayChecked(json, ".witnessIndividualEvalsAtRGateV2", witnessWidth), 13
        );
        _absorbClaim(transcript, refTrace, empty, 14);
        _absorbClaim(transcript, refTrace, empty, 15);
    }

    function _absorbClaim(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        uint256[] memory values,
        uint256 claimIndex
    ) internal pure {
        _absorbFieldVec(transcript, refTrace, values, string.concat("pcs.claim[", vm.toString(claimIndex), "]"));
    }

    function _replaySumcheck(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        string memory json,
        string memory proofPath,
        string memory challengePath,
        string memory tracePrefix,
        uint256 rounds,
        bool extensionPoint
    ) internal pure {
        uint256[] memory challenges;
        if (!extensionPoint) {
            challenges = _fieldArrayChecked(json, challengePath, rounds);
        }

        for (uint256 round = 0; round < rounds; round++) {
            string memory roundString = vm.toString(round);
            _domain(
                transcript, refTrace, "sumcheck-round", string.concat(tracePrefix, ".round[", roundString, "].domain")
            );
            string memory roundPath = string.concat(proofPath, ".roundPolys[", vm.toString(round), "]");
            _absorbFieldVec(
                transcript,
                refTrace,
                _fieldArray(json, roundPath),
                string.concat(tracePrefix, ".round[", roundString, "].message")
            );
            uint256 expected = extensionPoint ? _ext3BasePoint(json, challengePath, round) : challenges[round];
            _squeezeExpected(transcript, refTrace, expected, string.concat(tracePrefix, ".query[", roundString, "]"));
        }

        _requireNoRound(json, proofPath, rounds);
        if (extensionPoint) _requireNoExtPoint(json, challengePath, rounds);
    }

    function _squeezeArray(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        uint256[] memory expected,
        string memory tracePrefix
    ) internal pure {
        for (uint256 i = 0; i < expected.length; i++) {
            _squeezeExpected(transcript, refTrace, expected[i], string.concat(tracePrefix, "[", vm.toString(i), "]"));
        }
    }

    function _fieldArrayChecked(string memory json, string memory path, uint256 expectedLength)
        internal
        pure
        returns (uint256[] memory values)
    {
        values = _fieldArray(json, path);
        require(values.length == expectedLength, "fixture field-vector length");
    }

    function _fieldArray(string memory json, string memory path) internal pure returns (uint256[] memory values) {
        string[] memory strings = vm.parseJsonStringArray(json, path);
        values = new uint256[](strings.length);
        for (uint256 i = 0; i < strings.length; i++) {
            values[i] = vm.parseUint(strings[i]);
            require(values[i] < P, "non-canonical fixture field");
        }
    }

    function _field(string memory json, string memory path) internal pure returns (uint256 value) {
        value = vm.parseUint(vm.parseJsonString(json, path));
        require(value < P, "non-canonical fixture field");
    }

    function _ext3BasePoint(string memory json, string memory path, uint256 index) internal pure returns (uint256 c0) {
        string memory base = string.concat(path, "[", vm.toString(index), "]");
        c0 = _field(json, string.concat(base, ".c0"));
        require(_field(json, string.concat(base, ".c1")) == 0, "evaluation point c1");
        require(_field(json, string.concat(base, ".c2")) == 0, "evaluation point c2");
    }

    function _requireNoRound(string memory json, string memory proofPath, uint256 index) internal pure {
        string memory path = string.concat(proofPath, ".roundPolys[", vm.toString(index), "]");
        try vm.parseJsonStringArray(json, path) returns (string[] memory) {
            revert("sumcheck round tail");
        } catch {}
    }

    function _requireNoExtPoint(string memory json, string memory path, uint256 index) internal pure {
        string memory c0Path = string.concat(path, "[", vm.toString(index), "].c0");
        try vm.parseJsonString(json, c0Path) returns (string memory) {
            revert("evaluation point tail");
        } catch {}
    }

    function _loadGolden(ReferenceTrace memory refTrace, string memory tablePath, uint256 expectedCheckpoints)
        internal
        view
    {
        string memory json = vm.readFile("test/fixtures/transcript_v1_trace.json");
        require(vm.parseJsonUint(json, ".protocolVersion") == MLE_PROTOCOL_VERSION, "golden protocol version");
        require(
            keccak256(bytes(vm.parseJsonString(json, ".sourceFixture"))) == keccak256("small_mul.json"),
            "golden source fixture"
        );
        refTrace.goldenStateLengths = vm.parseJsonUintArray(json, string.concat(tablePath, ".stateLengths"));
        refTrace.goldenSqueezeCounters = vm.parseJsonUintArray(json, string.concat(tablePath, ".squeezeCounters"));
        refTrace.goldenStateDigests = vm.parseJsonBytes32Array(json, string.concat(tablePath, ".stateDigests"));
        refTrace.goldenLabels = vm.parseJsonStringArray(json, string.concat(tablePath, ".labels"));
        refTrace.goldenAbsorbedBytes = vm.parseJsonBytesArray(json, string.concat(tablePath, ".absorbedBytes"));
        refTrace.goldenChallengeCheckpointIndices =
            vm.parseJsonUintArray(json, string.concat(tablePath, ".challengeCheckpointIndices"));
        string[] memory squeezedChallenges =
            vm.parseJsonStringArray(json, string.concat(tablePath, ".squeezedChallenges"));
        refTrace.goldenSqueezedChallenges = new uint256[](squeezedChallenges.length);
        for (uint256 i = 0; i < squeezedChallenges.length; i++) {
            uint256 challenge = vm.parseUint(squeezedChallenges[i]);
            require(challenge < P, "non-canonical golden challenge");
            refTrace.goldenSqueezedChallenges[i] = challenge;
        }
        require(refTrace.goldenStateLengths.length == expectedCheckpoints, "golden state-length count");
        require(refTrace.goldenSqueezeCounters.length == expectedCheckpoints, "golden counter count");
        require(refTrace.goldenStateDigests.length == expectedCheckpoints, "golden digest count");
        require(refTrace.goldenLabels.length == expectedCheckpoints, "golden label count");
        require(refTrace.goldenAbsorbedBytes.length == expectedCheckpoints, "golden absorbed-byte count");
        require(
            refTrace.goldenChallengeCheckpointIndices.length == refTrace.goldenSqueezedChallenges.length,
            "golden challenge-index count"
        );
    }

    function _init(TranscriptLib.Transcript memory transcript, ReferenceTrace memory refTrace) internal pure {
        TranscriptLib.init(transcript);
        bytes memory protocol = bytes(MLE_TRANSCRIPT_PROTOCOL);
        refTrace.state = bytes.concat(_u64Le(protocol.length), protocol);
        refTrace.squeezeCounter = 0;
        _checkpoint(transcript, refTrace, "protocol");
    }

    function _domain(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        string memory label,
        string memory traceLabel
    ) internal pure {
        TranscriptLib.domainSeparate(transcript, label);
        bytes memory encoded = bytes(label);
        refTrace.state = bytes.concat(refTrace.state, _u64Le(encoded.length), encoded);
        refTrace.squeezeCounter = 0;
        _checkpoint(transcript, refTrace, traceLabel);
    }

    function _absorbU64(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        uint256 value,
        string memory traceLabel
    ) internal pure {
        require(value <= type(uint64).max, "schema u64 overflow");
        TranscriptLib.absorbU64Bytes(transcript, value);
        refTrace.state = bytes.concat(refTrace.state, _u64Le(8), _u64Le(value));
        refTrace.squeezeCounter = 0;
        _checkpoint(transcript, refTrace, traceLabel);
    }

    function _absorbBytes(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        bytes memory value,
        string memory traceLabel
    ) internal pure {
        TranscriptLib.absorbBytes(transcript, value);
        refTrace.state = bytes.concat(refTrace.state, _u64Le(value.length), value);
        refTrace.squeezeCounter = 0;
        _checkpoint(transcript, refTrace, traceLabel);
    }

    function _absorbFieldVec(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        uint256[] memory values,
        string memory traceLabel
    ) internal pure {
        TranscriptLib.absorbFieldVec(transcript, values);
        bytes memory encoded = new bytes(8 + 8 * values.length);
        _writeU64Le(encoded, 0, values.length);
        for (uint256 i = 0; i < values.length; i++) {
            require(values[i] < P, "non-canonical reference field");
            _writeU64Le(encoded, 8 + 8 * i, values[i]);
        }
        refTrace.state = bytes.concat(refTrace.state, encoded);
        refTrace.squeezeCounter = 0;
        _checkpoint(transcript, refTrace, traceLabel);
    }

    function _squeezeExpected(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        uint256 expected,
        string memory traceLabel
    ) internal pure returns (uint256 actual) {
        actual = TranscriptLib.squeezeChallenge(transcript);
        uint256 independent = _referenceChallenge(refTrace.state, refTrace.squeezeCounter);
        refTrace.squeezeCounter++;
        require(actual == independent, "independent squeeze mismatch");
        require(actual == expected, "Rust fixture challenge mismatch");
        _checkGoldenChallenge(refTrace, actual);
        _checkpoint(transcript, refTrace, traceLabel);
    }

    function _squeeze(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        string memory traceLabel
    ) internal pure returns (uint256 actual) {
        actual = TranscriptLib.squeezeChallenge(transcript);
        uint256 independent = _referenceChallenge(refTrace.state, refTrace.squeezeCounter);
        refTrace.squeezeCounter++;
        require(actual == independent, "independent squeeze mismatch");
        _checkGoldenChallenge(refTrace, actual);
        _checkpoint(transcript, refTrace, traceLabel);
    }

    function _checkGoldenChallenge(ReferenceTrace memory refTrace, uint256 actual) internal pure {
        if (refTrace.goldenSqueezedChallenges.length == 0) return;
        uint256 cursor = refTrace.goldenChallengeCursor;
        require(cursor < refTrace.goldenSqueezedChallenges.length, "unexpected golden challenge");
        require(
            refTrace.goldenChallengeCheckpointIndices[cursor] == refTrace.checkpoints, "golden challenge checkpoint"
        );
        require(refTrace.goldenSqueezedChallenges[cursor] == actual, "golden squeezed challenge");
        refTrace.goldenChallengeCursor++;
    }

    function _checkpoint(
        TranscriptLib.Transcript memory transcript,
        ReferenceTrace memory refTrace,
        string memory traceLabel
    ) internal pure {
        uint256 index = refTrace.checkpoints;
        require(transcript.state.length == refTrace.state.length, "checkpoint state length");
        require(keccak256(transcript.state) == keccak256(refTrace.state), "checkpoint digest");
        require(transcript.squeezeCounter == refTrace.squeezeCounter, "checkpoint counter");
        if (refTrace.goldenStateDigests.length != 0) {
            require(index < refTrace.goldenStateDigests.length, "unexpected transcript checkpoint");
            require(
                keccak256(bytes(traceLabel)) == keccak256(bytes(refTrace.goldenLabels[index])),
                "golden checkpoint label"
            );
            require(transcript.state.length == refTrace.goldenStateLengths[index], "golden state length");
            require(transcript.squeezeCounter == refTrace.goldenSqueezeCounters[index], "golden squeeze counter");
            require(keccak256(transcript.state) == refTrace.goldenStateDigests[index], "golden state digest");
            uint256 previousLength = index == 0 ? 0 : refTrace.goldenStateLengths[index - 1];
            require(previousLength <= refTrace.state.length, "golden previous state length");
            bytes memory absorbed = _slice(refTrace.state, previousLength, refTrace.state.length - previousLength);
            require(keccak256(absorbed) == keccak256(refTrace.goldenAbsorbedBytes[index]), "golden absorbed bytes");
        }
        refTrace.checkpoints++;
    }

    function _slice(bytes memory source, uint256 offset, uint256 length) internal pure returns (bytes memory result) {
        require(offset + length <= source.length, "slice bounds");
        result = new bytes(length);
        for (uint256 i = 0; i < length; i++) {
            result[i] = source[offset + i];
        }
    }

    function _referenceChallenge(bytes memory state, uint64 counter) internal pure returns (uint256 challenge) {
        bytes32 digest = keccak256(bytes.concat(state, _u64Le(counter)));
        uint256 limb0 = _readU64Le(digest, 0);
        uint256 limb1 = _readU64Le(digest, 8);
        uint256 limb2 = _readU64Le(digest, 16);
        uint256 limb3 = _readU64Le(digest, 24);
        challenge = addmod(mulmod(limb3, RADIX, P), limb2, P);
        challenge = addmod(mulmod(challenge, RADIX, P), limb1, P);
        challenge = addmod(mulmod(challenge, RADIX, P), limb0, P);
    }

    function _readU64Le(bytes32 data, uint256 offset) internal pure returns (uint256 value) {
        for (uint256 i = 0; i < 8; i++) {
            value |= uint256(uint8(data[offset + i])) << (8 * i);
        }
    }

    function _u64Le(uint256 value) internal pure returns (bytes memory encoded) {
        require(value <= type(uint64).max, "u64 overflow");
        encoded = new bytes(8);
        _writeU64Le(encoded, 0, value);
    }

    function _writeU64Le(bytes memory destination, uint256 offset, uint256 value) internal pure {
        require(value <= type(uint64).max, "u64 overflow");
        for (uint256 i = 0; i < 8; i++) {
            destination[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
    }

    function _ceilLog2(uint256 value) internal pure returns (uint256 bits) {
        require(value != 0, "zero constituent width");
        value--;
        while (value != 0) {
            bits++;
            value >>= 1;
        }
    }
}
