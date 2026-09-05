// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {CanonicalWhirProfileV2} from "../src/CanonicalWhirProfileV2.sol";
import {InvalidMleVerifierConfiguration} from "../src/MleProofErrors.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";

/// @notice Cross-language drift and mutation checks for the generated
/// `WhirPCS::for_constituents` deployment profile table.
contract CanonicalWhirProfileV2Test is Test {
    string internal constant FIXTURE = "test/fixtures/v2_cross_language.json";
    string internal constant CASE = ".cases[0]";

    function test_fixtureN10AbiDigestProtocolAndSessionMatchRustProfile() external view {
        string memory json = vm.readFile(FIXTURE);
        SpongefishWhirVerify.WhirParams memory params = _parseWhirParams(json);
        (bytes32[2] memory protocolId, bytes32 sessionId) = _parseIds(json);

        CanonicalWhirProfileV2.validateCanonical(
            params.numVariables, keccak256(abi.encode(params)), protocolId, sessionId
        );
    }

    function test_everyWhirTopLevelFieldMutationIsRejected() external {
        string memory json = vm.readFile(FIXTURE);
        SpongefishWhirVerify.WhirParams memory canonical = _parseWhirParams(json);
        (bytes32[2] memory protocolId, bytes32 sessionId) = _parseIds(json);

        for (uint256 field = 0; field < 24; ++field) {
            SpongefishWhirVerify.WhirParams memory invalid = _clone(canonical);
            _mutateTopLevelField(invalid, field);
            vm.expectRevert(InvalidMleVerifierConfiguration.selector);
            _validate(invalid, protocolId, sessionId);
        }
    }

    function test_everyWhirRoundFieldMutationIsRejected() external {
        string memory json = vm.readFile(FIXTURE);
        SpongefishWhirVerify.WhirParams memory canonical = _parseWhirParams(json);
        (bytes32[2] memory protocolId, bytes32 sessionId) = _parseIds(json);

        assertGt(canonical.rounds.length, 0, "fixture must exercise an intermediate round");
        for (uint256 roundIndex = 0; roundIndex < canonical.rounds.length; ++roundIndex) {
            for (uint256 field = 0; field < 12; ++field) {
                SpongefishWhirVerify.WhirParams memory invalid = _clone(canonical);
                _mutateRoundField(invalid.rounds[roundIndex], field);
                vm.expectRevert(InvalidMleVerifierConfiguration.selector);
                _validate(invalid, protocolId, sessionId);
            }
        }
    }

    function test_protocolAndSessionIdentityMutationsAreRejected() external {
        string memory json = vm.readFile(FIXTURE);
        SpongefishWhirVerify.WhirParams memory params = _parseWhirParams(json);
        (bytes32[2] memory protocolId, bytes32 sessionId) = _parseIds(json);

        for (uint256 half = 0; half < 2; ++half) {
            bytes32[2] memory invalidId = protocolId;
            invalidId[half] = bytes32(uint256(invalidId[half]) ^ 1);
            vm.expectRevert(InvalidMleVerifierConfiguration.selector);
            _validate(params, invalidId, sessionId);
        }
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        _validate(params, protocolId, bytes32(uint256(sessionId) ^ 1));
    }

    function test_dimensionOutsideGeneratedRangeIsRejected() external {
        string memory json = vm.readFile(FIXTURE);
        SpongefishWhirVerify.WhirParams memory params = _parseWhirParams(json);
        (bytes32[2] memory protocolId, bytes32 sessionId) = _parseIds(json);
        bytes32 digest = keccak256(abi.encode(params));

        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        CanonicalWhirProfileV2.validateCanonical(0, digest, protocolId, sessionId);
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        CanonicalWhirProfileV2.validateCanonical(22, digest, protocolId, sessionId);
    }

    function _validate(SpongefishWhirVerify.WhirParams memory params, bytes32[2] memory protocolId, bytes32 sessionId)
        private
        pure
    {
        CanonicalWhirProfileV2.validateCanonical(
            params.numVariables, keccak256(abi.encode(params)), protocolId, sessionId
        );
    }

    function _clone(SpongefishWhirVerify.WhirParams memory params)
        private
        pure
        returns (SpongefishWhirVerify.WhirParams memory)
    {
        return abi.decode(abi.encode(params), (SpongefishWhirVerify.WhirParams));
    }

    function _mutateTopLevelField(SpongefishWhirVerify.WhirParams memory params, uint256 field) private pure {
        if (field == 0) params.numVariables ^= 1;
        else if (field == 1) params.foldingFactor ^= 1;
        else if (field == 2) params.numVectors ^= 1;
        else if (field == 3) params.numCommitments ^= 1;
        else if (field == 4) params.outDomainSamples ^= 1;
        else if (field == 5) params.inDomainSamples ^= 1;
        else if (field == 6) params.initialSumcheckRounds ^= 1;
        else if (field == 7) params.numRounds ^= 1;
        else if (field == 8) params.finalSumcheckRounds ^= 1;
        else if (field == 9) params.finalSize ^= 1;
        else if (field == 10) params.initialCodewordLength ^= 1;
        else if (field == 11) params.initialMerkleDepth ^= 1;
        else if (field == 12) params.initialDomainGenerator ^= 1;
        else if (field == 13) params.initialInterleavingDepth ^= 1;
        else if (field == 14) params.initialNumVariables ^= 1;
        else if (field == 15) params.initialCosetSize ^= 1;
        else if (field == 16) params.initialNumCosets ^= 1;
        else if (field == 17) params.initialSumcheckPowThreshold ^= 1;
        else if (field == 18) params.finalPowThreshold ^= 1;
        else if (field == 19) params.finalSumcheckPowThreshold ^= 1;
        else if (field == 20) params.evaluationPoint = new GoldilocksExt3.Ext3[](1);
        else if (field == 21) params.evaluationPoint2 = new GoldilocksExt3.Ext3[](1);
        else if (field == 22) params.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](1);
        else if (field == 23) params.rounds = new SpongefishWhirVerify.RoundParams[](0);
        else revert("unknown top-level WHIR field");
    }

    function _mutateRoundField(SpongefishWhirVerify.RoundParams memory round, uint256 field) private pure {
        if (field == 0) round.codewordLength ^= 1;
        else if (field == 1) round.merkleDepth ^= 1;
        else if (field == 2) round.domainGenerator ^= 1;
        else if (field == 3) round.inDomainSamples ^= 1;
        else if (field == 4) round.outDomainSamples ^= 1;
        else if (field == 5) round.sumcheckRounds ^= 1;
        else if (field == 6) round.interleavingDepth ^= 1;
        else if (field == 7) round.cosetSize ^= 1;
        else if (field == 8) round.numCosets ^= 1;
        else if (field == 9) round.numVariables ^= 1;
        else if (field == 10) round.powThreshold ^= 1;
        else if (field == 11) round.sumcheckPowThreshold ^= 1;
        else revert("unknown WHIR round field");
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
    }

    function _parseWhirRound(string memory json, string memory base, uint256 index)
        private
        pure
        returns (SpongefishWhirVerify.RoundParams memory round)
    {
        string memory path = string.concat(base, ".rounds[", vm.toString(index), "]");
        round.codewordLength = vm.parseJsonUint(json, string.concat(path, ".codewordLength"));
        round.merkleDepth = vm.parseJsonUint(json, string.concat(path, ".merkleDepth"));
        round.domainGenerator = uint64(_jsonStringUint(json, string.concat(path, ".domainGenerator")));
        round.inDomainSamples = vm.parseJsonUint(json, string.concat(path, ".inDomainSamples"));
        round.outDomainSamples = vm.parseJsonUint(json, string.concat(path, ".outDomainSamples"));
        round.sumcheckRounds = vm.parseJsonUint(json, string.concat(path, ".sumcheckRounds"));
        round.interleavingDepth = vm.parseJsonUint(json, string.concat(path, ".interleavingDepth"));
        round.cosetSize = vm.parseJsonUint(json, string.concat(path, ".cosetSize"));
        round.numCosets = vm.parseJsonUint(json, string.concat(path, ".numCosets"));
        round.numVariables = vm.parseJsonUint(json, string.concat(path, ".numVariables"));
        round.powThreshold = uint64(_jsonStringUint(json, string.concat(path, ".powThreshold")));
        round.sumcheckPowThreshold = uint64(_jsonStringUint(json, string.concat(path, ".sumcheckPowThreshold")));
    }

    function _parseIds(string memory json) private pure returns (bytes32[2] memory protocolId, bytes32 sessionId) {
        bytes memory raw = vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.whirProtocolId"));
        require(raw.length == 64, "WHIR protocol ID length");
        protocolId[0] = _bytes32At(raw, 0);
        protocolId[1] = _bytes32At(raw, 32);
        sessionId = vm.parseJsonBytes32(json, string.concat(CASE, ".verificationKey.whirSessionId"));
    }

    function _jsonStringUint(string memory json, string memory path) private pure returns (uint256) {
        return vm.parseUint(vm.parseJsonString(json, path));
    }

    function _bytes32At(bytes memory value, uint256 offset) private pure returns (bytes32 word) {
        require(offset + 32 <= value.length, "bytes32 bounds");
        assembly ("memory-safe") {
            word := mload(add(add(value, 0x20), offset))
        }
    }
}
