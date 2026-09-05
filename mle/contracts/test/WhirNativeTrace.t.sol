// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {Keccak256Chain} from "../src/spongefish/Keccak256Chain.sol";
import {NUM_PCS_CLAIMS, NUM_PCS_GROUPS} from "../src/generated/MleWhirV1.sol";

/// @notice Differential replay of every native grouped-WHIR transcript event
/// emitted by the production Rust preflight parser for `small_mul.json`.
/// @dev This deliberately leaves production Solidity bytecode unchanged. It
/// checks the exact NARG/hint cursors, absorbed and squeezed bytes, Keccak state,
/// counter and derived query indices using the production Solidity
/// `Keccak256Chain` primitive. The existing MleE2E test separately runs the same
/// fixture through the production Solidity WHIR verifier. This test does not
/// directly instrument each call site inside `SpongefishWhirVerify`.
contract WhirNativeTrace is Test {
    uint256 internal constant ABSORB = 0;
    uint256 internal constant SQUEEZE = 1;
    uint256 internal constant QUERY_SQUEEZE = 2;
    uint256 internal constant QUERY_INDICES = 3;
    uint256 internal constant HINT = 4;
    uint256 internal constant EOF_EVENT = 5;

    struct Golden {
        string[] labels;
        uint256[] kinds;
        uint256[] nargPositions;
        uint256[] hintPositions;
        bytes32[] spongeStates;
        uint256[] squeezeCounters;
        bytes[] eventBytes;
        uint256[] queryCheckpointIndices;
        uint256[] queryOffsets;
        uint256[] queryIndices;
    }

    function test_small_mul_native_whir_differential_trace() external view {
        string memory fixtureJson = vm.readFile("test/fixtures/small_mul.json");
        string memory goldenJson = vm.readFile("test/fixtures/transcript_v1_trace.json");
        Golden memory golden = _loadGolden(goldenJson);
        bytes memory narg = vm.parseJsonBytes(fixtureJson, ".whirTranscript");
        bytes memory hints = vm.parseJsonBytes(fixtureJson, ".whirHints");

        require(golden.labels.length == 307, "native WHIR checkpoint count");
        require(_same(golden.labels[0], "init.protocol"), "native protocol label");
        require(_same(golden.labels[1], "init.session"), "native session label");
        require(_same(golden.labels[2], "init.instance"), "native instance label");
        require(
            _equalBytes(golden.eventBytes[0], vm.parseJsonBytes(fixtureJson, ".whirProtocolId")), "native protocol id"
        );
        require(
            _equalBytes(golden.eventBytes[1], vm.parseJsonBytes(fixtureJson, ".whirSplitSessionId")),
            "native session id"
        );
        require(golden.eventBytes[2].length == 0, "native empty instance");

        for (uint256 group = 0; group < NUM_PCS_GROUPS; group++) {
            _requireUniqueLabel(golden.labels, string.concat("initial.group[", vm.toString(group), "].root"));
            _requireUniqueLabel(golden.labels, string.concat("initial.group[", vm.toString(group), "].bound_root"));
        }
        for (uint256 claim = 0; claim < NUM_PCS_CLAIMS; claim++) {
            _requireUniqueLabel(golden.labels, string.concat("initial.statement.claim[", vm.toString(claim), "]"));
        }

        Keccak256Chain.Sponge memory sponge = Keccak256Chain.init();
        uint256 nargPosition;
        uint256 hintPosition;
        uint256 queryCursor;
        bytes memory pendingQueryEntropy;
        uint256[6] memory kindCounts;

        for (uint256 checkpoint = 0; checkpoint < golden.labels.length; checkpoint++) {
            uint256 kind = golden.kinds[checkpoint];
            require(kind <= EOF_EVENT, "native event kind");
            kindCounts[kind]++;

            if (kind == ABSORB) {
                if (golden.nargPositions[checkpoint] == nargPosition) {
                    require(checkpoint < 3, "non-NARG absorb after init");
                } else {
                    uint256 consumed = golden.nargPositions[checkpoint] - nargPosition;
                    require(consumed == golden.eventBytes[checkpoint].length, "native NARG event length");
                    require(
                        _equalBytes(_slice(narg, nargPosition, consumed), golden.eventBytes[checkpoint]),
                        "native NARG event bytes"
                    );
                    nargPosition = golden.nargPositions[checkpoint];
                }
                Keccak256Chain.absorb(sponge, golden.eventBytes[checkpoint]);
            } else {
                require(golden.nargPositions[checkpoint] == nargPosition, "native NARG cursor drift");
            }

            if (kind == SQUEEZE || kind == QUERY_SQUEEZE) {
                bytes memory actual = Keccak256Chain.squeeze(sponge, golden.eventBytes[checkpoint].length);
                require(_equalBytes(actual, golden.eventBytes[checkpoint]), "native squeezed bytes");
                if (kind == QUERY_SQUEEZE) {
                    pendingQueryEntropy = bytes.concat(pendingQueryEntropy, actual);
                }
            } else if (kind == QUERY_INDICES) {
                require(queryCursor < golden.queryCheckpointIndices.length, "unexpected query checkpoint");
                require(golden.queryCheckpointIndices[queryCursor] == checkpoint, "query checkpoint index");
                require(_equalBytes(pendingQueryEntropy, golden.eventBytes[checkpoint]), "query entropy batch");
                uint256[] memory indices = _deriveQueryIndices(fixtureJson, queryCursor, pendingQueryEntropy);
                uint256 begin = golden.queryOffsets[queryCursor];
                uint256 end = golden.queryOffsets[queryCursor + 1];
                require(indices.length == end - begin, "query index count");
                for (uint256 i = 0; i < indices.length; i++) {
                    require(indices[i] == golden.queryIndices[begin + i], "derived query index");
                }
                pendingQueryEntropy = new bytes(0);
                queryCursor++;
            }

            if (kind == HINT) {
                uint256 nextHintPosition = golden.hintPositions[checkpoint];
                require(nextHintPosition > hintPosition, "empty native hint segment");
                bytes memory segment = _slice(hints, hintPosition, nextHintPosition - hintPosition);
                require(golden.eventBytes[checkpoint].length == 32, "hint digest length");
                require(keccak256(segment) == _readBytes32(golden.eventBytes[checkpoint]), "native hint segment digest");
                hintPosition = nextHintPosition;
            } else {
                require(golden.hintPositions[checkpoint] == hintPosition, "native hint cursor drift");
            }

            require(sponge.state == golden.spongeStates[checkpoint], "native sponge state");
            require(uint256(sponge.squeezeCounter) == golden.squeezeCounters[checkpoint], "native squeeze counter");
        }

        require(kindCounts[ABSORB] == 69, "native absorb count");
        require(kindCounts[SQUEEZE] == 18, "native squeeze count");
        require(kindCounts[QUERY_SQUEEZE] == 212, "native query squeeze count");
        require(kindCounts[QUERY_INDICES] == 2, "native query checkpoint count");
        require(kindCounts[HINT] == 5, "native hint checkpoint count");
        require(kindCounts[EOF_EVENT] == 1, "native EOF count");
        require(golden.kinds[golden.kinds.length - 1] == EOF_EVENT, "native final EOF");
        require(nargPosition == narg.length, "native trailing NARG");
        require(hintPosition == hints.length, "native trailing hints");
        require(pendingQueryEntropy.length == 0, "native pending query entropy");
        require(queryCursor == golden.queryCheckpointIndices.length, "native query cursor");
        require(golden.queryOffsets.length == queryCursor + 1, "native query offsets");
        require(golden.queryOffsets[queryCursor] == golden.queryIndices.length, "native query tail");
    }

    function _loadGolden(string memory json) internal pure returns (Golden memory golden) {
        string memory path = ".whirNative";
        golden.labels = vm.parseJsonStringArray(json, string.concat(path, ".labels"));
        golden.kinds = vm.parseJsonUintArray(json, string.concat(path, ".kinds"));
        golden.nargPositions = vm.parseJsonUintArray(json, string.concat(path, ".nargPositions"));
        golden.hintPositions = vm.parseJsonUintArray(json, string.concat(path, ".hintPositions"));
        golden.spongeStates = vm.parseJsonBytes32Array(json, string.concat(path, ".spongeStates"));
        golden.squeezeCounters = vm.parseJsonUintArray(json, string.concat(path, ".squeezeCounters"));
        golden.eventBytes = vm.parseJsonBytesArray(json, string.concat(path, ".eventBytes"));
        golden.queryCheckpointIndices = vm.parseJsonUintArray(json, string.concat(path, ".queryCheckpointIndices"));
        golden.queryOffsets = vm.parseJsonUintArray(json, string.concat(path, ".queryOffsets"));
        golden.queryIndices = vm.parseJsonUintArray(json, string.concat(path, ".queryIndices"));

        uint256 checkpoints = golden.labels.length;
        require(golden.kinds.length == checkpoints, "native kinds length");
        require(golden.nargPositions.length == checkpoints, "native NARG positions length");
        require(golden.hintPositions.length == checkpoints, "native hint positions length");
        require(golden.spongeStates.length == checkpoints, "native states length");
        require(golden.squeezeCounters.length == checkpoints, "native counters length");
        require(golden.eventBytes.length == checkpoints, "native event bytes length");
        require(golden.queryOffsets.length == golden.queryCheckpointIndices.length + 1, "query offset shape");
        require(golden.queryOffsets[0] == 0, "query offset origin");
    }

    function _deriveQueryIndices(string memory fixtureJson, uint256 query, bytes memory entropy)
        internal
        pure
        returns (uint256[] memory indices)
    {
        uint256 codewordLength;
        uint256 sampleCount;
        if (query == 0) {
            codewordLength = vm.parseJsonUint(fixtureJson, ".whirParams.initialCodewordLength");
            sampleCount = vm.parseJsonUint(fixtureJson, ".whirParams.inDomainSamples");
        } else {
            string memory round = string.concat(".whirParams.rounds[", vm.toString(query - 1), "]");
            codewordLength = vm.parseJsonUint(fixtureJson, string.concat(round, ".codewordLength"));
            sampleCount = vm.parseJsonUint(fixtureJson, string.concat(round, ".inDomainSamples"));
        }
        require(codewordLength != 0 && codewordLength & (codewordLength - 1) == 0, "query domain");
        uint256 bytesPerIndex = (_ceilLog2(codewordLength) + 7) / 8;
        require(entropy.length == sampleCount * bytesPerIndex, "query entropy length");

        uint256[] memory raw = new uint256[](sampleCount);
        for (uint256 i = 0; i < sampleCount; i++) {
            uint256 value;
            for (uint256 j = 0; j < bytesPerIndex; j++) {
                value = (value << 8) | uint8(entropy[i * bytesPerIndex + j]);
            }
            raw[i] = value % codewordLength;
        }
        for (uint256 i = 1; i < raw.length; i++) {
            uint256 value = raw[i];
            uint256 cursor = i;
            while (cursor != 0 && raw[cursor - 1] > value) {
                raw[cursor] = raw[cursor - 1];
                cursor--;
            }
            raw[cursor] = value;
        }
        uint256 unique;
        for (uint256 i = 0; i < raw.length; i++) {
            if (i == 0 || raw[i] != raw[i - 1]) unique++;
        }
        indices = new uint256[](unique);
        uint256 output;
        for (uint256 i = 0; i < raw.length; i++) {
            if (i == 0 || raw[i] != raw[i - 1]) indices[output++] = raw[i];
        }
    }

    function _requireUniqueLabel(string[] memory labels, string memory expected) internal pure {
        uint256 count;
        for (uint256 i = 0; i < labels.length; i++) {
            if (_same(labels[i], expected)) count++;
        }
        require(count == 1, "native semantic checkpoint label");
    }

    function _same(string memory left, string memory right) internal pure returns (bool) {
        return keccak256(bytes(left)) == keccak256(bytes(right));
    }

    function _equalBytes(bytes memory left, bytes memory right) internal pure returns (bool) {
        return left.length == right.length && keccak256(left) == keccak256(right);
    }

    function _slice(bytes memory source, uint256 offset, uint256 length) internal pure returns (bytes memory result) {
        require(offset + length <= source.length, "native slice bounds");
        result = new bytes(length);
        for (uint256 i = 0; i < length; i++) {
            result[i] = source[offset + i];
        }
    }

    function _readBytes32(bytes memory encoded) internal pure returns (bytes32 value) {
        require(encoded.length == 32, "bytes32 length");
        assembly {
            value := mload(add(encoded, 0x20))
        }
    }

    function _ceilLog2(uint256 value) internal pure returns (uint256 bits) {
        require(value != 0, "zero log2 input");
        value--;
        while (value != 0) {
            bits++;
            value >>= 1;
        }
    }
}
