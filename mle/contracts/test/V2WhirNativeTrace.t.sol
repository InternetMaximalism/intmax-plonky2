// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {Keccak256Chain} from "../src/spongefish/Keccak256Chain.sol";

/// @notice Byte-exact replay of the Rust production grouped-WHIR preflight for
/// the canonical v2 cross-language proof.
contract V2WhirNativeTraceTest is Test {
    string internal constant FIXTURE = "test/fixtures/v2_cross_language.json";
    string internal constant CASE = ".cases[0]";
    uint256 internal constant CHECKPOINTS = 260;
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

    function test_replaysEveryCanonicalV2WhirNativeCheckpointByteExactly() external view {
        string memory json = vm.readFile(FIXTURE);
        Golden memory golden = _loadGolden(json);
        (bytes memory narg, bytes memory hints) = _extractWhirStreams(json);

        require(golden.labels.length == CHECKPOINTS, "v2 WHIR checkpoint count");
        require(_same(golden.labels[0], "init.protocol"), "v2 WHIR protocol label");
        require(_same(golden.labels[1], "init.session"), "v2 WHIR session label");
        require(_same(golden.labels[2], "init.instance"), "v2 WHIR instance label");
        require(
            _equalBytes(
                golden.eventBytes[0], vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.whirProtocolId"))
            ),
            "v2 WHIR protocol bytes"
        );
        require(
            _equalBytes(
                golden.eventBytes[1], vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.whirSessionId"))
            ),
            "v2 WHIR session bytes"
        );
        require(golden.eventBytes[2].length == 0, "v2 WHIR nonempty instance");

        _assertEvaluationOrder(json, golden);
        _replayNativeTrace(json, golden, narg, hints);
    }

    function _assertEvaluationOrder(string memory json, Golden memory golden) private pure {
        for (uint256 claim = 0; claim < 6; ++claim) {
            string memory label = string.concat("initial.statement.claim[", vm.toString(claim), "]");
            uint256 checkpoint = _uniqueLabel(golden.labels, label);
            require(golden.kinds[checkpoint] == ABSORB, "v2 WHIR claim kind");
            require(
                _equalBytes(
                    golden.eventBytes[checkpoint],
                    _encodeExt3Narg(json, string.concat(CASE, ".whirEvaluations[", vm.toString(claim), "]"))
                ),
                "v2 WHIR claim bytes/order"
            );
            require(
                vm.parseJsonUint(json, string.concat(CASE, ".packedClaims[", vm.toString(claim), "].pointIndex"))
                    == claim / 3,
                "v2 WHIR point-major claim order"
            );
            require(
                vm.parseJsonUint(json, string.concat(CASE, ".packedClaims[", vm.toString(claim), "].groupIndex"))
                    == claim % 3,
                "v2 WHIR group-minor claim order"
            );
            if (claim < 5) {
                require(
                    _equalBytes(
                        golden.eventBytes[checkpoint],
                        _encodeExt3Narg(json, string.concat(CASE, ".packedClaims[", vm.toString(claim), "].value"))
                    ),
                    "v2 bound packed claim/Rust evaluation mismatch"
                );
            }
        }
    }

    function _replayNativeTrace(string memory json, Golden memory golden, bytes memory narg, bytes memory hints)
        private
        pure
    {
        Keccak256Chain.Sponge memory sponge = Keccak256Chain.init();
        uint256 nargPosition;
        uint256 hintPosition;
        uint256 queryCursor;
        bytes memory pendingQueryEntropy;
        uint256[6] memory kindCounts;

        for (uint256 checkpoint = 0; checkpoint < golden.labels.length; ++checkpoint) {
            uint256 kind = golden.kinds[checkpoint];
            require(kind <= EOF_EVENT, "v2 WHIR event kind");
            ++kindCounts[kind];

            if (kind == ABSORB) {
                uint256 nextNargPosition = golden.nargPositions[checkpoint];
                if (nextNargPosition == nargPosition) {
                    require(checkpoint < 3, "v2 WHIR non-NARG absorb after init");
                } else {
                    uint256 consumed = nextNargPosition - nargPosition;
                    require(consumed == golden.eventBytes[checkpoint].length, "v2 WHIR NARG event length");
                    require(
                        _equalBytes(_slice(narg, nargPosition, consumed), golden.eventBytes[checkpoint]),
                        "v2 WHIR NARG event bytes"
                    );
                    nargPosition = nextNargPosition;
                }
                Keccak256Chain.absorb(sponge, golden.eventBytes[checkpoint]);
            } else {
                require(golden.nargPositions[checkpoint] == nargPosition, "v2 WHIR NARG cursor drift");
            }

            if (kind == SQUEEZE || kind == QUERY_SQUEEZE) {
                bytes memory actual = Keccak256Chain.squeeze(sponge, golden.eventBytes[checkpoint].length);
                require(_equalBytes(actual, golden.eventBytes[checkpoint]), "v2 WHIR squeezed bytes");
                if (kind == QUERY_SQUEEZE) pendingQueryEntropy = bytes.concat(pendingQueryEntropy, actual);
            } else if (kind == QUERY_INDICES) {
                require(queryCursor < golden.queryCheckpointIndices.length, "v2 WHIR unexpected query batch");
                require(golden.queryCheckpointIndices[queryCursor] == checkpoint, "v2 WHIR query checkpoint index");
                require(_equalBytes(pendingQueryEntropy, golden.eventBytes[checkpoint]), "v2 WHIR query entropy batch");
                _assertQueryIndices(json, golden, queryCursor, pendingQueryEntropy);
                pendingQueryEntropy = new bytes(0);
                ++queryCursor;
            }

            if (kind == HINT) {
                uint256 nextHintPosition = golden.hintPositions[checkpoint];
                require(nextHintPosition > hintPosition, "v2 WHIR empty hint segment");
                bytes memory segment = _slice(hints, hintPosition, nextHintPosition - hintPosition);
                require(golden.eventBytes[checkpoint].length == 32, "v2 WHIR hint digest width");
                require(keccak256(segment) == _readBytes32(golden.eventBytes[checkpoint]), "v2 WHIR hint bytes");
                hintPosition = nextHintPosition;
            } else {
                require(golden.hintPositions[checkpoint] == hintPosition, "v2 WHIR hint cursor drift");
            }

            require(sponge.state == golden.spongeStates[checkpoint], "v2 WHIR sponge state");
            require(uint256(sponge.squeezeCounter) == golden.squeezeCounters[checkpoint], "v2 WHIR squeeze counter");
        }

        require(kindCounts[ABSORB] == 52, "v2 WHIR absorb count");
        require(kindCounts[SQUEEZE] == 19, "v2 WHIR squeeze count");
        require(kindCounts[QUERY_SQUEEZE] == 182, "v2 WHIR query squeeze count");
        require(kindCounts[QUERY_INDICES] == 2, "v2 WHIR query batch count");
        require(kindCounts[HINT] == 4, "v2 WHIR hint count");
        require(kindCounts[EOF_EVENT] == 1, "v2 WHIR EOF count");
        require(golden.kinds[golden.kinds.length - 1] == EOF_EVENT, "v2 WHIR final event");
        require(nargPosition == narg.length, "v2 WHIR trailing NARG");
        require(hintPosition == hints.length, "v2 WHIR trailing hints");
        require(pendingQueryEntropy.length == 0, "v2 WHIR pending query entropy");
        require(queryCursor == golden.queryCheckpointIndices.length, "v2 WHIR query count");
        require(golden.queryOffsets.length == queryCursor + 1, "v2 WHIR query offset shape");
        require(golden.queryOffsets[queryCursor] == golden.queryIndices.length, "v2 WHIR query tail");
    }

    function _assertQueryIndices(string memory json, Golden memory golden, uint256 query, bytes memory entropy)
        private
        pure
    {
        uint256 codewordLength;
        uint256 sampleCount;
        if (query == 0) {
            codewordLength = vm.parseJsonUint(json, string.concat(CASE, ".whirParams.initialCodewordLength"));
            sampleCount = vm.parseJsonUint(json, string.concat(CASE, ".whirParams.inDomainSamples"));
        } else {
            string memory round = string.concat(CASE, ".whirParams.rounds[", vm.toString(query - 1), "]");
            codewordLength = vm.parseJsonUint(json, string.concat(round, ".codewordLength"));
            sampleCount = vm.parseJsonUint(json, string.concat(round, ".inDomainSamples"));
        }
        uint256[] memory indices = _deriveQueryIndices(codewordLength, sampleCount, entropy);
        uint256 begin = golden.queryOffsets[query];
        uint256 end = golden.queryOffsets[query + 1];
        require(indices.length == end - begin, "v2 WHIR query index count");
        for (uint256 i = 0; i < indices.length; ++i) {
            require(indices[i] == golden.queryIndices[begin + i], "v2 WHIR derived query index");
        }
    }

    function _deriveQueryIndices(uint256 codewordLength, uint256 sampleCount, bytes memory entropy)
        private
        pure
        returns (uint256[] memory indices)
    {
        require(codewordLength != 0 && codewordLength & (codewordLength - 1) == 0, "v2 WHIR query domain");
        uint256 bytesPerIndex = (_ceilLog2(codewordLength) + 7) / 8;
        require(entropy.length == sampleCount * bytesPerIndex, "v2 WHIR query entropy length");
        uint256[] memory raw = new uint256[](sampleCount);
        for (uint256 i = 0; i < sampleCount; ++i) {
            uint256 value;
            for (uint256 j = 0; j < bytesPerIndex; ++j) {
                value = (value << 8) | uint8(entropy[i * bytesPerIndex + j]);
            }
            raw[i] = value % codewordLength;
        }
        for (uint256 i = 1; i < raw.length; ++i) {
            uint256 value = raw[i];
            uint256 cursor = i;
            while (cursor != 0 && raw[cursor - 1] > value) {
                raw[cursor] = raw[cursor - 1];
                --cursor;
            }
            raw[cursor] = value;
        }
        uint256 unique;
        for (uint256 i = 0; i < raw.length; ++i) {
            if (i == 0 || raw[i] != raw[i - 1]) ++unique;
        }
        indices = new uint256[](unique);
        uint256 output;
        for (uint256 i = 0; i < raw.length; ++i) {
            if (i == 0 || raw[i] != raw[i - 1]) indices[output++] = raw[i];
        }
    }

    function _loadGolden(string memory json) private pure returns (Golden memory golden) {
        string memory path = string.concat(CASE, ".whirNative");
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
        require(golden.kinds.length == checkpoints, "v2 WHIR kinds shape");
        require(golden.nargPositions.length == checkpoints, "v2 WHIR NARG shape");
        require(golden.hintPositions.length == checkpoints, "v2 WHIR hint shape");
        require(golden.spongeStates.length == checkpoints, "v2 WHIR states shape");
        require(golden.squeezeCounters.length == checkpoints, "v2 WHIR counters shape");
        require(golden.eventBytes.length == checkpoints, "v2 WHIR bytes shape");
        require(golden.queryOffsets.length == golden.queryCheckpointIndices.length + 1, "v2 WHIR query offsets shape");
        require(golden.queryOffsets[0] == 0, "v2 WHIR query offset origin");
    }

    function _extractWhirStreams(string memory json) private pure returns (bytes memory narg, bytes memory hints) {
        bytes memory compact = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));
        uint256 offset = 8 + 8 + 4;
        offset += 8 * vm.parseJsonUint(json, string.concat(CASE, ".compactShape.circuitDigestLen"));
        offset += 8 * vm.parseJsonUint(json, string.concat(CASE, ".compactShape.publicInputsLen"));
        offset += 3 * 32;
        uint256 nargLength = _readU32Le(compact, offset);
        offset += 4;
        narg = _slice(compact, offset, nargLength);
        offset += nargLength;
        uint256 hintLength = _readU32Le(compact, offset);
        offset += 4;
        hints = _slice(compact, offset, hintLength);
    }

    function _encodeExt3Narg(string memory json, string memory path) private pure returns (bytes memory encoded) {
        string[] memory limbs = vm.parseJsonStringArray(json, path);
        require(limbs.length == 3, "v2 WHIR Ext3 limb count");
        encoded = new bytes(24);
        for (uint256 limb = 0; limb < 3; ++limb) {
            uint256 value = vm.parseUint(limbs[limb]);
            for (uint256 byteIndex = 0; byteIndex < 8; ++byteIndex) {
                encoded[8 * limb + byteIndex] = bytes1(uint8(value >> (8 * byteIndex)));
            }
        }
    }

    function _uniqueLabel(string[] memory labels, string memory expected) private pure returns (uint256 found) {
        uint256 count;
        for (uint256 i = 0; i < labels.length; ++i) {
            if (_same(labels[i], expected)) {
                found = i;
                ++count;
            }
        }
        require(count == 1, "v2 WHIR semantic label count");
    }

    function _same(string memory left, string memory right) private pure returns (bool) {
        return keccak256(bytes(left)) == keccak256(bytes(right));
    }

    function _equalBytes(bytes memory left, bytes memory right) private pure returns (bool) {
        return left.length == right.length && keccak256(left) == keccak256(right);
    }

    function _slice(bytes memory source, uint256 offset, uint256 length) private pure returns (bytes memory result) {
        require(offset + length <= source.length, "v2 WHIR byte slice bounds");
        result = new bytes(length);
        for (uint256 i = 0; i < length; ++i) {
            result[i] = source[offset + i];
        }
    }

    function _readBytes32(bytes memory encoded) private pure returns (bytes32 value) {
        require(encoded.length == 32, "v2 WHIR bytes32 width");
        assembly ("memory-safe") {
            value := mload(add(encoded, 0x20))
        }
    }

    function _readU32Le(bytes memory encoded, uint256 offset) private pure returns (uint256 value) {
        require(offset + 4 <= encoded.length, "v2 WHIR u32 bounds");
        value = uint8(encoded[offset]) | (uint256(uint8(encoded[offset + 1])) << 8)
            | (uint256(uint8(encoded[offset + 2])) << 16) | (uint256(uint8(encoded[offset + 3])) << 24);
    }

    function _ceilLog2(uint256 value) private pure returns (uint256 bits) {
        require(value != 0, "v2 WHIR zero log2 input");
        --value;
        while (value != 0) {
            ++bits;
            value >>= 1;
        }
    }
}
