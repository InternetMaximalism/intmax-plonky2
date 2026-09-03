// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {Keccak256Chain} from "../src/spongefish/Keccak256Chain.sol";
import {SpongefishMerkle} from "../src/spongefish/SpongefishMerkle.sol";
import {SpongefishWhir} from "../src/spongefish/SpongefishWhir.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";

contract WhirAssemblyProductionHarness {
    function challengeIndices(bytes32 state, uint64 counter, uint256 numLeaves, uint256 count)
        external
        pure
        returns (uint256[] memory indices, uint64 nextCounter)
    {
        SpongefishWhir.TranscriptState memory ts;
        ts.sponge.state = state;
        ts.sponge.squeezeCounter = counter;
        indices = SpongefishWhirVerify._challengeIndices(ts, numLeaves, count);
        nextCounter = ts.sponge.squeezeCounter;
    }

    function processMerkleLayer(
        uint256[] memory indices,
        bytes32[] memory hashes,
        bytes calldata hints,
        uint256 hintOffset
    ) external pure returns (uint256[] memory nextIndices, bytes32[] memory nextHashes, uint256 nextHintOffset) {
        nextIndices = new uint256[](indices.length);
        nextHashes = new bytes32[](hashes.length);
        SpongefishMerkle.CalldataBytes memory view_ = SpongefishMerkle.CalldataBytes({offset: 0, length: hints.length});
        assembly ("memory-safe") {
            mstore(view_, hints.offset)
        }
        uint256 nextLength;
        (nextLength, nextHintOffset) =
            SpongefishMerkle._processLayerInto(indices, hashes, nextIndices, nextHashes, view_, hintOffset);
        assembly ("memory-safe") {
            mstore(nextIndices, nextLength)
            mstore(nextHashes, nextLength)
        }
    }
}

contract WhirAssemblyDifferentialTest is Test {
    using Keccak256Chain for Keccak256Chain.Sponge;

    WhirAssemblyProductionHarness private immutable harness = new WhirAssemblyProductionHarness();
    bytes32 private constant STATE = keccak256("whir-assembly-differential-v2");

    function test_challengeIndicesMatchesReferenceAtDomainBoundaries() external view {
        uint256[7] memory leaves = [
            uint256(1),
            uint256(2),
            uint256(1) << 8,
            uint256(1) << 9,
            uint256(1) << 16,
            uint256(1) << 17,
            uint256(1) << 25
        ];
        uint256[3] memory counts = [uint256(0), uint256(1), uint256(32)];
        for (uint256 domain = 0; domain < leaves.length; ++domain) {
            for (uint256 countIndex = 0; countIndex < counts.length; ++countIndex) {
                _assertChallengeCase(STATE, 17, leaves[domain], counts[countIndex]);
            }
        }
    }

    function test_challengeIndicesDuplicateHeavyMatchesReference() external view {
        _assertChallengeCase(STATE, 0, 1, 64);
        (uint256[] memory actual, uint64 nextCounter) = harness.challengeIndices(STATE, 9, 2, 64);
        (uint256[] memory expected, uint64 expectedCounter) = _referenceChallengeIndices(STATE, 9, 2, 64);
        _assertUintArrayEq(actual, expected);
        assertEq(nextCounter, expectedCounter);
        assertEq(actual.length, 2, "two-leaf duplicate compaction");
    }

    function test_challengeIndicesCounterBoundaryIsExact() external view {
        _assertChallengeCase(STATE, type(uint64).max - 1, 2, 1);
        (, uint64 nextCounter) = harness.challengeIndices(STATE, type(uint64).max, 1, 100);
        assertEq(nextCounter, type(uint64).max, "one-leaf branch consumes no entropy");
    }

    function test_challengeIndicesRejectsCounterOverflow() external {
        vm.expectRevert(InvalidMleProof.selector);
        harness.challengeIndices(STATE, type(uint64).max, 2, 1);

        vm.expectRevert(InvalidMleProof.selector);
        harness.challengeIndices(STATE, type(uint64).max - 1, uint256(1) << 9, 1);
    }

    function test_merkleLayerPairedAndLoneMatchesReference() external view {
        uint256[] memory indices = new uint256[](3);
        indices[0] = 0;
        indices[1] = 1;
        indices[2] = 4;
        bytes32[] memory hashes = _hashes(3, "mixed");
        bytes memory hints = abi.encodePacked(bytes32(uint256(0x4444)));
        _assertMerkleCase(indices, hashes, hints, 0);
    }

    function test_merkleLayerAllPairedMatchesReference() external view {
        uint256[] memory indices = new uint256[](4);
        indices[0] = 0;
        indices[1] = 1;
        indices[2] = 2;
        indices[3] = 3;
        _assertMerkleCase(indices, _hashes(4, "paired"), "", 0);
    }

    function test_merkleLayerSingleOddWithNonzeroHintOffsetMatchesReference() external view {
        uint256[] memory indices = new uint256[](1);
        indices[0] = 5;
        bytes memory hints = abi.encodePacked(bytes7("prefix!"), bytes32(uint256(0x5555)));
        _assertMerkleCase(indices, _hashes(1, "single"), hints, 7);
    }

    function test_merkleLayerRejectsShortHintAndBadOffsets() external {
        uint256[] memory indices = new uint256[](1);
        indices[0] = 0;
        bytes32[] memory hashes = _hashes(1, "bounds");
        bytes memory shortHint = new bytes(31);

        vm.expectRevert(InvalidMleProof.selector);
        harness.processMerkleLayer(indices, hashes, shortHint, 0);

        bytes memory exactHint = new bytes(32);
        vm.expectRevert(InvalidMleProof.selector);
        harness.processMerkleLayer(indices, hashes, exactHint, 1);

        vm.expectRevert(InvalidMleProof.selector);
        harness.processMerkleLayer(indices, hashes, exactHint, 33);
    }

    function _assertChallengeCase(bytes32 state, uint64 counter, uint256 leaves, uint256 count) private view {
        (uint256[] memory actual, uint64 actualCounter) = harness.challengeIndices(state, counter, leaves, count);
        (uint256[] memory expected, uint64 expectedCounter) = _referenceChallengeIndices(state, counter, leaves, count);
        _assertUintArrayEq(actual, expected);
        assertEq(actualCounter, expectedCounter, "squeeze counter");
        for (uint256 i = 0; i < actual.length; ++i) {
            assertLt(actual[i], leaves, "query range");
            if (i != 0) assertLt(actual[i - 1], actual[i], "strict sorted dedup");
        }
    }

    function _referenceChallengeIndices(bytes32 state, uint64 counter, uint256 numLeaves, uint256 count)
        private
        pure
        returns (uint256[] memory indices, uint64 nextCounter)
    {
        Keccak256Chain.Sponge memory sponge;
        sponge.state = state;
        sponge.squeezeCounter = counter;
        if (count == 0) return (new uint256[](0), counter);
        if (numLeaves == 1) {
            indices = new uint256[](1);
            return (indices, counter);
        }

        uint256 sizeBytes = (_log2(numLeaves) + 7) / 8;
        indices = new uint256[](count);
        for (uint256 i = 0; i < count; ++i) {
            uint256 value;
            for (uint256 j = 0; j < sizeBytes; ++j) {
                value = (value << 8) | uint256(sponge.squeezeByte());
            }
            indices[i] = value % numLeaves;
        }
        _referenceSortAndDedup(indices);
        nextCounter = sponge.squeezeCounter;
    }

    function _referenceSortAndDedup(uint256[] memory values) private pure {
        for (uint256 i = 1; i < values.length; ++i) {
            uint256 value = values[i];
            uint256 cursor = i;
            while (cursor != 0 && values[cursor - 1] > value) {
                values[cursor] = values[cursor - 1];
                --cursor;
            }
            values[cursor] = value;
        }
        if (values.length < 2) return;
        uint256 write = 1;
        for (uint256 i = 1; i < values.length; ++i) {
            if (values[i] != values[i - 1]) values[write++] = values[i];
        }
        assembly ("memory-safe") {
            mstore(values, write)
        }
    }

    function _assertMerkleCase(
        uint256[] memory indices,
        bytes32[] memory hashes,
        bytes memory hints,
        uint256 hintOffset
    ) private view {
        (uint256[] memory actualIndices, bytes32[] memory actualHashes, uint256 actualOffset) =
            harness.processMerkleLayer(indices, hashes, hints, hintOffset);
        (uint256[] memory expectedIndices, bytes32[] memory expectedHashes, uint256 expectedOffset) =
            _referenceMerkleLayer(indices, hashes, hints, hintOffset);
        _assertUintArrayEq(actualIndices, expectedIndices);
        _assertBytes32ArrayEq(actualHashes, expectedHashes);
        assertEq(actualOffset, expectedOffset, "hint cursor");
    }

    function _referenceMerkleLayer(
        uint256[] memory indices,
        bytes32[] memory hashes,
        bytes memory hints,
        uint256 hintOffset
    ) private pure returns (uint256[] memory nextIndices, bytes32[] memory nextHashes, uint256 nextOffset) {
        nextIndices = new uint256[](indices.length);
        nextHashes = new bytes32[](hashes.length);
        nextOffset = hintOffset;
        uint256 read;
        uint256 write;
        while (read < indices.length) {
            uint256 index = indices[read];
            bytes32 current = hashes[read];
            bytes32 left;
            bytes32 right;
            if (read + 1 < indices.length && indices[read + 1] == (index ^ 1)) {
                if ((index & 1) == 0) {
                    left = current;
                    right = hashes[read + 1];
                } else {
                    left = hashes[read + 1];
                    right = current;
                }
                read += 2;
            } else {
                require(nextOffset <= hints.length && hints.length - nextOffset >= 32);
                bytes32 sibling;
                assembly ("memory-safe") {
                    sibling := mload(add(add(hints, 0x20), nextOffset))
                }
                nextOffset += 32;
                if ((index & 1) == 0) {
                    left = current;
                    right = sibling;
                } else {
                    left = sibling;
                    right = current;
                }
                ++read;
            }
            nextIndices[write] = index >> 1;
            nextHashes[write] = keccak256(abi.encodePacked(left, right));
            ++write;
        }
        assembly ("memory-safe") {
            mstore(nextIndices, write)
            mstore(nextHashes, write)
        }
    }

    function _hashes(uint256 count, string memory domain) private pure returns (bytes32[] memory values) {
        values = new bytes32[](count);
        for (uint256 i = 0; i < count; ++i) {
            values[i] = keccak256(abi.encode(domain, i));
        }
    }

    function _assertUintArrayEq(uint256[] memory actual, uint256[] memory expected) private pure {
        assertEq(actual.length, expected.length, "uint array length");
        for (uint256 i = 0; i < actual.length; ++i) {
            assertEq(actual[i], expected[i], "uint array item");
        }
    }

    function _assertBytes32ArrayEq(bytes32[] memory actual, bytes32[] memory expected) private pure {
        assertEq(actual.length, expected.length, "bytes32 array length");
        for (uint256 i = 0; i < actual.length; ++i) {
            assertEq(actual[i], expected[i], "bytes32 array item");
        }
    }

    function _log2(uint256 value) private pure returns (uint256 result) {
        while (value > 1) {
            value >>= 1;
            ++result;
        }
    }
}
