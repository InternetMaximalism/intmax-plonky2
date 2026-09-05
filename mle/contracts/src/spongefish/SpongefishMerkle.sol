// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {InvalidMleProof} from "../MleProofErrors.sol";

/// @title SpongefishMerkle
/// @notice Merkle tree verification matching WizardOfMenlo/whir's layered decommitment format.
///
///   Unlike OpenZeppelin multi-proof, this uses a simpler per-layer scheme:
///   - Indices are sorted and deduplicated
///   - For each layer, sibling hashes come from the "hints" buffer
///   - Neighbors (a, a^1) that are both present merge without needing a hint
///   - Hash function is Keccak256 (matching intmax3's hash_id: KECCAK)
library SpongefishMerkle {
    error MerkleVerificationFailed();

    /// @dev Read-only view over one ABI calldata byte string.
    struct CalldataBytes {
        uint256 offset;
        uint256 length;
    }

    /// @notice Verify a Merkle opening proof.
    /// @param root         Expected root hash
    /// @param numLayers    Number of tree layers (= log2(num_leaves))
    /// @param indices      Sorted, deduplicated leaf indices
    /// @param leafHashes   Leaf hashes corresponding to indices
    /// @param hints        Sibling hashes (decommitments), consumed sequentially
    /// @param hintOffset   Starting offset in hints
    /// @return newHintOffset  Number of hint bytes consumed
    function verify(
        bytes32 root,
        uint256 numLayers,
        uint256[] memory indices,
        bytes32[] memory leafHashes,
        CalldataBytes memory hints,
        uint256 hintOffset
    ) internal pure returns (uint256 newHintOffset) {
        if (indices.length != leafHashes.length) revert InvalidMleProof();
        if (indices.length == 0) return hintOffset;

        // SECURITY: Enforce strict ascending order to prevent unsorted or duplicate indices.
        // Without this check, a prover can force sibling detection to fail (treating true
        // siblings as lone nodes), then supply arbitrary hint bytes as sibling hashes.
        for (uint256 i = 1; i < indices.length; i++) {
            if (indices[i] <= indices[i - 1]) revert InvalidMleProof();
        }

        uint256[] memory curIndices = indices;
        bytes32[] memory curHashes = leafHashes;
        uint256[] memory nextIndices = new uint256[](indices.length);
        bytes32[] memory nextHashes = new bytes32[](leafHashes.length);
        newHintOffset = hintOffset;

        for (uint256 layer = 0; layer < numLayers; layer++) {
            uint256 nextLen;
            // Issue 3 fix: _processLayerInto now returns the updated hint offset,
            // eliminating the separate loneCount accounting that could drift from reality.
            (nextLen, newHintOffset) =
                _processLayerInto(curIndices, curHashes, nextIndices, nextHashes, hints, newHintOffset);

            assembly {
                mstore(nextIndices, nextLen)
                mstore(nextHashes, nextLen)
            }

            (curIndices, nextIndices) = (nextIndices, curIndices);
            (curHashes, nextHashes) = (nextHashes, curHashes);
        }

        // Should be left with a single root
        if (curIndices.length != 1 || curIndices[0] != 0 || curHashes[0] != root) {
            revert InvalidMleProof();
        }
    }

    /// @dev Process one Merkle tree layer: merge siblings, read hints for lone nodes.
    ///      Returns (nextLen, updatedHintOff) — the caller uses the returned hint offset
    ///      directly, avoiding a separate loneCount recomputation that could drift.
    function _processLayerInto(
        uint256[] memory curIndices,
        bytes32[] memory curHashes,
        uint256[] memory nextIndices,
        bytes32[] memory nextHashes,
        CalldataBytes memory hints,
        uint256 hintOff
    ) internal pure returns (uint256 nextLen, uint256 newHintOff) {
        uint256 n = curIndices.length;
        assembly ("memory-safe") {
            let currentIndexData := add(curIndices, 0x20)
            let currentHashData := add(curHashes, 0x20)
            let nextIndexData := add(nextIndices, 0x20)
            let nextHashData := add(nextHashes, 0x20)
            let hintsBase := mload(hints)
            let hintsLength := mload(add(hints, 0x20))
            newHintOff := hintOff

            for { let i := 0 } lt(i, n) {} {
                let a := mload(add(currentIndexData, mul(i, 0x20)))
                let currentHash := mload(add(currentHashData, mul(i, 0x20)))
                let left := currentHash
                let right := 0
                let paired := 0
                if lt(add(i, 1), n) {
                    paired := eq(mload(add(currentIndexData, mul(add(i, 1), 0x20))), xor(a, 1))
                }

                switch paired
                case 1 {
                    let neighborHash := mload(add(currentHashData, mul(add(i, 1), 0x20)))
                    if and(a, 1) {
                        left := neighborHash
                        right := currentHash
                    }
                    if iszero(and(a, 1)) { right := neighborHash }
                    i := add(i, 2)
                }
                default {
                    // The descriptor bounds the exact hints byte slice. Never
                    // allow calldataload to reach a later ABI argument.
                    if or(gt(newHintOff, hintsLength), gt(32, sub(hintsLength, newHintOff))) {
                        mstore(0x00, shl(224, 0xf0783a66))
                        revert(0x00, 0x04)
                    }
                    let sibling := calldataload(add(hintsBase, newHintOff))
                    newHintOff := add(newHintOff, 32)
                    if and(a, 1) {
                        left := sibling
                        right := currentHash
                    }
                    if iszero(and(a, 1)) { right := sibling }
                    i := add(i, 1)
                }

                mstore(0x00, left)
                mstore(0x20, right)
                mstore(add(nextIndexData, mul(nextLen, 0x20)), shr(1, a))
                mstore(add(nextHashData, mul(nextLen, 0x20)), keccak256(0x00, 0x40))
                nextLen := add(nextLen, 1)
            }
        }
    }
}
