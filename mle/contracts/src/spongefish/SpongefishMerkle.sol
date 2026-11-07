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
///
///   Internally a layer is a packed array of (index, hash) 64-byte pairs that is reduced in
///   place: the parent of position k is written at position <= k after the children at
///   positions >= k have been read, so one buffer serves every layer.
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
        uint256 n = indices.length;
        if (n != leafHashes.length) revert InvalidMleProof();
        if (n == 0) return hintOffset;

        uint256 pairs = _packLayer(indices, leafHashes, n);
        (uint256 hc, uint256 hcEnd) = _hintCursor(hints, hintOffset);
        uint256 hcStart = hc;
        (n, hc) = _reduceLayers(pairs, n, hc, hcEnd, numLayers);
        newHintOffset = hintOffset + (hc - hcStart);

        // Should be left with a single root
        bool ok;
        assembly ("memory-safe") {
            ok := and(and(eq(n, 1), iszero(mload(pairs))), eq(mload(add(pairs, 0x20)), root))
        }
        if (!ok) revert InvalidMleProof();
    }

    /// @dev Process one Merkle tree layer: merge siblings, read hints for lone nodes.
    ///      Returns (nextLen, updatedHintOff) — the caller uses the returned hint offset
    ///      directly, avoiding a separate loneCount recomputation that could drift.
    ///      Thin wrapper over `_reduceLayer` kept for the differential tests.
    function _processLayerInto(
        uint256[] memory curIndices,
        bytes32[] memory curHashes,
        uint256[] memory nextIndices,
        bytes32[] memory nextHashes,
        CalldataBytes memory hints,
        uint256 hintOff
    ) internal pure returns (uint256 nextLen, uint256 newHintOff) {
        uint256 n = curIndices.length;
        uint256 pairs = _packLayer(curIndices, curHashes, n);
        (uint256 hc, uint256 hcEnd) = _hintCursor(hints, hintOff);
        uint256 hcStart = hc;
        (nextLen, hc) = _reduceLayers(pairs, n, hc, hcEnd, 1);
        newHintOff = hintOff + (hc - hcStart);
        assembly ("memory-safe") {
            let src := pairs
            let dst := add(nextIndices, 0x20)
            let dstH := add(nextHashes, 0x20)
            for { let i := 0 } lt(i, nextLen) { i := add(i, 1) } {
                mstore(add(dst, shl(5, i)), mload(src))
                mstore(add(dstH, shl(5, i)), mload(add(src, 0x20)))
                src := add(src, 0x40)
            }
        }
    }

    /// @dev Allocate the packed (index, hash) layer buffer (plus one spare pair so the sibling
    ///      look-ahead never reads outside the allocation) and enforce strict ascending indices.
    function _packLayer(uint256[] memory indices, bytes32[] memory hashes, uint256 n)
        private
        pure
        returns (uint256 pairs)
    {
        assembly ("memory-safe") {
            pairs := mload(0x40)
            mstore(0x40, add(pairs, shl(6, add(n, 1))))
            let ip := add(indices, 0x20)
            let hp := add(hashes, 0x20)
            let end := add(ip, shl(5, n))
            let dst := pairs
            // SECURITY: Enforce strict ascending order to prevent unsorted or duplicate indices.
            // Without this check, a prover can force sibling detection to fail (treating true
            // siblings as lone nodes), then supply arbitrary hint bytes as sibling hashes.
            let prev := mload(ip)
            mstore(dst, prev)
            mstore(add(dst, 0x20), mload(hp))
            for { ip := add(ip, 0x20) } lt(ip, end) { ip := add(ip, 0x20) } {
                let cur := mload(ip)
                if iszero(gt(cur, prev)) {
                    mstore(0x00, shl(224, 0xf0783a66))
                    revert(0x00, 0x04)
                }
                prev := cur
                hp := add(hp, 0x20)
                dst := add(dst, 0x40)
                mstore(dst, cur)
                mstore(add(dst, 0x20), mload(hp))
            }
            mstore(add(dst, 0x40), 0)
        }
    }

    /// @dev Calldata cursor over the descriptor-bounded hints slice. A start offset already past
    ///      the slice yields an empty cursor, so the first sibling read fails exactly like the
    ///      original `hintOff > length` check while no read leaves the cursor unchanged.
    function _hintCursor(CalldataBytes memory hints, uint256 hintOff) private pure returns (uint256 hc, uint256 hcEnd) {
        uint256 base = hints.offset;
        uint256 length = hints.length;
        if (hintOff > length) return (32, 0);
        return (base + hintOff, base + length);
    }

    /// @dev Reduce `n` packed (index, hash) pairs at `pairs` to their ancestors `numLayers`
    ///      levels up, in place, one layer at a time. Pairs (a, a^1) that are both present
    ///      merge without a hint; a lone node reads its sibling from calldata at `hc` (never
    ///      past `hcEnd`). Returns the remaining node count and the advanced hint cursor.
    function _reduceLayers(uint256 pairs, uint256 n, uint256 hc, uint256 hcEnd, uint256 numLayers)
        private
        pure
        returns (uint256 nextLen, uint256 newHc)
    {
        assembly ("memory-safe") {
            // Few live values keep the EVM stack shallow (no SWAP/DUP storms per node).
            function reduce(rp, end, hc_, hcEnd_) -> wp, hcOut {
                wp := rp
                hcOut := hc_
                for {} lt(rp, end) {} {
                    let a := mload(rp)
                    let current := mload(add(rp, 0x20))
                    let sibling := 0
                    rp := add(rp, 0x40)
                    // The look-ahead read at `end` stays inside the spare pair of the buffer.
                    switch and(lt(rp, end), eq(mload(rp), xor(a, 1)))
                    case 1 {
                        sibling := mload(add(rp, 0x20))
                        rp := add(rp, 0x40)
                    }
                    default {
                        // The descriptor bounds the exact hints byte slice. Never
                        // allow calldataload to reach a later ABI argument.
                        if gt(add(hcOut, 32), hcEnd_) {
                            mstore(0x00, shl(224, 0xf0783a66))
                            revert(0x00, 0x04)
                        }
                        sibling := calldataload(hcOut)
                        hcOut := add(hcOut, 32)
                    }
                    // Odd index: parent = H(sibling || current); even: H(current || sibling).
                    let slot := shl(5, and(a, 1))
                    mstore(slot, current)
                    mstore(xor(slot, 0x20), sibling)
                    mstore(wp, shr(1, a))
                    mstore(add(wp, 0x20), keccak256(0x00, 0x40))
                    wp := add(wp, 0x40)
                }
            }
            let end := add(pairs, shl(6, n))
            for { let layer := 0 } lt(layer, numLayers) { layer := add(layer, 1) } {
                end, hc := reduce(pairs, end, hc, hcEnd)
            }
            nextLen := shr(6, sub(end, pairs))
            newHc := hc
        }
    }
}
