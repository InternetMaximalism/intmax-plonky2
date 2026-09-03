// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {InvalidMleProof} from "./MleProofErrors.sol";

/// @title PackedClaimLib
/// @notice Legacy-v1 evaluator for a zero-padded constituent-claim vector.
/// @dev V2 uses `PackedClaimExt3`, which preserves all three limbs of every
/// constituent. This legacy helper is retained only for migration and negative
/// tests. Kept behind an external-library boundary so the chain-pinned verifier remains
/// deployable under EIP-170. The dense layout is LSB-first: adjacent entries are folded
/// by indexPoint[0], then indexPoint[1], and so on.
library PackedClaimLib {
    uint256 private constant P = 0xFFFFFFFF00000001;
    uint256 private constant MAX_WIDTH = 160;
    uint256 private constant MAX_INDEX_BITS = 8;

    function fold(
        uint256[] memory values,
        uint256 width,
        GoldilocksExt3.Ext3[] memory indexPoint
    ) external pure returns (GoldilocksExt3.Ext3 memory result) {
        if (width == 0 || width > MAX_WIDTH || values.length > width || indexPoint.length > MAX_INDEX_BITS) {
            revert InvalidMleProof();
        }
        uint256 capacity = uint256(1) << indexPoint.length;
        if (capacity < width || (capacity >> 1) >= width) revert InvalidMleProof();

        GoldilocksExt3.Ext3[] memory layer = new GoldilocksExt3.Ext3[](capacity);
        for (uint256 i = 0; i < values.length; i++) {
            if (values[i] >= P) revert InvalidMleProof();
            layer[i] = GoldilocksExt3.Ext3(uint64(values[i]), 0, 0);
        }
        for (uint256 i = 0; i < indexPoint.length; ++i) {
            if (
                uint256(indexPoint[i].c0) >= P || uint256(indexPoint[i].c1) >= P
                    || uint256(indexPoint[i].c2) >= P
            ) revert InvalidMleProof();
        }
        uint256 active = capacity;
        for (uint256 bit = 0; bit < indexPoint.length; bit++) {
            uint256 next = active >> 1;
            for (uint256 i = 0; i < next; i++) {
                GoldilocksExt3.Ext3 memory even = layer[2 * i];
                GoldilocksExt3.Ext3 memory delta =
                    GoldilocksExt3.sub(layer[2 * i + 1], even);
                layer[i] = GoldilocksExt3.add(
                    even,
                    GoldilocksExt3.mul(indexPoint[bit], delta)
                );
            }
            active = next;
        }
        result = layer[0];
    }
}
