// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

/// @dev Gas-profiling probe. `mark(id)` records `gasleft()` and ships it to the forge console
/// via a 36-byte `log(uint256)` payload written into free memory *without* bumping the free
/// pointer (allowed by the memory-safe rules), so a mark costs a near-constant ~150-250 gas.
/// Encoded word: kind(8 bits) | id(24 bits) | freePtr(64 bits) | gasleft(160 bits).
/// Counting probes are compiled out unless COUNTING is true.
library GasProbe {
    bool internal constant COUNTING = false; // PROBE_COUNTING_FLAG

    function _markView(uint256 id) private view {
        assembly ("memory-safe") {
            let g := gas()
            let ptr := mload(0x40)
            mstore(ptr, shl(224, 0xf82c50f1))
            mstore(
                add(ptr, 4),
                or(or(shl(248, 1), shl(224, and(id, 0xffffff))), or(shl(160, and(ptr, 0xffffffffffffffff)), g))
            )
            pop(staticcall(gas(), 0x000000000000000000636F6e736F6c652e6c6f67, ptr, 36, 0, 0))
        }
    }

    function _countView(uint256 kind, uint256 id, uint256 a, uint256 b) private view {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, shl(224, 0xf82c50f1))
            mstore(
                add(ptr, 4),
                or(
                    or(shl(248, kind), shl(224, and(id, 0xffffff))),
                    or(shl(96, and(a, 0xffffffffffffffffffffffffffffffff)), and(b, 0xffffffffffffffffffffffff))
                )
            )
            pop(staticcall(gas(), 0x000000000000000000636F6e736F6c652e6c6f67, ptr, 36, 0, 0))
        }
    }

    function _castMark(function(uint256) internal view fnIn)
        private
        pure
        returns (function(uint256) internal pure fnOut)
    {
        assembly {
            fnOut := fnIn
        }
    }

    function _castCount(function(uint256, uint256, uint256, uint256) internal view fnIn)
        private
        pure
        returns (function(uint256, uint256, uint256, uint256) internal pure fnOut)
    {
        assembly {
            fnOut := fnIn
        }
    }

    /// @dev Timing checkpoint.
    function mark(uint256 id) internal pure {
        _castMark(_markView)(id);
    }

    /// @dev `n` keccak256 invocations of `len` bytes each (kind 2).
    function keccakCount(uint256 id, uint256 n, uint256 len) internal pure {
        if (!COUNTING) return;
        _castCount(_countView)(2, id, n, len);
    }

    /// @dev `n` full Ext3 x Ext3 multiplications (9 mulmod each) (kind 3).
    function ext3Count(uint256 id, uint256 n) internal pure {
        if (!COUNTING) return;
        _castCount(_countView)(3, id, n, 0);
    }

    /// @dev `n` Ext3 x base-scalar multiplications (3 mulmod each) (kind 4).
    function scalarCount(uint256 id, uint256 n) internal pure {
        if (!COUNTING) return;
        _castCount(_countView)(4, id, n, 0);
    }

    /// @dev `n` base-field mulmod (kind 5).
    function baseCount(uint256 id, uint256 n) internal pure {
        if (!COUNTING) return;
        _castCount(_countView)(5, id, n, 0);
    }
}
