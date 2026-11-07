// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

/// @title Keccak256Chain
/// @notice EVM-friendly Fiat-Shamir transcript using keccak256 hash chain.
///         Matches the Rust Keccak256Chain in src/transcript/keccak256_chain.rs.
///
///   absorb(input): state = keccak256(state || input), counter = 0
///   squeeze(n):    output_i = keccak256(state || "squeeze" || counter_be), counter++
///   ratchet():     state = keccak256(state || "ratchet"), counter = 0
library Keccak256Chain {
    struct Sponge {
        bytes32 state;
        uint64 squeezeCounter;
    }

    /// @notice Initialize a fresh sponge (state = 0, counter = 0).
    function init() internal pure returns (Sponge memory s) {
        // default zero-initialized
    }

    /// @notice Absorb arbitrary bytes: state = keccak256(state || input), counter = 0.
    function absorb(Sponge memory s, bytes memory input) internal pure {
        bytes32 st = s.state;
        bytes32 result;
        assembly {
            let inputLen := mload(input)
            let totalLen := add(32, inputLen)
            // Use scratch space: write state at free memory, then input data
            let scratch := mload(0x40)
            mstore(scratch, st)
            // Copy input bytes after state
            let src := add(input, 0x20)
            let dst := add(scratch, 32)
            for { let i := 0 } lt(i, inputLen) { i := add(i, 32) } {
                mstore(add(dst, i), mload(add(src, i)))
            }
            result := keccak256(scratch, totalLen)
        }
        s.state = result;
        s.squeezeCounter = 0;
    }

    /// @notice Squeeze n bytes: each 32-byte block = keccak256(state || "squeeze" || counter_be).
    ///         Counter is big-endian uint64 (matches Rust's .to_be_bytes()).
    ///         Uses SHA3 opcode directly via assembly for gas efficiency.
    function squeeze(Sponge memory s, uint256 n) internal pure returns (bytes memory output) {
        output = new bytes(n);
        uint256 counter = uint256(s.squeezeCounter);
        // SECURITY: Prevent squeezeCounter overflow. Each 32-byte block increments the
        // counter by 1. If the counter wraps, subsequent squeezes reuse earlier counter
        // values, producing repeated challenge bytes and breaking Fiat-Shamir security.
        uint256 blocksNeeded = (n + 31) / 32;
        require(counter + blocksNeeded <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        bytes32 st = s.state;
        assembly {
            let scratch := mload(0x40)
            mstore(scratch, st)
            let dst := add(output, 0x20)
            let offset := 0
            for {} lt(offset, n) {} {
                let tagWord := or(
                    shl(200, 0x73717565657a65),
                    shl(136, counter)
                )
                mstore(add(scratch, 32), tagWord)
                let h := keccak256(scratch, 47)
                counter := add(counter, 1)

                // Always mstore the full 32 bytes — safe because bytes memory has
                // at least 32 bytes of padding after its length due to Solidity ABI.
                // For the last partial chunk, the excess bytes overwrite padding
                // which will not be read (output.length is already set correctly).
                mstore(add(dst, offset), h)
                offset := add(offset, 32)
            }
        }
        s.squeezeCounter = uint64(counter);
    }

    /// @notice Squeeze exactly 1 byte. Optimized hot path for challenge_indices.
    function squeezeByte(Sponge memory s) internal pure returns (uint8 b) {
        bytes32 st = s.state;
        uint256 counter = uint256(s.squeezeCounter);
        // SECURITY: Prevent squeezeCounter overflow on single-byte squeeze.
        require(counter < type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        assembly {
            let scratch := mload(0x40)
            mstore(scratch, st)
            let tagWord := or(
                shl(200, 0x73717565657a65),
                shl(136, counter)
            )
            mstore(add(scratch, 32), tagWord)
            let h := keccak256(scratch, 47)
            b := shr(248, h) // first byte
        }
        s.squeezeCounter = uint64(counter + 1);
    }

    /// @notice Absorb `len` bytes of `data` starting at byte `offset` without allocating the slice:
    ///         state = keccak256(state || data[offset..offset+len]), counter = 0. Byte-identical to
    ///         `absorb(s, data[offset:offset+len])`. The caller bounds `offset + len <= data.length`.
    function absorbSlice(Sponge memory s, bytes memory data, uint256 offset, uint256 len) internal pure {
        assembly ("memory-safe") {
            // Temporary scratch after the free memory pointer (not retained).
            let scratch := mload(0x40)
            mstore(scratch, mload(s))
            let src := add(add(data, 0x20), offset)
            let dst := add(scratch, 0x20)
            for { let i := 0 } lt(i, len) { i := add(i, 0x20) } {
                mstore(add(dst, i), mload(add(src, i)))
            }
            mstore(s, keccak256(scratch, add(32, len)))
            mstore(add(s, 0x20), 0)
        }
    }

    /// @notice Squeeze exactly one 32-byte block; identical to `squeeze(s, 32)` returned as a word.
    function squeezeWord(Sponge memory s) internal pure returns (bytes32 h) {
        uint256 counter = uint256(s.squeezeCounter);
        // SECURITY: same overflow guard as squeeze(s, 32) (one block).
        require(counter + 1 <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        bytes32 st = s.state;
        assembly ("memory-safe") {
            mstore(0x00, st)
            mstore(0x20, or(shl(200, 0x73717565657a65), shl(136, counter)))
            h := keccak256(0x00, 47)
        }
        s.squeezeCounter = uint64(counter + 1);
    }

    /// @notice Squeeze 120 bytes (four blocks) and decode three Goldilocks elements. Each 40-byte
    ///         chunk is read as a little-endian integer and reduced mod GL_P, exactly like
    ///         `_leModReduce64(squeeze(s, 120), 40 * k, 40)` (value = low256 + high64 * 2^256 and
    ///         2^256 mod GL_P = 2^32 - 1), without allocating the byte string.
    function squeezeField64x3(Sponge memory s) internal pure returns (uint64 c0, uint64 c1, uint64 c2) {
        uint256 counter = uint256(s.squeezeCounter);
        // SECURITY: same overflow guard as squeeze(s, 120) (four blocks).
        require(counter + 4 <= type(uint64).max, "Keccak256Chain: squeeze counter overflow");
        bytes32 st = s.state;
        assembly ("memory-safe") {
            function bswap(x) -> y {
                y := or(shr(8, and(x, 0xFF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00)), shl(8, and(x, 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF)))
                y := or(shr(16, and(y, 0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000)), shl(16, and(y, 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF)))
                y := or(shr(32, and(y, 0xFFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000)), shl(32, and(y, 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF)))
                y := or(shr(64, and(y, 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000)), shl(64, and(y, 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF)))
                y := or(shr(128, y), shl(128, y))
            }
            // decode(off): chunk bytes [off, off+40) = low word at off, high 8 bytes at off+32.
            function decode(ptr) -> v {
                let p := 0xFFFFFFFF00000001
                v := addmod(mod(bswap(mload(ptr)), p), mulmod(and(bswap(mload(add(ptr, 32))), 0xFFFFFFFFFFFFFFFF), 0xFFFFFFFF, p), p)
            }
            // 128 bytes of temporary scratch after the free memory pointer (not retained).
            let out := mload(0x40)
            mstore(0x00, st)
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                mstore(0x20, or(shl(200, 0x73717565657a65), shl(136, add(counter, i))))
                mstore(add(out, shl(5, i)), keccak256(0x00, 47))
            }
            c0 := decode(out)
            c1 := decode(add(out, 40))
            c2 := decode(add(out, 80))
        }
        s.squeezeCounter = uint64(counter + 4);
    }

    /// @notice Ratchet: state = keccak256(state || "ratchet"), counter = 0.
    function ratchet(Sponge memory s) internal pure {
        bytes32 st = s.state;
        bytes32 result;
        assembly {
            // state(32) || "ratchet"(7) = 39 bytes
            // "ratchet" = 0x72617463686574
            let scratch := mload(0x40)
            mstore(scratch, st)
            mstore(add(scratch, 32), 0x7261746368657400000000000000000000000000000000000000000000000000)
            result := keccak256(scratch, 39)
        }
        s.state = result;
        s.squeezeCounter = 0;
    }
}
