// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof} from "./MleProofErrors.sol";
import {PoseidonConstants} from "./PoseidonConstants.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";

/// @title PoseidonGateExt3
/// @notice Exact Plonky2 Poseidon gate constraints over the Goldilocks cubic extension.
/// @dev Production entry points return the alpha-reduction rather than a large ABI array.
///      State, scratch space, and constraints use contiguous triples of EVM words and all
///      hot Fp3 operations are performed in assembly. This mirrors
///      `mle/src/gate_ext3.rs::{eval_poseidon, eval_poseidon_mds}`.
library PoseidonGateExt3 {
    uint256 internal constant P = 0xFFFFFFFF00000001;
    uint256 internal constant SPONGE_WIDTH = 12;
    uint256 internal constant HALF_N_FULL_ROUNDS = 4;
    uint256 internal constant N_PARTIAL_ROUNDS = 22;

    uint256 internal constant POSEIDON_WIRES = 135;
    uint256 internal constant POSEIDON_CONSTRAINTS = 123;
    uint256 internal constant POSEIDON_MDS_WIRES = 48;
    uint256 internal constant POSEIDON_MDS_CONSTRAINTS = 24;

    uint256 private constant WIRE_SWAP = 24;
    uint256 private constant START_DELTA = 25;
    uint256 private constant START_FULL_0 = 29;
    uint256 private constant START_PARTIAL = 65;
    uint256 private constant START_FULL_1 = 87;

    /// @notice Evaluate and alpha-reduce gate id 4 in canonical constraint order.
    /// @dev Callers perform the canonical-limb scan. A direct call remains memory-safe:
    ///      short inputs are rejected and field arithmetic reduces modulo P.
    function evalPoseidonReduced(GoldilocksExt3.Ext3[] memory wires, GoldilocksExt3.Ext3 memory alpha)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory reduced)
    {
        if (wires.length < POSEIDON_WIRES) revert InvalidMleProof();

        bytes memory allRC = PoseidonConstants.ALL_ROUND_CONSTANTS;
        bytes memory mdsCirc = PoseidonConstants.MDS_CIRC;
        bytes memory mdsDiag = PoseidonConstants.MDS_DIAG;
        bytes memory pfrc = PoseidonConstants.FAST_PARTIAL_FIRST_ROUND_CONSTANT;
        bytes memory prc = PoseidonConstants.FAST_PARTIAL_ROUND_CONSTANTS;
        bytes memory prvs = PoseidonConstants.FAST_PARTIAL_ROUND_VS;
        bytes memory prwh = PoseidonConstants.FAST_PARTIAL_ROUND_W_HATS;
        bytes memory pim = PoseidonConstants.FAST_PARTIAL_ROUND_INITIAL_MATRIX;

        uint256[] memory mds = new uint256[](13);
        uint256[] memory state = new uint256[](3 * SPONGE_WIDTH);
        uint256[] memory scratch = new uint256[](3 * SPONGE_WIDTH);
        uint256[] memory constraints = new uint256[](3 * POSEIDON_CONSTRAINTS);
        uint256 mdsPtr;
        uint256 statePtr;
        uint256 scratchPtr;
        uint256 constraintsPtr;
        assembly ("memory-safe") {
            mdsPtr := add(mds, 0x20)
            statePtr := add(state, 0x20)
            scratchPtr := add(scratch, 0x20)
            constraintsPtr := add(constraints, 0x20)
            let source := add(mdsCirc, 0x20)
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                mstore(add(mdsPtr, mul(i, 0x20)), shr(192, mload(add(source, mul(i, 8)))))
            }
            mstore(add(mdsPtr, 0x180), shr(192, mload(add(mdsDiag, 0x20))))
        }

        _evalSwapDelta(wires, statePtr, constraintsPtr);
        uint256 next = _firstFullRounds(wires, statePtr, scratchPtr, constraintsPtr, mdsPtr, allRC);
        _partialFirstConstantLayer(statePtr, pfrc);
        _mdsPartialLayerInit(statePtr, scratchPtr, pim);
        next = _partialRounds(wires, statePtr, scratchPtr, constraintsPtr, prc, prvs, prwh, next, mdsPtr);
        next = _secondFullRounds(wires, statePtr, scratchPtr, constraintsPtr, mdsPtr, allRC, next);
        _outputConstraints(wires, statePtr, constraintsPtr, next);
        reduced = _reduceRaw(constraintsPtr, POSEIDON_CONSTRAINTS, alpha);
    }

    /// @notice Evaluate and alpha-reduce gate id 5 in canonical constraint order.
    function evalPoseidonMdsReduced(GoldilocksExt3.Ext3[] memory wires, GoldilocksExt3.Ext3 memory alpha)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory reduced)
    {
        if (wires.length < POSEIDON_MDS_WIRES) revert InvalidMleProof();
        bytes memory mdsCirc = PoseidonConstants.MDS_CIRC;
        bytes memory mdsDiag = PoseidonConstants.MDS_DIAG;
        uint256[] memory constraints = new uint256[](3 * POSEIDON_MDS_CONSTRAINTS);
        uint256 constraintsPtr;
        assembly ("memory-safe") {
            constraintsPtr := add(constraints, 0x20)
            let p := P
            let wireTable := add(wires, 0x20)
            let circ := add(mdsCirc, 0x20)
            let diag := add(mdsDiag, 0x20)
            for { let row := 0 } lt(row, 12) { row := add(row, 1) } {
                let a0 := 0
                let a1 := 0
                let a2 := 0
                let b0 := 0
                let b1 := 0
                let b2 := 0
                for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                    let scalar := shr(192, mload(add(circ, mul(i, 8))))
                    let input := mul(2, mod(add(i, row), 12))
                    let left := mload(add(wireTable, mul(input, 0x20)))
                    let right := mload(add(wireTable, mul(add(input, 1), 0x20)))
                    a0 := addmod(a0, mulmod(mload(left), scalar, p), p)
                    a1 := addmod(a1, mulmod(mload(add(left, 0x20)), scalar, p), p)
                    a2 := addmod(a2, mulmod(mload(add(left, 0x40)), scalar, p), p)
                    b0 := addmod(b0, mulmod(mload(right), scalar, p), p)
                    b1 := addmod(b1, mulmod(mload(add(right, 0x20)), scalar, p), p)
                    b2 := addmod(b2, mulmod(mload(add(right, 0x40)), scalar, p), p)
                }
                let diagonal := shr(192, mload(add(diag, mul(row, 8))))
                let leftRow := mload(add(wireTable, mul(mul(2, row), 0x20)))
                let rightRow := mload(add(wireTable, mul(add(mul(2, row), 1), 0x20)))
                a0 := addmod(a0, mulmod(mload(leftRow), diagonal, p), p)
                a1 := addmod(a1, mulmod(mload(add(leftRow, 0x20)), diagonal, p), p)
                a2 := addmod(a2, mulmod(mload(add(leftRow, 0x40)), diagonal, p), p)
                b0 := addmod(b0, mulmod(mload(rightRow), diagonal, p), p)
                b1 := addmod(b1, mulmod(mload(add(rightRow, 0x20)), diagonal, p), p)
                b2 := addmod(b2, mulmod(mload(add(rightRow, 0x40)), diagonal, p), p)

                let outputStart := mul(2, add(12, row))
                let out0 := mload(add(wireTable, mul(outputStart, 0x20)))
                let out1 := mload(add(wireTable, mul(add(outputStart, 1), 0x20)))
                let slot0 := add(constraintsPtr, mul(mul(2, row), 0x60))
                let slot1 := add(slot0, 0x60)
                mstore(slot0, addmod(mload(out0), sub(p, a0), p))
                mstore(add(slot0, 0x20), addmod(mload(add(out0, 0x20)), sub(p, a1), p))
                mstore(add(slot0, 0x40), addmod(mload(add(out0, 0x40)), sub(p, a2), p))
                mstore(slot1, addmod(mload(out1), sub(p, b0), p))
                mstore(add(slot1, 0x20), addmod(mload(add(out1, 0x20)), sub(p, b1), p))
                mstore(add(slot1, 0x40), addmod(mload(add(out1, 0x40)), sub(p, b2), p))
            }
        }
        reduced = _reduceRaw(constraintsPtr, POSEIDON_MDS_CONSTRAINTS, alpha);
    }

    function _evalSwapDelta(GoldilocksExt3.Ext3[] memory wires, uint256 statePtr, uint256 constraintsPtr) private pure {
        assembly ("memory-safe") {
            function extMul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                let p := P
                c0 := addmod(mulmod(a0, b0, p), mulmod(2, addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p), p), p)
                c1 := addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p)
                c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            }
            let p := P
            let table := add(wires, 0x20)
            let swapPtr := mload(add(table, mul(WIRE_SWAP, 0x20)))
            let s0 := mload(swapPtr)
            let s1 := mload(add(swapPtr, 0x20))
            let s2 := mload(add(swapPtr, 0x40))
            let c0, c1, c2 := extMul(s0, s1, s2, addmod(s0, sub(p, 1), p), s1, s2)
            mstore(constraintsPtr, c0)
            mstore(add(constraintsPtr, 0x20), c1)
            mstore(add(constraintsPtr, 0x40), c2)

            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                let left := mload(add(table, mul(i, 0x20)))
                let right := mload(add(table, mul(add(i, 4), 0x20)))
                let delta := mload(add(table, mul(add(START_DELTA, i), 0x20)))
                let d0 := addmod(mload(right), sub(p, mod(mload(left), p)), p)
                let d1 := addmod(mload(add(right, 0x20)), sub(p, mod(mload(add(left, 0x20)), p)), p)
                let d2 := addmod(mload(add(right, 0x40)), sub(p, mod(mload(add(left, 0x40)), p)), p)
                c0, c1, c2 := extMul(s0, s1, s2, d0, d1, d2)
                let constraint := add(constraintsPtr, mul(add(i, 1), 0x60))
                mstore(constraint, addmod(c0, sub(p, mod(mload(delta), p)), p))
                mstore(add(constraint, 0x20), addmod(c1, sub(p, mod(mload(add(delta, 0x20)), p)), p))
                mstore(add(constraint, 0x40), addmod(c2, sub(p, mod(mload(add(delta, 0x40)), p)), p))

                let lowState := add(statePtr, mul(i, 0x60))
                let highState := add(statePtr, mul(add(i, 4), 0x60))
                mstore(lowState, addmod(mload(left), mload(delta), p))
                mstore(add(lowState, 0x20), addmod(mload(add(left, 0x20)), mload(add(delta, 0x20)), p))
                mstore(add(lowState, 0x40), addmod(mload(add(left, 0x40)), mload(add(delta, 0x40)), p))
                mstore(highState, addmod(mload(right), sub(p, mod(mload(delta), p)), p))
                mstore(
                    add(highState, 0x20),
                    addmod(mload(add(right, 0x20)), sub(p, mod(mload(add(delta, 0x20)), p)), p)
                )
                mstore(
                    add(highState, 0x40),
                    addmod(mload(add(right, 0x40)), sub(p, mod(mload(add(delta, 0x40)), p)), p)
                )
            }
            for { let i := 8 } lt(i, 12) { i := add(i, 1) } {
                let source := mload(add(table, mul(i, 0x20)))
                let target := add(statePtr, mul(i, 0x60))
                mstore(target, mload(source))
                mstore(add(target, 0x20), mload(add(source, 0x20)))
                mstore(add(target, 0x40), mload(add(source, 0x40)))
            }
        }
    }

    function _firstFullRounds(
        GoldilocksExt3.Ext3[] memory wires,
        uint256 statePtr,
        uint256 scratchPtr,
        uint256 constraintsPtr,
        uint256 mdsPtr,
        bytes memory allRC
    ) private pure returns (uint256 next) {
        next = 5;
        for (uint256 round = 0; round < HALF_N_FULL_ROUNDS; ++round) {
            _addConstantLayer(statePtr, allRC, round);
            if (round != 0) {
                next = _consumeFullRoundWires(
                    wires, statePtr, constraintsPtr, START_FULL_0 + SPONGE_WIDTH * (round - 1), next
                );
            }
            _sboxLayer(statePtr);
            _mdsLayer(statePtr, scratchPtr, mdsPtr);
        }
    }

    function _partialRounds(
        GoldilocksExt3.Ext3[] memory wires,
        uint256 statePtr,
        uint256 scratchPtr,
        uint256 constraintsPtr,
        bytes memory prc,
        bytes memory prvs,
        bytes memory prwh,
        uint256 next,
        uint256 mdsPtr
    ) private pure returns (uint256) {
        uint256 m00;
        assembly ("memory-safe") {
            m00 := addmod(mload(mdsPtr), mload(add(mdsPtr, 0x180)), P)
        }
        for (uint256 round = 0; round < N_PARTIAL_ROUNDS; ++round) {
            uint256 wireIndex = START_PARTIAL + round;
            assembly ("memory-safe") {
                let p := P
                let source := mload(add(add(wires, 0x20), mul(wireIndex, 0x20)))
                let constraint := add(constraintsPtr, mul(next, 0x60))
                mstore(constraint, addmod(mload(statePtr), sub(p, mod(mload(source), p)), p))
                mstore(
                    add(constraint, 0x20),
                    addmod(mload(add(statePtr, 0x20)), sub(p, mod(mload(add(source, 0x20)), p)), p)
                )
                mstore(
                    add(constraint, 0x40),
                    addmod(mload(add(statePtr, 0x40)), sub(p, mod(mload(add(source, 0x40)), p)), p)
                )
                mstore(statePtr, mload(source))
                mstore(add(statePtr, 0x20), mload(add(source, 0x20)))
                mstore(add(statePtr, 0x40), mload(add(source, 0x40)))
            }
            _sboxOne(statePtr);
            if (round + 1 != N_PARTIAL_ROUNDS) {
                assembly ("memory-safe") {
                    let rc := shr(192, mload(add(add(prc, 0x20), mul(round, 8))))
                    mstore(statePtr, addmod(mload(statePtr), rc, P))
                }
            }
            _mdsPartialLayerFast(statePtr, scratchPtr, prvs, prwh, round, m00);
            ++next;
        }
        return next;
    }

    function _secondFullRounds(
        GoldilocksExt3.Ext3[] memory wires,
        uint256 statePtr,
        uint256 scratchPtr,
        uint256 constraintsPtr,
        uint256 mdsPtr,
        bytes memory allRC,
        uint256 next
    ) private pure returns (uint256) {
        uint256 roundCounter = HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS;
        for (uint256 round = 0; round < HALF_N_FULL_ROUNDS; ++round) {
            _addConstantLayer(statePtr, allRC, roundCounter + round);
            next = _consumeFullRoundWires(wires, statePtr, constraintsPtr, START_FULL_1 + SPONGE_WIDTH * round, next);
            _sboxLayer(statePtr);
            _mdsLayer(statePtr, scratchPtr, mdsPtr);
        }
        return next;
    }

    function _consumeFullRoundWires(
        GoldilocksExt3.Ext3[] memory wires,
        uint256 statePtr,
        uint256 constraintsPtr,
        uint256 wireStart,
        uint256 next
    ) private pure returns (uint256) {
        assembly ("memory-safe") {
            let p := P
            let table := add(wires, 0x20)
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let source := mload(add(table, mul(add(wireStart, i), 0x20)))
                let stateSlot := add(statePtr, mul(i, 0x60))
                let constraint := add(constraintsPtr, mul(add(next, i), 0x60))
                mstore(constraint, addmod(mload(stateSlot), sub(p, mod(mload(source), p)), p))
                mstore(
                    add(constraint, 0x20),
                    addmod(mload(add(stateSlot, 0x20)), sub(p, mod(mload(add(source, 0x20)), p)), p)
                )
                mstore(
                    add(constraint, 0x40),
                    addmod(mload(add(stateSlot, 0x40)), sub(p, mod(mload(add(source, 0x40)), p)), p)
                )
                mstore(stateSlot, mload(source))
                mstore(add(stateSlot, 0x20), mload(add(source, 0x20)))
                mstore(add(stateSlot, 0x40), mload(add(source, 0x40)))
            }
        }
        unchecked {
            return next + SPONGE_WIDTH;
        }
    }

    function _outputConstraints(
        GoldilocksExt3.Ext3[] memory wires,
        uint256 statePtr,
        uint256 constraintsPtr,
        uint256 next
    ) private pure {
        assert(next + SPONGE_WIDTH == POSEIDON_CONSTRAINTS);
        assembly ("memory-safe") {
            let p := P
            let table := add(wires, 0x20)
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let output := mload(add(table, mul(add(12, i), 0x20)))
                let stateSlot := add(statePtr, mul(i, 0x60))
                let constraint := add(constraintsPtr, mul(add(next, i), 0x60))
                mstore(constraint, addmod(mload(stateSlot), sub(p, mod(mload(output), p)), p))
                mstore(
                    add(constraint, 0x20),
                    addmod(mload(add(stateSlot, 0x20)), sub(p, mod(mload(add(output, 0x20)), p)), p)
                )
                mstore(
                    add(constraint, 0x40),
                    addmod(mload(add(stateSlot, 0x40)), sub(p, mod(mload(add(output, 0x40)), p)), p)
                )
            }
        }
    }

    function _addConstantLayer(uint256 statePtr, bytes memory allRC, uint256 round) private pure {
        assembly ("memory-safe") {
            let base := add(add(allRC, 0x20), mul(round, 96))
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let slot := add(statePtr, mul(i, 0x60))
                mstore(slot, addmod(mload(slot), shr(192, mload(add(base, mul(i, 8)))), P))
            }
        }
    }

    function _partialFirstConstantLayer(uint256 statePtr, bytes memory pfrc) private pure {
        assembly ("memory-safe") {
            let base := add(pfrc, 0x20)
            for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                let slot := add(statePtr, mul(i, 0x60))
                mstore(slot, addmod(mload(slot), shr(192, mload(add(base, mul(i, 8)))), P))
            }
        }
    }

    function _sboxLayer(uint256 statePtr) private pure {
        for (uint256 i = 0; i < SPONGE_WIDTH; ++i) {
            _sboxOne(statePtr + i * 0x60);
        }
    }

    function _sboxOne(uint256 valuePtr) private pure {
        assembly ("memory-safe") {
            function extMul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                let p := P
                c0 := addmod(mulmod(a0, b0, p), mulmod(2, addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p), p), p)
                c1 := addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p)
                c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            }
            function extSquare(a0, a1, a2) -> c0, c1, c2 {
                let p := P
                c0 := addmod(mulmod(a0, a0, p), mulmod(4, mulmod(a1, a2, p), p), p)
                c1 := addmod(mulmod(2, mulmod(a0, a1, p), p), mulmod(2, mulmod(a2, a2, p), p), p)
                c2 := addmod(mulmod(2, mulmod(a0, a2, p), p), mulmod(a1, a1, p), p)
            }
            let x0 := mload(valuePtr)
            let x1 := mload(add(valuePtr, 0x20))
            let x2 := mload(add(valuePtr, 0x40))
            let q0, q1, q2 := extSquare(x0, x1, x2)
            let f0, f1, f2 := extSquare(q0, q1, q2)
            let t0, t1, t2 := extMul(x0, x1, x2, q0, q1, q2)
            let r0, r1, r2 := extMul(t0, t1, t2, f0, f1, f2)
            mstore(valuePtr, r0)
            mstore(add(valuePtr, 0x20), r1)
            mstore(add(valuePtr, 0x40), r2)
        }
    }

    function _mdsLayer(uint256 statePtr, uint256 scratchPtr, uint256 mdsPtr) private pure {
        assembly ("memory-safe") {
            let p := P
            for { let row := 0 } lt(row, 12) { row := add(row, 1) } {
                let a0 := 0
                let a1 := 0
                let a2 := 0
                for { let i := 0 } lt(i, 12) { i := add(i, 1) } {
                    let source := add(statePtr, mul(mod(add(i, row), 12), 0x60))
                    let scalar := mload(add(mdsPtr, mul(i, 0x20)))
                    a0 := addmod(a0, mulmod(mload(source), scalar, p), p)
                    a1 := addmod(a1, mulmod(mload(add(source, 0x20)), scalar, p), p)
                    a2 := addmod(a2, mulmod(mload(add(source, 0x40)), scalar, p), p)
                }
                if iszero(row) {
                    let diagonal := mload(add(mdsPtr, 0x180))
                    a0 := addmod(a0, mulmod(mload(statePtr), diagonal, p), p)
                    a1 := addmod(a1, mulmod(mload(add(statePtr, 0x20)), diagonal, p), p)
                    a2 := addmod(a2, mulmod(mload(add(statePtr, 0x40)), diagonal, p), p)
                }
                let target := add(scratchPtr, mul(row, 0x60))
                mstore(target, a0)
                mstore(add(target, 0x20), a1)
                mstore(add(target, 0x40), a2)
            }
            for { let i := 0 } lt(i, 36) { i := add(i, 1) } {
                mstore(add(statePtr, mul(i, 0x20)), mload(add(scratchPtr, mul(i, 0x20))))
            }
        }
    }

    function _mdsPartialLayerInit(uint256 statePtr, uint256 scratchPtr, bytes memory pim) private pure {
        assembly ("memory-safe") {
            let p := P
            mstore(scratchPtr, mload(statePtr))
            mstore(add(scratchPtr, 0x20), mload(add(statePtr, 0x20)))
            mstore(add(scratchPtr, 0x40), mload(add(statePtr, 0x40)))
            for { let i := 3 } lt(i, 36) { i := add(i, 1) } {
                mstore(add(scratchPtr, mul(i, 0x20)), 0)
            }
            let matrix := add(pim, 0x20)
            for { let row := 1 } lt(row, 12) { row := add(row, 1) } {
                let source := add(statePtr, mul(row, 0x60))
                let rowBase := add(matrix, mul(sub(row, 1), 88))
                for { let column := 1 } lt(column, 12) { column := add(column, 1) } {
                    let scalar := shr(192, mload(add(rowBase, mul(sub(column, 1), 8))))
                    let target := add(scratchPtr, mul(column, 0x60))
                    mstore(target, addmod(mload(target), mulmod(mload(source), scalar, p), p))
                    mstore(
                        add(target, 0x20),
                        addmod(mload(add(target, 0x20)), mulmod(mload(add(source, 0x20)), scalar, p), p)
                    )
                    mstore(
                        add(target, 0x40),
                        addmod(mload(add(target, 0x40)), mulmod(mload(add(source, 0x40)), scalar, p), p)
                    )
                }
            }
            for { let i := 0 } lt(i, 36) { i := add(i, 1) } {
                mstore(add(statePtr, mul(i, 0x20)), mload(add(scratchPtr, mul(i, 0x20))))
            }
        }
    }

    function _mdsPartialLayerFast(
        uint256 statePtr,
        uint256 scratchPtr,
        bytes memory prvs,
        bytes memory prwh,
        uint256 round,
        uint256 m00
    ) private pure {
        assembly ("memory-safe") {
            let p := P
            let s0 := mload(statePtr)
            let s1 := mload(add(statePtr, 0x20))
            let s2 := mload(add(statePtr, 0x40))
            let d0 := mulmod(s0, m00, p)
            let d1 := mulmod(s1, m00, p)
            let d2 := mulmod(s2, m00, p)
            let whBase := add(add(prwh, 0x20), mul(round, 88))
            let vsBase := add(add(prvs, 0x20), mul(round, 88))
            for { let i := 1 } lt(i, 12) { i := add(i, 1) } {
                let source := add(statePtr, mul(i, 0x60))
                let wh := shr(192, mload(add(whBase, mul(sub(i, 1), 8))))
                d0 := addmod(d0, mulmod(mload(source), wh, p), p)
                d1 := addmod(d1, mulmod(mload(add(source, 0x20)), wh, p), p)
                d2 := addmod(d2, mulmod(mload(add(source, 0x40)), wh, p), p)
                let v := shr(192, mload(add(vsBase, mul(sub(i, 1), 8))))
                let target := add(scratchPtr, mul(i, 0x60))
                mstore(target, addmod(mulmod(s0, v, p), mload(source), p))
                mstore(add(target, 0x20), addmod(mulmod(s1, v, p), mload(add(source, 0x20)), p))
                mstore(add(target, 0x40), addmod(mulmod(s2, v, p), mload(add(source, 0x40)), p))
            }
            mstore(scratchPtr, d0)
            mstore(add(scratchPtr, 0x20), d1)
            mstore(add(scratchPtr, 0x40), d2)
            for { let i := 0 } lt(i, 36) { i := add(i, 1) } {
                mstore(add(statePtr, mul(i, 0x20)), mload(add(scratchPtr, mul(i, 0x20))))
            }
        }
    }

    function _reduceRaw(uint256 constraintsPtr, uint256 count, GoldilocksExt3.Ext3 memory alpha)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory reduced)
    {
        assembly ("memory-safe") {
            function extMul(a0, a1, a2, b0, b1, b2) -> c0, c1, c2 {
                let p := P
                c0 := addmod(mulmod(a0, b0, p), mulmod(2, addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p), p), p)
                c1 := addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p)
                c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            }
            let p := P
            let alpha0 := mload(alpha)
            let alpha1 := mload(add(alpha, 0x20))
            let alpha2 := mload(add(alpha, 0x40))
            let r0 := 0
            let r1 := 0
            let r2 := 0
            for { let i := count } gt(i, 0) { i := sub(i, 1) } {
                let m0, m1, m2 := extMul(r0, r1, r2, alpha0, alpha1, alpha2)
                let term := add(constraintsPtr, mul(sub(i, 1), 0x60))
                r0 := addmod(m0, mload(term), p)
                r1 := addmod(m1, mload(add(term, 0x20)), p)
                r2 := addmod(m2, mload(add(term, 0x40)), p)
            }
            mstore(reduced, r0)
            mstore(add(reduced, 0x20), r1)
            mstore(add(reduced, 0x40), r2)
        }
    }
}
