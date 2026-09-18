// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {SpongefishMerkle} from "../src/spongefish/SpongefishMerkle.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";
import {WhirLinearAlgebra} from "../src/spongefish/WhirLinearAlgebra.sol";

/// @dev Calls the library's internal row decoder exactly the way
///      `_addConstraintValues` does, but with a caller-chosen `numCols`.
contract DotEqHarness {
    /// @notice Straight pass-through: `numCols` may exceed `eqW.length`.
    function dot(GoldilocksExt3.Ext3[] memory eqW, bytes calldata row, uint256 numCols, bool isBaseField)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory)
    {
        SpongefishMerkle.CalldataBytes memory view_ =
            SpongefishMerkle.CalldataBytes({offset: 0, length: row.length});
        assembly ("memory-safe") {
            mstore(view_, row.offset)
        }
        return SpongefishWhirVerify._dotEqWithRow(eqW, view_, 0, numCols, isBaseField);
    }

    /// @notice Builds a length-1 eq-weight array whose pointer slots 1..3 still
    ///         hold live Ext3 pointers (exactly what an over-allocated / later
    ///         shrunk weight vector looks like in EVM memory). Then calls the
    ///         decoder with numCols = 4.
    function dotWithLivePointersAfterEnd(bytes calldata row, uint256 tail)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory)
    {
        GoldilocksExt3.Ext3[] memory weights = new GoldilocksExt3.Ext3[](4);
        weights[0] = GoldilocksExt3.Ext3(1, 0, 0);
        weights[1] = GoldilocksExt3.Ext3(uint64(tail), 0, 0);
        weights[2] = GoldilocksExt3.Ext3(uint64(tail), 0, 0);
        weights[3] = GoldilocksExt3.Ext3(uint64(tail), 0, 0);
        // Shrink to length 1 — the three trailing element pointers survive.
        assembly ("memory-safe") {
            mstore(weights, 1)
        }
        SpongefishMerkle.CalldataBytes memory view_ =
            SpongefishMerkle.CalldataBytes({offset: 0, length: row.length});
        assembly ("memory-safe") {
            mstore(view_, row.offset)
        }
        return SpongefishWhirVerify._dotEqWithRow(weights, view_, 0, 4, true);
    }
}

/// @title PocWhirDotEqBounds
/// @notice ADVERSARIAL AUDIT ARTIFACT — not part of the production suite.
///
/// `SpongefishWhirVerify._dotEqWithRow` (SpongefishWhirVerify.sol:1460) bounds
/// only the *hints* slice; it never checks `numCols <= eqW.length`, and the
/// assembly loop dereferences `eqW[j]` as a pointer for every j < numCols:
///
///     let eqElem := mload(add(eqPtr, mul(j, 0x20)))   // no bound on j
///     let w0 := mload(eqElem)                          // arbitrary mload
///
/// Compare `WhirLinearAlgebra.dotProduct` (WhirLinearAlgebra.sol:419), which
/// *does* reject a length mismatch, and `eqWeightsFrom` (…:300), which bounds
/// its slice. The sole caller that can violate the invariant is
/// `_addConstraintValues` at round 0, reached from `_openAndVerifyCommitment`
/// (SpongefishWhirVerify.sol:1100/1128) when `numCommitments == 1`:
/// there `numCols = initialInterleavingDepth * numVectors` while
/// `eqW.length = 2**initialSumcheckRounds = initialInterleavingDepth`, so any
/// profile with `numVectors > 1 && numCommitments == 1 && numRounds >= 1`
/// reads `numCols - eqW.length` element pointers past the array.
///
/// The deployed wire-v3 profile uses numCommitments = 3 (> 1), which routes
/// round 0 through `_openSplitCommitments`/`_dotGroupedRow` instead, so this is
/// NOT reachable by a proof-only attacker. It is reported as a latent
/// defence-in-depth gap, not as a break of the deployed verifier.
contract PocWhirDotEqBoundsTest is Test {
    DotEqHarness internal harness = new DotEqHarness();

    /// @notice Baseline: with numCols == eqW.length the decoder is well-defined.
    function test_poc_dotEqWithRow_inBounds_baseline() public view {
        GoldilocksExt3.Ext3[] memory eqW = new GoldilocksExt3.Ext3[](2);
        eqW[0] = GoldilocksExt3.Ext3(1, 0, 0);
        eqW[1] = GoldilocksExt3.Ext3(1, 0, 0);
        // two base-field limbs: 3 and 5
        bytes memory row = hex"03000000000000000500000000000000";
        GoldilocksExt3.Ext3 memory out = harness.dot(eqW, row, 2, true);
        assertEq(out.c0, 8, "1*3 + 1*5");
    }

    /// @notice CONFIRMED: `numCols > eqW.length` does NOT revert. The call
    ///         silently consumes out-of-bounds element pointers. The reference
    ///         helper `WhirLinearAlgebra.dotProduct` rejects the same mismatch,
    ///         which is the inconsistency being reported.
    function test_poc_dotEqWithRow_readsPastEqWeights_withoutReverting() public {
        GoldilocksExt3.Ext3[] memory eqW = new GoldilocksExt3.Ext3[](1);
        eqW[0] = GoldilocksExt3.Ext3(1, 0, 0);
        // four base-field limbs; only one eq weight exists.
        bytes memory row = hex"0100000000000000020000000000000003000000000000000400000000000000";

        bool reverted;
        try harness.dot(eqW, row, 4, true) returns (GoldilocksExt3.Ext3 memory) {
            reverted = false;
        } catch {
            reverted = true;
        }
        assertFalse(reverted, "out-of-bounds numCols must have been rejected, but was not");

        // For contrast: the length-checked helper in the same codebase reverts.
        GoldilocksExt3.Ext3[] memory four = new GoldilocksExt3.Ext3[](4);
        vm.expectRevert();
        this.callDotProduct(eqW, four);
    }

    function callDotProduct(GoldilocksExt3.Ext3[] memory a, GoldilocksExt3.Ext3[] memory b)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory)
    {
        return WhirLinearAlgebra.dotProduct(a, b);
    }

    /// @notice CONFIRMED: the out-of-bounds words are not inert. `weights` has
    ///         length 1, yet the decoder folds four columns and the result
    ///         changes with memory that lies past the array end — the decoded
    ///         "folded leaf value" is therefore not a function of the committed
    ///         row and the eq weights alone.
    function test_poc_dotEqWithRow_outOfBounds_resultDependsOnAdjacentMemory() public view {
        bytes memory row = hex"0100000000000000020000000000000003000000000000000400000000000000";
        GoldilocksExt3.Ext3 memory a = harness.dotWithLivePointersAfterEnd(row, 0);
        GoldilocksExt3.Ext3 memory b = harness.dotWithLivePointersAfterEnd(row, 7);
        // With a correct bound check both calls would be identical (= 1*1 = 1).
        assertEq(a.c0, 1, "in-bounds contribution only");
        assertEq(b.c0, 1 + 7 * 2 + 7 * 3 + 7 * 4, "columns 1..3 folded with out-of-bounds weights");
    }
}
