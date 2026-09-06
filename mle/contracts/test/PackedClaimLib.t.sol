// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {PackedClaimLib} from "../src/PackedClaimLib.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";

contract PackedClaimLibTest is Test {
    uint256 private constant P = 0xFFFFFFFF00000001;

    function test_legacyFoldChecksCanonicalInputsBeforeNarrowing() external {
        uint256[] memory values = new uint256[](2);
        values[0] = 1;
        values[1] = 3;
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](1);
        point[0] = GoldilocksExt3.Ext3(2, 0, 0);
        GoldilocksExt3.Ext3 memory folded = PackedClaimLib.fold(values, 2, point);
        assertEq(folded.c0, 5);
        assertEq(folded.c1, 0);
        assertEq(folded.c2, 0);

        values[0] = P;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimLib.fold(values, 2, point);

        values[0] = 1;
        point[0] = GoldilocksExt3.Ext3(uint64(P), 0, 0);
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimLib.fold(values, 2, point);
    }

    function test_legacyFoldRejectsUnreviewedShapes() external {
        uint256[] memory values = new uint256[](0);
        GoldilocksExt3.Ext3[] memory noPoint = new GoldilocksExt3.Ext3[](0);
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimLib.fold(values, 0, noPoint);

        GoldilocksExt3.Ext3[] memory tooManyBits = new GoldilocksExt3.Ext3[](9);
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimLib.fold(values, 161, tooManyBits);
    }
}
