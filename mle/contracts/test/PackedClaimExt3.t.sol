// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {PackedClaimExt3} from "../src/PackedClaimExt3.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";

contract PackedClaimExt3Test is Test {
    uint64 private constant FIELD_MODULUS = 0xFFFFFFFF00000001;

    function test_rustDifferentialFiveCellVectorPreservesAllExt3Limbs() external pure {
        PackedClaimExt3.UsedClaims memory claims = _validClaims();
        (GoldilocksExt3.Ext3[] memory evaluations, bytes memory mask) =
            PackedClaimExt3.foldV2UsedCells(claims, _validSchema(), _indexPoints());

        assertEq(evaluations.length, 6);
        assertEq(mask.length, 1);
        assertEq(uint8(mask[0]), 0x1f);
        _assertExt3(evaluations[0], 0x0000000b213fb740, 0x0000000a96eec832, 0x00000007a03d794a);
        _assertExt3(evaluations[1], 0x0000001ff57a16ae, 0x0000001e57bb10da, 0x00000015df2aa962);
        _assertExt3(evaluations[2], 0xfffffffefe8b0783, 0xfffffffeff25c655, 0xfffffffeff070d05);
        _assertExt3(evaluations[3], 0x0000007621c021a4, 0x0000007002e7779a, 0x00000050cf4c063c);
        _assertExt3(evaluations[4], 0x000000963511766a, 0x0000008e75f5235a, 0x00000066bf8235f0);
        _assertExt3(evaluations[5], 0, 0, 0);
    }

    function test_standaloneFoldMatchesRustAndUsesNextPowerOfTwoPadding() external pure {
        PackedClaimExt3.UsedClaims memory claims = _validClaims();
        GoldilocksExt3.Ext3[][] memory points = _indexPoints();
        GoldilocksExt3.Ext3 memory widthFive = PackedClaimExt3.fold(claims.logWitness, 5, points[0]);
        GoldilocksExt3.Ext3 memory widthEight = PackedClaimExt3.fold(claims.logWitness, 8, points[0]);

        _assertExt3(widthFive, 0x0000001ff57a16ae, 0x0000001e57bb10da, 0x00000015df2aa962);
        assertTrue(GoldilocksExt3.eq(widthFive, widthEight));
    }

    function test_optimizedFoldMatchesIndependentReferenceAcrossReviewedWidths() external pure {
        uint256[7] memory widths = [uint256(1), 2, 3, 5, 80, 135, 160];
        for (uint256 caseIndex = 0; caseIndex < widths.length; ++caseIndex) {
            uint256 width = widths[caseIndex];
            GoldilocksExt3.Ext3[] memory values = new GoldilocksExt3.Ext3[](width);
            for (uint256 i = 0; i < width; ++i) {
                values[i] = _canonicalExt(17 + 131 * caseIndex + 19 * i);
            }
            uint256 indexBits;
            for (uint256 capacity = 1; capacity < width; capacity <<= 1) {
                ++indexBits;
            }
            GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](indexBits);
            for (uint256 bit = 0; bit < indexBits; ++bit) {
                point[bit] = _canonicalExt(1009 + 97 * caseIndex + 23 * bit);
            }

            GoldilocksExt3.Ext3 memory expected = _referenceFold(values, width, point);
            GoldilocksExt3.Ext3 memory actual = PackedClaimExt3.fold(values, width, point);
            assertTrue(GoldilocksExt3.eq(actual, expected), "optimized/reference fold drift");
        }

        // Production's preprocessed family is a strict 84-value prefix of the
        // width-160 constituent table. Exercise all 172 implicit zero slots in
        // the capacity-256 fold, rather than only full-width inputs.
        GoldilocksExt3.Ext3[] memory prefix = new GoldilocksExt3.Ext3[](84);
        for (uint256 i = 0; i < prefix.length; ++i) {
            prefix[i] = _canonicalExt(4001 + 29 * i);
        }
        GoldilocksExt3.Ext3[] memory maxPoint = new GoldilocksExt3.Ext3[](8);
        for (uint256 bit = 0; bit < maxPoint.length; ++bit) {
            maxPoint[bit] = _canonicalExt(8009 + 31 * bit);
        }
        GoldilocksExt3.Ext3 memory prefixExpected = _referenceFold(prefix, 160, maxPoint);
        GoldilocksExt3.Ext3 memory prefixActual = PackedClaimExt3.fold(prefix, 160, maxPoint);
        assertTrue(GoldilocksExt3.eq(prefixActual, prefixExpected), "width-160/prefix-84 padding drift");
    }

    function test_nonbaseInputLimbsCannotBeProjectedAway() external pure {
        GoldilocksExt3.Ext3[] memory values = _sequence(5, 2);
        GoldilocksExt3.Ext3[] memory point = _indexPoints()[0];
        GoldilocksExt3.Ext3 memory original = PackedClaimExt3.fold(values, 5, point);

        values[4].c1 += 1;
        GoldilocksExt3.Ext3 memory changedC1 = PackedClaimExt3.fold(values, 5, point);
        assertFalse(GoldilocksExt3.eq(original, changedC1));

        values = _sequence(5, 2);
        values[4].c2 += 1;
        GoldilocksExt3.Ext3 memory changedC2 = PackedClaimExt3.fold(values, 5, point);
        assertFalse(GoldilocksExt3.eq(original, changedC2));
    }

    function test_maskIsExactlyFiveUsedCellsInOneByte() external pure {
        bytes memory mask = PackedClaimExt3.usedCellMask();
        assertEq(mask.length, 1);
        assertEq(uint8(mask[0]), 0x1f);
        uint256 used;
        for (uint256 bit = 0; bit < 8; ++bit) {
            if ((uint8(mask[0]) & (uint8(1) << uint8(bit))) != 0) ++used;
        }
        assertEq(used, 5);
    }

    function test_rejectsNonCanonicalLimbInEveryUsedCell() external {
        for (uint256 cell = 0; cell < 5; ++cell) {
            for (uint256 limb = 0; limb < 3; ++limb) {
                PackedClaimExt3.UsedClaims memory claims = _validClaims();
                _setClaimLimb(claims, cell, limb, FIELD_MODULUS);
                vm.expectRevert(InvalidMleProof.selector);
                PackedClaimExt3.foldV2UsedCells(claims, _validSchema(), _indexPoints());
            }
        }
    }

    function test_rejectsNonCanonicalLimbInEveryIndexPoint() external {
        for (uint256 point = 0; point < 2; ++point) {
            for (uint256 bit = 0; bit < 3; ++bit) {
                for (uint256 limb = 0; limb < 3; ++limb) {
                    GoldilocksExt3.Ext3[][] memory indexPoints = _indexPoints();
                    _setLimb(indexPoints[point][bit], limb, FIELD_MODULUS);
                    vm.expectRevert(InvalidMleProof.selector);
                    PackedClaimExt3.foldV2UsedCells(_validClaims(), _validSchema(), indexPoints);
                }
            }
        }
    }

    function test_standaloneFoldRejectsNonCanonicalValueAndPoint() external {
        GoldilocksExt3.Ext3[] memory values = _sequence(5, 2);
        GoldilocksExt3.Ext3[] memory point = _indexPoints()[0];
        values[4].c2 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.fold(values, 5, point);

        values = _sequence(5, 2);
        point[2].c1 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.fold(values, 5, point);
    }

    function test_rejectsWrongWidthPointAndPrefixLengthsBeforeFolding() external {
        GoldilocksExt3.Ext3[] memory values = _sequence(5, 2);

        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.fold(values, 0, new GoldilocksExt3.Ext3[](0));

        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.fold(values, 161, new GoldilocksExt3.Ext3[](8));

        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.fold(values, 4, new GoldilocksExt3.Ext3[](2));

        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.fold(values, 5, new GoldilocksExt3.Ext3[](2));

        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.fold(values, 5, new GoldilocksExt3.Ext3[](4));
    }

    function test_rejectsEveryWrongUsedClaimLength() external {
        for (uint256 cell = 0; cell < 5; ++cell) {
            PackedClaimExt3.UsedClaims memory claims = _validClaims();
            if (cell == 0) claims.logPreprocessed = new GoldilocksExt3.Ext3[](2);
            if (cell == 1) claims.logWitness = new GoldilocksExt3.Ext3[](4);
            if (cell == 2) claims.logNormInverse = new GoldilocksExt3.Ext3[](3);
            if (cell == 3) claims.gatePreprocessed = new GoldilocksExt3.Ext3[](4);
            if (cell == 4) claims.gateWitness = new GoldilocksExt3.Ext3[](6);
            vm.expectRevert(InvalidMleProof.selector);
            PackedClaimExt3.foldV2UsedCells(claims, _validSchema(), _indexPoints());
        }
    }

    function test_rejectsWrongTwoPointShapeAndIndexBitLengths() external {
        GoldilocksExt3.Ext3[][] memory onePoint = new GoldilocksExt3.Ext3[][](1);
        onePoint[0] = new GoldilocksExt3.Ext3[](3);
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), _validSchema(), onePoint);

        GoldilocksExt3.Ext3[][] memory points = _indexPoints();
        points[0] = new GoldilocksExt3.Ext3[](2);
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), _validSchema(), points);

        points = _indexPoints();
        points[1] = new GoldilocksExt3.Ext3[](4);
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), _validSchema(), points);
    }

    function test_rejectsSchemaWidthDriftAndDimensionCaps() external {
        PackedClaimExt3.Schema memory schema = _validSchema();
        schema.width = 4;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), schema, _indexPoints());

        schema = _validSchema();
        schema.width = 6;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), schema, _indexPoints());

        schema = _validSchema();
        schema.numConstants = 161;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), schema, _indexPoints());

        schema = _validSchema();
        schema.numRoutedWires = 81;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), schema, _indexPoints());

        schema = _validSchema();
        schema.numWires = 161;
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(_validClaims(), schema, _indexPoints());
    }

    function test_emptySchemaIsRejected() external {
        PackedClaimExt3.Schema memory schema;
        GoldilocksExt3.Ext3[][] memory points = new GoldilocksExt3.Ext3[][](2);
        points[0] = new GoldilocksExt3.Ext3[](0);
        points[1] = new GoldilocksExt3.Ext3[](0);
        PackedClaimExt3.UsedClaims memory claims;
        claims.logPreprocessed = new GoldilocksExt3.Ext3[](0);
        claims.logWitness = new GoldilocksExt3.Ext3[](0);
        claims.logNormInverse = new GoldilocksExt3.Ext3[](0);
        claims.gatePreprocessed = new GoldilocksExt3.Ext3[](0);
        claims.gateWitness = new GoldilocksExt3.Ext3[](0);
        vm.expectRevert(InvalidMleProof.selector);
        PackedClaimExt3.foldV2UsedCells(claims, schema, points);
    }

    function _validSchema() private pure returns (PackedClaimExt3.Schema memory schema) {
        schema.width = 5;
        schema.numConstants = 1;
        schema.numRoutedWires = 2;
        schema.numWires = 5;
    }

    function _validClaims() private pure returns (PackedClaimExt3.UsedClaims memory claims) {
        claims.logPreprocessed = _sequence(3, 2);
        claims.logWitness = _sequence(5, 11);
        claims.logNormInverse = _sequence(4, 23);
        claims.gatePreprocessed = _sequence(3, 37);
        claims.gateWitness = _sequence(5, 47);
    }

    function _indexPoints() private pure returns (GoldilocksExt3.Ext3[][] memory points) {
        points = new GoldilocksExt3.Ext3[][](2);
        points[0] = new GoldilocksExt3.Ext3[](3);
        points[0][0] = _ext(101);
        points[0][1] = _ext(103);
        points[0][2] = _ext(107);
        points[1] = new GoldilocksExt3.Ext3[](3);
        points[1][0] = _ext(109);
        points[1][1] = _ext(113);
        points[1][2] = _ext(127);
    }

    function _sequence(uint256 length, uint64 start) private pure returns (GoldilocksExt3.Ext3[] memory values) {
        values = new GoldilocksExt3.Ext3[](length);
        for (uint256 i = 0; i < length; ++i) {
            values[i] = _ext(start + uint64(i));
        }
    }

    function _ext(uint64 seed) private pure returns (GoldilocksExt3.Ext3 memory value) {
        value = GoldilocksExt3.Ext3(seed, 3 * seed + 1, 5 * seed + 2);
    }

    function _canonicalExt(uint256 seed) private pure returns (GoldilocksExt3.Ext3 memory value) {
        value = GoldilocksExt3.Ext3(
            uint64(seed % FIELD_MODULUS), uint64((3 * seed + 1) % FIELD_MODULUS), uint64((5 * seed + 2) % FIELD_MODULUS)
        );
    }

    function _referenceFold(GoldilocksExt3.Ext3[] memory values, uint256 width, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory result)
    {
        uint256 capacity = 1;
        while (capacity < width) capacity <<= 1;
        GoldilocksExt3.Ext3[] memory layer = new GoldilocksExt3.Ext3[](capacity);
        for (uint256 i = 0; i < values.length; ++i) {
            GoldilocksExt3.Ext3 memory value = values[i];
            layer[i] = GoldilocksExt3.Ext3(value.c0, value.c1, value.c2);
        }
        uint256 active = capacity;
        for (uint256 bit = 0; bit < point.length; ++bit) {
            uint256 next = active >> 1;
            for (uint256 i = 0; i < next; ++i) {
                GoldilocksExt3.Ext3 memory even = layer[2 * i];
                GoldilocksExt3.Ext3 memory delta = GoldilocksExt3.sub(layer[2 * i + 1], even);
                layer[i] = GoldilocksExt3.add(even, GoldilocksExt3.mul(point[bit], delta));
            }
            active = next;
        }
        result = layer[0];
    }

    function _setClaimLimb(PackedClaimExt3.UsedClaims memory claims, uint256 cell, uint256 limb, uint64 value)
        private
        pure
    {
        if (cell == 0) _setLimb(claims.logPreprocessed[0], limb, value);
        if (cell == 1) _setLimb(claims.logWitness[0], limb, value);
        if (cell == 2) _setLimb(claims.logNormInverse[0], limb, value);
        if (cell == 3) _setLimb(claims.gatePreprocessed[0], limb, value);
        if (cell == 4) _setLimb(claims.gateWitness[0], limb, value);
    }

    function _setLimb(GoldilocksExt3.Ext3 memory target, uint256 limb, uint64 value) private pure {
        if (limb == 0) target.c0 = value;
        if (limb == 1) target.c1 = value;
        if (limb == 2) target.c2 = value;
    }

    function _assertExt3(GoldilocksExt3.Ext3 memory actual, uint64 c0, uint64 c1, uint64 c2) private pure {
        assertEq(actual.c0, c0);
        assertEq(actual.c1, c1);
        assertEq(actual.c2, c2);
    }
}
