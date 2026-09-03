// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {PoseidonPublicInputsHash} from "../src/PoseidonPublicInputsHash.sol";
import {PoseidonGate} from "../src/PoseidonGate.sol";

contract PoseidonMdsHarness {
    function mds(uint256[12] memory state) external pure returns (uint256[12] memory) {
        uint256[12] memory scratch;
        uint256 statePtr;
        uint256 scratchPtr;
        assembly {
            statePtr := state
            scratchPtr := scratch
        }
        PoseidonGate._mdsLayerInline(statePtr, scratchPtr);
        return state;
    }
}

/// @notice Cross-language and resource regression coverage for the exact
/// Plonky2 Goldilocks Poseidon `hash_no_pad` used to bind public inputs.
contract PoseidonPublicInputsHashTest is Test {
    uint256 private constant P = 0xFFFFFFFF00000001;
    uint256 private constant MAX_103_INPUT_HASH_GAS = 1_900_000;

    function test_mdsSequentialRustVector() external {
        uint256[12] memory state;
        for (uint256 i = 0; i < 12; ++i) {
            state[i] = i;
        }
        state = new PoseidonMdsHarness().mds(state);
        uint256[12] memory expected = [uint256(1496), 1512, 1360, 1400, 1188, 1288, 1388, 1308, 1540, 1604, 1368, 1444];
        for (uint256 i = 0; i < 12; ++i) {
            assertEq(state[i], expected[i], "Rust MDS output");
        }
    }

    function testFuzz_mdsMatchesDenseDefinition(uint256[12] memory state) external {
        for (uint256 i = 0; i < 12; ++i) {
            state[i] %= P;
        }
        uint256[12] memory expected = _denseMds(state);
        uint256[12] memory actual = new PoseidonMdsHarness().mds(state);
        for (uint256 i = 0; i < 12; ++i) {
            assertEq(actual[i], expected[i], "dense MDS equivalence");
        }
    }

    function test_hashNoPad_matchesRustRateBoundaryVectors() external pure {
        uint256[6] memory lengths = [uint256(0), 1, 7, 8, 9, 103];
        for (uint256 i = 0; i < lengths.length; ++i) {
            uint256[4] memory digest = PoseidonPublicInputsHash.hashNoPad(_sequentialInputs(lengths[i]));
            uint256[4] memory expected = _expectedDigest(i);
            for (uint256 limb = 0; limb < 4; ++limb) {
                assertEq(digest[limb], expected[limb], "Rust hash_no_pad output");
            }
        }
    }

    function test_hashNoPad_103ElementGasEnvelope() external {
        uint256[] memory inputs = _sequentialInputs(103);
        uint256 gasBefore = gasleft();
        uint256[4] memory digest = PoseidonPublicInputsHash.hashNoPad(inputs);
        uint256 used = gasBefore - gasleft();
        emit log_named_uint("Poseidon hash_no_pad 103 inputs gas", used);

        assertEq(digest[0], 17_287_484_645_839_759_726);
        assertEq(digest[1], 2_836_085_724_020_267_508);
        assertEq(digest[2], 11_420_194_361_566_745_580);
        assertEq(digest[3], 12_353_543_096_432_783_826);
        assertLt(used, MAX_103_INPUT_HASH_GAS, "103-input Poseidon gas regression");
    }

    function test_hashNoPad_rejectsNonCanonicalInput() external {
        uint256[] memory inputs = _sequentialInputs(9);
        inputs[8] = P;
        vm.expectRevert(InvalidMleProof.selector);
        PoseidonPublicInputsHash.hashNoPad(inputs);
    }

    function _sequentialInputs(uint256 length) private pure returns (uint256[] memory inputs) {
        inputs = new uint256[](length);
        for (uint256 i = 0; i < length; ++i) {
            inputs[i] = i;
        }
    }

    function _expectedDigest(uint256 vector) private pure returns (uint256[4] memory) {
        if (vector == 0) return [uint256(0), 0, 0, 0];
        if (vector == 1) {
            return [
                uint256(4_330_397_376_401_421_145),
                14_124_799_381_142_128_323,
                8_742_572_140_681_234_676,
                14_345_658_006_221_440_202
            ];
        }
        if (vector == 2) {
            return [
                uint256(13_371_083_541_496_999_660),
                7_739_921_955_450_379_130,
                10_572_004_275_396_999_076,
                3_599_502_497_184_312_851
            ];
        }
        if (vector == 3) {
            return [
                uint256(17_291_601_223_193_097_753),
                9_133_441_755_544_524_598,
                17_736_579_132_324_177_718,
                14_132_891_516_240_416_332
            ];
        }
        if (vector == 4) {
            return [
                uint256(18_007_381_329_477_297_286),
                11_010_590_292_829_788_888,
                258_931_329_831_288_973,
                9_046_877_563_820_385_107
            ];
        }
        return [
            uint256(17_287_484_645_839_759_726),
            2_836_085_724_020_267_508,
            11_420_194_361_566_745_580,
            12_353_543_096_432_783_826
        ];
    }

    function _denseMds(uint256[12] memory state) private pure returns (uint256[12] memory result) {
        uint256[12] memory circulant = [uint256(17), 15, 41, 16, 2, 28, 13, 13, 39, 18, 34, 20];
        for (uint256 row = 0; row < 12; ++row) {
            uint256 sum;
            for (uint256 column = 0; column < 12; ++column) {
                sum += state[(column + row) % 12] * circulant[column];
            }
            if (row == 0) sum += state[0] * 8;
            result[row] = sum % P;
        }
    }
}
