// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";

import {InvalidMleProof, InvalidMleVerifierConfiguration} from "../src/MleProofErrors.sol";
import {Plonky2GateEvaluatorExt3} from "../src/Plonky2GateEvaluatorExt3.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";

/// @notice Cross-language differential tests generated from
///         `mle/testdata/gate_ext3_vectors.json`.
contract Plonky2GateEvaluatorExt3Test is Test {
    uint64 internal constant P = 0xFFFFFFFF00000001;
    uint64 internal constant UNUSED_SELECTOR = 0x00000000FFFFFFFF;
    uint256 internal constant NUM_WIRES = 135;
    uint256 internal constant NUM_CONSTANTS = 5;
    uint256 internal constant NUM_SELECTORS = 3;
    uint256 internal constant NUM_GATE_CONSTRAINTS = 123;
    uint256 internal constant QUOTIENT_DEGREE_FACTOR = 8;

    function test_allFourteenGateFamiliesAndFullSlotsReplayCanonicalRustJson() public view {
        string memory json = vm.readFile("../testdata/gate_ext3_vectors.json");
        assertEq(vm.parseJsonUint(json, ".version"), 1);
        assertEq(vm.parseJsonUint(json, ".config.num_wires"), NUM_WIRES);
        assertEq(vm.parseJsonUint(json, ".config.num_constants"), NUM_CONSTANTS);
        assertEq(vm.parseJsonUint(json, ".config.num_selectors"), NUM_SELECTORS);
        assertEq(vm.parseJsonUint(json, ".config.num_gate_constraints"), NUM_GATE_CONSTRAINTS);
        uint256 quotientDegreeFactor = vm.parseJsonUint(json, ".config.quotient_degree_factor");
        assertEq(quotientDegreeFactor, QUOTIENT_DEGREE_FACTOR);

        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _jsonGates(json);
        GoldilocksExt3.Ext3[] memory wires = _jsonExt3Array(json, ".wires");
        uint256[4] memory publicInputsHash = _jsonPublicInputsHash(json);
        GoldilocksExt3.Ext3 memory alpha = _jsonExt3(json, ".alpha");
        assertEq(wires.length, NUM_WIRES);

        for (uint256 row = 0; row < gates.length; ++row) {
            string memory vectorPath = string.concat(".vectors[", vm.toString(row), "]");
            assertEq(vm.parseJsonUint(json, string.concat(vectorPath, ".target_gate_id")), gates[row].gateId);
            GoldilocksExt3.Ext3[] memory constants = _jsonExt3Array(json, string.concat(vectorPath, ".constants"));
            GoldilocksExt3.Ext3[] memory expectedSlots =
                _jsonExt3Array(json, string.concat(vectorPath, ".expected_filtered_constraints"));
            assertEq(constants.length, NUM_CONSTANTS);
            assertEq(expectedSlots.length, NUM_GATE_CONSTRAINTS);
            // The production API intentionally returns only the alpha-reduced
            // value. Reducing every Rust-recorded slot here makes all 123
            // filtered constraints part of the cross-language assertion.
            GoldilocksExt3.Ext3 memory expected = GoldilocksExt3.reduceWithPowers(expectedSlots, alpha);
            _assertExtEq(expected, _jsonExt3(json, string.concat(vectorPath, ".expected_aggregation")));
            GoldilocksExt3.Ext3 memory actual = Plonky2GateEvaluatorExt3.evalCombined(
                wires,
                constants,
                publicInputsHash,
                alpha,
                gates,
                NUM_SELECTORS,
                NUM_CONSTANTS,
                NUM_GATE_CONSTRAINTS,
                NUM_WIRES,
                quotientDegreeFactor
            );
            _assertExtEq(actual, expected);
            if (gates[row].gateId != 0) {
                assertTrue(actual.c1 != 0, "Rust vector c1 must exercise a non-base limb");
                assertTrue(actual.c2 != 0, "Rust vector c2 must exercise a non-base limb");
            }
        }

        // Every selector below has nonzero c1/c2. It therefore differs from
        // every embedded-base row and UNUSED value, making all 14 gate filters
        // nonzero in the same evaluation and exercising their Ext3 sum path.
        string memory mixedPath = ".mixed_selector_vector";
        GoldilocksExt3.Ext3[] memory mixedConstants = _jsonExt3Array(json, string.concat(mixedPath, ".constants"));
        for (uint256 selector = 0; selector < NUM_SELECTORS; ++selector) {
            assertTrue(mixedConstants[selector].c1 != 0 && mixedConstants[selector].c2 != 0);
        }
        GoldilocksExt3.Ext3[] memory mixedSlots =
            _jsonExt3Array(json, string.concat(mixedPath, ".expected_filtered_constraints"));
        assertEq(mixedSlots.length, NUM_GATE_CONSTRAINTS);
        GoldilocksExt3.Ext3 memory mixedExpected = GoldilocksExt3.reduceWithPowers(mixedSlots, alpha);
        _assertExtEq(mixedExpected, _jsonExt3(json, string.concat(mixedPath, ".expected_aggregation")));
        GoldilocksExt3.Ext3 memory mixedActual = Plonky2GateEvaluatorExt3.evalCombined(
            wires,
            mixedConstants,
            publicInputsHash,
            alpha,
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            quotientDegreeFactor
        );
        _assertExtEq(mixedActual, mixedExpected);
    }

    /// @notice Isolate one simultaneous evaluation of all fourteen supported gate families from
    /// JSON parsing and the fourteen one-hot differential calls made by the golden-vector test
    /// above. Every selector is a non-base Ext3 value, so no configured gate is skipped. This is a
    /// family-coverage measurement, not a gas bound for the wider 255-row generic decoder cap;
    /// current parent production configurations are admitted separately and contain 13 rows.
    function test_gasAllFourteenGateFamiliesAtOneMixedTerminal() public {
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
        GoldilocksExt3.Ext3[] memory constants = new GoldilocksExt3.Ext3[](NUM_CONSTANTS);
        for (uint64 i = 0; i < NUM_CONSTANTS; ++i) {
            uint64 seed = i + 211;
            constants[i] = _ext(seed, 7 * seed + 1, 11 * seed + 3);
        }

        uint256 gasBefore = gasleft();
        Plonky2GateEvaluatorExt3.evalCombined(
            _wires(),
            constants,
            [uint256(131), uint256(137), uint256(139), uint256(149)],
            _ext(17, 52, 87),
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            QUOTIENT_DEGREE_FACTOR
        );
        uint256 used = gasBefore - gasleft();
        emit log_named_uint("all-14 Ext3 gate terminal gas", used);
    }

    function test_unknownGateFailsEvenWhenSelectorFilterWouldBeZero() public {
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
        gates[0].gateId = 14;
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        _evaluateTarget(gates, 13);
    }

    function test_nonCanonicalWireLimbFails() public {
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
        GoldilocksExt3.Ext3[] memory wires = _wires();
        wires[17].c2 = P;
        vm.expectRevert(InvalidMleProof.selector);
        Plonky2GateEvaluatorExt3.evalCombined(
            wires,
            _constants(gates[13]),
            [uint256(131), uint256(137), uint256(139), uint256(149)],
            _ext(17, 52, 87),
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            QUOTIENT_DEGREE_FACTOR
        );
    }

    function test_nonCanonicalConstantLimbFails() public {
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
        GoldilocksExt3.Ext3[] memory constants = _constants(gates[13]);
        constants[4].c1 = P;
        vm.expectRevert(InvalidMleProof.selector);
        Plonky2GateEvaluatorExt3.evalCombined(
            _wires(),
            constants,
            [uint256(131), uint256(137), uint256(139), uint256(149)],
            _ext(17, 52, 87),
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            QUOTIENT_DEGREE_FACTOR
        );
    }

    function test_nonCanonicalAlphaAndPublicHashFail() public {
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
        GoldilocksExt3.Ext3 memory alpha = _ext(17, 52, P);
        vm.expectRevert(InvalidMleProof.selector);
        Plonky2GateEvaluatorExt3.evalCombined(
            _wires(),
            _constants(gates[13]),
            [uint256(131), uint256(137), uint256(139), uint256(149)],
            alpha,
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            QUOTIENT_DEGREE_FACTOR
        );

        vm.expectRevert(InvalidMleProof.selector);
        Plonky2GateEvaluatorExt3.evalCombined(
            _wires(),
            _constants(gates[13]),
            [uint256(131), uint256(137), uint256(P), uint256(149)],
            _ext(17, 52, 87),
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            QUOTIENT_DEGREE_FACTOR
        );
    }

    function test_exactShapesAndMetadataAreFailClosed() public {
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
        GoldilocksExt3.Ext3[] memory shortWires = new GoldilocksExt3.Ext3[](NUM_WIRES - 1);
        vm.expectRevert(InvalidMleProof.selector);
        Plonky2GateEvaluatorExt3.evalCombined(
            shortWires,
            _constants(gates[13]),
            [uint256(131), uint256(137), uint256(139), uint256(149)],
            _ext(17, 52, 87),
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            QUOTIENT_DEGREE_FACTOR
        );

        gates[10].numConstraints = 53;
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        _evaluateTarget(gates, 13);
    }

    function test_quotientDegreeAndExpandedSelectorGroupAreFailClosed() public {
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        _evaluateTargetWithQdf(gates, 13, 0);

        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        _evaluateTargetWithQdf(gates, 13, 7);

        // Poseidon has unfiltered degree seven. Expanding its selector group
        // raises filter degree from two to three, which exceeds qdf+1=9.
        gates[13].groupStart = 11;
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        _evaluateTargetWithQdf(gates, 13, QUOTIENT_DEGREE_FACTOR);
    }

    function _evaluateTarget(Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates, uint256 targetRow)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory)
    {
        return _evaluateTargetWithQdf(gates, targetRow, QUOTIENT_DEGREE_FACTOR);
    }

    function _evaluateTargetWithQdf(
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates,
        uint256 targetRow,
        uint256 quotientDegreeFactor
    ) private pure returns (GoldilocksExt3.Ext3 memory) {
        return Plonky2GateEvaluatorExt3.evalCombined(
            _wires(),
            _constants(gates[targetRow]),
            [uint256(131), uint256(137), uint256(139), uint256(149)],
            _ext(17, 52, 87),
            gates,
            NUM_SELECTORS,
            NUM_CONSTANTS,
            NUM_GATE_CONSTRAINTS,
            NUM_WIRES,
            quotientDegreeFactor
        );
    }

    function _jsonExt3Array(string memory json, string memory path)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory values)
    {
        string[][] memory limbs = abi.decode(vm.parseJson(json, path), (string[][]));
        values = new GoldilocksExt3.Ext3[](limbs.length);
        for (uint256 i = 0; i < limbs.length; ++i) {
            assertEq(limbs[i].length, 3, "Ext3 JSON value must have c0,c1,c2");
            values[i] = _ext(_rawFieldLimb(limbs[i][0]), _rawFieldLimb(limbs[i][1]), _rawFieldLimb(limbs[i][2]));
        }
    }

    function _jsonExt3(string memory json, string memory path) private pure returns (GoldilocksExt3.Ext3 memory value) {
        string[] memory limbs = abi.decode(vm.parseJson(json, path), (string[]));
        assertEq(limbs.length, 3, "Ext3 JSON value must have c0,c1,c2");
        value = _ext(_rawFieldLimb(limbs[0]), _rawFieldLimb(limbs[1]), _rawFieldLimb(limbs[2]));
    }

    function _jsonPublicInputsHash(string memory json) private pure returns (uint256[4] memory values) {
        string[] memory encoded = abi.decode(vm.parseJson(json, ".public_inputs_hash"), (string[]));
        assertEq(encoded.length, 4);
        for (uint256 i = 0; i < 4; ++i) {
            values[i] = _rawFieldLimb(encoded[i]);
        }
    }

    function _jsonGates(string memory json) private pure returns (Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates) {
        gates = new Plonky2GateEvaluatorExt3.GateInfoV2[](14);
        for (uint256 i = 0; i < gates.length; ++i) {
            string memory prefix = string.concat(".gates[", vm.toString(i), "].");
            gates[i] = _gate(
                _jsonU8(json, string.concat(prefix, "gate_id")),
                _jsonU8(json, string.concat(prefix, "selector_index")),
                _jsonU8(json, string.concat(prefix, "group_start")),
                _jsonU8(json, string.concat(prefix, "group_end")),
                _jsonU8(json, string.concat(prefix, "gate_row_index")),
                _jsonU16(json, string.concat(prefix, "num_constraints")),
                _jsonU16(json, string.concat(prefix, "num_or_consts")),
                _jsonU16(json, string.concat(prefix, "param2")),
                _jsonU16(json, string.concat(prefix, "param3"))
            );
        }
    }

    function _jsonU8(string memory json, string memory path) private pure returns (uint8 value) {
        uint256 decoded = vm.parseJsonUint(json, path);
        assertLe(decoded, type(uint8).max);
        // forge-lint: disable-next-line(unsafe-typecast)
        value = uint8(decoded);
    }

    function _jsonU16(string memory json, string memory path) private pure returns (uint16 value) {
        uint256 decoded = vm.parseJsonUint(json, path);
        assertLe(decoded, type(uint16).max);
        // forge-lint: disable-next-line(unsafe-typecast)
        value = uint16(decoded);
    }

    function _rawFieldLimb(string memory encodedString) private pure returns (uint64 value) {
        // Foundry decodes a fixed `0x` JSON string as its exact eight raw bytes.
        bytes memory encoded = bytes(encodedString);
        assertEq(encoded.length, 8, "field limb must be fixed-width u64 hex");
        for (uint256 i = 0; i < 8; ++i) {
            value = (value << 8) | uint64(uint8(encoded[i]));
        }
        assertLt(value, P, "field limb must be canonical");
    }

    function _wires() private pure returns (GoldilocksExt3.Ext3[] memory wires) {
        wires = new GoldilocksExt3.Ext3[](NUM_WIRES);
        for (uint64 i = 0; i < NUM_WIRES; ++i) {
            uint64 seed = i + 2;
            wires[i] = _ext(seed, 3 * seed + 1, 5 * seed + 2);
        }
    }

    function _constants(Plonky2GateEvaluatorExt3.GateInfoV2 memory target)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory constants)
    {
        constants = new GoldilocksExt3.Ext3[](NUM_CONSTANTS);
        for (uint64 i = 0; i < NUM_CONSTANTS; ++i) {
            uint64 seed = i + 211;
            constants[i] = _ext(seed, 7 * seed + 1, 11 * seed + 3);
        }
        for (uint256 i = 0; i < NUM_SELECTORS; ++i) {
            constants[i] = _ext(UNUSED_SELECTOR, 0, 0);
        }
        constants[target.selectorIndex] = _ext(target.gateRowIndex, 0, 0);
    }

    function _gates() private pure returns (Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates) {
        gates = new Plonky2GateEvaluatorExt3.GateInfoV2[](14);
        gates[0] = _gate(0, 0, 0, 7, 0, 0, 0, 0, 0);
        gates[1] = _gate(1, 0, 0, 7, 1, 2, 2, 0, 0);
        gates[2] = _gate(5, 0, 0, 7, 2, 24, 0, 0, 0);
        gates[3] = _gate(2, 0, 0, 7, 3, 4, 0, 0, 0);
        gates[4] = _gate(9, 0, 0, 7, 4, 5, 4, 2, 0);
        gates[5] = _gate(11, 0, 0, 7, 5, 6, 3, 0, 0);
        gates[6] = _gate(10, 0, 0, 7, 6, 6, 3, 0, 0);
        gates[7] = _gate(6, 1, 7, 12, 7, 4, 2, 0, 0);
        gates[8] = _gate(3, 1, 7, 12, 8, 2, 2, 0, 0);
        gates[9] = _gate(7, 1, 7, 12, 9, 4, 2, 0, 0);
        gates[10] = _gate(12, 1, 7, 12, 10, 54, 2, 13, 2);
        gates[11] = _gate(13, 1, 7, 12, 11, 20, 4, 4, 0);
        gates[12] = _gate(8, 2, 12, 14, 12, 4, 3, 0, 0);
        gates[13] = _gate(4, 2, 12, 14, 13, 123, 0, 0, 0);
    }

    function _gate(
        uint8 gateId,
        uint8 selectorIndex,
        uint8 groupStart,
        uint8 groupEnd,
        uint8 gateRowIndex,
        uint16 numConstraints,
        uint16 numOrConsts,
        uint16 param2,
        uint16 param3
    ) private pure returns (Plonky2GateEvaluatorExt3.GateInfoV2 memory) {
        return Plonky2GateEvaluatorExt3.GateInfoV2({
            gateId: gateId,
            selectorIndex: selectorIndex,
            groupStart: groupStart,
            groupEnd: groupEnd,
            gateRowIndex: gateRowIndex,
            numConstraints: numConstraints,
            numOrConsts: numOrConsts,
            param2: param2,
            param3: param3
        });
    }

    function _ext(uint64 c0, uint64 c1, uint64 c2) private pure returns (GoldilocksExt3.Ext3 memory) {
        return GoldilocksExt3.Ext3({c0: c0, c1: c1, c2: c2});
    }

    function _assertExtEq(GoldilocksExt3.Ext3 memory actual, GoldilocksExt3.Ext3 memory expected) private pure {
        assertEq(actual.c0, expected.c0);
        assertEq(actual.c1, expected.c1);
        assertEq(actual.c2, expected.c2);
    }
}
