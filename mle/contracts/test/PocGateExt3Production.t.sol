// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";

import {Plonky2GateEvaluatorExt3} from "../src/Plonky2GateEvaluatorExt3.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";

/// @notice Cross-language differential test at DEPLOYED gate parameters.
///
/// `testdata/gate_ext3_vectors.json` pins the Rust<->Solidity Ext3 gate
/// evaluator only at toy sizes (ArithmeticGate 2 ops, BaseSum 4 limbs,
/// Reducing/ReducingExtension 3 coeffs, Exponentiation 3 bits,
/// CosetInterpolation degree 4, RandomAccess bits 2). The deployed circuits use
/// ArithmeticGate 20 ops, ArithmeticExtension 10, MulExtension 13, BaseSum<2>
/// 63 limbs, Reducing 43, ReducingExtension 32, Exponentiation 66 bits,
/// RandomAccess bits 4 / copies 4 / extra 2, and CosetInterpolation
/// subgroup_bits 4 / degree 6.
///
/// This test replays `testdata/poc_gate_ext3_production_vectors.json`, produced
/// by `mle/tests/poc_gates_production_vectors.rs`, which rebuilds both deployed
/// gate tables from real `CommonCircuitData` and (for the base-embedded
/// vectors) cross-checks them against plonky2's own `evaluate_gate_constraints`.
contract PocGateExt3ProductionTest is Test {
    uint64 internal constant P = 0xFFFFFFFF00000001;
    string internal constant VECTOR_PATH = "../testdata/poc_gate_ext3_production_vectors.json";

    struct Cfg {
        uint256 numWires;
        uint256 numConstants;
        uint256 numSelectors;
        uint256 numGateConstraints;
        uint256 quotientDegreeFactor;
        uint256 numGates;
        uint256 numWireSets;
        uint256 numVectors;
    }

    /// @notice Withdrawal-family deployed configuration: 3 selectors, 5 constants,
    /// 13 gate rows, no ExponentiationGate.
    function test_withdrawalProductionGateTableReplaysRustVectors() public view {
        string memory json = vm.readFile(VECTOR_PATH);
        _assertSchema(json);
        _replayConfig(json, 0, "withdrawal", 5, 3);
    }

    /// @notice Post-close-claim-family deployed configuration: 4 selectors,
    /// 6 constants, 13 gate rows, includes ExponentiationGate with 66 power bits.
    function test_postCloseClaimProductionGateTableReplaysRustVectors() public view {
        string memory json = vm.readFile(VECTOR_PATH);
        _assertSchema(json);
        _replayConfig(json, 1, "post_close_claim", 6, 4);
    }

    /// @notice The vectors must actually carry the deployed parameter sizes, so
    /// this test cannot silently degrade back into the toy fixture's coverage.
    function test_vectorsCarryDeployedGateParameters() public view {
        string memory json = vm.readFile(VECTOR_PATH);
        // withdrawal rows: BaseSum<2> 63 limbs, ReducingExt 32, Reducing 43,
        // ArithExt 10, Arithmetic 20, MulExt 13, RandomAccess bits 4, Coset deg 6.
        _assertGateParam(json, 0, 4, 9, 63, 2, 64);
        _assertGateParam(json, 0, 5, 11, 32, 0, 64);
        _assertGateParam(json, 0, 6, 10, 43, 0, 86);
        _assertGateParam(json, 0, 7, 6, 10, 0, 20);
        _assertGateParam(json, 0, 8, 3, 20, 0, 20);
        _assertGateParam(json, 0, 9, 7, 13, 0, 26);
        _assertGateParam(json, 0, 10, 12, 4, 4, 26);
        _assertGateParam(json, 0, 11, 13, 4, 6, 12);
        _assertGateParam(json, 0, 12, 4, 0, 0, 123);
        // post_close_claim additionally exercises Exponentiation with 66 bits.
        _assertGateParam(json, 1, 9, 8, 66, 0, 67);
        _assertGateParam(json, 1, 10, 12, 4, 4, 26);
        _assertGateParam(json, 1, 11, 13, 4, 6, 12);
    }

    /// @notice Negative control: the replay above is not vacuous. Perturbing a
    /// single wire limb must change the Solidity aggregate away from the
    /// recorded Rust value, for BOTH deployed configurations.
    function test_solidityReplayIsNotVacuous() public view {
        string memory json = vm.readFile(VECTOR_PATH);
        for (uint256 configIndex = 0; configIndex < 2; ++configIndex) {
            string memory base = string.concat(".configs[", vm.toString(configIndex), "]");
            // Vector 1 isolates a non-trivial gate family (row 1) with a
            // non-zero selector filter, so its wires genuinely matter.
            string memory vpath = string.concat(base, ".vectors[1]");
            Cfg memory cfg = _cfg(json, base);
            Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _jsonGates(json, base, cfg.numGates);
            uint256 wiresIndex = vm.parseJsonUint(json, string.concat(vpath, ".wires_index"));
            GoldilocksExt3.Ext3[] memory wires =
                _jsonExt3Array(json, string.concat(base, ".wire_sets[", vm.toString(wiresIndex), "]"));
            GoldilocksExt3.Ext3[] memory constants = _jsonExt3Array(json, string.concat(vpath, ".constants"));
            uint256[4] memory publicInputsHash = _jsonHash(json, string.concat(vpath, ".public_inputs_hash"));
            GoldilocksExt3.Ext3 memory alpha = _jsonExt3(json, string.concat(vpath, ".alpha"));
            GoldilocksExt3.Ext3 memory recorded = _jsonExt3(json, string.concat(vpath, ".expected_aggregation"));

            // Perturb one wire limb, staying canonical.
            wires[0].c0 = wires[0].c0 == 0 ? 1 : wires[0].c0 - 1;
            GoldilocksExt3.Ext3 memory perturbed = Plonky2GateEvaluatorExt3.evalCombined(
                wires,
                constants,
                publicInputsHash,
                alpha,
                gates,
                cfg.numSelectors,
                cfg.numConstants,
                cfg.numGateConstraints,
                cfg.numWires,
                cfg.quotientDegreeFactor
            );
            assertTrue(
                perturbed.c0 != recorded.c0 || perturbed.c1 != recorded.c1 || perturbed.c2 != recorded.c2,
                "negative control: aggregate is insensitive to a wire limb"
            );
        }
    }

    // ------------------------------------------------------------------

    function _assertSchema(string memory json) private pure {
        assertEq(vm.parseJsonUint(json, ".version"), 1, "fixture version");
        assertEq(
            keccak256(bytes(vm.parseJsonString(json, ".schema"))),
            keccak256("plonky2-mle-gate-ext3-production-differential-v1"),
            "fixture schema"
        );
    }

    function _assertGateParam(
        string memory json,
        uint256 configIndex,
        uint256 row,
        uint256 gateId,
        uint256 numOrConsts,
        uint256 param2,
        uint256 numConstraints
    ) private pure {
        string memory prefix =
            string.concat(".configs[", vm.toString(configIndex), "].gates[", vm.toString(row), "].");
        assertEq(vm.parseJsonUint(json, string.concat(prefix, "gate_id")), gateId, "gate_id");
        assertEq(vm.parseJsonUint(json, string.concat(prefix, "num_or_consts")), numOrConsts, "num_or_consts");
        assertEq(vm.parseJsonUint(json, string.concat(prefix, "param2")), param2, "param2");
        assertEq(vm.parseJsonUint(json, string.concat(prefix, "num_constraints")), numConstraints, "num_constraints");
    }

    function _replayConfig(
        string memory json,
        uint256 configIndex,
        string memory expectedName,
        uint256 expectedConstants,
        uint256 expectedSelectors
    ) private view {
        string memory base = string.concat(".configs[", vm.toString(configIndex), "]");
        assertEq(
            keccak256(bytes(vm.parseJsonString(json, string.concat(base, ".name")))),
            keccak256(bytes(expectedName)),
            "config name"
        );

        Cfg memory cfg = _cfg(json, base);
        // The deployed shape, cross-checked against the parent-repo configs.
        assertEq(cfg.numWires, 135, "numWires");
        assertEq(cfg.numConstants, expectedConstants, "numConstants");
        assertEq(cfg.numSelectors, expectedSelectors, "numSelectors");
        assertEq(cfg.numGateConstraints, 123, "numGateConstraints");
        assertEq(cfg.quotientDegreeFactor, 8, "quotientDegreeFactor");
        assertEq(cfg.numGates, 13, "numGates");
        assertTrue(cfg.numVectors > 0, "no vectors");

        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _jsonGates(json, base, cfg.numGates);

        for (uint256 i = 0; i < cfg.numVectors; ++i) {
            _replayVector(json, base, cfg, gates, i);
        }
    }

    function _replayVector(
        string memory json,
        string memory base,
        Cfg memory cfg,
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates,
        uint256 vectorIndex
    ) private view {
        string memory vpath = string.concat(base, ".vectors[", vm.toString(vectorIndex), "]");

        uint256 wiresIndex = vm.parseJsonUint(json, string.concat(vpath, ".wires_index"));
        assertLt(wiresIndex, cfg.numWireSets, "wires_index out of range");
        GoldilocksExt3.Ext3[] memory wires =
            _jsonExt3Array(json, string.concat(base, ".wire_sets[", vm.toString(wiresIndex), "]"));
        assertEq(wires.length, cfg.numWires, "wire set length");

        GoldilocksExt3.Ext3[] memory constants = _jsonExt3Array(json, string.concat(vpath, ".constants"));
        assertEq(constants.length, cfg.numConstants, "constants length");

        uint256[4] memory publicInputsHash = _jsonHash(json, string.concat(vpath, ".public_inputs_hash"));

        GoldilocksExt3.Ext3[] memory slots =
            _jsonExt3Array(json, string.concat(vpath, ".expected_filtered_constraints"));
        assertEq(slots.length, cfg.numGateConstraints, "slot vector length");

        // Two independent aggregation challenges over the SAME Rust slot vector.
        // `evalCombined` only returns the alpha-reduction, so agreeing under two
        // independent random alphas makes every one of the 123 filtered slots
        // part of the assertion: a non-zero slot difference would have to be a
        // root of two independent degree-122 polynomials over Fp3.
        _replayChallenge(json, vpath, cfg, gates, wires, constants, publicInputsHash, slots, false);
        _replayChallenge(json, vpath, cfg, gates, wires, constants, publicInputsHash, slots, true);
    }

    function _replayChallenge(
        string memory json,
        string memory vpath,
        Cfg memory cfg,
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates,
        GoldilocksExt3.Ext3[] memory wires,
        GoldilocksExt3.Ext3[] memory constants,
        uint256[4] memory publicInputsHash,
        GoldilocksExt3.Ext3[] memory slots,
        bool second
    ) private view {
        GoldilocksExt3.Ext3 memory alpha =
            _jsonExt3(json, string.concat(vpath, second ? ".alpha2" : ".alpha"));
        GoldilocksExt3.Ext3 memory recorded =
            _jsonExt3(json, string.concat(vpath, second ? ".expected_aggregation2" : ".expected_aggregation"));

        // 1. The recorded aggregate really is sum_c alpha^c * slot_c over the
        //    recorded slots (checks the JSON against Solidity's own reducer).
        GoldilocksExt3.Ext3 memory reduced = GoldilocksExt3.reduceWithPowers(slots, alpha);
        _assertExtEq(reduced, recorded, "recorded aggregate != reduceWithPowers(recorded slots)");

        // 2. The Solidity gate evaluator reproduces it from wires/constants.
        GoldilocksExt3.Ext3 memory actual = Plonky2GateEvaluatorExt3.evalCombined(
            wires,
            constants,
            publicInputsHash,
            alpha,
            gates,
            cfg.numSelectors,
            cfg.numConstants,
            cfg.numGateConstraints,
            cfg.numWires,
            cfg.quotientDegreeFactor
        );
        _assertExtEq(actual, recorded, "Solidity evaluator != Rust production vector");
    }

    // ------------------------------------------------------------------
    // JSON helpers (same limb conventions as Plonky2GateEvaluatorExt3.t.sol)
    // ------------------------------------------------------------------

    function _cfg(string memory json, string memory base) private pure returns (Cfg memory c) {
        c.numWires = vm.parseJsonUint(json, string.concat(base, ".config.num_wires"));
        c.numConstants = vm.parseJsonUint(json, string.concat(base, ".config.num_constants"));
        c.numSelectors = vm.parseJsonUint(json, string.concat(base, ".config.num_selectors"));
        c.numGateConstraints = vm.parseJsonUint(json, string.concat(base, ".config.num_gate_constraints"));
        c.quotientDegreeFactor = vm.parseJsonUint(json, string.concat(base, ".config.quotient_degree_factor"));
        c.numGates = vm.parseJsonUint(json, string.concat(base, ".num_gates"));
        c.numWireSets = vm.parseJsonUint(json, string.concat(base, ".num_wire_sets"));
        c.numVectors = vm.parseJsonUint(json, string.concat(base, ".num_vectors"));
    }

    function _jsonGates(string memory json, string memory base, uint256 count)
        private
        pure
        returns (Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates)
    {
        gates = new Plonky2GateEvaluatorExt3.GateInfoV2[](count);
        for (uint256 i = 0; i < count; ++i) {
            string memory prefix = string.concat(base, ".gates[", vm.toString(i), "].");
            gates[i] = Plonky2GateEvaluatorExt3.GateInfoV2({
                gateId: _jsonU8(json, string.concat(prefix, "gate_id")),
                selectorIndex: _jsonU8(json, string.concat(prefix, "selector_index")),
                groupStart: _jsonU8(json, string.concat(prefix, "group_start")),
                groupEnd: _jsonU8(json, string.concat(prefix, "group_end")),
                gateRowIndex: _jsonU8(json, string.concat(prefix, "gate_row_index")),
                numConstraints: _jsonU16(json, string.concat(prefix, "num_constraints")),
                numOrConsts: _jsonU16(json, string.concat(prefix, "num_or_consts")),
                param2: _jsonU16(json, string.concat(prefix, "param2")),
                param3: _jsonU16(json, string.concat(prefix, "param3"))
            });
        }
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
            values[i] = GoldilocksExt3.Ext3({
                c0: _rawFieldLimb(limbs[i][0]),
                c1: _rawFieldLimb(limbs[i][1]),
                c2: _rawFieldLimb(limbs[i][2])
            });
        }
    }

    function _jsonExt3(string memory json, string memory path)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        string[] memory limbs = abi.decode(vm.parseJson(json, path), (string[]));
        assertEq(limbs.length, 3, "Ext3 JSON value must have c0,c1,c2");
        value = GoldilocksExt3.Ext3({
            c0: _rawFieldLimb(limbs[0]),
            c1: _rawFieldLimb(limbs[1]),
            c2: _rawFieldLimb(limbs[2])
        });
    }

    function _jsonHash(string memory json, string memory path) private pure returns (uint256[4] memory values) {
        string[] memory encoded = abi.decode(vm.parseJson(json, path), (string[]));
        assertEq(encoded.length, 4, "public_inputs_hash must have 4 limbs");
        for (uint256 i = 0; i < 4; ++i) {
            values[i] = _rawFieldLimb(encoded[i]);
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

    function _assertExtEq(
        GoldilocksExt3.Ext3 memory actual,
        GoldilocksExt3.Ext3 memory expected,
        string memory what
    ) private pure {
        assertEq(actual.c0, expected.c0, what);
        assertEq(actual.c1, expected.c1, what);
        assertEq(actual.c2, expected.c2, what);
    }
}
