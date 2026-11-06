// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";
import {Plonky2GateEvaluatorExt3} from "../src/Plonky2GateEvaluatorExt3.sol";
import {PoseidonPublicInputsHash} from "../src/PoseidonPublicInputsHash.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {MAX_COMPACT_PROOF_BYTES_V2} from "../src/generated/MleWhirV2.sol";

/// @notice Gas benchmark over a sampled degree-13 proof whose circuit reproduces the production
/// SHAPE of the deployed parent profiles: the union of every deployed gate family (gate ids
/// 0..=13 with the production parameters), 103 public inputs (the largest deployed count), six
/// constants, four selector groups and 21 WHIR variables.
/// @dev The fixture is produced by the ignored, explicit Rust generator in
/// `mle/tests/v2_production_shape.rs`; no Solidity-side reconstruction or hand-patched config is
/// used. Execution gas is measured as `gasleft()` deltas around raw `staticcall`s so that the
/// numbers exclude the test harness' own ABI encoding and include only what a caller pays after
/// intrinsic calldata gas.
contract V2ProductionShapeFixtureTest is Test {
    string private constant FIXTURE = "test/fixtures/v2_production_shape.json";
    uint256 private constant MAX_PRODUCTION_VERIFY_GAS = 30_000_000;
    uint256 private constant PRODUCTION_NUM_PUBLIC_INPUTS = 103;

    struct ShapeFixture {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes compact;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    function test_productionShapeFixtureMatchesDeployedDimensions() external {
        ShapeFixture memory fixture = _fixture();
        assertEq(fixture.config.circuit.degreeBits, 13, "degree bits");
        assertEq(fixture.config.circuit.numPublicInputs, PRODUCTION_NUM_PUBLIC_INPUTS, "public inputs");
        assertEq(fixture.config.circuit.numRoutedWires, 80, "routed wires");
        assertEq(fixture.config.circuit.numWires, 135, "wires");
        // The union gate set (ExponentiationGate included) forms four selector groups, exactly like
        // the deployed `post_close_claim` / `withdrawal_claim` profiles (6 = 4 selectors + 2 constants).
        assertEq(fixture.config.circuit.numConstants, 6, "constants");
        assertEq(fixture.config.circuit.numSelectors, 4, "selector groups");
        assertEq(fixture.config.circuit.numGateConstraints, 123, "gate constraints");
        assertEq(fixture.config.circuit.quotientDegreeFactor, 8, "quotient degree factor");
        assertEq(fixture.proof.constituentWidth, 160, "constituent width");
        assertEq(fixture.proof.publicInputs.length, PRODUCTION_NUM_PUBLIC_INPUTS, "proof public inputs");
        assertEq(fixture.config.gates.length, 14, "gate rows (union of deployed families)");

        bool[14] memory seen;
        for (uint256 i = 0; i < fixture.config.gates.length; ++i) {
            uint8 id = fixture.config.gates[i].gateId;
            assertLt(id, 14, "unknown gate id");
            assertFalse(seen[id], "duplicate gate id");
            seen[id] = true;
        }
        for (uint256 id = 0; id < 14; ++id) {
            assertTrue(seen[id], "missing deployed gate family");
        }

        string memory json = vm.readFile(FIXTURE);
        uint256 actual = vm.parseJsonUint(json, ".stats.compactBytes");
        uint256 maximum = vm.parseJsonUint(json, ".sizeUpperBound.maxCompactBytes");
        assertEq(vm.parseJsonBool(json, ".sizeUpperBound.fitsCompactCap"), true);
        assertLe(actual, maximum, "sampled proof exceeds grammar-theoretic maximum");
        assertLe(maximum, MAX_COMPACT_PROOF_BYTES_V2, "strict maximum exceeds two SimpleCoder blobs");
        emit log_named_uint("production-shape compact bytes", actual);
        emit log_named_uint("production-shape WHIR hint bytes", vm.parseJsonUint(json, ".stats.whirHintBytes"));
        emit log_named_uint(
            "production-shape WHIR transcript bytes", vm.parseJsonUint(json, ".stats.whirTranscriptBytes")
        );
        emit log_named_uint("production-shape ABI proof bytes", vm.parseJsonUint(json, ".stats.solidityAbiBytes"));
    }

    function test_productionShapeVerifyCompactGas() external {
        ShapeFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);

        bytes memory callData = abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (fixture.compact));
        (uint256 used, bytes memory ret) = _measuredStaticcall(address(pinned), callData);
        assertTrue(abi.decode(ret, (bool)), "production-shape compact v2 proof");

        uint256 intrinsicGas = _calldataIntrinsicGas(callData);
        emit log_named_uint("production-shape verifyCompact execution gas", used);
        emit log_named_uint("production-shape verifyCompact calldata bytes", callData.length);
        emit log_named_uint("production-shape verifyCompact calldata intrinsic gas", intrinsicGas);
        emit log_named_uint("production-shape verifyCompact transaction gas upper bound", used + intrinsicGas);
        assertLt(used + intrinsicGas, MAX_PRODUCTION_VERIFY_GAS, "compact transaction exceeds block envelope");
        assertLt(address(pinned).code.length, 24_576, "pinned compact adapter exceeds EIP-170");
    }

    function test_productionShapeVerifyCompactPublicInputsGas() external {
        ShapeFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, fixture.config);

        bytes memory callData = abi.encodeCall(PinnedMleVerifierV2.verifyCompactPublicInputs, (fixture.compact));
        (uint256 used, bytes memory ret) = _measuredStaticcall(address(pinned), callData);
        uint256[] memory publicInputs = abi.decode(ret, (uint256[]));
        assertEq(publicInputs.length, PRODUCTION_NUM_PUBLIC_INPUTS, "authenticated public input length");
        for (uint256 i = 0; i < publicInputs.length; ++i) {
            assertEq(publicInputs[i], fixture.proof.publicInputs[i], "authenticated public input value");
        }

        uint256 intrinsicGas = _calldataIntrinsicGas(callData);
        emit log_named_uint("production-shape verifyCompactPublicInputs execution gas", used);
        emit log_named_uint("production-shape verifyCompactPublicInputs calldata bytes", callData.length);
        emit log_named_uint("production-shape verifyCompactPublicInputs calldata intrinsic gas", intrinsicGas);
        emit log_named_uint(
            "production-shape verifyCompactPublicInputs transaction gas upper bound", used + intrinsicGas
        );
        assertLt(used + intrinsicGas, MAX_PRODUCTION_VERIFY_GAS, "PI-return transaction exceeds block envelope");
    }

    function test_productionShapeCoreVerifyGas() external {
        ShapeFixture memory fixture = _fixture();
        MleVerifierV2 core = _deployCore(fixture);

        bytes memory callData = abi.encodeCall(MleVerifierV2.verify, (fixture.proof, fixture.config));
        (uint256 used, bytes memory ret) = _measuredStaticcall(address(core), callData);
        assertTrue(abi.decode(ret, (bool)), "production-shape core v2 proof");

        uint256 intrinsicGas = _calldataIntrinsicGas(callData);
        emit log_named_uint("production-shape core verify execution gas", used);
        emit log_named_uint("production-shape core verify calldata bytes", callData.length);
        emit log_named_uint("production-shape core verify calldata intrinsic gas", intrinsicGas);
        emit log_named_uint("production-shape core verify transaction gas upper bound", used + intrinsicGas);
        assertLt(used + intrinsicGas, MAX_PRODUCTION_VERIFY_GAS, "core transaction exceeds block envelope");
        assertLt(address(core).code.length, 24_576, "v2 core exceeds EIP-170");
    }

    /// @dev Isolates the two shape-dependent terminal costs that the max-resource fixture under-
    /// represents: the Poseidon hash of the 103 public inputs (ceil(103 / 8) = 13 permutations)
    /// and the combined gate evaluation over all 14 deployed gate families. The gate evaluation
    /// is arithmetic over field elements, so its gas does not depend on the challenge value; a
    /// fixed alpha is used here instead of re-deriving the transcript.
    function test_productionShapeTerminalShareGas() external {
        ShapeFixture memory fixture = _fixture();

        (uint256 piHashGas, uint256[4] memory piHash) = this.profilePublicInputHash(fixture.proof.publicInputs);
        emit log_named_uint("production-shape 103-PI Poseidon hash gas (13 permutations)", piHashGas);
        assertTrue(piHash[0] | piHash[1] | piHash[2] | piHash[3] != 0);

        uint256[] memory onePublicInput = new uint256[](1);
        onePublicInput[0] = fixture.proof.publicInputs[0];
        (uint256 onePiHashGas,) = this.profilePublicInputHash(onePublicInput);
        emit log_named_uint("reference 1-PI Poseidon hash gas (1 permutation)", onePiHashGas);

        uint256[] memory eightPublicInputs = new uint256[](8);
        for (uint256 i = 0; i < 8; ++i) {
            eightPublicInputs[i] = fixture.proof.publicInputs[i];
        }
        (uint256 eightPiHashGas,) = this.profilePublicInputHash(eightPublicInputs);
        emit log_named_uint("reference 8-PI Poseidon hash gas (1 permutation)", eightPiHashGas);

        GoldilocksExt3.Ext3[] memory constants = new GoldilocksExt3.Ext3[](fixture.config.circuit.numConstants);
        for (uint256 i = 0; i < constants.length; ++i) {
            constants[i] = fixture.proof.gatePreprocessed[i];
        }
        GoldilocksExt3.Ext3 memory alpha = GoldilocksExt3.Ext3({c0: 1, c1: 2, c2: 3});
        uint256 beforeGas = gasleft();
        GoldilocksExt3.Ext3 memory gateEvaluation = Plonky2GateEvaluatorExt3.evalCombined(
            fixture.proof.gateWitness,
            constants,
            piHash,
            alpha,
            fixture.config.gates,
            fixture.config.circuit.numSelectors,
            fixture.config.circuit.numConstants,
            fixture.config.circuit.numGateConstraints,
            fixture.config.circuit.numWires,
            fixture.config.circuit.quotientDegreeFactor
        );
        uint256 gateGas = beforeGas - gasleft();
        emit log_named_uint("production-shape 14-family gate evaluation gas", gateGas);
        assertTrue(gateEvaluation.c0 | gateEvaluation.c1 | gateEvaluation.c2 != 0);
    }

    function profilePublicInputHash(uint256[] calldata publicInputs)
        external
        view
        returns (uint256 gasUsed, uint256[4] memory hash)
    {
        uint256[] memory inputs = publicInputs;
        uint256 beforeGas = gasleft();
        hash = PoseidonPublicInputsHash.hashNoPad(inputs);
        gasUsed = beforeGas - gasleft();
    }

    function _measuredStaticcall(address target, bytes memory callData)
        private
        view
        returns (uint256 used, bytes memory ret)
    {
        bool ok;
        uint256 beforeGas = gasleft();
        (ok, ret) = target.staticcall(callData);
        used = beforeGas - gasleft();
        assertTrue(ok, "measured staticcall reverted");
    }

    function _fixture() private view returns (ShapeFixture memory fixture) {
        string memory json = vm.readFile(FIXTURE);
        bytes memory proofAbi = vm.parseJsonBytes(json, ".solidityAbiProof.bytes");
        bytes memory configAbi = vm.parseJsonBytes(json, ".solidityAbiVerificationConfig.bytes");
        assertEq(proofAbi.length, vm.parseJsonUint(json, ".solidityAbiProof.byteLength"));
        assertEq(keccak256(proofAbi), vm.parseJsonBytes32(json, ".solidityAbiProof.keccak256"));
        assertEq(configAbi.length, vm.parseJsonUint(json, ".solidityAbiVerificationConfig.byteLength"));
        assertEq(keccak256(configAbi), vm.parseJsonBytes32(json, ".solidityAbiVerificationConfig.keccak256"));

        fixture.proof = abi.decode(proofAbi, (MleVerifierV2.MleProof));
        fixture.config = abi.decode(configAbi, (MleVerifierV2.VerificationConfig));
        fixture.compact = vm.parseJsonBytes(json, ".compactProof.bytes");
        assertEq(fixture.compact.length, vm.parseJsonUint(json, ".compactProof.byteLength"));
        assertEq(keccak256(fixture.compact), vm.parseJsonBytes32(json, ".compactProof.keccak256"));

        bytes memory protocolId = vm.parseJsonBytes(json, ".pinnedVerifier.whirProtocolId");
        assertEq(protocolId.length, 64, "WHIR protocol identifier length");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocolId, 0x20))
            second := mload(add(protocolId, 0x40))
        }
        fixture.whirProtocolId = [first, second];
        fixture.whirSessionId = vm.parseJsonBytes32(json, ".pinnedVerifier.whirSessionId");
        assertEq(fixture.proof.circuitDigest.length, 4, "circuit digest length");
        for (uint256 i = 0; i < 4; ++i) {
            fixture.circuitDigest[i] = uint64(fixture.proof.circuitDigest[i]);
        }
    }

    function _deployCore(ShapeFixture memory fixture) private returns (MleVerifierV2 core) {
        core = new MleVerifierV2(
            block.chainid,
            fixture.proof.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            fixture.config
        );
    }

    function _calldataIntrinsicGas(bytes memory data) private pure returns (uint256 gasCost) {
        gasCost = 21_000;
        for (uint256 i = 0; i < data.length; ++i) {
            gasCost += data[i] == 0 ? 4 : 16;
        }
    }
}
