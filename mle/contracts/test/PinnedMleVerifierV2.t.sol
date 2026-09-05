// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {CircuitConfigV2} from "../src/CircuitConfigV2.sol";
import {
    InvalidMleProof,
    InvalidMleVerifierChainId,
    InvalidMleVerifierConfiguration,
    MleProofEngineUnavailable
} from "../src/MleProofErrors.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";
import {Plonky2GateEvaluatorExt3} from "../src/Plonky2GateEvaluatorExt3.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";
import {COMPACT_MAGIC_V2, MLE_PROTOCOL_VERSION_CURRENT} from "../src/generated/MleWhirV2.sol";

/// @dev Minimal ABI-compatible core used to isolate the adapter's ownership and verdict rules.
/// Real Rust-proof verification and gas are exercised through the production core in
/// `V2CrossLanguageFixture.t.sol`.
contract MockMleVerifierV2Core {
    uint256 public immutable allowedChainId;
    bytes32 public immutable circuitConfigDigest;
    bytes32 public immutable whirParametersDigest;
    uint64 public immutable circuitDigest0;
    uint64 public immutable circuitDigest1;
    uint64 public immutable circuitDigest2;
    uint64 public immutable circuitDigest3;
    bytes32 private immutable _configEncodingHash;

    constructor(
        uint256 chainId_,
        bytes32 circuitConfigDigest_,
        bytes32 whirParametersDigest_,
        uint64[4] memory circuitDigest_,
        bytes32 configEncodingHash_
    ) {
        allowedChainId = chainId_;
        circuitConfigDigest = circuitConfigDigest_;
        whirParametersDigest = whirParametersDigest_;
        circuitDigest0 = circuitDigest_[0];
        circuitDigest1 = circuitDigest_[1];
        circuitDigest2 = circuitDigest_[2];
        circuitDigest3 = circuitDigest_[3];
        _configEncodingHash = configEncodingHash_;
    }

    function verify(MleVerifierV2.MleProof calldata proof, MleVerifierV2.VerificationConfig calldata config)
        external
        view
        returns (bool)
    {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        if (keccak256(abi.encode(config)) != _configEncodingHash) revert InvalidMleVerifierConfiguration();
        if (proof.protocolVersion != MLE_PROTOCOL_VERSION_CURRENT) revert InvalidMleProof();
        if (proof.witnessRoot == bytes32(uint256(1))) revert InvalidMleProof();
        if (proof.witnessRoot == bytes32(uint256(2))) revert InvalidMleVerifierConfiguration();
        if (proof.witnessRoot == bytes32(uint256(3))) {
            assembly ("memory-safe") {
                invalid()
            }
        }
        if (proof.witnessRoot == bytes32(uint256(4))) return false;
        return true;
    }
}

contract PinnedMleVerifierV2Test is Test {
    struct Setup {
        MleVerifierV2.VerificationConfig config;
        uint64[4] circuitDigest;
        MockMleVerifierV2Core mockCore;
        PinnedMleVerifierV2 adapter;
    }

    function test_constructorPinsAndDeepCopiesTheCompleteConfiguration() external {
        Setup memory setup = _deploySetup();
        assertEq(address(setup.adapter.core()), address(setup.mockCore));
        assertEq(setup.adapter.allowedChainId(), block.chainid);
        assertLt(address(setup.adapter).code.length, 24_576, "adapter exceeds EIP-170");
        emit log_named_uint("PinnedMleVerifierV2 runtime bytes", address(setup.adapter).code.length);

        // Mutating the caller's memory value after construction cannot affect adapter storage.
        setup.config.kIs[0] = 999;
        setup.config.gates[0].gateId = 99;
        setup.config.whir.rounds[0].codewordLength = 999;
        setup.config.publicInputWireMap[0] = bytes1(uint8(setup.config.publicInputWireMap[0]) ^ 1);
        MleVerifierV2.MleProof memory proof = _proof(MLE_PROTOCOL_VERSION_CURRENT);
        assertTrue(setup.adapter.verify(proof));
    }

    function test_constructorRejectsWrongWhirAndCircuitConfiguration() external {
        MleVerifierV2.VerificationConfig memory config = _config();
        uint64[4] memory circuitDigest = _circuitDigest();
        MockMleVerifierV2Core mockCore = _mockCore(config, circuitDigest, block.chainid);

        MleVerifierV2.VerificationConfig memory wrongWhir = _cloneConfig(config);
        ++wrongWhir.whir.inDomainSamples;
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        new PinnedMleVerifierV2(MleVerifierV2(address(mockCore)), wrongWhir);

        MleVerifierV2.VerificationConfig memory wrongCircuit = _cloneConfig(config);
        ++wrongCircuit.gates[0].param3;
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        new PinnedMleVerifierV2(MleVerifierV2(address(mockCore)), wrongCircuit);

        MleVerifierV2.VerificationConfig memory wrongMap = _cloneConfig(config);
        wrongMap.publicInputWireMap[0] = bytes1(uint8(wrongMap.publicInputWireMap[0]) ^ 1);
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        new PinnedMleVerifierV2(MleVerifierV2(address(mockCore)), wrongMap);

        MleVerifierV2.VerificationConfig memory shortMap = _cloneConfig(config);
        shortMap.publicInputWireMap = hex"0000";
        vm.expectRevert(InvalidMleProof.selector);
        new PinnedMleVerifierV2(MleVerifierV2(address(mockCore)), shortMap);
    }

    function test_constructorRejectsNonContractAndWrongChainCore() external {
        MleVerifierV2.VerificationConfig memory config = _config();
        vm.expectRevert(
            abi.encodeWithSelector(PinnedMleVerifierV2.InvalidPinnedMleVerifierCore.selector, address(0xBEEF))
        );
        new PinnedMleVerifierV2(MleVerifierV2(address(0xBEEF)), config);

        uint64[4] memory circuitDigest = _circuitDigest();
        MockMleVerifierV2Core wrongChain = _mockCore(config, circuitDigest, block.chainid + 1);
        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierChainId.selector, block.chainid + 1, block.chainid));
        new PinnedMleVerifierV2(MleVerifierV2(address(wrongChain)), config);
    }

    function test_verifyAndFraudVerdictGuardTheChainBeforeExpansionOrDecoding() external {
        Setup memory setup = _deploySetup();
        uint256 originalChainId = block.chainid;
        vm.chainId(originalChainId + 1);

        vm.expectRevert(abi.encodeWithSelector(MleProofEngineUnavailable.selector, originalChainId + 1));
        setup.adapter.verify(_proof(1));
        vm.expectRevert(abi.encodeWithSelector(MleProofEngineUnavailable.selector, originalChainId + 1));
        setup.adapter.verifyCompact(hex"010203");
        vm.expectRevert(abi.encodeWithSelector(MleProofEngineUnavailable.selector, originalChainId + 1));
        setup.adapter.verifyCompactPublicInputs(hex"010203");
        assertEq(
            setup.adapter.fraudVerdictEncoded(hex"010203", bytes32(0)),
            2,
            "wrong-chain malformed bytes must be unevaluable"
        );
        assertEq(
            setup.adapter.fraudVerdictCompact(hex"010203", bytes32(0)),
            2,
            "wrong-chain malformed compact bytes must be unevaluable"
        );
        vm.chainId(originalChainId);
    }

    function test_productionAdapterHasNoLegacyVerificationBypassSelectors() external {
        Setup memory setup = _deploySetup();
        (bool ok,) = address(setup.adapter).staticcall(
            abi.encodeWithSignature("fraudVerdictCompact(bytes,bytes32,bool)", hex"", bytes32(0), true)
        );
        assertFalse(ok, "legacy compact bypass selector remains callable");

        (ok,) = address(setup.adapter).staticcall(
            abi.encodeWithSignature("compactFraudVerdictBody(bytes,bytes32,bool)", hex"", bytes32(0), true)
        );
        assertFalse(ok, "legacy compact-body bypass selector remains callable");

        (ok,) = address(setup.adapter).staticcall(
            abi.encodeWithSignature("fraudVerdictEncoded(bytes,bytes32,bool)", hex"", bytes32(0), true)
        );
        assertFalse(ok, "legacy encoded bypass selector remains callable");
    }

    function test_fraudVerdictRejectsMalformedTrailingAndOldVersionBytes() external {
        Setup memory setup = _deploySetup();
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        setup.adapter.compactFraudVerdictBody(hex"010203", bytes32(0));

        bytes memory canonical = abi.encode(_proof(MLE_PROTOCOL_VERSION_CURRENT));
        assertEq(
            setup.adapter.fraudVerdictEncoded(bytes.concat(canonical, hex"00"), bytes32(0)),
            0,
            "trailing ABI bytes"
        );
        assertEq(setup.adapter.fraudVerdictEncoded(hex"010203", bytes32(0)), 0, "malformed ABI");
        assertEq(setup.adapter.fraudVerdictEncoded(abi.encode(_proof(1)), bytes32(0)), 0, "old version");
    }

    function test_fraudVerdictSeparatesProofPiConfigurationAndStarvation() external {
        Setup memory setup = _deploySetup();
        MleVerifierV2.MleProof memory proof = _proof(MLE_PROTOCOL_VERSION_CURRENT);
        proof.publicInputs = new uint256[](8);
        for (uint256 i = 0; i < 8; ++i) {
            proof.publicInputs[i] = i + 1;
        }
        bytes32 piHash = _publicInputsDigest(proof.publicInputs);
        assertEq(setup.adapter.fraudVerdictEncoded(abi.encode(proof), piHash), 1, "valid");
        assertEq(
            setup.adapter.fraudVerdictEncoded(abi.encode(proof), bytes32(uint256(piHash) ^ 1)), 4, "PI mismatch"
        );

        proof.witnessRoot = bytes32(uint256(1));
        assertEq(setup.adapter.fraudVerdictEncoded(abi.encode(proof), piHash), 0, "proof invalid");
        proof.witnessRoot = bytes32(uint256(2));
        assertEq(setup.adapter.fraudVerdictEncoded(abi.encode(proof), piHash), 2, "config unevaluable");
        proof.witnessRoot = bytes32(uint256(4));
        assertEq(setup.adapter.fraudVerdictEncoded(abi.encode(proof), piHash), 2, "false unevaluable");
        proof.witnessRoot = bytes32(uint256(3));
        (bool ok, bytes memory result) = address(setup.adapter).staticcall{gas: 1_000_000}(
            abi.encodeCall(PinnedMleVerifierV2.fraudVerdictEncoded, (abi.encode(proof), piHash))
        );
        assertTrue(ok, "classifier must preserve enough gas to return STARVED");
        assertEq(abi.decode(result, (uint8)), 3, "starved");
    }

    function test_compactFraudVerdictRequiresTheExactFourByteInvalidSelector() external {
        Setup memory setup = _deploySetup();
        bytes memory compact = _compactProof(0);

        vm.mockCallRevert(
            address(setup.mockCore), MleVerifierV2.verify.selector, abi.encodeWithSelector(InvalidMleProof.selector)
        );
        assertEq(setup.adapter.fraudVerdictCompact(compact, bytes32(0)), 0, "exact selector");
        vm.clearMockedCalls();

        vm.mockCallRevert(
            address(setup.mockCore),
            MleVerifierV2.verify.selector,
            bytes.concat(abi.encodeWithSelector(InvalidMleProof.selector), hex"00")
        );
        assertEq(
            setup.adapter.fraudVerdictCompact(compact, bytes32(0)), 2, "selector plus suffix must be UNEVALUABLE"
        );
        vm.clearMockedCalls();

        vm.mockCallRevert(address(setup.mockCore), MleVerifierV2.verify.selector, hex"deadbeef");
        assertEq(
            setup.adapter.fraudVerdictCompact(compact, bytes32(0)),
            2,
            "unknown four-byte selector must be UNEVALUABLE"
        );
        vm.clearMockedCalls();
    }

    function test_compactFraudVerdictSeparatesStrictDecodeCoreConfigAndDirectHelperFailures() external {
        Setup memory setup = _deploySetup();
        bytes memory compact = _compactProof(0);

        // The compact body is an isolated self-call implementation, not a public classifier.
        vm.expectRevert(InvalidMleVerifierConfiguration.selector);
        setup.adapter.compactFraudVerdictBody(compact, bytes32(0));

        bytes memory malformed = _cloneBytes(compact);
        malformed[0] ^= 0x01;
        assertEq(
            setup.adapter.fraudVerdictCompact(malformed, bytes32(0)),
            0,
            "strict decoder InvalidMleProof must convict"
        );

        // The mock core reserves witness-root tags 1 and 2 for proof-invalid and
        // configuration-invalid failures. Both compact proofs are syntactically canonical.
        assertEq(setup.adapter.fraudVerdictCompact(_compactProof(1), bytes32(0)), 0, "core proof invalid");
        assertEq(
            setup.adapter.fraudVerdictCompact(_compactProof(2), bytes32(0)),
            2,
            "core configuration failure must be UNEVALUABLE"
        );
        assertEq(
            setup.adapter.fraudVerdictCompact(_compactProof(4), bytes32(0)),
            2,
            "unexpected successful false return must be UNEVALUABLE"
        );
    }

    function test_compactFraudVerdictGasFloorNeverTurnsExhaustionIntoInvalid() external {
        Setup memory setup = _deploySetup();
        bytes memory exhaustingCompact = _compactProof(3);
        bytes memory exhaustingCall =
            abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (exhaustingCompact, bytes32(0)));

        bool sawContainedStarvation;
        uint256[8] memory budgets =
            [uint256(100_000), 150_000, 225_000, 350_000, 500_000, 750_000, 1_000_000, 2_000_000];
        for (uint256 i = 0; i < budgets.length; ++i) {
            (bool ok, bytes memory result) = address(setup.adapter).staticcall{gas: budgets[i]}(exhaustingCall);
            if (!ok) continue; // Below the outer frame's own return-gas floor.
            assertEq(result.length, 32, "contained verdict ABI length");
            uint8 verdict = abi.decode(result, (uint8));
            assertEq(verdict, 3, "contained exhaustion must be STARVED, never INVALID");
            sawContainedStarvation = true;
        }
        assertTrue(sawContainedStarvation, "no gas budget exercised the contained starvation boundary");

        bytes memory invalidCompact = _compactProof(1);
        bytes memory invalidCall =
            abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (invalidCompact, bytes32(0)));
        (bool invalidOk, bytes memory invalidResult) = address(setup.adapter).staticcall{gas: 2_000_000}(invalidCall);
        assertTrue(invalidOk, "adequately funded invalid-proof classification");
        assertEq(abi.decode(invalidResult, (uint8)), 0, "adequately funded exact InvalidMleProof");
    }

    function _deploySetup() private returns (Setup memory setup) {
        setup.config = _config();
        setup.circuitDigest = _circuitDigest();
        setup.mockCore = _mockCore(setup.config, setup.circuitDigest, block.chainid);
        setup.adapter = new PinnedMleVerifierV2(MleVerifierV2(address(setup.mockCore)), setup.config);
    }

    function _mockCore(MleVerifierV2.VerificationConfig memory config, uint64[4] memory circuitDigest, uint256 chainId)
        private
        returns (MockMleVerifierV2Core mockCore)
    {
        uint256[] memory digestVector = new uint256[](4);
        for (uint256 i = 0; i < 4; ++i) {
            digestVector[i] = circuitDigest[i];
        }
        bytes32 configDigest = CircuitConfigV2.digest(
            config.circuit, digestVector, config.kIs, config.subgroupGenPowers, config.gates, config.publicInputWireMap
        );
        mockCore = new MockMleVerifierV2Core(
            chainId, configDigest, keccak256(abi.encode(config.whir)), circuitDigest, keccak256(abi.encode(config))
        );
    }

    function _config() private pure returns (MleVerifierV2.VerificationConfig memory config) {
        config.circuit = CircuitConfigV2.Parameters({
            degreeBits: 2,
            numPublicInputs: 1,
            numConstants: 2,
            numRoutedWires: 1,
            numWires: 3,
            numSelectors: 1,
            numGateConstraints: 2,
            quotientDegreeFactor: 3
        });
        config.kIs = new uint256[](1);
        config.kIs[0] = 7;
        config.publicInputWireMap = hex"000000";
        config.subgroupGenPowers = new uint256[](2);
        config.subgroupGenPowers[0] = 9;
        config.subgroupGenPowers[1] = 81;
        config.gates = new Plonky2GateEvaluatorExt3.GateInfoV2[](1);
        config.gates[0] = Plonky2GateEvaluatorExt3.GateInfoV2({
            gateId: 3,
            selectorIndex: 0,
            groupStart: 0,
            groupEnd: 1,
            gateRowIndex: 0,
            numConstraints: 2,
            numOrConsts: 1,
            param2: 2,
            param3: 3
        });

        config.whir.numVariables = 10;
        config.whir.foldingFactor = 4;
        config.whir.numVectors = 1;
        config.whir.numCommitments = 3;
        config.whir.outDomainSamples = 5;
        config.whir.inDomainSamples = 6;
        config.whir.initialSumcheckRounds = 2;
        config.whir.numRounds = 1;
        config.whir.finalSumcheckRounds = 3;
        config.whir.finalSize = 16;
        config.whir.initialCodewordLength = 1024;
        config.whir.initialMerkleDepth = 10;
        config.whir.initialDomainGenerator = 11;
        config.whir.initialInterleavingDepth = 1;
        config.whir.initialNumVariables = 10;
        config.whir.initialCosetSize = 4;
        config.whir.initialNumCosets = 256;
        config.whir.initialSumcheckPowThreshold = 12;
        config.whir.finalPowThreshold = 13;
        config.whir.finalSumcheckPowThreshold = 14;
        config.whir.evaluationPoint = new GoldilocksExt3.Ext3[](0);
        config.whir.evaluationPoint2 = new GoldilocksExt3.Ext3[](0);
        config.whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        config.whir.rounds = new SpongefishWhirVerify.RoundParams[](1);
        config.whir.rounds[0] = SpongefishWhirVerify.RoundParams({
            codewordLength: 256,
            merkleDepth: 8,
            domainGenerator: 15,
            inDomainSamples: 2,
            outDomainSamples: 3,
            sumcheckRounds: 4,
            interleavingDepth: 1,
            cosetSize: 4,
            numCosets: 64,
            numVariables: 8,
            powThreshold: 16,
            sumcheckPowThreshold: 17
        });
    }

    function _circuitDigest() private pure returns (uint64[4] memory digest) {
        digest = [uint64(101), uint64(102), uint64(103), uint64(104)];
    }

    function _proof(uint256 protocolVersion) private pure returns (MleVerifierV2.MleProof memory proof) {
        proof.protocolVersion = protocolVersion;
    }

    function _cloneConfig(MleVerifierV2.VerificationConfig memory config)
        private
        pure
        returns (MleVerifierV2.VerificationConfig memory)
    {
        return abi.decode(abi.encode(config), (MleVerifierV2.VerificationConfig));
    }

    function _publicInputsDigest(uint256[] memory publicInputs) private pure returns (bytes32 digest) {
        for (uint256 i = 0; i < 8; ++i) {
            digest |= bytes32(publicInputs[i] << (224 - i * 32));
        }
    }

    /// @dev Build the unique compact encoding for `_config()` with zero-valued
    /// fixed vectors and empty WHIR streams. The mock core intentionally checks
    /// only the protocol version and the witness-root behavior tag.
    function _compactProof(uint8 witnessRootTag) private pure returns (bytes memory encoded) {
        MleVerifierV2.VerificationConfig memory config = _config();
        uint256 width = config.circuit.numConstants + config.circuit.numRoutedWires;
        if (config.circuit.numWires > width) width = config.circuit.numWires;
        uint256 normInverseLength = 2 * config.circuit.numRoutedWires;
        if (normInverseLength > width) width = normInverseLength;
        uint256 preprocessedLength = config.circuit.numConstants + config.circuit.numRoutedWires;
        uint256 gateDegree = config.circuit.quotientDegreeFactor + 2;

        uint256 encodedLength = 8 + 8 + 4 + 4 * 8 + config.circuit.numPublicInputs * 8 + 3 * 32 + 4 + 4
            + config.circuit.degreeBits * 5 * 24 + preprocessedLength * 24 + config.circuit.numWires * 24
            + normInverseLength * 24 + config.circuit.degreeBits * gateDegree * 24 + preprocessedLength * 24
            + config.circuit.numWires * 24;
        encoded = new bytes(encodedLength);

        bytes memory magic = abi.encodePacked(COMPACT_MAGIC_V2);
        for (uint256 i = 0; i < magic.length; ++i) {
            encoded[i] = magic[i];
        }
        _writeLe(encoded, 8, MLE_PROTOCOL_VERSION_CURRENT, 8);
        _writeLe(encoded, 16, width, 4);

        uint256 preprocessedRootOffset = 8 + 8 + 4 + 4 * 8 + config.circuit.numPublicInputs * 8;
        encoded[preprocessedRootOffset + 32 + 31] = bytes1(witnessRootTag);
    }

    function _writeLe(bytes memory output, uint256 offset, uint256 value, uint256 count) private pure {
        for (uint256 i = 0; i < count; ++i) {
            output[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
    }

    function _cloneBytes(bytes memory source) private pure returns (bytes memory clone) {
        clone = new bytes(source.length);
        for (uint256 i = 0; i < source.length; ++i) {
            clone[i] = source[i];
        }
    }
}
