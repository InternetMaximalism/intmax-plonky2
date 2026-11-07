// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {console} from "forge-std/console.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";

/// @dev Gas-profiling harness: one honest verification per fixture through the production
/// entry points, measured with a pre-encoded calldata buffer and a raw staticcall so the
/// caller-side argument copy is excluded from the measurement.
contract GasProfileTest is Test {
    struct Fx {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes compact;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    function _max() internal view returns (Fx memory fx) {
        string memory json = vm.readFile("test/fixtures/v2_max_resource.json");
        fx.proof = abi.decode(vm.parseJsonBytes(json, ".solidityAbiProof.bytes"), (MleVerifierV2.MleProof));
        fx.config = abi.decode(
            vm.parseJsonBytes(json, ".solidityAbiVerificationConfig.bytes"), (MleVerifierV2.VerificationConfig)
        );
        fx.compact = vm.parseJsonBytes(json, ".compactProof.bytes");
        _ids(
            fx,
            vm.parseJsonBytes(json, ".pinnedVerifier.whirProtocolId"),
            vm.parseJsonBytes32(json, ".pinnedVerifier.whirSessionId")
        );
    }

    function _small() internal view returns (Fx memory fx) {
        string memory json = vm.readFile("test/fixtures/v2_cross_language.json");
        fx.proof = abi.decode(vm.parseJsonBytes(json, ".cases[0].solidityAbiProof.bytes"), (MleVerifierV2.MleProof));
        fx.config = abi.decode(
            vm.parseJsonBytes(json, ".cases[0].solidityAbiVerificationConfig.bytes"), (MleVerifierV2.VerificationConfig)
        );
        fx.compact = vm.parseJsonBytes(json, ".cases[0].compactProof.bytes");
        _ids(
            fx,
            vm.parseJsonBytes(json, ".cases[0].verificationKey.whirProtocolId"),
            vm.parseJsonBytes32(json, ".cases[0].verificationKey.whirSessionId")
        );
    }

    function _ids(Fx memory fx, bytes memory protocolId, bytes32 sessionId) internal pure {
        require(protocolId.length == 64, "protocol id length");
        bytes32 a;
        bytes32 b;
        assembly ("memory-safe") {
            a := mload(add(protocolId, 0x20))
            b := mload(add(protocolId, 0x40))
        }
        fx.whirProtocolId = [a, b];
        fx.whirSessionId = sessionId;
        for (uint256 i; i < 4; ++i) {
            fx.circuitDigest[i] = uint64(fx.proof.circuitDigest[i]);
        }
    }

    function _deploy(Fx memory fx) internal returns (MleVerifierV2 core, PinnedMleVerifierV2 pinned) {
        core = new MleVerifierV2(
            block.chainid, fx.proof.preprocessedRoot, fx.whirProtocolId, fx.whirSessionId, fx.circuitDigest, fx.config
        );
        pinned = new PinnedMleVerifierV2(core, fx.config);
        console.log("CODESIZE core pinned", address(core).code.length, address(pinned).code.length);
    }

    function _stats(bytes memory data) internal pure returns (uint256 zeros, uint256 nonzeros) {
        for (uint256 i = 0; i < data.length; ++i) {
            if (data[i] == 0) ++zeros;
            else ++nonzeros;
        }
    }

    function _measure(address target, bytes memory cd, string memory label) internal view {
        (uint256 zeros, uint256 nonzeros) = _stats(cd);
        // legacy intrinsic (4/16 per byte) and the EIP-7623 floor (10 per token, 4 tokens per nonzero byte)
        uint256 legacy = 21_000 + 4 * zeros + 16 * nonzeros;
        uint256 floor = 21_000 + 10 * (zeros + 4 * nonzeros);
        console.log("CALLDATA bytes zeros nonzeros", cd.length, zeros, nonzeros);
        console.log("INTRINSIC legacy floor7623", legacy, floor);
        console.log("BEGIN", label);
        uint256 before = gasleft();
        (bool ok, bytes memory ret) = target.staticcall(cd);
        uint256 used = before - gasleft();
        console.log("END", label);
        require(ok, "call failed");
        console.log("TOTAL staticcall gas / return bytes", used, ret.length);
    }

    function _runAll(Fx memory fx, string memory which) internal {
        (, PinnedMleVerifierV2 pinned) = _deploy(fx);
        _measure(address(pinned), abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (fx.compact)), which);
    }

    function test_small_verifyCompact() external {
        _runAll(_small(), "small verifyCompact");
    }

    function test_max_verifyCompact() external {
        _runAll(_max(), "max verifyCompact");
    }

    function test_small_verifyCompactPublicInputs() external {
        Fx memory fx = _small();
        (, PinnedMleVerifierV2 pinned) = _deploy(fx);
        _measure(
            address(pinned), abi.encodeCall(PinnedMleVerifierV2.verifyCompactPublicInputs, (fx.compact)), "small PI"
        );
    }

    function test_max_verifyCompactPublicInputs() external {
        Fx memory fx = _max();
        (, PinnedMleVerifierV2 pinned) = _deploy(fx);
        _measure(address(pinned), abi.encodeCall(PinnedMleVerifierV2.verifyCompactPublicInputs, (fx.compact)), "max PI");
    }

    function test_small_coreVerify() external {
        Fx memory fx = _small();
        (MleVerifierV2 core,) = _deploy(fx);
        _measure(address(core), abi.encodeCall(MleVerifierV2.verify, (fx.proof, fx.config)), "small core.verify");
    }

    function test_max_coreVerify() external {
        Fx memory fx = _max();
        (MleVerifierV2 core,) = _deploy(fx);
        _measure(address(core), abi.encodeCall(MleVerifierV2.verify, (fx.proof, fx.config)), "max core.verify");
    }
}
