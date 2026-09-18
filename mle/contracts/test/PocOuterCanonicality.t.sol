// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";
import {BASE_FIELD_MODULUS_V2, LOG_ROUND_DEGREE_V2} from "../src/generated/MleWhirV2.sol";

/// @notice AUDIT PoC (re-audit of the outer verifier).
/// @dev `PinnedMleVerifierV2.verifyCompact` / `verifyCompactPublicInputs` decode with
/// `CompactMleProofV2.decodeForCoreVerification`, i.e. `_decode(..., requireCanonicalLimbs=false)`.
/// This test sweeps EVERY Goldilocks limb family that the lenient decoder lets through and
/// asserts that the pinned core rejects a non-canonical (>= p) representation on every entry
/// path, with the exact `InvalidMleProof()` selector (never an empty/OOG revert, never a panic,
/// and never acceptance).
contract PocOuterCanonicalityTest is Test {
    string private constant FIXTURE = "test/fixtures/v2_cross_language.json";
    string private constant CASE = ".cases[0]";

    struct Fix {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes compact;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    struct Layout {
        uint256 publicInputs;
        uint256 logRounds;
        uint256 logPreprocessed;
        uint256 logWitness;
        uint256 logNormInverse;
        uint256 gateRounds;
        uint256 gatePreprocessed;
        uint256 gateWitness;
        uint256 preprocessedLength;
        uint256 normInverseLength;
        uint256 gateDegree;
    }

    function test_poc_baselineCompactProofIsAccepted() external {
        Fix memory f = _fixture();
        (, PinnedMleVerifierV2 pinned) = _deploy(f);
        assertTrue(pinned.verifyCompact(f.compact), "baseline compact proof must verify");
        uint256[] memory pi = pinned.verifyCompactPublicInputs(f.compact);
        assertEq(pi.length, f.proof.publicInputs.length, "baseline PI length");
        for (uint256 i = 0; i < pi.length; ++i) {
            assertEq(pi[i], f.proof.publicInputs[i], "baseline PI value");
        }
    }

    /// @notice Non-canonical limbs in the public-input vector and in the first/last element of
    /// every Ext3 family, on all three limbs, through the lenient (core-bound) decoder.
    /// Split per family so no single Foundry transaction has to fund ~130 full verifications.
    function test_poc_nonCanonicalPublicInput() external {
        _runFamily(0);
    }

    function test_poc_nonCanonicalLogRoundCoefficient() external {
        _runFamily(1);
    }

    function test_poc_nonCanonicalLogPreprocessed() external {
        _runFamily(2);
    }

    function test_poc_nonCanonicalLogWitness() external {
        _runFamily(3);
    }

    function test_poc_nonCanonicalLogNormInverse() external {
        _runFamily(4);
    }

    function test_poc_nonCanonicalGateRoundCoefficient() external {
        _runFamily(5);
    }

    function test_poc_nonCanonicalGatePreprocessed() external {
        _runFamily(6);
    }

    function test_poc_nonCanonicalGateWitness() external {
        _runFamily(7);
    }

    function _runFamily(uint256 family) private {
        Fix memory f = _fixture();
        (, PinnedMleVerifierV2 pinned) = _deploy(f);
        Layout memory l = _layout(f.config, f.compact);
        if (family == 0) {
            _sweep(pinned, f.compact, l.publicInputs, f.config.circuit.numPublicInputs, 1, "publicInputs");
        } else if (family == 1) {
            _sweep(pinned, f.compact, l.logRounds, f.config.circuit.degreeBits * LOG_ROUND_DEGREE_V2, 3, "logRound");
        } else if (family == 2) {
            _sweep(pinned, f.compact, l.logPreprocessed, l.preprocessedLength, 3, "logPreprocessed");
        } else if (family == 3) {
            _sweep(pinned, f.compact, l.logWitness, f.config.circuit.numWires, 3, "logWitness");
        } else if (family == 4) {
            _sweep(pinned, f.compact, l.logNormInverse, l.normInverseLength, 3, "logNormInverse");
        } else if (family == 5) {
            _sweep(pinned, f.compact, l.gateRounds, f.config.circuit.degreeBits * l.gateDegree, 3, "gateRound");
        } else if (family == 6) {
            _sweep(pinned, f.compact, l.gatePreprocessed, l.preprocessedLength, 3, "gatePreprocessed");
        } else {
            _sweep(pinned, f.compact, l.gateWitness, f.config.circuit.numWires, 3, "gateWitness");
        }
    }

    /// @dev Mutate the first and last element of a family, limb by limb.
    function _sweep(
        PinnedMleVerifierV2 pinned,
        bytes memory canonical,
        uint256 base,
        uint256 count,
        uint256 limbsPerElement,
        string memory family
    ) private {
        uint256 stride = limbsPerElement * 8;
        uint256[2] memory elements = [uint256(0), count - 1];
        for (uint256 e = 0; e < 2; ++e) {
            if (e == 1 && count == 1) break;
            for (uint256 limb = 0; limb < limbsPerElement; ++limb) {
                uint256 offset = base + elements[e] * stride + limb * 8;
                bytes memory mutated = _clone(canonical);
                // p itself is the smallest non-canonical u64 encoding.
                _writeU64Le(mutated, offset, BASE_FIELD_MODULUS_V2);
                _assertRejected(
                    pinned,
                    mutated,
                    string.concat(family, ".element", vm.toString(elements[e]), ".limb", vm.toString(limb))
                );
            }
        }
    }

    function _assertRejected(PinnedMleVerifierV2 pinned, bytes memory compact, string memory label) private {
        (bool ok, bytes memory reason) =
            address(pinned).staticcall(abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (compact)));
        assertFalse(ok, string.concat(label, ": verifyCompact unexpectedly accepted"));
        assertEq(
            reason,
            abi.encodeWithSelector(InvalidMleProof.selector),
            string.concat(label, ": verifyCompact wrong selector (empty = OOG)")
        );

        (ok, reason) =
            address(pinned).staticcall(abi.encodeCall(PinnedMleVerifierV2.verifyCompactPublicInputs, (compact)));
        assertFalse(ok, string.concat(label, ": verifyCompactPublicInputs unexpectedly accepted"));
        assertEq(
            reason,
            abi.encodeWithSelector(InvalidMleProof.selector),
            string.concat(label, ": verifyCompactPublicInputs wrong selector")
        );

        assertEq(
            uint256(pinned.fraudVerdictCompact(compact, bytes32(0))),
            0,
            string.concat(label, ": fraudVerdictCompact must be INVALID")
        );
    }

    function _layout(MleVerifierV2.VerificationConfig memory config, bytes memory compact)
        private
        pure
        returns (Layout memory l)
    {
        l.preprocessedLength = config.circuit.numConstants + config.circuit.numRoutedWires;
        l.normInverseLength = 2 * config.circuit.numRoutedWires;
        l.gateDegree = config.circuit.quotientDegreeFactor + 2;
        l.publicInputs = 8 + 8 + 4 + 4 * 8;
        uint256 cursor = l.publicInputs + config.circuit.numPublicInputs * 8 + 3 * 32;
        // Two u32-length-prefixed opaque WHIR blobs.
        cursor += 4 + _readU32Le(compact, cursor);
        cursor += 4 + _readU32Le(compact, cursor);
        l.logRounds = cursor;
        cursor += config.circuit.degreeBits * LOG_ROUND_DEGREE_V2 * 24;
        l.logPreprocessed = cursor;
        cursor += l.preprocessedLength * 24;
        l.logWitness = cursor;
        cursor += config.circuit.numWires * 24;
        l.logNormInverse = cursor;
        cursor += l.normInverseLength * 24;
        l.gateRounds = cursor;
        cursor += config.circuit.degreeBits * l.gateDegree * 24;
        l.gatePreprocessed = cursor;
        cursor += l.preprocessedLength * 24;
        l.gateWitness = cursor;
        cursor += config.circuit.numWires * 24;
        require(cursor == compact.length, "PoC compact layout drift");
    }

    function _fixture() private view returns (Fix memory f) {
        string memory json = vm.readFile(FIXTURE);
        bytes memory proofAbi = vm.parseJsonBytes(json, string.concat(CASE, ".solidityAbiProof.bytes"));
        bytes memory configAbi = vm.parseJsonBytes(json, string.concat(CASE, ".solidityAbiVerificationConfig.bytes"));
        f.proof = abi.decode(proofAbi, (MleVerifierV2.MleProof));
        f.config = abi.decode(configAbi, (MleVerifierV2.VerificationConfig));
        f.compact = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));

        bytes memory protocolId = vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.whirProtocolId"));
        require(protocolId.length == 64, "PoC WHIR protocol id length");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocolId, 0x20))
            second := mload(add(protocolId, 0x40))
        }
        f.whirProtocolId = [first, second];
        f.whirSessionId = vm.parseJsonBytes32(json, string.concat(CASE, ".verificationKey.whirSessionId"));
        for (uint256 i = 0; i < 4; ++i) {
            f.circuitDigest[i] = uint64(f.proof.circuitDigest[i]);
        }
    }

    function _deploy(Fix memory f) private returns (MleVerifierV2 core, PinnedMleVerifierV2 pinned) {
        core = new MleVerifierV2(
            block.chainid,
            f.proof.preprocessedRoot,
            f.whirProtocolId,
            f.whirSessionId,
            f.circuitDigest,
            f.config
        );
        pinned = new PinnedMleVerifierV2(core, f.config);
    }

    function _clone(bytes memory source) private pure returns (bytes memory copy) {
        copy = new bytes(source.length);
        for (uint256 i = 0; i < source.length; ++i) {
            copy[i] = source[i];
        }
    }

    function _writeU64Le(bytes memory target, uint256 offset, uint256 value) private pure {
        for (uint256 i = 0; i < 8; ++i) {
            target[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
    }

    function _readU32Le(bytes memory source, uint256 offset) private pure returns (uint256 value) {
        for (uint256 i = 0; i < 4; ++i) {
            value |= uint256(uint8(source[offset + i])) << (8 * i);
        }
    }
}
