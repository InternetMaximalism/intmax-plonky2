// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";

/// @notice AUDIT PoC (re-audit of the outer verifier), checklist item 5.
/// @dev Measures the fraud classifier on the *most expensive rejectable* compact proof an
/// attacker can post: the sampled max-resource proof with one mutated terminal limb, which
/// is only rejected after the complete grouped WHIR verification. The question is whether
/// `fraudVerdictCompact`'s starvation floor (`gasleft() < reserve + budget/8`, i.e. an invalid
/// verdict needs the body to consume less than ~86% of the frame's gas) still reaches the
/// slashing-grade INVALID verdict inside one 30M-gas block.
contract PocOuterFraudVerdictTest is Test {
    string private constant FIXTURE = "test/fixtures/v2_max_resource.json";

    struct Fix {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes compact;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    function test_poc_lateFailingInvalidProofVerdictAcrossGasBudgets() external {
        Fix memory f = _fixture();
        MleVerifierV2 core = _deployCore(f);
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, f.config);

        // Sanity: the honest compact proof verifies through the pinned adapter.
        uint256 before = gasleft();
        assertTrue(pinned.verifyCompact(f.compact), "baseline max-resource compact proof");
        emit log_named_uint("honest verifyCompact gas", before - gasleft());

        // Flip one bit of the LAST gate-witness limb. Nothing before the grouped WHIR check
        // can detect it: the limb is shape-correct and canonical, it changes only the folded
        // (gate, witness) claim that WHIR authenticates.
        bytes memory mutated = _clone(f.compact);
        uint256 lastLimb = f.compact.length - 24;
        mutated[lastLimb] = bytes1(uint8(mutated[lastLimb]) ^ 0x01);

        before = gasleft();
        (bool ok, bytes memory reason) =
            address(pinned).staticcall(abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (mutated)));
        emit log_named_uint("invalid verifyCompact gas (rejection cost)", before - gasleft());
        assertFalse(ok, "mutated proof must not verify");
        assertEq(reason.length, 4, "rejection must be a four-byte InvalidMleProof, not an OOG");

        uint256[6] memory budgets = [uint256(30_000_000), 28_000_000, 25_000_000, 20_000_000, 15_000_000, 10_000_000];
        for (uint256 i = 0; i < budgets.length; ++i) {
            (bool success, bytes memory result) = address(pinned).staticcall{gas: budgets[i]}(
                abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (mutated, bytes32(0)))
            );
            if (!success) {
                emit log_named_uint("budget (outer frame reverted)", budgets[i]);
                continue;
            }
            uint8 verdict = abi.decode(result, (uint8));
            emit log_named_uint("budget", budgets[i]);
            emit log_named_uint("  verdict (0=INVALID 2=UNEVALUABLE 3=STARVED)", verdict);
            assertTrue(verdict != 1 && verdict != 4, "an invalid proof must never be VALID/PI_MISMATCH");
        }

        // Worst case for the classifier: flip the LAST byte of the opaque WHIR hint blob. The
        // attacker fully controls those bytes, so this is the latest (most expensive) rejection
        // an adversary can force out of the grouped WHIR verification.
        bytes memory lateFail = _clone(f.compact);
        uint256 hintTail = _hintTailOffset(f);
        lateFail[hintTail] = bytes1(uint8(lateFail[hintTail]) ^ 0x01);
        before = gasleft();
        (ok, reason) = address(pinned).staticcall(abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (lateFail)));
        emit log_named_uint("late-WHIR-fail verifyCompact gas (rejection cost)", before - gasleft());
        assertFalse(ok, "hint-tail mutated proof must not verify");
        assertEq(reason.length, 4, "late rejection must be a four-byte InvalidMleProof");
        for (uint256 i = 0; i < budgets.length; ++i) {
            (bool success, bytes memory result) = address(pinned).staticcall{gas: budgets[i]}(
                abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (lateFail, bytes32(0)))
            );
            if (!success) {
                emit log_named_uint("late-fail budget (outer frame reverted)", budgets[i]);
                continue;
            }
            uint8 verdict = abi.decode(result, (uint8));
            emit log_named_uint("late-fail budget", budgets[i]);
            emit log_named_uint("  late-fail verdict (0=INVALID 3=STARVED)", verdict);
            assertTrue(verdict != 1 && verdict != 4, "an invalid proof must never be VALID/PI_MISMATCH");
        }

        // Also report the verdict for the honest proof at the same budgets, so the report can
        // separate "classifier is too tight" from "this proof is simply expensive".
        for (uint256 i = 0; i < budgets.length; ++i) {
            (bool success, bytes memory result) = address(pinned).staticcall{gas: budgets[i]}(
                abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (f.compact, bytes32(0)))
            );
            if (!success) {
                emit log_named_uint("honest budget (outer frame reverted)", budgets[i]);
                continue;
            }
            uint8 verdict = abi.decode(result, (uint8));
            emit log_named_uint("honest budget", budgets[i]);
            emit log_named_uint("  honest verdict (4=PI_MISMATCH expected)", verdict);
            assertTrue(verdict != 0, "an honest proof must never be classified INVALID");
        }
    }

    /// @dev Byte offset of the last byte of the compact encoding's WHIR hint blob.
    function _hintTailOffset(Fix memory f) private pure returns (uint256) {
        uint256 cursor = 8 + 8 + 4 + 4 * 8 + f.config.circuit.numPublicInputs * 8 + 3 * 32;
        uint256 nargLength = _readU32Le(f.compact, cursor);
        cursor += 4 + nargLength;
        uint256 hintLength = _readU32Le(f.compact, cursor);
        require(hintLength > 0, "PoC hint blob empty");
        return cursor + 4 + hintLength - 1;
    }

    function _readU32Le(bytes memory source, uint256 offset) private pure returns (uint256 value) {
        for (uint256 i = 0; i < 4; ++i) {
            value |= uint256(uint8(source[offset + i])) << (8 * i);
        }
    }

    function _fixture() private view returns (Fix memory f) {
        string memory json = vm.readFile(FIXTURE);
        f.proof = abi.decode(vm.parseJsonBytes(json, ".solidityAbiProof.bytes"), (MleVerifierV2.MleProof));
        f.config = abi.decode(
            vm.parseJsonBytes(json, ".solidityAbiVerificationConfig.bytes"), (MleVerifierV2.VerificationConfig)
        );
        f.compact = vm.parseJsonBytes(json, ".compactProof.bytes");

        bytes memory protocolId = vm.parseJsonBytes(json, ".pinnedVerifier.whirProtocolId");
        require(protocolId.length == 64, "PoC WHIR protocol id length");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocolId, 0x20))
            second := mload(add(protocolId, 0x40))
        }
        f.whirProtocolId = [first, second];
        f.whirSessionId = vm.parseJsonBytes32(json, ".pinnedVerifier.whirSessionId");
        for (uint256 i = 0; i < 4; ++i) {
            f.circuitDigest[i] = uint64(f.proof.circuitDigest[i]);
        }
    }

    function _deployCore(Fix memory f) private returns (MleVerifierV2 core) {
        core = new MleVerifierV2(
            block.chainid,
            f.proof.preprocessedRoot,
            f.whirProtocolId,
            f.whirSessionId,
            f.circuitDigest,
            f.config
        );
    }

    function _clone(bytes memory source) private pure returns (bytes memory copy) {
        copy = new bytes(source.length);
        for (uint256 i = 0; i < source.length; ++i) {
            copy[i] = source[i];
        }
    }
}
