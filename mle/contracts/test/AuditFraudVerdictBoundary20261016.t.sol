// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";

/// Diagnostic only: distinguish an actual OOG from a completed proof rejection.
contract AuditFraudVerdictBoundary20261016Test is Test {
    function test_completedRejectionCanBecomeStarved() external {
        string memory json = vm.readFile("test/fixtures/v2_max_resource.json");
        MleVerifierV2.MleProof memory proof =
            abi.decode(vm.parseJsonBytes(json, ".solidityAbiProof.bytes"), (MleVerifierV2.MleProof));
        MleVerifierV2.VerificationConfig memory config = abi.decode(
            vm.parseJsonBytes(json, ".solidityAbiVerificationConfig.bytes"), (MleVerifierV2.VerificationConfig)
        );
        bytes memory protocolId = vm.parseJsonBytes(json, ".pinnedVerifier.whirProtocolId");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocolId, 0x20))
            second := mload(add(protocolId, 0x40))
        }
        uint64[4] memory digest;
        for (uint256 i; i < 4; ++i) {
            digest[i] = uint64(proof.circuitDigest[i]);
        }
        MleVerifierV2 core = new MleVerifierV2(
            block.chainid,
            proof.preprocessedRoot,
            [first, second],
            vm.parseJsonBytes32(json, ".pinnedVerifier.whirSessionId"),
            digest,
            config
        );
        PinnedMleVerifierV2 pinned = new PinnedMleVerifierV2(core, config);
        bytes memory compact = vm.parseJsonBytes(json, ".compactProof.bytes");
        assertTrue(pinned.verifyCompact(compact));
        uint256 cursor = 8 + 8 + 4 + 4 * 8 + config.circuit.numPublicInputs * 8 + 3 * 32;
        cursor += 4 + _u32(compact, cursor);
        uint256 hintLength = _u32(compact, cursor);
        compact[cursor + 4 + hintLength - 1] ^= bytes1(uint8(1));

        uint256[6] memory budgets = [uint256(10_000_000), 10_500_000, 11_000_000, 11_500_000, 12_000_000, 12_500_000];
        uint256 demonstrated;
        for (uint256 i; i < budgets.length; ++i) {
            uint256 budget = budgets[i];
            // Give the isolated body LESS gas than the classifier can forward.
            uint256 bodyBudget = budget - budget / 64 - 100_000;
            bytes memory bodyCall = abi.encodeCall(PinnedMleVerifierV2.compactFraudVerdictBody, (compact, bytes32(0)));
            vm.prank(address(pinned));
            uint256 beforeBody = gasleft();
            (bool bodyOk, bytes memory reason) = address(pinned).staticcall{gas: bodyBudget}(bodyCall);
            uint256 bodyCost = beforeBody - gasleft();
            bool completedInvalid = !bodyOk && reason.length == 4
                && keccak256(reason) == keccak256(abi.encodeWithSelector(InvalidMleProof.selector));
            (bool outerOk, bytes memory result) = address(pinned).staticcall{gas: budget}(
                abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (compact, bytes32(0)))
            );
            assertTrue(outerOk);
            uint8 verdict = abi.decode(result, (uint8));
            emit log_named_uint("classifier budget", budget);
            emit log_named_uint("body measured gas", bodyCost);
            emit log_named_uint("body exact InvalidMleProof with LESS gas", completedInvalid ? 1 : 0);
            emit log_named_uint("classifier verdict (0 INVALID, 3 STARVED)", verdict);
            assertTrue(verdict == 0 || verdict == 3);
            if (completedInvalid && verdict == 3) ++demonstrated;
        }
        assertGt(demonstrated, 0, "must demonstrate completed rejection mislabeled STARVED");
    }

    function _u32(bytes memory data, uint256 offset) private pure returns (uint256 n) {
        for (uint256 i; i < 4; ++i) {
            n |= uint256(uint8(data[offset + i])) << (8 * i);
        }
    }
}
