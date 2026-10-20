// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";

/// Exercises the pinned core at the maximum packed dimension, using an actual proof.
contract AuditWhirMaxDimension20261016Test is Test {
    MleVerifierV2 private core;

    function setUp() external {
        (MleVerifierV2.MleProof memory proof, MleVerifierV2.VerificationConfig memory config) = _fixture();
        string memory json = vm.readFile("test/fixtures/v2_max_resource.json");
        bytes memory protocol = vm.parseJsonBytes(json, ".pinnedVerifier.whirProtocolId");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocol, 0x20))
            second := mload(add(protocol, 0x40))
        }
        uint64[4] memory digest;
        for (uint256 i; i < 4; ++i) {
            digest[i] = uint64(proof.circuitDigest[i]);
        }
        core = new MleVerifierV2(
            block.chainid,
            proof.preprocessedRoot,
            [first, second],
            vm.parseJsonBytes32(json, ".pinnedVerifier.whirSessionId"),
            digest,
            config
        );
        assertEq(config.whir.numVariables, 21);
        assertEq(config.circuit.degreeBits, 13);
        assertTrue(core.verify(proof, config), "real max-dimension positive control");
    }

    // Partition into eight bounded tests; mutate every 8-byte NARG word,
    // including all three limbs of every Ext3 message, all roots and PoW nonces.
    function test_max21_nargWordsPart0() external {
        _nargPart(0);
    }

    function test_max21_nargWordsPart1() external {
        _nargPart(1);
    }

    function test_max21_nargWordsPart2() external {
        _nargPart(2);
    }

    function test_max21_nargWordsPart3() external {
        _nargPart(3);
    }

    function test_max21_nargWordsPart4() external {
        _nargPart(4);
    }

    function test_max21_nargWordsPart5() external {
        _nargPart(5);
    }

    function test_max21_nargWordsPart6() external {
        _nargPart(6);
    }

    function test_max21_nargWordsPart7() external {
        _nargPart(7);
    }

    function _nargPart(uint256 part) private {
        (MleVerifierV2.MleProof memory proof, MleVerifierV2.VerificationConfig memory config) = _fixture();
        assertEq(proof.whirTranscript.length % 8, 0);
        uint256 words = proof.whirTranscript.length / 8;
        for (uint256 word = part; word < words; word += 8) {
            uint256 offset = 8 * word;
            proof.whirTranscript[offset] ^= bytes1(uint8(1));
            _assertInvalid(proof, config);
            proof.whirTranscript[offset] ^= bytes1(uint8(1));
        }
    }

    function testFuzz_max21_arbitraryHintByteMutation(uint256 seed) external {
        (MleVerifierV2.MleProof memory proof, MleVerifierV2.VerificationConfig memory config) = _fixture();
        proof.whirHints[seed % proof.whirHints.length] ^= bytes1(uint8(1));
        _assertInvalid(proof, config);
    }

    function _assertInvalid(MleVerifierV2.MleProof memory proof, MleVerifierV2.VerificationConfig memory config)
        private
    {
        (bool ok, bytes memory reason) = address(core).staticcall(abi.encodeCall(MleVerifierV2.verify, (proof, config)));
        assertFalse(ok, "max-dimension WHIR mutation accepted");
        assertEq(reason, abi.encodeWithSelector(InvalidMleProof.selector), "must be a definitive proof rejection");
    }

    function _fixture()
        private
        view
        returns (MleVerifierV2.MleProof memory proof, MleVerifierV2.VerificationConfig memory config)
    {
        string memory json = vm.readFile("test/fixtures/v2_max_resource.json");
        proof = abi.decode(vm.parseJsonBytes(json, ".solidityAbiProof.bytes"), (MleVerifierV2.MleProof));
        config = abi.decode(
            vm.parseJsonBytes(json, ".solidityAbiVerificationConfig.bytes"), (MleVerifierV2.VerificationConfig)
        );
    }
}
