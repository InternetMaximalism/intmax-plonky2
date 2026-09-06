// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {CircuitConfigV2} from "../src/CircuitConfigV2.sol";
import {CompactMleProofV2} from "../src/CompactMleProofV2.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {
    BASE_FIELD_MODULUS_V2,
    COMPACT_MAGIC_V2,
    MAX_COMPACT_PROOF_BYTES_V2,
    MLE_PROTOCOL_VERSION_CURRENT
} from "../src/generated/MleWhirV2.sol";

contract CompactMleProofV2Harness {
    function decodeHash(bytes calldata encoded, CircuitConfigV2.Parameters calldata circuit)
        external
        pure
        returns (uint256 length, bytes32 digest)
    {
        CircuitConfigV2.Parameters memory trustedCircuit = circuit;
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decode(encoded, trustedCircuit);
        bytes memory abiProof = abi.encode(proof);
        return (abiProof.length, keccak256(abiProof));
    }
}

contract CompactMleProofV2Test is Test {
    string private constant FIXTURE = "test/fixtures/v2_max_resource.json";
    string private constant CASE = "";

    CompactMleProofV2Harness private harness;

    function setUp() external {
        harness = new CompactMleProofV2Harness();
    }

    function test_decodesRustCompactBytesToExactCanonicalSolidityAbi() external view {
        string memory json = vm.readFile(FIXTURE);
        bytes memory compact = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));
        (uint256 length, bytes32 digest) = harness.decodeHash(compact, _circuit(json));
        assertEq(length, vm.parseJsonUint(json, string.concat(CASE, ".solidityAbiProof.byteLength")));
        assertEq(digest, vm.parseJsonBytes32(json, string.concat(CASE, ".solidityAbiProof.keccak256")));
    }

    function test_rejectsNonCanonicalHeaderShapeFieldsAndTail() external view {
        string memory json = vm.readFile(FIXTURE);
        bytes memory canonical = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));
        CircuitConfigV2.Parameters memory circuit = _circuit(json);

        bytes memory mutated = _clone(canonical);
        mutated[0] ^= 0x01;
        _assertInvalid(mutated, circuit, "magic");

        assertEq(bytes8(uint64(_readU64Be(canonical, 0))), COMPACT_MAGIC_V2, "current magic");
        assertEq(_readU64Le(canonical, 8), MLE_PROTOCOL_VERSION_CURRENT, "current version");
        assertFalse(_legacyV2HeaderAccepts(canonical), "v3 must not parse as v2");

        bytes memory legacyV2 = _clone(canonical);
        bytes memory legacyMagic = bytes("MLEWHIR2");
        for (uint256 i = 0; i < 8; ++i) {
            legacyV2[i] = legacyMagic[i];
        }
        _writeU64Le(legacyV2, 8, 2);
        assertTrue(_legacyV2HeaderAccepts(legacyV2), "legacy discriminator fixture");
        _assertInvalid(legacyV2, circuit, "old v2 to new v3");

        bytes memory currentMagicOldVersion = _clone(canonical);
        _writeU64Le(currentMagicOldVersion, 8, 2);
        _assertInvalid(currentMagicOldVersion, circuit, "current magic with old v2 version");

        bytes memory legacyPayloadOnlyVersionBumped = _clone(legacyV2);
        _writeU64Le(legacyPayloadOnlyVersionBumped, 8, MLE_PROTOCOL_VERSION_CURRENT);
        assertFalse(_legacyV2HeaderAccepts(legacyPayloadOnlyVersionBumped), "v2 reader rejects bumped header");
        _assertInvalid(legacyPayloadOnlyVersionBumped, circuit, "old payload with version-only bump");

        mutated = _clone(canonical);
        mutated[8] ^= 0x01;
        _assertInvalid(mutated, circuit, "version");

        mutated = _clone(canonical);
        mutated[16] ^= 0x01;
        _assertInvalid(mutated, circuit, "constituent width");

        mutated = _clone(canonical);
        _writeU64Le(mutated, 20, BASE_FIELD_MODULUS_V2);
        _assertInvalid(mutated, circuit, "non-canonical circuit digest");

        mutated = _clone(canonical);
        _writeU64Le(mutated, mutated.length - 8, BASE_FIELD_MODULUS_V2);
        _assertInvalid(mutated, circuit, "non-canonical final Ext3 limb");

        mutated = bytes.concat(canonical, hex"00");
        _assertInvalid(mutated, circuit, "trailing byte");
    }

    function test_rejectsTruncationAndUnboundedWhirLengthsBeforeAllocation() external view {
        string memory json = vm.readFile(FIXTURE);
        bytes memory canonical = vm.parseJsonBytes(json, string.concat(CASE, ".compactProof.bytes"));
        CircuitConfigV2.Parameters memory circuit = _circuit(json);
        uint256 nargLengthOffset = 8 + 8 + 4 + 4 * 8 + circuit.numPublicInputs * 8 + 3 * 32;
        uint256 nargLength = _readU32Le(canonical, nargLengthOffset);
        uint256 hintsLengthOffset = nargLengthOffset + 4 + nargLength;

        uint256[] memory cuts = new uint256[](8);
        cuts[0] = 0;
        cuts[1] = 7;
        cuts[2] = 8;
        cuts[3] = 20;
        cuts[4] = nargLengthOffset;
        cuts[5] = nargLengthOffset + 4;
        cuts[6] = hintsLengthOffset + 4;
        cuts[7] = canonical.length - 1;
        for (uint256 i = 0; i < cuts.length; ++i) {
            _assertInvalid(_resize(canonical, cuts[i]), circuit, string.concat("truncated[", vm.toString(i), "]"));
        }

        bytes memory mutated = _clone(canonical);
        _writeU32Le(mutated, nargLengthOffset, type(uint32).max);
        _assertInvalid(mutated, circuit, "oversized WHIR transcript");

        mutated = _clone(canonical);
        _writeU32Le(mutated, hintsLengthOffset, type(uint32).max);
        _assertInvalid(mutated, circuit, "oversized WHIR hints");

        _assertInvalid(new bytes(MAX_COMPACT_PROOF_BYTES_V2 + 1), circuit, "two-blob capacity");
    }

    function _circuit(string memory json) private pure returns (CircuitConfigV2.Parameters memory circuit) {
        string memory shape = string.concat(CASE, ".compactShape");
        circuit.degreeBits = vm.parseJsonUint(json, string.concat(shape, ".degreeBits"));
        circuit.numPublicInputs = vm.parseJsonUint(json, string.concat(shape, ".publicInputsLen"));
        circuit.numConstants = vm.parseJsonUint(json, string.concat(shape, ".numConstants"));
        circuit.numRoutedWires = vm.parseJsonUint(json, string.concat(shape, ".numRoutedWires"));
        circuit.numWires = vm.parseJsonUint(json, string.concat(shape, ".numWires"));
        circuit.quotientDegreeFactor = vm.parseJsonUint(json, string.concat(shape, ".gateRoundDegree")) - 2;
    }

    function _assertInvalid(bytes memory encoded, CircuitConfigV2.Parameters memory circuit, string memory label)
        private
        view
    {
        (bool ok, bytes memory reason) =
            address(harness).staticcall(abi.encodeCall(CompactMleProofV2Harness.decodeHash, (encoded, circuit)));
        assertFalse(ok, string.concat(label, ": unexpectedly decoded"));
        assertEq(reason, abi.encodeWithSelector(InvalidMleProof.selector), string.concat(label, ": selector"));
    }

    function _clone(bytes memory input) private pure returns (bytes memory output) {
        output = new bytes(input.length);
        for (uint256 i = 0; i < input.length; ++i) {
            output[i] = input[i];
        }
    }

    function _resize(bytes memory input, uint256 length) private pure returns (bytes memory output) {
        output = new bytes(length);
        uint256 copied = length < input.length ? length : input.length;
        for (uint256 i = 0; i < copied; ++i) {
            output[i] = input[i];
        }
    }

    function _readU32Le(bytes memory input, uint256 offset) private pure returns (uint256 value) {
        for (uint256 i = 0; i < 4; ++i) {
            value |= uint256(uint8(input[offset + i])) << (8 * i);
        }
    }

    function _readU64Le(bytes memory input, uint256 offset) private pure returns (uint256 value) {
        for (uint256 i = 0; i < 8; ++i) {
            value |= uint256(uint8(input[offset + i])) << (8 * i);
        }
    }

    function _readU64Be(bytes memory input, uint256 offset) private pure returns (uint256 value) {
        for (uint256 i = 0; i < 8; ++i) {
            value = (value << 8) | uint256(uint8(input[offset + i]));
        }
    }

    function _legacyV2HeaderAccepts(bytes memory input) private pure returns (bool) {
        if (input.length < 16 || _readU64Le(input, 8) != 2) return false;
        return bytes8(uint64(_readU64Be(input, 0))) == bytes8("MLEWHIR2");
    }

    function _writeU32Le(bytes memory output, uint256 offset, uint256 value) private pure {
        for (uint256 i = 0; i < 4; ++i) {
            output[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
    }

    function _writeU64Le(bytes memory output, uint256 offset, uint256 value) private pure {
        for (uint256 i = 0; i < 8; ++i) {
            output[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
    }
}
