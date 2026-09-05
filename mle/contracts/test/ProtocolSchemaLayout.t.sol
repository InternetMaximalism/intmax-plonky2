// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifier} from "../src/MleVerifier.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {
    MLE_PROOF_ABI_FIELD_COUNT,
    MLE_PROOF_ABI_TEST_SELECTOR,
    MLE_PROOF_LAYOUT_HASH
} from "../src/generated/MleWhirV1.sol";
import {
    MLE_PROOF_ABI_FIELD_COUNT_V2,
    MLE_PROOF_ABI_TEST_SELECTOR_V2,
    MLE_PROOF_LAYOUT_HASH_V2
} from "../src/generated/MleWhirV2.sol";

contract MleProofAbiHarness {
    function accept(MleVerifier.MleProof calldata) external pure {}
}

contract MleProofAbiHarnessV2 {
    function acceptV2(MleVerifierV2.MleProof calldata) external pure {}
}

/// @notice Compiler-level guard for the generated proof ABI manifest.
/// @dev The Rust generator separately checks source field names/order and JSON
/// keys. Comparing a real Solidity selector also expands nested SumcheckProof
/// and GateInfo structs, so a nested ABI-type change cannot retain this selector.
contract ProtocolSchemaLayoutTest is Test {
    function test_generated_proof_abi_signature_matches_compiler() public pure {
        assertEq(MLE_PROOF_ABI_FIELD_COUNT, 48, "v1 proof ABI field count");
        assertTrue(MLE_PROOF_LAYOUT_HASH != bytes32(0), "proof layout hash");
        assertEq(MleProofAbiHarness.accept.selector, MLE_PROOF_ABI_TEST_SELECTOR, "generated proof ABI signature");
    }

    function test_generated_v2_proof_abi_signature_matches_compiler() public pure {
        assertEq(MLE_PROOF_ABI_FIELD_COUNT_V2, 16, "v2 proof ABI field count");
        assertTrue(MLE_PROOF_LAYOUT_HASH_V2 != bytes32(0), "v2 proof layout hash");
        assertEq(
            MleProofAbiHarnessV2.acceptV2.selector,
            MLE_PROOF_ABI_TEST_SELECTOR_V2,
            "generated v2 proof ABI signature"
        );
    }
}
