// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {LegacyMleVerifierHarness} from "./LegacyMleVerifierHarness.sol";

contract LegacyMleVerifierContainmentTest is Test {
    function test_productionLegacyArtifactHasNoDeployableBytecode() external view {
        string memory artifact = vm.readFile("out/MleVerifier.sol/MleVerifier.json");
        assertEq(vm.parseJsonString(artifact, ".bytecode.object"), "0x", "legacy creation bytecode must be absent");
        assertEq(
            vm.parseJsonString(artifact, ".deployedBytecode.object"), "0x", "legacy runtime bytecode must be absent"
        );
    }

    function test_legacyConformanceHarnessRetainsTheChainPin() external {
        LegacyMleVerifierHarness harness = new LegacyMleVerifierHarness(block.chainid);
        assertGt(address(harness).code.length, 0, "conformance harness must remain executable");
        assertEq(harness.allowedChainId(), block.chainid);
    }
}
