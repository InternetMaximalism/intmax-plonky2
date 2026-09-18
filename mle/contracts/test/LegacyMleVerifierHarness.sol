// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {MleVerifier} from "../src/MleVerifier.sol";

/// @notice Test-only concrete implementation for frozen legacy conformance fixtures.
/// @dev All verification and chain checks are inherited without modification.
contract LegacyMleVerifierHarness is MleVerifier {
    constructor(uint256 allowedChainId_) MleVerifier(allowedChainId_) {}
}
