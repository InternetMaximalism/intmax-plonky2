// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {PoseidonGate} from "./PoseidonGate.sol";

/// @title PoseidonPublicInputsHash
/// @notice External-library boundary for Plonky2's Poseidon `hash_no_pad`.
/// Keeping the permutation outside MleVerifier preserves EIP-170 deployability
/// while the verifier still re-derives, rather than trusts, publicInputsHash.
library PoseidonPublicInputsHash {
    function hashNoPad(uint256[] calldata inputs) external pure returns (uint256[4] memory) {
        return PoseidonGate.hashNoPad(inputs);
    }
}
