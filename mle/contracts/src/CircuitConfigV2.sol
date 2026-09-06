// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof} from "./MleProofErrors.sol";
import {Plonky2GateEvaluatorExt3} from "./Plonky2GateEvaluatorExt3.sol";
import {
    BASE_FIELD_MODULUS_V2,
    CIRCUIT_CONFIG_HASH_DOMAIN_V2,
    INNER_EXTENSION_DEGREE_V2,
    MLE_PROTOCOL_VERSION_CURRENT
} from "./generated/MleWhirV2.sol";

/// @title CircuitConfigV2
/// @notice Byte-exact Solidity mirror of Rust `circuit_config_digest_v2`.
library CircuitConfigV2 {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;

    struct Parameters {
        uint256 degreeBits;
        uint256 numPublicInputs;
        uint256 numConstants;
        uint256 numRoutedWires;
        uint256 numWires;
        uint256 numSelectors;
        uint256 numGateConstraints;
        uint256 quotientDegreeFactor;
    }

    /// @notice Hash the canonical fixed-width v2 configuration preimage.
    function digest(
        Parameters memory parameters,
        uint256[] memory circuitDigest,
        uint256[] memory kIs,
        uint256[] memory subgroupGenPowers,
        Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates,
        bytes memory publicInputWireMap
    ) external pure returns (bytes32) {
        _checkU64(parameters.degreeBits);
        _checkU64(parameters.numPublicInputs);
        _checkU64(parameters.numConstants);
        _checkU64(parameters.numRoutedWires);
        _checkU64(parameters.numWires);
        _checkU64(parameters.numSelectors);
        _checkU64(parameters.numGateConstraints);
        _checkU64(parameters.quotientDegreeFactor);
        _checkU64(circuitDigest.length);
        _checkU64(kIs.length);
        _checkU64(subgroupGenPowers.length);
        _checkU64(gates.length);
        _validatePublicInputWireMap(parameters, publicInputWireMap);

        bytes memory domain = bytes(CIRCUIT_CONFIG_HASH_DOMAIN_V2);
        uint256 payloadLength = domain.length + 14 * 8 + 8 * circuitDigest.length + 8 * kIs.length + 8
            * subgroupGenPowers.length + 13 * gates.length + 8 + publicInputWireMap.length;
        bytes memory preimage = new bytes(payloadLength);
        uint256 offset;
        for (uint256 i = 0; i < domain.length; ++i) {
            preimage[offset++] = domain[i];
        }
        offset = _writeU64Le(preimage, offset, uint64(MLE_PROTOCOL_VERSION_CURRENT));
        offset = _writeU64Le(preimage, offset, uint64(INNER_EXTENSION_DEGREE_V2));
        offset = _writeU64Le(preimage, offset, uint64(parameters.degreeBits));
        offset = _writeU64Le(preimage, offset, uint64(parameters.numPublicInputs));
        offset = _writeU64Le(preimage, offset, uint64(parameters.numConstants));
        offset = _writeU64Le(preimage, offset, uint64(parameters.numRoutedWires));
        offset = _writeU64Le(preimage, offset, uint64(parameters.numWires));
        offset = _writeU64Le(preimage, offset, uint64(parameters.numSelectors));
        offset = _writeU64Le(preimage, offset, uint64(parameters.numGateConstraints));
        offset = _writeU64Le(preimage, offset, uint64(parameters.quotientDegreeFactor));
        offset = _writeFieldVector(preimage, offset, circuitDigest);
        offset = _writeFieldVector(preimage, offset, kIs);
        offset = _writeFieldVector(preimage, offset, subgroupGenPowers);
        offset = _writeU64Le(preimage, offset, uint64(gates.length));
        for (uint256 i = 0; i < gates.length; ++i) {
            Plonky2GateEvaluatorExt3.GateInfoV2 memory gate = gates[i];
            preimage[offset++] = bytes1(gate.gateId);
            preimage[offset++] = bytes1(gate.selectorIndex);
            preimage[offset++] = bytes1(gate.groupStart);
            preimage[offset++] = bytes1(gate.groupEnd);
            preimage[offset++] = bytes1(gate.gateRowIndex);
            offset = _writeU16Le(preimage, offset, gate.numConstraints);
            offset = _writeU16Le(preimage, offset, gate.numOrConsts);
            offset = _writeU16Le(preimage, offset, gate.param2);
            offset = _writeU16Le(preimage, offset, gate.param3);
        }
        offset = _writeU64Le(preimage, offset, uint64(publicInputWireMap.length));
        for (uint256 i = 0; i < publicInputWireMap.length; ++i) {
            preimage[offset++] = publicInputWireMap[i];
        }
        if (offset != payloadLength) revert InvalidMleProof();
        return keccak256(preimage);
    }

    /// @dev Entries are exactly `row_u16_le || routed_column_u8`. Duplicates
    /// are allowed and meaningful; their byte-string order is PI order.
    function _validatePublicInputWireMap(Parameters memory parameters, bytes memory wireMap) private pure {
        if (parameters.numPublicInputs > type(uint256).max / 3 || wireMap.length != 3 * parameters.numPublicInputs) {
            revert InvalidMleProof();
        }
        uint256 degree = uint256(1) << parameters.degreeBits;
        for (uint256 offset = 0; offset < wireMap.length; offset += 3) {
            uint256 row = uint8(wireMap[offset]) | (uint256(uint8(wireMap[offset + 1])) << 8);
            uint256 column = uint8(wireMap[offset + 2]);
            if (row >= degree || column >= parameters.numRoutedWires) revert InvalidMleProof();
        }
    }

    function _writeFieldVector(bytes memory destination, uint256 offset, uint256[] memory values)
        private
        pure
        returns (uint256)
    {
        offset = _writeU64Le(destination, offset, uint64(values.length));
        for (uint256 i = 0; i < values.length; ++i) {
            if (values[i] >= P) revert InvalidMleProof();
            offset = _writeU64Le(destination, offset, uint64(values[i]));
        }
        return offset;
    }

    function _writeU16Le(bytes memory destination, uint256 offset, uint16 value) private pure returns (uint256) {
        destination[offset] = bytes1(uint8(value));
        destination[offset + 1] = bytes1(uint8(value >> 8));
        return offset + 2;
    }

    function _writeU64Le(bytes memory destination, uint256 offset, uint64 value) private pure returns (uint256) {
        for (uint256 i = 0; i < 8; ++i) {
            destination[offset + i] = bytes1(uint8(value >> (8 * i)));
        }
        return offset + 8;
    }

    function _checkU64(uint256 value) private pure {
        if (value > type(uint64).max) revert InvalidMleProof();
    }
}
