// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";

import {CircuitConfigV2} from "../src/CircuitConfigV2.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {Plonky2GateEvaluatorExt3} from "../src/Plonky2GateEvaluatorExt3.sol";

contract CircuitConfigV2Test is Test {
    uint256 internal constant P = 0xFFFFFFFF00000001;
    uint256 internal constant GENERATOR = 14293326489335486720;
    bytes32 internal constant RUST_GOLDEN = 0x74c04994e9e6178ca36d61e920679ad2f0055744fe05c33a42db82d7790dcf9b;

    function test_matchesIndependentRustGolden() external pure {
        assertEq(
            CircuitConfigV2.digest(_parameters(), _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), bytes("")),
            RUST_GOLDEN
        );
    }

    function test_everyFieldOfEveryGateDescriptorIsBound() external pure {
        CircuitConfigV2.Parameters memory parameters = _parameters();
        uint256[] memory circuitDigest = _circuitDigest();
        uint256[] memory kIs = _kIs();
        uint256[] memory subgroupPowers = _subgroupPowers();
        for (uint256 gateIndex = 0; gateIndex < 14; ++gateIndex) {
            for (uint256 fieldIndex = 0; fieldIndex < 9; ++fieldIndex) {
                Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates = _gates();
                _mutateGateField(gates[gateIndex], fieldIndex);
                bytes32 changed =
                    CircuitConfigV2.digest(parameters, circuitDigest, kIs, subgroupPowers, gates, bytes(""));
                assertTrue(changed != RUST_GOLDEN, "a GateInfoV2 field was not hash-bound");
            }
        }
    }

    function test_nonCanonicalFieldVectorFails() external {
        uint256[] memory circuitDigest = _circuitDigest();
        circuitDigest[2] = P;
        vm.expectRevert(InvalidMleProof.selector);
        CircuitConfigV2.digest(_parameters(), circuitDigest, _kIs(), _subgroupPowers(), _gates(), bytes(""));
    }

    function test_parameterOutsideU64FailsBeforeNarrowing() external {
        CircuitConfigV2.Parameters memory parameters = _parameters();
        parameters.degreeBits = uint256(type(uint64).max) + 1;
        vm.expectRevert(InvalidMleProof.selector);
        CircuitConfigV2.digest(parameters, _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), bytes(""));
    }

    function test_publicInputWireMapIsOrderedDigestBoundAndFailClosed() external {
        CircuitConfigV2.Parameters memory parameters = _parameters();
        parameters.numPublicInputs = 2;
        bytes memory ordered = hex"0000000f0001"; // (row 0,col 0), (row 15,col 1)
        bytes32 orderedDigest =
            CircuitConfigV2.digest(parameters, _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), ordered);

        bytes memory reversed = hex"0f0001000000";
        bytes32 reversedDigest =
            CircuitConfigV2.digest(parameters, _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), reversed);
        assertTrue(orderedDigest != reversedDigest, "PI map order must be hash-bound");

        // Repeated registered public inputs deliberately preserve repeated map
        // entries, rather than being deduplicated by the Solidity boundary.
        bytes memory duplicate = hex"000000000000";
        CircuitConfigV2.digest(parameters, _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), duplicate);

        vm.expectRevert(InvalidMleProof.selector);
        CircuitConfigV2.digest(parameters, _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), hex"000000");

        bytes memory invalidRow = hex"1000000f0001"; // row == 2^degreeBits
        vm.expectRevert(InvalidMleProof.selector);
        CircuitConfigV2.digest(parameters, _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), invalidRow);

        bytes memory invalidColumn = hex"0000500f0001"; // column == numRoutedWires
        vm.expectRevert(InvalidMleProof.selector);
        CircuitConfigV2.digest(parameters, _circuitDigest(), _kIs(), _subgroupPowers(), _gates(), invalidColumn);
    }

    function _parameters() private pure returns (CircuitConfigV2.Parameters memory parameters) {
        parameters = CircuitConfigV2.Parameters({
            degreeBits: 4,
            numPublicInputs: 0,
            numConstants: 5,
            numRoutedWires: 80,
            numWires: 135,
            numSelectors: 3,
            numGateConstraints: 123,
            quotientDegreeFactor: 8
        });
    }

    function _circuitDigest() private pure returns (uint256[] memory values) {
        values = new uint256[](4);
        values[0] = 151;
        values[1] = 157;
        values[2] = 163;
        values[3] = 167;
    }

    function _subgroupPowers() private pure returns (uint256[] memory values) {
        values = new uint256[](4);
        for (uint256 i = 0; i < values.length; ++i) {
            values[i] = 173 + i;
        }
    }

    function _kIs() private pure returns (uint256[] memory values) {
        values = new uint256[](80);
        values[0] = 1;
        for (uint256 i = 1; i < values.length; ++i) {
            values[i] = mulmod(values[i - 1], GENERATOR, P);
        }
    }

    function _gates() private pure returns (Plonky2GateEvaluatorExt3.GateInfoV2[] memory gates) {
        gates = new Plonky2GateEvaluatorExt3.GateInfoV2[](14);
        gates[0] = _gate(0, 0, 0, 7, 0, 0, 0, 0, 0);
        gates[1] = _gate(1, 0, 0, 7, 1, 2, 2, 0, 0);
        gates[2] = _gate(5, 0, 0, 7, 2, 24, 0, 0, 0);
        gates[3] = _gate(2, 0, 0, 7, 3, 4, 0, 0, 0);
        gates[4] = _gate(9, 0, 0, 7, 4, 5, 4, 2, 0);
        gates[5] = _gate(11, 0, 0, 7, 5, 6, 3, 0, 0);
        gates[6] = _gate(10, 0, 0, 7, 6, 6, 3, 0, 0);
        gates[7] = _gate(6, 1, 7, 12, 7, 4, 2, 0, 0);
        gates[8] = _gate(3, 1, 7, 12, 8, 2, 2, 0, 0);
        gates[9] = _gate(7, 1, 7, 12, 9, 4, 2, 0, 0);
        gates[10] = _gate(12, 1, 7, 12, 10, 54, 2, 13, 2);
        gates[11] = _gate(13, 1, 7, 12, 11, 20, 4, 4, 0);
        gates[12] = _gate(8, 2, 12, 14, 12, 4, 3, 0, 0);
        gates[13] = _gate(4, 2, 12, 14, 13, 123, 0, 0, 0);
    }

    function _gate(
        uint8 gateId,
        uint8 selectorIndex,
        uint8 groupStart,
        uint8 groupEnd,
        uint8 gateRowIndex,
        uint16 numConstraints,
        uint16 numOrConsts,
        uint16 param2,
        uint16 param3
    ) private pure returns (Plonky2GateEvaluatorExt3.GateInfoV2 memory) {
        return Plonky2GateEvaluatorExt3.GateInfoV2({
            gateId: gateId,
            selectorIndex: selectorIndex,
            groupStart: groupStart,
            groupEnd: groupEnd,
            gateRowIndex: gateRowIndex,
            numConstraints: numConstraints,
            numOrConsts: numOrConsts,
            param2: param2,
            param3: param3
        });
    }

    function _mutateGateField(Plonky2GateEvaluatorExt3.GateInfoV2 memory gate, uint256 fieldIndex) private pure {
        if (fieldIndex == 0) gate.gateId ^= 1;
        else if (fieldIndex == 1) gate.selectorIndex ^= 1;
        else if (fieldIndex == 2) gate.groupStart ^= 1;
        else if (fieldIndex == 3) gate.groupEnd ^= 1;
        else if (fieldIndex == 4) gate.gateRowIndex ^= 1;
        else if (fieldIndex == 5) gate.numConstraints ^= 1;
        else if (fieldIndex == 6) gate.numOrConsts ^= 1;
        else if (fieldIndex == 7) gate.param2 ^= 1;
        else if (fieldIndex == 8) gate.param3 ^= 1;
        else revert("GateInfoV2 field index out of range");
    }
}
