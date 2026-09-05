// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {TranscriptV2} from "../src/TranscriptV2.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";

contract TranscriptV2Harness {
    function typedTrace()
        external
        pure
        returns (
            bytes32[5] memory states,
            uint256[2] memory baseChallenges,
            GoldilocksExt3.Ext3 memory extChallenge,
            uint64 counter
        )
    {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        states[0] = transcript.state;
        TranscriptV2.absorbField(transcript, 7);
        states[1] = transcript.state;

        uint256[] memory fields = new uint256[](3);
        fields[0] = 0;
        fields[1] = 1;
        fields[2] = 0xFFFFFFFF00000000;
        TranscriptV2.absorbFieldVec(transcript, fields);
        states[2] = transcript.state;

        TranscriptV2.absorbExt3(transcript, GoldilocksExt3.Ext3(2, 3, 4));
        states[3] = transcript.state;
        GoldilocksExt3.Ext3[] memory extensions = new GoldilocksExt3.Ext3[](2);
        extensions[0] = GoldilocksExt3.Ext3(5, 6, 7);
        extensions[1] = GoldilocksExt3.Ext3(8, 9, 10);
        TranscriptV2.absorbExt3Vec(transcript, extensions);
        states[4] = transcript.state;

        baseChallenges[0] = TranscriptV2.squeezeChallenge(transcript);
        baseChallenges[1] = TranscriptV2.squeezeChallenge(transcript);
        extChallenge = TranscriptV2.squeezeExt3(transcript);
        counter = transcript.squeezeCounter;
    }

    function lockstep(uint64 finalGateValue)
        external
        pure
        returns (bytes32 state, uint64 counter, TranscriptV2.CoupledOuterRoundChallenges memory challenges)
    {
        TranscriptV2.Transcript memory transcript = _typedTracePrefix();
        GoldilocksExt3.Ext3[] memory log = new GoldilocksExt3.Ext3[](2);
        log[0] = GoldilocksExt3.Ext3(11, 12, 13);
        log[1] = GoldilocksExt3.Ext3(14, 15, 16);
        GoldilocksExt3.Ext3[] memory gate = new GoldilocksExt3.Ext3[](2);
        gate[0] = GoldilocksExt3.Ext3(21, 22, 23);
        gate[1] = GoldilocksExt3.Ext3(24, 25, finalGateValue);
        challenges = TranscriptV2.commitCoupledOuterRound(transcript, 3, log, gate);
        state = transcript.state;
        counter = transcript.squeezeCounter;
    }

    function fieldState(uint256 value) external pure returns (bytes32) {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        TranscriptV2.absorbField(transcript, value);
        return transcript.state;
    }

    function bytesState(bytes memory value) external pure returns (bytes32) {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        TranscriptV2.absorbBytes(transcript, value);
        return transcript.state;
    }

    function fieldVecState(uint256[] memory values) external pure returns (bytes32) {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        TranscriptV2.absorbFieldVec(transcript, values);
        return transcript.state;
    }

    function extState(GoldilocksExt3.Ext3 memory value) external pure returns (bytes32) {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        TranscriptV2.absorbExt3(transcript, value);
        return transcript.state;
    }

    function extVecState(GoldilocksExt3.Ext3[] memory values) external pure returns (bytes32) {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        TranscriptV2.absorbExt3Vec(transcript, values);
        return transcript.state;
    }

    function squeezeThenAbsorb() external pure returns (uint64) {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        TranscriptV2.squeezeChallenge(transcript);
        TranscriptV2.absorbBytes(transcript, hex"00");
        return transcript.squeezeCounter;
    }

    function bindWhirIdentifiers(bytes memory protocolId, bytes memory sessionId)
        external
        pure
        returns (bytes32 state, uint64 counter)
    {
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();
        TranscriptV2.bindWhirIdentifiers(transcript, protocolId, sessionId);
        return (transcript.state, transcript.squeezeCounter);
    }

    function _typedTracePrefix() private pure returns (TranscriptV2.Transcript memory transcript) {
        transcript = TranscriptV2.create();
        TranscriptV2.absorbField(transcript, 7);
        uint256[] memory fields = new uint256[](3);
        fields[0] = 0;
        fields[1] = 1;
        fields[2] = 0xFFFFFFFF00000000;
        TranscriptV2.absorbFieldVec(transcript, fields);
        TranscriptV2.absorbExt3(transcript, GoldilocksExt3.Ext3(2, 3, 4));
        GoldilocksExt3.Ext3[] memory extensions = new GoldilocksExt3.Ext3[](2);
        extensions[0] = GoldilocksExt3.Ext3(5, 6, 7);
        extensions[1] = GoldilocksExt3.Ext3(8, 9, 10);
        TranscriptV2.absorbExt3Vec(transcript, extensions);
        TranscriptV2.squeezeChallenge(transcript);
        TranscriptV2.squeezeChallenge(transcript);
        TranscriptV2.squeezeExt3(transcript);
    }
}

contract TranscriptV2Test is Test {
    TranscriptV2Harness private harness;

    function setUp() external {
        harness = new TranscriptV2Harness();
    }

    function test_rustTypedFrameAndSqueezeGolden() external view {
        (
            bytes32[5] memory states,
            uint256[2] memory baseChallenges,
            GoldilocksExt3.Ext3 memory extension,
            uint64 counter
        ) = harness.typedTrace();
        assertEq(states[0], 0x4eee7256a652e68d8b7a7b0460a1de52b8c10bfab17a7b5ec5c97b4ba120f236);
        assertEq(states[1], 0xe7c2d5013557fab96927ececb4eea1c8afda5c40078fd73f34f6d449e4e34adc);
        assertEq(states[2], 0xfc993ee71ec6b1a4011aa60afce7cb459dcf6ec321ea7bb5beac717b42235852);
        assertEq(states[3], 0xfed8599ef0f0987ddfde75c4f779382ed4401d9a780c8e9fea422b168e73b685);
        assertEq(states[4], 0xe727699ebf2501ed1554b63fa0409dfc876f26b4c45310ac1f4a9d696762be9f);
        assertEq(baseChallenges[0], 0xace93c7d4a6e54c9);
        assertEq(baseChallenges[1], 0x6653b74a5af389e9);
        _assertExt3(extension, 0x26c9eca14e4bcf44, 0xa463149450187e75, 0x85433e61a4ca93d2);
        assertEq(counter, 5);
    }

    function test_rustCoupledOuterRoundGolden() external view {
        (bytes32 state, uint64 counter, TranscriptV2.CoupledOuterRoundChallenges memory challenges) =
            harness.lockstep(26);
        assertEq(state, 0x1c5c8ee575d5a624ae2cab5acc842597a360a81bb99496af7ef448450d04c32b);
        assertEq(counter, 6);
        _assertExt3(challenges.log, 0x67030ba296206426, 0x160c6cb281baa3ae, 0x92fc9d717662050b);
        _assertExt3(challenges.gate, 0x743613855ac7898d, 0xf834e6c52a4e27f7, 0x56c655bb797ad0cc);
    }

    function test_rustWhirIdentifierBindingGolden() external view {
        bytes memory protocolId = new bytes(64);
        bytes memory sessionId = new bytes(32);
        for (uint256 i = 0; i < protocolId.length; ++i) {
            protocolId[i] = bytes1(uint8(i));
        }
        for (uint256 i = 0; i < sessionId.length; ++i) {
            sessionId[i] = bytes1(uint8(0x80 + i));
        }
        (bytes32 state, uint64 counter) = harness.bindWhirIdentifiers(protocolId, sessionId);
        assertEq(state, 0x9d186e7a5d202c97b788e898ac9e0b33ed2e7e27118ae0e2470ce82af522227d);
        assertEq(counter, 0);
    }

    function test_whirIdentifierLengthsAreExact() external {
        vm.expectRevert(InvalidMleProof.selector);
        harness.bindWhirIdentifiers(new bytes(63), new bytes(32));
        vm.expectRevert(InvalidMleProof.selector);
        harness.bindWhirIdentifiers(new bytes(65), new bytes(32));
        vm.expectRevert(InvalidMleProof.selector);
        harness.bindWhirIdentifiers(new bytes(64), new bytes(31));
        vm.expectRevert(InvalidMleProof.selector);
        harness.bindWhirIdentifiers(new bytes(64), new bytes(33));
    }

    function test_lastGateMessageChangesEveryCoupledChallenge() external view {
        (,, TranscriptV2.CoupledOuterRoundChallenges memory first) = harness.lockstep(26);
        (,, TranscriptV2.CoupledOuterRoundChallenges memory changed) = harness.lockstep(27);
        assertNotEq(first.log.c0, changed.log.c0);
        assertNotEq(first.log.c1, changed.log.c1);
        assertNotEq(first.log.c2, changed.log.c2);
        assertNotEq(first.gate.c0, changed.gate.c0);
        assertNotEq(first.gate.c1, changed.gate.c1);
        assertNotEq(first.gate.c2, changed.gate.c2);
    }

    function test_typedFramesCannotAlias() external view {
        assertNotEq(harness.fieldState(7), harness.bytesState(hex"0700000000000000"));
    }

    function test_absorbResetsSqueezeCounter() external view {
        assertEq(harness.squeezeThenAbsorb(), 0);
    }

    function test_nonCanonicalBaseAndExt3AreRejected() external {
        vm.expectRevert(InvalidMleProof.selector);
        harness.fieldState(0xFFFFFFFF00000001);

        uint256[] memory fields = new uint256[](1);
        fields[0] = 0xFFFFFFFF00000001;
        vm.expectRevert(InvalidMleProof.selector);
        harness.fieldVecState(fields);

        vm.expectRevert(InvalidMleProof.selector);
        harness.extState(GoldilocksExt3.Ext3(uint64(0xFFFFFFFF00000001), 0, 0));

        GoldilocksExt3.Ext3[] memory extensions = new GoldilocksExt3.Ext3[](1);
        extensions[0] = GoldilocksExt3.Ext3(0, uint64(0xFFFFFFFF00000001), 0);
        vm.expectRevert(InvalidMleProof.selector);
        harness.extVecState(extensions);
    }

    function _assertExt3(GoldilocksExt3.Ext3 memory value, uint64 c0, uint64 c1, uint64 c2) private pure {
        assertEq(value.c0, c0);
        assertEq(value.c1, c1);
        assertEq(value.c2, c2);
    }

    function _equal(GoldilocksExt3.Ext3 memory left, GoldilocksExt3.Ext3 memory right) private pure returns (bool) {
        return left.c0 == right.c0 && left.c1 == right.c1 && left.c2 == right.c2;
    }
}
