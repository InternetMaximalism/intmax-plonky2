// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {InvalidMleProof} from "../src/MleProofErrors.sol";
import {OuterLogupExt3Verifier} from "../src/OuterLogupExt3Verifier.sol";
import {TranscriptV2} from "../src/TranscriptV2.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";

contract OuterLogupExt3VerifierTest is Test {
    uint64 private constant FIELD_MODULUS = 0xFFFFFFFF00000001;

    function test_zeroOuterAlgebraReturnsCoupledExt3GateClaim() external pure {
        OuterLogupExt3Verifier.SumcheckProof memory logProof = _zeroLogProof(2);
        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _zeroGateProof(2, 2);
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(2);
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(2);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _trivialTerminal();
        TranscriptV2.Transcript memory transcript = TranscriptV2.create();

        (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateClaim,
            TranscriptV2.Transcript memory nextTranscript
        ) = OuterLogupExt3Verifier.verify(logProof, gateProof, vk, challenges, terminal, transcript);

        assertEq(logPoint.length, 2);
        assertEq(gatePoint.length, 2);
        _assertExt3(gateClaim, 0, 0, 0);
        // Every coupled round ends after two Ext3 squeezes.
        assertEq(nextTranscript.squeezeCounter, 6);
    }

    function test_bothMessagesAreCoupledIntoBothPoints() external pure {
        OuterLogupExt3Verifier.SumcheckProof memory logProof = _zeroLogProof(1);
        OuterLogupExt3Verifier.SumcheckProof memory changedLog = _zeroLogProof(1);
        OuterLogupExt3Verifier.SumcheckProof memory firstGate = _zeroGateProof(1, 2);
        OuterLogupExt3Verifier.SumcheckProof memory changedGate = _zeroGateProof(1, 2);
        changedLog.rounds[0].nonConstant[4].c0 = 1;
        changedGate.rounds[0].nonConstant[1].c2 = 1;

        TranscriptV2.Transcript memory firstTranscript = TranscriptV2.create();
        (GoldilocksExt3.Ext3[] memory firstLogPoint,, GoldilocksExt3.Ext3[] memory firstGatePoint,,) =
            OuterLogupExt3Verifier.verifyCoupledSumchecks(logProof, firstGate, 2, 1, firstTranscript);
        TranscriptV2.Transcript memory changedTranscript = TranscriptV2.create();
        (GoldilocksExt3.Ext3[] memory changedLogPoint,, GoldilocksExt3.Ext3[] memory changedGatePoint,,) =
            OuterLogupExt3Verifier.verifyCoupledSumchecks(logProof, changedGate, 2, 1, changedTranscript);
        assertFalse(_equal(firstLogPoint[0], changedLogPoint[0]));
        assertFalse(_equal(firstGatePoint[0], changedGatePoint[0]));

        TranscriptV2.Transcript memory changedLogTranscript = TranscriptV2.create();
        (GoldilocksExt3.Ext3[] memory logChangedLogPoint,, GoldilocksExt3.Ext3[] memory logChangedGatePoint,,) =
            OuterLogupExt3Verifier.verifyCoupledSumchecks(changedLog, firstGate, 2, 1, changedLogTranscript);
        assertFalse(_equal(firstLogPoint[0], logChangedLogPoint[0]));
        assertFalse(_equal(firstGatePoint[0], logChangedGatePoint[0]));
    }

    function test_rustCoupledCoefficientHornerGolden() external pure {
        OuterLogupExt3Verifier.SumcheckProof memory logProof = _zeroLogProof(1);
        for (uint256 i = 0; i < 5; ++i) {
            uint64 seed = uint64(i + 1);
            logProof.rounds[0].nonConstant[i] = _ext(seed, 3 * seed + 1, 5 * seed + 2);
        }
        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _zeroGateProof(1, 2);
        gateProof.rounds[0].nonConstant[0] = _ext(21, 22, 23);
        gateProof.rounds[0].nonConstant[1] = _ext(24, 25, 26);

        (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3 memory logClaim,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateClaim,
            TranscriptV2.Transcript memory transcript
        ) = OuterLogupExt3Verifier.verifyCoupledSumchecks(logProof, gateProof, 2, 1, TranscriptV2.create());
        _assertExt3(logPoint[0], 0x101d9af08db40617, 0x7529dd5b1fafe3e3, 0x2b9351ba9692677c);
        _assertExt3(gatePoint[0], 0x2a96f20b5bd7d1c2, 0xe7a35e0a0f649811, 0x6c92c57d946a386f);
        _assertExt3(logClaim, 0xf659a095b0a23acc, 0xa5ec18cc2773fdf4, 0xe7ddc8b5838d23e1);
        _assertExt3(gateClaim, 0xd05f19f354a90d75, 0x95cfdd85d425cc52, 0x81d8577401ac5afd);
        assertEq(transcript.state, 0xebdf7b3d5b53f7386388448633b9df46359226c130a99d6cc2f70973d7ed1226);
        assertEq(transcript.squeezeCounter, 6);
    }

    function test_formalAdjugateAndNormUseOffCubeCoordinatePolynomials() external pure {
        GoldilocksExt3.Ext3[3] memory coordinates;
        coordinates[0] = _ext(3, 5, 7);
        coordinates[1] = _ext(11, 13, 17);
        coordinates[2] = _ext(19, 23, 29);
        GoldilocksExt3.Ext3[3] memory adjugate = OuterLogupExt3Verifier.formalAdjugate(coordinates);
        _assertExt3(adjugate[0], 0xfffffffefffff2f4, 0xfffffffefffff4e5, 0xfffffffefffff8ea);
        _assertExt3(adjugate[1], 0x1629, 0x12ac, 0xbfd);
        _assertExt3(adjugate[2], 0x150, 0x126, 0xd0);
        _assertExt3(OuterLogupExt3Verifier.formalNorm(coordinates), 0xf9a95, 0xbdc57, 0x9dbf0);
    }

    function test_rustFormalNormLogupTerminalGolden() external {
        OuterLogupExt3Verifier.VerificationKey memory vk;
        vk.numVars = 2;
        vk.numRoutedWires = 2;
        vk.numWires = 2;
        vk.kIs = new uint256[](2);
        vk.kIs[0] = 1;
        vk.kIs[1] = 5;
        vk.subgroupGenPowers = new uint256[](2);
        vk.subgroupGenPowers[0] = 2;
        vk.subgroupGenPowers[1] = 3;

        OuterLogupExt3Verifier.Challenges memory challenges;
        challenges.beta = _ext(0xb, 0xd, 0x11);
        challenges.gamma = _ext(0x13, 0x17, 0x1d);
        challenges.lambda = _ext(0x1f, 0x25, 0x29);
        challenges.rho = _ext(0x2b, 0x2f, 0x35);
        challenges.kappa = _ext(0x3b, 0x3d, 0x43);
        challenges.tau = new GoldilocksExt3.Ext3[](2);
        challenges.tau[0] = _ext(0x47, 0x49, 0x4f);
        challenges.tau[1] = _ext(0x53, 0x59, 0x61);

        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](2);
        point[0] = _ext(0x65, 0x67, 0x6b);
        point[1] = _ext(0x6d, 0x71, 0x7f);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal;
        terminal.witness = new GoldilocksExt3.Ext3[](2);
        terminal.witness[0] = _ext(7, 0, 0);
        terminal.witness[1] = _ext(7, 0, 0);
        terminal.preprocessed = new GoldilocksExt3.Ext3[](2);
        terminal.preprocessed[0] = _ext(0xfffffffefffe22ca, 0xfffffffefffe7cf8, 0xfffffffefffee826);
        terminal.preprocessed[1] = _ext(0xfffffffeffe03616, 0xfffffffeffe63264, 0xfffffffeffed4da2);
        terminal.normInverse = new GoldilocksExt3.Ext3[](4);
        terminal.normInverse[0] = _ext(0xc4c27c5e45c77577, 0x64c3867257f97a54, 0x2778e83ac663c8cb);
        terminal.normInverse[1] = _ext(0x9dc20b6dfb188527, 0x3890e1cd9780ae50, 0x29ea44d8616a5013);
        terminal.normInverse[2] = _ext(0xab0ab85a9b966f15, 0xe6f45aad65ef5772, 0x562612f1c69527c9);
        terminal.normInverse[3] = _ext(0x0b0e2b5c04ab898d, 0x2a3e37ab7c4d104e, 0x7e6c94769f83c4f4);

        GoldilocksExt3.Ext3 memory expected = _ext(0x6b9b0be7693b8b9c, 0x08d96223959b1f0c, 0xec6c3d00e17cea3f);
        GoldilocksExt3.Ext3 memory actual = OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        assertTrue(_equal(actual, expected));
        OuterLogupExt3Verifier.verifyTerminal(vk, challenges, terminal, point, expected);

        terminal.normInverse[3].c2 += 1;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyTerminal(vk, challenges, terminal, point, expected);
    }

    function test_terminalMismatchIsRejected() external {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(1);
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(1);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _trivialTerminal();
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](1);
        point[0] = _ext(3, 5, 7);
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyTerminal(vk, challenges, terminal, point, _ext(1, 0, 0));
    }

    function test_directPiTerminalMatchesReferenceAndPreservesOrderDuplicatesAndLsbRows() external pure {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(9);
        vk.numRoutedWires = 2;
        vk.numWires = 2;
        vk.kIs = new uint256[](2);
        vk.kIs[0] = 3;
        vk.kIs[1] = 5;
        // row 1/col 0 twice, then row 258/col 1. The last entry fixes both
        // little-endian row decoding and nontrivial LSB-first bit selection.
        vk.publicInputWireMap = hex"010000010000020101";
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal;
        terminal.preprocessed = new GoldilocksExt3.Ext3[](3);
        terminal.preprocessed[0] = _ext(43, 47, 53);
        terminal.preprocessed[1] = _ext(59, 61, 67);
        terminal.preprocessed[2] = _ext(71, 73, 79);
        terminal.witness = new GoldilocksExt3.Ext3[](2);
        terminal.witness[0] = _ext(83, 89, 97);
        terminal.witness[1] = _ext(101, 103, 107);
        terminal.normInverse = new GoldilocksExt3.Ext3[](4);
        terminal.normInverse[0] = _ext(109, 113, 127);
        terminal.normInverse[1] = _ext(131, 137, 139);
        terminal.normInverse[2] = _ext(149, 151, 157);
        terminal.normInverse[3] = _ext(163, 167, 173);
        terminal.publicInputs = new uint256[](3);
        terminal.publicInputs[0] = 5;
        terminal.publicInputs[1] = 7;
        terminal.publicInputs[2] = 11;
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(9);
        challenges.eta = _ext(13, 0, 0);
        challenges.xi = _ext(17, 0, 0);
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](9);
        for (uint64 i = 0; i < 9; ++i) {
            point[i] = _ext(179 + i, 191 + i, 211 + i);
        }

        GoldilocksExt3.Ext3 memory actual = OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        assertTrue(_equal(actual, _referenceTerminal(vk, challenges, terminal, point)));

        OuterLogupExt3Verifier.VerificationKey memory reorderedVk = vk;
        reorderedVk.publicInputWireMap = hex"020101010000010000";
        GoldilocksExt3.Ext3 memory reordered =
            OuterLogupExt3Verifier.evaluateTerminal(reorderedVk, challenges, terminal, point);
        assertFalse(_equal(actual, reordered), "map order must select eta powers");

        OuterLogupExt3Verifier.VerificationKey memory oneVk = vk;
        oneVk.publicInputWireMap = hex"010000";
        OuterLogupExt3Verifier.TerminalEvaluations memory oneTerminal = terminal;
        oneTerminal.publicInputs = new uint256[](1);
        oneTerminal.publicInputs[0] = terminal.publicInputs[0];
        OuterLogupExt3Verifier.Challenges memory etaZero = challenges;
        etaZero.eta = _ext(0, 0, 0);
        assertTrue(
            _equal(
                OuterLogupExt3Verifier.evaluateTerminal(vk, etaZero, terminal, point),
                OuterLogupExt3Verifier.evaluateTerminal(oneVk, etaZero, oneTerminal, point)
            ),
            "eta=0 is the charged event hiding later terms"
        );

        OuterLogupExt3Verifier.Challenges memory xiZero = challenges;
        xiZero.xi = _ext(0, 0, 0);
        OuterLogupExt3Verifier.VerificationKey memory zeroVk = vk;
        zeroVk.publicInputWireMap = bytes("");
        OuterLogupExt3Verifier.TerminalEvaluations memory zeroTerminal = terminal;
        zeroTerminal.publicInputs = new uint256[](0);
        assertTrue(
            _equal(
                OuterLogupExt3Verifier.evaluateTerminal(vk, xiZero, terminal, point),
                OuterLogupExt3Verifier.evaluateTerminal(zeroVk, xiZero, zeroTerminal, point)
            ),
            "xi=0 is the charged event hiding the direct-PI relation"
        );
    }

    function test_directPiTerminalFailsClosedOnMapAndCanonicalRanges() external {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(2);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _trivialTerminal();
        terminal.publicInputs = new uint256[](1);
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(2);
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](2);

        vk.publicInputWireMap = hex"0000";
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        vk.publicInputWireMap = hex"040000"; // row == 2^numVars
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        vk.publicInputWireMap = hex"000001"; // column == numRoutedWires
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        vk.publicInputWireMap = hex"000000";
        terminal.publicInputs[0] = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        terminal.publicInputs[0] = 0;
        challenges.eta.c1 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        challenges = _trivialChallenges(2);
        challenges.xi.c2 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
    }

    function test_profile103PublicInputsUsesPackedMapAndUniqueRowCacheWithinGasMargin() external {
        uint256 count = 103;
        OuterLogupExt3Verifier.VerificationKey memory vk = _piGasVk();
        vk.publicInputWireMap = new bytes(3 * count);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _piGasTerminal();
        terminal.publicInputs = new uint256[](count);
        for (uint256 i = 0; i < count; ++i) {
            // Plonky2's public-input sponge packs eight raw inputs per
            // Poseidon rate block, so this conservative 103-PI profile spans
            // thirteen row-local runs. The differential test above separately
            // exercises row 258's high byte and nontrivial LSB ordering.
            uint256 row = i / 8;
            vk.publicInputWireMap[3 * i] = bytes1(uint8(row));
            vk.publicInputWireMap[3 * i + 1] = bytes1(uint8(row >> 8));
            vk.publicInputWireMap[3 * i + 2] = bytes1(uint8(i % 8));
            terminal.publicInputs[i] = i + 1;
        }
        assertEq(vk.publicInputWireMap.length, 309, "103 public inputs require exactly 309 packed map bytes");
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(13);
        challenges.eta = _ext(13, 17, 19);
        challenges.xi = _ext(23, 29, 31);
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](13);
        for (uint64 i = 0; i < 13; ++i) {
            point[i] = _ext(101 + i, 151 + i, 211 + i);
        }

        OuterLogupExt3Verifier.VerificationKey memory zeroVk = _piGasVk();
        OuterLogupExt3Verifier.TerminalEvaluations memory zeroTerminal = _piGasTerminal();
        // Warm the linked library account before both measurements.
        OuterLogupExt3Verifier.evaluateTerminal(zeroVk, challenges, zeroTerminal, point);

        uint256 before = gasleft();
        GoldilocksExt3.Ext3 memory baseline =
            OuterLogupExt3Verifier.evaluateTerminal(zeroVk, challenges, zeroTerminal, point);
        uint256 baselineGas = before - gasleft();
        before = gasleft();
        GoldilocksExt3.Ext3 memory withPublicInputs =
            OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        uint256 withPublicInputsGas = before - gasleft();
        assertFalse(_equal(baseline, withPublicInputs));
        emit log_named_uint("Outer terminal baseline gas", baselineGas);
        emit log_named_uint("Outer terminal 103-PI gas", withPublicInputsGas);
        emit log_named_uint("Outer terminal 103-PI delta gas", withPublicInputsGas - baselineGas);
        assertLt(withPublicInputsGas - baselineGas, 672_000, "direct PI binding consumes parent gas margin");
    }

    function test_rejectsShortAndLongLogRoundsWithoutTruncation() external {
        for (uint256 badLength = 4; badLength <= 6; badLength += 2) {
            OuterLogupExt3Verifier.SumcheckProof memory logProof = _zeroLogProof(1);
            logProof.rounds[0].nonConstant = new GoldilocksExt3.Ext3[](badLength);
            vm.expectRevert(InvalidMleProof.selector);
            OuterLogupExt3Verifier.verifyCoupledSumchecks(logProof, _zeroGateProof(1, 2), 2, 1, TranscriptV2.create());
        }
    }

    function test_rejectsShortAndLongGateRoundsWithoutTruncation() external {
        for (uint256 badLength = 1; badLength <= 3; badLength += 2) {
            OuterLogupExt3Verifier.SumcheckProof memory gateProof = _zeroGateProof(1, 2);
            gateProof.rounds[0].nonConstant = new GoldilocksExt3.Ext3[](badLength);
            vm.expectRevert(InvalidMleProof.selector);
            OuterLogupExt3Verifier.verifyCoupledSumchecks(_zeroLogProof(1), gateProof, 2, 1, TranscriptV2.create());
        }
    }

    function test_atomicGateDegreeComesFromVerificationKey() external {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(1);
        vk.gateDegree = 3;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verify(
            _zeroLogProof(1), _zeroGateProof(1, 2), vk, _trivialChallenges(1), _trivialTerminal(), TranscriptV2.create()
        );
    }

    function test_reviewedShapeCapsFailBeforeProofSizedAllocation() external {
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyCoupledSumchecks(
            _zeroLogProof(0), _zeroGateProof(0, 1), 11, 0, TranscriptV2.create()
        );

        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(0);
        vk.numRoutedWires = 81;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(
            vk, _trivialChallenges(0), _trivialTerminal(), new GoldilocksExt3.Ext3[](0)
        );
    }

    function test_rejectsWrongRoundCountInEveryProofFamily() external {
        OuterLogupExt3Verifier.SumcheckProof memory logProof = _zeroLogProof(0);
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyCoupledSumchecks(logProof, _zeroGateProof(1, 2), 2, 1, TranscriptV2.create());

        OuterLogupExt3Verifier.SumcheckProof memory gateProof = _zeroGateProof(1, 2);
        gateProof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](0);
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyCoupledSumchecks(_zeroLogProof(1), gateProof, 2, 1, TranscriptV2.create());
    }

    function test_rejectsEveryNonCanonicalProofAndChallengeFamily() external {
        OuterLogupExt3Verifier.SumcheckProof memory badLog = _zeroLogProof(1);
        badLog.rounds[0].nonConstant[0].c2 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyCoupledSumchecks(badLog, _zeroGateProof(1, 2), 2, 1, TranscriptV2.create());

        OuterLogupExt3Verifier.SumcheckProof memory badGate = _zeroGateProof(1, 2);
        badGate.rounds[0].nonConstant[0].c1 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyCoupledSumchecks(_zeroLogProof(1), badGate, 2, 1, TranscriptV2.create());

        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(1);
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(1);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _trivialTerminal();
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](1);
        challenges.beta.c0 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);

        challenges = _trivialChallenges(1);
        point[0].c1 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
    }

    function test_rejectsEveryNonCanonicalVkAndTerminalFamily() external {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(1);
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(1);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _trivialTerminal();
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](1);

        vk.kIs[0] = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        vk = _trivialVk(1);
        vk.subgroupGenPowers[0] = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);

        vk = _trivialVk(1);
        terminal.preprocessed[0].c0 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        terminal = _trivialTerminal();
        terminal.witness[1].c1 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        terminal = _trivialTerminal();
        terminal.normInverse[1].c2 = FIELD_MODULUS;
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
    }

    function test_rejectsShortAndLongTerminalFamilies() external {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(1);
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(1);
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](1);
        for (uint256 family = 0; family < 3; ++family) {
            for (uint256 delta = 0; delta < 2; ++delta) {
                OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _trivialTerminal();
                uint256 expected = family == 0 ? 2 : 2;
                uint256 length = delta == 0 ? expected - 1 : expected + 1;
                if (family == 0) {
                    terminal.preprocessed = new GoldilocksExt3.Ext3[](length);
                } else if (family == 1) {
                    terminal.witness = new GoldilocksExt3.Ext3[](length);
                } else {
                    terminal.normInverse = new GoldilocksExt3.Ext3[](length);
                }
                vm.expectRevert(InvalidMleProof.selector);
                OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
            }
        }
    }

    function test_rejectsNonCanonicalFinalClaimBeforeFieldEquality() external {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(1);
        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(1);
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal = _trivialTerminal();
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](1);
        vm.expectRevert(InvalidMleProof.selector);
        OuterLogupExt3Verifier.verifyTerminal(vk, challenges, terminal, point, _ext(FIELD_MODULUS, 0, 0));
    }

    function testFuzz_terminalScratchEvaluatorMatchesHighLevelReference(uint256 seed) external {
        OuterLogupExt3Verifier.VerificationKey memory vk;
        vk.numVars = 2;
        vk.gateDegree = 2;
        vk.numConstants = 1;
        vk.numRoutedWires = 3;
        vk.numWires = 4;
        vk.kIs = new uint256[](3);
        for (uint256 i = 0; i < vk.kIs.length; ++i) {
            vk.kIs[i] = 1 + uint256(_randomExt3(seed, 10 + i).c0) % (uint256(FIELD_MODULUS) - 1);
        }
        vk.subgroupGenPowers = new uint256[](2);
        vk.subgroupGenPowers[0] = uint256(_randomExt3(seed, 20).c0);
        vk.subgroupGenPowers[1] = uint256(_randomExt3(seed, 21).c0);

        OuterLogupExt3Verifier.Challenges memory challenges;
        challenges.beta = _randomExt3(seed, 30);
        challenges.gamma = _randomExt3(seed, 31);
        challenges.lambda = _randomExt3(seed, 32);
        challenges.rho = _randomExt3(seed, 33);
        challenges.kappa = _randomExt3(seed, 34);
        challenges.tau = new GoldilocksExt3.Ext3[](2);
        challenges.tau[0] = _randomExt3(seed, 35);
        challenges.tau[1] = _randomExt3(seed, 36);

        OuterLogupExt3Verifier.TerminalEvaluations memory terminal;
        terminal.preprocessed = new GoldilocksExt3.Ext3[](4);
        terminal.witness = new GoldilocksExt3.Ext3[](4);
        terminal.normInverse = new GoldilocksExt3.Ext3[](6);
        for (uint256 i = 0; i < terminal.preprocessed.length; ++i) {
            terminal.preprocessed[i] = _randomExt3(seed, 40 + i);
            terminal.witness[i] = _randomExt3(seed, 50 + i);
        }
        for (uint256 i = 0; i < terminal.normInverse.length; ++i) {
            terminal.normInverse[i] = _randomExt3(seed, 60 + i);
        }
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](2);
        point[0] = _randomExt3(seed, 70);
        point[1] = _randomExt3(seed, 71);

        GoldilocksExt3.Ext3 memory expected = _referenceTerminal(vk, challenges, terminal, point);
        GoldilocksExt3.Ext3 memory actual = OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        assertTrue(_equal(actual, expected), "scratch/high-level terminal differential");
    }

    function testFuzz_directPiCacheAndFactoringMatchHighLevelReference(uint256 seed, uint8 rawCount) external {
        _assertDirectPiDifferential(seed, uint256(rawCount) % 104, false);
    }

    function test_directPiAllUniqueRowsAndEveryVaryingBitMatchHighLevelReference() external {
        _assertDirectPiDifferential(0x50495f414c4c5f42495453, 103, true);
    }

    function _assertDirectPiDifferential(uint256 seed, uint256 count, bool forceAllBits) private {
        OuterLogupExt3Verifier.VerificationKey memory vk = _trivialVk(13);
        vk.numRoutedWires = 4;
        vk.numWires = 4;
        vk.kIs = new uint256[](4);
        for (uint256 i = 0; i < vk.kIs.length; ++i) {
            vk.kIs[i] = i + 3;
        }
        vk.publicInputWireMap = new bytes(3 * count);

        OuterLogupExt3Verifier.TerminalEvaluations memory terminal;
        terminal.preprocessed = new GoldilocksExt3.Ext3[](5);
        terminal.witness = new GoldilocksExt3.Ext3[](4);
        terminal.normInverse = new GoldilocksExt3.Ext3[](8);
        terminal.publicInputs = new uint256[](count);
        for (uint256 i = 0; i < terminal.preprocessed.length; ++i) {
            terminal.preprocessed[i] = _randomExt3(seed, 100 + i);
        }
        for (uint256 i = 0; i < terminal.witness.length; ++i) {
            terminal.witness[i] = _randomExt3(seed, 110 + i);
        }
        for (uint256 i = 0; i < terminal.normInverse.length; ++i) {
            terminal.normInverse[i] = _randomExt3(seed, 120 + i);
        }

        for (uint256 i = 0; i < count; ++i) {
            uint256 row;
            if (forceAllBits) {
                // 0 and 8191 force every one of the 13 row bits to vary. The
                // remaining arithmetic progression is injective for i<103.
                row = i == 0 ? 0 : (i == 1 ? 8191 : (i - 1) * 79);
            } else if (i != 0 && i % 7 == 0) {
                // Deterministically include non-adjacent duplicate rows, so
                // the cache must find entries older than its fast-path tail.
                uint256 previous = 3 * (i - 4);
                row =
                    uint8(vk.publicInputWireMap[previous]) | (uint256(uint8(vk.publicInputWireMap[previous + 1])) << 8);
            } else {
                row = uint256(keccak256(abi.encode(seed, i, "pi-row"))) & 8191;
            }
            uint256 column = uint256(keccak256(abi.encode(seed, i, "pi-column"))) % 4;
            uint256 offset = 3 * i;
            vk.publicInputWireMap[offset] = bytes1(uint8(row));
            vk.publicInputWireMap[offset + 1] = bytes1(uint8(row >> 8));
            vk.publicInputWireMap[offset + 2] = bytes1(uint8(column));
            terminal.publicInputs[i] = uint256(_randomExt3(seed, 200 + i).c0);
        }

        OuterLogupExt3Verifier.Challenges memory challenges = _trivialChallenges(13);
        challenges.eta = _randomExt3(seed, 300);
        challenges.xi = _randomExt3(seed, 301);
        GoldilocksExt3.Ext3[] memory point = new GoldilocksExt3.Ext3[](13);
        for (uint256 i = 0; i < point.length; ++i) {
            point[i] = _randomExt3(seed, 320 + i);
        }

        GoldilocksExt3.Ext3 memory expected = _referenceTerminal(vk, challenges, terminal, point);
        GoldilocksExt3.Ext3 memory actual = OuterLogupExt3Verifier.evaluateTerminal(vk, challenges, terminal, point);
        assertTrue(_equal(actual, expected), "direct PI cache/factoring differential");
    }

    function _zeroLogProof(uint256 numVars) private pure returns (OuterLogupExt3Verifier.SumcheckProof memory proof) {
        proof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](numVars);
        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            proof.rounds[roundIndex].nonConstant = new GoldilocksExt3.Ext3[](5);
        }
    }

    function _zeroGateProof(uint256 numVars, uint256 degree)
        private
        pure
        returns (OuterLogupExt3Verifier.SumcheckProof memory proof)
    {
        proof.rounds = new OuterLogupExt3Verifier.CoefficientRound[](numVars);
        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            proof.rounds[roundIndex].nonConstant = new GoldilocksExt3.Ext3[](degree);
        }
    }

    function _trivialVk(uint256 numVars) private pure returns (OuterLogupExt3Verifier.VerificationKey memory vk) {
        vk.numVars = numVars;
        vk.gateDegree = 2;
        vk.numConstants = 1;
        vk.numRoutedWires = 1;
        vk.numWires = 2;
        vk.kIs = new uint256[](1);
        vk.kIs[0] = 3;
        vk.subgroupGenPowers = new uint256[](numVars);
        for (uint256 i = 0; i < numVars; ++i) {
            vk.subgroupGenPowers[i] = i + 2;
        }
    }

    function _piGasVk() private pure returns (OuterLogupExt3Verifier.VerificationKey memory vk) {
        vk = _trivialVk(13);
        vk.numRoutedWires = 8;
        vk.numWires = 8;
        vk.kIs = new uint256[](8);
        for (uint256 i = 0; i < 8; ++i) {
            vk.kIs[i] = i + 3;
        }
    }

    function _piGasTerminal() private pure returns (OuterLogupExt3Verifier.TerminalEvaluations memory terminal) {
        terminal.preprocessed = new GoldilocksExt3.Ext3[](9);
        terminal.witness = new GoldilocksExt3.Ext3[](8);
        terminal.normInverse = new GoldilocksExt3.Ext3[](16);
        for (uint64 i = 0; i < 8; ++i) {
            terminal.witness[i] = _ext(73 + i, 89 + i, 101 + i);
        }
    }

    function _trivialChallenges(uint256 numVars)
        private
        pure
        returns (OuterLogupExt3Verifier.Challenges memory challenges)
    {
        // beta=1, gamma=0 and routed witness=0 make both formal denominators one.
        challenges.beta = _ext(1, 0, 0);
        challenges.gamma = _ext(0, 0, 0);
        challenges.lambda = _ext(5, 7, 11);
        challenges.rho = _ext(13, 17, 19);
        challenges.kappa = _ext(23, 29, 31);
        challenges.tau = new GoldilocksExt3.Ext3[](numVars);
        for (uint256 i = 0; i < numVars; ++i) {
            challenges.tau[i] = _ext(uint64(37 + i), uint64(41 + i), uint64(43 + i));
        }
    }

    function _trivialTerminal() private pure returns (OuterLogupExt3Verifier.TerminalEvaluations memory terminal) {
        terminal.preprocessed = new GoldilocksExt3.Ext3[](2);
        terminal.preprocessed[0] = _ext(47, 53, 59); // unused constant, still bound and checked
        terminal.preprocessed[1] = _ext(61, 67, 71); // sigma is irrelevant because gamma=0
        terminal.witness = new GoldilocksExt3.Ext3[](2);
        terminal.witness[1] = _ext(73, 79, 83); // unused wire, still bound and checked
        terminal.normInverse = new GoldilocksExt3.Ext3[](2);
        terminal.normInverse[0] = _ext(1, 0, 0);
        terminal.normInverse[1] = _ext(1, 0, 0);
    }

    function _referenceTerminal(
        OuterLogupExt3Verifier.VerificationKey memory vk,
        OuterLogupExt3Verifier.Challenges memory challenges,
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) private pure returns (GoldilocksExt3.Ext3 memory) {
        GoldilocksExt3.Ext3 memory eqValue = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory subgroup = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 i = 0; i < point.length; ++i) {
            GoldilocksExt3.Ext3 memory eqFactor = GoldilocksExt3.add(
                GoldilocksExt3.sub(GoldilocksExt3.sub(one, challenges.tau[i]), point[i]),
                GoldilocksExt3.double_(GoldilocksExt3.mul(challenges.tau[i], point[i]))
            );
            eqValue = GoldilocksExt3.mul(eqValue, eqFactor);
            uint64 generatorMinusOne = uint64(addmod(vk.subgroupGenPowers[i], FIELD_MODULUS - 1, FIELD_MODULUS));
            subgroup = GoldilocksExt3.mul(
                subgroup, GoldilocksExt3.add(one, GoldilocksExt3.mulScalar(point[i], generatorMinusOne))
            );
        }

        GoldilocksExt3.Ext3 memory helperChecks = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory logup = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory lambdaPower = GoldilocksExt3.one();
        for (uint256 i = 0; i < vk.numRoutedWires; ++i) {
            GoldilocksExt3.Ext3 memory identityPosition = GoldilocksExt3.mulScalar(subgroup, uint64(vk.kIs[i]));
            GoldilocksExt3.Ext3 memory sigmaPosition = terminal.preprocessed[vk.numConstants + i];
            GoldilocksExt3.Ext3[3] memory identityCoordinates =
                _referenceCoordinates(terminal.witness[i], identityPosition, challenges.beta, challenges.gamma);
            GoldilocksExt3.Ext3[3] memory sigmaCoordinates =
                _referenceCoordinates(terminal.witness[i], sigmaPosition, challenges.beta, challenges.gamma);
            GoldilocksExt3.Ext3[3] memory identityFormal = _referenceAdjugate(identityCoordinates);
            GoldilocksExt3.Ext3[3] memory sigmaFormal = _referenceAdjugate(sigmaCoordinates);
            GoldilocksExt3.Ext3 memory identityZero = GoldilocksExt3.sub(
                GoldilocksExt3.mul(terminal.normInverse[i], _referenceNorm(identityCoordinates, identityFormal)), one
            );
            GoldilocksExt3.Ext3 memory sigmaZero = GoldilocksExt3.sub(
                GoldilocksExt3.mul(
                    terminal.normInverse[vk.numRoutedWires + i], _referenceNorm(sigmaCoordinates, sigmaFormal)
                ),
                one
            );
            helperChecks = GoldilocksExt3.add(
                helperChecks,
                GoldilocksExt3.mul(
                    lambdaPower, GoldilocksExt3.add(identityZero, GoldilocksExt3.mul(challenges.rho, sigmaZero))
                )
            );
            logup = GoldilocksExt3.add(
                logup,
                GoldilocksExt3.sub(
                    GoldilocksExt3.mul(terminal.normInverse[i], _referenceRecompose(identityFormal)),
                    GoldilocksExt3.mul(terminal.normInverse[vk.numRoutedWires + i], _referenceRecompose(sigmaFormal))
                )
            );
            lambdaPower = GoldilocksExt3.mul(lambdaPower, challenges.lambda);
        }
        GoldilocksExt3.Ext3 memory permutation =
            GoldilocksExt3.add(GoldilocksExt3.mul(eqValue, helperChecks), GoldilocksExt3.mul(challenges.kappa, logup));
        return GoldilocksExt3.add(
            permutation,
            GoldilocksExt3.mul(challenges.xi, _referencePublicInputBinding(vk, challenges, terminal, point))
        );
    }

    function _referencePublicInputBinding(
        OuterLogupExt3Verifier.VerificationKey memory vk,
        OuterLogupExt3Verifier.Challenges memory challenges,
        OuterLogupExt3Verifier.TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) private pure returns (GoldilocksExt3.Ext3 memory binding) {
        GoldilocksExt3.Ext3 memory etaPower = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 i = 0; i < terminal.publicInputs.length; ++i) {
            uint256 offset = 3 * i;
            uint256 row =
                uint8(vk.publicInputWireMap[offset]) | (uint256(uint8(vk.publicInputWireMap[offset + 1])) << 8);
            uint256 column = uint8(vk.publicInputWireMap[offset + 2]);
            GoldilocksExt3.Ext3 memory eqRow = one;
            for (uint256 variable = 0; variable < point.length; ++variable) {
                eqRow = GoldilocksExt3.mul(
                    eqRow, ((row >> variable) & 1) == 0 ? GoldilocksExt3.sub(one, point[variable]) : point[variable]
                );
            }
            GoldilocksExt3.Ext3 memory difference =
                GoldilocksExt3.sub(terminal.witness[column], _ext(uint64(terminal.publicInputs[i]), 0, 0));
            binding = GoldilocksExt3.add(binding, GoldilocksExt3.mul(etaPower, GoldilocksExt3.mul(eqRow, difference)));
            etaPower = GoldilocksExt3.mul(etaPower, challenges.eta);
        }
    }

    function _referenceCoordinates(
        GoldilocksExt3.Ext3 memory wire,
        GoldilocksExt3.Ext3 memory position,
        GoldilocksExt3.Ext3 memory beta,
        GoldilocksExt3.Ext3 memory gamma
    ) private pure returns (GoldilocksExt3.Ext3[3] memory coordinates) {
        coordinates[0] = GoldilocksExt3.add(
            GoldilocksExt3.add(_ext(beta.c0, 0, 0), wire), GoldilocksExt3.mulScalar(position, gamma.c0)
        );
        coordinates[1] = GoldilocksExt3.add(_ext(beta.c1, 0, 0), GoldilocksExt3.mulScalar(position, gamma.c1));
        coordinates[2] = GoldilocksExt3.add(_ext(beta.c2, 0, 0), GoldilocksExt3.mulScalar(position, gamma.c2));
    }

    function _referenceAdjugate(GoldilocksExt3.Ext3[3] memory coordinates)
        private
        pure
        returns (GoldilocksExt3.Ext3[3] memory adjugate)
    {
        GoldilocksExt3.Ext3 memory a = coordinates[0];
        GoldilocksExt3.Ext3 memory b = coordinates[1];
        GoldilocksExt3.Ext3 memory c = coordinates[2];
        adjugate[0] = GoldilocksExt3.sub(GoldilocksExt3.square(a), GoldilocksExt3.double_(GoldilocksExt3.mul(b, c)));
        adjugate[1] = GoldilocksExt3.sub(GoldilocksExt3.double_(GoldilocksExt3.square(c)), GoldilocksExt3.mul(a, b));
        adjugate[2] = GoldilocksExt3.sub(GoldilocksExt3.square(b), GoldilocksExt3.mul(a, c));
    }

    function _referenceNorm(GoldilocksExt3.Ext3[3] memory coordinates, GoldilocksExt3.Ext3[3] memory adjugate)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory)
    {
        return GoldilocksExt3.add(
            GoldilocksExt3.mul(coordinates[0], adjugate[0]),
            GoldilocksExt3.double_(
                GoldilocksExt3.add(
                    GoldilocksExt3.mul(coordinates[2], adjugate[1]), GoldilocksExt3.mul(coordinates[1], adjugate[2])
                )
            )
        );
    }

    function _referenceRecompose(GoldilocksExt3.Ext3[3] memory adjugate)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory result)
    {
        GoldilocksExt3.Ext3 memory thetaS1 =
            _ext(uint64(addmod(adjugate[1].c2, adjugate[1].c2, FIELD_MODULUS)), adjugate[1].c0, adjugate[1].c1);
        GoldilocksExt3.Ext3 memory thetaSquaredS2 = _ext(
            uint64(addmod(adjugate[2].c1, adjugate[2].c1, FIELD_MODULUS)),
            uint64(addmod(adjugate[2].c2, adjugate[2].c2, FIELD_MODULUS)),
            adjugate[2].c0
        );
        result = GoldilocksExt3.add(adjugate[0], GoldilocksExt3.add(thetaS1, thetaSquaredS2));
    }

    function _randomExt3(uint256 seed, uint256 domain) private pure returns (GoldilocksExt3.Ext3 memory value) {
        value.c0 = uint64(uint256(keccak256(abi.encode(seed, domain, uint256(0)))) % uint256(FIELD_MODULUS));
        value.c1 = uint64(uint256(keccak256(abi.encode(seed, domain, uint256(1)))) % uint256(FIELD_MODULUS));
        value.c2 = uint64(uint256(keccak256(abi.encode(seed, domain, uint256(2)))) % uint256(FIELD_MODULUS));
    }

    function _ext(uint64 c0, uint64 c1, uint64 c2) private pure returns (GoldilocksExt3.Ext3 memory) {
        return GoldilocksExt3.Ext3(c0, c1, c2);
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
