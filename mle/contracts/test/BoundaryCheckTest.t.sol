// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifier} from "../src/MleVerifier.sol";
import {SumcheckVerifier} from "../src/SumcheckVerifier.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {GoldilocksField} from "../src/GoldilocksField.sol";
import {Plonky2GateEvaluator} from "../src/Plonky2GateEvaluator.sol";
import {EqPolyLib} from "../src/EqPolyLib.sol";
import {InvalidMleProof, InvalidMleVerifierChainId, MleProofEngineUnavailable} from "../src/MleProofErrors.sol";

/// @title BoundaryCheckTest — negative tests for C1 (gatesDigest) and C2
/// (canonicalization) boundary checks added under `vulcheck-mle-solidity`.
///
/// Reuses the `small_mul.json` fixture as a valid baseline and then mutates
/// exactly one field to verify each attack path is rejected.
contract BoundaryCheckTest is Test {
    using GoldilocksField for uint256;

    /// @dev Exact retired `MleVerifier.MleProof` ABI layout at
    /// submodule baseline 54c0b86a. Keeping this test-only type separate from
    /// the current struct ensures the old-proof regression exercises genuine
    /// v0-shaped bytes rather than a v1 proof with `protocolVersion = 0`.
    struct LegacyV0MleProof {
        uint256[] circuitDigest;
        bytes whirTranscript;
        bytes whirHints;
        bytes32 preprocessedRoot;
        bytes32 witnessRoot;
        bytes32 auxCommitmentRoot;
        uint256 preprocessedEvalValue;
        uint256 preprocessedBatchR;
        uint256[] preprocessedIndividualEvals;
        uint256 witnessEvalValue;
        uint256 witnessBatchR;
        uint256[] witnessIndividualEvals;
        uint256 auxBatchR;
        uint256 auxConstraintEval;
        uint256 auxPermEval;
        uint256 auxEvalValue;
        SumcheckVerifier.SumcheckProof combinedProof;
        uint256[] publicInputs;
        uint256 alpha;
        uint256 beta;
        uint256 gamma;
        uint256 mu;
        GoldilocksExt3.Ext3 preprocessedWhirEval;
        GoldilocksExt3.Ext3 witnessWhirEval;
        GoldilocksExt3.Ext3 auxWhirEval;
        bytes32 inverseHelpersCommitmentRoot;
        uint256 inverseHelpersBatchR;
        SumcheckVerifier.SumcheckProof invSumcheckProof;
        SumcheckVerifier.SumcheckProof hSumcheckProof;
        uint256 lambdaInv;
        uint256 muInv;
        uint256 lambdaH;
        uint256[] witnessIndividualEvalsAtRInv;
        uint256[] preprocessedIndividualEvalsAtRInv;
        uint256[] inverseHelpersEvalsAtRInv;
        uint256[] inverseHelpersEvalsAtRH;
        uint256 gSubEvalAtRInv;
        uint256 witnessEvalValueAtRInv;
        uint256 preprocessedEvalValueAtRInv;
        GoldilocksExt3.Ext3 inverseHelpersWhirEvalAtRGate;
        GoldilocksExt3.Ext3 preprocessedWhirEvalAtRInv;
        GoldilocksExt3.Ext3 witnessWhirEvalAtRInv;
        GoldilocksExt3.Ext3 auxWhirEvalAtRInv;
        GoldilocksExt3.Ext3 inverseHelpersWhirEvalAtRInv;
        GoldilocksExt3.Ext3 preprocessedWhirEvalAtRH;
        GoldilocksExt3.Ext3 witnessWhirEvalAtRH;
        GoldilocksExt3.Ext3 auxWhirEvalAtRH;
        GoldilocksExt3.Ext3 inverseHelpersWhirEvalAtRH;
        uint256 extChallenge;
        SumcheckVerifier.SumcheckProof gateSumcheckProof;
        uint256[] witnessIndividualEvalsAtRGateV2;
        uint256[] preprocessedIndividualEvalsAtRGateV2;
        uint256 witnessEvalValueAtRGateV2;
        uint256 preprocessedEvalValueAtRGateV2;
        GoldilocksExt3.Ext3 preprocessedWhirEvalAtRGateV2;
        GoldilocksExt3.Ext3 witnessWhirEvalAtRGateV2;
        GoldilocksExt3.Ext3 auxWhirEvalAtRGateV2;
        GoldilocksExt3.Ext3 inverseHelpersWhirEvalAtRGateV2;
        uint256 quotientDegreeFactor;
        uint256 numSelectors;
        uint256 numGateConstraints;
        Plonky2GateEvaluator.GateInfo[] gates;
        uint256[4] publicInputsHash;
    }

    MleVerifier verifier;

    uint256 constant P = 0xFFFFFFFF00000001;
    uint256 constant FROZEN_W0_BEFORE = 3051498664030569048;
    uint256 constant FROZEN_W0_AFTER = 3051498664030569049;
    uint256 constant FROZEN_W80_BEFORE = 6063719204085150528;
    uint256 constant FROZEN_W80_AFTER = 2587698932769584699;
    uint256 constant FROZEN_A1_BEFORE = 7495656216612080666;
    uint256 constant FROZEN_A1_AFTER = 14584819668673277578;
    uint256 constant FROZEN_RHO = 4731229214337826042;
    uint256 constant FROZEN_BETA = 17800375341204939063;
    uint256 constant FROZEN_GAMMA = 9041901820383133626;
    uint256 constant FROZEN_LAMBDA_INV = 16769653635246974393;
    uint256 constant FROZEN_MU_INV = 11315289580255226170;
    uint256 constant FROZEN_K1 = 14293326489335486720;
    uint256 constant FROZEN_G_SUB = 11042185228133710199;
    uint256 constant FROZEN_W1 = 78509372807566819;
    uint256 constant FROZEN_A0 = 16828114539042804903;
    uint256 constant FROZEN_B0 = 13178207313111168954;

    uint256 constant PARENT_W0_BEFORE = 8093513556413711660;
    uint256 constant PARENT_W0_AFTER = 8093513556413711661;
    uint256 constant PARENT_W80_BEFORE = 2800508231593448274;
    uint256 constant PARENT_W80_AFTER = 15862999140234155880;
    uint256 constant PARENT_A1_BEFORE = 17516173920822186472;
    uint256 constant PARENT_A1_AFTER = 6112368312529039975;
    uint256 constant PARENT_RHO = 6145656649326269386;
    uint256 constant PARENT_BETA = 18087660371601274625;
    uint256 constant PARENT_GAMMA = 10481604735508439039;
    uint256 constant PARENT_LAMBDA_INV = 1097435823362543930;
    uint256 constant PARENT_MU_INV = 171987289746320364;
    uint256 constant PARENT_G_SUB = 13562199838588320182;
    uint256 constant PARENT_W1 = 12819036921327938012;
    uint256 constant PARENT_A0 = 9601097877492032537;
    uint256 constant PARENT_B0 = 8488046535134267022;

    function setUp() public {
        verifier = new MleVerifier(block.chainid);
    }

    // ──────────────────────────────────────────────────────────────────
    //  Immutable deployment-chain pin — not a PCS soundness fix
    // ──────────────────────────────────────────────────────────────────

    function test_chainPin_zeroConfiguredChainReverts() public {
        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierChainId.selector, uint256(0), block.chainid));
        new MleVerifier(0);
    }

    function test_chainPin_deploymentMismatchReverts() public {
        vm.chainId(1);
        vm.expectRevert(abi.encodeWithSelector(InvalidMleVerifierChainId.selector, uint256(31337), uint256(1)));
        new MleVerifier(31337);
    }

    function test_chainPin_matchingConfiguredChainDeploys() public {
        vm.chainId(11155111);
        MleVerifier configured = new MleVerifier(11155111);
        assertEq(configured.allowedChainId(), 11155111);
    }

    function test_chainPin_validProofCannotVerifyAfterChainIdChange() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        vm.chainId(1);
        vm.expectRevert(abi.encodeWithSelector(MleProofEngineUnavailable.selector, uint256(1)));
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_chainPin_correlatedTerminalForgeryCannotVerifyAfterChainIdChange() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        // Concrete batching-kernel values found by red team. The historical
        // v0 fixture identities are asserted by the enabled-chain regression
        // below; this chain-order test only proves that containment runs first.
        // The immutable chain pin must run before proof-dependent checks.
        proof.witnessIndividualEvalsAtRInv[0] = FROZEN_W0_AFTER;
        proof.witnessIndividualEvalsAtRInv[80] = FROZEN_W80_AFTER;
        proof.inverseHelpersEvalsAtRInv[1] = FROZEN_A1_AFTER;

        vm.chainId(11155111);
        vm.expectRevert(abi.encodeWithSelector(MleProofEngineUnavailable.selector, uint256(11155111)));
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_chainPin_selectedChainFixtureRemainsUsable() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        assertEq(block.chainid, verifier.allowedChainId(), "fixture must run on the selected chain");
        assertTrue(verifier.verify(proof, vp, whir, gatesDigest));
    }

    /// @notice Freeze the audit's exact small_mul triple and reject it on the
    /// verifier's enabled allowed chain with the proof-dependent selector.
    /// Roots, WHIR bytes, sumchecks, public inputs and the serialized aggregate
    /// fields are left byte-for-byte unchanged. This freezes the historical
    /// mutation values; the following generalized test separately proves the
    /// batching and terminal-expression kernel against the current fixture.
    function test_pcs_frozen_smallMul_forgery_rejected_on_allowed_chain() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        bytes32 transcriptHash = keccak256(proof.whirTranscript);
        bytes32 hintsHash = keccak256(proof.whirHints);
        bytes32 witnessRoot = proof.witnessRoot;
        bytes32 helpersRoot = proof.inverseHelpersCommitmentRoot;
        uint256 witnessBatch = proof.witnessEvalValueAtRInv;

        // Keep both sides of the historical mutation and prove, over the
        // original transcript challenges, that this exact triple preserved
        // both the scalar witness batch and Phi_inv terminal expression.
        assertEq(FROZEN_W0_AFTER, FROZEN_W0_BEFORE + 1);
        assertTrue(FROZEN_W80_AFTER != FROZEN_W80_BEFORE);
        assertTrue(FROZEN_A1_AFTER != FROZEN_A1_BEFORE);
        uint256 witnessBatchDelta = uint256(1).add(FROZEN_RHO.modExp(80).mul(FROZEN_W80_AFTER.sub(FROZEN_W80_BEFORE)));
        assertEq(witnessBatchDelta, 0, "frozen witness delta must be an exact RLC kernel");
        uint256 denomId1 = FROZEN_BETA.add(FROZEN_W1).add(FROZEN_GAMMA.mul(FROZEN_K1.mul(FROZEN_G_SUB)));
        uint256 terminalDelta = FROZEN_A0.add(FROZEN_MU_INV.mul(FROZEN_B0))
            .add(FROZEN_LAMBDA_INV.mul(denomId1).mul(FROZEN_A1_AFTER.sub(FROZEN_A1_BEFORE)));
        assertEq(terminalDelta, 0, "frozen inverse delta must preserve Phi_inv");

        // Plonky2 randomizes unused PI wires, so the regenerated packed-v1
        // fixture does not have the historical BEFORE values. Injecting the
        // frozen AFTER values still has to fail on the enabled chain. The next
        // test rebuilds a terminal-preserving kernel for this exact v1 proof
        // and establishes that its rejecting boundary is the packed PCS.
        proof.witnessIndividualEvalsAtRInv[0] = FROZEN_W0_AFTER;
        proof.witnessIndividualEvalsAtRInv[80] = FROZEN_W80_AFTER;
        proof.inverseHelpersEvalsAtRInv[1] = FROZEN_A1_AFTER;

        assertEq(block.chainid, verifier.allowedChainId());
        assertEq(keccak256(proof.whirTranscript), transcriptHash);
        assertEq(keccak256(proof.whirHints), hintsHash);
        assertEq(proof.witnessRoot, witnessRoot);
        assertEq(proof.inverseHelpersCommitmentRoot, helpersRoot);
        assertEq(proof.witnessEvalValueAtRInv, witnessBatch);
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice Freeze the second concrete exploit from the parent validity
    /// fixture. Its retired v0 proof bytes cannot be interpreted as a packed
    /// v1 proof, so this test pins the exact arithmetic kernel independently
    /// from the current-fixture PCS rejection exercised below.
    function test_frozen_parentValidity_v0_kernel_constants() public pure {
        assertEq(PARENT_W0_AFTER, PARENT_W0_BEFORE + 1);
        uint256 witnessBatchDelta = uint256(1).add(PARENT_RHO.modExp(80).mul(PARENT_W80_AFTER.sub(PARENT_W80_BEFORE)));
        assertEq(witnessBatchDelta, 0, "parent witness delta must be an exact RLC kernel");

        uint256 denomId1 = PARENT_BETA.add(PARENT_W1).add(PARENT_GAMMA.mul(FROZEN_K1.mul(PARENT_G_SUB)));
        uint256 terminalDelta = PARENT_A0.add(PARENT_MU_INV.mul(PARENT_B0))
            .add(PARENT_LAMBDA_INV.mul(denomId1).mul(PARENT_A1_AFTER.sub(PARENT_A1_BEFORE)));
        assertEq(terminalDelta, 0, "parent inverse delta must preserve Phi_inv");
    }

    /// @notice Construct the batching-kernel attack against the current v1
    /// fixture rather than relying on historical challenge values. The two
    /// witness deltas preserve the witness RLC, while the A_1 delta preserves
    /// the complete Phi_inv terminal expression. The only remaining changed
    /// statement is therefore a false opening of the committed constituents.
    function test_pcs_generalized_kernel_forgery_rejected_on_allowed_chain() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        assertTrue(verifier.verify(proof, vp, whir, gatesDigest), "honest v1 fixture");
        uint256 originalBatch = _batchEval(proof.witnessIndividualEvalsAtRInv, proof.witnessBatchR);
        uint256 originalTerminal = _invInnerModel(proof, vp);
        bytes32 transcriptHash = keccak256(proof.whirTranscript);
        bytes32 hintsHash = keccak256(proof.whirHints);

        // delta_0 = 1 and delta_80 = -rho^-80 create a non-zero RLC kernel
        // vector. Wire 80 is outside the 80-routed-wire terminal loop.
        uint256 rho80 = proof.witnessBatchR.modExp(80);
        uint256 deltaW80 = rho80.inv().neg();
        proof.witnessIndividualEvalsAtRInv[0] = proof.witnessIndividualEvalsAtRInv[0].add(1);
        proof.witnessIndividualEvalsAtRInv[80] = proof.witnessIndividualEvalsAtRInv[80].add(deltaW80);

        // Changing w_0 by one changes Phi_inv's inner value by
        // A_0 + mu_inv*B_0. Cancel it through A_1, whose coefficient is
        // lambda_inv * D_id,1.
        uint256 nr = vp.numRoutedWires;
        uint256 numerator = proof.inverseHelpersEvalsAtRInv[0].add(proof.muInv.mul(proof.inverseHelpersEvalsAtRInv[nr]));
        uint256 denominatorId1 = proof.beta.add(proof.witnessIndividualEvalsAtRInv[1])
            .add(proof.gamma.mul(vp.kIs[1].mul(proof.gSubEvalAtRInv)));
        uint256 deltaA1 = numerator.mul(proof.lambdaInv.mul(denominatorId1).inv()).neg();
        proof.inverseHelpersEvalsAtRInv[1] = proof.inverseHelpersEvalsAtRInv[1].add(deltaA1);

        assertEq(_batchEval(proof.witnessIndividualEvalsAtRInv, proof.witnessBatchR), originalBatch);
        assertEq(_invInnerModel(proof, vp), originalTerminal);
        assertEq(keccak256(proof.whirTranscript), transcriptHash);
        assertEq(keccak256(proof.whirHints), hintsHash);
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice Preserve the complete Phi_h terminal expression with a
    /// non-zero two-coordinate kernel. No scalar batch check is available at
    /// r_h, so rejection is attributable to the direct inverse-helper opening.
    function test_pcs_inverse_h_terminal_kernel_rejected_on_allowed_chain() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        assertTrue(verifier.verify(proof, vp, whir, gatesDigest));
        uint256 beforeTerminal = _hInnerModel(proof);
        bytes32 transcriptHash = keccak256(proof.whirTranscript);
        bytes32 hintsHash = keccak256(proof.whirHints);
        bytes32 helperRoot = proof.inverseHelpersCommitmentRoot;

        uint256 nr = vp.numRoutedWires;
        proof.inverseHelpersEvalsAtRH[0] = proof.inverseHelpersEvalsAtRH[0].add(1);
        proof.inverseHelpersEvalsAtRH[nr] = proof.inverseHelpersEvalsAtRH[nr].add(1);

        assertEq(_hInnerModel(proof), beforeTerminal);
        assertEq(keccak256(proof.whirTranscript), transcriptHash);
        assertEq(keccak256(proof.whirHints), hintsHash);
        assertEq(proof.inverseHelpersCommitmentRoot, helperRoot);
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice Point 0 / preprocessed: preserve the retained scalar batch with
    /// a live-challenge two-coordinate kernel. This group has no input to the
    /// combined terminal, so packed PCS binding is the only changed check.
    function test_pcs_kernel_matrix_combined_preprocessed_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        bytes32 artifacts = _fixedArtifactHash(proof);
        uint256 originalBatch = _batchEval(proof.preprocessedIndividualEvals, proof.preprocessedBatchR);
        proof.preprocessedIndividualEvals[0] = proof.preprocessedIndividualEvals[0].add(proof.preprocessedBatchR);
        proof.preprocessedIndividualEvals[1] = proof.preprocessedIndividualEvals[1].sub(1);
        assertEq(_batchEval(proof.preprocessedIndividualEvals, proof.preprocessedBatchR), originalBatch);
        _expectPcsReject(proof, vp, whir, gatesDigest, artifacts);
    }

    /// @notice Point 0 / witness: the corresponding live-challenge scalar
    /// batch kernel for the witness group.
    function test_pcs_kernel_matrix_combined_witness_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        bytes32 artifacts = _fixedArtifactHash(proof);
        uint256 originalBatch = _batchEval(proof.witnessIndividualEvals, proof.witnessBatchR);
        proof.witnessIndividualEvals[0] = proof.witnessIndividualEvals[0].add(proof.witnessBatchR);
        proof.witnessIndividualEvals[1] = proof.witnessIndividualEvals[1].sub(1);
        assertEq(_batchEval(proof.witnessIndividualEvals, proof.witnessBatchR), originalBatch);
        _expectPcsReject(proof, vp, whir, gatesDigest, artifacts);
    }

    /// @notice Point 0 / auxiliary: preserve both the legacy auxiliary
    /// decomposition equation and the complete combined terminal. If the
    /// redundant auxEvalValue were also fixed, these two independent equations
    /// have only the zero solution for this proof; the determinant assertion
    /// records that exact mathematical limitation.
    function test_pcs_kernel_matrix_combined_auxiliary_compensation_rejected() public {
        string memory json = vm.readFile("test/fixtures/small_mul.json");
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        bytes32 artifacts = _fixedArtifactHash(proof);
        uint256[] memory tau = _parseKernelArray(json, ".tau");
        uint256[] memory r = _parseKernelEvaluationPoint(json);
        uint256 eqAtR = EqPolyLib.eqEval(tau, r);
        uint256 determinant = proof.mu.sub(eqAtR.mul(proof.auxBatchR));
        assertTrue(determinant != 0, "fixture unexpectedly has fixed-aggregate aux kernel");
        uint256 originalTerminal = eqAtR.mul(proof.auxConstraintEval).add(proof.mu.mul(proof.auxPermEval));
        uint256 originalAuxEval = proof.auxEvalValue;

        proof.auxConstraintEval = proof.auxConstraintEval.add(proof.mu);
        proof.auxPermEval = proof.auxPermEval.sub(eqAtR);
        proof.auxEvalValue = proof.auxConstraintEval.add(proof.auxBatchR.mul(proof.auxPermEval));

        assertEq(eqAtR.mul(proof.auxConstraintEval).add(proof.mu.mul(proof.auxPermEval)), originalTerminal);
        assertTrue(proof.auxEvalValue != originalAuxEval, "nonzero determinant must move aux aggregate");
        _expectPcsReject(proof, vp, whir, gatesDigest, artifacts);
    }

    /// @notice Point 1 / preprocessed: mutate sigma_0, preserve its scalar
    /// batch through constant_0, and preserve Phi_inv through A_1.
    function test_pcs_kernel_matrix_inverse_preprocessed_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        bytes32 artifacts = _fixedArtifactHash(proof);
        uint256 originalBatch = _batchEval(proof.preprocessedIndividualEvalsAtRInv, proof.preprocessedBatchR);
        uint256 originalTerminal = _invInnerModel(proof, vp);
        uint256 sigma0 = vp.numConstants;
        proof.preprocessedIndividualEvalsAtRInv[sigma0] = proof.preprocessedIndividualEvalsAtRInv[sigma0].add(1);
        proof.preprocessedIndividualEvalsAtRInv[0] =
            proof.preprocessedIndividualEvalsAtRInv[0].sub(proof.preprocessedBatchR.modExp(sigma0));
        uint256 afterSigma = _invInnerModel(proof, vp);
        uint256 denomId1 = proof.beta.add(proof.witnessIndividualEvalsAtRInv[1])
            .add(proof.gamma.mul(vp.kIs[1].mul(proof.gSubEvalAtRInv)));
        uint256 coefficient = proof.lambdaInv.mul(denomId1);
        assertTrue(coefficient != 0, "A_1 compensation coefficient");
        proof.inverseHelpersEvalsAtRInv[1] =
            proof.inverseHelpersEvalsAtRInv[1].add(originalTerminal.sub(afterSigma).mul(coefficient.inv()));
        assertEq(_batchEval(proof.preprocessedIndividualEvalsAtRInv, proof.preprocessedBatchR), originalBatch);
        assertEq(_invInnerModel(proof, vp), originalTerminal);
        _expectPcsReject(proof, vp, whir, gatesDigest, artifacts);
    }

    /// @notice Point 1 / inverse helpers: a direct A_0/A_1 kernel of the
    /// complete Phi_inv terminal for this proof's live coefficients.
    function test_pcs_kernel_matrix_inverse_helpers_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        bytes32 artifacts = _fixedArtifactHash(proof);
        uint256 originalTerminal = _invInnerModel(proof, vp);
        proof.inverseHelpersEvalsAtRInv[0] = proof.inverseHelpersEvalsAtRInv[0].add(1);
        uint256 afterA0 = _invInnerModel(proof, vp);
        uint256 denomId1 = proof.beta.add(proof.witnessIndividualEvalsAtRInv[1])
            .add(proof.gamma.mul(vp.kIs[1].mul(proof.gSubEvalAtRInv)));
        uint256 coefficient = proof.lambdaInv.mul(denomId1);
        assertTrue(coefficient != 0, "A_1 compensation coefficient");
        proof.inverseHelpersEvalsAtRInv[1] =
            proof.inverseHelpersEvalsAtRInv[1].add(originalTerminal.sub(afterA0).mul(coefficient.inv()));
        assertEq(_invInnerModel(proof, vp), originalTerminal);
        _expectPcsReject(proof, vp, whir, gatesDigest, artifacts);
    }

    /// @notice Point 3 / preprocessed: sigma_0/sigma_1 form a retained-batch
    /// kernel and are ignored by the gate formula, while still belonging to
    /// the exact packed claim opened by WHIR.
    function test_pcs_kernel_matrix_gate_preprocessed_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        bytes32 artifacts = _fixedArtifactHash(proof);
        uint256 originalBatch = _batchEval(proof.preprocessedIndividualEvalsAtRGateV2, proof.preprocessedBatchR);
        uint256 originalGate = _gateFlat(proof);
        uint256 sigma0 = vp.numConstants;
        proof.preprocessedIndividualEvalsAtRGateV2[sigma0] =
            proof.preprocessedIndividualEvalsAtRGateV2[sigma0].add(proof.preprocessedBatchR);
        proof.preprocessedIndividualEvalsAtRGateV2[sigma0 + 1] =
            proof.preprocessedIndividualEvalsAtRGateV2[sigma0 + 1].sub(1);
        assertEq(_batchEval(proof.preprocessedIndividualEvalsAtRGateV2, proof.preprocessedBatchR), originalBatch);
        assertEq(_gateFlat(proof), originalGate);
        _expectPcsReject(proof, vp, whir, gatesDigest, artifacts);
    }

    /// @notice Point 3 / witness: derive a simultaneous kernel of the live
    /// witness-batch row and gate-terminal row. Wires 15/19/23 are linear
    /// outputs in every small_mul gate family that consumes them, so the field
    /// cross product gives an exact nonzero proof-dependent attack.
    function test_pcs_kernel_matrix_gate_witness_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        bytes32 artifacts = _fixedArtifactHash(proof);
        uint256 originalBatch = _batchEval(proof.witnessIndividualEvalsAtRGateV2, proof.witnessBatchR);
        uint256 originalGate = _gateFlat(proof);
        uint256[3] memory indices = [uint256(15), uint256(19), uint256(23)];
        uint256[3] memory batchCoefficients;
        uint256[3] memory gateCoefficients;
        for (uint256 i = 0; i < indices.length; i++) {
            batchCoefficients[i] = proof.witnessBatchR.modExp(indices[i]);
            proof.witnessIndividualEvalsAtRGateV2[indices[i]] = proof.witnessIndividualEvalsAtRGateV2[indices[i]].add(1);
            gateCoefficients[i] = _gateFlat(proof).sub(originalGate);
            proof.witnessIndividualEvalsAtRGateV2[indices[i]] = proof.witnessIndividualEvalsAtRGateV2[indices[i]].sub(1);
        }
        uint256[3] memory deltas;
        deltas[0] = batchCoefficients[1].mul(gateCoefficients[2]).sub(batchCoefficients[2].mul(gateCoefficients[1]));
        deltas[1] = batchCoefficients[2].mul(gateCoefficients[0]).sub(batchCoefficients[0].mul(gateCoefficients[2]));
        deltas[2] = batchCoefficients[0].mul(gateCoefficients[1]).sub(batchCoefficients[1].mul(gateCoefficients[0]));
        assertTrue(deltas[0] != 0 || deltas[1] != 0 || deltas[2] != 0, "nonzero joint kernel");
        for (uint256 i = 0; i < indices.length; i++) {
            proof.witnessIndividualEvalsAtRGateV2[indices[i]] =
                proof.witnessIndividualEvalsAtRGateV2[indices[i]].add(deltas[i]);
        }
        assertEq(_batchEval(proof.witnessIndividualEvalsAtRGateV2, proof.witnessBatchR), originalBatch);
        assertEq(_gateFlat(proof), originalGate);
        _expectPcsReject(proof, vp, whir, gatesDigest, artifacts);
    }

    function test_protocol_old_version_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        proof.protocolVersion = 0;
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_protocol_wrong_constituent_width_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        proof.constituentWidth--;
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_protocol_new_proof_old_vk_protocol_id_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        vp.protocolId[0] = bytes1(uint8(vp.protocolId[0]) ^ 1);
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_protocol_new_proof_old_vk_session_id_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        vp.sessionId[0] = bytes1(uint8(vp.sessionId[0]) ^ 1);
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_pcs_root_reorder_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        (proof.witnessRoot, proof.auxCommitmentRoot) = (proof.auxCommitmentRoot, proof.witnessRoot);
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice Swap and duplicate canonical constituent values in each of the
    /// four packed groups. Legacy scalar aggregates are recomputed where they
    /// exist, so rejection cannot rely on an array-length or stale-batch check.
    function test_pcs_constituent_reorder_and_duplicate_matrix_rejected() public {
        for (uint256 group = 0; group < 4; group++) {
            for (uint256 duplicate = 0; duplicate < 2; duplicate++) {
                (
                    MleVerifier.MleProof memory proof,
                    MleVerifier.VerifyParams memory vp,
                    SpongefishWhirVerify.WhirParams memory whir,
                    bytes32 gatesDigest
                ) = _loadFixture("test/fixtures/small_mul.json");
                _mutateConstituentOrder(proof, group, duplicate != 0);
                vm.expectRevert(InvalidMleProof.selector);
                verifier.verify(proof, vp, whir, gatesDigest);
            }
        }
    }

    function test_proof_shape_trailing_whir_transcript_is_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        proof.whirTranscript = bytes.concat(proof.whirTranscript, hex"00");
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_proof_shape_trailing_whir_hint_is_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");
        proof.whirHints = bytes.concat(proof.whirHints, hex"00");
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_proof_shape_extra_sumcheck_round_is_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        uint256 oldLength = proof.combinedProof.roundPolys.length;
        SumcheckVerifier.RoundPoly[] memory extended = new SumcheckVerifier.RoundPoly[](oldLength + 1);
        for (uint256 i = 0; i < oldLength; i++) {
            extended[i] = proof.combinedProof.roundPolys[i];
        }
        extended[oldLength] = proof.combinedProof.roundPolys[oldLength - 1];
        proof.combinedProof.roundPolys = extended;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_proof_shape_extra_sumcheck_coefficient_is_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        uint256[] memory oldEvals = proof.gateSumcheckProof.roundPolys[0].evals;
        uint256[] memory extended = new uint256[](oldEvals.length + 1);
        for (uint256 i = 0; i < oldEvals.length; i++) {
            extended[i] = oldEvals[i];
        }
        extended[oldEvals.length] = 0;
        proof.gateSumcheckProof.roundPolys[0].evals = extended;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice Every exact constituent-array schema rejects both a one-entry
    /// truncation and a one-entry extension. This closes consumer-side aliases
    /// beyond the representative empty-array regression below.
    function test_proof_shape_all_constituent_arrays_reject_truncation_and_extension() public {
        for (uint256 field = 0; field < 8; field++) {
            for (uint256 extend = 0; extend < 2; extend++) {
                (
                    MleVerifier.MleProof memory proof,
                    MleVerifier.VerifyParams memory vp,
                    SpongefishWhirVerify.WhirParams memory whir,
                    bytes32 gatesDigest
                ) = _loadFixture("test/fixtures/small_mul.json");
                _resizeConstituentArray(proof, field, extend != 0);
                vm.expectRevert(InvalidMleProof.selector);
                verifier.verify(proof, vp, whir, gatesDigest);
            }
        }
    }

    /// @notice A tailed WHIR round table is stored verifier configuration,
    /// not authenticated proof data. It must fail with InvalidParameters so
    /// the fraud trampoline classifies it UNEVALUABLE rather than slashable.
    function test_config_extra_whir_round_is_not_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        uint256 oldLength = whir.rounds.length;
        SpongefishWhirVerify.RoundParams[] memory extended = new SpongefishWhirVerify.RoundParams[](oldLength + 1);
        for (uint256 i = 0; i < oldLength; i++) {
            extended[i] = whir.rounds[i];
        }
        extended[oldLength] = whir.rounds[oldLength - 1];
        whir.rounds = extended;

        vm.expectRevert(SpongefishWhirVerify.InvalidParameters.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_config_caller_supplied_whir_point_is_not_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        // MleVerifier derives this point from the authenticated sumcheck.
        // A configured value here is an ignored tail, so reject the broken
        // configuration before inspecting proof-dependent data.
        whir.evaluationPoint = new GoldilocksExt3.Ext3[](1);
        vm.expectRevert(bytes("WHIR derived point config"));
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_config_noncanonical_whir_point_is_invalid_parameters() public {
        (MleVerifier.MleProof memory proof,, SpongefishWhirVerify.WhirParams memory whir,) =
            _loadFixture("test/fixtures/small_mul.json");

        uint256 n = whir.numVariables;
        whir.evaluationPoint = new GoldilocksExt3.Ext3[](n);
        whir.evaluationPoint2 = new GoldilocksExt3.Ext3[](n);
        whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](2);
        whir.additionalEvaluationPoints[0] = new GoldilocksExt3.Ext3[](n);
        whir.additionalEvaluationPoints[1] = new GoldilocksExt3.Ext3[](n);
        whir.evaluationPoint[0].c0 = uint64(P);

        GoldilocksExt3.Ext3[] memory evaluations = new GoldilocksExt3.Ext3[](4 * whir.numCommitments * whir.numVectors);
        bytes memory mask = new bytes((evaluations.length + 7) / 8);
        bytes32[] memory roots = new bytes32[](4);
        roots[0] = proof.preprocessedRoot;
        roots[1] = proof.witnessRoot;
        roots[2] = proof.inverseHelpersCommitmentRoot;
        roots[3] = proof.auxCommitmentRoot;

        vm.expectRevert(SpongefishWhirVerify.InvalidParameters.selector);
        SpongefishWhirVerify.verifyWhirProofBound("", "", "", "", "", evaluations, mask, roots, whir);
    }

    function test_chainPin_fraudVerdictIsUnevaluableAfterChainIdChange() public {
        (MleVerifier.MleProof memory proof,,,) = _loadFixture("test/fixtures/small_mul.json");

        vm.chainId(1);
        uint8 verdict =
            verifier.fraudVerdictEncoded(abi.encode(proof), bytes32(0), this._publicChainVerifyCallback.selector);
        assertEq(verdict, 2, "unreleased verifier must be UNEVALUABLE");
    }

    function test_chainPin_malformedFraudInputStaysUnevaluableAfterChainIdChange() public {
        vm.chainId(1);
        assertEq(
            verifier.fraudVerdictEncoded(hex"01", bytes32(0), bytes4(0)),
            2,
            "wrong-chain malformed proof must not become INVALID"
        );
    }

    /// @dev Mirrors the rollup's typed verifier trampoline. Empty verifier
    /// parameters are intentional: after a chain-id change the pin must
    /// fire before any proof- or configuration-dependent access.
    function _publicChainVerifyCallback(MleVerifier.MleProof calldata proof) external view returns (bool) {
        MleVerifier.VerifyParams memory vp;
        SpongefishWhirVerify.WhirParams memory whir;
        return verifier.verify(proof, vp, whir, bytes32(0));
    }

    // ──────────────────────────────────────────────────────────────────
    //  C1 — gatesDigest mismatch must revert
    // ──────────────────────────────────────────────────────────────────

    function test_c1_wrong_gatesDigest_reverts() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 correctDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        // Bump one byte of the expected digest — the pre-verify check must
        // fire before any sumcheck work happens.
        bytes32 wrongDigest = bytes32(uint256(correctDigest) ^ 1);

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, wrongDigest);
    }

    function test_c1_mutated_gates_entry_reverts() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 correctDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        // Mutate gates[0].selectorIndex — simulates the gate-reinterpretation
        // attack. The deployer's digest was computed from the ORIGINAL layout,
        // so the mutated proof.gates produces a different computed digest.
        proof.gates[0].selectorIndex = uint8(uint256(proof.gates[0].selectorIndex) ^ 0xff);

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, correctDigest);
    }

    function test_c1_mutated_numSelectors_reverts() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 correctDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.numSelectors = proof.numSelectors + 1;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, correctDigest);
    }

    function test_c1_mutated_quotientDegreeFactor_reverts() public {
        // A higher-than-real `quotientDegreeFactor` would widen the sumcheck
        // accepting-set. Must be bound by gatesDigest.
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 correctDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.quotientDegreeFactor = proof.quotientDegreeFactor + 1;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, correctDigest);
    }

    function test_vk_digest_binds_circuit_digest() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 correctDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.circuitDigest[0] = proof.circuitDigest[0].add(1);
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, correctDigest);
    }

    function test_vk_digest_binds_public_input_count() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 correctDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        uint256[] memory extended = new uint256[](proof.publicInputs.length + 1);
        for (uint256 i = 0; i < proof.publicInputs.length; i++) {
            extended[i] = proof.publicInputs[i];
        }
        proof.publicInputs = extended;
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, correctDigest);
    }

    // ──────────────────────────────────────────────────────────────────
    //  C2 — non-canonical individual-eval entry must revert
    // ──────────────────────────────────────────────────────────────────

    function test_c2_non_canonical_witness_at_r_gate_v2_reverts() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        // Shift wire[0] by +P (attack representative from phase2_c2_poc_report.md).
        proof.witnessIndividualEvalsAtRGateV2[0] += P;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_c2_non_canonical_preprocessed_at_r_gate_v2_reverts() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.preprocessedIndividualEvalsAtRGateV2[0] += P;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_c2_non_canonical_public_inputs_hash_reverts() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        // publicInputsHash entry >= P
        proof.publicInputsHash[0] = P;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_public_inputs_hash_must_match_poseidon_preimage() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.publicInputsHash[0] = addmod(proof.publicInputsHash[0], 1, P);

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_c2_non_canonical_inverse_helpers_at_r_h_reverts() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.inverseHelpersEvalsAtRH[0] += P;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice Hit every prover-supplied dynamic field-array category consumed
    /// by the assembly-heavy verifier, including circuit digest and PIs.
    function test_c2_all_proof_array_categories_reject_noncanonical_entries() public {
        for (uint256 field = 0; field < 10; field++) {
            (
                MleVerifier.MleProof memory proof,
                MleVerifier.VerifyParams memory vp,
                SpongefishWhirVerify.WhirParams memory whir,
                bytes32 gatesDigest
            ) = _loadFixture("test/fixtures/small_mul.json");
            _setNoncanonicalArrayEntry(proof, field);
            vm.expectRevert(InvalidMleProof.selector);
            verifier.verify(proof, vp, whir, gatesDigest);
        }
    }

    function test_c2_all_sumcheck_categories_reject_noncanonical_entries() public {
        for (uint256 which = 0; which < 4; which++) {
            (
                MleVerifier.MleProof memory proof,
                MleVerifier.VerifyParams memory vp,
                SpongefishWhirVerify.WhirParams memory whir,
                bytes32 gatesDigest
            ) = _loadFixture("test/fixtures/small_mul.json");
            if (which == 0) proof.combinedProof.roundPolys[0].evals[0] = P;
            else if (which == 1) proof.invSumcheckProof.roundPolys[0].evals[0] = P;
            else if (which == 2) proof.hSumcheckProof.roundPolys[0].evals[0] = P;
            else proof.gateSumcheckProof.roundPolys[0].evals[0] = P;
            vm.expectRevert(InvalidMleProof.selector);
            verifier.verify(proof, vp, whir, gatesDigest);
        }
    }

    function test_c2_scalar_categories_reject_noncanonical_entries() public {
        for (uint256 which = 0; which < 4; which++) {
            (
                MleVerifier.MleProof memory proof,
                MleVerifier.VerifyParams memory vp,
                SpongefishWhirVerify.WhirParams memory whir,
                bytes32 gatesDigest
            ) = _loadFixture("test/fixtures/small_mul.json");
            if (which == 0) proof.alpha = P;
            else if (which == 1) proof.auxEvalValue = P;
            else if (which == 2) proof.witnessEvalValueAtRInv = P;
            else proof.preprocessedEvalValueAtRGateV2 = P;
            vm.expectRevert(InvalidMleProof.selector);
            verifier.verify(proof, vp, whir, gatesDigest);
        }
    }

    function test_c2_exactly_P_is_rejected() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        // Exactly P (not P-1) is the boundary case. `requireCanonical` uses
        // strict `< P`, so P itself must revert.
        proof.witnessIndividualEvalsAtRGateV2[0] = P;

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_c2_max_canonical_passes_digest_check() public {
        // Sanity: P-1 in a wire position passes the canonical check, so
        // C2 only rejects NON-canonical reps, not valid large values.
        // (Full verify still fails downstream because we tampered with data,
        // but it must not fail with "canonical".)
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.witnessIndividualEvalsAtRGateV2[0] = P - 1;

        // The canonical check accepts P-1, then a later proof-dependent consistency check rejects
        // the mutation using the common negative-verdict selector.
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice The r_gate_v2 preprocessed vector is prover-controlled while
    /// its exact width comes from the VK.  A short vector used to reach the
    /// evaluator's Solidity array access and revert with Panic(0x32), making
    /// the committed invalid proof look merely unevaluable to IntmaxRollup.
    function test_proof_shape_empty_preprocessed_at_r_gate_v2_is_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        require(vp.numConstants + vp.numRoutedWires != 0, "fixture has zero preprocessed width");
        proof.preprocessedIndividualEvalsAtRGateV2 = new uint256[](0);

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_proof_shape_empty_whir_transcript_is_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.whirTranscript = new bytes(0);

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function test_proof_shape_empty_whir_hints_is_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        proof.whirHints = new bytes(0);

        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    /// @notice A missing VK subgroup-power table is verifier configuration,
    /// not proof fraud.  Keep its revert distinct from InvalidMleProof so the
    /// rollup cannot convict an honest submission under a broken deployment.
    function test_config_short_subgroup_powers_is_not_invalid_proof() public {
        (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        ) = _loadFixture("test/fixtures/small_mul.json");

        vp.subgroupGenPowers = new uint256[](0);

        vm.expectRevert(bytes("subgroup powers len"));
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    // ──────────────────────────────────────────────────────────────────
    //  Authenticated raw-proof verdict trampoline
    // ──────────────────────────────────────────────────────────────────

    function test_encoded_verdict_undecodable_raw_is_invalid() public {
        uint8 verdict = verifier.fraudVerdictEncoded(hex"deadbeef", bytes32(0), bytes4(0));
        assertEq(verdict, 0, "undecodable authenticated bytes verdict");
    }

    function test_legacyVerifierHasNoVerificationBypassSelector() public {
        (bool ok,) = address(verifier).staticcall(
            abi.encodeWithSignature(
                "fraudVerdictEncoded(bytes,bytes32,bytes4,bool)", hex"", bytes32(0), bytes4(0), true
            )
        );
        assertFalse(ok, "legacy verifier bypass selector remains callable");
    }

    function test_encoded_verdict_canonical_legacyV0Abi_is_invalid() public {
        (MleVerifier.MleProof memory proof,,,) = _loadFixture("test/fixtures/small_mul.json");
        LegacyV0MleProof memory legacy = _asLegacyV0Proof(proof);
        bytes memory rawProof = abi.encode(legacy);

        // The bytes are canonical under the exact retired schema. This is not
        // an arbitrary malformed blob and not a current proof with a changed
        // version word.
        LegacyV0MleProof memory roundTrip = abi.decode(rawProof, (LegacyV0MleProof));
        assertEq(keccak256(abi.encode(roundTrip)), keccak256(rawProof), "noncanonical v0 test vector");

        // In v1 the old preprocessedRoot word occupies the whirTranscript
        // offset slot. The real root-sized word is out of bounds, so the
        // current ABI decoder must reject this canonical v0 encoding.
        assertGt(uint256(legacy.preprocessedRoot), rawProof.length, "v0 root must be an invalid v1 ABI offset");
        (bool decoded,) = address(verifier).staticcall(abi.encodeCall(MleVerifier.decodeCanonicalMleProof, (rawProof)));
        assertFalse(decoded, "canonical v0 proof bytes decoded as v1");

        uint8 verdict = verifier.fraudVerdictEncoded(rawProof, bytes32(0), bytes4(0));
        assertEq(verdict, 0, "canonical v0 proof bytes must be INVALID under v1");
    }

    function test_encoded_verdict_noncanonical_abi_is_invalid() public {
        (MleVerifier.MleProof memory proof,,,) = _loadFixture("test/fixtures/small_mul.json");
        bytes memory noncanonical = bytes.concat(abi.encode(proof), bytes32(0));

        uint8 verdict = verifier.fraudVerdictEncoded(noncanonical, bytes32(0), bytes4(0));
        assertEq(verdict, 0, "trailing ABI bytes verdict");
    }

    function test_encoded_verdict_whir_parameter_error_is_unevaluable() public {
        (MleVerifier.MleProof memory proof,,,) = _loadFixture("test/fixtures/small_mul.json");
        uint8 verdict =
            verifier.fraudVerdictEncoded(abi.encode(proof), bytes32(0), this._whirParameterErrorCallback.selector);
        assertEq(verdict, 2, "WHIR configuration error must not be slashable INVALID");
    }

    function _whirParameterErrorCallback(MleVerifier.MleProof calldata) external pure returns (bool) {
        revert SpongefishWhirVerify.InvalidParameters();
    }

    function test_encoded_verdict_pi_mismatch_is_failed_precondition() public {
        (MleVerifier.MleProof memory proof,,,) = _loadFixture("test/fixtures/small_mul.json");

        // This accepting callback exists only in test bytecode and isolates the post-verification
        // PI classification branch. Production verifier bytecode has no verification bypass.
        uint8 verdict = verifier.fraudVerdictEncoded(
            abi.encode(proof), bytes32(0), this._acceptProofForPiClassificationTest.selector
        );
        assertEq(verdict, 4, "PI mismatch must not be fraud");
    }

    function _acceptProofForPiClassificationTest(MleVerifier.MleProof calldata) external view returns (bool) {
        require(msg.sender == address(verifier), "test callback caller");
        return true;
    }

    // ──────────────────────────────────────────────────────────────────
    //  Fixture loader — thin shim around MleE2ETest's parsing.
    // ──────────────────────────────────────────────────────────────────
    //
    // We re-implement a minimal loader here rather than importing the large
    // MleE2ETest parser; only the fields we mutate in these tests matter.
    // The digest is computed consistently with MleE2ETest._runE2E.

    function _asLegacyV0Proof(MleVerifier.MleProof memory proof)
        internal
        pure
        returns (LegacyV0MleProof memory legacy)
    {
        legacy.circuitDigest = proof.circuitDigest;
        legacy.whirTranscript = proof.whirTranscript;
        legacy.whirHints = proof.whirHints;
        legacy.preprocessedRoot = proof.preprocessedRoot;
        legacy.witnessRoot = proof.witnessRoot;
        legacy.auxCommitmentRoot = proof.auxCommitmentRoot;
        legacy.preprocessedEvalValue = proof.preprocessedEvalValue;
        legacy.preprocessedBatchR = proof.preprocessedBatchR;
        legacy.preprocessedIndividualEvals = proof.preprocessedIndividualEvals;
        legacy.witnessEvalValue = proof.witnessEvalValue;
        legacy.witnessBatchR = proof.witnessBatchR;
        legacy.witnessIndividualEvals = proof.witnessIndividualEvals;
        legacy.auxBatchR = proof.auxBatchR;
        legacy.auxConstraintEval = proof.auxConstraintEval;
        legacy.auxPermEval = proof.auxPermEval;
        legacy.auxEvalValue = proof.auxEvalValue;
        legacy.combinedProof = proof.combinedProof;
        legacy.publicInputs = proof.publicInputs;
        legacy.alpha = proof.alpha;
        legacy.beta = proof.beta;
        legacy.gamma = proof.gamma;
        legacy.mu = proof.mu;
        legacy.preprocessedWhirEval = _legacyExt3(proof.preprocessedEvalValue);
        legacy.witnessWhirEval = _legacyExt3(proof.witnessEvalValue);
        legacy.auxWhirEval = _legacyExt3(proof.auxEvalValue);
        legacy.inverseHelpersCommitmentRoot = proof.inverseHelpersCommitmentRoot;
        legacy.inverseHelpersBatchR = proof.inverseHelpersBatchR;
        legacy.invSumcheckProof = proof.invSumcheckProof;
        legacy.hSumcheckProof = proof.hSumcheckProof;
        legacy.lambdaInv = proof.lambdaInv;
        legacy.muInv = proof.muInv;
        legacy.lambdaH = proof.lambdaInv;
        legacy.witnessIndividualEvalsAtRInv = proof.witnessIndividualEvalsAtRInv;
        legacy.preprocessedIndividualEvalsAtRInv = proof.preprocessedIndividualEvalsAtRInv;
        legacy.inverseHelpersEvalsAtRInv = proof.inverseHelpersEvalsAtRInv;
        legacy.inverseHelpersEvalsAtRH = proof.inverseHelpersEvalsAtRH;
        legacy.gSubEvalAtRInv = proof.gSubEvalAtRInv;
        legacy.witnessEvalValueAtRInv = proof.witnessEvalValueAtRInv;
        legacy.preprocessedEvalValueAtRInv = proof.preprocessedEvalValueAtRInv;
        legacy.inverseHelpersWhirEvalAtRGate = _legacyExt3(proof.inverseHelpersBatchR);
        legacy.preprocessedWhirEvalAtRInv = _legacyExt3(proof.preprocessedEvalValueAtRInv);
        legacy.witnessWhirEvalAtRInv = _legacyExt3(proof.witnessEvalValueAtRInv);
        legacy.auxWhirEvalAtRInv = _legacyExt3(proof.auxEvalValue);
        legacy.inverseHelpersWhirEvalAtRInv = _legacyExt3(proof.inverseHelpersBatchR);
        legacy.preprocessedWhirEvalAtRH = _legacyExt3(proof.preprocessedEvalValue);
        legacy.witnessWhirEvalAtRH = _legacyExt3(proof.witnessEvalValue);
        legacy.auxWhirEvalAtRH = _legacyExt3(proof.auxEvalValue);
        legacy.inverseHelpersWhirEvalAtRH = _legacyExt3(proof.inverseHelpersBatchR);
        legacy.extChallenge = proof.extChallenge;
        legacy.gateSumcheckProof = proof.gateSumcheckProof;
        legacy.witnessIndividualEvalsAtRGateV2 = proof.witnessIndividualEvalsAtRGateV2;
        legacy.preprocessedIndividualEvalsAtRGateV2 = proof.preprocessedIndividualEvalsAtRGateV2;
        legacy.witnessEvalValueAtRGateV2 = proof.witnessEvalValueAtRGateV2;
        legacy.preprocessedEvalValueAtRGateV2 = proof.preprocessedEvalValueAtRGateV2;
        legacy.preprocessedWhirEvalAtRGateV2 = _legacyExt3(proof.preprocessedEvalValueAtRGateV2);
        legacy.witnessWhirEvalAtRGateV2 = _legacyExt3(proof.witnessEvalValueAtRGateV2);
        legacy.auxWhirEvalAtRGateV2 = _legacyExt3(proof.auxEvalValue);
        legacy.inverseHelpersWhirEvalAtRGateV2 = _legacyExt3(proof.inverseHelpersBatchR);
        legacy.quotientDegreeFactor = proof.quotientDegreeFactor;
        legacy.numSelectors = proof.numSelectors;
        legacy.numGateConstraints = proof.numGateConstraints;
        legacy.gates = proof.gates;
        legacy.publicInputsHash = proof.publicInputsHash;
    }

    function _legacyExt3(uint256 c0) internal pure returns (GoldilocksExt3.Ext3 memory) {
        return GoldilocksExt3.Ext3({c0: uint64(c0), c1: 1, c2: 2});
    }

    function _mutateConstituentOrder(MleVerifier.MleProof memory proof, uint256 group, bool duplicate) internal pure {
        if (group == 3) {
            if (duplicate) {
                proof.auxPermEval = proof.auxConstraintEval;
            } else {
                (proof.auxConstraintEval, proof.auxPermEval) = (proof.auxPermEval, proof.auxConstraintEval);
            }
            proof.auxEvalValue = proof.auxConstraintEval.add(proof.auxBatchR.mul(proof.auxPermEval));
            return;
        }

        uint256[] memory values;
        if (group == 0) values = proof.preprocessedIndividualEvals;
        else if (group == 1) values = proof.witnessIndividualEvals;
        else values = proof.inverseHelpersEvalsAtRInv;
        require(values.length > 1, "constituent reorder fixture width");
        if (duplicate) values[1] = values[0];
        else (values[0], values[1]) = (values[1], values[0]);

        if (group == 0) {
            proof.preprocessedEvalValue = _batchEval(values, proof.preprocessedBatchR);
        } else if (group == 1) {
            proof.witnessEvalValue = _batchEval(values, proof.witnessBatchR);
        }
    }

    function _resizeConstituentArray(MleVerifier.MleProof memory proof, uint256 field, bool extend) internal pure {
        uint256[] memory source;
        if (field == 0) source = proof.preprocessedIndividualEvals;
        else if (field == 1) source = proof.witnessIndividualEvals;
        else if (field == 2) source = proof.preprocessedIndividualEvalsAtRInv;
        else if (field == 3) source = proof.witnessIndividualEvalsAtRInv;
        else if (field == 4) source = proof.inverseHelpersEvalsAtRInv;
        else if (field == 5) source = proof.inverseHelpersEvalsAtRH;
        else if (field == 6) source = proof.preprocessedIndividualEvalsAtRGateV2;
        else source = proof.witnessIndividualEvalsAtRGateV2;
        require(source.length > 0, "constituent shape fixture");

        uint256 newLength = extend ? source.length + 1 : source.length - 1;
        uint256[] memory changed = new uint256[](newLength);
        uint256 copied = source.length < newLength ? source.length : newLength;
        for (uint256 i = 0; i < copied; i++) {
            changed[i] = source[i];
        }
        if (extend) changed[newLength - 1] = source[0];

        if (field == 0) proof.preprocessedIndividualEvals = changed;
        else if (field == 1) proof.witnessIndividualEvals = changed;
        else if (field == 2) proof.preprocessedIndividualEvalsAtRInv = changed;
        else if (field == 3) proof.witnessIndividualEvalsAtRInv = changed;
        else if (field == 4) proof.inverseHelpersEvalsAtRInv = changed;
        else if (field == 5) proof.inverseHelpersEvalsAtRH = changed;
        else if (field == 6) proof.preprocessedIndividualEvalsAtRGateV2 = changed;
        else proof.witnessIndividualEvalsAtRGateV2 = changed;
    }

    function _setNoncanonicalArrayEntry(MleVerifier.MleProof memory proof, uint256 field) internal pure {
        if (field == 0) proof.preprocessedIndividualEvals[0] = P;
        else if (field == 1) proof.witnessIndividualEvals[0] = P;
        else if (field == 2) proof.preprocessedIndividualEvalsAtRInv[0] = P;
        else if (field == 3) proof.witnessIndividualEvalsAtRInv[0] = P;
        else if (field == 4) proof.inverseHelpersEvalsAtRInv[0] = P;
        else if (field == 5) proof.inverseHelpersEvalsAtRH[0] = P;
        else if (field == 6) proof.preprocessedIndividualEvalsAtRGateV2[0] = P;
        else if (field == 7) proof.witnessIndividualEvalsAtRGateV2[0] = P;
        else if (field == 8) proof.circuitDigest[0] = P;
        else proof.publicInputs[0] = P;
    }

    function _fixedArtifactHash(MleVerifier.MleProof memory proof) internal pure returns (bytes32 digest) {
        digest = keccak256(abi.encode(proof.whirTranscript, proof.whirHints));
        digest = keccak256(
            abi.encode(
                digest, proof.protocolVersion, proof.constituentWidth, keccak256(abi.encode(proof.circuitDigest))
            )
        );
        digest = keccak256(
            abi.encode(
                digest,
                proof.preprocessedRoot,
                proof.witnessRoot,
                proof.inverseHelpersCommitmentRoot,
                proof.auxCommitmentRoot
            )
        );
        digest = keccak256(
            abi.encode(
                digest,
                keccak256(abi.encode(proof.combinedProof)),
                keccak256(abi.encode(proof.invSumcheckProof)),
                keccak256(abi.encode(proof.hSumcheckProof)),
                keccak256(abi.encode(proof.gateSumcheckProof))
            )
        );
        digest = keccak256(abi.encode(digest, keccak256(abi.encode(proof.publicInputs)), proof.publicInputsHash));
    }

    function _expectPcsReject(
        MleVerifier.MleProof memory proof,
        MleVerifier.VerifyParams memory vp,
        SpongefishWhirVerify.WhirParams memory whir,
        bytes32 gatesDigest,
        bytes32 expectedArtifacts
    ) internal {
        assertEq(block.chainid, verifier.allowedChainId(), "kernel test must use allowed chain");
        assertEq(_fixedArtifactHash(proof), expectedArtifacts, "authenticated artifact changed");
        vm.expectRevert(InvalidMleProof.selector);
        verifier.verify(proof, vp, whir, gatesDigest);
    }

    function _gateFlat(MleVerifier.MleProof memory proof) internal pure returns (uint256) {
        return Plonky2GateEvaluator.evalCombinedFlat(
            proof.witnessIndividualEvalsAtRGateV2,
            proof.preprocessedIndividualEvalsAtRGateV2,
            proof.alpha,
            proof.extChallenge,
            proof.publicInputsHash,
            proof.gates,
            proof.numSelectors,
            0,
            proof.numGateConstraints
        );
    }

    function _parseKernelArray(string memory json, string memory path) internal pure returns (uint256[] memory result) {
        string[] memory values = vm.parseJsonStringArray(json, path);
        result = new uint256[](values.length);
        for (uint256 i = 0; i < values.length; i++) {
            result[i] = vm.parseUint(values[i]);
            require(result[i] < P, "kernel fixture field");
        }
    }

    function _parseKernelEvaluationPoint(string memory json) internal pure returns (uint256[] memory result) {
        uint256 degreeBits = vm.parseJsonUint(json, ".degreeBits");
        result = new uint256[](degreeBits);
        for (uint256 i = 0; i < degreeBits; i++) {
            string memory path = string.concat(".evaluationPoint[", vm.toString(i), "].c0");
            result[i] = vm.parseUint(vm.parseJsonString(json, path));
            require(result[i] < P, "kernel fixture point field");
        }
    }

    function _batchEval(uint256[] memory values, uint256 rho) internal pure returns (uint256 acc) {
        uint256 power = 1;
        for (uint256 i = 0; i < values.length; i++) {
            acc = acc.add(power.mul(values[i]));
            power = power.mul(rho);
        }
    }

    function _invInnerModel(MleVerifier.MleProof memory proof, MleVerifier.VerifyParams memory vp)
        internal
        pure
        returns (uint256 acc)
    {
        uint256 nr = vp.numRoutedWires;
        uint256 lambdaPower = 1;
        for (uint256 j = 0; j < nr; j++) {
            uint256 betaPlusWire = proof.beta.add(proof.witnessIndividualEvalsAtRInv[j]);
            uint256 idJ = vp.kIs[j].mul(proof.gSubEvalAtRInv);
            uint256 denomId = betaPlusWire.add(proof.gamma.mul(idJ));
            uint256 sigma = proof.preprocessedIndividualEvalsAtRInv[vp.numConstants + j];
            uint256 denomSigma = betaPlusWire.add(proof.gamma.mul(sigma));
            uint256 zId = proof.inverseHelpersEvalsAtRInv[j].mul(denomId).sub(1);
            uint256 zSigma = proof.inverseHelpersEvalsAtRInv[nr + j].mul(denomSigma).sub(1);
            acc = acc.add(lambdaPower.mul(zId.add(proof.muInv.mul(zSigma))));
            lambdaPower = lambdaPower.mul(proof.lambdaInv);
        }
    }

    function _hInnerModel(MleVerifier.MleProof memory proof) internal pure returns (uint256 acc) {
        uint256 nr = proof.inverseHelpersEvalsAtRH.length / 2;
        for (uint256 j = 0; j < nr; j++) {
            acc = acc.add(proof.inverseHelpersEvalsAtRH[j].sub(proof.inverseHelpersEvalsAtRH[nr + j]));
        }
    }

    function _loadFixture(string memory path)
        internal
        returns (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir,
            bytes32 gatesDigest
        )
    {
        string memory json = vm.readFile(path);
        MleE2ETestShim shim = new MleE2ETestShim();
        (proof, vp, whir) = shim.parseAll(json);

        gatesDigest = verifier.computeGatesDigest(
            proof.gates,
            proof.circuitDigest,
            proof.publicInputs.length,
            proof.witnessIndividualEvalsAtRGateV2.length,
            proof.numSelectors,
            proof.numGateConstraints,
            proof.quotientDegreeFactor
        );
    }
}

/// @dev Thin wrapper that exposes MleE2ETest's internal parsing helpers.
/// Kept separate so BoundaryCheckTest doesn't need to inherit the whole
/// MleE2ETest contract (which would pull all of its tests into this suite).
contract MleE2ETestShim is Test {
    function parseAll(string memory json)
        external
        view
        returns (
            MleVerifier.MleProof memory proof,
            MleVerifier.VerifyParams memory vp,
            SpongefishWhirVerify.WhirParams memory whir
        )
    {
        // Intentionally re-implement the minimal slice needed — any code
        // drift in MleE2ETest parser would otherwise silently break tests.
        proof.protocolVersion = vm.parseJsonUint(json, ".protocolVersion");
        proof.constituentWidth = vm.parseJsonUint(json, ".constituentWidth");
        proof.circuitDigest = _parseUintArray(json, ".circuitDigest");
        proof.whirTranscript = vm.parseJsonBytes(json, ".whirTranscript");
        proof.whirHints = vm.parseJsonBytes(json, ".whirHints");
        proof.preprocessedRoot = vm.parseJsonBytes32(json, ".preprocessedCommitmentRoot");
        proof.witnessRoot = vm.parseJsonBytes32(json, ".witnessCommitmentRoot");
        proof.preprocessedEvalValue = vm.parseUint(vm.parseJsonString(json, ".preprocessedEvalValue"));
        proof.preprocessedBatchR = vm.parseUint(vm.parseJsonString(json, ".preprocessedBatchR"));
        proof.preprocessedIndividualEvals = _parseUintArray(json, ".preprocessedIndividualEvals");
        proof.witnessEvalValue = vm.parseUint(vm.parseJsonString(json, ".witnessEvalValue"));
        proof.witnessBatchR = vm.parseUint(vm.parseJsonString(json, ".witnessBatchR"));
        proof.witnessIndividualEvals = _parseUintArray(json, ".witnessIndividualEvals");
        proof.auxCommitmentRoot = vm.parseJsonBytes32(json, ".auxCommitmentRoot");
        proof.auxBatchR = vm.parseUint(vm.parseJsonString(json, ".auxBatchR"));
        proof.auxConstraintEval = vm.parseUint(vm.parseJsonString(json, ".auxConstraintEval"));
        proof.auxPermEval = vm.parseUint(vm.parseJsonString(json, ".auxPermEval"));
        proof.auxEvalValue = vm.parseUint(vm.parseJsonString(json, ".auxEvalValue"));

        uint256 degreeBits = vm.parseJsonUint(json, ".degreeBits");
        proof.combinedProof = _parseSumcheckProof(json, ".combinedProof", degreeBits);
        proof.alpha = vm.parseUint(vm.parseJsonString(json, ".alpha"));
        proof.beta = vm.parseUint(vm.parseJsonString(json, ".beta"));
        proof.gamma = vm.parseUint(vm.parseJsonString(json, ".gamma"));
        proof.mu = vm.parseUint(vm.parseJsonString(json, ".mu"));
        proof.publicInputs = _parseUintArray(json, ".publicInputs");

        _parseV2(json, proof, degreeBits);
        _parseGates(json, proof, degreeBits);

        vp.degreeBits = degreeBits;
        vp.preprocessedCommitmentRoot = proof.preprocessedRoot;
        vp.numConstants = vm.parseJsonUint(json, ".numConstants");
        vp.numRoutedWires = vm.parseJsonUint(json, ".numRoutedWires");
        vp.protocolId = vm.parseJsonBytes(json, ".whirProtocolId");
        vp.sessionId = vm.parseJsonBytes(json, ".whirSplitSessionId");
        vp.kIs = _parseUintArray(json, ".kIs");
        vp.subgroupGenPowers = _parseUintArray(json, ".subgroupGenPowers");

        whir = _parseWhir(json, ".whirParams");
    }

    function _parseV2(string memory json, MleVerifier.MleProof memory proof, uint256 degreeBits) internal pure {
        proof.inverseHelpersCommitmentRoot = vm.parseJsonBytes32(json, ".inverseHelpersCommitmentRoot");
        proof.inverseHelpersBatchR = vm.parseUint(vm.parseJsonString(json, ".inverseHelpersBatchR"));
        proof.invSumcheckProof = _parseSumcheckProof(json, ".invSumcheckProof", degreeBits);
        proof.hSumcheckProof = _parseSumcheckProof(json, ".hSumcheckProof", degreeBits);
        proof.lambdaInv = vm.parseUint(vm.parseJsonString(json, ".lambdaInv"));
        proof.muInv = vm.parseUint(vm.parseJsonString(json, ".muInv"));
        proof.witnessIndividualEvalsAtRInv = _parseUintArray(json, ".witnessIndividualEvalsAtRInv");
        proof.preprocessedIndividualEvalsAtRInv = _parseUintArray(json, ".preprocessedIndividualEvalsAtRInv");
        proof.inverseHelpersEvalsAtRInv = _parseUintArray(json, ".inverseHelpersEvalsAtRInv");
        proof.inverseHelpersEvalsAtRH = _parseUintArray(json, ".inverseHelpersEvalsAtRH");
        proof.gSubEvalAtRInv = vm.parseUint(vm.parseJsonString(json, ".gSubEvalAtRInv"));
        proof.witnessEvalValueAtRInv = vm.parseUint(vm.parseJsonString(json, ".witnessEvalValueAtRInv"));
        proof.preprocessedEvalValueAtRInv = vm.parseUint(vm.parseJsonString(json, ".preprocessedEvalValueAtRInv"));
    }

    function _parseGates(string memory json, MleVerifier.MleProof memory proof, uint256 degreeBits) internal pure {
        proof.extChallenge = vm.parseUint(vm.parseJsonString(json, ".extChallenge"));
        proof.gateSumcheckProof = _parseSumcheckProof(json, ".gateSumcheckProof", degreeBits);
        proof.witnessIndividualEvalsAtRGateV2 = _parseUintArray(json, ".witnessIndividualEvalsAtRGateV2");
        proof.preprocessedIndividualEvalsAtRGateV2 = _parseUintArray(json, ".preprocessedIndividualEvalsAtRGateV2");
        proof.witnessEvalValueAtRGateV2 = vm.parseUint(vm.parseJsonString(json, ".witnessEvalValueAtRGateV2"));
        proof.preprocessedEvalValueAtRGateV2 = vm.parseUint(vm.parseJsonString(json, ".preprocessedEvalValueAtRGateV2"));
        proof.quotientDegreeFactor = vm.parseJsonUint(json, ".quotientDegreeFactor");
        proof.numSelectors = vm.parseJsonUint(json, ".numSelectors");
        proof.numGateConstraints = vm.parseJsonUint(json, ".numGateConstraints");

        uint256 nGates = 0;
        for (uint256 i = 0; i < 32; i++) {
            try vm.parseJsonUint(json, string.concat(".gates[", vm.toString(i), "].gateId")) returns (uint256) {
                nGates = i + 1;
            } catch {
                break;
            }
        }
        proof.gates = new Plonky2GateEvaluator.GateInfo[](nGates);
        for (uint256 i = 0; i < nGates; i++) {
            string memory p = string.concat(".gates[", vm.toString(i), "]");
            proof.gates[i] = Plonky2GateEvaluator.GateInfo({
                gateId: uint8(vm.parseJsonUint(json, string.concat(p, ".gateId"))),
                selectorIndex: uint8(vm.parseJsonUint(json, string.concat(p, ".selectorIndex"))),
                groupStart: uint8(vm.parseJsonUint(json, string.concat(p, ".groupStart"))),
                groupEnd: uint8(vm.parseJsonUint(json, string.concat(p, ".groupEnd"))),
                gateRowIndex: uint8(vm.parseJsonUint(json, string.concat(p, ".gateRowIndex"))),
                numConstraints: uint16(vm.parseJsonUint(json, string.concat(p, ".numConstraints"))),
                numOrConsts: uint16(vm.parseJsonUint(json, string.concat(p, ".numOrConsts"))),
                param2: uint16(vm.parseJsonUint(json, string.concat(p, ".param2"))),
                param3: uint16(vm.parseJsonUint(json, string.concat(p, ".param3")))
            });
        }

        try vm.parseJsonStringArray(json, ".publicInputsHash") returns (string[] memory hs) {
            require(hs.length == 4, "fixture: publicInputsHash length");
            for (uint256 i = 0; i < 4; i++) {
                proof.publicInputsHash[i] = vm.parseUint(hs[i]);
            }
        } catch {
            revert("fixture: publicInputsHash missing");
        }
    }

    function _parseSumcheckProof(string memory json, string memory path, uint256 n)
        internal
        pure
        returns (SumcheckVerifier.SumcheckProof memory p)
    {
        p.roundPolys = new SumcheckVerifier.RoundPoly[](n);
        for (uint256 i = 0; i < n; i++) {
            string[] memory strs =
                vm.parseJsonStringArray(json, string.concat(path, ".roundPolys[", vm.toString(i), "]"));
            uint256[] memory e = new uint256[](strs.length);
            for (uint256 j = 0; j < strs.length; j++) {
                e[j] = vm.parseUint(strs[j]);
            }
            p.roundPolys[i].evals = e;
        }
    }

    function _parseUintArray(string memory json, string memory path) internal pure returns (uint256[] memory) {
        string[] memory strs = vm.parseJsonStringArray(json, path);
        uint256[] memory result = new uint256[](strs.length);
        for (uint256 i = 0; i < strs.length; i++) {
            result[i] = vm.parseUint(strs[i]);
        }
        return result;
    }

    function _parseWhir(string memory json, string memory bp)
        internal
        pure
        returns (SpongefishWhirVerify.WhirParams memory w)
    {
        w.numVariables = vm.parseJsonUint(json, string.concat(bp, ".numVariables"));
        w.foldingFactor = vm.parseJsonUint(json, string.concat(bp, ".foldingFactor"));
        w.numVectors = vm.parseJsonUint(json, string.concat(bp, ".numVectors"));
        w.numCommitments = vm.parseJsonUint(json, string.concat(bp, ".numCommitments"));
        w.outDomainSamples = vm.parseJsonUint(json, string.concat(bp, ".outDomainSamples"));
        w.inDomainSamples = vm.parseJsonUint(json, string.concat(bp, ".inDomainSamples"));
        w.initialSumcheckRounds = vm.parseJsonUint(json, string.concat(bp, ".initialSumcheckRounds"));
        w.numRounds = vm.parseJsonUint(json, string.concat(bp, ".numRounds"));
        w.finalSumcheckRounds = vm.parseJsonUint(json, string.concat(bp, ".finalSumcheckRounds"));
        w.finalSize = vm.parseJsonUint(json, string.concat(bp, ".finalSize"));
        w.initialCodewordLength = vm.parseJsonUint(json, string.concat(bp, ".initialCodewordLength"));
        w.initialMerkleDepth = vm.parseJsonUint(json, string.concat(bp, ".initialMerkleDepth"));
        w.initialDomainGenerator =
            uint64(vm.parseUint(vm.parseJsonString(json, string.concat(bp, ".initialDomainGenerator"))));
        w.initialInterleavingDepth = vm.parseJsonUint(json, string.concat(bp, ".initialInterleavingDepth"));
        w.initialNumVariables = vm.parseJsonUint(json, string.concat(bp, ".initialNumVariables"));
        w.initialCosetSize = vm.parseJsonUint(json, string.concat(bp, ".initialCosetSize"));
        w.initialNumCosets = vm.parseJsonUint(json, string.concat(bp, ".initialNumCosets"));
        w.initialSumcheckPowThreshold =
            uint64(vm.parseUint(vm.parseJsonString(json, string.concat(bp, ".initialSumcheckPowThreshold"))));
        w.finalPowThreshold = uint64(vm.parseUint(vm.parseJsonString(json, string.concat(bp, ".finalPowThreshold"))));
        w.finalSumcheckPowThreshold =
            uint64(vm.parseUint(vm.parseJsonString(json, string.concat(bp, ".finalSumcheckPowThreshold"))));

        uint256 nr = w.numRounds;
        w.rounds = new SpongefishWhirVerify.RoundParams[](nr);
        for (uint256 i = 0; i < nr; i++) {
            string memory rp = string.concat(bp, ".rounds[", vm.toString(i), "]");
            w.rounds[i].codewordLength = vm.parseJsonUint(json, string.concat(rp, ".codewordLength"));
            w.rounds[i].merkleDepth = vm.parseJsonUint(json, string.concat(rp, ".merkleDepth"));
            w.rounds[i].domainGenerator =
                uint64(vm.parseUint(vm.parseJsonString(json, string.concat(rp, ".domainGenerator"))));
            w.rounds[i].inDomainSamples = vm.parseJsonUint(json, string.concat(rp, ".inDomainSamples"));
            w.rounds[i].outDomainSamples = vm.parseJsonUint(json, string.concat(rp, ".outDomainSamples"));
            w.rounds[i].sumcheckRounds = vm.parseJsonUint(json, string.concat(rp, ".sumcheckRounds"));
            w.rounds[i].interleavingDepth = vm.parseJsonUint(json, string.concat(rp, ".interleavingDepth"));
            w.rounds[i].cosetSize = vm.parseJsonUint(json, string.concat(rp, ".cosetSize"));
            w.rounds[i].numCosets = vm.parseJsonUint(json, string.concat(rp, ".numCosets"));
            w.rounds[i].numVariables = vm.parseJsonUint(json, string.concat(rp, ".numVariables"));
            w.rounds[i].powThreshold =
                uint64(vm.parseUint(vm.parseJsonString(json, string.concat(rp, ".powThreshold"))));
            w.rounds[i].sumcheckPowThreshold =
                uint64(vm.parseUint(vm.parseJsonString(json, string.concat(rp, ".sumcheckPowThreshold"))));
        }
        w.evaluationPoint = new GoldilocksExt3.Ext3[](0);
        w.evaluationPoint2 = new GoldilocksExt3.Ext3[](0);
    }
}
