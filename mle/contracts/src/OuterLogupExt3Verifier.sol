// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {InvalidMleProof} from "./MleProofErrors.sol";
import {TranscriptV2} from "./TranscriptV2.sol";
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {
    BASE_FIELD_MODULUS_V2,
    LOG_ROUND_DEGREE_V2,
    MAX_CONSTITUENT_WIDTH_V2,
    MAX_GATE_ROUND_DEGREE_V2,
    MAX_ROUTED_WIRES_V2,
    MAX_ROW_VARIABLES_V2
} from "./generated/MleWhirV2.sol";

/// @title OuterLogupExt3Verifier
/// @notice Coupled Ext3 sumchecks and formal norm/logUp terminal for MLE wire v3.
/// @dev The public functions deliberately form an external-library boundary: a future
///      production verifier can link this bulk implementation without consuming its own
///      EIP-170 bytecode budget. The terminal uses formal coordinate polynomials at the
///      off-cube Ext3 point. It never takes an actual Ext3 inverse there.
library OuterLogupExt3Verifier {
    uint256 internal constant P = BASE_FIELD_MODULUS_V2;
    uint64 private constant INV_TWO = uint64((BASE_FIELD_MODULUS_V2 + 1) / 2);
    uint256 internal constant MAX_DEGREE = LOG_ROUND_DEGREE_V2;
    uint256 internal constant MAX_ROW_VARIABLES = MAX_ROW_VARIABLES_V2;
    uint256 internal constant MAX_GATE_DEGREE = MAX_GATE_ROUND_DEGREE_V2;
    uint256 internal constant MAX_ROUTED_WIRES = MAX_ROUTED_WIRES_V2;
    uint256 internal constant MAX_CONSTITUENT_WIDTH = MAX_CONSTITUENT_WIDTH_V2;

    struct CoefficientRound {
        /// @dev Monomial coefficients `[a1, a2, a3, a4, a5]` in this exact order.
        GoldilocksExt3.Ext3[] nonConstant;
    }

    struct SumcheckProof {
        CoefficientRound[] rounds;
    }

    /// @dev All fields are verifier-derived Fiat--Shamir values, never proof echoes.
    struct Challenges {
        GoldilocksExt3.Ext3 beta;
        GoldilocksExt3.Ext3 gamma;
        GoldilocksExt3.Ext3 lambda;
        GoldilocksExt3.Ext3 rho;
        GoldilocksExt3.Ext3 kappa;
        GoldilocksExt3.Ext3 eta;
        GoldilocksExt3.Ext3 xi;
        GoldilocksExt3.Ext3[] tau;
    }

    struct VerificationKey {
        uint256 numVars;
        /// @dev Must be the canonical circuit's `quotient_degree_factor + 2`.
        uint256 gateDegree;
        uint256 numConstants;
        uint256 numRoutedWires;
        uint256 numWires;
        uint256[] kIs;
        uint256[] subgroupGenPowers;
        /// @dev Ordered `row_u16_le || routed_column_u8`, exactly 3 bytes/PI.
        bytes publicInputWireMap;
    }

    /// @dev Ordered PCS-bound constituent evaluations at the Ext3 logUp point.
    struct TerminalEvaluations {
        /// `[constants..., sigma_0, ..., sigma_(numRoutedWires-1)]`.
        GoldilocksExt3.Ext3[] preprocessed;
        /// All witness-wire constituents, not only the routed prefix.
        GoldilocksExt3.Ext3[] witness;
        /// `[T_id,0.., T_id,m-1, T_sigma,0.., T_sigma,m-1]`.
        GoldilocksExt3.Ext3[] normInverse;
        /// Raw statement PIs, in the exact order used by `publicInputWireMap`.
        uint256[] publicInputs;
    }

    /// @dev Fixed owner for the public-input accumulator and unique-row cache.
    /// Keeping these values behind one memory pointer avoids stack growth in
    /// the 103-entry production loop without changing the packed-map walk.
    struct PublicInputBindingScratch {
        uint256[] cachedRows;
        GoldilocksExt3.Ext3[] rowBindings;
        uint256 uniqueRows;
        uint256 varyingRowBits;
        GoldilocksExt3.Ext3 etaPower;
        GoldilocksExt3.Ext3 binding;
    }

    /// @notice Verify both lockstep Ext3 sumchecks and a norm/logUp terminal evaluation.
    /// @dev This verifies only the outer algebra. Before accepting a proof, the caller MUST
    ///      authenticate every member of `terminal` with grouped WHIR openings at the returned
    ///      points and check the Ext3 gate terminal equation. Supplying this function with
    ///      unauthenticated evaluations is not a complete proof verification.
    /// @param transcript Transcript snapshot after all earlier wire-v3 messages and challenges.
    /// @return logPoint Ext3 row point produced by the norm/logUp sumcheck.
    /// @return gatePoint Ext3 gate point produced in the same coupled rounds.
    /// @return gateFinalClaim Gate claim to be checked by a linked Ext3 gate evaluator.
    /// @return nextTranscript Transcript after all coupled sumcheck rounds.
    function verify(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        _validateAll(logProof, gateProof, vk, challenges, terminal);
        GoldilocksExt3.Ext3 memory logFinalClaim;
        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _verifyCoupledSumchecksUnchecked(logProof, gateProof, vk.numVars, transcript);
        GoldilocksExt3.Ext3 memory terminalValue = _evaluateTerminalUnchecked(vk, challenges, terminal, logPoint);
        if (!GoldilocksExt3.eq(logFinalClaim, terminalValue)) revert InvalidMleProof();
        nextTranscript = transcript;
    }

    /// @notice Verify the coupled sumchecks and terminal after a complete
    /// caller-side proof/VK preflight.
    /// @dev This entry is intentionally limited to the atomic verifier, which
    /// checks every proof coefficient and terminal limb in calldata before
    /// deriving canonical transcript challenges, and pins the VK by digest.
    /// It is not a standalone proof verifier and its return value must never be
    /// trusted without that preflight and the subsequent PCS/gate checks.
    function verifyPrevalidated(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        GoldilocksExt3.Ext3 memory logFinalClaim;
        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _verifyCoupledSumchecksUnchecked(logProof, gateProof, vk.numVars, transcript);
        GoldilocksExt3.Ext3 memory terminalValue = _evaluateTerminalUnchecked(vk, challenges, terminal, logPoint);
        if (!GoldilocksExt3.eq(logFinalClaim, terminalValue)) revert InvalidMleProof();
        nextTranscript = transcript;
    }

    /// @notice Verify all coefficient rounds without evaluating either terminal family.
    /// @dev There is intentionally no log-only or gate-only transcript API: every round
    ///      commits both Ext3 messages before either challenge is available.
    function verifyCoupledSumchecks(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        uint256 gateDegree,
        uint256 numVars,
        TranscriptV2.Transcript memory transcript
    )
        external
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3 memory logFinalClaim,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim,
            TranscriptV2.Transcript memory nextTranscript
        )
    {
        _validateProofs(logProof, gateProof, numVars, gateDegree);
        (logPoint, logFinalClaim, gatePoint, gateFinalClaim) =
            _verifyCoupledSumchecksUnchecked(logProof, gateProof, numVars, transcript);
        nextTranscript = transcript;
    }

    /// @notice Check one already-verified sumcheck claim against authenticated terminal values.
    /// @dev The caller is responsible for authenticating `terminal` with the PCS first.
    function verifyTerminal(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3 memory finalClaim
    ) external pure {
        _validateTerminalInputs(vk, challenges, terminal, point);
        _checkCanonical(finalClaim);
        GoldilocksExt3.Ext3 memory terminalValue = _evaluateTerminalUnchecked(vk, challenges, terminal, point);
        if (!GoldilocksExt3.eq(finalClaim, terminalValue)) revert InvalidMleProof();
    }

    /// @notice Evaluate the formal terminal polynomial without performing an inverse.
    function evaluateTerminal(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) external pure returns (GoldilocksExt3.Ext3 memory value) {
        _validateTerminalInputs(vk, challenges, terminal, point);
        value = _evaluateTerminalUnchecked(vk, challenges, terminal, point);
    }

    /// @notice Check the Ext3 gate sumcheck terminal after its constituent
    /// values have been authenticated by grouped WHIR.
    function verifyGateTerminal(
        GoldilocksExt3.Ext3[] memory tau,
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3 memory gateEvaluation,
        GoldilocksExt3.Ext3 memory finalClaim
    ) external pure {
        if (tau.length == 0 || tau.length != point.length || tau.length > MAX_ROW_VARIABLES) {
            revert InvalidMleProof();
        }
        for (uint256 i = 0; i < tau.length; ++i) {
            _checkCanonical(tau[i]);
            _checkCanonical(point[i]);
        }
        _checkCanonical(gateEvaluation);
        _checkCanonical(finalClaim);
        GoldilocksExt3.Ext3 memory expected = GoldilocksExt3.mul(_eqEvaluation(tau, point), gateEvaluation);
        if (!GoldilocksExt3.eq(expected, finalClaim)) revert InvalidMleProof();
    }

    /// @notice Evaluate formal adjugate coordinates over Ext3-valued coordinate polynomials.
    function formalAdjugate(GoldilocksExt3.Ext3[3] memory coordinates)
        external
        pure
        returns (GoldilocksExt3.Ext3[3] memory adjugate)
    {
        for (uint256 i = 0; i < 3; ++i) {
            _checkCanonical(coordinates[i]);
        }
        adjugate = _formalAdjugate(coordinates);
    }

    /// @notice Evaluate the formal cubic norm over Ext3-valued coordinate polynomials.
    function formalNorm(GoldilocksExt3.Ext3[3] memory coordinates)
        external
        pure
        returns (GoldilocksExt3.Ext3 memory norm)
    {
        for (uint256 i = 0; i < 3; ++i) {
            _checkCanonical(coordinates[i]);
        }
        norm = _formalNorm(coordinates);
    }

    function _verifyCoupledSumchecksUnchecked(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        uint256 numVars,
        TranscriptV2.Transcript memory transcript
    )
        private
        pure
        returns (
            GoldilocksExt3.Ext3[] memory logPoint,
            GoldilocksExt3.Ext3 memory logFinalClaim,
            GoldilocksExt3.Ext3[] memory gatePoint,
            GoldilocksExt3.Ext3 memory gateFinalClaim
        )
    {
        logPoint = new GoldilocksExt3.Ext3[](numVars);
        gatePoint = new GoldilocksExt3.Ext3[](numVars);
        GoldilocksExt3.Ext3 memory logClaim = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory gateClaim = GoldilocksExt3.zero();

        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            GoldilocksExt3.Ext3[] memory logCoefficients = logProof.rounds[roundIndex].nonConstant;
            GoldilocksExt3.Ext3[] memory gateCoefficients = gateProof.rounds[roundIndex].nonConstant;
            TranscriptV2.CoupledOuterRoundChallenges memory roundChallenges =
                TranscriptV2.commitCoupledOuterRound(transcript, roundIndex, logCoefficients, gateCoefficients);

            logPoint[roundIndex] = roundChallenges.log;
            logClaim = _evaluateExt3Round(logClaim, logCoefficients, roundChallenges.log);
            gatePoint[roundIndex] = roundChallenges.gate;
            gateClaim = _evaluateExt3RoundDynamic(gateClaim, gateCoefficients, roundChallenges.gate);
        }
        logFinalClaim = logClaim;
        gateFinalClaim = gateClaim;
    }

    function _evaluateExt3Round(
        GoldilocksExt3.Ext3 memory claim,
        GoldilocksExt3.Ext3[] memory coefficients,
        GoldilocksExt3.Ext3 memory challenge
    ) private pure returns (GoldilocksExt3.Ext3 memory) {
        GoldilocksExt3.Ext3 memory coefficientSum = GoldilocksExt3.zero();
        for (uint256 i = 0; i < MAX_DEGREE; ++i) {
            coefficientSum = GoldilocksExt3.add(coefficientSum, coefficients[i]);
        }
        GoldilocksExt3.Ext3 memory a0 = GoldilocksExt3.mulScalar(GoldilocksExt3.sub(claim, coefficientSum), INV_TWO);
        GoldilocksExt3.Ext3 memory evaluated = GoldilocksExt3.zero();
        for (uint256 i = MAX_DEGREE; i > 0; --i) {
            evaluated = GoldilocksExt3.add(GoldilocksExt3.mul(evaluated, challenge), coefficients[i - 1]);
        }
        return GoldilocksExt3.add(GoldilocksExt3.mul(evaluated, challenge), a0);
    }

    function _evaluateExt3RoundDynamic(
        GoldilocksExt3.Ext3 memory claim,
        GoldilocksExt3.Ext3[] memory coefficients,
        GoldilocksExt3.Ext3 memory challenge
    ) private pure returns (GoldilocksExt3.Ext3 memory) {
        GoldilocksExt3.Ext3 memory coefficientSum = GoldilocksExt3.zero();
        for (uint256 i = 0; i < coefficients.length; ++i) {
            coefficientSum = GoldilocksExt3.add(coefficientSum, coefficients[i]);
        }
        GoldilocksExt3.Ext3 memory a0 = GoldilocksExt3.mulScalar(GoldilocksExt3.sub(claim, coefficientSum), INV_TWO);
        GoldilocksExt3.Ext3 memory evaluated = GoldilocksExt3.zero();
        for (uint256 i = coefficients.length; i > 0; --i) {
            evaluated = GoldilocksExt3.add(GoldilocksExt3.mul(evaluated, challenge), coefficients[i - 1]);
        }
        return GoldilocksExt3.add(GoldilocksExt3.mul(evaluated, challenge), a0);
    }

    function _evaluateTerminalUnchecked(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) private pure returns (GoldilocksExt3.Ext3 memory) {
        GoldilocksExt3.Ext3 memory permutationValue = _permutationTerminalUnchecked(vk, challenges, terminal, point);
        GoldilocksExt3.Ext3 memory publicInputBinding = _publicInputBinding(vk, terminal, point, challenges.eta);
        return GoldilocksExt3.add(permutationValue, GoldilocksExt3.mul(challenges.xi, publicInputBinding));
    }

    /// @dev Existing degree-five norm/logUp terminal, isolated so adding the
    /// direct-PI relation cannot exhaust the EVM compiler's stack in its wire loop.
    function _permutationTerminalUnchecked(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) private pure returns (GoldilocksExt3.Ext3 memory permutationValue) {
        GoldilocksExt3.Ext3 memory eqValue = _eqEvaluation(challenges.tau, point);
        GoldilocksExt3.Ext3 memory subgroup = _subgroupEvaluation(vk.subgroupGenPowers, point);
        GoldilocksExt3.Ext3 memory helperZeroChecks = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory logupSum = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory lambdaPower = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory identityPosition = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory identityNorm = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory identityAdjugate = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory sigmaNorm = GoldilocksExt3.zero();
        GoldilocksExt3.Ext3 memory sigmaAdjugate = GoldilocksExt3.zero();
        // Nine reusable Ext3 records. Keeping the formal-coordinate algebra in
        // fixed scratch prevents the free-memory pointer from advancing for
        // every field operation across all routed wires.
        uint256[27] memory scratch;

        for (uint256 wireIndex = 0; wireIndex < vk.numRoutedWires; ++wireIndex) {
            GoldilocksExt3.Ext3 memory wire = terminal.witness[wireIndex];
            // `k_i` is a pinned, canonical base-field scalar. Multiplication by
            // its Ext3 embedding is exactly component-wise scalar
            // multiplication, so avoid the six cross terms which are known to
            // be zero. `_validateTerminalShapeAndCanonical` ran before this
            // unchecked evaluator and makes the uint64 cast lossless.
            _mulScalarInPlace(identityPosition, subgroup, uint64(vk.kIs[wireIndex]));
            GoldilocksExt3.Ext3 memory sigmaPosition = terminal.preprocessed[vk.numConstants + wireIndex];

            _denominatorTermsInPlace(
                wire, identityPosition, challenges.beta, challenges.gamma, identityNorm, identityAdjugate, scratch
            );
            _denominatorTermsInPlace(
                wire, sigmaPosition, challenges.beta, challenges.gamma, sigmaNorm, sigmaAdjugate, scratch
            );

            GoldilocksExt3.Ext3 memory identityHelper = terminal.normInverse[wireIndex];
            GoldilocksExt3.Ext3 memory sigmaHelper = terminal.normInverse[vk.numRoutedWires + wireIndex];
            _accumulateWireInPlace(
                helperZeroChecks,
                logupSum,
                lambdaPower,
                identityHelper,
                sigmaHelper,
                identityNorm,
                sigmaNorm,
                identityAdjugate,
                sigmaAdjugate,
                challenges.rho,
                challenges.lambda,
                scratch
            );
        }

        permutationValue = GoldilocksExt3.add(
            GoldilocksExt3.mul(eqValue, helperZeroChecks), GoldilocksExt3.mul(challenges.kappa, logupSum)
        );
    }

    /// @dev Evaluate Σ eta^i eq(row_i, point) (W_col_i(point) - PI_i).
    /// Duplicate map entries and PI order are intentionally retained. Equality
    /// factors are evaluated once per unique row: weighted differences are
    /// first accumulated by row, so a 103-PI statement does not repeat either
    /// `eq(row, point)` or its final Ext3 multiplication for every PI.
    function _publicInputBinding(
        VerificationKey memory vk,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point,
        GoldilocksExt3.Ext3 memory eta
    ) private pure returns (GoldilocksExt3.Ext3 memory binding) {
        uint256 count = terminal.publicInputs.length;
        if (count == 0) return binding;
        PublicInputBindingScratch memory scratch;
        scratch.cachedRows = new uint256[](count);
        scratch.rowBindings = new GoldilocksExt3.Ext3[](count);
        scratch.etaPower = GoldilocksExt3.one();

        for (uint256 i = 0; i < count; ++i) {
            uint256 offset = 3 * i;
            uint256 row =
                uint8(vk.publicInputWireMap[offset]) | (uint256(uint8(vk.publicInputWireMap[offset + 1])) << 8);
            uint256 column = uint8(vk.publicInputWireMap[offset + 2]);
            uint256 rowIndex = _cachedRowIndex(scratch, row);
            if (i != 0) scratch.varyingRowBits |= scratch.cachedRows[0] ^ row;
            GoldilocksExt3.Ext3 memory wire = terminal.witness[column];
            _accumulatePublicInputInPlace(
                scratch.rowBindings[rowIndex], scratch.etaPower, wire, terminal.publicInputs[i]
            );
            if (i + 1 < count) _mulExt3InPlace(scratch.etaPower, eta);
        }
        GoldilocksExt3.Ext3 memory commonEq = _eqBooleanRowSelectedBits(
            scratch.cachedRows[0], point, scratch.varyingRowBits, false, GoldilocksExt3.one()
        );
        for (uint256 rowIndex = 0; rowIndex < scratch.uniqueRows; ++rowIndex) {
            GoldilocksExt3.Ext3 memory eqRow =
                _eqBooleanRowSelectedBits(scratch.cachedRows[rowIndex], point, scratch.varyingRowBits, true, commonEq);
            scratch.binding =
                GoldilocksExt3.add(scratch.binding, GoldilocksExt3.mul(eqRow, scratch.rowBindings[rowIndex]));
        }
        binding = scratch.binding;
    }

    function _cachedRowIndex(PublicInputBindingScratch memory scratch, uint256 row)
        private
        pure
        returns (uint256 rowIndex)
    {
        // Canonical PI targets are commonly emitted in row-local runs. Search
        // newest-to-oldest so every repeated row after the first is O(1),
        // while preserving exact PI order and accepting arbitrary maps.
        for (uint256 cached = scratch.uniqueRows; cached != 0;) {
            --cached;
            if (scratch.cachedRows[cached] == row) return cached;
        }
        rowIndex = scratch.uniqueRows;
        scratch.cachedRows[rowIndex] = row;
        ++scratch.uniqueRows;
    }

    /// @dev Evaluate only the coordinates selected by `varying` (or its
    /// complement). The caller factors coordinates shared by every unique PI
    /// row once, then evaluates only genuinely varying bits per row.
    function _eqBooleanRowSelectedBits(
        uint256 row,
        GoldilocksExt3.Ext3[] memory point,
        uint256 varying,
        bool selectVarying,
        GoldilocksExt3.Ext3 memory initial
    ) private pure returns (GoldilocksExt3.Ext3 memory value) {
        value = initial;
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 variable = 0; variable < point.length; ++variable) {
            if ((((varying >> variable) & 1) != 0) != selectVarying) continue;
            GoldilocksExt3.Ext3 memory factor =
                ((row >> variable) & 1) == 0 ? GoldilocksExt3.sub(one, point[variable]) : point[variable];
            value = GoldilocksExt3.mul(value, factor);
        }
    }

    /// @dev destination += etaPower * (wire - embed(publicInput)).
    /// All operands are loaded before the destination is written, so this is
    /// safe for the caller-owned row accumulator and avoids two temporary
    /// Ext3 allocations per public input.
    function _accumulatePublicInputInPlace(
        GoldilocksExt3.Ext3 memory destination,
        GoldilocksExt3.Ext3 memory etaPower,
        GoldilocksExt3.Ext3 memory wire,
        uint256 publicInput
    ) private pure {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let a0 := mload(etaPower)
            let a1 := mload(add(etaPower, 0x20))
            let a2 := mload(add(etaPower, 0x40))
            let b0 := addmod(mload(wire), sub(p, publicInput), p)
            let b1 := mload(add(wire, 0x20))
            let b2 := mload(add(wire, 0x40))
            let c0 := addmod(mulmod(a0, b0, p), mulmod(2, addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p), p), p)
            let c1 := addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p)
            let c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            mstore(destination, addmod(mload(destination), c0, p))
            mstore(add(destination, 0x20), addmod(mload(add(destination, 0x20)), c1, p))
            mstore(add(destination, 0x40), addmod(mload(add(destination, 0x40)), c2, p))
        }
    }

    /// @dev destination *= multiplier, loading every limb before overwriting
    /// the aliased left operand.
    function _mulExt3InPlace(GoldilocksExt3.Ext3 memory destination, GoldilocksExt3.Ext3 memory multiplier)
        private
        pure
    {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            let a0 := mload(destination)
            let a1 := mload(add(destination, 0x20))
            let a2 := mload(add(destination, 0x40))
            let b0 := mload(multiplier)
            let b1 := mload(add(multiplier, 0x20))
            let b2 := mload(add(multiplier, 0x40))
            let c0 := addmod(mulmod(a0, b0, p), mulmod(2, addmod(mulmod(a1, b2, p), mulmod(a2, b1, p), p), p), p)
            let c1 := addmod(addmod(mulmod(a0, b1, p), mulmod(a1, b0, p), p), mulmod(2, mulmod(a2, b2, p), p), p)
            let c2 := addmod(addmod(mulmod(a0, b2, p), mulmod(a1, b1, p), p), mulmod(a2, b0, p), p)
            mstore(destination, c0)
            mstore(add(destination, 0x20), c1)
            mstore(add(destination, 0x40), c2)
        }
    }

    function _mulScalarInPlace(GoldilocksExt3.Ext3 memory destination, GoldilocksExt3.Ext3 memory value, uint64 scalar)
        private
        pure
    {
        assembly ("memory-safe") {
            let p := 0xFFFFFFFF00000001
            mstore(destination, mulmod(mload(value), scalar, p))
            mstore(add(destination, 0x20), mulmod(mload(add(value, 0x20)), scalar, p))
            mstore(add(destination, 0x40), mulmod(mload(add(value, 0x40)), scalar, p))
        }
    }

    /// @dev Compute both formal norm and recomposed formal adjugate with one
    /// adjugate evaluation. All intermediates are written into caller-owned,
    /// fixed scratch records rather than appended to Solidity free memory.
    function _denominatorTermsInPlace(
        GoldilocksExt3.Ext3 memory wire,
        GoldilocksExt3.Ext3 memory position,
        GoldilocksExt3.Ext3 memory beta,
        GoldilocksExt3.Ext3 memory gamma,
        GoldilocksExt3.Ext3 memory norm,
        GoldilocksExt3.Ext3 memory recomposed,
        uint256[27] memory scratch
    ) private pure {
        assembly ("memory-safe") {
            function mul3(out, x, y) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                let y0 := mload(y)
                let y1 := mload(add(y, 0x20))
                let y2 := mload(add(y, 0x40))
                mstore(out, addmod(mulmod(x0, y0, p), mulmod(2, addmod(mulmod(x1, y2, p), mulmod(x2, y1, p), p), p), p))
                mstore(
                    add(out, 0x20),
                    addmod(addmod(mulmod(x0, y1, p), mulmod(x1, y0, p), p), mulmod(2, mulmod(x2, y2, p), p), p)
                )
                mstore(add(out, 0x40), addmod(addmod(mulmod(x0, y2, p), mulmod(x1, y1, p), p), mulmod(x2, y0, p), p))
            }
            function square3(out, x) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                mstore(out, addmod(mulmod(x0, x0, p), mulmod(4, mulmod(x1, x2, p), p), p))
                mstore(add(out, 0x20), addmod(mulmod(2, mulmod(x0, x1, p), p), mulmod(2, mulmod(x2, x2, p), p), p))
                mstore(add(out, 0x40), addmod(mulmod(2, mulmod(x0, x2, p), p), mulmod(x1, x1, p), p))
            }

            let p := 0xFFFFFFFF00000001
            let a := scratch
            let b := add(scratch, 0x60)
            let c := add(scratch, 0xc0)
            let s0 := add(scratch, 0x120)
            let s1 := add(scratch, 0x180)
            let s2 := add(scratch, 0x1e0)
            let t0 := add(scratch, 0x240)
            let t1 := add(scratch, 0x2a0)
            let t2 := add(scratch, 0x300)

            let p0 := mload(position)
            let p1 := mload(add(position, 0x20))
            let p2 := mload(add(position, 0x40))
            let g0 := mload(gamma)
            let g1 := mload(add(gamma, 0x20))
            let g2 := mload(add(gamma, 0x40))

            // a = wire + embed(beta_0) + position * gamma_0.
            mstore(a, addmod(addmod(mload(wire), mload(beta), p), mulmod(p0, g0, p), p))
            mstore(add(a, 0x20), addmod(mload(add(wire, 0x20)), mulmod(p1, g0, p), p))
            mstore(add(a, 0x40), addmod(mload(add(wire, 0x40)), mulmod(p2, g0, p), p))
            // b/c have no wire term.
            mstore(b, addmod(mload(add(beta, 0x20)), mulmod(p0, g1, p), p))
            mstore(add(b, 0x20), mulmod(p1, g1, p))
            mstore(add(b, 0x40), mulmod(p2, g1, p))
            mstore(c, addmod(mload(add(beta, 0x40)), mulmod(p0, g2, p), p))
            mstore(add(c, 0x20), mulmod(p1, g2, p))
            mstore(add(c, 0x40), mulmod(p2, g2, p))

            // (s0,s1,s2) = (a^2-2bc, 2c^2-ab, b^2-ac).
            square3(s0, a)
            mul3(t0, b, c)
            mstore(s0, addmod(mload(s0), sub(p, addmod(mload(t0), mload(t0), p)), p))
            mstore(
                add(s0, 0x20),
                addmod(mload(add(s0, 0x20)), sub(p, addmod(mload(add(t0, 0x20)), mload(add(t0, 0x20)), p)), p)
            )
            mstore(
                add(s0, 0x40),
                addmod(mload(add(s0, 0x40)), sub(p, addmod(mload(add(t0, 0x40)), mload(add(t0, 0x40)), p)), p)
            )

            square3(s1, c)
            mul3(t0, a, b)
            mstore(s1, addmod(addmod(mload(s1), mload(s1), p), sub(p, mload(t0)), p))
            mstore(
                add(s1, 0x20),
                addmod(addmod(mload(add(s1, 0x20)), mload(add(s1, 0x20)), p), sub(p, mload(add(t0, 0x20))), p)
            )
            mstore(
                add(s1, 0x40),
                addmod(addmod(mload(add(s1, 0x40)), mload(add(s1, 0x40)), p), sub(p, mload(add(t0, 0x40))), p)
            )

            square3(s2, b)
            mul3(t0, a, c)
            mstore(s2, addmod(mload(s2), sub(p, mload(t0)), p))
            mstore(add(s2, 0x20), addmod(mload(add(s2, 0x20)), sub(p, mload(add(t0, 0x20))), p))
            mstore(add(s2, 0x40), addmod(mload(add(s2, 0x40)), sub(p, mload(add(t0, 0x40))), p))

            // norm = a*s0 + 2*(c*s1 + b*s2).
            mul3(t0, a, s0)
            mul3(t1, c, s1)
            mul3(t2, b, s2)
            mstore(
                norm,
                addmod(mload(t0), addmod(addmod(mload(t1), mload(t2), p), addmod(mload(t1), mload(t2), p), p), p)
            )
            mstore(
                add(norm, 0x20),
                addmod(
                    mload(add(t0, 0x20)),
                    addmod(
                        addmod(mload(add(t1, 0x20)), mload(add(t2, 0x20)), p),
                        addmod(mload(add(t1, 0x20)), mload(add(t2, 0x20)), p),
                        p
                    ),
                    p
                )
            )
            mstore(
                add(norm, 0x40),
                addmod(
                    mload(add(t0, 0x40)),
                    addmod(
                        addmod(mload(add(t1, 0x40)), mload(add(t2, 0x40)), p),
                        addmod(mload(add(t1, 0x40)), mload(add(t2, 0x40)), p),
                        p
                    ),
                    p
                )
            )

            // s0 + theta*s1 + theta^2*s2, theta^3 = 2.
            mstore(
                recomposed,
                addmod(
                    mload(s0),
                    addmod(
                        addmod(mload(add(s1, 0x40)), mload(add(s1, 0x40)), p),
                        addmod(mload(add(s2, 0x20)), mload(add(s2, 0x20)), p),
                        p
                    ),
                    p
                )
            )
            mstore(
                add(recomposed, 0x20),
                addmod(
                    mload(add(s0, 0x20)),
                    addmod(mload(s1), addmod(mload(add(s2, 0x40)), mload(add(s2, 0x40)), p), p),
                    p
                )
            )
            mstore(add(recomposed, 0x40), addmod(mload(add(s0, 0x40)), addmod(mload(add(s1, 0x20)), mload(s2), p), p))
        }
    }

    function _accumulateWireInPlace(
        GoldilocksExt3.Ext3 memory helperZeroChecks,
        GoldilocksExt3.Ext3 memory logupSum,
        GoldilocksExt3.Ext3 memory lambdaPower,
        GoldilocksExt3.Ext3 memory identityHelper,
        GoldilocksExt3.Ext3 memory sigmaHelper,
        GoldilocksExt3.Ext3 memory identityNorm,
        GoldilocksExt3.Ext3 memory sigmaNorm,
        GoldilocksExt3.Ext3 memory identityAdjugate,
        GoldilocksExt3.Ext3 memory sigmaAdjugate,
        GoldilocksExt3.Ext3 memory rho,
        GoldilocksExt3.Ext3 memory lambda,
        uint256[27] memory scratch
    ) private pure {
        assembly ("memory-safe") {
            function mul3(out, x, y) {
                let p := 0xFFFFFFFF00000001
                let x0 := mload(x)
                let x1 := mload(add(x, 0x20))
                let x2 := mload(add(x, 0x40))
                let y0 := mload(y)
                let y1 := mload(add(y, 0x20))
                let y2 := mload(add(y, 0x40))
                mstore(out, addmod(mulmod(x0, y0, p), mulmod(2, addmod(mulmod(x1, y2, p), mulmod(x2, y1, p), p), p), p))
                mstore(
                    add(out, 0x20),
                    addmod(addmod(mulmod(x0, y1, p), mulmod(x1, y0, p), p), mulmod(2, mulmod(x2, y2, p), p), p)
                )
                mstore(add(out, 0x40), addmod(addmod(mulmod(x0, y2, p), mulmod(x1, y1, p), p), mulmod(x2, y0, p), p))
            }

            let p := 0xFFFFFFFF00000001
            let identityZero := scratch
            let sigmaZero := add(scratch, 0x60)
            let tmp := add(scratch, 0xc0)
            let contribution := add(scratch, 0x120)
            let identityTerm := add(scratch, 0x180)
            let sigmaTerm := add(scratch, 0x1e0)

            mul3(identityZero, identityHelper, identityNorm)
            mstore(identityZero, addmod(mload(identityZero), sub(p, 1), p))
            mul3(sigmaZero, sigmaHelper, sigmaNorm)
            mstore(sigmaZero, addmod(mload(sigmaZero), sub(p, 1), p))
            mul3(tmp, rho, sigmaZero)
            mstore(tmp, addmod(mload(identityZero), mload(tmp), p))
            mstore(add(tmp, 0x20), addmod(mload(add(identityZero, 0x20)), mload(add(tmp, 0x20)), p))
            mstore(add(tmp, 0x40), addmod(mload(add(identityZero, 0x40)), mload(add(tmp, 0x40)), p))
            mul3(contribution, lambdaPower, tmp)
            mstore(helperZeroChecks, addmod(mload(helperZeroChecks), mload(contribution), p))
            mstore(
                add(helperZeroChecks, 0x20),
                addmod(mload(add(helperZeroChecks, 0x20)), mload(add(contribution, 0x20)), p)
            )
            mstore(
                add(helperZeroChecks, 0x40),
                addmod(mload(add(helperZeroChecks, 0x40)), mload(add(contribution, 0x40)), p)
            )

            mul3(identityTerm, identityHelper, identityAdjugate)
            mul3(sigmaTerm, sigmaHelper, sigmaAdjugate)
            mstore(logupSum, addmod(mload(logupSum), addmod(mload(identityTerm), sub(p, mload(sigmaTerm)), p), p))
            mstore(
                add(logupSum, 0x20),
                addmod(
                    mload(add(logupSum, 0x20)),
                    addmod(mload(add(identityTerm, 0x20)), sub(p, mload(add(sigmaTerm, 0x20))), p),
                    p
                )
            )
            mstore(
                add(logupSum, 0x40),
                addmod(
                    mload(add(logupSum, 0x40)),
                    addmod(mload(add(identityTerm, 0x40)), sub(p, mload(add(sigmaTerm, 0x40))), p),
                    p
                )
            )

            mul3(lambdaPower, lambdaPower, lambda)
        }
    }

    function _denominatorCoordinates(
        GoldilocksExt3.Ext3 memory wire,
        GoldilocksExt3.Ext3 memory position,
        GoldilocksExt3.Ext3 memory beta,
        GoldilocksExt3.Ext3 memory gamma
    ) private pure returns (GoldilocksExt3.Ext3[3] memory coordinates) {
        // Each gamma coordinate is a base-field scalar embedded into Ext3.
        // `embed(gamma_i) * position == mulScalar(position, gamma_i)` exactly.
        coordinates[0] =
            GoldilocksExt3.add(GoldilocksExt3.add(_embed(beta.c0), wire), GoldilocksExt3.mulScalar(position, gamma.c0));
        coordinates[1] = GoldilocksExt3.add(_embed(beta.c1), GoldilocksExt3.mulScalar(position, gamma.c1));
        coordinates[2] = GoldilocksExt3.add(_embed(beta.c2), GoldilocksExt3.mulScalar(position, gamma.c2));
    }

    function _formalAdjugate(GoldilocksExt3.Ext3[3] memory coordinates)
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

    function _formalNorm(GoldilocksExt3.Ext3[3] memory coordinates) private pure returns (GoldilocksExt3.Ext3 memory) {
        GoldilocksExt3.Ext3[3] memory adjugate = _formalAdjugate(coordinates);
        return _formalNormFromAdjugate(coordinates, adjugate);
    }

    function _formalNormFromAdjugate(GoldilocksExt3.Ext3[3] memory coordinates, GoldilocksExt3.Ext3[3] memory adjugate)
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

    function _recomposeAdjugate(GoldilocksExt3.Ext3[3] memory coordinates)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory)
    {
        GoldilocksExt3.Ext3[3] memory adjugate = _formalAdjugate(coordinates);
        return _recomposeFormalAdjugate(adjugate);
    }

    function _recomposeFormalAdjugate(GoldilocksExt3.Ext3[3] memory adjugate)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory)
    {
        return GoldilocksExt3.add(
            adjugate[0], GoldilocksExt3.add(_mulByTheta(adjugate[1]), _mulByThetaSquared(adjugate[2]))
        );
    }

    function _mulByTheta(GoldilocksExt3.Ext3 memory value) private pure returns (GoldilocksExt3.Ext3 memory result) {
        result.c0 = uint64(addmod(uint256(value.c2), uint256(value.c2), P));
        result.c1 = value.c0;
        result.c2 = value.c1;
    }

    function _mulByThetaSquared(GoldilocksExt3.Ext3 memory value)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory result)
    {
        result.c0 = uint64(addmod(uint256(value.c1), uint256(value.c1), P));
        result.c1 = uint64(addmod(uint256(value.c2), uint256(value.c2), P));
        result.c2 = value.c0;
    }

    function _eqEvaluation(GoldilocksExt3.Ext3[] memory tau, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        value = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 i = 0; i < point.length; ++i) {
            // tau*x + (1-tau)*(1-x) = 1 - tau - x + 2*tau*x.
            // The latter needs only one Ext3 product.
            GoldilocksExt3.Ext3 memory factor = GoldilocksExt3.add(
                GoldilocksExt3.sub(GoldilocksExt3.sub(one, tau[i]), point[i]),
                GoldilocksExt3.double_(GoldilocksExt3.mul(tau[i], point[i]))
            );
            value = GoldilocksExt3.mul(value, factor);
        }
    }

    function _subgroupEvaluation(uint256[] memory subgroupGenPowers, GoldilocksExt3.Ext3[] memory point)
        private
        pure
        returns (GoldilocksExt3.Ext3 memory value)
    {
        value = GoldilocksExt3.one();
        GoldilocksExt3.Ext3 memory one = GoldilocksExt3.one();
        for (uint256 i = 0; i < point.length; ++i) {
            // (1-x) + x*g = 1 + x*(g-1). Since g is base-field
            // embedded, use scalar multiplication rather than a full Ext3 mul.
            uint64 generatorMinusOne = uint64(addmod(subgroupGenPowers[i], P - 1, P));
            GoldilocksExt3.Ext3 memory factor =
                GoldilocksExt3.add(one, GoldilocksExt3.mulScalar(point[i], generatorMinusOne));
            value = GoldilocksExt3.mul(value, factor);
        }
    }

    function _validateAll(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal
    ) private pure {
        _validateProofs(logProof, gateProof, vk.numVars, vk.gateDegree);
        // The actual point is generated canonically by TranscriptV2 after this
        // preflight, so do not allocate a proof-sized placeholder here.
        _validateTerminalShapeAndCanonical(vk, challenges, terminal);
    }

    function _validateProofs(
        SumcheckProof memory logProof,
        SumcheckProof memory gateProof,
        uint256 numVars,
        uint256 gateDegree
    ) private pure {
        if (
            numVars == 0 || numVars > MAX_ROW_VARIABLES || gateDegree == 0 || gateDegree > MAX_GATE_DEGREE
                || logProof.rounds.length != numVars || gateProof.rounds.length != numVars
        ) {
            revert InvalidMleProof();
        }
        for (uint256 roundIndex = 0; roundIndex < numVars; ++roundIndex) {
            GoldilocksExt3.Ext3[] memory coefficients = logProof.rounds[roundIndex].nonConstant;
            if (coefficients.length != MAX_DEGREE) revert InvalidMleProof();
            for (uint256 coefficientIndex = 0; coefficientIndex < MAX_DEGREE; ++coefficientIndex) {
                _checkCanonical(coefficients[coefficientIndex]);
            }
            GoldilocksExt3.Ext3[] memory gateCoefficients = gateProof.rounds[roundIndex].nonConstant;
            if (gateCoefficients.length != gateDegree) revert InvalidMleProof();
            for (uint256 coefficientIndex = 0; coefficientIndex < gateDegree; ++coefficientIndex) {
                _checkCanonical(gateCoefficients[coefficientIndex]);
            }
        }
    }

    function _validateTerminalInputs(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal,
        GoldilocksExt3.Ext3[] memory point
    ) private pure {
        _validateTerminalShapeAndCanonical(vk, challenges, terminal);
        if (point.length != vk.numVars) revert InvalidMleProof();
        for (uint256 i = 0; i < point.length; ++i) {
            _checkCanonical(point[i]);
        }
    }

    function _validateTerminalShapeAndCanonical(
        VerificationKey memory vk,
        Challenges memory challenges,
        TerminalEvaluations memory terminal
    ) private pure {
        if (
            vk.numVars > MAX_ROW_VARIABLES || vk.numRoutedWires > MAX_ROUTED_WIRES
                || vk.numWires > MAX_CONSTITUENT_WIDTH || vk.numRoutedWires > vk.numWires
                || vk.numConstants > MAX_CONSTITUENT_WIDTH - vk.numRoutedWires || vk.kIs.length != vk.numRoutedWires
                || vk.subgroupGenPowers.length != vk.numVars || challenges.tau.length != vk.numVars
                || terminal.preprocessed.length != vk.numConstants + vk.numRoutedWires
                || terminal.witness.length != vk.numWires || terminal.normInverse.length != 2 * vk.numRoutedWires
                || terminal.publicInputs.length > type(uint256).max / 3
                || vk.publicInputWireMap.length != 3 * terminal.publicInputs.length
        ) revert InvalidMleProof();

        _checkCanonical(challenges.beta);
        _checkCanonical(challenges.gamma);
        _checkCanonical(challenges.lambda);
        _checkCanonical(challenges.rho);
        _checkCanonical(challenges.kappa);
        _checkCanonical(challenges.eta);
        _checkCanonical(challenges.xi);
        for (uint256 i = 0; i < challenges.tau.length; ++i) {
            _checkCanonical(challenges.tau[i]);
        }
        for (uint256 i = 0; i < vk.kIs.length; ++i) {
            if (vk.kIs[i] >= P) revert InvalidMleProof();
        }
        for (uint256 i = 0; i < vk.subgroupGenPowers.length; ++i) {
            if (vk.subgroupGenPowers[i] >= P) revert InvalidMleProof();
        }
        for (uint256 i = 0; i < terminal.preprocessed.length; ++i) {
            _checkCanonical(terminal.preprocessed[i]);
        }
        for (uint256 i = 0; i < terminal.witness.length; ++i) {
            _checkCanonical(terminal.witness[i]);
        }
        for (uint256 i = 0; i < terminal.normInverse.length; ++i) {
            _checkCanonical(terminal.normInverse[i]);
        }
        uint256 degree = uint256(1) << vk.numVars;
        for (uint256 i = 0; i < terminal.publicInputs.length; ++i) {
            if (terminal.publicInputs[i] >= P) revert InvalidMleProof();
            uint256 offset = 3 * i;
            uint256 row =
                uint8(vk.publicInputWireMap[offset]) | (uint256(uint8(vk.publicInputWireMap[offset + 1])) << 8);
            uint256 column = uint8(vk.publicInputWireMap[offset + 2]);
            if (row >= degree || column >= vk.numRoutedWires) revert InvalidMleProof();
        }
    }

    function _embed(uint256 value) private pure returns (GoldilocksExt3.Ext3 memory result) {
        result.c0 = uint64(value);
    }

    function _checkCanonical(GoldilocksExt3.Ext3 memory value) private pure {
        if (uint256(value.c0) >= P || uint256(value.c1) >= P || uint256(value.c2) >= P) {
            revert InvalidMleProof();
        }
    }
}
