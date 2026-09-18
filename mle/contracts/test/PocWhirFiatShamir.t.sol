// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {GoldilocksExt3} from "../src/spongefish/GoldilocksExt3.sol";
import {SpongefishWhirVerify} from "../src/spongefish/SpongefishWhirVerify.sol";
import {NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2} from "../src/generated/MleWhirV2.sol";

/// @title PocWhirFiatShamir
/// @notice ADVERSARIAL AUDIT ARTIFACT — not part of the production suite.
///         Drives `SpongefishWhirVerify.verifyWhirProofBound` directly with the
///         honest wire-v3 fixture and applies proof-only mutations (narg string
///         and hint stream), which is exactly the audit attacker model.
///
///         Byte layout of the honest narg string for this fixture (taken from
///         the Rust native trace shipped in the fixture, `whirNative.labels`):
///           0   ..32   group[0].root
///           32  ..56   group[0].ood_answer[0]
///           56  ..88   group[0].bound_root      (duplicate of group[0].root)
///           88  ..176  group[1] (same 88-byte stride)
///           176 ..264  group[2] (same 88-byte stride)
///           264 ..408  statement.claim[0..6)    (6 x 24 bytes)
///           408 ..552  cross_ood[0..6)          (6 x 24 bytes)
///           <<< initial.vector_rlc and initial.constraint_rlc are squeezed
///               HERE, at narg = 552: strictly after all three roots and all
///               six claims. This is the historical forgery point. >>>
///           552 ..744  initial sumcheck (4 rounds x (c0,c2))
///           744 ..776  folding_round[0].root
///           776 ..800  folding_round[0].ood_answer[0]
///           800 ..808  folding_round[0].pow.nonce
///           808 ..1000 folding_round[0] sumcheck (4 rounds)
///           1000..1096 final.vector[0..4)
///           1096..1104 final.pow.nonce
///           1104..1200 final sumcheck (2 rounds)
contract PocWhirFiatShamirTest is Test {
    string internal constant FIXTURE = "test/fixtures/v2_cross_language.json";
    string internal constant CASE = ".cases[0]";

    uint256 internal constant NARG_ROOT_0 = 0;
    uint256 internal constant NARG_BOUND_ROOT_0 = 56;
    uint256 internal constant NARG_ROOT_1 = 88;
    uint256 internal constant NARG_BOUND_ROOT_1 = 144;
    uint256 internal constant NARG_ROOT_2 = 176;
    uint256 internal constant NARG_BOUND_ROOT_2 = 232;
    uint256 internal constant NARG_CLAIMS = 264;
    uint256 internal constant NARG_CROSS_OOD = 408;
    uint256 internal constant NARG_INITIAL_SUMCHECK = 552;
    uint256 internal constant NARG_ROUND0_ROOT = 744;
    uint256 internal constant NARG_ROUND0_POW_NONCE = 800;
    uint256 internal constant NARG_FINAL_VECTOR = 1000;

    // Hint-stream offsets, from the same native trace (`whirNative.hintPositions`):
    //   0     ..9800   folding_round[0].previous_opening.hint[0]  (group 0)
    //   9800  ..19600  folding_round[0].previous_opening.hint[1]  (group 1)
    //   19600 ..29400  folding_round[0].previous_opening.hint[2]  (group 2)
    //   29400 ..40384  final.opening.hint[0]
    uint256 internal constant GROUP0_HINT_END = 9800;
    uint256 internal constant FINAL_HINT_START = 29400;

    uint64 internal constant P = 0xFFFFFFFF00000001;

    struct Case {
        bytes protocolId;
        bytes sessionId;
        bytes narg;
        bytes hints;
        bytes32[] roots;
        GoldilocksExt3.Ext3[] evaluations;
        bytes mask;
        SpongefishWhirVerify.WhirParams whir;
    }

    // ------------------------------------------------------------------
    // Fixture loading
    // ------------------------------------------------------------------

    function _load(uint8 maskByte) internal view returns (Case memory c) {
        string memory json = vm.readFile(FIXTURE);

        MleVerifierV2.MleProof memory proof = abi.decode(
            vm.parseJsonBytes(json, string.concat(CASE, ".solidityAbiProof.bytes")), (MleVerifierV2.MleProof)
        );
        MleVerifierV2.VerificationConfig memory config = abi.decode(
            vm.parseJsonBytes(json, string.concat(CASE, ".solidityAbiVerificationConfig.bytes")),
            (MleVerifierV2.VerificationConfig)
        );

        bytes memory protocolId = vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.whirProtocolId"));
        require(protocolId.length == 64, "protocol id length");
        c.protocolId = protocolId;
        c.sessionId = vm.parseJsonBytes(json, string.concat(CASE, ".verificationKey.whirSessionId"));
        c.narg = proof.whirTranscript;
        c.hints = proof.whirHints;

        c.roots = new bytes32[](NUM_PCS_GROUPS_V2);
        c.roots[0] = proof.preprocessedRoot;
        c.roots[1] = proof.witnessRoot;
        c.roots[2] = proof.normInverseRoot;

        c.whir = config.whir;
        c.whir.evaluationPoint =
            _reverse(_ext3Array(json, string.concat(CASE, ".packedPoints[0].packedPoint"), c.whir.numVariables));
        c.whir.evaluationPoint2 =
            _reverse(_ext3Array(json, string.concat(CASE, ".packedPoints[1].packedPoint"), c.whir.numVariables));
        c.whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);

        c.evaluations = new GoldilocksExt3.Ext3[](NUM_PCS_CLAIMS_V2);
        // Claim 5 (gate point x norm_inverse group) is the unbound slot; the
        // fixture records `null` for it, which is exactly the point of item 8.
        for (uint256 i = 0; i < NUM_PCS_CLAIMS_V2 - 1; ++i) {
            c.evaluations[i] = _ext3(json, string.concat(CASE, ".packedClaims[", vm.toString(i), "].value"));
        }
        c.mask = new bytes(1);
        c.mask[0] = bytes1(maskByte);
    }

    function _ext3Array(string memory json, string memory path, uint256 len)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory out)
    {
        out = new GoldilocksExt3.Ext3[](len);
        for (uint256 i = 0; i < len; ++i) {
            out[i] = _ext3(json, string.concat(path, "[", vm.toString(i), "]"));
        }
    }

    function _ext3(string memory json, string memory path) private pure returns (GoldilocksExt3.Ext3 memory v) {
        string[] memory limbs = vm.parseJsonStringArray(json, path);
        require(limbs.length == 3, "ext3 limbs");
        v = GoldilocksExt3.Ext3(_hex64(limbs[0]), _hex64(limbs[1]), _hex64(limbs[2]));
    }

    function _hex64(string memory s) private pure returns (uint64) {
        bytes memory raw = bytes(s);
        require(raw.length == 18 && raw[0] == "0" && raw[1] == "x", "hex64 shape");
        uint256 value;
        for (uint256 i = 2; i < 18; ++i) {
            uint8 ch = uint8(raw[i]);
            uint256 digit;
            if (ch >= 48 && ch <= 57) digit = ch - 48;
            else if (ch >= 97 && ch <= 102) digit = ch - 87;
            else if (ch >= 65 && ch <= 70) digit = ch - 55;
            else revert("hex64 digit");
            value = (value << 4) | digit;
        }
        require(value < P, "hex64 canonical");
        return uint64(value);
    }

    function _reverse(GoldilocksExt3.Ext3[] memory dense)
        private
        pure
        returns (GoldilocksExt3.Ext3[] memory reversed)
    {
        reversed = new GoldilocksExt3.Ext3[](dense.length);
        for (uint256 i = 0; i < dense.length; ++i) {
            reversed[i] = dense[dense.length - 1 - i];
        }
    }

    // ------------------------------------------------------------------
    // Verifier entry (external so try/catch and expectRevert work)
    // ------------------------------------------------------------------

    function run(Case memory c) external pure returns (bool) {
        return SpongefishWhirVerify.verifyWhirProofBound(
            c.protocolId, c.sessionId, "", c.narg, c.hints, c.evaluations, c.mask, c.roots, c.whir
        );
    }

    function _accepts(Case memory c) internal returns (bool ok) {
        try this.run(c) returns (bool result) {
            ok = result;
        } catch {
            ok = false;
        }
    }

    // ------------------------------------------------------------------
    // Baseline
    // ------------------------------------------------------------------

    /// @notice Positive control. Everything below is measured against this.
    function test_poc_baseline_honest_proof_is_accepted() public {
        assertTrue(_accepts(_load(0x1f)), "honest wire-v3 WHIR proof must verify");
    }

    // ------------------------------------------------------------------
    // Checklist 8: the unbound sixth claim
    // ------------------------------------------------------------------

    /// @notice CHECKLIST 8. With the production mask (0x1f) claim 5 is not
    ///         compared against any outer value. This shows WHIR itself still
    ///         binds it: a single-limb change to the claim-5 bytes in the narg
    ///         string is rejected, so the slot carries no prover freedom that
    ///         could cancel an error elsewhere.
    function test_poc_unbound_sixth_claim_is_still_bound_by_whir() public {
        Case memory c = _load(0x1f);
        c.narg[NARG_CLAIMS + 5 * 24] = bytes1(uint8(c.narg[NARG_CLAIMS + 5 * 24]) ^ 0x01);
        // The fixture's recorded value for claim 5 is only used when masked in;
        // with mask 0x1f the verifier copies the narg value, so no early
        // equality check can fire. Only WHIR can reject this.
        assertFalse(_accepts(c), "mutated unbound claim 5 must be rejected");
    }

    /// @notice CHECKLIST 8 (stronger). Drop the mask entirely (0x00) so that NO
    ///         claim is compared against an outer value, then mutate each claim
    ///         in turn. Every one must still be rejected: WHIR binds all six
    ///         claims individually, which is what makes the unbound slot safe.
    function test_poc_every_claim_is_bound_by_whir_even_with_empty_mask() public {
        assertTrue(_accepts(_load(0x00)), "unmasked honest proof must still verify");
        for (uint256 i = 0; i < NUM_PCS_CLAIMS_V2; ++i) {
            Case memory c = _load(0x00);
            uint256 off = NARG_CLAIMS + i * 24;
            c.narg[off] = bytes1(uint8(c.narg[off]) ^ 0x01);
            assertFalse(_accepts(c), string.concat("claim ", vm.toString(i), " must be WHIR-bound"));
        }
    }

    /// @notice CHECKLIST 8 / 1. Cross-commitment OOD answers are also free
    ///         prover values absorbed before the two RLC squeezes. Mutating one
    ///         must be rejected.
    function test_poc_cross_ood_answer_mutation_rejected() public {
        for (uint256 i = 0; i < 6; ++i) {
            Case memory c = _load(0x1f);
            uint256 off = NARG_CROSS_OOD + i * 24;
            c.narg[off] = bytes1(uint8(c.narg[off]) ^ 0x01);
            assertFalse(_accepts(c), string.concat("cross OOD ", vm.toString(i), " must be bound"));
        }
    }

    // ------------------------------------------------------------------
    // Checklist 6: canonicality
    // ------------------------------------------------------------------

    /// @notice CHECKLIST 6. p = 0xFFFFFFFF00000001 encodes the same field value
    ///         as 0 but a different byte string, so it would give one field
    ///         oracle two Fiat-Shamir states. Every 24-byte prover Ext3 read
    ///         must reject it.
    function test_poc_noncanonical_claim_encoding_rejected() public {
        Case memory c = _load(0x00);
        // p little-endian = 01 00 00 00 ff ff ff ff
        bytes8 pLe = hex"01000000ffffffff";
        for (uint256 b = 0; b < 8; ++b) {
            c.narg[NARG_CLAIMS + b] = pLe[b];
        }
        assertFalse(_accepts(c), "non-canonical claim limb must be rejected");
    }

    /// @notice CHECKLIST 6. Both streams must be consumed exactly; no ignored
    ///         tail on either side.
    function test_poc_stream_tails_rejected() public {
        Case memory c = _load(0x1f);
        c.narg = bytes.concat(c.narg, hex"00");
        assertFalse(_accepts(c), "trailing narg byte must be rejected");

        c = _load(0x1f);
        c.hints = bytes.concat(c.hints, hex"00");
        assertFalse(_accepts(c), "trailing hint byte must be rejected");

        c = _load(0x1f);
        c.narg = _shrink(c.narg, c.narg.length - 1);
        assertFalse(_accepts(c), "truncated narg must be rejected");

        c = _load(0x1f);
        c.hints = _shrink(c.hints, c.hints.length - 1);
        assertFalse(_accepts(c), "truncated hints must be rejected");
    }

    function _shrink(bytes memory data, uint256 newLength) private pure returns (bytes memory out) {
        out = new bytes(newLength);
        for (uint256 i = 0; i < newLength; ++i) {
            out[i] = data[i];
        }
    }

    // ------------------------------------------------------------------
    // Checklist 1/2: roots, commitments, Merkle
    // ------------------------------------------------------------------

    /// @notice CHECKLIST 1/2. Rewrite BOTH narg copies of group 0's root and
    ///         the caller-supplied expected root consistently, so every root
    ///         equality check still passes. Only the Merkle opening can catch
    ///         this — and it must.
    function test_poc_consistently_rewritten_root_still_rejected_by_merkle() public {
        Case memory c = _load(0x1f);
        bytes32 forged = bytes32(uint256(c.roots[0]) ^ 1);
        _writeBytes32(c.narg, NARG_ROOT_0, forged);
        _writeBytes32(c.narg, NARG_BOUND_ROOT_0, forged);
        c.roots[0] = forged;
        assertFalse(_accepts(c), "forged-but-consistent group-0 root must fail Merkle verification");
    }

    /// @notice CHECKLIST 2. Group roots are not interchangeable: swapping the
    ///         narg copies of group 0 and group 2 together with the expected
    ///         roots must be rejected (the leaves no longer match the trees,
    ///         and the transcript changes).
    function test_poc_group_root_swap_rejected() public {
        Case memory c = _load(0x1f);
        bytes32 r0 = c.roots[0];
        bytes32 r2 = c.roots[2];
        _writeBytes32(c.narg, NARG_ROOT_0, r2);
        _writeBytes32(c.narg, NARG_BOUND_ROOT_0, r2);
        _writeBytes32(c.narg, NARG_ROOT_2, r0);
        _writeBytes32(c.narg, NARG_BOUND_ROOT_2, r0);
        c.roots[0] = r2;
        c.roots[2] = r0;
        assertFalse(_accepts(c), "group root permutation must be rejected");
    }

    /// @notice CHECKLIST 1. The two evaluation points are the ONE part of the
    ///         public statement that is never absorbed into the inner WHIR
    ///         Keccak chain (it matches the Rust reference, which builds the
    ///         linear forms only after `config.verify`). Confirm they are still
    ///         load-bearing: perturbing any single coordinate of either point
    ///         must be rejected by the FinalClaim equation.
    function test_poc_evaluation_point_perturbation_rejected() public {
        // `run` is an external call, so the callee works on an ABI copy and the
        // local case can be mutated and restored in place (one fixture load).
        Case memory c = _load(0x1f);
        uint256 n = c.whir.numVariables;
        for (uint256 i = 0; i < n; ++i) {
            uint64 original = c.whir.evaluationPoint[i].c0;
            c.whir.evaluationPoint[i].c0 = uint64((uint256(original) + 1) % P);
            assertFalse(_accepts(c), string.concat("point1 coord ", vm.toString(i), " must matter"));
            c.whir.evaluationPoint[i].c0 = original;

            original = c.whir.evaluationPoint2[i].c0;
            c.whir.evaluationPoint2[i].c0 = uint64((uint256(original) + 1) % P);
            assertFalse(_accepts(c), string.concat("point2 coord ", vm.toString(i), " must matter"));
            c.whir.evaluationPoint2[i].c0 = original;
        }
        assertTrue(_accepts(c), "restored case must verify again");
    }

    /// @notice CHECKLIST 1. Reversing a point (the WHIR reversal convention) is
    ///         a semantically meaningful reorder that must be rejected.
    function test_poc_evaluation_point_reversal_rejected() public {
        Case memory c = _load(0x1f);
        c.whir.evaluationPoint = _reverse(c.whir.evaluationPoint);
        assertFalse(_accepts(c), "point1 reversal must be rejected");

        Case memory d = _load(0x1f);
        (d.whir.evaluationPoint, d.whir.evaluationPoint2) = (d.whir.evaluationPoint2, d.whir.evaluationPoint);
        assertFalse(_accepts(d), "point swap must be rejected");
    }

    /// @notice CHECKLIST 2. Flip a leaf byte inside group 1's opened rows (a
    ///         different tree from group 0) and inside the final opening.
    function test_poc_other_group_and_final_leaf_mutations_rejected() public {
        Case memory c = _load(0x1f);
        c.hints[GROUP0_HINT_END + 8] = bytes1(uint8(c.hints[GROUP0_HINT_END + 8]) ^ 0x01);
        assertFalse(_accepts(c), "group-1 leaf mutation must be rejected");

        Case memory d = _load(0x1f);
        d.hints[FINAL_HINT_START + 8] = bytes1(uint8(d.hints[FINAL_HINT_START + 8]) ^ 0x01);
        assertFalse(_accepts(d), "final-opening leaf mutation must be rejected");
    }

    /// @notice CHECKLIST 2. Flip the last Merkle sibling word of group 0's
    ///         round-0 opening.
    function test_poc_merkle_sibling_mutation_rejected() public {
        Case memory c = _load(0x1f);
        c.hints[GROUP0_HINT_END - 1] = bytes1(uint8(c.hints[GROUP0_HINT_END - 1]) ^ 0x01);
        assertFalse(_accepts(c), "mutated Merkle sibling must be rejected");
    }

    /// @notice CHECKLIST 2/3. Swap two opened leaf rows inside group 0. The row
    ///         ordering is pinned to the sorted query index list, so a
    ///         permutation must break both the Merkle root and the fold.
    function test_poc_opened_row_permutation_rejected() public {
        Case memory c = _load(0x1f);
        // group 0 rows start after the 8-byte Arkworks Vec length prefix.
        uint256 rowBytes = 16 * 1 * 8; // initialInterleavingDepth * numVectors * 8
        uint256 rowA = 8;
        uint256 rowB = 8 + rowBytes;
        for (uint256 i = 0; i < rowBytes; ++i) {
            bytes1 tmp = c.hints[rowA + i];
            c.hints[rowA + i] = c.hints[rowB + i];
            c.hints[rowB + i] = tmp;
        }
        assertFalse(_accepts(c), "permuted opened rows must be rejected");
    }

    /// @notice CHECKLIST 6. A non-canonical base-field limb inside an opened
    ///         leaf (p instead of 0) must be rejected even though the Merkle
    ///         tree commits raw bytes.
    function test_poc_noncanonical_leaf_limb_rejected() public {
        Case memory c = _load(0x1f);
        bytes8 pLe = hex"01000000ffffffff";
        for (uint256 b = 0; b < 8; ++b) {
            c.hints[8 + b] = pLe[b];
        }
        assertFalse(_accepts(c), "non-canonical leaf limb must be rejected");
    }

    /// @notice CHECKLIST 6. The Arkworks Vec length prefix in front of each
    ///         opened-row block is bound to the transcript-derived query count.
    function test_poc_vec_length_prefix_mutation_rejected() public {
        Case memory c = _load(0x1f);
        c.hints[0] = bytes1(uint8(c.hints[0]) ^ 0x01);
        assertFalse(_accepts(c), "mutated Vec length prefix must be rejected");
    }

    // ------------------------------------------------------------------
    // Checklist 1/4/5: round commitments, sumcheck, PoW, final polynomial
    // ------------------------------------------------------------------

    /// @notice CHECKLIST 1/4. Each initial sumcheck round message is bound.
    function test_poc_initial_sumcheck_message_mutation_rejected() public {
        Case memory c = _load(0x1f);
        c.narg[NARG_INITIAL_SUMCHECK] = bytes1(uint8(c.narg[NARG_INITIAL_SUMCHECK]) ^ 0x01);
        assertFalse(_accepts(c), "initial sumcheck c0 must be bound");
    }

    /// @notice CHECKLIST 1. The round-0 commitment root is absorbed before the
    ///         round's OOD point is squeezed and before the previous
    ///         commitment's query indices are drawn.
    function test_poc_round_commitment_root_mutation_rejected() public {
        Case memory c = _load(0x1f);
        c.narg[NARG_ROUND0_ROOT] = bytes1(uint8(c.narg[NARG_ROUND0_ROOT]) ^ 0x01);
        assertFalse(_accepts(c), "round-0 root must be bound");
    }

    /// @notice CHECKLIST 1. The PoW nonce is a prover message; an arbitrary
    ///         nonce must fail the threshold test.
    function test_poc_pow_nonce_mutation_rejected() public {
        Case memory c = _load(0x1f);
        c.narg[NARG_ROUND0_POW_NONCE] = bytes1(uint8(c.narg[NARG_ROUND0_POW_NONCE]) ^ 0xFF);
        assertFalse(_accepts(c), "round-0 PoW nonce must be checked");
    }

    /// @notice CHECKLIST 5. The final polynomial coefficients are checked
    ///         against every opened leaf and against the final sumcheck claim.
    function test_poc_final_vector_mutation_rejected() public {
        for (uint256 i = 0; i < 4; ++i) {
            Case memory c = _load(0x1f);
            uint256 off = NARG_FINAL_VECTOR + i * 24;
            c.narg[off] = bytes1(uint8(c.narg[off]) ^ 0x01);
            assertFalse(_accepts(c), string.concat("final vector coeff ", vm.toString(i), " must be bound"));
        }
    }

    function _writeBytes32(bytes memory data, uint256 offset, bytes32 value) private pure {
        require(offset + 32 <= data.length, "write bounds");
        assembly ("memory-safe") {
            mstore(add(add(data, 0x20), offset), value)
        }
    }
}
