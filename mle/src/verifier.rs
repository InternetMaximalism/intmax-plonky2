/// MLE proof verifier — combined sumcheck architecture.
///
/// Verification chain (all evaluations at sumcheck points):
///   1. Transcript reconstruction + challenge re-derivation
///   2. Packed-group WHIR openings of post-claim Ext3 index folds
///   4. Combined sumcheck: eq(τ,r)·C̃(r) + μ·eq(τ_perm,r)·h̃(r) = final_eval
///   5. Gate and logUp terminal equations over those PCS-bound openings
use anyhow::{ensure, Result};
use plonky2::hash::hash_types::RichField;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::plonk::config::Hasher;
use plonky2::plonk::vanishing_poly::evaluate_gate_constraints;
use plonky2::plonk::vars::EvaluationVars;
use plonky2_field::extension::{Extendable, FieldExtension};
use plonky2_field::types::Field;
use whir::algebra::fields::Field64_3;

use crate::commitment::whir_pcs::{WhirPCS, WHIR_SESSION_SPLIT};
use crate::eq_poly;
use crate::proof::{
    constituent_group_width, constituent_index_bits, packed_group_num_vars, MleProof,
    MleVerificationKey, GROUP_AUXILIARY, GROUP_INVERSE_HELPERS, GROUP_PREPROCESSED, GROUP_WITNESS,
    MLE_PROTOCOL_VERSION, NUM_PACKED_VECTORS_PER_GROUP, NUM_SPLIT_COMMITMENTS,
};
use crate::protocol_schema::{
    NUM_PCS_TERMINAL_POINTS, PACKED_BOUND_CLAIM_MASK, POINT_COMBINED, POINT_GATE, POINT_H,
    POINT_INVERSE,
};
use crate::prover::{
    absorb_claims_and_sample_index_points, absorb_schema_and_base_roots,
    derive_preprocessed_batch_r, fold_constituent_claim,
};
use crate::sumcheck::verifier::verify_sumcheck;
use crate::transcript::Transcript;

fn bind_expected_fold<F: RichField>(
    expected: &mut [Option<Field64_3>],
    point: usize,
    group: usize,
    values: &[F],
    constituent_width: usize,
    index_point: &[Field64_3],
) {
    expected[point * NUM_SPLIT_COMMITMENTS + group] = Some(fold_constituent_claim(
        values,
        constituent_width,
        index_point,
    ));
}

fn packed_eval_point<F: RichField>(row_point: &[F], index_point: &[Field64_3]) -> Vec<Field64_3> {
    row_point
        .iter()
        .map(|value| Field64_3::from(value.to_canonical_u64()))
        .chain(index_point.iter().copied())
        .collect()
}

/// Verify an MLE proof for a Plonky2 circuit.
pub fn mle_verify<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    vk: &MleVerificationKey<F>,
    proof: &MleProof<F>,
) -> Result<()> {
    let degree_bits = plonky2_util::log2_strict(common_data.degree());
    ensure!(
        vk.protocol_version == MLE_PROTOCOL_VERSION
            && proof.protocol_version == MLE_PROTOCOL_VERSION,
        "MLE protocol version mismatch"
    );
    let expected_constituent_width = constituent_group_width(
        common_data.num_constants,
        common_data.config.num_routed_wires,
        common_data.config.num_wires,
    );
    ensure!(
        vk.constituent_width == expected_constituent_width
            && proof.constituent_width == expected_constituent_width,
        "constituent schema width mismatch"
    );
    ensure!(
        proof.num_wires == common_data.config.num_wires
            && proof.num_routed_wires == common_data.config.num_routed_wires
            && proof.num_constants == common_data.num_constants
            && vk.num_routed_wires == common_data.config.num_routed_wires
            && vk.num_constants == common_data.num_constants,
        "circuit/schema dimensions mismatch"
    );
    ensure!(
        vk.k_is == common_data.k_is && proof.k_is == vk.k_is,
        "permutation coset shifts are not VK-bound"
    );
    ensure!(
        vk.subgroup_gen_powers.len() == degree_bits
            && proof.subgroup_gen_powers == vk.subgroup_gen_powers,
        "subgroup generator powers are not VK-bound"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 1: Circuit binding + transcript reconstruction
    // ═══════════════════════════════════════════════════════════════════
    ensure!(
        proof.circuit_digest == vk.circuit_digest,
        "Circuit digest mismatch"
    );
    ensure!(
        proof.public_inputs.len() == common_data.num_public_inputs,
        "public input length mismatch"
    );
    let expected_public_inputs_hash = PoseidonHash::hash_no_pad(&proof.public_inputs);
    ensure!(
        proof.public_inputs_hash == expected_public_inputs_hash,
        "public input hash mismatch"
    );

    ensure!(
        proof.preprocessed_root == vk.preprocessed_commitment_root,
        "Preprocessed commitment root mismatch — circuit binding violated"
    );
    let expected_pre_r: F =
        derive_preprocessed_batch_r(&proof.circuit_digest, &proof.preprocessed_root);
    ensure!(
        expected_pre_r == proof.preprocessed_batch_r,
        "Preprocessed batch_r mismatch"
    );

    let mut transcript = Transcript::new();
    transcript.domain_separate("circuit");
    transcript.absorb_field_vec(&proof.circuit_digest);
    transcript.absorb_field_vec(&proof.public_inputs);
    absorb_schema_and_base_roots::<F>(
        &mut transcript,
        common_data.num_constants,
        common_data.config.num_routed_wires,
        common_data.config.num_wires,
        expected_constituent_width,
        &proof.preprocessed_root,
        &proof.witness_root,
    );

    transcript.domain_separate("batch-commit-witness");
    let batch_r_wit: F = transcript.squeeze_challenge();
    ensure!(
        batch_r_wit == proof.witness_batch_r,
        "Witness batch_r mismatch"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 2: Re-derive challenges (must mirror prover transcript order)
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("challenges");
    let beta: F = transcript.squeeze_challenge();
    let gamma: F = transcript.squeeze_challenge();
    ensure!(beta == proof.beta, "Beta mismatch");
    ensure!(gamma == proof.gamma, "Gamma mismatch");

    // ── v2 logUp: inverse-helpers commitment is absorbed AFTER β,γ. ─────
    transcript.domain_separate("pcs-group-inverse-helpers");
    transcript.absorb_bytes(&proof.inverse_helpers_root);
    transcript.domain_separate("inverse-helpers-batch-r");
    let inv_helpers_batch_r: F = transcript.squeeze_challenge();
    ensure!(
        inv_helpers_batch_r == proof.inverse_helpers_batch_r,
        "Inverse helpers batch_r mismatch"
    );

    let alpha: F = transcript.squeeze_challenge();
    ensure!(alpha == proof.alpha, "Alpha mismatch");

    transcript.domain_separate("extension-combine");
    let ext_challenge: F = transcript.squeeze_challenge();
    ensure!(
        ext_challenge == proof.ext_challenge,
        "ext_challenge mismatch"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 3: Auxiliary commitment verification
    //
    // SECURITY: the packed auxiliary root commits C̃ and h̃ as separate,
    // ordered constituents before rho_aux, mu, and their query points. The
    // later Ext3 index projection plus grouped WHIR opening binds both claims.
    // The scalar identity below is retained as transcript consistency; it is
    // not the constituent-binding argument.
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("pcs-group-auxiliary");
    transcript.absorb_bytes(&proof.aux_commitment_root);
    transcript.domain_separate("aux-batch-r");
    let batch_r_aux: F = transcript.squeeze_challenge();
    ensure!(batch_r_aux == proof.aux_batch_r, "Aux batch_r mismatch");

    transcript.domain_separate("post-auxiliary-challenges-v1");
    let tau: Vec<F> = transcript.squeeze_challenges(degree_bits);
    let tau_perm: Vec<F> = transcript.squeeze_challenges(degree_bits);
    ensure!(tau == proof.tau, "Tau mismatch");
    ensure!(tau_perm == proof.tau_perm, "Tau_perm mismatch");

    transcript.domain_separate("v2-logup-challenges");
    let lambda_inv: F = transcript.squeeze_challenge();
    let mu_inv: F = transcript.squeeze_challenge();
    let tau_inv: Vec<F> = transcript.squeeze_challenges(degree_bits);
    ensure!(lambda_inv == proof.lambda_inv, "lambda_inv mismatch");
    ensure!(mu_inv == proof.mu_inv, "mu_inv mismatch");
    ensure!(tau_inv == proof.tau_inv, "tau_inv mismatch");

    // Verify P_aux(r) decomposition: P_aux(r) = C̃(r) + batch_r_aux · h̃(r)
    let expected_aux_eval = proof.aux_constraint_eval + batch_r_aux * proof.aux_perm_eval;
    ensure!(
        expected_aux_eval == proof.aux_eval_value,
        "Auxiliary decomposition mismatch: C̃(r) + batch_r_aux·h̃(r) ≠ P_aux(r)"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 4: Derive μ + verify combined sumcheck
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("combined-sumcheck");
    let mu: F = transcript.squeeze_challenge();
    ensure!(mu == proof.mu, "Mu mismatch");

    // SECURITY: Lookup argument is not yet implemented. Reject any circuit
    // that contains lookup tables to prevent unsound verification.
    let has_lookup = !common_data.luts.is_empty();
    ensure!(
        !has_lookup,
        "MLE verifier does not yet support lookup tables"
    );
    ensure!(
        proof.lookup_proofs.is_empty(),
        "lookup proofs are not part of protocol version 1"
    );

    // Verify combined sumcheck: Σ [eq(τ,b)·C̃(b) + μ·eq(τ_perm,b)·h̃(b)] = 0
    for (i, rp) in proof.combined_proof.round_polys.iter().enumerate() {
        ensure!(
            rp.evaluations.len() == 3,
            "combined round {i}: expected exactly 3 evaluations"
        );
    }
    let combined_result =
        verify_sumcheck(&proof.combined_proof, F::ZERO, degree_bits, &mut transcript);
    let (sumcheck_challenges, final_eval) =
        combined_result.map_err(|e| anyhow::anyhow!("Combined sumcheck failed: {}", e))?;
    ensure!(
        sumcheck_challenges == proof.sumcheck_challenges,
        "Combined sumcheck challenges mismatch"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 4.5 (v2 logUp): Verify Φ_inv zero-check sumcheck.
    //   Σ_b eq(τ_inv,b)·Σ_j λ^j·(A_j·D_id − 1 + μ_inv·(B_j·D_σ − 1)) = 0
    // Round-poly degree bound: 3.
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("v2-inv-zerocheck");
    // The versioned schema encodes every degree-3 round polynomial with
    // exactly four evaluations; shorter encodings are not aliases.
    for (i, rp) in proof.inv_sumcheck_proof.round_polys.iter().enumerate() {
        ensure!(
            rp.evaluations.len() == 4,
            "Φ_inv round {i}: expected exactly 4 evaluations"
        );
    }
    let inv_result = verify_sumcheck(
        &proof.inv_sumcheck_proof,
        F::ZERO,
        degree_bits,
        &mut transcript,
    );
    let (inv_challenges, inv_final_eval) =
        inv_result.map_err(|e| anyhow::anyhow!("Φ_inv sumcheck failed: {}", e))?;
    ensure!(
        inv_challenges == proof.inv_sumcheck_challenges,
        "Φ_inv sumcheck challenges mismatch"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 4.7 (v2 logUp): Verify Φ_h linear sumcheck.
    //   Σ_b H(b) = 0, H(b) = Σ_j (A_j(b) − B_j(b))
    // Round-poly degree bound: 1.
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("v2-h-linear");
    for (i, rp) in proof.h_sumcheck_proof.round_polys.iter().enumerate() {
        ensure!(
            rp.evaluations.len() == 2,
            "Φ_h round {i}: expected 2 evaluations (degree 1), got {}",
            rp.evaluations.len()
        );
    }
    let h_result = verify_sumcheck(
        &proof.h_sumcheck_proof,
        F::ZERO,
        degree_bits,
        &mut transcript,
    );
    let (h_challenges, h_final_eval) =
        h_result.map_err(|e| anyhow::anyhow!("Φ_h sumcheck failed: {}", e))?;
    ensure!(
        h_challenges == proof.h_sumcheck_challenges,
        "Φ_h sumcheck challenges mismatch"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 4.8 (v2 gate binding — Issue R2-#1, paper §7.3):
    //   Verify the Φ_gate zero-check sumcheck.
    //     Φ_gate(x) := eq(τ_gate, x) · flatten_ext(
    //                      Σ_j α^j · c_j(lift(W_k(x)), lift(const_k(x))),
    //                      ext_challenge
    //                  )
    //   claimed sum = 0. Round-poly degree bound: 1 + quotient_degree_factor.
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("v2-gate-challenges");
    let tau_gate: Vec<F> = transcript.squeeze_challenges(degree_bits);
    ensure!(tau_gate == proof.tau_gate, "tau_gate mismatch");

    transcript.domain_separate("v2-gate-zerocheck");
    // Matches the prover: Φ_gate has degree ≤ qdf + 2 per variable (1 for eq,
    // up to qdf + 1 for the filtered gate constraint formula).
    let max_round_degree_gate = 2 + common_data.quotient_degree_factor;
    for (i, rp) in proof.gate_sumcheck_proof.round_polys.iter().enumerate() {
        ensure!(
            rp.evaluations.len() == max_round_degree_gate + 1,
            "Φ_gate round {i}: expected {} evaluations (degree {max_round_degree_gate}), got {}",
            max_round_degree_gate + 1,
            rp.evaluations.len()
        );
    }
    let gate_result = verify_sumcheck(
        &proof.gate_sumcheck_proof,
        F::ZERO,
        degree_bits,
        &mut transcript,
    );
    let (gate_challenges, gate_final_eval) =
        gate_result.map_err(|e| anyhow::anyhow!("Φ_gate sumcheck failed: {}", e))?;
    ensure!(
        gate_challenges == proof.gate_sumcheck_challenges,
        "Φ_gate sumcheck challenges mismatch"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 5: Verify WHIR proofs + batch consistency
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("pcs-eval");

    let pre_len = proof.num_constants + proof.num_routed_wires;
    let witness_len = proof.num_wires;
    let inverse_len = 2 * proof.num_routed_wires;
    ensure!(
        proof.preprocessed_individual_evals.len() == pre_len
            && proof.preprocessed_individual_evals_at_r_inv.len() == pre_len
            && proof.preprocessed_individual_evals_at_r_gate_v2.len() == pre_len,
        "preprocessed constituent opening shape mismatch"
    );
    ensure!(
        proof.witness_individual_evals.len() == witness_len
            && proof.witness_individual_evals_at_r_inv.len() == witness_len
            && proof.witness_individual_evals_at_r_gate_v2.len() == witness_len,
        "witness constituent opening shape mismatch"
    );
    ensure!(
        proof.inverse_helpers_evals_at_r_inv.len() == inverse_len
            && proof.inverse_helpers_evals_at_r_h.len() == inverse_len,
        "inverse-helper constituent opening shape mismatch"
    );

    // Bind the exact claim matrix before sampling any constituent-index point.
    let empty: &[F] = &[];
    let aux_claims = [proof.aux_constraint_eval, proof.aux_perm_eval];
    let claims: [&[F]; 16] = [
        &proof.preprocessed_individual_evals,
        &proof.witness_individual_evals,
        empty,
        &aux_claims,
        &proof.preprocessed_individual_evals_at_r_inv,
        &proof.witness_individual_evals_at_r_inv,
        &proof.inverse_helpers_evals_at_r_inv,
        empty,
        empty,
        empty,
        &proof.inverse_helpers_evals_at_r_h,
        empty,
        &proof.preprocessed_individual_evals_at_r_gate_v2,
        &proof.witness_individual_evals_at_r_gate_v2,
        empty,
        empty,
    ];
    let index_points = absorb_claims_and_sample_index_points(
        &mut transcript,
        &claims,
        constituent_index_bits(expected_constituent_width),
    );

    // One packed WHIR vector per group and one linear form per terminal point.
    // Only group/point pairs consumed by terminal equations are equality-fixed;
    // WHIR still verifies all sixteen packed openings in its combined claim.
    let mut expected_evals = vec![None; NUM_PCS_TERMINAL_POINTS * NUM_SPLIT_COMMITMENTS];
    bind_expected_fold(
        &mut expected_evals,
        POINT_COMBINED,
        GROUP_PREPROCESSED,
        &proof.preprocessed_individual_evals,
        expected_constituent_width,
        &index_points[POINT_COMBINED],
    );
    bind_expected_fold(
        &mut expected_evals,
        POINT_COMBINED,
        GROUP_WITNESS,
        &proof.witness_individual_evals,
        expected_constituent_width,
        &index_points[POINT_COMBINED],
    );
    bind_expected_fold(
        &mut expected_evals,
        POINT_COMBINED,
        GROUP_AUXILIARY,
        &[proof.aux_constraint_eval, proof.aux_perm_eval],
        expected_constituent_width,
        &index_points[POINT_COMBINED],
    );
    // Point 1: Phi_inv terminal.
    bind_expected_fold(
        &mut expected_evals,
        POINT_INVERSE,
        GROUP_PREPROCESSED,
        &proof.preprocessed_individual_evals_at_r_inv,
        expected_constituent_width,
        &index_points[POINT_INVERSE],
    );
    bind_expected_fold(
        &mut expected_evals,
        POINT_INVERSE,
        GROUP_WITNESS,
        &proof.witness_individual_evals_at_r_inv,
        expected_constituent_width,
        &index_points[POINT_INVERSE],
    );
    bind_expected_fold(
        &mut expected_evals,
        POINT_INVERSE,
        GROUP_INVERSE_HELPERS,
        &proof.inverse_helpers_evals_at_r_inv,
        expected_constituent_width,
        &index_points[POINT_INVERSE],
    );
    // Point 2: Phi_h terminal.
    bind_expected_fold(
        &mut expected_evals,
        POINT_H,
        GROUP_INVERSE_HELPERS,
        &proof.inverse_helpers_evals_at_r_h,
        expected_constituent_width,
        &index_points[POINT_H],
    );
    // Point 3: Phi_gate terminal.
    bind_expected_fold(
        &mut expected_evals,
        POINT_GATE,
        GROUP_PREPROCESSED,
        &proof.preprocessed_individual_evals_at_r_gate_v2,
        expected_constituent_width,
        &index_points[POINT_GATE],
    );
    bind_expected_fold(
        &mut expected_evals,
        POINT_GATE,
        GROUP_WITNESS,
        &proof.witness_individual_evals_at_r_gate_v2,
        expected_constituent_width,
        &index_points[POINT_GATE],
    );
    let mut actual_bound_claim_mask = [0u8; PACKED_BOUND_CLAIM_MASK.len()];
    for (claim_index, expected_eval) in expected_evals.iter().enumerate() {
        if expected_eval.is_some() {
            actual_bound_claim_mask[claim_index / 8] |= 1 << (claim_index % 8);
        }
    }
    ensure!(
        actual_bound_claim_mask == PACKED_BOUND_CLAIM_MASK,
        "internal packed claim schema mismatch"
    );

    let r_packed = packed_eval_point(&sumcheck_challenges, &index_points[POINT_COMBINED]);
    let r_inv_packed =
        packed_eval_point(&proof.inv_sumcheck_challenges, &index_points[POINT_INVERSE]);
    let r_h_packed = packed_eval_point(&proof.h_sumcheck_challenges, &index_points[POINT_H]);
    let r_gate_v2_packed =
        packed_eval_point(&proof.gate_sumcheck_challenges, &index_points[POINT_GATE]);
    let packed_num_vars = packed_group_num_vars(degree_bits, expected_constituent_width);
    let whir_pcs = WhirPCS::for_constituents_v1(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP);

    let whir_result = whir_pcs.verify_grouped(
        packed_num_vars,
        &proof.whir_eval_proof,
        &expected_evals,
        WHIR_SESSION_SPLIT,
        &[&r_packed, &r_inv_packed, &r_h_packed, &r_gate_v2_packed],
        NUM_SPLIT_COMMITMENTS,
        &[
            &proof.preprocessed_root,
            &proof.witness_root,
            &proof.inverse_helpers_root,
            &proof.aux_commitment_root,
        ],
    );
    ensure!(
        whir_result.is_ok(),
        "WHIR verification failed: {}",
        whir_result.err().unwrap_or_default()
    );

    // WHIR has now fixed the complete constituent matrix used below. The
    // scalar batch identities are retained as transcript-parity and internal
    // consistency checks, not as the PCS binding argument.

    // 5c: Batch consistency — preprocessed at r
    let batch_r_pre = proof.preprocessed_batch_r;
    let mut expected_pre = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.preprocessed_individual_evals {
        expected_pre += r_pow * eval;
        r_pow *= batch_r_pre;
    }
    ensure!(
        expected_pre == proof.preprocessed_eval_value,
        "Preprocessed batch mismatch"
    );

    // 5d: Batch consistency — witness at r
    let mut expected_wit = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.witness_individual_evals {
        expected_wit += r_pow * eval;
        r_pow *= batch_r_wit;
    }
    ensure!(
        expected_wit == proof.witness_eval_value,
        "Witness batch mismatch"
    );

    // 5e: Batch consistency — witness at r_inv
    let mut expected_wit_at_r_inv = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.witness_individual_evals_at_r_inv {
        expected_wit_at_r_inv += r_pow * eval;
        r_pow *= batch_r_wit;
    }
    ensure!(
        expected_wit_at_r_inv == proof.witness_eval_value_at_r_inv,
        "Witness batch mismatch at r_inv"
    );

    // 5f: Batch consistency — preprocessed at r_inv.
    //     Full layout `[const_0..const_C, sigma_0..sigma_R]`. The sigma subset
    //     drives the Φ_inv terminal check; the const subset is unused there
    //     but required to identify the batched value with the WHIR Ext3 binding.
    let mut expected_pre_at_r_inv = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.preprocessed_individual_evals_at_r_inv {
        expected_pre_at_r_inv += r_pow * eval;
        r_pow *= batch_r_pre;
    }
    ensure!(
        expected_pre_at_r_inv == proof.preprocessed_eval_value_at_r_inv,
        "Preprocessed batch mismatch at r_inv"
    );
    let expected_pre_len = proof.num_constants + proof.num_routed_wires;
    ensure!(
        proof.preprocessed_individual_evals_at_r_inv.len() == expected_pre_len,
        "preprocessed_individual_evals_at_r_inv has wrong length"
    );

    // 5g: Inverse helpers batch consistency at r_inv
    ensure!(
        proof.inverse_helpers_evals_at_r_inv.len() == 2 * proof.num_routed_wires,
        "inverse_helpers_evals_at_r_inv has wrong length"
    );
    let mut expected_inv_at_r_inv = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.inverse_helpers_evals_at_r_inv {
        expected_inv_at_r_inv += r_pow * eval;
        r_pow *= proof.inverse_helpers_batch_r;
    }

    // 5h: Inverse helpers batch consistency at r_h
    ensure!(
        proof.inverse_helpers_evals_at_r_h.len() == 2 * proof.num_routed_wires,
        "inverse_helpers_evals_at_r_h has wrong length"
    );
    let mut _expected_inv_at_r_h = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.inverse_helpers_evals_at_r_h {
        _expected_inv_at_r_h += r_pow * eval;
        r_pow *= proof.inverse_helpers_batch_r;
    }
    let _ = expected_inv_at_r_inv; // silence unused-binding warnings (used via WHIR)

    // 5j: Batch consistency — witness at r_gate_v2 (Issue R2-#1).
    ensure!(
        proof.witness_individual_evals_at_r_gate_v2.len() == proof.num_wires,
        "witness_individual_evals_at_r_gate_v2 has wrong length"
    );
    let mut expected_wit_at_r_gate_v2 = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.witness_individual_evals_at_r_gate_v2 {
        expected_wit_at_r_gate_v2 += r_pow * eval;
        r_pow *= batch_r_wit;
    }
    ensure!(
        expected_wit_at_r_gate_v2 == proof.witness_eval_value_at_r_gate_v2,
        "Witness batch mismatch at r_gate_v2"
    );

    // 5k: Batch consistency — preprocessed at r_gate_v2.
    let expected_pre_len_v2 = proof.num_constants + proof.num_routed_wires;
    ensure!(
        proof.preprocessed_individual_evals_at_r_gate_v2.len() == expected_pre_len_v2,
        "preprocessed_individual_evals_at_r_gate_v2 has wrong length"
    );
    let mut expected_pre_at_r_gate_v2 = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &proof.preprocessed_individual_evals_at_r_gate_v2 {
        expected_pre_at_r_gate_v2 += r_pow * eval;
        r_pow *= batch_r_pre;
    }
    ensure!(
        expected_pre_at_r_gate_v2 == proof.preprocessed_eval_value_at_r_gate_v2,
        "Preprocessed batch mismatch at r_gate_v2"
    );

    // 5i: g_sub(r_inv) consistency — verifier recomputes from VK-bound powers.
    let mut expected_g_sub_at_r_inv = F::ONE;
    for (i, &r_i) in proof.inv_sumcheck_challenges.iter().enumerate() {
        let g_pow_i = vk.subgroup_gen_powers[i];
        let factor = (F::ONE - r_i) + r_i * g_pow_i;
        expected_g_sub_at_r_inv *= factor;
    }
    ensure!(
        expected_g_sub_at_r_inv == proof.g_sub_eval_at_r_inv,
        "g_sub(r_inv) mismatch — subgroup MLE evaluation inconsistent"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 6: Final evaluation check
    //
    // C̃(r) and h̃(r) are direct openings of the committed auxiliary group.
    //   - eq(τ,r) and eq(τ_perm,r) computed by verifier from Fiat-Shamir challenges
    //   - μ is a Fiat-Shamir challenge
    //
    // The combined check:
    //   eq(τ,r)·C̃(r) + μ·eq(τ_perm,r)·h̃(r) = final_eval
    //
    // If the prover ran a fake sumcheck, final_eval would be inconsistent
    // with the claimed C̃(r) and h̃(r), and this check fails.
    // ═══════════════════════════════════════════════════════════════════
    // Combined: eq(τ,r)·C̃(r) + μ·h̃(r) = final_eval
    // Note: h term is UNWEIGHTED (no eq_perm) because logUp guarantees Σ h(b) = 0
    // (total sum), not h(b) = 0 at each row.
    let eq_at_r = eq_poly::eq_eval(&tau, &sumcheck_challenges);
    let expected_final = eq_at_r * proof.aux_constraint_eval + mu * proof.aux_perm_eval;

    ensure!(
        expected_final == final_eval,
        "Combined final eval mismatch: \
         eq(τ,r)·C̃(r) + μ·eq(τ_perm,r)·h̃(r) ≠ sumcheck final_eval"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 7 (v2 logUp): Φ_inv terminal check.
    //
    //   inv_final_eval ?= eq(τ_inv, r_inv) · Σ_j λ_inv^j ·
    //                       ( a_j(r_inv) · D_j^id(r_inv) − 1
    //                       + μ_inv · (b_j(r_inv) · D_j^σ(r_inv) − 1) )
    //
    // where D_j^id(r_inv) = β + w_j(r_inv) + γ · K_j · g_sub(r_inv)
    //       D_j^σ(r_inv)  = β + w_j(r_inv) + γ · σ_j(r_inv)
    //
    // The a_j, b_j, w_j and σ_j terms are direct openings of their ordered
    // constituent groups.
    // No 1/x is evaluated by the verifier; the polynomial identity
    // A_j · D_j − 1 = 0 is enforced row-wise by the zero-check sumcheck.
    // ═══════════════════════════════════════════════════════════════════
    let eq_at_r_inv = eq_poly::eq_eval(&tau_inv, &inv_challenges);
    let num_routed = proof.num_routed_wires;
    ensure!(
        proof.witness_individual_evals_at_r_inv.len() == proof.num_wires,
        "witness_individual_evals_at_r_inv has wrong length"
    );

    let mut inv_pred_inner = F::ZERO;
    let mut lambda_pow = F::ONE;
    for j in 0..num_routed {
        let a_j = proof.inverse_helpers_evals_at_r_inv[j];
        let b_j = proof.inverse_helpers_evals_at_r_inv[num_routed + j];
        let w_j = proof.witness_individual_evals_at_r_inv[j];
        // sigma sits after the constants in the preprocessed batch layout.
        let s_j = proof.preprocessed_individual_evals_at_r_inv[proof.num_constants + j];
        let id_j = vk.k_is[j] * proof.g_sub_eval_at_r_inv;
        let denom_id = beta + w_j + gamma * id_j;
        let denom_sigma = beta + w_j + gamma * s_j;
        let z_id = a_j * denom_id - F::ONE;
        let z_sigma = b_j * denom_sigma - F::ONE;
        inv_pred_inner += lambda_pow * (z_id + mu_inv * z_sigma);
        lambda_pow *= lambda_inv;
    }
    let inv_pred = eq_at_r_inv * inv_pred_inner;
    ensure!(
        inv_pred == inv_final_eval,
        "Φ_inv terminal check failed — inverse helpers not consistent with logUp denominators"
    );

    // ═══════════════════════════════════════════════════════════════════
    // Step 8 (v2 logUp): Φ_h terminal check.
    //   h_final_eval ?= Σ_j ( a_j(r_h) − b_j(r_h) )
    // (no eq weight — claimed sum 0 is unweighted)
    // ═══════════════════════════════════════════════════════════════════
    ensure!(
        proof.inverse_helpers_evals_at_r_h.len() == 2 * num_routed,
        "inverse_helpers_evals_at_r_h has wrong length"
    );
    let mut h_pred = F::ZERO;
    for j in 0..num_routed {
        let a_j = proof.inverse_helpers_evals_at_r_h[j];
        let b_j = proof.inverse_helpers_evals_at_r_h[num_routed + j];
        h_pred += a_j - b_j;
    }
    ensure!(
        h_pred == h_final_eval,
        "Φ_h terminal check failed — H = Σ_j (A_j − B_j) inconsistent at r_h"
    );
    // ═══════════════════════════════════════════════════════════════════
    // Step 9 (v2 gate binding — Issue R2-#1): Φ_gate terminal check.
    //
    //   gate_final_eval ?= eq(τ_gate, r_gate_v2) · flatten_ext(
    //       Σ_j α^j · c_j(lift(W_k(r_gate_v2)), lift(const_k(r_gate_v2))),
    //       ext_challenge
    //   )
    //
    // The Plonky2 gate evaluator is invoked at the sumcheck output point
    // with claimed wire/const evaluations. Because all inputs are
    // multilinear extensions and the gate formula is a polynomial with
    // the same coefficients at Boolean inputs and at arbitrary field
    // points, this check binds the commitment to the ACTUAL gate formula
    // and not merely to the MLE of its row-wise values. This closes the
    // soundness gap for gates of degree ≥ 2 (ArithmeticGate, PoseidonGate,
    // …) that made the legacy `aux_constraint_eval` oracle insufficient.
    //
    // SECURITY:
    //   - α, ext_challenge, τ_gate are Fiat-Shamir challenges squeezed
    //     after all wire/const commitments.
    //   - Wire/const individual evals at r_gate_v2 are direct grouped-WHIR
    //     openings.
    //   - public_inputs_hash is recomputed from the transcript-bound public
    //     inputs before any protocol verification.
    // ═══════════════════════════════════════════════════════════════════
    ensure!(
        proof.witness_individual_evals_at_r_gate_v2.len() == proof.num_wires,
        "witness_individual_evals_at_r_gate_v2 has wrong length for gate evaluator"
    );
    ensure!(
        proof.preprocessed_individual_evals_at_r_gate_v2.len()
            == common_data.num_constants + common_data.config.num_routed_wires,
        "preprocessed_individual_evals_at_r_gate_v2 has wrong length"
    );
    let local_wires_ext: Vec<F::Extension> = proof
        .witness_individual_evals_at_r_gate_v2
        .iter()
        .take(common_data.config.num_wires)
        .map(|&f| F::Extension::from_basefield(f))
        .collect();
    let local_constants_ext: Vec<F::Extension> = proof
        .preprocessed_individual_evals_at_r_gate_v2
        .iter()
        .take(common_data.num_constants)
        .map(|&f| F::Extension::from_basefield(f))
        .collect();

    let vars = EvaluationVars {
        local_constants: &local_constants_ext,
        local_wires: &local_wires_ext,
        public_inputs_hash: &proof.public_inputs_hash,
    };
    let constraint_values = evaluate_gate_constraints(common_data, vars);

    let alpha_ext = F::Extension::from_basefield(alpha);
    let mut combined_ext = F::Extension::ZERO;
    let mut alpha_pow = F::Extension::ONE;
    for &cv in &constraint_values {
        combined_ext += alpha_pow * cv;
        alpha_pow *= alpha_ext;
    }

    // Flatten extension components with ext_challenge powers.
    let components = combined_ext.to_basefield_array();
    let mut flat = F::ZERO;
    let mut ext_pow = F::ONE;
    for &c in components.iter() {
        flat += ext_pow * c;
        ext_pow *= ext_challenge;
    }

    let eq_at_r_gate_v2 = eq_poly::eq_eval(&tau_gate, &gate_challenges);
    let pred = eq_at_r_gate_v2 * flat;
    ensure!(
        pred == gate_final_eval,
        "Φ_gate terminal check failed — wire/const evals at r_gate_v2 are \
         not consistent with the gate constraint formula"
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use plonky2::iop::witness::{PartialWitness, WitnessWrite};
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::PoseidonGoldilocksConfig;
    use plonky2::util::timing::TimingTree;
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::Field;

    use super::*;
    use crate::prover::{mle_prove, mle_setup};

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    fn build_mul_circuit() -> (
        plonky2::plonk::circuit_data::ProverOnlyCircuitData<F, C, D>,
        plonky2::plonk::circuit_data::CommonCircuitData<F, D>,
        plonky2::iop::target::Target,
        plonky2::iop::target::Target,
    ) {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.add_virtual_target();
        let y = builder.add_virtual_target();
        let z = builder.mul(x, y);
        builder.register_public_input(z);
        let circuit = builder.build::<C>();
        (circuit.prover_only, circuit.common, x, y)
    }

    #[test]
    fn test_prove_verify_roundtrip() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);

        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(3)).unwrap();
        pw.set_target(y, F::from_canonical_u64(7)).unwrap();

        let mut timing = TimingTree::default();
        let proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();

        let result = mle_verify::<F, D>(&common_data, &vk, &proof);
        assert!(result.is_ok(), "Verification failed: {:?}", result.err());
    }

    #[test]
    fn test_tampered_preprocessed_root_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);

        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(5)).unwrap();
        pw.set_target(y, F::from_canonical_u64(11)).unwrap();

        let mut timing = TimingTree::default();
        let mut proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();

        if !proof.preprocessed_root.is_empty() {
            proof.preprocessed_root[0] ^= 0xFF;
        }

        let result = mle_verify::<F, D>(&common_data, &vk, &proof);
        assert!(result.is_err(), "Tampered root should be rejected");
    }

    #[test]
    fn test_cross_circuit_proof_rejected() {
        let (prover_data_a, common_data_a, x_a, y_a) = build_mul_circuit();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder_b = CircuitBuilder::<F, D>::new(config);
        let x_b = builder_b.add_virtual_target();
        let y_b = builder_b.add_virtual_target();
        let z_b = builder_b.add(x_b, y_b);
        builder_b.register_public_input(z_b);
        let circuit_b = builder_b.build::<C>();
        let vk_b = mle_setup::<F, C, D>(&circuit_b.prover_only, &circuit_b.common);

        let mut pw_a = PartialWitness::new();
        pw_a.set_target(x_a, F::from_canonical_u64(3)).unwrap();
        pw_a.set_target(y_a, F::from_canonical_u64(7)).unwrap();

        let mut timing = TimingTree::default();
        let proof_a =
            mle_prove::<F, C, D>(&prover_data_a, &common_data_a, pw_a, &mut timing).unwrap();

        let result = mle_verify::<F, D>(&common_data_a, &vk_b, &proof_a);
        assert!(result.is_err(), "Cross-circuit proof should be rejected");
    }

    /// Issue R2-#1: tampering with the witness individual evals at `r_gate_v2`
    /// must be rejected by the Φ_gate terminal check — this is exactly the
    /// attack surface that motivated the v2 gate binding fix.
    ///
    /// Before R2-#1, a prover could commit `C̃ ≡ 0` to WHIR and pass the
    /// legacy `eq(τ,r)·C̃(r) == final_eval` check. Now the verifier calls
    /// `evaluate_gate_constraints` at `r_gate_v2` with PCS-bound wire evals,
    /// so any inconsistency between claimed witness evals and the actual
    /// polynomial (including fabricated evals) is caught.
    #[test]
    fn test_tampered_witness_evals_at_r_gate_v2_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);

        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(3)).unwrap();
        pw.set_target(y, F::from_canonical_u64(7)).unwrap();

        let mut timing = TimingTree::default();
        let mut proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();

        // Sanity: an untampered proof verifies.
        let ok = mle_verify::<F, D>(&common_data, &vk, &proof);
        assert!(ok.is_ok(), "Baseline proof must verify: {:?}", ok.err());

        // Flip a wire evaluation at r_gate_v2 — this should break the
        // Φ_gate terminal check (batch-consistency check triggers first in
        // practice, but either way verification must be rejected).
        proof.witness_individual_evals_at_r_gate_v2[0] += F::ONE;

        let result = mle_verify::<F, D>(&common_data, &vk, &proof);
        assert!(
            result.is_err(),
            "Tampered witness evals at r_gate_v2 must be rejected"
        );
    }

    /// Issue R2-#1: tampering with the Φ_gate sumcheck proof itself (the
    /// fake-sumcheck attack) must be caught by the round-poly consistency
    /// check in `verify_sumcheck`.
    #[test]
    fn test_tampered_gate_sumcheck_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);

        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(2)).unwrap();
        pw.set_target(y, F::from_canonical_u64(3)).unwrap();

        let mut timing = TimingTree::default();
        let mut proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();

        // Corrupt the first round polynomial of Φ_gate.
        if let Some(rp) = proof.gate_sumcheck_proof.round_polys.first_mut() {
            rp.evaluations[0] += F::ONE;
        }

        let result = mle_verify::<F, D>(&common_data, &vk, &proof);
        assert!(
            result.is_err(),
            "Tampered Φ_gate sumcheck round poly must be rejected"
        );
    }

    /// Issue R2-#1: a preprocessed constant evaluation at `r_gate_v2` is a
    /// direct input to `evaluate_gate_constraints` inside the terminal
    /// check. Tampering must be rejected.
    #[test]
    fn test_tampered_const_evals_at_r_gate_v2_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);

        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(4)).unwrap();
        pw.set_target(y, F::from_canonical_u64(9)).unwrap();

        let mut timing = TimingTree::default();
        let mut proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();

        if common_data.num_constants > 0 {
            proof.preprocessed_individual_evals_at_r_gate_v2[0] += F::ONE;
            let result = mle_verify::<F, D>(&common_data, &vk, &proof);
            assert!(
                result.is_err(),
                "Tampered const eval at r_gate_v2 must be rejected"
            );
        }
    }

    fn batch_eval(values: &[F], rho: F) -> F {
        let mut result = F::ZERO;
        let mut power = F::ONE;
        for value in values {
            result += power * *value;
            power *= rho;
        }
        result
    }

    fn inv_terminal_inner(proof: &MleProof<F>, vk: &MleVerificationKey<F>) -> F {
        let nr = proof.num_routed_wires;
        let mut result = F::ZERO;
        let mut lambda_power = F::ONE;
        for j in 0..nr {
            let wire = proof.witness_individual_evals_at_r_inv[j];
            let denom_id = proof.beta + wire + proof.gamma * vk.k_is[j] * proof.g_sub_eval_at_r_inv;
            let denom_sigma = proof.beta
                + wire
                + proof.gamma
                    * proof.preprocessed_individual_evals_at_r_inv[proof.num_constants + j];
            let z_id = proof.inverse_helpers_evals_at_r_inv[j] * denom_id - F::ONE;
            let z_sigma = proof.inverse_helpers_evals_at_r_inv[nr + j] * denom_sigma - F::ONE;
            result += lambda_power * (z_id + proof.mu_inv * z_sigma);
            lambda_power *= proof.lambda_inv;
        }
        result
    }

    fn h_terminal_inner(proof: &MleProof<F>) -> F {
        let nr = proof.num_routed_wires;
        (0..nr).fold(F::ZERO, |acc, j| {
            acc + proof.inverse_helpers_evals_at_r_h[j] - proof.inverse_helpers_evals_at_r_h[nr + j]
        })
    }

    fn combined_terminal_inner(proof: &MleProof<F>) -> F {
        eq_poly::eq_eval(&proof.tau, &proof.sumcheck_challenges) * proof.aux_constraint_eval
            + proof.mu * proof.aux_perm_eval
    }

    fn gate_terminal_flat(common_data: &CommonCircuitData<F, D>, proof: &MleProof<F>) -> F {
        type FE = <F as Extendable<D>>::Extension;
        let local_wires_ext: Vec<FE> = proof
            .witness_individual_evals_at_r_gate_v2
            .iter()
            .copied()
            .map(<FE as FieldExtension<D>>::from_basefield)
            .collect();
        let local_constants_ext: Vec<FE> = proof
            .preprocessed_individual_evals_at_r_gate_v2
            .iter()
            .take(common_data.num_constants)
            .copied()
            .map(<FE as FieldExtension<D>>::from_basefield)
            .collect();
        let vars = EvaluationVars {
            local_constants: &local_constants_ext,
            local_wires: &local_wires_ext,
            public_inputs_hash: &proof.public_inputs_hash,
        };
        let constraints = evaluate_gate_constraints(common_data, vars);
        let alpha_ext = <FE as FieldExtension<D>>::from_basefield(proof.alpha);
        let mut combined_ext = FE::ZERO;
        let mut alpha_power = FE::ONE;
        for constraint in constraints {
            combined_ext += alpha_power * constraint;
            alpha_power *= alpha_ext;
        }
        let mut flat = F::ZERO;
        let mut extension_power = F::ONE;
        for component in <FE as FieldExtension<D>>::to_basefield_array(&combined_ext) {
            flat += extension_power * component;
            extension_power *= proof.ext_challenge;
        }
        flat
    }

    fn sumcheck_evaluations(proof: &crate::sumcheck::types::SumcheckProof<F>) -> Vec<Vec<F>> {
        proof
            .round_polys
            .iter()
            .map(|round| round.evaluations.clone())
            .collect()
    }

    /// The generalized attacks are allowed to alter only constituent claims
    /// (and, for the two-coordinate auxiliary compensation, its redundant
    /// legacy scalar aggregate). Everything authenticated by the old proof is
    /// held byte/value exact so a rejection below is attributable to packed
    /// PCS binding rather than a changed sumcheck or public statement.
    fn assert_attack_artifacts_unchanged(original: &MleProof<F>, attack: &MleProof<F>) {
        assert_eq!(attack.protocol_version, original.protocol_version);
        assert_eq!(attack.constituent_width, original.constituent_width);
        assert_eq!(attack.circuit_digest, original.circuit_digest);
        assert_eq!(attack.preprocessed_root, original.preprocessed_root);
        assert_eq!(attack.witness_root, original.witness_root);
        assert_eq!(attack.inverse_helpers_root, original.inverse_helpers_root);
        assert_eq!(attack.aux_commitment_root, original.aux_commitment_root);
        assert_eq!(
            attack.whir_eval_proof.narg_string,
            original.whir_eval_proof.narg_string
        );
        assert_eq!(attack.whir_eval_proof.hints, original.whir_eval_proof.hints);
        assert_eq!(attack.public_inputs, original.public_inputs);
        assert_eq!(attack.public_inputs_hash, original.public_inputs_hash);
        assert_eq!(attack.sumcheck_challenges, original.sumcheck_challenges);
        assert_eq!(
            attack.inv_sumcheck_challenges,
            original.inv_sumcheck_challenges
        );
        assert_eq!(attack.h_sumcheck_challenges, original.h_sumcheck_challenges);
        assert_eq!(
            attack.gate_sumcheck_challenges,
            original.gate_sumcheck_challenges
        );
        assert_eq!(
            sumcheck_evaluations(&attack.combined_proof),
            sumcheck_evaluations(&original.combined_proof)
        );
        assert_eq!(
            sumcheck_evaluations(&attack.inv_sumcheck_proof),
            sumcheck_evaluations(&original.inv_sumcheck_proof)
        );
        assert_eq!(
            sumcheck_evaluations(&attack.h_sumcheck_proof),
            sumcheck_evaluations(&original.h_sumcheck_proof)
        );
        assert_eq!(
            sumcheck_evaluations(&attack.gate_sumcheck_proof),
            sumcheck_evaluations(&original.gate_sumcheck_proof)
        );
    }

    fn assert_pcs_rejects(
        label: &str,
        common_data: &CommonCircuitData<F, D>,
        vk: &MleVerificationKey<F>,
        original: &MleProof<F>,
        attack: &MleProof<F>,
    ) {
        assert_attack_artifacts_unchanged(original, attack);
        let error = mle_verify::<F, D>(common_data, vk, attack)
            .expect_err("terminal-preserving forgery unexpectedly verified")
            .to_string();
        assert!(
            error.contains("WHIR verification failed"),
            "{label} was rejected before the PCS boundary: {error}"
        );
    }

    /// Freeze the exact arithmetic identities used by the historical
    /// `small_mul` v0 witness/inverse forgery. The regenerated v1 fixture has
    /// different randomized unused-wire evaluations, so this model is kept
    /// separate from the proof-dependent v1 rejection test below.
    #[test]
    fn test_frozen_small_mul_v0_kernel_constants() {
        let w0_before = F::from_canonical_u64(3_051_498_664_030_569_048);
        let w0_after = F::from_canonical_u64(3_051_498_664_030_569_049);
        let w80_before = F::from_canonical_u64(6_063_719_204_085_150_528);
        let w80_after = F::from_canonical_u64(2_587_698_932_769_584_699);
        let a1_before = F::from_canonical_u64(7_495_656_216_612_080_666);
        let a1_after = F::from_canonical_u64(14_584_819_668_673_277_578);
        let rho = F::from_canonical_u64(4_731_229_214_337_826_042);

        assert_eq!(w0_after - w0_before, F::ONE);
        let witness_batch_delta =
            (w0_after - w0_before) + rho.exp_u64(80) * (w80_after - w80_before);
        assert_eq!(witness_batch_delta, F::ZERO);

        let beta = F::from_canonical_u64(17_800_375_341_204_939_063);
        let gamma = F::from_canonical_u64(9_041_901_820_383_133_626);
        let lambda_inv = F::from_canonical_u64(16_769_653_635_246_974_393);
        let mu_inv = F::from_canonical_u64(11_315_289_580_255_226_170);
        let k1 = F::from_canonical_u64(14_293_326_489_335_486_720);
        let g_sub = F::from_canonical_u64(11_042_185_228_133_710_199);
        let w1 = F::from_canonical_u64(78_509_372_807_566_819);
        let a0 = F::from_canonical_u64(16_828_114_539_042_804_903);
        let b0 = F::from_canonical_u64(13_178_207_313_111_168_954);
        let denom_id_1 = beta + w1 + gamma * k1 * g_sub;
        assert_eq!(
            denom_id_1,
            F::from_canonical_u64(10_367_067_124_889_157_128)
        );
        let changed_wire_delta = a0 + mu_inv * b0;
        let compensating_helper_delta = lambda_inv * denom_id_1 * (a1_after - a1_before);
        assert_eq!(
            changed_wire_delta,
            F::from_canonical_u64(1_813_035_432_707_231_050)
        );
        assert_eq!(
            compensating_helper_delta,
            F::from_canonical_u64(16_633_708_636_707_353_271)
        );
        let terminal_delta = changed_wire_delta + compensating_helper_delta;
        assert_eq!(terminal_delta, F::ZERO);
    }

    /// Freeze the exact arithmetic kernel from the parent validity fixture.
    /// The retired v0 proof uses a different schema, so proof-dependent packed
    /// v1 rejection is covered by the generalized test rather than by trying
    /// to reinterpret those old proof bytes.
    #[test]
    fn test_frozen_parent_validity_v0_kernel_constants() {
        let w0_before = F::from_canonical_u64(8_093_513_556_413_711_660);
        let w0_after = F::from_canonical_u64(8_093_513_556_413_711_661);
        let w80_before = F::from_canonical_u64(2_800_508_231_593_448_274);
        let w80_after = F::from_canonical_u64(15_862_999_140_234_155_880);
        let a1_before = F::from_canonical_u64(17_516_173_920_822_186_472);
        let a1_after = F::from_canonical_u64(6_112_368_312_529_039_975);
        let rho = F::from_canonical_u64(6_145_656_649_326_269_386);

        assert_eq!(w0_after - w0_before, F::ONE);
        let witness_batch_delta =
            (w0_after - w0_before) + rho.exp_u64(80) * (w80_after - w80_before);
        assert_eq!(witness_batch_delta, F::ZERO);

        let beta = F::from_canonical_u64(18_087_660_371_601_274_625);
        let gamma = F::from_canonical_u64(10_481_604_735_508_439_039);
        let lambda_inv = F::from_canonical_u64(1_097_435_823_362_543_930);
        let mu_inv = F::from_canonical_u64(171_987_289_746_320_364);
        let k1 = F::from_canonical_u64(14_293_326_489_335_486_720);
        let g_sub = F::from_canonical_u64(13_562_199_838_588_320_182);
        let w1 = F::from_canonical_u64(12_819_036_921_327_938_012);
        let a0 = F::from_canonical_u64(9_601_097_877_492_032_537);
        let b0 = F::from_canonical_u64(8_488_046_535_134_267_022);
        let denom_id_1 = beta + w1 + gamma * k1 * g_sub;
        let terminal_delta = a0 + mu_inv * b0 + lambda_inv * denom_id_1 * (a1_after - a1_before);
        assert_eq!(terminal_delta, F::ZERO);
    }

    /// Recreate the historical witness/inverse batching-kernel attack against
    /// the current challenges. The legacy scalar batch and complete Phi_inv
    /// terminal value remain unchanged; grouped WHIR is the rejecting check.
    #[test]
    fn test_generalized_same_chain_kernel_forgery_is_pcs_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);
        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(3)).unwrap();
        pw.set_target(y, F::from_canonical_u64(7)).unwrap();
        let mut timing = TimingTree::default();
        let mut proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();
        mle_verify::<F, D>(&common_data, &vk, &proof).expect("honest proof");

        let original_batch = batch_eval(
            &proof.witness_individual_evals_at_r_inv,
            proof.witness_batch_r,
        );
        let original_terminal = inv_terminal_inner(&proof, &vk);
        let roots = (
            proof.witness_root.clone(),
            proof.inverse_helpers_root.clone(),
        );
        let whir_bytes = (
            proof.whir_eval_proof.narg_string.clone(),
            proof.whir_eval_proof.hints.clone(),
        );

        let cancellation_index = proof.num_routed_wires;
        assert!(cancellation_index < proof.num_wires);
        let rho_n = proof.witness_batch_r.exp_u64(cancellation_index as u64);
        proof.witness_individual_evals_at_r_inv[0] += F::ONE;
        proof.witness_individual_evals_at_r_inv[cancellation_index] -= rho_n.inverse();

        let nr = proof.num_routed_wires;
        let numerator = proof.inverse_helpers_evals_at_r_inv[0]
            + proof.mu_inv * proof.inverse_helpers_evals_at_r_inv[nr];
        let denom_id_1 = proof.beta
            + proof.witness_individual_evals_at_r_inv[1]
            + proof.gamma * vk.k_is[1] * proof.g_sub_eval_at_r_inv;
        proof.inverse_helpers_evals_at_r_inv[1] -=
            numerator * (proof.lambda_inv * denom_id_1).inverse();

        assert_eq!(
            batch_eval(
                &proof.witness_individual_evals_at_r_inv,
                proof.witness_batch_r
            ),
            original_batch
        );
        assert_eq!(inv_terminal_inner(&proof, &vk), original_terminal);
        assert_eq!(proof.witness_root, roots.0);
        assert_eq!(proof.inverse_helpers_root, roots.1);
        assert_eq!(proof.whir_eval_proof.narg_string, whir_bytes.0);
        assert_eq!(proof.whir_eval_proof.hints, whir_bytes.1);
        assert!(
            mle_verify::<F, D>(&common_data, &vk, &proof).is_err(),
            "kernel forgery must be rejected by direct PCS openings"
        );
    }

    /// Exercise every one of the nine point/group cells consumed by an outer
    /// terminal equation. Each mutation is computed from this proof's own
    /// challenges, preserves the legacy scalar and terminal equations, and
    /// leaves roots, WHIR bytes, sumchecks, and public inputs unchanged. The
    /// packed constituent opening must therefore be the rejecting boundary.
    #[test]
    fn test_generalized_terminal_kernel_matrix_is_pcs_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);
        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(3)).unwrap();
        pw.set_target(y, F::from_canonical_u64(7)).unwrap();
        let mut timing = TimingTree::default();
        let proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();
        mle_verify::<F, D>(&common_data, &vk, &proof).expect("honest proof");

        // Point 0 / preprocessed: a two-coordinate kernel of the retained
        // scalar batch. This group does not enter the combined terminal.
        let mut attack = proof.clone();
        let original_batch = batch_eval(
            &attack.preprocessed_individual_evals,
            attack.preprocessed_batch_r,
        );
        attack.preprocessed_individual_evals[0] += attack.preprocessed_batch_r;
        attack.preprocessed_individual_evals[1] -= F::ONE;
        assert_eq!(
            batch_eval(
                &attack.preprocessed_individual_evals,
                attack.preprocessed_batch_r
            ),
            original_batch
        );
        assert_pcs_rejects("point 0 / preprocessed", &common_data, &vk, &proof, &attack);

        // Point 0 / witness: the same proof-dependent batch kernel in the
        // witness group; no combined-terminal input is changed.
        let mut attack = proof.clone();
        let original_batch = batch_eval(&attack.witness_individual_evals, attack.witness_batch_r);
        attack.witness_individual_evals[0] += attack.witness_batch_r;
        attack.witness_individual_evals[1] -= F::ONE;
        assert_eq!(
            batch_eval(&attack.witness_individual_evals, attack.witness_batch_r),
            original_batch
        );
        assert_pcs_rejects("point 0 / witness", &common_data, &vk, &proof, &attack);

        // Point 0 / auxiliary: preserve eq(tau,r)*C + mu*h exactly, and
        // update the legacy aggregate so C + rho_aux*h = aux_eval still
        // holds. With aux_eval itself fixed these two independent equations
        // have only the zero solution; record the nonzero determinant so that
        // limitation of the requested kernel matrix is explicit.
        let mut attack = proof.clone();
        let original_terminal = combined_terminal_inner(&attack);
        let eq_at_r = eq_poly::eq_eval(&attack.tau, &attack.sumcheck_challenges);
        let determinant = attack.mu - eq_at_r * attack.aux_batch_r;
        assert_ne!(
            determinant,
            F::ZERO,
            "fixture accidentally admits a fixed-aux-aggregate kernel"
        );
        attack.aux_constraint_eval += attack.mu;
        attack.aux_perm_eval -= eq_at_r;
        attack.aux_eval_value =
            attack.aux_constraint_eval + attack.aux_batch_r * attack.aux_perm_eval;
        assert_eq!(combined_terminal_inner(&attack), original_terminal);
        assert_ne!(attack.aux_eval_value, proof.aux_eval_value);
        assert_pcs_rejects("point 0 / auxiliary", &common_data, &vk, &proof, &attack);

        // Point 1 / preprocessed: alter sigma_0, cancel its retained batch
        // contribution through constant_0, then cancel its Phi_inv effect
        // through A_1.
        let mut attack = proof.clone();
        let original_batch = batch_eval(
            &attack.preprocessed_individual_evals_at_r_inv,
            attack.preprocessed_batch_r,
        );
        let original_terminal = inv_terminal_inner(&attack, &vk);
        let sigma_0 = attack.num_constants;
        attack.preprocessed_individual_evals_at_r_inv[sigma_0] += F::ONE;
        attack.preprocessed_individual_evals_at_r_inv[0] -=
            attack.preprocessed_batch_r.exp_u64(sigma_0 as u64);
        let terminal_after_sigma = inv_terminal_inner(&attack, &vk);
        let denom_id_1 = attack.beta
            + attack.witness_individual_evals_at_r_inv[1]
            + attack.gamma * vk.k_is[1] * attack.g_sub_eval_at_r_inv;
        let compensation_coefficient = attack.lambda_inv * denom_id_1;
        assert_ne!(compensation_coefficient, F::ZERO);
        attack.inverse_helpers_evals_at_r_inv[1] +=
            (original_terminal - terminal_after_sigma) * compensation_coefficient.inverse();
        assert_eq!(
            batch_eval(
                &attack.preprocessed_individual_evals_at_r_inv,
                attack.preprocessed_batch_r
            ),
            original_batch
        );
        assert_eq!(inv_terminal_inner(&attack, &vk), original_terminal);
        assert_pcs_rejects("point 1 / preprocessed", &common_data, &vk, &proof, &attack);

        // Point 1 / witness: recreate the historical cross-group kernel from
        // the live proof. An unrouted witness coordinate preserves the batch,
        // while A_1 restores the complete Phi_inv value.
        let mut attack = proof.clone();
        let original_batch = batch_eval(
            &attack.witness_individual_evals_at_r_inv,
            attack.witness_batch_r,
        );
        let original_terminal = inv_terminal_inner(&attack, &vk);
        let unused_wire = attack.num_routed_wires;
        let unused_weight = attack.witness_batch_r.exp_u64(unused_wire as u64);
        attack.witness_individual_evals_at_r_inv[0] += F::ONE;
        attack.witness_individual_evals_at_r_inv[unused_wire] -= unused_weight.inverse();
        let terminal_after_witness = inv_terminal_inner(&attack, &vk);
        let denom_id_1 = attack.beta
            + attack.witness_individual_evals_at_r_inv[1]
            + attack.gamma * vk.k_is[1] * attack.g_sub_eval_at_r_inv;
        let compensation_coefficient = attack.lambda_inv * denom_id_1;
        assert_ne!(compensation_coefficient, F::ZERO);
        attack.inverse_helpers_evals_at_r_inv[1] +=
            (original_terminal - terminal_after_witness) * compensation_coefficient.inverse();
        assert_eq!(
            batch_eval(
                &attack.witness_individual_evals_at_r_inv,
                attack.witness_batch_r
            ),
            original_batch
        );
        assert_eq!(inv_terminal_inner(&attack, &vk), original_terminal);
        assert_pcs_rejects("point 1 / witness", &common_data, &vk, &proof, &attack);

        // Point 1 / inverse helpers: A_0 and A_1 form a direct kernel of the
        // single Phi_inv terminal equation.
        let mut attack = proof.clone();
        let original_terminal = inv_terminal_inner(&attack, &vk);
        attack.inverse_helpers_evals_at_r_inv[0] += F::ONE;
        let terminal_after_a0 = inv_terminal_inner(&attack, &vk);
        let denom_id_1 = attack.beta
            + attack.witness_individual_evals_at_r_inv[1]
            + attack.gamma * vk.k_is[1] * attack.g_sub_eval_at_r_inv;
        let compensation_coefficient = attack.lambda_inv * denom_id_1;
        assert_ne!(compensation_coefficient, F::ZERO);
        attack.inverse_helpers_evals_at_r_inv[1] +=
            (original_terminal - terminal_after_a0) * compensation_coefficient.inverse();
        assert_eq!(inv_terminal_inner(&attack, &vk), original_terminal);
        assert_pcs_rejects("point 1 / inverse", &common_data, &vk, &proof, &attack);

        // Point 2 / inverse helpers: equal A_0/B_0 deltas preserve H=sum(A-B).
        let mut attack = proof.clone();
        let original_terminal = h_terminal_inner(&attack);
        let nr = attack.num_routed_wires;
        attack.inverse_helpers_evals_at_r_h[0] += F::ONE;
        attack.inverse_helpers_evals_at_r_h[nr] += F::ONE;
        assert_eq!(h_terminal_inner(&attack), original_terminal);
        assert_pcs_rejects("point 2 / inverse", &common_data, &vk, &proof, &attack);

        // Point 3 / preprocessed: sigma columns are deliberately ignored by
        // the gate formula, but are still in the exact packed claim. A batch
        // kernel over sigma_0/sigma_1 therefore preserves both old checks.
        let mut attack = proof.clone();
        let original_batch = batch_eval(
            &attack.preprocessed_individual_evals_at_r_gate_v2,
            attack.preprocessed_batch_r,
        );
        let original_terminal = gate_terminal_flat(&common_data, &attack);
        let sigma_0 = attack.num_constants;
        let sigma_1 = sigma_0 + 1;
        attack.preprocessed_individual_evals_at_r_gate_v2[sigma_0] += attack.preprocessed_batch_r;
        attack.preprocessed_individual_evals_at_r_gate_v2[sigma_1] -= F::ONE;
        assert_eq!(
            batch_eval(
                &attack.preprocessed_individual_evals_at_r_gate_v2,
                attack.preprocessed_batch_r
            ),
            original_batch
        );
        assert_eq!(gate_terminal_flat(&common_data, &attack), original_terminal);
        assert_pcs_rejects("point 3 / preprocessed", &common_data, &vk, &proof, &attack);

        // Point 3 / witness: wires 15, 19 and 23 are linear outputs in both
        // small_mul gate families that consume them. The cross product of the
        // live batch and gate coefficient rows is a nonzero simultaneous
        // kernel, without relying on hard-coded challenge values.
        let mut attack = proof.clone();
        let original_batch = batch_eval(
            &attack.witness_individual_evals_at_r_gate_v2,
            attack.witness_batch_r,
        );
        let original_terminal = gate_terminal_flat(&common_data, &attack);
        let indices = [15usize, 19, 23];
        assert!(attack.witness_individual_evals_at_r_gate_v2.len() > indices[2]);
        let batch_coefficients = indices.map(|index| attack.witness_batch_r.exp_u64(index as u64));
        let mut gate_coefficients = [F::ZERO; 3];
        for (coefficient, &index) in gate_coefficients.iter_mut().zip(&indices) {
            attack.witness_individual_evals_at_r_gate_v2[index] += F::ONE;
            *coefficient = gate_terminal_flat(&common_data, &attack) - original_terminal;
            attack.witness_individual_evals_at_r_gate_v2[index] -= F::ONE;
        }
        let deltas = [
            batch_coefficients[1] * gate_coefficients[2]
                - batch_coefficients[2] * gate_coefficients[1],
            batch_coefficients[2] * gate_coefficients[0]
                - batch_coefficients[0] * gate_coefficients[2],
            batch_coefficients[0] * gate_coefficients[1]
                - batch_coefficients[1] * gate_coefficients[0],
        ];
        assert!(deltas.iter().any(|&delta| delta != F::ZERO));
        for (&index, &delta) in indices.iter().zip(&deltas) {
            attack.witness_individual_evals_at_r_gate_v2[index] += delta;
        }
        assert_eq!(
            batch_eval(
                &attack.witness_individual_evals_at_r_gate_v2,
                attack.witness_batch_r
            ),
            original_batch
        );
        assert_eq!(gate_terminal_flat(&common_data, &attack), original_terminal);
        assert_pcs_rejects("point 3 / witness", &common_data, &vk, &proof, &attack);
    }

    #[test]
    fn test_version_schema_and_vk_context_mutations_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);
        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(5)).unwrap();
        pw.set_target(y, F::from_canonical_u64(9)).unwrap();
        let mut timing = TimingTree::default();
        let proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();

        let mut old_version = proof.clone();
        old_version.protocol_version = 0;
        assert!(mle_verify::<F, D>(&common_data, &vk, &old_version).is_err());

        // A current proof must not verify against a stale v0 VK, even though
        // all proof-carried fields and commitment bytes remain current.
        let mut old_vk = vk.clone();
        old_vk.protocol_version = 0;
        assert!(mle_verify::<F, D>(&common_data, &old_vk, &proof).is_err());

        let mut wrong_width = proof.clone();
        wrong_width.constituent_width -= 1;
        assert!(mle_verify::<F, D>(&common_data, &vk, &wrong_width).is_err());

        let mut wrong_vk_width = vk.clone();
        wrong_vk_width.constituent_width -= 1;
        assert!(mle_verify::<F, D>(&common_data, &wrong_vk_width, &proof).is_err());

        let mut wrong_vk_root = vk.clone();
        wrong_vk_root.preprocessed_commitment_root[0] ^= 1;
        assert!(mle_verify::<F, D>(&common_data, &wrong_vk_root, &proof).is_err());

        let mut wrong_k = proof.clone();
        wrong_k.k_is[0] += F::ONE;
        assert!(mle_verify::<F, D>(&common_data, &vk, &wrong_k).is_err());

        let mut wrong_public_hash = proof.clone();
        wrong_public_hash.public_inputs_hash.elements[0] += F::ONE;
        assert!(mle_verify::<F, D>(&common_data, &vk, &wrong_public_hash).is_err());

        let mut unexpected_lookup = proof.clone();
        unexpected_lookup
            .lookup_proofs
            .push(crate::permutation::lookup::LookupProof {
                sumcheck_proof: crate::sumcheck::types::SumcheckProof {
                    round_polys: vec![],
                },
                challenges: vec![],
                claimed_sum: F::ZERO,
            });
        assert!(mle_verify::<F, D>(&common_data, &vk, &unexpected_lookup).is_err());

        let mut wrong_subgroup = proof;
        wrong_subgroup.subgroup_gen_powers[0] += F::ONE;
        assert!(mle_verify::<F, D>(&common_data, &vk, &wrong_subgroup).is_err());
    }

    #[test]
    fn test_sumcheck_round_and_coefficient_tails_rejected() {
        let (prover_data, common_data, x, y) = build_mul_circuit();
        let vk = mle_setup::<F, C, D>(&prover_data, &common_data);
        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(5)).unwrap();
        pw.set_target(y, F::from_canonical_u64(9)).unwrap();
        let mut timing = TimingTree::default();
        let proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();
        mle_verify::<F, D>(&common_data, &vk, &proof).expect("honest proof");

        let mut extra_round = proof.clone();
        let trailing_round = extra_round.combined_proof.round_polys[0].clone();
        extra_round.combined_proof.round_polys.push(trailing_round);
        assert!(
            mle_verify::<F, D>(&common_data, &vk, &extra_round).is_err(),
            "a trailing sumcheck round must not be ignored"
        );

        let mut combined_tail = proof.clone();
        combined_tail.combined_proof.round_polys[0]
            .evaluations
            .push(F::ZERO);
        assert!(mle_verify::<F, D>(&common_data, &vk, &combined_tail).is_err());

        let mut inverse_tail = proof.clone();
        inverse_tail.inv_sumcheck_proof.round_polys[0]
            .evaluations
            .push(F::ZERO);
        assert!(mle_verify::<F, D>(&common_data, &vk, &inverse_tail).is_err());

        let mut h_tail = proof.clone();
        h_tail.h_sumcheck_proof.round_polys[0]
            .evaluations
            .push(F::ZERO);
        assert!(mle_verify::<F, D>(&common_data, &vk, &h_tail).is_err());

        let mut gate_tail = proof;
        gate_tail.gate_sumcheck_proof.round_polys[0]
            .evaluations
            .push(F::ZERO);
        assert!(mle_verify::<F, D>(&common_data, &vk, &gate_tail).is_err());
    }

    #[test]
    fn test_bad_order_model_recreates_rlc_kernel() {
        let rho = F::from_canonical_u64(17);
        let original = [F::from_canonical_u64(3), F::from_canonical_u64(9)];
        let mut forged = original;
        forged[0] += F::ONE;
        forged[1] -= rho.inverse();
        assert_ne!(forged, original);
        assert_eq!(batch_eval(&forged, rho), batch_eval(&original, rho));
    }

    #[test]
    fn test_setup_determinism() {
        let (prover_data, common_data, _, _) = build_mul_circuit();
        let vk1 = mle_setup::<F, C, D>(&prover_data, &common_data);
        let vk2 = mle_setup::<F, C, D>(&prover_data, &common_data);

        assert_eq!(vk1.circuit_digest, vk2.circuit_digest);
        assert_eq!(vk1.k_is, vk2.k_is);
        assert_eq!(vk1.subgroup_gen_powers, vk2.subgroup_gen_powers);
        assert_eq!(
            vk1.preprocessed_commitment_root,
            vk2.preprocessed_commitment_root
        );
    }
}
