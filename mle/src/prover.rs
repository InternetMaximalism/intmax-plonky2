/// Integrated MLE prover combining all sub-protocols.
///
/// Architecture: one staged WHIR session over four ordered packed groups:
/// preprocessed, witness, inverse helpers, and auxiliary `[C̃, h̃]`.
/// Each root commits one bivariate `(row, constituent_index)` MLE before the
/// relevant outer challenges. Terminal constituent claims are folded at a
/// post-claim Ext3 index point and opened from those packed commitments.
use anyhow::Result;
use ark_ff::AdditiveGroup;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_data::{CommonCircuitData, EvaluationTables, ProverOnlyCircuitData};
use plonky2::plonk::config::{GenericConfig, Hasher};
use plonky2::plonk::prover::extract_evaluation_tables;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::Extendable;
use plonky2_field::types::Field as PlonkyField;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::commitment::whir_pcs::{plonky2_vec_to_ark, WhirPCS, WHIR_SESSION_SPLIT};
use crate::constraint_eval::{compute_combined_constraints, flatten_extension_constraints};
use crate::dense_mle::{row_major_to_mles, tables_to_mles, DenseMultilinearExtension};
use crate::eq_poly;
use crate::proof::{
    constituent_group_width, constituent_index_bits, packed_group_num_vars, MleProof,
    MleVerificationKey, MLE_PROTOCOL_VERSION, NUM_PACKED_VECTORS_PER_GROUP,
};
use crate::protocol_schema::{
    EXTENSION_FIELD_LIMBS, NUM_PCS_CLAIMS, NUM_PCS_TERMINAL_POINTS, NUM_SPLIT_COMMITMENTS,
    PACKED_PCS_SCHEMA_DOMAIN, PACKED_VARIABLE_ORDER_CODE, POINT_COMBINED, POINT_GATE, POINT_H,
    POINT_INVERSE,
};
use crate::sumcheck::prover::{
    prove_sumcheck_combined, prove_sumcheck_gate_zerocheck, prove_sumcheck_inv_zerocheck,
    prove_sumcheck_plain,
};
use crate::transcript::Transcript;

/// Derive the deterministic batching scalar for preprocessed polynomials.
///
/// SECURITY: This must produce the same value during setup and proving for the
/// same circuit and packed preprocessed commitment. The root is absorbed before
/// the challenge so the batching scalar cannot be selected before the ordered
/// constituent vectors are committed.
pub fn derive_preprocessed_batch_r<F: RichField>(
    circuit_digest: &[F],
    preprocessed_root: &[u8],
) -> F {
    let mut t = Transcript::new();
    t.domain_separate("preprocessed-batch-r");
    t.absorb_field_vec(circuit_digest);
    t.absorb_bytes(preprocessed_root);
    t.squeeze_challenge()
}

/// Pack ordered constituent columns into one bivariate MLE. Dense-table index
/// `row + (constituent << degree_bits)` makes the row variables the low
/// (LSB-first) variables and the constituent-index variables the high ones.
fn mles_to_packed_ark_group<F: RichField>(
    mles: &[&DenseMultilinearExtension<F>],
    constituent_width: usize,
    num_rows: usize,
) -> Vec<Vec<whir::algebra::fields::Field64>> {
    assert!(
        mles.len() <= constituent_width,
        "constituent group exceeds schema width"
    );
    let index_capacity = constituent_width.next_power_of_two();
    let mut packed = vec![whir::algebra::fields::Field64::ZERO; num_rows * index_capacity];
    for (constituent, mle) in mles.iter().enumerate() {
        assert_eq!(
            mle.evaluations.len(),
            num_rows,
            "constituent row count mismatch"
        );
        let start = constituent * num_rows;
        for (row, value) in mle.evaluations.iter().enumerate() {
            packed[start + row] = whir::algebra::fields::Field64::from(value.to_canonical_u64());
        }
    }
    vec![packed]
}

fn tables_to_packed_ark_group<F: RichField>(
    tables: &[Vec<F>],
    constituent_width: usize,
    num_rows: usize,
) -> Vec<Vec<whir::algebra::fields::Field64>> {
    assert!(
        tables.len() <= constituent_width,
        "constituent group exceeds schema width"
    );
    let index_capacity = constituent_width.next_power_of_two();
    let mut packed = vec![whir::algebra::fields::Field64::ZERO; num_rows * index_capacity];
    for (constituent, table) in tables.iter().enumerate() {
        assert!(
            table.len() <= num_rows,
            "constituent row count exceeds domain"
        );
        let start = constituent * num_rows;
        for (row, value) in table.iter().enumerate() {
            packed[start + row] = whir::algebra::fields::Field64::from(value.to_canonical_u64());
        }
    }
    vec![packed]
}

pub(crate) fn absorb_schema_and_base_roots<F: RichField>(
    transcript: &mut Transcript,
    num_constants: usize,
    num_routed_wires: usize,
    num_wires: usize,
    constituent_width: usize,
    preprocessed_root: &[u8],
    witness_root: &[u8],
) {
    transcript.domain_separate(PACKED_PCS_SCHEMA_DOMAIN);
    for value in [
        MLE_PROTOCOL_VERSION as usize,
        NUM_SPLIT_COMMITMENTS,
        num_constants,
        num_routed_wires,
        num_wires,
        constituent_width,
        constituent_index_bits(constituent_width),
        NUM_PACKED_VECTORS_PER_GROUP,
        EXTENSION_FIELD_LIMBS,
        PACKED_VARIABLE_ORDER_CODE,
    ] {
        transcript.absorb_bytes(&(value as u64).to_le_bytes());
    }
    transcript.domain_separate("pcs-group-preprocessed");
    transcript.absorb_bytes(preprocessed_root);
    transcript.domain_separate("pcs-group-witness");
    transcript.absorb_bytes(witness_root);
}

/// Absorb the exact point-major/group-major constituent claim schema and then
/// derive one independent Ext3 index point for each terminal point. Every
/// claim is fixed before any index coordinate is sampled.
pub(crate) fn absorb_claims_and_sample_index_points<F: RichField>(
    transcript: &mut Transcript,
    claims: &[&[F]],
    index_bits: usize,
) -> Vec<Vec<Field64_3>> {
    assert_eq!(
        claims.len(),
        NUM_PCS_CLAIMS,
        "unexpected terminal-point/group claim matrix"
    );
    transcript.domain_separate("pcs-constituent-claims-v1");
    for claim in claims {
        transcript.absorb_field_vec(*claim);
    }
    transcript.domain_separate("pcs-constituent-index-v1");
    (0..NUM_PCS_TERMINAL_POINTS)
        .map(|_| {
            (0..index_bits)
                .map(|_| {
                    let c0: F = transcript.squeeze_challenge();
                    let c1: F = transcript.squeeze_challenge();
                    let c2: F = transcript.squeeze_challenge();
                    Field64_3::new(
                        ArkGoldilocks::from(c0.to_canonical_u64()),
                        ArkGoldilocks::from(c1.to_canonical_u64()),
                        ArkGoldilocks::from(c2.to_canonical_u64()),
                    )
                })
                .collect()
        })
        .collect()
}

/// Evaluate the constituent-index MLE of a claimed value vector at `index_point`.
/// Values beyond the exact group count, through `width.next_power_of_two()`,
/// are the schema-mandated zero padding committed by the prover.
pub(crate) fn fold_constituent_claim<F: RichField>(
    values: &[F],
    width: usize,
    index_point: &[Field64_3],
) -> Field64_3 {
    assert!(values.len() <= width, "claim exceeds constituent width");
    assert_eq!(
        index_point.len(),
        constituent_index_bits(width),
        "constituent index point width mismatch"
    );
    let mut layer = vec![Field64_3::from(0u64); width.next_power_of_two()];
    for (slot, value) in values.iter().enumerate() {
        layer[slot] = Field64_3::from(value.to_canonical_u64());
    }
    for challenge in index_point {
        for i in 0..(layer.len() / 2) {
            let even = layer[2 * i];
            let odd = layer[2 * i + 1];
            layer[i] = even + *challenge * (odd - even);
        }
        layer.truncate(layer.len() / 2);
    }
    layer[0]
}

fn packed_eval_point<F: RichField>(row_point: &[F], index_point: &[Field64_3]) -> Vec<Field64_3> {
    row_point
        .iter()
        .map(|value| Field64_3::from(value.to_canonical_u64()))
        .chain(index_point.iter().copied())
        .collect()
}

/// Return preprocessed constituents in the schema-bound constants-then-sigmas
/// order used by the packed commitment and every terminal claim.
fn collect_preprocessed_mles<'a, F: RichField>(
    const_mles: &'a [DenseMultilinearExtension<F>],
    sigma_mles: &'a [DenseMultilinearExtension<F>],
) -> Vec<&'a DenseMultilinearExtension<F>> {
    let mut preprocessed_mles: Vec<&DenseMultilinearExtension<F>> = Vec::new();
    for m in const_mles {
        preprocessed_mles.push(m);
    }
    for m in sigma_mles {
        preprocessed_mles.push(m);
    }
    preprocessed_mles
}

/// Compute the MLE verification key for a circuit (setup phase).
pub fn mle_setup<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    prover_data: &ProverOnlyCircuitData<F, C, D>,
    common_data: &CommonCircuitData<F, D>,
) -> MleVerificationKey<F>
where
    C::Hasher: Hasher<F>,
{
    let degree_bits = common_data.degree_bits();
    let num_routed_wires = common_data.config.num_routed_wires;

    let digest_bytes =
        serde_json::to_vec(&prover_data.circuit_digest).expect("circuit_digest serialization");
    let circuit_digest: Vec<F> = {
        let hash_out: plonky2::hash::hash_types::HashOut<F> =
            serde_json::from_slice(&digest_bytes).expect("circuit_digest deserialization");
        hash_out.elements.to_vec()
    };

    let const_mles = row_major_to_mles(&prover_data.constant_evals, common_data.num_constants);
    let sigma_mles = row_major_to_mles(&prover_data.sigmas, num_routed_wires);

    let num_wires = common_data.config.num_wires;
    let constituent_width =
        constituent_group_width(common_data.num_constants, num_routed_wires, num_wires);
    let mut preprocessed_refs: Vec<&DenseMultilinearExtension<F>> = const_mles.iter().collect();
    preprocessed_refs.extend(sigma_mles.iter());
    let pre_group =
        mles_to_packed_ark_group(&preprocessed_refs, constituent_width, 1usize << degree_bits);
    let whir_pcs = WhirPCS::for_constituents_v1(
        packed_group_num_vars(degree_bits, constituent_width),
        NUM_PACKED_VECTORS_PER_GROUP,
    );
    let commit_data = whir_pcs.commit_grouped(&[pre_group], WHIR_SESSION_SPLIT);
    let preprocessed_commitment_root = commit_data.roots[0].clone();
    let subgroup_gen_powers = {
        let g = prover_data.subgroup.get(1).copied().unwrap_or(F::ONE);
        let mut powers = Vec::with_capacity(degree_bits);
        let mut current = g;
        for _ in 0..degree_bits {
            powers.push(current);
            current *= current;
        }
        powers
    };

    MleVerificationKey {
        protocol_version: MLE_PROTOCOL_VERSION,
        constituent_width,
        circuit_digest,
        preprocessed_commitment_root,
        num_constants: common_data.num_constants,
        num_routed_wires,
        k_is: common_data.k_is.clone(),
        subgroup_gen_powers,
    }
}

/// Generate an MLE proof for a Plonky2 circuit.
pub fn mle_prove<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    prover_data: &ProverOnlyCircuitData<F, C, D>,
    common_data: &CommonCircuitData<F, D>,
    inputs: PartialWitness<F>,
    timing: &mut TimingTree,
) -> Result<MleProof<F>>
where
    C::Hasher: Hasher<F>,
    C::InnerHasher: Hasher<F>,
{
    let tables = extract_evaluation_tables::<F, C, D>(prover_data, common_data, inputs, timing)?;

    let digest_bytes =
        serde_json::to_vec(&prover_data.circuit_digest).expect("circuit_digest serialization");
    let circuit_digest: Vec<F> = {
        let hash_out: plonky2::hash::hash_types::HashOut<F> =
            serde_json::from_slice(&digest_bytes).expect("circuit_digest deserialization");
        hash_out.elements.to_vec()
    };

    mle_prove_from_tables::<F, D>(common_data, &tables, &circuit_digest)
}

/// Generate an MLE proof from pre-extracted evaluation tables.
pub fn mle_prove_from_tables<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    tables: &EvaluationTables<F>,
    circuit_digest: &[F],
) -> Result<MleProof<F>> {
    let degree = tables.degree;
    let degree_bits = tables.degree_bits;
    let num_routed_wires = tables.num_routed_wires;

    eprintln!("[prover] degree_bits={degree_bits}, degree={degree}");

    // ═══════════════════════════════════════════════════════════════════
    // Phase 1: Commit preprocessed + witness
    // ═══════════════════════════════════════════════════════════════════
    let mut transcript = Transcript::new();
    transcript.domain_separate("circuit");
    transcript.absorb_field_vec(circuit_digest);
    transcript.absorb_field_vec(&tables.public_inputs);

    let _t = std::time::Instant::now();
    let wire_mles = tables_to_mles(&tables.wire_values);
    let const_mles = row_major_to_mles(&tables.constant_values, common_data.num_constants);
    let sigma_mles = row_major_to_mles(&tables.sigma_values, num_routed_wires);
    eprintln!("[prover] build MLEs: {:?}", _t.elapsed());

    let constituent_width = constituent_group_width(
        common_data.num_constants,
        num_routed_wires,
        tables.num_wires,
    );
    let packed_num_vars = packed_group_num_vars(degree_bits, constituent_width);
    let whir_pcs = WhirPCS::for_constituents_v1(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP);

    // Commit the ordered base constituents before deriving either batching
    // scalar. In particular, preprocessedBatchR is root-dependent rather than
    // a circuit-only challenge sampled before the constituent commitment.
    let _t = std::time::Instant::now();
    let preprocessed_mles = collect_preprocessed_mles(&const_mles, &sigma_mles);

    let n_rows = 1usize << degree_bits;
    let pre_group = mles_to_packed_ark_group(&preprocessed_mles, constituent_width, n_rows);
    let witness_refs: Vec<&DenseMultilinearExtension<F>> = wire_mles.iter().collect();
    let witness_group = mles_to_packed_ark_group(&witness_refs, constituent_width, n_rows);

    // The two base groups are committed, in canonical schema order, before
    // any batching, permutation, or terminal-point challenge is sampled.
    let mut commit_data = whir_pcs.commit_grouped(&[pre_group, witness_group], WHIR_SESSION_SPLIT);
    let pre_root = commit_data.roots[0].clone();
    let witness_root = commit_data.roots[1].clone();
    let batch_r_pre: F = derive_preprocessed_batch_r(circuit_digest, &pre_root);
    absorb_schema_and_base_roots::<F>(
        &mut transcript,
        common_data.num_constants,
        num_routed_wires,
        tables.num_wires,
        constituent_width,
        &pre_root,
        &witness_root,
    );

    transcript.domain_separate("batch-commit-witness");
    let batch_r_wit: F = transcript.squeeze_challenge();

    // Witness batch
    let mut wit_batched_evals = vec![F::ZERO; 1 << degree_bits];
    let mut r_pow = F::ONE;
    for mle in &wire_mles {
        for (j, &eval) in mle.evaluations.iter().enumerate() {
            if j < wit_batched_evals.len() {
                wit_batched_evals[j] += r_pow * eval;
            }
        }
        r_pow *= batch_r_wit;
    }
    let wit_goldilocks_evals: Vec<plonky2_field::goldilocks_field::GoldilocksField> =
        wit_batched_evals
            .iter()
            .map(|&f| {
                plonky2_field::goldilocks_field::GoldilocksField::from_canonical_u64(
                    f.to_canonical_u64(),
                )
            })
            .collect();
    let wit_ark_evals = plonky2_vec_to_ark(&wit_goldilocks_evals);

    // The legacy Goldilocks batch values remain serialized for migration
    // diagnostics, but they are no longer the PCS soundness statement.
    let _ = wit_ark_evals;
    eprintln!("[prover] phase1 commit: {:?}", _t.elapsed());

    // ═══════════════════════════════════════════════════════════════════
    // Phase 2a: Squeeze β, γ (logUp denominators).
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("challenges");
    let beta: F = transcript.squeeze_challenge();
    let gamma: F = transcript.squeeze_challenge();

    // ═══════════════════════════════════════════════════════════════════
    // Phase 2b (v2 logUp): Build inverse helpers A_j, B_j and commit.
    //
    // SECURITY (Issue R2-#2): A_j(b) = 1/(β + W_j(b) + γ·ID_j(b)) and B_j(b)
    // = 1/(β + W_j(b) + γ·σ_j(b)) are committed AFTER β, γ are squeezed
    // (so the inverses depend on the challenges) and bound by two sumchecks
    // (Φ_inv zero-check + Φ_h linear) — see paper §4.2 in
    // mle/paper/plonky2_mle_paper_v2.md. The terminal checks operate on
    // multilinear quantities only; no 1/x is evaluated by the verifier.
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();
    let id_values_for_inv = crate::permutation::logup::compute_identity_values(
        &tables.k_is,
        &tables.subgroup,
        num_routed_wires,
        degree,
    );
    let (a_tables, b_tables) = crate::permutation::logup::compute_inverse_helpers(
        &tables.wire_values,
        &tables.sigma_values,
        &id_values_for_inv,
        beta,
        gamma,
        num_routed_wires,
        degree,
    )
    .map_err(|e| anyhow::anyhow!("v2 logUp inverse build: {e}"))?;

    let inverse_tables: Vec<Vec<F>> = a_tables
        .iter()
        .take(num_routed_wires)
        .cloned()
        .chain(b_tables.iter().take(num_routed_wires).cloned())
        .collect();
    let inverse_group = tables_to_packed_ark_group(&inverse_tables, constituent_width, n_rows);
    let inverse_helpers_root = whir_pcs.commit_additional_group(&mut commit_data, inverse_group);
    transcript.domain_separate("pcs-group-inverse-helpers");
    transcript.absorb_bytes(&inverse_helpers_root);
    transcript.domain_separate("inverse-helpers-batch-r");
    let inv_helpers_batch_r: F = transcript.squeeze_challenge();
    eprintln!(
        "[prover] phase2b inverse-helpers commit: {:?}",
        _t.elapsed()
    );

    // ═══════════════════════════════════════════════════════════════════
    // Phase 2c: Squeeze only the challenges required to construct C̃.
    // Query/sumcheck challenges stay after the auxiliary constituent root.
    // ═══════════════════════════════════════════════════════════════════
    let alpha: F = transcript.squeeze_challenge();
    transcript.domain_separate("extension-combine");
    let ext_challenge: F = transcript.squeeze_challenge();

    // Compute C̃ (constraint MLE)
    let _t = std::time::Instant::now();
    let combined_ext = compute_combined_constraints::<F, D>(
        common_data,
        &tables.wire_values,
        &tables.constant_values,
        &[alpha],
        &tables.public_inputs_hash,
        degree,
    );
    let mut padded_constraints =
        flatten_extension_constraints::<F, D>(&combined_ext, ext_challenge);
    padded_constraints.resize(1 << degree_bits, F::ZERO);

    // Compute h̃ (permutation numerator MLE)
    let id_values = crate::permutation::logup::compute_identity_values(
        &tables.k_is,
        &tables.subgroup,
        num_routed_wires,
        degree,
    );
    let perm_h = crate::permutation::logup::compute_permutation_numerator(
        &tables.wire_values,
        &tables.sigma_values,
        &id_values,
        beta,
        gamma,
        num_routed_wires,
        degree,
    );
    let mut perm_h_padded = perm_h;
    perm_h_padded.resize(1 << degree_bits, F::ZERO);
    eprintln!("[prover] phase2 constraints+perm: {:?}", _t.elapsed());

    // ═══════════════════════════════════════════════════════════════════
    // Phase 3: Commit the two auxiliary constituents C̃ and h̃.
    // They legitimately depend on earlier challenges, but their ordered group
    // root precedes rho_aux, mu, all sumcheck messages, and all query points.
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();
    let aux_group = tables_to_packed_ark_group(
        &[padded_constraints.clone(), perm_h_padded.clone()],
        constituent_width,
        n_rows,
    );
    let aux_root = whir_pcs.commit_additional_group(&mut commit_data, aux_group);
    transcript.domain_separate("pcs-group-auxiliary");
    transcript.absorb_bytes(&aux_root);
    transcript.domain_separate("aux-batch-r");
    let batch_r_aux: F = transcript.squeeze_challenge();
    eprintln!("[prover] phase3 aux commit (phased): {:?}", _t.elapsed());

    // Every challenge that defines a sumcheck polynomial/query point follows
    // the auxiliary root. This prevents challenge-dependent C̃/h̃ selection.
    transcript.domain_separate("post-auxiliary-challenges-v1");
    let tau: Vec<F> = transcript.squeeze_challenges(degree_bits);
    let tau_perm: Vec<F> = transcript.squeeze_challenges(degree_bits);
    transcript.domain_separate("v2-logup-challenges");
    let lambda_inv: F = transcript.squeeze_challenge();
    let mu_inv: F = transcript.squeeze_challenge();
    let tau_inv: Vec<F> = transcript.squeeze_challenges(degree_bits);

    // ═══════════════════════════════════════════════════════════════════
    // Phase 4: Derive combination scalar μ + lookups
    // ═══════════════════════════════════════════════════════════════════
    transcript.domain_separate("combined-sumcheck");
    let mu: F = transcript.squeeze_challenge();

    // SECURITY: Lookup argument is not yet implemented. Fail-fast to prevent
    // silently accepting circuits with lookup tables (which would be unsound).
    let has_lookup = !common_data.luts.is_empty();
    anyhow::ensure!(
        !has_lookup,
        "Lookup tables not yet supported in MLE prover ({} LUTs present)",
        common_data.luts.len()
    );
    let lookup_proofs = Vec::new();

    // ═══════════════════════════════════════════════════════════════════
    // Phase 5: Combined sumcheck
    //   Σ_b [eq(τ,b)·C̃(b) + μ·eq(τ_perm,b)·h̃(b)] = 0
    // Single sumcheck → single output point r
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();
    let eq_table = eq_poly::eq_evals(&tau);

    let mut eq_mle = DenseMultilinearExtension::new(eq_table);
    let mut constraint_mle = DenseMultilinearExtension::new(padded_constraints.clone());
    let mut h_mle = DenseMultilinearExtension::new(perm_h_padded.clone());

    // Max degree: eq(τ,·)·C(·) has degree 2 per variable (product of two multilinear),
    // μ·h(·) has degree 1 per variable (scaled multilinear). Combined: degree 2.
    let max_constraint_degree = 2;
    let (combined_proof, sumcheck_challenges) = prove_sumcheck_combined(
        &mut eq_mle,
        &mut constraint_mle,
        &mut h_mle,
        mu,
        max_constraint_degree,
        &mut transcript,
    );
    eprintln!("[prover] phase5 combined sumcheck: {:?}", _t.elapsed());

    // ═══════════════════════════════════════════════════════════════════
    // Phase 5.5 (v2 logUp): Φ_inv zero-check sumcheck.
    //   Σ_b eq(τ_inv, b)·Σ_j λ^j·(A_j·D_j^id − 1 + μ_inv·(B_j·D_j^σ − 1)) = 0
    // Round-poly degree 3.   → r_inv, S_n_inv (claimed = 0).
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();
    transcript.domain_separate("v2-inv-zerocheck");
    let mut eq_inv_mle = DenseMultilinearExtension::new(eq_poly::eq_evals(&tau_inv));
    let mut a_inv_mles: Vec<DenseMultilinearExtension<F>> = a_tables
        .iter()
        .map(|t| {
            let mut padded = t.clone();
            padded.resize(n_rows, F::ZERO);
            DenseMultilinearExtension::new(padded)
        })
        .collect();
    let mut b_inv_mles: Vec<DenseMultilinearExtension<F>> = b_tables
        .iter()
        .map(|t| {
            let mut padded = t.clone();
            padded.resize(n_rows, F::ZERO);
            DenseMultilinearExtension::new(padded)
        })
        .collect();
    // Working copies of W, σ, g_sub (the prover-internal sumcheck consumes them).
    let mut w_inv_mles: Vec<DenseMultilinearExtension<F>> =
        wire_mles.iter().take(num_routed_wires).cloned().collect();
    let mut sigma_inv_mles: Vec<DenseMultilinearExtension<F>> =
        sigma_mles.iter().take(num_routed_wires).cloned().collect();
    let mut g_sub_padded = tables.subgroup.clone();
    g_sub_padded.resize(n_rows, F::ZERO);
    let mut g_sub_mle = DenseMultilinearExtension::new(g_sub_padded);

    let (inv_sumcheck_proof, inv_sumcheck_challenges) = prove_sumcheck_inv_zerocheck::<F>(
        &mut eq_inv_mle,
        &mut a_inv_mles,
        &mut b_inv_mles,
        &mut w_inv_mles,
        &mut sigma_inv_mles,
        &mut g_sub_mle,
        &tables.k_is,
        beta,
        gamma,
        lambda_inv,
        mu_inv,
        &mut transcript,
    );
    eprintln!("[prover] phase5.5 Φ_inv: {:?}", _t.elapsed());

    // ═══════════════════════════════════════════════════════════════════
    // Phase 5.7 (v2 logUp): Φ_h linear sumcheck.
    //   Σ_b H(b) = 0, H(b) = Σ_j (A_j(b) − B_j(b))
    // Round-poly degree 1 (linear in each variable).
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();
    transcript.domain_separate("v2-h-linear");
    // SECURITY: H is the *unweighted* sum Σ_j (A_j − B_j). Only the unweighted
    // sum telescopes via logUp (Σ_b Σ_j (1/D_id − 1/D_σ) = 0); per-j sums do
    // not vanish in general, so a λ_h^j weighting would NOT have a zero
    // claimed sum on an honest prover.
    let mut h_combined = vec![F::ZERO; n_rows];
    for jj in 0..num_routed_wires {
        for row in 0..n_rows {
            let a_v = if row < a_tables[jj].len() {
                a_tables[jj][row]
            } else {
                F::ZERO
            };
            let b_v = if row < b_tables[jj].len() {
                b_tables[jj][row]
            } else {
                F::ZERO
            };
            h_combined[row] += a_v - b_v;
        }
    }
    let mut h_combined_mle = DenseMultilinearExtension::new(h_combined);
    let (h_sumcheck_proof, h_sumcheck_challenges) =
        prove_sumcheck_plain::<F>(&mut h_combined_mle, &mut transcript);
    eprintln!("[prover] phase5.7 Φ_h: {:?}", _t.elapsed());

    // ═══════════════════════════════════════════════════════════════════
    // Phase 5.8 (v2 gate binding — Issue R2-#1, paper §7.3):
    //
    // Run the Φ_gate zero-check sumcheck that binds the ACTUAL Plonky2 gate
    // formula evaluated at a random point to the sumcheck output, rather
    // than relying on the legacy `aux_constraint_eval` oracle (which did
    // not close the MLE-commutativity gap for gates of degree ≥ 2).
    //
    //   Φ_gate(x) := eq(τ_gate, x) · flatten_ext(
    //                    Σ_j α^j · c_j( lift(W_k(x)), lift(const_k(x)) ),
    //                    ext_challenge
    //                )
    // claimed sum = 0.
    //
    // SECURITY: τ_gate is squeezed AFTER all wire/const commitments and
    // all prior transcript content. α and ext_challenge are the same
    // scalars used for `compute_combined_constraints` /
    // `flatten_extension_constraints`, so the row-wise value equals C̃
    // on the Boolean hypercube (honest prover).
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();
    transcript.domain_separate("v2-gate-challenges");
    let tau_gate: Vec<F> = transcript.squeeze_challenges(degree_bits);

    transcript.domain_separate("v2-gate-zerocheck");
    // Φ_gate degree per variable: 1 (eq) + max filtered-constraint degree.
    // Plonky2 bounds the filtered constraint degree by `quotient_degree_factor + 1`
    // when selector_polynomials produces multiple groups (many_selector = true).
    // Use the safe upper bound qdf + 2 so the round poly captures the full
    // polynomial regardless of how gates were grouped.
    let max_round_degree_gate = 2 + common_data.quotient_degree_factor;

    let mut eq_gate_mle = DenseMultilinearExtension::new(eq_poly::eq_evals(&tau_gate));
    // Ensure the wire/const MLE vectors match exactly what the gate evaluator
    // expects (pad with zero-MLEs if the prover did not build all columns).
    let mut wire_gate_mles: Vec<DenseMultilinearExtension<F>> = wire_mles.clone();
    while wire_gate_mles.len() < common_data.config.num_wires {
        wire_gate_mles.push(DenseMultilinearExtension::new(vec![F::ZERO; n_rows]));
    }
    let mut const_gate_mles: Vec<DenseMultilinearExtension<F>> = const_mles.clone();
    while const_gate_mles.len() < common_data.num_constants {
        const_gate_mles.push(DenseMultilinearExtension::new(vec![F::ZERO; n_rows]));
    }

    let (gate_sumcheck_proof, gate_sumcheck_challenges) = prove_sumcheck_gate_zerocheck::<F, D>(
        common_data,
        &mut wire_gate_mles,
        &mut const_gate_mles,
        &mut eq_gate_mle,
        alpha,
        ext_challenge,
        &tables.public_inputs_hash,
        max_round_degree_gate,
        &mut transcript,
    );
    eprintln!("[prover] phase5.8 Φ_gate: {:?}", _t.elapsed());

    // ═══════════════════════════════════════════════════════════════════
    // Phase 6: Evaluate at sumcheck output point r
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();

    // Individual evals from main commitment
    let preprocessed_individual_evals: Vec<F> = preprocessed_mles
        .iter()
        .map(|m| m.evaluate(&sumcheck_challenges))
        .collect();
    let witness_individual_evals: Vec<F> = wire_mles
        .iter()
        .map(|m| m.evaluate(&sumcheck_challenges))
        .collect();

    // Auxiliary oracle evals at r
    let constraint_mle_eval = DenseMultilinearExtension::new(padded_constraints);
    let perm_h_mle_eval = DenseMultilinearExtension::new(perm_h_padded);
    let aux_constraint_eval = constraint_mle_eval.evaluate(&sumcheck_challenges);
    let aux_perm_eval = perm_h_mle_eval.evaluate(&sumcheck_challenges);
    let aux_eval_value = aux_constraint_eval + batch_r_aux * aux_perm_eval;

    // Batched main evaluations
    let mut preprocessed_eval_value = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &preprocessed_individual_evals {
        preprocessed_eval_value += r_pow * eval;
        r_pow *= batch_r_pre;
    }
    let mut witness_eval_value = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &witness_individual_evals {
        witness_eval_value += r_pow * eval;
        r_pow *= batch_r_wit;
    }
    eprintln!("[prover] phase6 evals: {:?}", _t.elapsed());

    // ═══════════════════════════════════════════════════════════════════
    // Phase 6.5 (v2 logUp): Per-point individual evaluations needed for
    // terminal checks at r_inv and r_h.
    // ═══════════════════════════════════════════════════════════════════
    // At r_inv: w_j, σ_j, a_j, b_j, g_sub
    let witness_individual_evals_at_r_inv: Vec<F> = wire_mles
        .iter()
        .map(|m| m.evaluate(&inv_sumcheck_challenges))
        .collect();
    // Preprocessed individual evals at r_inv (full layout: const || sigma).
    let preprocessed_individual_evals_at_r_inv_full: Vec<F> = preprocessed_mles
        .iter()
        .map(|m| m.evaluate(&inv_sumcheck_challenges))
        .collect();
    let inverse_helpers_evals_at_r_inv: Vec<F> = {
        let a_evals: Vec<F> = a_tables
            .iter()
            .map(|t| {
                let mut padded = t.clone();
                padded.resize(n_rows, F::ZERO);
                DenseMultilinearExtension::new(padded).evaluate(&inv_sumcheck_challenges)
            })
            .collect();
        let b_evals: Vec<F> = b_tables
            .iter()
            .map(|t| {
                let mut padded = t.clone();
                padded.resize(n_rows, F::ZERO);
                DenseMultilinearExtension::new(padded).evaluate(&inv_sumcheck_challenges)
            })
            .collect();
        a_evals.into_iter().chain(b_evals).collect()
    };
    let g_sub_eval_at_r_inv: F = {
        let mut g_padded = tables.subgroup.clone();
        g_padded.resize(n_rows, F::ZERO);
        DenseMultilinearExtension::new(g_padded).evaluate(&inv_sumcheck_challenges)
    };

    // At r_gate_v2: witness (wires) and full preprocessed (const||sigma) are
    // needed so the verifier can (i) run the Plonky2 gate evaluator at
    // `r_gate_v2` and (ii) reconstruct the batched Goldilocks sum for WHIR
    // consistency.
    let witness_individual_evals_at_r_gate_v2: Vec<F> = wire_mles
        .iter()
        .map(|m| m.evaluate(&gate_sumcheck_challenges))
        .collect();
    let preprocessed_individual_evals_at_r_gate_v2_full: Vec<F> = preprocessed_mles
        .iter()
        .map(|m| m.evaluate(&gate_sumcheck_challenges))
        .collect();

    let mut witness_eval_value_at_r_gate_v2 = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &witness_individual_evals_at_r_gate_v2 {
        witness_eval_value_at_r_gate_v2 += r_pow * eval;
        r_pow *= batch_r_wit;
    }
    let mut preprocessed_eval_value_at_r_gate_v2 = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &preprocessed_individual_evals_at_r_gate_v2_full {
        preprocessed_eval_value_at_r_gate_v2 += r_pow * eval;
        r_pow *= batch_r_pre;
    }

    // At r_h: only inverse-helper evals are needed for terminal check.
    let inverse_helpers_evals_at_r_h: Vec<F> = {
        let a_evals: Vec<F> = a_tables
            .iter()
            .map(|t| {
                let mut padded = t.clone();
                padded.resize(n_rows, F::ZERO);
                DenseMultilinearExtension::new(padded).evaluate(&h_sumcheck_challenges)
            })
            .collect();
        let b_evals: Vec<F> = b_tables
            .iter()
            .map(|t| {
                let mut padded = t.clone();
                padded.resize(n_rows, F::ZERO);
                DenseMultilinearExtension::new(padded).evaluate(&h_sumcheck_challenges)
            })
            .collect();
        a_evals.into_iter().chain(b_evals).collect()
    };

    // Batched Goldilocks evaluations (for batch consistency in verifier).
    let mut witness_eval_value_at_r_inv = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &witness_individual_evals_at_r_inv {
        witness_eval_value_at_r_inv += r_pow * eval;
        r_pow *= batch_r_wit;
    }
    let mut preprocessed_eval_value_at_r_inv = F::ZERO;
    let mut r_pow = F::ONE;
    for &eval in &preprocessed_individual_evals_at_r_inv_full {
        preprocessed_eval_value_at_r_inv += r_pow * eval;
        r_pow *= batch_r_pre;
    }

    // ═══════════════════════════════════════════════════════════════════
    // Phase 7: packed WHIR prove — bind every terminal constituent vector.
    //
    // The exact claim arrays (including empty group/point combinations) enter
    // the outer transcript first. Four Ext3 index points are then sampled and
    // appended to the corresponding row points. A WHIR opening of the packed
    // bivariate group at `(row_point, index_point)` authenticates the random
    // multilinear fold of every constituent claim with ~192-bit field size.
    // ═══════════════════════════════════════════════════════════════════
    let _t = std::time::Instant::now();
    transcript.domain_separate("pcs-eval");
    let empty: &[F] = &[];
    let aux_claims = [aux_constraint_eval, aux_perm_eval];
    let claims: [&[F]; NUM_PCS_CLAIMS] = [
        &preprocessed_individual_evals,
        &witness_individual_evals,
        empty,
        &aux_claims,
        &preprocessed_individual_evals_at_r_inv_full,
        &witness_individual_evals_at_r_inv,
        &inverse_helpers_evals_at_r_inv,
        empty,
        empty,
        empty,
        &inverse_helpers_evals_at_r_h,
        empty,
        &preprocessed_individual_evals_at_r_gate_v2_full,
        &witness_individual_evals_at_r_gate_v2,
        empty,
        empty,
    ];
    let index_points = absorb_claims_and_sample_index_points(
        &mut transcript,
        &claims,
        constituent_index_bits(constituent_width),
    );
    let r_gate_packed = packed_eval_point(&sumcheck_challenges, &index_points[POINT_COMBINED]);
    let r_inv_packed = packed_eval_point(&inv_sumcheck_challenges, &index_points[POINT_INVERSE]);
    let r_h_packed = packed_eval_point(&h_sumcheck_challenges, &index_points[POINT_H]);
    let r_gate_v2_packed = packed_eval_point(&gate_sumcheck_challenges, &index_points[POINT_GATE]);

    let (whir_eval_proof, _) = whir_pcs.prove_grouped_with_eval(
        commit_data,
        &[
            &r_gate_packed,
            &r_inv_packed,
            &r_h_packed,
            &r_gate_v2_packed,
        ],
    );

    eprintln!(
        "[prover] phase7 WHIR prove ({NUM_PCS_TERMINAL_POINTS}-point): {:?}",
        _t.elapsed()
    );

    // ═══════════════════════════════════════════════════════════════════
    // Phase 8: Proof assembly
    // ═══════════════════════════════════════════════════════════════════
    Ok(MleProof {
        protocol_version: MLE_PROTOCOL_VERSION,
        constituent_width,
        circuit_digest: circuit_digest.to_vec(),
        // Main WHIR PCS
        whir_eval_proof,
        preprocessed_root: pre_root,
        witness_root,
        // Preprocessed batch at r
        preprocessed_eval_value,
        preprocessed_batch_r: batch_r_pre,
        preprocessed_individual_evals,
        // Witness batch at r
        witness_eval_value,
        witness_batch_r: batch_r_wit,
        witness_individual_evals,
        // Auxiliary polynomial (fourth constituent group)
        aux_commitment_root: aux_root,
        aux_batch_r: batch_r_aux,
        aux_constraint_eval,
        aux_perm_eval,
        aux_eval_value,
        // Sumcheck output
        sumcheck_challenges: sumcheck_challenges.clone(),
        // Combined sumcheck
        combined_proof,
        lookup_proofs,
        // Public data
        public_inputs: tables.public_inputs.clone(),
        public_inputs_hash: tables.public_inputs_hash,
        alpha,
        beta,
        gamma,
        tau,
        tau_perm,
        mu,
        num_wires: tables.num_wires,
        num_routed_wires,
        num_constants: common_data.num_constants,
        // Issue #2: expose VK-bound permutation context so the Solidity verifier can
        // bind h̃(r) to the actual permutation numerator computed from witness/sigma
        // evaluations.
        k_is: tables.k_is.clone(),
        subgroup_gen_powers: {
            // g^{2^i} for i in 0..degree_bits.
            // tables.subgroup[1] = g (the primitive 2^degree_bits-th root of unity used
            // by the prover when constructing the subgroup vector).
            let g: F = if tables.subgroup.len() >= 2 {
                tables.subgroup[1]
            } else {
                F::ONE
            };
            let mut powers = Vec::with_capacity(degree_bits);
            let mut cur = g;
            for _ in 0..degree_bits {
                powers.push(cur);
                cur = cur * cur;
            }
            powers
        },
        // ── v2 logUp soundness fix (Issue R2-#2) ────────────────────────
        inverse_helpers_root,
        inverse_helpers_batch_r: inv_helpers_batch_r,
        inv_sumcheck_challenges,
        inv_sumcheck_proof,
        h_sumcheck_challenges,
        h_sumcheck_proof,
        lambda_inv,
        mu_inv,
        tau_inv,
        inverse_helpers_evals_at_r_inv,
        inverse_helpers_evals_at_r_h,
        witness_individual_evals_at_r_inv,
        preprocessed_individual_evals_at_r_inv: preprocessed_individual_evals_at_r_inv_full,
        g_sub_eval_at_r_inv,
        witness_eval_value_at_r_inv,
        preprocessed_eval_value_at_r_inv,
        // ── v2 gate binding fix (Issue R2-#1) ──────────────────────────
        ext_challenge,
        tau_gate,
        gate_sumcheck_proof,
        gate_sumcheck_challenges,
        witness_individual_evals_at_r_gate_v2,
        preprocessed_individual_evals_at_r_gate_v2: preprocessed_individual_evals_at_r_gate_v2_full,
        witness_eval_value_at_r_gate_v2,
        preprocessed_eval_value_at_r_gate_v2,
    })
}

#[cfg(test)]
mod tests {
    use ark_ff::Field as ArkField;
    use plonky2::iop::witness::WitnessWrite;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::PoseidonGoldilocksConfig;
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::{Field, PrimeField64};

    use super::*;
    use crate::commitment::whir_pcs::ark_to_plonky2;
    use crate::proof::{GROUP_AUXILIARY, GROUP_INVERSE_HELPERS, GROUP_PREPROCESSED, GROUP_WITNESS};

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_mle_prove_simple_circuit() {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.add_virtual_target();
        let y = builder.add_virtual_target();
        let z = builder.mul(x, y);
        builder.register_public_input(z);

        let circuit = builder.build::<C>();
        let mut pw = PartialWitness::new();
        pw.set_target(x, F::from_canonical_u64(3)).unwrap();
        pw.set_target(y, F::from_canonical_u64(7)).unwrap();

        let mut timing = TimingTree::default();
        let proof =
            mle_prove::<F, C, D>(&circuit.prover_only, &circuit.common, pw, &mut timing).unwrap();

        assert_eq!(proof.public_inputs[0], F::from_canonical_u64(21));
        assert!(!proof.witness_individual_evals.is_empty());
        assert!(!proof.preprocessed_individual_evals.is_empty());
    }

    fn sample_packed_index_points(
        prefix: &Transcript,
        claims: &[Vec<F>],
        index_bits: usize,
    ) -> Vec<Vec<Field64_3>> {
        let claim_refs: Vec<&[F]> = claims.iter().map(Vec::as_slice).collect();
        let mut transcript = prefix.clone();
        absorb_claims_and_sample_index_points(&mut transcript, &claim_refs, index_bits)
    }

    fn packed_expected_evals(
        claims: &[Vec<F>],
        index_points: &[Vec<Field64_3>],
        used_cells: &[(usize, usize)],
        constituent_width: usize,
    ) -> Vec<Option<Field64_3>> {
        let mut expected = vec![None; 4 * NUM_SPLIT_COMMITMENTS];
        for &(point, group) in used_cells {
            let cell = point * NUM_SPLIT_COMMITMENTS + group;
            expected[cell] = Some(fold_constituent_claim(
                &claims[cell],
                constituent_width,
                &index_points[point],
            ));
        }
        expected
    }

    fn packed_points(
        row_points: &[Vec<F>],
        index_points: &[Vec<Field64_3>],
    ) -> Vec<Vec<Field64_3>> {
        row_points
            .iter()
            .zip(index_points)
            .map(|(row, index)| packed_eval_point(row, index))
            .collect()
    }

    #[test]
    fn test_post_claim_ext3_projection_rejects_every_used_constituent_delta() {
        const DEGREE_BITS: usize = 2;
        const NUM_ROWS: usize = 1 << DEGREE_BITS;
        const CONSTITUENT_WIDTH: usize = 4;

        // These are precisely the nine point/group cells consumed by the
        // verifier's terminal equations. The other seven WHIR evaluations are
        // transcript-bound internally but have no outer expected value.
        let used_cells = [
            (0, GROUP_PREPROCESSED),
            (0, GROUP_WITNESS),
            (0, GROUP_AUXILIARY),
            (1, GROUP_PREPROCESSED),
            (1, GROUP_WITNESS),
            (1, GROUP_INVERSE_HELPERS),
            (2, GROUP_INVERSE_HELPERS),
            (3, GROUP_PREPROCESSED),
            (3, GROUP_WITNESS),
        ];

        // Exact production group shapes for C=1, R=2 and W=4:
        // preprocessed=3, witness=4, inverse=4 and auxiliary=2.
        let group_lengths = [3usize, 4, 4, 2];
        let table_groups: Vec<Vec<Vec<F>>> = group_lengths
            .iter()
            .enumerate()
            .map(|(group, &count)| {
                (0..count)
                    .map(|constituent| {
                        (0..NUM_ROWS)
                            .map(|row| {
                                F::from_canonical_usize(
                                    1 + 101 * group + 17 * constituent + 3 * row,
                                )
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let packed_groups: Vec<Vec<Vec<ArkGoldilocks>>> = table_groups
            .iter()
            .map(|tables| tables_to_packed_ark_group(tables, CONSTITUENT_WIDTH, NUM_ROWS))
            .collect();

        let packed_num_vars = packed_group_num_vars(DEGREE_BITS, CONSTITUENT_WIDTH);
        let pcs = WhirPCS::for_constituents_v1(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP);
        let commit_data = pcs.commit_grouped(&packed_groups, WHIR_SESSION_SPLIT);
        let roots = commit_data.roots.clone();
        let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

        let row_points = vec![
            vec![F::from_canonical_u64(2), F::from_canonical_u64(3)],
            vec![F::from_canonical_u64(5), F::from_canonical_u64(7)],
            vec![F::from_canonical_u64(11), F::from_canonical_u64(13)],
            vec![F::from_canonical_u64(17), F::from_canonical_u64(19)],
        ];
        let mut claims = vec![Vec::new(); 4 * NUM_SPLIT_COMMITMENTS];
        for &(point, group) in &used_cells {
            claims[point * NUM_SPLIT_COMMITMENTS + group] = table_groups[group]
                .iter()
                .map(|table| {
                    DenseMultilinearExtension::new(table.clone()).evaluate(&row_points[point])
                })
                .collect();
        }

        // The committed roots precede the complete claim matrix. Only after
        // all sixteen length-prefixed arrays are fixed may the index points be
        // sampled. The helper below is the same one used by prove and verify.
        let mut transcript_prefix = Transcript::new();
        absorb_schema_and_base_roots::<F>(
            &mut transcript_prefix,
            1,
            2,
            4,
            CONSTITUENT_WIDTH,
            &roots[GROUP_PREPROCESSED],
            &roots[GROUP_WITNESS],
        );
        transcript_prefix.domain_separate("pcs-group-inverse-helpers");
        transcript_prefix.absorb_bytes(&roots[GROUP_INVERSE_HELPERS]);
        transcript_prefix.domain_separate("pcs-group-auxiliary");
        transcript_prefix.absorb_bytes(&roots[GROUP_AUXILIARY]);
        transcript_prefix.domain_separate("pcs-eval");

        let index_bits = constituent_index_bits(CONSTITUENT_WIDTH);
        let index_points = sample_packed_index_points(&transcript_prefix, &claims, index_bits);
        let points = packed_points(&row_points, &index_points);
        let point_refs: Vec<&[Field64_3]> = points.iter().map(Vec::as_slice).collect();
        let (proof, _) = pcs.prove_grouped_with_eval(commit_data, &point_refs);
        let expected =
            packed_expected_evals(&claims, &index_points, &used_cells, CONSTITUENT_WIDTH);
        pcs.verify_grouped(
            packed_num_vars,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            NUM_SPLIT_COMMITMENTS,
            &root_refs,
        )
        .expect("honest post-claim packed projection");

        // The production packed query also binds index-bit order and the full
        // extension coordinate, not merely each coordinate's c0 limb.
        let mut swapped_index_points = index_points.clone();
        swapped_index_points[0].swap(0, 1);
        assert_ne!(swapped_index_points[0], index_points[0]);
        let swapped_expected = packed_expected_evals(
            &claims,
            &swapped_index_points,
            &used_cells,
            CONSTITUENT_WIDTH,
        );
        let swapped_points = packed_points(&row_points, &swapped_index_points);
        let swapped_point_refs: Vec<&[Field64_3]> =
            swapped_points.iter().map(Vec::as_slice).collect();
        assert!(
            pcs.verify_grouped(
                packed_num_vars,
                &proof,
                &swapped_expected,
                WHIR_SESSION_SPLIT,
                &swapped_point_refs,
                NUM_SPLIT_COMMITMENTS,
                &root_refs,
            )
            .is_err(),
            "accepted an LSB/MSB index-coordinate swap"
        );
        for limb in 1..=2 {
            let mut changed_index_points = index_points.clone();
            let mut coefficients: Vec<ArkGoldilocks> =
                ArkField::to_base_prime_field_elements(&changed_index_points[0][0]).collect();
            coefficients[limb] += ArkGoldilocks::ONE;
            changed_index_points[0][0] = Field64_3::from_base_prime_field_elems(coefficients)
                .expect("three coefficients define an Ext3 element");
            let changed_expected = packed_expected_evals(
                &claims,
                &changed_index_points,
                &used_cells,
                CONSTITUENT_WIDTH,
            );
            let changed_points = packed_points(&row_points, &changed_index_points);
            let changed_point_refs: Vec<&[Field64_3]> =
                changed_points.iter().map(Vec::as_slice).collect();
            assert!(
                pcs.verify_grouped(
                    packed_num_vars,
                    &proof,
                    &changed_expected,
                    WHIR_SESSION_SPLIT,
                    &changed_point_refs,
                    NUM_SPLIT_COMMITMENTS,
                    &root_refs,
                )
                .is_err(),
                "accepted an index-point c{limb} mutation"
            );
        }

        // Exercise every constituent coordinate of every used cell with a
        // distinct nonzero delta fixed into the transcript before its index
        // challenge is sampled.
        for &(point, group) in &used_cells {
            let cell = point * NUM_SPLIT_COMMITMENTS + group;
            for constituent in 0..claims[cell].len() {
                let delta = F::from_canonical_usize(1 + 101 * point + 17 * group + constituent);
                assert_ne!(delta, F::ZERO);
                let mut changed_claims = claims.clone();
                changed_claims[cell][constituent] += delta;
                let changed_index_points =
                    sample_packed_index_points(&transcript_prefix, &changed_claims, index_bits);

                let mut unit = vec![F::ZERO; claims[cell].len()];
                unit[constituent] = F::ONE;
                let basis_weight =
                    fold_constituent_claim(&unit, CONSTITUENT_WIDTH, &changed_index_points[point]);
                assert_ne!(
                    basis_weight,
                    Field64_3::from(0u64),
                    "zero projection weight at point {point}, group {group}, constituent {constituent}"
                );
                let truthful_fold = fold_constituent_claim(
                    &claims[cell],
                    CONSTITUENT_WIDTH,
                    &changed_index_points[point],
                );
                let forged_fold = fold_constituent_claim(
                    &changed_claims[cell],
                    CONSTITUENT_WIDTH,
                    &changed_index_points[point],
                );
                assert_eq!(
                    forged_fold - truthful_fold,
                    basis_weight * Field64_3::from(delta.to_canonical_u64()),
                    "unexpected projection delta at point {point}, group {group}, constituent {constituent}"
                );

                let changed_expected = packed_expected_evals(
                    &changed_claims,
                    &changed_index_points,
                    &used_cells,
                    CONSTITUENT_WIDTH,
                );
                let changed_points = packed_points(&row_points, &changed_index_points);
                let changed_point_refs: Vec<&[Field64_3]> =
                    changed_points.iter().map(Vec::as_slice).collect();
                assert!(
                    pcs.verify_grouped(
                        packed_num_vars,
                        &proof,
                        &changed_expected,
                        WHIR_SESSION_SPLIT,
                        &changed_point_refs,
                        NUM_SPLIT_COMMITMENTS,
                        &root_refs,
                    )
                    .is_err(),
                    "accepted constituent delta at point {point}, group {group}, constituent {constituent}"
                );
            }
        }
    }

    /// Return a nonzero base-field vector in the kernel of the supplied Ext3
    /// weights. Four columns in a three-dimensional base-field space always
    /// have such a relation; row reduction makes the adversarial construction
    /// explicit instead of relying on a hard-coded lucky collision.
    fn ext3_projection_kernel(weights: &[Field64_3]) -> Vec<F> {
        let columns = weights.len();
        assert!(columns > 3);
        let mut matrix = vec![vec![ArkGoldilocks::ZERO; columns]; 3];
        for (column, weight) in weights.iter().enumerate() {
            let coefficients: Vec<ArkGoldilocks> =
                ArkField::to_base_prime_field_elements(weight).collect();
            assert_eq!(coefficients.len(), 3);
            for row in 0..3 {
                matrix[row][column] = coefficients[row];
            }
        }

        let mut pivot_columns = Vec::new();
        let mut pivot_row = 0usize;
        for column in 0..columns {
            let Some(nonzero_row) =
                (pivot_row..3).find(|&row| matrix[row][column] != ArkGoldilocks::ZERO)
            else {
                continue;
            };
            matrix.swap(pivot_row, nonzero_row);
            let inverse = matrix[pivot_row][column]
                .inverse()
                .expect("nonzero pivot is invertible");
            for entry in &mut matrix[pivot_row] {
                *entry *= inverse;
            }
            let pivot = matrix[pivot_row].clone();
            for row in 0..3 {
                if row == pivot_row {
                    continue;
                }
                let factor = matrix[row][column];
                for next_column in column..columns {
                    matrix[row][next_column] -= factor * pivot[next_column];
                }
            }
            pivot_columns.push(column);
            pivot_row += 1;
            if pivot_row == 3 {
                break;
            }
        }

        let free_column = (0..columns)
            .find(|column| !pivot_columns.contains(column))
            .expect("four Ext3 weights must have a free base-field column");
        let mut kernel = vec![ArkGoldilocks::ZERO; columns];
        kernel[free_column] = ArkGoldilocks::ONE;
        for (row, &pivot_column) in pivot_columns.iter().enumerate() {
            kernel[pivot_column] = -matrix[row][free_column];
        }
        kernel.into_iter().map(ark_to_plonky2).collect()
    }

    #[test]
    fn test_bad_order_ext3_index_challenge_has_a_claim_kernel() {
        const CONSTITUENT_WIDTH: usize = 4;

        // Deliberately wrong ordering: expose the Ext3 index point while every
        // claim slot is still empty, then let the prover select claim values.
        let empty: &[F] = &[];
        let empty_claims = [empty; 4 * NUM_SPLIT_COMMITMENTS];
        let mut bad_order_transcript = Transcript::new();
        bad_order_transcript.domain_separate("deliberate-bad-order-model");
        let early_index_points = absorb_claims_and_sample_index_points(
            &mut bad_order_transcript,
            &empty_claims,
            constituent_index_bits(CONSTITUENT_WIDTH),
        );
        let early_index_point = &early_index_points[0];

        let weights: Vec<Field64_3> = (0..CONSTITUENT_WIDTH)
            .map(|constituent| {
                let mut unit = vec![F::ZERO; CONSTITUENT_WIDTH];
                unit[constituent] = F::ONE;
                fold_constituent_claim(&unit, CONSTITUENT_WIDTH, early_index_point)
            })
            .collect();
        let kernel = ext3_projection_kernel(&weights);
        assert!(kernel.iter().any(|&delta| delta != F::ZERO));
        assert_eq!(
            fold_constituent_claim(&kernel, CONSTITUENT_WIDTH, early_index_point),
            Field64_3::from(0u64),
            "constructed delta is not in the early-challenge projection kernel"
        );

        let honest = vec![
            F::from_canonical_u64(3),
            F::from_canonical_u64(5),
            F::from_canonical_u64(7),
            F::from_canonical_u64(11),
        ];
        let forged: Vec<F> = honest
            .iter()
            .zip(&kernel)
            .map(|(&value, &delta)| value + delta)
            .collect();
        assert_ne!(honest, forged);
        assert_eq!(
            fold_constituent_claim(&honest, CONSTITUENT_WIDTH, early_index_point),
            fold_constituent_claim(&forged, CONSTITUENT_WIDTH, early_index_point),
            "bad-order model did not preserve the projected claim"
        );
    }

    #[test]
    fn test_constituent_fold_is_lsb_first_and_uses_all_ext3_limbs() {
        let u0 = Field64_3::new(
            ArkGoldilocks::from(2u64),
            ArkGoldilocks::from(3u64),
            ArkGoldilocks::from(5u64),
        );
        let u1 = Field64_3::new(
            ArkGoldilocks::from(7u64),
            ArkGoldilocks::from(11u64),
            ArkGoldilocks::from(13u64),
        );
        let values = [
            F::from_canonical_u64(17),
            F::from_canonical_u64(19),
            F::from_canonical_u64(23),
            F::from_canonical_u64(29),
        ];
        let one = Field64_3::from(1u64);
        let [v0, v1, v2, v3] = values.map(|value| Field64_3::from(value.to_canonical_u64()));
        let expected_lsb = v0 * (one - u0) * (one - u1)
            + v1 * u0 * (one - u1)
            + v2 * (one - u0) * u1
            + v3 * u0 * u1;
        assert_eq!(fold_constituent_claim(&values, 4, &[u0, u1]), expected_lsb);
        assert_ne!(
            fold_constituent_claim(&values, 4, &[u1, u0]),
            expected_lsb,
            "MSB-first coordinate order was indistinguishable"
        );

        let changed_c1 = Field64_3::new(
            ArkGoldilocks::from(2u64),
            ArkGoldilocks::from(4u64),
            ArkGoldilocks::from(5u64),
        );
        let changed_c2 = Field64_3::new(
            ArkGoldilocks::from(2u64),
            ArkGoldilocks::from(3u64),
            ArkGoldilocks::from(6u64),
        );
        assert_ne!(
            fold_constituent_claim(&values, 4, &[changed_c1, u1]),
            expected_lsb,
            "c1 limb was ignored"
        );
        assert_ne!(
            fold_constituent_claim(&values, 4, &[changed_c2, u1]),
            expected_lsb,
            "c2 limb was ignored"
        );
    }
}
