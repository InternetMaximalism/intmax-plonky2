/// Proof structure for the MLE-native proving system.
///
/// Architecture: each of the four ordered constituent groups is packed into
/// one bivariate MLE `F(row, constituent_index)`. The index axis is padded to
/// the next power of two with zero columns. After all terminal claims are
/// transcript-bound, an Ext3 index point folds each claimed constituent vector
/// and WHIR opens the corresponding packed commitment. This keeps the complete
/// constituent binding while avoiding a Merkle row whose width is the full
/// circuit schema.
use plonky2_field::types::Field;

use crate::commitment::whir_pcs::WhirEvalProof;
use crate::permutation::lookup::LookupProof;
pub use crate::protocol_schema::{
    GROUP_AUXILIARY, GROUP_INVERSE_HELPERS, GROUP_PREPROCESSED, GROUP_WITNESS,
    MLE_PROTOCOL_VERSION, NUM_PACKED_VECTORS_PER_GROUP, NUM_SPLIT_COMMITMENTS,
};
use crate::sumcheck::types::SumcheckProof;

// The generated constants above are driven by `protocol/mle_whir_v1.json`,
// shared with the Solidity verifier. They fix the four separately committed
// packed groups and their canonical order: preprocessed, witness, inverse
// helpers, auxiliary. Keep the public re-exports here for the existing
// proof/verifier API.

/// Schema-bound number of constituent slots. Shorter groups occupy the prefix
/// fixed by their group schema and the remaining index-domain slots are zero.
pub fn constituent_group_width(
    num_constants: usize,
    num_routed_wires: usize,
    num_wires: usize,
) -> usize {
    (num_constants + num_routed_wires)
        .max(num_wires)
        .max(2 * num_routed_wires)
        .max(2)
}

/// Number of binary variables used by the packed constituent-index axis.
pub fn constituent_index_bits(constituent_width: usize) -> usize {
    assert!(constituent_width > 0, "constituent width must be non-zero");
    constituent_width.next_power_of_two().trailing_zeros() as usize
}

/// Total variable count of a packed `(row, constituent_index)` group MLE.
pub fn packed_group_num_vars(degree_bits: usize, constituent_width: usize) -> usize {
    degree_bits + constituent_index_bits(constituent_width)
}

/// Verification key for the MLE proving system.
///
/// Contains the WHIR commitment root for the preprocessed polynomials
/// (constants + sigmas), computed once during circuit setup.
///
/// SECURITY: The preprocessed_commitment_root binds the verifier to a specific
/// set of gate selectors, constant values, and permutation routing. Without this,
/// an attacker could substitute fabricated constants/sigmas that trivially satisfy
/// all constraints.
#[derive(Clone, Debug)]
pub struct MleVerificationKey<F: Field> {
    pub protocol_version: u64,
    pub constituent_width: usize,
    /// Circuit digest (verifying key hash) — 4 Goldilocks field elements.
    pub circuit_digest: Vec<F>,
    /// WHIR commitment root for the packed preprocessed constituent group.
    pub preprocessed_commitment_root: Vec<u8>,
    /// Number of constant columns in the circuit.
    pub num_constants: usize,
    /// Number of routed wire columns (sigma permutation columns).
    pub num_routed_wires: usize,
    /// Coset shifts defining the circuit's identity permutation columns.
    pub k_is: Vec<F>,
    /// Powers of the circuit evaluation subgroup generator.
    pub subgroup_gen_powers: Vec<F>,
}

/// A complete MLE proof for a Plonky2 circuit.
///
/// Version 1 commits the ordered constituent columns before their corresponding
/// batching/query challenges and binds every terminal value directly through
/// the grouped WHIR opening statement.
#[derive(Clone, Debug)]
pub struct MleProof<F: Field> {
    /// ABI/proof schema discriminator. Version 0 encodings are not accepted.
    pub protocol_version: u64,
    /// Schema-bound count of constituent slots before power-of-two index
    /// padding. WHIR itself commits one packed vector per group.
    pub constituent_width: usize,
    /// Circuit digest (verifying key hash) — 4 Goldilocks field elements.
    pub circuit_digest: Vec<F>,

    // ── Grouped packed WHIR PCS ────────────────────────────────────────
    /// Single grouped WHIR evaluation proof covering all four ordered
    /// commitments at all four terminal points.
    pub whir_eval_proof: WhirEvalProof,
    /// Preprocessed commitment root (32 bytes, for VK binding check).
    pub preprocessed_root: Vec<u8>,
    /// Witness commitment root (32 bytes).
    pub witness_root: Vec<u8>,

    // ── Preprocessed batch evaluation at r ──────────────────────────────
    pub preprocessed_eval_value: F,
    pub preprocessed_batch_r: F,
    /// Individual evals at r: [const_0..const_C, sigma_0..sigma_R].
    pub preprocessed_individual_evals: Vec<F>,

    // ── Witness batch evaluation at r ───────────────────────────────────
    pub witness_eval_value: F,
    pub witness_batch_r: F,
    /// Individual evals at r: [wire_0..wire_W].
    pub witness_individual_evals: Vec<F>,

    // ── Auxiliary polynomial (C̃ + h̃, fourth constituent group) ──
    /// Root of the ordered constituent group `[C̃, h̃, 0, …]`.
    pub aux_commitment_root: Vec<u8>,
    pub aux_batch_r: F,
    /// Directly PCS-bound C̃(r) opening.
    pub aux_constraint_eval: F,
    /// Directly PCS-bound h̃(r) opening.
    pub aux_perm_eval: F,
    /// Auxiliary batched evaluation at r: P_aux(r) = C̃(r) + batch_r_aux · h̃(r).
    pub aux_eval_value: F,

    // ── Sumcheck output ────────────────────────────────────────────────
    /// Combined sumcheck output point r.
    pub sumcheck_challenges: Vec<F>,

    // ── Combined sumcheck proof ────────────────────────────────────────
    /// Single sumcheck proof for: eq(τ,b)·C(b) + μ·eq(τ_perm,b)·h(b) = 0.
    pub combined_proof: SumcheckProof<F>,
    /// Lookup proofs (one per lookup table, empty if no lookups).
    pub lookup_proofs: Vec<LookupProof<F>>,

    // ── Public data ────────────────────────────────────────────────────
    pub public_inputs: Vec<F>,
    pub public_inputs_hash: plonky2::hash::hash_types::HashOut<F>,
    /// Fiat-Shamir challenges.
    pub alpha: F,
    pub beta: F,
    pub gamma: F,
    pub tau: Vec<F>,
    pub tau_perm: Vec<F>,
    /// Combined sumcheck combination scalar.
    pub mu: F,
    /// Circuit dimensions.
    pub num_wires: usize,
    pub num_routed_wires: usize,
    pub num_constants: usize,

    // ── Permutation argument context (Issue #2) ────────────────────────
    /// Coset shifts k_is from Plonky2's permutation routing
    /// (id[row][col] = k_is[col] * subgroup[row]). VK-bound public data.
    pub k_is: Vec<F>,
    /// Powers g^{2^i} of the multiplicative subgroup generator g,
    /// for i = 0..degree_bits. Used to evaluate the subgroup MLE at the
    /// sumcheck point r via Π_i ((1 - r_i) + r_i · g^{2^i}). VK-bound public data.
    pub subgroup_gen_powers: Vec<F>,

    // ═══════════════════════════════════════════════════════════════════
    // Phased logUp argument — Issue R2-#2 (paper §4.2)
    //
    // Auxiliary inverse helpers A_j(b) = 1/D_j^id(b), B_j(b) = 1/D_j^σ(b)
    // are committed via WHIR (commit_additional, after β,γ are squeezed)
    // and bound via two sumchecks:
    //   Φ_inv: zero-check on A_j·D_j^id − 1 = 0 and B_j·D_j^σ − 1 = 0  (deg 3)
    //   Φ_h:   linear sumcheck on H = Σ_j (A_j − B_j), claimed sum = 0
    //
    // The terminal checks reconstruct predictions from constituent values that
    // are individually bound by the grouped WHIR statement.
    // a_j(r_inv), b_j(r_inv), w_j(r_inv), σ_j(r_inv), g_sub(r_inv) for Φ_inv,
    // and a_j(r_h), b_j(r_h) for Φ_h. No 1/x is evaluated by the verifier.
    // ═══════════════════════════════════════════════════════════════════
    /// Commitment root for the packed inverse-helper constituent group
    /// `[A_0, …, A_{W_R-1}, B_0, …, B_{W_R-1}]`. Committed after `(β, γ)`
    /// are squeezed and before its batching/query challenges.
    pub inverse_helpers_root: Vec<u8>,
    /// Legacy scalar batch consistency challenge for the inverse-helper claims.
    pub inverse_helpers_batch_r: F,
    /// Φ_inv sumcheck challenge point (length = degree_bits).
    pub inv_sumcheck_challenges: Vec<F>,
    /// Φ_inv sumcheck proof (round polys of degree ≤ 3).
    pub inv_sumcheck_proof: SumcheckProof<F>,
    /// Φ_h sumcheck challenge point (length = degree_bits).
    pub h_sumcheck_challenges: Vec<F>,
    /// Φ_h sumcheck proof (round polys of degree 1).
    pub h_sumcheck_proof: SumcheckProof<F>,
    /// Fiat-Shamir challenges for the v2 logUp protocol.
    pub lambda_inv: F,
    pub mu_inv: F,
    pub tau_inv: Vec<F>,
    /// Inverse helper individual evals at r_inv (length = 2 · num_routed_wires,
    /// laid out as `[a_0, a_1, …, a_{W_R-1}, b_0, …, b_{W_R-1}]`).
    pub inverse_helpers_evals_at_r_inv: Vec<F>,
    /// Inverse helper individual evals at r_h (same layout).
    pub inverse_helpers_evals_at_r_h: Vec<F>,
    /// Witness individual evals at r_inv (needed for Φ_inv terminal check).
    pub witness_individual_evals_at_r_inv: Vec<F>,
    /// Full preprocessed individual evals at r_inv (needed for batch
    /// consistency with `preprocessed_eval_value_at_r_inv` ↔ WHIR Ext3 eval).
    /// Layout `[const_0 .. const_{C-1}, sigma_0 .. sigma_{R-1}]`.
    /// The sigma subset (indices `[num_constants..num_constants+num_routed]`)
    /// feeds the Φ_inv terminal check; the const subset is unused there but
    /// required by the batch identity Σ batch_r_pre^i · eval_i.
    pub preprocessed_individual_evals_at_r_inv: Vec<F>,
    /// Subgroup MLE g_sub(r_inv) — verifier recomputes this from
    /// `subgroup_gen_powers` and checks consistency.
    pub g_sub_eval_at_r_inv: F,
    /// Witness batch eval (Goldilocks) at r_inv, for batch consistency.
    pub witness_eval_value_at_r_inv: F,
    /// Preprocessed batch eval (Goldilocks) at r_inv, for batch consistency.
    pub preprocessed_eval_value_at_r_inv: F,

    // ═══════════════════════════════════════════════════════════════════
    // Gate-formula binding — Issue R2-#1 (paper §7.3)
    //
    // A standalone Φ_gate zero-check sumcheck closes the gap where the
    // legacy `aux_constraint_eval` oracle is not the polynomially-correct
    // evaluation of the gate constraint formula at a random point. Instead
    // of trusting C̃(r) via a single WHIR commit, we run:
    //
    //   Φ_gate(x) := eq(τ_gate, x) · flatten_ext(
    //                    Σ_j α^j · c_j( lift(W_k(x)), lift(const_k(x)) ),
    //                    ext_challenge
    //                )
    //
    // claimed sum = 0. The verifier terminal check calls the Plonky2 gate
    // evaluator at `r_gate_v2` with PCS-bound individual wire/const evals.
    // All quantities are multilinear or polynomial over base field points,
    // so no MLE-non-commutativity gap remains.
    // ═══════════════════════════════════════════════════════════════════
    /// Extension-combine challenge — re-derived in the verifier but stored
    /// here so fixture consumers (Solidity) can absorb it deterministically.
    pub ext_challenge: F,
    /// Fiat-Shamir point `τ_gate` for the Φ_gate zero-check.
    pub tau_gate: Vec<F>,
    /// Φ_gate sumcheck proof (round polys of degree
    /// `1 + common_data.quotient_degree_factor`).
    pub gate_sumcheck_proof: SumcheckProof<F>,
    /// Φ_gate sumcheck output point `r_gate_v2` (length = degree_bits).
    pub gate_sumcheck_challenges: Vec<F>,
    /// Witness individual evals at `r_gate_v2` — one per wire column,
    /// required by the terminal check (`evaluate_gate_constraints`).
    pub witness_individual_evals_at_r_gate_v2: Vec<F>,
    /// Full preprocessed individual evals at `r_gate_v2`: layout
    /// `[const_0..const_{C-1}, sigma_0..sigma_{R-1}]`. The constants subset
    /// feeds the Φ_gate terminal check; the sigma subset is unused there
    /// but required for batch consistency with the WHIR Ext3 eval.
    pub preprocessed_individual_evals_at_r_gate_v2: Vec<F>,
    /// Witness batch eval (Goldilocks) at `r_gate_v2`.
    pub witness_eval_value_at_r_gate_v2: F,
    /// Preprocessed batch eval (Goldilocks) at `r_gate_v2`.
    pub preprocessed_eval_value_at_r_gate_v2: F,
}
