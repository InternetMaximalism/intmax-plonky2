/// JSON fixture generation and parsing for Solidity verification.
///
/// SECURITY: All Goldilocks field elements MUST be serialized as decimal strings,
/// NOT as JSON numbers. JSON numbers use IEEE 754 double precision (53-bit mantissa),
/// which silently truncates values > 2^53. Goldilocks field elements can be up to
/// 2^64 - 2^32 ≈ 1.8 × 10^19, far exceeding the safe integer range.
///
/// Example of precision loss:
///   Original:  18089690094123470162
///   JSON num:  18089690094123470848  (off by 686!)
///   As string: "18089690094123470162" (exact)
use ark_ff::PrimeField as ArkPrimeField;
use plonky2::gates::arithmetic_base::ArithmeticGate;
use plonky2::gates::arithmetic_extension::ArithmeticExtensionGate;
use plonky2::gates::base_sum::BaseSumGate;
use plonky2::gates::constant::ConstantGate;
use plonky2::gates::coset_interpolation::CosetInterpolationGate;
use plonky2::gates::exponentiation::ExponentiationGate;
use plonky2::gates::gate::GateRef;
use plonky2::gates::multiplication_extension::MulExtensionGate;
use plonky2::gates::noop::NoopGate;
use plonky2::gates::poseidon::PoseidonGate;
use plonky2::gates::poseidon_mds::PoseidonMdsGate;
use plonky2::gates::public_input::PublicInputGate;
use plonky2::gates::random_access::RandomAccessGate;
use plonky2::gates::reducing::ReducingGate;
use plonky2::gates::reducing_extension::ReducingExtensionGate;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2_field::extension::Extendable;
use plonky2_field::types::PrimeField64;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};
use whir::algebra::fields::Field64 as ArkGoldilocks;

use crate::commitment::whir_pcs::{WhirPCS, WHIR_SESSION_SPLIT};
use crate::proof::{
    packed_group_num_vars, MleProof, MLE_PROTOCOL_VERSION, NUM_PACKED_VECTORS_PER_GROUP,
    NUM_SPLIT_COMMITMENTS,
};
use crate::sumcheck::types::SumcheckProof;

// ═══════════════════════════════════════════════════════════════════════════
//  Serializable fixture types (all field elements as strings)
// ═══════════════════════════════════════════════════════════════════════════

/// A complete serializable proof fixture for Solidity consumption.
///
/// The version-one layout contains one grouped WHIR proof over four packed
/// commitments and four terminal points.
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ProofFixture {
    pub protocol_version: u64,
    pub constituent_width: usize,
    pub circuit_digest: Vec<String>,

    // ── Packed WHIR PCS (four ordered constituent groups) ──────────────
    pub preprocessed_commitment_root: String,
    pub witness_commitment_root: String,
    pub whir_transcript: String,
    pub whir_hints: String,
    pub preprocessed_eval_value: String,
    pub preprocessed_batch_r: String,
    pub preprocessed_individual_evals: Vec<String>,
    pub witness_eval_value: String,
    pub witness_batch_r: String,
    pub witness_individual_evals: Vec<String>,

    // ── Auxiliary constituent group ────────────────────────────────────
    pub aux_commitment_root: String,
    pub aux_batch_r: String,
    pub aux_constraint_eval: String,
    pub aux_perm_eval: String,
    pub aux_eval_value: String,

    // ── Evaluation point (combined sumcheck output r) ──────────────────
    pub evaluation_point: Vec<Ext3Fixture>,

    // ── Combined sumcheck proof ────────────────────────────────────────
    pub combined_proof: SumcheckFixture,

    // ── Public data ────────────────────────────────────────────────────
    pub public_inputs: Vec<String>,
    pub alpha: String,
    pub beta: String,
    pub gamma: String,
    pub mu: String,
    pub tau: Vec<String>,
    pub tau_perm: Vec<String>,
    pub num_wires: usize,
    pub num_routed_wires: usize,
    pub num_constants: usize,
    pub degree_bits: usize,

    // ── Permutation argument context (Issue #2) ────────────────────────
    /// Coset shifts k_is: id_col(b) = k_is[col] · subgroup[b] in field encoding.
    pub k_is: Vec<String>,
    /// Powers g^{2^i} of the subgroup generator, length = degree_bits.
    /// Used to evaluate subgroup_MLE(r) = Π_i ((1-r_i) + r_i · g^{2^i}).
    pub subgroup_gen_powers: Vec<String>,

    // ── v2 logUp soundness fix (Issue R2-#2) ───────────────────────────
    pub inverse_helpers_commitment_root: String,
    pub inverse_helpers_batch_r: String,
    pub inv_sumcheck_challenges: Vec<String>,
    pub inv_sumcheck_proof: SumcheckFixture,
    pub h_sumcheck_challenges: Vec<String>,
    pub h_sumcheck_proof: SumcheckFixture,
    pub lambda_inv: String,
    pub mu_inv: String,
    pub tau_inv: Vec<String>,
    pub inverse_helpers_evals_at_r_inv: Vec<String>,
    pub inverse_helpers_evals_at_r_h: Vec<String>,
    pub witness_individual_evals_at_r_inv: Vec<String>,
    /// Full preprocessed evals at r_inv `[const_0..const_C, sigma_0..sigma_R]`.
    pub preprocessed_individual_evals_at_r_inv: Vec<String>,
    pub g_sub_eval_at_r_inv: String,
    pub witness_eval_value_at_r_inv: String,
    pub preprocessed_eval_value_at_r_inv: String,

    // ── v2 gate binding fix (Issue R2-#1) ──────────────────────────────
    pub ext_challenge: String,
    pub tau_gate: Vec<String>,
    pub gate_sumcheck_challenges: Vec<String>,
    pub gate_sumcheck_proof: SumcheckFixture,
    pub witness_individual_evals_at_r_gate_v2: Vec<String>,
    pub preprocessed_individual_evals_at_r_gate_v2: Vec<String>,
    pub witness_eval_value_at_r_gate_v2: String,
    pub preprocessed_eval_value_at_r_gate_v2: String,

    // ── Circuit metadata for Φ_gate terminal check (Issue R2-#1) ───────
    /// Public inputs hash (4 Goldilocks elements, Poseidon digest).
    /// Fixed-width Poseidon digest. Using an array is intentional: accepting
    /// a JSON tail here would let fixture/deployment tooling silently ignore a
    /// fifth limb even though both Rust `HashOut` and the Solidity ABI bind
    /// exactly four limbs.
    pub public_inputs_hash: [String; 4],
    /// Number of selector columns.
    pub num_selectors: usize,
    /// Upper bound on the filtered gate-constraint polynomial degree
    /// (`common_data.quotient_degree_factor`). Φ_gate round-poly degree
    /// per variable = `quotient_degree_factor + 2`.
    pub quotient_degree_factor: usize,
    /// Total number of gate-constraint slots (`common_data.num_gate_constraints`).
    pub num_gate_constraints: usize,
    /// Per-gate metadata (same order as `common_data.gates`, which plonky2
    /// sorts ascending by gate.degree()).
    pub gates: Vec<GateInfoFixture>,

    // ── WHIR config ─────────────────────────────────────────────────────
    /// WHIR protocol ID (hex, 0x-prefixed, 64 bytes).
    pub whir_protocol_id: String,
    /// WHIR session ID for split-commit mode (hex, 0x-prefixed, 32 bytes).
    pub whir_split_session_id: String,
    /// WHIR protocol parameters for on-chain verification.
    pub whir_params: WhirParamsFixture,
}

/// Ext3 field element fixture {c0, c1, c2} as decimal strings.
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(deny_unknown_fields)]
pub struct Ext3Fixture {
    pub c0: String,
    pub c1: String,
    pub c2: String,
}

/// Per-gate metadata needed by the Solidity Φ_gate terminal check.
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct GateInfoFixture {
    /// Human-readable gate id string (`gate.id()`). Not consumed by the
    /// on-chain verifier — retained as diagnostic context so fixtures
    /// remain self-describing.
    pub name: String,
    /// Classifier consumed by Plonky2GateEvaluator.sol:
    ///   0 = NoopGate, 1 = ConstantGate, 2 = PublicInputGate,
    ///   3 = ArithmeticGate, 4 = PoseidonGate,
    ///   5 = PoseidonMdsGate, 6 = ArithmeticExtensionGate,
    ///   7 = MulExtensionGate, 8 = ExponentiationGate,
    ///   9 = BaseSumGate, 10 = ReducingGate, 11 = ReducingExtensionGate,
    ///   12 = RandomAccessGate, 13 = CosetInterpolationGate,
    ///   255 = unsupported.
    pub gate_id: u8,
    /// Which selector column drives this gate (index into
    /// `preprocessed_individual_evals_at_r_gate_v2[0..num_selectors]`).
    pub selector_index: u8,
    /// Start of the gate's selector group (inclusive).
    pub group_start: u8,
    /// End of the gate's selector group (exclusive).
    pub group_end: u8,
    /// Row index of this gate inside `common_data.gates` (ascending by degree).
    pub gate_row_index: u8,
    /// `gate.num_constraints()` — how many slots this gate's eval writes to.
    pub num_constraints: u16,
    /// Primary gate-specific parameter:
    ///   ArithmeticGate / ArithmeticExtensionGate / MulExtensionGate: `num_ops`
    ///   ConstantGate: `num_consts`
    ///   BaseSumGate: `num_limbs`
    ///   ReducingGate / ReducingExtensionGate: `num_coeffs`
    ///   ExponentiationGate: `num_power_bits`
    ///   RandomAccessGate: `bits`
    ///   CosetInterpolationGate: `subgroup_bits`
    ///   Else: 0
    pub num_or_consts: u16,
    /// Secondary gate-specific parameter:
    ///   BaseSumGate: `B` (base) — not currently exposed via `gate.id()`, so
    ///     we hardcode 2 for `BaseSumGate<2>` occurrences (only one in scope).
    ///   RandomAccessGate: `num_copies`
    ///   CosetInterpolationGate: `degree`
    ///   Else: 0
    pub param2: u16,
    /// Tertiary gate-specific parameter:
    ///   RandomAccessGate: `num_extra_constants`
    ///   Else: 0
    pub param3: u16,
}

/// WHIR protocol parameters for Solidity verifier.
/// Matches SpongefishWhirVerify.WhirParams struct.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WhirParamsFixture {
    pub num_variables: usize,
    pub folding_factor: usize,
    pub num_vectors: usize,
    /// Number of separate split-commit vectors: preprocessed + witness + auxiliary +
    /// inverse_helpers. See [`crate::proof::NUM_SPLIT_COMMITMENTS`].
    pub num_commitments: usize,
    pub out_domain_samples: usize,
    pub in_domain_samples: usize,
    pub initial_sumcheck_rounds: usize,
    pub num_rounds: usize,
    pub final_sumcheck_rounds: usize,
    pub final_size: usize,
    pub initial_codeword_length: usize,
    pub initial_merkle_depth: usize,
    pub initial_domain_generator: String,
    pub initial_interleaving_depth: usize,
    pub initial_num_variables: usize,
    pub initial_coset_size: usize,
    pub initial_num_cosets: usize,
    pub initial_sumcheck_pow_threshold: String,
    pub final_pow_threshold: String,
    pub final_sumcheck_pow_threshold: String,
    pub rounds: Vec<WhirRoundParamsFixture>,
}

/// Per-round WHIR parameters.
/// Matches SpongefishWhirVerify.RoundParams struct exactly.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct WhirRoundParamsFixture {
    pub codeword_length: usize,
    pub merkle_depth: usize,
    pub domain_generator: String,
    pub in_domain_samples: usize,
    pub out_domain_samples: usize,
    pub sumcheck_rounds: usize,
    pub interleaving_depth: usize,
    pub coset_size: usize,
    pub num_cosets: usize,
    pub num_variables: usize,
    pub pow_threshold: String,
    pub sumcheck_pow_threshold: String,
}

/// Serializable sumcheck proof.
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SumcheckFixture {
    /// Round polynomials, each as a vector of evaluation strings.
    pub round_polys: Vec<Vec<String>>,
}

// ═══════════════════════════════════════════════════════════════════════════
//  Conversion from MleProof to ProofFixture
// ═══════════════════════════════════════════════════════════════════════════

fn field_to_string<F: PrimeField64>(f: F) -> String {
    f.to_canonical_u64().to_string()
}

fn field_vec_to_strings<F: PrimeField64>(v: &[F]) -> Vec<String> {
    v.iter().map(|f| field_to_string(*f)).collect()
}

fn sumcheck_to_fixture<F: PrimeField64>(proof: &SumcheckProof<F>) -> SumcheckFixture {
    SumcheckFixture {
        round_polys: proof
            .round_polys
            .iter()
            .map(|rp| field_vec_to_strings(&rp.evaluations))
            .collect(),
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    format!(
        "0x{}",
        bytes
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect::<String>()
    )
}

fn log2_of(n: usize) -> usize {
    assert!(n.is_power_of_two());
    n.trailing_zeros() as usize
}

/// Compute the primitive root of unity for a domain of given size (Goldilocks field).
fn gl_root_of_unity(size: usize) -> u64 {
    use ark_ff::FftField;
    let gen = ArkGoldilocks::get_root_of_unity(size as u64).expect("No root of unity");
    gen.into_bigint().0[0]
}

/// Compute WHIR session_id from a session name string.
fn compute_whir_session_id(session_name: &str) -> Vec<u8> {
    let mut session_bytes = Vec::new();
    ciborium::into_writer(&session_name, &mut session_bytes).expect("CBOR serialization failed");
    let mut h = Keccak256::new();
    h.update(&session_bytes);
    h.finalize().to_vec()
}

/// Extract WHIR protocol parameters from config for Solidity verifier.
/// Returns (params, protocol_id, split_session_id).
fn extract_whir_params(
    degree_bits: usize,
    constituent_width: usize,
) -> (WhirParamsFixture, Vec<u8>, Vec<u8>) {
    let num_variables = packed_group_num_vars(degree_bits, constituent_width);
    let pcs = WhirPCS::for_constituents_v1(num_variables, NUM_PACKED_VECTORS_PER_GROUP);
    let size = 1 << num_variables;
    let config = pcs.constituent_config(size);

    let folding_factor = pcs.params.folding_factor;
    let num_vectors = pcs.params.batch_size;
    // SECURITY (audit M-10): NOT a literal. `preprocessed + witness` was correct before v2 added
    // the auxiliary and inverse-helper commitments; the stale `2` was then corrected by hand in
    // three separate Solidity consumers instead of here, so the exported fixture was simply wrong
    // data. This value and Solidity's verifier constant are generated from the same canonical
    // `protocol/mle_whir_v1.json` artifact.
    let num_commitments = NUM_SPLIT_COMMITMENTS;
    let out_domain_samples = config.initial_committer.out_domain_samples;
    let in_domain_samples = config.initial_committer.in_domain_samples;
    let initial_sumcheck_rounds = config.initial_sumcheck.num_rounds;
    let num_rounds = config.round_configs.len();
    let final_sumcheck_rounds = config.final_sumcheck.num_rounds;

    // Final size: after all folding, what remains
    let mut remaining_vars = num_variables - pcs.params.initial_folding_factor;
    for _ in &config.round_configs {
        remaining_vars = remaining_vars.saturating_sub(folding_factor);
    }
    let final_size = 1 << remaining_vars;

    let initial_codeword_length = config.initial_committer.codeword_length;
    let initial_merkle_depth = log2_of(initial_codeword_length);
    let initial_domain_generator = gl_root_of_unity(initial_codeword_length);

    // Initial committer additional params
    let initial_interleaving_depth = config.initial_committer.interleaving_depth;
    let initial_num_variables = config.initial_num_variables();
    let initial_mml = config.initial_committer.masked_message_length();
    let initial_coset_size = {
        let mut cs = initial_mml.next_power_of_two();
        while !initial_codeword_length.is_multiple_of(cs) {
            cs *= 2;
        }
        cs
    };
    let initial_num_cosets = initial_codeword_length / initial_coset_size;

    // Build per-round params using WHIR's own methods
    let rounds: Vec<WhirRoundParamsFixture> = config
        .round_configs
        .iter()
        .map(|rc| {
            let cl = rc.irs_committer.codeword_length;
            let mml = rc.irs_committer.masked_message_length();
            let cs = {
                let mut c = mml.next_power_of_two();
                while cl % c != 0 {
                    c *= 2;
                }
                c
            };
            let rv = rc.initial_num_variables();
            WhirRoundParamsFixture {
                codeword_length: cl,
                merkle_depth: log2_of(cl),
                domain_generator: gl_root_of_unity(cl).to_string(),
                in_domain_samples: rc.irs_committer.in_domain_samples,
                out_domain_samples: rc.irs_committer.out_domain_samples,
                sumcheck_rounds: rc.sumcheck.num_rounds,
                interleaving_depth: rc.irs_committer.interleaving_depth,
                coset_size: cs,
                num_cosets: cl / cs,
                num_variables: rv,
                pow_threshold: rc.pow.threshold.to_string(),
                sumcheck_pow_threshold: rc.sumcheck.round_pow.threshold.to_string(),
            }
        })
        .collect();

    let params_fixture = WhirParamsFixture {
        num_variables,
        folding_factor,
        num_vectors,
        num_commitments,
        out_domain_samples,
        in_domain_samples,
        initial_sumcheck_rounds,
        num_rounds,
        final_sumcheck_rounds,
        final_size,
        initial_codeword_length,
        initial_merkle_depth,
        initial_domain_generator: initial_domain_generator.to_string(),
        initial_interleaving_depth,
        initial_num_variables,
        initial_coset_size,
        initial_num_cosets,
        initial_sumcheck_pow_threshold: config.initial_sumcheck.round_pow.threshold.to_string(),
        final_pow_threshold: config.final_pow.threshold.to_string(),
        final_sumcheck_pow_threshold: config.final_sumcheck.round_pow.threshold.to_string(),
        rounds,
    };

    // Compute protocol_id: keccak256(0x00 || cbor(config)) || keccak256(0x01 || cbor(config))
    let protocol_id = {
        let mut config_bytes = Vec::new();
        ciborium::into_writer(&config, &mut config_bytes).expect("CBOR serialization failed");
        let first: [u8; 32] = {
            let mut h = Keccak256::new();
            h.update([0x00]);
            h.update(&config_bytes);
            h.finalize().into()
        };
        let second: [u8; 32] = {
            let mut h = Keccak256::new();
            h.update([0x01]);
            h.update(&config_bytes);
            h.finalize().into()
        };
        let mut result = vec![0u8; 64];
        result[..32].copy_from_slice(&first);
        result[32..].copy_from_slice(&second);
        result
    };

    // Compute session_id for split-commit mode
    let split_session_id = compute_whir_session_id(WHIR_SESSION_SPLIT);

    (params_fixture, protocol_id, split_session_id)
}

// ═══════════════════════════════════════════════════════════════════════════
//  Gate classification (audit finding M-10)
//
//  SECURITY: the values below drive `Plonky2GateEvaluator.sol`'s per-gate constraint evaluation.
//  Until 2026-08-30 they were scraped out of `format!("{:?}")` output with a
//  `.unwrap_or(0)` fallback and a `.max(2)` "default base", and an unrecognised gate was
//  mapped to the `255` sentinel. Every one of those three paths produces a WELL-FORMED
//  fixture, a valid `gatesDigest`, and a PASSING Rust `mle_verify` — with the on-chain
//  revert (or, worse, an evaluation against the WRONG number of constraints) as the only
//  signal, and only on a real submission on a real chain. That is exactly how
//  `ExponentiationGate` (id 8) shipped; see `doc/audit/why-gate8-was-missed.md` §8 (R3).
//
//  The classifier is therefore STRUCTURAL: it downcasts the gate through
//  `AnyGate::as_any` and reads the gate's own typed fields, so the parameters cannot
//  disagree with the circuit no matter how plonky2's `Debug`/`id()` rendering changes.
//  Anything it cannot resolve is a hard error naming the gate and the field — never a
//  guess, never a sentinel.
// ═══════════════════════════════════════════════════════════════════════════

/// The `(gate_id, num_or_consts, param2, param3)` tuple consumed by `Plonky2GateEvaluator.sol`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GateParams {
    pub gate_id: u8,
    pub num_or_consts: u16,
    pub param2: u16,
    pub param3: u16,
}

/// A gate whose on-chain parameters could not be established with certainty.
///
/// SECURITY: this type exists so that "I could not determine this parameter" can never be
/// rendered as a number. Every construction site names the gate and what specifically failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateClassificationError {
    /// `gate.id()` of the offending gate (or the raw id string, when parsing one).
    pub gate_name: String,
    /// What could not be established, and what to do about it.
    pub detail: String,
}

impl core::fmt::Display for GateClassificationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "gate `{}`: {}\nRefusing to write a fixture with a guessed on-chain gate parameter: \
             a wrong `numOrConsts` / `param2` / `param3` still hashes into a valid `gatesDigest` \
             and still passes the Rust verifier, but makes every on-chain verification evaluate \
             the wrong constraints (or revert).",
            self.gate_name, self.detail
        )
    }
}

impl std::error::Error for GateClassificationError {}

impl GateClassificationError {
    fn new(gate_name: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            gate_name: gate_name.into(),
            detail: detail.into(),
        }
    }
}

/// Narrow a gate parameter to the fixture's `u16`, hard-erroring instead of wrapping.
fn narrow_u16(gate_name: &str, field: &str, value: usize) -> Result<u16, GateClassificationError> {
    u16::try_from(value).map_err(|_| {
        GateClassificationError::new(
            gate_name,
            format!(
                "`{field}` = {value} does not fit the fixture's u16 (max {}); `as u16` would \
                 silently wrap it",
                u16::MAX
            ),
        )
    })
}

/// Narrow a gate row's index-like field to the fixture's `u8`, hard-erroring instead of wrapping.
fn narrow_u8(gate_name: &str, field: &str, value: usize) -> Result<u8, GateClassificationError> {
    u8::try_from(value).map_err(|_| {
        GateClassificationError::new(
            gate_name,
            format!(
                "`{field}` = {value} does not fit the fixture's u8 (max {}); `as u8` would \
                 silently wrap it and the fixture would name the WRONG selector column or row",
                u8::MAX
            ),
        )
    })
}

/// `BaseSumGate<B>`'s base is a const generic, so it can only be recovered by downcasting
/// against a concrete `B`. This is the set of bases the classifier can resolve structurally;
/// any other base is a hard error telling the maintainer to extend the list (NOT a silent
/// "default 2", which is what the pre-2026-08-30 `.max(2)` did).
pub const SUPPORTED_BASE_SUM_BASES: &[usize] = &[2, 3, 4, 5, 6, 7, 8, 16, 32, 64, 128, 256];

/// Classify a plonky2 gate STRUCTURALLY — from the gate's own typed data, never from its
/// `Debug` rendering — into the tuple `Plonky2GateEvaluator.sol` consumes.
///
/// SECURITY: returns `Err` rather than a sentinel or a zero for anything it cannot resolve.
/// See the module comment above and `src/utils/mle_prover.rs`'s export guard, which
/// re-derives these same values independently and compares them against what was serialized.
pub fn classify_gate<F: RichField + Extendable<D>, const D: usize>(
    gate: &GateRef<F, D>,
) -> Result<GateParams, GateClassificationError> {
    let name = gate.0.id();
    let any = gate.0.as_any();

    // NoopGate / PublicInputGate / PoseidonGate / PoseidonMdsGate are parameterless on-chain.
    if any.is::<NoopGate>() {
        return Ok(GateParams {
            gate_id: 0,
            num_or_consts: 0,
            param2: 0,
            param3: 0,
        });
    }
    if any.is::<ConstantGate>() {
        // `ConstantGate::num_consts` is `pub(crate)` upstream, but `Gate::num_constants()` IS
        // that field (`plonky2/src/gates/constant.rs:101-103`) and is public trait API, so this
        // is still a read of the gate's own typed data rather than a parse.
        let num_consts = gate.0.num_constants();
        return Ok(GateParams {
            gate_id: 1,
            num_or_consts: narrow_u16(&name, "num_consts", num_consts)?,
            param2: 0,
            param3: 0,
        });
    }
    if any.is::<PublicInputGate>() {
        return Ok(GateParams {
            gate_id: 2,
            num_or_consts: 0,
            param2: 0,
            param3: 0,
        });
    }
    if let Some(g) = any.downcast_ref::<ArithmeticGate>() {
        return Ok(GateParams {
            gate_id: 3,
            num_or_consts: narrow_u16(&name, "num_ops", g.num_ops)?,
            param2: 0,
            param3: 0,
        });
    }
    if any.is::<PoseidonGate<F, D>>() {
        return Ok(GateParams {
            gate_id: 4,
            num_or_consts: 0,
            param2: 0,
            param3: 0,
        });
    }
    if any.is::<PoseidonMdsGate<F, D>>() {
        return Ok(GateParams {
            gate_id: 5,
            num_or_consts: 0,
            param2: 0,
            param3: 0,
        });
    }
    if let Some(g) = any.downcast_ref::<ArithmeticExtensionGate<D>>() {
        return Ok(GateParams {
            gate_id: 6,
            num_or_consts: narrow_u16(&name, "num_ops", g.num_ops)?,
            param2: 0,
            param3: 0,
        });
    }
    if let Some(g) = any.downcast_ref::<MulExtensionGate<D>>() {
        return Ok(GateParams {
            gate_id: 7,
            num_or_consts: narrow_u16(&name, "num_ops", g.num_ops)?,
            param2: 0,
            param3: 0,
        });
    }
    if let Some(g) = any.downcast_ref::<ExponentiationGate<F, D>>() {
        return Ok(GateParams {
            gate_id: 8,
            num_or_consts: narrow_u16(&name, "num_power_bits", g.num_power_bits)?,
            param2: 0,
            param3: 0,
        });
    }

    // BaseSumGate<B>: `B` is a const generic, recoverable only by downcasting against a
    // concrete instantiation. Never defaulted.
    macro_rules! try_base_sum {
        ($($b:literal),* $(,)?) => {{
            let mut found: Option<Result<GateParams, GateClassificationError>> = None;
            $(
                if found.is_none() {
                    if let Some(g) = any.downcast_ref::<BaseSumGate<$b>>() {
                        found = Some((|| Ok(GateParams {
                            gate_id: 9,
                            num_or_consts: narrow_u16(&name, "num_limbs", g.num_limbs)?,
                            param2: narrow_u16(&name, "B (base)", $b)?,
                            param3: 0,
                        }))());
                    }
                }
            )*
            found
        }};
    }
    if let Some(result) = try_base_sum!(2, 3, 4, 5, 6, 7, 8, 16, 32, 64, 128, 256) {
        return result;
    }

    if let Some(g) = any.downcast_ref::<ReducingGate<D>>() {
        return Ok(GateParams {
            gate_id: 10,
            num_or_consts: narrow_u16(&name, "num_coeffs", g.num_coeffs)?,
            param2: 0,
            param3: 0,
        });
    }
    if let Some(g) = any.downcast_ref::<ReducingExtensionGate<D>>() {
        return Ok(GateParams {
            gate_id: 11,
            num_or_consts: narrow_u16(&name, "num_coeffs", g.num_coeffs)?,
            param2: 0,
            param3: 0,
        });
    }
    if let Some(g) = any.downcast_ref::<RandomAccessGate<F, D>>() {
        return Ok(GateParams {
            gate_id: 12,
            num_or_consts: narrow_u16(&name, "bits", g.bits)?,
            param2: narrow_u16(&name, "num_copies", g.num_copies)?,
            param3: narrow_u16(&name, "num_extra_constants", g.num_extra_constants)?,
        });
    }
    if let Some(g) = any.downcast_ref::<CosetInterpolationGate<F, D>>() {
        return Ok(GateParams {
            gate_id: 13,
            num_or_consts: narrow_u16(&name, "subgroup_bits", g.subgroup_bits)?,
            param2: narrow_u16(&name, "degree", g.degree)?,
            param3: 0,
        });
    }

    // A `BaseSumGate<B>` whose base is outside SUPPORTED_BASE_SUM_BASES lands here; say so
    // explicitly, because "extend the list" is a different fix from "port the gate".
    if name.starts_with("BaseSumGate") {
        return Err(GateClassificationError::new(
            name,
            format!(
                "this is a `BaseSumGate<B>` whose base `B` is not in \
                 SUPPORTED_BASE_SUM_BASES ({SUPPORTED_BASE_SUM_BASES:?}). The base is a const \
                 generic and can only be recovered by downcasting against a concrete `B`; add \
                 this one to the list in mle/src/fixture.rs. It must NOT be defaulted to 2 — \
                 `Plonky2GateEvaluator._evalBaseSum` would then check a base-2 decomposition of \
                 a base-B value and accept limbs the circuit forbids"
            ),
        ));
    }

    Err(GateClassificationError::new(
        name,
        "is not classified by plonky2_mle. It previously became the `255` sentinel: a \
         well-formed fixture, a valid `gatesDigest`, a PASSING Rust `mle_verify`, and an \
         on-chain revert (\"unsupported gate with non-zero filter\") with no signal until a real \
         submission on a real chain — exactly how gate 8 shipped on 2026-07-31. Port the gate to \
         Plonky2GateEvaluator.sol AND classify it here, or change the circuit so it is not \
         emitted. Do NOT relax this error and do NOT relax the on-chain revert",
    ))
}

// ─── Independent cross-check: recover the same parameters from `gate.id()` ────────────────
//
// SECURITY: this is deliberately NOT used by the exporter. It is the second, independent
// derivation that `tests/mle_gate_support.rs` runs over every checked-in
// `contracts/test/data/*_mle.json`, whose gate rows carry `gate.id()` verbatim in `name`. Two
// derivations from different sources (the live typed gate vs. the recorded name) agreeing is
// what makes a hand-edited or stale fixture detectable. Unlike the pre-2026-08-30 exporter it
// is STRICT: every field is required, nothing defaults, and an unknown gate is an error.

/// True when `id` names exactly `gate` (and not, say, `ExponentiationGateV2`).
fn id_names_gate(id: &str, gate: &str) -> bool {
    match id.strip_prefix(gate) {
        None => false,
        Some("") => true,
        // `Debug`-derived renderings continue with ` {`, `(`, `{` or `<`.
        Some(rest) => rest.starts_with([' ', '(', '{', '<']),
    }
}

/// Read `field: <digits>` out of a `Debug` struct rendering, requiring the key to sit at a
/// field boundary (`{ ` or `, `) so that `bits:` cannot match `subgroup_bits:`. Requires
/// exactly one occurrence and a parseable value — no fallback.
fn debug_field_u16(id: &str, field: &str) -> Result<u16, GateClassificationError> {
    let needle = format!("{field}:");
    let mut found: Option<u16> = None;
    let bytes = id.as_bytes();
    for (pos, _) in id.match_indices(&needle) {
        // The character before the key, skipping spaces, must open the struct or end a field.
        let mut i = pos;
        while i > 0 && bytes[i - 1] == b' ' {
            i -= 1;
        }
        if i > 0 && bytes[i - 1] != b'{' && bytes[i - 1] != b',' {
            continue;
        }
        let digits: String = id[pos + needle.len()..]
            .trim_start()
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect();
        let value = digits.parse::<u16>().map_err(|e| {
            GateClassificationError::new(
                id,
                format!("field `{field}` is present but not a u16 ({e}); refusing to default it"),
            )
        })?;
        if found.is_some_and(|prev| prev != value) {
            return Err(GateClassificationError::new(
                id,
                format!("field `{field}` occurs more than once with different values"),
            ));
        }
        found = Some(value);
    }
    found.ok_or_else(|| {
        GateClassificationError::new(
            id,
            format!(
                "field `{field}` is absent from the gate's `id()` string. The pre-2026-08-30 \
                 exporter substituted 0 here, which is a silently WRONG on-chain parameter"
            ),
        )
    })
}

/// Recover [`GateParams`] from a `gate.id()` string, strictly. See the block comment above.
pub fn parse_gate_params_from_id(id: &str) -> Result<GateParams, GateClassificationError> {
    let p = |gate_id, num_or_consts, param2, param3| {
        Ok(GateParams {
            gate_id,
            num_or_consts,
            param2,
            param3,
        })
    };
    if id_names_gate(id, "NoopGate") {
        p(0, 0, 0, 0)
    } else if id_names_gate(id, "ConstantGate") {
        p(1, debug_field_u16(id, "num_consts")?, 0, 0)
    } else if id_names_gate(id, "PublicInputGate") {
        p(2, 0, 0, 0)
    } else if id_names_gate(id, "ArithmeticGate") {
        p(3, debug_field_u16(id, "num_ops")?, 0, 0)
    } else if id_names_gate(id, "PoseidonGate") {
        p(4, 0, 0, 0)
    } else if id_names_gate(id, "PoseidonMdsGate") {
        p(5, 0, 0, 0)
    } else if id_names_gate(id, "ArithmeticExtensionGate") {
        p(6, debug_field_u16(id, "num_ops")?, 0, 0)
    } else if id_names_gate(id, "MulExtensionGate") {
        p(7, debug_field_u16(id, "num_ops")?, 0, 0)
    } else if id_names_gate(id, "ExponentiationGate") {
        p(8, debug_field_u16(id, "num_power_bits")?, 0, 0)
    } else if id_names_gate(id, "BaseSumGate") {
        // `BaseSumGate<B>::id()` is `format!("{self:?} + Base: {B}")`.
        let num_limbs = debug_field_u16(id, "num_limbs")?;
        let base_str = id.split(" + Base: ").nth(1).ok_or_else(|| {
            GateClassificationError::new(
                id,
                "no ` + Base: <B>` suffix, so the base is unknown. The pre-2026-08-30 exporter \
                 defaulted it to 2 via `.max(2)`, silently CLAIMING base 2 for a base-B gate",
            )
        })?;
        let base = base_str.trim().parse::<u16>().map_err(|e| {
            GateClassificationError::new(id, format!("` + Base:` suffix is not a u16 ({e})"))
        })?;
        p(9, num_limbs, base, 0)
    } else if id_names_gate(id, "ReducingExtensionGate") {
        p(11, debug_field_u16(id, "num_coeffs")?, 0, 0)
    } else if id_names_gate(id, "ReducingGate") {
        p(10, debug_field_u16(id, "num_coeffs")?, 0, 0)
    } else if id_names_gate(id, "RandomAccessGate") {
        p(
            12,
            debug_field_u16(id, "bits")?,
            debug_field_u16(id, "num_copies")?,
            debug_field_u16(id, "num_extra_constants")?,
        )
    } else if id_names_gate(id, "CosetInterpolationGate") {
        p(
            13,
            debug_field_u16(id, "subgroup_bits")?,
            debug_field_u16(id, "degree")?,
            0,
        )
    } else {
        Err(GateClassificationError::new(
            id,
            "is not a gate plonky2_mle classifies (and therefore not one \
             Plonky2GateEvaluator.sol can evaluate)",
        ))
    }
}

fn collect_gate_metadata<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
) -> Result<Vec<GateInfoFixture>, GateClassificationError> {
    let si = &common_data.selectors_info;
    common_data
        .gates
        .iter()
        .enumerate()
        .map(|(row, gate)| {
            let id = gate.0.id();
            let params = classify_gate::<F, D>(gate)?;
            let sel_idx = si.selector_indices[row];
            let group = &si.groups[sel_idx];
            Ok(GateInfoFixture {
                gate_id: params.gate_id,
                selector_index: narrow_u8(&id, "selector_index", sel_idx)?,
                group_start: narrow_u8(&id, "group_start", group.start)?,
                group_end: narrow_u8(&id, "group_end", group.end)?,
                gate_row_index: narrow_u8(&id, "gate_row_index", row)?,
                num_constraints: narrow_u16(&id, "num_constraints", gate.0.num_constraints())?,
                num_or_consts: params.num_or_consts,
                param2: params.param2,
                param3: params.param3,
                name: id,
            })
        })
        .collect()
}

/// Convert an MleProof to a ProofFixture for JSON serialization.
///
/// Generates the unified grouped-WHIR fixture format with one transcript and
/// hint stream covering the four ordered packed constituent commitments.
///
/// SECURITY: panics (rather than emitting a guessed parameter or the `255` sentinel) if any
/// gate in the circuit cannot be classified — see [`classify_gate`]. Callers that want the
/// error as a value should use [`try_proof_to_fixture`].
pub fn proof_to_fixture<F: RichField + Extendable<D> + PrimeField64, const D: usize>(
    proof: &MleProof<F>,
    common_data: &CommonCircuitData<F, D>,
    degree_bits: usize,
) -> ProofFixture {
    try_proof_to_fixture(proof, common_data, degree_bits)
        .unwrap_or_else(|e| panic!("cannot build an on-chain-usable fixture — {e}"))
}

/// Fallible form of [`proof_to_fixture`].
pub fn try_proof_to_fixture<F: RichField + Extendable<D> + PrimeField64, const D: usize>(
    proof: &MleProof<F>,
    common_data: &CommonCircuitData<F, D>,
    degree_bits: usize,
) -> Result<ProofFixture, GateClassificationError> {
    let (whir_params, protocol_id, split_session_id) =
        extract_whir_params(degree_bits, proof.constituent_width);

    // Commitment roots
    let pre_root_hex: String = proof
        .preprocessed_root
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect();

    let wit_root_hex: String = proof
        .witness_root
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect();

    Ok(ProofFixture {
        protocol_version: proof.protocol_version,
        constituent_width: proof.constituent_width,
        circuit_digest: field_vec_to_strings(&proof.circuit_digest),
        // Packed WHIR PCS
        preprocessed_commitment_root: format!("0x{pre_root_hex}"),
        witness_commitment_root: format!("0x{wit_root_hex}"),
        whir_transcript: hex_encode(&proof.whir_eval_proof.narg_string),
        whir_hints: hex_encode(&proof.whir_eval_proof.hints),
        preprocessed_eval_value: field_to_string(proof.preprocessed_eval_value),
        preprocessed_batch_r: field_to_string(proof.preprocessed_batch_r),
        preprocessed_individual_evals: field_vec_to_strings(&proof.preprocessed_individual_evals),
        witness_eval_value: field_to_string(proof.witness_eval_value),
        witness_batch_r: field_to_string(proof.witness_batch_r),
        witness_individual_evals: field_vec_to_strings(&proof.witness_individual_evals),
        // Auxiliary constituent group
        aux_commitment_root: hex_encode(&proof.aux_commitment_root),
        aux_batch_r: field_to_string(proof.aux_batch_r),
        aux_constraint_eval: field_to_string(proof.aux_constraint_eval),
        aux_perm_eval: field_to_string(proof.aux_perm_eval),
        aux_eval_value: field_to_string(proof.aux_eval_value),
        // Evaluation point
        evaluation_point: proof
            .sumcheck_challenges
            .iter()
            .map(|&f| Ext3Fixture {
                c0: f.to_canonical_u64().to_string(),
                c1: "0".to_string(),
                c2: "0".to_string(),
            })
            .collect(),
        // Combined sumcheck
        combined_proof: sumcheck_to_fixture(&proof.combined_proof),
        // Public data
        public_inputs: field_vec_to_strings(&proof.public_inputs),
        alpha: field_to_string(proof.alpha),
        beta: field_to_string(proof.beta),
        gamma: field_to_string(proof.gamma),
        mu: field_to_string(proof.mu),
        tau: field_vec_to_strings(&proof.tau),
        tau_perm: field_vec_to_strings(&proof.tau_perm),
        num_wires: proof.num_wires,
        num_routed_wires: proof.num_routed_wires,
        num_constants: proof.num_constants,
        degree_bits,
        // WHIR config
        whir_protocol_id: hex_encode(&protocol_id),
        whir_split_session_id: hex_encode(&split_session_id),
        whir_params,
        // Issue #2: permutation argument context
        k_is: field_vec_to_strings(&proof.k_is),
        subgroup_gen_powers: field_vec_to_strings(&proof.subgroup_gen_powers),

        // v2 logUp soundness fix (Issue R2-#2)
        inverse_helpers_commitment_root: hex_encode(&proof.inverse_helpers_root),
        inverse_helpers_batch_r: field_to_string(proof.inverse_helpers_batch_r),
        inv_sumcheck_challenges: field_vec_to_strings(&proof.inv_sumcheck_challenges),
        inv_sumcheck_proof: sumcheck_to_fixture(&proof.inv_sumcheck_proof),
        h_sumcheck_challenges: field_vec_to_strings(&proof.h_sumcheck_challenges),
        h_sumcheck_proof: sumcheck_to_fixture(&proof.h_sumcheck_proof),
        lambda_inv: field_to_string(proof.lambda_inv),
        mu_inv: field_to_string(proof.mu_inv),
        tau_inv: field_vec_to_strings(&proof.tau_inv),
        inverse_helpers_evals_at_r_inv: field_vec_to_strings(&proof.inverse_helpers_evals_at_r_inv),
        inverse_helpers_evals_at_r_h: field_vec_to_strings(&proof.inverse_helpers_evals_at_r_h),
        witness_individual_evals_at_r_inv: field_vec_to_strings(
            &proof.witness_individual_evals_at_r_inv,
        ),
        preprocessed_individual_evals_at_r_inv: field_vec_to_strings(
            &proof.preprocessed_individual_evals_at_r_inv,
        ),
        g_sub_eval_at_r_inv: field_to_string(proof.g_sub_eval_at_r_inv),
        witness_eval_value_at_r_inv: field_to_string(proof.witness_eval_value_at_r_inv),
        preprocessed_eval_value_at_r_inv: field_to_string(proof.preprocessed_eval_value_at_r_inv),

        // Issue R2-#1: v2 gate binding fix
        ext_challenge: field_to_string(proof.ext_challenge),
        tau_gate: field_vec_to_strings(&proof.tau_gate),
        gate_sumcheck_challenges: field_vec_to_strings(&proof.gate_sumcheck_challenges),
        gate_sumcheck_proof: sumcheck_to_fixture(&proof.gate_sumcheck_proof),
        witness_individual_evals_at_r_gate_v2: field_vec_to_strings(
            &proof.witness_individual_evals_at_r_gate_v2,
        ),
        preprocessed_individual_evals_at_r_gate_v2: field_vec_to_strings(
            &proof.preprocessed_individual_evals_at_r_gate_v2,
        ),
        witness_eval_value_at_r_gate_v2: field_to_string(proof.witness_eval_value_at_r_gate_v2),
        preprocessed_eval_value_at_r_gate_v2: field_to_string(
            proof.preprocessed_eval_value_at_r_gate_v2,
        ),

        // Circuit metadata for Φ_gate terminal check
        public_inputs_hash: proof.public_inputs_hash.elements.map(field_to_string),
        num_selectors: common_data.selectors_info.num_selectors(),
        quotient_degree_factor: common_data.quotient_degree_factor,
        num_gate_constraints: common_data.num_gate_constraints,
        gates: collect_gate_metadata::<F, D>(common_data)?,
    })
}

/// Serialize an MleProof to a JSON string (all field elements as strings).
pub fn proof_to_json<F: RichField + Extendable<D> + PrimeField64, const D: usize>(
    proof: &MleProof<F>,
    common_data: &CommonCircuitData<F, D>,
    degree_bits: usize,
) -> String {
    let fixture = proof_to_fixture(proof, common_data, degree_bits);
    serde_json::to_string_pretty(&fixture).expect("Failed to serialize proof fixture")
}

/// Fallible form of [`proof_to_json`]: returns the classification error instead of panicking.
///
/// SECURITY: this is the entry point the repo's export guard
/// (`src/utils/mle_prover.rs::export_mle_json`) uses, so an unclassifiable gate surfaces as a
/// normal `Err` on the production path instead of a `255` row in a well-formed fixture.
pub fn try_proof_to_json<F: RichField + Extendable<D> + PrimeField64, const D: usize>(
    proof: &MleProof<F>,
    common_data: &CommonCircuitData<F, D>,
    degree_bits: usize,
) -> Result<String, GateClassificationError> {
    let fixture = try_proof_to_fixture(proof, common_data, degree_bits)?;
    Ok(serde_json::to_string_pretty(&fixture).expect("Failed to serialize proof fixture"))
}

// ═══════════════════════════════════════════════════════════════════════════
//  Parsing: ProofFixture back to values
// ═══════════════════════════════════════════════════════════════════════════

/// Parse a decimal string to a u64 (for Goldilocks field elements).
pub fn parse_field_string(s: &str) -> u64 {
    canonical_fixture_field("field", s)
        .unwrap_or_else(|e| panic!("Invalid field element string '{s}': {e}"))
}

/// Parse a vector of decimal strings to u64 values.
pub fn parse_field_strings(v: &[String]) -> Vec<u64> {
    v.iter().map(|s| parse_field_string(s)).collect()
}

fn validate_sumcheck_fixture(
    name: &str,
    proof: &SumcheckFixture,
    expected_rounds: usize,
    expected_evaluations: usize,
) -> Result<(), String> {
    if proof.round_polys.len() != expected_rounds {
        return Err(format!(
            "{name}: expected exactly {expected_rounds} rounds, got {}",
            proof.round_polys.len()
        ));
    }
    for (round, evaluations) in proof.round_polys.iter().enumerate() {
        if evaluations.len() != expected_evaluations {
            return Err(format!(
                "{name} round {round}: expected exactly {expected_evaluations} evaluations, got {}",
                evaluations.len()
            ));
        }
    }
    Ok(())
}

fn canonical_fixture_field(name: &str, value: &str) -> Result<u64, String> {
    const GOLDILOCKS_MODULUS: u64 = 0xffff_ffff_0000_0001;
    let parsed = value
        .parse::<u64>()
        .map_err(|e| format!("{name}: invalid u64 field encoding: {e}"))?;
    if parsed >= GOLDILOCKS_MODULUS {
        return Err(format!("{name}: non-canonical Goldilocks element"));
    }
    if parsed.to_string() != value {
        return Err(format!("{name}: non-canonical decimal encoding"));
    }
    Ok(parsed)
}

fn canonical_fixture_u64(name: &str, value: &str) -> Result<u64, String> {
    let parsed = value
        .parse::<u64>()
        .map_err(|e| format!("{name}: invalid u64 encoding: {e}"))?;
    if parsed.to_string() != value {
        return Err(format!("{name}: non-canonical decimal encoding"));
    }
    Ok(parsed)
}

fn validate_fixture_field_vec(name: &str, values: &[String]) -> Result<(), String> {
    for (index, value) in values.iter().enumerate() {
        canonical_fixture_field(&format!("{name}[{index}]"), value)?;
    }
    Ok(())
}

fn validate_fixture_hex(
    name: &str,
    value: &str,
    expected_bytes: Option<usize>,
) -> Result<(), String> {
    let encoded = value
        .strip_prefix("0x")
        .ok_or_else(|| format!("{name}: missing 0x prefix"))?;
    if encoded.is_empty() || !encoded.len().is_multiple_of(2) {
        return Err(format!("{name}: empty or odd-length hex encoding"));
    }
    if let Some(expected) = expected_bytes {
        if encoded.len() != expected * 2 {
            return Err(format!(
                "{name}: expected {expected} bytes, got {}",
                encoded.len() / 2
            ));
        }
    }
    if !encoded
        .bytes()
        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!("{name}: non-canonical lowercase hex encoding"));
    }
    Ok(())
}

fn expected_gate_constraints(gate: &GateInfoFixture) -> Result<usize, String> {
    let parsed = parse_gate_params_from_id(&gate.name)
        .map_err(|e| format!("gate `{}`: invalid diagnostic id: {e}", gate.name))?;
    if (gate.gate_id, gate.num_or_consts, gate.param2, gate.param3)
        != (
            parsed.gate_id,
            parsed.num_or_consts,
            parsed.param2,
            parsed.param3,
        )
    {
        return Err(format!(
            "gate `{}`: numeric classifier does not match the independently parsed gate id",
            gate.name
        ));
    }

    let n = usize::from(gate.num_or_consts);
    let p2 = usize::from(gate.param2);
    let p3 = usize::from(gate.param3);
    match gate.gate_id {
        0 => Ok(0),
        1 | 3 => Ok(n),
        2 => Ok(4),
        4 => Ok(123),
        5 => Ok(24),
        6 | 7 | 10 | 11 => n
            .checked_mul(2)
            .ok_or_else(|| format!("gate `{}`: constraint count overflow", gate.name)),
        8 => {
            if n == 0 {
                return Err(format!("gate `{}`: zero exponent bit count", gate.name));
            }
            n.checked_add(1)
                .ok_or_else(|| format!("gate `{}`: constraint count overflow", gate.name))
        }
        9 => {
            if !SUPPORTED_BASE_SUM_BASES.contains(&p2) {
                return Err(format!(
                    "gate `{}`: unsupported BaseSum base {p2}",
                    gate.name
                ));
            }
            n.checked_add(1)
                .ok_or_else(|| format!("gate `{}`: constraint count overflow", gate.name))
        }
        12 => {
            if n == 0 || n >= usize::BITS as usize || p2 == 0 {
                return Err(format!(
                    "gate `{}`: invalid random-access bits or copy count",
                    gate.name
                ));
            }
            p2.checked_mul(
                n.checked_add(2)
                    .ok_or_else(|| format!("gate `{}`: constraint count overflow", gate.name))?,
            )
            .and_then(|value| value.checked_add(p3))
            .ok_or_else(|| format!("gate `{}`: constraint count overflow", gate.name))
        }
        13 => {
            if !(1..=5).contains(&n) || p2 <= 1 {
                return Err(format!(
                    "gate `{}`: invalid coset subgroup bits or degree",
                    gate.name
                ));
            }
            let points = 1usize << n;
            if p2 > points {
                return Err(format!(
                    "gate `{}`: coset degree exceeds its subgroup",
                    gate.name
                ));
            }
            let intermediates = (points - 2) / (p2 - 1);
            intermediates
                .checked_mul(4)
                .and_then(|value| value.checked_add(4))
                .ok_or_else(|| format!("gate `{}`: constraint count overflow", gate.name))
        }
        _ => Err(format!(
            "gate `{}`: unsupported on-chain gate id {}",
            gate.name, gate.gate_id
        )),
    }
}

fn fixture_gate_degree(gate: &GateInfoFixture) -> Result<usize, String> {
    let n = usize::from(gate.num_or_consts);
    match gate.gate_id {
        0 => Ok(0),
        1 | 2 | 5 => Ok(1),
        3 | 6 | 7 => Ok(3),
        4 => Ok(7),
        8 => Ok(4),
        9 => Ok(usize::from(gate.param2)),
        10 | 11 => Ok(2),
        12 => n
            .checked_add(1)
            .ok_or_else(|| format!("gate `{}`: degree overflow", gate.name)),
        13 => Ok(usize::from(gate.param2)),
        _ => Err(format!(
            "gate `{}`: unsupported on-chain gate id {}",
            gate.name, gate.gate_id
        )),
    }
}

fn validate_gate_fixture(fixture: &ProofFixture) -> Result<(), String> {
    if fixture.num_routed_wires > fixture.num_wires {
        return Err("numRoutedWires exceeds numWires".to_string());
    }
    if fixture.num_selectors == 0
        || fixture.num_selectors > fixture.num_constants
        || fixture.num_selectors > fixture.gates.len()
    {
        return Err("numSelectors is zero or exceeds numConstants/gates".to_string());
    }
    if fixture.gates.is_empty() || fixture.gates.len() > usize::from(u8::MAX) {
        return Err("gates is empty or exceeds the u8 row-index space".to_string());
    }

    let mut max_constraints = 0usize;
    let mut degrees = Vec::with_capacity(fixture.gates.len());
    for (row, gate) in fixture.gates.iter().enumerate() {
        if gate.name.is_empty() {
            return Err(format!("gates[{row}].name is empty"));
        }
        if usize::from(gate.gate_row_index) != row {
            return Err(format!("gates[{row}].gateRowIndex is not canonical"));
        }
        let expected_constraints = expected_gate_constraints(gate)?;
        if usize::from(gate.num_constraints) != expected_constraints {
            return Err(format!(
                "gates[{row}].numConstraints: expected {expected_constraints}, got {}",
                gate.num_constraints
            ));
        }
        max_constraints = max_constraints.max(expected_constraints);
        degrees.push(fixture_gate_degree(gate)?);
    }

    for row in 1..fixture.gates.len() {
        let previous = &fixture.gates[row - 1];
        let current = &fixture.gates[row];
        if degrees[row - 1] > degrees[row]
            || (degrees[row - 1] == degrees[row] && previous.name >= current.name)
        {
            return Err("gates are not canonically sorted by degree and id".to_string());
        }
    }

    let max_degree = fixture
        .quotient_degree_factor
        .checked_add(1)
        .ok_or_else(|| "quotientDegreeFactor overflow".to_string())?;
    let last_degree = *degrees.last().expect("non-empty gates checked above");
    let mut groups = Vec::new();
    if last_degree
        .checked_add(fixture.gates.len() - 1)
        .is_some_and(|degree| degree <= max_degree)
    {
        groups.push((0usize, fixture.gates.len()));
    } else {
        if last_degree >= max_degree {
            return Err("gate degree is incompatible with quotientDegreeFactor".to_string());
        }
        let mut start = 0usize;
        while start < fixture.gates.len() {
            let mut size = 0usize;
            while start + size < fixture.gates.len()
                && size
                    .checked_add(degrees[start + size])
                    .is_some_and(|degree| degree < max_degree)
            {
                size += 1;
            }
            if size == 0 {
                return Err("empty canonical selector group".to_string());
            }
            groups.push((start, start + size));
            start += size;
        }
    }
    if groups.len() != fixture.num_selectors {
        return Err(format!(
            "numSelectors: expected {}, got {}",
            groups.len(),
            fixture.num_selectors
        ));
    }
    for (selector, &(start, end)) in groups.iter().enumerate() {
        for row in start..end {
            let gate = &fixture.gates[row];
            if usize::from(gate.selector_index) != selector
                || usize::from(gate.group_start) != start
                || usize::from(gate.group_end) != end
            {
                return Err(format!(
                    "gates[{row}]: non-canonical selector group metadata"
                ));
            }
        }
    }
    if max_constraints != fixture.num_gate_constraints {
        return Err(format!(
            "numGateConstraints: expected {max_constraints}, got {}",
            fixture.num_gate_constraints
        ));
    }
    Ok(())
}

fn validate_fixture_shape(fixture: &ProofFixture) -> Result<(), String> {
    if fixture.protocol_version != MLE_PROTOCOL_VERSION {
        return Err(format!(
            "protocolVersion: expected {MLE_PROTOCOL_VERSION}, got {}",
            fixture.protocol_version
        ));
    }
    if fixture.constituent_width == 0 {
        return Err("constituentWidth must be non-zero".to_string());
    }
    validate_gate_fixture(fixture)?;
    if fixture.circuit_digest.len() != 4 {
        return Err(format!(
            "circuitDigest: expected exactly 4 limbs, got {}",
            fixture.circuit_digest.len()
        ));
    }

    for (name, value) in [
        (
            "preprocessedEvalValue",
            fixture.preprocessed_eval_value.as_str(),
        ),
        ("preprocessedBatchR", fixture.preprocessed_batch_r.as_str()),
        ("witnessEvalValue", fixture.witness_eval_value.as_str()),
        ("witnessBatchR", fixture.witness_batch_r.as_str()),
        ("auxBatchR", fixture.aux_batch_r.as_str()),
        ("auxConstraintEval", fixture.aux_constraint_eval.as_str()),
        ("auxPermEval", fixture.aux_perm_eval.as_str()),
        ("auxEvalValue", fixture.aux_eval_value.as_str()),
        ("alpha", fixture.alpha.as_str()),
        ("beta", fixture.beta.as_str()),
        ("gamma", fixture.gamma.as_str()),
        ("mu", fixture.mu.as_str()),
        (
            "inverseHelpersBatchR",
            fixture.inverse_helpers_batch_r.as_str(),
        ),
        ("lambdaInv", fixture.lambda_inv.as_str()),
        ("muInv", fixture.mu_inv.as_str()),
        ("gSubEvalAtRInv", fixture.g_sub_eval_at_r_inv.as_str()),
        (
            "witnessEvalValueAtRInv",
            fixture.witness_eval_value_at_r_inv.as_str(),
        ),
        (
            "preprocessedEvalValueAtRInv",
            fixture.preprocessed_eval_value_at_r_inv.as_str(),
        ),
        ("extChallenge", fixture.ext_challenge.as_str()),
        (
            "witnessEvalValueAtRGateV2",
            fixture.witness_eval_value_at_r_gate_v2.as_str(),
        ),
        (
            "preprocessedEvalValueAtRGateV2",
            fixture.preprocessed_eval_value_at_r_gate_v2.as_str(),
        ),
    ] {
        canonical_fixture_field(name, value)?;
    }
    for (name, values) in [
        ("circuitDigest", fixture.circuit_digest.as_slice()),
        (
            "preprocessedIndividualEvals",
            fixture.preprocessed_individual_evals.as_slice(),
        ),
        (
            "witnessIndividualEvals",
            fixture.witness_individual_evals.as_slice(),
        ),
        ("publicInputs", fixture.public_inputs.as_slice()),
        ("tau", fixture.tau.as_slice()),
        ("tauPerm", fixture.tau_perm.as_slice()),
        ("kIs", fixture.k_is.as_slice()),
        ("subgroupGenPowers", fixture.subgroup_gen_powers.as_slice()),
        (
            "invSumcheckChallenges",
            fixture.inv_sumcheck_challenges.as_slice(),
        ),
        (
            "hSumcheckChallenges",
            fixture.h_sumcheck_challenges.as_slice(),
        ),
        ("tauInv", fixture.tau_inv.as_slice()),
        (
            "inverseHelpersEvalsAtRInv",
            fixture.inverse_helpers_evals_at_r_inv.as_slice(),
        ),
        (
            "inverseHelpersEvalsAtRH",
            fixture.inverse_helpers_evals_at_r_h.as_slice(),
        ),
        (
            "witnessIndividualEvalsAtRInv",
            fixture.witness_individual_evals_at_r_inv.as_slice(),
        ),
        (
            "preprocessedIndividualEvalsAtRInv",
            fixture.preprocessed_individual_evals_at_r_inv.as_slice(),
        ),
        ("tauGate", fixture.tau_gate.as_slice()),
        (
            "gateSumcheckChallenges",
            fixture.gate_sumcheck_challenges.as_slice(),
        ),
        (
            "witnessIndividualEvalsAtRGateV2",
            fixture.witness_individual_evals_at_r_gate_v2.as_slice(),
        ),
        (
            "preprocessedIndividualEvalsAtRGateV2",
            fixture
                .preprocessed_individual_evals_at_r_gate_v2
                .as_slice(),
        ),
        ("publicInputsHash", fixture.public_inputs_hash.as_slice()),
    ] {
        validate_fixture_field_vec(name, values)?;
    }
    for (name, proof) in [
        ("combinedProof", &fixture.combined_proof),
        ("invSumcheckProof", &fixture.inv_sumcheck_proof),
        ("hSumcheckProof", &fixture.h_sumcheck_proof),
        ("gateSumcheckProof", &fixture.gate_sumcheck_proof),
    ] {
        for (round, evaluations) in proof.round_polys.iter().enumerate() {
            validate_fixture_field_vec(&format!("{name}.roundPolys[{round}]"), evaluations)?;
        }
    }
    for (name, value, expected_bytes) in [
        (
            "preprocessedCommitmentRoot",
            fixture.preprocessed_commitment_root.as_str(),
            Some(32),
        ),
        (
            "witnessCommitmentRoot",
            fixture.witness_commitment_root.as_str(),
            Some(32),
        ),
        (
            "inverseHelpersCommitmentRoot",
            fixture.inverse_helpers_commitment_root.as_str(),
            Some(32),
        ),
        (
            "auxCommitmentRoot",
            fixture.aux_commitment_root.as_str(),
            Some(32),
        ),
        ("whirTranscript", fixture.whir_transcript.as_str(), None),
        ("whirHints", fixture.whir_hints.as_str(), None),
        (
            "whirProtocolId",
            fixture.whir_protocol_id.as_str(),
            Some(64),
        ),
        (
            "whirSplitSessionId",
            fixture.whir_split_session_id.as_str(),
            Some(32),
        ),
    ] {
        validate_fixture_hex(name, value, expected_bytes)?;
    }
    if fixture.evaluation_point.len() != fixture.degree_bits {
        return Err(format!(
            "evaluationPoint: expected exactly {} coordinates, got {}",
            fixture.degree_bits,
            fixture.evaluation_point.len()
        ));
    }
    for (coordinate, value) in fixture.evaluation_point.iter().enumerate() {
        canonical_fixture_field(&format!("evaluationPoint[{coordinate}].c0"), &value.c0)?;
        if canonical_fixture_field(&format!("evaluationPoint[{coordinate}].c1"), &value.c1)? != 0
            || canonical_fixture_field(&format!("evaluationPoint[{coordinate}].c2"), &value.c2)?
                != 0
        {
            return Err(format!(
                "evaluationPoint[{coordinate}]: row point is not a base-field embedding"
            ));
        }
    }

    let preprocessed_len = fixture
        .num_constants
        .checked_add(fixture.num_routed_wires)
        .ok_or_else(|| "preprocessed constituent count overflow".to_string())?;
    let inverse_len = fixture
        .num_routed_wires
        .checked_mul(2)
        .ok_or_else(|| "inverse constituent count overflow".to_string())?;
    let expected_width = preprocessed_len
        .max(fixture.num_wires)
        .max(inverse_len)
        .max(2);
    if fixture.constituent_width != expected_width {
        return Err(format!(
            "constituentWidth: expected {expected_width}, got {}",
            fixture.constituent_width
        ));
    }
    for (name, actual, expected) in [
        (
            "preprocessedIndividualEvals",
            fixture.preprocessed_individual_evals.len(),
            preprocessed_len,
        ),
        (
            "preprocessedIndividualEvalsAtRInv",
            fixture.preprocessed_individual_evals_at_r_inv.len(),
            preprocessed_len,
        ),
        (
            "preprocessedIndividualEvalsAtRGateV2",
            fixture.preprocessed_individual_evals_at_r_gate_v2.len(),
            preprocessed_len,
        ),
        (
            "witnessIndividualEvals",
            fixture.witness_individual_evals.len(),
            fixture.num_wires,
        ),
        (
            "witnessIndividualEvalsAtRInv",
            fixture.witness_individual_evals_at_r_inv.len(),
            fixture.num_wires,
        ),
        (
            "witnessIndividualEvalsAtRGateV2",
            fixture.witness_individual_evals_at_r_gate_v2.len(),
            fixture.num_wires,
        ),
        (
            "inverseHelpersEvalsAtRInv",
            fixture.inverse_helpers_evals_at_r_inv.len(),
            inverse_len,
        ),
        (
            "inverseHelpersEvalsAtRH",
            fixture.inverse_helpers_evals_at_r_h.len(),
            inverse_len,
        ),
    ] {
        if actual != expected {
            return Err(format!(
                "{name}: expected exactly {expected} elements, got {actual}"
            ));
        }
    }

    validate_sumcheck_fixture(
        "combinedProof",
        &fixture.combined_proof,
        fixture.degree_bits,
        3,
    )?;
    validate_sumcheck_fixture(
        "invSumcheckProof",
        &fixture.inv_sumcheck_proof,
        fixture.degree_bits,
        4,
    )?;
    validate_sumcheck_fixture(
        "hSumcheckProof",
        &fixture.h_sumcheck_proof,
        fixture.degree_bits,
        2,
    )?;
    let gate_evaluations = fixture
        .quotient_degree_factor
        .checked_add(3)
        .ok_or_else(|| "gateSumcheckProof evaluation count overflow".to_string())?;
    validate_sumcheck_fixture(
        "gateSumcheckProof",
        &fixture.gate_sumcheck_proof,
        fixture.degree_bits,
        gate_evaluations,
    )?;

    for (name, point) in [
        ("tau", &fixture.tau),
        ("tauPerm", &fixture.tau_perm),
        ("tauInv", &fixture.tau_inv),
        ("tauGate", &fixture.tau_gate),
        ("invSumcheckChallenges", &fixture.inv_sumcheck_challenges),
        ("hSumcheckChallenges", &fixture.h_sumcheck_challenges),
        ("gateSumcheckChallenges", &fixture.gate_sumcheck_challenges),
        ("subgroupGenPowers", &fixture.subgroup_gen_powers),
    ] {
        if point.len() != fixture.degree_bits {
            return Err(format!(
                "{name}: expected exactly {} elements, got {}",
                fixture.degree_bits,
                point.len()
            ));
        }
    }
    if fixture.k_is.len() != fixture.num_routed_wires {
        return Err(format!(
            "kIs: expected exactly {} elements, got {}",
            fixture.num_routed_wires,
            fixture.k_is.len()
        ));
    }

    let whir = &fixture.whir_params;
    canonical_fixture_field(
        "whirParams.initialDomainGenerator",
        &whir.initial_domain_generator,
    )?;
    canonical_fixture_u64(
        "whirParams.initialSumcheckPowThreshold",
        &whir.initial_sumcheck_pow_threshold,
    )?;
    canonical_fixture_u64("whirParams.finalPowThreshold", &whir.final_pow_threshold)?;
    canonical_fixture_u64(
        "whirParams.finalSumcheckPowThreshold",
        &whir.final_sumcheck_pow_threshold,
    )?;
    for (round, params) in whir.rounds.iter().enumerate() {
        canonical_fixture_field(
            &format!("whirParams.rounds[{round}].domainGenerator"),
            &params.domain_generator,
        )?;
        canonical_fixture_u64(
            &format!("whirParams.rounds[{round}].powThreshold"),
            &params.pow_threshold,
        )?;
        canonical_fixture_u64(
            &format!("whirParams.rounds[{round}].sumcheckPowThreshold"),
            &params.sumcheck_pow_threshold,
        )?;
    }
    let index_capacity = fixture
        .constituent_width
        .checked_next_power_of_two()
        .ok_or_else(|| "constituentWidth exceeds the supported packed index domain".to_string())?;
    let index_bits = index_capacity.trailing_zeros() as usize;
    let expected_whir_variables = fixture
        .degree_bits
        .checked_add(index_bits)
        .ok_or_else(|| "packed WHIR variable count overflow".to_string())?;
    if expected_whir_variables > 32 {
        return Err(format!(
            "packed WHIR variable count {expected_whir_variables} exceeds the Goldilocks two-adicity"
        ));
    }
    if whir.num_variables != expected_whir_variables {
        return Err(format!(
            "whirParams.numVariables: expected {expected_whir_variables}, got {}",
            whir.num_variables
        ));
    }
    if whir.num_vectors != NUM_PACKED_VECTORS_PER_GROUP {
        return Err(format!(
            "whirParams.numVectors: expected {NUM_PACKED_VECTORS_PER_GROUP}, got {}",
            whir.num_vectors
        ));
    }
    if whir.num_commitments != NUM_SPLIT_COMMITMENTS {
        return Err(format!(
            "whirParams.numCommitments: expected {NUM_SPLIT_COMMITMENTS}, got {}",
            whir.num_commitments
        ));
    }
    if whir.rounds.len() != whir.num_rounds {
        return Err(format!(
            "whirParams.rounds: expected exactly {} rounds, got {}",
            whir.num_rounds,
            whir.rounds.len()
        ));
    }
    let (expected_whir, expected_protocol_id, expected_session_id) =
        extract_whir_params(fixture.degree_bits, fixture.constituent_width);
    if *whir != expected_whir {
        return Err("whirParams: unsupported or inconsistent packed configuration".to_string());
    }
    if fixture.whir_protocol_id != hex_encode(&expected_protocol_id) {
        return Err("whirProtocolId does not match whirParams".to_string());
    }
    if fixture.whir_split_session_id != hex_encode(&expected_session_id) {
        return Err("whirSplitSessionId does not match packed v1 session".to_string());
    }

    Ok(())
}

/// Strictly decode a JSON fixture, rejecting schema tails and inconsistent
/// shape/configuration metadata before a consumer can truncate them.
pub fn try_fixture_from_json(json: &str) -> Result<ProofFixture, String> {
    let fixture: ProofFixture = serde_json::from_str(json)
        .map_err(|e| format!("Failed to parse proof fixture JSON: {e}"))?;
    validate_fixture_shape(&fixture)?;
    Ok(fixture)
}

/// Load a strictly validated ProofFixture from a JSON string.
pub fn fixture_from_json(json: &str) -> ProofFixture {
    try_fixture_from_json(json)
        .unwrap_or_else(|e| panic!("Failed to parse proof fixture JSON: {e}"))
}

#[cfg(test)]
mod tests {
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::Field;

    use super::*;

    type F = GoldilocksField;

    #[test]
    fn test_large_field_element_roundtrip() {
        // This value > 2^53 — would be corrupted by JSON number
        let val = 18089690094123470162u64;
        let s = val.to_string();
        let parsed = parse_field_string(&s);
        assert_eq!(val, parsed, "String roundtrip should be exact");
        assert!(
            val > (1u64 << 53),
            "Test value should exceed IEEE 754 safe range"
        );
    }

    #[test]
    fn test_proof_fixture_roundtrip() {
        use plonky2::iop::witness::{PartialWitness, WitnessWrite};
        use plonky2::plonk::circuit_builder::CircuitBuilder;
        use plonky2::plonk::circuit_data::CircuitConfig;
        use plonky2::plonk::config::PoseidonGoldilocksConfig;
        use plonky2::util::timing::TimingTree;

        use crate::prover::mle_prove;

        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;

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

        // Serialize to JSON
        let json = proof_to_json::<F, D>(&proof, &circuit.common, circuit.common.degree_bits());

        // Verify unified WHIR format
        assert!(
            json.contains("\"whirTranscript\": \""),
            "should have unified whirTranscript"
        );
        assert!(
            json.contains("\"whirHints\": \""),
            "should have unified whirHints"
        );
        assert!(
            json.contains("\"witnessBatchR\": \""),
            "witnessBatchR should be a string"
        );
        assert!(
            json.contains("\"preprocessedBatchR\": \""),
            "preprocessedBatchR should be a string"
        );
        assert!(json.contains("\"alpha\": \""), "alpha should be a string");
        assert!(json.contains("\"roundPolys\""), "should have roundPolys");

        // Parse back
        let fixture = fixture_from_json(&json);
        assert_eq!(fixture.degree_bits, circuit.common.degree_bits());

        // The fixture decoder is a security boundary for deployment tooling:
        // it must not silently truncate a fifth hash limb, an extra sumcheck
        // round/coefficient, or an unused WHIR configuration tail.
        let canonical_json: serde_json::Value = serde_json::from_str(&json).unwrap();

        let mut extra_hash_limb = canonical_json.clone();
        extra_hash_limb["publicInputsHash"]
            .as_array_mut()
            .unwrap()
            .push(serde_json::Value::String("0".to_string()));
        assert!(
            try_fixture_from_json(&extra_hash_limb.to_string()).is_err(),
            "fixture decoder accepted an extra publicInputsHash limb"
        );

        let mut legacy_lambda_h = canonical_json.clone();
        legacy_lambda_h["lambdaH"] = serde_json::Value::String("1".to_string());
        assert!(
            try_fixture_from_json(&legacy_lambda_h.to_string()).is_err(),
            "fixture decoder accepted a removed v0 field"
        );

        let mut extra_claim = canonical_json.clone();
        extra_claim["witnessIndividualEvalsAtRInv"]
            .as_array_mut()
            .unwrap()
            .push(serde_json::Value::String("0".to_string()));
        assert!(
            try_fixture_from_json(&extra_claim.to_string()).is_err(),
            "fixture decoder accepted a constituent-claim tail"
        );

        let mut noncanonical_row_point = canonical_json.clone();
        noncanonical_row_point["evaluationPoint"][0]["c1"] =
            serde_json::Value::String("1".to_string());
        assert!(
            try_fixture_from_json(&noncanonical_row_point.to_string()).is_err(),
            "fixture decoder accepted a non-base row point"
        );

        let mut extra_sumcheck_round = canonical_json.clone();
        let first_round = extra_sumcheck_round["combinedProof"]["roundPolys"][0].clone();
        extra_sumcheck_round["combinedProof"]["roundPolys"]
            .as_array_mut()
            .unwrap()
            .push(first_round);
        assert!(
            try_fixture_from_json(&extra_sumcheck_round.to_string()).is_err(),
            "fixture decoder accepted an extra combined sumcheck round"
        );

        let mut extra_sumcheck_coefficient = canonical_json.clone();
        extra_sumcheck_coefficient["combinedProof"]["roundPolys"][0]
            .as_array_mut()
            .unwrap()
            .push(serde_json::Value::String("0".to_string()));
        assert!(
            try_fixture_from_json(&extra_sumcheck_coefficient.to_string()).is_err(),
            "fixture decoder accepted an extra combined sumcheck coefficient"
        );

        let mut extra_whir_round = canonical_json.clone();
        let first_whir_round = extra_whir_round["whirParams"]["rounds"][0].clone();
        extra_whir_round["whirParams"]["rounds"]
            .as_array_mut()
            .unwrap()
            .push(first_whir_round);
        assert!(
            try_fixture_from_json(&extra_whir_round.to_string()).is_err(),
            "fixture decoder accepted an ignored WHIR round tail"
        );

        let mut noncanonical_scalar = canonical_json.clone();
        noncanonical_scalar["alpha"] =
            serde_json::Value::String("18446744069414584321".to_string());
        assert!(
            try_fixture_from_json(&noncanonical_scalar.to_string()).is_err(),
            "fixture decoder accepted the Goldilocks modulus as a field element"
        );

        let mut aliased_decimal = canonical_json.clone();
        let alpha = aliased_decimal["alpha"].as_str().unwrap().to_string();
        aliased_decimal["alpha"] = serde_json::Value::String(format!("0{alpha}"));
        assert!(
            try_fixture_from_json(&aliased_decimal.to_string()).is_err(),
            "fixture decoder accepted a decimal encoding alias"
        );

        let mut malformed_root = canonical_json.clone();
        malformed_root["witnessCommitmentRoot"] = serde_json::Value::String("0x00".to_string());
        assert!(
            try_fixture_from_json(&malformed_root.to_string()).is_err(),
            "fixture decoder accepted a short commitment root"
        );

        let mut unsupported_gate = canonical_json.clone();
        unsupported_gate["gates"][0]["gateId"] = serde_json::Value::from(255);
        assert!(
            try_fixture_from_json(&unsupported_gate.to_string()).is_err(),
            "fixture decoder accepted an unsupported gate classifier"
        );

        let mut wrong_gate_constraints = canonical_json.clone();
        wrong_gate_constraints["gates"][0]["numConstraints"] = serde_json::Value::from(0);
        assert!(
            try_fixture_from_json(&wrong_gate_constraints.to_string()).is_err(),
            "fixture decoder accepted a gate constraint-count mismatch"
        );

        let mut wrong_selector_group = canonical_json.clone();
        wrong_selector_group["gates"][0]["groupEnd"] = serde_json::Value::from(1);
        assert!(
            try_fixture_from_json(&wrong_selector_group.to_string()).is_err(),
            "fixture decoder accepted non-canonical selector grouping"
        );

        let mut wrong_max_constraints = canonical_json.clone();
        wrong_max_constraints["numGateConstraints"] = serde_json::Value::from(124);
        assert!(
            try_fixture_from_json(&wrong_max_constraints.to_string()).is_err(),
            "fixture decoder accepted a wrong global gate constraint count"
        );

        let mut impossible_dimensions = canonical_json.clone();
        impossible_dimensions["degreeBits"] = serde_json::Value::from(56);
        let decode =
            std::panic::catch_unwind(|| try_fixture_from_json(&impossible_dimensions.to_string()));
        assert!(
            decode.is_ok(),
            "fallible fixture decoder panicked on dimensions"
        );
        assert!(
            decode.unwrap().is_err(),
            "fixture decoder accepted unsupported packed dimensions"
        );

        let mut wrong_num_vectors = canonical_json;
        wrong_num_vectors["whirParams"]["numVectors"] = serde_json::Value::from(2);
        assert!(
            try_fixture_from_json(&wrong_num_vectors.to_string()).is_err(),
            "fixture decoder accepted non-packed whirParams.numVectors"
        );

        // Verify field element roundtrips
        let wit_batch_r_parsed = parse_field_string(&fixture.witness_batch_r);
        assert_eq!(wit_batch_r_parsed, proof.witness_batch_r.to_canonical_u64());
        let pre_batch_r_parsed = parse_field_string(&fixture.preprocessed_batch_r);
        assert_eq!(
            pre_batch_r_parsed,
            proof.preprocessed_batch_r.to_canonical_u64()
        );

        // Verify combined proof round polys roundtrip
        for (i, rp) in fixture.combined_proof.round_polys.iter().enumerate() {
            for (j, s) in rp.iter().enumerate() {
                let parsed = parse_field_string(s);
                let original =
                    proof.combined_proof.round_polys[i].evaluations[j].to_canonical_u64();
                assert_eq!(parsed, original, "combined round[{i}][{j}] mismatch");
            }
        }
    }

    #[test]
    fn test_ieee754_precision_loss_detected() {
        // Demonstrate that using JSON numbers would lose precision
        let large_val = 18089690094123470162u64;
        let as_f64 = large_val as f64;
        let back_to_u64 = as_f64 as u64;
        assert_ne!(
            large_val, back_to_u64,
            "IEEE 754 double SHOULD lose precision for this value"
        );

        // Our string serialization preserves it
        let s = large_val.to_string();
        let parsed: u64 = s.parse().unwrap();
        assert_eq!(large_val, parsed, "String serialization MUST be exact");
    }
}
