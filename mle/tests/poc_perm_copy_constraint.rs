//! Adversarial PoCs for the wire-v3 copy-constraint (permutation) lane.
//!
//! The attacker model is the table-level prover: it controls every witness
//! cell and every proof byte, and it recomputes *honest* auxiliary columns
//! (including the norm-inverse helper group) for whatever tables it likes.
//! The VK (sigma commitment root, `k_is`, public-input wire map, subgroup
//! generator powers) is honest.
//!
//! Test circuit (`degree_bits = 2`, 4 rows, 80 routed wires):
//!   row 0 = `ArithmeticGate { num_ops: 20 }` holding
//!       op0 = mul(x, y) -> wires (m0=x@c0, m1=y@c1, addend=x@c2, out=p@c3)
//!       op1 = mul(x, z) -> wires (m0=x@c4, m1=z@c5, addend=x@c6, out=q@c7)
//!   `CircuitBuilder::mul(a, b)` lowers to `arithmetic(1, 0, a, b, a)`, so the
//!   addend column is multiplied by `const_1 = 0` and is therefore *not*
//!   gate-constrained, while still being a routed cell in `x`'s copy class
//!   {(0,0), (0,2), (0,4), (0,6)}. Changing `(0,6)` violates exactly one copy
//!   constraint and leaves every gate constraint satisfied.

use ark_ff::{AdditiveGroup, Field as ArkField, PrimeField as ArkPrimeField};
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, EvaluationTables};
use plonky2::plonk::config::{Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::prover::extract_evaluation_tables;
use plonky2::plonk::vanishing_poly::evaluate_gate_constraints;
use plonky2::plonk::vars::EvaluationVars;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::quadratic::QuadraticExtension;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use plonky2_mle::permutation::norm_logup::{
    compute_norm_inverse_tables, evaluate_joint_norm_logup_terminal_with_public_inputs,
    formal_adjugate_from_coords, formal_norm_from_coords, NormInverseTables, NormLogupChallenges,
    NormLogupProverState, NORM_LOGUP_MAX_DEGREE,
};
use plonky2_mle::prover_v2::{mle_prove_v2_from_tables, mle_setup_v2};
use plonky2_mle::sumcheck::coefficients::verify_ext3_coefficient_sumcheck;
use plonky2_mle::sumcheck::ext3::Ext3DenseMle;
use plonky2_mle::transcript_v2::TranscriptV2;
use plonky2_mle::verifier_v2::mle_verify_v2;
use plonky2_mle::vk_v2::decode_public_input_wire_map_v2;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
type FE = QuadraticExtension<GoldilocksField>;
const D: usize = 2;

/// Column of `op1`'s addend wire: `4 * 1 + 2`.
const TAMPER_COLUMN: usize = 6;
const TAMPER_ROW: usize = 0;

fn build() -> (CircuitData<F, C, D>, EvaluationTables<F>) {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let y = builder.add_virtual_target();
    let z = builder.add_virtual_target();
    let p = builder.mul(x, y);
    let q = builder.mul(x, z);
    builder.register_public_input(p);
    let _ = q;
    let circuit = builder.build::<C>();

    let mut witness = PartialWitness::new();
    witness.set_target(x, F::from_canonical_u64(3)).unwrap();
    witness.set_target(y, F::from_canonical_u64(7)).unwrap();
    witness.set_target(z, F::from_canonical_u64(11)).unwrap();
    let mut timing = TimingTree::default();
    let tables = extract_evaluation_tables::<F, C, D>(
        &circuit.prover_only,
        &circuit.common,
        witness,
        &mut timing,
    )
    .expect("evaluation-table extraction");
    (circuit, tables)
}

/// Run Plonky2's own selector-filtered gate-constraint evaluator on one row.
/// All `num_gate_constraints` outputs must be zero for a satisfying witness.
fn gate_constraints_at_row(
    circuit: &CircuitData<F, C, D>,
    tables: &EvaluationTables<F>,
    row: usize,
) -> Vec<FE> {
    let local_constants: Vec<FE> = tables.constant_values[row]
        .iter()
        .map(|&value| FE::from(value))
        .collect();
    let local_wires: Vec<FE> = (0..tables.num_wires)
        .map(|column| FE::from(tables.wire_values[column][row]))
        .collect();
    let public_inputs_hash: HashOut<F> = tables.public_inputs_hash;
    let vars = EvaluationVars {
        local_constants: &local_constants,
        local_wires: &local_wires,
        public_inputs_hash: &public_inputs_hash,
    };
    evaluate_gate_constraints::<F, D>(&circuit.common, vars)
}

fn assert_all_gate_constraints_hold(
    label: &str,
    circuit: &CircuitData<F, C, D>,
    tables: &EvaluationTables<F>,
) {
    for row in 0..tables.degree {
        let constraints = gate_constraints_at_row(circuit, tables, row);
        assert!(
            constraints.iter().all(|value| *value == FE::ZERO),
            "{label}: gate constraints violated at row {row}"
        );
    }
}

/// Reproduce the exact production norm/logUp lane in isolation: the same
/// challenge tuple shape, the same prover state, the same terminal evaluator,
/// on real Plonky2 tables. No gate lane, no WHIR.
#[allow(clippy::type_complexity)]
fn standalone_log_lane(
    tables: &EvaluationTables<F>,
    public_input_wires: &[(usize, usize)],
    challenges: NormLogupChallenges,
    tau: &[Field64_3],
    inverse_tables: &NormInverseTables<F>,
) -> (Field64_3, Field64_3) {
    let num_routed = tables.num_routed_wires;
    let mut state = NormLogupProverState::new_with_public_inputs(
        &tables.wire_values,
        &tables.sigma_values,
        &tables.k_is,
        &tables.subgroup,
        inverse_tables,
        tau,
        challenges,
        &tables.public_inputs,
        public_input_wires,
    );
    let mut prover_transcript = TranscriptV2::new();
    prover_transcript.domain_separate("poc-perm-standalone-lane");
    while !state.is_complete() {
        let round = state.current_round().unwrap();
        prover_transcript.domain_separate("sumcheck-round-coeff-ext3-v3");
        prover_transcript.absorb_ext3_vec(&round.non_constant);
        let challenge = prover_transcript.squeeze_ext3::<F>();
        state.bind_challenge(challenge).unwrap();
    }
    let (proof, _) = state.into_proof_and_point().unwrap();

    let mut verifier_transcript = TranscriptV2::new();
    verifier_transcript.domain_separate("poc-perm-standalone-lane");
    let (point, final_claim) = verify_ext3_coefficient_sumcheck::<F>(
        &proof,
        Field64_3::ZERO,
        tau.len(),
        NORM_LOGUP_MAX_DEGREE,
        &mut verifier_transcript,
    )
    .unwrap();

    let column = |values: &[F]| Ext3DenseMle::from_base(values).evaluate(&point);
    let routed_wires: Vec<Field64_3> = (0..num_routed)
        .map(|c| column(&tables.wire_values[c]))
        .collect();
    let sigmas: Vec<Field64_3> = (0..num_routed)
        .map(|c| {
            let values: Vec<F> = tables.sigma_values.iter().map(|row| row[c]).collect();
            column(&values)
        })
        .collect();
    let inverse_identity: Vec<Field64_3> = inverse_tables
        .identity
        .iter()
        .map(|c| column(c))
        .collect();
    let inverse_sigma: Vec<Field64_3> = inverse_tables.sigma.iter().map(|c| column(c)).collect();
    let subgroup = column(&tables.subgroup);
    let terminal = evaluate_joint_norm_logup_terminal_with_public_inputs(
        tau,
        &point,
        &routed_wires,
        &sigmas,
        &inverse_identity,
        &inverse_sigma,
        subgroup,
        &tables.k_is,
        challenges,
        &tables.public_inputs,
        public_input_wires,
    );
    (final_claim, terminal)
}

fn ext3(seed: u64) -> Field64_3 {
    Field64_3::new(
        ArkGoldilocks::from(seed),
        ArkGoldilocks::from(seed.wrapping_mul(3).wrapping_add(1)),
        ArkGoldilocks::from(seed.wrapping_mul(5).wrapping_add(2)),
    )
}

fn demo_challenges() -> NormLogupChallenges {
    NormLogupChallenges {
        beta: ext3(1009),
        gamma: ext3(1013),
        lambda: ext3(1019),
        rho: ext3(1021),
        kappa: ext3(1031),
        eta: ext3(1033),
        xi: ext3(1039),
    }
}

fn honest_inverse_tables(tables: &EvaluationTables<F>, beta: Field64_3, gamma: Field64_3) -> NormInverseTables<F> {
    compute_norm_inverse_tables(
        &tables.wire_values,
        &tables.sigma_values,
        &tables.k_is,
        &tables.subgroup,
        beta,
        gamma,
        tables.num_routed_wires,
        tables.degree,
    )
    .expect("honest norm-inverse tables")
}

fn pi_wires(circuit: &CircuitData<F, C, D>, tables: &EvaluationTables<F>) -> Vec<(usize, usize)> {
    tables
        .public_input_wires
        .iter()
        .map(|wire| (wire.row, wire.column))
        .collect::<Vec<_>>()
        .tap_check(circuit)
}

trait TapCheck {
    fn tap_check(self, circuit: &CircuitData<F, C, D>) -> Self;
}
impl TapCheck for Vec<(usize, usize)> {
    fn tap_check(self, circuit: &CircuitData<F, C, D>) -> Self {
        assert_eq!(self.len(), circuit.common.num_public_inputs);
        self
    }
}

// ---------------------------------------------------------------------------
// (i) one violated copy constraint, every gate constraint still satisfied
// ---------------------------------------------------------------------------

#[test]
fn poc_i_single_violated_copy_constraint_is_rejected() {
    let (circuit, honest_tables) = build();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let digest = vk.circuit_digest.clone();

    // Sanity: the honest tables verify.
    let honest_proof = mle_prove_v2_from_tables(&circuit.common, &honest_tables, &digest)
        .expect("honest table-level proof");
    mle_verify_v2::<F, D>(&circuit.common, &vk, &honest_proof).expect("honest proof must verify");

    // The tampered cell is in `x`'s copy class and holds `x = 3`.
    assert_eq!(
        honest_tables.wire_values[TAMPER_COLUMN][TAMPER_ROW],
        F::from_canonical_u64(3)
    );
    let mut tables = clone_tables(&honest_tables);
    tables.wire_values[TAMPER_COLUMN][TAMPER_ROW] += F::ONE;

    // Plonky2's own selector-filtered gate-constraint evaluator still reports
    // a fully satisfied witness on every row, before and after the tamper.
    assert_all_gate_constraints_hold("honest", &circuit, &honest_tables);
    assert_all_gate_constraints_hold("tampered", &circuit, &tables);
    let before = gate_constraints_at_row(&circuit, &honest_tables, TAMPER_ROW);
    let after = gate_constraints_at_row(&circuit, &tables, TAMPER_ROW);
    assert_eq!(
        before, after,
        "the tampered addend cell must not move any gate constraint"
    );
    println!(
        "every one of the {} filtered gate constraints stays 0 on all {} rows after the tamper",
        before.len(),
        tables.degree
    );

    // Public inputs, PI hash and the PI wire map are untouched.
    assert_eq!(tables.public_inputs, honest_tables.public_inputs);
    assert_eq!(tables.public_inputs_hash, honest_tables.public_inputs_hash);

    let proof = mle_prove_v2_from_tables(&circuit.common, &tables, &digest)
        .expect("table-level prover accepts the tampered witness");
    // Structural identity with the honest proof: same VK, same PI, same roots
    // schema. Only the witness commitment and the sumchecks differ.
    assert_eq!(proof.public_inputs, honest_proof.public_inputs);

    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &proof)
        .expect_err("a violated copy constraint must be rejected");
    println!("poc(i) end-to-end rejection: {error}");
    assert!(
        error.to_string().contains("norm/logUp terminal equation failed"),
        "expected the permutation lane to reject, got: {error}"
    );
}

#[test]
fn poc_i_lane_isolated_copy_constraint_violation() {
    let (circuit, honest_tables) = build();
    let mut tables = clone_tables(&honest_tables);
    tables.wire_values[TAMPER_COLUMN][TAMPER_ROW] += F::ONE;

    let challenges = demo_challenges();
    let tau: Vec<Field64_3> = (0..tables.degree_bits)
        .map(|i| ext3(2003 + i as u64))
        .collect();
    let wires = pi_wires(&circuit, &honest_tables);

    let honest_helpers = honest_inverse_tables(&honest_tables, challenges.beta, challenges.gamma);
    let (honest_claim, honest_terminal) = standalone_log_lane(
        &honest_tables,
        &wires,
        challenges,
        &tau,
        &honest_helpers,
    );
    assert_eq!(
        honest_claim, honest_terminal,
        "honest tables must satisfy the log lane"
    );

    let helpers = honest_inverse_tables(&tables, challenges.beta, challenges.gamma);
    let (claim, terminal) = standalone_log_lane(&tables, &wires, challenges, &tau, &helpers);
    println!("poc(i) lane-isolated claim   = {claim:?}");
    println!("poc(i) lane-isolated terminal= {terminal:?}");
    assert_ne!(
        claim, terminal,
        "the norm/logUp lane alone must reject the violated copy constraint"
    );
}

// ---------------------------------------------------------------------------
// (ii) change one public input, keep the witness
// ---------------------------------------------------------------------------

#[test]
fn poc_ii_public_input_changed_witness_unchanged_is_rejected() {
    let (circuit, honest_tables) = build();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let digest = vk.circuit_digest.clone();

    let mut tables = clone_tables(&honest_tables);
    tables.public_inputs[0] += F::ONE;
    // Keep the gate lane perfectly consistent with the modified statement so
    // the rejection is attributable to D_PI alone: the verifier recomputes the
    // PI hash from `proof.public_inputs`, so the prover must do the same.
    tables.public_inputs_hash = PoseidonHash::hash_no_pad(&tables.public_inputs);

    let proof = mle_prove_v2_from_tables(&circuit.common, &tables, &digest)
        .expect("table-level prover accepts the modified statement");
    assert_eq!(proof.public_inputs, tables.public_inputs);
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &proof)
        .expect_err("a public input that disagrees with its routed cell must be rejected");
    println!("poc(ii) rejection: {error}");
    assert!(
        error.to_string().contains("norm/logUp terminal equation failed"),
        "expected D_PI to reject, got: {error}"
    );
}

// ---------------------------------------------------------------------------
// (iii) keep the public inputs, move the witness cell the VK map points at
// ---------------------------------------------------------------------------

#[test]
fn poc_iii_mapped_witness_cell_changed_is_rejected() {
    let (circuit, honest_tables) = build();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let digest = vk.circuit_digest.clone();
    let mapped = decode_public_input_wire_map_v2(
        &vk.public_input_wire_map,
        circuit.common.num_public_inputs,
        circuit.common.degree(),
        circuit.common.config.num_routed_wires,
    )
    .expect("VK public-input wire map decodes");
    println!("poc(iii) VK public-input wire map = {mapped:?}");

    let (row, column) = mapped[0];
    let mut tables = clone_tables(&honest_tables);
    tables.wire_values[column][row] += F::ONE;
    assert_eq!(tables.public_inputs, honest_tables.public_inputs);
    assert_eq!(tables.public_inputs_hash, honest_tables.public_inputs_hash);

    let proof = mle_prove_v2_from_tables(&circuit.common, &tables, &digest)
        .expect("table-level prover accepts the tampered mapped cell");
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &proof)
        .expect_err("a mapped cell that disagrees with its public input must be rejected");
    println!("poc(iii) rejection: {error}");
    assert!(
        error.to_string().contains("norm/logUp terminal equation failed"),
        "expected the log lane to reject, got: {error}"
    );
}

// ---------------------------------------------------------------------------
// (iv-a) the helper columns cannot be forged: base-field scalars cannot cancel
//        an Ext3 logUp defect, and the Z-checks fire when they are moved.
// ---------------------------------------------------------------------------

#[test]
fn poc_iv_forged_norm_inverse_cannot_cancel_the_logup_defect() {
    let (circuit, honest_tables) = build();
    let mut tables = clone_tables(&honest_tables);
    tables.wire_values[TAMPER_COLUMN][TAMPER_ROW] += F::ONE;

    let challenges = demo_challenges();
    let (beta, gamma) = (challenges.beta, challenges.gamma);
    let helpers = honest_inverse_tables(&tables, beta, gamma);
    let num_routed = tables.num_routed_wires;

    // Reconstruct the Boolean-cube logUp defect
    //   S = sum_rows sum_j ( 1/D_id,j - 1/D_sigma,j ).
    let mut defect = Field64_3::ZERO;
    let denominator = |wire: F, position: Field64_3| -> Field64_3 {
        Field64_3::from(wire.to_canonical_u64()) + beta + gamma * position
    };
    for j in 0..num_routed {
        for row in 0..tables.degree {
            let wire = tables.wire_values[j][row];
            let identity = Field64_3::from(
                (tables.k_is[j] * tables.subgroup[row]).to_canonical_u64(),
            );
            let sigma = Field64_3::from(tables.sigma_values[row][j].to_canonical_u64());
            defect += denominator(wire, identity).inverse().unwrap()
                - denominator(wire, sigma).inverse().unwrap();
        }
    }
    println!("poc(iv) Boolean-cube logUp defect S = {defect:?}");
    assert_ne!(defect, Field64_3::ZERO, "tampering must move the logUp sum");

    // The only degree of freedom the prover has inside the committed helper
    // group is a *base-field* offset delta on one cell, which moves the logUp
    // sum by delta * adj(D). Cancelling S therefore requires
    //   -S * adj(D)^{-1} in F_p.
    let mut any_base_field_fix = false;
    for j in 0..num_routed {
        for row in 0..tables.degree {
            let wire = tables.wire_values[j][row];
            for position in [
                Field64_3::from((tables.k_is[j] * tables.subgroup[row]).to_canonical_u64()),
                Field64_3::from(tables.sigma_values[row][j].to_canonical_u64()),
            ] {
                let d = denominator(wire, position);
                let coords = [d.c0, d.c1, d.c2];
                let adj = formal_adjugate_from_coords(coords);
                let adj_ext = Field64_3::new(adj[0], adj[1], adj[2]);
                let required = -defect * adj_ext.inverse().unwrap();
                if required.c1 == ArkGoldilocks::ZERO && required.c2 == ArkGoldilocks::ZERO {
                    any_base_field_fix = true;
                }
            }
        }
    }
    assert!(
        !any_base_field_fix,
        "no single base-field helper offset may cancel the Ext3 logUp defect"
    );

    // Even so: move one helper cell by the base-field part of the required
    // offset and confirm the eq-weighted Z relation fires.
    let mut forged = helpers.clone();
    let d = {
        let wire = tables.wire_values[0][0];
        denominator(
            wire,
            Field64_3::from((tables.k_is[0] * tables.subgroup[0]).to_canonical_u64()),
        )
    };
    let adj = formal_adjugate_from_coords([d.c0, d.c1, d.c2]);
    let adj_ext = Field64_3::new(adj[0], adj[1], adj[2]);
    let required = -defect * adj_ext.inverse().unwrap();
    forged.identity[0][0] += F::from_canonical_u64(required.c0.into_bigint().0[0]);

    let tau: Vec<Field64_3> = (0..tables.degree_bits)
        .map(|i| ext3(4001 + i as u64))
        .collect();
    let wires = pi_wires(&circuit, &honest_tables);
    let (claim, terminal) = standalone_log_lane(&tables, &wires, challenges, &tau, &forged);
    assert_ne!(
        claim, terminal,
        "a forged helper cell must be caught by the per-row Z relation"
    );
    println!("poc(iv) forged-helper lane rejection confirmed");
}

// ---------------------------------------------------------------------------
// (iv-b) the formal norm is the field norm: it vanishes only at zero, so a
//        prover cannot manufacture an unconstrained helper cell.
// ---------------------------------------------------------------------------

#[test]
fn poc_iv_formal_norm_is_the_field_norm_and_only_vanishes_at_zero() {
    // 2 is not a cube in Goldilocks, so x^3 - 2 is irreducible and
    // F_p[theta]/(theta^3 - 2) is a field.
    let p: u128 = 0xFFFF_FFFF_0000_0001;
    let mut acc: u128 = 1;
    let mut base: u128 = 2;
    let mut exponent = (p - 1) / 3;
    while exponent > 0 {
        if exponent & 1 == 1 {
            acc = acc * base % p;
        }
        base = base * base % p;
        exponent >>= 1;
    }
    println!("poc(iv) 2^((p-1)/3) mod p = {acc}");
    assert_ne!(acc, 1, "x^3 - 2 must be irreducible over Goldilocks");

    // N(a,b,c) = a^3 + 2 b^3 + 4 c^3 - 6 a b c, and N(v) = 0 iff v = 0.
    let mut seed = 1u64;
    for _ in 0..4096 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let a = ArkGoldilocks::from(seed);
        let b = ArkGoldilocks::from(seed.rotate_left(17));
        let c = ArkGoldilocks::from(seed.rotate_left(41));
        let value = Field64_3::new(a, b, c);
        let norm = formal_norm_from_coords([a, b, c]);
        let expanded = a * a * a
            + ArkGoldilocks::from(2u64) * b * b * b
            + ArkGoldilocks::from(4u64) * c * c * c
            - ArkGoldilocks::from(6u64) * a * b * c;
        assert_eq!(norm, expanded);
        assert_eq!(norm == ArkGoldilocks::ZERO, value == Field64_3::ZERO);
        if value != Field64_3::ZERO {
            // adj(v) * v = N(v), so T = N^{-1} yields exactly v^{-1}.
            let adj = formal_adjugate_from_coords([a, b, c]);
            let adj_ext = Field64_3::new(adj[0], adj[1], adj[2]);
            assert_eq!(
                value * adj_ext,
                Field64_3::new(norm, ArkGoldilocks::ZERO, ArkGoldilocks::ZERO)
            );
        }
    }
    assert_eq!(
        formal_norm_from_coords([
            ArkGoldilocks::ZERO,
            ArkGoldilocks::ZERO,
            ArkGoldilocks::ZERO
        ]),
        ArkGoldilocks::ZERO
    );
}

fn clone_tables(tables: &EvaluationTables<F>) -> EvaluationTables<F> {
    EvaluationTables {
        wire_values: tables.wire_values.clone(),
        constant_values: tables.constant_values.clone(),
        sigma_values: tables.sigma_values.clone(),
        public_inputs: tables.public_inputs.clone(),
        public_input_wires: tables.public_input_wires.clone(),
        public_inputs_hash: tables.public_inputs_hash,
        num_wires: tables.num_wires,
        num_routed_wires: tables.num_routed_wires,
        k_is: tables.k_is.clone(),
        subgroup: tables.subgroup.clone(),
        degree: tables.degree,
        degree_bits: tables.degree_bits,
    }
}
