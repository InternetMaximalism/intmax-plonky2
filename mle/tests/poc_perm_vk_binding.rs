//! Adversarial PoCs for the VK-side inputs of the wire-v3 permutation lane:
//! the sigma columns, the public-input wire map, and the identity-side
//! subgroup column. A table-level prover controls all three inputs to
//! `mle_prove_v2_from_tables`; none of them may become a free parameter.

use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::iop::wire::Wire;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, EvaluationTables};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::{Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::prover::extract_evaluation_tables;
use plonky2::util::timing::TimingTree;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field;
use plonky2_mle::prover_v2::{mle_prove_v2_from_tables, mle_setup_v2};
use plonky2_mle::verifier_v2::mle_verify_v2;

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

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

/// (v) Reroute the copy constraint itself: make sigma a different permutation
/// so the tampered witness *would* satisfy the multiset relation.
#[test]
fn poc_v_rerouted_sigma_is_rejected_by_the_vk_preprocessed_root() {
    let (circuit, honest) = build();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let digest = vk.circuit_digest.clone();

    let mut tables = clone_tables(&honest);
    // Break x's copy class {(0,0),(0,2),(0,4),(0,6)} at cell (0,6) ...
    tables.wire_values[6][0] += F::ONE;
    // ... and "repair" it by making (0,6) its own sigma fixed point, i.e. the
    // prover's preferred routing. sigma(row, col) = k_col * g^row.
    tables.sigma_values[0][6] = tables.k_is[6] * tables.subgroup[0];
    tables.sigma_values[0][4] = tables.k_is[4] * tables.subgroup[0];

    let proof = mle_prove_v2_from_tables(&circuit.common, &tables, &digest)
        .expect("table-level prover accepts rerouted sigmas");
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &proof)
        .expect_err("prover-chosen sigma columns must be rejected");
    println!("poc(v) rejection: {error}");
    assert!(
        error.to_string().contains("preprocessed root is not VK-bound"),
        "expected the VK preprocessed-root bind to reject, got: {error}"
    );
    assert_ne!(proof.preprocessed_root, vk.preprocessed_commitment_root);
}

/// (vi) Re-aim the public-input wire map at a cell that happens to hold the
/// claimed value. The map lives in the VK-bound circuit-config digest.
#[test]
fn poc_vi_reaimed_public_input_wire_map_is_rejected() {
    let (circuit, honest) = build();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let digest = vk.circuit_digest.clone();
    assert_eq!(honest.public_input_wires.len(), 1);
    println!("poc(vi) honest PI wire = {:?}", honest.public_input_wires[0]);

    let mut tables = clone_tables(&honest);
    // Claim a different public input and point the map at a spare routed cell
    // holding that value, leaving the real PI cell alone.
    let forged_value = F::from_canonical_u64(999);
    tables.public_inputs[0] = forged_value;
    tables.public_inputs_hash = PoseidonHash::hash_no_pad(&tables.public_inputs);
    let spare = Wire { row: 3, column: 60 };
    tables.wire_values[spare.column][spare.row] = forged_value;
    tables.public_input_wires[0] = spare;

    let proof = mle_prove_v2_from_tables(&circuit.common, &tables, &digest)
        .expect("table-level prover accepts a self-consistent forged map");
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &proof)
        .expect_err("a prover-chosen public-input wire map must be rejected");
    println!("poc(vi) rejection: {error}");
}

/// (vii) The identity side's `g^row` column is never committed: the verifier
/// recomputes its MLE evaluation from VK-bound generator powers. A prover that
/// permutes its own subgroup table therefore fails the terminal.
#[test]
fn poc_vii_permuted_subgroup_column_is_rejected() {
    let (circuit, honest) = build();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let digest = vk.circuit_digest.clone();

    let mut tables = clone_tables(&honest);
    assert!(tables.degree >= 4);
    // Keep index 1 (the only entry the generator-power derivation reads) so the
    // circuit-config digest and the whole transcript prefix stay identical.
    tables.subgroup.swap(2, 3);
    // Keep sigma consistent with the prover's own view of the positions.
    let proof = mle_prove_v2_from_tables(&circuit.common, &tables, &digest)
        .expect("table-level prover accepts a permuted subgroup column");
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &proof)
        .expect_err("a prover-chosen subgroup column must be rejected");
    println!("poc(vii) rejection: {error}");
    assert!(
        error.to_string().contains("norm/logUp terminal equation failed"),
        "expected the recomputed subgroup evaluation to reject, got: {error}"
    );
}
