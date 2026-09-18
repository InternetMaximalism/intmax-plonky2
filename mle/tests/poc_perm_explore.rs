//! Audit scratch: decode the plonky2 sigma map back into copy classes so the
//! adversarial PoCs can target one specific violated copy constraint.
//!
//! This file is exploratory instrumentation for the permutation re-audit; it
//! asserts only structural facts it prints.

use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, EvaluationTables};
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::plonk::prover::extract_evaluation_tables;
use plonky2::util::timing::TimingTree;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use std::collections::HashMap;

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

/// Invert `sigma[row][col] = k_is[tc] * subgroup[tr]` back to `(tr, tc)`.
pub fn decode_sigma(tables: &EvaluationTables<F>) -> Vec<Vec<(usize, usize)>> {
    let mut position: HashMap<u64, (usize, usize)> = HashMap::new();
    for (column, &k) in tables.k_is.iter().enumerate() {
        for (row, &g) in tables.subgroup.iter().enumerate() {
            position.insert((k * g).to_canonical_u64(), (row, column));
        }
    }
    (0..tables.degree)
        .map(|row| {
            (0..tables.num_routed_wires)
                .map(|column| {
                    *position
                        .get(&tables.sigma_values[row][column].to_canonical_u64())
                        .expect("sigma value is a valid k_i * g^row position")
                })
                .collect()
        })
        .collect()
}

/// Follow the sigma cycle from every cell and return the copy classes.
pub fn copy_classes(tables: &EvaluationTables<F>) -> Vec<Vec<(usize, usize)>> {
    let sigma = decode_sigma(tables);
    let mut seen = vec![vec![false; tables.num_routed_wires]; tables.degree];
    let mut classes = Vec::new();
    for row in 0..tables.degree {
        for column in 0..tables.num_routed_wires {
            if seen[row][column] {
                continue;
            }
            let mut cycle = Vec::new();
            let mut cursor = (row, column);
            loop {
                if seen[cursor.0][cursor.1] {
                    break;
                }
                seen[cursor.0][cursor.1] = true;
                cycle.push(cursor);
                cursor = sigma[cursor.0][cursor.1];
            }
            classes.push(cycle);
        }
    }
    classes
}

pub fn build_tables() -> (
    plonky2::plonk::circuit_data::CircuitData<F, C, D>,
    EvaluationTables<F>,
) {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let y = builder.add_virtual_target();
    let z = builder.add_virtual_target();
    // `p` is the public statement; `q` is a dead-end product that also reads
    // `x`, so `x` lives in a copy class of size >= 2 and the second endpoint's
    // gate constraint can be re-satisfied by adjusting only its output wire.
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

#[test]
fn dump_copy_classes() {
    let (circuit, tables) = build_tables();
    println!(
        "degree_bits={} degree={} num_wires={} num_routed={} num_pis={}",
        tables.degree_bits,
        tables.degree,
        tables.num_wires,
        tables.num_routed_wires,
        tables.public_inputs.len()
    );
    for (row, gate) in circuit.common.gates.iter().enumerate() {
        println!("gate row {row}: {}", gate.0.id());
    }
    println!("public_input_wires = {:?}", tables.public_input_wires);
    println!("public_inputs = {:?}", tables.public_inputs);
    let classes = copy_classes(&tables);
    let mut nontrivial = 0;
    for class in &classes {
        if class.len() < 2 {
            continue;
        }
        nontrivial += 1;
        let values = class
            .iter()
            .map(|&(row, column)| tables.wire_values[column][row].to_canonical_u64())
            .collect::<Vec<_>>();
        println!("class {class:?} values {values:?}");
    }
    println!("nontrivial classes: {nontrivial} / {}", classes.len());
    assert!(nontrivial > 0, "test circuit must have a copy constraint");
}
