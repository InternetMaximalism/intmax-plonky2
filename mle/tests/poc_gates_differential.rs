//! Adversarial differential test: MLE `gate_ext3` vs plonky2's own gate evaluator.
//!
//! GROUND TRUTH is `plonky2::plonk::vanishing_poly::evaluate_gate_constraints`,
//! which calls `Gate::eval_filtered` -> `compute_filter` + `Gate::eval_unfiltered`
//! for every gate row and accumulates into `num_gate_constraints` slots.
//!
//! The MLE side is `plonky2_mle::gate_ext3::evaluate_gate_constraints_ext3`
//! (plus `validate_gate_ext3_context` / `evaluate_gate_constraints_ext3_validated`).
//!
//! Both sides are evaluated at the SAME base-field (Goldilocks) wire/constant
//! assignment: plonky2 over `QuadraticExtension<F>` embedded from the base, the
//! MLE side over `Field64_3` embedded from the base (c1 = c2 = 0). Every slot of
//! the two accumulated constraint vectors must agree.
//!
//! Soundness argument for why base-point agreement suffices: both evaluators are
//! polynomial maps with Goldilocks coefficients in the wires/constants. Agreement
//! at many independent uniform base points implies formal polynomial equality by
//! Schwartz-Zippel (total degree <= a few hundred vs |F| = 2^64 - 2^32 + 1), and
//! formal equality over F implies equality over every extension of F, including
//! Fp3. (The "the MLE map really is defined over Goldilocks" half is the existing
//! in-crate Frobenius test `off_base_ext3_evaluation_commutes_with_frobenius_for_every_gate`.)

use std::collections::BTreeSet;

use plonky2::gates::arithmetic_base::ArithmeticGate;
use plonky2::gates::arithmetic_extension::ArithmeticExtensionGate;
use plonky2::gates::base_sum::BaseSumGate;
use plonky2::gates::constant::ConstantGate;
use plonky2::gates::coset_interpolation::CosetInterpolationGate;
use plonky2::gates::exponentiation::ExponentiationGate;
use plonky2::gates::multiplication_extension::MulExtensionGate;
use plonky2::gates::noop::NoopGate;
use plonky2::gates::poseidon::PoseidonGate;
use plonky2::gates::poseidon_mds::PoseidonMdsGate;
use plonky2::gates::public_input::PublicInputGate;
use plonky2::gates::random_access::RandomAccessGate;
use plonky2::gates::reducing::ReducingGate;
use plonky2::gates::reducing_extension::ReducingExtensionGate;
use plonky2::hash::hash_types::HashOut;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::plonk::vanishing_poly::evaluate_gate_constraints;
use plonky2::plonk::vars::EvaluationVars;
use plonky2_field::extension::quadratic::QuadraticExtension;
use plonky2_field::extension::FieldExtension;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field as PlonkyField, Field64, PrimeField64};
use plonky2_mle::gate_ext3::{
    aggregate_gate_constraints_ext3, evaluate_gate_aggregation_ext3,
    evaluate_gate_constraints_ext3_validated, validate_gate_ext3_context,
};
use plonky2_mle::vk_v2::collect_gate_info_v2;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use whir::algebra::fields::Field64_3;

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;
const UNUSED_SELECTOR: u64 = u32::MAX as u64;

fn base_to_k(value: F) -> Field64_3 {
    Field64_3::from(value.to_canonical_u64())
}

fn rand_f(rng: &mut StdRng) -> F {
    F::from_canonical_u64(rng.gen::<u64>() % F::ORDER)
}

/// Circuit A: the parameter sizes a real `standard_recursion_config` circuit uses.
fn common_a() -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let ra = RandomAccessGate::<F, D>::new_from_config(&config, 1);
    let ra_consts = ra.num_extra_constants;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    builder.add_gate(NoopGate, vec![]);
    builder.add_gate(ConstantGate::new(2), vec![F::from_canonical_u64(3); 2]);
    builder.add_gate(PublicInputGate, vec![]);
    builder.add_gate(
        ArithmeticGate { num_ops: 20 },
        vec![F::from_canonical_u64(5), F::from_canonical_u64(7)],
    );
    builder.add_gate(
        ArithmeticExtensionGate::<D> { num_ops: 10 },
        vec![F::from_canonical_u64(11), F::from_canonical_u64(13)],
    );
    builder.add_gate(
        MulExtensionGate::<D> { num_ops: 13 },
        vec![F::from_canonical_u64(17)],
    );
    builder.add_gate(BaseSumGate::<2>::new(63), vec![]);
    builder.add_gate(ReducingGate::<D>::new(43), vec![]);
    builder.add_gate(ReducingExtensionGate::<D>::new(32), vec![]);
    builder.add_gate(ExponentiationGate::<F, D>::new(66), vec![]);
    builder.add_gate(PoseidonGate::<F, D>::new(), vec![]);
    builder.add_gate(PoseidonMdsGate::<F, D>::new(), vec![]);
    builder.add_gate(ra, vec![F::from_canonical_u64(19); ra_consts]);
    builder.add_gate(
        CosetInterpolationGate::<F, D>::with_max_degree(4, 4),
        vec![],
    );
    builder.build::<C>().common
}

/// Circuit B: alternative parameter choices (base-4 BaseSum, small op counts,
/// CosetInterpolation at subgroup_bits 2 and 5, RandomAccess bits = 2).
fn common_b() -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let ra = RandomAccessGate::<F, D>::new_from_config(&config, 2);
    let ra_consts = ra.num_extra_constants;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    builder.add_gate(NoopGate, vec![]);
    builder.add_gate(ConstantGate::new(1), vec![F::from_canonical_u64(3)]);
    builder.add_gate(PublicInputGate, vec![]);
    builder.add_gate(
        ArithmeticGate { num_ops: 1 },
        vec![F::from_canonical_u64(5), F::from_canonical_u64(7)],
    );
    builder.add_gate(
        ArithmeticExtensionGate::<D> { num_ops: 1 },
        vec![F::from_canonical_u64(11), F::from_canonical_u64(13)],
    );
    builder.add_gate(
        MulExtensionGate::<D> { num_ops: 1 },
        vec![F::from_canonical_u64(17)],
    );
    builder.add_gate(ReducingGate::<D>::new(3), vec![]);
    builder.add_gate(ReducingExtensionGate::<D>::new(3), vec![]);
    builder.add_gate(ExponentiationGate::<F, D>::new(1), vec![]);
    builder.add_gate(PoseidonMdsGate::<F, D>::new(), vec![]);
    builder.add_gate(ra, vec![F::from_canonical_u64(19); ra_consts]);
    builder.add_gate(
        CosetInterpolationGate::<F, D>::with_max_degree(2, 2),
        vec![],
    );
    builder.add_gate(
        CosetInterpolationGate::<F, D>::with_max_degree(5, 4),
        vec![],
    );
    builder.add_gate(BaseSumGate::<4>::new(31), vec![]);
    builder.build::<C>().common
}

/// Circuit C: the high-degree RandomAccess widths (bits 3 and 4) plus Poseidon.
fn common_c() -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let ra3 = RandomAccessGate::<F, D>::new_from_config(&config, 3);
    let ra3_consts = ra3.num_extra_constants;
    let ra4 = RandomAccessGate::<F, D>::new_from_config(&config, 4);
    let ra4_consts = ra4.num_extra_constants;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    builder.add_gate(NoopGate, vec![]);
    builder.add_gate(ConstantGate::new(2), vec![F::from_canonical_u64(3); 2]);
    builder.add_gate(PublicInputGate, vec![]);
    builder.add_gate(PoseidonMdsGate::<F, D>::new(), vec![]);
    builder.add_gate(ra3, vec![F::from_canonical_u64(19); ra3_consts]);
    builder.add_gate(ra4, vec![F::from_canonical_u64(23); ra4_consts]);
    builder.add_gate(PoseidonGate::<F, D>::new(), vec![]);
    builder.add_gate(ExponentiationGate::<F, D>::new(66), vec![]);
    builder.build::<C>().common
}

/// Compare the two evaluators at one (wires, constants, public_inputs_hash).
fn assert_agrees(
    label: &str,
    common: &CommonCircuitData<F, D>,
    context: &plonky2_mle::gate_ext3::GateExt3Context,
    wires: &[F],
    constants: &[F],
    pih: &HashOut<F>,
) -> Vec<Field64_3> {
    let wires_ext: Vec<QuadraticExtension<F>> = wires
        .iter()
        .copied()
        .map(<QuadraticExtension<F> as FieldExtension<D>>::from_basefield)
        .collect();
    let constants_ext: Vec<QuadraticExtension<F>> = constants
        .iter()
        .copied()
        .map(<QuadraticExtension<F> as FieldExtension<D>>::from_basefield)
        .collect();
    let production = evaluate_gate_constraints::<F, D>(
        common,
        EvaluationVars {
            local_constants: &constants_ext,
            local_wires: &wires_ext,
            public_inputs_hash: pih,
        },
    );
    let wires_k: Vec<Field64_3> = wires.iter().copied().map(base_to_k).collect();
    let constants_k: Vec<Field64_3> = constants.iter().copied().map(base_to_k).collect();
    let ours = evaluate_gate_constraints_ext3_validated(context, &wires_k, &constants_k, pih)
        .unwrap_or_else(|e| panic!("[{label}] MLE evaluator failed: {e:#}"));

    assert_eq!(
        ours.len(),
        production.len(),
        "[{label}] constraint-vector length mismatch (MLE {} vs plonky2 {})",
        ours.len(),
        production.len()
    );
    assert_eq!(
        ours.len(),
        common.num_gate_constraints,
        "[{label}] MLE vector is not num_gate_constraints long"
    );
    for (slot, (mine, theirs)) in ours.iter().zip(&production).enumerate() {
        let components: [F; D] =
            <QuadraticExtension<F> as FieldExtension<D>>::to_basefield_array(theirs);
        assert_eq!(
            components[1],
            F::ZERO,
            "[{label}] plonky2 left the base field at slot {slot}"
        );
        assert_eq!(
            *mine,
            base_to_k(components[0]),
            "[{label}] slot {slot}: MLE {mine:?} != plonky2 {:?}",
            components[0]
        );
    }
    ours
}

fn run_circuit(label: &str, common: &CommonCircuitData<F, D>, seed: u64, trials: usize) -> Vec<u8> {
    let gate_infos = collect_gate_info_v2(common).expect("collect_gate_info_v2");
    let context = validate_gate_ext3_context(common, &gate_infos).expect("validate context");
    let num_selectors = common.selectors_info.num_selectors();
    let mut rng = StdRng::seed_from_u64(seed);

    // 1. Per-gate isolation: exactly one gate family is selected, every other
    //    selector polynomial is UNUSED. This pins down per-constraint-index
    //    formulas for that family.
    for target in &gate_infos {
        for _ in 0..trials {
            let wires: Vec<F> = (0..common.config.num_wires).map(|_| rand_f(&mut rng)).collect();
            let mut constants: Vec<F> = (0..common.num_constants)
                .map(|_| rand_f(&mut rng))
                .collect();
            for sel in constants.iter_mut().take(num_selectors) {
                *sel = F::from_canonical_u64(UNUSED_SELECTOR);
            }
            constants[usize::from(target.selector_index)] =
                F::from_canonical_u64(u64::from(target.gate_row_index));
            let pih = HashOut {
                elements: [
                    rand_f(&mut rng),
                    rand_f(&mut rng),
                    rand_f(&mut rng),
                    rand_f(&mut rng),
                ],
            };
            let ours = assert_agrees(
                &format!("{label}/isolated gate_id={} row={}", target.gate_id, target.gate_row_index),
                common,
                &context,
                &wires,
                &constants,
                &pih,
            );
            // With the gate isolated, everything past its own constraint count
            // must be identically zero: catches a family that writes into more
            // slots than plonky2's num_constraints().
            for (slot, value) in ours.iter().enumerate().skip(usize::from(target.num_constraints)) {
                assert_eq!(
                    *value,
                    Field64_3::from(0u64),
                    "[{label}] gate_id={} wrote slot {slot} beyond its {} constraints",
                    target.gate_id,
                    target.num_constraints
                );
            }
        }
    }

    // 2. Fully random selectors: every gate row contributes with a non-trivial
    //    filter, so this exercises compute_filter (group ranges, UNUSED_SELECTOR,
    //    many_selector) and the cross-gate slot accumulation.
    for _ in 0..trials {
        let wires: Vec<F> = (0..common.config.num_wires).map(|_| rand_f(&mut rng)).collect();
        let constants: Vec<F> = (0..common.num_constants)
            .map(|_| rand_f(&mut rng))
            .collect();
        let pih = HashOut {
            elements: [
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
            ],
        };
        let ours = assert_agrees(
            &format!("{label}/random-selectors"),
            common,
            &context,
            &wires,
            &constants,
            &pih,
        );

        // 3. The alpha aggregation the verifier actually consumes.
        let alpha = Field64_3::from(rng.gen::<u64>() % F::ORDER);
        let aggregate = evaluate_gate_aggregation_ext3(
            common,
            &gate_infos,
            &wires.iter().copied().map(base_to_k).collect::<Vec<_>>(),
            &constants.iter().copied().map(base_to_k).collect::<Vec<_>>(),
            &pih,
            alpha,
        )
        .expect("aggregation");
        assert_eq!(
            aggregate,
            aggregate_gate_constraints_ext3(&ours, alpha),
            "[{label}] aggregation is not sum_c alpha^c C_c over the same vector"
        );
    }

    // Constraint-count agreement, stated separately from the value agreement.
    for (row, gate) in common.gates.iter().enumerate() {
        assert_eq!(
            usize::from(gate_infos[row].num_constraints),
            gate.0.num_constraints(),
            "[{label}] row {row} GateInfoV2.num_constraints != plonky2 num_constraints()"
        );
    }

    println!(
        "[{label}] OK: {} rows, {} selectors, num_gate_constraints={}, qdf={}, gate_ids={:?}",
        common.gates.len(),
        num_selectors,
        common.num_gate_constraints,
        common.quotient_degree_factor,
        gate_infos.iter().map(|g| g.gate_id).collect::<BTreeSet<_>>()
    );
    for (row, gate) in common.gates.iter().enumerate() {
        println!(
            "    row {row}: id={} gate_id={} nc={} p1={} p2={} p3={} sel={} group={}..{} deg={}",
            gate.0.id(),
            gate_infos[row].gate_id,
            gate_infos[row].num_constraints,
            gate_infos[row].num_or_consts,
            gate_infos[row].param2,
            gate_infos[row].param3,
            gate_infos[row].selector_index,
            gate_infos[row].group_start,
            gate_infos[row].group_end,
            gate.0.degree(),
        );
    }
    gate_infos.iter().map(|g| g.gate_id).collect()
}

/// Negative control: the comparison above is not vacuous. Perturbing a single
/// wire on the MLE side only must make at least one slot disagree, for every
/// gate family that has at least one constraint.
#[test]
fn differential_comparison_is_not_vacuous() {
    let common = common_a();
    let gate_infos = collect_gate_info_v2(&common).unwrap();
    let context = validate_gate_ext3_context(&common, &gate_infos).unwrap();
    let num_selectors = common.selectors_info.num_selectors();
    let mut rng = StdRng::seed_from_u64(0xDEAD_BEEF);

    for target in &gate_infos {
        if target.num_constraints == 0 {
            continue; // NoopGate has nothing to disagree about.
        }
        let wires: Vec<F> = (0..common.config.num_wires)
            .map(|_| rand_f(&mut rng))
            .collect();
        let mut constants: Vec<F> = (0..common.num_constants)
            .map(|_| rand_f(&mut rng))
            .collect();
        for sel in constants.iter_mut().take(num_selectors) {
            *sel = F::from_canonical_u64(UNUSED_SELECTOR);
        }
        constants[usize::from(target.selector_index)] =
            F::from_canonical_u64(u64::from(target.gate_row_index));
        let pih = HashOut {
            elements: [
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
            ],
        };

        let wires_ext: Vec<QuadraticExtension<F>> = wires
            .iter()
            .copied()
            .map(<QuadraticExtension<F> as FieldExtension<D>>::from_basefield)
            .collect();
        let constants_ext: Vec<QuadraticExtension<F>> = constants
            .iter()
            .copied()
            .map(<QuadraticExtension<F> as FieldExtension<D>>::from_basefield)
            .collect();
        let production = evaluate_gate_constraints::<F, D>(
            &common,
            EvaluationVars {
                local_constants: &constants_ext,
                local_wires: &wires_ext,
                public_inputs_hash: &pih,
            },
        );

        // Perturb every wire on the MLE side only.
        let mut wires_k: Vec<Field64_3> = wires.iter().copied().map(base_to_k).collect();
        for w in wires_k.iter_mut() {
            *w += Field64_3::from(1u64);
        }
        let constants_k: Vec<Field64_3> = constants.iter().copied().map(base_to_k).collect();
        let perturbed =
            evaluate_gate_constraints_ext3_validated(&context, &wires_k, &constants_k, &pih)
                .unwrap();
        let differs = perturbed.iter().zip(&production).any(|(mine, theirs)| {
            let components: [F; D] =
                <QuadraticExtension<F> as FieldExtension<D>>::to_basefield_array(theirs);
            *mine != base_to_k(components[0])
        });
        assert!(
            differs,
            "negative control failed: gate_id={} is insensitive to its wires",
            target.gate_id
        );
    }
    println!("negative control OK: every non-trivial gate family is wire-sensitive");
}

#[test]
fn mle_gate_evaluator_matches_plonky2_on_realistic_parameters() {
    let mut covered: BTreeSet<u8> = BTreeSet::new();
    covered.extend(run_circuit("A", &common_a(), 0xA11CE, 4));
    covered.extend(run_circuit("B", &common_b(), 0xB0B, 4));
    covered.extend(run_circuit("C", &common_c(), 0xC0FFEE, 4));
    assert_eq!(
        covered,
        (0u8..=13).collect::<BTreeSet<_>>(),
        "differential test must cover every supported gate id"
    );
    println!("covered gate ids: {covered:?}");
}
