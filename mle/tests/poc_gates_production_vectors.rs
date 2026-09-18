//! Production-parameter gate vectors: Rust MLE evaluator -> JSON -> Solidity.
//!
//! The checked-in `testdata/gate_ext3_vectors.json` pins the Rust<->Solidity
//! Ext3 gate evaluator at TOY parameters (ArithmeticGate 2 ops, BaseSum 4 limbs,
//! Reducing 3 coeffs, Exponentiation 3 bits, CosetInterpolation degree 4, ...).
//! The deployed circuits use very different sizes. This test reproduces the two
//! real deployed gate tables
//! (`intmax3-zkp/contracts/test/data/withdrawal_mle_config.json` and
//! `post_close_claim_mle_config.json`), checks them against plonky2's own
//! evaluator on base-embedded points, and emits
//! `testdata/poc_gate_ext3_production_vectors.json` for the companion Foundry
//! test `contracts/test/PocGateExt3Production.t.sol`.
//!
//! Nothing existing is modified: the JSON path is new and is only written by
//! the `#[ignore]`d dump test.

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
use plonky2_mle::gate_ext3::{evaluate_gate_aggregation_ext3, evaluate_gate_constraints_ext3};
use plonky2_mle::proof_v2::GateInfoV2;
use plonky2_mle::vk_v2::collect_gate_info_v2;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde::{Deserialize, Serialize};
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use ark_ff::PrimeField as ArkPrimeField;

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;
const UNUSED_SELECTOR: u64 = u32::MAX as u64;
const JSON_PATH: &str = "testdata/poc_gate_ext3_production_vectors.json";

type ExtRecord = [String; 3];

// ---------------------------------------------------------------------------
// JSON schema (mirrors testdata/gate_ext3_vectors.json's conventions: fixed
// width lowercase `0x%016x` limbs, [c0, c1, c2] order)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct GateRecord {
    gate_id: u8,
    selector_index: u8,
    group_start: u8,
    group_end: u8,
    gate_row_index: u8,
    num_constraints: u16,
    num_or_consts: u16,
    param2: u16,
    param3: u16,
}

impl From<GateInfoV2> for GateRecord {
    fn from(v: GateInfoV2) -> Self {
        Self {
            gate_id: v.gate_id,
            selector_index: v.selector_index,
            group_start: v.group_start,
            group_end: v.group_end,
            gate_row_index: v.gate_row_index,
            num_constraints: v.num_constraints,
            num_or_consts: v.num_or_consts,
            param2: v.param2,
            param3: v.param3,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ConfigRecord {
    num_wires: usize,
    num_constants: usize,
    num_selectors: usize,
    num_gate_constraints: usize,
    quotient_degree_factor: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct VectorRecord {
    label: String,
    /// Index into the enclosing config's `wire_sets`.
    wires_index: usize,
    /// True when every wire/constant limb has c1 = c2 = 0, i.e. this vector was
    /// also cross-checked against plonky2's `evaluate_gate_constraints`.
    base_embedded: bool,
    constants: Vec<ExtRecord>,
    public_inputs_hash: [String; 4],
    alpha: ExtRecord,
    expected_filtered_constraints: Vec<ExtRecord>,
    expected_aggregation: ExtRecord,
    /// A second, independent aggregation challenge over the SAME slot vector.
    /// `evalCombined` only returns the alpha-reduction, so two independent
    /// alphas turn "the aggregate matches" into "every one of the 123 slots
    /// matches" with soundness error ~ (numGateConstraints/|Fp3|)^2.
    alpha2: ExtRecord,
    expected_aggregation2: ExtRecord,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ConfigVectors {
    name: String,
    config: ConfigRecord,
    num_gates: usize,
    num_wire_sets: usize,
    num_vectors: usize,
    gates: Vec<GateRecord>,
    wire_sets: Vec<Vec<ExtRecord>>,
    vectors: Vec<VectorRecord>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ProductionFixture {
    schema: String,
    version: u64,
    field_modulus: String,
    limb_order: [String; 3],
    configs: Vec<ConfigVectors>,
}

// ---------------------------------------------------------------------------
// Encoding helpers (identical conventions to tests/dump_gate_ext3_vectors.rs)
// ---------------------------------------------------------------------------

fn encode_limb(value: u64) -> String {
    format!("0x{value:016x}")
}

fn encode_ext(value: Field64_3) -> ExtRecord {
    [
        encode_limb(value.c0.into_bigint().0[0]),
        encode_limb(value.c1.into_bigint().0[0]),
        encode_limb(value.c2.into_bigint().0[0]),
    ]
}

fn rand_u64(rng: &mut StdRng) -> u64 {
    rng.gen::<u64>() % F::ORDER
}

fn rand_f(rng: &mut StdRng) -> F {
    F::from_canonical_u64(rand_u64(rng))
}

/// Uniform Ext3 with both extension limbs forced non-zero, so the Solidity
/// evaluator really runs its cubic-extension arithmetic.
fn rand_ext3(rng: &mut StdRng) -> Field64_3 {
    let nonzero = |rng: &mut StdRng| {
        let mut v = rand_u64(rng);
        if v == 0 {
            v = 1;
        }
        v
    };
    Field64_3::new(
        ArkGoldilocks::from(rand_u64(rng)),
        ArkGoldilocks::from(nonzero(rng)),
        ArkGoldilocks::from(nonzero(rng)),
    )
}

fn base_to_k(value: F) -> Field64_3 {
    Field64_3::from(value.to_canonical_u64())
}

// ---------------------------------------------------------------------------
// The two deployed gate tables, transcribed from the parent-repo configs
// ---------------------------------------------------------------------------

const fn g(
    gate_id: u8,
    selector_index: u8,
    group_start: u8,
    group_end: u8,
    gate_row_index: u8,
    num_constraints: u16,
    num_or_consts: u16,
    param2: u16,
    param3: u16,
) -> GateInfoV2 {
    GateInfoV2 {
        gate_id,
        selector_index,
        group_start,
        group_end,
        gate_row_index,
        num_constraints,
        num_or_consts,
        param2,
        param3,
    }
}

/// `intmax3-zkp/contracts/test/data/withdrawal_mle_config.json`
/// `.verificationConfig.gates` (3 selectors, numConstants 5).
const WITHDRAWAL_GATES: [GateInfoV2; 13] = [
    g(0, 0, 0, 7, 0, 0, 0, 0, 0),
    g(1, 0, 0, 7, 1, 2, 2, 0, 0),
    g(5, 0, 0, 7, 2, 24, 0, 0, 0),
    g(2, 0, 0, 7, 3, 4, 0, 0, 0),
    g(9, 0, 0, 7, 4, 64, 63, 2, 0),
    g(11, 0, 0, 7, 5, 64, 32, 0, 0),
    g(10, 0, 0, 7, 6, 86, 43, 0, 0),
    g(6, 1, 7, 11, 7, 20, 10, 0, 0),
    g(3, 1, 7, 11, 8, 20, 20, 0, 0),
    g(7, 1, 7, 11, 9, 26, 13, 0, 0),
    g(12, 1, 7, 11, 10, 26, 4, 4, 2),
    g(13, 2, 11, 13, 11, 12, 4, 6, 0),
    g(4, 2, 11, 13, 12, 123, 0, 0, 0),
];

/// `intmax3-zkp/contracts/test/data/post_close_claim_mle_config.json`
/// `.verificationConfig.gates` (4 selectors, numConstants 6).
const POST_CLOSE_CLAIM_GATES: [GateInfoV2; 13] = [
    g(0, 0, 0, 6, 0, 0, 0, 0, 0),
    g(5, 0, 0, 6, 1, 24, 0, 0, 0),
    g(2, 0, 0, 6, 2, 4, 0, 0, 0),
    g(9, 0, 0, 6, 3, 64, 63, 2, 0),
    g(11, 0, 0, 6, 4, 64, 32, 0, 0),
    g(10, 0, 0, 6, 5, 86, 43, 0, 0),
    g(6, 1, 6, 10, 6, 20, 10, 0, 0),
    g(3, 1, 6, 10, 7, 20, 20, 0, 0),
    g(7, 1, 6, 10, 8, 26, 13, 0, 0),
    g(8, 1, 6, 10, 9, 67, 66, 0, 0),
    g(12, 2, 10, 12, 10, 26, 4, 4, 2),
    g(13, 2, 10, 12, 11, 12, 4, 6, 0),
    g(4, 3, 12, 13, 12, 123, 0, 0, 0),
];

/// Rebuild the withdrawal-family circuit's gate table. `CircuitBuilder` sorts
/// `common_data.gates` by `(degree, id())` (plonky2/src/plonk/circuit_builder.rs:1185),
/// which is deterministic, so this reproduces the deployed row order exactly.
fn common_withdrawal() -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let ra = RandomAccessGate::<F, D>::new_from_config(&config, 4);
    let ra_consts = ra.num_extra_constants;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    builder.add_gate(NoopGate, vec![]);
    builder.add_gate(ConstantGate::new(2), vec![F::from_canonical_u64(3); 2]);
    builder.add_gate(PoseidonMdsGate::<F, D>::new(), vec![]);
    builder.add_gate(PublicInputGate, vec![]);
    builder.add_gate(BaseSumGate::<2>::new(63), vec![]);
    builder.add_gate(ReducingExtensionGate::<D>::new(32), vec![]);
    builder.add_gate(ReducingGate::<D>::new(43), vec![]);
    builder.add_gate(
        ArithmeticExtensionGate::<D> { num_ops: 10 },
        vec![F::from_canonical_u64(11), F::from_canonical_u64(13)],
    );
    builder.add_gate(
        ArithmeticGate { num_ops: 20 },
        vec![F::from_canonical_u64(5), F::from_canonical_u64(7)],
    );
    builder.add_gate(
        MulExtensionGate::<D> { num_ops: 13 },
        vec![F::from_canonical_u64(17)],
    );
    builder.add_gate(ra, vec![F::from_canonical_u64(19); ra_consts]);
    builder.add_gate(
        CosetInterpolationGate::<F, D>::with_max_degree(4, 6),
        vec![],
    );
    builder.add_gate(PoseidonGate::<F, D>::new(), vec![]);
    builder.build::<C>().common
}

/// Rebuild the post-close-claim-family circuit's gate table (adds
/// `ExponentiationGate(66)`, drops `ConstantGate`, 4 selectors).
fn common_post_close_claim() -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let ra = RandomAccessGate::<F, D>::new_from_config(&config, 4);
    let ra_consts = ra.num_extra_constants;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    builder.add_gate(NoopGate, vec![]);
    builder.add_gate(PoseidonMdsGate::<F, D>::new(), vec![]);
    builder.add_gate(PublicInputGate, vec![]);
    builder.add_gate(BaseSumGate::<2>::new(63), vec![]);
    builder.add_gate(ReducingExtensionGate::<D>::new(32), vec![]);
    builder.add_gate(ReducingGate::<D>::new(43), vec![]);
    builder.add_gate(
        ArithmeticExtensionGate::<D> { num_ops: 10 },
        vec![F::from_canonical_u64(11), F::from_canonical_u64(13)],
    );
    builder.add_gate(
        ArithmeticGate { num_ops: 20 },
        vec![F::from_canonical_u64(5), F::from_canonical_u64(7)],
    );
    builder.add_gate(
        MulExtensionGate::<D> { num_ops: 13 },
        vec![F::from_canonical_u64(17)],
    );
    builder.add_gate(ExponentiationGate::<F, D>::new(66), vec![]);
    builder.add_gate(ra, vec![F::from_canonical_u64(19); ra_consts]);
    builder.add_gate(
        CosetInterpolationGate::<F, D>::with_max_degree(4, 6),
        vec![],
    );
    builder.add_gate(PoseidonGate::<F, D>::new(), vec![]);
    builder.build::<C>().common
}

// ---------------------------------------------------------------------------

/// Evaluate on base-embedded values and cross-check plonky2's own evaluator.
fn plonky2_cross_check(
    label: &str,
    common: &CommonCircuitData<F, D>,
    gate_infos: &[GateInfoV2],
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
    let ours = evaluate_gate_constraints_ext3(
        common,
        gate_infos,
        &wires.iter().copied().map(base_to_k).collect::<Vec<_>>(),
        &constants.iter().copied().map(base_to_k).collect::<Vec<_>>(),
        pih,
    )
    .unwrap_or_else(|e| panic!("[{label}] MLE evaluator failed: {e:#}"));
    assert_eq!(ours.len(), production.len(), "[{label}] length mismatch");
    for (slot, (mine, theirs)) in ours.iter().zip(&production).enumerate() {
        let c: [F; D] = <QuadraticExtension<F> as FieldExtension<D>>::to_basefield_array(theirs);
        assert_eq!(c[1], F::ZERO, "[{label}] plonky2 left the base field at {slot}");
        assert_eq!(
            *mine,
            base_to_k(c[0]),
            "[{label}] slot {slot}: MLE != plonky2 ({:?})",
            c[0]
        );
    }
    ours
}

fn build_config_vectors(
    name: &str,
    common: &CommonCircuitData<F, D>,
    expected_gates: &[GateInfoV2],
    expected_num_constants: usize,
    expected_num_selectors: usize,
    seed: u64,
) -> ConfigVectors {
    let gate_infos = collect_gate_info_v2(common).expect("collect_gate_info_v2");
    assert_eq!(
        gate_infos, expected_gates,
        "[{name}] rebuilt gate table does not match the deployed configuration"
    );
    assert_eq!(common.config.num_wires, 135, "[{name}] numWires");
    assert_eq!(common.config.num_routed_wires, 80, "[{name}] numRoutedWires");
    assert_eq!(common.num_constants, expected_num_constants, "[{name}] numConstants");
    assert_eq!(
        common.selectors_info.num_selectors(),
        expected_num_selectors,
        "[{name}] numSelectors"
    );
    assert_eq!(common.num_gate_constraints, 123, "[{name}] numGateConstraints");
    assert_eq!(common.quotient_degree_factor, 8, "[{name}] quotientDegreeFactor");

    let mut rng = StdRng::seed_from_u64(seed);
    let num_selectors = common.selectors_info.num_selectors();
    let num_constants = common.num_constants;
    let num_wires = common.config.num_wires;

    // wire_sets[0], [1]: full Ext3. wire_sets[2]: base-embedded (c1 = c2 = 0).
    let wires_ext3_a: Vec<Field64_3> = (0..num_wires).map(|_| rand_ext3(&mut rng)).collect();
    let wires_ext3_b: Vec<Field64_3> = (0..num_wires).map(|_| rand_ext3(&mut rng)).collect();
    let wires_base: Vec<F> = (0..num_wires).map(|_| rand_f(&mut rng)).collect();
    let wires_base_k: Vec<Field64_3> = wires_base.iter().copied().map(base_to_k).collect();
    let wire_sets = vec![
        wires_ext3_a.iter().copied().map(encode_ext).collect(),
        wires_ext3_b.iter().copied().map(encode_ext).collect(),
        wires_base_k.iter().copied().map(encode_ext).collect(),
    ];

    let mut vectors = Vec::new();

    let mut emit = |label: String,
                    wires_index: usize,
                    base_embedded: bool,
                    wires: &[Field64_3],
                    constants: &[Field64_3],
                    pih: &HashOut<F>,
                    alpha: Field64_3,
                    alpha2: Field64_3,
                    rust_slots: Vec<Field64_3>| {
        let reduce = |challenge: Field64_3| {
            let mut power = Field64_3::from(1u64);
            let mut acc = Field64_3::from(0u64);
            for slot in &rust_slots {
                acc += power * *slot;
                power *= challenge;
            }
            acc
        };
        let aggregation =
            evaluate_gate_aggregation_ext3(common, &gate_infos, wires, constants, pih, alpha)
                .expect("aggregation");
        let aggregation2 =
            evaluate_gate_aggregation_ext3(common, &gate_infos, wires, constants, pih, alpha2)
                .expect("aggregation2");
        // The aggregate must be sum_c alpha^c * slot_c over the very vector we
        // are about to publish.
        assert_eq!(reduce(alpha), aggregation, "[{label}] alpha aggregation mismatch");
        assert_eq!(reduce(alpha2), aggregation2, "[{label}] alpha2 aggregation mismatch");
        assert_ne!(alpha, alpha2, "[{label}] the two challenges must differ");
        vectors.push(VectorRecord {
            label,
            wires_index,
            base_embedded,
            constants: constants.iter().copied().map(encode_ext).collect(),
            public_inputs_hash: [
                encode_limb(pih.elements[0].to_canonical_u64()),
                encode_limb(pih.elements[1].to_canonical_u64()),
                encode_limb(pih.elements[2].to_canonical_u64()),
                encode_limb(pih.elements[3].to_canonical_u64()),
            ],
            alpha: encode_ext(alpha),
            expected_filtered_constraints: rust_slots.into_iter().map(encode_ext).collect(),
            expected_aggregation: encode_ext(aggregation),
            alpha2: encode_ext(alpha2),
            expected_aggregation2: encode_ext(aggregation2),
        });
    };

    // (a) One isolated-family Ext3 vector per deployed row: the target selector
    //     equals its row index, every other selector is UNUSED, and all local
    //     constants and wires are full Ext3 values.
    for target in &gate_infos {
        let mut constants: Vec<Field64_3> = (0..num_constants).map(|_| rand_ext3(&mut rng)).collect();
        for sel in constants.iter_mut().take(num_selectors) {
            *sel = Field64_3::from(UNUSED_SELECTOR);
        }
        constants[usize::from(target.selector_index)] =
            Field64_3::from(u64::from(target.gate_row_index));
        let pih = HashOut {
            elements: [
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
            ],
        };
        let alpha = rand_ext3(&mut rng);
        let alpha2 = rand_ext3(&mut rng);
        let slots = evaluate_gate_constraints_ext3(
            common,
            &gate_infos,
            &wires_ext3_a,
            &constants,
            &pih,
        )
        .expect("ext3 isolated");
        emit(
            format!("{name}/ext3-isolated/gate_id={}/row={}", target.gate_id, target.gate_row_index),
            0,
            false,
            &wires_ext3_a,
            &constants,
            &pih,
            alpha,
            alpha2,
            slots,
        );
    }

    // (b) Two mixed Ext3 vectors: every selector is a non-base Ext3 value, so no
    //     filter can vanish and all 13 deployed rows contribute simultaneously.
    for index in 0..2 {
        let constants: Vec<Field64_3> = (0..num_constants).map(|_| rand_ext3(&mut rng)).collect();
        let pih = HashOut {
            elements: [
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
            ],
        };
        let alpha = rand_ext3(&mut rng);
        let alpha2 = rand_ext3(&mut rng);
        let slots =
            evaluate_gate_constraints_ext3(common, &gate_infos, &wires_ext3_b, &constants, &pih)
                .expect("ext3 mixed");
        emit(
            format!("{name}/ext3-mixed-selectors/{index}"),
            1,
            false,
            &wires_ext3_b,
            &constants,
            &pih,
            alpha,
            alpha2,
            slots,
        );
    }

    // (c) Three base-embedded vectors with fully random base selectors. These are
    //     ALSO cross-checked against plonky2's `evaluate_gate_constraints`, so the
    //     JSON the Solidity test replays is anchored to plonky2, not only to the
    //     Rust MLE evaluator.
    for index in 0..3 {
        let constants_base: Vec<F> = (0..num_constants).map(|_| rand_f(&mut rng)).collect();
        let pih = HashOut {
            elements: [
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
                rand_f(&mut rng),
            ],
        };
        let alpha = rand_ext3(&mut rng);
        let alpha2 = rand_ext3(&mut rng);
        let label = format!("{name}/base-embedded-random-selectors/{index}");
        let slots = plonky2_cross_check(
            &label,
            common,
            &gate_infos,
            &wires_base,
            &constants_base,
            &pih,
        );
        let constants_k: Vec<Field64_3> = constants_base.iter().copied().map(base_to_k).collect();
        emit(
            label,
            2,
            true,
            &wires_base_k,
            &constants_k,
            &pih,
            alpha,
            alpha2,
            slots,
        );
    }

    ConfigVectors {
        name: name.to_string(),
        config: ConfigRecord {
            num_wires,
            num_constants,
            num_selectors,
            num_gate_constraints: common.num_gate_constraints,
            quotient_degree_factor: common.quotient_degree_factor,
        },
        num_gates: gate_infos.len(),
        num_wire_sets: wire_sets.len(),
        num_vectors: vectors.len(),
        gates: gate_infos.into_iter().map(GateRecord::from).collect(),
        wire_sets,
        vectors,
    }
}

fn build_fixture() -> ProductionFixture {
    ProductionFixture {
        schema: "plonky2-mle-gate-ext3-production-differential-v1".to_string(),
        version: 1,
        field_modulus: "0xffffffff00000001".to_string(),
        limb_order: ["c0".to_string(), "c1".to_string(), "c2".to_string()],
        configs: vec![
            build_config_vectors(
                "withdrawal",
                &common_withdrawal(),
                &WITHDRAWAL_GATES,
                5,
                3,
                0x0000_0BAD_C0DE_0001,
            ),
            build_config_vectors(
                "post_close_claim",
                &common_post_close_claim(),
                &POST_CLOSE_CLAIM_GATES,
                6,
                4,
                0x0000_0BAD_C0DE_0002,
            ),
        ],
    }
}

/// Also cross-check every deployed row family one at a time against plonky2 on
/// base-embedded points, at the DEPLOYED parameter sizes.
#[test]
fn deployed_gate_tables_match_plonky2_per_family() {
    for (name, common, expected) in [
        ("withdrawal", common_withdrawal(), &WITHDRAWAL_GATES[..]),
        (
            "post_close_claim",
            common_post_close_claim(),
            &POST_CLOSE_CLAIM_GATES[..],
        ),
    ] {
        let gate_infos = collect_gate_info_v2(&common).unwrap();
        assert_eq!(gate_infos, expected, "[{name}] gate table");
        let num_selectors = common.selectors_info.num_selectors();
        let mut rng = StdRng::seed_from_u64(0x5EED_0000 ^ name.len() as u64);
        for target in &gate_infos {
            for trial in 0..4 {
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
                let slots = plonky2_cross_check(
                    &format!("{name}/isolated gate_id={} trial={trial}", target.gate_id),
                    &common,
                    &gate_infos,
                    &wires,
                    &constants,
                    &pih,
                );
                for (slot, value) in slots
                    .iter()
                    .enumerate()
                    .skip(usize::from(target.num_constraints))
                {
                    assert_eq!(
                        *value,
                        Field64_3::from(0u64),
                        "[{name}] gate_id={} wrote slot {slot} beyond {} constraints",
                        target.gate_id,
                        target.num_constraints
                    );
                }
            }
        }
        println!("[{name}] plonky2 per-family cross-check OK ({} rows)", gate_infos.len());
    }
}

/// Regenerating the fixture must be deterministic and must still agree with the
/// checked-in JSON once it exists.
#[test]
fn production_vectors_are_reproducible() {
    let a = build_fixture();
    let b = build_fixture();
    assert_eq!(a, b, "fixture generation is not deterministic");
    let path = std::path::Path::new(JSON_PATH);
    if path.exists() {
        let checked_in: ProductionFixture =
            serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
        assert_eq!(checked_in, a, "checked-in production vectors are stale");
        println!("checked-in {JSON_PATH} replays exactly");
    } else {
        println!("{JSON_PATH} not present yet; run the `dump_production_vectors_json` test");
    }
}

#[test]
#[ignore = "writes the new production-vector JSON"]
fn dump_production_vectors_json() {
    let fixture = build_fixture();
    let json = serde_json::to_string(&fixture).unwrap();
    std::fs::create_dir_all("testdata").unwrap();
    std::fs::write(JSON_PATH, &json).unwrap();
    println!(
        "wrote {JSON_PATH} ({} bytes, {} configs, {} vectors total)",
        json.len(),
        fixture.configs.len(),
        fixture
            .configs
            .iter()
            .map(|c| c.vectors.len())
            .sum::<usize>()
    );
}
