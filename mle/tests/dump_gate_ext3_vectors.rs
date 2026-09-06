//! Deterministic Rust source-of-truth vectors for the Solidity Fp3 gate evaluator.

use std::collections::BTreeSet;

use ark_ff::PrimeField;
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
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field;
use plonky2_mle::gate_ext3::{evaluate_gate_aggregation_ext3, evaluate_gate_constraints_ext3};
use plonky2_mle::proof_v2::GateInfoV2;
use plonky2_mle::vk_v2::{circuit_config_digest_v2, collect_gate_info_v2};
use serde::{Deserialize, Serialize};
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;
const UNUSED_SELECTOR: u64 = u32::MAX as u64;
type ExtRecord = [String; 3];

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
    fn from(value: GateInfoV2) -> Self {
        Self {
            gate_id: value.gate_id,
            selector_index: value.selector_index,
            group_start: value.group_start,
            group_end: value.group_end,
            gate_row_index: value.gate_row_index,
            num_constraints: value.num_constraints,
            num_or_consts: value.num_or_consts,
            param2: value.param2,
            param3: value.param3,
        }
    }
}

impl From<GateRecord> for GateInfoV2 {
    fn from(value: GateRecord) -> Self {
        Self {
            gate_id: value.gate_id,
            selector_index: value.selector_index,
            group_start: value.group_start,
            group_end: value.group_end,
            gate_row_index: value.gate_row_index,
            num_constraints: value.num_constraints,
            num_or_consts: value.num_or_consts,
            param2: value.param2,
            param3: value.param3,
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
struct GateVector {
    target_gate_id: u8,
    constants: Vec<ExtRecord>,
    expected_filtered_constraints: Vec<ExtRecord>,
    expected_aggregation: ExtRecord,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct MixedSelectorVector {
    constants: Vec<ExtRecord>,
    expected_filtered_constraints: Vec<ExtRecord>,
    expected_aggregation: ExtRecord,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct GateExt3Fixture {
    schema: String,
    version: u64,
    field_modulus: String,
    limb_order: [String; 3],
    config: ConfigRecord,
    gates: Vec<GateRecord>,
    wires: Vec<ExtRecord>,
    public_inputs_hash: [String; 4],
    alpha: ExtRecord,
    vectors: Vec<GateVector>,
    mixed_selector_vector: MixedSelectorVector,
}

fn all_supported_gate_common_data() -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let random_access = RandomAccessGate::<F, D>::new_from_config(&config, 2);
    let random_constants = random_access.num_extra_constants;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    builder.add_gate(NoopGate, vec![]);
    builder.add_gate(ConstantGate::new(2), vec![F::from_canonical_u64(3)]);
    builder.add_gate(PublicInputGate, vec![]);
    builder.add_gate(
        ArithmeticGate { num_ops: 2 },
        vec![F::from_canonical_u64(5), F::from_canonical_u64(7)],
    );
    builder.add_gate(PoseidonGate::<F, D>::new(), vec![]);
    builder.add_gate(PoseidonMdsGate::<F, D>::new(), vec![]);
    builder.add_gate(
        ArithmeticExtensionGate::<D> { num_ops: 2 },
        vec![F::from_canonical_u64(11), F::from_canonical_u64(13)],
    );
    builder.add_gate(
        MulExtensionGate::<D> { num_ops: 2 },
        vec![F::from_canonical_u64(17)],
    );
    builder.add_gate(ExponentiationGate::<F, D>::new(3), vec![]);
    builder.add_gate(BaseSumGate::<2>::new(4), vec![]);
    builder.add_gate(ReducingGate::<D>::new(3), vec![]);
    builder.add_gate(ReducingExtensionGate::<D>::new(3), vec![]);
    builder.add_gate(
        random_access,
        vec![F::from_canonical_u64(19); random_constants],
    );
    builder.add_gate(
        CosetInterpolationGate::<F, D>::with_max_degree(4, 4),
        vec![],
    );
    builder.build::<C>().common
}

fn ext(seed: u64) -> Field64_3 {
    Field64_3::new(
        ArkGoldilocks::from(seed),
        ArkGoldilocks::from(3 * seed + 1),
        ArkGoldilocks::from(5 * seed + 2),
    )
}

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

fn decode_limb(value: &str) -> u64 {
    let digits = value.strip_prefix("0x").expect("limb must have 0x prefix");
    assert_eq!(digits.len(), 16, "limb must be fixed-width u64 hex");
    u64::from_str_radix(digits, 16).expect("limb must be lowercase hex")
}

fn decode_ext(value: &ExtRecord) -> Field64_3 {
    Field64_3::new(
        ArkGoldilocks::from(decode_limb(&value[0])),
        ArkGoldilocks::from(decode_limb(&value[1])),
        ArkGoldilocks::from(decode_limb(&value[2])),
    )
}

fn build_fixture() -> GateExt3Fixture {
    let common = all_supported_gate_common_data();
    let gate_infos = collect_gate_info_v2(&common).unwrap();
    assert_eq!(
        gate_infos
            .iter()
            .map(|gate| gate.gate_id)
            .collect::<BTreeSet<_>>(),
        (0u8..=13).collect()
    );
    let wires = (0..common.config.num_wires)
        .map(|i| ext(i as u64 + 2))
        .collect::<Vec<_>>();
    let public_inputs_hash = HashOut {
        elements: [
            F::from_canonical_u64(131),
            F::from_canonical_u64(137),
            F::from_canonical_u64(139),
            F::from_canonical_u64(149),
        ],
    };
    let alpha = ext(17);
    let mut vectors = Vec::with_capacity(gate_infos.len());
    for target in &gate_infos {
        let mut constants = (0..common.num_constants)
            .map(|i| {
                let seed = i as u64 + 211;
                Field64_3::new(
                    ArkGoldilocks::from(seed),
                    ArkGoldilocks::from(7 * seed + 1),
                    ArkGoldilocks::from(11 * seed + 3),
                )
            })
            .collect::<Vec<_>>();
        for selector in constants
            .iter_mut()
            .take(common.selectors_info.num_selectors())
        {
            *selector = Field64_3::from(UNUSED_SELECTOR);
        }
        constants[usize::from(target.selector_index)] =
            Field64_3::from(u64::from(target.gate_row_index));
        let constraints = evaluate_gate_constraints_ext3(
            &common,
            &gate_infos,
            &wires,
            &constants,
            &public_inputs_hash,
        )
        .unwrap();
        let aggregation = evaluate_gate_aggregation_ext3(
            &common,
            &gate_infos,
            &wires,
            &constants,
            &public_inputs_hash,
            alpha,
        )
        .unwrap();
        vectors.push(GateVector {
            target_gate_id: target.gate_id,
            constants: constants.into_iter().map(encode_ext).collect(),
            expected_filtered_constraints: constraints.into_iter().map(encode_ext).collect(),
            expected_aggregation: encode_ext(aggregation),
        });
    }

    // Unlike the isolated-family cases above, every selector is a non-base
    // Ext3 value here. No filter can vanish against a base row/UNUSED value,
    // so this exercises simultaneous contributions and the full Ext3 filter.
    let mixed_constants = (0..common.num_constants)
        .map(|i| {
            let seed = i as u64 + 211;
            Field64_3::new(
                ArkGoldilocks::from(seed),
                ArkGoldilocks::from(7 * seed + 1),
                ArkGoldilocks::from(11 * seed + 3),
            )
        })
        .collect::<Vec<_>>();
    let mixed_constraints = evaluate_gate_constraints_ext3(
        &common,
        &gate_infos,
        &wires,
        &mixed_constants,
        &public_inputs_hash,
    )
    .unwrap();
    let mixed_aggregation = evaluate_gate_aggregation_ext3(
        &common,
        &gate_infos,
        &wires,
        &mixed_constants,
        &public_inputs_hash,
        alpha,
    )
    .unwrap();

    GateExt3Fixture {
        schema: "plonky2-mle-gate-ext3-differential-v1".to_string(),
        version: 1,
        field_modulus: "0xffffffff00000001".to_string(),
        limb_order: ["c0".to_string(), "c1".to_string(), "c2".to_string()],
        config: ConfigRecord {
            num_wires: common.config.num_wires,
            num_constants: common.num_constants,
            num_selectors: common.selectors_info.num_selectors(),
            num_gate_constraints: common.num_gate_constraints,
            quotient_degree_factor: common.quotient_degree_factor,
        },
        gates: gate_infos.into_iter().map(GateRecord::from).collect(),
        wires: wires.into_iter().map(encode_ext).collect(),
        public_inputs_hash: [
            encode_limb(131),
            encode_limb(137),
            encode_limb(139),
            encode_limb(149),
        ],
        alpha: encode_ext(alpha),
        vectors,
        mixed_selector_vector: MixedSelectorVector {
            constants: mixed_constants.into_iter().map(encode_ext).collect(),
            expected_filtered_constraints: mixed_constraints.into_iter().map(encode_ext).collect(),
            expected_aggregation: encode_ext(mixed_aggregation),
        },
    }
}

#[test]
fn checked_in_gate_ext3_vectors_replay() {
    let checked_in: GateExt3Fixture =
        serde_json::from_str(include_str!("../testdata/gate_ext3_vectors.json")).unwrap();
    assert_eq!(checked_in, build_fixture());

    let common = all_supported_gate_common_data();
    let gates = checked_in
        .gates
        .clone()
        .into_iter()
        .map(GateInfoV2::from)
        .collect::<Vec<_>>();
    let wires = checked_in.wires.iter().map(decode_ext).collect::<Vec<_>>();
    let public_inputs_hash = HashOut {
        elements: checked_in
            .public_inputs_hash
            .each_ref()
            .map(|value| F::from_canonical_u64(decode_limb(value))),
    };
    let alpha = decode_ext(&checked_in.alpha);
    for case in &checked_in.vectors {
        let constants = case.constants.iter().map(decode_ext).collect::<Vec<_>>();
        let constraints = evaluate_gate_constraints_ext3(
            &common,
            &gates,
            &wires,
            &constants,
            &public_inputs_hash,
        )
        .unwrap();
        assert_eq!(
            constraints,
            case.expected_filtered_constraints
                .iter()
                .map(decode_ext)
                .collect::<Vec<_>>(),
            "filtered slots changed for gate {}",
            case.target_gate_id
        );
        let aggregation = evaluate_gate_aggregation_ext3(
            &common,
            &gates,
            &wires,
            &constants,
            &public_inputs_hash,
            alpha,
        )
        .unwrap();
        assert_eq!(aggregation, decode_ext(&case.expected_aggregation));
    }
}

#[test]
#[ignore = "prints the canonical JSON for an intentional snapshot update"]
fn dump_gate_ext3_vectors_json() {
    let json = serde_json::to_string_pretty(&build_fixture()).unwrap();
    let chunk = std::env::var("GATE_VECTOR_CHUNK").ok().map(|value| {
        value
            .parse::<usize>()
            .expect("GATE_VECTOR_CHUNK must be a usize")
    });
    if let Some(chunk) = chunk {
        // The fixture is ASCII-only. Keep each captured command comfortably below
        // output truncation limits while preserving one canonical pretty snapshot.
        const CHUNK_BYTES: usize = 16_000;
        let chunks = json.len().div_ceil(CHUNK_BYTES);
        assert!(
            chunk < chunks,
            "requested chunk {chunk} but there are {chunks}"
        );
        let start = chunk * CHUNK_BYTES;
        let end = (start + CHUNK_BYTES).min(json.len());
        println!("BEGIN_GATE_VECTOR_CHUNK {chunk} {chunks} {}", json.len());
        print!("{}", &json[start..end]);
        println!("\nEND_GATE_VECTOR_CHUNK");
    } else {
        println!("{json}");
    }
}

#[test]
fn circuit_config_v2_digest_golden() {
    let common = all_supported_gate_common_data();
    let gates = collect_gate_info_v2(&common).unwrap();
    let circuit_digest = [151, 157, 163, 167].map(F::from_canonical_u64);
    let subgroup_gen_powers = (0..common.degree_bits())
        .map(|i| F::from_canonical_usize(173 + i))
        .collect::<Vec<_>>();
    let digest =
        circuit_config_digest_v2(&common, &circuit_digest, &subgroup_gen_powers, &gates, &[])
            .unwrap();
    let encoded = digest
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert_eq!(
        encoded,
        "74c04994e9e6178ca36d61e920679ad2f0055744fe05c33a42db82d7790dcf9b"
    );
    assert_eq!(common.degree_bits(), 4);
    assert_eq!(common.k_is.len(), 80);
}
