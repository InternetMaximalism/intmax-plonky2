//! Opt-in generation of a degree-13 v2 proof whose circuit reproduces the
//! production SHAPE of the parent (`intmax3-zkp`) deployment profiles.
//!
//! The checked-in `v2_max_resource.json` fixture reaches the row / wire /
//! gate-constraint maxima but has one public input and five configured gate
//! rows. The deployed parent circuits (`*_mle_config.json`) have the same
//! dimensions (degree_bits 13, 135 wires, 80 routed, constituent width 160,
//! 21 WHIR variables) but a richer gate set and up to 103 public inputs.
//! Both of those drive verifier gas: every gate family is evaluated at the
//! gate terminal and the public inputs are Poseidon-hashed on chain.
//!
//! This generator builds a synthetic circuit with:
//! - `standard_recursion_config` and `degree_bits == 13`;
//! - at least one row of every gate family deployed by any parent profile
//!   (gate ids 0..=13, i.e. the union of the 103-PI `close_intent` profile
//!   and the `post_close_claim` / `withdrawal_claim` profiles which also use
//!   `ExponentiationGate` with 66 power bits) with the production parameters;
//! - exactly 103 public inputs, some duplicated and some constant-backed;
//! - arithmetic padding so the builder pads to exactly `2^13` rows.
//!
//! Regeneration is explicit (`#[ignore]`) because the proof takes minutes and
//! WHIR masking randomness changes roots and byte lengths between instances:
//!
//! ```text
//! MLE_WRITE_V2_PRODUCTION_SHAPE_FIXTURE=1 cargo test --offline --release \
//!     -p plonky2_mle --test v2_production_shape -- --ignored --nocapture
//! ```

use plonky2::gates::coset_interpolation::CosetInterpolationGate;
use plonky2::hash::poseidon::{Poseidon, PoseidonHash};
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::util::reducing::ReducingFactorTarget;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::quadratic::QuadraticExtension;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field;
use plonky2_mle::fixture_v2::{
    try_prove_and_export_mle_v2, MleVerifierV2Fixture, SOLIDITY_MLE_PROOF_ENCODING_V2,
    SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2,
};
use plonky2_mle::protocol_schema_v2::{
    COMPACT_MAGIC_V2, MAX_COMPACT_PROOF_BYTES_V2, MAX_ROW_VARIABLES_V2,
};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

/// Largest public-input count over the deployed parent profiles
/// (`close_intent_mle_config.json`).
const PRODUCTION_NUM_PUBLIC_INPUTS: usize = 103;
/// Production row dimension shared by every deployed parent profile.
const PRODUCTION_DEGREE_BITS: usize = 13;
/// Arithmetic padding target: 20 ops per `ArithmeticGate` row, so this keeps
/// the circuit between `2^12` and `2^13` rows once every other gate family
/// and the public-input hash rows are counted.
const PADDING_MULTIPLICATIONS: usize = 96_000;
/// Production `CosetInterpolationGate` parameters (`subgroup_bits 4`,
/// `max_degree 6`, 12 constraints, 2 intermediates).
const COSET_SUBGROUP_BITS: usize = 4;
const COSET_MAX_DEGREE: usize = 6;
/// Production `ExponentiationGate` power-bit count (`(135 - 2) / 2`).
const EXPONENTIATION_POWER_BITS: usize = 66;
/// Production `BaseSumGate<2>` limb count (`log_floor(p - 1, 2)`).
const BASE_SUM_LIMBS: usize = 63;
/// Production `ReducingGate` / `ReducingExtensionGate` coefficient counts.
const REDUCING_COEFFS: usize = 43;
const REDUCING_EXTENSION_COEFFS: usize = 32;
/// Production `RandomAccessGate` list size (`bits 4`).
const RANDOM_ACCESS_BITS: usize = 4;

/// Every witness-bearing virtual target of the synthetic circuit.
struct ShapeWitnessTargets {
    x: Target,
    small: Target,
    exponent: Target,
    access_index: Target,
    list: Vec<Target>,
    reducing_terms: Vec<Target>,
    coset_shift: Target,
    coset_values: Vec<ExtensionTarget<D>>,
    coset_evaluation_point: ExtensionTarget<D>,
    mds_state: [ExtensionTarget<D>; 12],
    alpha: ExtensionTarget<D>,
    reducing_ext_terms: Vec<ExtensionTarget<D>>,
    ext_a: ExtensionTarget<D>,
    ext_b: ExtensionTarget<D>,
    ext_c: ExtensionTarget<D>,
}

/// Gate families (by `GateRef::id()` prefix) that every parent profile union
/// must contain, with the production parameter string that the Plonky2 gate
/// id embeds.
const EXPECTED_GATE_ID_PREFIXES: [&str; 14] = [
    "NoopGate",
    "ConstantGate",
    "PublicInputGate",
    "ArithmeticGate { num_ops: 20 }",
    "PoseidonGate",
    "PoseidonMdsGate",
    "ArithmeticExtensionGate { num_ops: 10 }",
    "MulExtensionGate { num_ops: 13 }",
    "ExponentiationGate { num_power_bits: 66",
    "BaseSumGate { num_limbs: 63 } + Base: 2",
    "ReducingGate { num_coeffs: 43 }",
    "ReducingExtensionGate { num_coeffs: 32 }",
    "RandomAccessGate { bits: 4, num_copies: 4, num_extra_constants: 2",
    "CosetInterpolationGate { subgroup_bits: 4, degree: 6",
];

fn build_production_shape_circuit() -> (CircuitData<F, C, D>, ShapeWitnessTargets) {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let x = builder.add_virtual_target();
    let small = builder.add_virtual_target();
    let exponent = builder.add_virtual_target();
    let access_index = builder.add_virtual_target();

    // ArithmeticGate { num_ops: 20 }: the bulk padding plus the real relation.
    let mut value = x;
    for _ in 0..PADDING_MULTIPLICATIONS {
        value = builder.mul(value, x);
    }
    let chained_power = value;

    // ConstantGate: constant-backed public inputs and gadget constants.
    let constant_a = builder.constant(F::from_canonical_u64(0x1234_5678_9abc_def0));
    let constant_b = builder.constant(F::from_canonical_u64(7));

    // BaseSumGate<2> { num_limbs: 63 }: a single 63-bit decomposition row.
    let small_bits = builder.split_le(small, BASE_SUM_LIMBS);
    let low_bit = small_bits[0].target;

    // ExponentiationGate { num_power_bits: 66 }: `split_le(exponent, 66)` adds
    // two more BaseSum rows (63 + 3 limbs) and one exponentiation row.
    let power = builder.exp(x, exponent, EXPONENTIATION_POWER_BITS);

    // RandomAccessGate { bits: 4, num_copies: 4, num_extra_constants: 2 }.
    let list: Vec<Target> = (0..(1 << RANDOM_ACCESS_BITS))
        .map(|_| builder.add_virtual_target())
        .collect();
    let accessed = builder.random_access(access_index, list.clone());

    // ReducingGate { num_coeffs: 43 } over base-field terms.
    let alpha = builder.add_virtual_extension_target();
    let reducing_terms: Vec<Target> = (0..REDUCING_COEFFS)
        .map(|_| builder.add_virtual_target())
        .collect();
    let reduced_base = ReducingFactorTarget::new(alpha).reduce_base(&reducing_terms, &mut builder);

    // ReducingExtensionGate { num_coeffs: 32 } over extension terms.
    let reducing_ext_terms: Vec<ExtensionTarget<D>> = (0..REDUCING_EXTENSION_COEFFS)
        .map(|_| builder.add_virtual_extension_target())
        .collect();
    let reduced_ext = ReducingFactorTarget::new(alpha).reduce(&reducing_ext_terms, &mut builder);

    // ArithmeticExtensionGate { num_ops: 10 } (non-zero addend) and
    // MulExtensionGate { num_ops: 13 } (zero addend).
    let ext_a = builder.add_virtual_extension_target();
    let ext_b = builder.add_virtual_extension_target();
    let ext_c = builder.add_virtual_extension_target();
    let ext_mul_add = builder.mul_add_extension(ext_a, ext_b, ext_c);
    let ext_mul = builder.mul_extension(reduced_base, reduced_ext);
    let ext_sum = builder.add_extension(ext_mul_add, ext_mul);

    // PoseidonMdsGate: one explicit MDS layer over a width-12 extension state.
    let mds_state: [ExtensionTarget<D>; 12] =
        core::array::from_fn(|_| builder.add_virtual_extension_target());
    let mds_out = <F as Poseidon>::mds_layer_circuit(&mut builder, &mds_state);
    let mds_mixed = builder.add_extension(mds_out[0], mds_out[11]);

    // CosetInterpolationGate { subgroup_bits: 4, degree: 6 }: the gadget is
    // crate-private, so wire the gate row by hand (shift at wire 0, then the
    // 16 extension values, the evaluation point and the evaluation value).
    let coset_gate =
        CosetInterpolationGate::<F, D>::with_max_degree(COSET_SUBGROUP_BITS, COSET_MAX_DEGREE);
    let coset_shift = builder.add_virtual_target();
    let coset_values: Vec<ExtensionTarget<D>> = (0..(1 << COSET_SUBGROUP_BITS))
        .map(|_| builder.add_virtual_extension_target())
        .collect();
    let coset_evaluation_point = builder.add_virtual_extension_target();
    let coset_row = builder.num_gates();
    builder.connect(coset_shift, Target::wire(coset_row, 0));
    for (i, &v) in coset_values.iter().enumerate() {
        let start = 1 + i * D;
        builder.connect_extension(v, ExtensionTarget::from_range(coset_row, start..start + D));
    }
    let evaluation_point_start = 1 + coset_values.len() * D;
    builder.connect_extension(
        coset_evaluation_point,
        ExtensionTarget::from_range(
            coset_row,
            evaluation_point_start..evaluation_point_start + D,
        ),
    );
    let evaluation_value_start = evaluation_point_start + D;
    let coset_evaluation: ExtensionTarget<D> = ExtensionTarget::from_range(
        coset_row,
        evaluation_value_start..evaluation_value_start + D,
    );
    let added_row = builder.add_gate(coset_gate, vec![]);
    assert_eq!(
        added_row, coset_row,
        "coset interpolation row index drifted"
    );

    // PoseidonGate: an explicit in-circuit hash (the public-input hash adds
    // ceil(103 / 8) = 13 more Poseidon rows at build time).
    let digest = builder.hash_n_to_hash_no_pad::<PoseidonHash>(vec![
        chained_power,
        power,
        accessed,
        low_bit,
        constant_a,
        ext_sum.0[0],
        ext_sum.0[1],
        mds_mixed.0[0],
        mds_mixed.0[1],
        coset_evaluation.0[0],
        coset_evaluation.0[1],
    ]);

    // PublicInputGate: exactly 103 public inputs. The first group is
    // witness-derived, then duplicates of those, then constant-backed values.
    let mut public_inputs: Vec<Target> = vec![
        chained_power,
        power,
        accessed,
        low_bit,
        ext_sum.0[0],
        ext_sum.0[1],
        mds_mixed.0[0],
        mds_mixed.0[1],
        coset_evaluation.0[0],
        coset_evaluation.0[1],
        reduced_base.0[0],
        reduced_base.0[1],
        reduced_ext.0[0],
        reduced_ext.0[1],
    ];
    public_inputs.extend(digest.elements);
    public_inputs.extend(mds_out.iter().take(12).map(|t| t.0[0]));
    // Duplicated public inputs (the parent profiles re-export several targets).
    public_inputs.extend_from_slice(&[chained_power, power, accessed, digest.elements[0]]);
    public_inputs.extend(mds_out.iter().map(|t| t.0[1]));
    // Constant-backed public inputs.
    public_inputs.push(constant_a);
    public_inputs.push(constant_b);
    while public_inputs.len() < PRODUCTION_NUM_PUBLIC_INPUTS {
        let k = public_inputs.len() as u64;
        public_inputs.push(builder.constant(F::from_canonical_u64(1_000 + k)));
    }
    public_inputs.truncate(PRODUCTION_NUM_PUBLIC_INPUTS);
    assert_eq!(public_inputs.len(), PRODUCTION_NUM_PUBLIC_INPUTS);
    builder.register_public_inputs(&public_inputs);

    let targets = ShapeWitnessTargets {
        x,
        small,
        exponent,
        access_index,
        list,
        reducing_terms,
        coset_shift,
        coset_values,
        coset_evaluation_point,
        mds_state,
        alpha,
        reducing_ext_terms,
        ext_a,
        ext_b,
        ext_c,
    };
    (builder.build::<C>(), targets)
}

fn production_shape_witness(targets: &ShapeWitnessTargets) -> PartialWitness<F> {
    let mut witness = PartialWitness::new();
    let f = F::from_canonical_u64;
    let ff = |a: u64, b: u64| QuadraticExtension::<F>([f(a), f(b)]);
    witness.set_target(targets.x, f(3)).unwrap();
    witness
        .set_target(targets.small, f(0x7fff_ffff_ffff_fff1))
        .unwrap();
    witness
        .set_target(targets.exponent, f(0xdead_beef))
        .unwrap();
    witness.set_target(targets.access_index, f(5)).unwrap();
    for (i, &t) in targets.list.iter().enumerate() {
        witness.set_target(t, f(100 + i as u64)).unwrap();
    }
    for (i, &t) in targets.reducing_terms.iter().enumerate() {
        witness.set_target(t, f(0x1000 + i as u64)).unwrap();
    }
    witness.set_target(targets.coset_shift, f(7)).unwrap();
    for (i, &t) in targets.coset_values.iter().enumerate() {
        witness
            .set_extension_target(t, ff(0x2000 + i as u64, 0x3000 + i as u64))
            .unwrap();
    }
    witness
        .set_extension_target(targets.coset_evaluation_point, ff(0x4242, 0x4343))
        .unwrap();
    for (i, &t) in targets.mds_state.iter().enumerate() {
        witness
            .set_extension_target(t, ff(0x5000 + i as u64, 0x6000 + i as u64))
            .unwrap();
    }
    witness
        .set_extension_target(targets.alpha, ff(0x7777, 0x8888))
        .unwrap();
    for (i, &t) in targets.reducing_ext_terms.iter().enumerate() {
        witness
            .set_extension_target(t, ff(0x9000 + i as u64, 0xa000 + i as u64))
            .unwrap();
    }
    witness
        .set_extension_target(targets.ext_a, ff(11, 12))
        .unwrap();
    witness
        .set_extension_target(targets.ext_b, ff(13, 14))
        .unwrap();
    witness
        .set_extension_target(targets.ext_c, ff(15, 16))
        .unwrap();
    witness
}

#[test]
#[ignore = "expensive opt-in degree-13 production-shape proof and fixture generation"]
fn generate_production_shape_fixture() {
    let (circuit, targets) = build_production_shape_circuit();
    assert_eq!(
        circuit.common.degree_bits(),
        PRODUCTION_DEGREE_BITS,
        "production-shape fixture must have the deployed row dimension"
    );
    assert_eq!(circuit.common.degree_bits(), MAX_ROW_VARIABLES_V2);
    assert_eq!(
        circuit.common.num_public_inputs,
        PRODUCTION_NUM_PUBLIC_INPUTS
    );

    let gate_ids: Vec<String> = circuit.common.gates.iter().map(|g| g.0.id()).collect();
    println!("plonky2 gate ids ({}):", gate_ids.len());
    for id in &gate_ids {
        println!("  {id}");
    }
    for expected in EXPECTED_GATE_ID_PREFIXES {
        assert!(
            gate_ids.iter().any(|id| id.starts_with(expected)),
            "circuit is missing the production gate family `{expected}`"
        );
    }

    let witness = production_shape_witness(&targets);
    let mut timing = TimingTree::default();
    let exported = try_prove_and_export_mle_v2(&circuit, witness, &mut timing)
        .expect("production-shape v2 proof must verify and export");
    let fixture = &exported.fixture;
    let stats = &fixture.stats;
    let vk = &fixture.verification_key;

    println!("degree_bits={}", circuit.common.degree_bits());
    println!("num_public_inputs={}", circuit.common.num_public_inputs);
    println!("num_constants={}", circuit.common.num_constants);
    println!(
        "num_routed_wires={}",
        circuit.common.config.num_routed_wires
    );
    println!("num_wires={}", circuit.common.config.num_wires);
    println!("num_gates={}", circuit.common.gates.len());
    println!("num_selectors={}", vk.num_selectors);
    println!("constituent_width={}", vk.constituent_width);
    println!(
        "num_gate_constraints={}",
        circuit.common.num_gate_constraints
    );
    println!(
        "quotient_degree_factor={}",
        circuit.common.quotient_degree_factor
    );
    println!("vk gates ({}):", vk.gates.len());
    for gate in &vk.gates {
        println!(
            "  gate_id={} selector={} group={}..{} row={} constraints={} num_or_consts={} param2={} param3={}",
            gate.gate_id,
            gate.selector_index,
            gate.group_start,
            gate.group_end,
            gate.gate_row_index,
            gate.num_constraints,
            gate.num_or_consts,
            gate.param2,
            gate.param3
        );
    }
    let mut vk_gate_ids: Vec<u8> = vk.gates.iter().map(|g| g.gate_id).collect();
    vk_gate_ids.sort_unstable();
    assert_eq!(
        vk_gate_ids,
        (0u8..=13).collect::<Vec<_>>(),
        "VK gate metadata must cover the union of deployed gate ids 0..=13"
    );
    assert_eq!(fixture.verification_config.circuit.num_public_inputs, 103);
    println!("whir_transcript_bytes={}", stats.whir_transcript_bytes);
    println!("whir_hint_bytes={}", stats.whir_hint_bytes);
    println!("compact_bytes={}", stats.compact_bytes);
    println!("solidity_abi_bytes={}", stats.solidity_abi_bytes);
    println!(
        "solidity_abi_verification_config_bytes={}",
        stats.solidity_abi_verification_config_bytes
    );
    println!(
        "max_compact_bytes={}",
        fixture.size_upper_bound.max_compact_bytes
    );
    assert!(
        stats.compact_bytes <= MAX_COMPACT_PROOF_BYTES_V2,
        "a production-shape proof exceeded the two-blob compact DA cap"
    );

    if std::env::var("MLE_WRITE_V2_PRODUCTION_SHAPE_FIXTURE").as_deref() == Ok("1") {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("contracts/test/fixtures/v2_production_shape.json");
        let mut json = serde_json::to_string_pretty(fixture).expect("serialize fixture");
        json.push('\n');
        std::fs::write(&path, json).expect("write explicit v2 production-shape fixture");
        println!("wrote {}", path.display());
    }
}

#[test]
fn checked_in_production_shape_fixture_has_current_schema_and_bounds() {
    let text = include_str!("../contracts/test/fixtures/v2_production_shape.json");
    let fixture = MleVerifierV2Fixture::from_canonical_json(text)
        .expect("checked-in production-shape fixture uses the current strict schema");
    let stats = &fixture.stats;
    let vk = &fixture.verification_key;
    let circuit = &fixture.verification_config.circuit;

    println!("production-shape compact_bytes={}", stats.compact_bytes);
    println!("production-shape whir_hint_bytes={}", stats.whir_hint_bytes);
    println!(
        "production-shape whir_transcript_bytes={}",
        stats.whir_transcript_bytes
    );
    println!(
        "production-shape solidity_abi_bytes={}",
        stats.solidity_abi_bytes
    );

    // Production dimensions shared by every deployed parent profile.
    assert_eq!(circuit.degree_bits, PRODUCTION_DEGREE_BITS);
    assert_eq!(circuit.num_public_inputs, PRODUCTION_NUM_PUBLIC_INPUTS);
    assert_eq!(circuit.num_routed_wires, 80);
    assert_eq!(circuit.num_wires, 135);
    assert_eq!(circuit.num_gate_constraints, 123);
    assert_eq!(circuit.quotient_degree_factor, 8);
    assert_eq!(vk.constituent_width, 160);
    assert_eq!(vk.num_constants, circuit.num_constants);
    assert_eq!(vk.num_selectors, circuit.num_selectors);
    assert_eq!(vk.num_constants, vk.num_selectors + 2);

    // Union of the deployed gate families with the production parameters.
    let mut gate_ids: Vec<u8> = vk.gates.iter().map(|g| g.gate_id).collect();
    gate_ids.sort_unstable();
    assert_eq!(gate_ids, (0u8..=13).collect::<Vec<_>>());
    let find = |id: u8| vk.gates.iter().find(|g| g.gate_id == id).unwrap();
    let expect = |id: u8, constraints: u16, n: u16, p2: u16, p3: u16| {
        let g = find(id);
        assert_eq!(
            (g.num_constraints, g.num_or_consts, g.param2, g.param3),
            (constraints, n, p2, p3),
            "gate id {id} parameters"
        );
    };
    expect(0, 0, 0, 0, 0);
    expect(1, 2, 2, 0, 0);
    expect(2, 4, 0, 0, 0);
    expect(3, 20, 20, 0, 0);
    expect(4, 123, 0, 0, 0);
    expect(5, 24, 0, 0, 0);
    expect(6, 20, 10, 0, 0);
    expect(7, 26, 13, 0, 0);
    expect(8, 67, 66, 0, 0);
    expect(9, 64, 63, 2, 0);
    expect(10, 86, 43, 0, 0);
    expect(11, 64, 32, 0, 0);
    expect(12, 26, 4, 4, 2);
    expect(13, 12, 4, 6, 0);

    // Public-input wire map: 103 entries of (row u16, column u8).
    let wire_map = fixture
        .verification_config
        .public_input_wire_map
        .trim_start_matches("0x");
    assert_eq!(wire_map.len(), PRODUCTION_NUM_PUBLIC_INPUTS * 3 * 2);

    assert_eq!(
        stats.solidity_abi_verification_config_bytes,
        fixture.solidity_abi_verification_config.byte_length
    );
    assert_eq!(
        fixture.pinned_verifier.verification_config_digest,
        fixture.solidity_abi_verification_config.keccak256
    );
    fixture
        .solidity_abi_proof
        .decode_and_validate(SOLIDITY_MLE_PROOF_ENCODING_V2)
        .expect("integral production-shape proof ABI bytes");
    fixture
        .solidity_abi_verification_config
        .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)
        .expect("integral production-shape config ABI bytes");
    fixture
        .compact_proof
        .decode_and_validate(std::str::from_utf8(&COMPACT_MAGIC_V2).unwrap())
        .expect("integral production-shape compact bytes");
    assert_eq!(
        fixture.proof.public_inputs.len(),
        PRODUCTION_NUM_PUBLIC_INPUTS
    );
    assert!(fixture.size_upper_bound.fits_whir_blob_caps);
    assert!(fixture.size_upper_bound.fits_compact_cap);
    assert!(stats.compact_bytes <= fixture.size_upper_bound.max_compact_bytes);
    assert!(fixture.size_upper_bound.max_compact_bytes <= MAX_COMPACT_PROOF_BYTES_V2);
    assert!(stats.whir_hint_bytes <= fixture.size_upper_bound.max_whir_hint_bytes);
    assert!(stats.whir_transcript_bytes <= fixture.size_upper_bound.max_whir_transcript_bytes);
}
