//! Opt-in generation of a real degree-13 v2 proof for DA and gas admission.
//!
//! The ordinary test suite does not rewrite or re-prove this expensive
//! fixture. Regeneration is explicit because WHIR masking randomness changes
//! roots, query collisions, and byte lengths between proof instances.

use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::util::timing::TimingTree;
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

fn build_max_resource_circuit() -> (CircuitData<F, C, D>, plonky2::iop::target::Target) {
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let x = builder.add_virtual_target();
    let mut value = x;
    for _ in 0..100_000 {
        value = builder.mul(value, x);
    }
    builder.register_public_input(value);
    (builder.build::<C>(), x)
}

#[test]
#[ignore = "expensive opt-in degree-13 proof and fixture generation"]
fn generate_real_max_row_profile_fixture() {
    let (circuit, x) = build_max_resource_circuit();
    assert_eq!(
        circuit.common.degree_bits(),
        MAX_ROW_VARIABLES_V2,
        "resource fixture must exercise the reviewed maximum row dimension"
    );

    let mut witness = PartialWitness::new();
    witness
        .set_target(x, F::from_canonical_u64(2))
        .expect("set resource-fixture witness");
    let mut timing = TimingTree::default();
    let exported = try_prove_and_export_mle_v2(&circuit, witness, &mut timing)
        .expect("real maximum-row v2 proof must verify and export");
    let stats = &exported.fixture.stats;
    println!("degree_bits={}", circuit.common.degree_bits());
    println!("num_public_inputs={}", circuit.common.num_public_inputs);
    println!("num_constants={}", circuit.common.num_constants);
    println!(
        "num_routed_wires={}",
        circuit.common.config.num_routed_wires
    );
    println!("num_wires={}", circuit.common.config.num_wires);
    println!("num_gates={}", circuit.common.gates.len());
    println!(
        "num_gate_constraints={}",
        circuit.common.num_gate_constraints
    );
    println!(
        "quotient_degree_factor={}",
        circuit.common.quotient_degree_factor
    );
    println!("whir_transcript_bytes={}", stats.whir_transcript_bytes);
    println!("whir_hint_bytes={}", stats.whir_hint_bytes);
    println!("compact_bytes={}", stats.compact_bytes);
    println!("solidity_abi_bytes={}", stats.solidity_abi_bytes);
    assert!(
        stats.compact_bytes <= MAX_COMPACT_PROOF_BYTES_V2,
        "a real maximum-row proof exceeded the two-blob compact DA cap"
    );

    if std::env::var("MLE_WRITE_V2_RESOURCE_FIXTURE").as_deref() == Ok("1") {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("contracts/test/fixtures/v2_max_resource.json");
        let mut json = serde_json::to_string_pretty(&exported.fixture).expect("serialize fixture");
        json.push('\n');
        std::fs::write(&path, json).expect("write explicit v2 resource fixture");
        println!("wrote {}", path.display());
    }
}

#[test]
fn checked_in_max_resource_fixture_has_current_schema_and_bounds() {
    let text = include_str!("../contracts/test/fixtures/v2_max_resource.json");
    let fixture = MleVerifierV2Fixture::from_canonical_json(text)
        .expect("checked-in max-resource fixture uses the current strict schema");
    assert_eq!(fixture.stats.solidity_abi_bytes, 255_584);
    assert_eq!(fixture.stats.compact_bytes, 195_012);
    assert_eq!(fixture.stats.whir_transcript_bytes, 2_032);
    assert_eq!(fixture.stats.whir_hint_bytes, 173_784);
    assert_eq!(
        fixture.stats.solidity_abi_verification_config_bytes,
        fixture.solidity_abi_verification_config.byte_length
    );
    assert_eq!(
        fixture.solidity_abi_proof.keccak256,
        "0xb63f08551e3b123836f1123097f2589fc4fd6525fda48406088e099d86e8429b"
    );
    assert_eq!(
        fixture.compact_proof.keccak256,
        "0xf1094bb2cc33e2c7368d9bd12e3a8c08b81c8b9e8ce0c5b653887862e16ced0f"
    );
    assert_eq!(fixture.solidity_abi_verification_config.byte_length, 7_456);
    assert_eq!(
        fixture.solidity_abi_verification_config.keccak256,
        "0xdaa7db23fdd56ae27f0d67703c23d005340af03e11903a2262845eb7e7856119"
    );
    assert_eq!(
        fixture.pinned_verifier.verification_config_digest,
        fixture.solidity_abi_verification_config.keccak256
    );
    fixture
        .solidity_abi_proof
        .decode_and_validate(SOLIDITY_MLE_PROOF_ENCODING_V2)
        .expect("integral max-resource proof ABI bytes");
    fixture
        .solidity_abi_verification_config
        .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)
        .expect("integral max-resource config ABI bytes");
    fixture
        .compact_proof
        .decode_and_validate(std::str::from_utf8(&COMPACT_MAGIC_V2).unwrap())
        .expect("integral max-resource compact bytes");
    assert_eq!(fixture.size_upper_bound.fixed_compact_bytes, 19_196);
    assert_eq!(fixture.size_upper_bound.max_whir_transcript_bytes, 2_032);
    assert_eq!(fixture.size_upper_bound.max_whir_hint_bytes, 180_408);
    assert_eq!(fixture.size_upper_bound.max_compact_bytes, 201_636);
    assert_eq!(fixture.size_upper_bound.max_solidity_abi_bytes, 262_208);
    assert!(fixture.size_upper_bound.fits_whir_blob_caps);
    assert!(fixture.size_upper_bound.fits_compact_cap);
    assert!(fixture.stats.compact_bytes <= fixture.size_upper_bound.max_compact_bytes);
    assert!(fixture.size_upper_bound.max_compact_bytes <= MAX_COMPACT_PROOF_BYTES_V2);
}

#[test]
fn full_fixture_parser_rejects_relabelled_top_level_schema() {
    let mut value: serde_json::Value = serde_json::from_str(include_str!(
        "../contracts/test/fixtures/v2_max_resource.json"
    ))
    .expect("checked-in max-resource JSON");
    value["schema"] = serde_json::Value::String("plonky2-mle-v2-solidity".to_string());
    let mut relabelled =
        serde_json::to_string_pretty(&value).expect("serialize relabelled fixture");
    relabelled.push('\n');
    assert!(
        MleVerifierV2Fixture::from_canonical_json(&relabelled).is_err(),
        "a retired or arbitrary top-level schema must fail before full/config projection"
    );
}
