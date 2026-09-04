//! Production MLE/WHIR v2 export API round-trip and drift tests.

use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::util::timing::TimingTree;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field;
use plonky2_mle::compact_v2::CompactV2Shape;
use plonky2_mle::fixture_v2::{
    derive_whir_deployment_profile_for_packed_num_vars_v2, proof_encoding_size_upper_bound_v2,
    solidity_abi_encode_verification_config_v2, solidity_abi_encode_whir_params_v2,
    try_export_mle_v2_config_fixture, try_prove_and_export_mle_v2, EncodedProofV2Fixture,
    MleVerifierV2ConfigFixture, MleVerifierV2Fixture, MLE_VERIFIER_CONFIG_FIXTURE_SCHEMA_V2,
    SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2,
};
use plonky2_mle::protocol_schema_v2::{
    CIRCUIT_DIGEST_LENGTH_V2, COMPACT_LAYOUT_HASH_V2, COMPACT_MAGIC_V2, MAX_COMPACT_PROOF_BYTES_V2,
    MAX_WHIR_HINT_BYTES_V2, MAX_WHIR_NARG_BYTES_V2, MLE_PROOF_ABI_FIELDS_V2,
    MLE_PROOF_ABI_FIELD_COUNT_V2, MLE_PROOF_ABI_SIGNATURE_V2, MLE_PROOF_LAYOUT_HASH_V2,
    MLE_PROTOCOL_VERSION_CURRENT, SCHEMA_VERSION_CURRENT, WHIR_POW_BITS_V2,
};
use serde_json::Value;
use sha3::{Digest, Keccak256};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

fn hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::from("0x");
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").unwrap();
    }
    out
}

fn decode_hex(value: &str) -> Vec<u8> {
    let value = value.strip_prefix("0x").unwrap();
    (0..value.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(&value[index..index + 2], 16).unwrap())
        .collect()
}

fn small_mul() -> (CircuitData<F, C, D>, PartialWitness<F>) {
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let x = builder.add_virtual_target();
    let square = builder.mul(x, x);
    builder.register_public_input(square);
    let data = builder.build::<C>();
    let mut witness = PartialWitness::new();
    witness.set_target(x, F::from_canonical_u64(9)).unwrap();
    (data, witness)
}

fn exported() -> (CircuitData<F, C, D>, MleVerifierV2Fixture) {
    let (data, witness) = small_mul();
    let proved = try_prove_and_export_mle_v2(&data, witness, &mut TimingTree::default()).unwrap();
    (data, proved.fixture)
}

#[test]
fn production_fixture_round_trips_all_native_and_wire_views() {
    let (data, fixture) = exported();
    let json = fixture.to_canonical_json().unwrap();
    let reparsed = MleVerifierV2Fixture::from_canonical_json(&json).unwrap();
    assert_eq!(fixture, reparsed);
    reparsed.validate_against_common(&data.common).unwrap();

    assert_eq!(fixture.schema_version, SCHEMA_VERSION_CURRENT);
    assert_eq!(fixture.proof_abi_signature, MLE_PROOF_ABI_SIGNATURE_V2);
    assert_eq!(
        fixture.proof_layout_hash,
        hex_bytes(&MLE_PROOF_LAYOUT_HASH_V2)
    );
    assert_eq!(fixture.verification_key.circuit_digest.len(), 4);
    assert_eq!(fixture.verification_key.whir_protocol_id.len(), 2 + 2 * 64);
    assert_eq!(fixture.verification_key.whir_session_id.len(), 2 + 2 * 32);
    assert!(fixture.verification_config.whir.evaluation_point.is_empty());
    assert!(fixture
        .verification_config
        .whir
        .evaluation_point2
        .is_empty());
    assert!(fixture
        .verification_config
        .whir
        .additional_evaluation_points
        .is_empty());
    assert_eq!(
        fixture.stats.compact_bytes,
        fixture.compact_proof.byte_length
    );
    assert_eq!(
        fixture.stats.solidity_abi_bytes,
        fixture.solidity_abi_proof.byte_length
    );
    assert_eq!(
        fixture.stats.solidity_abi_verification_config_bytes,
        fixture.solidity_abi_verification_config.byte_length
    );
    assert_eq!(
        fixture.pinned_verifier.verification_config_digest,
        fixture.solidity_abi_verification_config.keccak256
    );
    assert_eq!(fixture.solidity_abi_verification_config.byte_length, 5664);
    assert_eq!(
        fixture.solidity_abi_verification_config.keccak256,
        "0xdeb7b1c55030dc60b29c93c02880e2e07dde6aefef3bb50f17f84290d44a15a1"
    );
    assert!(fixture.stats.solidity_abi_bytes > fixture.stats.compact_bytes);
    eprintln!(
        "small-mul-v2 config-abi={} config-keccak={}",
        fixture.solidity_abi_verification_config.byte_length,
        fixture.solidity_abi_verification_config.keccak256,
    );

    let proof_json = serde_json::to_value(&fixture.proof).unwrap();
    let proof_object = proof_json.as_object().unwrap();
    assert_eq!(proof_object.len(), MLE_PROOF_ABI_FIELD_COUNT_V2);
    for (_, json_name, _, _) in MLE_PROOF_ABI_FIELDS_V2 {
        assert!(proof_object.contains_key(json_name), "missing {json_name}");
    }

    // Configuration export requires no witness/proof and must stay exactly in
    // lockstep with the deterministic portion of the full proof artifact.
    let config = try_export_mle_v2_config_fixture(&data).unwrap();
    let second_config = try_export_mle_v2_config_fixture(&data).unwrap();
    assert_eq!(config, second_config);
    assert_eq!(fixture.config_fixture(), config);
    config.validate_against_circuit(&data).unwrap();

    let config_json = config.to_canonical_json().unwrap();
    assert_eq!(
        MleVerifierV2ConfigFixture::from_canonical_json(&config_json).unwrap(),
        config
    );
    let config_object = serde_json::from_str::<Value>(&config_json)
        .unwrap()
        .as_object()
        .unwrap()
        .clone();
    for proof_only_key in ["proof", "solidityAbiProof", "compactProof", "stats"] {
        assert!(
            !config_object.contains_key(proof_only_key),
            "config-only fixture unexpectedly contains {proof_only_key}"
        );
    }
    assert_eq!(config.schema, MLE_VERIFIER_CONFIG_FIXTURE_SCHEMA_V2);
    assert_eq!(config.schema_version, SCHEMA_VERSION_CURRENT);
    assert_eq!(config.protocol_version, MLE_PROTOCOL_VERSION_CURRENT);
    assert_eq!(
        config.compact_layout_hash,
        hex_bytes(&COMPACT_LAYOUT_HASH_V2)
    );
    assert_eq!(config.compact_proof_encoding.as_bytes(), &COMPACT_MAGIC_V2);
    assert_eq!(config.whir_pow_bits, WHIR_POW_BITS_V2);
    assert_eq!(
        config.pinned_verifier.verification_config_digest,
        config.solidity_abi_verification_config.keccak256
    );
    assert!(config.size_upper_bound.fits_whir_blob_caps);
    assert!(config.size_upper_bound.fits_compact_cap);
    assert_eq!(
        config.compact_shape.max_encoded_bytes,
        MAX_COMPACT_PROOF_BYTES_V2
    );

    let mut unknown_field: Value = serde_json::from_str(&config_json).unwrap();
    unknown_field["proof"] = Value::Null;
    assert!(MleVerifierV2ConfigFixture::from_json(&unknown_field.to_string()).is_err());
}

#[test]
fn config_only_fixture_rejects_self_consistent_profile_and_digest_drift() {
    let (data, _) = small_mul();
    let config = try_export_mle_v2_config_fixture(&data).unwrap();
    config.validate_self_consistency().unwrap();

    // Recompute both relevant Keccak pins after changing a WHIR parameter.
    // This is internally digest-consistent, but still must not be accepted as
    // the canonical circuit-derived deployment profile.
    let mut profile_drift = config.clone();
    let original_threshold = profile_drift
        .verification_config
        .whir
        .final_pow_threshold
        .clone();
    profile_drift.verification_config.whir.final_pow_threshold =
        if original_threshold == "0" { "1" } else { "0" }.to_string();
    let whir_abi =
        solidity_abi_encode_whir_params_v2(&profile_drift.verification_config.whir).unwrap();
    profile_drift.pinned_verifier.whir_parameters_digest =
        hex_bytes(&<[u8; 32]>::from(Keccak256::digest(&whir_abi)));
    let config_abi =
        solidity_abi_encode_verification_config_v2(&profile_drift.verification_config).unwrap();
    profile_drift.solidity_abi_verification_config = EncodedProofV2Fixture::from_bytes(
        SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2,
        &config_abi,
    );
    profile_drift.pinned_verifier.verification_config_digest = profile_drift
        .solidity_abi_verification_config
        .keccak256
        .clone();
    profile_drift
        .solidity_abi_verification_config
        .decode_and_validate(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2)
        .unwrap();
    assert!(profile_drift.validate_self_consistency().is_err());
    assert!(MleVerifierV2ConfigFixture::from_canonical_json(
        &profile_drift.to_canonical_json().unwrap()
    )
    .is_err());
    assert!(profile_drift.validate_against_circuit(&data).is_err());

    // Likewise, synchronizing the duplicate pin cannot turn an arbitrary VK
    // digest into the one derived by mle_setup_v2 for this circuit.
    let mut digest_drift = config.clone();
    let forged_digest = format!("0x{}", "00".repeat(32));
    assert_ne!(
        digest_drift.verification_key.circuit_config_digest,
        forged_digest
    );
    digest_drift.verification_key.circuit_config_digest = forged_digest.clone();
    digest_drift.pinned_verifier.circuit_config_digest = forged_digest;
    assert!(digest_drift.validate_self_consistency().is_err());
    assert!(digest_drift.validate_against_circuit(&data).is_err());

    // Both maps are authenticated independently, so neither a valid but
    // different config-side map nor an invalid mutually copied map can pass.
    let mut split_map = config.clone();
    let mut different_map = decode_hex(&split_map.verification_config.public_input_wire_map);
    different_map[0] ^= 1;
    split_map.verification_config.public_input_wire_map = hex_bytes(&different_map);
    let split_abi =
        solidity_abi_encode_verification_config_v2(&split_map.verification_config).unwrap();
    split_map.solidity_abi_verification_config =
        EncodedProofV2Fixture::from_bytes(SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2, &split_abi);
    split_map.pinned_verifier.verification_config_digest =
        split_map.solidity_abi_verification_config.keccak256.clone();
    assert!(split_map.validate_self_consistency().is_err());

    let mut out_of_range_map = config.clone();
    let mut invalid_map = decode_hex(&out_of_range_map.verification_key.public_input_wire_map);
    invalid_map[0] = 0xff;
    invalid_map[1] = 0xff;
    let invalid_map = hex_bytes(&invalid_map);
    out_of_range_map.verification_key.public_input_wire_map = invalid_map.clone();
    out_of_range_map.verification_config.public_input_wire_map = invalid_map;
    let invalid_abi =
        solidity_abi_encode_verification_config_v2(&out_of_range_map.verification_config).unwrap();
    out_of_range_map.solidity_abi_verification_config = EncodedProofV2Fixture::from_bytes(
        SOLIDITY_MLE_VERIFICATION_CONFIG_ENCODING_V2,
        &invalid_abi,
    );
    out_of_range_map.pinned_verifier.verification_config_digest = out_of_range_map
        .solidity_abi_verification_config
        .keccak256
        .clone();
    assert!(out_of_range_map.validate_self_consistency().is_err());

    let mut pow_drift = config;
    pow_drift.whir_pow_bits -= 1;
    assert!(pow_drift.validate_self_consistency().is_err());
    assert!(pow_drift.validate_against_circuit(&data).is_err());
}

#[test]
fn proof_aliases_and_self_consistent_cross_view_mutations_fail_closed() {
    let (data, fixture) = exported();

    let mut json: Value = serde_json::from_str(&fixture.to_canonical_json().unwrap()).unwrap();
    json["proof"]["legacyAlias"] = Value::String("0x00".to_string());
    assert!(MleVerifierV2Fixture::from_json(&json.to_string()).is_err());

    let mut proof_drift = fixture.clone();
    proof_drift.proof.public_inputs[0] = "0x0000000000000052".to_string();
    assert!(proof_drift.validate_against_common(&data.common).is_err());

    let mut abi_drift = fixture.clone();
    let mut abi = decode_hex(&abi_drift.solidity_abi_proof.bytes);
    *abi.last_mut().unwrap() ^= 1;
    abi_drift.solidity_abi_proof =
        EncodedProofV2Fixture::from_bytes("abi.encode(MleVerifierV2.MleProof)", &abi);
    assert!(abi_drift.validate_against_common(&data.common).is_err());

    let mut config_abi_drift = fixture.clone();
    let mut config_abi = decode_hex(&config_abi_drift.solidity_abi_verification_config.bytes);
    *config_abi.last_mut().unwrap() ^= 1;
    config_abi_drift.solidity_abi_verification_config = EncodedProofV2Fixture::from_bytes(
        "abi.encode(MleVerifierV2.VerificationConfig)",
        &config_abi,
    );
    config_abi_drift.pinned_verifier.verification_config_digest = config_abi_drift
        .solidity_abi_verification_config
        .keccak256
        .clone();
    assert!(config_abi_drift
        .validate_against_common(&data.common)
        .is_err());

    let mut whir_drift = fixture.clone();
    whir_drift.pinned_verifier.whir_parameters_digest = format!("0x{}", "00".repeat(32));
    assert!(whir_drift.validate_against_common(&data.common).is_err());
}

fn largest_parent_production_shape() -> CompactV2Shape {
    CompactV2Shape {
        degree_bits: 13,
        constituent_width: 160,
        circuit_digest_len: CIRCUIT_DIGEST_LENGTH_V2,
        // The close statement is the largest currently admitted parent profile. Generic decoder
        // caps are wider, but a future profile must receive its own DA/gas admission first.
        public_inputs_len: 103,
        num_constants: 5,
        num_routed_wires: 80,
        num_wires: 135,
        gate_round_degree: 10,
        max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
        max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
        max_encoded_bytes: MAX_COMPACT_PROOF_BYTES_V2,
    }
}

#[test]
fn every_canonical_whir_profile_fits_the_two_blob_compact_boundary() {
    // Use the largest outer payload requested for production admission even
    // for smaller WHIR dimensions. This is conservative: only n=21 actually
    // combines degreeBits=13 with a width whose padded index consumes 8 bits.
    let shape = largest_parent_production_shape();
    let fixed = shape.fixed_encoded_len().unwrap();
    let mut worst_profile = (0usize, 0usize);
    let mut max_narg_bytes = 0usize;
    let mut max_hint_bytes = 0usize;
    for packed_num_variables in 1..=21 {
        let profile =
            derive_whir_deployment_profile_for_packed_num_vars_v2(packed_num_variables).unwrap();
        let whir = profile.proof_size_upper_bound;
        let conservative_compact = fixed + whir.max_total_bytes;
        assert!(whir.narg_bytes <= MAX_WHIR_NARG_BYTES_V2);
        assert!(whir.max_hint_bytes <= MAX_WHIR_HINT_BYTES_V2);
        assert!(
            conservative_compact <= MAX_COMPACT_PROOF_BYTES_V2,
            "packed n={packed_num_variables}: {conservative_compact} > {MAX_COMPACT_PROOF_BYTES_V2}"
        );
        if conservative_compact > worst_profile.1 {
            worst_profile = (packed_num_variables, conservative_compact);
        }
        max_narg_bytes = max_narg_bytes.max(whir.narg_bytes);
        max_hint_bytes = max_hint_bytes.max(whir.max_hint_bytes);
    }
    assert_eq!(max_narg_bytes, MAX_WHIR_NARG_BYTES_V2);
    assert_eq!(max_hint_bytes, MAX_WHIR_HINT_BYTES_V2);
    assert_eq!(worst_profile, (21, 134_372));

    let upper = proof_encoding_size_upper_bound_v2(&shape).unwrap();
    assert_eq!(upper.packed_num_variables, 21);
    assert_eq!(upper.fixed_compact_bytes, 20_060);
    assert_eq!(upper.max_whir_transcript_bytes, 1_904);
    assert_eq!(upper.max_whir_hint_bytes, 112_408);
    assert_eq!(upper.max_compact_bytes, 134_372);
    assert_eq!(upper.max_solidity_abi_bytes, 197_536);
    assert!(upper.fits_whir_blob_caps);
    assert!(upper.fits_compact_cap);
    eprintln!(
        "largest-parent-profile-v2 packed={} fixed={} narg={} hints={} compact={} abi={} cap={}",
        upper.packed_num_variables,
        upper.fixed_compact_bytes,
        upper.max_whir_transcript_bytes,
        upper.max_whir_hint_bytes,
        upper.max_compact_bytes,
        upper.max_solidity_abi_bytes,
        upper.compact_cap_bytes,
    );
}
