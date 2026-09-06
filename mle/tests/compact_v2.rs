//! Canonical compact-v2 codec tests, including a real WHIR debug-pattern
//! reconstruction and byte-exact size accounting.

use ark_ff::PrimeField as ArkPrimeField;
use keccak_hash::keccak;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::util::timing::TimingTree;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field;
use plonky2_mle::compact_v2::{
    decode_compact_v2, encode_compact_v2, CompactV2Error, CompactV2Shape,
};
use plonky2_mle::protocol_schema_v2::{
    COMPACT_MAGIC_V2, MAX_COMPACT_PROOF_BYTES_V2, MAX_WHIR_HINT_BYTES_V2, MAX_WHIR_NARG_BYTES_V2,
    MLE_PROTOCOL_VERSION_CURRENT,
};
use plonky2_mle::prover_v2::{mle_prove_v2, mle_setup_v2};
use plonky2_mle::verifier_v2::mle_verify_v2;

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;
const TEST_MAX_PROOF_BYTES: usize = MAX_COMPACT_PROOF_BYTES_V2;
const HISTORICAL_WIRE_V2_FIXTURE: &str =
    include_str!("../testdata/historical_wire_v2_compact.json");
const HISTORICAL_WIRE_V2_KECCAK: &str =
    "0xd7eb1b018d6e33a8546436e05788ca9946cd994dd93ed9b8c689ac97f92e418a";

#[test]
fn genuine_wire_v2_is_rejected_before_decode_and_after_header_relabel() {
    let fixture: serde_json::Value =
        serde_json::from_str(HISTORICAL_WIRE_V2_FIXTURE).expect("historical wire-v2 JSON");
    assert_eq!(
        fixture["source"]["sourceFixtureSha256"],
        "0xe4bd26575fb6b101e8be487251689bc073511e1df7ba69996afccfbf14ac6af3",
        "the recovery provenance must remain pinned"
    );
    assert_eq!(fixture["case"], "small_mul");
    assert_eq!(fixture["compactProof"]["encoding"], "MLEWHIR2");

    let legacy = decode_hex(
        fixture["compactProof"]["bytes"]
            .as_str()
            .expect("historical compact bytes"),
    );
    assert_eq!(
        legacy.len(),
        fixture["compactProof"]["byteLength"]
            .as_u64()
            .expect("historical compact length") as usize
    );
    assert_eq!(
        format!("0x{:x}", keccak(&legacy)),
        HISTORICAL_WIRE_V2_KECCAK
    );
    assert!(legacy_v2_header_accepts(&legacy));

    let (circuit, vk) = current_small_mul_circuit_and_vk();
    let shape = CompactV2Shape {
        degree_bits: circuit.common.degree_bits(),
        constituent_width: vk.constituent_width,
        circuit_digest_len: vk.circuit_digest.len(),
        public_inputs_len: circuit.common.num_public_inputs,
        num_constants: circuit.common.num_constants,
        num_routed_wires: circuit.common.config.num_routed_wires,
        num_wires: circuit.common.config.num_wires,
        gate_round_degree: circuit.common.quotient_degree_factor + 2,
        max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
        max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
        max_encoded_bytes: TEST_MAX_PROOF_BYTES,
    };

    // The production decoder must stop a genuine old wire at the revision
    // boundary, before any attacker-controlled vector body is interpreted.
    assert!(matches!(
        decode_compact_v2::<F>(&legacy, &shape),
        Err(CompactV2Error::BadMagic)
    ));

    // Changing exactly the 16-byte discriminator makes the old body
    // structurally parseable under the unchanged compact grammar. It must
    // still fail under the current transcript and WHIR protocol/session.
    let mut relabeled = legacy.clone();
    relabeled[..8].copy_from_slice(&COMPACT_MAGIC_V2);
    relabeled[8..16].copy_from_slice(&MLE_PROTOCOL_VERSION_CURRENT.to_le_bytes());
    assert_eq!(
        &relabeled[16..],
        &legacy[16..],
        "only the header may change"
    );
    let decoded = match decode_compact_v2::<F>(&relabeled, &shape) {
        Ok(decoded) => decoded,
        #[cfg(debug_assertions)]
        Err(CompactV2Error::WhirPatternReconstruction(message)) => {
            // Debug builds reconstruct WHIR's non-wire diagnostic pattern as
            // the last decode step, after exact body consumption. The v2
            // proof used the superseded 130-bit WHIR profile, so the current
            // 133-bit preflight rejects it here. Release decoding deliberately
            // omits this diagnostic and exercises full verification below.
            assert!(
                message.contains("hint vector length mismatch"),
                "unexpected current-WHIR preflight rejection: {message}"
            );
            return;
        }
        Err(error) => panic!(
            "header-relabeled legacy body failed before current-WHIR cryptographic preflight: {error}"
        ),
    };
    assert_eq!(
        encode_compact_v2(&decoded, &shape).unwrap(),
        relabeled,
        "the relabeled legacy body must decode canonically"
    );
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &decoded)
        .expect_err("wire-v2 proof must not verify under wire-v3 domains");
    assert!(
        error
            .to_string()
            .contains("grouped WHIR verification failed"),
        "legacy proof must reach and fail the current WHIR verifier, got: {error:#}"
    );
}

fn current_small_mul_circuit_and_vk() -> (
    plonky2::plonk::circuit_data::CircuitData<F, C, D>,
    plonky2_mle::proof_v2::MleVerificationKeyV2<F>,
) {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let mut current = x;
    for _ in 0..5 {
        current = builder.mul(current, x);
    }
    builder.register_public_input(current);
    let circuit = builder.build::<C>();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    (circuit, vk)
}

fn decode_hex(encoded: &str) -> Vec<u8> {
    let encoded = encoded.strip_prefix("0x").expect("hex prefix");
    assert_eq!(encoded.len() % 2, 0, "hex byte length");
    encoded
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let hi = (pair[0] as char).to_digit(16).expect("hex high nibble");
            let lo = (pair[1] as char).to_digit(16).expect("hex low nibble");
            ((hi << 4) | lo) as u8
        })
        .collect()
}

#[test]
fn real_proof_roundtrip_is_canonical_bounded_and_exactly_accounted() {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let y = builder.add_virtual_target();
    let product = builder.mul(x, y);
    builder.register_public_input(product);
    let circuit = builder.build::<C>();

    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let mut witness = PartialWitness::new();
    witness.set_target(x, F::from_canonical_u64(3)).unwrap();
    witness.set_target(y, F::from_canonical_u64(7)).unwrap();
    let proof = mle_prove_v2::<F, C, D>(
        &circuit.prover_only,
        &circuit.common,
        witness,
        &mut TimingTree::default(),
    )
    .expect("honest v2 proof generation");
    let shape = CompactV2Shape {
        degree_bits: circuit.common.degree_bits(),
        constituent_width: vk.constituent_width,
        circuit_digest_len: vk.circuit_digest.len(),
        public_inputs_len: circuit.common.num_public_inputs,
        num_constants: circuit.common.num_constants,
        num_routed_wires: circuit.common.config.num_routed_wires,
        num_wires: circuit.common.config.num_wires,
        gate_round_degree: circuit.common.quotient_degree_factor + 2,
        max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
        max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
        max_encoded_bytes: TEST_MAX_PROOF_BYTES,
    };

    let encoded = encode_compact_v2(&proof, &shape).expect("compact encode");
    assert_eq!(&encoded[..8], &COMPACT_MAGIC_V2);
    assert_eq!(
        u64::from_le_bytes(encoded[8..16].try_into().unwrap()),
        MLE_PROTOCOL_VERSION_CURRENT
    );

    // Wire revision 3 is a hard cutover. A strict legacy-v2 discriminator
    // rejects current bytes, while the current decoder rejects both a genuine
    // legacy header and an old payload whose version alone was rewritten to 3.
    assert!(
        !legacy_v2_header_accepts(&encoded),
        "v3 must not parse as v2"
    );
    let mut legacy_v2 = encoded.clone();
    legacy_v2[..8].copy_from_slice(b"MLEWHIR2");
    legacy_v2[8..16].copy_from_slice(&2u64.to_le_bytes());
    assert!(legacy_v2_header_accepts(&legacy_v2));
    assert!(matches!(
        decode_compact_v2::<F>(&legacy_v2, &shape),
        Err(CompactV2Error::BadMagic)
    ));

    let mut current_magic_old_version = encoded.clone();
    current_magic_old_version[8..16].copy_from_slice(&2u64.to_le_bytes());
    assert!(matches!(
        decode_compact_v2::<F>(&current_magic_old_version, &shape),
        Err(CompactV2Error::WrongProtocolVersion { got: 2 })
    ));

    let mut legacy_payload_with_only_version_bumped = legacy_v2.clone();
    legacy_payload_with_only_version_bumped[8..16]
        .copy_from_slice(&MLE_PROTOCOL_VERSION_CURRENT.to_le_bytes());
    assert!(!legacy_v2_header_accepts(
        &legacy_payload_with_only_version_bumped
    ));
    assert!(matches!(
        decode_compact_v2::<F>(&legacy_payload_with_only_version_bumped, &shape),
        Err(CompactV2Error::BadMagic)
    ));
    println!(
        "compact-v2 bytes: total={}, fixed={}, WHIR narg={}, WHIR hints={}",
        encoded.len(),
        shape.fixed_encoded_len().unwrap(),
        proof.whir_eval_proof.narg_string.len(),
        proof.whir_eval_proof.hints.len(),
    );
    assert_eq!(
        encoded.len(),
        shape
            .encoded_len(
                proof.whir_eval_proof.narg_string.len(),
                proof.whir_eval_proof.hints.len(),
            )
            .unwrap()
    );

    // Independent accounting: 8-byte magic, u64 version, u32 width, three
    // roots, and two u32 WHIR lengths, followed only by canonical field limbs.
    let preprocessed = shape.num_constants + shape.num_routed_wires;
    let norm_inverse = 2 * shape.num_routed_wires;
    let fixed_header = 8 + 8 + 4 + 3 * 32 + 2 * 4;
    let statement = (shape.circuit_digest_len + shape.public_inputs_len) * 8;
    let log_rounds = shape.degree_bits * 5 * 3 * 8;
    let log_terminal = (preprocessed + shape.num_wires + norm_inverse) * 3 * 8;
    let gates =
        3 * (shape.degree_bits * shape.gate_round_degree + preprocessed + shape.num_wires) * 8;
    assert_eq!(
        shape.fixed_encoded_len().unwrap(),
        fixed_header + statement + log_rounds + log_terminal + gates
    );

    let decoded = decode_compact_v2::<F>(&encoded, &shape).expect("compact decode");
    mle_verify_v2::<F, D>(&circuit.common, &vk, &decoded).expect("decoded proof must verify");
    assert_eq!(
        encode_compact_v2(&decoded, &shape).unwrap(),
        encoded,
        "decode/re-encode must be byte-identical"
    );
    #[cfg(debug_assertions)]
    assert_eq!(
        decoded.whir_eval_proof.pattern, proof.whir_eval_proof.pattern,
        "the codec must reconstruct, not omit, WHIR's debug interaction pattern"
    );

    let narg_length_offset = 20 + (shape.circuit_digest_len + shape.public_inputs_len) * 8 + 3 * 32;
    let hints_length_offset = narg_length_offset + 4 + proof.whir_eval_proof.narg_string.len();
    let first_log_coefficient_offset = hints_length_offset + 4 + proof.whir_eval_proof.hints.len();
    let first_log_coefficient = proof.log_sumcheck_proof.rounds[0].non_constant[0];
    for (limb, expected) in [
        first_log_coefficient.c0.into_bigint().0[0],
        first_log_coefficient.c1.into_bigint().0[0],
        first_log_coefficient.c2.into_bigint().0[0],
    ]
    .into_iter()
    .enumerate()
    {
        let start = first_log_coefficient_offset + limb * 8;
        assert_eq!(
            &encoded[start..start + 8],
            &expected.to_le_bytes(),
            "Ext3 must be encoded in c0,c1,c2 order"
        );
    }

    let mut noncanonical = encoded.clone();
    // First circuit-digest limb starts immediately after the fixed 20-byte
    // magic/version/width prefix.
    noncanonical[20..28].copy_from_slice(&0xffff_ffff_0000_0001u64.to_le_bytes());
    assert!(matches!(
        decode_compact_v2::<F>(&noncanonical, &shape),
        Err(CompactV2Error::NonCanonicalGoldilocks { offset: 20, .. })
    ));
    let mut noncanonical_ext3 = encoded.clone();
    let c1_offset = first_log_coefficient_offset + 8;
    noncanonical_ext3[c1_offset..c1_offset + 8]
        .copy_from_slice(&0xffff_ffff_0000_0001u64.to_le_bytes());
    assert!(matches!(
        decode_compact_v2::<F>(&noncanonical_ext3, &shape),
        Err(CompactV2Error::NonCanonicalGoldilocks { offset, .. }) if offset == c1_offset
    ));

    let mut trailing = encoded.clone();
    trailing.push(0);
    assert!(matches!(
        decode_compact_v2::<F>(&trailing, &shape),
        Err(CompactV2Error::TrailingBytes { count: 1 })
    ));
    for truncated_len in [0, 7, 19, encoded.len() - 1] {
        assert!(
            decode_compact_v2::<F>(&encoded[..truncated_len], &shape).is_err(),
            "truncation at {truncated_len} must be rejected"
        );
    }

    let mut bounded_shape = shape.clone();
    bounded_shape.max_encoded_bytes = encoded.len() - 1;
    assert!(matches!(
        decode_compact_v2::<F>(&encoded, &bounded_shape),
        Err(CompactV2Error::ProofTooLarge { .. })
    ));

    let mut oversized_blob = encoded.clone();
    oversized_blob[narg_length_offset..narg_length_offset + 4]
        .copy_from_slice(&((shape.max_whir_narg_bytes + 1) as u32).to_le_bytes());
    assert!(matches!(
        decode_compact_v2::<F>(&oversized_blob, &shape),
        Err(CompactV2Error::WhirBlobTooLarge {
            blob: "narg_string",
            ..
        })
    ));

    let mut malformed = proof.clone();
    malformed.preprocessed_root.pop();
    assert!(matches!(
        encode_compact_v2(&malformed, &shape),
        Err(CompactV2Error::WrongRootLength {
            root: "preprocessed",
            got: 31
        })
    ));
    let mut malformed = proof.clone();
    malformed.log_sumcheck_proof.rounds[0].non_constant.pop();
    assert!(matches!(
        encode_compact_v2(&malformed, &shape),
        Err(CompactV2Error::WrongVectorLength {
            field: "log round coefficients",
            ..
        })
    ));
}

/// Models the strict revision discriminator of a frozen wire-v2 reader. The
/// body grammar need not be duplicated here: neither revision reaches body
/// decoding when the other's exact magic/version pair is supplied.
fn legacy_v2_header_accepts(encoded: &[u8]) -> bool {
    encoded.len() >= 16
        && &encoded[..8] == b"MLEWHIR2"
        && u64::from_le_bytes(encoded[8..16].try_into().unwrap()) == 2
}

#[test]
fn decoder_shape_is_pinned_to_the_reviewed_v2_envelope() {
    let canonical = CompactV2Shape {
        degree_bits: 2,
        constituent_width: 160,
        circuit_digest_len: 4,
        public_inputs_len: 1,
        num_constants: 4,
        num_routed_wires: 80,
        num_wires: 135,
        gate_round_degree: 10,
        max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
        max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
        max_encoded_bytes: TEST_MAX_PROOF_BYTES,
    };
    canonical.fixed_encoded_len().expect("canonical shape");

    let fixed = canonical.fixed_encoded_len().unwrap();
    let maximum_canonical = fixed + MAX_WHIR_NARG_BYTES_V2 + MAX_WHIR_HINT_BYTES_V2;
    assert_eq!(
        canonical
            .encoded_len(MAX_WHIR_NARG_BYTES_V2, MAX_WHIR_HINT_BYTES_V2)
            .unwrap(),
        maximum_canonical,
        "the exact grammar-derived WHIR caps are accepted"
    );
    assert!(maximum_canonical < MAX_COMPACT_PROOF_BYTES_V2);
    assert!(matches!(
        canonical.encoded_len(MAX_WHIR_NARG_BYTES_V2 + 1, 0),
        Err(CompactV2Error::WhirBlobTooLarge {
            blob: "narg_string",
            ..
        })
    ));
    assert!(matches!(
        canonical.encoded_len(0, MAX_WHIR_HINT_BYTES_V2 + 1),
        Err(CompactV2Error::WhirBlobTooLarge { blob: "hints", .. })
    ));

    let mut invalid = canonical.clone();
    invalid.degree_bits = 0;
    assert!(matches!(
        invalid.fixed_encoded_len(),
        Err(CompactV2Error::InvalidShape(
            "row-variable count must be non-zero"
        ))
    ));

    let mut invalid = canonical.clone();
    invalid.circuit_digest_len = 3;
    assert!(matches!(
        invalid.fixed_encoded_len(),
        Err(CompactV2Error::InvalidShape(
            "circuit digest length does not match the wire-v3 protocol"
        ))
    ));

    let mut invalid = canonical.clone();
    invalid.gate_round_degree = 2;
    assert!(matches!(
        invalid.fixed_encoded_len(),
        Err(CompactV2Error::InvalidShape(
            "gate round degree must include a positive quotient degree factor"
        ))
    ));

    let mut invalid = canonical.clone();
    invalid.max_encoded_bytes += 1;
    assert!(matches!(
        invalid.fixed_encoded_len(),
        Err(CompactV2Error::InvalidShape(
            "compact proof cap exceeds the reviewed v2 envelope"
        ))
    ));
}
