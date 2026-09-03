//! End-to-end adversarial checks for the MLE/WHIR v2 protocol.
//!
//! These tests intentionally mutate one proof component at a time. They are
//! integration tests so they exercise the same public setup/prove/verify API
//! that downstream callers use, including the grouped WHIR opening.

use ark_ff::{AdditiveGroup, Field as ArkField, PrimeField as ArkPrimeField};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::plonk::prover::extract_evaluation_tables;
use plonky2::util::timing::TimingTree;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use plonky2_mle::proof_v2::{MleProofV2, MleVerificationKeyV2};
use plonky2_mle::protocol_schema_v2::{
    DOMAIN_WHIR_PROTOCOL_ID_V2, DOMAIN_WHIR_SESSION_ID_V2, MAX_WHIR_HINT_BYTES_V2,
    MAX_WHIR_NARG_BYTES_V2,
};
use plonky2_mle::prover_v2::{mle_prove_v2, mle_prove_v2_from_tables, mle_setup_v2};
use plonky2_mle::sumcheck::coefficients::evaluate_ext3_coefficient_round;
use plonky2_mle::transcript_v2::TranscriptV2;
use plonky2_mle::verifier_v2::mle_verify_v2;
use plonky2_mle::vk_v2::circuit_config_digest_v2;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

fn assert_rejected(
    label: &str,
    common_data: &CommonCircuitData<F, D>,
    vk: &MleVerificationKeyV2<F>,
    proof: &MleProofV2<F>,
) {
    let result = mle_verify_v2::<F, D>(common_data, vk, proof);
    assert!(result.is_err(), "v2 verifier accepted {label} tampering");
}

#[test]
fn either_ext3_round_message_commits_before_both_challenges() {
    let log_message = [
        whir::algebra::fields::Field64_3::from(11u64),
        whir::algebra::fields::Field64_3::from(12u64),
        whir::algebra::fields::Field64_3::from(13u64),
        whir::algebra::fields::Field64_3::from(14u64),
        whir::algebra::fields::Field64_3::from(15u64),
    ];
    let gate_message = [Field64_3::from(21u64), Field64_3::from(22u64)];

    let mut baseline_transcript = TranscriptV2::new();
    let baseline =
        baseline_transcript.commit_coupled_outer_round::<F>(0, &log_message, &gate_message);

    let mut changed_gate_message = gate_message;
    changed_gate_message[0].c2 += ArkGoldilocks::from(1u64);
    let mut changed_transcript = TranscriptV2::new();
    let changed =
        changed_transcript.commit_coupled_outer_round::<F>(0, &log_message, &changed_gate_message);

    assert_ne!(
        baseline.log, changed.log,
        "gate message must be committed before the log challenge is sampled"
    );
    assert_ne!(
        baseline.gate, changed.gate,
        "gate message must affect the gate challenge"
    );
}

#[test]
fn coupled_round_v3_rust_solidity_golden() {
    let ext = |c0: u64, c1: u64, c2: u64| {
        Field64_3::new(
            ArkGoldilocks::from(c0),
            ArkGoldilocks::from(c1),
            ArkGoldilocks::from(c2),
        )
    };
    let log_message = (0..5)
        .map(|i| {
            let seed = i + 1;
            ext(seed, 3 * seed + 1, 5 * seed + 2)
        })
        .collect::<Vec<_>>();
    let gate_message = [ext(21, 22, 23), ext(24, 25, 26)];
    let mut transcript = TranscriptV2::new();
    let challenges = transcript.commit_coupled_outer_round::<F>(0, &log_message, &gate_message);
    let log_claim = evaluate_ext3_coefficient_round(Field64_3::ZERO, &log_message, challenges.log);
    let gate_claim =
        evaluate_ext3_coefficient_round(Field64_3::ZERO, &gate_message, challenges.gate);

    let limbs = |value: Field64_3| {
        [
            value.c0.into_bigint().0[0],
            value.c1.into_bigint().0[0],
            value.c2.into_bigint().0[0],
        ]
    };
    assert_eq!(
        limbs(challenges.log),
        [0x101d9af08db40617, 0x7529dd5b1fafe3e3, 0x2b9351ba9692677c]
    );
    assert_eq!(
        limbs(challenges.gate),
        [0x2a96f20b5bd7d1c2, 0xe7a35e0a0f649811, 0x6c92c57d946a386f]
    );
    assert_eq!(
        limbs(log_claim),
        [0xf659a095b0a23acc, 0xa5ec18cc2773fdf4, 0xe7ddc8b5838d23e1]
    );
    assert_eq!(
        limbs(gate_claim),
        [0xd05f19f354a90d75, 0x95cfdd85d425cc52, 0x81d8577401ac5afd]
    );
    assert_eq!(
        transcript.state_digest(),
        [
            0xeb, 0xdf, 0x7b, 0x3d, 0x5b, 0x53, 0xf7, 0x38, 0x63, 0x88, 0x44, 0x86, 0x33, 0xb9,
            0xdf, 0x46, 0x35, 0x92, 0x26, 0xc1, 0x30, 0xa9, 0x9d, 0x6c, 0xc2, 0xf7, 0x09, 0x73,
            0xd7, 0xed, 0x12, 0x26,
        ]
    );
    assert_eq!(transcript.current_squeeze_counter(), 6);
}

#[test]
fn transcript_v3_rust_solidity_goldens() {
    let ext = |c0: u64, c1: u64, c2: u64| {
        Field64_3::new(
            ArkGoldilocks::from(c0),
            ArkGoldilocks::from(c1),
            ArkGoldilocks::from(c2),
        )
    };
    let mut transcript = TranscriptV2::new();
    let mut states = vec![transcript.state_digest()];
    transcript.absorb_field(F::from_canonical_u64(7));
    states.push(transcript.state_digest());
    transcript.absorb_field_vec(&[
        F::ZERO,
        F::ONE,
        F::from_canonical_u64(0xffff_ffff_0000_0000),
    ]);
    states.push(transcript.state_digest());
    transcript.absorb_ext3(ext(2, 3, 4));
    states.push(transcript.state_digest());
    transcript.absorb_ext3_vec(&[ext(5, 6, 7), ext(8, 9, 10)]);
    states.push(transcript.state_digest());
    let base0 = transcript.squeeze_challenge::<F>().to_canonical_u64();
    let base1 = transcript.squeeze_challenge::<F>().to_canonical_u64();
    let extension = transcript.squeeze_ext3::<F>();
    let encode_hex = |bytes: &[u8]| {
        bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };
    assert_eq!(
        states
            .iter()
            .map(|state| encode_hex(state))
            .collect::<Vec<_>>(),
        [
            "4eee7256a652e68d8b7a7b0460a1de52b8c10bfab17a7b5ec5c97b4ba120f236",
            "e7c2d5013557fab96927ececb4eea1c8afda5c40078fd73f34f6d449e4e34adc",
            "fc993ee71ec6b1a4011aa60afce7cb459dcf6ec321ea7bb5beac717b42235852",
            "fed8599ef0f0987ddfde75c4f779382ed4401d9a780c8e9fea422b168e73b685",
            "e727699ebf2501ed1554b63fa0409dfc876f26b4c45310ac1f4a9d696762be9f",
        ]
    );
    assert_eq!([base0, base1], [0xace93c7d4a6e54c9, 0x6653b74a5af389e9]);
    assert_eq!(
        [
            extension.c0.into_bigint().0[0],
            extension.c1.into_bigint().0[0],
            extension.c2.into_bigint().0[0],
        ],
        [0x26c9eca14e4bcf44, 0xa463149450187e75, 0x85433e61a4ca93d2]
    );

    let log = [ext(11, 12, 13), ext(14, 15, 16)];
    let gate = [ext(21, 22, 23), ext(24, 25, 26)];
    let coupled = transcript.commit_coupled_outer_round::<F>(3, &log, &gate);
    assert_eq!(
        encode_hex(&transcript.state_digest()),
        "1c5c8ee575d5a624ae2cab5acc842597a360a81bb99496af7ef448450d04c32b"
    );
    assert_eq!(
        [
            coupled.log.c0.into_bigint().0[0],
            coupled.log.c1.into_bigint().0[0],
            coupled.log.c2.into_bigint().0[0],
        ],
        [0x67030ba296206426, 0x160c6cb281baa3ae, 0x92fc9d717662050b]
    );
    assert_eq!(
        [
            coupled.gate.c0.into_bigint().0[0],
            coupled.gate.c1.into_bigint().0[0],
            coupled.gate.c2.into_bigint().0[0],
        ],
        [0x743613855ac7898d, 0xf834e6c52a4e27f7, 0x56c655bb797ad0cc]
    );

    let protocol_id = (0u8..64).collect::<Vec<_>>();
    let session_id = (0x80u8..=0x9f).collect::<Vec<_>>();
    let mut whir = TranscriptV2::new();
    whir.domain_separate(DOMAIN_WHIR_PROTOCOL_ID_V2);
    whir.absorb_bytes(&protocol_id);
    whir.domain_separate(DOMAIN_WHIR_SESSION_ID_V2);
    whir.absorb_bytes(&session_id);
    assert_eq!(
        encode_hex(&whir.state_digest()),
        "9d186e7a5d202c97b788e898ac9e0b33ed2e7e27118ae0e2470ce82af522227d"
    );
}

#[test]
fn honest_roundtrip_and_high_value_tampering_matrix() {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let y = builder.add_virtual_target();
    let product = builder.mul(x, y);
    builder.register_public_input(product);
    builder.register_public_input(product);
    builder.register_public_input(x);
    let circuit = builder.build::<C>();

    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let mut witness = PartialWitness::new();
    witness.set_target(x, F::from_canonical_u64(3)).unwrap();
    witness.set_target(y, F::from_canonical_u64(7)).unwrap();
    let mut timing = TimingTree::default();
    let proof =
        mle_prove_v2::<F, C, D>(&circuit.prover_only, &circuit.common, witness, &mut timing)
            .expect("honest v2 proof generation");

    mle_verify_v2::<F, D>(&circuit.common, &vk, &proof).expect("honest v2 proof must verify");
    assert_eq!(proof.public_inputs[0], proof.public_inputs[1]);
    assert_eq!(
        &vk.public_input_wire_map[0..3],
        &vk.public_input_wire_map[3..6]
    );

    let mut tampered = proof.clone();
    tampered.public_inputs[0] += F::ONE;
    assert_rejected("raw public input", &circuit.common, &vk, &tampered);

    let mut tampered_vk = vk.clone();
    tampered_vk.public_input_wire_map.pop();
    assert_rejected(
        "short public-input wire map",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    let degree = circuit.common.degree();
    assert!(degree <= u16::MAX as usize);
    tampered_vk.public_input_wire_map[0] = degree as u8;
    tampered_vk.public_input_wire_map[1] = (degree >> 8) as u8;
    assert_rejected(
        "out-of-range public-input row",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    tampered_vk.public_input_wire_map[2] = circuit.common.config.num_routed_wires as u8;
    assert_rejected(
        "non-routed public-input column",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    let third = tampered_vk.public_input_wire_map[6..9].to_vec();
    tampered_vk.public_input_wire_map.copy_within(0..6, 3);
    tampered_vk.public_input_wire_map[0..3].copy_from_slice(&third);
    assert_ne!(tampered_vk.public_input_wire_map, vk.public_input_wire_map);
    assert_rejected(
        "reordered public-input wire map",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    // The native verifier is a separate public trust boundary from the
    // compact/Solidity decoders. It must reject oversized attacker-controlled
    // WHIR blobs before replay clones or parses them.
    let mut tampered = proof.clone();
    tampered
        .whir_eval_proof
        .narg_string
        .resize(MAX_WHIR_NARG_BYTES_V2 + 1, 0);
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &tampered)
        .expect_err("oversized WHIR transcript must be rejected");
    assert!(error.to_string().contains("resource envelope"));

    let mut tampered = proof.clone();
    tampered
        .whir_eval_proof
        .hints
        .resize(MAX_WHIR_HINT_BYTES_V2 + 1, 0);
    let error = mle_verify_v2::<F, D>(&circuit.common, &vk, &tampered)
        .expect_err("oversized WHIR hints must be rejected");
    assert!(error.to_string().contains("resource envelope"));

    // V2's cross-language circuit-digest schema is exactly four canonical
    // Goldilocks limbs. Matching variable-length proof/VK vectors must not
    // create a Rust-only statement that Solidity cannot represent.
    let mut tampered = proof.clone();
    let mut tampered_vk = vk.clone();
    tampered.circuit_digest.push(F::ONE);
    tampered_vk.circuit_digest.push(F::ONE);
    let error = mle_verify_v2::<F, D>(&circuit.common, &tampered_vk, &tampered)
        .expect_err("non-canonical circuit digest shape must be rejected");
    assert!(error.to_string().contains("circuit digest shape"));

    let mut oversized_digest = vk.circuit_digest.clone();
    oversized_digest.push(F::ONE);
    let error = circuit_config_digest_v2(
        &circuit.common,
        &oversized_digest,
        &vk.subgroup_gen_powers,
        &vk.gates,
        &vk.public_input_wire_map,
    )
    .expect_err("config digest must reject a non-canonical circuit digest shape");
    assert!(error.to_string().contains("circuit digest shape"));

    let mut extraction_witness = PartialWitness::new();
    extraction_witness
        .set_target(x, F::from_canonical_u64(3))
        .unwrap();
    extraction_witness
        .set_target(y, F::from_canonical_u64(7))
        .unwrap();
    let mut extraction_timing = TimingTree::default();
    let tables = extract_evaluation_tables::<F, C, D>(
        &circuit.prover_only,
        &circuit.common,
        extraction_witness,
        &mut extraction_timing,
    )
    .expect("evaluation-table extraction");
    let error = mle_prove_v2_from_tables(&circuit.common, &tables, &oversized_digest)
        .err()
        .expect("table-level prover must reject a non-canonical circuit digest shape");
    assert!(error.to_string().contains("circuit digest shape"));

    let mut tampered = proof.clone();
    tampered.gate_proof.sumcheck_proof.rounds[0].non_constant[0].c2 += ArkGoldilocks::from(1u64);
    assert_rejected("Ext3 gate round message", &circuit.common, &vk, &tampered);

    // Change only one coordinate of one Ext3 coefficient, rather than adding
    // an embedded base-field value to all of the logical proof object.
    let mut tampered = proof.clone();
    tampered.log_sumcheck_proof.rounds[0].non_constant[0].c1 += ArkGoldilocks::from(1u64);
    assert_rejected(
        "norm/logUp Ext3 round limb",
        &circuit.common,
        &vk,
        &tampered,
    );

    // Roots are both outer-transcript-bound and checked against the roots
    // carried inside the grouped WHIR proof. Preprocessed is additionally
    // fixed by the verification key.
    for root_index in 0..3 {
        let mut tampered = proof.clone();
        let root = match root_index {
            0 => &mut tampered.preprocessed_root,
            1 => &mut tampered.witness_root,
            2 => &mut tampered.norm_inverse_root,
            _ => unreachable!(),
        };
        root[0] ^= 1;
        assert_rejected(
            &format!("commitment root {root_index}"),
            &circuit.common,
            &vk,
            &tampered,
        );
    }

    assert_ne!(proof.witness_root, proof.norm_inverse_root);
    let mut tampered = proof.clone();
    std::mem::swap(&mut tampered.witness_root, &mut tampered.norm_inverse_root);
    assert_rejected("commitment root ordering", &circuit.common, &vk, &tampered);

    // Each of the five used point/group cells is reconstructed from one of
    // these constituent vectors and compared with the pre-RLC WHIR claims.
    let mut tampered = proof.clone();
    tampered.log_preprocessed_evals[0] += whir::algebra::fields::Field64_3::from(1u64);
    assert_rejected(
        "log preprocessed terminal vector",
        &circuit.common,
        &vk,
        &tampered,
    );

    let mut tampered = proof.clone();
    tampered.log_witness_evals[0] += whir::algebra::fields::Field64_3::from(1u64);
    assert_rejected(
        "log witness terminal vector",
        &circuit.common,
        &vk,
        &tampered,
    );

    let mut tampered = proof.clone();
    tampered.log_norm_inverse_evals[0] += whir::algebra::fields::Field64_3::from(1u64);
    assert_rejected(
        "log helper terminal vector",
        &circuit.common,
        &vk,
        &tampered,
    );

    let mut tampered = proof.clone();
    tampered.gate_proof.preprocessed_evals[0].c1 += ArkGoldilocks::from(1u64);
    assert_rejected(
        "Ext3 gate preprocessed terminal vector",
        &circuit.common,
        &vk,
        &tampered,
    );

    let mut tampered = proof.clone();
    tampered.gate_proof.witness_evals[0].c2 += ArkGoldilocks::from(1u64);
    assert_rejected(
        "Ext3 gate witness terminal vector",
        &circuit.common,
        &vk,
        &tampered,
    );

    let mut tampered = proof.clone();
    tampered.protocol_version = 2;
    assert_rejected("proof protocol version", &circuit.common, &vk, &tampered);

    let mut tampered = proof.clone();
    tampered.constituent_width = tampered.constituent_width.saturating_add(1);
    assert_rejected("proof constituent width", &circuit.common, &vk, &tampered);

    let mut tampered_vk = vk.clone();
    tampered_vk.protocol_version = 2;
    assert_rejected(
        "verification-key protocol version",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    tampered_vk.constituent_width = tampered_vk.constituent_width.saturating_add(1);
    assert_rejected(
        "verification-key constituent width",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    tampered_vk.whir_protocol_id[0] ^= 1;
    assert_rejected(
        "verification-key WHIR protocol/config id",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    tampered_vk.whir_session_id[0] ^= 1;
    assert_rejected(
        "verification-key WHIR session id",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    tampered_vk.circuit_config_digest[0] ^= 1;
    assert_rejected(
        "verification-key circuit configuration digest",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    let mut tampered_vk = vk.clone();
    tampered_vk.gates[0].gate_id ^= 1;
    assert_rejected(
        "verification-key gate metadata",
        &circuit.common,
        &tampered_vk,
        &proof,
    );

    // Model the retired scalar-RLC attack language directly. For each of the
    // five terminal-used point/group cells, alter two coordinates by a
    // non-zero vector in the kernel of an arbitrary legacy coefficient vector
    // `(1, rho)`. The scalar batch is unchanged, but v2 re-folds the complete
    // vector at a post-claim Ext3 index point and the committed WHIR statement
    // rejects it. The v1 auxiliary group has no v2 analogue: its relation was
    // eliminated by the joint norm/logUp construction rather than retained as
    // another prover-controlled compensation surface.
    let rho = ArkGoldilocks::from(7u64);
    let delta0 = ArkGoldilocks::ONE;
    let delta1 = -rho.inverse().expect("non-zero legacy RLC challenge");
    assert_eq!(delta0 + rho * delta1, ArkGoldilocks::ZERO);
    for cell in 0..5 {
        let mut tampered = proof.clone();
        let values = match cell {
            0 => &mut tampered.log_preprocessed_evals,
            1 => &mut tampered.log_witness_evals,
            2 => &mut tampered.log_norm_inverse_evals,
            3 => &mut tampered.gate_proof.preprocessed_evals,
            4 => &mut tampered.gate_proof.witness_evals,
            _ => unreachable!(),
        };
        assert!(values.len() >= 2);
        values[0].c0 += delta0;
        values[1].c0 += delta1;
        assert_rejected(
            &format!("legacy two-coordinate RLC kernel in used v2 cell {cell}"),
            &circuit.common,
            &vk,
            &tampered,
        );
    }
}
