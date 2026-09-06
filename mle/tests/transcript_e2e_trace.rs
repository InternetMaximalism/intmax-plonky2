//! Byte-exact v1 preprocessed-batch and outer-transcript golden traces.
//!
//! Replays the canonical `small_mul` fixture through the dedicated
//! `preprocessedBatchR` mini-transcript and every outer root, challenge,
//! sumcheck message and terminal query point. It also consumes the serialized
//! grouped-WHIR proof through the production Rust preflight schedule and pins
//! every native Keccak absorb, squeeze, root, bound claim and query-index batch.

use keccak_hash::keccak;
use plonky2_field::goldilocks_field::GoldilocksField as F;
use plonky2_field::types::{Field, PrimeField64};
use plonky2_mle::commitment::whir_pcs::{
    WhirEvalProof, WhirNativeTraceEvent, WhirNativeTraceEventKind, WhirPCS, WHIR_SESSION_SPLIT,
};
use plonky2_mle::fixture::{try_fixture_from_json, Ext3Fixture, ProofFixture, SumcheckFixture};
use plonky2_mle::protocol_schema::{
    EXTENSION_FIELD_LIMBS, MLE_PROTOCOL_VERSION, NUM_PACKED_VECTORS_PER_GROUP, NUM_PCS_CLAIMS,
    NUM_PCS_TERMINAL_POINTS, NUM_SPLIT_COMMITMENTS, PACKED_PCS_SCHEMA_DOMAIN,
    PACKED_VARIABLE_ORDER_CODE,
};
use plonky2_mle::transcript::Transcript;

#[derive(serde::Deserialize, serde::Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct GoldenTrace {
    protocol_version: u64,
    source_fixture: String,
    preprocessed_batch: GoldenTraceTable,
    outer: GoldenTraceTable,
    whir_native: WhirNativeGoldenTrace,
}

#[derive(Debug, Eq, PartialEq, serde::Deserialize, serde::Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WhirNativeGoldenTrace {
    labels: Vec<String>,
    kinds: Vec<u8>,
    narg_positions: Vec<usize>,
    hint_positions: Vec<usize>,
    sponge_states: Vec<String>,
    squeeze_counters: Vec<u64>,
    event_bytes: Vec<String>,
    query_checkpoint_indices: Vec<usize>,
    query_offsets: Vec<usize>,
    query_indices: Vec<usize>,
}

#[derive(serde::Deserialize, serde::Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct GoldenTraceTable {
    labels: Vec<String>,
    state_lengths: Vec<usize>,
    squeeze_counters: Vec<u64>,
    state_digests: Vec<String>,
    absorbed_bytes: Vec<String>,
    challenge_checkpoint_indices: Vec<usize>,
    squeezed_challenges: Vec<String>,
}

struct TraceCheckpoint {
    label: String,
    state_length: usize,
    squeeze_counter: u64,
    state_digest: String,
    absorbed_bytes: String,
    squeezed_challenge: Option<String>,
}

fn table_from_trace(trace: &[TraceCheckpoint]) -> GoldenTraceTable {
    GoldenTraceTable {
        labels: trace.iter().map(|item| item.label.clone()).collect(),
        state_lengths: trace.iter().map(|item| item.state_length).collect(),
        squeeze_counters: trace.iter().map(|item| item.squeeze_counter).collect(),
        state_digests: trace.iter().map(|item| item.state_digest.clone()).collect(),
        absorbed_bytes: trace
            .iter()
            .map(|item| item.absorbed_bytes.clone())
            .collect(),
        challenge_checkpoint_indices: trace
            .iter()
            .enumerate()
            .filter_map(|(index, item)| item.squeezed_challenge.as_ref().map(|_| index))
            .collect(),
        squeezed_challenges: trace
            .iter()
            .filter_map(|item| item.squeezed_challenge.clone())
            .collect(),
    }
}

fn whir_native_table_from_trace(trace: &[WhirNativeTraceEvent]) -> WhirNativeGoldenTrace {
    let mut query_checkpoint_indices = Vec::new();
    let mut query_offsets = vec![0];
    let mut query_indices = Vec::new();
    for (checkpoint, event) in trace.iter().enumerate() {
        if event.kind == WhirNativeTraceEventKind::QueryIndices {
            query_checkpoint_indices.push(checkpoint);
            query_indices.extend_from_slice(&event.query_indices);
            query_offsets.push(query_indices.len());
        } else {
            assert!(
                event.query_indices.is_empty(),
                "non-query checkpoint carries indices: {}",
                event.label
            );
        }
    }
    WhirNativeGoldenTrace {
        labels: trace.iter().map(|event| event.label.clone()).collect(),
        kinds: trace.iter().map(|event| event.kind as u8).collect(),
        narg_positions: trace.iter().map(|event| event.narg_position).collect(),
        hint_positions: trace.iter().map(|event| event.hint_position).collect(),
        sponge_states: trace
            .iter()
            .map(|event| encode_hex(&event.sponge_state))
            .collect(),
        squeeze_counters: trace.iter().map(|event| event.squeeze_counter).collect(),
        event_bytes: trace
            .iter()
            .map(|event| encode_hex(&event.event_bytes))
            .collect(),
        query_checkpoint_indices,
        query_offsets,
        query_indices,
    }
}

fn assert_trace_table(golden: &GoldenTraceTable, trace: &[TraceCheckpoint], name: &str) {
    assert_eq!(golden.labels.len(), trace.len(), "{name} label count");
    assert_eq!(
        golden.state_lengths.len(),
        trace.len(),
        "{name} state-length count"
    );
    assert_eq!(
        golden.squeeze_counters.len(),
        trace.len(),
        "{name} squeeze-counter count"
    );
    assert_eq!(
        golden.state_digests.len(),
        trace.len(),
        "{name} state-digest count"
    );
    assert_eq!(
        golden.absorbed_bytes.len(),
        trace.len(),
        "{name} absorbed-byte count"
    );
    let generated = table_from_trace(trace);
    assert_eq!(
        golden.challenge_checkpoint_indices, generated.challenge_checkpoint_indices,
        "{name} challenge checkpoint indices"
    );
    assert_eq!(
        golden.squeezed_challenges, generated.squeezed_challenges,
        "{name} squeezed challenges"
    );
    for (index, item) in trace.iter().enumerate() {
        assert_eq!(
            golden.labels[index], item.label,
            "{name} label mismatch at checkpoint {index}"
        );
        assert_eq!(
            golden.state_lengths[index], item.state_length,
            "{name} state length mismatch at checkpoint {index}: {}",
            item.label
        );
        assert_eq!(
            golden.squeeze_counters[index], item.squeeze_counter,
            "{name} squeeze counter mismatch at checkpoint {index}: {}",
            item.label
        );
        assert_eq!(
            golden.state_digests[index], item.state_digest,
            "{name} state digest mismatch at checkpoint {index}: {}",
            item.label
        );
        assert_eq!(
            golden.absorbed_bytes[index], item.absorbed_bytes,
            "{name} absorbed bytes mismatch at checkpoint {index}: {}",
            item.label
        );
    }
}

fn field(value: &str) -> F {
    F::from_canonical_u64(value.parse().expect("decimal Goldilocks field"))
}

fn fields(values: &[String]) -> Vec<F> {
    values.iter().map(|value| field(value)).collect()
}

fn decode_hex(value: &str) -> Vec<u8> {
    let raw = value.strip_prefix("0x").unwrap_or(value);
    assert_eq!(raw.len() % 2, 0);
    (0..raw.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(&raw[index..index + 2], 16).unwrap())
        .collect()
}

fn encode_hex(value: &[u8]) -> String {
    let mut encoded = String::with_capacity(2 + value.len() * 2);
    encoded.push_str("0x");
    for byte in value {
        use std::fmt::Write;
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    encoded
}

fn point(values: &[Ext3Fixture]) -> Vec<F> {
    values
        .iter()
        .map(|value| {
            assert_eq!(value.c1, "0");
            assert_eq!(value.c2, "0");
            field(&value.c0)
        })
        .collect()
}

fn checkpoint(trace: &mut Vec<TraceCheckpoint>, label: impl Into<String>, transcript: &Transcript) {
    checkpoint_with_challenge(trace, label, transcript, None);
}

fn checkpoint_with_challenge(
    trace: &mut Vec<TraceCheckpoint>,
    label: impl Into<String>,
    transcript: &Transcript,
    challenge: Option<F>,
) {
    let previous_length = trace.last().map_or(0, |item| item.state_length);
    assert!(previous_length <= transcript.state_bytes().len());
    trace.push(TraceCheckpoint {
        label: label.into(),
        state_length: transcript.state_bytes().len(),
        squeeze_counter: transcript.current_squeeze_counter(),
        state_digest: format!("0x{:x}", keccak(transcript.state_bytes())),
        absorbed_bytes: encode_hex(&transcript.state_bytes()[previous_length..]),
        squeezed_challenge: challenge.map(|value| value.to_canonical_u64().to_string()),
    });
}

fn squeeze(
    transcript: &mut Transcript,
    expected: F,
    label: &str,
    trace: &mut Vec<TraceCheckpoint>,
) {
    let actual: F = transcript.squeeze_challenge();
    assert_eq!(actual, expected, "challenge mismatch at {label}");
    checkpoint_with_challenge(trace, label, transcript, Some(actual));
}

fn domain(
    transcript: &mut Transcript,
    label: &str,
    trace_label: &str,
    trace: &mut Vec<TraceCheckpoint>,
) {
    transcript.domain_separate(label);
    checkpoint(trace, format!("{trace_label}.domain"), transcript);
}

fn sumcheck(
    transcript: &mut Transcript,
    proof: &SumcheckFixture,
    expected_queries: &[F],
    prefix: &str,
    trace: &mut Vec<TraceCheckpoint>,
) {
    assert_eq!(proof.round_polys.len(), expected_queries.len());
    for (round, (evals, expected)) in proof.round_polys.iter().zip(expected_queries).enumerate() {
        domain(
            transcript,
            "sumcheck-round",
            &format!("{prefix}.round[{round}]"),
            trace,
        );
        transcript.absorb_field_vec(&fields(evals));
        checkpoint(
            trace,
            format!("{prefix}.round[{round}].message"),
            transcript,
        );
        squeeze(
            transcript,
            *expected,
            &format!("{prefix}.query[{round}]"),
            trace,
        );
    }
}

#[test]
fn test_v1_transcript_golden_trace() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/contracts/test/fixtures/small_mul.json"
    );
    let fixture: ProofFixture = try_fixture_from_json(&std::fs::read_to_string(path).unwrap())
        .expect("canonical packed-v1 source fixture");
    assert_eq!(fixture.protocol_version, MLE_PROTOCOL_VERSION);
    assert_eq!(fixture.whir_params.num_commitments, NUM_SPLIT_COMMITMENTS);
    assert_eq!(
        fixture.whir_params.num_vectors,
        NUM_PACKED_VECTORS_PER_GROUP
    );
    let index_bits = fixture.constituent_width.next_power_of_two().ilog2() as usize;
    assert_eq!(
        fixture.whir_params.num_variables,
        fixture.degree_bits + index_bits
    );
    let whir_proof = WhirEvalProof {
        narg_string: decode_hex(&fixture.whir_transcript),
        hints: decode_hex(&fixture.whir_hints),
        #[cfg(debug_assertions)]
        pattern: Vec::new(),
    };
    let whir_pcs = WhirPCS::for_constituents_v1(
        fixture.whir_params.num_variables,
        NUM_PACKED_VECTORS_PER_GROUP,
    );
    let whir_native_trace = whir_pcs
        .trace_grouped_preflight(
            fixture.whir_params.num_variables,
            &whir_proof,
            WHIR_SESSION_SPLIT,
            NUM_SPLIT_COMMITMENTS,
            NUM_PCS_CLAIMS,
        )
        .expect("production grouped-WHIR preflight trace");
    assert_eq!(
        whir_native_trace.last().map(|event| event.kind),
        Some(WhirNativeTraceEventKind::Eof),
        "WHIR native trace must end at exact EOF"
    );
    assert_eq!(
        whir_native_trace.last().map(|event| event.narg_position),
        Some(whir_proof.narg_string.len()),
        "WHIR native NARG cursor"
    );
    assert_eq!(
        whir_native_trace.last().map(|event| event.hint_position),
        Some(whir_proof.hints.len()),
        "WHIR native hint cursor"
    );
    assert_eq!(
        whir_native_trace
            .iter()
            .filter(|event| event.kind == WhirNativeTraceEventKind::QueryIndices)
            .count(),
        fixture.whir_params.num_rounds + 1,
        "one query-index checkpoint per opened codeword"
    );
    for claim in 0..NUM_PCS_CLAIMS {
        let label = format!("initial.statement.claim[{claim}]");
        let matching: Vec<_> = whir_native_trace
            .iter()
            .filter(|event| event.label == label)
            .collect();
        assert_eq!(matching.len(), 1, "each bound claim is absorbed once");
        assert_eq!(matching[0].event_bytes.len(), 24, "bound claim is Ext3");
    }
    let expected_roots = [
        decode_hex(&fixture.preprocessed_commitment_root),
        decode_hex(&fixture.witness_commitment_root),
        decode_hex(&fixture.inverse_helpers_commitment_root),
        decode_hex(&fixture.aux_commitment_root),
    ];
    for (group, expected_root) in expected_roots.iter().enumerate() {
        for suffix in ["root", "bound_root"] {
            let label = format!("initial.group[{group}].{suffix}");
            let matching: Vec<_> = whir_native_trace
                .iter()
                .filter(|event| event.label == label)
                .collect();
            assert_eq!(matching.len(), 1, "each root copy is absorbed once");
            assert_eq!(
                matching[0].event_bytes.as_slice(),
                expected_root.as_slice(),
                "root byte order"
            );
        }
    }

    // `preprocessedBatchR` is derived in a dedicated prover/verifier
    // mini-transcript. Its committed root is absorbed before the challenge.
    // Keep that exported challenge in the same golden artifact even though it
    // is not part of the outer transcript.
    let mut preprocessed_batch_trace = Vec::new();
    let mut preprocessed_batch_transcript = Transcript::new();
    checkpoint(
        &mut preprocessed_batch_trace,
        "protocol",
        &preprocessed_batch_transcript,
    );
    domain(
        &mut preprocessed_batch_transcript,
        "preprocessed-batch-r",
        "preprocessed",
        &mut preprocessed_batch_trace,
    );
    preprocessed_batch_transcript.absorb_field_vec(&fields(&fixture.circuit_digest));
    checkpoint(
        &mut preprocessed_batch_trace,
        "preprocessed.circuit_digest",
        &preprocessed_batch_transcript,
    );
    preprocessed_batch_transcript.absorb_bytes(&decode_hex(&fixture.preprocessed_commitment_root));
    checkpoint(
        &mut preprocessed_batch_trace,
        "preprocessed.root",
        &preprocessed_batch_transcript,
    );
    squeeze(
        &mut preprocessed_batch_transcript,
        field(&fixture.preprocessed_batch_r),
        "preprocessed.batch_r",
        &mut preprocessed_batch_trace,
    );

    let mut trace = Vec::new();
    let mut transcript = Transcript::new();
    checkpoint(&mut trace, "protocol", &transcript);

    domain(&mut transcript, "circuit", "circuit", &mut trace);
    transcript.absorb_field_vec(&fields(&fixture.circuit_digest));
    checkpoint(&mut trace, "circuit.digest", &transcript);
    transcript.absorb_field_vec(&fields(&fixture.public_inputs));
    checkpoint(&mut trace, "circuit.public_inputs", &transcript);

    domain(
        &mut transcript,
        PACKED_PCS_SCHEMA_DOMAIN,
        "pcs.schema",
        &mut trace,
    );
    for (index, value) in [
        fixture.protocol_version,
        NUM_SPLIT_COMMITMENTS as u64,
        fixture.num_constants as u64,
        fixture.num_routed_wires as u64,
        fixture.num_wires as u64,
        fixture.constituent_width as u64,
        index_bits as u64,
        NUM_PACKED_VECTORS_PER_GROUP as u64,
        EXTENSION_FIELD_LIMBS as u64,
        PACKED_VARIABLE_ORDER_CODE as u64,
    ]
    .into_iter()
    .enumerate()
    {
        transcript.absorb_bytes(&value.to_le_bytes());
        checkpoint(&mut trace, format!("pcs.schema[{index}]"), &transcript);
    }

    domain(
        &mut transcript,
        "pcs-group-preprocessed",
        "pcs.preprocessed",
        &mut trace,
    );
    transcript.absorb_bytes(&decode_hex(&fixture.preprocessed_commitment_root));
    checkpoint(&mut trace, "pcs.root.preprocessed", &transcript);
    domain(
        &mut transcript,
        "pcs-group-witness",
        "pcs.witness",
        &mut trace,
    );
    transcript.absorb_bytes(&decode_hex(&fixture.witness_commitment_root));
    checkpoint(&mut trace, "pcs.root.witness", &transcript);

    domain(
        &mut transcript,
        "batch-commit-witness",
        "rho.witness",
        &mut trace,
    );
    squeeze(
        &mut transcript,
        field(&fixture.witness_batch_r),
        "rho.witness",
        &mut trace,
    );
    domain(&mut transcript, "challenges", "base", &mut trace);
    squeeze(&mut transcript, field(&fixture.beta), "beta", &mut trace);
    squeeze(&mut transcript, field(&fixture.gamma), "gamma", &mut trace);

    domain(
        &mut transcript,
        "pcs-group-inverse-helpers",
        "pcs.inverse",
        &mut trace,
    );
    transcript.absorb_bytes(&decode_hex(&fixture.inverse_helpers_commitment_root));
    checkpoint(&mut trace, "pcs.root.inverse", &transcript);
    domain(
        &mut transcript,
        "inverse-helpers-batch-r",
        "rho.inverse",
        &mut trace,
    );
    squeeze(
        &mut transcript,
        field(&fixture.inverse_helpers_batch_r),
        "rho.inverse",
        &mut trace,
    );
    squeeze(&mut transcript, field(&fixture.alpha), "alpha", &mut trace);
    domain(
        &mut transcript,
        "extension-combine",
        "extension",
        &mut trace,
    );
    squeeze(
        &mut transcript,
        field(&fixture.ext_challenge),
        "extension",
        &mut trace,
    );
    domain(
        &mut transcript,
        "pcs-group-auxiliary",
        "pcs.auxiliary",
        &mut trace,
    );
    transcript.absorb_bytes(&decode_hex(&fixture.aux_commitment_root));
    checkpoint(&mut trace, "pcs.root.auxiliary", &transcript);
    domain(&mut transcript, "aux-batch-r", "rho.auxiliary", &mut trace);
    squeeze(
        &mut transcript,
        field(&fixture.aux_batch_r),
        "rho.auxiliary",
        &mut trace,
    );
    domain(
        &mut transcript,
        "post-auxiliary-challenges-v1",
        "post_auxiliary",
        &mut trace,
    );
    for (i, expected) in fields(&fixture.tau).into_iter().enumerate() {
        squeeze(&mut transcript, expected, &format!("tau[{i}]"), &mut trace);
    }
    for (i, expected) in fields(&fixture.tau_perm).into_iter().enumerate() {
        squeeze(
            &mut transcript,
            expected,
            &format!("tau_perm[{i}]"),
            &mut trace,
        );
    }

    domain(&mut transcript, "v2-logup-challenges", "logup", &mut trace);
    squeeze(
        &mut transcript,
        field(&fixture.lambda_inv),
        "lambda_inv",
        &mut trace,
    );
    squeeze(
        &mut transcript,
        field(&fixture.mu_inv),
        "mu_inv",
        &mut trace,
    );
    for (i, expected) in fields(&fixture.tau_inv).into_iter().enumerate() {
        squeeze(
            &mut transcript,
            expected,
            &format!("tau_inv[{i}]"),
            &mut trace,
        );
    }

    domain(&mut transcript, "combined-sumcheck", "combined", &mut trace);
    squeeze(&mut transcript, field(&fixture.mu), "mu", &mut trace);

    sumcheck(
        &mut transcript,
        &fixture.combined_proof,
        &point(&fixture.evaluation_point),
        "combined",
        &mut trace,
    );
    domain(&mut transcript, "v2-inv-zerocheck", "inverse", &mut trace);
    sumcheck(
        &mut transcript,
        &fixture.inv_sumcheck_proof,
        &fields(&fixture.inv_sumcheck_challenges),
        "inverse",
        &mut trace,
    );
    domain(&mut transcript, "v2-h-linear", "h", &mut trace);
    sumcheck(
        &mut transcript,
        &fixture.h_sumcheck_proof,
        &fields(&fixture.h_sumcheck_challenges),
        "h",
        &mut trace,
    );
    domain(
        &mut transcript,
        "v2-gate-challenges",
        "gate.challenge",
        &mut trace,
    );
    for (i, expected) in fields(&fixture.tau_gate).into_iter().enumerate() {
        squeeze(
            &mut transcript,
            expected,
            &format!("tau_gate[{i}]"),
            &mut trace,
        );
    }
    domain(&mut transcript, "v2-gate-zerocheck", "gate", &mut trace);
    sumcheck(
        &mut transcript,
        &fixture.gate_sumcheck_proof,
        &fields(&fixture.gate_sumcheck_challenges),
        "gate",
        &mut trace,
    );
    domain(&mut transcript, "pcs-eval", "pcs.eval", &mut trace);

    let empty: Vec<F> = Vec::new();
    let aux = vec![
        field(&fixture.aux_constraint_eval),
        field(&fixture.aux_perm_eval),
    ];
    let claim_vectors: [Vec<F>; NUM_PCS_CLAIMS] = [
        fields(&fixture.preprocessed_individual_evals),
        fields(&fixture.witness_individual_evals),
        empty.clone(),
        aux,
        fields(&fixture.preprocessed_individual_evals_at_r_inv),
        fields(&fixture.witness_individual_evals_at_r_inv),
        fields(&fixture.inverse_helpers_evals_at_r_inv),
        empty.clone(),
        empty.clone(),
        empty.clone(),
        fields(&fixture.inverse_helpers_evals_at_r_h),
        empty.clone(),
        fields(&fixture.preprocessed_individual_evals_at_r_gate_v2),
        fields(&fixture.witness_individual_evals_at_r_gate_v2),
        empty.clone(),
        empty,
    ];
    domain(
        &mut transcript,
        "pcs-constituent-claims-v1",
        "pcs.claims",
        &mut trace,
    );
    for (claim_index, values) in claim_vectors.iter().enumerate() {
        transcript.absorb_field_vec(values);
        checkpoint(&mut trace, format!("pcs.claim[{claim_index}]"), &transcript);
    }

    domain(
        &mut transcript,
        "pcs-constituent-index-v1",
        "pcs.index",
        &mut trace,
    );
    for point_index in 0..NUM_PCS_TERMINAL_POINTS {
        for bit in 0..index_bits {
            for limb in 0..EXTENSION_FIELD_LIMBS {
                let challenge: F = transcript.squeeze_challenge();
                checkpoint_with_challenge(
                    &mut trace,
                    format!("pcs.index[{point_index}][{bit}].c{limb}"),
                    &transcript,
                    Some(challenge),
                );
            }
        }
    }

    let golden_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/contracts/test/fixtures/transcript_v1_trace.json"
    );
    let generated = GoldenTrace {
        protocol_version: MLE_PROTOCOL_VERSION,
        source_fixture: "small_mul.json".to_string(),
        preprocessed_batch: table_from_trace(&preprocessed_batch_trace),
        outer: table_from_trace(&trace),
        whir_native: whir_native_table_from_trace(&whir_native_trace),
    };
    if std::env::var_os("MLE_WRITE_TRANSCRIPT_TRACE").as_deref() == Some(std::ffi::OsStr::new("1"))
    {
        let mut json = serde_json::to_string_pretty(&generated).unwrap();
        json.push('\n');
        std::fs::write(golden_path, json).unwrap();
    }
    let golden: GoldenTrace =
        serde_json::from_str(&std::fs::read_to_string(golden_path).unwrap()).unwrap();
    assert_eq!(golden.protocol_version, MLE_PROTOCOL_VERSION);
    assert_eq!(golden.source_fixture, "small_mul.json");
    assert_eq!(
        preprocessed_batch_trace.len(),
        5,
        "mini-transcript table changed"
    );
    assert_eq!(trace.len(), 192, "checkpoint table changed");
    assert_trace_table(
        &golden.preprocessed_batch,
        &preprocessed_batch_trace,
        "preprocessed batch",
    );
    assert_trace_table(&golden.outer, &trace, "outer");
    assert_eq!(
        golden.whir_native,
        whir_native_table_from_trace(&whir_native_trace),
        "WHIR native production-preflight trace drift"
    );
}
