//! Canonical cross-language fixture for the security-amplified MLE/WHIR v2
//! protocol.
//!
//! The checked-in JSON is intentionally self-contained: it pins every field
//! of the v2 verification key, the compact proof bytes, the ordered outer
//! transcript domain states and Ext3 challenges, the two packed PCS points,
//! all six point-major claims, and both terminal equations.  Additional gate
//! families can be appended to the top-level `cases` array without changing
//! the schema.

use std::fmt::Write as _;

use ark_ff::{AdditiveGroup, Field as ArkField, PrimeField as ArkPrimeField};
use keccak_hash::keccak;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData};
use plonky2::plonk::config::{Hasher, PoseidonGoldilocksConfig};
use plonky2::util::timing::TimingTree;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use plonky2_mle::commitment::whir_pcs::{WhirNativeTraceEvent, WhirNativeTraceEventKind, WhirPCS};
use plonky2_mle::compact_v2::{decode_compact_v2, encode_compact_v2, CompactV2Error};
use plonky2_mle::fixture::WhirParamsFixture;
use plonky2_mle::fixture_v2::{
    compact_v2_shape_for_common, derive_whir_deployment_profile_v2, try_export_mle_v2_fixture,
    CompactV2ShapeFixture as CompactShapeRecord, EncodedProofV2Fixture as CompactProofRecord,
    MleVerificationKeyV2Fixture as VerificationKeyRecord, ProofEncodingSizeUpperBoundV2,
};
use plonky2_mle::gate_ext3::evaluate_gate_aggregation_ext3;
use plonky2_mle::permutation::norm_logup::{
    evaluate_joint_norm_logup_terminal_with_public_inputs, NormLogupChallenges,
};
use plonky2_mle::proof_v2::{
    constituent_index_bits_v2, packed_group_num_vars_v2, MleProofV2, MleVerificationKeyV2,
};
use plonky2_mle::protocol_schema_v2::{
    BASE_FIELD_MODULUS_V2, COMPACT_MAGIC_V2, DOMAIN_CIRCUIT_CONFIG_DIGEST_V2,
    DOMAIN_CIRCUIT_STATEMENT_V2, DOMAIN_CONSTITUENT_CLAIMS_V2, DOMAIN_CONSTITUENT_INDEX_V2,
    DOMAIN_GROUP_NORM_INVERSE_V2, DOMAIN_GROUP_PREPROCESSED_V2, DOMAIN_GROUP_WITNESS_V2,
    DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2, DOMAIN_OUTER_RELATION_CHALLENGES_V2,
    DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2, DOMAIN_OUTER_SUMCHECK_ROUND_V2,
    DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2, DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2,
    DOMAIN_WHIR_PROTOCOL_ID_V2, DOMAIN_WHIR_SESSION_ID_V2, EXTENSION_FIELD_LIMBS_V2,
    EXTENSION_NON_RESIDUE_V2, GATE_SUMCHECK_COUNT_V2, INNER_EXTENSION_NON_RESIDUE_V2,
    LOG_ROUND_DEGREE_V2, MLE_PROTOCOL_VERSION_CURRENT, NUM_PACKED_VECTORS_PER_GROUP_V2,
    NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2, NUM_PCS_TERMINAL_POINTS_V2, OUTER_TRANSCRIPT_PROTOCOL_V2,
    PACKED_BOUND_CLAIM_MASK_V2, PACKED_PCS_SCHEMA_DOMAIN_V2, PACKED_VARIABLE_ORDER_CODE_V2,
    TAG_BYTES_V2, TAG_DOMAIN_V2, TAG_EXT3_V2, TAG_EXT3_VEC_V2, TAG_FIELD_V2, TAG_FIELD_VEC_V2,
    TRANSCRIPT_CHALLENGE_PREFIX_V2, TRANSCRIPT_FRAME_PREFIX_V2, WHIR_SESSION_SPLIT_V2,
};
use plonky2_mle::prover_v2::{mle_prove_v2, mle_setup_v2};
use plonky2_mle::sumcheck::coefficients::evaluate_ext3_coefficient_round;
use plonky2_mle::sumcheck::gate_ext3_v2::ext3_eq_eval;
use plonky2_mle::transcript_v2::TranscriptV2;
use plonky2_mle::verifier_v2::mle_verify_v2;
use plonky2_mle::vk_v2::decode_public_input_wire_map_v2;
use serde::{Deserialize, Serialize};
use whir::algebra::fields::Field64_3;

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;
const EXPECTED_FIXTURE_KECCAK: &str =
    "0x8c4de7a4b6cae1663eaec8accf9aa0b4e1ec06778411550859d0a4863f6211b3";
const EXPECTED_SOLIDITY_ABI_PROOF_BYTES: usize = 118_528;
const EXPECTED_SOLIDITY_ABI_PROOF_KECCAK: &str =
    "0x388b52d7a548d08e51455df44faeb830a3eb7f59e1cee50830ef8e7812620e23";
const EXPECTED_SOLIDITY_ABI_CONFIG_BYTES: usize = 5_664;
const EXPECTED_SOLIDITY_ABI_CONFIG_KECCAK: &str =
    "0x61c7fcecfd5b6839926e2579bde990144cfcdc9b3e2f0f24f0f72b3aa2094c9f";
type Ext3Record = [String; 3];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CrossLanguageFixture {
    schema: String,
    version: u64,
    field: FieldSchema,
    point_order: [String; 2],
    group_order: [String; 3],
    cases: Vec<CaseRecord>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FieldSchema {
    modulus: String,
    ext3_polynomial: String,
    inner_extension_non_residue: String,
    ext3_limb_order: [String; 3],
    compact_limb_byte_order: String,
    transcript_initial_state: String,
    transcript_frame_prefix: String,
    transcript_challenge_prefix: String,
    transcript_tags: TranscriptTagRecord,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TranscriptTagRecord {
    domain: u8,
    bytes: u8,
    field: u8,
    field_vec: u8,
    ext3: u8,
    ext3_vec: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CaseRecord {
    name: String,
    circuit: CircuitRecord,
    verification_key: VerificationKeyRecord,
    solidity_abi_proof: CompactProofRecord,
    solidity_abi_verification_config: CompactProofRecord,
    whir_params: WhirParamsFixture,
    whir_native: WhirNativeTraceRecord,
    whir_evaluations: Vec<Ext3Record>,
    compact_shape: CompactShapeRecord,
    compact_proof: CompactProofRecord,
    size_upper_bound: ProofEncodingSizeUpperBoundV2,
    compact_negative_cases: Vec<CompactNegativeCaseRecord>,
    packed_claim_mask: String,
    outer_transcript: Vec<TranscriptEventRecord>,
    packed_points: Vec<PackedPointRecord>,
    packed_claims: Vec<PackedClaimRecord>,
    terminals: TerminalRecord,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WhirNativeTraceRecord {
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CircuitRecord {
    builder: String,
    relation: String,
    chain_length: usize,
    witness_x: String,
    expected_public_inputs: Vec<String>,
    degree_bits: usize,
    num_public_inputs: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CompactNegativeCaseRecord {
    name: String,
    operation: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    offset: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    new_length: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<String>,
    expected_error: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TranscriptEventRecord {
    kind: String,
    label: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    tag: Option<u8>,
    #[serde(skip_serializing_if = "Option::is_none")]
    domain: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    payload: Option<String>,
    state: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    squeeze_counter_before: Option<u64>,
    squeeze_counter: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    challenge: Option<Ext3Record>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PackedPointRecord {
    name: String,
    row_point: Vec<Ext3Record>,
    constituent_index_point: Vec<Ext3Record>,
    packed_point: Vec<Ext3Record>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PackedClaimRecord {
    point_index: usize,
    group_index: usize,
    point: String,
    group: String,
    used: bool,
    value: Option<Ext3Record>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TerminalRecord {
    public_inputs_hash: [String; 4],
    subgroup_evaluation_at_log_point: Ext3Record,
    log_final_claim: Ext3Record,
    log_terminal: Ext3Record,
    gate_final_claim: Ext3Record,
    gate_constraint_aggregation: Ext3Record,
    gate_eq_evaluation: Ext3Record,
    gate_expected_final_claim: Ext3Record,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DerivedRecord {
    outer_transcript: Vec<TranscriptEventRecord>,
    packed_points: Vec<PackedPointRecord>,
    packed_claims: Vec<PackedClaimRecord>,
    terminals: TerminalRecord,
}

struct TranscriptRecorder {
    transcript: TranscriptV2,
    events: Vec<TranscriptEventRecord>,
}

impl TranscriptRecorder {
    fn new() -> Self {
        let transcript = TranscriptV2::new();
        let event = TranscriptEventRecord {
            kind: "domain".to_string(),
            label: "protocol".to_string(),
            tag: Some(TAG_DOMAIN_V2),
            domain: Some(OUTER_TRANSCRIPT_PROTOCOL_V2.to_string()),
            payload: Some(encode_hex(OUTER_TRANSCRIPT_PROTOCOL_V2.as_bytes())),
            state: encode_hex(&transcript.state_digest()),
            squeeze_counter_before: None,
            squeeze_counter: transcript.current_squeeze_counter(),
            challenge: None,
        };
        Self {
            transcript,
            events: vec![event],
        }
    }

    fn domain(&mut self, label: impl Into<String>, domain: &str) {
        self.transcript.domain_separate(domain);
        self.events.push(TranscriptEventRecord {
            kind: "domain".to_string(),
            label: label.into(),
            tag: Some(TAG_DOMAIN_V2),
            domain: Some(domain.to_string()),
            payload: Some(encode_hex(domain.as_bytes())),
            state: encode_hex(&self.transcript.state_digest()),
            squeeze_counter_before: None,
            squeeze_counter: self.transcript.current_squeeze_counter(),
            challenge: None,
        });
    }

    fn absorb_bytes(&mut self, label: impl Into<String>, bytes: &[u8]) {
        self.transcript.absorb_bytes(bytes);
        self.events.push(TranscriptEventRecord {
            kind: "absorbBytes".to_string(),
            label: label.into(),
            tag: Some(TAG_BYTES_V2),
            domain: None,
            payload: Some(encode_hex(bytes)),
            state: encode_hex(&self.transcript.state_digest()),
            squeeze_counter_before: None,
            squeeze_counter: self.transcript.current_squeeze_counter(),
            challenge: None,
        });
    }

    fn absorb_field_vec(&mut self, label: impl Into<String>, values: &[F]) {
        let mut payload = Vec::with_capacity(8 + 8 * values.len());
        payload.extend_from_slice(&(values.len() as u64).to_le_bytes());
        for value in values {
            payload.extend_from_slice(&value.to_canonical_u64().to_le_bytes());
        }
        self.transcript.absorb_field_vec(values);
        self.events.push(TranscriptEventRecord {
            kind: "absorbFieldVec".to_string(),
            label: label.into(),
            tag: Some(TAG_FIELD_VEC_V2),
            domain: None,
            payload: Some(encode_hex(&payload)),
            state: encode_hex(&self.transcript.state_digest()),
            squeeze_counter_before: None,
            squeeze_counter: self.transcript.current_squeeze_counter(),
            challenge: None,
        });
    }

    fn absorb_ext3_vec(&mut self, label: impl Into<String>, values: &[Field64_3]) {
        let mut payload = Vec::with_capacity(8 + 24 * values.len());
        payload.extend_from_slice(&(values.len() as u64).to_le_bytes());
        for value in values {
            for limb in [value.c0, value.c1, value.c2] {
                payload.extend_from_slice(&limb.into_bigint().0[0].to_le_bytes());
            }
        }
        self.transcript.absorb_ext3_vec(values);
        self.events.push(TranscriptEventRecord {
            kind: "absorbExt3Vec".to_string(),
            label: label.into(),
            tag: Some(TAG_EXT3_VEC_V2),
            domain: None,
            payload: Some(encode_hex(&payload)),
            state: encode_hex(&self.transcript.state_digest()),
            squeeze_counter_before: None,
            squeeze_counter: self.transcript.current_squeeze_counter(),
            challenge: None,
        });
    }

    fn checkpoint(&mut self, label: impl Into<String>) {
        self.events.push(TranscriptEventRecord {
            kind: "checkpoint".to_string(),
            label: label.into(),
            tag: None,
            domain: None,
            payload: None,
            state: encode_hex(&self.transcript.state_digest()),
            squeeze_counter_before: None,
            squeeze_counter: self.transcript.current_squeeze_counter(),
            challenge: None,
        });
    }

    fn squeeze_ext3(&mut self, label: impl Into<String>) -> Field64_3 {
        let squeeze_counter_before = self.transcript.current_squeeze_counter();
        let challenge = self.transcript.squeeze_ext3::<F>();
        self.events.push(TranscriptEventRecord {
            kind: "squeezeExt3".to_string(),
            label: label.into(),
            tag: None,
            domain: None,
            payload: None,
            state: encode_hex(&self.transcript.state_digest()),
            squeeze_counter_before: Some(squeeze_counter_before),
            squeeze_counter: self.transcript.current_squeeze_counter(),
            challenge: Some(encode_ext3(challenge)),
        });
        challenge
    }
}

fn encode_limb(value: u64) -> String {
    format!("0x{value:016x}")
}

fn encode_base(value: &F) -> String {
    encode_limb(value.to_canonical_u64())
}

fn encode_ext3(value: Field64_3) -> Ext3Record {
    [
        encode_limb(value.c0.into_bigint().0[0]),
        encode_limb(value.c1.into_bigint().0[0]),
        encode_limb(value.c2.into_bigint().0[0]),
    ]
}

fn encode_hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(2 + 2 * bytes.len());
    encoded.push_str("0x");
    for byte in bytes {
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    encoded
}

fn whir_native_record(trace: &[WhirNativeTraceEvent]) -> WhirNativeTraceRecord {
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
                "non-query WHIR checkpoint carries indices: {}",
                event.label
            );
        }
    }
    WhirNativeTraceRecord {
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

fn whir_bound_evaluations(trace: &[WhirNativeTraceEvent]) -> Vec<Ext3Record> {
    trace
        .iter()
        .filter(|event| event.label.starts_with("initial.statement.claim["))
        .map(|event| {
            assert_eq!(event.kind, WhirNativeTraceEventKind::Absorb);
            assert_eq!(event.event_bytes.len(), 24, "WHIR bound Ext3 width");
            [
                encode_limb(u64::from_le_bytes(
                    event.event_bytes[0..8].try_into().unwrap(),
                )),
                encode_limb(u64::from_le_bytes(
                    event.event_bytes[8..16].try_into().unwrap(),
                )),
                encode_limb(u64::from_le_bytes(
                    event.event_bytes[16..24].try_into().unwrap(),
                )),
            ]
        })
        .collect()
}

fn decode_hex(value: &str) -> Vec<u8> {
    let digits = value.strip_prefix("0x").expect("bytes must have 0x prefix");
    assert_eq!(digits.len() % 2, 0, "hex byte string must have even length");
    assert!(
        digits
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "bytes must be lowercase canonical hex"
    );
    (0..digits.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(&digits[index..index + 2], 16).unwrap())
        .collect()
}

fn decode_fixed_hex<const N: usize>(value: &str) -> [u8; N] {
    let bytes = decode_hex(value);
    assert_eq!(bytes.len(), N, "fixed byte string has the wrong length");
    bytes.try_into().expect("length checked above")
}

fn apply_compact_mutation(encoded: &[u8], mutation: &CompactNegativeCaseRecord) -> Vec<u8> {
    let mut mutated = encoded.to_vec();
    match mutation.operation.as_str() {
        "replace" => {
            let offset = mutation.offset.expect("replace mutation offset");
            let data = decode_hex(mutation.data.as_deref().expect("replace mutation data"));
            let end = offset.checked_add(data.len()).expect("replace end");
            assert!(end <= mutated.len(), "replace mutation is in bounds");
            mutated[offset..end].copy_from_slice(&data);
        }
        "truncate" => {
            assert!(mutation.offset.is_none() && mutation.data.is_none());
            mutated.truncate(mutation.new_length.expect("truncate mutation length"));
        }
        "append" => {
            assert!(mutation.offset.is_none() && mutation.new_length.is_none());
            mutated.extend_from_slice(&decode_hex(
                mutation.data.as_deref().expect("append mutation data"),
            ));
        }
        other => panic!("unknown compact mutation operation {other}"),
    }
    mutated
}

fn assert_expected_compact_error(error: CompactV2Error, expected: &str) {
    match (expected, error) {
        ("wrongProtocolVersion:2", CompactV2Error::WrongProtocolVersion { got: 2 })
        | ("unexpectedEof", CompactV2Error::UnexpectedEof { .. })
        | ("trailingBytes:1", CompactV2Error::TrailingBytes { count: 1 })
        | (
            "nonCanonicalGoldilocks:offset20",
            CompactV2Error::NonCanonicalGoldilocks {
                offset: 20,
                value: BASE_FIELD_MODULUS_V2,
            },
        ) => {}
        (_, actual) => panic!("expected compact-v2 error {expected}, got {actual}"),
    }
}

fn reduce_challenge(bytes: &[u8]) -> u64 {
    assert_eq!(bytes.len(), 32);
    let radix = F::from_noncanonical_u96((0, 1));
    let chunks = bytes.chunks_exact(8);
    assert!(chunks.remainder().is_empty());
    chunks
        .rev()
        .fold(F::ZERO, |acc, chunk| {
            let limb = u64::from_le_bytes(chunk.try_into().expect("eight-byte challenge limb"));
            acc * radix + F::from_noncanonical_u64(limb)
        })
        .to_canonical_u64()
}

fn assert_byte_exact_transcript(field: &FieldSchema, events: &[TranscriptEventRecord]) {
    let frame_prefix = decode_hex(&field.transcript_frame_prefix);
    let challenge_prefix = decode_hex(&field.transcript_challenge_prefix);
    let mut state = decode_fixed_hex::<32>(&field.transcript_initial_state);
    let mut squeeze_counter = 0u64;

    for (event_index, event) in events.iter().enumerate() {
        match event.kind.as_str() {
            "domain" | "absorbBytes" | "absorbFieldVec" | "absorbExt3Vec" => {
                let expected_tag = match event.kind.as_str() {
                    "domain" => field.transcript_tags.domain,
                    "absorbBytes" => field.transcript_tags.bytes,
                    "absorbFieldVec" => field.transcript_tags.field_vec,
                    "absorbExt3Vec" => field.transcript_tags.ext3_vec,
                    _ => unreachable!(),
                };
                assert_eq!(event.tag, Some(expected_tag), "tag at event {event_index}");
                let payload = decode_hex(
                    event
                        .payload
                        .as_deref()
                        .expect("absorption event must carry its exact payload"),
                );
                if event.kind == "domain" {
                    assert_eq!(
                        payload,
                        event.domain.as_deref().unwrap().as_bytes(),
                        "domain payload at event {event_index}"
                    );
                }
                let mut preimage =
                    Vec::with_capacity(frame_prefix.len() + state.len() + 1 + 8 + payload.len());
                preimage.extend_from_slice(&frame_prefix);
                preimage.extend_from_slice(&state);
                preimage.push(expected_tag);
                preimage.extend_from_slice(&(payload.len() as u64).to_le_bytes());
                preimage.extend_from_slice(&payload);
                state.copy_from_slice(keccak(&preimage).as_ref());
                squeeze_counter = 0;
            }
            "squeezeExt3" => {
                assert!(event.tag.is_none());
                assert!(event.payload.is_none());
                assert_eq!(
                    event.squeeze_counter_before,
                    Some(squeeze_counter),
                    "pre-squeeze counter at event {event_index}"
                );
                let mut limbs = [String::new(), String::new(), String::new()];
                for limb in &mut limbs {
                    let mut preimage = Vec::with_capacity(challenge_prefix.len() + state.len() + 8);
                    preimage.extend_from_slice(&challenge_prefix);
                    preimage.extend_from_slice(&state);
                    preimage.extend_from_slice(&squeeze_counter.to_le_bytes());
                    *limb = encode_limb(reduce_challenge(keccak(&preimage).as_ref()));
                    squeeze_counter += 1;
                }
                assert_eq!(
                    event.challenge.as_ref(),
                    Some(&limbs),
                    "Ext3 challenge at event {event_index}"
                );
            }
            "checkpoint" => {
                assert!(event.tag.is_none());
                assert!(event.payload.is_none());
                assert!(event.challenge.is_none());
            }
            other => panic!("unknown transcript event kind {other}"),
        }
        assert_eq!(
            event.state,
            encode_hex(&state),
            "state at transcript event {event_index}: {}",
            event.label
        );
        assert_eq!(
            event.squeeze_counter, squeeze_counter,
            "counter at transcript event {event_index}: {}",
            event.label
        );
    }
}

fn fold_ext3_claim(values: &[Field64_3], width: usize, point: &[Field64_3]) -> Field64_3 {
    assert!(values.len() <= width);
    assert_eq!(point.len(), constituent_index_bits_v2(width));
    let mut layer = vec![Field64_3::ZERO; width.next_power_of_two()];
    layer[..values.len()].copy_from_slice(values);
    for &challenge in point {
        for index in 0..layer.len() / 2 {
            layer[index] = layer[2 * index] + challenge * (layer[2 * index + 1] - layer[2 * index]);
        }
        layer.truncate(layer.len() / 2);
    }
    layer[0]
}

fn derive_records(
    common: &CommonCircuitData<F, D>,
    vk: &MleVerificationKeyV2<F>,
    proof: &MleProofV2<F>,
) -> DerivedRecord {
    let degree_bits = common.degree_bits();
    let mut trace = TranscriptRecorder::new();

    trace.domain("statement", DOMAIN_CIRCUIT_STATEMENT_V2);
    trace.absorb_field_vec("statement.circuitDigest", &proof.circuit_digest);
    trace.absorb_field_vec("statement.publicInputs", &proof.public_inputs);

    trace.domain("schema", PACKED_PCS_SCHEMA_DOMAIN_V2);
    let metadata = [
        MLE_PROTOCOL_VERSION_CURRENT,
        NUM_PCS_GROUPS_V2 as u64,
        NUM_PCS_TERMINAL_POINTS_V2 as u64,
        NUM_PCS_CLAIMS_V2 as u64,
        common.num_constants as u64,
        common.config.num_routed_wires as u64,
        common.config.num_wires as u64,
        degree_bits as u64,
        vk.constituent_width as u64,
        constituent_index_bits_v2(vk.constituent_width) as u64,
        NUM_PACKED_VECTORS_PER_GROUP_V2 as u64,
        EXTENSION_FIELD_LIMBS_V2 as u64,
        PACKED_VARIABLE_ORDER_CODE_V2 as u64,
        GATE_SUMCHECK_COUNT_V2 as u64,
        LOG_ROUND_DEGREE_V2 as u64,
    ];
    let mut encoded_metadata = Vec::with_capacity(metadata.len() * 8);
    for value in metadata {
        encoded_metadata.extend_from_slice(&value.to_le_bytes());
    }
    trace.absorb_bytes("schema.metadata", &encoded_metadata);

    trace.domain("circuitConfigDigest", DOMAIN_CIRCUIT_CONFIG_DIGEST_V2);
    trace.absorb_bytes("circuitConfigDigest.value", &vk.circuit_config_digest);
    trace.domain("whirProtocolId", DOMAIN_WHIR_PROTOCOL_ID_V2);
    trace.absorb_bytes("whirProtocolId.value", &vk.whir_protocol_id);
    trace.domain("whirSessionId", DOMAIN_WHIR_SESSION_ID_V2);
    trace.absorb_bytes("whirSessionId.value", &vk.whir_session_id);
    trace.domain("preprocessedRoot", DOMAIN_GROUP_PREPROCESSED_V2);
    trace.absorb_bytes("preprocessedRoot.value", &proof.preprocessed_root);
    trace.domain("witnessRoot", DOMAIN_GROUP_WITNESS_V2);
    trace.absorb_bytes("witnessRoot.value", &proof.witness_root);
    trace.domain(
        "publicInputAggregationChallenge",
        DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2,
    );
    let eta = trace.squeeze_ext3("etaPi");
    trace.domain(
        "normDenominatorChallenges",
        DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2,
    );
    let beta = trace.squeeze_ext3("beta");
    let gamma = trace.squeeze_ext3("gamma");

    trace.domain("normInverseRoot", DOMAIN_GROUP_NORM_INVERSE_V2);
    trace.absorb_bytes("normInverseRoot.value", &proof.norm_inverse_root);
    trace.domain(
        "publicInputMixChallenge",
        DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2,
    );
    let xi = trace.squeeze_ext3("xiPi");
    trace.domain(
        "outerRelationChallenges",
        DOMAIN_OUTER_RELATION_CHALLENGES_V2,
    );
    let lambda = trace.squeeze_ext3("lambda");
    let rho = trace.squeeze_ext3("rho");
    let kappa = trace.squeeze_ext3("kappa");
    let tau_log = (0..degree_bits)
        .map(|index| trace.squeeze_ext3(format!("tauLog[{index}]")))
        .collect::<Vec<_>>();
    let gate_alpha = trace.squeeze_ext3("gateAlpha");
    let gate_tau = (0..degree_bits)
        .map(|index| trace.squeeze_ext3(format!("gateTau[{index}]")))
        .collect::<Vec<_>>();

    let mut log_final_claim = Field64_3::ZERO;
    let mut gate_final_claim = Field64_3::ZERO;
    let mut log_point = Vec::with_capacity(degree_bits);
    let mut gate_point = Vec::with_capacity(degree_bits);
    assert_eq!(proof.log_sumcheck_proof.rounds.len(), degree_bits);
    assert_eq!(proof.gate_proof.sumcheck_proof.rounds.len(), degree_bits);
    for round_index in 0..degree_bits {
        let log_round = &proof.log_sumcheck_proof.rounds[round_index];
        let gate_round = &proof.gate_proof.sumcheck_proof.rounds[round_index];
        trace.checkpoint(format!("round[{round_index}].before"));
        trace.domain(
            format!("round[{round_index}].messages"),
            DOMAIN_OUTER_SUMCHECK_ROUND_V2,
        );
        trace.absorb_bytes(
            format!("round[{round_index}].index"),
            &(round_index as u64).to_le_bytes(),
        );
        trace.absorb_ext3_vec(
            format!("round[{round_index}].logNonConstant"),
            &log_round.non_constant,
        );
        trace.absorb_ext3_vec(
            format!("round[{round_index}].gateNonConstant"),
            &gate_round.non_constant,
        );
        trace.domain(
            format!("round[{round_index}].challenges"),
            DOMAIN_OUTER_SUMCHECK_CHALLENGES_V2,
        );
        let log_challenge = trace.squeeze_ext3(format!("round[{round_index}].log"));
        let gate_challenge = trace.squeeze_ext3(format!("round[{round_index}].gate"));
        log_final_claim = evaluate_ext3_coefficient_round(
            log_final_claim,
            &log_round.non_constant,
            log_challenge,
        );
        gate_final_claim = evaluate_ext3_coefficient_round(
            gate_final_claim,
            &gate_round.non_constant,
            gate_challenge,
        );
        log_point.push(log_challenge);
        gate_point.push(gate_challenge);
        trace.checkpoint(format!("round[{round_index}].after"));
    }

    trace.domain("constituentClaims", DOMAIN_CONSTITUENT_CLAIMS_V2);
    trace.absorb_ext3_vec("claim[0].log.preprocessed", &proof.log_preprocessed_evals);
    trace.absorb_ext3_vec("claim[1].log.witness", &proof.log_witness_evals);
    trace.absorb_ext3_vec("claim[2].log.normInverse", &proof.log_norm_inverse_evals);
    trace.absorb_ext3_vec(
        "claim[3].gate.preprocessed",
        &proof.gate_proof.preprocessed_evals,
    );
    trace.absorb_ext3_vec("claim[4].gate.witness", &proof.gate_proof.witness_evals);
    trace.absorb_ext3_vec("claim[5].gate.normInverse.unused", &[]);
    trace.checkpoint("constituentClaims.after");
    trace.domain("constituentIndices", DOMAIN_CONSTITUENT_INDEX_V2);
    let index_bits = constituent_index_bits_v2(vk.constituent_width);
    let index_points = (0..NUM_PCS_TERMINAL_POINTS_V2)
        .map(|point_index| {
            (0..index_bits)
                .map(|coordinate| trace.squeeze_ext3(format!("index[{point_index}][{coordinate}]")))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    trace.checkpoint("final");

    let claim_values = [
        Some(fold_ext3_claim(
            &proof.log_preprocessed_evals,
            vk.constituent_width,
            &index_points[0],
        )),
        Some(fold_ext3_claim(
            &proof.log_witness_evals,
            vk.constituent_width,
            &index_points[0],
        )),
        Some(fold_ext3_claim(
            &proof.log_norm_inverse_evals,
            vk.constituent_width,
            &index_points[0],
        )),
        Some(fold_ext3_claim(
            &proof.gate_proof.preprocessed_evals,
            vk.constituent_width,
            &index_points[1],
        )),
        Some(fold_ext3_claim(
            &proof.gate_proof.witness_evals,
            vk.constituent_width,
            &index_points[1],
        )),
        None,
    ];
    let point_names = ["log", "gate"];
    let group_names = ["preprocessed", "witness", "norm_inverse"];
    let packed_claims = claim_values
        .into_iter()
        .enumerate()
        .map(|(index, value)| {
            let point_index = index / NUM_PCS_GROUPS_V2;
            let group_index = index % NUM_PCS_GROUPS_V2;
            let used = PACKED_BOUND_CLAIM_MASK_V2[index / 8] & (1 << (index % 8)) != 0;
            assert_eq!(used, value.is_some(), "claim mask/order mismatch");
            PackedClaimRecord {
                point_index,
                group_index,
                point: point_names[point_index].to_string(),
                group: group_names[group_index].to_string(),
                used,
                value: value.map(encode_ext3),
            }
        })
        .collect::<Vec<_>>();

    let row_points = [&log_point, &gate_point];
    let packed_points = (0..NUM_PCS_TERMINAL_POINTS_V2)
        .map(|point_index| {
            let packed = row_points[point_index]
                .iter()
                .chain(&index_points[point_index])
                .copied()
                .collect::<Vec<_>>();
            PackedPointRecord {
                name: point_names[point_index].to_string(),
                row_point: row_points[point_index]
                    .iter()
                    .copied()
                    .map(encode_ext3)
                    .collect(),
                constituent_index_point: index_points[point_index]
                    .iter()
                    .copied()
                    .map(encode_ext3)
                    .collect(),
                packed_point: packed.into_iter().map(encode_ext3).collect(),
            }
        })
        .collect::<Vec<_>>();

    let public_inputs_hash = PoseidonHash::hash_no_pad(&proof.public_inputs);
    let mut subgroup_evaluation = Field64_3::ONE;
    for (&coordinate, &generator_power) in log_point.iter().zip(&vk.subgroup_gen_powers) {
        let generator = Field64_3::from(generator_power.to_canonical_u64());
        subgroup_evaluation *= (Field64_3::ONE - coordinate) + coordinate * generator;
    }
    let num_routed = common.config.num_routed_wires;
    let public_input_wires = decode_public_input_wire_map_v2(
        &vk.public_input_wire_map,
        common.num_public_inputs,
        common.degree(),
        common.config.num_routed_wires,
    )
    .unwrap();
    let log_terminal = evaluate_joint_norm_logup_terminal_with_public_inputs(
        &tau_log,
        &log_point,
        &proof.log_witness_evals[..num_routed],
        &proof.log_preprocessed_evals[common.num_constants..common.num_constants + num_routed],
        &proof.log_norm_inverse_evals[..num_routed],
        &proof.log_norm_inverse_evals[num_routed..],
        subgroup_evaluation,
        &vk.k_is,
        NormLogupChallenges {
            beta,
            gamma,
            lambda,
            rho,
            kappa,
            eta,
            xi,
        },
        &proof.public_inputs,
        &public_input_wires,
    );
    assert_eq!(log_terminal, log_final_claim, "log terminal mismatch");

    let gate_aggregation = evaluate_gate_aggregation_ext3(
        common,
        &vk.gates,
        &proof.gate_proof.witness_evals,
        &proof.gate_proof.preprocessed_evals[..common.num_constants],
        &public_inputs_hash,
        gate_alpha,
    )
    .expect("gate terminal evaluation");
    let gate_eq = ext3_eq_eval(&gate_tau, &gate_point).expect("gate eq evaluation");
    let gate_expected_final_claim = gate_eq * gate_aggregation;
    assert_eq!(
        gate_expected_final_claim, gate_final_claim,
        "gate terminal mismatch"
    );

    DerivedRecord {
        outer_transcript: trace.events,
        packed_points,
        packed_claims,
        terminals: TerminalRecord {
            public_inputs_hash: public_inputs_hash.elements.each_ref().map(encode_base),
            subgroup_evaluation_at_log_point: encode_ext3(subgroup_evaluation),
            log_final_claim: encode_ext3(log_final_claim),
            log_terminal: encode_ext3(log_terminal),
            gate_final_claim: encode_ext3(gate_final_claim),
            gate_constraint_aggregation: encode_ext3(gate_aggregation),
            gate_eq_evaluation: encode_ext3(gate_eq),
            gate_expected_final_claim: encode_ext3(gate_expected_final_claim),
        },
    }
}

fn build_small_mul() -> (CircuitData<F, C, D>, PartialWitness<F>) {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let mut current = x;
    for _ in 0..5 {
        current = builder.mul(current, x);
    }
    builder.register_public_input(current);
    let circuit = builder.build::<C>();
    let mut witness = PartialWitness::new();
    witness.set_target(x, F::from_canonical_u64(2)).unwrap();
    (circuit, witness)
}

fn build_fixture() -> CrossLanguageFixture {
    let (circuit, witness) = build_small_mul();
    let vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    let proof = mle_prove_v2::<F, C, D>(
        &circuit.prover_only,
        &circuit.common,
        witness,
        &mut TimingTree::default(),
    )
    .expect("small_mul v2 proof generation");
    mle_verify_v2::<F, D>(&circuit.common, &vk, &proof).expect("generated proof verifies");
    let shape = compact_v2_shape_for_common(&circuit.common, vk.constituent_width)
        .expect("canonical compact-v2 shape");
    let encoded = encode_compact_v2(&proof, &shape).expect("compact-v2 encoding");
    let decoded = decode_compact_v2::<F>(&encoded, &shape).expect("compact-v2 decoding");
    mle_verify_v2::<F, D>(&circuit.common, &vk, &decoded).expect("decoded proof verifies");
    let production = try_export_mle_v2_fixture(&decoded, &vk, &circuit.common)
        .expect("generated proof has one production v2 export");
    let derived = derive_records(&circuit.common, &vk, &decoded);
    let whir_profile =
        derive_whir_deployment_profile_v2(circuit.common.degree_bits(), vk.constituent_width)
            .expect("canonical v2 WHIR deployment profile");
    let whir_params = whir_profile
        .params
        .without_points()
        .expect("deployment WHIR points are verifier-derived");
    assert_eq!(whir_profile.protocol_id.as_slice(), vk.whir_protocol_id);
    assert_eq!(whir_profile.session_id.as_slice(), vk.whir_session_id);
    let packed_num_vars =
        packed_group_num_vars_v2(circuit.common.degree_bits(), vk.constituent_width);
    let whir_native = WhirPCS::for_constituents(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP_V2)
        .trace_grouped_preflight(
            packed_num_vars,
            &decoded.whir_eval_proof,
            WHIR_SESSION_SPLIT_V2,
            NUM_PCS_GROUPS_V2,
            NUM_PCS_CLAIMS_V2,
        )
        .expect("canonical grouped-WHIR trace");
    assert_eq!(
        whir_native.last().map(|event| event.kind),
        Some(WhirNativeTraceEventKind::Eof),
        "canonical grouped-WHIR trace must reach exact EOF"
    );
    let digest = keccak(&encoded);
    let case = CaseRecord {
        name: "small_mul".to_string(),
        circuit: CircuitRecord {
            builder: "CircuitConfig::standard_recursion_config()".to_string(),
            relation: "public = x^6".to_string(),
            chain_length: 5,
            witness_x: encode_limb(2),
            expected_public_inputs: decoded.public_inputs.iter().map(encode_base).collect(),
            degree_bits: circuit.common.degree_bits(),
            num_public_inputs: circuit.common.num_public_inputs,
        },
        verification_key: VerificationKeyRecord::encode(&vk),
        solidity_abi_proof: production.solidity_abi_proof,
        solidity_abi_verification_config: production.solidity_abi_verification_config,
        whir_params,
        whir_native: whir_native_record(&whir_native),
        whir_evaluations: whir_bound_evaluations(&whir_native),
        compact_shape: CompactShapeRecord::encode(&shape),
        compact_proof: CompactProofRecord {
            encoding: String::from_utf8(COMPACT_MAGIC_V2.to_vec()).unwrap(),
            byte_length: encoded.len(),
            keccak256: encode_hex(digest.as_ref()),
            bytes: encode_hex(&encoded),
        },
        size_upper_bound: production.size_upper_bound,
        compact_negative_cases: vec![
            CompactNegativeCaseRecord {
                name: "old_v2_protocol_version".to_string(),
                operation: "replace".to_string(),
                offset: Some(8),
                new_length: None,
                data: Some(encode_hex(&2u64.to_le_bytes())),
                expected_error: "wrongProtocolVersion:2".to_string(),
            },
            CompactNegativeCaseRecord {
                name: "truncated_last_byte".to_string(),
                operation: "truncate".to_string(),
                offset: None,
                new_length: Some(encoded.len() - 1),
                data: None,
                expected_error: "unexpectedEof".to_string(),
            },
            CompactNegativeCaseRecord {
                name: "trailing_zero_byte".to_string(),
                operation: "append".to_string(),
                offset: None,
                new_length: None,
                data: Some("0x00".to_string()),
                expected_error: "trailingBytes:1".to_string(),
            },
            CompactNegativeCaseRecord {
                name: "noncanonical_first_circuit_digest_limb".to_string(),
                operation: "replace".to_string(),
                offset: Some(20),
                new_length: None,
                data: Some(encode_hex(&BASE_FIELD_MODULUS_V2.to_le_bytes())),
                expected_error: "nonCanonicalGoldilocks:offset20".to_string(),
            },
        ],
        packed_claim_mask: encode_hex(&PACKED_BOUND_CLAIM_MASK_V2),
        outer_transcript: derived.outer_transcript,
        packed_points: derived.packed_points,
        packed_claims: derived.packed_claims,
        terminals: derived.terminals,
    };
    CrossLanguageFixture {
        schema: "plonky2-mle-v3-cross-language".to_string(),
        version: MLE_PROTOCOL_VERSION_CURRENT,
        field: FieldSchema {
            modulus: encode_limb(BASE_FIELD_MODULUS_V2),
            ext3_polynomial: format!("theta^3 - {EXTENSION_NON_RESIDUE_V2}"),
            inner_extension_non_residue: encode_limb(INNER_EXTENSION_NON_RESIDUE_V2),
            ext3_limb_order: ["c0".to_string(), "c1".to_string(), "c2".to_string()],
            compact_limb_byte_order: "little-endian".to_string(),
            transcript_initial_state: encode_hex(&[0u8; 32]),
            transcript_frame_prefix: encode_hex(TRANSCRIPT_FRAME_PREFIX_V2.as_bytes()),
            transcript_challenge_prefix: encode_hex(TRANSCRIPT_CHALLENGE_PREFIX_V2.as_bytes()),
            transcript_tags: TranscriptTagRecord {
                domain: TAG_DOMAIN_V2,
                bytes: TAG_BYTES_V2,
                field: TAG_FIELD_V2,
                field_vec: TAG_FIELD_VEC_V2,
                ext3: TAG_EXT3_V2,
                ext3_vec: TAG_EXT3_VEC_V2,
            },
        },
        point_order: ["log".to_string(), "gate".to_string()],
        group_order: [
            "preprocessed".to_string(),
            "witness".to_string(),
            "norm_inverse".to_string(),
        ],
        cases: vec![case],
    }
}

fn canonical_json(fixture: &CrossLanguageFixture) -> String {
    let mut json = serde_json::to_string_pretty(fixture).expect("serialize v2 fixture");
    json.push('\n');
    json
}

#[test]
fn v2_small_mul_snapshot_decodes_and_verifies() {
    let checked_in_text = include_str!("../contracts/test/fixtures/v2_cross_language.json");
    let checked_in: CrossLanguageFixture =
        serde_json::from_str(checked_in_text).expect("checked-in v2 fixture JSON");
    assert_eq!(
        checked_in_text,
        canonical_json(&checked_in),
        "v2 cross-language fixture is not the exact canonical JSON snapshot"
    );
    assert_eq!(
        encode_hex(keccak(checked_in_text.as_bytes()).as_ref()),
        EXPECTED_FIXTURE_KECCAK,
        "v2 cross-language snapshot bytes changed without an intentional hash update"
    );

    let (circuit, _) = build_small_mul();
    assert_eq!(checked_in.cases.len(), 1);
    assert_eq!(checked_in.version, MLE_PROTOCOL_VERSION_CURRENT);
    assert_eq!(checked_in.field.modulus, encode_limb(BASE_FIELD_MODULUS_V2));
    let case = &checked_in.cases[0];
    assert_eq!(case.name, "small_mul");
    let setup_vk = mle_setup_v2::<F, C, D>(&circuit.prover_only, &circuit.common);
    assert_eq!(
        case.verification_key,
        VerificationKeyRecord::encode(&setup_vk),
        "checked-in verification key drifted from deterministic setup"
    );
    let vk = case.verification_key.decode();
    let expected_profile = derive_whir_deployment_profile_v2(
        case.circuit.degree_bits,
        case.verification_key.constituent_width,
    )
    .expect("canonical v2 WHIR deployment profile");
    let expected_whir = expected_profile.params.without_points().unwrap();
    assert_eq!(
        case.whir_params, expected_whir,
        "checked-in WHIR parameters drifted"
    );
    assert_eq!(
        decode_fixed_hex::<64>(&case.verification_key.whir_protocol_id),
        expected_profile.protocol_id,
        "WHIR protocol identifier does not match the exported configuration"
    );
    assert_eq!(
        decode_fixed_hex::<32>(&case.verification_key.whir_session_id),
        expected_profile.session_id,
        "WHIR session identifier does not match the v2 session"
    );
    let shape = case.compact_shape.decode();
    assert_eq!(case.compact_proof.encoding.as_bytes(), COMPACT_MAGIC_V2);
    let encoded = decode_hex(&case.compact_proof.bytes);
    assert_eq!(encoded.len(), case.compact_proof.byte_length);
    assert_eq!(
        encode_hex(keccak(&encoded).as_ref()),
        case.compact_proof.keccak256
    );
    let proof = decode_compact_v2::<F>(&encoded, &shape).expect("decode checked-in compact proof");
    assert_eq!(case.compact_negative_cases.len(), 4);
    for negative in &case.compact_negative_cases {
        let mutated = apply_compact_mutation(&encoded, negative);
        let error = decode_compact_v2::<F>(&mutated, &shape)
            .expect_err("recorded compact-v2 mutation must fail closed");
        assert_expected_compact_error(error, &negative.expected_error);
    }
    assert_eq!(
        proof
            .public_inputs
            .iter()
            .map(encode_base)
            .collect::<Vec<_>>(),
        case.circuit.expected_public_inputs
    );
    assert_eq!(
        encode_compact_v2(&proof, &shape).unwrap(),
        encoded,
        "checked-in proof is not canonical compact-v2"
    );
    mle_verify_v2::<F, D>(&circuit.common, &vk, &proof)
        .expect("checked-in compact-v2 proof must verify");
    let production = try_export_mle_v2_fixture(&proof, &vk, &circuit.common)
        .expect("checked-in proof has one production v2 export");
    assert_eq!(
        case.solidity_abi_proof, production.solidity_abi_proof,
        "checked-in Solidity proof ABI view drifted from the production exporter"
    );
    assert_eq!(
        case.solidity_abi_verification_config, production.solidity_abi_verification_config,
        "checked-in Solidity verification-config ABI view drifted from the production exporter"
    );
    assert_eq!(
        case.size_upper_bound, production.size_upper_bound,
        "checked-in proof-size upper bound drifted from the production exporter"
    );
    assert_eq!(
        production.solidity_abi_proof.byte_length, EXPECTED_SOLIDITY_ABI_PROOF_BYTES,
        "canonical Solidity ABI proof length drifted"
    );
    assert_eq!(
        production.solidity_abi_proof.keccak256, EXPECTED_SOLIDITY_ABI_PROOF_KECCAK,
        "canonical Solidity ABI proof hash drifted"
    );
    assert_eq!(
        production.solidity_abi_verification_config.byte_length, EXPECTED_SOLIDITY_ABI_CONFIG_BYTES,
        "canonical Solidity ABI verification-config length drifted"
    );
    assert_eq!(
        production.solidity_abi_verification_config.keccak256, EXPECTED_SOLIDITY_ABI_CONFIG_KECCAK,
        "canonical Solidity ABI verification-config hash drifted"
    );
    println!(
        "canonical v2 export: solidity_abi_bytes={} compact_bytes={} whir_narg_bytes={} whir_hint_bytes={} abi_keccak={} config_abi_bytes={} config_abi_keccak={}",
        production.solidity_abi_proof.byte_length,
        production.stats.compact_bytes,
        production.stats.whir_transcript_bytes,
        production.stats.whir_hint_bytes,
        production.solidity_abi_proof.keccak256,
        production.solidity_abi_verification_config.byte_length,
        production.solidity_abi_verification_config.keccak256,
    );

    let packed_num_vars = packed_group_num_vars_v2(
        case.circuit.degree_bits,
        case.verification_key.constituent_width,
    );
    let whir_native = WhirPCS::for_constituents(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP_V2)
        .trace_grouped_preflight(
            packed_num_vars,
            &proof.whir_eval_proof,
            WHIR_SESSION_SPLIT_V2,
            NUM_PCS_GROUPS_V2,
            NUM_PCS_CLAIMS_V2,
        )
        .expect("checked-in grouped-WHIR trace");
    assert_eq!(
        case.whir_native,
        whir_native_record(&whir_native),
        "checked-in grouped-WHIR native trace drifted"
    );
    let whir_evaluations = whir_bound_evaluations(&whir_native);
    assert_eq!(case.whir_evaluations, whir_evaluations);
    assert_eq!(case.whir_evaluations.len(), NUM_PCS_CLAIMS_V2);
    for index in 0..NUM_PCS_CLAIMS_V2 - 1 {
        assert_eq!(
            case.packed_claims[index].value.as_ref(),
            Some(&case.whir_evaluations[index]),
            "used packed claim does not match Rust grouped-WHIR output at {index}"
        );
    }
    assert!(!case.packed_claims[NUM_PCS_CLAIMS_V2 - 1].used);
    assert!(case.packed_claims[NUM_PCS_CLAIMS_V2 - 1].value.is_none());

    let derived = derive_records(&circuit.common, &vk, &proof);
    assert_eq!(case.outer_transcript, derived.outer_transcript);
    assert_eq!(case.packed_points, derived.packed_points);
    assert_eq!(case.packed_claims, derived.packed_claims);
    assert_eq!(case.terminals, derived.terminals);
    assert_eq!(case.packed_claims.len(), NUM_PCS_CLAIMS_V2);
    assert_eq!(case.packed_points.len(), NUM_PCS_TERMINAL_POINTS_V2);
    assert_byte_exact_transcript(&checked_in.field, &case.outer_transcript);
    let final_event = case
        .outer_transcript
        .last()
        .expect("final transcript event");
    assert_eq!(final_event.kind, "checkpoint");
    assert_eq!(final_event.label, "final");
}

#[test]
#[ignore = "writes the canonical cross-language snapshot only on explicit opt-in"]
fn regenerate_v2_cross_language_fixture() {
    assert_eq!(
        std::env::var("MLE_WRITE_V2_FIXTURE").as_deref(),
        Ok("1"),
        "set MLE_WRITE_V2_FIXTURE=1 for an intentional snapshot update"
    );
    let generated = build_fixture();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("contracts/test/fixtures/v2_cross_language.json");
    std::fs::write(path, canonical_json(&generated)).unwrap();
}

#[test]
fn schema_only_cross_language_migration_is_disabled_for_wire_v3() {
    // Revision 3 changes the transcript, relation and WHIR session/profile.
    // Relabelling legacy proof bytes is never a valid migration; the ignored
    // real-proof generator above is the only supported snapshot update path.
    assert_eq!(&COMPACT_MAGIC_V2, b"MLEWHIR3");
}
