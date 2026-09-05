//! Cross-language schema generation and drift checks for MLE/WHIR v2.
//!
//! `protocol/mle_whir_v2.json` is the sole hand-maintained source for the
//! protocol labels, resource envelope, ordered commitment/point matrix, and
//! compact proof layout. Rust and Solidity consume generated artifacts.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::{Field, PrimeField64};
use serde::Deserialize;
use sha3::{Digest, Keccak256};

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProtocolSchemaV2 {
    schema_version: u64,
    mle_protocol_version: u64,
    outer_transcript_protocol: String,
    packed_schema_domain: String,
    whir_split_session: String,
    compact_magic: String,
    transcript_frame_prefix: String,
    transcript_challenge_prefix: String,
    circuit_config_hash_domain: String,
    base_field_modulus: u64,
    base_field_two_adicity: usize,
    base_field_power_of_two_generator: u64,
    base_field_multiplicative_generator: u64,
    extension_non_residue: u64,
    inner_extension_non_residue: u64,
    extension_field_limbs: usize,
    inner_extension_degree: usize,
    packed_vectors_per_group: usize,
    variable_order_code: usize,
    log_round_degree: usize,
    gate_sumcheck_count: usize,
    max_row_variables: usize,
    max_routed_wires: usize,
    max_constituent_width: usize,
    max_constituent_index_bits: usize,
    max_gate_constraints: usize,
    max_gate_round_degree: usize,
    max_gate_rows: usize,
    circuit_digest_length: usize,
    max_public_inputs: usize,
    whir_security_level: usize,
    whir_pow_bits: usize,
    whir_max_starting_log_inv_rate: usize,
    whir_folding_factor: usize,
    whir_hash_id: String,
    whir_unique_decoding: bool,
    whir_deduplicate_in_domain: bool,
    max_whir_narg_bytes: usize,
    max_whir_hint_bytes: usize,
    max_compact_proof_bytes: usize,
    transcript_tags: Vec<TranscriptTag>,
    statement_metadata: Vec<String>,
    relation_challenges: Vec<String>,
    outer_round_messages: Vec<String>,
    outer_round_challenges: Vec<String>,
    transcript_domains: Vec<Domain>,
    groups: Vec<OrderedItem>,
    terminal_points: Vec<OrderedItem>,
    bound_cells: Vec<BoundCell>,
    proof_abi: Vec<ProofAbiField>,
    compact_fields: Vec<CompactField>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Domain {
    constant: String,
    value: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct TranscriptTag {
    constant: String,
    value: u8,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct OrderedItem {
    name: String,
    constant: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct BoundCell {
    point: String,
    group: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompactField {
    name: String,
    encoding: String,
    shape: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProofAbiField {
    name: String,
    json_name: String,
    solidity_type: String,
    abi_type: String,
}

struct Derived {
    claim_count: usize,
    bound_mask: Vec<u8>,
    compact_layout_hash: [u8; 32],
    proof_abi_signature: String,
    proof_layout_hash: [u8; 32],
    proof_test_selector: [u8; 4],
}

fn is_constant(value: &str) -> bool {
    !value.is_empty()
        && value.as_bytes()[0].is_ascii_uppercase()
        && value
            .bytes()
            .all(|byte| byte == b'_' || byte.is_ascii_uppercase() || byte.is_ascii_digit())
}

fn is_label(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b'/'))
}

fn is_schema_token(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| {
            byte.is_ascii_alphanumeric()
                || matches!(byte, b'-' | b'_' | b'.' | b'/' | b'[' | b']' | b'*' | b'+')
        })
}

fn is_field_identifier(value: &str) -> bool {
    !value.is_empty()
        && value.as_bytes()[0].is_ascii_lowercase()
        && value
            .bytes()
            .all(|byte| byte == b'_' || byte.is_ascii_alphanumeric())
}

fn is_type_expression(value: &str, source_type: bool) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| {
            byte.is_ascii_alphanumeric()
                || matches!(byte, b'_' | b'[' | b']' | b'(' | b')' | b',')
                || (source_type && byte == b'.')
        })
}

fn derive_proof_layout(proof_abi: &[ProofAbiField]) -> (String, [u8; 32], [u8; 4]) {
    let signature = format!(
        "({})",
        proof_abi
            .iter()
            .map(|field| field.abi_type.as_str())
            .collect::<Vec<_>>()
            .join(",")
    );
    let mut semantic_layout = String::from("plonky2-mle-proof-abi-v3\n");
    for field in proof_abi {
        writeln!(
            semantic_layout,
            "{}\t{}\t{}\t{}",
            field.name, field.json_name, field.solidity_type, field.abi_type
        )
        .unwrap();
    }
    let layout_hash: [u8; 32] = Keccak256::digest(semantic_layout.as_bytes()).into();
    let selector_digest = Keccak256::digest(format!("acceptV2({signature})").as_bytes());
    let selector = selector_digest[..4].try_into().unwrap();
    (signature, layout_hash, selector)
}

fn ordered_indices(items: &[OrderedItem], kind: &str) -> BTreeMap<String, usize> {
    let mut names = BTreeMap::new();
    let mut constants = BTreeSet::new();
    for (index, item) in items.iter().enumerate() {
        assert!(is_label(&item.name), "invalid {kind} name: {}", item.name);
        assert!(is_constant(&item.constant), "invalid {kind} constant");
        assert!(
            names.insert(item.name.clone(), index).is_none(),
            "duplicate {kind} name: {}",
            item.name
        );
        assert!(
            constants.insert(item.constant.as_str()),
            "duplicate {kind} constant: {}",
            item.constant
        );
    }
    names
}

fn validate_and_derive(schema: &ProtocolSchemaV2) -> Derived {
    assert_eq!(schema.schema_version, 3);
    assert_eq!(schema.mle_protocol_version, 3);
    assert_eq!(schema.compact_magic.len(), 8);
    assert_eq!(schema.base_field_modulus, 0xffff_ffff_0000_0001);
    assert_eq!(schema.base_field_two_adicity, GoldilocksField::TWO_ADICITY);
    assert_eq!(
        schema.base_field_power_of_two_generator,
        GoldilocksField::POWER_OF_TWO_GENERATOR.to_canonical_u64()
    );
    assert_eq!(
        schema.base_field_multiplicative_generator,
        GoldilocksField::MULTIPLICATIVE_GROUP_GENERATOR.to_canonical_u64()
    );
    assert_eq!(schema.extension_non_residue, 2);
    assert_eq!(schema.inner_extension_non_residue, 7);
    assert_eq!(schema.extension_field_limbs, 3);
    assert_eq!(schema.inner_extension_degree, 2);
    assert_eq!(schema.packed_vectors_per_group, 1);
    assert_eq!(schema.variable_order_code, 0);
    assert_eq!(schema.log_round_degree, 5);
    assert_eq!(schema.gate_sumcheck_count, 1);
    assert_eq!(schema.max_row_variables, 13);
    assert_eq!(schema.max_routed_wires, 80);
    assert_eq!(schema.max_constituent_width, 160);
    assert_eq!(schema.max_constituent_index_bits, 8);
    assert_eq!(schema.max_gate_constraints, 123);
    assert_eq!(schema.max_gate_round_degree, 10);
    assert_eq!(schema.max_gate_rows, 255);
    assert_eq!(schema.circuit_digest_length, 4);
    assert_eq!(schema.max_public_inputs, 256);
    assert_eq!(schema.whir_security_level, 133);
    assert_eq!(schema.whir_pow_bits, 22);
    assert_eq!(schema.whir_max_starting_log_inv_rate, 4);
    assert_eq!(schema.whir_folding_factor, 4);
    assert_eq!(schema.whir_hash_id, "keccak-256");
    assert!(!schema.whir_unique_decoding);
    assert!(schema.whir_deduplicate_in_domain);
    assert_eq!(schema.max_whir_narg_bytes, 2_032);
    assert_eq!(schema.max_whir_hint_bytes, 180_408);
    // The submitted compact proof must fit the parent's exact two-blob DA payload.
    assert_eq!(schema.max_compact_proof_bytes, 253_921);
    for label in [
        &schema.outer_transcript_protocol,
        &schema.packed_schema_domain,
        &schema.whir_split_session,
        &schema.transcript_frame_prefix,
        &schema.transcript_challenge_prefix,
        &schema.circuit_config_hash_domain,
    ] {
        assert!(is_label(label), "invalid protocol label: {label}");
    }

    let expected_tags = [
        ("TAG_DOMAIN", 1),
        ("TAG_BYTES", 2),
        ("TAG_FIELD", 3),
        ("TAG_FIELD_VEC", 4),
        ("TAG_EXT3", 5),
        ("TAG_EXT3_VEC", 6),
    ];
    assert_eq!(schema.transcript_tags.len(), expected_tags.len());
    for (tag, (expected_constant, expected_value)) in
        schema.transcript_tags.iter().zip(expected_tags)
    {
        assert_eq!(tag.constant, expected_constant);
        assert_eq!(tag.value, expected_value);
    }
    let expected_statement_metadata = [
        "protocol_version",
        "num_pcs_groups",
        "num_terminal_points",
        "num_pcs_claims",
        "num_constants",
        "num_routed_wires",
        "num_wires",
        "degree_bits",
        "constituent_width",
        "constituent_index_bits",
        "packed_vectors_per_group",
        "extension_field_limbs",
        "variable_order_code",
        "gate_sumcheck_count",
        "log_round_degree",
    ];
    assert_eq!(schema.statement_metadata, expected_statement_metadata);
    assert_eq!(
        schema.relation_challenges,
        [
            "eta_pi",
            "beta",
            "gamma",
            "xi_pi",
            "lambda",
            "rho",
            "kappa",
            "tau_log",
            "gate_alpha",
            "gate_tau"
        ]
    );
    assert_eq!(
        schema.outer_round_messages,
        ["log_non_constant", "gate_non_constant"]
    );
    assert_eq!(schema.outer_round_challenges, ["log", "gate"]);

    let mut domain_constants = BTreeSet::new();
    let mut domain_values = BTreeSet::new();
    assert_eq!(schema.transcript_domains.len(), 15);
    for domain in &schema.transcript_domains {
        assert!(is_constant(&domain.constant));
        assert!(is_label(&domain.value));
        assert!(domain_constants.insert(domain.constant.as_str()));
        assert!(domain_values.insert(domain.value.as_str()));
    }

    let groups = ordered_indices(&schema.groups, "group");
    let points = ordered_indices(&schema.terminal_points, "terminal point");
    assert_eq!(groups.len(), 3, "v2 has exactly three commitment groups");
    assert_eq!(points.len(), 2, "v2 has exactly two terminal points");
    let claim_count = groups.len() * points.len();
    assert_eq!(claim_count, 6);
    let mut bound_mask = vec![0u8; claim_count.div_ceil(8)];
    let mut seen = BTreeSet::new();
    for cell in &schema.bound_cells {
        let point = *points
            .get(&cell.point)
            .unwrap_or_else(|| panic!("unknown bound point: {}", cell.point));
        let group = *groups
            .get(&cell.group)
            .unwrap_or_else(|| panic!("unknown bound group: {}", cell.group));
        let slot = point * groups.len() + group;
        assert!(seen.insert(slot), "duplicate bound cell {slot}");
        bound_mask[slot / 8] |= 1 << (slot % 8);
    }
    assert_eq!(seen.len(), 5);
    assert_eq!(bound_mask, [0x1f]);

    let expected_proof_fields = [
        "protocolVersion",
        "constituentWidth",
        "circuitDigest",
        "publicInputs",
        "preprocessedRoot",
        "witnessRoot",
        "normInverseRoot",
        "whirTranscript",
        "whirHints",
        "logProof",
        "logPreprocessed",
        "logWitness",
        "logNormInverse",
        "gateProof",
        "gatePreprocessed",
        "gateWitness",
    ];
    assert_eq!(schema.proof_abi.len(), expected_proof_fields.len());
    let mut proof_names = BTreeSet::new();
    let mut proof_json_names = BTreeSet::new();
    for (field, expected_name) in schema.proof_abi.iter().zip(expected_proof_fields) {
        assert_eq!(field.name, expected_name, "v2 proof ABI field order drift");
        assert!(is_field_identifier(&field.name));
        assert!(is_field_identifier(&field.json_name));
        assert!(is_type_expression(&field.solidity_type, true));
        assert!(is_type_expression(&field.abi_type, false));
        assert!(proof_names.insert(field.name.as_str()));
        assert!(proof_json_names.insert(field.json_name.as_str()));
    }
    let (proof_abi_signature, proof_layout_hash, proof_test_selector) =
        derive_proof_layout(&schema.proof_abi);

    let expected_compact_fields = [
        "magic",
        "protocol_version",
        "constituent_width",
        "circuit_digest",
        "public_inputs",
        "preprocessed_root",
        "witness_root",
        "norm_inverse_root",
        "whir_narg",
        "whir_hints",
        "log_round_coefficients",
        "log_preprocessed",
        "log_witness",
        "log_norm_inverse",
        "gate_round_coefficients",
        "gate_preprocessed",
        "gate_witness",
    ];
    assert_eq!(schema.compact_fields.len(), expected_compact_fields.len());
    let mut compact_names = BTreeSet::new();
    let mut semantic_layout = String::from("plonky2-mle-compact-v3\n");
    for (field, expected_name) in schema.compact_fields.iter().zip(expected_compact_fields) {
        assert_eq!(field.name, expected_name, "compact field order drift");
        assert!(is_label(&field.name));
        assert!(is_schema_token(&field.encoding));
        assert!(is_schema_token(&field.shape));
        assert!(compact_names.insert(field.name.as_str()));
        writeln!(
            semantic_layout,
            "{}\t{}\t{}",
            field.name, field.encoding, field.shape
        )
        .unwrap();
    }

    Derived {
        claim_count,
        bound_mask,
        compact_layout_hash: Keccak256::digest(semantic_layout.as_bytes()).into(),
        proof_abi_signature,
        proof_layout_hash,
        proof_test_selector,
    }
}

fn render_rust(schema: &ProtocolSchemaV2, derived: &Derived) -> String {
    let mut out = String::new();
    out.push_str(
        "// @generated by tests/protocol_schema_v2_codegen.rs from protocol/mle_whir_v2.json.\n\
         // Do not edit by hand.\n\n",
    );
    macro_rules! number {
        ($name:literal, $value:expr) => {
            writeln!(out, "pub const {}: usize = {};", $name, $value).unwrap()
        };
    }
    writeln!(
        out,
        "pub const SCHEMA_VERSION_CURRENT: u64 = {};",
        schema.schema_version
    )
    .unwrap();
    writeln!(
        out,
        "pub const MLE_PROTOCOL_VERSION_CURRENT: u64 = {};",
        schema.mle_protocol_version
    )
    .unwrap();
    writeln!(
        out,
        "pub const OUTER_TRANSCRIPT_PROTOCOL_V2: &str = {:?};",
        schema.outer_transcript_protocol
    )
    .unwrap();
    writeln!(
        out,
        "pub const PACKED_PCS_SCHEMA_DOMAIN_V2: &str = {:?};",
        schema.packed_schema_domain
    )
    .unwrap();
    writeln!(
        out,
        "pub const WHIR_SESSION_SPLIT_V2: &str = {:?};",
        schema.whir_split_session
    )
    .unwrap();
    writeln!(
        out,
        "pub const COMPACT_MAGIC_V2: [u8; 8] = *b{:?};",
        schema.compact_magic
    )
    .unwrap();
    writeln!(
        out,
        "pub const TRANSCRIPT_FRAME_PREFIX_V2: &str = {:?};",
        schema.transcript_frame_prefix
    )
    .unwrap();
    writeln!(
        out,
        "pub const TRANSCRIPT_CHALLENGE_PREFIX_V2: &str = {:?};",
        schema.transcript_challenge_prefix
    )
    .unwrap();
    writeln!(
        out,
        "pub const CIRCUIT_CONFIG_HASH_DOMAIN_V2: &str = {:?};",
        schema.circuit_config_hash_domain
    )
    .unwrap();
    writeln!(
        out,
        "pub const BASE_FIELD_MODULUS_V2: u64 = 0x{:016x};",
        schema.base_field_modulus
    )
    .unwrap();
    number!("BASE_FIELD_TWO_ADICITY_V2", schema.base_field_two_adicity);
    writeln!(
        out,
        "pub const BASE_FIELD_POWER_OF_TWO_GENERATOR_V2: u64 = {};",
        schema.base_field_power_of_two_generator
    )
    .unwrap();
    writeln!(
        out,
        "pub const BASE_FIELD_MULTIPLICATIVE_GENERATOR_V2: u64 = {};",
        schema.base_field_multiplicative_generator
    )
    .unwrap();
    writeln!(
        out,
        "pub const EXTENSION_NON_RESIDUE_V2: u64 = {};",
        schema.extension_non_residue
    )
    .unwrap();
    writeln!(
        out,
        "pub const INNER_EXTENSION_NON_RESIDUE_V2: u64 = {};",
        schema.inner_extension_non_residue
    )
    .unwrap();
    number!("EXTENSION_FIELD_LIMBS_V2", schema.extension_field_limbs);
    number!("INNER_EXTENSION_DEGREE_V2", schema.inner_extension_degree);
    number!(
        "NUM_PACKED_VECTORS_PER_GROUP_V2",
        schema.packed_vectors_per_group
    );
    number!("PACKED_VARIABLE_ORDER_CODE_V2", schema.variable_order_code);
    number!("LOG_ROUND_DEGREE_V2", schema.log_round_degree);
    number!("GATE_SUMCHECK_COUNT_V2", schema.gate_sumcheck_count);
    number!("MAX_ROW_VARIABLES_V2", schema.max_row_variables);
    number!("MAX_ROUTED_WIRES_V2", schema.max_routed_wires);
    number!("MAX_CONSTITUENT_WIDTH_V2", schema.max_constituent_width);
    number!(
        "MAX_CONSTITUENT_INDEX_BITS_V2",
        schema.max_constituent_index_bits
    );
    number!("MAX_GATE_CONSTRAINTS_V2", schema.max_gate_constraints);
    number!("MAX_GATE_ROUND_DEGREE_V2", schema.max_gate_round_degree);
    number!("MAX_GATE_ROWS_V2", schema.max_gate_rows);
    number!("CIRCUIT_DIGEST_LENGTH_V2", schema.circuit_digest_length);
    number!("MAX_PUBLIC_INPUTS_V2", schema.max_public_inputs);
    number!("WHIR_SECURITY_LEVEL_V2", schema.whir_security_level);
    number!("WHIR_POW_BITS_V2", schema.whir_pow_bits);
    number!(
        "WHIR_MAX_STARTING_LOG_INV_RATE_V2",
        schema.whir_max_starting_log_inv_rate
    );
    number!("WHIR_FOLDING_FACTOR_V2", schema.whir_folding_factor);
    writeln!(
        out,
        "pub const WHIR_HASH_ID_V2: &str = {:?};",
        schema.whir_hash_id
    )
    .unwrap();
    writeln!(
        out,
        "pub const WHIR_UNIQUE_DECODING_V2: bool = {};",
        schema.whir_unique_decoding
    )
    .unwrap();
    writeln!(
        out,
        "pub const WHIR_DEDUPLICATE_IN_DOMAIN_V2: bool = {};",
        schema.whir_deduplicate_in_domain
    )
    .unwrap();
    number!("MAX_WHIR_NARG_BYTES_V2", schema.max_whir_narg_bytes);
    number!("MAX_WHIR_HINT_BYTES_V2", schema.max_whir_hint_bytes);
    number!("MAX_COMPACT_PROOF_BYTES_V2", schema.max_compact_proof_bytes);
    for tag in &schema.transcript_tags {
        writeln!(out, "pub const {}_V2: u8 = {};", tag.constant, tag.value).unwrap();
    }
    number!(
        "STATEMENT_METADATA_FIELD_COUNT_V2",
        schema.statement_metadata.len()
    );
    out.push_str("#[rustfmt::skip]\n");
    writeln!(
        out,
        "pub const STATEMENT_METADATA_FIELDS_V2: [&str; {}] = [",
        schema.statement_metadata.len()
    )
    .unwrap();
    for field in &schema.statement_metadata {
        writeln!(out, "    {:?},", field).unwrap();
    }
    out.push_str("];\n");
    number!(
        "RELATION_CHALLENGE_COUNT_V2",
        schema.relation_challenges.len()
    );
    for (index, challenge) in schema.relation_challenges.iter().enumerate() {
        writeln!(
            out,
            "pub const RELATION_CHALLENGE_{}_V2: usize = {index};",
            challenge.to_ascii_uppercase()
        )
        .unwrap();
    }
    number!(
        "OUTER_ROUND_MESSAGE_COUNT_V2",
        schema.outer_round_messages.len()
    );
    for (index, message) in schema.outer_round_messages.iter().enumerate() {
        writeln!(
            out,
            "pub const OUTER_ROUND_MESSAGE_{}_V2: usize = {index};",
            message.to_ascii_uppercase()
        )
        .unwrap();
    }
    number!(
        "OUTER_ROUND_CHALLENGE_COUNT_V2",
        schema.outer_round_challenges.len()
    );
    for (index, challenge) in schema.outer_round_challenges.iter().enumerate() {
        writeln!(
            out,
            "pub const OUTER_ROUND_CHALLENGE_{}_V2: usize = {index};",
            challenge.to_ascii_uppercase()
        )
        .unwrap();
    }
    for domain in &schema.transcript_domains {
        let declaration = format!(
            "pub const {}_V2: &str = {:?};",
            domain.constant, domain.value
        );
        if declaration.len() > 100 {
            writeln!(
                out,
                "pub const {}_V2: &str =\n    {:?};",
                domain.constant, domain.value
            )
            .unwrap();
        } else {
            writeln!(out, "{declaration}").unwrap();
        }
    }
    number!("NUM_PCS_GROUPS_V2", schema.groups.len());
    number!("NUM_PCS_TERMINAL_POINTS_V2", schema.terminal_points.len());
    number!("NUM_PCS_CLAIMS_V2", derived.claim_count);
    number!("NUM_BOUND_PCS_CLAIMS_V2", schema.bound_cells.len());
    for (index, item) in schema.groups.iter().enumerate() {
        writeln!(out, "pub const {}: usize = {index};", item.constant).unwrap();
    }
    for (index, item) in schema.terminal_points.iter().enumerate() {
        writeln!(out, "pub const {}: usize = {index};", item.constant).unwrap();
    }
    write!(
        out,
        "pub const PACKED_BOUND_CLAIM_MASK_V2: [u8; {}] = [",
        derived.bound_mask.len()
    )
    .unwrap();
    for (index, byte) in derived.bound_mask.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        write!(out, "0x{byte:02x}").unwrap();
    }
    out.push_str("];\n");
    number!("MLE_PROOF_ABI_FIELD_COUNT_V2", schema.proof_abi.len());
    writeln!(
        out,
        "pub const MLE_PROOF_ABI_SIGNATURE_V2: &str = {:?};",
        derived.proof_abi_signature
    )
    .unwrap();
    out.push_str("#[rustfmt::skip]\n");
    out.push_str("pub const MLE_PROOF_LAYOUT_HASH_V2: [u8; 32] = [");
    for (index, byte) in derived.proof_layout_hash.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        write!(out, "0x{byte:02x}").unwrap();
    }
    out.push_str("];\n#[rustfmt::skip]\n");
    out.push_str("pub const MLE_PROOF_ABI_TEST_SELECTOR_V2: [u8; 4] = [");
    for (index, byte) in derived.proof_test_selector.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        write!(out, "0x{byte:02x}").unwrap();
    }
    out.push_str("];\n#[rustfmt::skip]\n");
    writeln!(
        out,
        "pub const MLE_PROOF_ABI_FIELDS_V2: [(&str, &str, &str, &str); {}] = [",
        schema.proof_abi.len()
    )
    .unwrap();
    for field in &schema.proof_abi {
        writeln!(
            out,
            "    ({:?}, {:?}, {:?}, {:?}),",
            field.name, field.json_name, field.solidity_type, field.abi_type
        )
        .unwrap();
    }
    out.push_str("];\n");
    number!("COMPACT_FIELD_COUNT_V2", schema.compact_fields.len());
    out.push_str("#[rustfmt::skip]\n");
    out.push_str("pub const COMPACT_LAYOUT_HASH_V2: [u8; 32] = [");
    for (index, byte) in derived.compact_layout_hash.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        write!(out, "0x{byte:02x}").unwrap();
    }
    out.push_str("];\n#[rustfmt::skip]\n");
    writeln!(
        out,
        "pub const COMPACT_FIELDS_V2: [(&str, &str, &str); {}] = [",
        schema.compact_fields.len()
    )
    .unwrap();
    for field in &schema.compact_fields {
        writeln!(
            out,
            "    ({:?}, {:?}, {:?}),",
            field.name, field.encoding, field.shape
        )
        .unwrap();
    }
    out.push_str("];\n");
    out
}

fn render_solidity(schema: &ProtocolSchemaV2, derived: &Derived) -> String {
    let mut out = String::new();
    out.push_str(
        "// SPDX-License-Identifier: MIT OR Apache-2.0\n\
         pragma solidity ^0.8.25;\n\n\
         // @generated by tests/protocol_schema_v2_codegen.rs from protocol/mle_whir_v2.json.\n\
         // Do not edit by hand.\n\n",
    );
    macro_rules! number {
        ($name:expr, $value:expr) => {
            writeln!(out, "uint256 constant {} = {};", $name, $value).unwrap()
        };
    }
    number!("MLE_SCHEMA_VERSION_CURRENT", schema.schema_version);
    number!("MLE_PROTOCOL_VERSION_CURRENT", schema.mle_protocol_version);
    writeln!(
        out,
        "string constant OUTER_TRANSCRIPT_PROTOCOL_V2 = {:?};",
        schema.outer_transcript_protocol
    )
    .unwrap();
    writeln!(
        out,
        "string constant PACKED_PCS_SCHEMA_DOMAIN_V2 = {:?};",
        schema.packed_schema_domain
    )
    .unwrap();
    writeln!(
        out,
        "string constant WHIR_SESSION_SPLIT_V2 = {:?};",
        schema.whir_split_session
    )
    .unwrap();
    writeln!(
        out,
        "bytes8 constant COMPACT_MAGIC_V2 = {:?};",
        schema.compact_magic
    )
    .unwrap();
    writeln!(
        out,
        "string constant TRANSCRIPT_FRAME_PREFIX_V2 = {:?};",
        schema.transcript_frame_prefix
    )
    .unwrap();
    writeln!(
        out,
        "string constant TRANSCRIPT_CHALLENGE_PREFIX_V2 = {:?};",
        schema.transcript_challenge_prefix
    )
    .unwrap();
    writeln!(
        out,
        "string constant CIRCUIT_CONFIG_HASH_DOMAIN_V2 = {:?};",
        schema.circuit_config_hash_domain
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant BASE_FIELD_MODULUS_V2 = 0x{:016x};",
        schema.base_field_modulus
    )
    .unwrap();
    number!("BASE_FIELD_TWO_ADICITY_V2", schema.base_field_two_adicity);
    number!(
        "BASE_FIELD_POWER_OF_TWO_GENERATOR_V2",
        schema.base_field_power_of_two_generator
    );
    number!(
        "BASE_FIELD_MULTIPLICATIVE_GENERATOR_V2",
        schema.base_field_multiplicative_generator
    );
    number!("EXTENSION_NON_RESIDUE_V2", schema.extension_non_residue);
    number!(
        "INNER_EXTENSION_NON_RESIDUE_V2",
        schema.inner_extension_non_residue
    );
    number!("EXTENSION_FIELD_LIMBS_V2", schema.extension_field_limbs);
    number!("INNER_EXTENSION_DEGREE_V2", schema.inner_extension_degree);
    number!(
        "NUM_PACKED_VECTORS_PER_GROUP_V2",
        schema.packed_vectors_per_group
    );
    number!("PACKED_VARIABLE_ORDER_CODE_V2", schema.variable_order_code);
    number!("LOG_ROUND_DEGREE_V2", schema.log_round_degree);
    number!("GATE_SUMCHECK_COUNT_V2", schema.gate_sumcheck_count);
    number!("MAX_ROW_VARIABLES_V2", schema.max_row_variables);
    number!("MAX_ROUTED_WIRES_V2", schema.max_routed_wires);
    number!("MAX_CONSTITUENT_WIDTH_V2", schema.max_constituent_width);
    number!(
        "MAX_CONSTITUENT_INDEX_BITS_V2",
        schema.max_constituent_index_bits
    );
    number!("MAX_GATE_CONSTRAINTS_V2", schema.max_gate_constraints);
    number!("MAX_GATE_ROUND_DEGREE_V2", schema.max_gate_round_degree);
    number!("MAX_GATE_ROWS_V2", schema.max_gate_rows);
    number!("CIRCUIT_DIGEST_LENGTH_V2", schema.circuit_digest_length);
    number!("MAX_PUBLIC_INPUTS_V2", schema.max_public_inputs);
    number!("WHIR_SECURITY_LEVEL_V2", schema.whir_security_level);
    number!("WHIR_POW_BITS_V2", schema.whir_pow_bits);
    number!(
        "WHIR_MAX_STARTING_LOG_INV_RATE_V2",
        schema.whir_max_starting_log_inv_rate
    );
    number!("WHIR_FOLDING_FACTOR_V2", schema.whir_folding_factor);
    writeln!(
        out,
        "string constant WHIR_HASH_ID_V2 = {:?};",
        schema.whir_hash_id
    )
    .unwrap();
    writeln!(
        out,
        "bool constant WHIR_UNIQUE_DECODING_V2 = {};",
        schema.whir_unique_decoding
    )
    .unwrap();
    writeln!(
        out,
        "bool constant WHIR_DEDUPLICATE_IN_DOMAIN_V2 = {};",
        schema.whir_deduplicate_in_domain
    )
    .unwrap();
    number!("MAX_WHIR_NARG_BYTES_V2", schema.max_whir_narg_bytes);
    number!("MAX_WHIR_HINT_BYTES_V2", schema.max_whir_hint_bytes);
    number!("MAX_COMPACT_PROOF_BYTES_V2", schema.max_compact_proof_bytes);
    for tag in &schema.transcript_tags {
        writeln!(out, "uint8 constant {}_V2 = {};", tag.constant, tag.value).unwrap();
    }
    number!(
        "STATEMENT_METADATA_FIELD_COUNT_V2",
        schema.statement_metadata.len()
    );
    number!(
        "RELATION_CHALLENGE_COUNT_V2",
        schema.relation_challenges.len()
    );
    for (index, challenge) in schema.relation_challenges.iter().enumerate() {
        number!(
            format!("RELATION_CHALLENGE_{}_V2", challenge.to_ascii_uppercase()),
            index
        );
    }
    number!(
        "OUTER_ROUND_MESSAGE_COUNT_V2",
        schema.outer_round_messages.len()
    );
    for (index, message) in schema.outer_round_messages.iter().enumerate() {
        number!(
            format!("OUTER_ROUND_MESSAGE_{}_V2", message.to_ascii_uppercase()),
            index
        );
    }
    number!(
        "OUTER_ROUND_CHALLENGE_COUNT_V2",
        schema.outer_round_challenges.len()
    );
    for (index, challenge) in schema.outer_round_challenges.iter().enumerate() {
        number!(
            format!(
                "OUTER_ROUND_CHALLENGE_{}_V2",
                challenge.to_ascii_uppercase()
            ),
            index
        );
    }
    for domain in &schema.transcript_domains {
        writeln!(
            out,
            "string constant {}_V2 = {:?};",
            domain.constant, domain.value
        )
        .unwrap();
    }
    number!("NUM_PCS_GROUPS_V2", schema.groups.len());
    number!("NUM_PCS_TERMINAL_POINTS_V2", schema.terminal_points.len());
    number!("NUM_PCS_CLAIMS_V2", derived.claim_count);
    number!("NUM_BOUND_PCS_CLAIMS_V2", schema.bound_cells.len());
    for (index, item) in schema.groups.iter().enumerate() {
        number!(&item.constant, index);
    }
    for (index, item) in schema.terminal_points.iter().enumerate() {
        number!(&item.constant, index);
    }
    write!(
        out,
        "bytes{} constant PACKED_BOUND_CLAIM_MASK_V2 = hex\"",
        derived.bound_mask.len()
    )
    .unwrap();
    for byte in &derived.bound_mask {
        write!(out, "{byte:02x}").unwrap();
    }
    out.push_str("\";\n");
    number!("MLE_PROOF_ABI_FIELD_COUNT_V2", schema.proof_abi.len());
    writeln!(
        out,
        "string constant MLE_PROOF_ABI_SIGNATURE_V2 = {:?};",
        derived.proof_abi_signature
    )
    .unwrap();
    out.push_str("bytes32 constant MLE_PROOF_LAYOUT_HASH_V2 = 0x");
    for byte in derived.proof_layout_hash {
        write!(out, "{byte:02x}").unwrap();
    }
    out.push_str(";\nbytes4 constant MLE_PROOF_ABI_TEST_SELECTOR_V2 = 0x");
    for byte in derived.proof_test_selector {
        write!(out, "{byte:02x}").unwrap();
    }
    out.push_str(";\n");
    number!("COMPACT_FIELD_COUNT_V2", schema.compact_fields.len());
    out.push_str("bytes32 constant COMPACT_LAYOUT_HASH_V2 = 0x");
    for byte in derived.compact_layout_hash {
        write!(out, "{byte:02x}").unwrap();
    }
    out.push_str(";\n");
    out
}

fn write_or_check(path: &Path, expected: &str, write: bool) {
    if write {
        std::fs::write(path, expected)
            .unwrap_or_else(|error| panic!("failed to regenerate {}: {error}", path.display()));
    }
    let actual = std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    assert_eq!(
        actual,
        expected,
        "stale v2 schema artifact {}; regenerate deliberately",
        path.display()
    );
}

fn solidity_struct_fields(source: &str, struct_name: &str) -> Vec<(String, String)> {
    let marker = format!("struct {struct_name} {{");
    let tail = source
        .split_once(&marker)
        .unwrap_or_else(|| panic!("missing Solidity {marker}"))
        .1;
    let body = tail
        .split_once("\n    }")
        .unwrap_or_else(|| panic!("unterminated Solidity {marker}"))
        .0;
    body.lines()
        .filter_map(|line| {
            let declaration = line.split("//").next().unwrap().trim();
            if !declaration.ends_with(';') {
                return None;
            }
            let parts: Vec<&str> = declaration
                .trim_end_matches(';')
                .split_whitespace()
                .collect();
            assert_eq!(
                parts.len(),
                2,
                "unsupported Solidity field declaration in {struct_name}: {declaration}"
            );
            Some((parts[0].to_string(), parts[1].to_string()))
        })
        .collect()
}

fn assert_proof_layout_consumer(schema: &ProtocolSchemaV2, manifest: &Path) {
    let verifier_path = manifest.join("contracts/src/MleVerifierV2.sol");
    let verifier = std::fs::read_to_string(&verifier_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", verifier_path.display()));
    let actual = solidity_struct_fields(&verifier, "MleProof");
    let expected: Vec<(String, String)> = schema
        .proof_abi
        .iter()
        .map(|field| (field.solidity_type.clone(), field.name.clone()))
        .collect();
    assert_eq!(
        actual, expected,
        "MleVerifierV2.MleProof drifted from protocol/mle_whir_v2.json"
    );
}

#[test]
fn generated_v2_rust_and_solidity_schema_are_current() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let schema_path = manifest.join("protocol/mle_whir_v2.json");
    let schema: ProtocolSchemaV2 = serde_json::from_str(
        &std::fs::read_to_string(&schema_path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", schema_path.display())),
    )
    .expect("canonical v2 protocol schema JSON");
    let derived = validate_and_derive(&schema);
    assert_proof_layout_consumer(&schema, manifest);
    let rust = render_rust(&schema, &derived);
    let solidity = render_solidity(&schema, &derived);
    let write = std::env::var_os("MLE_WRITE_PROTOCOL_SCHEMA_V2").as_deref()
        == Some(std::ffi::OsStr::new("1"));

    write_or_check(&manifest.join("src/generated/mle_whir_v2.rs"), &rust, write);
    write_or_check(
        &manifest.join("contracts/src/generated/MleWhirV2.sol"),
        &solidity,
        write,
    );

    use plonky2_mle::protocol_schema_v2 as generated;
    assert_eq!(
        generated::MLE_PROTOCOL_VERSION_CURRENT,
        schema.mle_protocol_version
    );
    assert_eq!(generated::NUM_PCS_GROUPS_V2, schema.groups.len());
    assert_eq!(
        generated::NUM_PCS_TERMINAL_POINTS_V2,
        schema.terminal_points.len()
    );
    assert_eq!(generated::PACKED_BOUND_CLAIM_MASK_V2, [0x1f]);
    assert_eq!(
        generated::MLE_PROOF_ABI_FIELD_COUNT_V2,
        schema.proof_abi.len()
    );
    assert_eq!(
        generated::MLE_PROOF_ABI_SIGNATURE_V2,
        derived.proof_abi_signature
    );
    assert_eq!(
        generated::MLE_PROOF_LAYOUT_HASH_V2,
        derived.proof_layout_hash
    );
    assert_eq!(
        generated::MLE_PROOF_ABI_TEST_SELECTOR_V2,
        derived.proof_test_selector
    );
    for (generated_field, field) in generated::MLE_PROOF_ABI_FIELDS_V2
        .iter()
        .zip(&schema.proof_abi)
    {
        assert_eq!(
            *generated_field,
            (
                field.name.as_str(),
                field.json_name.as_str(),
                field.solidity_type.as_str(),
                field.abi_type.as_str()
            )
        );
    }
    assert_eq!(
        generated::COMPACT_LAYOUT_HASH_V2,
        derived.compact_layout_hash
    );
    assert_eq!(
        generated::COMPACT_FIELDS_V2.len(),
        schema.compact_fields.len()
    );
}
