//! Cross-language packed-PCS schema generation and drift check.
//!
//! `protocol/mle_whir_v1.json` is the only hand-maintained source for the
//! protocol/version labels, ordered commitment groups, ordered terminal points,
//! terminal-equation claim mask, and public Solidity proof-ABI manifest. Rust
//! and Solidity consume generated artifacts. The normal test path is read-only
//! and fails on stale output or a handwritten proof-layout drift; set
//! `MLE_WRITE_PROTOCOL_SCHEMA=1` to regenerate both artifacts deliberately.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use serde::Deserialize;
use sha3::{Digest, Keccak256};

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProtocolSchema {
    schema_version: u64,
    mle_protocol_version: u64,
    outer_transcript_protocol: String,
    packed_schema_domain: String,
    whir_split_session: String,
    extension_field_limbs: usize,
    packed_vectors_per_group: usize,
    variable_order_code: usize,
    proof_abi: Vec<ProofAbiField>,
    groups: Vec<OrderedItem>,
    terminal_points: Vec<OrderedItem>,
    bound_cells: Vec<BoundCell>,
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
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProofAbiField {
    name: String,
    json_name: String,
    solidity_type: String,
    abi_type: String,
}

struct DerivedSchema {
    claim_count: usize,
    bound_mask: Vec<u8>,
    proof_abi_signature: String,
    proof_layout_hash: [u8; 32],
    proof_test_selector: [u8; 4],
}

fn is_constant_identifier(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte == b'_' || byte.is_ascii_uppercase() || byte.is_ascii_digit())
        && value.as_bytes()[0].is_ascii_uppercase()
}

fn is_protocol_label(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b'/'))
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

fn derive_proof_layout(proof_abi: &[ProofAbiField]) -> (String, [u8; 32]) {
    let signature = format!(
        "({})",
        proof_abi
            .iter()
            .map(|field| field.abi_type.as_str())
            .collect::<Vec<_>>()
            .join(",")
    );
    let mut semantic_layout = String::from("plonky2-mle-proof-abi-v1\n");
    for field in proof_abi {
        writeln!(
            semantic_layout,
            "{}\t{}\t{}\t{}",
            field.name, field.json_name, field.solidity_type, field.abi_type
        )
        .unwrap();
    }
    let hash: [u8; 32] = Keccak256::digest(semantic_layout.as_bytes()).into();
    (signature, hash)
}

fn ordered_indices(items: &[OrderedItem], kind: &str) -> BTreeMap<String, usize> {
    assert!(!items.is_empty(), "{kind} order must not be empty");
    let mut names = BTreeMap::new();
    let mut constants = BTreeSet::new();
    for (index, item) in items.iter().enumerate() {
        assert!(
            is_protocol_label(&item.name),
            "invalid {kind} name: {}",
            item.name
        );
        assert!(
            is_constant_identifier(&item.constant),
            "invalid {kind} constant: {}",
            item.constant
        );
        assert!(
            names.insert(item.name.clone(), index).is_none(),
            "duplicate {kind} name: {}",
            item.name
        );
        assert!(
            constants.insert(item.constant.clone()),
            "duplicate {kind} constant: {}",
            item.constant
        );
    }
    names
}

fn validate_and_derive(schema: &ProtocolSchema) -> DerivedSchema {
    assert_eq!(
        schema.schema_version, 1,
        "unsupported schema artifact version"
    );
    assert_eq!(schema.mle_protocol_version, 1, "v1 generator only");
    assert_eq!(
        schema.extension_field_limbs, 3,
        "grouped PCS uses Field64_3"
    );
    assert_eq!(
        schema.packed_vectors_per_group, 1,
        "v1 commits one packed vector per group"
    );
    assert_eq!(
        schema.variable_order_code, 0,
        "v1 variable order is row then constituent index, both LSB-first"
    );
    assert!(is_protocol_label(&schema.outer_transcript_protocol));
    assert!(is_protocol_label(&schema.packed_schema_domain));
    assert!(is_protocol_label(&schema.whir_split_session));

    // `MleVerifier.MleProof` is a public ABI. A field reorder is a wire-format
    // change even when every field retains the same Solidity type. Keep names,
    // fixture keys, source-level types, and canonical ABI types together in
    // the versioned artifact so consumers can migrate without reconstructing
    // the layout from three handwritten definitions.
    assert_eq!(schema.proof_abi.len(), 48, "v1 MleProof ABI field count");
    let mut proof_names = BTreeSet::new();
    let mut json_names = BTreeSet::new();
    for field in &schema.proof_abi {
        assert!(
            is_field_identifier(&field.name),
            "invalid proof ABI field name"
        );
        assert!(
            is_field_identifier(&field.json_name),
            "invalid proof fixture JSON field name"
        );
        assert!(
            is_type_expression(&field.solidity_type, true),
            "invalid Solidity source type for {}",
            field.name
        );
        assert!(
            is_type_expression(&field.abi_type, false),
            "invalid canonical ABI type for {}",
            field.name
        );
        assert!(
            proof_names.insert(field.name.as_str()),
            "duplicate proof ABI field {}",
            field.name
        );
        assert!(
            json_names.insert(field.json_name.as_str()),
            "duplicate proof fixture key {}",
            field.json_name
        );
    }
    assert_eq!(schema.proof_abi[0].name, "protocolVersion");
    assert_eq!(schema.proof_abi[1].name, "constituentWidth");
    let (proof_abi_signature, proof_layout_hash) = derive_proof_layout(&schema.proof_abi);
    // The proof is one tuple-valued function argument, so the selector
    // signature needs both the function argument list and the tuple's own
    // parentheses: `accept((...))`.
    let selector_digest = Keccak256::digest(format!("accept({proof_abi_signature})").as_bytes());
    let proof_test_selector = selector_digest[..4]
        .try_into()
        .expect("Keccak selector prefix");

    let groups = ordered_indices(&schema.groups, "group");
    let points = ordered_indices(&schema.terminal_points, "terminal point");
    // The current proof ABI has four named roots and four named terminal
    // sumchecks. A v2 artifact must be introduced before either cardinality
    // changes; silently widening v1 would leave ABI fields unbound.
    assert_eq!(groups.len(), 4, "v1 group count");
    assert_eq!(points.len(), 4, "v1 terminal-point count");

    let claim_count = groups
        .len()
        .checked_mul(points.len())
        .expect("claim matrix overflow");
    let mut bound_mask = vec![0u8; (claim_count + 7) / 8];
    let mut seen = BTreeSet::new();
    for cell in &schema.bound_cells {
        let point = *points
            .get(&cell.point)
            .unwrap_or_else(|| panic!("unknown bound-cell point: {}", cell.point));
        let group = *groups
            .get(&cell.group)
            .unwrap_or_else(|| panic!("unknown bound-cell group: {}", cell.group));
        let slot = point * groups.len() + group;
        assert!(seen.insert(slot), "duplicate bound cell at slot {slot}");
        bound_mask[slot >> 3] |= 1 << (slot & 7);
    }
    assert_eq!(seen.len(), 9, "v1 terminal equations bind nine claim cells");
    DerivedSchema {
        claim_count,
        bound_mask,
        proof_abi_signature,
        proof_layout_hash,
        proof_test_selector,
    }
}

fn render_rust(schema: &ProtocolSchema, derived: &DerivedSchema) -> String {
    let mut out = String::new();
    out.push_str(
        "// @generated by tests/protocol_schema_codegen.rs from protocol/mle_whir_v1.json.\n\
         // Do not edit by hand; run with MLE_WRITE_PROTOCOL_SCHEMA=1 to regenerate.\n\n",
    );
    writeln!(
        out,
        "pub const SCHEMA_VERSION: u64 = {};",
        schema.schema_version
    )
    .unwrap();
    writeln!(
        out,
        "pub const MLE_PROTOCOL_VERSION: u64 = {};",
        schema.mle_protocol_version
    )
    .unwrap();
    writeln!(
        out,
        "pub const MLE_TRANSCRIPT_PROTOCOL: &str = {:?};",
        schema.outer_transcript_protocol
    )
    .unwrap();
    writeln!(
        out,
        "pub const PACKED_PCS_SCHEMA_DOMAIN: &str = {:?};",
        schema.packed_schema_domain
    )
    .unwrap();
    writeln!(
        out,
        "pub const WHIR_SESSION_SPLIT: &str = {:?};",
        schema.whir_split_session
    )
    .unwrap();
    writeln!(
        out,
        "pub const EXTENSION_FIELD_LIMBS: usize = {};",
        schema.extension_field_limbs
    )
    .unwrap();
    writeln!(
        out,
        "pub const NUM_PACKED_VECTORS_PER_GROUP: usize = {};",
        schema.packed_vectors_per_group
    )
    .unwrap();
    writeln!(
        out,
        "pub const PACKED_VARIABLE_ORDER_CODE: usize = {};",
        schema.variable_order_code
    )
    .unwrap();
    writeln!(
        out,
        "pub const MLE_PROOF_ABI_FIELD_COUNT: usize = {};",
        schema.proof_abi.len()
    )
    .unwrap();
    writeln!(
        out,
        "pub const MLE_PROOF_ABI_SIGNATURE: &str = {:?};",
        derived.proof_abi_signature
    )
    .unwrap();
    // Keep machine-generated tables byte-stable under `cargo fmt --check`.
    // Their compact representation is deliberate and regenerated as a unit.
    out.push_str("#[rustfmt::skip]\n");
    out.push_str("pub const MLE_PROOF_LAYOUT_HASH: [u8; 32] = [");
    for (index, byte) in derived.proof_layout_hash.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        write!(out, "0x{byte:02x}").unwrap();
    }
    out.push_str("];\n");
    out.push_str("pub const MLE_PROOF_ABI_TEST_SELECTOR: [u8; 4] = [");
    for (index, byte) in derived.proof_test_selector.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        write!(out, "0x{byte:02x}").unwrap();
    }
    out.push_str("];\n");
    out.push_str("#[rustfmt::skip]\n");
    writeln!(
        out,
        "pub const MLE_PROOF_ABI_FIELDS: [(&str, &str, &str, &str); {}] = [",
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
    writeln!(
        out,
        "pub const NUM_SPLIT_COMMITMENTS: usize = {};",
        schema.groups.len()
    )
    .unwrap();
    writeln!(
        out,
        "pub const NUM_PCS_TERMINAL_POINTS: usize = {};",
        schema.terminal_points.len()
    )
    .unwrap();
    writeln!(
        out,
        "pub const NUM_PCS_CLAIMS: usize = {};",
        derived.claim_count
    )
    .unwrap();
    writeln!(
        out,
        "pub const NUM_BOUND_PCS_CLAIMS: usize = {};",
        schema.bound_cells.len()
    )
    .unwrap();
    for (index, item) in schema.groups.iter().enumerate() {
        writeln!(out, "pub const {}: usize = {index};", item.constant).unwrap();
    }
    for (index, item) in schema.terminal_points.iter().enumerate() {
        writeln!(out, "pub const {}: usize = {index};", item.constant).unwrap();
    }
    write!(
        out,
        "pub const PACKED_BOUND_CLAIM_MASK: [u8; {}] = [",
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
    out
}

fn render_solidity(schema: &ProtocolSchema, derived: &DerivedSchema) -> String {
    let mut out = String::new();
    out.push_str(
        "// SPDX-License-Identifier: MIT OR Apache-2.0\n\
         pragma solidity ^0.8.25;\n\n\
         // @generated by tests/protocol_schema_codegen.rs from protocol/mle_whir_v1.json.\n\
         // Do not edit by hand; run with MLE_WRITE_PROTOCOL_SCHEMA=1 to regenerate.\n\n",
    );
    writeln!(
        out,
        "uint256 constant MLE_SCHEMA_VERSION = {};",
        schema.schema_version
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant MLE_PROTOCOL_VERSION = {};",
        schema.mle_protocol_version
    )
    .unwrap();
    writeln!(
        out,
        "string constant MLE_TRANSCRIPT_PROTOCOL = \"{}\";",
        schema.outer_transcript_protocol
    )
    .unwrap();
    writeln!(
        out,
        "string constant PACKED_PCS_SCHEMA_DOMAIN = \"{}\";",
        schema.packed_schema_domain
    )
    .unwrap();
    writeln!(
        out,
        "string constant WHIR_SPLIT_SESSION = \"{}\";",
        schema.whir_split_session
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant EXTENSION_FIELD_LIMBS = {};",
        schema.extension_field_limbs
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant NUM_PACKED_VECTORS_PER_GROUP = {};",
        schema.packed_vectors_per_group
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant PACKED_VARIABLE_ORDER_CODE = {};",
        schema.variable_order_code
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant MLE_PROOF_ABI_FIELD_COUNT = {};",
        schema.proof_abi.len()
    )
    .unwrap();
    writeln!(out, "string constant MLE_PROOF_ABI_SIGNATURE =").unwrap();
    writeln!(out, "    \"{}\";", derived.proof_abi_signature).unwrap();
    out.push_str("bytes32 constant MLE_PROOF_LAYOUT_HASH = 0x");
    for byte in derived.proof_layout_hash {
        write!(out, "{byte:02x}").unwrap();
    }
    out.push_str(";\n");
    out.push_str("bytes4 constant MLE_PROOF_ABI_TEST_SELECTOR = 0x");
    for byte in derived.proof_test_selector {
        write!(out, "{byte:02x}").unwrap();
    }
    out.push_str(";\n");
    writeln!(
        out,
        "uint256 constant NUM_PCS_GROUPS = {};",
        schema.groups.len()
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant NUM_PCS_TERMINAL_POINTS = {};",
        schema.terminal_points.len()
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant NUM_PCS_CLAIMS = {};",
        derived.claim_count
    )
    .unwrap();
    writeln!(
        out,
        "uint256 constant NUM_BOUND_PCS_CLAIMS = {};",
        schema.bound_cells.len()
    )
    .unwrap();
    for (index, item) in schema.groups.iter().enumerate() {
        writeln!(out, "uint256 constant {} = {index};", item.constant).unwrap();
    }
    for (index, item) in schema.terminal_points.iter().enumerate() {
        writeln!(out, "uint256 constant {} = {index};", item.constant).unwrap();
    }
    out.push_str("bytes2 constant PACKED_BOUND_CLAIM_MASK = hex\"");
    for byte in &derived.bound_mask {
        write!(out, "{byte:02x}").unwrap();
    }
    out.push_str("\";\n");
    out
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

fn rust_struct_field_names(source: &str, struct_name: &str) -> BTreeSet<String> {
    let marker = format!("pub struct {struct_name} {{");
    let tail = source
        .split_once(&marker)
        .unwrap_or_else(|| panic!("missing Rust {marker}"))
        .1;
    let body = tail
        .split_once("\n}")
        .unwrap_or_else(|| panic!("unterminated Rust {marker}"))
        .0;
    body.lines()
        .filter_map(|line| {
            let declaration = line.split("//").next().unwrap().trim();
            let field = declaration.strip_prefix("pub ")?.split_once(':')?.0.trim();
            Some(field.to_string())
        })
        .collect()
}

fn camel_to_snake(value: &str) -> String {
    let mut snake = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_uppercase() {
            snake.push('_');
            snake.push((byte + (b'a' - b'A')) as char);
        } else {
            snake.push(byte as char);
        }
    }
    snake
}

fn assert_proof_layout_consumers(schema: &ProtocolSchema, manifest: &Path) {
    let verifier_path = manifest.join("contracts/src/MleVerifier.sol");
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
        "MleVerifier.MleProof drifted from protocol/mle_whir_v1.json"
    );

    // JSON object order is not an ABI property, but every canonical ABI field
    // must have a serializable key in the strict Rust fixture. Extra fixture
    // keys are verifier/VK inputs or rederived transcript checkpoints and are
    // deliberately outside the Solidity proof tuple.
    let fixture_path = manifest.join("src/fixture.rs");
    let fixture = std::fs::read_to_string(&fixture_path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", fixture_path.display()));
    let fixture_fields = rust_struct_field_names(&fixture, "ProofFixture");
    for field in &schema.proof_abi {
        let rust_name = camel_to_snake(&field.json_name);
        assert!(
            fixture_fields.contains(&rust_name),
            "ProofFixture is missing canonical JSON key {} ({rust_name})",
            field.json_name
        );
    }
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
        "stale generated protocol schema {}; run \
         `MLE_WRITE_PROTOCOL_SCHEMA=1 cargo test -p plonky2_mle --test protocol_schema_codegen`",
        path.display()
    );
}

#[test]
fn generated_rust_and_solidity_schema_are_current() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let schema_path = manifest.join("protocol/mle_whir_v1.json");
    let schema: ProtocolSchema = serde_json::from_str(
        &std::fs::read_to_string(&schema_path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", schema_path.display())),
    )
    .expect("canonical protocol schema JSON");
    let derived = validate_and_derive(&schema);
    assert_proof_layout_consumers(&schema, manifest);
    let rust = render_rust(&schema, &derived);
    let solidity = render_solidity(&schema, &derived);
    let write =
        std::env::var_os("MLE_WRITE_PROTOCOL_SCHEMA").as_deref() == Some(std::ffi::OsStr::new("1"));

    write_or_check(&manifest.join("src/generated/mle_whir_v1.rs"), &rust, write);
    write_or_check(
        &manifest.join("contracts/src/generated/MleWhirV1.sol"),
        &solidity,
        write,
    );

    // Check that the artifact compiled into the Rust verifier is the same
    // schema object, rather than a second handwritten constant set.
    assert_eq!(
        plonky2_mle::protocol_schema::MLE_PROTOCOL_VERSION,
        schema.mle_protocol_version
    );
    assert_eq!(
        plonky2_mle::protocol_schema::NUM_SPLIT_COMMITMENTS,
        schema.groups.len()
    );
    assert_eq!(
        plonky2_mle::protocol_schema::NUM_PCS_TERMINAL_POINTS,
        schema.terminal_points.len()
    );
    assert_eq!(
        plonky2_mle::protocol_schema::PACKED_BOUND_CLAIM_MASK.as_slice(),
        derived.bound_mask
    );
    assert_eq!(
        plonky2_mle::protocol_schema::MLE_PROOF_ABI_FIELD_COUNT,
        schema.proof_abi.len()
    );
    assert_eq!(
        plonky2_mle::protocol_schema::MLE_PROOF_ABI_SIGNATURE,
        derived.proof_abi_signature
    );
    assert_eq!(
        plonky2_mle::protocol_schema::MLE_PROOF_LAYOUT_HASH,
        derived.proof_layout_hash
    );
    assert_eq!(
        plonky2_mle::protocol_schema::MLE_PROOF_ABI_TEST_SELECTOR,
        derived.proof_test_selector
    );
    for (generated, field) in plonky2_mle::protocol_schema::MLE_PROOF_ABI_FIELDS
        .iter()
        .zip(&schema.proof_abi)
    {
        assert_eq!(
            *generated,
            (
                field.name.as_str(),
                field.json_name.as_str(),
                field.solidity_type.as_str(),
                field.abi_type.as_str()
            )
        );
    }
}
