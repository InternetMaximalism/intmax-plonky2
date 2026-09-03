//! One-shot wire-size probe for one canonical v2 three-group/two-point proof
//! instance at a supplied circuit shape.
//!
//! The values are synthetic, but both WHIR streams are produced by the native
//! PCS and the Solidity ABI length is produced by the production fixture
//! encoder. WHIR query de-duplication makes the result instance-dependent; use
//! the deterministic resource-bound tests, not this sample, for DA admission.

use plonky2_mle::commitment::whir_pcs::WhirPCS;
use plonky2_mle::compact_v2::CompactV2Shape;
use plonky2_mle::fixture_v2::{
    solidity_abi_encode_mle_proof_v2, CoefficientRoundV2Fixture, Ext3V2Fixture, MleProofV2Fixture,
    SumcheckProofV2Fixture,
};
use plonky2_mle::proof_v2::{constituent_index_bits_v2, packed_group_num_vars_v2};
use plonky2_mle::protocol_schema_v2::{
    CIRCUIT_DIGEST_LENGTH_V2, LOG_ROUND_DEGREE_V2, MAX_COMPACT_PROOF_BYTES_V2,
    MAX_WHIR_HINT_BYTES_V2, MAX_WHIR_NARG_BYTES_V2, MLE_PROTOCOL_VERSION_CURRENT,
    NUM_PCS_GROUPS_V2, NUM_PCS_TERMINAL_POINTS_V2, WHIR_SESSION_SPLIT_V2,
};
use whir::algebra::fields::{Field64, Field64_3};

fn main() {
    let mut args = std::env::args().skip(1);
    let row_bits: usize = args.next().as_deref().unwrap_or("13").parse().unwrap();
    let constituent_width: usize = args.next().as_deref().unwrap_or("160").parse().unwrap();
    let num_constants: usize = args.next().as_deref().unwrap_or("5").parse().unwrap();
    let num_routed_wires: usize = args.next().as_deref().unwrap_or("80").parse().unwrap();
    let num_wires: usize = args.next().as_deref().unwrap_or("135").parse().unwrap();
    let num_public_inputs: usize = args.next().as_deref().unwrap_or("8").parse().unwrap();
    let quotient_degree_factor: usize = args.next().as_deref().unwrap_or("8").parse().unwrap();
    let num_points = NUM_PCS_TERMINAL_POINTS_V2;
    let num_vars = packed_group_num_vars_v2(row_bits, constituent_width);
    let size = 1usize << num_vars;
    let pcs = WhirPCS::for_constituents(num_vars, 1);

    let groups: Vec<Vec<Vec<Field64>>> = (0..NUM_PCS_GROUPS_V2)
        .map(|group| {
            vec![(0..size)
                .map(|row| {
                    // A nonconstant, deterministic table keeps the probe
                    // reproducible while avoiding the all-zero final fold.
                    let value = (row as u64)
                        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                        .wrapping_add(1 + 0x10001 * group as u64);
                    Field64::from(value)
                })
                .collect()]
        })
        .collect();
    let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT_V2);
    let points: Vec<Vec<Field64_3>> = (0..num_points)
        .map(|point| {
            (0..num_vars)
                .map(|i| {
                    Field64_3::new(
                        Field64::from((3 * i + 17 * point + 2) as u64),
                        Field64::from((5 * i + 19 * point + 7) as u64),
                        Field64::from((11 * i + 23 * point + 13) as u64),
                    )
                })
                .collect()
        })
        .collect();
    let point_refs: Vec<&[Field64_3]> = points.iter().map(Vec::as_slice).collect();
    let (proof, _) = pcs.prove_grouped_with_eval(data, &point_refs);

    let gate_round_degree = quotient_degree_factor + 2;
    let preprocessed_len = num_constants + num_routed_wires;
    let norm_inverse_len = 2 * num_routed_wires;
    assert_eq!(
        constituent_width,
        preprocessed_len.max(num_wires).max(norm_inverse_len),
        "constituent width must be canonical for the supplied circuit shape"
    );
    let compact_shape = CompactV2Shape {
        degree_bits: row_bits,
        constituent_width,
        circuit_digest_len: CIRCUIT_DIGEST_LENGTH_V2,
        public_inputs_len: num_public_inputs,
        num_constants,
        num_routed_wires,
        num_wires,
        gate_round_degree,
        max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
        max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
        max_encoded_bytes: MAX_COMPACT_PROOF_BYTES_V2,
    };
    let compact_bytes = compact_shape
        .encoded_len(proof.narg_string.len(), proof.hints.len())
        .expect("canonical v2 compact proof must fit its DA cap");

    let zero_limb = "0x0000000000000000".to_string();
    let zero_root = format!("0x{}", "00".repeat(32));
    let ext3_vec = |length: usize| {
        vec![
            Ext3V2Fixture {
                c0: zero_limb.clone(),
                c1: zero_limb.clone(),
                c2: zero_limb.clone(),
            };
            length
        ]
    };
    let sumcheck = |degree: usize| SumcheckProofV2Fixture {
        rounds: (0..row_bits)
            .map(|_| CoefficientRoundV2Fixture {
                non_constant: ext3_vec(degree),
            })
            .collect(),
    };
    let fixture = MleProofV2Fixture {
        protocol_version: MLE_PROTOCOL_VERSION_CURRENT,
        constituent_width,
        circuit_digest: vec![zero_limb.clone(); CIRCUIT_DIGEST_LENGTH_V2],
        public_inputs: vec![zero_limb.clone(); num_public_inputs],
        preprocessed_root: zero_root.clone(),
        witness_root: zero_root.clone(),
        norm_inverse_root: zero_root,
        whir_transcript: encode_hex(&proof.narg_string),
        whir_hints: encode_hex(&proof.hints),
        log_proof: sumcheck(LOG_ROUND_DEGREE_V2),
        log_preprocessed: ext3_vec(preprocessed_len),
        log_witness: ext3_vec(num_wires),
        log_norm_inverse: ext3_vec(norm_inverse_len),
        gate_proof: sumcheck(gate_round_degree),
        gate_preprocessed: ext3_vec(preprocessed_len),
        gate_witness: ext3_vec(num_wires),
    };
    let solidity_abi_bytes = solidity_abi_encode_mle_proof_v2(&fixture)
        .expect("synthetic canonical ABI shape")
        .len();

    println!("row_bits={row_bits}");
    println!(
        "index_bits={}",
        constituent_index_bits_v2(constituent_width)
    );
    println!("packed_num_vars={num_vars}");
    println!("num_points={num_points}");
    println!("narg_bytes={}", proof.narg_string.len());
    println!("hint_bytes={}", proof.hints.len());
    println!("whir_bytes={}", proof.narg_string.len() + proof.hints.len());
    println!("compact_sample_bytes={compact_bytes}");
    println!("compact_da_cap={MAX_COMPACT_PROOF_BYTES_V2}");
    println!(
        "compact_da_headroom={}",
        MAX_COMPACT_PROOF_BYTES_V2 - compact_bytes
    );
    println!("solidity_abi_sample_bytes={solidity_abi_bytes}");
    println!(
        "solidity_abi_over_two_blob_cap={}",
        solidity_abi_bytes.saturating_sub(MAX_COMPACT_PROOF_BYTES_V2)
    );
    println!(
        "security_bits={:.6}",
        pcs.constituent_security_level(size, NUM_PCS_GROUPS_V2, num_points)
    );
}

fn encode_hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;

    let mut encoded = String::with_capacity(2 + 2 * bytes.len());
    encoded.push_str("0x");
    for byte in bytes {
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    encoded
}
