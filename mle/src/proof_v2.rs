//! Canonical proof objects for the security-amplified MLE/WHIR v2 protocol.
//!
//! V1 remains available solely as a migration/negative-test format. V2 drops
//! all challenge echoes and legacy scalar batch claims: Fiat--Shamir values
//! are re-derived, and each terminal constituent vector is bound directly by
//! the grouped WHIR statement.

use plonky2_field::types::Field;
use whir::algebra::fields::Field64_3;

use crate::commitment::whir_pcs::WhirEvalProof;
// Re-export the generated constants for compatibility with the v2 API. The
// sole hand-maintained source is `protocol/mle_whir_v2.json`.
pub use crate::protocol_schema_v2::{
    GROUP_NORM_INVERSE_V2, GROUP_PREPROCESSED_V2, GROUP_WITNESS_V2, MAX_CONSTITUENT_WIDTH_V2,
    MAX_GATE_CONSTRAINTS_V2, MAX_GATE_ROUND_DEGREE_V2, MAX_GATE_ROWS_V2, MAX_PUBLIC_INPUTS_V2,
    MAX_ROUTED_WIRES_V2, MAX_ROW_VARIABLES_V2, MLE_PROTOCOL_VERSION_CURRENT,
    NUM_PACKED_VECTORS_PER_GROUP_V2, NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2,
    NUM_PCS_TERMINAL_POINTS_V2, OUTER_TRANSCRIPT_PROTOCOL_V2, PACKED_BOUND_CLAIM_MASK_V2,
    POINT_GATE_V2, POINT_LOG_V2, WHIR_SESSION_SPLIT_V2,
};
use crate::sumcheck::coefficients::Ext3CoefficientSumcheckProof;

pub fn constituent_group_width_v2(
    num_constants: usize,
    num_routed_wires: usize,
    num_wires: usize,
) -> usize {
    (num_constants + num_routed_wires)
        .max(num_wires)
        .max(2 * num_routed_wires)
}

pub fn constituent_index_bits_v2(width: usize) -> usize {
    assert!(width > 0, "v2 constituent width must be non-zero");
    width.next_power_of_two().trailing_zeros() as usize
}

pub fn packed_group_num_vars_v2(degree_bits: usize, width: usize) -> usize {
    degree_bits + constituent_index_bits_v2(width)
}

/// Canonical cross-language gate metadata consumed by the Solidity terminal
/// evaluator. All integer widths and ordering are part of the V2
/// implementation's current wire-v3 protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GateInfoV2 {
    pub gate_id: u8,
    pub selector_index: u8,
    pub group_start: u8,
    pub group_end: u8,
    pub gate_row_index: u8,
    pub num_constraints: u16,
    pub num_or_consts: u16,
    pub param2: u16,
    pub param3: u16,
}

#[derive(Clone, Debug)]
pub struct MleVerificationKeyV2<F: Field> {
    pub protocol_version: u64,
    pub constituent_width: usize,
    pub circuit_digest: Vec<F>,
    pub preprocessed_commitment_root: Vec<u8>,
    /// WHIR domains are VK-bound and are also absorbed by the outer
    /// transcript, preventing cross-configuration/session proof reuse.
    pub whir_protocol_id: [u8; 64],
    pub whir_session_id: [u8; 32],
    /// Digest and decoded metadata for the exact Plonky2 gate semantics used
    /// by both Rust and Solidity terminal evaluation.
    pub circuit_config_digest: [u8; 32],
    pub num_selectors: usize,
    pub num_gate_constraints: usize,
    pub quotient_degree_factor: usize,
    pub gates: Vec<GateInfoV2>,
    /// Ordered `row_u16_le || routed_column_u8` records binding every raw
    /// public input to its canonical witness copy-class representative.
    pub public_input_wire_map: Vec<u8>,
    pub num_constants: usize,
    pub num_routed_wires: usize,
    pub num_wires: usize,
    pub k_is: Vec<F>,
    pub subgroup_gen_powers: Vec<F>,
}

#[derive(Clone, Debug)]
pub struct GateProofV2 {
    /// Degree `quotient_degree_factor + 2` over Goldilocks Fp3. A single
    /// extension-field transition has enough entropy; base-field repetition
    /// is forbidden because a Fiat--Shamir prover can bridge repetitions in
    /// different rounds.
    pub sumcheck_proof: Ext3CoefficientSumcheckProof,
    /// Exact constituent evaluations at the Ext3 terminal point.
    pub preprocessed_evals: Vec<Field64_3>,
    pub witness_evals: Vec<Field64_3>,
}

#[derive(Clone, Debug)]
pub struct MleProofV2<F: Field> {
    pub protocol_version: u64,
    pub constituent_width: usize,
    pub circuit_digest: Vec<F>,
    pub public_inputs: Vec<F>,

    /// One grouped proof for three ordered commitments at two ordered points.
    pub whir_eval_proof: WhirEvalProof,
    pub preprocessed_root: Vec<u8>,
    pub witness_root: Vec<u8>,
    pub norm_inverse_root: Vec<u8>,

    /// Degree-five Ext3 joint norm-correctness/logUp sumcheck.
    pub log_sumcheck_proof: Ext3CoefficientSumcheckProof,
    /// Exact Ext3 terminal constituents at `r_log`.
    pub log_preprocessed_evals: Vec<Field64_3>,
    pub log_witness_evals: Vec<Field64_3>,
    pub log_norm_inverse_evals: Vec<Field64_3>,

    /// One complete Ext3 gate-formula sumcheck.
    pub gate_proof: GateProofV2,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v2_shape_and_mask_are_exact() {
        assert_eq!(NUM_PCS_CLAIMS_V2, 6);
        let used = (0..NUM_PCS_CLAIMS_V2)
            .filter(|index| PACKED_BOUND_CLAIM_MASK_V2[index / 8] & (1 << (index % 8)) != 0)
            .collect::<Vec<_>>();
        assert_eq!(used, vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn current_maximum_width_stays_160() {
        assert_eq!(constituent_group_width_v2(4, 80, 135), 160);
        assert_eq!(constituent_index_bits_v2(160), 8);
    }
}
