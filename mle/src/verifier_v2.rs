//! Verifier for MLE/WHIR wire v3 (historical `V2` API generation).
//!
//! The outer arithmetic consists of one cubic-extension norm/logUp sumcheck
//! and one cubic-extension gate sumcheck. Both round messages are processed
//! in lockstep and their terminal constituents are bound directly by one
//! three-group/two-point WHIR statement.

use anyhow::{anyhow, ensure, Result};
use ark_ff::{AdditiveGroup, Field as ArkField};
use plonky2::hash::hash_types::RichField;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::plonk::config::Hasher;
use plonky2_field::extension::Extendable;
use whir::algebra::fields::Field64_3;

use crate::commitment::whir_pcs::{whir_session_id, WhirPCS};
use crate::gate_ext3::evaluate_gate_aggregation_ext3;
use crate::permutation::norm_logup::{
    evaluate_joint_norm_logup_terminal_with_public_inputs, NormLogupChallenges,
    NORM_LOGUP_MAX_DEGREE,
};
use crate::proof_v2::{
    constituent_group_width_v2, constituent_index_bits_v2, packed_group_num_vars_v2, MleProofV2,
    MleVerificationKeyV2, GROUP_NORM_INVERSE_V2, GROUP_PREPROCESSED_V2, GROUP_WITNESS_V2,
    MAX_CONSTITUENT_WIDTH_V2, MAX_GATE_CONSTRAINTS_V2, MAX_GATE_ROUND_DEGREE_V2, MAX_GATE_ROWS_V2,
    MAX_PUBLIC_INPUTS_V2, MAX_ROUTED_WIRES_V2, MAX_ROW_VARIABLES_V2, MLE_PROTOCOL_VERSION_CURRENT,
    NUM_PACKED_VECTORS_PER_GROUP_V2, NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2,
    NUM_PCS_TERMINAL_POINTS_V2, PACKED_BOUND_CLAIM_MASK_V2, POINT_GATE_V2, POINT_LOG_V2,
    WHIR_SESSION_SPLIT_V2,
};
use crate::protocol_schema_v2::{
    BASE_FIELD_MODULUS_V2, CIRCUIT_DIGEST_LENGTH_V2, DOMAIN_GROUP_NORM_INVERSE_V2,
    DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2, DOMAIN_OUTER_RELATION_CHALLENGES_V2,
    DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2, DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2,
    LOG_ROUND_DEGREE_V2, MAX_WHIR_HINT_BYTES_V2, MAX_WHIR_NARG_BYTES_V2,
};
use crate::prover_v2::{
    absorb_v2_claims_and_sample_indices, absorb_v2_statement_and_base_roots, fold_ext3_claim,
};
use crate::sumcheck::coefficients::evaluate_ext3_coefficient_round;
use crate::sumcheck::gate_ext3_v2::ext3_eq_eval;
use crate::transcript_v2::TranscriptV2;
use crate::vk_v2::{
    circuit_config_digest_v2, collect_gate_info_v2, decode_public_input_wire_map_v2,
};

fn packed_ext3_point(row: &[Field64_3], index: &[Field64_3]) -> Vec<Field64_3> {
    row.iter().chain(index).copied().collect()
}

fn bind_expected(expected: &mut [Option<Field64_3>], point: usize, group: usize, value: Field64_3) {
    expected[point * NUM_PCS_GROUPS_V2 + group] = Some(value);
}

/// Verify a wire-v3 MLE proof against the circuit common data and its setup key.
pub fn mle_verify_v2<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    vk: &MleVerificationKeyV2<F>,
    proof: &MleProofV2<F>,
) -> Result<()> {
    ensure!(F::ORDER == BASE_FIELD_MODULUS_V2, "v2 requires Goldilocks");
    ensure!(
        D == 2,
        "MLE v2 supports exactly Plonky2's quadratic extension"
    );
    ensure!(
        common_data.luts.is_empty(),
        "v2 lookup argument is not implemented"
    );
    // Enforce the public resource envelope before cloning the attacker-owned
    // WHIR byte strings into the native verifier. The compact/Solidity paths
    // have the same caps, but the direct Rust API is also a trust boundary.
    ensure!(
        proof.whir_eval_proof.narg_string.len() <= MAX_WHIR_NARG_BYTES_V2
            && proof.whir_eval_proof.hints.len() <= MAX_WHIR_HINT_BYTES_V2,
        "v2 WHIR proof exceeds the reviewed resource envelope"
    );
    ensure!(
        vk.circuit_digest.len() == CIRCUIT_DIGEST_LENGTH_V2
            && proof.circuit_digest.len() == CIRCUIT_DIGEST_LENGTH_V2,
        "v2 circuit digest shape mismatch"
    );
    let degree_bits = common_data.degree_bits();
    let expected_width = constituent_group_width_v2(
        common_data.num_constants,
        common_data.config.num_routed_wires,
        common_data.config.num_wires,
    );
    ensure!(expected_width > 0, "v2 constituent schema cannot be empty");
    ensure!(
        degree_bits > 0
            && degree_bits <= MAX_ROW_VARIABLES_V2
            && common_data.config.num_routed_wires <= MAX_ROUTED_WIRES_V2
            && expected_width <= MAX_CONSTITUENT_WIDTH_V2
            && common_data.num_public_inputs <= MAX_PUBLIC_INPUTS_V2
            && common_data.num_gate_constraints <= MAX_GATE_CONSTRAINTS_V2
            && common_data.quotient_degree_factor > 0
            && common_data.quotient_degree_factor + 2 <= MAX_GATE_ROUND_DEGREE_V2
            && !common_data.gates.is_empty()
            && common_data.gates.len() <= MAX_GATE_ROWS_V2
            && common_data.selectors_info.num_selectors() > 0,
        "circuit exceeds the reviewed MLE v2 security profile"
    );
    ensure!(
        vk.protocol_version == MLE_PROTOCOL_VERSION_CURRENT
            && proof.protocol_version == MLE_PROTOCOL_VERSION_CURRENT,
        "MLE v2 protocol version mismatch"
    );
    ensure!(
        vk.constituent_width == expected_width && proof.constituent_width == expected_width,
        "v2 constituent schema width mismatch"
    );
    ensure!(
        vk.num_constants == common_data.num_constants
            && vk.num_routed_wires == common_data.config.num_routed_wires
            && vk.num_wires == common_data.config.num_wires,
        "v2 circuit/schema dimensions mismatch"
    );
    ensure!(
        vk.k_is.len() == common_data.config.num_routed_wires && vk.k_is == common_data.k_is,
        "v2 permutation coset shifts are not VK-bound"
    );
    ensure!(
        vk.num_selectors == common_data.selectors_info.num_selectors()
            && vk.num_gate_constraints == common_data.num_gate_constraints
            && vk.quotient_degree_factor == common_data.quotient_degree_factor,
        "v2 gate configuration dimensions mismatch"
    );
    ensure!(
        vk.subgroup_gen_powers.len() == degree_bits,
        "v2 subgroup generator powers have the wrong length"
    );
    let expected_subgroup_gen_powers = {
        let subgroup = F::two_adic_subgroup(degree_bits);
        let mut value = subgroup.get(1).copied().unwrap_or(F::ONE);
        let mut powers = Vec::with_capacity(degree_bits);
        for _ in 0..degree_bits {
            powers.push(value);
            value *= value;
        }
        powers
    };
    ensure!(
        vk.subgroup_gen_powers == expected_subgroup_gen_powers,
        "v2 subgroup generator powers are not canonical"
    );
    let expected_gates = collect_gate_info_v2(common_data)?;
    ensure!(vk.gates == expected_gates, "v2 gate metadata mismatch");
    let public_input_wires = decode_public_input_wire_map_v2(
        &vk.public_input_wire_map,
        common_data.num_public_inputs,
        common_data.degree(),
        common_data.config.num_routed_wires,
    )?;
    let expected_config_digest = circuit_config_digest_v2(
        common_data,
        &vk.circuit_digest,
        &expected_subgroup_gen_powers,
        &expected_gates,
        &vk.public_input_wire_map,
    )?;
    ensure!(
        vk.circuit_config_digest == expected_config_digest,
        "v2 circuit-configuration digest mismatch"
    );
    let packed_num_vars = packed_group_num_vars_v2(degree_bits, expected_width);
    let pcs = WhirPCS::for_constituents(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP_V2);
    let expected_whir_protocol_id = pcs.constituent_protocol_id(1usize << packed_num_vars);
    let expected_whir_session_id = whir_session_id(WHIR_SESSION_SPLIT_V2);
    ensure!(
        vk.whir_protocol_id == expected_whir_protocol_id
            && vk.whir_session_id == expected_whir_session_id,
        "v2 WHIR protocol/session domain is not VK-bound"
    );
    ensure!(
        proof.circuit_digest == vk.circuit_digest,
        "v2 circuit digest mismatch"
    );
    ensure!(
        proof.public_inputs.len() == common_data.num_public_inputs,
        "v2 public input length mismatch"
    );
    ensure!(
        proof.preprocessed_root == vk.preprocessed_commitment_root,
        "v2 preprocessed root is not VK-bound"
    );
    ensure!(
        proof.preprocessed_root.len() == 32
            && proof.witness_root.len() == 32
            && proof.norm_inverse_root.len() == 32,
        "v2 commitment root shape mismatch"
    );

    let preprocessed_len = common_data.num_constants + common_data.config.num_routed_wires;
    let witness_len = common_data.config.num_wires;
    let norm_inverse_len = 2 * common_data.config.num_routed_wires;
    ensure!(
        proof.log_preprocessed_evals.len() == preprocessed_len
            && proof.log_witness_evals.len() == witness_len
            && proof.log_norm_inverse_evals.len() == norm_inverse_len,
        "v2 norm/logUp constituent opening shape mismatch"
    );
    ensure!(
        proof.gate_proof.preprocessed_evals.len() == preprocessed_len
            && proof.gate_proof.witness_evals.len() == witness_len,
        "v2 Ext3 gate constituent opening shape mismatch"
    );

    let gate_degree = common_data.quotient_degree_factor + 2;
    ensure!(
        proof.log_sumcheck_proof.rounds.len() == degree_bits,
        "v2 norm/logUp sumcheck round count mismatch"
    );
    for (round_index, round) in proof.log_sumcheck_proof.rounds.iter().enumerate() {
        ensure!(
            round.non_constant.len() == LOG_ROUND_DEGREE_V2,
            "v2 norm/logUp round {round_index} degree mismatch"
        );
    }
    ensure!(
        proof.gate_proof.sumcheck_proof.rounds.len() == degree_bits,
        "v2 Ext3 gate round count mismatch"
    );
    for (round_index, round) in proof.gate_proof.sumcheck_proof.rounds.iter().enumerate() {
        ensure!(
            round.non_constant.len() == gate_degree,
            "v2 Ext3 gate round {round_index} degree mismatch"
        );
    }

    let public_inputs_hash = PoseidonHash::hash_no_pad(&proof.public_inputs);
    let mut transcript = TranscriptV2::new();
    absorb_v2_statement_and_base_roots(
        &mut transcript,
        &proof.circuit_digest,
        &proof.public_inputs,
        common_data.num_constants,
        common_data.config.num_routed_wires,
        common_data.config.num_wires,
        degree_bits,
        expected_width,
        &vk.circuit_config_digest,
        &vk.whir_protocol_id,
        &vk.whir_session_id,
        &proof.preprocessed_root,
        &proof.witness_root,
    );
    ensure!(
        NORM_LOGUP_MAX_DEGREE == LOG_ROUND_DEGREE_V2,
        "v2 schema/logUp round-degree implementation mismatch"
    );
    transcript.domain_separate(DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
    let eta = transcript.squeeze_ext3::<F>();
    transcript.domain_separate(DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2);
    let beta = transcript.squeeze_ext3::<F>();
    let gamma = transcript.squeeze_ext3::<F>();
    transcript.domain_separate(DOMAIN_GROUP_NORM_INVERSE_V2);
    transcript.absorb_bytes(&proof.norm_inverse_root);
    transcript.domain_separate(DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2);
    let xi = transcript.squeeze_ext3::<F>();

    transcript.domain_separate(DOMAIN_OUTER_RELATION_CHALLENGES_V2);
    let log_challenges = NormLogupChallenges {
        beta,
        gamma,
        lambda: transcript.squeeze_ext3::<F>(),
        rho: transcript.squeeze_ext3::<F>(),
        kappa: transcript.squeeze_ext3::<F>(),
        eta,
        xi,
    };
    let tau_log = transcript.squeeze_ext3_challenges::<F>(degree_bits);
    let gate_alpha = transcript.squeeze_ext3::<F>();
    let gate_tau = transcript.squeeze_ext3_challenges::<F>(degree_bits);

    let mut log_final_claim = Field64_3::ZERO;
    let mut gate_final_claim = Field64_3::ZERO;
    let mut log_point = Vec::with_capacity(degree_bits);
    let mut gate_point = Vec::with_capacity(degree_bits);
    for round_index in 0..degree_bits {
        let log_round = &proof.log_sumcheck_proof.rounds[round_index];
        let gate_round = &proof.gate_proof.sumcheck_proof.rounds[round_index];
        let round_challenges = transcript.commit_coupled_outer_round::<F>(
            round_index,
            &log_round.non_constant,
            &gate_round.non_constant,
        );
        log_final_claim = evaluate_ext3_coefficient_round(
            log_final_claim,
            &log_round.non_constant,
            round_challenges.log,
        );
        log_point.push(round_challenges.log);
        gate_final_claim = evaluate_ext3_coefficient_round(
            gate_final_claim,
            &gate_round.non_constant,
            round_challenges.gate,
        );
        gate_point.push(round_challenges.gate);
    }

    let index_points = absorb_v2_claims_and_sample_indices::<F>(
        &mut transcript,
        &proof.log_preprocessed_evals,
        &proof.log_witness_evals,
        &proof.log_norm_inverse_evals,
        &proof.gate_proof.preprocessed_evals,
        &proof.gate_proof.witness_evals,
        constituent_index_bits_v2(expected_width),
    );

    let mut expected_evals = vec![None; NUM_PCS_CLAIMS_V2];
    bind_expected(
        &mut expected_evals,
        POINT_LOG_V2,
        GROUP_PREPROCESSED_V2,
        fold_ext3_claim(
            &proof.log_preprocessed_evals,
            expected_width,
            &index_points[POINT_LOG_V2],
        ),
    );
    bind_expected(
        &mut expected_evals,
        POINT_LOG_V2,
        GROUP_WITNESS_V2,
        fold_ext3_claim(
            &proof.log_witness_evals,
            expected_width,
            &index_points[POINT_LOG_V2],
        ),
    );
    bind_expected(
        &mut expected_evals,
        POINT_LOG_V2,
        GROUP_NORM_INVERSE_V2,
        fold_ext3_claim(
            &proof.log_norm_inverse_evals,
            expected_width,
            &index_points[POINT_LOG_V2],
        ),
    );
    bind_expected(
        &mut expected_evals,
        POINT_GATE_V2,
        GROUP_PREPROCESSED_V2,
        fold_ext3_claim(
            &proof.gate_proof.preprocessed_evals,
            expected_width,
            &index_points[POINT_GATE_V2],
        ),
    );
    bind_expected(
        &mut expected_evals,
        POINT_GATE_V2,
        GROUP_WITNESS_V2,
        fold_ext3_claim(
            &proof.gate_proof.witness_evals,
            expected_width,
            &index_points[POINT_GATE_V2],
        ),
    );
    for (index, value) in expected_evals.iter().enumerate() {
        let mask_bit = PACKED_BOUND_CLAIM_MASK_V2[index / 8] & (1 << (index % 8)) != 0;
        ensure!(
            value.is_some() == mask_bit,
            "v2 packed claim mask/internal ordering mismatch"
        );
    }

    let packed_points = [
        packed_ext3_point(&log_point, &index_points[POINT_LOG_V2]),
        packed_ext3_point(&gate_point, &index_points[POINT_GATE_V2]),
    ];
    ensure!(
        packed_points.len() == NUM_PCS_TERMINAL_POINTS_V2,
        "v2 terminal point count mismatch"
    );
    let point_refs = packed_points.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let roots = [
        proof.preprocessed_root.as_slice(),
        proof.witness_root.as_slice(),
        proof.norm_inverse_root.as_slice(),
    ];
    pcs.verify_grouped(
        packed_num_vars,
        &proof.whir_eval_proof,
        &expected_evals,
        WHIR_SESSION_SPLIT_V2,
        &point_refs,
        NUM_PCS_GROUPS_V2,
        &roots,
    )
    .map_err(|error| anyhow!("v2 grouped WHIR verification failed: {error}"))?;

    let num_routed = common_data.config.num_routed_wires;
    let mut subgroup_eval = Field64_3::ONE;
    for (&coordinate, &generator_power) in log_point.iter().zip(&vk.subgroup_gen_powers) {
        let generator = Field64_3::from(generator_power.to_canonical_u64());
        subgroup_eval *= (Field64_3::ONE - coordinate) + coordinate * generator;
    }
    let log_terminal = evaluate_joint_norm_logup_terminal_with_public_inputs(
        &tau_log,
        &log_point,
        &proof.log_witness_evals[..num_routed],
        &proof.log_preprocessed_evals
            [common_data.num_constants..common_data.num_constants + num_routed],
        &proof.log_norm_inverse_evals[..num_routed],
        &proof.log_norm_inverse_evals[num_routed..],
        subgroup_eval,
        &vk.k_is,
        log_challenges,
        &proof.public_inputs,
        &public_input_wires,
    );
    ensure!(
        log_terminal == log_final_claim,
        "v2 norm/logUp terminal equation failed"
    );

    let gate_terminal = evaluate_gate_aggregation_ext3(
        common_data,
        &vk.gates,
        &proof.gate_proof.witness_evals,
        &proof.gate_proof.preprocessed_evals[..common_data.num_constants],
        &public_inputs_hash,
        gate_alpha,
    )?;
    let expected_gate_final = ext3_eq_eval(&gate_tau, &gate_point)? * gate_terminal;
    ensure!(
        expected_gate_final == gate_final_claim,
        "v2 Ext3 gate terminal equation failed"
    );

    Ok(())
}
