//! Security-amplified MLE/WHIR wire-v3 prover (historical `V2` API generation).
//!
//! This generation uses one cubic-extension norm/logUp sumcheck and one cubic-extension
//! gate sumcheck. Their round messages share a lockstep transcript, and the
//! three packed commitment groups are opened at exactly two row points.

use anyhow::{ensure, Result};
use ark_ff::AdditiveGroup;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::PartialWitness;
use plonky2::plonk::circuit_data::{CommonCircuitData, EvaluationTables, ProverOnlyCircuitData};
use plonky2::plonk::config::{GenericConfig, Hasher};
use plonky2::plonk::prover::extract_evaluation_tables;
use plonky2::util::timing::TimingTree;
use plonky2_field::extension::Extendable;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::commitment::whir_pcs::{whir_session_id, WhirPCS};
use crate::dense_mle::{row_major_to_mles, tables_to_mles, DenseMultilinearExtension};
use crate::permutation::norm_logup::{
    compute_norm_inverse_tables, NormLogupChallenges, NormLogupProverState,
};
use crate::proof_v2::{
    constituent_group_width_v2, constituent_index_bits_v2, packed_group_num_vars_v2, GateProofV2,
    MleProofV2, MleVerificationKeyV2, MAX_CONSTITUENT_WIDTH_V2, MAX_GATE_CONSTRAINTS_V2,
    MAX_GATE_ROUND_DEGREE_V2, MAX_GATE_ROWS_V2, MAX_PUBLIC_INPUTS_V2, MAX_ROUTED_WIRES_V2,
    MAX_ROW_VARIABLES_V2, MLE_PROTOCOL_VERSION_CURRENT, NUM_PACKED_VECTORS_PER_GROUP_V2,
    NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2, NUM_PCS_TERMINAL_POINTS_V2, WHIR_SESSION_SPLIT_V2,
};
use crate::protocol_schema_v2::{
    BASE_FIELD_MODULUS_V2, CIRCUIT_DIGEST_LENGTH_V2, DOMAIN_CIRCUIT_CONFIG_DIGEST_V2,
    DOMAIN_CIRCUIT_STATEMENT_V2, DOMAIN_CONSTITUENT_CLAIMS_V2, DOMAIN_CONSTITUENT_INDEX_V2,
    DOMAIN_GROUP_NORM_INVERSE_V2, DOMAIN_GROUP_PREPROCESSED_V2, DOMAIN_GROUP_WITNESS_V2,
    DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2, DOMAIN_OUTER_RELATION_CHALLENGES_V2,
    DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2, DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2,
    DOMAIN_WHIR_PROTOCOL_ID_V2, DOMAIN_WHIR_SESSION_ID_V2, EXTENSION_FIELD_LIMBS_V2,
    GATE_SUMCHECK_COUNT_V2, LOG_ROUND_DEGREE_V2, PACKED_PCS_SCHEMA_DOMAIN_V2,
    PACKED_VARIABLE_ORDER_CODE_V2,
};
use crate::sumcheck::gate_ext3_v2::GateExt3ProverState;
use crate::transcript_v2::TranscriptV2;
use crate::vk_v2::{
    circuit_config_digest_v2, collect_gate_info_v2, decode_public_input_wire_map_v2,
    encode_public_input_wires_v2, public_input_wire_map_v2,
};

fn pack_mles<F: RichField>(
    mles: &[&DenseMultilinearExtension<F>],
    width: usize,
    num_rows: usize,
) -> Vec<Vec<ArkGoldilocks>> {
    assert!(mles.len() <= width, "v2 constituent group exceeds width");
    let mut packed = vec![ArkGoldilocks::ZERO; num_rows * width.next_power_of_two()];
    for (column, mle) in mles.iter().enumerate() {
        assert_eq!(
            mle.evaluations.len(),
            num_rows,
            "v2 constituent row mismatch"
        );
        for (row, value) in mle.evaluations.iter().enumerate() {
            packed[column * num_rows + row] = ArkGoldilocks::from(value.to_canonical_u64());
        }
    }
    vec![packed]
}

fn pack_tables<F: RichField>(
    tables: &[Vec<F>],
    width: usize,
    num_rows: usize,
) -> Vec<Vec<ArkGoldilocks>> {
    assert!(tables.len() <= width, "v2 helper group exceeds width");
    let mut packed = vec![ArkGoldilocks::ZERO; num_rows * width.next_power_of_two()];
    for (column, table) in tables.iter().enumerate() {
        assert_eq!(table.len(), num_rows, "v2 helper row mismatch");
        for (row, value) in table.iter().enumerate() {
            packed[column * num_rows + row] = ArkGoldilocks::from(value.to_canonical_u64());
        }
    }
    vec![packed]
}

fn preprocessed_mles<'a, F: RichField>(
    constants: &'a [DenseMultilinearExtension<F>],
    sigmas: &'a [DenseMultilinearExtension<F>],
) -> Vec<&'a DenseMultilinearExtension<F>> {
    constants.iter().chain(sigmas).collect()
}

pub(crate) fn absorb_v2_statement_and_base_roots<F: RichField>(
    transcript: &mut TranscriptV2,
    circuit_digest: &[F],
    public_inputs: &[F],
    num_constants: usize,
    num_routed_wires: usize,
    num_wires: usize,
    degree_bits: usize,
    width: usize,
    circuit_config_digest: &[u8],
    whir_protocol_id: &[u8],
    whir_session_id: &[u8],
    preprocessed_root: &[u8],
    witness_root: &[u8],
) {
    transcript.domain_separate(DOMAIN_CIRCUIT_STATEMENT_V2);
    transcript.absorb_field_vec(circuit_digest);
    transcript.absorb_field_vec(public_inputs);

    transcript.domain_separate(PACKED_PCS_SCHEMA_DOMAIN_V2);
    let metadata = [
        MLE_PROTOCOL_VERSION_CURRENT,
        NUM_PCS_GROUPS_V2 as u64,
        NUM_PCS_TERMINAL_POINTS_V2 as u64,
        NUM_PCS_CLAIMS_V2 as u64,
        num_constants as u64,
        num_routed_wires as u64,
        num_wires as u64,
        degree_bits as u64,
        width as u64,
        constituent_index_bits_v2(width) as u64,
        NUM_PACKED_VECTORS_PER_GROUP_V2 as u64,
        EXTENSION_FIELD_LIMBS_V2 as u64,
        PACKED_VARIABLE_ORDER_CODE_V2 as u64,
        GATE_SUMCHECK_COUNT_V2 as u64,
        LOG_ROUND_DEGREE_V2 as u64,
    ];
    let mut encoded = Vec::with_capacity(metadata.len() * 8);
    for value in metadata {
        encoded.extend_from_slice(&value.to_le_bytes());
    }
    transcript.absorb_bytes(&encoded);
    transcript.domain_separate(DOMAIN_CIRCUIT_CONFIG_DIGEST_V2);
    transcript.absorb_bytes(circuit_config_digest);
    transcript.domain_separate(DOMAIN_WHIR_PROTOCOL_ID_V2);
    transcript.absorb_bytes(whir_protocol_id);
    transcript.domain_separate(DOMAIN_WHIR_SESSION_ID_V2);
    transcript.absorb_bytes(whir_session_id);
    transcript.domain_separate(DOMAIN_GROUP_PREPROCESSED_V2);
    transcript.absorb_bytes(preprocessed_root);
    transcript.domain_separate(DOMAIN_GROUP_WITNESS_V2);
    transcript.absorb_bytes(witness_root);
}

pub(crate) fn absorb_v2_claims_and_sample_indices<F: RichField>(
    transcript: &mut TranscriptV2,
    log_preprocessed: &[Field64_3],
    log_witness: &[Field64_3],
    log_norm_inverse: &[Field64_3],
    gate_preprocessed: &[Field64_3],
    gate_witness: &[Field64_3],
    index_bits: usize,
) -> Vec<Vec<Field64_3>> {
    transcript.domain_separate(DOMAIN_CONSTITUENT_CLAIMS_V2);
    transcript.absorb_ext3_vec(log_preprocessed);
    transcript.absorb_ext3_vec(log_witness);
    transcript.absorb_ext3_vec(log_norm_inverse);
    transcript.absorb_ext3_vec(gate_preprocessed);
    transcript.absorb_ext3_vec(gate_witness);
    transcript.absorb_ext3_vec(&[]);
    transcript.domain_separate(DOMAIN_CONSTITUENT_INDEX_V2);
    (0..NUM_PCS_TERMINAL_POINTS_V2)
        .map(|_| transcript.squeeze_ext3_challenges::<F>(index_bits))
        .collect()
}

pub(crate) fn fold_ext3_claim(
    values: &[Field64_3],
    width: usize,
    point: &[Field64_3],
) -> Field64_3 {
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

fn evaluate_at_ext3<F: RichField>(
    mle: &DenseMultilinearExtension<F>,
    point: &[Field64_3],
) -> Field64_3 {
    crate::sumcheck::ext3::Ext3DenseMle::from_base(&mle.evaluations).evaluate(point)
}

fn packed_ext3_point(row: &[Field64_3], index: &[Field64_3]) -> Vec<Field64_3> {
    row.iter().chain(index).copied().collect()
}

pub fn mle_setup_v2<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    prover_data: &ProverOnlyCircuitData<F, C, D>,
    common_data: &CommonCircuitData<F, D>,
) -> MleVerificationKeyV2<F>
where
    C::Hasher: Hasher<F>,
{
    assert_eq!(
        D, 2,
        "MLE v2 supports exactly Plonky2's quadratic extension"
    );
    assert!(
        common_data.luts.is_empty(),
        "MLE v2 lookup arguments are not implemented"
    );
    let digest_bytes =
        serde_json::to_vec(&prover_data.circuit_digest).expect("circuit digest serialization");
    let digest_hash: plonky2::hash::hash_types::HashOut<F> =
        serde_json::from_slice(&digest_bytes).expect("circuit digest deserialization");
    let circuit_digest = digest_hash.elements.to_vec();
    assert_eq!(
        circuit_digest.len(),
        CIRCUIT_DIGEST_LENGTH_V2,
        "MLE v2 circuit digest has the wrong shape"
    );
    let degree_bits = common_data.degree_bits();
    let num_routed = common_data.config.num_routed_wires;
    let num_wires = common_data.config.num_wires;
    let width = constituent_group_width_v2(common_data.num_constants, num_routed, num_wires);
    assert!(
        degree_bits > 0
            && degree_bits <= MAX_ROW_VARIABLES_V2
            && num_routed <= MAX_ROUTED_WIRES_V2
            && width <= MAX_CONSTITUENT_WIDTH_V2
            && common_data.num_public_inputs <= MAX_PUBLIC_INPUTS_V2
            && common_data.num_gate_constraints <= MAX_GATE_CONSTRAINTS_V2
            && common_data.quotient_degree_factor > 0
            && common_data.quotient_degree_factor + 2 <= MAX_GATE_ROUND_DEGREE_V2
            && !common_data.gates.is_empty()
            && common_data.gates.len() <= MAX_GATE_ROWS_V2
            && common_data.selectors_info.num_selectors() > 0,
        "circuit exceeds the reviewed MLE v2 security profile"
    );
    let constants = row_major_to_mles(&prover_data.constant_evals, common_data.num_constants);
    let sigmas = row_major_to_mles(&prover_data.sigmas, num_routed);
    let preprocessed = preprocessed_mles(&constants, &sigmas);
    let group = pack_mles(&preprocessed, width, 1usize << degree_bits);
    let pcs = WhirPCS::for_constituents(
        packed_group_num_vars_v2(degree_bits, width),
        NUM_PACKED_VECTORS_PER_GROUP_V2,
    );
    let whir_size = 1usize << packed_group_num_vars_v2(degree_bits, width);
    let whir_protocol_id = pcs.constituent_protocol_id(whir_size);
    let whir_session_id = whir_session_id(WHIR_SESSION_SPLIT_V2);
    let committed = pcs.commit_grouped(&[group], WHIR_SESSION_SPLIT_V2);
    let subgroup_gen_powers = {
        let mut powers = Vec::with_capacity(degree_bits);
        let mut value = prover_data.subgroup.get(1).copied().unwrap_or(F::ONE);
        for _ in 0..degree_bits {
            powers.push(value);
            value *= value;
        }
        powers
    };
    let gates = collect_gate_info_v2(common_data)
        .expect("circuit gates must have exact Solidity v2 metadata");
    let public_input_wire_map = public_input_wire_map_v2(prover_data, common_data)
        .expect("public inputs must have canonical routed-wire representatives");
    let circuit_config_digest = circuit_config_digest_v2(
        common_data,
        &circuit_digest,
        &subgroup_gen_powers,
        &gates,
        &public_input_wire_map,
    )
    .expect("circuit configuration must have a canonical v2 digest");
    MleVerificationKeyV2 {
        protocol_version: MLE_PROTOCOL_VERSION_CURRENT,
        constituent_width: width,
        circuit_digest,
        preprocessed_commitment_root: committed.roots[0].clone(),
        whir_protocol_id,
        whir_session_id,
        circuit_config_digest,
        num_selectors: common_data.selectors_info.num_selectors(),
        num_gate_constraints: common_data.num_gate_constraints,
        quotient_degree_factor: common_data.quotient_degree_factor,
        gates,
        public_input_wire_map,
        num_constants: common_data.num_constants,
        num_routed_wires: num_routed,
        num_wires,
        k_is: common_data.k_is.clone(),
        subgroup_gen_powers,
    }
}

pub fn mle_prove_v2<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    prover_data: &ProverOnlyCircuitData<F, C, D>,
    common_data: &CommonCircuitData<F, D>,
    inputs: PartialWitness<F>,
    timing: &mut TimingTree,
) -> Result<MleProofV2<F>>
where
    C::Hasher: Hasher<F>,
    C::InnerHasher: Hasher<F>,
{
    let tables = extract_evaluation_tables::<F, C, D>(prover_data, common_data, inputs, timing)?;
    let digest_bytes =
        serde_json::to_vec(&prover_data.circuit_digest).expect("circuit digest serialization");
    let digest_hash: plonky2::hash::hash_types::HashOut<F> =
        serde_json::from_slice(&digest_bytes).expect("circuit digest deserialization");
    mle_prove_v2_from_tables(common_data, &tables, &digest_hash.elements)
}

pub fn mle_prove_v2_from_tables<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    tables: &EvaluationTables<F>,
    circuit_digest: &[F],
) -> Result<MleProofV2<F>> {
    ensure!(F::ORDER == BASE_FIELD_MODULUS_V2, "v2 requires Goldilocks");
    ensure!(
        D == 2,
        "MLE v2 supports exactly Plonky2's quadratic extension"
    );
    ensure!(
        common_data.luts.is_empty(),
        "v2 lookup argument is not implemented"
    );
    ensure!(
        circuit_digest.len() == CIRCUIT_DIGEST_LENGTH_V2,
        "v2 circuit digest shape mismatch"
    );
    let degree_bits = tables.degree_bits;
    let num_rows = 1usize << degree_bits;
    let num_routed = tables.num_routed_wires;
    ensure!(
        tables.degree == num_rows,
        "v2 requires a full power-of-two row table"
    );
    ensure!(
        tables.num_wires == common_data.config.num_wires
            && tables.num_routed_wires == common_data.config.num_routed_wires
            && tables.k_is == common_data.k_is,
        "v2 evaluation tables do not match the circuit configuration"
    );

    let wires = tables_to_mles(&tables.wire_values);
    let constants = row_major_to_mles(&tables.constant_values, common_data.num_constants);
    let sigmas = row_major_to_mles(&tables.sigma_values, num_routed);
    let preprocessed = preprocessed_mles(&constants, &sigmas);
    let width = constituent_group_width_v2(
        common_data.num_constants,
        num_routed,
        common_data.config.num_wires,
    );
    ensure!(
        degree_bits > 0
            && degree_bits <= MAX_ROW_VARIABLES_V2
            && num_routed <= MAX_ROUTED_WIRES_V2
            && width <= MAX_CONSTITUENT_WIDTH_V2
            && common_data.num_public_inputs <= MAX_PUBLIC_INPUTS_V2
            && common_data.num_gate_constraints <= MAX_GATE_CONSTRAINTS_V2
            && common_data.quotient_degree_factor > 0
            && common_data.quotient_degree_factor + 2 <= MAX_GATE_ROUND_DEGREE_V2
            && !common_data.gates.is_empty()
            && common_data.gates.len() <= MAX_GATE_ROWS_V2
            && common_data.selectors_info.num_selectors() > 0,
        "circuit exceeds the reviewed MLE v2 security profile"
    );
    let packed_num_vars = packed_group_num_vars_v2(degree_bits, width);
    let pcs = WhirPCS::for_constituents(packed_num_vars, NUM_PACKED_VECTORS_PER_GROUP_V2);
    let whir_protocol_id = pcs.constituent_protocol_id(1usize << packed_num_vars);
    let whir_session_id = whir_session_id(WHIR_SESSION_SPLIT_V2);
    let subgroup_gen_powers = {
        let mut powers = Vec::with_capacity(degree_bits);
        let mut value = tables.subgroup.get(1).copied().unwrap_or(F::ONE);
        for _ in 0..degree_bits {
            powers.push(value);
            value *= value;
        }
        powers
    };
    let gates = collect_gate_info_v2(common_data)?;
    ensure!(
        tables.public_input_wires.len() == tables.public_inputs.len(),
        "v2 public-input values and wire map have different lengths"
    );
    let public_input_wire_map = encode_public_input_wires_v2(
        tables
            .public_input_wires
            .iter()
            .map(|wire| (wire.row, wire.column)),
        common_data.num_public_inputs,
        num_rows,
        num_routed,
    )?;
    let public_input_wires = decode_public_input_wire_map_v2(
        &public_input_wire_map,
        common_data.num_public_inputs,
        num_rows,
        num_routed,
    )?;
    let circuit_config_digest = circuit_config_digest_v2(
        common_data,
        circuit_digest,
        &subgroup_gen_powers,
        &gates,
        &public_input_wire_map,
    )?;
    let pre_group = pack_mles(&preprocessed, width, num_rows);
    let wire_refs = wires.iter().collect::<Vec<_>>();
    let witness_group = pack_mles(&wire_refs, width, num_rows);
    let mut committed = pcs.commit_grouped(&[pre_group, witness_group], WHIR_SESSION_SPLIT_V2);
    let preprocessed_root = committed.roots[0].clone();
    let witness_root = committed.roots[1].clone();

    let mut master = TranscriptV2::new();
    absorb_v2_statement_and_base_roots(
        &mut master,
        circuit_digest,
        &tables.public_inputs,
        common_data.num_constants,
        num_routed,
        tables.num_wires,
        degree_bits,
        width,
        &circuit_config_digest,
        &whir_protocol_id,
        &whir_session_id,
        &preprocessed_root,
        &witness_root,
    );
    master.domain_separate(DOMAIN_PUBLIC_INPUT_AGGREGATION_CHALLENGE_V2);
    // Zero is retained as an ordinary bad-challenge event and charged in the
    // m/|Fp3| public-input binding soundness term. This preserves uniformity.
    let eta = master.squeeze_ext3::<F>();
    master.domain_separate(DOMAIN_NORM_DENOMINATOR_CHALLENGES_V2);
    let beta = master.squeeze_ext3::<F>();
    let gamma = master.squeeze_ext3::<F>();
    let norm_tables = compute_norm_inverse_tables(
        &tables.wire_values,
        &tables.sigma_values,
        &tables.k_is,
        &tables.subgroup,
        beta,
        gamma,
        num_routed,
        tables.degree,
    )?;
    let norm_columns = norm_tables
        .identity
        .iter()
        .cloned()
        .chain(norm_tables.sigma.iter().cloned())
        .collect::<Vec<_>>();
    let norm_group = pack_tables(&norm_columns, width, num_rows);
    let norm_inverse_root = pcs.commit_additional_group(&mut committed, norm_group);
    master.domain_separate(DOMAIN_GROUP_NORM_INVERSE_V2);
    master.absorb_bytes(&norm_inverse_root);
    master.domain_separate(DOMAIN_PUBLIC_INPUT_MIX_CHALLENGE_V2);
    let xi = master.squeeze_ext3::<F>();

    // All relation-combining challenges are derived from the same committed
    // root state. Each individual sumcheck challenge is an Fp3 element; the
    // lockstep batch additionally prevents one relation from being adapted to
    // the other within the same round.
    master.domain_separate(DOMAIN_OUTER_RELATION_CHALLENGES_V2);
    let log_challenges = NormLogupChallenges {
        beta,
        gamma,
        lambda: master.squeeze_ext3::<F>(),
        rho: master.squeeze_ext3::<F>(),
        kappa: master.squeeze_ext3::<F>(),
        eta,
        xi,
    };
    let tau_log = master.squeeze_ext3_challenges::<F>(degree_bits);

    let gate_alpha = master.squeeze_ext3::<F>();
    let gate_tau = master.squeeze_ext3_challenges::<F>(degree_bits);

    let mut log_state = NormLogupProverState::new_with_public_inputs(
        &tables.wire_values,
        &tables.sigma_values,
        &tables.k_is,
        &tables.subgroup,
        &norm_tables,
        &tau_log,
        log_challenges,
        &tables.public_inputs,
        &public_input_wires,
    );

    let gate_degree = common_data.quotient_degree_factor + 2;
    let mut gate_state = GateExt3ProverState::new(
        common_data,
        &gates,
        &wires,
        &constants,
        &tables.public_inputs_hash,
        gate_alpha,
        &gate_tau,
        gate_degree,
    )?;

    for round_index in 0..degree_bits {
        let log_round = log_state.current_round()?;
        let gate_round = gate_state.current_round()?;
        let round_challenges = master.commit_coupled_outer_round::<F>(
            round_index,
            &log_round.non_constant,
            &gate_round.non_constant,
        );
        log_state.bind_challenge(round_challenges.log)?;
        gate_state.bind_challenge(gate_round, round_challenges.gate)?;
    }
    let (log_sumcheck_proof, r_log) = log_state.into_proof_and_point()?;
    let (gate_sumcheck_proof, r_gate) = gate_state.into_proof_and_point()?;

    let log_preprocessed_evals = preprocessed
        .iter()
        .map(|mle| evaluate_at_ext3(mle, &r_log))
        .collect::<Vec<_>>();
    let log_witness_evals = wires
        .iter()
        .map(|mle| evaluate_at_ext3(mle, &r_log))
        .collect::<Vec<_>>();
    let log_norm_inverse_evals = norm_columns
        .iter()
        .map(|column| crate::sumcheck::ext3::Ext3DenseMle::from_base(column).evaluate(&r_log))
        .collect::<Vec<_>>();

    let gate_preprocessed = preprocessed
        .iter()
        .map(|mle| evaluate_at_ext3(mle, &r_gate))
        .collect::<Vec<_>>();
    let gate_witness = wires
        .iter()
        .map(|mle| evaluate_at_ext3(mle, &r_gate))
        .collect::<Vec<_>>();
    let index_points = absorb_v2_claims_and_sample_indices::<F>(
        &mut master,
        &log_preprocessed_evals,
        &log_witness_evals,
        &log_norm_inverse_evals,
        &gate_preprocessed,
        &gate_witness,
        constituent_index_bits_v2(width),
    );
    let packed_points = [
        packed_ext3_point(&r_log, &index_points[0]),
        packed_ext3_point(&r_gate, &index_points[1]),
    ];
    let point_refs = packed_points.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let (whir_eval_proof, _) = pcs.prove_grouped_with_eval(committed, &point_refs);

    let gate_proof = GateProofV2 {
        sumcheck_proof: gate_sumcheck_proof,
        preprocessed_evals: gate_preprocessed,
        witness_evals: gate_witness,
    };
    Ok(MleProofV2 {
        protocol_version: MLE_PROTOCOL_VERSION_CURRENT,
        constituent_width: width,
        circuit_digest: circuit_digest.to_vec(),
        public_inputs: tables.public_inputs.clone(),
        whir_eval_proof,
        preprocessed_root,
        witness_root,
        norm_inverse_root,
        log_sumcheck_proof,
        log_preprocessed_evals,
        log_witness_evals,
        log_norm_inverse_evals,
        gate_proof,
    })
}
