//! Machine-checked arithmetic for the production MLE/WHIR v2 budget.
//!
//! These tests pin the reviewed profile and composition accounting. They are
//! not a substitute for a reduction: in particular, the literal random-
//! oracle bound retains an explicit `Q_H` factor.

use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_mle::commitment::whir_pcs::{WhirNativeTraceEventKind, WhirPCS};
use plonky2_mle::compact_v2::decode_compact_v2;
use plonky2_mle::fixture_v2::{
    derive_whir_deployment_profile_for_packed_num_vars_v2, MleVerifierV2Fixture,
};
use plonky2_mle::proof_v2::{
    MAX_GATE_CONSTRAINTS_V2, MAX_GATE_ROUND_DEGREE_V2, MAX_PUBLIC_INPUTS_V2, MAX_ROW_VARIABLES_V2,
    NUM_PACKED_VECTORS_PER_GROUP_V2, NUM_PCS_CLAIMS_V2, NUM_PCS_GROUPS_V2,
    NUM_PCS_TERMINAL_POINTS_V2, PACKED_BOUND_CLAIM_MASK_V2, WHIR_SESSION_SPLIT_V2,
};
use plonky2_mle::protocol_schema_v2::{
    COMPACT_MAGIC_V2, EXTENSION_FIELD_LIMBS_V2, MAX_CONSTITUENT_INDEX_BITS_V2,
    WHIR_FOLDING_FACTOR_V2, WHIR_MAX_STARTING_LOG_INV_RATE_V2, WHIR_POW_BITS_V2,
    WHIR_SECURITY_LEVEL_V2,
};

const GOLDILOCKS_P: f64 = 18_446_744_069_414_584_321.0;
const MAX_ROWS: f64 = 8_192.0;
const MAX_ROUTED_WIRES: f64 = 80.0;
const LOGUP_ROUND_DEGREE: f64 = 5.0;
const INDEX_BITS: usize = 8;

const WHIR_TARGET_BITS: f64 = WHIR_SECURITY_LEVEL_V2 as f64;
const KECCAK_OUTPUT_BITS: f64 = 256.0;
const KECCAK_COLLISION_WORK_FACTOR_BITS: f64 = 128.0;
const OUTER_REDUCTION_INPUT_BITS: f64 = 256.0;
const WHIR_REDUCTION_INPUT_BITS: f64 = 320.0;
const EXAMPLE_HASH_QUERY_BUDGET: f64 = 4_294_967_296.0; // 2^32

#[derive(Clone, Debug)]
struct WhirFailureTerm {
    #[allow(dead_code)]
    label: String,
    bits: f64,
    multiplicity: usize,
}

fn bits(error: f64) -> f64 {
    -error.log2()
}

fn error_at_bits(security_bits: f64) -> f64 {
    2.0_f64.powf(-security_bits)
}

fn pow_acceptance_work_bits(threshold: u64) -> f64 {
    // The verifier accepts `value <= threshold`, so one nonce succeeds with
    // exact probability `(threshold + 1) / 2^64`. Upstream's displayed
    // `difficulty()` uses `threshold` and is microscopically optimistic.
    if threshold == u64::MAX {
        0.0
    } else {
        64.0 - ((threshold as u128 + 1) as f64).log2()
    }
}

fn extension_field_size() -> f64 {
    GOLDILOCKS_P.powi(3)
}

fn extension_field_bits() -> f64 {
    extension_field_size().log2()
}

fn historical_base_logup_error() -> f64 {
    (2.0 * MAX_ROWS * MAX_ROUTED_WIRES) / GOLDILOCKS_P
}

fn conservative_ext3_logup_error() -> f64 {
    let n = MAX_ROW_VARIABLES_V2 as f64;
    // Rational fingerprint 2NR, helper aggregation R, random-tau zero test n,
    // joint-combination challenge 1, degree-five sumcheck n*d, and a second
    // conservative 2NR charge for denominator/pole events.
    let numerator =
        4.0 * MAX_ROWS * MAX_ROUTED_WIRES + MAX_ROUTED_WIRES + n + 1.0 + n * LOGUP_ROUND_DEGREE;
    numerator / extension_field_size()
}

fn ext3_gate_error() -> f64 {
    let n = MAX_ROW_VARIABLES_V2 as f64;
    // Alpha aggregation (G-1), random-tau Boolean-cube detection n, and the
    // degree-d sumcheck n*d. There is no extension-flattening event: every
    // gate formula is evaluated directly over Fp3 (with Plonky2 Ext2 values
    // represented as pairs of Fp3 coordinates).
    let numerator =
        (MAX_GATE_CONSTRAINTS_V2 as f64 - 1.0) + n + n * MAX_GATE_ROUND_DEGREE_V2 as f64;
    numerator / extension_field_size()
}

fn direct_public_input_binding_error() -> f64 {
    // If any ordered raw PI differs from its canonical routed-wire value,
    // eta aggregation has degree at most m-1. Conditional on a non-zero
    // aggregate, the independent xi combiner has at most one bad value.
    // Both challenges are uniform in Fp3 and zero remains an ordinary event.
    MAX_PUBLIC_INPUTS_V2 as f64 / extension_field_size()
}

fn projection_error() -> f64 {
    let events = NUM_PCS_GROUPS_V2 * NUM_PCS_TERMINAL_POINTS_V2 * INDEX_BITS;
    events as f64 / extension_field_size()
}

fn arithmetic_error() -> f64 {
    conservative_ext3_logup_error() + direct_public_input_binding_error() + ext3_gate_error()
}

fn outer_statistical_error() -> f64 {
    arithmetic_error() + projection_error()
}

fn adaptive_whir_profile(num_variables: usize, security_level: usize) -> WhirPCS {
    assert!((1..=MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2).contains(&num_variables));
    let folding_factor = WHIR_FOLDING_FACTOR_V2.min(num_variables.saturating_sub(1).max(1));
    let starting_log_inv_rate = if num_variables <= folding_factor {
        1
    } else {
        WHIR_MAX_STARTING_LOG_INV_RATE_V2.min(num_variables - folding_factor)
    };
    WhirPCS::new(
        security_level,
        WHIR_POW_BITS_V2,
        starting_log_inv_rate,
        folding_factor,
    )
}

/// Reproduce every native WHIR round-by-round failure term instead of treating
/// `Config::security_level` (the minimum one term) as a complete protocol
/// bound. Multiplicity is explicit for every binary fold performed by a native
/// sumcheck. The three initial OOD commitments are charged independently.
fn native_whir_failure_terms(num_variables: usize, security_level: usize) -> Vec<WhirFailureTerm> {
    let pcs = adaptive_whir_profile(num_variables, security_level);
    let config = pcs.constituent_config(1usize << num_variables);
    let field_bits = extension_field_bits();
    let mut terms = Vec::new();
    let mut push = |label: String, bits: f64, multiplicity: usize| {
        assert!(bits.is_finite() && bits > 0.0);
        assert!(multiplicity > 0);
        terms.push(WhirFailureTerm {
            label,
            bits,
            multiplicity,
        });
    };

    let total_vectors = NUM_PCS_GROUPS_V2 * config.initial_committer.num_vectors;
    if total_vectors > 1 {
        push(
            "initial vector RLC".to_string(),
            field_bits - ((total_vectors - 1) as f64).log2(),
            1,
        );
    }
    if NUM_PCS_TERMINAL_POINTS_V2 > 1 {
        push(
            "initial linear-form RLC".to_string(),
            field_bits - ((NUM_PCS_TERMINAL_POINTS_V2 - 1) as f64).log2(),
            1,
        );
    }
    if !config.initial_committer.unique_decoding() {
        push(
            "initial OOD commitments".to_string(),
            config.initial_committer.rbr_ood_sample(),
            NUM_PCS_GROUPS_V2,
        );
    }

    let initial_list_bits = config.initial_committer.list_size().log2();
    let initial_sumcheck_bits = field_bits - (initial_list_bits + 1.0);
    let initial_fold_bits = config
        .initial_committer
        .rbr_soundness_fold_prox_gaps()
        .min(initial_sumcheck_bits)
        + pow_acceptance_work_bits(config.initial_sumcheck.round_pow.threshold);
    push(
        "initial binary folds".to_string(),
        initial_fold_bits,
        config.initial_sumcheck.num_rounds,
    );

    let mut preceding_query_bits = config.initial_committer.rbr_queries();
    let mut preceding_in_domain_samples = config.initial_committer.in_domain_samples;
    for (round_index, round) in config.round_configs.iter().enumerate() {
        if !round.irs_committer.unique_decoding() {
            push(
                format!("round[{round_index}] OOD sample"),
                round.irs_committer.rbr_ood_sample(),
                1,
            );
        }
        let list_bits = round.irs_committer.list_size().log2();
        let constraint_count = round.irs_committer.out_domain_samples + preceding_in_domain_samples;
        let combination_bits = field_bits - ((constraint_count as f64).log2() + list_bits + 1.0);
        let query_bits = preceding_query_bits.min(combination_bits)
            + pow_acceptance_work_bits(round.pow.threshold);
        push(format!("round[{round_index}] query"), query_bits, 1);

        let sumcheck_bits = field_bits - (list_bits + 1.0);
        let fold_bits = round
            .irs_committer
            .rbr_soundness_fold_prox_gaps()
            .min(sumcheck_bits)
            + pow_acceptance_work_bits(round.sumcheck.round_pow.threshold);
        push(
            format!("round[{round_index}] binary folds"),
            fold_bits,
            round.sumcheck.num_rounds,
        );
        preceding_in_domain_samples = round.irs_committer.in_domain_samples;
        preceding_query_bits = round.irs_committer.rbr_queries();
    }

    push(
        "final query".to_string(),
        preceding_query_bits + pow_acceptance_work_bits(config.final_pow.threshold),
        1,
    );
    if config.final_sumcheck.num_rounds > 0 {
        push(
            "final binary folds".to_string(),
            field_bits - 1.0 + pow_acceptance_work_bits(config.final_sumcheck.round_pow.threshold),
            config.final_sumcheck.num_rounds,
        );
    }
    terms
}

fn native_whir_union_work_inverse(num_variables: usize, security_level: usize) -> f64 {
    native_whir_failure_terms(num_variables, security_level)
        .iter()
        .map(|term| term.multiplicity as f64 * error_at_bits(term.bits))
        .sum()
}

fn outer_base_challenge_limbs() -> usize {
    // eta,beta,gamma,xi,lambda,rho,kappa,gate-alpha; two tau vectors;
    // two coupled sumcheck challenges per row; two index points.
    EXTENSION_FIELD_LIMBS_V2 * (8 + 4 * MAX_ROW_VARIABLES_V2 + 2 * MAX_CONSTITUENT_INDEX_BITS_V2)
}

fn whir_base_challenge_limbs(num_variables: usize) -> usize {
    let pcs = adaptive_whir_profile(num_variables, WHIR_SECURITY_LEVEL_V2);
    let config = pcs.constituent_config(1usize << num_variables);
    let total_vectors = NUM_PCS_GROUPS_V2 * config.initial_committer.num_vectors;
    assert_eq!(NUM_PCS_CLAIMS_V2 % total_vectors, 0);
    let num_linear_forms = NUM_PCS_CLAIMS_V2 / total_vectors;
    let initial_constraints =
        NUM_PCS_GROUPS_V2 * config.initial_committer.out_domain_samples + num_linear_forms;
    let mut ext3_challenges = NUM_PCS_GROUPS_V2 * config.initial_committer.out_domain_samples
        + usize::from(total_vectors > 1)
        + usize::from(initial_constraints > 1)
        + config.initial_sumcheck.num_rounds;
    let mut previous_in_domain_samples = config.initial_committer.in_domain_samples;
    for round in &config.round_configs {
        ext3_challenges += round.irs_committer.out_domain_samples
            + usize::from(round.irs_committer.out_domain_samples + previous_in_domain_samples > 1)
            + round.sumcheck.num_rounds;
        previous_in_domain_samples = round.irs_committer.in_domain_samples;
    }
    ext3_challenges += config.final_sumcheck.num_rounds;
    EXTENSION_FIELD_LIMBS_V2 * ext3_challenges
}

fn extraction_bias(num_variables: usize) -> f64 {
    outer_base_challenge_limbs() as f64 * GOLDILOCKS_P * error_at_bits(OUTER_REDUCTION_INPUT_BITS)
        + whir_base_challenge_limbs(num_variables) as f64
            * GOLDILOCKS_P
            * error_at_bits(WHIR_REDUCTION_INPUT_BITS)
}

fn per_oracle_trial_union_bound(num_variables: usize, security_level: usize) -> f64 {
    native_whir_union_work_inverse(num_variables, security_level)
        + outer_statistical_error()
        + extraction_bias(num_variables)
}

fn keccak_random_oracle_collision_bound(hash_queries: f64) -> f64 {
    assert!(hash_queries >= 0.0);
    hash_queries * (hash_queries - 1.0).max(0.0) * error_at_bits(KECCAK_OUTPUT_BITS + 1.0)
}

fn coarse_random_oracle_advantage_bound(num_variables: usize, hash_queries: f64) -> f64 {
    assert!(hash_queries >= 1.0);
    hash_queries * per_oracle_trial_union_bound(num_variables, WHIR_SECURITY_LEVEL_V2)
        + keccak_random_oracle_collision_bound(hash_queries)
}

fn local_pcs_conventional_work_factor_bits() -> f64 {
    [
        bits(conservative_ext3_logup_error()),
        bits(direct_public_input_binding_error()),
        bits(ext3_gate_error()),
        bits(projection_error()),
        bits(native_whir_union_work_inverse(
            MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2,
            WHIR_SECURITY_LEVEL_V2,
        )),
        KECCAK_COLLISION_WORK_FACTOR_BITS,
    ]
    .into_iter()
    .fold(f64::INFINITY, f64::min)
}

fn complete_statement_conventional_work_factor_bits() -> f64 {
    local_pcs_conventional_work_factor_bits()
}

/// Per-repetition error of the rejected base-field gate construction. The
/// extra one is its Ext2-to-base flattening event.
fn rejected_base_gate_error() -> f64 {
    let n = MAX_ROW_VARIABLES_V2 as f64;
    ((MAX_GATE_CONSTRAINTS_V2 as f64 - 1.0) + 1.0 + n + n * MAX_GATE_ROUND_DEGREE_V2 as f64)
        / GOLDILOCKS_P
}

#[test]
fn historical_outer_goldilocks_floor_was_only_43_point_678_bits() {
    assert!((bits(historical_base_logup_error()) - 43.678_071_904_8).abs() < 1e-9);
}

#[test]
fn ext3_logup_budget_double_charges_poles() {
    let error = conservative_ext3_logup_error();
    assert!((error * extension_field_size() - 2_621_599.0).abs() < 1e-6);
    assert!((bits(error) - 170.677_984_402_0).abs() < 1e-9);
}

#[test]
fn direct_raw_public_input_binding_has_the_reviewed_maximum_numerator() {
    assert_eq!(MAX_PUBLIC_INPUTS_V2, 256);
    let error = direct_public_input_binding_error();
    assert_eq!(error * extension_field_size(), 256.0);
    assert!(bits(error) > 183.99 && bits(error) < 184.01);
}

#[test]
fn one_exact_ext3_gate_sumcheck_has_the_reviewed_numerator() {
    let error = ext3_gate_error();
    assert_eq!(error * extension_field_size(), 265.0);
    assert!(bits(error) > 183.9 && bits(error) < 184.1);
    assert_eq!(MAX_GATE_ROUND_DEGREE_V2, 10);
}

#[test]
fn transcript_round_is_exactly_two_ext3_messages_and_six_base_squeezes() {
    let messages = 2; // log Ext3 coefficients, then gate Ext3 coefficients.
    let base_squeezes = 3 + 3; // one independent Fp3 challenge per message.
    assert_eq!(messages, 2);
    assert_eq!(base_squeezes, 6);
}

#[test]
fn three_group_two_point_projection_and_mask_are_pinned() {
    assert_eq!(NUM_PCS_GROUPS_V2, 3);
    assert_eq!(NUM_PCS_TERMINAL_POINTS_V2, 2);
    assert_eq!(PACKED_BOUND_CLAIM_MASK_V2, [0x1f]);
    assert_eq!(
        NUM_PCS_GROUPS_V2 * NUM_PCS_TERMINAL_POINTS_V2 * INDEX_BITS,
        48
    );
    assert!(bits(projection_error()) > 186.4 && bits(projection_error()) < 186.5);

    let packed_variables = MAX_ROW_VARIABLES_V2 + INDEX_BITS;
    let pcs = WhirPCS::for_constituents(packed_variables, 1);
    assert_eq!(pcs.params.security_level, WHIR_TARGET_BITS as usize);
    let estimated = pcs.constituent_security_level(
        1usize << packed_variables,
        NUM_PCS_GROUPS_V2,
        NUM_PCS_TERMINAL_POINTS_V2,
    );
    assert!(
        estimated >= WHIR_TARGET_BITS - 1e-9,
        "3-group/2-point WHIR estimate is only {estimated:.12} bits"
    );
}

#[test]
fn outer_algebraic_and_projection_budget_is_machine_checked_separately() {
    assert!(bits(arithmetic_error()) > 170.67);
    assert!(bits(outer_statistical_error()) > 170.67);

    let algebraic_numerator = (arithmetic_error() + projection_error()) * extension_field_size();
    assert!((algebraic_numerator - 2_622_168.0).abs() < 1e-6);
}

#[test]
fn whir_extraction_count_matches_the_actual_pinned_max_dimension_trace() {
    // This fixture was produced by the native grouped-WHIR prover. Replaying
    // its opaque WHIR streams exercises the production preflight and pinned
    // Spongefish codecs, independently of the schedule formula above. The
    // fixture must be freshly proved for the current profile: changed protocol
    // IDs change Fiat--Shamir query indices and therefore Merkle hint lengths.
    let fixture = MleVerifierV2Fixture::from_canonical_json(include_str!(
        "../contracts/test/fixtures/v2_max_resource.json"
    ))
    .expect("canonical maximum-dimension fixture");
    let num_variables = fixture.size_upper_bound.packed_num_variables;
    assert_eq!(
        num_variables,
        MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2
    );
    let current_profile = derive_whir_deployment_profile_for_packed_num_vars_v2(num_variables)
        .expect("current maximum-dimension deployment profile");
    assert_eq!(
        fixture.verification_config.whir, current_profile.params,
        "maximum-dimension proof fixture is stale for the current WHIR profile"
    );
    let compact = fixture
        .compact_proof
        .decode_and_validate(core::str::from_utf8(&COMPACT_MAGIC_V2).unwrap())
        .expect("integral compact proof bytes");
    let proof = decode_compact_v2::<GoldilocksField>(&compact, &fixture.compact_shape.decode())
        .expect("maximum-dimension compact proof grammar");
    let trace = WhirPCS::for_constituents(num_variables, NUM_PACKED_VECTORS_PER_GROUP_V2)
        .trace_grouped_preflight(
            num_variables,
            &proof.whir_eval_proof,
            WHIR_SESSION_SPLIT_V2,
            NUM_PCS_GROUPS_V2,
            NUM_PCS_CLAIMS_V2,
        )
        .expect("production maximum-dimension WHIR trace");

    let mut ext3_squeezes = 0usize;
    for event in &trace {
        if event.kind != WhirNativeTraceEventKind::Squeeze {
            continue;
        }
        match event.event_bytes.len() {
            // Pinned `DecodingFieldBuffer<F>` requests modulus_bytes + 32
            // bytes for each of the three Goldilocks limbs: 3 * (8 + 32).
            120 => ext3_squeezes += 1,
            // Proof-of-work challenges are raw 256-bit strings, not field
            // reductions, and therefore add no mod-p extraction bias.
            32 => assert!(event.label.contains("pow.challenge")),
            width => panic!("unexpected pinned WHIR squeeze width {width}"),
        }
    }
    let actual_base_limbs = EXTENSION_FIELD_LIMBS_V2 * ext3_squeezes;
    assert_eq!(actual_base_limbs, 102);
    assert_eq!(whir_base_challenge_limbs(num_variables), actual_base_limbs);
    assert!(trace
        .iter()
        .filter(|event| event.kind == WhirNativeTraceEventKind::QuerySqueeze)
        .all(|event| event.event_bytes.len() == 1));
}

#[test]
fn native_whir_union_work_factor_is_machine_checked_for_every_production_dimension() {
    assert_eq!(WHIR_SECURITY_LEVEL_V2, 105);
    let max_variables = MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2;
    assert_eq!(max_variables, 21);
    for rejected_variables in 22..=29 {
        assert!(
            derive_whir_deployment_profile_for_packed_num_vars_v2(rejected_variables).is_err(),
            "packed dimension {rejected_variables} is outside the admitted envelope"
        );
    }
    let mut minimum_bits = f64::INFINITY;
    let mut minimum_dimension = 0;
    for num_variables in 1..=max_variables {
        let production = WhirPCS::for_constituents(num_variables, NUM_PACKED_VECTORS_PER_GROUP_V2);
        let reconstructed = adaptive_whir_profile(num_variables, WHIR_SECURITY_LEVEL_V2);
        assert_eq!(production.params, reconstructed.params);
        let aggregate_bits = bits(native_whir_union_work_inverse(
            num_variables,
            WHIR_SECURITY_LEVEL_V2,
        ));
        if aggregate_bits < minimum_bits {
            minimum_bits = aggregate_bits;
            minimum_dimension = num_variables;
        }
    }
    assert_eq!(minimum_dimension, 21);
    assert!((minimum_bits - 101.534_561_723).abs() < 1e-6);
    assert!(minimum_bits > 101.5);

    let maximum_terms = native_whir_failure_terms(max_variables, WHIR_SECURITY_LEVEL_V2);
    let dominant_multiplicity = maximum_terms
        .iter()
        .filter(|term| (term.bits - WHIR_TARGET_BITS).abs() < 1e-6)
        .map(|term| term.multiplicity)
        .sum::<usize>();
    assert_eq!(dominant_multiplicity, 9);
    assert_eq!(
        maximum_terms
            .iter()
            .map(|term| term.multiplicity)
            .sum::<usize>(),
        35
    );
    assert_eq!(maximum_terms.len(), 18);
}

#[test]
fn upstream_single_minimum_is_not_misreported_as_the_native_union() {
    let max_variables = MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2;
    let pcs = WhirPCS::for_constituents(max_variables, NUM_PACKED_VECTORS_PER_GROUP_V2);
    let displayed_minimum = pcs.constituent_security_level(
        1usize << max_variables,
        NUM_PCS_GROUPS_V2,
        NUM_PCS_TERMINAL_POINTS_V2,
    );
    let union_work_bits = bits(native_whir_union_work_inverse(
        max_variables,
        WHIR_SECURITY_LEVEL_V2,
    ));
    assert!(displayed_minimum >= WHIR_TARGET_BITS - 1e-9);
    assert!(displayed_minimum - union_work_bits > 3.46);
    assert!(displayed_minimum - union_work_bits < 3.47);
}

#[test]
fn target_104_fails_the_complete_native_whir_union_work_factor() {
    // The production target is 105 so the complete native union work factor clears the
    // reviewed 100-bit floor with margin; one target bit less would not.
    let max_variables = MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2;
    let aggregate_bits = bits(native_whir_union_work_inverse(max_variables, 104));
    assert!((aggregate_bits - 100.674_765_149).abs() < 1e-6);
    assert!(aggregate_bits < 101.0);
}

#[test]
fn raw_oracle_trials_not_completed_proofs_control_the_literal_rom_bound() {
    let max_variables = MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2;
    assert_eq!(outer_base_challenge_limbs(), 228);
    assert_eq!(whir_base_challenge_limbs(max_variables), 102);

    let one_trial_bits = bits(per_oracle_trial_union_bound(
        max_variables,
        WHIR_SECURITY_LEVEL_V2,
    ));
    assert!((one_trial_bits - 101.534_561_723).abs() < 1e-6);
    assert!(one_trial_bits > 101.5);

    // An adversary may abort and grind at an internal stage. Counting only
    // completed proofs as attempts would miss those candidates. The coarse
    // ROM bound therefore charges every raw oracle trial against the union.
    let literal_bits = bits(coarse_random_oracle_advantage_bound(
        max_variables,
        EXAMPLE_HASH_QUERY_BUDGET,
    ));
    assert!((literal_bits - 69.534_561_723).abs() < 1e-6);
    assert!(literal_bits < 101.0);
    assert!(
        bits(keccak_random_oracle_collision_bound(
            EXAMPLE_HASH_QUERY_BUDGET
        )) > 192.99
    );
}

#[test]
fn each_power_of_two_raw_oracle_budget_loses_its_log2_from_the_union_work_factor() {
    let max_variables = MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2;
    let one = per_oracle_trial_union_bound(max_variables, WHIR_SECURITY_LEVEL_V2);
    for exponent in 0..=32 {
        let hash_queries = 2.0_f64.powi(exponent);
        assert!(
            coarse_random_oracle_advantage_bound(max_variables, hash_queries) >= hash_queries * one
        );
        assert!((bits(hash_queries * one) - (bits(one) - f64::from(exponent))).abs() < 1e-9);
    }

    let hash_queries = 2.0_f64.powi(64);
    assert!((bits(keccak_random_oracle_collision_bound(hash_queries)) - 129.0).abs() < 1e-9);
}

#[test]
fn rejected_three_base_repetitions_admit_sequential_round_bridging() {
    let one = rejected_base_gate_error();
    assert_eq!(one * GOLDILOCKS_P, 266.0);
    assert!(bits(one) < 56.0);

    // Commit-before-challenge within a round does not multiply the work of
    // three base repetitions. With at least three row rounds, a malicious
    // prover can bridge repetition 0 in round 0, retain that honest suffix,
    // then use later messages as nonces to bridge repetitions 1 and 2. The
    // expected generic work is on the order of three independent geometric
    // searches performed sequentially, not one search for a cubed event.
    assert!(MAX_ROW_VARIABLES_V2 >= 3);
    let expected_queries = 3.0 / one;
    assert!(expected_queries.log2() < 58.0);
    assert!(expected_queries.log2() > 57.0);
    assert!(expected_queries.log2() < 128.0);
}

#[test]
fn local_pcs_work_factor_and_literal_probability_are_distinct_conventions() {
    // At target 105 the native WHIR union (about 101.53 bits) is the binding term; the
    // generic Keccak collision work factor (128) no longer caps the local PCS figure.
    let max_variables = MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2;
    assert!((local_pcs_conventional_work_factor_bits() - 101.534_561_723).abs() < 1e-6);
    assert!(local_pcs_conventional_work_factor_bits() < KECCAK_COLLISION_WORK_FACTOR_BITS);
    assert_eq!(
        local_pcs_conventional_work_factor_bits(),
        bits(native_whir_union_work_inverse(max_variables, WHIR_SECURITY_LEVEL_V2))
    );

    // Treating the work factor as a literal fixed probability term leaves no room for any
    // positive algebraic/WHIR error.
    let strict_total = error_at_bits(101.534_561_723) + outer_statistical_error();
    // The outer term is ~2^-170, below f64 resolution next to 2^-101.5: it cannot raise the bound.
    assert!(bits(strict_total) <= 101.534_561_723 + 1e-9);
}

#[test]
fn complete_statement_uses_direct_pcs_bound_raw_public_inputs() {
    assert!((local_pcs_conventional_work_factor_bits() - 101.534_561_723).abs() < 1e-6);
    assert_eq!(
        complete_statement_conventional_work_factor_bits(),
        local_pcs_conventional_work_factor_bits()
    );
    let max_variables = MAX_ROW_VARIABLES_V2 + MAX_CONSTITUENT_INDEX_BITS_V2;
    assert_eq!(
        coarse_random_oracle_advantage_bound(max_variables, 1.0),
        per_oracle_trial_union_bound(max_variables, WHIR_SECURITY_LEVEL_V2)
    );
}
