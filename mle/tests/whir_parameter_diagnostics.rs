//! Read-only native WHIR parameter diagnostics for the largest current parent v2 profile.
//!
//! This deliberately does not feed production schema generation. It exists
//! only to compare native constructor outputs before any protocol migration is
//! proposed.

use std::time::{Duration, Instant};

use plonky2_mle::commitment::whir_pcs::WhirPCS;
use plonky2_mle::compact_v2::CompactV2Shape;
use plonky2_mle::fixture::WhirRoundParamsFixture;
use plonky2_mle::fixture_v2::{
    solidity_abi_mle_proof_encoded_len_v2, whir_proof_size_upper_bound_v2, WhirParamsV2Fixture,
    WhirProofSizeUpperBoundV2,
};
use plonky2_mle::protocol_schema_v2::{
    MAX_COMPACT_PROOF_BYTES_V2, MAX_WHIR_HINT_BYTES_V2, MAX_WHIR_NARG_BYTES_V2,
    WHIR_SESSION_SPLIT_V2,
};
use whir::algebra::fields::{Field64, Field64_3};

const NUM_VARIABLES: usize = 21;
const NUM_COMMITMENTS: usize = 3;
const NUM_LINEAR_FORMS: usize = 2;
const MAX_PROFILE_FIXED_COMPACT_BYTES: usize = 19_196;
const MAX_ENVELOPE_FIXED_COMPACT_BYTES: usize = 20_060;
const SMALL_PROFILE_FIXED_COMPACT_BYTES: usize = 15_236;

#[derive(Clone, Debug)]
struct PowStage {
    label: String,
    repetitions: usize,
    threshold: u64,
    difficulty_bits: f64,
    expected_work: f64,
}

#[derive(Clone, Debug)]
struct Metrics {
    num_variables: usize,
    folding_factor: usize,
    starting_log_inv_rate: usize,
    requested_pow_bits: usize,
    security_target: usize,
    effective_security_bits: f64,
    num_rounds: usize,
    final_sumcheck_rounds: usize,
    samples: Vec<usize>,
    out_of_domain_samples: Vec<usize>,
    codeword_log_lengths: Vec<u32>,
    sumcheck_rounds: usize,
    active_pow_checks: usize,
    max_generated_pow_bits: f64,
    expected_pow_work_log2: f64,
    pow_stages: Vec<PowStage>,
    committed_codeword_rows: usize,
    committed_codeword_limbs: usize,
    queried_leaf_limbs: usize,
    merkle_siblings: usize,
    merkle_hashes: usize,
    round_constraint_terms: usize,
    dimension_weighted_round_constraints: usize,
    proof_size: WhirProofSizeUpperBoundV2,
}

fn metrics(
    security_target: usize,
    requested_pow_bits: usize,
    starting_log_inv_rate: usize,
    folding_factor: usize,
) -> Metrics {
    metrics_for_n(
        NUM_VARIABLES,
        security_target,
        requested_pow_bits,
        starting_log_inv_rate,
        folding_factor,
    )
}

fn metrics_for_n(
    num_variables: usize,
    security_target: usize,
    requested_pow_bits: usize,
    starting_log_inv_rate: usize,
    folding_factor: usize,
) -> Metrics {
    let pcs = WhirPCS::new(
        security_target,
        requested_pow_bits,
        starting_log_inv_rate,
        folding_factor,
    );
    let config = pcs.constituent_config(1 << num_variables);

    let rounds = config
        .round_configs
        .iter()
        .map(|round| WhirRoundParamsFixture {
            codeword_length: round.irs_committer.codeword_length,
            merkle_depth: round.irs_committer.codeword_length.ilog2() as usize,
            // These three values are irrelevant to proof grammar sizing; use
            // structurally valid placeholders rather than duplicating the
            // deployment profile's roots-of-unity/coset derivation here.
            domain_generator: "1".to_string(),
            in_domain_samples: round.irs_committer.in_domain_samples,
            out_domain_samples: round.irs_committer.out_domain_samples,
            sumcheck_rounds: round.sumcheck.num_rounds,
            interleaving_depth: round.irs_committer.interleaving_depth,
            coset_size: 1,
            num_cosets: round.irs_committer.codeword_length,
            num_variables: round.initial_num_variables(),
            pow_threshold: round.pow.threshold.to_string(),
            sumcheck_pow_threshold: round.sumcheck.round_pow.threshold.to_string(),
        })
        .collect::<Vec<_>>();
    let params = WhirParamsV2Fixture {
        num_variables,
        folding_factor,
        num_vectors: 1,
        num_commitments: NUM_COMMITMENTS,
        out_domain_samples: config.initial_committer.out_domain_samples,
        in_domain_samples: config.initial_committer.in_domain_samples,
        initial_sumcheck_rounds: config.initial_sumcheck.num_rounds,
        num_rounds: rounds.len(),
        final_sumcheck_rounds: config.final_sumcheck.num_rounds,
        // WHIR transmits the vector entering the final sumcheck, not the
        // scalar left after that sumcheck has folded it.
        final_size: config.final_sumcheck.initial_size,
        initial_codeword_length: config.initial_committer.codeword_length,
        initial_merkle_depth: config.initial_committer.codeword_length.ilog2() as usize,
        initial_domain_generator: "1".to_string(),
        initial_interleaving_depth: config.initial_committer.interleaving_depth,
        initial_num_variables: config.initial_num_variables(),
        initial_coset_size: 1,
        initial_num_cosets: config.initial_committer.codeword_length,
        initial_sumcheck_pow_threshold: config.initial_sumcheck.round_pow.threshold.to_string(),
        final_pow_threshold: config.final_pow.threshold.to_string(),
        final_sumcheck_pow_threshold: config.final_sumcheck.round_pow.threshold.to_string(),
        evaluation_point: Vec::new(),
        evaluation_point2: Vec::new(),
        additional_evaluation_points: Vec::new(),
        rounds,
    };
    let proof_size = whir_proof_size_upper_bound_v2(&params).unwrap();

    let samples = std::iter::once(config.initial_committer.in_domain_samples)
        .chain(
            config
                .round_configs
                .iter()
                .map(|round| round.irs_committer.in_domain_samples),
        )
        .collect::<Vec<_>>();
    let out_of_domain_samples = std::iter::once(config.initial_committer.out_domain_samples)
        .chain(
            config
                .round_configs
                .iter()
                .map(|round| round.irs_committer.out_domain_samples),
        )
        .collect::<Vec<_>>();
    let codeword_lengths = std::iter::once(config.initial_committer.codeword_length)
        .chain(
            config
                .round_configs
                .iter()
                .map(|round| round.irs_committer.codeword_length),
        )
        .collect::<Vec<_>>();
    let codeword_log_lengths = codeword_lengths
        .iter()
        .map(|length| length.ilog2())
        .collect::<Vec<_>>();
    let committed_codeword_rows = codeword_lengths
        .iter()
        .enumerate()
        .map(|(index, length)| length * if index == 0 { NUM_COMMITMENTS } else { 1 })
        .sum();
    let committed_codeword_limbs = config.initial_committer.codeword_length
        * config.initial_committer.interleaving_depth
        * NUM_COMMITMENTS
        + config
            .round_configs
            .iter()
            .map(|round| {
                round.irs_committer.codeword_length * round.irs_committer.interleaving_depth * 3
            })
            .sum::<usize>();
    let queried_leaf_limbs = proof_size
        .openings
        .iter()
        .map(|opening| {
            opening.max_distinct_queries
                * opening.num_columns
                * opening.field_limbs
                * opening.num_commitments
        })
        .sum();
    let merkle_siblings = proof_size
        .openings
        .iter()
        .map(|opening| opening.max_merkle_siblings_per_commitment * opening.num_commitments)
        .sum();
    // For k opened leaves and s supplied siblings, a canonical binary
    // multiproof hashes k+s-1 internal nodes. Solidity additionally hashes
    // each opened row once before entering the tree.
    let merkle_hashes = proof_size
        .openings
        .iter()
        .map(|opening| {
            opening.num_commitments
                * (2 * opening.max_distinct_queries + opening.max_merkle_siblings_per_commitment
                    - 1)
        })
        .sum();

    // The initial FinalClaim constraint entry contains every commitment's OOD
    // point. Each intermediate entry combines the preceding opening queries
    // with that round's OOD points.
    let mut round_constraint_terms = NUM_COMMITMENTS * config.initial_committer.out_domain_samples;
    let mut dimension_weighted_round_constraints = round_constraint_terms * num_variables;
    for (round_index, round) in config.round_configs.iter().enumerate() {
        let terms = samples[round_index] + round.irs_committer.out_domain_samples;
        round_constraint_terms += terms;
        dimension_weighted_round_constraints += terms * round.initial_num_variables();
    }

    let mut active_pow_checks = 0usize;
    let mut max_generated_pow_bits = 0.0f64;
    let mut expected_pow_work = 0.0f64;
    let mut pow_stages = Vec::new();
    let mut add_pow = |label: String, threshold: u64, repetitions: usize| {
        if threshold != u64::MAX {
            active_pow_checks += repetitions;
            let difficulty = 64.0 - (threshold as f64).log2();
            let work = repetitions as f64 * difficulty.exp2();
            max_generated_pow_bits = max_generated_pow_bits.max(difficulty);
            expected_pow_work += work;
            pow_stages.push(PowStage {
                label,
                repetitions,
                threshold,
                difficulty_bits: difficulty,
                expected_work: work,
            });
        }
    };
    add_pow(
        "initial_sumcheck".to_string(),
        config.initial_sumcheck.round_pow.threshold,
        config.initial_sumcheck.num_rounds,
    );
    for (round_index, round) in config.round_configs.iter().enumerate() {
        add_pow(
            format!("round[{round_index}]_query"),
            round.pow.threshold,
            1,
        );
        add_pow(
            format!("round[{round_index}]_sumcheck"),
            round.sumcheck.round_pow.threshold,
            round.sumcheck.num_rounds,
        );
    }
    add_pow("final_query".to_string(), config.final_pow.threshold, 1);
    add_pow(
        "final_sumcheck".to_string(),
        config.final_sumcheck.round_pow.threshold,
        config.final_sumcheck.num_rounds,
    );

    Metrics {
        num_variables,
        folding_factor,
        starting_log_inv_rate,
        requested_pow_bits,
        security_target,
        effective_security_bits: config.security_level(NUM_COMMITMENTS, NUM_LINEAR_FORMS),
        num_rounds: config.round_configs.len(),
        final_sumcheck_rounds: config.final_sumcheck.num_rounds,
        samples,
        out_of_domain_samples,
        codeword_log_lengths,
        sumcheck_rounds: config.initial_sumcheck.num_rounds
            + config
                .round_configs
                .iter()
                .map(|round| round.sumcheck.num_rounds)
                .sum::<usize>()
            + config.final_sumcheck.num_rounds,
        active_pow_checks,
        max_generated_pow_bits,
        expected_pow_work_log2: expected_pow_work.log2(),
        pow_stages,
        committed_codeword_rows,
        committed_codeword_limbs,
        queried_leaf_limbs,
        merkle_siblings,
        merkle_hashes,
        round_constraint_terms,
        dimension_weighted_round_constraints,
        proof_size,
    }
}

fn percent(value: usize, baseline: usize) -> f64 {
    100.0 * value as f64 / baseline as f64
}

fn print_metrics(label: &str, value: &Metrics, baseline: &Metrics) {
    println!(
        "{label}: n={} f={} rate=1/{} requested_pow={} target={} effective={:.12} rounds={}+final{} samples={:?} ood={:?} codeword_logs={:?} narg={} hint_max={} total_max={} leaf_limbs={}({:.1}%) siblings={}({:.1}%) merkle_hashes={}({:.1}%) constraints={}({:.1}%) weighted_constraints={}({:.1}%) sumcheck_rounds={} pow_checks={} max_generated_pow={:.2} pow_work_log2={:.2} committed_rows={}({:.1}%) committed_limbs={}({:.1}%)",
        value.num_variables,
        value.folding_factor,
        1usize << value.starting_log_inv_rate,
        value.requested_pow_bits,
        value.security_target,
        value.effective_security_bits,
        value.num_rounds,
        value.final_sumcheck_rounds,
        value.samples,
        value.out_of_domain_samples,
        value.codeword_log_lengths,
        value.proof_size.narg_bytes,
        value.proof_size.max_hint_bytes,
        value.proof_size.max_total_bytes,
        value.queried_leaf_limbs,
        percent(value.queried_leaf_limbs, baseline.queried_leaf_limbs),
        value.merkle_siblings,
        percent(value.merkle_siblings, baseline.merkle_siblings),
        value.merkle_hashes,
        percent(value.merkle_hashes, baseline.merkle_hashes),
        value.round_constraint_terms,
        percent(value.round_constraint_terms, baseline.round_constraint_terms),
        value.dimension_weighted_round_constraints,
        percent(
            value.dimension_weighted_round_constraints,
            baseline.dimension_weighted_round_constraints,
        ),
        value.sumcheck_rounds,
        value.active_pow_checks,
        value.max_generated_pow_bits,
        value.expected_pow_work_log2,
        value.committed_codeword_rows,
        percent(value.committed_codeword_rows, baseline.committed_codeword_rows),
        value.committed_codeword_limbs,
        percent(
            value.committed_codeword_limbs,
            baseline.committed_codeword_limbs,
        ),
    );
}

fn print_pow_schedule(label: &str, value: &Metrics) {
    let total_work = value
        .pow_stages
        .iter()
        .map(|stage| stage.expected_work)
        .sum::<f64>();
    println!(
        "{label}_pow: checks={} total_expected_work={total_work:.6} total_log2={:.6}",
        value.active_pow_checks,
        total_work.log2(),
    );
    for stage in &value.pow_stages {
        println!(
            "{label}_pow_stage: label={} repetitions={} threshold={} difficulty={:.9} stage_expected_work={:.6} stage_log2={:.9}",
            stage.label,
            stage.repetitions,
            stage.threshold,
            stage.difficulty_bits,
            stage.expected_work,
            stage.expected_work.log2(),
        );
    }
}

fn production_adaptive_folding_and_rate(num_variables: usize) -> (usize, usize) {
    adaptive_folding_and_rate(num_variables, 4)
}

fn adaptive_folding_and_rate(
    num_variables: usize,
    maximum_starting_log_inv_rate: usize,
) -> (usize, usize) {
    let folding_factor = 4.min(num_variables.saturating_sub(1).max(1));
    let starting_log_inv_rate = if num_variables <= folding_factor {
        1
    } else {
        maximum_starting_log_inv_rate.min(num_variables - folding_factor)
    };
    (folding_factor, starting_log_inv_rate)
}

#[test]
#[ignore = "read-only native WHIR parameter sweep; run explicitly with --nocapture"]
fn compare_max_profile_native_whir_parameters() {
    let baseline = metrics(130, 0, 4, 4);
    print_metrics("baseline", &baseline, &baseline);
    assert!(baseline.effective_security_bits + 1e-9 >= 130.0);

    let pow20 = metrics(130, 20, 4, 4);
    assert!(pow20.effective_security_bits + 1e-9 >= 130.0);

    for (label, security, pow, rate, folding) in [
        ("rate16_pow8", 130, 8, 4, 4),
        ("rate16_pow16", 130, 16, 4, 4),
        ("rate16_pow18", 130, 18, 4, 4),
        ("rate16_pow20", 130, 20, 4, 4),
        ("rate16_pow22", 130, 22, 4, 4),
        ("rate16_pow24", 130, 24, 4, 4),
        ("rate16_pow20_target140", 140, 20, 4, 4),
        ("rate16_pow20_target162", 162, 20, 4, 4),
        ("rate32_pow0", 130, 0, 5, 4),
        ("rate32_pow8", 130, 8, 5, 4),
        ("rate32_pow16", 130, 16, 5, 4),
        ("rate32_pow8_target131", 131, 8, 5, 4),
        ("rate32_pow16_target131", 131, 16, 5, 4),
        ("rate64_pow0", 130, 0, 6, 4),
        ("rate64_pow8", 130, 8, 6, 4),
        ("rate64_pow16", 130, 16, 6, 4),
        ("rate64_pow24", 130, 24, 6, 4),
        ("rate64_pow16_target131", 131, 16, 6, 4),
        ("rate128_pow0", 130, 0, 7, 4),
        ("f3_rate16_pow0", 130, 0, 4, 3),
        ("f3_rate32_pow0", 130, 0, 5, 3),
        ("f3_rate64_pow0", 130, 0, 6, 3),
        ("f5_rate16_pow0", 130, 0, 4, 5),
        ("f5_rate32_pow0", 130, 0, 5, 5),
        ("f5_rate64_pow0", 130, 0, 6, 5),
    ] {
        print_metrics(label, &metrics(security, pow, rate, folding), &baseline);
    }

    let mut candidates = Vec::new();
    // Retain the historical 130--132 search space for comparison and include
    // the current target 133; this diagnostic is exploratory and does not
    // select or authorize a production profile.
    for security_target in [130, 131, 132, 133] {
        for folding_factor in 2..=8 {
            for starting_log_inv_rate in 2..=10 {
                for requested_pow_bits in [0, 8, 16, 24] {
                    let candidate = metrics(
                        security_target,
                        requested_pow_bits,
                        starting_log_inv_rate,
                        folding_factor,
                    );
                    if candidate.effective_security_bits + 1e-9 >= 130.0
                        && candidate.queried_leaf_limbs * 4 <= baseline.queried_leaf_limbs * 3
                        && candidate.merkle_siblings * 4 <= baseline.merkle_siblings * 3
                        && candidate.dimension_weighted_round_constraints * 4
                            <= baseline.dimension_weighted_round_constraints * 3
                    {
                        candidates.push(candidate);
                    }
                }
            }
        }
    }
    candidates.sort_by_key(|candidate| {
        (
            candidate.proof_size.max_total_bytes,
            candidate.queried_leaf_limbs,
            candidate.merkle_siblings,
        )
    });
    println!("strong_candidates={}", candidates.len());
    for (index, candidate) in candidates.iter().take(40).enumerate() {
        print_metrics(&format!("candidate[{index}]"), candidate, &baseline);
    }

    let mut bounded = candidates
        .into_iter()
        .filter(|candidate| {
            candidate.committed_codeword_rows <= 4 * baseline.committed_codeword_rows
                && candidate.max_generated_pow_bits <= 24.0
        })
        .collect::<Vec<_>>();
    bounded.sort_by_key(|candidate| {
        (
            candidate.dimension_weighted_round_constraints,
            candidate.queried_leaf_limbs,
            candidate.merkle_siblings,
        )
    });
    println!("bounded_strong_candidates={}", bounded.len());
    for (index, candidate) in bounded.iter().enumerate() {
        print_metrics(&format!("bounded[{index}]"), candidate, &baseline);
    }
}

#[test]
#[ignore = "read-only native PoW schedule explanation; run explicitly with --nocapture"]
fn explain_native_pow0_and_pow20_schedules() {
    let baseline = metrics(130, 0, 4, 4);
    let pow20 = metrics(130, 20, 4, 4);

    assert!((baseline.effective_security_bits - 130.0).abs() < 1e-9);
    assert!((pow20.effective_security_bits - 130.0).abs() < 1e-9);
    assert_eq!(baseline.active_pow_checks, 20);
    assert_eq!(pow20.active_pow_checks, 25);
    assert_eq!(baseline.pow_stages.len(), 5);
    assert_eq!(pow20.pow_stages.len(), 10);

    print_metrics("baseline", &baseline, &baseline);
    print_pow_schedule("baseline", &baseline);
    print_metrics("rate16_pow20", &pow20, &baseline);
    print_pow_schedule("rate16_pow20", &pow20);
}

#[test]
#[ignore = "performs real native WHIR proving, including stochastic proof of work"]
fn benchmark_real_shortlist_proofs_n10() {
    const N: usize = 10;
    let size = 1usize << N;
    let groups = (0..NUM_COMMITMENTS)
        .map(|group| {
            vec![(0..size)
                .map(|row| {
                    Field64::from(
                        (row as u64)
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .wrapping_add(1 + 0x10001 * group as u64),
                    )
                })
                .collect::<Vec<_>>()]
        })
        .collect::<Vec<_>>();
    let points = (0..NUM_LINEAR_FORMS)
        .map(|point| {
            (0..N)
                .map(|coordinate| {
                    Field64_3::new(
                        Field64::from((3 * coordinate + 17 * point + 2) as u64),
                        Field64::from((5 * coordinate + 19 * point + 7) as u64),
                        Field64::from((11 * coordinate + 23 * point + 13) as u64),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    fn prove_once(
        label: &str,
        pcs: &WhirPCS,
        groups: &[Vec<Vec<Field64>>],
        points: &[Vec<Field64_3>],
    ) -> (Duration, Duration, usize, usize) {
        assert!(
            pcs.constituent_security_level(1 << N, NUM_COMMITMENTS, NUM_LINEAR_FORMS) + 1e-9
                >= 130.0
        );
        let commit_start = Instant::now();
        let committed = pcs.commit_grouped(groups, WHIR_SESSION_SPLIT_V2);
        let roots = committed.roots.clone();
        let commit_time = commit_start.elapsed();
        let point_refs = points.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let prove_start = Instant::now();
        let (proof, evaluations) = pcs.prove_grouped_with_eval(committed, &point_refs);
        let prove_time = prove_start.elapsed();
        let expected = evaluations
            .into_iter()
            .flatten()
            .map(Some)
            .collect::<Vec<_>>();
        let root_refs = roots.iter().map(Vec::as_slice).collect::<Vec<_>>();
        pcs.verify_grouped(
            N,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT_V2,
            &point_refs,
            NUM_COMMITMENTS,
            &root_refs,
        )
        .expect("timed proof must verify");
        println!(
            "{label}_real_n10 commit_ms={:.3} prove_ms={:.3} narg={} hints={} whir_bytes={}",
            commit_time.as_secs_f64() * 1000.0,
            prove_time.as_secs_f64() * 1000.0,
            proof.narg_string.len(),
            proof.hints.len(),
            proof.narg_string.len() + proof.hints.len(),
        );
        (
            commit_time,
            prove_time,
            proof.narg_string.len(),
            proof.hints.len(),
        )
    }

    let baseline_metrics = metrics_for_n(N, 130, 0, 4, 4);
    print_pow_schedule("baseline_n10", &baseline_metrics);
    let baseline_pcs = WhirPCS::new(130, 0, 4, 4);
    let (baseline_commit, baseline_prove, _, _) =
        prove_once("baseline", &baseline_pcs, &groups, &points);

    for (label, requested_pow_bits, starting_log_inv_rate) in [
        ("rate16_pow20", 20, 4),
        ("rate16_pow22", 22, 4),
        ("rate16_pow24", 24, 4),
        ("rate32_pow0", 0, 5),
        ("rate32_pow16", 16, 5),
    ] {
        let candidate_metrics = metrics_for_n(N, 130, requested_pow_bits, starting_log_inv_rate, 4);
        print_pow_schedule(&format!("{label}_n10"), &candidate_metrics);
        let pcs = WhirPCS::new(130, requested_pow_bits, starting_log_inv_rate, 4);
        let (commit, prove, _, _) = prove_once(label, &pcs, &groups, &points);
        println!(
            "{label}_real_n10_ratio commit={:.4} prove={:.4} total={:.4} expected_pow_work_ratio={:.4}",
            commit.as_secs_f64() / baseline_commit.as_secs_f64(),
            prove.as_secs_f64() / baseline_prove.as_secs_f64(),
            (commit + prove).as_secs_f64()
                / (baseline_commit + baseline_prove).as_secs_f64(),
            if baseline_metrics.expected_pow_work_log2.is_finite() {
                (candidate_metrics.expected_pow_work_log2
                    - baseline_metrics.expected_pow_work_log2)
                    .exp2()
            } else {
                f64::INFINITY
            },
        );
    }
}

#[test]
#[ignore = "read-only candidate envelope calculation; run explicitly with --nocapture"]
fn shortlisted_candidates_all_native_profiles_fit_two_blob_compact_cap() {
    let mut worst_current = (0usize, 0usize);
    let mut worst_pow20 = (0usize, 0usize);

    for num_variables in 1..=NUM_VARIABLES {
        let (folding_factor, starting_log_inv_rate) =
            production_adaptive_folding_and_rate(num_variables);
        let current = metrics_for_n(num_variables, 130, 0, starting_log_inv_rate, folding_factor);
        let candidate = metrics_for_n(
            num_variables,
            130,
            20,
            starting_log_inv_rate,
            folding_factor,
        );
        assert!(candidate.effective_security_bits + 1e-9 >= 130.0);

        // This intentionally applies the maximum reviewed outer fixed payload
        // to every packed dimension. It is therefore conservative for smaller
        // circuits and isolates the WHIR parameter change from circuit shape.
        let current_compact = MAX_PROFILE_FIXED_COMPACT_BYTES
            .checked_add(current.proof_size.max_total_bytes)
            .unwrap();
        let candidate_compact = MAX_PROFILE_FIXED_COMPACT_BYTES
            .checked_add(candidate.proof_size.max_total_bytes)
            .unwrap();
        assert!(
            candidate_compact <= MAX_COMPACT_PROOF_BYTES_V2,
            "pow20 candidate exceeds compact cap at n={num_variables}"
        );
        if current_compact > worst_current.1 {
            worst_current = (num_variables, current_compact);
        }
        if candidate_compact > worst_pow20.1 {
            worst_pow20 = (num_variables, candidate_compact);
        }
        println!(
            "profile n={num_variables} f={folding_factor} rate=1/{} current_whir_max={} pow20_whir_max={} conservative_current_compact={} conservative_pow20_compact={} cap={}",
            1usize << starting_log_inv_rate,
            current.proof_size.max_total_bytes,
            candidate.proof_size.max_total_bytes,
            current_compact,
            candidate_compact,
            MAX_COMPACT_PROOF_BYTES_V2,
        );

        if num_variables == 10 {
            let current_small = SMALL_PROFILE_FIXED_COMPACT_BYTES
                .checked_add(current.proof_size.max_total_bytes)
                .unwrap();
            let candidate_small = SMALL_PROFILE_FIXED_COMPACT_BYTES
                .checked_add(candidate.proof_size.max_total_bytes)
                .unwrap();
            println!(
                "small_n10 current_compact_max={current_small} pow20_compact_max={candidate_small} fixed={} current_narg={} current_hint={} pow20_narg={} pow20_hint={}",
                SMALL_PROFILE_FIXED_COMPACT_BYTES,
                current.proof_size.narg_bytes,
                current.proof_size.max_hint_bytes,
                candidate.proof_size.narg_bytes,
                candidate.proof_size.max_hint_bytes,
            );
        }
    }
    println!(
        "all_profiles current_worst_n={} current_worst_compact={} pow20_worst_n={} pow20_worst_compact={} cap={}",
        worst_current.0,
        worst_current.1,
        worst_pow20.0,
        worst_pow20.1,
        MAX_COMPACT_PROOF_BYTES_V2,
    );

    for (label, requested_pow_bits, maximum_rate) in [
        ("rate16_pow22", 22, 4),
        ("rate16_pow24", 24, 4),
        ("rate32_pow0", 0, 5),
        ("rate32_pow16", 16, 5),
    ] {
        let mut worst = (0usize, 0usize, 0usize, 0usize);
        for num_variables in 1..=NUM_VARIABLES {
            let (folding_factor, starting_log_inv_rate) =
                adaptive_folding_and_rate(num_variables, maximum_rate);
            let candidate = metrics_for_n(
                num_variables,
                130,
                requested_pow_bits,
                starting_log_inv_rate,
                folding_factor,
            );
            assert!(candidate.effective_security_bits + 1e-9 >= 130.0);
            let compact = MAX_PROFILE_FIXED_COMPACT_BYTES
                .checked_add(candidate.proof_size.max_total_bytes)
                .unwrap();
            assert!(
                compact <= MAX_COMPACT_PROOF_BYTES_V2,
                "{label} exceeds compact cap at n={num_variables}"
            );
            if compact > worst.1 {
                worst = (
                    num_variables,
                    compact,
                    candidate.proof_size.narg_bytes,
                    candidate.proof_size.max_hint_bytes,
                );
            }
            if num_variables == 10 {
                println!(
                    "{label}_small_n10 compact_max={} whir_max={} narg={} hint={}",
                    SMALL_PROFILE_FIXED_COMPACT_BYTES + candidate.proof_size.max_total_bytes,
                    candidate.proof_size.max_total_bytes,
                    candidate.proof_size.narg_bytes,
                    candidate.proof_size.max_hint_bytes,
                );
            }
        }
        println!(
            "{label}_all_profiles worst_n={} conservative_compact_max={} narg={} hint={} cap={}",
            worst.0, worst.1, worst.2, worst.3, MAX_COMPACT_PROOF_BYTES_V2,
        );
    }
}

#[test]
#[ignore = "read-only target-140 envelope calculation; run explicitly with --nocapture"]
fn target140_pow20_all_native_profiles_two_blob_diagnostic() {
    let shape = CompactV2Shape {
        degree_bits: 13,
        constituent_width: 160,
        circuit_digest_len: 4,
        public_inputs_len: 103,
        num_constants: 5,
        num_routed_wires: 80,
        num_wires: 135,
        gate_round_degree: 10,
        // Keep the production shape caps here so structural validation remains
        // read-only. The ABI length helper accepts the candidate blob lengths
        // separately; the assertions below record that target140 would require
        // raising the hint cap from 180,408 to 194,552 bytes.
        max_whir_narg_bytes: MAX_WHIR_NARG_BYTES_V2,
        max_whir_hint_bytes: MAX_WHIR_HINT_BYTES_V2,
        max_encoded_bytes: MAX_COMPACT_PROOF_BYTES_V2,
    };
    let fixed_compact_bytes = shape.fixed_encoded_len().unwrap();
    // This is the largest currently admitted parent envelope
    // (close: PI=103/constants=5), which is 864 bytes wider than the sampled
    // generated resource fixture (PI=1/constants=4).
    assert_eq!(fixed_compact_bytes, MAX_ENVELOPE_FIXED_COMPACT_BYTES);

    let current_max = metrics_for_n(21, 130, 20, 4, 4);
    let candidate_max = metrics_for_n(21, 140, 20, 4, 4);
    print_metrics("target140_pow20_n21", &candidate_max, &current_max);

    let mut worst = (0usize, 0usize, 0usize, 0usize);
    for num_variables in 1..=NUM_VARIABLES {
        let (folding_factor, starting_log_inv_rate) =
            production_adaptive_folding_and_rate(num_variables);
        let candidate = metrics_for_n(
            num_variables,
            140,
            20,
            starting_log_inv_rate,
            folding_factor,
        );
        assert!(candidate.effective_security_bits + 1e-9 >= 140.0);
        let compact = fixed_compact_bytes + candidate.proof_size.max_total_bytes;
        assert!(
            compact <= MAX_COMPACT_PROOF_BYTES_V2,
            "target140/pow20 exceeds two-blob cap at n={num_variables}"
        );
        if compact > worst.1 {
            worst = (
                num_variables,
                compact,
                candidate.proof_size.narg_bytes,
                candidate.proof_size.max_hint_bytes,
            );
        }
        if num_variables == 10 {
            println!(
                "target140_pow20_small_n10 compact_max={} whir_max={} narg={} hint={}",
                SMALL_PROFILE_FIXED_COMPACT_BYTES + candidate.proof_size.max_total_bytes,
                candidate.proof_size.max_total_bytes,
                candidate.proof_size.narg_bytes,
                candidate.proof_size.max_hint_bytes,
            );
        }
    }
    println!(
        "target140_pow20_all_profiles worst_n={} compact_max={} narg={} hint={} cap={}",
        worst.0, worst.1, worst.2, worst.3, MAX_COMPACT_PROOF_BYTES_V2,
    );
    assert_eq!(worst, (21, 216_644, 2_032, 194_552));

    let abi_max = solidity_abi_mle_proof_encoded_len_v2(&shape, worst.2, worst.3).unwrap();
    println!("target140_pow20_max_solidity_abi={abi_max}");
    assert_eq!(abi_max, 279_808);
}
