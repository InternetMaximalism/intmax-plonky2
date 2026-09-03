use plonky2_mle::commitment::whir_pcs::{WhirPCS, WHIR_SESSION_SPLIT};
use whir::algebra::fields::{Field64, Field64_3};

fn main() {
    let num_vars = 4;
    let size = 1usize << num_vars;
    let pcs = WhirPCS::for_constituents(num_vars, 1);
    let groups = vec![vec![vec![Field64::from(0_u64); size]]; 4];
    let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
    let roots = data.roots.clone();
    let point = vec![Field64_3::from(2_u64); num_vars];
    let point_refs = [point.as_slice()];
    let (proof, per_point) = pcs.prove_grouped_with_eval(data, &point_refs);
    let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
    let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

    let error = pcs
        .verify_grouped(
            num_vars,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            4,
            &root_refs,
        )
        .expect_err("zero grouped proof was accepted");
    assert_eq!(
        error, "WHIR final folded polynomial evaluates to zero",
        "zero-divisor proof reached the upstream verifier"
    );

    let groups: Vec<Vec<Vec<Field64>>> = (0..4)
        .map(|group| {
            vec![(0..size)
                .map(|row| Field64::from((1 + row + 101 * group) as u64))
                .collect()]
        })
        .collect();
    let data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
    let roots = data.roots.clone();
    let (proof, per_point) = pcs.prove_grouped_with_eval(data, &point_refs);
    let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
    let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();
    pcs.verify_grouped(
        num_vars,
        &proof,
        &expected,
        WHIR_SESSION_SPLIT,
        &point_refs,
        4,
        &root_refs,
    )
    .expect("honest non-zero grouped proof");

    let mut oversized_hint = proof.clone();
    oversized_hint.hints[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    let error = pcs
        .verify_grouped(
            num_vars,
            &oversized_hint,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            4,
            &root_refs,
        )
        .expect_err("oversized hint Vec prefix was accepted");
    assert!(error.contains("hint vector length mismatch"));

    let mut noncanonical_hint = proof.clone();
    noncanonical_hint.hints[8..16].copy_from_slice(&0xffff_ffff_0000_0001_u64.to_le_bytes());
    let error = pcs
        .verify_grouped(
            num_vars,
            &noncanonical_hint,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            4,
            &root_refs,
        )
        .expect_err("non-canonical base-field hint was accepted");
    assert!(error.contains("non-canonical Goldilocks limb"));

    let mut truncated_hint = proof.clone();
    truncated_hint.hints.truncate(7);
    let error = pcs
        .verify_grouped(
            num_vars,
            &truncated_hint,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            4,
            &root_refs,
        )
        .expect_err("truncated hint prefix was accepted");
    assert!(error.contains("hint is truncated"));

    let mut trailing_hint = proof;
    trailing_hint.hints.push(0);
    let error = pcs
        .verify_grouped(
            num_vars,
            &trailing_hint,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            4,
            &root_refs,
        )
        .expect_err("trailing hint byte was accepted");
    assert!(error.contains("trailing hint bytes"));

    // Exercise the same EOF guard after at least one WHIR folding round. The
    // small case above has no `round_configs`, so it cannot by itself prove
    // that abort-mode preflight traverses the complete production hint grammar.
    let deep_num_vars = 10;
    let deep_size = 1usize << deep_num_vars;
    let deep_pcs = WhirPCS::for_constituents(deep_num_vars, 1);
    assert!(
        !deep_pcs
            .constituent_config(deep_size)
            .round_configs
            .is_empty(),
        "deep abort regression must include a WHIR folding round"
    );
    let deep_groups: Vec<Vec<Vec<Field64>>> = (0..4)
        .map(|group| {
            vec![(0..deep_size)
                .map(|row| Field64::from((1 + row + 101 * group) as u64))
                .collect()]
        })
        .collect();
    let deep_data = deep_pcs.commit_grouped(&deep_groups, WHIR_SESSION_SPLIT);
    let deep_roots = deep_data.roots.clone();
    let deep_point = vec![Field64_3::from(2_u64); deep_num_vars];
    let deep_point_refs = [deep_point.as_slice()];
    let (deep_proof, deep_per_point) =
        deep_pcs.prove_grouped_with_eval(deep_data, &deep_point_refs);
    let deep_expected: Vec<Option<Field64_3>> =
        deep_per_point.into_iter().flatten().map(Some).collect();
    let deep_root_refs: Vec<&[u8]> = deep_roots.iter().map(Vec::as_slice).collect();
    deep_pcs
        .verify_grouped(
            deep_num_vars,
            &deep_proof,
            &deep_expected,
            WHIR_SESSION_SPLIT,
            &deep_point_refs,
            4,
            &deep_root_refs,
        )
        .expect("honest multi-round grouped proof");

    let mut deep_truncated_hint = deep_proof.clone();
    deep_truncated_hint.hints.pop();
    let error = deep_pcs
        .verify_grouped(
            deep_num_vars,
            &deep_truncated_hint,
            &deep_expected,
            WHIR_SESSION_SPLIT,
            &deep_point_refs,
            4,
            &deep_root_refs,
        )
        .expect_err("truncated multi-round hint was accepted");
    assert!(error.contains("hint is truncated"));

    let mut deep_trailing_hint = deep_proof;
    deep_trailing_hint.hints.push(0);
    let error = deep_pcs
        .verify_grouped(
            deep_num_vars,
            &deep_trailing_hint,
            &deep_expected,
            WHIR_SESSION_SPLIT,
            &deep_point_refs,
            4,
            &deep_root_refs,
        )
        .expect_err("trailing multi-round hint byte was accepted");
    assert!(error.contains("trailing hint bytes"));
}
