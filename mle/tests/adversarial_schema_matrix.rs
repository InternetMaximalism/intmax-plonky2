//! Differential adversarial coverage for the packed-v1 statement and its
//! strict fixture encoding. These tests intentionally use only public APIs so
//! they exercise the same boundary available to downstream consumers.

use std::panic::{catch_unwind, AssertUnwindSafe};

use plonky2_mle::commitment::whir_pcs::{WhirPCS, WHIR_SESSION_SPLIT};
use plonky2_mle::fixture::try_fixture_from_json;
use serde_json::{json, Value};
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

const NUM_GROUPS: usize = 4;
const NUM_POINTS: usize = 4;

fn assert_fixture_rejected(value: &Value, label: &str) {
    assert!(
        try_fixture_from_json(&value.to_string()).is_err(),
        "strict fixture decoder accepted {label}"
    );
}

#[test]
fn grouped_statement_rejects_reorder_reuse_mixing_and_malformed_bytes() {
    let num_vars = 4;
    let size = 1usize << num_vars;
    let vectors_per_group = 2;
    let pcs = WhirPCS::for_constituents(num_vars, vectors_per_group);
    let groups: Vec<Vec<Vec<ArkGoldilocks>>> = (0..NUM_GROUPS)
        .map(|group| {
            (0..vectors_per_group)
                .map(|vector| {
                    (0..size)
                        .map(|row| {
                            ArkGoldilocks::from((1 + row + 17 * vector + 101 * group) as u64)
                        })
                        .collect()
                })
                .collect()
        })
        .collect();
    let commit_data = pcs.commit_grouped(&groups, WHIR_SESSION_SPLIT);
    let roots = commit_data.roots.clone();
    let points: Vec<Vec<Field64_3>> = (0..NUM_POINTS)
        .map(|point| {
            (0..num_vars)
                .map(|coordinate| Field64_3::from((2 + 11 * point + 3 * coordinate) as u64))
                .collect()
        })
        .collect();
    let point_refs: Vec<&[Field64_3]> = points.iter().map(Vec::as_slice).collect();
    let (proof, per_point) = pcs.prove_grouped_with_eval(commit_data, &point_refs);
    let expected: Vec<Option<Field64_3>> = per_point.into_iter().flatten().map(Some).collect();
    let root_refs: Vec<&[u8]> = roots.iter().map(Vec::as_slice).collect();

    pcs.verify_grouped(
        num_vars,
        &proof,
        &expected,
        WHIR_SESSION_SPLIT,
        &point_refs,
        NUM_GROUPS,
        &root_refs,
    )
    .expect("honest grouped statement");

    // Every root-order transposition and every cross-group root reuse.
    for left in 0..NUM_GROUPS {
        for right in (left + 1)..NUM_GROUPS {
            let mut changed = roots.clone();
            changed.swap(left, right);
            let refs: Vec<&[u8]> = changed.iter().map(Vec::as_slice).collect();
            assert!(
                pcs.verify_grouped(
                    num_vars,
                    &proof,
                    &expected,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_GROUPS,
                    &refs,
                )
                .is_err(),
                "root transposition {left}<->{right} was accepted"
            );
        }
        for source in 0..NUM_GROUPS {
            if source == left {
                continue;
            }
            let mut changed = roots.clone();
            changed[left] = roots[source].clone();
            let refs: Vec<&[u8]> = changed.iter().map(Vec::as_slice).collect();
            assert!(
                pcs.verify_grouped(
                    num_vars,
                    &proof,
                    &expected,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_GROUPS,
                    &refs,
                )
                .is_err(),
                "root {source} was reused as group {left}"
            );
        }
    }

    // Mix each commitment slot with a root produced by an independently
    // committed statement. This models stale/new proof-VK root mixing, not
    // merely a random bit flip.
    let alternate_groups: Vec<Vec<Vec<ArkGoldilocks>>> = groups
        .iter()
        .enumerate()
        .map(|(group, vectors)| {
            vectors
                .iter()
                .enumerate()
                .map(|(vector, values)| {
                    values
                        .iter()
                        .enumerate()
                        .map(|(row, _)| {
                            ArkGoldilocks::from((10_001 + row + 29 * vector + 307 * group) as u64)
                        })
                        .collect()
                })
                .collect()
        })
        .collect();
    let alternate_roots = pcs
        .commit_grouped(&alternate_groups, WHIR_SESSION_SPLIT)
        .roots;
    for group in 0..NUM_GROUPS {
        assert_ne!(alternate_roots[group], roots[group]);
        let mut mixed = roots.clone();
        mixed[group] = alternate_roots[group].clone();
        let refs: Vec<&[u8]> = mixed.iter().map(Vec::as_slice).collect();
        assert!(
            pcs.verify_grouped(
                num_vars,
                &proof,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                NUM_GROUPS,
                &refs,
            )
            .is_err(),
            "independent root was mixed into group {group}"
        );
    }

    // Explicit vector reorder, duplicate and cross-group reuse in every
    // point/group cell. Shape is unchanged, so these cannot pass by aliasing
    // vector labels or by exploiting a consumer-side truncation.
    let cell_width = vectors_per_group;
    for point in 0..NUM_POINTS {
        for group in 0..NUM_GROUPS {
            let base = (point * NUM_GROUPS + group) * cell_width;
            assert_ne!(expected[base], expected[base + 1]);

            let mut reordered = expected.clone();
            reordered.swap(base, base + 1);
            assert!(
                pcs.verify_grouped(
                    num_vars,
                    &proof,
                    &reordered,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_GROUPS,
                    &root_refs,
                )
                .is_err(),
                "vector reorder at point {point}, group {group} was accepted"
            );

            let mut duplicated = expected.clone();
            duplicated[base + 1] = duplicated[base];
            assert!(
                pcs.verify_grouped(
                    num_vars,
                    &proof,
                    &duplicated,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_GROUPS,
                    &root_refs,
                )
                .is_err(),
                "vector duplicate at point {point}, group {group} was accepted"
            );

            let source_group = (group + 1) % NUM_GROUPS;
            let source_base = (point * NUM_GROUPS + source_group) * cell_width;
            let mut reused = expected.clone();
            reused[base..base + cell_width]
                .clone_from_slice(&expected[source_base..source_base + cell_width]);
            assert!(
                pcs.verify_grouped(
                    num_vars,
                    &proof,
                    &reused,
                    WHIR_SESSION_SPLIT,
                    &point_refs,
                    NUM_GROUPS,
                    &root_refs,
                )
                .is_err(),
                "claims from group {source_group} were reused as group {group}"
            );
        }
    }

    // Exact list shapes: omission, truncation and extension are all rejected.
    assert!(pcs
        .verify_grouped(
            num_vars,
            &proof,
            &expected[..expected.len() - 1],
            WHIR_SESSION_SPLIT,
            &point_refs,
            NUM_GROUPS,
            &root_refs,
        )
        .is_err());
    let mut extended_expected = expected.clone();
    extended_expected.push(expected[0]);
    assert!(pcs
        .verify_grouped(
            num_vars,
            &proof,
            &extended_expected,
            WHIR_SESSION_SPLIT,
            &point_refs,
            NUM_GROUPS,
            &root_refs,
        )
        .is_err());
    assert!(pcs
        .verify_grouped(
            num_vars,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT,
            &point_refs[..NUM_POINTS - 1],
            NUM_GROUPS,
            &root_refs,
        )
        .is_err());
    let mut extended_points = points.clone();
    extended_points.push(points[0].clone());
    let extended_point_refs: Vec<&[Field64_3]> =
        extended_points.iter().map(Vec::as_slice).collect();
    assert!(pcs
        .verify_grouped(
            num_vars,
            &proof,
            &expected,
            WHIR_SESSION_SPLIT,
            &extended_point_refs,
            NUM_GROUPS,
            &root_refs,
        )
        .is_err());

    // Every non-identity point transposition is bound, not only point 0/1.
    for left in 0..NUM_POINTS {
        for right in (left + 1)..NUM_POINTS {
            let mut changed = points.clone();
            changed.swap(left, right);
            let refs: Vec<&[Field64_3]> = changed.iter().map(Vec::as_slice).collect();
            assert!(
                pcs.verify_grouped(
                    num_vars,
                    &proof,
                    &expected,
                    WHIR_SESSION_SPLIT,
                    &refs,
                    NUM_GROUPS,
                    &root_refs,
                )
                .is_err(),
                "query-point transposition {left}<->{right} was accepted"
            );
        }
    }

    assert!(
        pcs.verify_grouped(
            num_vars,
            &proof,
            &expected,
            "plonky2-mle-whir-split-v0",
            &point_refs,
            NUM_GROUPS,
            &root_refs,
        )
        .is_err(),
        "old/new WHIR session mixing was accepted"
    );

    // Malformed proof encodings must return Err and never unwind the host.
    let malformed = [
        {
            let mut changed = proof.clone();
            changed.narg_string.pop();
            changed
        },
        {
            let mut changed = proof.clone();
            changed.narg_string.push(0);
            changed
        },
        {
            let mut changed = proof.clone();
            changed.hints.pop();
            changed
        },
        {
            let mut changed = proof.clone();
            changed.hints.push(0);
            changed
        },
    ];
    for (index, changed) in malformed.iter().enumerate() {
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            pcs.verify_grouped(
                num_vars,
                changed,
                &expected,
                WHIR_SESSION_SPLIT,
                &point_refs,
                NUM_GROUPS,
                &root_refs,
            )
        }));
        assert!(outcome.is_ok(), "malformed proof {index} unwound verifier");
        assert!(
            outcome.unwrap().is_err(),
            "malformed proof {index} verified"
        );
    }
}

#[test]
fn strict_fixture_rejects_old_schema_malformed_and_noncanonical_encodings() {
    const FIXTURE: &str = include_str!("../contracts/test/fixtures/small_mul.json");
    try_fixture_from_json(FIXTURE).expect("canonical packed-v1 fixture");
    let canonical: Value = serde_json::from_str(FIXTURE).unwrap();

    let mut old_version = canonical.clone();
    old_version["protocolVersion"] = json!(0);
    assert_fixture_rejected(&old_version, "old proof version");

    let mut wrong_width = canonical.clone();
    wrong_width["constituentWidth"] = json!(159);
    assert_fixture_rejected(&wrong_width, "wrong packed constituent width");

    let mut missing_required = canonical.clone();
    missing_required
        .as_object_mut()
        .unwrap()
        .remove("inverseHelpersCommitmentRoot");
    assert_fixture_rejected(&missing_required, "omitted required field");

    let mut old_field = canonical.clone();
    old_field["lambdaH"] = json!("1");
    assert_fixture_rejected(&old_field, "removed v0 field");

    let mut wrong_type = canonical.clone();
    wrong_type["alpha"] = json!(1);
    assert_fixture_rejected(
        &wrong_type,
        "numeric field in place of canonical decimal string",
    );

    let mut noncanonical_scalar = canonical.clone();
    noncanonical_scalar["alpha"] = json!("18446744069414584321");
    assert_fixture_rejected(&noncanonical_scalar, "Goldilocks modulus scalar");

    let mut noncanonical_array = canonical.clone();
    noncanonical_array["witnessIndividualEvals"][0] = json!("18446744069414584321");
    assert_fixture_rejected(&noncanonical_array, "Goldilocks modulus array entry");

    let mut decimal_alias = canonical.clone();
    let alpha = decimal_alias["alpha"].as_str().unwrap().to_string();
    decimal_alias["alpha"] = json!(format!("0{alpha}"));
    assert_fixture_rejected(&decimal_alias, "leading-zero decimal alias");

    let mut short_root = canonical.clone();
    short_root["witnessCommitmentRoot"] = json!("0x00");
    assert_fixture_rejected(&short_root, "short root");

    let mut uppercase_root = canonical.clone();
    uppercase_root["witnessCommitmentRoot"] = json!(canonical["witnessCommitmentRoot"]
        .as_str()
        .unwrap()
        .to_uppercase());
    assert_fixture_rejected(&uppercase_root, "noncanonical uppercase root encoding");

    let mut wrong_protocol_id = canonical.clone();
    wrong_protocol_id["whirProtocolId"] = json!(format!("0x{}", "00".repeat(64)));
    assert_fixture_rejected(&wrong_protocol_id, "old/mismatched WHIR protocol ID");

    let mut wrong_session_id = canonical.clone();
    wrong_session_id["whirSplitSessionId"] = json!(format!("0x{}", "00".repeat(32)));
    assert_fixture_rejected(&wrong_session_id, "old/mismatched WHIR session ID");

    for field in [
        "preprocessedIndividualEvals",
        "witnessIndividualEvals",
        "preprocessedIndividualEvalsAtRInv",
        "witnessIndividualEvalsAtRInv",
        "inverseHelpersEvalsAtRInv",
        "inverseHelpersEvalsAtRH",
        "preprocessedIndividualEvalsAtRGateV2",
        "witnessIndividualEvalsAtRGateV2",
    ] {
        let mut truncated = canonical.clone();
        truncated[field].as_array_mut().unwrap().pop();
        assert_fixture_rejected(&truncated, &format!("truncated {field}"));

        let mut extended = canonical.clone();
        extended[field].as_array_mut().unwrap().push(json!("0"));
        assert_fixture_rejected(&extended, &format!("extended {field}"));
    }

    for field in ["circuitDigest", "evaluationPoint", "publicInputsHash"] {
        let mut truncated = canonical.clone();
        truncated[field].as_array_mut().unwrap().pop();
        assert_fixture_rejected(&truncated, &format!("truncated {field}"));

        let mut extended = canonical.clone();
        let first = extended[field][0].clone();
        extended[field].as_array_mut().unwrap().push(first);
        assert_fixture_rejected(&extended, &format!("extended {field}"));
    }

    let mut extra_round = canonical.clone();
    let round = extra_round["combinedProof"]["roundPolys"][0].clone();
    extra_round["combinedProof"]["roundPolys"]
        .as_array_mut()
        .unwrap()
        .push(round);
    assert_fixture_rejected(&extra_round, "extra sumcheck round");

    let mut extra_coefficient = canonical.clone();
    extra_coefficient["gateSumcheckProof"]["roundPolys"][0]
        .as_array_mut()
        .unwrap()
        .push(json!("0"));
    assert_fixture_rejected(&extra_coefficient, "extra sumcheck coefficient");

    let mut non_base_row_point = canonical;
    non_base_row_point["evaluationPoint"][0]["c1"] = json!("1");
    assert_fixture_rejected(&non_base_row_point, "non-base-field row point");
}
