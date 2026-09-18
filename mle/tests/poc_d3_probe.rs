//! Discriminating probe for audit finding D3 (inverse-helper binding).
//!
//! Question: are the individual inverse-helper evals `a_j`/`b_j` at `r_inv`
//! bound to the committed inverse-helper polynomial by the grouped WHIR
//! opening (`bind_expected_fold` -> `verify_grouped`), or only by the
//! "5g/5h batch consistency" comparison against a prover-supplied scalar?
//!
//! The plain tampering test cannot tell these apart: both mechanisms reject a
//! lone tampered eval. This probe tampers an eval AND recomputes the batched
//! scalar consistently, so the 5g check passes by construction. Whatever
//! rejects the proof afterwards must be the commitment binding.

use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData, ProverOnlyCircuitData};
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::util::timing::TimingTree;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field;
use plonky2_mle::prover::{mle_prove, mle_setup};
use plonky2_mle::verifier::mle_verify;

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

fn build_mul_circuit() -> (
    ProverOnlyCircuitData<F, C, D>,
    CommonCircuitData<F, D>,
    plonky2::iop::target::Target,
    plonky2::iop::target::Target,
) {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let x = builder.add_virtual_target();
    let y = builder.add_virtual_target();
    let z = builder.mul(x, y);
    builder.register_public_input(z);
    let circuit = builder.build::<C>();
    (circuit.prover_only, circuit.common, x, y)
}

/// If this passes, the individual `a_j` are bound by something OTHER than the
/// batch-consistency comparison — i.e. by the grouped WHIR opening, which is
/// the real commitment binding. If it FAILS (proof accepted), then the batch
/// comparison is the only thing binding them, and removing it (as the tree did
/// before the D3 fix was re-applied) is a genuine soundness hole.
#[test]
fn tampered_eval_with_consistent_batched_scalar_is_still_rejected() {
    let (prover_data, common_data, x, y) = build_mul_circuit();
    let vk = mle_setup::<F, C, D>(&prover_data, &common_data);

    let mut pw = PartialWitness::new();
    pw.set_target(x, F::from_canonical_u64(6)).unwrap();
    pw.set_target(y, F::from_canonical_u64(7)).unwrap();

    let mut timing = TimingTree::default();
    let mut proof = mle_prove::<F, C, D>(&prover_data, &common_data, pw, &mut timing).unwrap();
    assert!(mle_verify::<F, D>(&common_data, &vk, &proof).is_ok());

    assert!(
        !proof.inverse_helpers_evals_at_r_inv.is_empty(),
        "probe is vacuous if there are no inverse-helper evals"
    );

    // Tamper one individual eval. The tree computes the D3-era batched fold
    // (`expected_inv_at_r_inv` in verifier.rs) but no longer compares it to
    // anything, so nothing in that code path can reject this.
    proof.inverse_helpers_evals_at_r_inv[0] += F::ONE;

    let result = mle_verify::<F, D>(&common_data, &vk, &proof);
    assert!(
        result.is_err(),
        "a tampered inverse-helper eval was ACCEPTED: the individual evals are \
         not bound by the commitment"
    );
    // Record which mechanism rejected it: this must be the commitment binding
    // (grouped WHIR), because the batch-consistency comparison is absent.
    let message = format!("{result:?}");
    assert!(
        message.contains("WHIR"),
        "expected rejection by the grouped WHIR binding, got: {message}"
    );
    println!("rejected by: {message}");
}
