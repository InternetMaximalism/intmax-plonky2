//! Cubic-extension gate sumcheck for the MLE/WHIR V2 implementation (wire v3).
//!
//! Gate constraints are evaluated directly over Goldilocks `Fp3`. This is a
//! single extension-field sumcheck; base-field repetitions are deliberately
//! not part of the current wire-v3 protocol because they admit sequential Fiat--Shamir
//! bridging across different rounds.

use anyhow::{ensure, Result};
use ark_ff::{AdditiveGroup, Field as ArkField};
use plonky2::hash::hash_types::{HashOut, RichField};
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2_field::extension::Extendable;
use whir::algebra::fields::Field64_3;

use crate::dense_mle::DenseMultilinearExtension;
use crate::gate_ext3::{
    aggregate_gate_constraints_ext3, evaluate_gate_constraints_ext3_validated,
    validate_gate_ext3_context, GateExt3Context,
};
use crate::proof_v2::GateInfoV2;
use crate::sumcheck::coefficients::{
    ext3_evaluations_to_coefficients, Ext3CoefficientRound, Ext3CoefficientSumcheckProof,
};
use crate::sumcheck::ext3::Ext3DenseMle;

fn ext3_eq_evals(tau: &[Field64_3]) -> Vec<Field64_3> {
    let mut table = vec![Field64_3::ONE; 1usize << tau.len()];
    for (coordinate, &value) in tau.iter().enumerate() {
        let one_minus = Field64_3::ONE - value;
        for (index, entry) in table.iter_mut().enumerate() {
            *entry *= if (index >> coordinate) & 1 == 0 {
                one_minus
            } else {
                value
            };
        }
    }
    table
}

/// Stateful prover interface whose challenges must be supplied by the joint
/// outer transcript. It intentionally has no standalone Fiat--Shamir API.
pub struct GateExt3ProverState<'a, F: RichField> {
    gate_context: GateExt3Context,
    public_inputs_hash: &'a HashOut<F>,
    wires: Vec<Ext3DenseMle>,
    constants: Vec<Ext3DenseMle>,
    eq: Ext3DenseMle,
    alpha: Field64_3,
    degree: usize,
    rounds: Vec<Ext3CoefficientRound>,
    point: Vec<Field64_3>,
}

impl<'a, F: RichField> GateExt3ProverState<'a, F> {
    #[allow(clippy::too_many_arguments)]
    pub fn new<const D: usize>(
        common_data: &'a CommonCircuitData<F, D>,
        gate_infos: &'a [GateInfoV2],
        wire_mles: &[DenseMultilinearExtension<F>],
        constant_mles: &[DenseMultilinearExtension<F>],
        public_inputs_hash: &'a HashOut<F>,
        alpha: Field64_3,
        tau: &[Field64_3],
        degree: usize,
    ) -> Result<Self>
    where
        F: Extendable<D>,
    {
        ensure!(
            wire_mles.len() == common_data.config.num_wires
                && constant_mles.len() == common_data.num_constants,
            "Ext3 gate MLE shape mismatch"
        );
        ensure!(
            wire_mles.iter().all(|mle| mle.num_vars == tau.len())
                && constant_mles.iter().all(|mle| mle.num_vars == tau.len()),
            "Ext3 gate MLE variable count mismatch"
        );
        ensure!(
            degree == common_data.quotient_degree_factor + 2,
            "Ext3 gate round degree is not the reviewed bound"
        );
        Ok(Self {
            gate_context: validate_gate_ext3_context(common_data, gate_infos)?,
            public_inputs_hash,
            wires: wire_mles
                .iter()
                .map(|mle| Ext3DenseMle::from_base(&mle.evaluations))
                .collect(),
            constants: constant_mles
                .iter()
                .map(|mle| Ext3DenseMle::from_base(&mle.evaluations))
                .collect(),
            eq: Ext3DenseMle::new(ext3_eq_evals(tau)),
            alpha,
            degree,
            rounds: Vec::with_capacity(tau.len()),
            point: Vec::with_capacity(tau.len()),
        })
    }

    /// Compute the next degree-exact coefficient message without exposing a
    /// challenge. The caller must commit both outer messages before binding.
    pub fn current_round(&self) -> Result<Ext3CoefficientRound> {
        ensure!(self.eq.num_vars > 0, "Ext3 gate sumcheck has no round left");
        let half = self.eq.evaluations.len() / 2;
        let mut evaluations = vec![Field64_3::ZERO; self.degree + 1];
        let mut wire_values = vec![Field64_3::ZERO; self.wires.len()];
        let mut constant_values = vec![Field64_3::ZERO; self.constants.len()];

        for suffix in 0..half {
            for (integer, sum) in evaluations.iter_mut().enumerate() {
                let x = Field64_3::from(integer as u64);
                let one_minus = Field64_3::ONE - x;
                let eq_value = one_minus * self.eq.evaluations[2 * suffix]
                    + x * self.eq.evaluations[2 * suffix + 1];
                for (column, mle) in self.wires.iter().enumerate() {
                    wire_values[column] = one_minus * mle.evaluations[2 * suffix]
                        + x * mle.evaluations[2 * suffix + 1];
                }
                for (column, mle) in self.constants.iter().enumerate() {
                    constant_values[column] = one_minus * mle.evaluations[2 * suffix]
                        + x * mle.evaluations[2 * suffix + 1];
                }
                let constraints = evaluate_gate_constraints_ext3_validated(
                    &self.gate_context,
                    &wire_values,
                    &constant_values,
                    self.public_inputs_hash,
                )?;
                *sum += eq_value * aggregate_gate_constraints_ext3(&constraints, self.alpha);
            }
        }

        let coefficients = ext3_evaluations_to_coefficients(&evaluations);
        Ok(Ext3CoefficientRound {
            non_constant: coefficients[1..].to_vec(),
        })
    }

    pub fn bind_challenge(
        &mut self,
        round: Ext3CoefficientRound,
        challenge: Field64_3,
    ) -> Result<()> {
        ensure!(
            round.non_constant.len() == self.degree,
            "Ext3 gate coefficient degree mismatch"
        );
        self.eq.bind_variable_in_place(challenge);
        for mle in &mut self.wires {
            mle.bind_variable_in_place(challenge);
        }
        for mle in &mut self.constants {
            mle.bind_variable_in_place(challenge);
        }
        self.rounds.push(round);
        self.point.push(challenge);
        Ok(())
    }

    pub fn into_proof_and_point(self) -> Result<(Ext3CoefficientSumcheckProof, Vec<Field64_3>)> {
        ensure!(self.eq.num_vars == 0, "Ext3 gate sumcheck is incomplete");
        Ok((
            Ext3CoefficientSumcheckProof {
                rounds: self.rounds,
            },
            self.point,
        ))
    }
}

pub fn ext3_eq_eval(tau: &[Field64_3], point: &[Field64_3]) -> Result<Field64_3> {
    ensure!(tau.len() == point.len(), "Ext3 eq point length mismatch");
    Ok(tau
        .iter()
        .zip(point)
        .map(|(&t, &r)| t * r + (Field64_3::ONE - t) * (Field64_3::ONE - r))
        .product())
}
