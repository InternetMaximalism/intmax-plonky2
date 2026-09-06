//! Cubic-extension sumcheck primitives for the security-amplified outer proof.
//!
//! This module intentionally uses WHIR's canonical `Field64_3` type.  The
//! committed polynomials still have Goldilocks coefficients, while sumcheck
//! messages and random points live in the degree-three extension.

use ark_ff::{AdditiveGroup, Field as ArkField, PrimeField as ArkPrimeField};
use plonky2_field::types::PrimeField64;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::transcript::Transcript;

/// Dense multilinear extension whose Boolean table has been embedded in
/// `Field64_3` and which may subsequently be partially bound at Ext3 points.
#[derive(Clone, Debug)]
pub struct Ext3DenseMle {
    pub num_vars: usize,
    pub evaluations: Vec<Field64_3>,
}

impl Ext3DenseMle {
    pub fn new(evaluations: Vec<Field64_3>) -> Self {
        assert!(
            !evaluations.is_empty() && evaluations.len().is_power_of_two(),
            "Ext3 MLE table length must be a non-zero power of two"
        );
        Self {
            num_vars: evaluations.len().trailing_zeros() as usize,
            evaluations,
        }
    }

    pub fn from_base<F: PrimeField64>(evaluations: &[F]) -> Self {
        assert_eq!(
            F::ORDER,
            0xFFFF_FFFF_0000_0001,
            "Ext3 MLE embedding is defined only over Goldilocks"
        );
        Self::new(
            evaluations
                .iter()
                .map(|value| Field64_3::from(value.to_canonical_u64()))
                .collect(),
        )
    }

    pub fn bind_variable_in_place(&mut self, value: Field64_3) {
        assert!(self.num_vars > 0, "cannot bind a constant Ext3 MLE");
        let half = self.evaluations.len() / 2;
        let one_minus = Field64_3::ONE - value;
        for i in 0..half {
            self.evaluations[i] =
                one_minus * self.evaluations[2 * i] + value * self.evaluations[2 * i + 1];
        }
        self.evaluations.truncate(half);
        self.num_vars -= 1;
    }

    pub fn evaluate(&self, point: &[Field64_3]) -> Field64_3 {
        assert_eq!(point.len(), self.num_vars, "Ext3 MLE point length mismatch");
        let mut work = self.clone();
        for &coordinate in point {
            work.bind_variable_in_place(coordinate);
        }
        work.evaluations[0]
    }
}

/// A univariate round polynomial represented at integer nodes
/// `0, 1, ..., degree`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext3RoundPolynomial {
    pub evaluations: Vec<Field64_3>,
}

impl Ext3RoundPolynomial {
    pub fn evaluate(&self, point: Field64_3) -> Field64_3 {
        interpolate_integer_nodes(&self.evaluations, point)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext3SumcheckProof {
    pub round_polys: Vec<Ext3RoundPolynomial>,
}

/// Evaluate from consecutive integer samples with Newton forward
/// interpolation.  This uses only fixed small-scalar inverses and avoids one
/// variable-field inversion per interpolation term, matching the intended
/// Solidity implementation.
fn interpolate_integer_nodes(evals: &[Field64_3], point: Field64_3) -> Field64_3 {
    assert!(!evals.is_empty(), "round polynomial has no evaluations");
    let mut differences = evals.to_vec();
    let mut result = Field64_3::ZERO;
    let mut falling = Field64_3::ONE;
    let mut factorial = ArkGoldilocks::ONE;

    for order in 0..evals.len() {
        let inv_factorial = factorial
            .inverse()
            .expect("small factorial is non-zero in Goldilocks");
        result += differences[0] * Field64_3::from(inv_factorial.into_bigint().0[0]) * falling;

        for i in 0..(differences.len() - 1) {
            differences[i] = differences[i + 1] - differences[i];
        }
        differences.pop();

        if order + 1 < evals.len() {
            falling *= point - Field64_3::from(order as u64);
            factorial *= ArkGoldilocks::from((order + 1) as u64);
        }
    }
    result
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ext3SumcheckVerifyError {
    WrongNumberOfRounds {
        expected: usize,
        got: usize,
    },
    WrongRoundDegree {
        round: usize,
        expected_evaluations: usize,
        got: usize,
    },
    RoundCheckFailed {
        round: usize,
    },
}

impl core::fmt::Display for Ext3SumcheckVerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WrongNumberOfRounds { expected, got } => {
                write!(f, "expected {expected} Ext3 sumcheck rounds, got {got}")
            }
            Self::WrongRoundDegree {
                round,
                expected_evaluations,
                got,
            } => write!(
                f,
                "Ext3 sumcheck round {round}: expected {expected_evaluations} evaluations, got {got}"
            ),
            Self::RoundCheckFailed { round } => {
                write!(f, "Ext3 sumcheck round {round}: g(0) + g(1) != claim")
            }
        }
    }
}

/// Verify the algebraic consistency of a fixed-degree Ext3 sumcheck.
///
/// The terminal equation remains the caller's responsibility.
pub fn verify_ext3_sumcheck<F: PrimeField64>(
    proof: &Ext3SumcheckProof,
    claimed_sum: Field64_3,
    num_vars: usize,
    max_degree: usize,
    transcript: &mut Transcript,
) -> Result<(Vec<Field64_3>, Field64_3), Ext3SumcheckVerifyError> {
    if proof.round_polys.len() != num_vars {
        return Err(Ext3SumcheckVerifyError::WrongNumberOfRounds {
            expected: num_vars,
            got: proof.round_polys.len(),
        });
    }

    let expected_evaluations = max_degree + 1;
    let mut claim = claimed_sum;
    let mut challenges = Vec::with_capacity(num_vars);
    for (round, round_poly) in proof.round_polys.iter().enumerate() {
        if round_poly.evaluations.len() != expected_evaluations {
            return Err(Ext3SumcheckVerifyError::WrongRoundDegree {
                round,
                expected_evaluations,
                got: round_poly.evaluations.len(),
            });
        }
        if round_poly.evaluations[0] + round_poly.evaluations[1] != claim {
            return Err(Ext3SumcheckVerifyError::RoundCheckFailed { round });
        }

        transcript.domain_separate("sumcheck-round-ext3-v3");
        transcript.absorb_ext3_vec(&round_poly.evaluations);
        let challenge = transcript.squeeze_ext3::<F>();
        claim = round_poly.evaluate(challenge);
        challenges.push(challenge);
    }
    Ok((challenges, claim))
}

#[cfg(test)]
mod tests {
    use ark_ff::{AdditiveGroup, Field as ArkField};
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::Field as PlonkyField;

    use super::*;

    type F = GoldilocksField;

    #[test]
    fn newton_interpolation_matches_degree_five_polynomial() {
        let x = Field64_3::new(
            ArkGoldilocks::from(7u64),
            ArkGoldilocks::from(11u64),
            ArkGoldilocks::from(13u64),
        );
        let polynomial = |z: Field64_3| {
            z.pow([5])
                + z.square() * Field64_3::from(9u64)
                + z * Field64_3::from(4u64)
                + Field64_3::from(17u64)
        };
        let evals = (0..=5)
            .map(|i| polynomial(Field64_3::from(i as u64)))
            .collect::<Vec<_>>();
        assert_eq!(interpolate_integer_nodes(&evals, x), polynomial(x));
    }

    #[test]
    fn verifier_roundtrip_and_tamper_rejection() {
        let mut prover_transcript = Transcript::new();
        prover_transcript.domain_separate("ext3-sumcheck-test");

        // Two-round proof for the constant-zero polynomial.  Six samples pin
        // the production degree-five shape.
        let zero_round = Ext3RoundPolynomial {
            evaluations: vec![Field64_3::ZERO; 6],
        };
        let proof = Ext3SumcheckProof {
            round_polys: vec![zero_round.clone(), zero_round],
        };
        let (point, final_eval) =
            verify_ext3_sumcheck::<F>(&proof, Field64_3::ZERO, 2, 5, &mut prover_transcript)
                .unwrap();
        assert_eq!(point.len(), 2);
        assert_eq!(final_eval, Field64_3::ZERO);

        let mut bad = proof;
        bad.round_polys[0].evaluations[0] += Field64_3::ONE;
        let mut verifier_transcript = Transcript::new();
        verifier_transcript.domain_separate("ext3-sumcheck-test");
        assert!(
            verify_ext3_sumcheck::<F>(&bad, Field64_3::ZERO, 2, 5, &mut verifier_transcript,)
                .is_err()
        );
    }

    #[test]
    fn ext3_mle_embedding_and_binding_agree() {
        let base = [
            F::from_canonical_u64(1),
            F::from_canonical_u64(2),
            F::from_canonical_u64(3),
            F::from_canonical_u64(4),
        ];
        let point = [Field64_3::from(5u64), Field64_3::from(9u64)];
        let mle = Ext3DenseMle::from_base(&base);
        let direct = mle.evaluate(&point);
        let mut folded = mle;
        folded.bind_variable_in_place(point[0]);
        folded.bind_variable_in_place(point[1]);
        assert_eq!(direct, folded.evaluations[0]);
    }
}
