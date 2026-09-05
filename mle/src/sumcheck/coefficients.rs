//! V2 sumcheck encoding using non-constant monomial coefficients.
//!
//! For `g(X)=a_0+...+a_d X^d`, the verifier already knows
//! `g(0)+g(1)=claim`, hence
//! `a_0=(claim-sum_{k=1}^d a_k)/2`. Sending only `a_1..a_d` saves one field
//! element per round and permits inversion-free Horner evaluation on-chain.

use ark_ff::{AdditiveGroup, Field as ArkField};
use plonky2_field::types::{Field, PrimeField64};
use whir::algebra::fields::Field64_3;

use crate::transcript_v2::TranscriptV2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoefficientRound<F: Field> {
    pub non_constant: Vec<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoefficientSumcheckProof<F: Field> {
    pub rounds: Vec<CoefficientRound<F>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext3CoefficientRound {
    pub non_constant: Vec<Field64_3>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ext3CoefficientSumcheckProof {
    pub rounds: Vec<Ext3CoefficientRound>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoefficientSumcheckError {
    WrongNumberOfRounds {
        expected: usize,
        got: usize,
    },
    WrongDegree {
        round: usize,
        expected: usize,
        got: usize,
    },
}

impl core::fmt::Display for CoefficientSumcheckError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WrongNumberOfRounds { expected, got } => {
                write!(f, "expected {expected} coefficient rounds, got {got}")
            }
            Self::WrongDegree {
                round,
                expected,
                got,
            } => write!(
                f,
                "coefficient round {round}: expected degree {expected}, got {got}"
            ),
        }
    }
}

/// Recover `a_0` from the sumcheck relation and evaluate at `point`.
pub fn evaluate_base_coefficient_round<F: Field>(claim: F, non_constant: &[F], point: F) -> F {
    let non_constant_at_one: F = non_constant.iter().copied().sum();
    let a0 = (claim - non_constant_at_one) * F::TWO.inverse();
    non_constant
        .iter()
        .rev()
        .fold(F::ZERO, |acc, coefficient| acc * point + *coefficient)
        * point
        + a0
}

pub fn evaluate_ext3_coefficient_round(
    claim: Field64_3,
    non_constant: &[Field64_3],
    point: Field64_3,
) -> Field64_3 {
    let non_constant_at_one: Field64_3 = non_constant.iter().copied().sum();
    let half = Field64_3::from(2u64)
        .inverse()
        .expect("two is invertible in Goldilocks Ext3");
    let a0 = (claim - non_constant_at_one) * half;
    non_constant
        .iter()
        .rev()
        .fold(Field64_3::ZERO, |acc, coefficient| {
            acc * point + coefficient
        })
        * point
        + a0
}

pub fn verify_coefficient_sumcheck<F: Field + PrimeField64>(
    proof: &CoefficientSumcheckProof<F>,
    claimed_sum: F,
    num_vars: usize,
    degree: usize,
    transcript: &mut TranscriptV2,
) -> Result<(Vec<F>, F), CoefficientSumcheckError> {
    if proof.rounds.len() != num_vars {
        return Err(CoefficientSumcheckError::WrongNumberOfRounds {
            expected: num_vars,
            got: proof.rounds.len(),
        });
    }
    let mut claim = claimed_sum;
    let mut point = Vec::with_capacity(num_vars);
    for (round_index, round) in proof.rounds.iter().enumerate() {
        if round.non_constant.len() != degree {
            return Err(CoefficientSumcheckError::WrongDegree {
                round: round_index,
                expected: degree,
                got: round.non_constant.len(),
            });
        }
        transcript.domain_separate("sumcheck-round-coeff-v3");
        transcript.absorb_field_vec(&round.non_constant);
        let challenge = transcript.squeeze_challenge::<F>();
        claim = evaluate_base_coefficient_round(claim, &round.non_constant, challenge);
        point.push(challenge);
    }
    Ok((point, claim))
}

pub fn verify_ext3_coefficient_sumcheck<F: PrimeField64>(
    proof: &Ext3CoefficientSumcheckProof,
    claimed_sum: Field64_3,
    num_vars: usize,
    degree: usize,
    transcript: &mut TranscriptV2,
) -> Result<(Vec<Field64_3>, Field64_3), CoefficientSumcheckError> {
    if proof.rounds.len() != num_vars {
        return Err(CoefficientSumcheckError::WrongNumberOfRounds {
            expected: num_vars,
            got: proof.rounds.len(),
        });
    }
    let mut claim = claimed_sum;
    let mut point = Vec::with_capacity(num_vars);
    for (round_index, round) in proof.rounds.iter().enumerate() {
        if round.non_constant.len() != degree {
            return Err(CoefficientSumcheckError::WrongDegree {
                round: round_index,
                expected: degree,
                got: round.non_constant.len(),
            });
        }
        transcript.domain_separate("sumcheck-round-coeff-ext3-v3");
        transcript.absorb_ext3_vec(&round.non_constant);
        let challenge = transcript.squeeze_ext3::<F>();
        claim = evaluate_ext3_coefficient_round(claim, &round.non_constant, challenge);
        point.push(challenge);
    }
    Ok((point, claim))
}

/// Interpolate values at `0..degree` into base-field monomial coefficients.
pub fn base_evaluations_to_coefficients<F: Field>(evaluations: &[F]) -> Vec<F> {
    assert!(!evaluations.is_empty());
    let degree = evaluations.len() - 1;
    let mut matrix = vec![vec![F::ZERO; degree + 2]; degree + 1];
    for row in 0..=degree {
        let x = F::from_canonical_usize(row);
        let mut power = F::ONE;
        for col in 0..=degree {
            matrix[row][col] = power;
            power *= x;
        }
        matrix[row][degree + 1] = evaluations[row];
    }
    gaussian_eliminate_base(&mut matrix);
    matrix.into_iter().map(|row| row[degree + 1]).collect()
}

/// Interpolate values at `0..degree` into Ext3 monomial coefficients.
pub fn ext3_evaluations_to_coefficients(evaluations: &[Field64_3]) -> Vec<Field64_3> {
    assert!(!evaluations.is_empty());
    let degree = evaluations.len() - 1;
    let mut matrix = vec![vec![Field64_3::ZERO; degree + 2]; degree + 1];
    for row in 0..=degree {
        let x = Field64_3::from(row as u64);
        let mut power = Field64_3::ONE;
        for col in 0..=degree {
            matrix[row][col] = power;
            power *= x;
        }
        matrix[row][degree + 1] = evaluations[row];
    }
    gaussian_eliminate_ext3(&mut matrix);
    matrix.into_iter().map(|row| row[degree + 1]).collect()
}

// Preserve the audited pivot/row/column order and its in-place dependencies.
#[allow(clippy::needless_range_loop)]
fn gaussian_eliminate_base<F: Field>(matrix: &mut [Vec<F>]) {
    let n = matrix.len();
    for pivot in 0..n {
        let pivot_inverse = matrix[pivot][pivot].inverse();
        for col in pivot..=n {
            matrix[pivot][col] *= pivot_inverse;
        }
        let pivot_row = matrix[pivot].clone();
        for row in 0..n {
            if row == pivot {
                continue;
            }
            let factor = matrix[row][pivot];
            for col in pivot..=n {
                matrix[row][col] -= factor * pivot_row[col];
            }
        }
    }
}

// Keep the same indexed elimination order as the base-field implementation.
#[allow(clippy::needless_range_loop)]
fn gaussian_eliminate_ext3(matrix: &mut [Vec<Field64_3>]) {
    let n = matrix.len();
    for pivot in 0..n {
        let pivot_inverse = matrix[pivot][pivot]
            .inverse()
            .expect("distinct small interpolation nodes");
        for col in pivot..=n {
            matrix[pivot][col] *= pivot_inverse;
        }
        let pivot_row = matrix[pivot].clone();
        for row in 0..n {
            if row == pivot {
                continue;
            }
            let factor = matrix[row][pivot];
            for col in pivot..=n {
                matrix[row][col] -= factor * pivot_row[col];
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use plonky2_field::goldilocks_field::GoldilocksField;

    use super::*;

    type F = GoldilocksField;

    #[test]
    fn base_interpolation_recovers_coefficients() {
        let coefficients = [
            F::from_canonical_u64(3),
            F::from_canonical_u64(5),
            F::from_canonical_u64(7),
        ];
        let evals = (0..=2)
            .map(|i| {
                let x = F::from_canonical_usize(i);
                coefficients[0] + coefficients[1] * x + coefficients[2] * x * x
            })
            .collect::<Vec<_>>();
        assert_eq!(base_evaluations_to_coefficients(&evals), coefficients);
    }

    #[test]
    fn ext3_interpolation_recovers_coefficients() {
        let coefficients = [
            Field64_3::from(3u64),
            Field64_3::new(5u64.into(), 7u64.into(), 11u64.into()),
            Field64_3::new(13u64.into(), 17u64.into(), 19u64.into()),
        ];
        let evals = (0..=2)
            .map(|i| {
                let x = Field64_3::from(i as u64);
                coefficients[0] + coefficients[1] * x + coefficients[2] * x.square()
            })
            .collect::<Vec<_>>();
        assert_eq!(ext3_evaluations_to_coefficients(&evals), coefficients);
    }

    #[test]
    fn malformed_degree_is_rejected_before_challenge() {
        let proof = CoefficientSumcheckProof {
            rounds: vec![CoefficientRound {
                non_constant: vec![F::ONE],
            }],
        };
        let mut transcript = TranscriptV2::new();
        let before = transcript.state_digest();
        assert!(verify_coefficient_sumcheck(&proof, F::ZERO, 1, 2, &mut transcript).is_err());
        assert_eq!(transcript.state_digest(), before);
    }
}
