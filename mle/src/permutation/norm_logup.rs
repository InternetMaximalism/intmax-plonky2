//! Cubic-extension norm helpers and the joint norm/logUp sumcheck.
//!
//! Boolean-row tables remain over Goldilocks and are therefore directly
//! commit-able by the existing grouped WHIR PCS.  The outer sumcheck, its
//! random point, and its terminal equation live in
//! `K = Fp[theta] / (theta^3 - 2)`.
//!
//! The off-cube formulas in this module are intentionally *formal coordinate
//! polynomials*.  In particular, [`formal_norm_from_coords`] must be used at
//! an Ext3 sumcheck point; calling the field norm or inverse on a recomposed
//! off-cube value would have the wrong polynomial degree.

use ark_ff::{AdditiveGroup, Field as ArkField, PrimeField as ArkPrimeField};
use plonky2_field::types::PrimeField64;
use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

use crate::sumcheck::coefficients::{
    ext3_evaluations_to_coefficients, Ext3CoefficientRound, Ext3CoefficientSumcheckProof,
};
use crate::sumcheck::ext3::Ext3DenseMle;
use crate::transcript_v2::TranscriptV2;

/// Exact per-variable degree of the joint norm/logUp target.
pub const NORM_LOGUP_MAX_DEGREE: usize = 5;

/// Fiat--Shamir challenges that define the joint norm/logUp target.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NormLogupChallenges {
    /// Cubic-extension denominator offset.
    pub beta: Field64_3,
    /// Cubic-extension denominator position coefficient.
    pub gamma: Field64_3,
    /// Geometric combiner across routed-wire helper relations.
    pub lambda: Field64_3,
    /// Independent combiner for identity and sigma helper relations.
    pub rho: Field64_3,
    /// Independent combiner between helper zero checks and the global logUp sum.
    pub kappa: Field64_3,
    /// Uniform Ext3 geometric combiner over the ordered raw public-input vector.
    /// Zero is allowed and its bad-challenge event is charged in the soundness bound.
    pub eta: Field64_3,
    /// Uniform independent combiner between the permutation relation and the
    /// public-input/witness copy relation. Zero is likewise allowed and charged.
    pub xi: Field64_3,
}

/// Base-field helper tables committed as the third packed WHIR group.
///
/// Both families are column-major. `identity[j][row]` stores
/// `N(D_id,j(row))^-1`; `sigma[j][row]` stores
/// `N(D_sigma,j(row))^-1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormInverseTables<F> {
    pub identity: Vec<Vec<F>>,
    pub sigma: Vec<Vec<F>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NormDenominatorSide {
    Identity,
    Sigma,
}

/// Honest-prover failure while constructing a norm-inverse table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NormInverseTableError {
    InvalidShape(&'static str),
    ZeroDenominator {
        side: NormDenominatorSide,
        routed_wire: usize,
        row: usize,
    },
}

impl core::fmt::Display for NormInverseTableError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidShape(message) => write!(f, "norm/logUp table shape: {message}"),
            Self::ZeroDenominator {
                side,
                routed_wire,
                row,
            } => write!(
                f,
                "zero {side:?} norm/logUp denominator at routed wire {routed_wire}, row {row}"
            ),
        }
    }
}

impl std::error::Error for NormInverseTableError {}

/// Formal adjugate coordinates for `a + b*theta + c*theta^2`, where
/// `theta^3 = 2`.
///
/// This is generic over an arkworks field so it can be evaluated over the base
/// field on Boolean rows and over `Field64_3` at an off-cube sumcheck point.
pub fn formal_adjugate_from_coords<E: ArkField>(coords: [E; 3]) -> [E; 3] {
    let [a, b, c] = coords;
    let two = E::from(2u64);
    [
        a.square() - two * b * c,
        two * c.square() - a * b,
        b.square() - a * c,
    ]
}

/// Formal cubic norm polynomial for coordinate polynomials `(a,b,c)`.
///
/// When `E = Field64`, this is the ordinary field norm.  When
/// `E = Field64_3`, the inputs are themselves off-cube polynomial values and
/// this function deliberately evaluates the degree-three coordinate formula
/// rather than applying Frobenius or a `p^2+p+1` exponent.
pub fn formal_norm_from_coords<E: ArkField>(coords: [E; 3]) -> E {
    let [a, b, c] = coords;
    let [s0, s1, s2] = formal_adjugate_from_coords(coords);
    a * s0 + E::from(2u64) * (c * s1 + b * s2)
}

fn canonical_u64(value: ArkGoldilocks) -> u64 {
    value.into_bigint().0[0]
}

fn embed_ark_base(value: ArkGoldilocks) -> Field64_3 {
    Field64_3::new(value, ArkGoldilocks::ZERO, ArkGoldilocks::ZERO)
}

fn embed_plonky_base<F: PrimeField64>(value: F) -> Field64_3 {
    Field64_3::from(value.to_canonical_u64())
}

fn lifted_coefficients(value: Field64_3) -> [Field64_3; 3] {
    [
        embed_ark_base(value.c0),
        embed_ark_base(value.c1),
        embed_ark_base(value.c2),
    ]
}

fn denominator_coords_base(
    wire: ArkGoldilocks,
    position: ArkGoldilocks,
    beta: Field64_3,
    gamma: Field64_3,
) -> [ArkGoldilocks; 3] {
    [
        beta.c0 + wire + gamma.c0 * position,
        beta.c1 + gamma.c1 * position,
        beta.c2 + gamma.c2 * position,
    ]
}

fn denominator_coords_ext3(
    wire: Field64_3,
    position: Field64_3,
    beta: [Field64_3; 3],
    gamma: [Field64_3; 3],
) -> [Field64_3; 3] {
    [
        beta[0] + wire + gamma[0] * position,
        beta[1] + gamma[1] * position,
        beta[2] + gamma[2] * position,
    ]
}

fn recompose_formal_adjugate(coords: [Field64_3; 3]) -> Field64_3 {
    let [s0, s1, s2] = formal_adjugate_from_coords(coords);
    let theta = Field64_3::new(ArkGoldilocks::ZERO, ArkGoldilocks::ONE, ArkGoldilocks::ZERO);
    s0 + theta * s1 + theta.square() * s2
}

/// Construct the two base-field norm-inverse helper families on the Boolean
/// row domain.
///
/// Input layouts match Plonky2's extracted evaluation tables:
/// `wire_values[wire][row]`, `sigma_values[row][wire]`, and `subgroup[row]`.
/// Only the first `num_routed_wires` witness/sigma columns are consumed.
#[allow(clippy::too_many_arguments)]
pub fn compute_norm_inverse_tables<F: PrimeField64>(
    wire_values: &[Vec<F>],
    sigma_values: &[Vec<F>],
    k_is: &[F],
    subgroup: &[F],
    beta: Field64_3,
    gamma: Field64_3,
    num_routed_wires: usize,
    degree: usize,
) -> Result<NormInverseTables<F>, NormInverseTableError> {
    if F::ORDER != 0xFFFF_FFFF_0000_0001 {
        return Err(NormInverseTableError::InvalidShape(
            "helper field is not Goldilocks",
        ));
    }
    if wire_values.len() < num_routed_wires {
        return Err(NormInverseTableError::InvalidShape(
            "fewer witness columns than routed wires",
        ));
    }
    if k_is.len() < num_routed_wires {
        return Err(NormInverseTableError::InvalidShape(
            "fewer identity coset shifts than routed wires",
        ));
    }
    if subgroup.len() < degree || sigma_values.len() < degree {
        return Err(NormInverseTableError::InvalidShape(
            "row table is shorter than degree",
        ));
    }
    if wire_values
        .iter()
        .take(num_routed_wires)
        .any(|column| column.len() < degree)
    {
        return Err(NormInverseTableError::InvalidShape(
            "routed witness column is shorter than degree",
        ));
    }
    if sigma_values
        .iter()
        .take(degree)
        .any(|row| row.len() < num_routed_wires)
    {
        return Err(NormInverseTableError::InvalidShape(
            "sigma row is shorter than routed-wire count",
        ));
    }

    let mut identity = vec![vec![F::ZERO; degree]; num_routed_wires];
    let mut sigma = vec![vec![F::ZERO; degree]; num_routed_wires];

    for routed_wire in 0..num_routed_wires {
        let k = ArkGoldilocks::from(k_is[routed_wire].to_canonical_u64());
        for row in 0..degree {
            let wire = ArkGoldilocks::from(wire_values[routed_wire][row].to_canonical_u64());
            let subgroup_value = ArkGoldilocks::from(subgroup[row].to_canonical_u64());
            let identity_position = k * subgroup_value;
            let sigma_position =
                ArkGoldilocks::from(sigma_values[row][routed_wire].to_canonical_u64());

            for (side, position, destination) in [
                (
                    NormDenominatorSide::Identity,
                    identity_position,
                    &mut identity[routed_wire][row],
                ),
                (
                    NormDenominatorSide::Sigma,
                    sigma_position,
                    &mut sigma[routed_wire][row],
                ),
            ] {
                let norm =
                    formal_norm_from_coords(denominator_coords_base(wire, position, beta, gamma));
                let inverse = norm
                    .inverse()
                    .ok_or(NormInverseTableError::ZeroDenominator {
                        side,
                        routed_wire,
                        row,
                    })?;
                *destination = F::from_canonical_u64(canonical_u64(inverse));
            }
        }
    }

    Ok(NormInverseTables { identity, sigma })
}

#[derive(Clone)]
struct PreparedChallenges {
    beta: [Field64_3; 3],
    gamma: [Field64_3; 3],
    lambda_powers: Vec<Field64_3>,
    rho: Field64_3,
    kappa: Field64_3,
    eta: Field64_3,
    xi: Field64_3,
    k_is: Vec<Field64_3>,
}

impl PreparedChallenges {
    fn new<F: PrimeField64>(
        challenges: NormLogupChallenges,
        k_is: &[F],
        num_routed_wires: usize,
    ) -> Self {
        assert_eq!(
            F::ORDER,
            0xFFFF_FFFF_0000_0001,
            "norm/logUp Ext3 is defined only over Goldilocks"
        );
        assert!(k_is.len() >= num_routed_wires);

        let mut lambda_powers = Vec::with_capacity(num_routed_wires);
        let mut power = Field64_3::ONE;
        for _ in 0..num_routed_wires {
            lambda_powers.push(power);
            power *= challenges.lambda;
        }
        Self {
            beta: lifted_coefficients(challenges.beta),
            gamma: lifted_coefficients(challenges.gamma),
            lambda_powers,
            rho: challenges.rho,
            kappa: challenges.kappa,
            eta: challenges.eta,
            xi: challenges.xi,
            k_is: k_is
                .iter()
                .take(num_routed_wires)
                .copied()
                .map(embed_plonky_base)
                .collect(),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn evaluate_target_from_values(
    eq_value: Field64_3,
    routed_wires: &[Field64_3],
    sigmas: &[Field64_3],
    inverse_identity: &[Field64_3],
    inverse_sigma: &[Field64_3],
    subgroup: Field64_3,
    public_input_binding: Field64_3,
    prepared: &PreparedChallenges,
) -> Field64_3 {
    let num_routed_wires = prepared.lambda_powers.len();
    assert_eq!(routed_wires.len(), num_routed_wires);
    assert_eq!(sigmas.len(), num_routed_wires);
    assert_eq!(inverse_identity.len(), num_routed_wires);
    assert_eq!(inverse_sigma.len(), num_routed_wires);

    let mut helper_zero_checks = Field64_3::ZERO;
    let mut logup_sum = Field64_3::ZERO;
    for routed_wire in 0..num_routed_wires {
        let wire = routed_wires[routed_wire];
        let identity_position = prepared.k_is[routed_wire] * subgroup;
        let identity_coords =
            denominator_coords_ext3(wire, identity_position, prepared.beta, prepared.gamma);
        let sigma_coords =
            denominator_coords_ext3(wire, sigmas[routed_wire], prepared.beta, prepared.gamma);

        let t_identity = inverse_identity[routed_wire];
        let t_sigma = inverse_sigma[routed_wire];
        let z_identity = t_identity * formal_norm_from_coords(identity_coords) - Field64_3::ONE;
        let z_sigma = t_sigma * formal_norm_from_coords(sigma_coords) - Field64_3::ONE;
        helper_zero_checks +=
            prepared.lambda_powers[routed_wire] * (z_identity + prepared.rho * z_sigma);

        let inverse_identity_value = t_identity * recompose_formal_adjugate(identity_coords);
        let inverse_sigma_value = t_sigma * recompose_formal_adjugate(sigma_coords);
        logup_sum += inverse_identity_value - inverse_sigma_value;
    }

    eq_value * helper_zero_checks + prepared.kappa * logup_sum + prepared.xi * public_input_binding
}

fn eq_evals_ext3(tau: &[Field64_3]) -> Vec<Field64_3> {
    let size = 1usize << tau.len();
    let mut result = vec![Field64_3::ONE; size];
    for (variable, &coordinate) in tau.iter().enumerate() {
        let one_minus = Field64_3::ONE - coordinate;
        for (row, value) in result.iter_mut().enumerate() {
            *value *= if (row >> variable) & 1 == 0 {
                one_minus
            } else {
                coordinate
            };
        }
    }
    result
}

fn eq_eval_ext3(tau: &[Field64_3], point: &[Field64_3]) -> Field64_3 {
    assert_eq!(tau.len(), point.len(), "norm/logUp eq point width mismatch");
    tau.iter()
        .zip(point)
        .map(|(&tau_i, &point_i)| {
            tau_i * point_i + (Field64_3::ONE - tau_i) * (Field64_3::ONE - point_i)
        })
        .product()
}

fn line_value(mle: &Ext3DenseMle, suffix: usize, point: Field64_3) -> Field64_3 {
    let low = mle.evaluations[2 * suffix];
    let high = mle.evaluations[2 * suffix + 1];
    low + point * (high - low)
}

struct NormLogupMleState {
    eq: Ext3DenseMle,
    wires: Vec<Ext3DenseMle>,
    sigmas: Vec<Ext3DenseMle>,
    inverse_identity: Vec<Ext3DenseMle>,
    inverse_sigma: Vec<Ext3DenseMle>,
    subgroup: Ext3DenseMle,
    public_input_bindings: Vec<PublicInputBindingState>,
    bound_variables: usize,
}

#[derive(Clone)]
struct PublicInputBindingState {
    row: usize,
    column: usize,
    value: Field64_3,
    eta_power: Field64_3,
    prefix_eq: Field64_3,
}

impl NormLogupMleState {
    #[allow(clippy::too_many_arguments)]
    fn from_base<F: PrimeField64>(
        wire_values: &[Vec<F>],
        sigma_values: &[Vec<F>],
        subgroup: &[F],
        inverse_tables: &NormInverseTables<F>,
        tau: &[Field64_3],
        num_routed_wires: usize,
        public_inputs: &[F],
        public_input_wires: &[(usize, usize)],
        eta: Field64_3,
    ) -> Self {
        let num_rows = 1usize << tau.len();
        assert!(wire_values.len() >= num_routed_wires);
        assert_eq!(sigma_values.len(), num_rows);
        assert_eq!(subgroup.len(), num_rows);
        assert_eq!(inverse_tables.identity.len(), num_routed_wires);
        assert_eq!(inverse_tables.sigma.len(), num_routed_wires);
        assert!(wire_values
            .iter()
            .take(num_routed_wires)
            .all(|column| column.len() == num_rows));
        assert!(sigma_values.iter().all(|row| row.len() >= num_routed_wires));
        assert!(inverse_tables
            .identity
            .iter()
            .chain(&inverse_tables.sigma)
            .all(|column| column.len() == num_rows));
        assert_eq!(public_inputs.len(), public_input_wires.len());
        assert!(public_input_wires
            .iter()
            .all(|&(row, column)| row < num_rows && column < num_routed_wires));

        let mut eta_power = Field64_3::ONE;
        let public_input_bindings = public_inputs
            .iter()
            .zip(public_input_wires)
            .map(|(&value, &(row, column))| {
                let binding = PublicInputBindingState {
                    row,
                    column,
                    value: embed_plonky_base(value),
                    eta_power,
                    prefix_eq: Field64_3::ONE,
                };
                eta_power *= eta;
                binding
            })
            .collect();

        let sigmas = (0..num_routed_wires)
            .map(|column| {
                let values: Vec<F> = sigma_values.iter().map(|row| row[column]).collect();
                Ext3DenseMle::from_base(&values)
            })
            .collect();
        Self {
            eq: Ext3DenseMle::new(eq_evals_ext3(tau)),
            wires: wire_values
                .iter()
                .take(num_routed_wires)
                .map(|column| Ext3DenseMle::from_base(column))
                .collect(),
            sigmas,
            inverse_identity: inverse_tables
                .identity
                .iter()
                .map(|column| Ext3DenseMle::from_base(column))
                .collect(),
            inverse_sigma: inverse_tables
                .sigma
                .iter()
                .map(|column| Ext3DenseMle::from_base(column))
                .collect(),
            subgroup: Ext3DenseMle::from_base(subgroup),
            public_input_bindings,
            bound_variables: 0,
        }
    }

    fn round_sum_at(&self, point: Field64_3, prepared: &PreparedChallenges) -> Field64_3 {
        let half = self.eq.evaluations.len() / 2;
        let num_routed_wires = self.wires.len();
        let mut wires = vec![Field64_3::ZERO; num_routed_wires];
        let mut sigmas = vec![Field64_3::ZERO; num_routed_wires];
        let mut inverse_identity = vec![Field64_3::ZERO; num_routed_wires];
        let mut inverse_sigma = vec![Field64_3::ZERO; num_routed_wires];
        let mut sum = Field64_3::ZERO;

        for suffix in 0..half {
            for routed_wire in 0..num_routed_wires {
                wires[routed_wire] = line_value(&self.wires[routed_wire], suffix, point);
                sigmas[routed_wire] = line_value(&self.sigmas[routed_wire], suffix, point);
                inverse_identity[routed_wire] =
                    line_value(&self.inverse_identity[routed_wire], suffix, point);
                inverse_sigma[routed_wire] =
                    line_value(&self.inverse_sigma[routed_wire], suffix, point);
            }
            sum += evaluate_target_from_values(
                line_value(&self.eq, suffix, point),
                &wires,
                &sigmas,
                &inverse_identity,
                &inverse_sigma,
                line_value(&self.subgroup, suffix, point),
                Field64_3::ZERO,
                prepared,
            );
        }

        // For eq(row_i, x), every Boolean suffix except the one selected by
        // row_i is zero. Evaluate only that suffix. Variables are bound in
        // LSB-first order, matching DenseMle's adjacent-pair convention.
        let mut public_input_binding = Field64_3::ZERO;
        for binding in &self.public_input_bindings {
            let suffix = binding.row >> (self.bound_variables + 1);
            let bit = (binding.row >> self.bound_variables) & 1;
            let eq_line = binding.prefix_eq
                * if bit == 0 {
                    Field64_3::ONE - point
                } else {
                    point
                };
            let wire = line_value(&self.wires[binding.column], suffix, point);
            public_input_binding += binding.eta_power * eq_line * (wire - binding.value);
        }
        sum + prepared.xi * public_input_binding
    }

    fn bind(&mut self, challenge: Field64_3) {
        for binding in &mut self.public_input_bindings {
            let bit = (binding.row >> self.bound_variables) & 1;
            binding.prefix_eq *= if bit == 0 {
                Field64_3::ONE - challenge
            } else {
                challenge
            };
        }
        self.bound_variables += 1;
        self.eq.bind_variable_in_place(challenge);
        self.subgroup.bind_variable_in_place(challenge);
        for mle in self
            .wires
            .iter_mut()
            .chain(&mut self.sigmas)
            .chain(&mut self.inverse_identity)
            .chain(&mut self.inverse_sigma)
        {
            mle.bind_variable_in_place(challenge);
        }
    }
}

/// Invalid transition in the transcript-agnostic norm/logUp prover state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NormLogupProverStateError {
    /// A challenge was supplied before the current round coefficients were
    /// requested.
    RoundNotComputed { round: usize },
    /// All variables have already been bound.
    NoRoundsRemaining,
    /// Proof extraction was requested before every round was bound.
    Incomplete {
        completed_rounds: usize,
        total_rounds: usize,
    },
}

impl core::fmt::Display for NormLogupProverStateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RoundNotComputed { round } => {
                write!(f, "norm/logUp round {round} has not been computed")
            }
            Self::NoRoundsRemaining => write!(f, "norm/logUp sumcheck has no rounds remaining"),
            Self::Incomplete {
                completed_rounds,
                total_rounds,
            } => write!(
                f,
                "norm/logUp sumcheck is incomplete: {completed_rounds}/{total_rounds} rounds bound"
            ),
        }
    }
}

impl std::error::Error for NormLogupProverStateError {}

/// Transcript-independent state for the degree-five norm/logUp sumcheck.
///
/// A lockstep orchestrator calls [`Self::current_round`] on this state and on
/// every gate-fork state, absorbs all returned coefficient vectors into one
/// transcript, derives one shared challenge, then calls
/// [`Self::bind_challenge`]. No transcript is owned or advanced here.
pub struct NormLogupProverState {
    mle_state: NormLogupMleState,
    prepared: PreparedChallenges,
    total_rounds: usize,
    completed_rounds: Vec<Ext3CoefficientRound>,
    pending_round: Option<Ext3CoefficientRound>,
    point: Vec<Field64_3>,
}

impl NormLogupProverState {
    /// Initialize the state from Boolean-row base-field tables.
    #[allow(clippy::too_many_arguments)]
    pub fn new<F: PrimeField64>(
        wire_values: &[Vec<F>],
        sigma_values: &[Vec<F>],
        k_is: &[F],
        subgroup: &[F],
        inverse_tables: &NormInverseTables<F>,
        tau: &[Field64_3],
        challenges: NormLogupChallenges,
    ) -> Self {
        Self::new_with_public_inputs(
            wire_values,
            sigma_values,
            k_is,
            subgroup,
            inverse_tables,
            tau,
            challenges,
            &[],
            &[],
        )
    }

    /// Initialize the production relation, including direct ordered public-
    /// input binding to canonical routed witness locations.
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_public_inputs<F: PrimeField64>(
        wire_values: &[Vec<F>],
        sigma_values: &[Vec<F>],
        k_is: &[F],
        subgroup: &[F],
        inverse_tables: &NormInverseTables<F>,
        tau: &[Field64_3],
        challenges: NormLogupChallenges,
        public_inputs: &[F],
        public_input_wires: &[(usize, usize)],
    ) -> Self {
        let num_routed_wires = inverse_tables.identity.len();
        assert_eq!(inverse_tables.sigma.len(), num_routed_wires);
        Self {
            mle_state: NormLogupMleState::from_base(
                wire_values,
                sigma_values,
                subgroup,
                inverse_tables,
                tau,
                num_routed_wires,
                public_inputs,
                public_input_wires,
                challenges.eta,
            ),
            prepared: PreparedChallenges::new(challenges, k_is, num_routed_wires),
            total_rounds: tau.len(),
            completed_rounds: Vec::with_capacity(tau.len()),
            pending_round: None,
            point: Vec::with_capacity(tau.len()),
        }
    }

    /// Return the current round's five non-constant monomial coefficients.
    ///
    /// Repeated calls before binding are idempotent and return the same cached
    /// round. This permits an orchestrator to inspect/serialize the round
    /// without accidentally advancing the algebraic state.
    pub fn current_round(&mut self) -> Result<Ext3CoefficientRound, NormLogupProverStateError> {
        if self.is_complete() {
            return Err(NormLogupProverStateError::NoRoundsRemaining);
        }
        if self.pending_round.is_none() {
            let evaluations = (0..=NORM_LOGUP_MAX_DEGREE)
                .map(|integer| {
                    self.mle_state
                        .round_sum_at(Field64_3::from(integer as u64), &self.prepared)
                })
                .collect::<Vec<_>>();
            let coefficients = ext3_evaluations_to_coefficients(&evaluations);
            self.pending_round = Some(Ext3CoefficientRound {
                non_constant: coefficients[1..].to_vec(),
            });
        }
        Ok(self
            .pending_round
            .as_ref()
            .expect("pending round was initialized")
            .clone())
    }

    /// Bind every constituent MLE with a challenge derived by the external
    /// lockstep transcript orchestrator.
    pub fn bind_challenge(
        &mut self,
        challenge: Field64_3,
    ) -> Result<(), NormLogupProverStateError> {
        if self.is_complete() {
            return Err(NormLogupProverStateError::NoRoundsRemaining);
        }
        let round =
            self.pending_round
                .take()
                .ok_or(NormLogupProverStateError::RoundNotComputed {
                    round: self.completed_rounds.len(),
                })?;
        self.mle_state.bind(challenge);
        self.completed_rounds.push(round);
        self.point.push(challenge);
        Ok(())
    }

    pub fn is_complete(&self) -> bool {
        self.completed_rounds.len() == self.total_rounds
    }

    pub fn completed_round_count(&self) -> usize {
        self.completed_rounds.len()
    }

    pub fn total_round_count(&self) -> usize {
        self.total_rounds
    }

    pub fn point(&self) -> &[Field64_3] {
        &self.point
    }

    /// Consume a complete state and return the transcript-bound proof messages
    /// together with the externally supplied challenge point.
    pub fn into_proof_and_point(
        self,
    ) -> Result<(Ext3CoefficientSumcheckProof, Vec<Field64_3>), NormLogupProverStateError> {
        if !self.is_complete() {
            return Err(NormLogupProverStateError::Incomplete {
                completed_rounds: self.completed_rounds.len(),
                total_rounds: self.total_rounds,
            });
        }
        Ok((
            Ext3CoefficientSumcheckProof {
                rounds: self.completed_rounds,
            },
            self.point,
        ))
    }
}

/// Prove the degree-five joint norm-helper and logUp claim
///
/// ```text
/// Phi(x) = eq(tau,x) * sum_j lambda^j * (Z_id,j + rho*Z_sigma,j)
///          + kappa * sum_j (A_id,j - A_sigma,j),
/// sum_{x in {0,1}^n} Phi(x) = 0.
/// ```
///
/// The prover evaluates each degree-five round polynomial at the six integer
/// nodes `0..=5`, converts those samples to monomial coefficients, and emits
/// only the five non-constant coefficients. The constant coefficient is
/// reconstructed by the verifier from the incoming claim. The returned point
/// is the sole norm/logUp terminal row point and can be passed directly to
/// grouped WHIR after appending the constituent-index coordinates.
///
/// This is a compatibility helper for callers proving only this sumcheck. The
/// v2 production protocol must instead drive [`NormLogupProverState`] from its
/// joint lockstep outer-transcript orchestrator; it must not create a separate
/// transcript or fork for norm/logUp.
#[allow(clippy::too_many_arguments)]
pub fn prove_joint_norm_logup<F: PrimeField64>(
    wire_values: &[Vec<F>],
    sigma_values: &[Vec<F>],
    k_is: &[F],
    subgroup: &[F],
    inverse_tables: &NormInverseTables<F>,
    tau: &[Field64_3],
    challenges: NormLogupChallenges,
    transcript: &mut TranscriptV2,
) -> (Ext3CoefficientSumcheckProof, Vec<Field64_3>) {
    let mut state = NormLogupProverState::new(
        wire_values,
        sigma_values,
        k_is,
        subgroup,
        inverse_tables,
        tau,
        challenges,
    );

    while !state.is_complete() {
        let round = state
            .current_round()
            .expect("incomplete norm/logUp state has a current round");
        transcript.domain_separate("sumcheck-round-coeff-ext3-v3");
        transcript.absorb_ext3_vec(&round.non_constant);
        let challenge = transcript.squeeze_ext3::<F>();
        state
            .bind_challenge(challenge)
            .expect("current norm/logUp round was computed");
    }

    state
        .into_proof_and_point()
        .expect("all norm/logUp rounds were bound")
}

/// Evaluate the exact terminal polynomial from PCS-bound constituent values at
/// the Ext3 sumcheck output point.
///
/// `routed_wires`, `sigmas`, `inverse_identity`, and `inverse_sigma` are all
/// direct `K`-valued MLE evaluations at `point`; `subgroup` is recomputed from
/// VK-bound subgroup powers by the verifier rather than trusted as a proof
/// field.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_joint_norm_logup_terminal<F: PrimeField64>(
    tau: &[Field64_3],
    point: &[Field64_3],
    routed_wires: &[Field64_3],
    sigmas: &[Field64_3],
    inverse_identity: &[Field64_3],
    inverse_sigma: &[Field64_3],
    subgroup: Field64_3,
    k_is: &[F],
    challenges: NormLogupChallenges,
) -> Field64_3 {
    evaluate_joint_norm_logup_terminal_with_public_inputs(
        tau,
        point,
        routed_wires,
        sigmas,
        inverse_identity,
        inverse_sigma,
        subgroup,
        k_is,
        challenges,
        &[],
        &[],
    )
}

/// Evaluate the production terminal with direct raw-public-input binding.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_joint_norm_logup_terminal_with_public_inputs<F: PrimeField64>(
    tau: &[Field64_3],
    point: &[Field64_3],
    routed_wires: &[Field64_3],
    sigmas: &[Field64_3],
    inverse_identity: &[Field64_3],
    inverse_sigma: &[Field64_3],
    subgroup: Field64_3,
    k_is: &[F],
    challenges: NormLogupChallenges,
    public_inputs: &[F],
    public_input_wires: &[(usize, usize)],
) -> Field64_3 {
    let prepared = PreparedChallenges::new(challenges, k_is, routed_wires.len());
    assert_eq!(public_inputs.len(), public_input_wires.len());
    let mut eta_power = Field64_3::ONE;
    let mut public_input_binding = Field64_3::ZERO;
    for (&public_input, &(row, column)) in public_inputs.iter().zip(public_input_wires) {
        assert!(column < routed_wires.len());
        assert!(row < (1usize << point.len()));
        let eq_row = point
            .iter()
            .enumerate()
            .map(|(variable, &coordinate)| {
                if (row >> variable) & 1 == 0 {
                    Field64_3::ONE - coordinate
                } else {
                    coordinate
                }
            })
            .product::<Field64_3>();
        public_input_binding +=
            eta_power * eq_row * (routed_wires[column] - embed_plonky_base(public_input));
        eta_power *= prepared.eta;
    }
    evaluate_target_from_values(
        eq_eval_ext3(tau, point),
        routed_wires,
        sigmas,
        inverse_identity,
        inverse_sigma,
        subgroup,
        public_input_binding,
        &prepared,
    )
}

#[cfg(test)]
mod tests {
    use ark_ff::{AdditiveGroup, Field as ArkField};
    use plonky2_field::goldilocks_field::GoldilocksField;
    use plonky2_field::types::Field as PlonkyField;

    use super::*;
    use crate::sumcheck::coefficients::verify_ext3_coefficient_sumcheck;

    type F = GoldilocksField;

    fn ext3(seed: u64) -> Field64_3 {
        Field64_3::new(
            ArkGoldilocks::from(seed),
            ArkGoldilocks::from(seed.wrapping_mul(3).wrapping_add(1)),
            ArkGoldilocks::from(seed.wrapping_mul(5).wrapping_add(2)),
        )
    }

    // The tuple mirrors the ordered inputs consumed by the relation tests.
    #[allow(clippy::type_complexity)]
    fn honest_tables(
        num_vars: usize,
        num_routed: usize,
        beta: Field64_3,
        gamma: Field64_3,
    ) -> (
        Vec<Vec<F>>,
        Vec<Vec<F>>,
        Vec<F>,
        Vec<F>,
        NormInverseTables<F>,
    ) {
        let rows = 1usize << num_vars;
        let wires = (0..num_routed)
            .map(|wire| {
                (0..rows)
                    .map(|row| F::from_canonical_usize(17 + 11 * wire + 7 * row))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let subgroup = (0..rows)
            .map(|row| F::from_canonical_usize(2 * row + 1))
            .collect::<Vec<_>>();
        let k_is = (0..num_routed)
            .map(|wire| F::from_canonical_usize(3 * wire + 1))
            .collect::<Vec<_>>();
        // Identity sigma makes every log-derivative difference zero while
        // retaining nontrivial helper polynomials off the Boolean cube.
        let sigma = (0..rows)
            .map(|row| {
                (0..num_routed)
                    .map(|wire| k_is[wire] * subgroup[row])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let helpers = compute_norm_inverse_tables(
            &wires, &sigma, &k_is, &subgroup, beta, gamma, num_routed, rows,
        )
        .unwrap();
        (wires, sigma, k_is, subgroup, helpers)
    }

    fn evaluate_base_column(column: &[F], point: &[Field64_3]) -> Field64_3 {
        Ext3DenseMle::from_base(column).evaluate(point)
    }

    #[test]
    fn formal_adjugate_and_norm_match_ext3_multiplication_on_base_coords() {
        for seed in 1..64u64 {
            let a = ArkGoldilocks::from(seed);
            let b = ArkGoldilocks::from(2 * seed + 1);
            let c = ArkGoldilocks::from(5 * seed + 3);
            let value = Field64_3::new(a, b, c);
            let adjugate = formal_adjugate_from_coords([a, b, c]);
            let norm = formal_norm_from_coords([a, b, c]);
            assert_eq!(
                value * Field64_3::new(adjugate[0], adjugate[1], adjugate[2]),
                embed_ark_base(norm)
            );
            if let Some(norm_inverse) = norm.inverse() {
                assert_eq!(
                    value.inverse().unwrap(),
                    Field64_3::new(
                        adjugate[0] * norm_inverse,
                        adjugate[1] * norm_inverse,
                        adjugate[2] * norm_inverse,
                    )
                );
            }
        }
    }

    #[test]
    fn boolean_helpers_satisfy_both_norm_relations_and_reject_zero() {
        let beta = ext3(19);
        let gamma = ext3(23);
        let (wires, sigma, k_is, subgroup, helpers) = honest_tables(3, 2, beta, gamma);

        for routed_wire in 0..2 {
            for row in 0..8 {
                let wire = ArkGoldilocks::from(wires[routed_wire][row].to_canonical_u64());
                let identity_position =
                    ArkGoldilocks::from((k_is[routed_wire] * subgroup[row]).to_canonical_u64());
                let sigma_position =
                    ArkGoldilocks::from(sigma[row][routed_wire].to_canonical_u64());
                let identity_norm = formal_norm_from_coords(denominator_coords_base(
                    wire,
                    identity_position,
                    beta,
                    gamma,
                ));
                let sigma_norm = formal_norm_from_coords(denominator_coords_base(
                    wire,
                    sigma_position,
                    beta,
                    gamma,
                ));
                assert_eq!(
                    identity_norm
                        * ArkGoldilocks::from(
                            helpers.identity[routed_wire][row].to_canonical_u64(),
                        ),
                    ArkGoldilocks::ONE
                );
                assert_eq!(
                    sigma_norm
                        * ArkGoldilocks::from(helpers.sigma[routed_wire][row].to_canonical_u64(),),
                    ArkGoldilocks::ONE
                );
            }
        }

        let zero = vec![vec![F::ZERO]];
        let error = compute_norm_inverse_tables(
            &zero,
            &zero,
            &[F::ONE],
            &[F::ONE],
            Field64_3::ZERO,
            Field64_3::ZERO,
            1,
            1,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            NormInverseTableError::ZeroDenominator {
                side: NormDenominatorSide::Identity,
                routed_wire: 0,
                row: 0
            }
        ));
    }

    #[test]
    fn state_api_advances_only_after_external_lockstep_challenge() {
        let beta = ext3(101);
        let gamma = ext3(103);
        let challenges = NormLogupChallenges {
            beta,
            gamma,
            lambda: ext3(107),
            rho: ext3(109),
            kappa: ext3(113),
            eta: ext3(115),
            xi: ext3(117),
        };
        let tau = vec![ext3(127), ext3(131), ext3(137)];
        let (wires, sigma, k_is, subgroup, helpers) = honest_tables(tau.len(), 2, beta, gamma);
        let mut state =
            NormLogupProverState::new(&wires, &sigma, &k_is, &subgroup, &helpers, &tau, challenges);
        assert_eq!(state.completed_round_count(), 0);
        assert_eq!(state.total_round_count(), tau.len());
        assert!(matches!(
            state.bind_challenge(ext3(139)),
            Err(NormLogupProverStateError::RoundNotComputed { round: 0 })
        ));

        let mut prover_transcript = TranscriptV2::new();
        prover_transcript.domain_separate("norm-logup-state-test");
        while !state.is_complete() {
            let round = state.current_round().unwrap();
            assert_eq!(state.current_round().unwrap(), round);
            assert_eq!(round.non_constant.len(), NORM_LOGUP_MAX_DEGREE);
            prover_transcript.domain_separate("sumcheck-round-coeff-ext3-v3");
            prover_transcript.absorb_ext3_vec(&round.non_constant);
            let challenge = prover_transcript.squeeze_ext3::<F>();
            state.bind_challenge(challenge).unwrap();
            assert_eq!(state.point().last(), Some(&challenge));
        }
        assert!(matches!(
            state.current_round(),
            Err(NormLogupProverStateError::NoRoundsRemaining)
        ));
        let (proof, prover_point) = state.into_proof_and_point().unwrap();

        let mut verifier_transcript = TranscriptV2::new();
        verifier_transcript.domain_separate("norm-logup-state-test");
        let (verifier_point, _) = verify_ext3_coefficient_sumcheck::<F>(
            &proof,
            Field64_3::ZERO,
            tau.len(),
            NORM_LOGUP_MAX_DEGREE,
            &mut verifier_transcript,
        )
        .unwrap();
        assert_eq!(prover_point, verifier_point);
    }

    #[test]
    fn degree_five_joint_sumcheck_roundtrips_and_terminal_is_identical() {
        let beta = ext3(31);
        let gamma = ext3(37);
        let challenges = NormLogupChallenges {
            beta,
            gamma,
            lambda: ext3(41),
            rho: ext3(43),
            kappa: ext3(47),
            eta: ext3(48),
            xi: ext3(49),
        };
        let tau = vec![ext3(53), ext3(59), ext3(61)];
        let (wires, sigma, k_is, subgroup, helpers) = honest_tables(tau.len(), 2, beta, gamma);

        let mut prover_transcript = TranscriptV2::new();
        prover_transcript.domain_separate("norm-logup-test");
        let (proof, prover_point) = prove_joint_norm_logup(
            &wires,
            &sigma,
            &k_is,
            &subgroup,
            &helpers,
            &tau,
            challenges,
            &mut prover_transcript,
        );
        assert_eq!(proof.rounds.len(), tau.len());
        assert!(proof
            .rounds
            .iter()
            .all(|round| round.non_constant.len() == NORM_LOGUP_MAX_DEGREE));

        let mut verifier_transcript = TranscriptV2::new();
        verifier_transcript.domain_separate("norm-logup-test");
        let (verifier_point, final_eval) = verify_ext3_coefficient_sumcheck::<F>(
            &proof,
            Field64_3::ZERO,
            tau.len(),
            NORM_LOGUP_MAX_DEGREE,
            &mut verifier_transcript,
        )
        .unwrap();
        assert_eq!(verifier_point, prover_point);

        let routed_wires = wires
            .iter()
            .map(|column| evaluate_base_column(column, &verifier_point))
            .collect::<Vec<_>>();
        let sigmas = (0..2)
            .map(|column| {
                let values = sigma.iter().map(|row| row[column]).collect::<Vec<_>>();
                evaluate_base_column(&values, &verifier_point)
            })
            .collect::<Vec<_>>();
        let inverse_identity = helpers
            .identity
            .iter()
            .map(|column| evaluate_base_column(column, &verifier_point))
            .collect::<Vec<_>>();
        let inverse_sigma = helpers
            .sigma
            .iter()
            .map(|column| evaluate_base_column(column, &verifier_point))
            .collect::<Vec<_>>();
        let subgroup_eval = evaluate_base_column(&subgroup, &verifier_point);
        let terminal = evaluate_joint_norm_logup_terminal(
            &tau,
            &verifier_point,
            &routed_wires,
            &sigmas,
            &inverse_identity,
            &inverse_sigma,
            subgroup_eval,
            &k_is,
            challenges,
        );
        assert_eq!(final_eval, terminal);

        // The degree claim is executable: the five transmitted non-constant
        // coefficients plus the claim-derived constant determine the same
        // value at the seventh node as direct evaluation of the target.
        let prepared = PreparedChallenges::new(challenges, &k_is, 2);
        let state = NormLogupMleState::from_base(
            &wires,
            &sigma,
            &subgroup,
            &helpers,
            &tau,
            2,
            &[],
            &[],
            challenges.eta,
        );
        let seventh = state.round_sum_at(Field64_3::from(6u64), &prepared);
        let non_constant = &proof.rounds[0].non_constant;
        let half = Field64_3::from(2u64).inverse().unwrap();
        let a0 = -non_constant.iter().copied().sum::<Field64_3>() * half;
        let encoded_seventh = non_constant
            .iter()
            .rev()
            .fold(Field64_3::ZERO, |acc, coefficient| {
                acc * Field64_3::from(6u64) + coefficient
            })
            * Field64_3::from(6u64)
            + a0;
        assert_eq!(encoded_seventh, seventh);
    }

    #[test]
    fn tampered_round_or_terminal_helper_is_rejected() {
        let beta = ext3(67);
        let gamma = ext3(71);
        let challenges = NormLogupChallenges {
            beta,
            gamma,
            lambda: ext3(73),
            rho: ext3(79),
            kappa: ext3(83),
            eta: ext3(84),
            xi: ext3(85),
        };
        let tau = vec![ext3(89), ext3(97)];
        let (wires, sigma, k_is, subgroup, helpers) = honest_tables(tau.len(), 1, beta, gamma);
        let mut transcript = TranscriptV2::new();
        transcript.domain_separate("norm-logup-tamper-test");
        let (proof, point) = prove_joint_norm_logup(
            &wires,
            &sigma,
            &k_is,
            &subgroup,
            &helpers,
            &tau,
            challenges,
            &mut transcript,
        );

        let mut bad_proof = proof.clone();
        bad_proof.rounds[0].non_constant[0] += Field64_3::ONE;
        let mut bad_transcript = TranscriptV2::new();
        bad_transcript.domain_separate("norm-logup-tamper-test");
        let (bad_point, bad_final_eval) = verify_ext3_coefficient_sumcheck::<F>(
            &bad_proof,
            Field64_3::ZERO,
            tau.len(),
            NORM_LOGUP_MAX_DEGREE,
            &mut bad_transcript,
        )
        .unwrap();
        let bad_wire_eval = [evaluate_base_column(&wires[0], &bad_point)];
        let sigma_column = sigma.iter().map(|row| row[0]).collect::<Vec<_>>();
        let bad_sigma_eval = [evaluate_base_column(&sigma_column, &bad_point)];
        let bad_identity_eval = [evaluate_base_column(&helpers.identity[0], &bad_point)];
        let bad_sigma_inverse_eval = [evaluate_base_column(&helpers.sigma[0], &bad_point)];
        let bad_terminal = evaluate_joint_norm_logup_terminal(
            &tau,
            &bad_point,
            &bad_wire_eval,
            &bad_sigma_eval,
            &bad_identity_eval,
            &bad_sigma_inverse_eval,
            evaluate_base_column(&subgroup, &bad_point),
            &k_is,
            challenges,
        );
        assert_ne!(bad_final_eval, bad_terminal);

        let mut verifier_transcript = TranscriptV2::new();
        verifier_transcript.domain_separate("norm-logup-tamper-test");
        let (_, final_eval) = verify_ext3_coefficient_sumcheck::<F>(
            &proof,
            Field64_3::ZERO,
            tau.len(),
            NORM_LOGUP_MAX_DEGREE,
            &mut verifier_transcript,
        )
        .unwrap();
        let wire_eval = [evaluate_base_column(&wires[0], &point)];
        let sigma_column = sigma.iter().map(|row| row[0]).collect::<Vec<_>>();
        let sigma_eval = [evaluate_base_column(&sigma_column, &point)];
        let mut identity_eval = [evaluate_base_column(&helpers.identity[0], &point)];
        let sigma_inverse_eval = [evaluate_base_column(&helpers.sigma[0], &point)];
        identity_eval[0] += Field64_3::ONE;
        let tampered_terminal = evaluate_joint_norm_logup_terminal(
            &tau,
            &point,
            &wire_eval,
            &sigma_eval,
            &identity_eval,
            &sigma_inverse_eval,
            evaluate_base_column(&subgroup, &point),
            &k_is,
            challenges,
        );
        assert_ne!(final_eval, tampered_terminal);
    }

    #[test]
    fn direct_public_input_relation_is_load_bearing_even_without_statement_transcript_binding() {
        let beta = ext3(151);
        let gamma = ext3(157);
        let challenges = NormLogupChallenges {
            beta,
            gamma,
            lambda: ext3(163),
            rho: ext3(167),
            kappa: ext3(173),
            // Base embeddings make the exact nonzero Boolean-sum defect easy
            // to audit: changing PI #1 by +1 contributes -xi*eta.
            eta: Field64_3::from(2u64),
            xi: Field64_3::from(3u64),
        };
        let tau = vec![ext3(179), ext3(181), ext3(191)];
        let (wires, sigma, k_is, subgroup, helpers) = honest_tables(tau.len(), 2, beta, gamma);
        let public_input_wires = vec![(1usize, 0usize), (6, 1), (1, 0)];
        let honest_public_inputs = public_input_wires
            .iter()
            .map(|&(row, column)| wires[column][row])
            .collect::<Vec<_>>();

        let prove = |public_inputs: &[F]| {
            let mut state = NormLogupProverState::new_with_public_inputs(
                &wires,
                &sigma,
                &k_is,
                &subgroup,
                &helpers,
                &tau,
                challenges,
                public_inputs,
                &public_input_wires,
            );
            let mut transcript = TranscriptV2::new();
            transcript.domain_separate("direct-pi-load-bearing-test");
            while !state.is_complete() {
                let round = state.current_round().unwrap();
                transcript.domain_separate("sumcheck-round-coeff-ext3-v3");
                transcript.absorb_ext3_vec(&round.non_constant);
                let challenge = transcript.squeeze_ext3::<F>();
                state.bind_challenge(challenge).unwrap();
            }
            state.into_proof_and_point().unwrap().0
        };

        let verify_terminal = |proof: &Ext3CoefficientSumcheckProof, public_inputs: &[F]| {
            let mut transcript = TranscriptV2::new();
            transcript.domain_separate("direct-pi-load-bearing-test");
            let (point, final_eval) = verify_ext3_coefficient_sumcheck::<F>(
                proof,
                Field64_3::ZERO,
                tau.len(),
                NORM_LOGUP_MAX_DEGREE,
                &mut transcript,
            )
            .unwrap();
            let routed_wires = wires
                .iter()
                .map(|column| evaluate_base_column(column, &point))
                .collect::<Vec<_>>();
            let sigmas = (0..2)
                .map(|column| {
                    evaluate_base_column(
                        &sigma.iter().map(|row| row[column]).collect::<Vec<_>>(),
                        &point,
                    )
                })
                .collect::<Vec<_>>();
            let inverse_identity = helpers
                .identity
                .iter()
                .map(|column| evaluate_base_column(column, &point))
                .collect::<Vec<_>>();
            let inverse_sigma = helpers
                .sigma
                .iter()
                .map(|column| evaluate_base_column(column, &point))
                .collect::<Vec<_>>();
            let terminal = evaluate_joint_norm_logup_terminal_with_public_inputs(
                &tau,
                &point,
                &routed_wires,
                &sigmas,
                &inverse_identity,
                &inverse_sigma,
                evaluate_base_column(&subgroup, &point),
                &k_is,
                challenges,
                public_inputs,
                &public_input_wires,
            );
            (final_eval, terminal)
        };

        let honest_proof = prove(&honest_public_inputs);
        let (honest_final, honest_terminal) = verify_terminal(&honest_proof, &honest_public_inputs);
        assert_eq!(honest_final, honest_terminal);

        let mut malicious_public_inputs = honest_public_inputs.clone();
        malicious_public_inputs[1] += F::ONE;
        let malicious_state = NormLogupMleState::from_base(
            &wires,
            &sigma,
            &subgroup,
            &helpers,
            &tau,
            2,
            &malicious_public_inputs,
            &public_input_wires,
            challenges.eta,
        );
        let prepared = PreparedChallenges::new(challenges, &k_is, 2);
        let boolean_sum = malicious_state.round_sum_at(Field64_3::ZERO, &prepared)
            + malicious_state.round_sum_at(Field64_3::ONE, &prepared);
        assert_eq!(boolean_sum, -challenges.xi * challenges.eta);

        // Prover and verifier intentionally use the same local transcript;
        // no public-input transcript mismatch is available to reject this.
        // Rejection is therefore caused solely by the new committed-witness
        // relation having a nonzero claimed Boolean sum.
        let malicious_proof = prove(&malicious_public_inputs);
        let (malicious_final, malicious_terminal) =
            verify_terminal(&malicious_proof, &malicious_public_inputs);
        assert_ne!(malicious_final, malicious_terminal);
    }

    #[test]
    fn public_input_terminal_preserves_lsb_rows_order_duplicates_and_zero_bad_events() {
        let beta = ext3(193);
        let gamma = ext3(197);
        let mut challenges = NormLogupChallenges {
            beta,
            gamma,
            lambda: ext3(199),
            rho: ext3(211),
            kappa: ext3(223),
            eta: Field64_3::from(5u64),
            xi: Field64_3::from(7u64),
        };
        let tau = vec![ext3(227), ext3(229), ext3(233)];
        let point = vec![ext3(239), ext3(241), ext3(251)];
        let (wires, sigma, k_is, subgroup, helpers) = honest_tables(tau.len(), 2, beta, gamma);
        let routed_wires = wires
            .iter()
            .map(|column| evaluate_base_column(column, &point))
            .collect::<Vec<_>>();
        let sigmas = (0..2)
            .map(|column| {
                evaluate_base_column(
                    &sigma.iter().map(|row| row[column]).collect::<Vec<_>>(),
                    &point,
                )
            })
            .collect::<Vec<_>>();
        let inverse_identity = helpers
            .identity
            .iter()
            .map(|column| evaluate_base_column(column, &point))
            .collect::<Vec<_>>();
        let inverse_sigma = helpers
            .sigma
            .iter()
            .map(|column| evaluate_base_column(column, &point))
            .collect::<Vec<_>>();
        let subgroup_eval = evaluate_base_column(&subgroup, &point);
        let public_inputs = vec![
            F::from_canonical_u64(13),
            F::from_canonical_u64(17),
            F::from_canonical_u64(19),
        ];
        let ordered_map = vec![(1usize, 0usize), (1, 0), (6, 1)];

        let terminal =
            |challenge_set: NormLogupChallenges, inputs: &[F], map: &[(usize, usize)]| {
                evaluate_joint_norm_logup_terminal_with_public_inputs(
                    &tau,
                    &point,
                    &routed_wires,
                    &sigmas,
                    &inverse_identity,
                    &inverse_sigma,
                    subgroup_eval,
                    &k_is,
                    challenge_set,
                    inputs,
                    map,
                )
            };
        let base = evaluate_joint_norm_logup_terminal(
            &tau,
            &point,
            &routed_wires,
            &sigmas,
            &inverse_identity,
            &inverse_sigma,
            subgroup_eval,
            &k_is,
            challenges,
        );

        let eq_row = |row: usize| {
            point
                .iter()
                .enumerate()
                .map(|(variable, &coordinate)| {
                    if (row >> variable) & 1 == 0 {
                        Field64_3::ONE - coordinate
                    } else {
                        coordinate
                    }
                })
                .product::<Field64_3>()
        };
        let mut expected_binding = Field64_3::ZERO;
        let mut eta_power = Field64_3::ONE;
        for (&pi, &(row, column)) in public_inputs.iter().zip(&ordered_map) {
            expected_binding +=
                eta_power * eq_row(row) * (routed_wires[column] - embed_plonky_base(pi));
            eta_power *= challenges.eta;
        }
        assert_eq!(
            terminal(challenges, &public_inputs, &ordered_map) - base,
            challenges.xi * expected_binding
        );

        let reordered_map = vec![ordered_map[2], ordered_map[0], ordered_map[1]];
        assert_ne!(
            terminal(challenges, &public_inputs, &ordered_map),
            terminal(challenges, &public_inputs, &reordered_map),
            "eta powers must follow PI/map order"
        );
        assert_ne!(
            terminal(challenges, &public_inputs, &ordered_map),
            terminal(challenges, &public_inputs[..2], &ordered_map[..2]),
            "duplicate entries are terms, not a set"
        );

        challenges.eta = Field64_3::ZERO;
        assert_eq!(
            terminal(challenges, &public_inputs, &ordered_map),
            terminal(challenges, &public_inputs[..1], &ordered_map[..1]),
            "eta=0 is exactly the charged event that hides all later PI terms"
        );
        challenges.eta = Field64_3::from(5u64);
        challenges.xi = Field64_3::ZERO;
        assert_eq!(
            terminal(challenges, &public_inputs, &ordered_map),
            evaluate_joint_norm_logup_terminal(
                &tau,
                &point,
                &routed_wires,
                &sigmas,
                &inverse_identity,
                &inverse_sigma,
                subgroup_eval,
                &k_is,
                challenges,
            ),
            "xi=0 is exactly the charged event that hides the PI relation"
        );
    }
}
