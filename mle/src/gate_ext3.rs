//! Exact Plonky2 gate evaluation over the WHIR Goldilocks cubic extension.
//!
//! The committed wire and constant multilinear extensions are opened at a
//! point in `K = Fp3`.  Consequently every scalar operation in a Plonky2 gate
//! has to be evaluated in `K`; lifting the openings back to Goldilocks would
//! discard two coordinates and make the terminal identity unsound.  Plonky2's
//! inner extension degree is still two.  Such values are represented here as
//! pairs of `K` elements and are manipulated as the polynomial algebra
//! `K[t]/(t^2 - 7)`.  None of the supported gate formulas requires an inverse
//! in that algebra.

use anyhow::{bail, ensure, Context, Result};
use ark_ff::{AdditiveGroup, Field as ArkField};
use plonky2::gates::coset_interpolation::CosetInterpolationGate;
use plonky2::hash::hash_types::{HashOut, RichField};
use plonky2::hash::poseidon::{
    Poseidon, ALL_ROUND_CONSTANTS, HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, SPONGE_WIDTH,
};
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2_field::extension::Extendable;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::interpolation::barycentric_weights;
use plonky2_field::types::{Field as PlonkyField, Field64, PrimeField64};
use whir::algebra::fields::Field64_3;

use crate::proof_v2::GateInfoV2;
use crate::vk_v2::collect_gate_info_v2;

type K = Field64_3;

const INNER_EXTENSION_DEGREE: usize = 2;
const INNER_EXTENSION_NONRESIDUE: u64 = 7;
const UNUSED_SELECTOR: u64 = u32::MAX as u64;
const POSEIDON_CONSTRAINTS: usize = 123;
const POSEIDON_WIRES: usize = 135;

/// Parameters prevalidated once before the gate sumcheck hot loop.
///
/// Fields are deliberately private: callers cannot manufacture a context that
/// bypasses the exact comparison with `CommonCircuitData` performed by
/// [`validate_gate_ext3_context`].
#[derive(Clone, Debug)]
pub struct GateExt3Context {
    gates: Vec<ValidatedGate>,
    num_selectors: usize,
    num_constants: usize,
    num_gate_constraints: usize,
    num_wires: usize,
}

#[derive(Clone, Debug)]
struct ValidatedGate {
    info: GateInfoV2,
    coset: Option<CosetData>,
}

#[derive(Clone, Debug)]
struct CosetData {
    domain: Vec<K>,
    weights: Vec<K>,
    num_intermediates: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Ext2 {
    c0: K,
    c1: K,
}

impl Ext2 {
    const ZERO: Self = Self {
        c0: K::ZERO,
        c1: K::ZERO,
    };
    const ONE: Self = Self {
        c0: K::ONE,
        c1: K::ZERO,
    };

    #[inline]
    fn from_slice(values: &[K], start: usize) -> Self {
        Self {
            c0: values[start],
            c1: values[start + 1],
        }
    }

    #[inline]
    fn scalar_mul(self, scalar: K) -> Self {
        Self {
            c0: self.c0 * scalar,
            c1: self.c1 * scalar,
        }
    }

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
        }
    }

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
        }
    }

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let nonresidue = k_u64(INNER_EXTENSION_NONRESIDUE);
        Self {
            c0: self.c0 * rhs.c0 + nonresidue * self.c1 * rhs.c1,
            c1: self.c0 * rhs.c1 + self.c1 * rhs.c0,
        }
    }

    #[inline]
    fn push_to(self, output: &mut Vec<K>) {
        output.push(self.c0);
        output.push(self.c1);
    }
}

#[inline]
fn k_u64(value: u64) -> K {
    K::from(value)
}

#[inline]
fn k_usize(value: usize) -> Result<K> {
    Ok(k_u64(
        u64::try_from(value).context("gate integer does not fit u64")?,
    ))
}

#[inline]
fn checked_add(a: usize, b: usize, what: &str) -> Result<usize> {
    a.checked_add(b)
        .with_context(|| format!("{what} overflows usize"))
}

#[inline]
fn checked_mul(a: usize, b: usize, what: &str) -> Result<usize> {
    a.checked_mul(b)
        .with_context(|| format!("{what} overflows usize"))
}

fn require_zero_params(info: &GateInfoV2) -> Result<()> {
    ensure!(
        info.num_or_consts == 0 && info.param2 == 0 && info.param3 == 0,
        "gate {} has non-zero parameters reserved for this gate family",
        info.gate_id
    );
    Ok(())
}

fn require_aux_params_zero(info: &GateInfoV2) -> Result<()> {
    ensure!(
        info.param2 == 0 && info.param3 == 0,
        "gate {} has non-zero unused auxiliary parameters",
        info.gate_id
    );
    Ok(())
}

fn validate_gate_shape(
    info: &GateInfoV2,
    num_wires: usize,
    num_selectors: usize,
    num_constants: usize,
) -> Result<Option<CosetData>> {
    let n = usize::from(info.num_or_consts);
    let (expected_constraints, required_wires, required_local_constants, coset) = match info.gate_id
    {
        0 => {
            require_zero_params(info)?;
            (0, 0, 0, None)
        }
        1 => {
            require_aux_params_zero(info)?;
            (n, n, n, None)
        }
        2 => {
            require_zero_params(info)?;
            (4, 4, 0, None)
        }
        3 => {
            require_aux_params_zero(info)?;
            (n, checked_mul(4, n, "ArithmeticGate wire count")?, 2, None)
        }
        4 => {
            require_zero_params(info)?;
            (POSEIDON_CONSTRAINTS, POSEIDON_WIRES, 0, None)
        }
        5 => {
            require_zero_params(info)?;
            (2 * SPONGE_WIDTH, 4 * SPONGE_WIDTH, 0, None)
        }
        6 => {
            require_aux_params_zero(info)?;
            (
                checked_mul(
                    INNER_EXTENSION_DEGREE,
                    n,
                    "ArithmeticExtensionGate constraints",
                )?,
                checked_mul(
                    4 * INNER_EXTENSION_DEGREE,
                    n,
                    "ArithmeticExtensionGate wires",
                )?,
                2,
                None,
            )
        }
        7 => {
            require_aux_params_zero(info)?;
            (
                checked_mul(INNER_EXTENSION_DEGREE, n, "MulExtensionGate constraints")?,
                checked_mul(3 * INNER_EXTENSION_DEGREE, n, "MulExtensionGate wires")?,
                1,
                None,
            )
        }
        8 => {
            require_aux_params_zero(info)?;
            ensure!(n > 0, "ExponentiationGate requires at least one power bit");
            (
                checked_add(n, 1, "ExponentiationGate constraints")?,
                checked_add(
                    checked_mul(2, n, "ExponentiationGate wires")?,
                    2,
                    "ExponentiationGate wires",
                )?,
                0,
                None,
            )
        }
        9 => {
            ensure!(info.param3 == 0, "BaseSumGate has non-zero unused param3");
            let base = usize::from(info.param2);
            ensure!(
                matches!(base, 2 | 3 | 4 | 5 | 6 | 7 | 8 | 16 | 32 | 64 | 128 | 256),
                "BaseSumGate base {base} is not structurally supported"
            );
            (
                checked_add(n, 1, "BaseSumGate constraints")?,
                checked_add(n, 1, "BaseSumGate wires")?,
                0,
                None,
            )
        }
        10 => {
            require_aux_params_zero(info)?;
            ensure!(n > 0, "ReducingGate requires at least one coefficient");
            (
                checked_mul(2, n, "ReducingGate constraints")?,
                checked_add(
                    4,
                    checked_mul(3, n, "ReducingGate wires")?,
                    "ReducingGate wires",
                )?,
                0,
                None,
            )
        }
        11 => {
            require_aux_params_zero(info)?;
            ensure!(
                n > 0,
                "ReducingExtensionGate requires at least one coefficient"
            );
            (
                checked_mul(2, n, "ReducingExtensionGate constraints")?,
                checked_add(
                    4,
                    checked_mul(4, n, "ReducingExtensionGate wires")?,
                    "ReducingExtensionGate wires",
                )?,
                0,
                None,
            )
        }
        12 => {
            let bits = n;
            let copies = usize::from(info.param2);
            let extra = usize::from(info.param3);
            ensure!(bits > 0, "RandomAccessGate requires at least one index bit");
            ensure!(copies > 0, "RandomAccessGate requires at least one copy");
            let vec_size = 1usize
                .checked_shl(
                    u32::try_from(bits).context("RandomAccessGate bit count does not fit u32")?,
                )
                .context("RandomAccessGate vector size overflows usize")?;
            let copy_routed = checked_add(2, vec_size, "RandomAccessGate routed wires")?;
            let routed = checked_add(
                checked_mul(copy_routed, copies, "RandomAccessGate routed wires")?,
                extra,
                "RandomAccessGate routed wires",
            )?;
            let required_wires = checked_add(
                routed,
                checked_mul(copies, bits, "RandomAccessGate bit wires")?,
                "RandomAccessGate wires",
            )?;
            let expected_constraints = checked_add(
                checked_mul(
                    copies,
                    checked_add(bits, 2, "RandomAccessGate constraints")?,
                    "RandomAccessGate constraints",
                )?,
                extra,
                "RandomAccessGate constraints",
            )?;
            (expected_constraints, required_wires, extra, None)
        }
        13 => {
            ensure!(
                info.param3 == 0,
                "CosetInterpolationGate has non-zero unused param3"
            );
            let subgroup_bits = n;
            let degree = usize::from(info.param2);
            ensure!(
                (1..=5).contains(&subgroup_bits),
                "CosetInterpolationGate subgroup_bits={subgroup_bits} is outside the audited Solidity table range 1..=5"
            );
            let points = 1usize << subgroup_bits;
            ensure!(
                degree >= 2,
                "CosetInterpolationGate degree must be at least two"
            );
            ensure!(
                degree <= points,
                "CosetInterpolationGate degree exceeds its subgroup size"
            );
            let num_intermediates = (points - 2) / (degree - 1);
            let expected_constraints = checked_add(
                4,
                checked_mul(4, num_intermediates, "CosetInterpolationGate constraints")?,
                "CosetInterpolationGate constraints",
            )?;
            let required_wires = checked_add(
                checked_add(
                    7,
                    checked_mul(2, points, "CosetInterpolationGate wires")?,
                    "CosetInterpolationGate wires",
                )?,
                checked_mul(4, num_intermediates, "CosetInterpolationGate wires")?,
                "CosetInterpolationGate wires",
            )?;

            let base_domain = GoldilocksField::two_adic_subgroup(subgroup_bits);
            let base_weights = barycentric_weights(
                &base_domain
                    .iter()
                    .copied()
                    .map(|x| (x, GoldilocksField::ZERO))
                    .collect::<Vec<_>>(),
            );
            let domain = base_domain
                .iter()
                .map(|x| k_u64(x.to_canonical_u64()))
                .collect();
            let weights = base_weights
                .iter()
                .map(|x| k_u64(x.to_canonical_u64()))
                .collect();
            (
                expected_constraints,
                required_wires,
                0,
                Some(CosetData {
                    domain,
                    weights,
                    num_intermediates,
                }),
            )
        }
        unsupported => bail!("unsupported Plonky2 gate id {unsupported}"),
    };

    ensure!(
        usize::from(info.num_constraints) == expected_constraints,
        "gate {} declares {} constraints, exact evaluator requires {expected_constraints}",
        info.gate_id,
        info.num_constraints
    );
    ensure!(
        required_wires <= num_wires,
        "gate {} requires {required_wires} wires, circuit has {num_wires}",
        info.gate_id
    );
    let constants_end = checked_add(
        num_selectors,
        required_local_constants,
        "gate local-constant range",
    )?;
    ensure!(
        constants_end <= num_constants,
        "gate {} requires {required_local_constants} local constants after {num_selectors} selectors, circuit has {num_constants} total constants",
        info.gate_id
    );
    Ok(coset)
}

/// Validate and cache the exact gate configuration once before sumcheck.
pub fn validate_gate_ext3_context<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    gate_infos: &[GateInfoV2],
) -> Result<GateExt3Context> {
    ensure!(
        D == INNER_EXTENSION_DEGREE,
        "Fp3 gate evaluator supports Plonky2 inner extension degree two only"
    );
    ensure!(
        F::ORDER == GoldilocksField::ORDER,
        "Fp3 gate evaluator requires the Goldilocks base field"
    );
    ensure!(
        common_data.luts.is_empty() && common_data.num_lookup_selectors == 0,
        "lookup gates/selectors are not supported by the Fp3 terminal evaluator"
    );
    ensure!(!gate_infos.is_empty(), "gate metadata must not be empty");

    let canonical =
        collect_gate_info_v2(common_data).context("failed to derive canonical v2 gate metadata")?;
    ensure!(
        canonical == gate_infos,
        "provided gate metadata differs from CommonCircuitData"
    );

    let num_selectors = common_data.selectors_info.num_selectors();
    ensure!(num_selectors > 0, "circuit has no selector polynomial");
    ensure!(
        common_data.num_constants >= num_selectors,
        "circuit constant count is smaller than selector count"
    );

    let mut gates = Vec::with_capacity(gate_infos.len());
    for (index, info) in gate_infos.iter().copied().enumerate() {
        ensure!(
            usize::from(info.gate_row_index) == index,
            "gate metadata row {} is out of order at position {index}",
            info.gate_row_index
        );
        let selector = usize::from(info.selector_index);
        ensure!(
            selector < num_selectors,
            "gate {index} selector index is out of bounds"
        );
        let group_start = usize::from(info.group_start);
        let group_end = usize::from(info.group_end);
        ensure!(
            group_start < group_end && (group_start..group_end).contains(&index),
            "gate {index} has a malformed selector-group range"
        );
        let filter_degree = checked_add(
            group_end - group_start - 1,
            usize::from(num_selectors > 1),
            "selector-filter degree",
        )?;
        let filtered_gate_degree = checked_add(
            common_data.gates[index].0.degree(),
            filter_degree,
            "filtered gate degree",
        )?;
        let reviewed_degree_bound = checked_add(
            common_data.quotient_degree_factor,
            1,
            "reviewed filtered-gate degree bound",
        )?;
        ensure!(
            filtered_gate_degree <= reviewed_degree_bound,
            "gate row {index} has filtered degree {filtered_gate_degree}, exceeding the reviewed bound {reviewed_degree_bound}; multiplying by eq would exceed quotient_degree_factor + 2"
        );
        let coset = validate_gate_shape(
            &info,
            common_data.config.num_wires,
            num_selectors,
            common_data.num_constants,
        )
        .with_context(|| format!("invalid metadata for gate row {index}"))?;
        if info.gate_id == 13 {
            let actual = common_data.gates[index]
                .0
                .as_any()
                .downcast_ref::<CosetInterpolationGate<F, D>>()
                .context("gate id 13 is not a CosetInterpolationGate")?;
            let domain = F::two_adic_subgroup(actual.subgroup_bits);
            let canonical_weights = barycentric_weights(
                &domain
                    .iter()
                    .copied()
                    .map(|x| (x, F::ZERO))
                    .collect::<Vec<_>>(),
            );
            ensure!(
                actual.barycentric_weights == canonical_weights,
                "CosetInterpolationGate row {index} carries non-canonical barycentric weights"
            );
        }
        gates.push(ValidatedGate { info, coset });
    }

    let max_constraints = gate_infos
        .iter()
        .map(|gate| usize::from(gate.num_constraints))
        .max()
        .context("gate metadata must not be empty")?;
    ensure!(
        max_constraints == common_data.num_gate_constraints,
        "num_gate_constraints is {}, exact maximum from gate metadata is {max_constraints}",
        common_data.num_gate_constraints
    );

    Ok(GateExt3Context {
        gates,
        num_selectors,
        num_constants: common_data.num_constants,
        num_gate_constraints: common_data.num_gate_constraints,
        num_wires: common_data.config.num_wires,
    })
}

/// Fail-closed convenience wrapper. Sumcheck provers should validate once and
/// call [`evaluate_gate_constraints_ext3_validated`] in their hot loop.
pub fn evaluate_gate_constraints_ext3<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    gate_infos: &[GateInfoV2],
    wires: &[K],
    constants: &[K],
    public_inputs_hash: &HashOut<F>,
) -> Result<Vec<K>> {
    let context = validate_gate_ext3_context(common_data, gate_infos)?;
    evaluate_gate_constraints_ext3_validated(&context, wires, constants, public_inputs_hash)
}

/// Evaluate all filtered gate constraints using a previously validated context.
pub fn evaluate_gate_constraints_ext3_validated<F: RichField>(
    context: &GateExt3Context,
    wires: &[K],
    constants: &[K],
    public_inputs_hash: &HashOut<F>,
) -> Result<Vec<K>> {
    ensure!(
        F::ORDER == GoldilocksField::ORDER,
        "Fp3 gate evaluator requires a Goldilocks public-input hash"
    );
    ensure!(
        wires.len() == context.num_wires,
        "gate wire opening count is {}, expected {}",
        wires.len(),
        context.num_wires
    );
    ensure!(
        constants.len() == context.num_constants,
        "gate constant opening count is {}, expected {}",
        constants.len(),
        context.num_constants
    );

    let public_hash = public_inputs_hash
        .elements
        .map(|element| k_u64(element.to_canonical_u64()));
    let mut accumulated = vec![K::ZERO; context.num_gate_constraints];
    let mut unfiltered = Vec::with_capacity(context.num_gate_constraints);
    for gate in &context.gates {
        unfiltered.clear();
        evaluate_unfiltered(
            gate,
            wires,
            constants,
            context.num_selectors,
            &public_hash,
            &mut unfiltered,
        )?;
        ensure!(
            unfiltered.len() == usize::from(gate.info.num_constraints),
            "gate {} evaluator emitted {} constraints, metadata requires {}",
            gate.info.gate_id,
            unfiltered.len(),
            gate.info.num_constraints
        );

        let selector = constants[usize::from(gate.info.selector_index)];
        let filter = compute_filter(&gate.info, selector, context.num_selectors > 1)?;
        for (slot, value) in unfiltered.iter().copied().enumerate() {
            accumulated[slot] += filter * value;
        }
    }
    Ok(accumulated)
}

/// Geometrically aggregate constraint slots as `sum_i alpha^i * c_i`.
pub fn aggregate_gate_constraints_ext3(constraints: &[K], alpha: K) -> K {
    let mut power = K::ONE;
    let mut combined = K::ZERO;
    for constraint in constraints {
        combined += power * constraint;
        power *= alpha;
    }
    combined
}

/// Validate, evaluate, and geometrically aggregate in one convenience call.
pub fn evaluate_gate_aggregation_ext3<F: RichField + Extendable<D>, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    gate_infos: &[GateInfoV2],
    wires: &[K],
    constants: &[K],
    public_inputs_hash: &HashOut<F>,
    alpha: K,
) -> Result<K> {
    let constraints = evaluate_gate_constraints_ext3(
        common_data,
        gate_infos,
        wires,
        constants,
        public_inputs_hash,
    )?;
    Ok(aggregate_gate_constraints_ext3(&constraints, alpha))
}

fn compute_filter(info: &GateInfoV2, selector: K, many_selectors: bool) -> Result<K> {
    let row = usize::from(info.gate_row_index);
    let start = usize::from(info.group_start);
    let end = usize::from(info.group_end);
    ensure!(
        start < end && (start..end).contains(&row),
        "malformed selector range"
    );
    let mut filter = K::ONE;
    for other in start..end {
        if other != row {
            filter *= k_usize(other)? - selector;
        }
    }
    if many_selectors {
        filter *= k_u64(UNUSED_SELECTOR) - selector;
    }
    Ok(filter)
}

fn evaluate_unfiltered(
    gate: &ValidatedGate,
    wires: &[K],
    constants: &[K],
    num_selectors: usize,
    public_hash: &[K; 4],
    output: &mut Vec<K>,
) -> Result<()> {
    let info = &gate.info;
    let local_constants = &constants[num_selectors..];
    match info.gate_id {
        0 => {}
        1 => eval_constant(
            wires,
            local_constants,
            usize::from(info.num_or_consts),
            output,
        ),
        2 => eval_public_input(wires, public_hash, output),
        3 => eval_arithmetic(
            wires,
            local_constants,
            usize::from(info.num_or_consts),
            output,
        ),
        4 => eval_poseidon(wires, output),
        5 => eval_poseidon_mds(wires, output),
        6 => eval_arithmetic_extension(
            wires,
            local_constants,
            usize::from(info.num_or_consts),
            output,
        ),
        7 => eval_mul_extension(
            wires,
            local_constants,
            usize::from(info.num_or_consts),
            output,
        ),
        8 => eval_exponentiation(wires, usize::from(info.num_or_consts), output),
        9 => eval_base_sum(
            wires,
            usize::from(info.num_or_consts),
            usize::from(info.param2),
            output,
        ),
        10 => eval_reducing(wires, usize::from(info.num_or_consts), false, output),
        11 => eval_reducing(wires, usize::from(info.num_or_consts), true, output),
        12 => eval_random_access(
            wires,
            local_constants,
            usize::from(info.num_or_consts),
            usize::from(info.param2),
            usize::from(info.param3),
            output,
        ),
        13 => eval_coset_interpolation(
            wires,
            usize::from(info.param2),
            gate.coset
                .as_ref()
                .context("validated coset gate is missing cached constants")?,
            output,
        ),
        unsupported => bail!("unsupported Plonky2 gate id {unsupported}"),
    }
    Ok(())
}

fn eval_constant(wires: &[K], constants: &[K], count: usize, output: &mut Vec<K>) {
    for i in 0..count {
        output.push(constants[i] - wires[i]);
    }
}

fn eval_public_input(wires: &[K], public_hash: &[K; 4], output: &mut Vec<K>) {
    for i in 0..4 {
        output.push(wires[i] - public_hash[i]);
    }
}

fn eval_arithmetic(wires: &[K], constants: &[K], count: usize, output: &mut Vec<K>) {
    let c0 = constants[0];
    let c1 = constants[1];
    for i in 0..count {
        let start = 4 * i;
        let computed = c0 * wires[start] * wires[start + 1] + c1 * wires[start + 2];
        output.push(wires[start + 3] - computed);
    }
}

#[inline]
fn pow7(value: K) -> K {
    let square = value.square();
    let fourth = square.square();
    value * square * fourth
}

fn poseidon_constant_layer(state: &mut [K; SPONGE_WIDTH], round: usize) {
    for i in 0..SPONGE_WIDTH {
        state[i] += k_u64(ALL_ROUND_CONSTANTS[i + SPONGE_WIDTH * round]);
    }
}

fn poseidon_mds_layer(state: &[K; SPONGE_WIDTH]) -> [K; SPONGE_WIDTH] {
    let mut result = [K::ZERO; SPONGE_WIDTH];
    for row in 0..SPONGE_WIDTH {
        for i in 0..SPONGE_WIDTH {
            result[row] += state[(i + row) % SPONGE_WIDTH]
                * k_u64(<GoldilocksField as Poseidon>::MDS_MATRIX_CIRC[i]);
        }
        result[row] += state[row] * k_u64(<GoldilocksField as Poseidon>::MDS_MATRIX_DIAG[row]);
    }
    result
}

fn poseidon_partial_first_constant_layer(state: &mut [K; SPONGE_WIDTH]) {
    for (i, value) in state.iter_mut().enumerate() {
        *value += k_u64(<GoldilocksField as Poseidon>::FAST_PARTIAL_FIRST_ROUND_CONSTANT[i]);
    }
}

fn poseidon_mds_partial_init(state: &[K; SPONGE_WIDTH]) -> [K; SPONGE_WIDTH] {
    let mut result = [K::ZERO; SPONGE_WIDTH];
    result[0] = state[0];
    for (row, state_value) in state.iter().copied().enumerate().skip(1) {
        for (column, result_value) in result.iter_mut().enumerate().skip(1) {
            *result_value += state_value
                * k_u64(
                    <GoldilocksField as Poseidon>::FAST_PARTIAL_ROUND_INITIAL_MATRIX[row - 1]
                        [column - 1],
                );
        }
    }
    result
}

fn poseidon_mds_partial_fast(state: &[K; SPONGE_WIDTH], round: usize) -> [K; SPONGE_WIDTH] {
    let state0 = state[0];
    let mut d = state0
        * k_u64(
            <GoldilocksField as Poseidon>::MDS_MATRIX_CIRC[0]
                + <GoldilocksField as Poseidon>::MDS_MATRIX_DIAG[0],
        );
    for (i, state_value) in state.iter().copied().enumerate().skip(1) {
        d += state_value
            * k_u64(<GoldilocksField as Poseidon>::FAST_PARTIAL_ROUND_W_HATS[round][i - 1]);
    }
    let mut result = [K::ZERO; SPONGE_WIDTH];
    result[0] = d;
    for i in 1..SPONGE_WIDTH {
        result[i] = state0
            * k_u64(<GoldilocksField as Poseidon>::FAST_PARTIAL_ROUND_VS[round][i - 1])
            + state[i];
    }
    result
}

fn eval_poseidon(wires: &[K], output: &mut Vec<K>) {
    const WIRE_SWAP: usize = 24;
    const START_DELTA: usize = 25;
    const START_FULL_0: usize = 29;
    const START_PARTIAL: usize = 65;
    const START_FULL_1: usize = 87;

    let swap = wires[WIRE_SWAP];
    output.push(swap * (swap - K::ONE));
    for i in 0..4 {
        let delta = wires[START_DELTA + i];
        output.push(swap * (wires[i + 4] - wires[i]) - delta);
    }

    let mut state = [K::ZERO; SPONGE_WIDTH];
    for i in 0..4 {
        let delta = wires[START_DELTA + i];
        state[i] = wires[i] + delta;
        state[i + 4] = wires[i + 4] - delta;
    }
    state[8..SPONGE_WIDTH].copy_from_slice(&wires[8..SPONGE_WIDTH]);

    let mut round_counter = 0;
    for round in 0..HALF_N_FULL_ROUNDS {
        poseidon_constant_layer(&mut state, round_counter);
        if round != 0 {
            for i in 0..SPONGE_WIDTH {
                let sbox_input = wires[START_FULL_0 + SPONGE_WIDTH * (round - 1) + i];
                output.push(state[i] - sbox_input);
                state[i] = sbox_input;
            }
        }
        for value in &mut state {
            *value = pow7(*value);
        }
        state = poseidon_mds_layer(&state);
        round_counter += 1;
    }

    poseidon_partial_first_constant_layer(&mut state);
    state = poseidon_mds_partial_init(&state);
    for round in 0..N_PARTIAL_ROUNDS {
        let sbox_input = wires[START_PARTIAL + round];
        output.push(state[0] - sbox_input);
        state[0] = pow7(sbox_input)
            + k_u64(<GoldilocksField as Poseidon>::FAST_PARTIAL_ROUND_CONSTANTS[round]);
        state = poseidon_mds_partial_fast(&state, round);
    }
    round_counter += N_PARTIAL_ROUNDS;

    for round in 0..HALF_N_FULL_ROUNDS {
        poseidon_constant_layer(&mut state, round_counter);
        for i in 0..SPONGE_WIDTH {
            let sbox_input = wires[START_FULL_1 + SPONGE_WIDTH * round + i];
            output.push(state[i] - sbox_input);
            state[i] = sbox_input;
        }
        for value in &mut state {
            *value = pow7(*value);
        }
        state = poseidon_mds_layer(&state);
        round_counter += 1;
    }

    for i in 0..SPONGE_WIDTH {
        output.push(state[i] - wires[SPONGE_WIDTH + i]);
    }
    debug_assert_eq!(round_counter, 2 * HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS);
}

fn eval_poseidon_mds(wires: &[K], output: &mut Vec<K>) {
    for row in 0..SPONGE_WIDTH {
        let mut computed = Ext2::ZERO;
        for i in 0..SPONGE_WIDTH {
            computed = computed.add(
                Ext2::from_slice(wires, 2 * ((i + row) % SPONGE_WIDTH))
                    .scalar_mul(k_u64(<GoldilocksField as Poseidon>::MDS_MATRIX_CIRC[i])),
            );
        }
        computed = computed.add(
            Ext2::from_slice(wires, 2 * row)
                .scalar_mul(k_u64(<GoldilocksField as Poseidon>::MDS_MATRIX_DIAG[row])),
        );
        Ext2::from_slice(wires, 2 * (SPONGE_WIDTH + row))
            .sub(computed)
            .push_to(output);
    }
}

fn eval_arithmetic_extension(wires: &[K], constants: &[K], count: usize, output: &mut Vec<K>) {
    for i in 0..count {
        let start = 8 * i;
        let multiplicand0 = Ext2::from_slice(wires, start);
        let multiplicand1 = Ext2::from_slice(wires, start + 2);
        let addend = Ext2::from_slice(wires, start + 4);
        let gate_output = Ext2::from_slice(wires, start + 6);
        let computed = multiplicand0
            .mul(multiplicand1)
            .scalar_mul(constants[0])
            .add(addend.scalar_mul(constants[1]));
        gate_output.sub(computed).push_to(output);
    }
}

fn eval_mul_extension(wires: &[K], constants: &[K], count: usize, output: &mut Vec<K>) {
    for i in 0..count {
        let start = 6 * i;
        let computed = Ext2::from_slice(wires, start)
            .mul(Ext2::from_slice(wires, start + 2))
            .scalar_mul(constants[0]);
        Ext2::from_slice(wires, start + 4)
            .sub(computed)
            .push_to(output);
    }
}

fn eval_exponentiation(wires: &[K], bits: usize, output: &mut Vec<K>) {
    let base = wires[0];
    let intermediate_start = 2 + bits;
    for i in 0..bits {
        let previous = if i == 0 {
            K::ONE
        } else {
            wires[intermediate_start + i - 1].square()
        };
        let current_bit = wires[bits - i];
        let computed = previous * (current_bit * base + (K::ONE - current_bit));
        output.push(computed - wires[intermediate_start + i]);
    }
    output.push(wires[1 + bits] - wires[intermediate_start + bits - 1]);
}

fn eval_base_sum(wires: &[K], limbs: usize, base: usize, output: &mut Vec<K>) {
    let base_k = k_u64(base as u64);
    let mut computed_sum = K::ZERO;
    for limb in wires[1..1 + limbs].iter().rev() {
        computed_sum = computed_sum * base_k + limb;
    }
    output.push(computed_sum - wires[0]);
    for limb in &wires[1..1 + limbs] {
        let mut range_check = K::ONE;
        for value in 0..base {
            range_check *= *limb - k_u64(value as u64);
        }
        output.push(range_check);
    }
}

fn eval_reducing(
    wires: &[K],
    coefficients: usize,
    extension_coefficients: bool,
    output: &mut Vec<K>,
) {
    let alpha = Ext2::from_slice(wires, 2);
    let mut accumulator = Ext2::from_slice(wires, 4);
    let coefficient_width = if extension_coefficients { 2 } else { 1 };
    let coefficient_start = 6;
    let accumulator_start = coefficient_start + coefficient_width * coefficients;
    for i in 0..coefficients {
        let coefficient = if extension_coefficients {
            Ext2::from_slice(wires, coefficient_start + 2 * i)
        } else {
            Ext2 {
                c0: wires[coefficient_start + i],
                c1: K::ZERO,
            }
        };
        let next = if i + 1 == coefficients {
            Ext2::from_slice(wires, 0)
        } else {
            Ext2::from_slice(wires, accumulator_start + 2 * i)
        };
        accumulator
            .mul(alpha)
            .add(coefficient)
            .sub(next)
            .push_to(output);
        accumulator = next;
    }
}

fn eval_random_access(
    wires: &[K],
    constants: &[K],
    bits: usize,
    copies: usize,
    extra_constants: usize,
    output: &mut Vec<K>,
) {
    let vector_size = 1usize << bits;
    let copy_width = 2 + vector_size;
    let routed_wires = copy_width * copies + extra_constants;
    for copy in 0..copies {
        let copy_start = copy_width * copy;
        let access_index = wires[copy_start];
        let claimed_element = wires[copy_start + 1];
        let bit_values = &wires[routed_wires + copy * bits..routed_wires + (copy + 1) * bits];
        for bit in bit_values {
            output.push(*bit * (*bit - K::ONE));
        }
        let reconstructed = bit_values
            .iter()
            .rev()
            .fold(K::ZERO, |accumulator, bit| accumulator.double() + bit);
        output.push(reconstructed - access_index);

        let mut list = wires[copy_start + 2..copy_start + 2 + vector_size].to_vec();
        for bit in bit_values {
            let half = list.len() / 2;
            for i in 0..half {
                let left = list[2 * i];
                let right = list[2 * i + 1];
                list[i] = left + *bit * (right - left);
            }
            list.truncate(half);
        }
        output.push(list[0] - claimed_element);
    }
    for i in 0..extra_constants {
        output.push(constants[i] - wires[copy_width * copies + i]);
    }
}

fn coset_partial_interpolate(
    domain: &[K],
    values: &[Ext2],
    weights: &[K],
    point: Ext2,
    mut evaluation: Ext2,
    mut product: Ext2,
) -> (Ext2, Ext2) {
    for ((domain_value, value), weight) in domain.iter().zip(values).zip(weights) {
        let term = point.sub(Ext2 {
            c0: *domain_value,
            c1: K::ZERO,
        });
        let weighted_value = value.scalar_mul(*weight);
        evaluation = evaluation.mul(term).add(weighted_value.mul(product));
        product = product.mul(term);
    }
    (evaluation, product)
}

fn eval_coset_interpolation(wires: &[K], degree: usize, data: &CosetData, output: &mut Vec<K>) {
    let points = data.domain.len();
    let evaluation_point = Ext2::from_slice(wires, 1 + 2 * points);
    let start_intermediates = 2 * points + 5;
    let shifted_point = Ext2::from_slice(wires, start_intermediates + 4 * data.num_intermediates);
    evaluation_point
        .sub(shifted_point.scalar_mul(wires[0]))
        .push_to(output);

    let values = (0..points)
        .map(|i| Ext2::from_slice(wires, 1 + 2 * i))
        .collect::<Vec<_>>();
    let (mut computed_evaluation, mut computed_product) = coset_partial_interpolate(
        &data.domain[..degree],
        &values[..degree],
        &data.weights[..degree],
        shifted_point,
        Ext2::ZERO,
        Ext2::ONE,
    );

    for i in 0..data.num_intermediates {
        let intermediate_evaluation = Ext2::from_slice(wires, start_intermediates + 2 * i);
        let intermediate_product = Ext2::from_slice(
            wires,
            start_intermediates + 2 * data.num_intermediates + 2 * i,
        );
        intermediate_evaluation
            .sub(computed_evaluation)
            .push_to(output);
        intermediate_product.sub(computed_product).push_to(output);

        let start = 1 + (degree - 1) * (i + 1);
        let end = (start + degree - 1).min(points);
        (computed_evaluation, computed_product) = coset_partial_interpolate(
            &data.domain[start..end],
            &values[start..end],
            &data.weights[start..end],
            shifted_point,
            intermediate_evaluation,
            intermediate_product,
        );
    }

    Ext2::from_slice(wires, 1 + 2 * (points + 1))
        .sub(computed_evaluation)
        .push_to(output);
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use ark_ff::{AdditiveGroup, Field as ArkField};
    use plonky2::gates::arithmetic_base::ArithmeticGate;
    use plonky2::gates::arithmetic_extension::ArithmeticExtensionGate;
    use plonky2::gates::base_sum::BaseSumGate;
    use plonky2::gates::constant::ConstantGate;
    use plonky2::gates::coset_interpolation::CosetInterpolationGate;
    use plonky2::gates::exponentiation::ExponentiationGate;
    use plonky2::gates::multiplication_extension::MulExtensionGate;
    use plonky2::gates::noop::NoopGate;
    use plonky2::gates::poseidon::PoseidonGate;
    use plonky2::gates::poseidon_mds::PoseidonMdsGate;
    use plonky2::gates::public_input::PublicInputGate;
    use plonky2::gates::random_access::RandomAccessGate;
    use plonky2::gates::reducing::ReducingGate;
    use plonky2::gates::reducing_extension::ReducingExtensionGate;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
    use plonky2::plonk::config::PoseidonGoldilocksConfig;
    use plonky2::plonk::vanishing_poly::evaluate_gate_constraints;
    use plonky2::plonk::vars::EvaluationVars;
    use plonky2_field::extension::quadratic::QuadraticExtension;
    use plonky2_field::extension::FieldExtension;
    use plonky2_field::types::{Field as PlonkyField, PrimeField64};
    use whir::algebra::fields::{Field64 as ArkGoldilocks, Field64_3};

    use super::*;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    fn all_supported_gate_common_data() -> CommonCircuitData<F, D> {
        let config = CircuitConfig::standard_recursion_config();
        let random_access = RandomAccessGate::<F, D>::new_from_config(&config, 2);
        let random_constants = random_access.num_extra_constants;
        let mut builder = CircuitBuilder::<F, D>::new(config);

        builder.add_gate(NoopGate, vec![]);
        builder.add_gate(ConstantGate::new(2), vec![F::from_canonical_u64(3)]);
        builder.add_gate(PublicInputGate, vec![]);
        builder.add_gate(
            ArithmeticGate { num_ops: 2 },
            vec![F::from_canonical_u64(5), F::from_canonical_u64(7)],
        );
        builder.add_gate(PoseidonGate::<F, D>::new(), vec![]);
        builder.add_gate(PoseidonMdsGate::<F, D>::new(), vec![]);
        builder.add_gate(
            ArithmeticExtensionGate::<D> { num_ops: 2 },
            vec![F::from_canonical_u64(11), F::from_canonical_u64(13)],
        );
        builder.add_gate(
            MulExtensionGate::<D> { num_ops: 2 },
            vec![F::from_canonical_u64(17)],
        );
        builder.add_gate(ExponentiationGate::<F, D>::new(3), vec![]);
        builder.add_gate(BaseSumGate::<2>::new(4), vec![]);
        builder.add_gate(ReducingGate::<D>::new(3), vec![]);
        builder.add_gate(ReducingExtensionGate::<D>::new(3), vec![]);
        builder.add_gate(
            random_access,
            vec![F::from_canonical_u64(19); random_constants],
        );
        builder.add_gate(
            CosetInterpolationGate::<F, D>::with_max_degree(4, 4),
            vec![],
        );

        builder.build::<C>().common
    }

    fn base_to_k(value: F) -> Field64_3 {
        Field64_3::from(value.to_canonical_u64())
    }

    #[test]
    fn base_embedded_ext3_matches_production_evaluator_for_all_supported_gates() {
        let common = all_supported_gate_common_data();
        let gate_infos = collect_gate_info_v2(&common).unwrap();
        assert_eq!(
            gate_infos
                .iter()
                .map(|gate| gate.gate_id)
                .collect::<BTreeSet<_>>(),
            (0u8..=13).collect(),
            "test circuit must exercise every supported gate id"
        );

        let wires_base = (0..common.config.num_wires)
            .map(|i| F::from_canonical_usize(31 + 7 * i))
            .collect::<Vec<_>>();
        let public_inputs_hash = HashOut {
            elements: [
                F::from_canonical_u64(101),
                F::from_canonical_u64(103),
                F::from_canonical_u64(107),
                F::from_canonical_u64(109),
            ],
        };

        let wires_extension: Vec<QuadraticExtension<F>> = wires_base
            .iter()
            .copied()
            .map(<QuadraticExtension<F> as FieldExtension<D>>::from_basefield)
            .collect();
        let context = validate_gate_ext3_context(&common, &gate_infos).unwrap();
        let wires_k = wires_base
            .iter()
            .copied()
            .map(base_to_k)
            .collect::<Vec<_>>();
        for target in &gate_infos {
            // Set the target selector to its gate row and every other selector
            // to UNUSED. This isolates one gate family at a time even when
            // several gates share the same constraint slots.
            let mut constants_base = (0..common.num_constants)
                .map(|i| F::from_canonical_usize(43 + 11 * i))
                .collect::<Vec<_>>();
            for selector in constants_base
                .iter_mut()
                .take(common.selectors_info.num_selectors())
            {
                *selector = F::from_canonical_u64(UNUSED_SELECTOR);
            }
            constants_base[usize::from(target.selector_index)] =
                F::from_canonical_u64(u64::from(target.gate_row_index));

            let constants_extension: Vec<QuadraticExtension<F>> = constants_base
                .iter()
                .copied()
                .map(<QuadraticExtension<F> as FieldExtension<D>>::from_basefield)
                .collect();
            let production = evaluate_gate_constraints::<F, D>(
                &common,
                EvaluationVars {
                    local_constants: &constants_extension,
                    local_wires: &wires_extension,
                    public_inputs_hash: &public_inputs_hash,
                },
            );
            let constants_k = constants_base
                .iter()
                .copied()
                .map(base_to_k)
                .collect::<Vec<_>>();
            let ours = evaluate_gate_constraints_ext3_validated(
                &context,
                &wires_k,
                &constants_k,
                &public_inputs_hash,
            )
            .unwrap();

            assert_eq!(ours.len(), production.len());
            for (slot, (ours, production)) in ours.iter().zip(&production).enumerate() {
                let components: [F; D] =
                    <QuadraticExtension<F> as FieldExtension<D>>::to_basefield_array(production);
                assert_eq!(
                    components[1],
                    F::ZERO,
                    "base-embedded gate {} escaped the base field at slot {slot}",
                    target.gate_id
                );
                assert_eq!(
                    *ours,
                    base_to_k(components[0]),
                    "Fp3 evaluator disagrees with production gate {} at slot {slot}",
                    target.gate_id
                );
            }
        }
    }

    #[test]
    fn non_base_openings_propagate_into_cubic_coordinates() {
        let common = all_supported_gate_common_data();
        let gate_infos = collect_gate_info_v2(&common).unwrap();
        let context = validate_gate_ext3_context(&common, &gate_infos).unwrap();
        let mut wires = (0..common.config.num_wires)
            .map(|i| Field64_3::from((i as u64) + 2))
            .collect::<Vec<_>>();
        let mut constants = (0..common.num_constants)
            .map(|i| Field64_3::from((i as u64) + 17))
            .collect::<Vec<_>>();
        for selector in constants.iter_mut().take(context.num_selectors) {
            *selector = Field64_3::from(UNUSED_SELECTOR);
        }
        let public_input_gate = gate_infos
            .iter()
            .find(|gate| gate.gate_id == 2)
            .expect("test circuit contains PublicInputGate");
        constants[usize::from(public_input_gate.selector_index)] =
            Field64_3::from(u64::from(public_input_gate.gate_row_index));
        wires[0] = Field64_3::new(
            ArkGoldilocks::from(5u64),
            ArkGoldilocks::from(7u64),
            ArkGoldilocks::from(11u64),
        );
        let constraints = evaluate_gate_constraints_ext3_validated(
            &context,
            &wires,
            &constants,
            &HashOut::<F>::ZERO,
        )
        .unwrap();
        assert!(
            constraints
                .iter()
                .any(|constraint| constraint.c1 != ArkGoldilocks::ZERO),
            "a non-base c1 opening must not be projected away"
        );
        assert!(
            constraints
                .iter()
                .any(|constraint| constraint.c2 != ArkGoldilocks::ZERO),
            "a non-base c2 opening must not be projected away"
        );
    }

    #[test]
    fn off_base_ext3_evaluation_commutes_with_frobenius_for_every_gate() {
        let common = all_supported_gate_common_data();
        let gate_infos = collect_gate_info_v2(&common).unwrap();
        let context = validate_gate_ext3_context(&common, &gate_infos).unwrap();
        let public_inputs_hash = HashOut {
            elements: [
                F::from_canonical_u64(131),
                F::from_canonical_u64(137),
                F::from_canonical_u64(139),
                F::from_canonical_u64(149),
            ],
        };
        let wires = (0..common.config.num_wires)
            .map(|i| {
                let seed = i as u64 + 2;
                Field64_3::new(
                    ArkGoldilocks::from(seed),
                    ArkGoldilocks::from(3 * seed + 1),
                    ArkGoldilocks::from(5 * seed + 2),
                )
            })
            .collect::<Vec<_>>();
        let local_constants = (0..common.num_constants)
            .map(|i| {
                let seed = i as u64 + 211;
                Field64_3::new(
                    ArkGoldilocks::from(seed),
                    ArkGoldilocks::from(7 * seed + 1),
                    ArkGoldilocks::from(11 * seed + 3),
                )
            })
            .collect::<Vec<_>>();

        let frobenius = |mut value: Field64_3| {
            value.frobenius_map_in_place(1);
            value
        };
        let frobenius_wires = wires.iter().copied().map(frobenius).collect::<Vec<_>>();

        for target in &gate_infos {
            let mut constants = local_constants.clone();
            for selector in constants.iter_mut().take(context.num_selectors) {
                *selector = Field64_3::from(UNUSED_SELECTOR);
            }
            constants[usize::from(target.selector_index)] =
                Field64_3::from(u64::from(target.gate_row_index));
            let expected = evaluate_gate_constraints_ext3_validated(
                &context,
                &wires,
                &constants,
                &public_inputs_hash,
            )
            .unwrap()
            .into_iter()
            .map(frobenius)
            .collect::<Vec<_>>();
            let frobenius_constants = constants.iter().copied().map(frobenius).collect::<Vec<_>>();
            let actual = evaluate_gate_constraints_ext3_validated(
                &context,
                &frobenius_wires,
                &frobenius_constants,
                &public_inputs_hash,
            )
            .unwrap();
            assert_eq!(
                actual, expected,
                "off-base Fp3 evaluation is not defined over Goldilocks for gate {}",
                target.gate_id
            );
        }
    }

    #[test]
    fn malformed_metadata_fails_before_evaluation() {
        let common = all_supported_gate_common_data();
        let mut gate_infos = collect_gate_info_v2(&common).unwrap();
        gate_infos[0].num_constraints ^= 1;
        assert!(validate_gate_ext3_context(&common, &gate_infos).is_err());

        let mut gate_infos = collect_gate_info_v2(&common).unwrap();
        gate_infos[0].gate_id = 255;
        assert!(validate_gate_ext3_context(&common, &gate_infos).is_err());

        let mut malformed_common = all_supported_gate_common_data();
        let canonical_gate_infos = collect_gate_info_v2(&malformed_common).unwrap();
        malformed_common.quotient_degree_factor = 0;
        let error = validate_gate_ext3_context(&malformed_common, &canonical_gate_infos)
            .expect_err("an understated round-degree bound must fail closed");
        assert!(
            error.to_string().contains("filtered degree"),
            "degree failure should identify the violated bound: {error:#}"
        );
    }
}
