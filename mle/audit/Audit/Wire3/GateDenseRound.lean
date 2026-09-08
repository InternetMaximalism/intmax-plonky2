import Audit.Wire3.GateTerminalBinding
import Audit.Wire3.OuterInterpolationTotal

/-!
# The gate prover's `current_round` end to end, and its round chain

Source: mle/src/sumcheck/gate_ext3_v2.rs, read in full (181 lines):
* `GateExt3ProverState` (43-53) and `new` (57-101): the three `ensure!`s at
  70-83 (`wires.len() == num_wires` / `constants.len() == num_constants`, every
  MLE's `num_vars == tau.len()`, and `degree == quotient_degree_factor + 2`),
  `eq: Ext3DenseMle::new(ext3_eq_evals(tau))` (95), empty `rounds`/`point`;
* `current_round` (105-140): the `num_vars > 0` ensure (106), `half =
  eq.evaluations.len()/2` (107), the `vec![ZERO; degree+1]` accumulator (108),
  the transposed grid loop (112-134) with the adjacent reads at `2*suffix` /
  `2*suffix+1` interpolated at `Field64_3::from(integer as u64)` (114-125), the
  validated gate evaluator and forward-power aggregate (126-132), then
  `ext3_evaluations_to_coefficients(&evaluations)` (136) and
  `coefficients[1..].to_vec()` (138);
* `bind_challenge` (142-161): the `non_constant.len() == degree` ensure
  (147-150), `bind_variable_in_place` on eq (151), on every wire (152-154) and
  every constant (155-157), then `rounds.push` (158) and `point.push` (159);
* `into_proof_and_point` (163-171): the `eq.num_vars == 0` ensure.
Interpolation is mle/src/sumcheck/coefficients.rs:180-238 through the adopted
`OuterInterpolation.interpolate` / `OuterInterpolationTotal`; it is NOT
re-proved here, only invoked at its adopted gate specialisation.

This is the gate counterpart of `Audit.Wire3.NormDenseRound` (norm lane) and of
`Audit.Wire3.OuterClaimChain.bound_endpoint_sum_is_round_value`. Everything
below the interpolation call is the ALREADY ADOPTED gate machinery, reused and
not re-implemented: `GateSlotRound.currentRoundGrid` /
`currentRoundEvaluations` / `grid_entries_are_suffix_sums` /
`configured_grid_executes` / `valid_source_half` for the grid,
`GateSuffixPolynomial.captureSlice` / `evalSlice` / `sumSuffixes` /
`currentRoundValue` / `captured_round_polynomial` for the per-integer suffix
sum, `GateTerminalBinding.ProverState` / `bindChallenge` / `bindTables` /
`ProverShape` / `bind_challenge_executes` / `intoProofAndPoint` for the state,
and `OuterInterpolationTotal.validated_gate_configuration_total` /
`total_sample_actual_outer_round` for interpolation totality.

What is added here:
1. `computeRound`: the WHOLE of `current_round` including the interpolation
   call and the dropped constant. `current_round_coefficients_shaped` proves
   the sent message has exactly `degree = quotientDegree+2` entries (the length
   `bind_challenge` re-checks) and `omitted_constant_coefficient` proves the
   dropped entry is the constant coefficient AND is exactly what the verifier's
   half-sum reconstruction recovers from the sent tail plus the endpoint sum.
2. `sent_round_evaluates_as_verifier`: with the endpoint sum as claim, the
   ACTUAL `Verifier.evaluateRound` on the sent coefficients reproduces the
   source round value at every challenge.
3. `Consistent`, `currentRound`, `bindChallenge`, `intoProofAndPoint` at state
   level, and `bound_endpoint_sum_is_round_value` /
   `bound_endpoint_sum_is_state_round_value` / `honest_chain_step`: the NEXT
   tables' `f'(0)+f'(1)` is the CURRENT round value at the drawn challenge.
   Every adjacent read the identity needs is proved in range from the table
   shape (`bound_affine_values_zero`/`_one`, `bound_eq_weight_zero`/`_one`,
   `cube_reads_bounded`); nothing is defaulted to cover a missing bound.
4. `cubeSum`: the eq-weighted all-gates aggregate summed over the Boolean cube,
   and `endpoint_sum_is_cube_sum`: a round's endpoint sum IS that cube sum.

Modelling notes and boundaries:
* EVERY theorem naming a prover state or its tables is HONEST-PROVER ONLY. No
  statement here says that a verifier-accepted transcript came from such a
  prover; no soundness, transcript, Fiat-Shamir, PCS/WHIR or extraction claim
  is made, and challenges are arbitrary field elements.
* "cube sum = 0" is NOT proved and is not claimed. `cubeSum` is defined so that
  a later module can state it; whether it vanishes is circuit truth, which is
  outside this model. The eq table's provenance from `tau` (`ext3_eq_evals`,
  26-39) is likewise NOT modelled: `eq` is a supplied table.
* `Element` and `Field64_3`/`Verifier.Ext3` are the same datum wrapped
  (`Element.toVerifier` / `NormPolynomial.lift` are mutually inverse by
  definition); `gridElements` is that type adapter, not a computation.
* `suffixElement` / `rowElement` totalise an `Option` whose `some`-ness is
  separately proved from `Gates.validateConfiguration` and the table shape.
  They are NOT zero-default reads standing in for source bounds; the actual
  table reads keep the adopted `getD` form of `GateSuffixPolynomial`, and their
  in-range proofs are the explicit theorems listed above.
* `ProverShape` / `TableShape` / `Consistent` are the constructor's ensures as
  caller invariants; no runtime guard the source lacks is added, and none of
  the source's own ensures is removed (each is `none` in the model).
* Not modelled here: `ext3_eq_evals`, the base-to-Ext3 `from_base`
  transposition, the origin of `alpha` and of the public-inputs hash, the
  `degree == quotient_degree_factor + 2` ensure itself (it is the hypothesis
  `s.degree = c.quotientDegree+2` of `Consistent`), Rust
  compiler/word/memory/panic refinement, circuit truth, and PCS/Fiat-Shamir
  soundness.
-/
namespace Audit.Wire3.GateDenseRound
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial
open Audit.Wire3.GateAggregatePolynomial Audit.Wire3.GateSuffixPolynomial
open Audit.Wire3.GateSlotRound Audit.Wire3.GateTerminalBinding

/-! ## Field-level helpers -/

theorem add_lift (a b : Element) : Verifier.add a.toVerifier b.toVerifier = (a+b).toVerifier := rfl

theorem map_lift_getD (vs : List Verifier.Ext3) (i : Nat) :
    (vs.map NormPolynomial.lift).getD i 0 = NormPolynomial.lift (vs.getD i Verifier.zero) := by
  induction vs generalizing i with
  | nil => rfl
  | cons v vs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.map_cons,List.getD_cons_succ] using ih i

theorem interleave_sum (g : Nat → Element) (M : Nat) :
    ((List.range M).map (fun s => g (2*s))).sum + ((List.range M).map (fun s => g (2*s+1))).sum =
      ((List.range (2*M)).map g).sum := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [show 2*(M+1) = 2*M+1+1 by ring,List.range_succ,List.range_succ,List.range_succ]
      simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
        List.sum_nil,add_zero]
      rw [← ih]
      ring

theorem affine_weight_at_zero (a b : Element) : affineWeight a b 0 = a.toVerifier :=
  (affine_actual_arithmetic a b 0).symm.trans (affine_at_zero a b)

theorem affine_weight_at_one (a b : Element) : affineWeight a b 1 = b.toVerifier :=
  (affine_actual_arithmetic a b 1).symm.trans (affine_at_one a b)

/-! ## The per-integer suffix sum as a field sum -/

/-- The value of one captured Boolean suffix as a field element. The `none`
branch is unreachable under the hypotheses of every theorem below: with
`Gates.validateConfiguration` and the slice widths, `evalSlice` is total
(`slice_polynomial_complete`). This totalises an `Option` whose `some`-ness is
separately proved; it is NOT a zero-default read of a source table. -/
def suffixElement (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (t : Tables) (s : Nat) : Element :=
  match evalSlice c gates publicHash alpha x (captureSlice t s) with
  | some v => NormPolynomial.lift v
  | none => 0

theorem suffix_element_defined (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (t : Tables) (half s : Nat)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c half t) :
    evalSlice c gates publicHash alpha x (captureSlice t s) =
      some (suffixElement c gates publicHash alpha x t s).toVerifier := by
  obtain ⟨p,_,_,he⟩ := slice_polynomial_complete c gates publicHash alpha (captureSlice t s) hv
    (captured_slice_widths c t half s ht)
  have h := he x
  unfold suffixElement
  rw [h]
  rfl

/-- The round value of the whole suffix sweep at `x`, as a field element. -/
def roundElement (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (t : Tables) (half : Nat) : Element :=
  ((List.range half).map (suffixElement c gates publicHash alpha x t)).sum

theorem sum_suffixes_indexed (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (t : Tables) (half : Nat)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c half t)
    (indices : List Nat) : ∀ acc : Element,
    sumSuffixes c gates publicHash alpha x (indices.map (captureSlice t)) acc.toVerifier =
      some (acc + (indices.map (suffixElement c gates publicHash alpha x t)).sum).toVerifier := by
  induction indices with
  | nil => intro acc; simp [sumSuffixes]
  | cons s rest ih =>
      intro acc
      have hs := suffix_element_defined c gates publicHash alpha x t half s hv ht
      simp only [List.map_cons,sumSuffixes,hs,Option.bind_eq_bind,Option.some_bind,add_lift]
      rw [ih (acc + suffixElement c gates publicHash alpha x t s)]
      congr 2
      simp only [List.sum_cons]
      ring

/-- The adopted `currentRoundValue` (the per-integer suffix-first sum of
gate_ext3_v2.rs:112-132) is total on a shaped table and equals `roundElement`. -/
theorem current_round_value_sum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (t : Tables) (half : Nat)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c half t) :
    currentRoundValue c gates publicHash alpha x t half =
      some (roundElement c gates publicHash alpha x t half).toVerifier := by
  have h := sum_suffixes_indexed c gates publicHash alpha x t half hv ht (List.range half) 0
  rw [zero_exact] at h
  simpa only [currentRoundValue,captureSuffixes,roundElement,zero_add] using h

/-- One fixed polynomial of degree at most `quotientDegree+2` whose evaluation
at every field point is the round value. -/
theorem round_element_polynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (half : Nat)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c half t) :
    ∃ p : P, p.natDegree ≤ c.quotientDegree+2 ∧
      ∀ x, p.eval x = roundElement c gates publicHash alpha x t half := by
  obtain ⟨p,_,hd,he⟩ := captured_round_polynomial c gates publicHash alpha t half hv ht
  refine ⟨p,hd,fun x => ?_⟩
  have h1 := he x
  rw [current_round_value_sum c gates publicHash alpha x t half hv ht] at h1
  exact (element_eq _ _ (Option.some.inj h1)).symm

/-! ## (1) `current_round` end to end: grid, interpolation, dropped constant -/

/-- `ext3_evaluations_to_coefficients(&evaluations)` (136) consumes the
accumulator's `Field64_3` entries. `Element` is the same datum wrapped
(`Element.toVerifier` and `NormPolynomial.lift` are mutually inverse by
definition), so this is a type adapter, not a computation. -/
def gridElements (evaluations : List Verifier.Ext3) : List Element :=
  evaluations.map NormPolynomial.lift

/-- `current_round` 105-139 in full: the `num_vars > 0` ensure (106), the
grid (107-134) through the adopted `GateSlotRound.currentRoundEvaluations`,
the interpolation call (136) through the adopted
`OuterInterpolation.interpolate`, and the `coefficients[1..].to_vec()` drop
(138). `none` is the ensure, an evaluator failure, or an interpolation
pivot/empty-input failure. -/
def computeRound (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (wires constants : List (List Element)) (eq : DenseMleIndexed.State) (degree : Nat) :
    Option (List Element) := do
  let evaluations ← currentRoundEvaluations c gates publicHash alpha wires constants eq degree
  let coefficients ← OuterInterpolation.interpolate (gridElements evaluations)
  pure coefficients.tail

theorem compute_round_after_completion (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (wires constants : List (List Element)) (eq : DenseMleIndexed.State) (degree : Nat)
    (h : eq.numVars = 0) : computeRound c gates publicHash alpha wires constants eq degree = none := by
  simp only [computeRound,constant_round_rejected c gates publicHash alpha wires constants eq degree h,
    Option.bind_eq_bind,Option.none_bind]

theorem compute_round_exact (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (wires constants : List (List Element)) (eq : DenseMleIndexed.State) (degree : Nat)
    (evaluations : List Verifier.Ext3) (coefficients : List Element)
    (he : currentRoundEvaluations c gates publicHash alpha wires constants eq degree = some evaluations)
    (hi : OuterInterpolation.interpolate (gridElements evaluations) = some coefficients) :
    computeRound c gates publicHash alpha wires constants eq degree = some coefficients.tail := by
  simp only [computeRound,he,hi,Option.bind_eq_bind,Option.some_bind,Option.pure_def]

/-- The executed grid is exactly the `degree+1` point-value sample of the ONE
round polynomial at the source's integer grid points. -/
theorem grid_is_polynomial_sample (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (wires constants : List (List Element)) (eq : DenseMleIndexed.State) (degree : Nat)
    (hv : Gates.validateConfiguration c gates = some ()) (hvalid : DenseMleIndexed.Valid eq)
    (hn : 0 < eq.numVars)
    (ht : TableShape c (2^(eq.numVars-1)) (tablesOf wires constants eq)) :
    ∃ p : P, p.natDegree ≤ c.quotientDegree+2 ∧
      (∀ x, p.eval x =
        roundElement c gates publicHash alpha x (tablesOf wires constants eq) (2^(eq.numVars-1))) ∧
      ∃ evaluations, currentRoundEvaluations c gates publicHash alpha wires constants eq degree =
          some evaluations ∧ evaluations.length = degree+1 ∧
        gridElements evaluations = OuterInterpolation.samplePolynomial p degree := by
  obtain ⟨p,hd,hp⟩ := round_element_polynomial c gates publicHash alpha
    (tablesOf wires constants eq) (2^(eq.numVars-1)) hv ht
  rw [positive_round_exact c gates publicHash alpha wires constants eq degree hn,
    (valid_source_half eq hvalid hn).1]
  obtain ⟨evaluations,hgrid⟩ := configured_grid_executes c gates publicHash alpha
    (tablesOf wires constants eq) degree (2^(eq.numVars-1)) hv ht
  obtain ⟨hlen,hcells⟩ := grid_entries_are_suffix_sums c gates publicHash alpha
    (tablesOf wires constants eq) degree (2^(eq.numVars-1)) evaluations hv hgrid
  refine ⟨p,hd,hp,evaluations,hgrid,hlen,?_⟩
  apply List.ext_get (by rw [gridElements,List.length_map,hlen,OuterInterpolation.sample_count])
  intro i h1 h2
  rw [← List.getD_eq_get _ 0 h1,← List.getD_eq_get _ 0 h2]
  have hi : i ≤ degree := by
    rw [gridElements,List.length_map,hlen] at h1
    omega
  have hc := hcells i hi
  rw [current_round_value_sum c gates publicHash alpha (gridPoint i)
    (tablesOf wires constants eq) (2^(eq.numVars-1)) hv ht] at hc
  have hc' : evaluations.getD i Verifier.zero =
      (roundElement c gates publicHash alpha (i : Element) (tablesOf wires constants eq)
        (2^(eq.numVars-1))).toVerifier := (Option.some.inj hc).symm
  rw [gridElements,map_lift_getD,hc',OuterInterpolation.sample_value p degree i hi,hp (i : Element)]
  rfl

/-- gate_ext3_v2.rs:80-83 forces `degree = quotient_degree_factor + 2`, and the
validated configuration keeps that below the field size, so interpolation at
the `degree+1` distinct integer nodes is total. -/
theorem gate_degree_below_modulus (c : Gates.Config) (gates : List Gates.GateInfo)
    (hv : Gates.validateConfiguration c gates = some ()) :
    c.quotientDegree+2 < Arithmetic.modulus := by
  have hq := OuterInterpolation.actual_gate_configuration_implies_profile c gates hv
  have h := hq.2
  unfold Arithmetic.modulus
  omega

/-- (1) The whole of `current_round` at the constructor's reviewed degree:
the interpolated coefficient list IS the round polynomial, the sent message is
its tail with exactly `degree = quotientDegree+2` entries (the length
`bind_challenge` 147-150 re-checks), and the DROPPED entry is the constant
coefficient. -/
theorem current_round_coefficients_shaped (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (wires constants : List (List Element)) (eq : DenseMleIndexed.State)
    (hv : Gates.validateConfiguration c gates = some ()) (hvalid : DenseMleIndexed.Valid eq)
    (hn : 0 < eq.numVars)
    (ht : TableShape c (2^(eq.numVars-1)) (tablesOf wires constants eq)) :
    ∃ (p : P) (coefficients : List Element),
      (∀ x, p.eval x =
        roundElement c gates publicHash alpha x (tablesOf wires constants eq) (2^(eq.numVars-1))) ∧
      WhirPolynomial.ofCoefficients coefficients = p ∧
      computeRound c gates publicHash alpha wires constants eq (c.quotientDegree+2) =
        some coefficients.tail ∧
      coefficients.tail.length = c.quotientDegree+2 ∧
      coefficients.getD 0 0 = p.coeff 0 := by
  obtain ⟨p,hd,hp,evaluations,he,_,hsample⟩ := grid_is_polynomial_sample c gates publicHash alpha
    wires constants eq (c.quotientDegree+2) hv hvalid hn ht
  obtain ⟨coefficients,hi,hpoly,hlen⟩ :=
    OuterInterpolationTotal.validated_gate_configuration_total p c gates hv hd
  refine ⟨p,coefficients,hp,hpoly,?_,hlen,?_⟩
  · exact compute_round_exact c gates publicHash alpha wires constants eq _ evaluations coefficients he
      (by rw [hsample]; exact hi)
  · rw [← hpoly,WhirPolynomial.coefficient_exact]

/-- (1) The gate analogue of `NormDenseRound.omitted_constant_coefficient`: the
entry the source drops at 138 is the constant coefficient of the round
polynomial, and it is EXACTLY what the verifier's half-sum reconstruction
recovers from the sent tail together with the honest endpoint sum
`f(0)+f(1)`. HONEST PROVER ONLY. -/
theorem omitted_constant_coefficient (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (wires constants : List (List Element)) (eq : DenseMleIndexed.State)
    (hv : Gates.validateConfiguration c gates = some ()) (hvalid : DenseMleIndexed.Valid eq)
    (hn : 0 < eq.numVars)
    (ht : TableShape c (2^(eq.numVars-1)) (tablesOf wires constants eq)) :
    ∃ coefficients : List Element,
      computeRound c gates publicHash alpha wires constants eq (c.quotientDegree+2) =
        some coefficients.tail ∧
      coefficients.tail.length = c.quotientDegree+2 ∧
      OuterRound.constantCoefficient
        (roundElement c gates publicHash alpha 0 (tablesOf wires constants eq) (2^(eq.numVars-1)) +
         roundElement c gates publicHash alpha 1 (tablesOf wires constants eq) (2^(eq.numVars-1)))
        coefficients.tail = coefficients.getD 0 0 := by
  obtain ⟨p,coefficients,hp,hpoly,hround,hlen,hconst⟩ := current_round_coefficients_shaped c gates
    publicHash alpha wires constants eq hv hvalid hn ht
  refine ⟨coefficients,hround,hlen,?_⟩
  cases coefficients with
  | nil => simp at hlen
  | cons a rest =>
      rw [← hp 0,← hp 1,← hpoly]
      exact OuterInterpolation.reconstruct_constant_from_full_coefficients a rest

/-! ## (4) The gate Boolean-cube sum -/

/-- One Boolean row of the cube: the eq weight at that row times the SAME
all-gates aggregate the round body uses (gate_ext3_v2.rs:126-132 evaluated at a
Boolean point). The reads at `index` are bounded by `cube_reads_bounded`. -/
def rowTerm (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (index : Nat) :
    Option Verifier.Ext3 := do
  let gate ← GatesComplete.evalCombined c gates
    (t.wires.map (fun column => (column.getD index 0).toVerifier))
    (t.constants.map (fun column => (column.getD index 0).toVerifier)) publicHash alpha.toVerifier
  pure (Verifier.mul (t.eq.getD index 0).toVerifier gate)

/-- Every read of a cube row is in range on a shaped table.  STANDALONE
guarantee: the cube identity below does NOT use this lemma, holding regardless
because both sides default identically.  This records that the reads are
nonetheless in range. -/
theorem cube_reads_bounded (c : Gates.Config) (t : Tables) (half index : Nat)
    (ht : TableShape c half t) (hi : index < 2*half) :
    index < t.eq.length ∧ (∀ column ∈ t.wires, index < column.length) ∧
      (∀ column ∈ t.constants, index < column.length) := by
  refine ⟨by rw [ht.2.2.1]; omega, fun column hc => ?_, fun column hc => ?_⟩
  · rw [ht.2.2.2.1 column hc]; omega
  · rw [ht.2.2.2.2 column hc]; omega

/-- The two endpoint evaluations of one captured suffix ARE the two Boolean
rows it covers: `x = 0` reads row `2s`, `x = 1` reads row `2s+1`. -/
theorem slice_endpoint_is_row (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (s : Nat) :
    evalSlice c gates publicHash alpha 0 (captureSlice t s) = rowTerm c gates publicHash alpha t (2*s) ∧
    evalSlice c gates publicHash alpha 1 (captureSlice t s) = rowTerm c gates publicHash alpha t (2*s+1) := by
  constructor
  · simp only [evalSlice,evaluateWeighted,rowTerm,captureSlice,captureAdjacent,affineValues,
      List.map_map,Function.comp_def,affine_weight_at_zero]
  · simp only [evalSlice,evaluateWeighted,rowTerm,captureSlice,captureAdjacent,affineValues,
      List.map_map,Function.comp_def,affine_weight_at_one]

/-- One Boolean row's value as a field element; the `none` branch is
unreachable under configuration validity and the table shape. -/
def rowElement (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (index : Nat) : Element :=
  match rowTerm c gates publicHash alpha t index with
  | some v => NormPolynomial.lift v
  | none => 0

/-- The eq-weighted gate aggregate summed over the whole Boolean cube
(`count = 2^numVars` rows). This is the quantity the gate sumcheck claims is
zero; that claim is NOT proved here. -/
def cubeSum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (count : Nat) : Element :=
  ((List.range count).map (rowElement c gates publicHash alpha t)).sum

theorem suffix_element_is_row_element (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (s : Nat) :
    suffixElement c gates publicHash alpha 0 t s = rowElement c gates publicHash alpha t (2*s) ∧
    suffixElement c gates publicHash alpha 1 t s = rowElement c gates publicHash alpha t (2*s+1) := by
  have h := slice_endpoint_is_row c gates publicHash alpha t s
  constructor
  · unfold suffixElement rowElement; rw [h.1]
  · unfold suffixElement rowElement; rw [h.2]

/-- (4) HONEST PROVER ONLY. The endpoint sum `f(0)+f(1)` of a round is exactly
the eq-weighted gate aggregate summed over the Boolean cube of that round's
tables. For the FIRST round this is the cube sum of the original tables, so a
later module can state "cube sum = 0" against the verifier's initial claim. -/
theorem endpoint_sum_is_cube_sum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (half : Nat) :
    roundElement c gates publicHash alpha 0 t half + roundElement c gates publicHash alpha 1 t half =
      cubeSum c gates publicHash alpha t (2*half) := by
  unfold roundElement cubeSum
  rw [List.map_congr_left (fun s _ => (suffix_element_is_row_element c gates publicHash alpha t s).1),
    List.map_congr_left (fun s _ => (suffix_element_is_row_element c gates publicHash alpha t s).2)]
  exact interleave_sum (rowElement c gates publicHash alpha t) half

/-- (4) The same statement against the ACTUAL source round values: both
endpoint evaluations of the executed grid exist, and their sum is the cube
sum. HONEST PROVER ONLY. -/
theorem executed_endpoint_sum_is_cube_sum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (half : Nat)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c half t) :
    currentRoundValue c gates publicHash alpha 0 t half =
      some (roundElement c gates publicHash alpha 0 t half).toVerifier ∧
    currentRoundValue c gates publicHash alpha 1 t half =
      some (roundElement c gates publicHash alpha 1 t half).toVerifier ∧
    roundElement c gates publicHash alpha 0 t half + roundElement c gates publicHash alpha 1 t half =
      cubeSum c gates publicHash alpha t (2*half) :=
  ⟨current_round_value_sum c gates publicHash alpha 0 t half hv ht,
   current_round_value_sum c gates publicHash alpha 1 t half hv ht,
   endpoint_sum_is_cube_sum c gates publicHash alpha t half⟩

/-! ## (3a) The cross-round endpoint identity at table level -/

theorem bound_affine_values_zero (columns : List (List Element)) (r : Element) (half' s : Nat)
    (hlen : ∀ column ∈ columns, column.length = 2*(2*half')) (hs : s < half') :
    affineValues (captureAdjacent (columns.map (fun column => DenseMleIndexed.bindBuffer column r)) s) 0 =
      affineValues (captureAdjacent columns (2*s)) r := by
  simp only [affineValues,captureAdjacent,List.map_map,Function.comp_def]
  refine List.map_congr_left (fun column hc => ?_)
  have h1 : 2*s < column.length/2 := by rw [hlen column hc]; omega
  rw [affine_weight_at_zero,DenseMleIndexed.bind_buffer_reads_exact_line column r (2*s) h1]
  rfl

theorem bound_affine_values_one (columns : List (List Element)) (r : Element) (half' s : Nat)
    (hlen : ∀ column ∈ columns, column.length = 2*(2*half')) (hs : s < half') :
    affineValues (captureAdjacent (columns.map (fun column => DenseMleIndexed.bindBuffer column r)) s) 1 =
      affineValues (captureAdjacent columns (2*s+1)) r := by
  simp only [affineValues,captureAdjacent,List.map_map,Function.comp_def]
  refine List.map_congr_left (fun column hc => ?_)
  have h1 : 2*s+1 < column.length/2 := by rw [hlen column hc]; omega
  rw [affine_weight_at_one,DenseMleIndexed.bind_buffer_reads_exact_line column r (2*s+1) h1]
  rfl

theorem bound_eq_weight_zero (eqTable : List Element) (r : Element) (half' s : Nat)
    (hlen : eqTable.length = 2*(2*half')) (hs : s < half') :
    affineWeight ((DenseMleIndexed.bindBuffer eqTable r).getD (2*s) 0)
        ((DenseMleIndexed.bindBuffer eqTable r).getD (2*s+1) 0) 0 =
      affineWeight (eqTable.getD (2*(2*s)) 0) (eqTable.getD (2*(2*s)+1) 0) r := by
  have h1 : 2*s < eqTable.length/2 := by rw [hlen]; omega
  rw [affine_weight_at_zero,DenseMleIndexed.bind_buffer_reads_exact_line eqTable r (2*s) h1]
  rfl

theorem bound_eq_weight_one (eqTable : List Element) (r : Element) (half' s : Nat)
    (hlen : eqTable.length = 2*(2*half')) (hs : s < half') :
    affineWeight ((DenseMleIndexed.bindBuffer eqTable r).getD (2*s) 0)
        ((DenseMleIndexed.bindBuffer eqTable r).getD (2*s+1) 0) 1 =
      affineWeight (eqTable.getD (2*(2*s+1)) 0) (eqTable.getD (2*(2*s+1)+1) 0) r := by
  have h1 : 2*s+1 < eqTable.length/2 := by rw [hlen]; omega
  rw [affine_weight_at_one,DenseMleIndexed.bind_buffer_reads_exact_line eqTable r (2*s+1) h1]
  rfl

/-- After `bind_challenge` (151-157) the table shape halves. -/
theorem bound_table_shape (c : Gates.Config) (t : Tables) (r : Element) (half' : Nat)
    (ht : TableShape c (2*half') t) :
    TableShape c half' (GateTerminalBinding.bindTables t r) := by
  refine ⟨by simpa only [GateTerminalBinding.bindTables,List.length_map] using ht.1,
    by simpa only [GateTerminalBinding.bindTables,List.length_map] using ht.2.1, ?_, ?_, ?_⟩
  · show (DenseMleIndexed.bindBuffer t.eq r).length = 2*half'
    rw [DenseMleIndexed.bind_buffer_length,ht.2.2.1]; omega
  · intro column hc
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hc
    rw [DenseMleIndexed.bind_buffer_length,ht.2.2.2.1 original ho]; omega
  · intro column hc
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hc
    rw [DenseMleIndexed.bind_buffer_length,ht.2.2.2.2 original ho]; omega

/-- One captured suffix of the BOUND tables, evaluated at 0 and at 1, is this
round's suffix `2s` / `2s+1` evaluated at the bound challenge. Every adjacent
read it needs is proved in range from the table shape. -/
theorem bound_slice_evaluates (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (r : Element) (half' s : Nat)
    (ht : TableShape c (2*half') t) (hs : s < half') :
    evalSlice c gates publicHash alpha 0 (captureSlice (GateTerminalBinding.bindTables t r) s) =
      evalSlice c gates publicHash alpha r (captureSlice t (2*s)) ∧
    evalSlice c gates publicHash alpha 1 (captureSlice (GateTerminalBinding.bindTables t r) s) =
      evalSlice c gates publicHash alpha r (captureSlice t (2*s+1)) := by
  constructor
  · simp only [evalSlice,evaluateWeighted,captureSlice,GateTerminalBinding.bindTables,
      bound_affine_values_zero t.wires r half' s ht.2.2.2.1 hs,
      bound_affine_values_zero t.constants r half' s ht.2.2.2.2 hs,
      bound_eq_weight_zero t.eq r half' s ht.2.2.1 hs]
  · simp only [evalSlice,evaluateWeighted,captureSlice,GateTerminalBinding.bindTables,
      bound_affine_values_one t.wires r half' s ht.2.2.2.1 hs,
      bound_affine_values_one t.constants r half' s ht.2.2.2.2 hs,
      bound_eq_weight_one t.eq r half' s ht.2.2.1 hs]

theorem bound_suffix_elements (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (r : Element) (half' s : Nat)
    (ht : TableShape c (2*half') t) (hs : s < half') :
    suffixElement c gates publicHash alpha 0 (GateTerminalBinding.bindTables t r) s =
      suffixElement c gates publicHash alpha r t (2*s) ∧
    suffixElement c gates publicHash alpha 1 (GateTerminalBinding.bindTables t r) s =
      suffixElement c gates publicHash alpha r t (2*s+1) := by
  have h := bound_slice_evaluates c gates publicHash alpha t r half' s ht hs
  constructor
  · unfold suffixElement; rw [h.1]
  · unfold suffixElement; rw [h.2]

/-- (3) HONEST PROVER ONLY. The gate analogue of
`OuterClaimChain.bound_endpoint_sum_is_round_value`: after the source's
`bind_challenge` the NEXT round's endpoint sum `f'(0)+f'(1)` is exactly the
CURRENT round value at the drawn challenge. This is what makes the verifier's
running gate claim chain across rounds. -/
theorem bound_endpoint_sum_is_round_value (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat -> Verifier.Base) (alpha : Element) (t : Tables) (r : Element) (half' : Nat)
    (ht : TableShape c (2*half') t) :
    roundElement c gates publicHash alpha 0 (GateTerminalBinding.bindTables t r) half' +
    roundElement c gates publicHash alpha 1 (GateTerminalBinding.bindTables t r) half' =
      roundElement c gates publicHash alpha r t (2*half') := by
  unfold roundElement
  rw [List.map_congr_left (fun s hs =>
      (bound_suffix_elements c gates publicHash alpha t r half' s ht (List.mem_range.mp hs)).1),
    List.map_congr_left (fun s hs =>
      (bound_suffix_elements c gates publicHash alpha t r half' s ht (List.mem_range.mp hs)).2)]
  exact interleave_sum (suffixElement c gates publicHash alpha r t) half'

/-! ## (2) The sent message under the ACTUAL verifier round evaluation -/

/-- (2) HONEST PROVER ONLY. The gate analogue of
`NormDenseRound.sent_round_evaluates_as_verifier`: with the honest endpoint sum
as the claim, the verifier's own `evaluateRound` on the sent coefficients
reproduces the source's round value at EVERY challenge. Totality of the
interpolation is the adopted gate specialisation
`OuterInterpolationTotal.validated_gate_configuration_total` /
`total_sample_actual_outer_round`; interpolation is not re-proved here. -/
theorem sent_round_evaluates_as_verifier (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (wires constants : List (List Element)) (eq : DenseMleIndexed.State)
    (hv : Gates.validateConfiguration c gates = some ()) (hvalid : DenseMleIndexed.Valid eq)
    (hn : 0 < eq.numVars)
    (ht : TableShape c (2^(eq.numVars-1)) (tablesOf wires constants eq)) :
    ∃ message : List Element,
      computeRound c gates publicHash alpha wires constants eq (c.quotientDegree+2) = some message ∧
      message.length = c.quotientDegree+2 ∧
      ∀ r : Element, Verifier.evaluateRound
        (Verifier.add
          (roundElement c gates publicHash alpha 0 (tablesOf wires constants eq)
            (2^(eq.numVars-1))).toVerifier
          (roundElement c gates publicHash alpha 1 (tablesOf wires constants eq)
            (2^(eq.numVars-1))).toVerifier)
        (message.map Element.toVerifier) r.toVerifier =
        (roundElement c gates publicHash alpha r (tablesOf wires constants eq)
          (2^(eq.numVars-1))).toVerifier := by
  obtain ⟨p,hd,hp,evaluations,he,_,hsample⟩ := grid_is_polynomial_sample c gates publicHash alpha
    wires constants eq (c.quotientDegree+2) hv hvalid hn ht
  obtain ⟨coefficients,hi,hlen,hev⟩ := OuterInterpolationTotal.total_sample_actual_outer_round p
    (c.quotientDegree+2) (gate_degree_below_modulus c gates hv) hd
  refine ⟨coefficients.tail,compute_round_exact c gates publicHash alpha wires constants eq _
    evaluations coefficients he (by rw [hsample]; exact hi),hlen,fun r => ?_⟩
  have h := hev r
  rw [hp 0,hp 1,hp r,add_exact] at h
  exact h

/-! ## (3b) The gate prover state and its round chain -/

/-- `into_proof_and_point`'s completion test (164): no Boolean variable left. -/
def isComplete (s : ProverState) : Prop := s.eq.numVars = 0

instance (s : ProverState) : Decidable (isComplete s) := by unfold isComplete; infer_instance

/-- The constructor's invariants (70-83) as they stand after any number of
`bind_challenge` calls: the table shape at the remaining variable count, the
reviewed degree, and the paired `rounds`/`point` pushes (158-159). A supplied
caller invariant, not a new runtime check. -/
def Consistent (c : Gates.Config) (s : ProverState) : Prop :=
  ProverShape c s.eq.numVars s ∧ s.degree = c.quotientDegree+2 ∧ s.rounds.length = s.point.length

/-- `current_round` (105-139) on the prover state's own tables. -/
def stateRound (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) : Option (List Element) :=
  computeRound c gates publicHash alpha (s.wires.map DenseMleIndexed.State.evaluations)
    (s.constants.map DenseMleIndexed.State.evaluations) s.eq s.degree

/-- The returned `Ext3CoefficientRound.non_constant` (137-139). -/
def currentRound (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) :
    Option (List Verifier.Ext3) :=
  (stateRound c gates publicHash alpha s).map (fun cs => cs.map Element.toVerifier)

/-- The round value of the state's own tables at `x`. -/
def stateRoundElement (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (s : ProverState) : Element :=
  roundElement c gates publicHash alpha x s.tables (2^(s.eq.numVars-1))

theorem current_round_after_completion (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) (h : isComplete s) :
    currentRound c gates publicHash alpha s = none := by
  simp only [currentRound,stateRound,
    compute_round_after_completion c gates publicHash alpha _ _ s.eq s.degree h,Option.map_none']

theorem consistent_table_shape (c : Gates.Config) (s : ProverState)
    (hc : Consistent c s) (hn : ¬isComplete s) : TableShape c (2^(s.eq.numVars-1)) s.tables :=
  shape_gives_table_shape c s.eq.numVars s hc.1 (by unfold isComplete at hn; omega)

theorem consistent_eq_valid (c : Gates.Config) (s : ProverState) (hc : Consistent c s) :
    DenseMleIndexed.Valid s.eq := hc.1.2.2.1.1

/-- (1)+(2) at state level: a consistent, incomplete state computes exactly the
`degree`-entry non-constant message, and that message reconstructs the round
value through the ACTUAL verifier evaluation at every challenge.
HONEST PROVER ONLY. -/
theorem current_round_shaped (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState)
    (hv : Gates.validateConfiguration c gates = some ()) (hc : Consistent c s) (hn : ¬isComplete s) :
    ∃ message : List Verifier.Ext3, currentRound c gates publicHash alpha s = some message ∧
      message.length = s.degree ∧
      ∀ r : Element, Verifier.evaluateRound
        (Verifier.add (stateRoundElement c gates publicHash alpha 0 s).toVerifier
          (stateRoundElement c gates publicHash alpha 1 s).toVerifier)
        message r.toVerifier = (stateRoundElement c gates publicHash alpha r s).toVerifier := by
  obtain ⟨message,hm,hlen,hev⟩ := sent_round_evaluates_as_verifier c gates publicHash alpha
    (s.wires.map DenseMleIndexed.State.evaluations) (s.constants.map DenseMleIndexed.State.evaluations)
    s.eq hv (consistent_eq_valid c s hc) (by unfold isComplete at hn; omega)
    (consistent_table_shape c s hc hn)
  refine ⟨message.map Element.toVerifier,?_,by rw [List.length_map,hlen,hc.2.1],hev⟩
  simp only [currentRound,stateRound,hc.2.1,hm,Option.map_some']

/-- The honest prover's own message has exactly the length `bind_challenge`
re-checks at 147-150, so the ensure passes. -/
theorem honest_round_binds (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) (r : Element)
    (hv : Gates.validateConfiguration c gates = some ()) (hc : Consistent c s) (hn : ¬isComplete s) :
    ∃ message : List Verifier.Ext3, currentRound c gates publicHash alpha s = some message ∧
      ∃ t, GateTerminalBinding.bindChallenge s message r = some t := by
  obtain ⟨message,hm,hlen,_⟩ := current_round_shaped c gates publicHash alpha s hv hc hn
  obtain ⟨n,hnv⟩ : ∃ n, s.eq.numVars = n+1 := ⟨s.eq.numVars-1,by unfold isComplete at hn; omega⟩
  obtain ⟨t,hb,_⟩ := bind_challenge_executes c n s message r (by rw [← hnv]; exact hc.1) hlen
  exact ⟨message,hm,t,hb⟩

/-- `bind_challenge` (142-161) preserves the state invariant, consumes one
variable, and appends exactly the round and the challenge. -/
theorem bind_challenge_consistent (c : Gates.Config) (s : ProverState) (round : List Verifier.Ext3)
    (r : Element) (hc : Consistent c s) (hn : ¬isComplete s) (hr : round.length = s.degree) :
    ∃ t, GateTerminalBinding.bindChallenge s round r = some t ∧ Consistent c t ∧
      t.eq.numVars+1 = s.eq.numVars ∧ t.degree = s.degree ∧
      t.rounds = s.rounds ++ [round] ∧ t.point = s.point ++ [r] ∧
      t.tables = GateTerminalBinding.bindTables s.tables r := by
  obtain ⟨n,hnv⟩ : ∃ n, s.eq.numVars = n+1 := ⟨s.eq.numVars-1,by unfold isComplete at hn; omega⟩
  obtain ⟨t,hb,hs'⟩ := bind_challenge_executes c n s round r (by rw [← hnv]; exact hc.1) hr
  obtain ⟨_,_,_,_,hdeg,hrounds,hpoint⟩ := bind_challenge_success s t round r hb
  have hnum : t.eq.numVars = n := hs'.2.2.1.2
  refine ⟨t,hb,⟨by rw [hnum]; exact hs',by rw [hdeg]; exact hc.2.1,?_⟩,by omega,hdeg,hrounds,hpoint,
    bind_challenge_tables s t round r hb⟩
  rw [hrounds,hpoint,List.length_append,List.length_append,hc.2.2]
  rfl

/-- (3) HONEST PROVER ONLY, at prover-state level: with at least two variables
left, the endpoint sum of the state AFTER `bind_challenge` is the round value of
the state BEFORE it, at the bound challenge. -/
theorem bound_endpoint_sum_is_state_round_value (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s t : ProverState)
    (round : List Verifier.Ext3) (r : Element) (hc : Consistent c s) (hn : 2 ≤ s.eq.numVars)
    (hb : GateTerminalBinding.bindChallenge s round r = some t) :
    stateRoundElement c gates publicHash alpha 0 t + stateRoundElement c gates publicHash alpha 1 t =
      stateRoundElement c gates publicHash alpha r s := by
  obtain ⟨m,hm⟩ : ∃ m, s.eq.numVars = m+2 := ⟨s.eq.numVars-2,by omega⟩
  obtain ⟨_,he,_,_,_,_,_⟩ := bind_challenge_success s t round r hb
  have hnum : t.eq.numVars = m+1 := by
    rw [(bind_variable_success s.eq t.eq r he).2]
    show s.eq.numVars-1 = m+1
    omega
  have htab : t.tables = GateTerminalBinding.bindTables s.tables r := bind_challenge_tables s t round r hb
  have hexp : (2:Nat)^(m+2-1) = 2*2^m := by
    rw [show m+2-1 = m+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have hshape : TableShape c (2*2^m) s.tables := by
    have h := shape_gives_table_shape c s.eq.numVars s hc.1 (by omega)
    rw [hm,hexp] at h
    exact h
  unfold stateRoundElement
  rw [hnum,hm,htab,hexp]
  simp only [Nat.add_sub_cancel]
  exact bound_endpoint_sum_is_round_value c gates publicHash alpha s.tables r (2^m) hshape

theorem proof_extraction_requires_completion (s : ProverState) (h : ¬isComplete s) :
    GateTerminalBinding.intoProofAndPoint s = none :=
  incomplete_sumcheck_rejected s (by unfold isComplete at h; omega)

theorem proof_extraction_exact (s : ProverState) (h : isComplete s) :
    GateTerminalBinding.intoProofAndPoint s = some (s.rounds,s.point) :=
  into_proof_and_point_exact s h

/-- (3) The complete honest chain step. A consistent state with at least two
Boolean variables left: computes its `Ext3CoefficientRound`, that message has
exactly the length `bind_challenge` re-checks so the ensure passes, the bound
state stays consistent with one fewer variable and the round/challenge appended,
the verifier's own `evaluateRound` on the message reproduces this round's value
at the challenge, and the NEXT state's endpoint sum is exactly that value.
HONEST PROVER ONLY: nothing here says a verifier-accepted transcript came from
such a prover, and the challenge is an arbitrary field element (no transcript,
Fiat-Shamir or soundness claim). -/
theorem honest_chain_step (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) (r : Element)
    (hv : Gates.validateConfiguration c gates = some ()) (hc : Consistent c s)
    (hn : 2 ≤ s.eq.numVars) :
    ∃ (message : List Verifier.Ext3) (t : ProverState),
      currentRound c gates publicHash alpha s = some message ∧ message.length = s.degree ∧
      GateTerminalBinding.bindChallenge s message r = some t ∧ Consistent c t ∧
      t.eq.numVars+1 = s.eq.numVars ∧ t.rounds = s.rounds ++ [message] ∧
      t.point = s.point ++ [r] ∧
      Verifier.evaluateRound
        (Verifier.add (stateRoundElement c gates publicHash alpha 0 s).toVerifier
          (stateRoundElement c gates publicHash alpha 1 s).toVerifier) message r.toVerifier =
        (stateRoundElement c gates publicHash alpha r s).toVerifier ∧
      stateRoundElement c gates publicHash alpha 0 t +
        stateRoundElement c gates publicHash alpha 1 t =
        stateRoundElement c gates publicHash alpha r s := by
  have hnc : ¬isComplete s := by unfold isComplete; omega
  obtain ⟨message,hm,hlen,hev⟩ := current_round_shaped c gates publicHash alpha s hv hc hnc
  obtain ⟨t,hb,hcon,hnum,_,hrounds,hpoint,_⟩ :=
    bind_challenge_consistent c s message r hc hnc hlen
  exact ⟨message,t,hm,hlen,hb,hcon,hnum,hrounds,hpoint,hev r,
    bound_endpoint_sum_is_state_round_value c gates publicHash alpha s t message r hc hn hb⟩

/-! ## (5) A concrete non-vacuous example -/

-- The literal `decide` proofs below run the whole gate evaluator in the kernel.
-- Elaboration budget only, not a soundness or kernel option; eight adopted
-- modules use the identical setting.
set_option maxHeartbeats 4000000

/-- The arithmetic gate of Gates.lean (`exampleArithmetic`: one constraint
`output - (c0*a*b + c1*addend)`) in the already validated configuration
`⟨numSelectors 1, numConstants 3, numGateConstraints 1, numWires 4,
quotientDegree 2⟩`, so the reviewed degree is `quotientDegree + 2 = 4`. -/
def exampleConfig : Gates.Config := ⟨1,3,1,4,2⟩
def exampleGates : List Gates.GateInfo := [Gates.exampleArithmetic]
def examplePublicHash : Nat → Verifier.Base := fun _ => Verifier.base 0
def exampleAlpha : Element := 9
def exampleChallenge : Element := 2

/-- TWO Boolean variables left, so the round is a real (four-suffix-pair) round
and one full chain step is available: four wire columns, three constant columns
(selector, c0, c1) and the eq table, each with `2^2 = 4` entries. -/
def exampleState : ProverState :=
  ⟨[⟨2,[5,1,2,3]⟩,⟨2,[7,1,1,2]⟩,⟨2,[11,1,4,5]⟩,⟨2,[103,1,9,17]⟩],
   [⟨2,[0,0,0,0]⟩,⟨2,[2,2,2,2]⟩,⟨2,[3,3,3,3]⟩],⟨2,[4,6,1,2]⟩,4,[],[]⟩

/-- The state after `bind_challenge` at `x = 2`: every column is the adopted
`bindBuffer`, i.e. `(1-2)*left + 2*right` on adjacent pairs. -/
def exampleBoundState : ProverState :=
  ⟨[⟨1,[-3,4]⟩,⟨1,[-5,3]⟩,⟨1,[-9,6]⟩,⟨1,[-101,25]⟩],
   [⟨1,[0,0]⟩,⟨1,[2,2]⟩,⟨1,[3,3]⟩],⟨1,[8,3]⟩,4,[List.replicate 4 Verifier.zero],[2]⟩

theorem example_configuration :
    Gates.validateConfiguration exampleConfig exampleGates = some () := by decide

theorem example_consistent : Consistent exampleConfig exampleState :=
  ⟨by decide,rfl,rfl⟩

theorem example_variables : 2 ≤ exampleState.eq.numVars := by decide

/-- The example's round values at 0, at 1 and at the challenge are all nonzero,
and so is its Boolean-cube sum: the statements below are not vacuous. -/
theorem example_nonzero :
    roundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0 exampleState.tables 2 ≠ 0 ∧
    roundElement exampleConfig exampleGates examplePublicHash exampleAlpha 1 exampleState.tables 2 ≠ 0 ∧
    roundElement exampleConfig exampleGates examplePublicHash exampleAlpha exampleChallenge
      exampleState.tables 2 ≠ 0 ∧
    cubeSum exampleConfig exampleGates examplePublicHash exampleAlpha exampleState.tables 4 ≠ 0 ∧
    stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0
      exampleBoundState ≠ 0 := by decide

/-- The literal Boolean-cube sum of the example equals the literal endpoint sum
of its first round; the general theorem instantiated agrees. -/
theorem example_cube_sum :
    roundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0 exampleState.tables 2 +
      roundElement exampleConfig exampleGates examplePublicHash exampleAlpha 1 exampleState.tables 2 =
      cubeSum exampleConfig exampleGates examplePublicHash exampleAlpha exampleState.tables 4 :=
  endpoint_sum_is_cube_sum exampleConfig exampleGates examplePublicHash exampleAlpha
    exampleState.tables 2

theorem example_cube_sum_literal :
    roundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0 exampleState.tables 2 +
      roundElement exampleConfig exampleGates examplePublicHash exampleAlpha 1 exampleState.tables 2 =
      cubeSum exampleConfig exampleGates examplePublicHash exampleAlpha exampleState.tables 4 := by
  decide

/-- The literal `bind_challenge` result of the example. -/
theorem example_bind :
    GateTerminalBinding.bindChallenge exampleState (List.replicate 4 Verifier.zero) exampleChallenge =
      some exampleBoundState := by decide

/-- The literal cross-round identity of the example, and the general theorem
instantiated on it. -/
theorem example_chain_literal :
    stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0 exampleBoundState +
      stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 1 exampleBoundState =
      stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha exampleChallenge
        exampleState := by decide

theorem example_chain :
    stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0 exampleBoundState +
      stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 1 exampleBoundState =
      stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha exampleChallenge
        exampleState :=
  bound_endpoint_sum_is_state_round_value exampleConfig exampleGates examplePublicHash exampleAlpha
    exampleState exampleBoundState (List.replicate 4 Verifier.zero) exampleChallenge
    example_consistent example_variables example_bind

/-- (5) The whole chain step on the example: the message exists, has the four
entries `bind_challenge` demands, binds, and the bound state's endpoint sum is
the value the verifier reconstructs from the message at the challenge. -/
theorem example_chain_step :
    ∃ (message : List Verifier.Ext3) (t : ProverState),
      currentRound exampleConfig exampleGates examplePublicHash exampleAlpha exampleState =
        some message ∧ message.length = 4 ∧
      GateTerminalBinding.bindChallenge exampleState message exampleChallenge = some t ∧
      Consistent exampleConfig t ∧ t.eq.numVars = 1 ∧
      Verifier.evaluateRound
        (Verifier.add
          (stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0
            exampleState).toVerifier
          (stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 1
            exampleState).toVerifier) message exampleChallenge.toVerifier =
        (stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha exampleChallenge
          exampleState).toVerifier ∧
      stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 0 t +
        stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha 1 t =
        stateRoundElement exampleConfig exampleGates examplePublicHash exampleAlpha exampleChallenge
          exampleState := by
  obtain ⟨message,t,hm,hlen,hb,hcon,hnum,_,_,hev,hsum⟩ := honest_chain_step exampleConfig
    exampleGates examplePublicHash exampleAlpha exampleState exampleChallenge example_configuration
    example_consistent example_variables
  exact ⟨message,t,hm,hlen,hb,hcon,by have : exampleState.eq.numVars = 2 := rfl; omega,hev,hsum⟩

end Audit.Wire3.GateDenseRound
