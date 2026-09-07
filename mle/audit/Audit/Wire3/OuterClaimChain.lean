import Audit.Wire3.NormDenseRound
import Audit.Wire3.OuterAdapter

/-!
# Outer LOG-lane claim chain for the honest NormDenseRound prover

Sources reviewed:
* mle/src/verifier_v2.rs 277-301: `log_final_claim`/`gate_final_claim` start at
  `Field64_3::ZERO`; each round commits both `non_constant` vectors to the
  transcript, then `evaluate_ext3_coefficient_round` folds the running claim
  and the challenge is pushed onto `log_point`/`gate_point`;
* mle/contracts/src/OuterLogupExt3Verifier.sol 254-322
  (`_verifyCoupledSumchecksUnchecked`): `logClaim = gateClaim = zero()`,
  ordered rounds, `logPoint[roundIndex] = roundChallenges.log`;
* mle/src/permutation/norm_logup.rs 682-758: `current_round` (cached pending
  round, `coefficients[1..]`), `bind_challenge` (bind every table, push the
  completed round and the challenge), `into_proof_and_point`.

Adopted Lean models reused unchanged: `Verifier.RoundState`/`start`/`roundStep`/
`runRounds`/`derivedRounds` (Verifier.lean 158-182, 386-387),
`OuterRound.actual_typed_round_is_polynomial_eval`/
`actual_coupled_round_uses_both_derived_polynomials`/`polynomial_endpoint_sum_is_claim`
(OuterRound.lean), and the NormDenseRound prover state machine
(`currentRound`, `bindChallenge`, `intoProofAndPoint`, `Consistent`,
`sent_round_evaluates_as_verifier`, `bind_challenge_consistent`,
`proof_extraction_exact`). No new evaluator, decoder, transcript or
interpolation model is introduced and interpolation is not re-proved.

What is proved (honest prover only):
1. `bound_endpoint_sum_is_round_value`: after the modelled `bind`, the next
   round's endpoint sum `f'(0)+f'(1)` equals the previous round polynomial at
   the bound challenge. This is the cross-round identity NormDenseRound left
   open; every table read it uses is covered by an explicit bound.
2. `honest_step_exact`/`honest_run_exact`/`honest_log_chain_step`/
   `honest_log_chain`: driving the honest prover in lockstep with the ACTUAL
   `Verifier.roundStep` (the verifier's log challenge is what the prover
   binds), the verifier's log claim after step i is `roundValue t_i p r_i`
   with `t_i` the tables after i binds, and the run is literally
   `Verifier.runRounds` on the sent messages.
3. `chain_initial_claim`: the source's zero initial claim is in lockstep with
   the honest prover iff the honest first endpoint sum is zero; the endpoint
   sum itself is `f(0)+f(1)` of the degree-5 round polynomial and is NOT
   shown to be zero (that is the norm/logUp relation, out of scope).
4. `honest_extraction_matches_verifier`/`honest_run_is_derived_rounds`:
   `into_proof_and_point` returns exactly the message list and challenge list
   the verifier consumed, and `Verifier.derivedRounds` of a proof carrying
   those messages is the lockstep verifier state.
5. Gate lane: no gate prover with `bind_challenge` is adopted
   (GateSlotRound stops before interpolation and has no binding). The gate
   theorems are parameterised by the explicit hypothesis that the verifier's
   reconstruction of `message_i` from the running gate claim agrees with a
   polynomial of degree at most d at the d+1 integer grid nodes
   (`gate_claim_from_grid_agreement`); no gate prover is faked.
6. `one_round_example`: a concrete n = 1 instance satisfying every hypothesis.

Not proved: any statement about arbitrary (dishonest) messages, sumcheck or
PCS soundness, transcript randomness, that the honest endpoint sum is zero,
Rust/EVM refinement, or the terminal norm/gate evaluations.
-/
namespace Audit.Wire3.OuterClaimChain
open Audit.Wire3 GoldilocksExt3Field NormDenseRound

/-! ## Element-valued sums of the adopted Verifier.add folds -/

theorem lift_zero : NormPolynomial.lift Verifier.zero = (0 : Element) := rfl

theorem fold_add_lift {α : Type} (f : α → Verifier.Ext3) (xs : List α) (acc : Verifier.Ext3) :
    xs.foldl (fun acc x => Verifier.add acc (f x)) acc =
      (xs.foldl (fun acc x => acc + NormPolynomial.lift (f x)) (NormPolynomial.lift acc)).toVerifier := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x _ ih => exact ih (Verifier.add acc (f x))

theorem foldl_add_eq_sum {α : Type} (g : α → Element) (xs : List α) (a : Element) :
    xs.foldl (fun acc x => acc + g x) a = a + (xs.map g).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, add_assoc]

/-- The adopted `Verifier.add` fold from zero, as a list sum in the field. -/
def esum {α : Type} (f : α → Verifier.Ext3) (xs : List α) : Element :=
  (xs.map (fun x => NormPolynomial.lift (f x))).sum

theorem fold_is_esum {α : Type} (f : α → Verifier.Ext3) (xs : List α) :
    xs.foldl (fun acc x => Verifier.add acc (f x)) Verifier.zero = (esum f xs).toVerifier := by
  rw [fold_add_lift, foldl_add_eq_sum, lift_zero, zero_add]
  rfl

theorem sum_map_add {α : Type} (f g : α → Element) (xs : List α) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem interleave_sum (g : Nat → Element) (M : Nat) :
    ((List.range M).map (fun s => g (2*s))).sum + ((List.range M).map (fun s => g (2*s+1))).sum =
      ((List.range (2*M)).map g).sum := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [show 2*(M+1) = 2*M+1+1 by ring, List.range_succ, List.range_succ, List.range_succ]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      rw [← ih]
      ring

/-- The row part and the public-input part of `roundValue` as field sums. -/
def rowSum (t : Tables) (p : Prepared) (x : Element) : Element :=
  esum (fun s => rowValue t p s x) (List.range (t.eq.length/2))

def piSum (t : Tables) (x : Element) : Element :=
  esum (fun b => piValue t b x) t.bindings

/-- `roundValue` (the modelled `round_sum_at` of the honest prover) as field sums. -/
theorem round_value_as_sums (t : Tables) (p : Prepared) (x : Element) :
    roundValue t p x = (rowSum t p x + NormPolynomial.lift p.challenges.xi * piSum t x).toVerifier := by
  unfold roundValue rowSum piSum
  rw [fold_is_esum, fold_is_esum]
  rfl

/-- The honest endpoint sum `f(0)+f(1)` of the current round of `t`
(norm_logup.rs:687-692 samples at 0 and 1; the verifier's `evaluateRound`
reconstructs the omitted constant from exactly this sum). -/
def endpointSum (t : Tables) (p : Prepared) : Verifier.Ext3 :=
  Verifier.add (roundValue t p 0) (roundValue t p 1)

/-- The honest prover's endpoint sum is `f(0)+f(1)` of its degree-5 round polynomial. -/
theorem honest_endpoint_sum_is_polynomial (t : Tables) (p : Prepared) :
    endpointSum t p = ((roundPolynomial t p).eval 0 + (roundPolynomial t p).eval 1).toVerifier := by
  unfold endpointSum
  rw [add_exact, round_polynomial_same_ordered_evaluation, round_polynomial_same_ordered_evaluation]

/-- Field form of `honest_endpoint_sum_is_polynomial` (honest prover). -/
theorem lift_endpoint_sum (t : Tables) (p : Prepared) :
    NormPolynomial.lift (endpointSum t p) = (roundPolynomial t p).eval 0 + (roundPolynomial t p).eval 1 := by
  rw [honest_endpoint_sum_is_polynomial]
  rfl

/-! ## Lines of a bound column at the Boolean endpoints -/

theorem line_at_zero (column : List Element) (s : Nat) : line column s 0 = column.getD (2*s) 0 := by
  unfold line
  ring

theorem line_at_one (column : List Element) (s : Nat) : line column s 1 = column.getD (2*s+1) 0 := by
  unfold line
  ring

/-- Reading the bound column at `2*s` is the previous round's line at `2*s`
(the honest prover's modelled bind, via the adopted `bound_cell_is_round_line`);
the read is in range by hypothesis, not by the totalized default. -/
theorem bound_line_zero (column : List Element) (s : Nat) (r : Element) (h : 2*s < column.length/2) :
    line (DenseMleIndexed.bindBuffer column r) s 0 = line column (2*s) r := by
  rw [line_at_zero, bound_cell_is_round_line column (2*s) r h]

/-- The odd cell of the honest prover's bound column, in range by hypothesis. -/
theorem bound_line_one (column : List Element) (s : Nat) (r : Element) (h : 2*s+1 < column.length/2) :
    line (DenseMleIndexed.bindBuffer column r) s 1 = line column (2*s+1) r := by
  rw [line_at_one, bound_cell_is_round_line column (2*s+1) r h]

/-- `bound_line_zero` with the bound derived from the honest prover's `Shape`. -/
theorem shaped_line_zero (column : List Element) (n s : Nat) (r : Element)
    (hlen : column.length = 2^n) (hs : 2*s+1 < 2^n/2) :
    line (DenseMleIndexed.bindBuffer column r) s 0 = line column (2*s) r :=
  bound_line_zero column s r (by rw [hlen]; omega)

/-- `bound_line_one` with the bound derived from the honest prover's `Shape`. -/
theorem shaped_line_one (column : List Element) (n s : Nat) (r : Element)
    (hlen : column.length = 2^n) (hs : 2*s+1 < 2^n/2) :
    line (DenseMleIndexed.bindBuffer column r) s 1 = line column (2*s+1) r :=
  bound_line_one column s r (by rw [hlen]; omega)

/-- Column read of a mapped table at an in-range index. -/
theorem column_at_map (f : List Element → List Element) (columns : List (List Element)) (j : Nat)
    (hj : j < columns.length) : columnAt (columns.map f) j = f (columnAt columns j) := by
  unfold columnAt
  rw [List.getD_eq_get _ _ (by rw [List.length_map]; exact hj), List.getD_eq_get _ _ hj]
  simp only [List.get_eq_getElem, List.getElem_map]

/-! ## The tables after one modelled bind -/

/-- The `some` payload of `bindTables` (norm_logup.rs:542-563), named so that
the cross-round identity can be stated about it. -/
def boundTables (t : Tables) (r : Element) : Tables :=
  { eq := DenseMleIndexed.bindBuffer t.eq r,
    subgroup := DenseMleIndexed.bindBuffer t.subgroup r,
    wires := t.wires.map (fun column => DenseMleIndexed.bindBuffer column r),
    sigmas := t.sigmas.map (fun column => DenseMleIndexed.bindBuffer column r),
    identityHelpers := t.identityHelpers.map (fun column => DenseMleIndexed.bindBuffer column r),
    sigmaHelpers := t.sigmaHelpers.map (fun column => DenseMleIndexed.bindBuffer column r),
    bindings := t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b r }),
    boundVariables := t.boundVariables+1,
    remaining := t.remaining-1 }

/-- The modelled `bind` of the honest prover succeeds with `boundTables` when a variable remains. -/
theorem bind_tables_is_bound (t : Tables) (r : Element) (h : 0 < t.remaining) :
    bindTables t r = some (boundTables t r) := by
  simp only [bindTables, if_neg (show t.remaining ≠ 0 by omega)]
  rfl

/-- The honest prover's wire reads of the bound tables at 0/1 are this round's
reads at the challenge (adjacent suffixes `2s`, `2s+1`). -/
theorem bound_wire_values (t : Tables) (p : Prepared) (r : Element) (s j : Nat)
    (h : Shape t p) (hs : 2*s+1 < 2^t.remaining/2) (hj : j < t.wires.length) :
    wireValues (boundTables t r) p s j 0 = wireValues t p (2*s) j r ∧
    wireValues (boundTables t r) p s j 1 = wireValues t p (2*s+1) j r := by
  obtain ⟨_, hg, hw, hsig, hi, hh, _, _, _⟩ := h
  have a := column_at_shape _ _ _ j hw hj
  have b := column_at_shape _ _ _ j hsig hj
  have c := column_at_shape _ _ _ j hi hj
  have d := column_at_shape _ _ _ j hh hj
  constructor
  · simp only [wireValues, boundTables, column_at_map _ _ _ a.1, column_at_map _ _ _ b.1,
      column_at_map _ _ _ c.1, column_at_map _ _ _ d.1, shaped_line_zero _ _ _ _ a.2 hs,
      shaped_line_zero _ _ _ _ b.2 hs, shaped_line_zero _ _ _ _ c.2 hs,
      shaped_line_zero _ _ _ _ d.2 hs, shaped_line_zero _ _ _ _ hg hs]
  · simp only [wireValues, boundTables, column_at_map _ _ _ a.1, column_at_map _ _ _ b.1,
      column_at_map _ _ _ c.1, column_at_map _ _ _ d.1, shaped_line_one _ _ _ _ a.2 hs,
      shaped_line_one _ _ _ _ b.2 hs, shaped_line_one _ _ _ _ c.2 hs,
      shaped_line_one _ _ _ _ d.2 hs, shaped_line_one _ _ _ _ hg hs]

/-- The routed-wire contribution after the honest prover's bind, at 0/1. -/
theorem bound_contribution (t : Tables) (p : Prepared) (r : Element) (s j : Nat)
    (h : Shape t p) (hs : 2*s+1 < 2^t.remaining/2) (hj : j < t.wires.length) :
    contribution (boundTables t r) p s 0 j = contribution t p (2*s) r j ∧
    contribution (boundTables t r) p s 1 j = contribution t p (2*s+1) r j := by
  have hw := bound_wire_values t p r s j h hs hj
  exact ⟨by simp only [contribution, hw.1], by simp only [contribution, hw.2]⟩

/-- One suffix row of the honest prover's bound tables at 0/1 is this round's
row `2s`/`2s+1` at the challenge. -/
theorem bound_row_value (t : Tables) (p : Prepared) (r : Element) (s : Nat)
    (h : Shape t p) (hs : 2*s+1 < 2^t.remaining/2) :
    rowValue (boundTables t r) p s 0 = rowValue t p (2*s) r ∧
    rowValue (boundTables t r) p s 1 = rowValue t p (2*s+1) r := by
  have hlen : (boundTables t r).wires.length = t.wires.length := List.length_map _ _
  have heq : (boundTables t r).eq = DenseMleIndexed.bindBuffer t.eq r := rfl
  have hc : ∀ j ∈ List.range t.wires.length,
      contribution (boundTables t r) p s 0 j = contribution t p (2*s) r j ∧
      contribution (boundTables t r) p s 1 j = contribution t p (2*s+1) r j :=
    fun j hj => bound_contribution t p r s j h hs (List.mem_range.mp hj)
  have h01 : (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution (boundTables t r) p s 0 j).1) Verifier.zero =
      (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution t p (2*s) r j).1) Verifier.zero :=
    List.foldl_ext _ _ _ (fun acc j hj => by rw [(hc j hj).1])
  have h02 : (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution (boundTables t r) p s 0 j).2) Verifier.zero =
      (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution t p (2*s) r j).2) Verifier.zero :=
    List.foldl_ext _ _ _ (fun acc j hj => by rw [(hc j hj).1])
  have h11 : (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution (boundTables t r) p s 1 j).1) Verifier.zero =
      (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution t p (2*s+1) r j).1) Verifier.zero :=
    List.foldl_ext _ _ _ (fun acc j hj => by rw [(hc j hj).2])
  have h12 : (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution (boundTables t r) p s 1 j).2) Verifier.zero =
      (List.range t.wires.length).foldl
        (fun acc j => Verifier.add acc (contribution t p (2*s+1) r j).2) Verifier.zero :=
    List.foldl_ext _ _ _ (fun acc j hj => by rw [(hc j hj).2])
  constructor
  · unfold rowValue
    rw [hlen, heq, shaped_line_zero _ _ _ _ h.1 hs, h01, h02]
  · unfold rowValue
    rw [hlen, heq, shaped_line_one _ _ _ _ h.1 hs, h11, h12]

/-- The honest prover's row sums after a bind interleave to this round's row
sum at the challenge (`2 ≤ remaining`). -/
theorem bound_row_sum (t : Tables) (p : Prepared) (r : Element) (m : Nat)
    (h : Shape t p) (hm : t.remaining = m+1+1) :
    rowSum (boundTables t r) p 0 + rowSum (boundTables t r) p 1 = rowSum t p r := by
  have hb : (boundTables t r).eq.length/2 = 2^m := by
    show (DenseMleIndexed.bindBuffer t.eq r).length/2 = 2^m
    rw [DenseMleIndexed.bind_buffer_length, h.1, hm, half_pow, half_pow]
  have ht : t.eq.length/2 = 2*2^m := by
    rw [h.1, hm, half_pow, Nat.pow_succ, Nat.mul_comm]
  have hs : ∀ s ∈ List.range (2^m), 2*s+1 < 2^t.remaining/2 := by
    intro s hs
    rw [List.mem_range] at hs
    rw [hm, half_pow, Nat.pow_succ]
    omega
  unfold rowSum esum
  rw [hb, ht,
    List.map_congr_left (fun s hs' => congrArg NormPolynomial.lift (bound_row_value t p r s h (hs s hs')).1),
    List.map_congr_left (fun s hs' => congrArg NormPolynomial.lift (bound_row_value t p r s h (hs s hs')).2)]
  exact interleave_sum (fun s => NormPolynomial.lift (rowValue t p s r)) (2^m)

/-! ## The public-input line after one bind -/

/-- `piValue` (the honest prover's PI term) in the field. -/
theorem pi_value_lift (t : Tables) (b : Binding) (x : Element) :
    NormPolynomial.lift (piValue t b x) =
      b.etaPower * piFactor t b x *
        (line (columnAt t.wires b.column) (piSuffix t b) x -
          NormPolynomial.lift (Norm.embed b.publicValue.val)) := rfl

/-- The honest prover's PI suffix after a bind halves (row >> (bound+2)). -/
theorem bound_pi_suffix (t : Tables) (r : Element) (b : Binding) :
    piSuffix (boundTables t r) { b with prefixEq := prefixUpdate t b r } = piSuffix t b / 2 := by
  simp only [piSuffix, boundTables]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- The honest prover's PI factor after a bind: the updated prefix times the next Boolean factor. -/
theorem bound_pi_factor (t : Tables) (r : Element) (b : Binding) (x : Element) :
    piFactor (boundTables t r) { b with prefixEq := prefixUpdate t b r } x =
      piFactor t b r * (if piSuffix t b % 2 = 0 then 1 - x else x) := by
  simp only [piFactor, boundTables, piSuffix, prefix_update_is_pi_factor]

/-- With at least two variables left, both adjacent reads of the honest
prover's bound wire column made by the next round's PI line are in range. -/
theorem bound_pi_reads_in_range (t : Tables) (p : Prepared) (r : Element) (b : Binding)
    (h : Shape t p) (hr : 2 ≤ t.remaining) (hb : b ∈ t.bindings) :
    2*(piSuffix t b / 2) < (DenseMleIndexed.bindBuffer (columnAt t.wires b.column) r).length ∧
    2*(piSuffix t b / 2)+1 < (DenseMleIndexed.bindBuffer (columnAt t.wires b.column) r).length := by
  have hcol := pi_reads_bounded t p b h (by omega) hb
  have hw := (column_at_shape _ _ _ b.column h.2.2.1 hcol.1).2
  obtain ⟨m, hm⟩ : ∃ m, t.remaining = m+1+1 := ⟨t.remaining-2, by omega⟩
  have hn : piSuffix t b < 2^(m+1) := by
    have := hcol.2.1
    rw [h.1, hm, half_pow] at this
    exact this
  rw [DenseMleIndexed.bind_buffer_length, hw, hm, half_pow]
  have h2 : 2^(m+1) = 2*2^m := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [h2] at hn ⊢
  omega

/-- The honest prover's next-round PI line at 0 plus at 1 is this round's PI
line at the challenge: the bound prefix is `piFactor t b r`, the bound wire cell at
`piSuffix t b` is the line at `r`, and the Boolean factor selects it. -/
theorem bound_pi_value (t : Tables) (p : Prepared) (r : Element) (b : Binding)
    (h : Shape t p) (hr : 2 ≤ t.remaining) (hb : b ∈ t.bindings) :
    NormPolynomial.lift (piValue (boundTables t r) { b with prefixEq := prefixUpdate t b r } 0) +
      NormPolynomial.lift (piValue (boundTables t r) { b with prefixEq := prefixUpdate t b r } 1) =
      NormPolynomial.lift (piValue t b r) := by
  have hcol := pi_reads_bounded t p b h (by omega) hb
  have hw := (column_at_shape _ _ _ b.column h.2.2.1 hcol.1).2
  have hn : piSuffix t b < (columnAt t.wires b.column).length/2 := by
    rw [hw, ← h.1]
    exact hcol.2.1
  have hcolb : columnAt (boundTables t r).wires b.column =
      DenseMleIndexed.bindBuffer (columnAt t.wires b.column) r :=
    column_at_map _ _ _ hcol.1
  simp only [pi_value_lift, bound_pi_factor, bound_pi_suffix, hcolb, line_at_zero, line_at_one]
  rcases Nat.mod_two_eq_zero_or_one (piSuffix t b) with h0 | h1
  · have hi : 2*(piSuffix t b / 2) = piSuffix t b := by omega
    rw [if_pos h0, if_pos h0, hi, bound_cell_is_round_line _ _ _ hn]
    ring
  · have hi : 2*(piSuffix t b / 2)+1 = piSuffix t b := by omega
    rw [if_neg (by omega), if_neg (by omega), hi, bound_cell_is_round_line _ _ _ hn]
    ring

/-- The honest prover's PI sums after a bind, at 0 plus at 1, equal this round's PI sum at the challenge. -/
theorem bound_pi_sum (t : Tables) (p : Prepared) (r : Element)
    (h : Shape t p) (hr : 2 ≤ t.remaining) :
    piSum (boundTables t r) 0 + piSum (boundTables t r) 1 = piSum t r := by
  show ((t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b r })).map
      (fun b' => NormPolynomial.lift (piValue (boundTables t r) b' 0))).sum +
    ((t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b r })).map
      (fun b' => NormPolynomial.lift (piValue (boundTables t r) b' 1))).sum =
    (t.bindings.map (fun b => NormPolynomial.lift (piValue t b r))).sum
  rw [List.map_map, List.map_map, ← sum_map_add]
  exact congrArg List.sum (List.map_congr_left (fun b hb => bound_pi_value t p r b h hr hb))

/-- Cross-round identity of the honest prover's modelled `bind`
(norm_logup.rs:542-563): with at least two variables left, the endpoint sum
of the NEXT round polynomial equals the CURRENT round polynomial at the bound
challenge. This is what lets the verifier's running claim chain: the claim
`roundValue t p r` it computes from round i is exactly the endpoint sum from
which round i+1's omitted constant is reconstructed. Every adjacent read is
covered by `Shape` plus the explicit bounds above. Honest prover only. -/
theorem bound_endpoint_sum_is_round_value (t : Tables) (p : Prepared) (r : Element) (t' : Tables)
    (h : Shape t p) (hr : 2 ≤ t.remaining) (hb : bindTables t r = some t') :
    endpointSum t' p = roundValue t p r := by
  obtain ⟨m, hm⟩ : ∃ m, t.remaining = m+1+1 := ⟨t.remaining-2, by omega⟩
  rw [bind_tables_is_bound t r (by omega)] at hb
  have ht' := Option.some.inj hb
  subst ht'
  unfold endpointSum
  rw [round_value_as_sums, round_value_as_sums, round_value_as_sums, ← add_exact]
  congr 1
  calc rowSum (boundTables t r) p 0 + NormPolynomial.lift p.challenges.xi * piSum (boundTables t r) 0 +
        (rowSum (boundTables t r) p 1 + NormPolynomial.lift p.challenges.xi * piSum (boundTables t r) 1)
      = (rowSum (boundTables t r) p 0 + rowSum (boundTables t r) p 1) +
          NormPolynomial.lift p.challenges.xi * (piSum (boundTables t r) 0 + piSum (boundTables t r) 1) := by
        ring
    _ = rowSum t p r + NormPolynomial.lift p.challenges.xi * piSum t r := by
        rw [bound_row_sum t p r m h hm, bound_pi_sum t p r h hr]

/-! ## The honest prover driven by the actual verifier loop -/

/-- The coupled message the verifier receives: the prover's five Ext3
coefficients (`non_constant`) as the log message, the gate message supplied
externally (no gate prover is modelled). -/
def coupled (message : List Element) (gate : List Verifier.Ext3) : Verifier.CoupledMessage :=
  (message.map Element.toVerifier, gate)

/-- The verifier's log challenge for this round (verifier_v2.rs:283-287 /
TranscriptV2.commitCoupledOuterRound), as the field element the honest prover
binds. -/
def logChallenge (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (message : List Element) (gate : List Verifier.Ext3) : Element :=
  NormPolynomial.lift (commit v.transcript v.roundIndex (message.map Element.toVerifier) gate).log

/-- The bound challenge is exactly the verifier's log challenge. -/
theorem log_challenge_exact (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (message : List Element) (gate : List Verifier.Ext3) :
    (logChallenge commit v message gate).toVerifier =
      (commit v.transcript v.roundIndex (message.map Element.toVerifier) gate).log := rfl

/-- One lockstep round of the honest prover against the ACTUAL verifier step:
`current_round`, the verifier's coupled commit and `Verifier.roundStep`,
then `bind_challenge` with the verifier's log challenge. Any prover
`Err`/panic propagates; nothing is defaulted. -/
def honestStep (commit : Verifier.CommitRound) (gate : List Verifier.Ext3)
    (v : Verifier.RoundState) (s : ProverState) : Outcome (Verifier.RoundState × ProverState) :=
  match currentRound s with
  | .panic => .panic
  | .error e => .error e
  | .ok q =>
    match bindChallenge q.2 (logChallenge commit v q.1 gate) with
    | .panic => .panic
    | .error e => .error e
    | .ok s' => .ok (Verifier.roundStep commit v (coupled q.1 gate), s')

/-- The lockstep loop over the externally supplied gate messages, one per
round (verifier_v2.rs:281-301 iterates `0..degree_bits`). -/
def honestRun (commit : Verifier.CommitRound) :
    Verifier.RoundState → ProverState → List (List Verifier.Ext3) →
      Outcome (Verifier.RoundState × ProverState)
  | v, s, [] => .ok (v, s)
  | v, s, g :: gs =>
    match honestStep commit g v s with
    | .panic => .panic
    | .error e => .error e
    | .ok q => honestRun commit q.1 q.2 gs

/-- Sequential composition of the honest prover's lockstep loop. -/
theorem honest_run_append (commit : Verifier.CommitRound) (a b : List (List Verifier.Ext3)) :
    ∀ (v : Verifier.RoundState) (s : ProverState) (v' : Verifier.RoundState) (s' : ProverState),
      honestRun commit v s a = .ok (v', s') → honestRun commit v s (a ++ b) = honestRun commit v' s' b := by
  induction a with
  | nil =>
      intro v s v' s' h
      simp only [honestRun, Outcome.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | cons g a ih =>
      intro v s v' s' h
      simp only [List.cons_append, honestRun] at h ⊢
      cases hs : honestStep commit g v s with
      | panic => rw [hs] at h; exact Outcome.noConfusion h
      | error e => rw [hs] at h; exact Outcome.noConfusion h
      | ok q => rw [hs] at h; exact ih _ _ _ _ h

/-- The lockstep invariant: the prover state is consistent with no cached
round, and (while rounds remain) the verifier's running log claim is the
honest endpoint sum of the prover's current round. -/
structure Lockstep (v : Verifier.RoundState) (s : ProverState) : Prop where
  consistent : Consistent s
  pending : s.pendingRound = none
  claim : ¬isComplete s → v.logClaim = endpointSum s.tables s.prepared

/-- A successful `bind_challenge` of the honest prover binds the tables with `bindTables`. -/
theorem bind_challenge_ok_tables (s s' : ProverState) (c : Element)
    (h : bindChallenge s c = .ok s') : bindTables s.tables c = some s'.tables := by
  unfold bindChallenge at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i tables ht
        cases h
        exact ht

/-- A consistent honest prover state with a variable left is not complete. -/
theorem incomplete_of_remaining (s : ProverState) (hc : Consistent s) (hr : 0 < s.tables.remaining) :
    ¬isComplete s := by
  intro h
  have := complete_means_no_variables_remain s hc h
  omega

/-- One honest-prover lockstep step. The verifier's new log claim is
`roundValue t p r` for the prover's CURRENT tables `t` and the verifier's
log challenge `r` (`sent_round_evaluates_as_verifier`); the prover binds
exactly that challenge (`bind_challenge_consistent`), and if a further round
remains the invariant is re-established by
`bound_endpoint_sum_is_round_value`. Honest prover only. -/
theorem honest_step_exact (commit : Verifier.CommitRound) (gate : List Verifier.Ext3)
    (v : Verifier.RoundState) (s : ProverState) (hl : Lockstep v s) (hn : ¬isComplete s) :
    ∃ (message : List Element) (s' : ProverState),
      honestStep commit gate v s = .ok (Verifier.roundStep commit v (coupled message gate), s') ∧
      computeRound s.tables s.prepared = some message ∧ message.length = 5 ∧
      Consistent s' ∧ s'.pendingRound = none ∧ s'.prepared = s.prepared ∧
      s'.totalRounds = s.totalRounds ∧
      s'.completedRounds = s.completedRounds ++ [message] ∧
      s'.point = s.point ++ [logChallenge commit v message gate] ∧
      s'.tables.remaining + 1 = s.tables.remaining ∧
      bindTables s.tables (logChallenge commit v message gate) = some s'.tables ∧
      (Verifier.roundStep commit v (coupled message gate)).logClaim =
        roundValue s.tables s.prepared (logChallenge commit v message gate) ∧
      Lockstep (Verifier.roundStep commit v (coupled message gate)) s' := by
  obtain ⟨message, hcr, hlen, hev⟩ := current_round_shaped s hl.consistent hn hl.pending
  have hcomp : computeRound s.tables s.prepared = some message := by
    have h := hcr
    unfold currentRound at h
    rw [if_neg hn, hl.pending] at h
    cases hc : computeRound s.tables s.prepared with
    | none => rw [hc] at h; cases h
    | some round =>
        rw [hc] at h
        simp only [Outcome.ok.injEq, Prod.mk.injEq] at h
        rw [h.1]
  have hc₁ : Consistent { s with pendingRound := some message } := hl.consistent
  have hn₁ : ¬isComplete { s with pendingRound := some message } := hn
  obtain ⟨s', hbind, hcons, hcomp', hpt, hpend, hprep, htot, hrem, _⟩ :=
    bind_challenge_consistent { s with pendingRound := some message }
      (logChallenge commit v message gate) message hc₁ hn₁ rfl
  have hstep : honestStep commit gate v s =
      .ok (Verifier.roundStep commit v (coupled message gate), s') := by
    simp only [honestStep, hcr, hbind]
  have hclaim : (Verifier.roundStep commit v (coupled message gate)).logClaim =
      roundValue s.tables s.prepared (logChallenge commit v message gate) := by
    show Verifier.evaluateRound v.logClaim (message.map Element.toVerifier)
      (commit v.transcript v.roundIndex (message.map Element.toVerifier) gate).log = _
    rw [hl.claim hn]
    exact hev (logChallenge commit v message gate)
  have htables := bind_challenge_ok_tables _ s' _ hbind
  refine ⟨message, s', hstep, hcomp, hlen, hcons, hpend, hprep, htot, hcomp', hpt, hrem,
    htables, hclaim, hcons, hpend, ?_⟩
  intro hn'
  have hpos := incomplete_means_variables_remain s' hcons hn'
  have hrem' : s'.tables.remaining + 1 = s.tables.remaining := hrem
  rw [hclaim, hprep]
  exact (bound_endpoint_sum_is_round_value s.tables s.prepared _ s'.tables
    hl.consistent.2.2.2 (by omega) htables).symm

/-- The whole honest lockstep run: it succeeds, the prover's completed rounds
and point grow by exactly the sent messages and the verifier's log
challenges, and the verifier state is literally `Verifier.runRounds` on the
coupled messages from the same start state. Honest prover only. -/
theorem honest_run_exact (commit : Verifier.CommitRound) (gates : List (List Verifier.Ext3)) :
    ∀ (v : Verifier.RoundState) (s : ProverState), Lockstep v s →
      gates.length ≤ s.tables.remaining →
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element)) (chals : List Element),
      honestRun commit v s gates = .ok (v', s') ∧
      Consistent s' ∧ s'.pendingRound = none ∧ s'.prepared = s.prepared ∧
      s'.totalRounds = s.totalRounds ∧
      s'.completedRounds = s.completedRounds ++ sent ∧ s'.point = s.point ++ chals ∧
      sent.length = gates.length ∧ chals.length = gates.length ∧ (∀ m ∈ sent, m.length = 5) ∧
      s'.tables.remaining + gates.length = s.tables.remaining ∧
      v' = Verifier.runRounds commit v ((sent.map (List.map Element.toVerifier)).zip gates) ∧
      v'.logPoint = v.logPoint ++ chals.map Element.toVerifier ∧
      Lockstep v' s' := by
  induction gates with
  | nil =>
      intro v s hl _
      exact ⟨v, s, [], [], rfl, hl.consistent, hl.pending, rfl, rfl, by simp, by simp, rfl, rfl,
        by simp, by simp, rfl, by simp, hl⟩
  | cons g gs ih =>
      intro v s hl hlen
      simp only [List.length_cons] at hlen
      have hn : ¬isComplete s := incomplete_of_remaining s hl.consistent (by omega)
      obtain ⟨message, s₁, hstep, _, hm5, _, _, hprep₁, htot₁, hcomp₁, hpt₁, hrem₁, _, _,
        hl₁⟩ :=
        honest_step_exact commit g v s hl hn
      obtain ⟨v', s', sent, chals, hrun, hcons, hpend, hprep, htot, hcomp, hpt, hsl, hcl, h5, hrem,
        hv, hlp, hlock⟩ := ih _ s₁ hl₁ (by omega)
      refine ⟨v', s', message :: sent, logChallenge commit v message g :: chals, ?_, hcons, hpend,
        hprep.trans hprep₁, htot.trans htot₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlock⟩
      · simp only [honestRun, hstep]
        exact hrun
      · rw [hcomp, hcomp₁, List.append_assoc]
        rfl
      · rw [hpt, hpt₁, List.append_assoc]
        rfl
      · simp [hsl]
      · simp [hcl]
      · intro m hm
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact hm5
        · exact h5 m hm
      · simp only [List.length_cons]
        omega
      · rw [hv]
        rfl
      · rw [hlp, List.map_cons, ← List.singleton_append, ← List.append_assoc]
        rfl

/-- "At every step": for any decomposition `pre ++ g :: post` of the gate
messages, the honest run over `pre` reaches `(vᵢ, sᵢ)` with `sᵢ` holding the
tables after `pre.length` binds, and the next actual `Verifier.roundStep`
sets the log claim to `roundValue sᵢ.tables p rᵢ` for the verifier's own log
challenge `rᵢ`, which the prover then binds. Honest prover only. -/
theorem honest_log_chain_step (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (s : ProverState) (hl : Lockstep v s) (pre : List (List Verifier.Ext3))
    (g : List Verifier.Ext3) (post : List (List Verifier.Ext3))
    (hn : (pre ++ g :: post).length ≤ s.tables.remaining) :
    ∃ (vᵢ : Verifier.RoundState) (sᵢ : ProverState) (message : List Element) (sNext : ProverState),
      honestRun commit v s pre = .ok (vᵢ, sᵢ) ∧
      Lockstep vᵢ sᵢ ∧ sᵢ.prepared = s.prepared ∧
      sᵢ.completedRounds.length = s.completedRounds.length + pre.length ∧
      sᵢ.tables.remaining + pre.length = s.tables.remaining ∧
      honestStep commit g vᵢ sᵢ = .ok (Verifier.roundStep commit vᵢ (coupled message g), sNext) ∧
      honestRun commit v s (pre ++ [g]) = .ok (Verifier.roundStep commit vᵢ (coupled message g), sNext) ∧
      computeRound sᵢ.tables s.prepared = some message ∧ message.length = 5 ∧
      (Verifier.roundStep commit vᵢ (coupled message g)).logClaim =
        roundValue sᵢ.tables s.prepared (logChallenge commit vᵢ message g) ∧
      bindTables sᵢ.tables (logChallenge commit vᵢ message g) = some sNext.tables ∧
      sNext.point = sᵢ.point ++ [logChallenge commit vᵢ message g] ∧
      sNext.completedRounds = sᵢ.completedRounds ++ [message] ∧
      Consistent sNext ∧ sNext.tables.remaining + 1 = sᵢ.tables.remaining := by
  simp only [List.length_append, List.length_cons] at hn
  obtain ⟨vᵢ, sᵢ, sent, chals, hrun, hcons, _, hprep, _, hcomp, _, hsl, _, _, hrem, _, _, hlock⟩ :=
    honest_run_exact commit pre v s hl (by omega)
  have hn' : ¬isComplete sᵢ := incomplete_of_remaining sᵢ hcons (by omega)
  obtain ⟨message, sNext, hstep, hcr, hm5, hcons', _, _, _, hcomp', hpt', hrem', htab, hclaim, _⟩ :=
    honest_step_exact commit g vᵢ sᵢ hlock hn'
  refine ⟨vᵢ, sᵢ, message, sNext, hrun, hlock, hprep, ?_, hrem, hstep, ?_, ?_, hm5, ?_, htab, hpt',
    hcomp', hcons', hrem'⟩
  · rw [hcomp, List.length_append, hsl]
  · rw [honest_run_append commit pre [g] v s vᵢ sᵢ hrun]
    simp only [honestRun, hstep]
  · rw [← hprep]
    exact hcr
  · rw [← hprep]
    exact hclaim

/-- The final log claim of an honest run over `pre ++ [g]` is
`roundValue t_{n-1} p r_{n-1}`: the round polynomial of the tables after
`n-1` binds (the last tables on which `round_sum_at` runs), evaluated at the
verifier's last log challenge, which is also the last coordinate of both the
verifier's `logPoint` and the prover's `point`. Honest prover only. -/
theorem honest_log_chain (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (s : ProverState) (hl : Lockstep v s) (pre : List (List Verifier.Ext3))
    (g : List Verifier.Ext3) (hn : pre.length + 1 ≤ s.tables.remaining) :
    ∃ (vLast : Verifier.RoundState) (sLast : ProverState) (message : List Element) (sEnd : ProverState),
      honestRun commit v s pre = .ok (vLast, sLast) ∧
      honestRun commit v s (pre ++ [g]) = .ok (Verifier.roundStep commit vLast (coupled message g), sEnd) ∧
      sLast.completedRounds.length = s.completedRounds.length + pre.length ∧
      computeRound sLast.tables s.prepared = some message ∧ message.length = 5 ∧
      (Verifier.roundStep commit vLast (coupled message g)).logClaim =
        roundValue sLast.tables s.prepared (logChallenge commit vLast message g) ∧
      sEnd.point = sLast.point ++ [logChallenge commit vLast message g] ∧
      (Verifier.roundStep commit vLast (coupled message g)).logPoint =
        vLast.logPoint ++ [(logChallenge commit vLast message g).toVerifier] ∧
      sEnd.completedRounds = sLast.completedRounds ++ [message] ∧
      Consistent sEnd ∧ sEnd.tables.remaining + pre.length + 1 = s.tables.remaining := by
  have hn' : (pre ++ g :: []).length ≤ s.tables.remaining := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨vᵢ, sᵢ, message, sNext, hrun, _, _, hlen, hrem, _, hrun', hcr, hm5, hclaim, _, hpt,
    hcomp, hcons, hrem'⟩ :=
    honest_log_chain_step commit v s hl pre g [] hn'
  exact ⟨vᵢ, sᵢ, message, sNext, hrun, hrun', hlen, hcr, hm5, hclaim, hpt, rfl, hcomp, hcons,
    by omega⟩

/-! ## The source's initial claim -/

/-- verifier_v2.rs:277-278 and OuterLogupExt3Verifier.sol:272-273: both lanes
start from zero with empty points at round index 0. -/
theorem source_start_claims_zero (i : Verifier.Initial) :
    (Verifier.start i).logClaim = Verifier.zero ∧ (Verifier.start i).gateClaim = Verifier.zero ∧
    (Verifier.start i).logPoint = [] ∧ (Verifier.start i).gatePoint = [] ∧
    (Verifier.start i).roundIndex = 0 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The source's zero initial claim is in lockstep with the honest prover's
fresh state exactly when the honest first endpoint sum is zero. This does
NOT assert that the endpoint sum is zero: that is the norm/logUp relation
over the cube, outside this module. Honest prover only. -/
theorem chain_initial_claim (t : Tables) (p : Prepared) (i : Verifier.Initial)
    (h : Shape t p) (h0 : t.boundVariables = 0) (hr : 0 < t.remaining) :
    Lockstep (Verifier.start i) (initialState t p) ↔ endpointSum t p = Verifier.zero := by
  constructor
  · intro hl
    have hn : ¬isComplete (initialState t p) := by
      intro hc
      have : (0 : Nat) = t.remaining := hc
      omega
    exact (hl.claim hn).symm
  · intro hz
    exact ⟨initial_consistent t p h h0, rfl, fun _ => hz.symm⟩

/-- The honest first message, reconstructed by the verifier's constant
recovery from the honest endpoint sum, IS the round polynomial
(`current_round_coefficients_shaped` + the adopted tail reconstruction).
Honest prover only. -/
theorem honest_first_message_polynomial (t : Tables) (p : Prepared)
    (h : Shape t p) (hr : 0 < t.remaining) :
    ∃ message, computeRound t p = some message ∧ message.length = 5 ∧
      OuterRound.polynomial (NormPolynomial.lift (endpointSum t p)) message = roundPolynomial t p := by
  obtain ⟨coefficients, _, hpoly, hround, hlen⟩ := current_round_coefficients_shaped t p h hr
  refine ⟨coefficients.tail, hround, hlen, ?_⟩
  have hne : coefficients ≠ [] := by
    intro hz
    rw [hz] at hlen
    simp at hlen
  rw [lift_endpoint_sum, ← hpoly, OuterInterpolation.reconstruction_from_nonconstant_tail coefficients hne]

/-- The verifier reconstructs the honest first message from the source's ZERO
claim; that reconstruction is the honest round polynomial iff the honest
endpoint sum is zero. Otherwise the two fixed polynomials differ
(`different_claims_give_different_polynomials`). Honest prover only; nothing
is claimed about what an arbitrary prover sends. -/
theorem zero_claim_matches_honest_polynomial_iff (t : Tables) (p : Prepared)
    (h : Shape t p) (hr : 0 < t.remaining) :
    ∃ message, computeRound t p = some message ∧
      (OuterRound.polynomial 0 message = roundPolynomial t p ↔ endpointSum t p = Verifier.zero) := by
  obtain ⟨message, hm, _, hpoly⟩ := honest_first_message_polynomial t p h hr
  refine ⟨message, hm, ?_⟩
  constructor
  · intro he
    rw [← hpoly] at he
    have hsum := OuterRound.polynomial_endpoint_sum_is_claim 0 message
    rw [he, OuterRound.polynomial_endpoint_sum_is_claim] at hsum
    exact congrArg Element.toVerifier hsum
  · intro hz
    rw [← hpoly, hz]
    rfl

/-! ## into_proof_and_point returns what the verifier consumed -/

/-- After exactly `remaining` lockstep rounds the prover is complete and
`into_proof_and_point` (norm_logup.rs:744-758) returns precisely the message
list fed to `Verifier.runRounds` and the verifier's log challenges (in
order); the verifier's `logPoint` is the same list. Honest prover only. -/
theorem honest_extraction_matches_verifier (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (s : ProverState) (hl : Lockstep v s) (gates : List (List Verifier.Ext3))
    (hn : gates.length = s.tables.remaining) :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element)) (chals : List Element),
      honestRun commit v s gates = .ok (v', s') ∧ isComplete s' ∧
      intoProofAndPoint s' = .ok (s.completedRounds ++ sent, s.point ++ chals) ∧
      sent.length = gates.length ∧ (∀ m ∈ sent, m.length = 5) ∧ chals.length = gates.length ∧
      v' = Verifier.runRounds commit v ((sent.map (List.map Element.toVerifier)).zip gates) ∧
      v'.logPoint = v.logPoint ++ chals.map Element.toVerifier := by
  obtain ⟨v', s', sent, chals, hrun, hcons, _, _, _, hcomp, hpt, hsl, hcl, h5, hrem, hv, hlp, _⟩ :=
    honest_run_exact commit gates v s hl (by omega)
  have hcomplete : isComplete s' := by
    unfold isComplete
    rcases hcons with ⟨h1, h2, _, _⟩
    omega
  refine ⟨v', s', sent, chals, hrun, hcomplete, ?_, hsl, h5, hcl, hv, hlp⟩
  rw [proof_extraction_exact s' hcomplete, hcomp, hpt]

/-- From the source's fresh prover state and `Verifier.start`: the extracted
proof is exactly the sent messages and the verifier's log point, and
`Verifier.derivedRounds` (verifier_v2.rs:281-301 as used by `verify`) of any
proof whose `logRounds`/`gateRounds` are those lists is the lockstep verifier
state. The zero-claim hypothesis is explicit. Honest prover only. -/
theorem honest_run_is_derived_rounds (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (t : Tables) (pr : Prepared) (gates : List (List Verifier.Ext3))
    (h : Shape t pr) (h0 : t.boundVariables = 0) (hz : endpointSum t pr = Verifier.zero)
    (hn : gates.length = t.remaining) :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element)) (chals : List Element),
      honestRun e.commitRound (Verifier.start (e.initialTranscript c p)) (initialState t pr) gates =
        .ok (v', s') ∧
      intoProofAndPoint s' = .ok (sent, chals) ∧
      v'.logPoint = chals.map Element.toVerifier ∧
      (p.logRounds = sent.map (List.map Element.toVerifier) → p.gateRounds = gates →
        Verifier.derivedRounds e c p = v') := by
  have hl : Lockstep (Verifier.start (e.initialTranscript c p)) (initialState t pr) :=
    ⟨initial_consistent t pr h h0, rfl, fun _ => hz.symm⟩
  obtain ⟨v', s', sent, chals, hrun, _, hext, _, _, _, hv, hlp⟩ :=
    honest_extraction_matches_verifier e.commitRound _ _ hl gates hn
  refine ⟨v', s', sent, chals, hrun, hext, hlp, fun hlr hgr => ?_⟩
  rw [Verifier.derivedRounds, hlr, hgr, hv]

/-! ## Gate lane: explicit hypothesis, no gate prover -/

/-- The gate lane of the actual coupled step is the verifier's reconstructed
polynomial of the running gate claim and the gate message, at the gate
challenge (unconditional; says nothing about which polynomial that is). -/
theorem gate_lane_is_reconstructed_polynomial (commit : Verifier.CommitRound)
    (v : Verifier.RoundState) (m : Verifier.CoupledMessage) :
    (Verifier.roundStep commit v m).gateClaim =
      ((OuterRound.polynomial (OuterRound.lift v.gateClaim) (m.2.map OuterRound.lift)).eval
        (OuterRound.lift (commit v.transcript v.roundIndex m.1 m.2).gate)).toVerifier :=
  (OuterRound.actual_coupled_round_uses_both_derived_polynomials commit v m).2.1

/-- Gate-lane chaining under an EXPLICIT hypothesis, because no gate prover
with `bind_challenge` is adopted (GateSlotRound models the integer grid of
`current_round` only): if the verifier's reconstruction of the gate message
from the running claim agrees with a polynomial `f` of degree at most `d` at
the `d+1` integer nodes `0..d` (the grid `GateSlotRound.reviewed_degree_grid`
produces, with `d = quotientDegree+2`), and the message has at most `d`
nonconstant coefficients, then the reconstruction is `f` everywhere. -/
theorem gate_claim_from_grid_agreement (claim : Verifier.Ext3) (g : List Verifier.Ext3)
    (f : NormPolynomial.Poly) (d : Nat) (hd : d < Arithmetic.modulus) (hf : f.natDegree ≤ d)
    (hg : g.length ≤ d)
    (hgrid : ∀ i ≤ d, Verifier.evaluateRound claim g (Norm.embed i) = (f.eval (i : Element)).toVerifier) :
    ∀ r : Verifier.Ext3, Verifier.evaluateRound claim g r = (f.eval (OuterRound.lift r)).toVerifier := by
  have hdeg : (OuterRound.polynomial (OuterRound.lift claim) (g.map OuterRound.lift)).natDegree ≤ d :=
    (OuterRound.polynomial_degree_at_most_message_length _ _).trans (by rw [List.length_map]; exact hg)
  have he : ∀ i ≤ d,
      (OuterRound.polynomial (OuterRound.lift claim) (g.map OuterRound.lift)).eval (i : Element) =
      f.eval (i : Element) := by
    intro i hi
    have h := hgrid i hi
    rw [OuterRound.actual_typed_round_is_polynomial_eval] at h
    exact element_eq _ _ h
  have hpoly := OuterInterpolation.interpolation_unique _ _ d hd hdeg hf he
  intro r
  rw [OuterRound.actual_typed_round_is_polynomial_eval, hpoly]

/-- The gate claim after one actual coupled step, under the explicit
grid-agreement hypothesis for that step's gate message: it is `f` at the
verifier's gate challenge. Hypothesis-parameterised; no gate prover. -/
theorem gate_lane_chain_step (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (m : Verifier.CoupledMessage) (f : NormPolynomial.Poly) (d : Nat) (hd : d < Arithmetic.modulus)
    (hf : f.natDegree ≤ d) (hg : m.2.length ≤ d)
    (hgrid : ∀ i ≤ d, Verifier.evaluateRound v.gateClaim m.2 (Norm.embed i) =
      (f.eval (i : Element)).toVerifier) :
    (Verifier.roundStep commit v m).gateClaim =
      (f.eval (OuterRound.lift (commit v.transcript v.roundIndex m.1 m.2).gate)).toVerifier :=
  gate_claim_from_grid_agreement v.gateClaim m.2 f d hd hf hg hgrid _

/-- The checked adapter loop (OuterAdapter.runChecked), when it succeeds on the
honest run's coupled messages and its commit observation agrees with `commit`,
returns the same lockstep verifier state. Honest prover only. -/
theorem checked_adapter_agrees_with_honest_run (hash : OuterInitial.Hash) (commit : Verifier.CommitRound)
    (hc : OuterAdapter.CommitAgrees hash commit) (v : Verifier.RoundState) (s : ProverState)
    (hl : Lockstep v s) (gates : List (List Verifier.Ext3)) (hn : gates.length ≤ s.tables.remaining) :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element)),
      honestRun commit v s gates = .ok (v', s') ∧ s'.completedRounds = s.completedRounds ++ sent ∧
      ∀ u, OuterAdapter.runChecked hash v ((sent.map (List.map Element.toVerifier)).zip gates) = some u →
        u = v' := by
  obtain ⟨v', s', sent, _, hrun, _, _, _, _, hcomp, _, _, _, _, _, hv, _, _⟩ :=
    honest_run_exact commit gates v s hl hn
  refine ⟨v', s', sent, hrun, hcomp, fun u hu => ?_⟩
  rw [hv]
  exact OuterAdapter.checked_success_matches_existing hash commit hc v u _ hu

/-! ## A concrete one-round instance -/

/-- All relation challenges zero (so only the identity-helper term
contributes), one routed wire with `k = 1` and lambda power 1. -/
def exampleChallenges : Norm.Challenges :=
  ⟨Verifier.zero, Verifier.zero, Verifier.zero, Verifier.zero, Verifier.zero, Verifier.zero,
    Verifier.zero, []⟩

def examplePrepared : Prepared := ⟨exampleChallenges, [Verifier.base 1], [1]⟩

/-- One variable left, `eq = [1, -1]` and constant wire/sigma/helper columns,
no public-input bindings. -/
def exampleTables : Tables :=
  ⟨[1, -1], [1, 1], [[2, 2]], [[2, 2]], [[1, 1]], [[1, 1]], [], 0, 1⟩

def exampleCommit : Verifier.CommitRound := fun _ _ _ _ => ⟨[], Norm.embed 3, Norm.embed 7⟩

def exampleInitial : Verifier.Initial := ⟨[], [], [], Verifier.zero, []⟩

def exampleGate : List Verifier.Ext3 := [Norm.embed 1, Norm.embed 2, Norm.embed 3]

/-- The example satisfies the honest prover's constructor invariants. -/
theorem example_shape : Shape exampleTables examplePrepared := by
  unfold Shape ColumnShape exampleTables examplePrepared
  decide

/-- The honest prover's cube sum of this instance is zero, so the source's
zero start claim is in lockstep with it. -/
theorem example_endpoint_sum_zero : endpointSum exampleTables examplePrepared = Verifier.zero := by
  decide

/-- The honest prover's round polynomial of this instance is `(1 - 2x) * 7`: at
the verifier's challenge 3 it is `-35`, nonzero and distinct from both endpoints. -/
theorem example_round_value_at_three :
    roundValue exampleTables examplePrepared 3 = (-(35 : Element)).toVerifier := by
  decide

/-- The example's fresh honest prover state is in lockstep with the source's zero start. -/
theorem example_lockstep :
    Lockstep (Verifier.start exampleInitial) (initialState exampleTables examplePrepared) :=
  (chain_initial_claim exampleTables examplePrepared exampleInitial example_shape rfl (by decide)).mpr
    example_endpoint_sum_zero

/-- n = 1: the honest run succeeds, the verifier's final log claim is the
round polynomial at the challenge 3, its log point is `[3]`, and
`into_proof_and_point` returns the single sent message with `[3]`. Honest
prover only. -/
theorem one_round_example :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (message : List Element),
      honestRun exampleCommit (Verifier.start exampleInitial)
        (initialState exampleTables examplePrepared) [exampleGate] = .ok (v', s') ∧
      computeRound exampleTables examplePrepared = some message ∧ message.length = 5 ∧
      v' = Verifier.roundStep exampleCommit (Verifier.start exampleInitial) (coupled message exampleGate) ∧
      v'.logClaim = roundValue exampleTables examplePrepared 3 ∧
      v'.logClaim = (-(35 : Element)).toVerifier ∧
      v'.logPoint = [Norm.embed 3] ∧
      isComplete s' ∧ intoProofAndPoint s' = .ok ([message], [3]) := by
  obtain ⟨v₀, s₀, message, s₁, hrun0, hrun, _, hcr, hm5, hclaim, hpt, hlp, hcomp, hcons, hrem⟩ :=
    honest_log_chain exampleCommit _ _ example_lockstep [] exampleGate (by decide)
  simp only [honestRun, Outcome.ok.injEq, Prod.mk.injEq] at hrun0
  obtain ⟨rfl, rfl⟩ := hrun0
  have hcomplete : isComplete s₁ := by
    have hrem1 : s₁.tables.remaining + 0 + 1 = 1 := hrem
    unfold isComplete
    rcases hcons with ⟨h1, h2, _, _⟩
    omega
  refine ⟨_, s₁, message, hrun, hcr, hm5, rfl, hclaim, ?_, hlp, hcomplete, ?_⟩
  · rw [← example_round_value_at_three]
    exact hclaim
  · rw [proof_extraction_exact s₁ hcomplete, hcomp, hpt]
    rfl

end Audit.Wire3.OuterClaimChain
