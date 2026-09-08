import Audit.Wire3.ZeroCheckSemantics
import Audit.Wire3.GateSlotRound
import Audit.Wire3.WhirPolynomial

/-!
# The gate alpha zero check: from "the alpha-Horner combination is zero" to
"every filtered gate constraint is zero"

The adopted `Audit.Wire3.ZeroCheckSemantics` closes the multilinear step: for a
`tau` outside `zeroCheckBadSet`, EVERY Boolean-cube row's gate aggregate is zero
(`gate_rows_vanish`).  But a row's aggregate is the alpha-Horner combination of
that row's FILTERED CONSTRAINT VALUES (`GatesComplete.contribution` /
`combineRows`, `Gates.horner`), and "the combination is zero" is NOT "every
constraint is zero".  This module supplies exactly that missing step, and
nothing else.

WHAT IS USED, UNCHANGED, FROM THE ADOPTED DEVELOPMENT
* the slot-first form: `GateSlotCommutation.slotRows` / `rowFilter` /
  `evalPreparedSlots` and `configured_slots_equal_complete`, i.e. the source's
  `vec![ZERO; num_gate_constraints]` slot buffer (gate_ext3.rs:570), its
  `accumulated[slot] += filter*value` write loop (591-594) and its forward power
  reduction (600-608).  The aggregate is NOT re-derived here;
* the slot algebra: `GateSlotAlgebra.horner` / `reduce` / `reduce_horner` /
  `indexed_lookup` / `indexed_length`;
* the polynomial: `WhirPolynomial.ofCoefficients` (constant-term FIRST, matching
  the forward power loop), its `coefficient_exact` and
  `degree_bound_including_empty`, and Mathlib's `Polynomial.roots`;
* the field: the concrete `GoldilocksExt3Field.Element` with its constructed
  `Field` instance — `Element` being a field is what makes `filter * value = 0`
  split into "filter zero" or "value zero";
* the configuration envelope: `Gates.validateConfiguration` /
  `validate_configuration_success` / `Gates.envelope`, which caps
  `c.numGateConstraints` at `123`;
* the bad-event style: `alphaBadSet` MIRRORS THE SHAPE of the adopted
  `ZeroCheckSemantics.zeroCheckBadSet` and `ConditionalSoundness.roundBadSet`
  (empty in the good branch, unconditional card bound).

WHAT IS PROVED
1. `aggregate_is_polynomial_in_alpha`: for a validated configuration the actual
   `GatesComplete.evalCombined` aggregate at EVERY alpha is the evaluation of ONE
   fixed polynomial, whose coefficient list is the alpha-free slot buffer, of
   length exactly `c.numGateConstraints` and natDegree at most
   `c.numGateConstraints - 1`.  `slot_coefficient_exact` /
   `aggregate_polynomial_coefficient` identify coefficient `k` as
   `slotValue ... k`, the SUM over the ordered gate rows of
   `rowFilter g * (gate g's constraint k)` — coefficient IDENTIFICATION, not
   merely a degree bound.
2. `vanishingAlphas_card_succ_le`: EXACT STATEMENT PROVED — a slot list of length
   `L` with a nonzero entry gives a nonzero polynomial, whose root set therefore
   satisfies `card + 1 <= L`, i.e. at most `L-1` roots.
3. `alphaBadSet` with `alphaBadSet_card_bound` (unconditional,
   `card <= L - 1`) and `configured_alphaBadSet_card_bound`
   (`L = c.numGateConstraints <= 123`, so `card <= 122`).
4. `gate_slots_vanish`: the consumable corollary.  Then
   `filteredValue_zero_iff` / `selected_constraint_zero` /
   `active_gate_constraints_vanish` take the step to gate semantics.
5. `gate_constraints_vanish_of_tau_and_alpha` and
   `selected_gate_constraints_vanish_of_tau_and_alpha`: the composition with the
   adopted tau step, PROVED, not merely stated.
   `gate_constraints_vanish_at_derived_challenges` instantiates both challenges
   at the adopted transcript derivation.

THE HONEST STATEMENT ABOUT ZERO-FILTER ROWS.  The source's slot loop restarts at
slot 0 for EVERY gate, so slot `k` of the buffer is the SUM over the configured
gate rows of `filter_g * constraint_(g,k)`, not one gate's value.  A gate whose
selector filter is zero contributes nothing to any slot
(`zero_filter_contributes_nothing`), so its constraints are simply UNCONSTRAINED
by this argument.  That is CORRECT BEHAVIOUR for a row outside a gate's selector
range, and it is why the step to individual constraints
(`active_gate_constraints_vanish`) carries the explicit premises "every other
gate in the ordered list has zero filter" and "this gate's filter is nonzero".
No theorem here claims every constraint of every gate vanishes everywhere;
`example_zero_filter_gate_is_unconstrained` exhibits the gap concretely.

PROVENANCE AND ADAPTIVITY.  Alpha's provenance IS available: the adopted
`TranscriptProvenance.gateAlphaElement` is the derived `gate_alpha`, and
`TranscriptProvenance.derived_columns_at_source_counters` places it at counter
block `9 + 3*degreeBits`, BEFORE the gate tau blocks at `12 + 3*degreeBits + 3i`
— so alpha is drawn before tau, and `gate_constraints_vanish_at_derived_challenges`
is stated at those derived challenges.  ADAPTIVITY IS NOT ADDRESSED.  Both
`hgood` premises are memberships in sets indexed by the PROVER'S OWN TABLES; a
Fiat--Shamir argument fixing those tables by transcript material preceding the
gate-alpha block, and a distribution law for the drawn alpha, are obligations
left to a later module — exactly the obligation `ZeroCheckSemantics` records for
tau.  `alphaBadSet` has the same shape as an entry of
`ConditionalSoundness.badSets` (a `Finset Element` over a SINGLE field
challenge), but it is NOT inserted into `badSets` here.

BOUNDARIES.  No probability statement about any deterministic hash; the density
bound is an EXPLICIT ideal uniform law.  No soundness, extraction, PCS/WHIR,
Merkle, memory-refinement or Rust/Solidity-compilation claim.  Whether the
circuit's aggregate is in fact zero remains circuit truth, outside the model.
`filteredValue`'s `none` branch is unreachable whenever `slotRows` succeeds, and
its `getD` past a gate's constraint count records that the source performs NO
write at that slot for that gate (`GateSlotAlgebra.indexed_preserve_trailing`);
it is not a zero-default read standing in for a source bound.
ROW INDICES ARE NOT BOUNDED BY A COLUMN LENGTH.  The composition theorems of
section 6 require only clauses 1-2 of the adopted
`GateSuffixPolynomial.TableShape` — the two WIDTH equalities
`t.wires.length = c.numWires` and `t.constants.length = c.numConstants` — and
never its column-LENGTH clauses.  A row index `i` at or past a column's length
therefore reads the `List.getD ... 0` padding of `rowWires` / `rowConstants`, so
on such an index the conclusion is a true statement about a ZERO row rather than
about a stored row.  That is inherited verbatim from the adopted
`ZeroCheckSemantics.gateValue` totalisation, which reads its columns the same
way; it is a consequence of not assuming the length clauses, not an extra
assumption made here.  A caller who wants the conclusion to be about stored data
must supply the remaining `TableShape` clauses together with `i < 2 * half`.
Tactic note: as in `ZeroCheckSemantics`, no tactic may evaluate
`Fintype.card Element` or `Finset.univ` on `Element`; the bad set is therefore
built from `Polynomial.roots`, and the density step is routed through the
size-generic `ZeroCheckSemantics.density_of_count`.
-/

set_option maxRecDepth 8000

namespace Audit.Wire3.AlphaZeroCheck
open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.GateSlotAlgebra Audit.Wire3.GateSlotCommutation
open Polynomial

/-! ## 1. The alpha aggregate IS a polynomial evaluation -/

theorem ofCoefficients_eval (coeffs : List Element) (alpha : Element) :
    (WhirPolynomial.ofCoefficients coeffs).eval alpha = horner alpha coeffs := by
  induction coeffs with
  | nil => simp [WhirPolynomial.ofCoefficients, horner]
  | cons t ts ih => simp only [WhirPolynomial.ofCoefficients, horner, eval_add, eval_mul, eval_X,
      eval_C, ih]

theorem ofCoefficients_eval_reduce (coeffs : List Element) (alpha : Element) :
    (WhirPolynomial.ofCoefficients coeffs).eval alpha = reduce alpha coeffs := by
  rw [ofCoefficients_eval, reduce_horner]

/-! ## 2. The alpha-free slot coefficient list -/

def slotCoefficients (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) :
    Option (List Element) :=
  if wires.length ≠ c.numWires ∨ constants.length ≠ c.numConstants then none else
    slotRows c wires constants publicHash gates (List.replicate c.numGateConstraints 0)

theorem prepared_slots_is_coefficient_evaluation (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (alpha : Element) :
    evalPreparedSlots c gates wires constants publicHash alpha =
      (slotCoefficients c gates wires constants publicHash).map
        (fun coeffs => (reduce alpha coeffs).toVerifier) := by
  unfold evalPreparedSlots slotCoefficients
  split
  · rfl
  · cases slotRows c wires constants publicHash gates (List.replicate c.numGateConstraints 0) <;> rfl

theorem combined_is_coefficient_evaluation (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateConfiguration c gates = some ()) :
    GatesComplete.evalCombined c gates wires constants publicHash alpha.toVerifier =
      (slotCoefficients c gates wires constants publicHash).map
        (fun coeffs => (reduce alpha coeffs).toVerifier) := by
  rw [← configured_slots_equal_complete c gates wires constants publicHash alpha hv]
  exact prepared_slots_is_coefficient_evaluation c gates wires constants publicHash alpha

theorem configured_slot_coefficients (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (hv : Gates.validateConfiguration c gates = some ())
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    ∃ coeffs, slotCoefficients c gates wires constants publicHash = some coeffs ∧
      coeffs.length = c.numGateConstraints := by
  have hr := (Gates.validate_configuration_success c gates hv).2
  obtain ⟨result, hs, hlen, _⟩ := validated_rows_commute c gates.length 0 c.numGateConstraints gates
    wires constants publicHash 0 (List.replicate c.numGateConstraints 0) hr hw (by simp)
  exact ⟨result, by simp only [slotCoefficients, hw, hc, ne_eq, not_true_eq_false, or_self,
    ↓reduceIte, hs], by simpa using hlen⟩


/-! ## 3. Which value sits in each constraint slot -/

theorem getD_replicate_zero (n k : Nat) (hk : k < n) :
    (List.replicate n (0 : Element)).getD k 0 = 0 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => rfl
      | succ k => simpa only [List.replicate_succ, List.getD_cons_succ] using ih k (by omega)

/-- The filtered constraint value that gate `g` writes into constraint slot `k`:
the adopted `GateSlotCommutation.rowFilter` times the gate's own unfiltered
constraint `k`.  For `k` at or beyond the gate's constraint count the source
performs NO write at that slot for this gate (adopted
`GateSlotAlgebra.indexed_preserve_trailing`), so the contribution is genuinely
zero rather than a defaulted read.  The `none` branch is unreachable whenever
`slotRows` succeeds, which every theorem below assumes. -/
def filteredValue (c : Gates.Config) (g : Gates.GateInfo) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (k : Nat) : Element :=
  match GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors with
  | some terms => rowFilter c g constants * (wrap terms).getD k 0
  | none => 0

/-- Constraint slot `k` of the whole configured row list: the sum, over the gates
in the actual `slotRows` order, of their filtered constraint values at slot `k`. -/
def slotValue (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (k : Nat) : Element :=
  (gates.map (fun g => filteredValue c g wires constants publicHash k)).sum

theorem slotValue_nil (c : Gates.Config) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (k : Nat) :
    slotValue c [] wires constants publicHash k = 0 := rfl

theorem slotValue_cons (c : Gates.Config) (g : Gates.GateInfo) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (k : Nat) :
    slotValue c (g :: gates) wires constants publicHash k =
      filteredValue c g wires constants publicHash k + slotValue c gates wires constants publicHash k := by
  simp only [slotValue, List.map_cons, List.sum_cons]

/-- (1) SLOT LOOKUP.  Every in-range slot of the executed slot buffer is the old
slot plus the sum of the filtered constraint values written into it. -/
theorem slotRows_lookup (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (buffer result : List Element) (k : Nat) (hk : k < buffer.length)
    (h : slotRows c wires constants publicHash gates buffer = some result) :
    result.getD k 0 = buffer.getD k 0 + slotValue c gates wires constants publicHash k := by
  induction gates generalizing buffer result with
  | nil =>
      simp only [slotRows, Option.some.injEq] at h
      rw [← h, slotValue_nil, add_zero]
  | cons g rest ih =>
      cases he : GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors with
      | none => simp only [slotRows, he, bind, Option.bind] at h
      | some terms =>
          simp only [slotRows, he, bind, Option.bind] at h
          split at h
          · exact absurd h (by simp)
          · split at h
            · exact absurd h (by simp)
            · 
              have hnext : k < (addIndexed (rowFilter c g constants) 0 (wrap terms) buffer).length := by
                rw [indexed_length]; exact hk
              have hstep := ih _ result hnext h
              rw [hstep, indexed_lookup (rowFilter c g constants) (wrap terms) buffer k hk,
                slotValue_cons]
              simp only [filteredValue, he]
              ring

/-- (1) COEFFICIENT IDENTIFICATION.  Entry `k` of the alpha-free slot coefficient
list is EXACTLY the row's filtered constraint value at constraint slot `k`. -/
theorem slot_coefficient_exact (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (coeffs : List Element) (k : Nat) (hk : k < c.numGateConstraints)
    (h : slotCoefficients c gates wires constants publicHash = some coeffs) :
    coeffs.getD k 0 = slotValue c gates wires constants publicHash k := by
  unfold slotCoefficients at h
  split at h
  · exact absurd h (by simp)
  · have hlen : k < (List.replicate c.numGateConstraints (0 : Element)).length := by
      rw [List.length_replicate]; exact hk
    rw [slotRows_lookup c gates wires constants publicHash _ coeffs k hlen h,
      getD_replicate_zero c.numGateConstraints k hk, zero_add]

/-- (1) The SAME identification against Mathlib's polynomial coefficient: the
aggregate polynomial in alpha has the row's filtered constraint values as its
coefficients, in the adopted (constant-term-first) slot order. -/
theorem aggregate_polynomial_coefficient (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (coeffs : List Element) (k : Nat) (hk : k < c.numGateConstraints)
    (h : slotCoefficients c gates wires constants publicHash = some coeffs) :
    (WhirPolynomial.ofCoefficients coeffs).coeff k =
      slotValue c gates wires constants publicHash k := by
  rw [WhirPolynomial.coefficient_exact]
  exact slot_coefficient_exact c gates wires constants publicHash coeffs k hk h

/-- (1) THE AGGREGATE IS THE POLYNOMIAL.  For a validated configuration the
actual `GatesComplete.evalCombined` aggregate at ANY alpha is the evaluation, at
that alpha, of ONE fixed polynomial whose coefficients are the filtered
constraint values of the row, and whose degree is below the configured
constraint count. -/
theorem aggregate_is_polynomial_in_alpha (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (hv : Gates.validateConfiguration c gates = some ())
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    ∃ coeffs : List Element,
      slotCoefficients c gates wires constants publicHash = some coeffs ∧
      coeffs.length = c.numGateConstraints ∧
      (∀ k, k < c.numGateConstraints →
        (WhirPolynomial.ofCoefficients coeffs).coeff k =
          slotValue c gates wires constants publicHash k) ∧
      (WhirPolynomial.ofCoefficients coeffs).natDegree ≤ c.numGateConstraints - 1 ∧
      ∀ alpha : Element, GatesComplete.evalCombined c gates wires constants publicHash alpha.toVerifier
        = some ((WhirPolynomial.ofCoefficients coeffs).eval alpha).toVerifier := by
  obtain ⟨coeffs, hcoeffs, hlen⟩ := configured_slot_coefficients c gates wires constants publicHash hv hw hc
  refine ⟨coeffs, hcoeffs, hlen, fun k hk =>
    aggregate_polynomial_coefficient c gates wires constants publicHash coeffs k hk hcoeffs, ?_, ?_⟩
  · rw [← hlen]; exact WhirPolynomial.degree_bound_including_empty coeffs
  · intro alpha
    rw [combined_is_coefficient_evaluation c gates wires constants publicHash alpha hv, hcoeffs,
      Option.map_some', ofCoefficients_eval_reduce]


/-! ## 4. The alpha bad set -/

/-- Every constraint slot of the row already carries zero.  This is the good
branch: there is then nothing for the alpha challenge to detect. -/
def AllSlotsZero (coeffs : List Element) : Prop := ∀ x ∈ coeffs, x = 0

instance decidableAllSlotsZero (coeffs : List Element) : Decidable (AllSlotsZero coeffs) :=
  inferInstanceAs (Decidable (∀ x ∈ coeffs, x = 0))

/-- A slot list with a nonzero entry gives a NONZERO polynomial: the entry sits
at its own index as a coefficient. -/
theorem ofCoefficients_ne_zero (coeffs : List Element) (h : ¬ AllSlotsZero coeffs) :
    WhirPolynomial.ofCoefficients coeffs ≠ 0 := by
  unfold AllSlotsZero at h
  push_neg at h
  obtain ⟨x, hx, hxz⟩ := h
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx
  intro hzero
  apply hxz
  have hc : (WhirPolynomial.ofCoefficients coeffs).coeff n.val = coeffs.getD n.val 0 :=
    WhirPolynomial.coefficient_exact coeffs n.val
  rw [hzero, coeff_zero, List.getD_eq_get coeffs 0 n.isLt] at hc
  rw [← hn]
  exact hc.symm

theorem coeffs_ne_nil (coeffs : List Element) (h : ¬ AllSlotsZero coeffs) : coeffs ≠ [] := by
  intro hnil
  exact h (by rw [hnil]; intro x hx; simp at hx)

/-- The alphas at which the row's alpha-Horner aggregate vanishes.  These are
exactly the roots of the aggregate polynomial; the `Finset` is built from
`Polynomial.roots` rather than as a `Finset.univ` filter precisely so that no
tactic ever has to unfold `Finset.univ` on the `p^3`-element field. -/
noncomputable def vanishingAlphas (coeffs : List Element) : Finset Element :=
  (WhirPolynomial.ofCoefficients coeffs).roots.toFinset

theorem mem_vanishingAlphas (coeffs : List Element) (a : Element) :
    a ∈ vanishingAlphas coeffs ↔
      (WhirPolynomial.ofCoefficients coeffs ≠ 0 ∧ horner a coeffs = 0) := by
  rw [vanishingAlphas, Multiset.mem_toFinset, mem_roots']
  constructor
  · rintro ⟨hne, hr⟩
    exact ⟨hne, by rw [← ofCoefficients_eval]; exact hr⟩
  · rintro ⟨hne, hz⟩
    refine ⟨hne, ?_⟩
    change (WhirPolynomial.ofCoefficients coeffs).eval a = 0
    rw [ofCoefficients_eval]
    exact hz

/-- With a nonzero slot list the polynomial is nonzero, so membership is exactly
"the aggregate vanishes at this alpha". -/
theorem mem_vanishingAlphas_of_not_all_zero (coeffs : List Element)
    (h : ¬ AllSlotsZero coeffs) (a : Element) :
    a ∈ vanishingAlphas coeffs ↔ horner a coeffs = 0 := by
  rw [mem_vanishingAlphas]
  exact ⟨fun hm => hm.2, fun hz => ⟨ofCoefficients_ne_zero coeffs h, hz⟩⟩

/-- (2) THE ROOT BOUND.  A slot list of length `L` with a nonzero entry gives a
nonzero polynomial of degree at most `L-1`, so the aggregate vanishes at at most
`L-1` alphas — stated without `Nat` subtraction as `card + 1 ≤ L`. -/
theorem vanishingAlphas_card_succ_le (coeffs : List Element) (h : ¬ AllSlotsZero coeffs) :
    (vanishingAlphas coeffs).card + 1 ≤ coeffs.length := by
  have hpos : 0 < coeffs.length := List.length_pos.mpr (coeffs_ne_nil coeffs h)
  have h2 := Multiset.toFinset_card_le (WhirPolynomial.ofCoefficients coeffs).roots
  have h3 := Polynomial.card_roots' (WhirPolynomial.ofCoefficients coeffs)
  have hdeg := WhirPolynomial.degree_bound_including_empty coeffs
  rw [vanishingAlphas]
  omega

theorem vanishingAlphas_card_bound (coeffs : List Element) (h : ¬ AllSlotsZero coeffs) :
    (vanishingAlphas coeffs).card ≤ coeffs.length - 1 := by
  have := vanishingAlphas_card_succ_le coeffs h
  omega

/-- BAD EVENT (gate alpha).  The alphas at which the row's alpha-Horner aggregate
vanishes although some filtered constraint value does NOT.  Empty when every
filtered constraint value is already zero.  This MIRRORS THE SHAPE of the adopted
`ZeroCheckSemantics.zeroCheckBadSet` and of `ConditionalSoundness.roundBadSet`,
whose good branches are likewise `∅`.  Unlike `zeroCheckBadSet` it ranges over a
SINGLE field challenge, the same shape as the entries of
`ConditionalSoundness.badSets`; it is nevertheless NOT inserted into `badSets`
here, and no probability statement about any deterministic hash is made. -/
noncomputable def alphaBadSet (coeffs : List Element) : Finset Element :=
  if AllSlotsZero coeffs then ∅ else vanishingAlphas coeffs

theorem alphaBadSet_empty (coeffs : List Element) (h : AllSlotsZero coeffs) :
    alphaBadSet coeffs = ∅ := by rw [alphaBadSet, if_pos h]

theorem alphaBadSet_of_not_all_zero (coeffs : List Element) (h : ¬ AllSlotsZero coeffs) :
    alphaBadSet coeffs = vanishingAlphas coeffs := by rw [alphaBadSet, if_neg h]

/-- (3) The bad set is small UNCONDITIONALLY. -/
theorem alphaBadSet_card_bound (coeffs : List Element) :
    (alphaBadSet coeffs).card ≤ coeffs.length - 1 := by
  by_cases h : AllSlotsZero coeffs
  · rw [alphaBadSet_empty coeffs h, Finset.card_empty]; exact Nat.zero_le _
  · rw [alphaBadSet_of_not_all_zero coeffs h]; exact vanishingAlphas_card_bound coeffs h

theorem alphaBadSet_card_succ_le (coeffs : List Element) (hne : coeffs ≠ []) :
    (alphaBadSet coeffs).card + 1 ≤ coeffs.length := by
  by_cases h : AllSlotsZero coeffs
  · rw [alphaBadSet_empty coeffs h, Finset.card_empty]
    exact List.length_pos.mpr hne
  · rw [alphaBadSet_of_not_all_zero coeffs h]; exact vanishingAlphas_card_succ_le coeffs h

/-- (3) THE BOUND IN REAL CONFIGURATION QUANTITIES.  The slot list has length
`c.numGateConstraints` (the size of the source's `vec![ZERO; num_gate_constraints]`
slot buffer), which the adopted `Gates.validateConfiguration` envelope caps at
`123`; the bad set therefore has at most `c.numGateConstraints - 1`, hence at most
`122`, elements out of the `p^3` of the field. -/
theorem configured_alphaBadSet_card_bound (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (coeffs : List Element) (hv : Gates.validateConfiguration c gates = some ())
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants)
    (hcoeffs : slotCoefficients c gates wires constants publicHash = some coeffs) :
    coeffs.length = c.numGateConstraints ∧
      (alphaBadSet coeffs).card ≤ c.numGateConstraints - 1 ∧
      c.numGateConstraints ≤ 123 ∧ (alphaBadSet coeffs).card ≤ 122 := by
  obtain ⟨coeffs', hcoeffs', hlen⟩ :=
    configured_slot_coefficients c gates wires constants publicHash hv hw hc
  have hsame : coeffs = coeffs' := Option.some.inj (hcoeffs.symm.trans hcoeffs')
  subst hsame
  have henv := (Gates.validate_configuration_success c gates hv).1
  simp only [Gates.envelope] at henv
  have hb := alphaBadSet_card_bound coeffs
  rw [hlen] at hb
  exact ⟨hlen, hb, henv.2.2.1, by omega⟩

/-- (3) Explicit uniform-law density, in the shape of
`ZeroCheckSemantics.zeroCheckBadSet_density_bound`: an IDEAL law over the field,
NOT a statement about any deterministic hash.  Routed through the size-generic
`ZeroCheckSemantics.density_of_count` so that no tactic evaluates
`Fintype.card Element`. -/
theorem alphaBadSet_density_bound (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (coeffs : List Element) (hv : Gates.validateConfiguration c gates = some ())
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants)
    (hcoeffs : slotCoefficients c gates wires constants publicHash = some coeffs) :
    ((alphaBadSet coeffs).card : ℚ) / ((Fintype.card Element : ℚ))
      ≤ (122 : ℚ) / ((Fintype.card Element : ℚ)) := by
  have hq : 0 < Fintype.card Element := Fintype.card_pos
  have h122 :=
    (configured_alphaBadSet_card_bound c gates wires constants publicHash coeffs hv hw hc hcoeffs).2.2.2
  exact ZeroCheckSemantics.density_of_count (alphaBadSet coeffs).card 122 (Fintype.card Element)
    (Fintype.card Element) hq hq (Nat.mul_le_mul_right _ h122)

/-! ## 5. The consumable corollary -/

/-- (4) THE ALPHA-CHECK STEP, in pure coefficient form.  A vanishing aggregate at
an alpha OUTSIDE the bad set forces every slot coefficient to be zero.  This is
the exact analogue of `ZeroCheckSemantics.cube_zero_of_extension_zero`. -/
theorem all_slots_zero_of_aggregate_zero (coeffs : List Element) (alpha : Element)
    (hzero : horner alpha coeffs = 0) (hgood : alpha ∉ alphaBadSet coeffs) :
    ∀ x ∈ coeffs, x = 0 := by
  by_cases h : AllSlotsZero coeffs
  · exact h
  · exact absurd (by
      rw [alphaBadSet_of_not_all_zero coeffs h, mem_vanishingAlphas_of_not_all_zero coeffs h]
      exact hzero) hgood

theorem getD_eq_zero_of_all_zero (coeffs : List Element) (h : ∀ x ∈ coeffs, x = 0)
    (k : Nat) : coeffs.getD k 0 = 0 := by
  by_cases hk : k < coeffs.length
  · rw [List.getD_eq_get coeffs 0 hk]
    exact h _ (List.get_mem coeffs k hk)
  · rw [List.getD_eq_default coeffs 0 (Nat.not_lt.mp hk)]

/-- (4) THE CONSUMABLE COROLLARY.  If a row's actual `GatesComplete.evalCombined`
aggregate is zero and the gate alpha lies OUTSIDE this row's alpha bad set, then
EVERY filtered constraint value of that row is zero: every entry of the slot
buffer is zero, and for every constraint slot `k` below the configured
`c.numGateConstraints` the value `slotValue ... k` is zero.

READ THIS EXACTLY.  Because the source's write loop restarts at slot 0 for every
gate, `slotValue ... k` is the SUM over the ordered gate rows of
`rowFilter g * (gate g's constraint k)`, not one gate's value.  Gates whose
filter is zero contribute nothing to that sum and are left unconstrained;
`active_gate_constraints_vanish` takes the further step for a row on which a
single gate is selected. -/
theorem gate_slots_vanish (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (coeffs : List Element)
    (hv : Gates.validateConfiguration c gates = some ())
    (hcoeffs : slotCoefficients c gates wires constants publicHash = some coeffs)
    (hzero : GatesComplete.evalCombined c gates wires constants publicHash alpha.toVerifier
      = some Verifier.zero)
    (hgood : alpha ∉ alphaBadSet coeffs) :
    (∀ x ∈ coeffs, x = 0) ∧
      ∀ k, k < c.numGateConstraints → slotValue c gates wires constants publicHash k = 0 := by
  have heval : (reduce alpha coeffs).toVerifier = Verifier.zero := by
    have h := combined_is_coefficient_evaluation c gates wires constants publicHash alpha hv
    rw [hcoeffs, Option.map_some', hzero] at h
    exact (Option.some.inj h).symm
  have hh : horner alpha coeffs = 0 := by
    rw [← reduce_horner]
    exact element_eq _ 0 heval
  have hall := all_slots_zero_of_aggregate_zero coeffs alpha hh hgood
  refine ⟨hall, fun k hk => ?_⟩
  rw [← slot_coefficient_exact c gates wires constants publicHash coeffs k hk hcoeffs]
  exact getD_eq_zero_of_all_zero coeffs hall k

/-! ### From "filtered constraint value is zero" to the gate semantics -/

theorem wrap_getD (terms : List Verifier.Ext3) (k : Nat) (hk : k < terms.length) :
    (wrap terms).getD k 0 = ⟨terms.get ⟨k, hk⟩⟩ := by
  induction terms generalizing k with
  | nil => simp at hk
  | cons t ts ih =>
      cases k with
      | zero => rfl
      | succ k =>
          simpa only [wrap, List.map_cons, List.getD_cons_succ, List.get_cons_succ] using
            ih k (by simpa using hk)

theorem element_mk_eq_zero (x : Verifier.Ext3) : (⟨x⟩ : Element) = 0 ↔ x = Verifier.zero := by
  constructor
  · intro h; exact congrArg Element.toVerifier h
  · intro h; exact element_eq _ 0 h

/-- HONESTY: where a gate's selector filter is ZERO the gate contributes nothing
to any constraint slot, WHATEVER its constraints evaluate to.  A zero filter is
the correct behaviour for a row outside that gate's selector range, and the
constraints of such a gate are simply UNCONSTRAINED by this argument. -/
theorem zero_filter_contributes_nothing (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (h : rowFilter c g constants = 0) (k : Nat) :
    filteredValue c g wires constants publicHash k = 0 := by
  unfold filteredValue
  cases GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors with
  | none => rfl
  | some terms =>
      show rowFilter c g constants * (wrap terms).getD k 0 = 0
      rw [h, zero_mul]

/-- The EXACT content of "this gate's filtered constraint value at slot `k` is
zero": either the selector filter is zero (the gate is not selected on this row),
or the gate's own constraint `k` really is zero.  `Element` is a field, so there
is no third possibility. -/
theorem filteredValue_zero_iff (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (terms : List Verifier.Ext3) (k : Nat) (hk : k < terms.length)
    (hterms : GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors
      = some terms) :
    filteredValue c g wires constants publicHash k = 0 ↔
      (rowFilter c g constants = 0 ∨ terms.get ⟨k, hk⟩ = Verifier.zero) := by
  simp only [filteredValue, hterms, wrap_getD terms k hk]
  rw [mul_eq_zero]
  exact or_congr Iff.rfl (element_mk_eq_zero _)

/-- (4) Where the selector filter is NONZERO, the CONSTRAINT itself is zero. -/
theorem selected_constraint_zero (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (terms : List Verifier.Ext3) (k : Nat) (hk : k < terms.length)
    (hterms : GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors
      = some terms)
    (hactive : rowFilter c g constants ≠ 0)
    (hzero : filteredValue c g wires constants publicHash k = 0) :
    terms.get ⟨k, hk⟩ = Verifier.zero := by
  rcases (filteredValue_zero_iff c g wires constants publicHash terms k hk hterms).mp hzero with h | h
  · exact absurd h hactive
  · exact h

/-! ### Isolating one selected gate row -/

theorem slotValue_append_cons (c : Gates.Config) (pre : List Gates.GateInfo)
    (g : Gates.GateInfo) (post : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (k : Nat) :
    slotValue c (pre ++ g :: post) wires constants publicHash k =
      slotValue c pre wires constants publicHash k +
        (filteredValue c g wires constants publicHash k +
          slotValue c post wires constants publicHash k) := by
  simp only [slotValue, List.map_append, List.sum_append, List.map_cons, List.sum_cons]

theorem slotValue_zero_of_filters_zero (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (k : Nat)
    (h : ∀ g ∈ gates, rowFilter c g constants = 0) :
    slotValue c gates wires constants publicHash k = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
  exact zero_filter_contributes_nothing c g wires constants publicHash (h g hg) k

/-- On a row where exactly one configured gate is selected (every OTHER gate in
the ordered row list has zero filter — the Plonky2 selector-group situation), the
slot value IS that gate's filtered constraint value. -/
theorem active_gate_slot_value (c : Gates.Config) (pre : List Gates.GateInfo)
    (g : Gates.GateInfo) (post : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (k : Nat)
    (hpre : ∀ g' ∈ pre, rowFilter c g' constants = 0)
    (hpost : ∀ g' ∈ post, rowFilter c g' constants = 0) :
    slotValue c (pre ++ g :: post) wires constants publicHash k =
      filteredValue c g wires constants publicHash k := by
  rw [slotValue_append_cons,
    slotValue_zero_of_filters_zero c pre wires constants publicHash k hpre,
    slotValue_zero_of_filters_zero c post wires constants publicHash k hpost, zero_add, add_zero]

/-- (4) THE GATE-SEMANTIC STEP.  On a row where a single gate `g` is selected,
"every filtered constraint value of the row is zero" says exactly that EVERY
CONSTRAINT of `g` is zero.  Gates with a zero filter on this row are untouched by
the conclusion, which is correct: they are outside their selector range.

WHY `hterms` AND `hlen` ARE HYPOTHESES HERE.  No configuration validity is in
scope in this lemma — `c` and the row list are arbitrary — so neither the
existence of `terms` nor the bound `terms.length ≤ c.numGateConstraints` is
derivable: an unvalidated `g` may make `GatesComplete.evaluateUnfiltered` return
`none`, and an unvalidated `c` may declare a `numGateConstraints` below the
gate's own constraint count.  Both ARE derivable once
`Gates.validateConfiguration` is available, and
`selected_gate_constraints_vanish_of_tau_and_alpha` below derives them from its
`hv` rather than assuming them. -/
theorem active_gate_constraints_vanish (c : Gates.Config) (pre : List Gates.GateInfo)
    (g : Gates.GateInfo) (post : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (terms : List Verifier.Ext3)
    (hpre : ∀ g' ∈ pre, rowFilter c g' constants = 0)
    (hpost : ∀ g' ∈ post, rowFilter c g' constants = 0)
    (hactive : rowFilter c g constants ≠ 0)
    (hterms : GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors
      = some terms)
    (hlen : terms.length ≤ c.numGateConstraints)
    (hslots : ∀ k, k < c.numGateConstraints →
      slotValue c (pre ++ g :: post) wires constants publicHash k = 0) :
    ∀ x ∈ terms, x = Verifier.zero := by
  intro x hx
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx
  have hk : n.val < c.numGateConstraints := lt_of_lt_of_le n.isLt hlen
  have hz : filteredValue c g wires constants publicHash n.val = 0 := by
    rw [← active_gate_slot_value c pre g post wires constants publicHash n.val hpre hpost]
    exact hslots n.val hk
  have := selected_constraint_zero c g wires constants publicHash terms n.val n.isLt hterms hactive hz
  rw [← hn]
  simpa using this

/-! ## 6. Composing the tau step and the alpha step -/

/-- The wire column reads of one Boolean row, EXACTLY as
`ZeroCheckSemantics.gateValue` / `GateDenseRound.rowTerm` make them. -/
def rowWires (t : GateSuffixPolynomial.Tables) (index : Nat) : List Verifier.Ext3 :=
  t.wires.map (fun column => (column.getD index 0).toVerifier)

def rowConstants (t : GateSuffixPolynomial.Tables) (index : Nat) : List Verifier.Ext3 :=
  t.constants.map (fun column => (column.getD index 0).toVerifier)

theorem rowWires_length (t : GateSuffixPolynomial.Tables) (index : Nat) :
    (rowWires t index).length = t.wires.length := List.length_map _ _

theorem rowConstants_length (t : GateSuffixPolynomial.Tables) (index : Nat) :
    (rowConstants t index).length = t.constants.length := List.length_map _ _

/-- Under configuration validity and the two table widths (the first two clauses
of the adopted `GateSuffixPolynomial.TableShape`), the row's evaluator really
returns a value, so `gateValue = 0` is the genuine statement that the row's
aggregate is the field zero, not the `none` totalisation. -/
theorem combined_zero_of_gateValue_zero (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : GateSuffixPolynomial.Tables) (index : Nat)
    (hv : Gates.validateConfiguration c gates = some ())
    (hw : t.wires.length = c.numWires) (hc : t.constants.length = c.numConstants)
    (hzero : ZeroCheckSemantics.gateValue c gates publicHash alpha t index = 0) :
    GatesComplete.evalCombined c gates (rowWires t index) (rowConstants t index) publicHash
      alpha.toVerifier = some Verifier.zero := by
  obtain ⟨v, hev⟩ := GatesComplete.valid_configuration_always_evaluates c gates
    (rowWires t index) (rowConstants t index) publicHash alpha.toVerifier hv
    (by rw [rowWires_length]; exact hw) (by rw [rowConstants_length]; exact hc)
  have hg : ZeroCheckSemantics.gateValue c gates publicHash alpha t index
      = NormPolynomial.lift v := by
    unfold ZeroCheckSemantics.gateValue
    rw [show (t.wires.map (fun column => (column.getD index 0).toVerifier)) = rowWires t index from rfl,
      show (t.constants.map (fun column => (column.getD index 0).toVerifier)) = rowConstants t index from rfl,
      hev]
  rw [hev]
  have : NormPolynomial.lift v = (0 : Element) := by rw [← hg]; exact hzero
  exact congrArg some (congrArg Element.toVerifier this)

/-- (5) THE COMPOSITION, PROVED.  `tau` outside the adopted
`ZeroCheckSemantics.zeroCheckBadSet` and `alpha` outside this module's
`alphaBadSet` for the row together force EVERY filtered constraint value of that
row to be zero.

The `tau` half is the adopted `ZeroCheckSemantics.gate_rows_vanish`; the `alpha`
half is `gate_slots_vanish`.  The conclusion is per-slot: for slot `k`, the SUM
over the ordered gate rows of `filter_g * constraint_(g,k)` is zero.  Rows whose
filter is zero contribute nothing to that sum and remain unconstrained; see
`active_gate_constraints_vanish` for the step to individual constraints of a
selected gate. -/
theorem gate_constraints_vanish_of_tau_and_alpha (c : Gates.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base) (alpha : Element)
    (t : GateSuffixPolynomial.Tables) (tau : List Element)
    (hv : Gates.validateConfiguration c gates = some ())
    (hw : t.wires.length = c.numWires) (hc : t.constants.length = c.numConstants)
    (heq : t.eq = EqTableProvenance.eqTable tau)
    (hsum : GateDenseRound.cubeSum c gates publicHash alpha t (2 ^ tau.length) = 0)
    (hgoodTau : ZeroCheckSemantics.tupleOf tau ∉
      ZeroCheckSemantics.zeroCheckBadSet tau.length
        (ZeroCheckSemantics.gateValue c gates publicHash alpha t))
    (i : Nat) (hi : i < 2 ^ tau.length) (coeffs : List Element)
    (hcoeffs : slotCoefficients c gates (rowWires t i) (rowConstants t i) publicHash = some coeffs)
    (hgoodAlpha : alpha ∉ alphaBadSet coeffs) :
    ∀ k, k < c.numGateConstraints →
      slotValue c gates (rowWires t i) (rowConstants t i) publicHash k = 0 := by
  have hrow := (ZeroCheckSemantics.gate_rows_vanish c gates publicHash alpha t tau heq hsum
    hgoodTau i hi).1
  exact (gate_slots_vanish c gates (rowWires t i) (rowConstants t i) publicHash alpha coeffs hv
    hcoeffs (combined_zero_of_gateValue_zero c gates publicHash alpha t i hv hw hc hrow)
    hgoodAlpha).2

/-- The gate singled out by `pre ++ g :: post` sits at index `pre.length` of that
list, so the adopted `Gates.every_configured_gate_checked` applies to it. -/
theorem getOpt_append_cons (pre : List Gates.GateInfo) (g : Gates.GateInfo)
    (post : List Gates.GateInfo) : (pre ++ g :: post).get? pre.length = some g := by
  induction pre with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- The two evaluator facts about the singled-out gate that
`active_gate_constraints_vanish` needs are CONSEQUENCES of configuration
validity, not extra assumptions: the adopted `Gates.every_configured_gate_checked`
validates `g` at its own row index, `GatesComplete.every_validated_family_evaluates`
turns that into an actual constraint list, and
`Gates.validate_gate_success ... .2.2.2.2.1` (`numConstraints = r.constraints`)
transports the validated bound `r.constraints ≤ c.numGateConstraints` onto that
list's length. -/
theorem validated_selected_gate_terms (c : Gates.Config) (pre : List Gates.GateInfo)
    (g : Gates.GateInfo) (post : List Gates.GateInfo) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base)
    (hv : Gates.validateConfiguration c (pre ++ g :: post) = some ())
    (hw : wires.length = c.numWires) :
    ∃ terms, GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors
        = some terms ∧ terms.length ≤ c.numGateConstraints := by
  obtain ⟨r, hvg, hrc⟩ := Gates.every_configured_gate_checked c (pre ++ g :: post) hv pre.length g
    (getOpt_append_cons pre g post)
  obtain ⟨terms, hterms, hlterms⟩ := GatesComplete.every_validated_family_evaluates c pre.length
    (pre ++ g :: post).length g r wires constants publicHash hvg hw
  refine ⟨terms, hterms, ?_⟩
  rw [hlterms, (Gates.validate_gate_success c pre.length (pre ++ g :: post).length g r hvg).2.2.2.2.1]
  exact hrc

/-- (5) …and, on a row where exactly one gate is selected, EVERY CONSTRAINT of
that gate is zero.

NO EVALUATOR HYPOTHESIS IS ASSUMED.  Earlier this theorem took the singled-out
gate's constraint list `terms`, its evaluator equation, and the bound
`terms.length ≤ c.numGateConstraints` as hypotheses.  Both are derived here from
`hv` alone by `validated_selected_gate_terms`, so the statement is STRICTLY
STRONGER than that earlier form: it now also ASSERTS that `g`'s evaluator
succeeds on this row.  The previous shape is recovered verbatim as
`selected_gate_constraints_vanish_of_tau_and_alpha_of_terms`. -/
theorem selected_gate_constraints_vanish_of_tau_and_alpha (c : Gates.Config)
    (pre : List Gates.GateInfo) (g : Gates.GateInfo) (post : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : GateSuffixPolynomial.Tables) (tau : List Element)
    (hv : Gates.validateConfiguration c (pre ++ g :: post) = some ())
    (hw : t.wires.length = c.numWires) (hc : t.constants.length = c.numConstants)
    (heq : t.eq = EqTableProvenance.eqTable tau)
    (hsum : GateDenseRound.cubeSum c (pre ++ g :: post) publicHash alpha t (2 ^ tau.length) = 0)
    (hgoodTau : ZeroCheckSemantics.tupleOf tau ∉
      ZeroCheckSemantics.zeroCheckBadSet tau.length
        (ZeroCheckSemantics.gateValue c (pre ++ g :: post) publicHash alpha t))
    (i : Nat) (hi : i < 2 ^ tau.length) (coeffs : List Element)
    (hcoeffs : slotCoefficients c (pre ++ g :: post) (rowWires t i) (rowConstants t i) publicHash
      = some coeffs)
    (hgoodAlpha : alpha ∉ alphaBadSet coeffs)
    (hpre : ∀ g' ∈ pre, rowFilter c g' (rowConstants t i) = 0)
    (hpost : ∀ g' ∈ post, rowFilter c g' (rowConstants t i) = 0)
    (hactive : rowFilter c g (rowConstants t i) ≠ 0) :
    ∃ terms, GatesComplete.evaluateUnfiltered g (rowWires t i) (rowConstants t i) publicHash
        c.numSelectors = some terms ∧ ∀ x ∈ terms, x = Verifier.zero := by
  obtain ⟨terms, hterms, hlen⟩ := validated_selected_gate_terms c pre g post (rowWires t i)
    (rowConstants t i) publicHash hv (by rw [rowWires_length]; exact hw)
  exact ⟨terms, hterms,
    active_gate_constraints_vanish c pre g post (rowWires t i) (rowConstants t i) publicHash terms
      hpre hpost hactive hterms hlen
      (gate_constraints_vanish_of_tau_and_alpha c (pre ++ g :: post) publicHash alpha t tau hv hw hc
        heq hsum hgoodTau i hi coeffs hcoeffs hgoodAlpha)⟩

/-- The previous shape of the theorem above, kept so that the strengthening is
visible: for ANY `terms` the evaluator does return on this row, every entry is
zero.  No `terms.length ≤ c.numGateConstraints` hypothesis is needed any more. -/
theorem selected_gate_constraints_vanish_of_tau_and_alpha_of_terms (c : Gates.Config)
    (pre : List Gates.GateInfo) (g : Gates.GateInfo) (post : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : GateSuffixPolynomial.Tables) (tau : List Element)
    (hv : Gates.validateConfiguration c (pre ++ g :: post) = some ())
    (hw : t.wires.length = c.numWires) (hc : t.constants.length = c.numConstants)
    (heq : t.eq = EqTableProvenance.eqTable tau)
    (hsum : GateDenseRound.cubeSum c (pre ++ g :: post) publicHash alpha t (2 ^ tau.length) = 0)
    (hgoodTau : ZeroCheckSemantics.tupleOf tau ∉
      ZeroCheckSemantics.zeroCheckBadSet tau.length
        (ZeroCheckSemantics.gateValue c (pre ++ g :: post) publicHash alpha t))
    (i : Nat) (hi : i < 2 ^ tau.length) (coeffs : List Element)
    (hcoeffs : slotCoefficients c (pre ++ g :: post) (rowWires t i) (rowConstants t i) publicHash
      = some coeffs)
    (hgoodAlpha : alpha ∉ alphaBadSet coeffs)
    (terms : List Verifier.Ext3)
    (hterms : GatesComplete.evaluateUnfiltered g (rowWires t i) (rowConstants t i) publicHash
      c.numSelectors = some terms)
    (hpre : ∀ g' ∈ pre, rowFilter c g' (rowConstants t i) = 0)
    (hpost : ∀ g' ∈ post, rowFilter c g' (rowConstants t i) = 0)
    (hactive : rowFilter c g (rowConstants t i) ≠ 0) :
    ∀ x ∈ terms, x = Verifier.zero := by
  obtain ⟨terms', hterms', hzero⟩ := selected_gate_constraints_vanish_of_tau_and_alpha c pre g post
    publicHash alpha t tau hv hw hc heq hsum hgoodTau i hi coeffs hcoeffs hgoodAlpha hpre hpost
    hactive
  rw [Option.some.inj (hterms.symm.trans hterms')]
  exact hzero

/-- (5, provenance) The SAME composition with both challenges taken from the
adopted transcript derivation: `alpha` is `TranscriptProvenance.gateAlphaElement`
and `tau` is `TranscriptProvenance.gateTauColumn`.  The adopted
`TranscriptProvenance.derived_columns_at_source_counters` places gate alpha at
counter block `9+3*degreeBits` and gate tau at `12+3*degreeBits+3i`, i.e. ALPHA
IS DRAWN BEFORE TAU.  Both `hgood` premises remain for a later module: nothing
here says the drawn challenges are uniform or independent of the prover's tables
(ADAPTIVITY IS NOT ADDRESSED).

THIS IS WEAKER THAN THE ADOPTED DERIVED FORM.  The adopted
`ZeroCheckSemantics.gate_rows_vanish_of_derived_tau` takes its eq-table premise
through `EqTableProvenance.GateEqProvenance s (TranscriptProvenance.gateTauColumn
hash cfg p)` for an actual `GateTerminalBinding.ProverState s`, and reads its
tables out of that same `s`.  Here `heq : t.eq = EqTableProvenance.eqTable
(TranscriptProvenance.gateTauColumn hash cfg pr)` is taken RAW, on a bare
`GateSuffixPolynomial.Tables t` that is tied to no prover state: only the eq
column is pinned to the derived tau, while `t.wires` and `t.constants` are
arbitrary lists of the right widths.  So the challenges are derived, but the
TABLES the conclusion speaks about are NOT connected to any prover's committed
tables, and the `numVars` half of `GateEqProvenance` is not required.  Restating
this over a `ProverState` with `GateEqProvenance` — as
`gate_rows_vanish_of_derived_tau` does — is left to a later module. -/
theorem gate_constraints_vanish_at_derived_challenges
    (hash : TranscriptProvenance.Hash) (cfg : Verifier.Config) (pr : Verifier.Proof)
    (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (t : GateSuffixPolynomial.Tables)
    (hv : Gates.validateConfiguration c gates = some ())
    (hw : t.wires.length = c.numWires) (hc : t.constants.length = c.numConstants)
    (heq : t.eq = EqTableProvenance.eqTable (TranscriptProvenance.gateTauColumn hash cfg pr))
    (hsum : GateDenseRound.cubeSum c gates publicHash
      (TranscriptProvenance.gateAlphaElement hash cfg pr) t (2 ^ cfg.degreeBits) = 0)
    (hgoodTau : ZeroCheckSemantics.tupleOf (TranscriptProvenance.gateTauColumn hash cfg pr) ∉
      ZeroCheckSemantics.zeroCheckBadSet (TranscriptProvenance.gateTauColumn hash cfg pr).length
        (ZeroCheckSemantics.gateValue c gates publicHash
          (TranscriptProvenance.gateAlphaElement hash cfg pr) t))
    (i : Nat) (hi : i < 2 ^ cfg.degreeBits) (coeffs : List Element)
    (hcoeffs : slotCoefficients c gates (rowWires t i) (rowConstants t i) publicHash = some coeffs)
    (hgoodAlpha : TranscriptProvenance.gateAlphaElement hash cfg pr ∉ alphaBadSet coeffs) :
    ∀ k, k < c.numGateConstraints →
      slotValue c gates (rowWires t i) (rowConstants t i) publicHash k = 0 := by
  have hlen : (TranscriptProvenance.gateTauColumn hash cfg pr).length = cfg.degreeBits :=
    (TranscriptProvenance.derived_column_lengths hash cfg pr).2
  refine gate_constraints_vanish_of_tau_and_alpha c gates publicHash
    (TranscriptProvenance.gateAlphaElement hash cfg pr) t
    (TranscriptProvenance.gateTauColumn hash cfg pr) hv hw hc heq (by rw [hlen]; exact hsum)
    hgoodTau i (by rw [hlen]; exact hi) coeffs hcoeffs hgoodAlpha

/-! ## 7. Concrete examples -/

/-- Orientation: the slot list is CONSTANT-TERM FIRST, as the source's forward
power loop reads it.  At `alpha = 0` the aggregate is slot `0`. -/
theorem example_alpha_zero_selects_first_slot : horner (0 : Element) [3, 4, 5] = 3 := by decide

theorem example_coefficient_order :
    (WhirPolynomial.ofCoefficients [(3 : Element), 4, 5]).coeff 0 = 3 ∧
    (WhirPolynomial.ofCoefficients [(3 : Element), 4, 5]).coeff 1 = 4 ∧
    (WhirPolynomial.ofCoefficients [(3 : Element), 4, 5]).coeff 2 = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [WhirPolynomial.coefficient_exact]; decide

/-- A row whose second constraint slot is nonzero. -/
def exampleSlots : List Element := [0, 1]

theorem example_not_all_slots_zero : ¬ AllSlotsZero exampleSlots := by
  intro h
  exact one_ne_zero (h 1 (by simp [exampleSlots]))

/-- The aggregate of that row is the polynomial `alpha`. -/
theorem example_aggregate_at_zero : horner (0 : Element) exampleSlots = 0 := by decide

theorem example_aggregate_at_one : horner (1 : Element) exampleSlots = 1 := by decide

/-- (6) THE ALPHA BAD SET IS GENUINELY NONEMPTY, so the `alpha` condition of the
consumable corollary is NOT vacuous: at `alpha = 0` the row's aggregate vanishes
even though its second filtered constraint value does not. -/
theorem example_alphaBadSet_nonempty : (alphaBadSet exampleSlots).Nonempty := by
  refine ⟨0, ?_⟩
  rw [alphaBadSet_of_not_all_zero exampleSlots example_not_all_slots_zero,
    mem_vanishingAlphas_of_not_all_zero exampleSlots example_not_all_slots_zero]
  exact example_aggregate_at_zero

/-- …and a good `alpha` outside it does exist for the same row. -/
theorem example_good_alpha : (1 : Element) ∉ alphaBadSet exampleSlots := by
  rw [alphaBadSet_of_not_all_zero exampleSlots example_not_all_slots_zero,
    mem_vanishingAlphas_of_not_all_zero exampleSlots example_not_all_slots_zero,
    example_aggregate_at_one]
  exact one_ne_zero

/-- The alpha condition is exactly what rules out the false accept: the row has a
nonzero filtered constraint value, yet its aggregate vanishes at `alpha = 0`. -/
theorem example_alpha_condition_necessary :
    (1 : Element) ∈ exampleSlots ∧ (1 : Element) ≠ 0 ∧
      horner (0 : Element) exampleSlots = 0 ∧ horner (1 : Element) exampleSlots ≠ 0 := by
  refine ⟨by simp [exampleSlots], one_ne_zero, example_aggregate_at_zero, ?_⟩
  rw [example_aggregate_at_one]
  exact one_ne_zero

/-- The bad set for this two-slot row has at most one element. -/
theorem example_alphaBadSet_card : (alphaBadSet exampleSlots).card ≤ 1 := by
  have h := alphaBadSet_card_bound exampleSlots
  simpa [exampleSlots] using h

/-- A nonzero bad alpha also occurs: `[1,1]` is the polynomial `alpha + 1`. -/
def exampleSlots' : List Element := [1, 1]

theorem example_not_all_slots_zero_alt : ¬ AllSlotsZero exampleSlots' := by
  intro h
  exact one_ne_zero (h 1 (by simp [exampleSlots']))

theorem example_nonzero_bad_alpha : (-1 : Element) ∈ alphaBadSet exampleSlots' := by
  rw [alphaBadSet_of_not_all_zero exampleSlots' example_not_all_slots_zero_alt,
    mem_vanishingAlphas_of_not_all_zero exampleSlots' example_not_all_slots_zero_alt]
  decide

/-! ### A row on which a gate's selector filter is zero -/

/-- A no-constraint gate in a two-row selector group, with a two-selector
configuration so that the source's UNUSED_SELECTOR factor is present. -/
def exampleGate : Gates.GateInfo := ⟨0, 0, 0, 2, 0, 0, 0, 0, 0⟩

def exampleConfig : Gates.Config := ⟨2, 3, 1, 160, 8⟩

/-- A FULL-WIDTH constant opening for `exampleConfig`: three entries, because
`exampleConfig.numConstants = 3`.  The source's constant-width `ensure!`
(gate_ext3.rs:560-565, `constants.len() == context.num_constants`) — modelled by
the `constants.length ≠ c.numConstants` guard of `slotCoefficients` /
`GatesComplete.evalCombined` — would reject any shorter opening, so the examples
below really are stated on an ADMISSIBLE row.  Entry `0`, the one read at
`exampleGate.selectorIndex`, carries the source's UNUSED_SELECTOR marker
`4294967295`; entries `1` (the second selector column) and `2` (the single local
constant) are zero and play no part in the filter. -/
def exampleConstants : List Verifier.Ext3 :=
  [Gates.embed 4294967295, Verifier.zero, Verifier.zero]

/-- The example row passes the source's constant-width check. -/
theorem example_constants_width : exampleConstants.length = exampleConfig.numConstants := rfl

theorem example_zero_filter :
    rowFilter exampleConfig exampleGate exampleConstants = 0 := by
  apply element_eq
  show Gates.computeFilter exampleGate (Gates.embed 4294967295) true = Verifier.zero
  exact Gates.unused_selector_zero_filter exampleGate

/-- (6) HONESTY, CONCRETELY.  On this row the gate's filter is zero, so it
contributes zero to EVERY constraint slot whatever its constraints evaluate to.
"Every filtered constraint value of the row is zero" therefore says NOTHING about
this gate's constraints — which is the correct behaviour for a row outside the
gate's selector range, and exactly why `active_gate_constraints_vanish` needs its
`rowFilter ≠ 0` premise. -/
theorem example_zero_filter_gate_is_unconstrained
    (wires : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (k : Nat) :
    filteredValue exampleConfig exampleGate wires exampleConstants publicHash k = 0 :=
  zero_filter_contributes_nothing exampleConfig exampleGate wires exampleConstants publicHash
    example_zero_filter k

end Audit.Wire3.AlphaZeroCheck
