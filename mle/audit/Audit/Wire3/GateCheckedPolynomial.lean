import Audit.Wire3.GateMdsPolynomial

/-!
# Checked seven-family contribution polynomials

Symbolic dispatch is deliberately partial: IDs 0,1,2,3,5,6,7 only. Other IDs
return NONE, not a silently successful zero polynomial. All fourteen actual
families' pointwise zero-filter erasure is proved separately in the foundation.

This module derives an actual contribution polynomial of degree at most q+1
from the actual per-gate validation and literal family equations. The affine
wrapper additionally derives both wire and constant degree bounds from their
endpoints. Full configured entry and concrete list lengths are explicit in the
entry wrapper. Fixed public hash, metadata, tables, and aggregation alpha do
not vary with the row-round variable. Multiplication by an explicitly affine
weight raises the bound to q+2; this does NOT assume or prove actual row-eq
provenance, a gate-truth predicate, MLE/circuit soundness, transcript randomness,
PCS binding or Rust/Solidity/compiler refinement.
-/
namespace Audit.Wire3.GateCheckedPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial
open Audit.Wire3.GateBasicPolynomial Audit.Wire3.GateMdsPolynomial Polynomial

def Supported (g : Gates.GateInfo) : Prop :=
  g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨
  g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7

noncomputable def unfilteredPolys (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) : Option (List P) :=
  match g.gateId with
  | 0 => some []
  | 1 => some (constantPolys wires constants offset g.numOrConsts)
  | 2 => some (publicInputPolys wires publicHash)
  | 3 => some (arithmeticPolys wires constants offset g.numOrConsts)
  | 5 => some (mdsPolys wires)
  | 6 => some (arithmeticExtensionPolys wires constants offset g.numOrConsts)
  | 7 => some (multiplicationExtensionPolys wires constants offset g.numOrConsts)
  | _ => none

theorem unsupported_polynomial_dispatch_none (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (h : ¬Supported g) :
    unfilteredPolys g wires constants publicHash offset = none := by
  simp only [Supported, not_or] at h
  simp only [unfilteredPolys]
  split <;> simp_all

theorem supported_polynomials_exist (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (hs : Supported g) :
    ∃ terms, unfilteredPolys g wires constants publicHash offset = some terms := by
  rcases hs with h | h | h | h | h | h | h
  all_goals simp only [unfilteredPolys,h]; exact ⟨_,rfl⟩

theorem polynomial_dispatch_actual_evaluation (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (terms : List P) (x : Element)
    (hs : Supported g) (hp : unfilteredPolys g wires constants publicHash offset = some terms) :
    GatesComplete.evaluateUnfiltered g (columnValues wires x) (columnValues constants x)
      publicHash offset = some (columnValues terms x) := by
  rcases hs with hid | hid | hid | hid | hid | hid | hid
  all_goals
    simp only [unfilteredPolys,hid,Option.some.injEq] at hp
    subst terms
    simp only [GatesComplete.evaluateUnfiltered,Gates.evaluateUnfiltered,hid,
      OfNat.ofNat_ne_zero, Nat.reduceEqDiff, Nat.reduceLeDiff, ↓reduceIte,
      constant_evaluation_exact, public_input_evaluation_exact, arithmetic_list_evaluation_exact,
      arithmetic_extension_evaluation_exact, multiplication_extension_evaluation_exact,
      mds_list_actual_eval]
  rfl

theorem validated_polynomial_terms_degree (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (terms : List P) (r : Gates.Requirements)
    (hs : Supported g) (hr : Gates.requirements g = some r)
    (hp : unfilteredPolys g wires constants publicHash offset = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ terms, p.natDegree ≤ r.degree := by
  rcases hs with hid | hid | hid | hid | hid | hid | hid
  all_goals
    simp only [Gates.requirements,hid] at hr
    split at hr
    · simp only [Option.some.injEq] at hr
      subst r
      simp only [unfilteredPolys,hid,Option.some.injEq] at hp
      subst terms
      first
      | solve | simp
      | exact constant_degree wires constants offset g.numOrConsts hw hc
      | exact public_input_degree wires publicHash hw
      | exact arithmetic_list_degree wires constants offset g.numOrConsts hw hc
      | exact mds_list_degree wires hw
      | exact arithmetic_extension_degree wires constants offset g.numOrConsts hw hc
      | exact multiplication_extension_degree wires constants offset g.numOrConsts hw hc
    · simp at hr

noncomputable def contributionPoly (c : Gates.Config) (g : Gates.GateInfo)
    (terms constants : List P) (alpha : Element) : P :=
  selectorPoly g (readPoly constants g.selectorIndex) (decide (1 < c.numSelectors)) *
    hornerPoly terms alpha

/-- The exact list-length check is derived from actual validated dispatch;
even the zero-filter path evaluates the SAME literal polynomial pointwise. -/
theorem checked_contribution_exact (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P)
    (publicHash : Nat → Verifier.Base) (alpha x : Element)
    (hs : Supported g) (hv : Gates.validateGate c row total g = some r)
    (hw : wires.length = c.numWires)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms) :
    GatesComplete.contribution c g (columnValues wires x) (columnValues constants x)
      publicHash alpha.toVerifier = some (value (contributionPoly c g terms constants alpha) x) := by
  have he := polynomial_dispatch_actual_evaluation g wires constants publicHash c.numSelectors terms x hs hp
  obtain ⟨actual,ha,hl⟩ := GatesComplete.every_validated_family_evaluates c row total g r
    (columnValues wires x) (columnValues constants x) publicHash hv
    (by simpa only [column_values_preserve_length] using hw)
  have heq : actual = columnValues terms x := Option.some.inj (ha.symm.trans he)
  subst actual
  rw [actual_contribution_branch_erased c g _ _ publicHash alpha.toVerifier _ he hl]
  simp only [contributionPoly,value_mul,selector_actual_evaluation,read_poly_is_actual_read,
    actual_horner_eval]

theorem checked_contribution_degree (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hs : Supported g) (hv : Gates.validateGate c row total g = some r)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    (contributionPoly c g terms constants alpha).natDegree ≤ c.quotientDegree+1 := by
  have hh := Gates.validate_gate_success c row total g r hv
  have ht := validated_polynomial_terms_degree g wires constants publicHash c.numSelectors terms r
    hs hh.2.2.2.1 hp hw hc
  have hf := selector_poly_degree_bound c row total g (readPoly constants g.selectorIndex)
    hh.2.1 (read_poly_degree constants 1 g.selectorIndex hc)
  have ha := fixed_alpha_horner_degree terms alpha r.degree ht
  have hm := mul_degree_bound _ _ (Gates.filterDegree c g) r.degree hf ha
  exact hm.trans (by have := hh.2.2.2.2.2.2.2; omega)

/-- Both wire and constant columns are actual affine interpolation, not
constant coefficients. The polynomial is fixed before the quantified x. -/
theorem affine_checked_contribution (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wireEndpoints constantEndpoints : List (Element × Element))
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hs : Supported g) (hv : Gates.validateGate c row total g = some r)
    (hw : wireEndpoints.length = c.numWires) :
    ∃ polynomial : P,
      polynomial.natDegree ≤ c.quotientDegree+1 ∧
      ∀ x, GatesComplete.contribution c g (columnValues (affineColumns wireEndpoints) x)
        (columnValues (affineColumns constantEndpoints) x) publicHash alpha.toVerifier =
        some (value polynomial x) := by
  obtain ⟨terms,hp⟩ := supported_polynomials_exist g (affineColumns wireEndpoints)
    (affineColumns constantEndpoints) publicHash c.numSelectors hs
  refine ⟨contributionPoly c g terms (affineColumns constantEndpoints) alpha, ?_, ?_⟩
  · exact checked_contribution_degree c row total g r _ _ terms publicHash alpha hs hv hp
      (affine_columns_have_degree_one wireEndpoints) (affine_columns_have_degree_one constantEndpoints)
  · intro x
    exact checked_contribution_exact c row total g r _ _ terms publicHash alpha x hs hv
      (by simpa only [affine_columns_preserve_length] using hw) hp

/-- Pure polynomial bound for one explicitly affine weight. No assertion
that this weight is the actual MLE equality weight is hidden in the theorem. -/
theorem affine_weighted_contribution_degree (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P)
    (publicHash : Nat → Verifier.Base) (alpha left right : Element)
    (hs : Supported g) (hv : Gates.validateGate c row total g = some r)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    (affine left right * contributionPoly c g terms constants alpha).natDegree ≤ c.quotientDegree+2 := by
  have hd := checked_contribution_degree c row total g r wires constants terms publicHash alpha hs hv hp hw hc
  have hm := mul_degree_bound _ _ 1 (c.quotientDegree+1) (affine_degree left right) hd
  exact hm.trans (by omega)

/-- Full configured entry, ALL fourteen families. The unfiltered terms and
branch-erasure equation are obtained for an actual configured row. Success
of the real combined evaluator is retained, so BOTH source list-length
guards and the full configuration guard occur in this statement. -/
theorem every_configured_family_branch_erased (c : Gates.Config) (gates : List Gates.GateInfo)
    (i : Nat) (g : Gates.GateInfo) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (alpha : Verifier.Ext3)
    (hv : Gates.validateConfiguration c gates = some ()) (hg : gates.get? i = some g)
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    (∃ result, GatesComplete.evalCombined c gates wires constants publicHash alpha = some result) ∧
    ∃ terms,
      GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors = some terms ∧
      terms.length = g.numConstraints ∧
      GatesComplete.contribution c g wires constants publicHash alpha = some (Verifier.mul
        (Gates.computeFilter g (Gates.readValue constants g.selectorIndex) (decide (1 < c.numSelectors)))
        (Gates.horner terms alpha)) := by
  obtain ⟨r,hr,_⟩ := Gates.every_configured_gate_checked c gates hv i g hg
  exact ⟨GatesComplete.valid_configuration_always_evaluates c gates wires constants publicHash alpha hv hw hc,
    every_validated_family_branch_erased c i gates.length g r wires constants publicHash alpha hr hw⟩

/-- A selected supported row inside the actual fully checked configuration.
This is NOT a degree bound for a combination containing the other families. -/
theorem fully_configured_affine_row (c : Gates.Config) (gates : List Gates.GateInfo)
    (i : Nat) (g : Gates.GateInfo) (wireEndpoints constantEndpoints : List (Element × Element))
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hs : Supported g) (hv : Gates.validateConfiguration c gates = some ())
    (hg : gates.get? i = some g) (hw : wireEndpoints.length = c.numWires)
    (hc : constantEndpoints.length = c.numConstants) :
    ∃ polynomial : P, polynomial.natDegree ≤ c.quotientDegree+1 ∧
      ∀ x,
        GatesComplete.contribution c g (columnValues (affineColumns wireEndpoints) x)
          (columnValues (affineColumns constantEndpoints) x) publicHash alpha.toVerifier =
          some (value polynomial x) ∧
        ∃ result, GatesComplete.evalCombined c gates (columnValues (affineColumns wireEndpoints) x)
          (columnValues (affineColumns constantEndpoints) x) publicHash alpha.toVerifier = some result := by
  obtain ⟨r,hr,_⟩ := Gates.every_configured_gate_checked c gates hv i g hg
  obtain ⟨polynomial,hd,he⟩ := affine_checked_contribution c i gates.length g r wireEndpoints constantEndpoints
    publicHash alpha hs hr hw
  refine ⟨polynomial,hd,fun x => ⟨he x,?_⟩⟩
  exact GatesComplete.valid_configuration_always_evaluates c gates _ _ publicHash alpha.toVerifier hv
    (by simpa only [column_values_preserve_length,affine_columns_preserve_length] using hw)
    (by simpa only [column_values_preserve_length,affine_columns_preserve_length] using hc)

/-- Ordinary symbolic example: allowing the local coefficient column to
vary genuinely yields cubic degree, not a quadratic arithmetic constraint. -/
theorem varying_coefficient_arithmetic_polynomial :
    arithmeticPoly X 0 X X 0 0 = -(X^3 : P) := by
  unfold arithmeticPoly
  ring

theorem varying_coefficient_arithmetic_degree :
    (arithmeticPoly X 0 X X 0 0).natDegree = 3 := by
  rw [varying_coefficient_arithmetic_polynomial]
  simp

end Audit.Wire3.GateCheckedPolynomial
