import Audit.Wire3.GateRandomPolynomial

/-!
Checked degree/evaluation bridge for TWELVE concrete families: IDs 0,1,2,3,
5,6,7,8,9,10,11,12. Missing nonlinear Poseidon 4 and Coset 13 deliberately
remain NONE in this symbolic dispatcher. The executable GatesComplete audit
dispatcher still evaluates ALL fourteen, including their zero-filter branch
erasure from the previously frozen candidate.

Every supported formula's degree is proved from its literal computation.
Both wire and constant columns are affine; metadata/public hash/aggregation
alpha are fixed. No degree oracle or constraint-truth assumption is used.
Configuration validation and input-length boundaries are explicit; these are
not new runtime checks. Full-source/Yul/ABI, MLE endpoint provenance, circuit
truth, PCS and Fiat-Shamir distributions remain outside these theorems.
-/
namespace Audit.Wire3.GateTwelvePolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateBasicPolynomial
open Audit.Wire3.GateLoopPolynomial Audit.Wire3.GateRandomPolynomial Polynomial

def LoopSupported (g : Gates.GateInfo) : Prop :=
  g.gateId = 8 ∨ g.gateId = 9 ∨ g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12
def Supported (g : Gates.GateInfo) : Prop := Audit.Wire3.GateCheckedPolynomial.Supported g ∨ LoopSupported g

noncomputable def loopPolys (g : Gates.GateInfo) (wires constants : List P) (offset : Nat) : Option (List P) :=
  match g.gateId with
  | 8 => some (exponentiationPolys wires g.numOrConsts)
  | 9 => some (baseSumPolys wires g.numOrConsts g.param2)
  | 10 => some (reducingPolys wires g.numOrConsts false)
  | 11 => some (reducingPolys wires g.numOrConsts true)
  | 12 => some (randomAccessPolys wires constants offset g.numOrConsts g.param2 g.param3)
  | _ => none

noncomputable def unfilteredPolys (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) : Option (List P) :=
  if 8 ≤ g.gateId then loopPolys g wires constants offset
  else Audit.Wire3.GateCheckedPolynomial.unfilteredPolys g wires constants publicHash offset

theorem loop_supported_large (g : Gates.GateInfo) (h : LoopSupported g) : 8 ≤ g.gateId := by
  rcases h with h | h | h | h | h <;> omega

theorem old_supported_small (g : Gates.GateInfo) (h : Audit.Wire3.GateCheckedPolynomial.Supported g) :
    g.gateId < 8 := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem unsupported_polynomial_dispatch_none (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (hs : ¬Supported g) :
    unfilteredPolys g wires constants publicHash offset = none := by
  have ho : ¬Audit.Wire3.GateCheckedPolynomial.Supported g := fun h => hs (Or.inl h)
  have hl : ¬LoopSupported g := fun h => hs (Or.inr h)
  unfold unfilteredPolys
  split
  · unfold loopPolys
    simp only [LoopSupported,not_or] at hl
    split <;> simp_all
  · exact Audit.Wire3.GateCheckedPolynomial.unsupported_polynomial_dispatch_none g wires constants publicHash offset ho

theorem supported_polynomials_exist (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (hs : Supported g) :
    ∃ terms, unfilteredPolys g wires constants publicHash offset = some terms := by
  rcases hs with ho | hl
  · simpa only [unfilteredPolys,if_neg (Nat.not_le.mpr (old_supported_small g ho))] using
      Audit.Wire3.GateCheckedPolynomial.supported_polynomials_exist g wires constants publicHash offset ho
  · have hi := loop_supported_large g hl
    simp only [unfilteredPolys,if_pos hi]
    rcases hl with h | h | h | h | h
    all_goals simp only [loopPolys,h]; exact ⟨_,rfl⟩

theorem loop_polynomial_actual (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (terms : List P) (x : Element)
    (hs : LoopSupported g) (hp : loopPolys g wires constants offset = some terms) :
    GatesComplete.evaluateUnfiltered g (columnValues wires x) (columnValues constants x)
      publicHash offset = some (columnValues terms x) := by
  rcases hs with hid | hid | hid | hid | hid
  all_goals
    simp only [loopPolys,hid,Option.some.injEq] at hp
    subst terms
    simp only [GatesComplete.evaluateUnfiltered,GatesAdditional.dispatchUnchecked,hid,
      Nat.reduceEqDiff,Nat.reduceLeDiff,↓reduceIte,exponentiation_list_actual,
      base_sum_list_actual,reducing_list_actual,random_access_actual]

theorem polynomial_dispatch_actual_evaluation (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (terms : List P) (x : Element)
    (hs : Supported g) (hp : unfilteredPolys g wires constants publicHash offset = some terms) :
    GatesComplete.evaluateUnfiltered g (columnValues wires x) (columnValues constants x)
      publicHash offset = some (columnValues terms x) := by
  rcases hs with ho | hl
  · simp only [unfilteredPolys,if_neg (Nat.not_le.mpr (old_supported_small g ho))] at hp
    exact Audit.Wire3.GateCheckedPolynomial.polynomial_dispatch_actual_evaluation g wires constants publicHash offset terms x ho hp
  · simp only [unfilteredPolys,if_pos (loop_supported_large g hl)] at hp
    exact loop_polynomial_actual g wires constants publicHash offset terms x hl hp

theorem loop_terms_degree (g : Gates.GateInfo) (wires constants : List P)
    (offset : Nat) (terms : List P) (r : Gates.Requirements)
    (hs : LoopSupported g) (hr : Gates.requirements g = some r)
    (hp : loopPolys g wires constants offset = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ terms, p.natDegree ≤ r.degree := by
  rcases hs with hid | hid | hid | hid | hid
  all_goals
    simp only [Gates.requirements,hid] at hr
    split at hr
    · rename_i hmeta
      simp only [Option.some.injEq] at hr
      subst r
      simp only [loopPolys,hid,Option.some.injEq] at hp
      subst terms
      first
      | exact exponentiation_list_degree wires g.numOrConsts hw
      | exact base_sum_list_degree wires g.numOrConsts g.param2 (by
          simp only [Bool.and_eq_true,Gates.supportedBase,decide_eq_true_eq] at hmeta
          omega) hw
      | exact reducing_list_degree wires g.numOrConsts false hw
      | exact reducing_list_degree wires g.numOrConsts true hw
      | exact random_access_degree wires constants offset g.numOrConsts g.param2 g.param3 (by omega) hw hc
    · simp at hr

theorem validated_polynomial_terms_degree (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) (terms : List P) (r : Gates.Requirements)
    (hs : Supported g) (hr : Gates.requirements g = some r)
    (hp : unfilteredPolys g wires constants publicHash offset = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ terms, p.natDegree ≤ r.degree := by
  rcases hs with ho | hl
  · simp only [unfilteredPolys,if_neg (Nat.not_le.mpr (old_supported_small g ho))] at hp
    exact Audit.Wire3.GateCheckedPolynomial.validated_polynomial_terms_degree g wires constants publicHash offset terms r ho hr hp hw hc
  · simp only [unfilteredPolys,if_pos (loop_supported_large g hl)] at hp
    exact loop_terms_degree g wires constants offset terms r hl hr hp hw hc

/-- The original contribution polynomial is reused without modifying it. -/
noncomputable def contributionPoly := Audit.Wire3.GateCheckedPolynomial.contributionPoly

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
  simp only [contributionPoly,Audit.Wire3.GateCheckedPolynomial.contributionPoly,value_mul,
    selector_actual_evaluation,read_poly_is_actual_read,actual_horner_eval]

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
  obtain ⟨terms,hp⟩ := supported_polynomials_exist g (affineColumns wireEndpoints)
    (affineColumns constantEndpoints) publicHash c.numSelectors hs
  refine ⟨contributionPoly c g terms (affineColumns constantEndpoints) alpha,?_,?_⟩
  · exact checked_contribution_degree c i gates.length g r _ _ terms publicHash alpha hs hr hp
      (affine_columns_have_degree_one wireEndpoints) (affine_columns_have_degree_one constantEndpoints)
  · intro x
    constructor
    · exact checked_contribution_exact c i gates.length g r _ _ terms publicHash alpha x hs hr
        (by simpa only [affine_columns_preserve_length] using hw) hp
    · exact GatesComplete.valid_configuration_always_evaluates c gates _ _ publicHash alpha.toVerifier hv
        (by simpa only [column_values_preserve_length,affine_columns_preserve_length] using hw)
        (by simpa only [column_values_preserve_length,affine_columns_preserve_length] using hc)

theorem affine_weighted_contribution_degree (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P)
    (publicHash : Nat → Verifier.Base) (alpha left right : Element)
    (hs : Supported g) (hv : Gates.validateGate c row total g = some r)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    (affine left right * contributionPoly c g terms constants alpha).natDegree ≤ c.quotientDegree+2 := by
  have hd := checked_contribution_degree c row total g r wires constants terms publicHash alpha hs hv hp hw hc
  exact (mul_degree_bound _ _ 1 (c.quotientDegree+1) (affine_degree left right) hd).trans (by omega)

end Audit.Wire3.GateTwelvePolynomial
