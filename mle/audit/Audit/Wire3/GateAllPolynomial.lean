import Audit.Wire3.GatePoseidonPolynomial

/-!
ALL FOURTEEN concrete gate-family polynomial bridges, under the actual gate
validation/input-length boundary. No per-family evaluator or degree hypothesis
fills the former Poseidon/Coset holes. Coset uses the SAME exact wire prefix as
actual dispatch and derives its layout from actual validated execution.
The inherited literal selector/Horner polynomial gives q+1 per contribution,
or q+2 after an explicit affine weight. Both wire and constant columns vary;
alpha/public hash/metadata are fixed. No circuit truth, committed endpoint
provenance, aggregate soundness, FS uniformity, PCS or source/Yul refinement.
-/
namespace Audit.Wire3.GateAllPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Polynomial

noncomputable def unfilteredPolys (g : Gates.GateInfo) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (offset : Nat) : Option (List P) :=
  if g.gateId=4 then some (Audit.Wire3.GatePoseidonPolynomial.poseidonPolys wires)
  else if g.gateId=13 then some (Audit.Wire3.GateCosetPolynomial.cosetPolys
    (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2)) g.numOrConsts g.param2)
  else Audit.Wire3.GateTwelvePolynomial.unfilteredPolys g wires constants publicHash offset

theorem other_known_family_supported (g : Gates.GateInfo) (hk : g.gateId < 14)
    (h4 : g.gateId ≠ 4) (h13 : g.gateId ≠ 13) : Audit.Wire3.GateTwelvePolynomial.Supported g := by
  unfold Audit.Wire3.GateTwelvePolynomial.Supported Audit.Wire3.GateTwelvePolynomial.LoopSupported
    Audit.Wire3.GateCheckedPolynomial.Supported
  omega

theorem all_validated_families_have_polynomials (c : Gates.Config) (row total : Nat)
    (g : Gates.GateInfo) (r : Gates.Requirements) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (hv : Gates.validateGate c row total g = some r) :
    ∃ terms, unfilteredPolys g wires constants publicHash c.numSelectors = some terms := by
  have hk := (Gates.validate_gate_success c row total g r hv).2.2.1
  by_cases h4 : g.gateId=4
  · simp only [unfilteredPolys,if_pos h4]; exact ⟨_,rfl⟩
  · by_cases h13 : g.gateId=13
    · simp only [unfilteredPolys,if_neg h4,if_pos h13]; exact ⟨_,rfl⟩
    · simpa only [unfilteredPolys,if_neg h4,if_neg h13] using
        Audit.Wire3.GateTwelvePolynomial.supported_polynomials_exist g wires constants publicHash c.numSelectors
          (other_known_family_supported g hk h4 h13)

theorem column_values_take (polys : List P) (count : Nat) (x : Element) :
    columnValues (polys.take count) x = (columnValues polys x).take count := List.map_take _ _ _

theorem take_degree (polys : List P) (count : Nat) (hp : ∀ p ∈ polys, p.natDegree ≤ 1) :
    ∀ p ∈ polys.take count, p.natDegree ≤ 1 := by
  intro p h
  have ha : p ∈ polys.take count ++ polys.drop count := List.mem_append.mpr (Or.inl h)
  rw [List.take_append_drop] at ha
  exact hp p ha

/-- This helper extracts Coset's checked layout from the actual validated
dispatcher, not from a free layout hypothesis or an unchecked decoder. -/
theorem validated_coset_layout (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants : List Verifier.Ext3)
    (hv : Gates.validateGate c row total g = some r) (hg : g.gateId=13)
    (hw : wires.length=c.numWires) :
    GatesAdditionalCoset.layoutValid (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2))
      g.numOrConsts g.param2 := by
  obtain ⟨actual,ha,_⟩ := GatesAdditional.validated_coset_dispatch c row total g r wires constants hv hg hw
  simp only [GatesAdditional.dispatchUnchecked,hg] at ha
  exact (GatesAdditionalCoset.evaluated_length_and_layout _ _ _ _ ha).1

theorem all_validated_polynomial_evaluations (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P) (publicHash : Nat → Verifier.Base)
    (x : Element) (hv : Gates.validateGate c row total g = some r) (hw : wires.length=c.numWires)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms) :
    GatesComplete.evaluateUnfiltered g (columnValues wires x) (columnValues constants x) publicHash c.numSelectors =
      some (columnValues terms x) := by
  have hk := (Gates.validate_gate_success c row total g r hv).2.2.1
  by_cases h4 : g.gateId=4
  · simp only [unfilteredPolys,if_pos h4,Option.some.injEq] at hp
    subst terms
    simp only [GatesComplete.evaluateUnfiltered,if_pos h4,Audit.Wire3.GatePoseidonPolynomial.poseidon_actual]
  · by_cases h13 : g.gateId=13
    · simp only [unfilteredPolys,if_neg h4,if_pos h13,Option.some.injEq] at hp
      subst terms
      have hl := validated_coset_layout c row total g r (columnValues wires x) (columnValues constants x) hv h13
        (by simpa only [column_values_preserve_length] using hw)
      simp only [GatesComplete.evaluateUnfiltered,h13,Nat.reduceEqDiff,Nat.reduceLeDiff,↓reduceIte,
        GatesAdditional.dispatchUnchecked,GatesAdditionalCoset.evaluate,hl,
        Audit.Wire3.GateCosetPolynomial.coset_actual,column_values_take]
    · simp only [unfilteredPolys,if_neg h4,if_neg h13] at hp
      exact Audit.Wire3.GateTwelvePolynomial.polynomial_dispatch_actual_evaluation g wires constants publicHash
        c.numSelectors terms x (other_known_family_supported g hk h4 h13) hp

theorem all_validated_polynomial_degrees (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P) (publicHash : Nat → Verifier.Base)
    (hv : Gates.validateGate c row total g = some r)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∀ p ∈ terms, p.natDegree ≤ r.degree := by
  have hh := Gates.validate_gate_success c row total g r hv
  have hr := hh.2.2.2.1
  by_cases h4 : g.gateId=4
  · simp only [Gates.requirements,h4] at hr
    split at hr
    · simp only [Option.some.injEq] at hr
      subst r
      simp only [unfilteredPolys,if_pos h4,Option.some.injEq] at hp
      subst terms
      exact Audit.Wire3.GatePoseidonPolynomial.poseidon_degree wires hw
    · simp at hr
  · by_cases h13 : g.gateId=13
    · simp only [Gates.requirements,h13] at hr
      split at hr
      · rename_i hmeta
        simp only [Option.some.injEq] at hr
        subst r
        simp only [unfilteredPolys,if_neg h4,if_pos h13,Option.some.injEq] at hp
        subst terms
        exact Audit.Wire3.GateCosetPolynomial.coset_degree _ g.numOrConsts g.param2 (take_degree wires _ hw) (by omega)
      · simp at hr
    · simp only [unfilteredPolys,if_neg h4,if_neg h13] at hp
      exact Audit.Wire3.GateTwelvePolynomial.validated_polynomial_terms_degree g wires constants publicHash c.numSelectors
        terms r (other_known_family_supported g hh.2.2.1 h4 h13) hr hp hw hc

noncomputable def contributionPoly := Audit.Wire3.GateCheckedPolynomial.contributionPoly

theorem all_validated_contributions_exact (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P) (publicHash : Nat → Verifier.Base)
    (alpha x : Element) (hv : Gates.validateGate c row total g = some r) (hw : wires.length=c.numWires)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms) :
    GatesComplete.contribution c g (columnValues wires x) (columnValues constants x) publicHash alpha.toVerifier =
      some (value (contributionPoly c g terms constants alpha) x) := by
  have he := all_validated_polynomial_evaluations c row total g r wires constants terms publicHash x hv hw hp
  obtain ⟨actual,ha,hl⟩ := GatesComplete.every_validated_family_evaluates c row total g r
    (columnValues wires x) (columnValues constants x) publicHash hv
    (by simpa only [column_values_preserve_length] using hw)
  have heq : actual = columnValues terms x := Option.some.inj (ha.symm.trans he)
  subst actual
  rw [actual_contribution_branch_erased c g _ _ publicHash alpha.toVerifier _ he hl]
  simp only [contributionPoly,Audit.Wire3.GateCheckedPolynomial.contributionPoly,value_mul,
    selector_actual_evaluation,read_poly_is_actual_read,actual_horner_eval]

theorem all_validated_contribution_degree (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P) (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateGate c row total g = some r)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    (contributionPoly c g terms constants alpha).natDegree ≤ c.quotientDegree+1 := by
  have hh := Gates.validate_gate_success c row total g r hv
  have ht := all_validated_polynomial_degrees c row total g r wires constants terms publicHash hv hp hw hc
  have hf := selector_poly_degree_bound c row total g (readPoly constants g.selectorIndex)
    hh.2.1 (read_poly_degree constants 1 g.selectorIndex hc)
  have ha := fixed_alpha_horner_degree terms alpha r.degree ht
  exact (mul_degree_bound _ _ (Gates.filterDegree c g) r.degree hf ha).trans
    (by have := hh.2.2.2.2.2.2.2; omega)

/-- No Supported premise remains: all fourteen validated configured rows.
The fixed polynomial is chosen before the universally quantified field x. -/
theorem fully_configured_affine_row (c : Gates.Config) (gates : List Gates.GateInfo)
    (i : Nat) (g : Gates.GateInfo) (wireEndpoints constantEndpoints : List (Element × Element))
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateConfiguration c gates = some ()) (hg : gates.get? i = some g)
    (hw : wireEndpoints.length=c.numWires) (hc : constantEndpoints.length=c.numConstants) :
    ∃ polynomial : P, polynomial.natDegree ≤ c.quotientDegree+1 ∧
      ∀ x,
        GatesComplete.contribution c g (columnValues (affineColumns wireEndpoints) x)
          (columnValues (affineColumns constantEndpoints) x) publicHash alpha.toVerifier = some (value polynomial x) ∧
        ∃ result, GatesComplete.evalCombined c gates (columnValues (affineColumns wireEndpoints) x)
          (columnValues (affineColumns constantEndpoints) x) publicHash alpha.toVerifier = some result := by
  obtain ⟨r,hr,_⟩ := Gates.every_configured_gate_checked c gates hv i g hg
  obtain ⟨terms,hp⟩ := all_validated_families_have_polynomials c i gates.length g r
    (affineColumns wireEndpoints) (affineColumns constantEndpoints) publicHash hr
  refine ⟨contributionPoly c g terms (affineColumns constantEndpoints) alpha,?_,?_⟩
  · exact all_validated_contribution_degree c i gates.length g r _ _ terms publicHash alpha hr hp
      (affine_columns_have_degree_one wireEndpoints) (affine_columns_have_degree_one constantEndpoints)
  · intro x
    constructor
    · exact all_validated_contributions_exact c i gates.length g r _ _ terms publicHash alpha x hr
        (by simpa only [affine_columns_preserve_length] using hw) hp
    · exact GatesComplete.valid_configuration_always_evaluates c gates _ _ publicHash alpha.toVerifier hv
        (by simpa only [column_values_preserve_length,affine_columns_preserve_length] using hw)
        (by simpa only [column_values_preserve_length,affine_columns_preserve_length] using hc)

theorem affine_weighted_contribution_degree (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (r : Gates.Requirements) (wires constants terms : List P) (publicHash : Nat → Verifier.Base)
    (alpha left right : Element) (hv : Gates.validateGate c row total g = some r)
    (hp : unfilteredPolys g wires constants publicHash c.numSelectors = some terms)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    (affine left right * contributionPoly c g terms constants alpha).natDegree ≤ c.quotientDegree+2 := by
  have hd := all_validated_contribution_degree c row total g r wires constants terms publicHash alpha hv hp hw hc
  exact (mul_degree_bound _ _ 1 (c.quotientDegree+1) (affine_degree left right) hd).trans (by omega)

end Audit.Wire3.GateAllPolynomial
