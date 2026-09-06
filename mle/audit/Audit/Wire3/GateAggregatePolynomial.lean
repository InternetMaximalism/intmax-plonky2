import Audit.Wire3.GateAllPolynomial

/-!
All configured gate rows, in actual GatesComplete.combineRows order, share
the SAME wires/constants/public hash/fixed alpha and contribute to one fixed
polynomial. Validation produces each literal family polynomial; no evaluator,
per-row correctness or degree callback is assumed. The exact zero-filter/
Horner boundary is inherited from the frozen all-fourteen bridge.

The final theorem covers actual GatesComplete.evalCombined, not merely one
selected row. Both wire and constant columns are captured affine endpoints.
Source: Plonky2GateEvaluatorExt3.sol:115-149,164-190; the exact executable Lean
boundary is GatesComplete.lean:63-82. Rust's slot-first accumulation and forward
power order is a separate source-refinement/algebraic commutation boundary;
no source/Yul/compiler equivalence, MLE/PCS endpoint provenance or gate truth
is implied. This is the OUTER gate polynomial, not inner WHIR quadratic/FS.
For the Solidity prevalidated entry, full configuration validation is a prior
deployment/context condition, not a new check inside that entry. The source's
special Poseidon/MDS reduced emitters are also not newly refined by this file.
Canonical raw-input/public-hash preflight is a separate source boundary:
this file evaluates field-canonical wire/constant endpoints and alpha, while
its fixed publicHash function retains the existing totalized model type.
-/
namespace Audit.Wire3.GateAggregatePolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Polynomial

noncomputable def combinePoly (c : Gates.Config) (wires constants : List P)
    (publicHash : Nat → Verifier.Base) (alpha : Element) : List Gates.GateInfo → P → Option P
  | [],accumulated => some accumulated
  | g::rest,accumulated => do
      let terms ← Audit.Wire3.GateAllPolynomial.unfilteredPolys g wires constants publicHash c.numSelectors
      combinePoly c wires constants publicHash alpha rest
        (accumulated+Audit.Wire3.GateAllPolynomial.contributionPoly c g terms constants alpha)

/-- Complete execution/degree invariant through the real ordered row list.
All per-gate validation facts are extracted from validateRows itself. -/
theorem validated_rows_polynomial (c : Gates.Config) (total row maximum : Nat)
    (gates : List Gates.GateInfo) (wires constants : List P) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (accumulated : P)
    (hv : Gates.validateRows c total row gates = some maximum)
    (hl : wires.length=c.numWires)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1)
    (ha : accumulated.natDegree ≤ c.quotientDegree+1) :
    ∃ polynomial : P,
      combinePoly c wires constants publicHash alpha gates accumulated = some polynomial ∧
      polynomial.natDegree ≤ c.quotientDegree+1 ∧
      ∀ x, GatesComplete.combineRows c (columnValues wires x) (columnValues constants x)
        publicHash alpha.toVerifier gates (value accumulated x) = some (value polynomial x) := by
  induction gates generalizing row maximum accumulated with
  | nil => exact ⟨accumulated,rfl,ha,fun _ => rfl⟩
  | cons g rest ih =>
      cases hr : Gates.validateGate c row total g with
      | none => simp [Gates.validateRows,hr] at hv
      | some req =>
          cases hs : Gates.validateRows c total (row+1) rest with
          | none => simp [Gates.validateRows,hr,hs] at hv
          | some restMaximum =>
              obtain ⟨terms,hp⟩ := Audit.Wire3.GateAllPolynomial.all_validated_families_have_polynomials
                c row total g req wires constants publicHash hr
              have hd := Audit.Wire3.GateAllPolynomial.all_validated_contribution_degree c row total g req
                wires constants terms publicHash alpha hr hp hw hc
              have hnext := add_degree_bound accumulated
                (Audit.Wire3.GateAllPolynomial.contributionPoly c g terms constants alpha)
                (c.quotientDegree+1) (c.quotientDegree+1) ha hd
              obtain ⟨polynomial,hpoly,hdegree,hactual⟩ := ih (row+1) restMaximum
                (accumulated+Audit.Wire3.GateAllPolynomial.contributionPoly c g terms constants alpha) hs
                (by simpa only [max_self] using hnext)
              refine ⟨polynomial,?_,hdegree,?_⟩
              · simpa only [combinePoly,hp,bind,Option.bind] using hpoly
              · intro x
                have hterm := Audit.Wire3.GateAllPolynomial.all_validated_contributions_exact c row total g req
                  wires constants terms publicHash alpha x hr hl hp
                simpa only [GatesComplete.combineRows,hterm,bind,Option.bind,value_add] using hactual x

noncomputable def evaluatePolynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List P) (publicHash : Nat → Verifier.Base) (alpha : Element) : Option P := do
  if wires.length ≠ c.numWires ∨ constants.length ≠ c.numConstants then none else do
    let _ ← Gates.validateConfiguration c gates
    combinePoly c wires constants publicHash alpha gates 0

theorem configured_polynomial_complete (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List P) (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateConfiguration c gates = some ())
    (hlw : wires.length=c.numWires) (hlc : constants.length=c.numConstants)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hc : ∀ p ∈ constants, p.natDegree ≤ 1) :
    ∃ polynomial : P,
      evaluatePolynomial c gates wires constants publicHash alpha = some polynomial ∧
      polynomial.natDegree ≤ c.quotientDegree+1 ∧
      ∀ x, GatesComplete.evalCombined c gates (columnValues wires x) (columnValues constants x)
        publicHash alpha.toVerifier = some (value polynomial x) := by
  have hr := (Gates.validate_configuration_success c gates hv).2
  obtain ⟨polynomial,hp,hd,he⟩ := validated_rows_polynomial c gates.length 0 c.numGateConstraints
    gates wires constants publicHash alpha 0 hr hlw hw hc (by simp)
  refine ⟨polynomial,?_,hd,?_⟩
  · simp only [evaluatePolynomial,hlw,hlc,ne_eq,not_true_eq_false,or_self,↓reduceIte,hv,bind,Option.bind,hp]
  · intro x
    simpa only [GatesComplete.evalCombined,column_values_preserve_length,hlw,hlc,ne_eq,
      not_true_eq_false,or_self,↓reduceIte,hv,bind,Option.bind,value_zero] using he x

/-- Successful symbolic evaluation cannot omit the length/configuration
guards represented by GatesComplete. Raw canonical preflight is separate. -/
theorem polynomial_success_retains_configuration (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List P) (publicHash : Nat → Verifier.Base) (alpha : Element) (p : P)
    (h : evaluatePolynomial c gates wires constants publicHash alpha = some p) :
    wires.length=c.numWires ∧ constants.length=c.numConstants ∧ Gates.validateConfiguration c gates=some () := by
  unfold evaluatePolynomial at h
  split at h
  · simp at h
  · rename_i hl
    cases hv : Gates.validateConfiguration c gates with
    | none => simp [hv] at h
    | some u => cases u; exact ⟨by omega,by omega,rfl⟩

theorem configured_affine_aggregate (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element × Element))
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateConfiguration c gates=some ())
    (hw : wireEndpoints.length=c.numWires) (hc : constantEndpoints.length=c.numConstants) :
    ∃ polynomial : P,
      evaluatePolynomial c gates (affineColumns wireEndpoints) (affineColumns constantEndpoints)
        publicHash alpha = some polynomial ∧
      polynomial.natDegree ≤ c.quotientDegree+1 ∧
      ∀ x, GatesComplete.evalCombined c gates (columnValues (affineColumns wireEndpoints) x)
        (columnValues (affineColumns constantEndpoints) x) publicHash alpha.toVerifier = some (value polynomial x) :=
  configured_polynomial_complete c gates _ _ publicHash alpha hv
    (by simpa only [affine_columns_preserve_length] using hw)
    (by simpa only [affine_columns_preserve_length] using hc)
    (affine_columns_have_degree_one wireEndpoints) (affine_columns_have_degree_one constantEndpoints)

/-- The real Ext3 arithmetic of the affine equality-weight evaluation.
The endpoint values are supplied, not asserted to be authenticated eq data. -/
def affineWeight (left right x : Element) : Verifier.Ext3 :=
  Verifier.add (Verifier.mul (Verifier.sub Norm.one x.toVerifier) left.toVerifier)
    (Verifier.mul x.toVerifier right.toVerifier)

/-- Executable endpoint arithmetic, with no symbolic polynomial evaluation. -/
def affineValues (endpoints : List (Element × Element)) (x : Element) : List Verifier.Ext3 :=
  endpoints.map (fun pair => affineWeight pair.1 pair.2 x)

theorem affine_columns_actual_values (endpoints : List (Element × Element)) (x : Element) :
    columnValues (affineColumns endpoints) x = affineValues endpoints x := by
  simp only [columnValues,affineColumns,affineValues,List.map_map,Function.comp_def,
    affine_actual_arithmetic,affineWeight]

def evaluateWeighted (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element × Element)) (publicHash : Nat → Verifier.Base)
    (alpha left right x : Element) : Option Verifier.Ext3 := do
  let gate ← GatesComplete.evalCombined c gates (affineValues wireEndpoints x)
    (affineValues constantEndpoints x) publicHash alpha.toVerifier
  pure (Verifier.mul (affineWeight left right x) gate)

theorem configured_weighted_aggregate (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element × Element)) (publicHash : Nat → Verifier.Base)
    (alpha left right : Element) (hv : Gates.validateConfiguration c gates=some ())
    (hw : wireEndpoints.length=c.numWires) (hc : constantEndpoints.length=c.numConstants) :
    ∃ polynomial : P, polynomial.natDegree ≤ c.quotientDegree+2 ∧
      ∀ x, evaluateWeighted c gates wireEndpoints constantEndpoints publicHash alpha left right x =
        some (value polynomial x) := by
  obtain ⟨gate,_,hd,he⟩ := configured_affine_aggregate c gates wireEndpoints constantEndpoints publicHash alpha hv hw hc
  simp only [affine_columns_actual_values] at he
  refine ⟨affine left right*gate,?_,?_⟩
  · exact (mul_degree_bound _ _ 1 (c.quotientDegree+1) (affine_degree left right) hd).trans (by omega)
  · intro x
    simp only [evaluateWeighted,he,bind,Option.bind,value_mul,affine_actual_arithmetic,affineWeight,pure,Option.pure_def]

theorem configured_weighted_degree_at_most_ten (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element × Element)) (publicHash : Nat → Verifier.Base)
    (alpha left right : Element) (hv : Gates.validateConfiguration c gates=some ())
    (hw : wireEndpoints.length=c.numWires) (hc : constantEndpoints.length=c.numConstants) :
    ∃ polynomial : P, polynomial.natDegree ≤ 10 ∧
      ∀ x, evaluateWeighted c gates wireEndpoints constantEndpoints publicHash alpha left right x =
        some (value polynomial x) := by
  obtain ⟨p,hd,he⟩ := configured_weighted_aggregate c gates wireEndpoints constantEndpoints publicHash alpha left right hv hw hc
  have henv := (Gates.validate_configuration_success c gates hv).1
  simp only [Gates.envelope] at henv
  exact ⟨p,hd.trans (by omega),he⟩

end Audit.Wire3.GateAggregatePolynomial
