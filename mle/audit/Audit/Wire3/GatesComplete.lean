import Audit.Wire3.GatesAdditional
import Audit.Wire3.Poseidon

/-!
Concrete dispatcher for all fourteen gate families at runtime becfe98e.
This completes the *evaluation algorithm* missing from Gates.evaluateUnfiltered.
All configured rows are validated before zero-filter skipping; valid metadata
and input lengths imply an actual result for every gate, including active ones.
No evaluator oracle is used. Completeness here is dispatch coverage, NOT circuit
soundness, degree bounds, aggregation soundness, or Rust/Solidity refinement.
The totalized low-level List reads inherit the metadata/length preconditions.
-/
namespace Audit.Wire3.GatesComplete
open Verifier (Ext3 Base zero add mul)
open Gates (GateInfo Config Requirements computeFilter readValue horner validateConfiguration)

def evaluateUnfiltered (g : GateInfo) (wires constants : List Ext3) (publicHash : Nat → Base)
    (numSelectors : Nat) : Option (List Ext3) :=
  if g.gateId = 4 then some (Poseidon.evalPoseidon wires)
  else if g.gateId = 5 then some (Poseidon.evalPoseidonMds wires)
  else if 8 ≤ g.gateId then GatesAdditional.dispatchUnchecked g wires constants numSelectors
  else Gates.evaluateUnfiltered g wires constants publicHash numSelectors

theorem validated_small_dispatch (c : Config) (row total : Nat) (g : GateInfo)
    (r : Requirements) (wires constants : List Ext3) (publicHash : Nat → Base)
    (hv : Gates.validateGate c row total g = some r) (hi : g.gateId < 8) :
    ∃ output, evaluateUnfiltered g wires constants publicHash c.numSelectors = some output ∧
      output.length = g.numConstraints := by
  have ids : g.gateId = 0 ∨ g.gateId = 1 ∨ g.gateId = 2 ∨ g.gateId = 3 ∨
      g.gateId = 4 ∨ g.gateId = 5 ∨ g.gateId = 6 ∨ g.gateId = 7 := by omega
  rcases ids with hid | hid | hid | hid | hid | hid | hid | hid
  all_goals
    have h := Gates.validate_gate_success c row total g r hv
    have hr := h.2.2.2.1
    simp only [Gates.requirements, hid] at hr
    split at hr
    · simp only [Option.some.injEq] at hr
      subst r
      have hn := h.2.2.2.2.1
      simp only at hn
      simp [evaluateUnfiltered, Gates.evaluateUnfiltered, hid,
        (Gates.concrete_constraint_lengths wires constants publicHash c.numSelectors g.numOrConsts).1,
        (Gates.concrete_constraint_lengths wires constants publicHash c.numSelectors g.numOrConsts).2.1,
        (Gates.concrete_constraint_lengths wires constants publicHash c.numSelectors g.numOrConsts).2.2,
        (Gates.extension_constraint_lengths wires constants c.numSelectors g.numOrConsts).1,
        (Gates.extension_constraint_lengths wires constants c.numSelectors g.numOrConsts).2,
        Poseidon.poseidon_constraint_count, Poseidon.mds_constraint_count, hn]
    · simp at hr

theorem every_validated_family_evaluates (c : Config) (row total : Nat) (g : GateInfo)
    (r : Requirements) (wires constants : List Ext3) (publicHash : Nat → Base)
    (hv : Gates.validateGate c row total g = some r) (hw : wires.length = c.numWires) :
    ∃ output, evaluateUnfiltered g wires constants publicHash c.numSelectors = some output ∧
      output.length = g.numConstraints := by
  by_cases hi : g.gateId < 8
  · exact validated_small_dispatch c row total g r wires constants publicHash hv hi
  · have hk := (Gates.validate_gate_success c row total g r hv).2.2.1
    obtain ⟨terms, he, hl⟩ := GatesAdditional.validated_additional_dispatch c row total g r wires constants
      hv (by omega) hw
    exact ⟨terms, by simpa [evaluateUnfiltered, show g.gateId ≠ 4 by omega,
      show g.gateId ≠ 5 by omega, show 8 ≤ g.gateId by omega] using he, hl⟩

def contribution (c : Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3) : Option Ext3 :=
  let filter := computeFilter g (readValue constants g.selectorIndex) (decide (1 < c.numSelectors))
  if filter = zero then some zero else do
    let terms ← evaluateUnfiltered g wires constants publicHash c.numSelectors
    if terms.length = g.numConstraints then some (mul filter (horner terms alpha)) else none

def combineRows (c : Config) (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3) :
    List GateInfo → Ext3 → Option Ext3
  | [], accumulated => some accumulated
  | g :: gs, accumulated => do
    let term ← contribution c g wires constants publicHash alpha
    combineRows c wires constants publicHash alpha gs (add accumulated term)

def evalCombined (c : Config) (gates : List GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3) : Option Ext3 := do
  if wires.length ≠ c.numWires ∨ constants.length ≠ c.numConstants then none else do
    let _ ← validateConfiguration c gates
    combineRows c wires constants publicHash alpha gates zero

theorem validated_contribution_exists (c : Config) (row total : Nat) (g : GateInfo)
    (r : Requirements) (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3)
    (hv : Gates.validateGate c row total g = some r) (hw : wires.length = c.numWires) :
    ∃ result, contribution c g wires constants publicHash alpha = some result := by
  obtain ⟨terms, he, hl⟩ := every_validated_family_evaluates c row total g r wires constants publicHash hv hw
  unfold contribution
  dsimp only
  split
  · exact ⟨zero, rfl⟩
  · simp [he, hl]

theorem validated_rows_evaluate (c : Config) (total row maximum : Nat) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha acc : Ext3)
    (hv : Gates.validateRows c total row gates = some maximum) (hw : wires.length = c.numWires) :
    ∃ result, combineRows c wires constants publicHash alpha gates acc = some result := by
  induction gates generalizing row maximum acc with
  | nil => exact ⟨acc, rfl⟩
  | cons g gs ih =>
    cases hr : Gates.validateGate c row total g with
    | none => simp [Gates.validateRows, hr] at hv
    | some req =>
      cases hs : Gates.validateRows c total (row + 1) gs with
      | none => simp [Gates.validateRows, hr, hs] at hv
      | some rest =>
        obtain ⟨term, ht⟩ := validated_contribution_exists c row total g req wires constants publicHash alpha hr hw
        obtain ⟨result, he⟩ := ih (row + 1) rest (add acc term) hs
        exact ⟨result, by simpa [combineRows, ht] using he⟩

theorem valid_configuration_always_evaluates (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3)
    (hv : validateConfiguration c gates = some ())
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants) :
    ∃ result, evalCombined c gates wires constants publicHash alpha = some result := by
  have hr := (Gates.validate_configuration_success c gates hv).2
  obtain ⟨result, he⟩ := validated_rows_evaluate c gates.length 0 c.numGateConstraints gates
    wires constants publicHash alpha zero hr hw
  exact ⟨result, by simpa [evalCombined, hw, hc, hv] using he⟩

theorem combined_success_requires_all_configuration (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha result : Ext3)
    (h : evalCombined c gates wires constants publicHash alpha = some result) :
    wires.length = c.numWires ∧ constants.length = c.numConstants ∧ validateConfiguration c gates = some () := by
  unfold evalCombined at h
  split at h
  · simp at h
  · rename_i hs
    cases hv : validateConfiguration c gates with
    | none => simp [hv] at h
    | some resultUnit => cases resultUnit; exact ⟨by omega, by omega, rfl⟩

theorem combined_has_output_iff_valid (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3) :
    (∃ result, evalCombined c gates wires constants publicHash alpha = some result) ↔
      wires.length = c.numWires ∧ constants.length = c.numConstants ∧ validateConfiguration c gates = some () := by
  constructor
  · rintro ⟨result, h⟩
    exact combined_success_requires_all_configuration c gates wires constants publicHash alpha result h
  · rintro ⟨hw, hc, hv⟩
    exact valid_configuration_always_evaluates c gates wires constants publicHash alpha hv hw hc

theorem unknown_gate_rejected_even_when_inactive (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3)
    (i : Nat) (g : GateInfo) (hg : gates.get? i = some g) (hu : 14 ≤ g.gateId) :
    evalCombined c gates wires constants publicHash alpha = none := by
  cases hr : evalCombined c gates wires constants publicHash alpha with
  | none => rfl
  | some result =>
    have hc := (combined_success_requires_all_configuration c gates wires constants publicHash alpha result hr).2.2
    rcases Gates.every_configured_gate_checked c gates hc i g hg with ⟨req, hv, _⟩
    have hknown := (Gates.validate_gate_success c i gates.length g req hv).2.2.1
    omega

theorem inactive_contribution_zero (c : Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3)
    (h : computeFilter g (readValue constants g.selectorIndex) (decide (1 < c.numSelectors)) = zero) :
    contribution c g wires constants publicHash alpha = some zero := by simp [contribution, h]

theorem satisfied_contribution_zero (c : Config) (g : GateInfo) (wires constants : List Ext3)
    (publicHash : Nat → Base) (alpha : Ext3) (terms : List Ext3)
    (he : evaluateUnfiltered g wires constants publicHash c.numSelectors = some terms)
    (hl : terms.length = g.numConstraints) (hz : ∀ x ∈ terms, x = zero) :
    contribution c g wires constants publicHash alpha = some zero := by
  unfold contribution
  dsimp only
  split
  · rfl
  · simp [he, hl, Gates.horner_all_zero terms alpha hz, Gates.mul_zero]

theorem all_satisfied_combination_zero (c : Config) (gates : List GateInfo)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3)
    (h : ∀ g ∈ gates, contribution c g wires constants publicHash alpha = some zero) :
    combineRows c wires constants publicHash alpha gates zero = some zero := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [combineRows, h g (by simp)]
    simpa [Gates.add_zero] using ih (by intro x hx; exact h x (by simp [hx]))

theorem fourteen_family_dispatch_coverage (g : GateInfo) (hg : g ∈ Gates.representativeGates)
    (wires constants : List Ext3) (publicHash : Nat → Base) (alpha : Ext3)
    (hw : wires.length = 160) (hc : constants.length = 3) :
    ∃ result, evalCombined ⟨1, 3, g.numConstraints, 160, 8⟩ [g] wires constants publicHash alpha = some result := by
  apply valid_configuration_always_evaluates ⟨1, 3, g.numConstraints, 160, 8⟩ [g]
    wires constants publicHash alpha ?_ hw hc
  have ha := Gates.all_fourteen_families_have_valid_configuration_examples.2
  have hv := List.all_eq_true.mp ha g hg
  exact of_decide_eq_true hv

end Audit.Wire3.GatesComplete
