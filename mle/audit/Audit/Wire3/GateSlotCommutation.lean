import Audit.Wire3.GateSlotAlgebra

/-!
Rust mle/src/gate_ext3.rs:543-608 (`evaluate_gate_constraints_ext3_validated`
543-597 with its filter/slot loop at 591-593, and
`aggregate_gate_constraints_ext3` 599-608), using the SAME existing concrete
unfiltered gate dispatch and filter as GatesComplete. Each gate is evaluated
even when its filter is zero; its literal output count is checked, and each
emitted slot is added to the same fixed-width buffer. The source's forward
alpha-power loop then reduces that entire buffer. No per-gate
equality/degree callback appears.

`slotRows` fails when a gate's term list is longer than the slot buffer, the
situation in which the source's `accumulated[slot]` write (593) panics; the
executed model is therefore not more total than the source at that write.
`slotRowsChecked` uses the per-write partial loop instead and is proved equal.

Theorems derive output counts and capacity from full configuration validation.
This is a concrete algorithm/order commutation proof, not Rust/Yul compiler
refinement. The specialized Solidity Poseidon/MDS reduced emitters, ABI/usize
arithmetic and canonical raw-input/public-hash preflight remain separate.
Configuration validation is a prepared-context theorem premise, not an added
check inside the source's prevalidated evaluator.
-/
namespace Audit.Wire3.GateSlotCommutation
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateAggregatePolynomial
open Audit.Wire3.GateSlotAlgebra

/-- The source filter (gate_ext3.rs:590-591): the selector is
`constants[selector_index]` and the filter is `compute_filter`. Both
`Gates.readValue` (zero-defaulting `getD`) and `Gates.computeFilter` are the
existing totalized model functions. Their totality is NOT relied on: the
`locationValid` clause of `validateGate` (`selectorIndex < numSelectors`),
the envelope clause `numSelectors ≤ numConstants`, and the
`constants.length = numConstants` width check of `evalPreparedSlots` together
put the selector read in range; `abiWidths` bounds the metadata the filter's
selector factors are built from. `compute_filter`'s own `ensure!`
(gate_ext3.rs:633-636, `start < end` and row in range) and its `k_usize`
conversion (640) are likewise closed by `locationValid` and `abiWidths`
(`groupEnd < 256`). The Goldilocks-order ensure (550-553) is not modelled:
the Lean field is fixed to Goldilocks. -/
def rowFilter (c : Gates.Config) (g : Gates.GateInfo) (constants : List Verifier.Ext3) : Element :=
  ⟨Gates.computeFilter g (Gates.readValue constants g.selectorIndex) (decide (1<c.numSelectors))⟩

/-- The gate loop of gate_ext3.rs:572-595 over a slot buffer. The source's
`unfiltered.len() == num_constraints` ensure (582-588) is the first `none`;
the second `none` is the write-bound failure of the slot loop (592-594),
where the source panics on `accumulated[slot]`. -/
def slotRows (c : Gates.Config) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) : List Gates.GateInfo → List Element → Option (List Element)
  | [],buffer => some buffer
  | g::rest,buffer => do
      let terms ← GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors
      if terms.length ≠ g.numConstraints then none else
      if buffer.length < (wrap terms).length then none else
        slotRows c wires constants publicHash rest
          (addIndexed (rowFilter c g constants) 0 (wrap terms) buffer)

/-- The same gate loop with the per-write partial slot loop: `none` on the
first individual out-of-range write, exactly where the source panics. -/
def slotRowsChecked (c : Gates.Config) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) : List Gates.GateInfo → List Element → Option (List Element)
  | [],buffer => some buffer
  | g::rest,buffer => do
      let terms ← GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors
      if terms.length ≠ g.numConstraints then none else do
        let next ← addIndexedChecked (rowFilter c g constants) 0 (wrap terms) buffer
        slotRowsChecked c wires constants publicHash rest next

/-- The executed loop's whole-list write guard is exactly the per-write bound:
`slotRows` succeeds iff every individual `accumulated[slot]` write of every
gate is in range, and then both compute the same buffer. No configuration
hypothesis is needed; this is a statement about the executed loop itself. -/
theorem slotRows_all_writes_in_bounds (c : Gates.Config) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (gates : List Gates.GateInfo) (buffer : List Element) :
    slotRowsChecked c wires constants publicHash gates buffer =
      slotRows c wires constants publicHash gates buffer := by
  induction gates generalizing buffer with
  | nil => rfl
  | cons g rest ih =>
      simp only [slotRowsChecked,slotRows]
      cases GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors with
      | none => rfl
      | some terms =>
          simp only [bind,Option.bind]
          by_cases hl : terms.length = g.numConstraints
          · by_cases hle : (wrap terms).length ≤ buffer.length
            · simp only [hl,ne_eq,not_true_eq_false,↓reduceIte,indexed_checked_exact,hle,
                Nat.not_lt.mpr hle,ih]
            · simp only [hl,ne_eq,not_true_eq_false,↓reduceIte,indexed_checked_exact,hle,
                Nat.lt_of_not_le hle]
          · simp only [hl,ne_eq,not_false_eq_true,↓reduceIte]

/-- The entire real row list executes: equal scalar reduction is a conclusion,
not a premise. The starting slot buffer need not be zero.

There is deliberately NO `constants.length = c.numConstants` hypothesis here:
the source's constant-width ensure (gate_ext3.rs:560-565) precedes the gate
loop and is performed by `evalPreparedSlots`, not inside the loop. The gate
dispatch and the filter read are total model functions, so the loop's
execution result is well-defined for any `constants`; the width check is
closed at `evalPreparedSlots`/`configured_slots_equal_complete`. -/
theorem validated_rows_commute (c : Gates.Config) (total row maximum : Nat)
    (gates : List Gates.GateInfo) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (buffer : List Element)
    (hv : Gates.validateRows c total row gates=some maximum) (hw : wires.length=c.numWires)
    (hcap : maximum ≤ buffer.length) :
    ∃ result, slotRows c wires constants publicHash gates buffer=some result ∧
      result.length=buffer.length ∧
      GatesComplete.combineRows c wires constants publicHash alpha.toVerifier gates
        (reduce alpha buffer).toVerifier=some (reduce alpha result).toVerifier := by
  induction gates generalizing row maximum buffer with
  | nil => exact ⟨buffer,rfl,rfl,rfl⟩
  | cons g rest ih =>
      cases hg : Gates.validateGate c row total g with
      | none => simp [Gates.validateRows,hg] at hv
      | some req =>
          cases hr : Gates.validateRows c total (row+1) rest with
          | none => simp [Gates.validateRows,hg,hr] at hv
          | some restMax =>
              have hm : max req.constraints restMax=maximum := by simpa [Gates.validateRows,hg,hr] using hv
              obtain ⟨terms,he,hl⟩ := GatesComplete.every_validated_family_evaluates
                c row total g req wires constants publicHash hg hw
              have hn := (Gates.validate_gate_success c row total g req hg).2.2.2.2.1
              have hterms : (wrap terms).length ≤ buffer.length := by
                simp only [wrap,List.length_map]
                have := Nat.le_max_left req.constraints restMax
                omega
              let next := addIndexed (rowFilter c g constants) 0 (wrap terms) buffer
              have hlen : next.length=buffer.length := indexed_length _ _ _ _
              have hrest : restMax ≤ next.length := by
                have := Nat.le_max_right req.constraints restMax
                omega
              obtain ⟨result,hs,hsize,hactual⟩ := ih (row+1) restMax next hr hrest
              have hc := actual_contribution_branch_erased c g wires constants publicHash alpha.toVerifier terms he hl
              have hstep : Verifier.add (reduce alpha buffer).toVerifier
                  (Verifier.mul (rowFilter c g constants).toVerifier (Gates.horner terms alpha.toVerifier)) =
                  (reduce alpha next).toVerifier := by
                rw [← reduce_actual_horner alpha terms]
                change (reduce alpha buffer+rowFilter c g constants*reduce alpha (wrap terms)).toVerifier =
                  (reduce alpha next).toVerifier
                rw [show next=addIndexed (rowFilter c g constants) 0 (wrap terms) buffer from rfl,
                  reduce_indexed alpha _ buffer _ hterms]
              refine ⟨result,?_,hsize.trans hlen,?_⟩
              · simpa only [slotRows,he,bind,Option.bind,hl,ne_eq,not_true_eq_false,↓reduceIte,
                  Nat.not_lt.mpr hterms] using hs
              · simp only [rowFilter] at hstep
                simpa only [GatesComplete.combineRows,hc,bind,Option.bind,hstep] using hactual

/-- The source's prepared context supplies metadata validity. This function
performs the source's two exact input-width checks (gate_ext3.rs:554-565),
but no new metadata guard. The buffer is `vec![ZERO; num_gate_constraints]`
(570) and the result is the forward power reduction (600-608). -/
def evalPreparedSlots (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (alpha : Element) :
    Option Verifier.Ext3 := do
  if wires.length ≠ c.numWires ∨ constants.length ≠ c.numConstants then none else do
    let result ← slotRows c wires constants publicHash gates (List.replicate c.numGateConstraints 0)
    pure (reduce alpha result).toVerifier

theorem configured_slots_equal_complete (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateConfiguration c gates=some ()) :
    evalPreparedSlots c gates wires constants publicHash alpha =
      GatesComplete.evalCombined c gates wires constants publicHash alpha.toVerifier := by
  by_cases hw : wires.length=c.numWires
  · by_cases hc : constants.length=c.numConstants
    · have hr := (Gates.validate_configuration_success c gates hv).2
      obtain ⟨result,hs,_,he⟩ := validated_rows_commute c gates.length 0 c.numGateConstraints gates
        wires constants publicHash alpha (List.replicate c.numGateConstraints 0) hr hw (by simp)
      simp only [reduce_zero_padding,zero_exact] at he
      simp only [evalPreparedSlots,GatesComplete.evalCombined,hw,hc,ne_eq,not_true_eq_false,or_self,
        ↓reduceIte,hv,bind,Option.bind,hs,he,pure,Option.pure_def]
    · simp [evalPreparedSlots,GatesComplete.evalCombined,hc]
  · simp [evalPreparedSlots,GatesComplete.evalCombined,hw]

/-- Under full configuration validation and the wire width check, the per-write
partial loop also executes on the zero buffer: no `accumulated[slot]` write of
the prepared evaluator is out of range. -/
theorem configured_slots_checked_execute (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (hv : Gates.validateConfiguration c gates=some ()) (hw : wires.length=c.numWires) :
    ∃ result, slotRowsChecked c wires constants publicHash gates (List.replicate c.numGateConstraints 0)
      =some result ∧ result.length=c.numGateConstraints := by
  have hr := (Gates.validate_configuration_success c gates hv).2
  obtain ⟨result,hs,hlen,_⟩ := validated_rows_commute c gates.length 0 c.numGateConstraints gates
    wires constants publicHash 0 (List.replicate c.numGateConstraints 0) hr hw (by simp)
  refine ⟨result,?_,by simpa using hlen⟩
  rw [slotRows_all_writes_in_bounds]
  exact hs

/-- One fixed polynomial for ALL slot-first gate rows, sharing both affine
column lists, the same fixed metadata/public hash/alpha and every point x. -/
theorem configured_slot_polynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element×Element))
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (hv : Gates.validateConfiguration c gates=some ())
    (hw : wireEndpoints.length=c.numWires) (hc : constantEndpoints.length=c.numConstants) :
    ∃ polynomial : P,
      evaluatePolynomial c gates (affineColumns wireEndpoints) (affineColumns constantEndpoints)
        publicHash alpha=some polynomial ∧ polynomial.natDegree ≤ c.quotientDegree+1 ∧
      ∀ x, evalPreparedSlots c gates (affineValues wireEndpoints x) (affineValues constantEndpoints x)
        publicHash alpha=some (value polynomial x) := by
  obtain ⟨polynomial,hp,hd,he⟩ := configured_affine_aggregate c gates wireEndpoints constantEndpoints publicHash alpha hv hw hc
  simp only [affine_columns_actual_values] at he
  exact ⟨polynomial,hp,hd,fun x => (configured_slots_equal_complete c gates _ _ publicHash alpha hv).trans (he x)⟩

def weightedSlots (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element×Element)) (publicHash : Nat → Verifier.Base)
    (alpha left right x : Element) : Option Verifier.Ext3 := do
  let gate ← evalPreparedSlots c gates (affineValues wireEndpoints x) (affineValues constantEndpoints x) publicHash alpha
  pure (Verifier.mul (affineWeight left right x) gate)

theorem weighted_slots_equal_rows (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element×Element)) (publicHash : Nat → Verifier.Base)
    (alpha left right x : Element) (hv : Gates.validateConfiguration c gates=some ()) :
    weightedSlots c gates wireEndpoints constantEndpoints publicHash alpha left right x =
      evaluateWeighted c gates wireEndpoints constantEndpoints publicHash alpha left right x := by
  simp only [weightedSlots,evaluateWeighted,configured_slots_equal_complete c gates _ _ publicHash alpha hv]

theorem configured_weighted_slot_polynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (wireEndpoints constantEndpoints : List (Element×Element)) (publicHash : Nat → Verifier.Base)
    (alpha left right : Element) (hv : Gates.validateConfiguration c gates=some ())
    (hw : wireEndpoints.length=c.numWires) (hc : constantEndpoints.length=c.numConstants) :
    ∃ polynomial : P, polynomial.natDegree ≤ c.quotientDegree+2 ∧
      ∀ x, weightedSlots c gates wireEndpoints constantEndpoints publicHash alpha left right x =
        some (value polynomial x) := by
  obtain ⟨p,hd,he⟩ := configured_weighted_aggregate c gates wireEndpoints constantEndpoints publicHash alpha left right hv hw hc
  exact ⟨p,hd,fun x => (weighted_slots_equal_rows c gates wireEndpoints constantEndpoints publicHash alpha left right x hv).trans (he x)⟩

end Audit.Wire3.GateSlotCommutation
