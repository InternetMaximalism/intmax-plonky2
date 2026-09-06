import Audit.Wire3.GatesAdditionalCoset

/-!
Additional concrete gate evaluations, runtime snapshot 69516414.
Source: Plonky2GateEvaluatorExt3._evalExponentiation/_evalBaseSum/_evalReducing/
_evalRandomAccess, plus GatesAdditionalCoset for id 13. All arithmetic retains
the full canonical Ext3 subtype and the inner Ext2 nonresidue is 7.
These functions have no evaluator observations. Their raw totalized List reads
must only be used after Gates.validateConfiguration and the wire-length checks.
The parent dispatcher owns those checks. This is not a new standalone safe API.

Theorems establish the actual recurrence, output order/length, indexed layout
bounds, and concrete normal examples. They do not establish polynomial degree,
boolean/range root exclusion, completeness of the Plonky2 circuit, or compiler/
Yul memory refinement. In particular, zero product does not imply one factor is
zero without additional field algebra. Random-access folding is an executable
copy of the adjacent difference butterfly, not an assumed selection oracle.
-/
namespace Audit.Wire3.GatesAdditional
open Verifier
open Gates (GateInfo readValue readExt2 embed Ext2)
open GatesAdditionalCoset (pairAdd pairSub pairValues)

def exponentiationPrevious (wires : List Ext3) (bits i : Nat) : Ext3 :=
  if i = 0 then Gates.one else Norm.square (readValue wires (2 + bits + i - 1))

def exponentiationExpected (wires : List Ext3) (bits i : Nat) : Ext3 :=
  let bit := readValue wires (bits - i)
  mul (exponentiationPrevious wires bits i)
    (add (mul bit (readValue wires 0)) (sub Gates.one bit))

def evalExponentiation (wires : List Ext3) (bits : Nat) : List Ext3 :=
  (List.range bits).map (fun i =>
    sub (exponentiationExpected wires bits i) (readValue wires (2 + bits + i))) ++
  [sub (readValue wires (1 + bits)) (readValue wires (2 + bits + bits - 1))]

theorem exponentiation_output_length (wires : List Ext3) (bits : Nat) :
    (evalExponentiation wires bits).length = bits + 1 := by
  simp [evalExponentiation, Gates.range_length]

theorem exponentiation_uses_high_bit_first (wires : List Ext3) (bits : Nat) :
    exponentiationExpected wires bits 0 =
      mul Gates.one (add (mul (readValue wires bits) (readValue wires 0))
        (sub Gates.one (readValue wires bits))) := by
  simp [exponentiationExpected, exponentiationPrevious]

theorem exponentiation_constraint_exact (wires : List Ext3) (bits i : Nat) :
    sub (exponentiationExpected wires bits i) (readValue wires (2 + bits + i)) = zero ↔
      exponentiationExpected wires bits i = readValue wires (2 + bits + i) := Algebra.vsub_eq_zero_iff _ _

def baseSumValue (wires : List Ext3) (limbs baseValue : Nat) : Ext3 :=
  Gates.horner ((List.range limbs).map fun i => readValue wires (i + 1)) (embed baseValue)

def baseSumRangeProduct (value : Ext3) (baseValue : Nat) : Ext3 :=
  Gates.productFactors ((List.range baseValue).map fun v => sub value (embed v)) Gates.one

def evalBaseSum (wires : List Ext3) (limbs baseValue : Nat) : List Ext3 :=
  sub (baseSumValue wires limbs baseValue) (readValue wires 0) ::
    (List.range limbs).map (fun i => baseSumRangeProduct (readValue wires (i + 1)) baseValue)

theorem base_sum_output_length (wires : List Ext3) (limbs baseValue : Nat) :
    (evalBaseSum wires limbs baseValue).length = limbs + 1 := by
  simp [evalBaseSum, Gates.range_length]

theorem base_sum_range_member_satisfies_product (value baseValue : Nat) (h : value < baseValue) :
    baseSumRangeProduct (embed value) baseValue = zero := by
  apply Gates.product_with_zero_factor
  apply List.mem_map.mpr
  exact ⟨value, (Gates.range_membership _ _).mpr h, Algebra.vsub_self _⟩

theorem base_sum_value_constraint_exact (wires : List Ext3) (limbs baseValue : Nat) :
    sub (baseSumValue wires limbs baseValue) (readValue wires 0) = zero ↔
      baseSumValue wires limbs baseValue = readValue wires 0 := Algebra.vsub_eq_zero_iff _ _

def coefficientWidth (extension : Bool) : Nat := if extension then 2 else 1
def accumulatorStart (count : Nat) (extension : Bool) : Nat := 6 + coefficientWidth extension * count

def reducingCoefficient (wires : List Ext3) (extension : Bool) (i : Nat) : Ext2 :=
  if extension then readExt2 wires (6 + 2 * i) else ⟨readValue wires (6 + i), zero⟩

def reducingNext (wires : List Ext3) (count : Nat) (extension : Bool) (i : Nat) : Ext2 :=
  if i + 1 = count then readExt2 wires 0 else readExt2 wires (accumulatorStart count extension + 2 * i)

def reducingExpected (wires : List Ext3) (extension : Bool) (i : Nat) (previous : Ext2) : Ext2 :=
  pairAdd (Gates.ext2Mul previous (readExt2 wires 2)) (reducingCoefficient wires extension i)

structure ReducingState where
  accumulator : Ext2
  output : List Ext3

def reducingStep (wires : List Ext3) (count : Nat) (extension : Bool) (i : Nat)
    (s : ReducingState) : ReducingState :=
  let next := reducingNext wires count extension i
  ⟨next, s.output ++ pairValues (pairSub (reducingExpected wires extension i s.accumulator) next)⟩

def runReducing (wires : List Ext3) (count : Nat) (extension : Bool) :
    Nat → Nat → ReducingState → ReducingState
  | _, 0, s => s
  | i, remaining + 1, s => runReducing wires count extension (i + 1) remaining
      (reducingStep wires count extension i s)

def evalReducing (wires : List Ext3) (count : Nat) (extension : Bool) : List Ext3 :=
  (runReducing wires count extension 0 count ⟨readExt2 wires 4, []⟩).output

theorem reducing_step_installs_claimed_next (wires : List Ext3) (count : Nat) (extension : Bool)
    (i : Nat) (s : ReducingState) :
    (reducingStep wires count extension i s).accumulator = reducingNext wires count extension i := rfl

theorem reducing_step_constraints_exact (wires : List Ext3) (count : Nat) (extension : Bool)
    (i : Nat) (s : ReducingState) :
    (∀ value ∈ pairValues (pairSub (reducingExpected wires extension i s.accumulator)
      (reducingNext wires count extension i)), value = zero) ↔
      reducingExpected wires extension i s.accumulator = reducingNext wires count extension i :=
  GatesAdditionalCoset.pair_difference_exact _ _

theorem reducing_step_adds_two (wires : List Ext3) (count : Nat) (extension : Bool)
    (i : Nat) (s : ReducingState) :
    (reducingStep wires count extension i s).output.length = s.output.length + 2 := by
  simp [reducingStep, pairValues]

theorem reducing_run_length (wires : List Ext3) (count : Nat) (extension : Bool)
    (i remaining : Nat) (s : ReducingState) :
    (runReducing wires count extension i remaining s).output.length = s.output.length + 2 * remaining := by
  induction remaining generalizing i s with
  | zero => simp [runReducing]
  | succ remaining ih =>
      rw [runReducing, ih, reducing_step_adds_two]
      omega

theorem reducing_output_length (wires : List Ext3) (count : Nat) (extension : Bool) :
    (evalReducing wires count extension).length = 2 * count := by
  simp [evalReducing, reducing_run_length]

theorem reducing_last_output_is_gate_output (wires : List Ext3) (count : Nat) (extension : Bool)
    (h : 0 < count) : reducingNext wires count extension (count - 1) = readExt2 wires 0 := by
  simp [reducingNext, show count - 1 + 1 = count by omega]

def randomVectorSize (bits : Nat) : Nat := 2 ^ bits
def randomCopyWidth (bits : Nat) : Nat := 2 + randomVectorSize bits
def randomRouted (bits copies extra : Nat) : Nat := randomCopyWidth bits * copies + extra
def randomWireCount (bits copies extra : Nat) : Nat := randomRouted bits copies extra + copies * bits

def randomBits (wires : List Ext3) (bits copies extra copy : Nat) : List Ext3 :=
  (List.range bits).map fun b => readValue wires (randomRouted bits copies extra + copy * bits + b)

def randomValues (wires : List Ext3) (bits copy : Nat) : List Ext3 :=
  (List.range (randomVectorSize bits)).map fun i => readValue wires (randomCopyWidth bits * copy + 2 + i)

def selectionLayer (bit : Ext3) : List Ext3 → List Ext3
  | even :: odd :: rest => add even (mul bit (sub odd even)) :: selectionLayer bit rest
  | _ => []

def selectionLayers : List Ext3 → List Ext3 → List Ext3
  | [], values => values
  | bit :: rest, values => selectionLayers rest (selectionLayer bit values)

def selection (values bits : List Ext3) : Ext3 := (selectionLayers bits values).getD 0 zero

def randomReconstructedIndex (bits : List Ext3) : Ext3 :=
  bits.reverse.foldl (fun acc bit => add (add acc acc) bit) zero

def randomCopyConstraints (wires : List Ext3) (bits copies extra copy : Nat) : List Ext3 :=
  let bs := randomBits wires bits copies extra copy
  bs.map (fun bit => mul bit (sub bit Gates.one)) ++
    [sub (randomReconstructedIndex bs) (readValue wires (randomCopyWidth bits * copy)),
     sub (selection (randomValues wires bits copy) bs) (readValue wires (randomCopyWidth bits * copy + 1))]

def evalRandomAccess (wires constants : List Ext3) (constantOffset bits copies extra : Nat) : List Ext3 :=
  (List.range copies).bind (fun copy => randomCopyConstraints wires bits copies extra copy) ++
    (List.range extra).map (fun i =>
      sub (readValue constants (constantOffset + i)) (readValue wires (randomCopyWidth bits * copies + i)))

theorem fixed_bind_length (indices : List Nat) (f : Nat → List Ext3) (width : Nat)
    (h : ∀ i, (f i).length = width) : (indices.bind f).length = indices.length * width := by
  induction indices with
  | nil => simp
  | cons i is ih => simp [List.bind_cons, h, ih, Nat.add_mul, Nat.add_comm]

theorem random_copy_constraint_length (wires : List Ext3) (bits copies extra copy : Nat) :
    (randomCopyConstraints wires bits copies extra copy).length = bits + 2 := by
  simp [randomCopyConstraints, randomBits, Gates.range_length, Nat.add_assoc]

theorem random_access_output_length (wires constants : List Ext3) (offset bits copies extra : Nat) :
    (evalRandomAccess wires constants offset bits copies extra).length = copies * (bits + 2) + extra := by
  unfold evalRandomAccess
  rw [List.length_append, fixed_bind_length _ _ _ (random_copy_constraint_length wires bits copies extra)]
  simp [Gates.range_length]

theorem selection_layer_length (bit : Ext3) : ∀ values : List Ext3,
    (selectionLayer bit values).length = values.length / 2
  | [] => rfl
  | [_] => by simp [selectionLayer]
  | even :: odd :: rest => by
      simp only [selectionLayer, List.length_cons, selection_layer_length bit rest]
      omega

theorem complete_selection_has_one_value (bits values : List Ext3)
    (h : values.length = 2 ^ bits.length) : (selectionLayers bits values).length = 1 := by
  induction bits generalizing values with
  | nil => simpa [selectionLayers] using h
  | cons b bs ih =>
      apply ih
      rw [selection_layer_length, h]
      simp [List.length_cons, Nat.pow_succ, Nat.mul_comm]

theorem random_selection_uses_exact_dimensions (wires : List Ext3) (bits copies extra copy : Nat) :
    (selectionLayers (randomBits wires bits copies extra copy) (randomValues wires bits copy)).length = 1 := by
  apply complete_selection_has_one_value
  simp [randomBits, randomValues, Gates.range_length, randomVectorSize]

theorem selection_zero_bit (even odd : Ext3) : selection [even, odd] [zero] = even := by
  simp [selection, selectionLayers, selectionLayer, Algebra.vzero_mul, Algebra.vadd_zero]

theorem selection_one_bit (even odd : Ext3) : selection [even, odd] [Gates.one] = odd := by
  change add even (mul Norm.one (sub odd even)) = odd
  rw [Algebra.vone_mul, Algebra.vadd_comm, Algebra.vsub_add_cancel]

theorem reconstructed_index_two_bits (low high : Ext3) :
    randomReconstructedIndex [low, high] = add (add high high) low := by
  simp [randomReconstructedIndex, Algebra.vadd_zero, Algebra.vzero_add]

theorem block_index_bounded (blocks width block offset : Nat)
    (hb : block < blocks) (ho : offset < width) : block * width + offset < blocks * width := by
  have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hb)
  simp only [Nat.succ_mul] at hm
  omega

theorem random_bit_access_bounds (bits copies extra copy b : Nat)
    (hc : copy < copies) (hb : b < bits) :
    randomRouted bits copies extra + copy * bits + b < randomWireCount bits copies extra := by
  have := block_index_bounded copies bits copy b hc hb
  unfold randomWireCount
  omega

theorem random_value_access_bounds (bits copies extra copy index : Nat)
    (hc : copy < copies) (hi : index < randomVectorSize bits) :
    randomCopyWidth bits * copy + 2 + index < randomWireCount bits copies extra := by
  have hi' : 2 + index < randomCopyWidth bits := by unfold randomCopyWidth; omega
  have h := block_index_bounded copies (randomCopyWidth bits) copy (2 + index) hc hi'
  have hh : randomCopyWidth bits * copy + 2 + index < randomCopyWidth bits * copies := by
    simpa [Nat.mul_comm, Nat.add_assoc] using h
  apply Nat.lt_of_lt_of_le hh
  unfold randomWireCount randomRouted
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem random_header_access_bounds (bits copies extra copy : Nat) (hc : copy < copies) :
    randomCopyWidth bits * copy < randomWireCount bits copies extra ∧
    randomCopyWidth bits * copy + 1 < randomWireCount bits copies extra := by
  have hi : 1 < randomCopyWidth bits := by unfold randomCopyWidth; omega
  have h := block_index_bounded copies (randomCopyWidth bits) copy 1 hc hi
  have hh : randomCopyWidth bits * copy + 1 < randomCopyWidth bits * copies := by
    simpa [Nat.mul_comm] using h
  have ht : randomCopyWidth bits * copies ≤ randomWireCount bits copies extra := by
    unfold randomWireCount randomRouted
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  constructor
  · exact Nat.lt_of_lt_of_le (by omega) ht
  · exact Nat.lt_of_lt_of_le hh ht

theorem random_extra_access_bounds (bits copies extra i : Nat) (hi : i < extra) :
    randomCopyWidth bits * copies + i < randomWireCount bits copies extra := by
  have h : randomCopyWidth bits * copies + i < randomCopyWidth bits * copies + extra := by omega
  unfold randomWireCount randomRouted
  exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)

theorem exponentiation_access_bounds (bits i : Nat) (hb : 0 < bits) (hi : i < bits) :
    bits - i < 2 * bits + 2 ∧ 2 + bits + i < 2 * bits + 2 ∧
    (i ≠ 0 → 2 + bits + i - 1 < 2 * bits + 2) ∧
    1 + bits < 2 * bits + 2 ∧ 2 + bits + bits - 1 < 2 * bits + 2 := by omega

theorem base_sum_access_bounds (limbs i : Nat) (hi : i < limbs) : i + 1 < limbs + 1 := by omega

theorem reducing_coefficient_access_bounds (count i : Nat) (extension : Bool)
    (hi : i < count) :
    (if extension then 6 + 2 * i + 1 else 6 + i) <
      accumulatorStart count extension + 2 * (count - 1) := by
  cases extension <;> simp [accumulatorStart, coefficientWidth] <;> omega

theorem reducing_wire_count_matches_metadata (count : Nat) (extension : Bool) (h : 0 < count) :
    accumulatorStart count extension + 2 * (count - 1) =
      if extension then 4 + 4 * count else 4 + 3 * count := by
  cases extension <;> simp [accumulatorStart, coefficientWidth] <;> omega

theorem reducing_fixed_prefix_access_bounds (count : Nat) (extension : Bool) :
    5 < accumulatorStart count extension + 2 * (count - 1) := by
  cases extension <;> simp [accumulatorStart, coefficientWidth] <;> omega

theorem reducing_accumulator_access_bounds (count i : Nat) (extension : Bool)
    (hc : 0 < count) (hi : i + 1 < count) :
    accumulatorStart count extension + 2 * i + 1 <
      accumulatorStart count extension + 2 * (count - 1) := by omega

/-- Concrete dispatch only; the all-gate parent first validates metadata and
    circuit-wide lengths. Coset's external-library boundary gets its exact prefix. -/
def dispatchUnchecked (g : GateInfo) (wires constants : List Ext3) (numSelectors : Nat) :
    Option (List Ext3) :=
  match g.gateId with
  | 8 => some (evalExponentiation wires g.numOrConsts)
  | 9 => some (evalBaseSum wires g.numOrConsts g.param2)
  | 10 => some (evalReducing wires g.numOrConsts false)
  | 11 => some (evalReducing wires g.numOrConsts true)
  | 12 => some (evalRandomAccess wires constants numSelectors g.numOrConsts g.param2 g.param3)
  | 13 => GatesAdditionalCoset.evaluate
      (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2)) g.numOrConsts g.param2
  | _ => none

theorem validated_coset_dispatch (c : Gates.Config) (row total : Nat) (g : GateInfo)
    (r : Gates.Requirements) (wires constants : List Ext3)
    (hv : Gates.validateGate c row total g = some r) (hg : g.gateId = 13)
    (hw : wires.length = c.numWires) :
    ∃ output, dispatchUnchecked g wires constants c.numSelectors = some output ∧
      output.length = g.numConstraints := by
  have h := Gates.validate_gate_success c row total g r hv
  have hr := h.2.2.2.1
  simp only [Gates.requirements, hg] at hr
  split at hr
  · rename_i hp
    simp only [Option.some.injEq] at hr
    subst r
    have hreq := h.2.2.2.2.2.1
    have hnum := h.2.2.2.2.1
    simp only at hreq hnum
    have hbits : 1 ≤ g.numOrConsts ∧ g.numOrConsts ≤ 5 := by omega
    have hwidth : GatesAdditionalCoset.wireCount g.numOrConsts g.param2 ≤ wires.length := by
      unfold GatesAdditionalCoset.wireCount GatesAdditionalCoset.shiftedPointIndex
        GatesAdditionalCoset.intermediateStart GatesAdditionalCoset.intermediates GatesAdditionalCoset.points
      omega
    have hl : GatesAdditionalCoset.layoutValid
        (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2)) g.numOrConsts g.param2 := by
      exact ⟨hbits.1, hbits.2, hp.2.2.2.1, hp.2.2.2.2,
        List.length_take_of_le hwidth, GatesAdditionalCoset.weight_zero_canonical _ hbits⟩
    refine ⟨GatesAdditionalCoset.evaluateUnchecked
      (wires.take (GatesAdditionalCoset.wireCount g.numOrConsts g.param2)) g.numOrConsts g.param2, ?_, ?_⟩
    · simp [dispatchUnchecked, hg, GatesAdditionalCoset.evaluate, hl]
    · rw [GatesAdditionalCoset.output_length]
      exact hnum.symm
  · simp at hr

theorem validated_simple_dispatch (c : Gates.Config) (row total : Nat) (g : GateInfo)
    (r : Gates.Requirements) (wires constants : List Ext3)
    (hv : Gates.validateGate c row total g = some r) (hg : 8 ≤ g.gateId ∧ g.gateId ≤ 12) :
    ∃ output, dispatchUnchecked g wires constants c.numSelectors = some output ∧
      output.length = g.numConstraints := by
  have hids : g.gateId = 8 ∨ g.gateId = 9 ∨ g.gateId = 10 ∨ g.gateId = 11 ∨ g.gateId = 12 := by omega
  rcases hids with hid | hid | hid | hid | hid
  all_goals
    have h := Gates.validate_gate_success c row total g r hv
    have hr := h.2.2.2.1
    simp only [Gates.requirements, hid] at hr
    split at hr
    · simp only [Option.some.injEq] at hr
      subst r
      have hn := h.2.2.2.2.1
      simp only at hn
      simp [dispatchUnchecked, hid, exponentiation_output_length, base_sum_output_length,
        reducing_output_length, random_access_output_length, hn]
    · simp at hr

theorem validated_additional_dispatch (c : Gates.Config) (row total : Nat) (g : GateInfo)
    (r : Gates.Requirements) (wires constants : List Ext3)
    (hv : Gates.validateGate c row total g = some r) (hg : 8 ≤ g.gateId ∧ g.gateId ≤ 13)
    (hw : wires.length = c.numWires) :
    ∃ output, dispatchUnchecked g wires constants c.numSelectors = some output ∧
      output.length = g.numConstraints := by
  by_cases hid : g.gateId = 13
  · exact validated_coset_dispatch c row total g r wires constants hv hid hw
  · exact validated_simple_dispatch c row total g r wires constants hv (by omega)

theorem exponentiation_nonbase_positive :
    evalExponentiation [Gates.extensionGenerator, Gates.one,
      Gates.extensionGenerator, Gates.extensionGenerator] 1 = [zero, zero] := by decide

theorem base_sum_binary_positive :
    evalBaseSum [embed 3, Gates.one, Gates.one] 2 2 = [zero, zero, zero] := by decide

theorem base_sum_keeps_nonbase_limb :
    baseSumValue [zero, Gates.extensionGenerator, Gates.one] 2 2 =
      add (embed 2) Gates.extensionGenerator := by decide

theorem reducing_nonbase_positive :
    evalReducing [add Gates.extensionGenerator Gates.extensionGenerator, zero,
      Gates.extensionGenerator, zero, Gates.one, zero, Gates.extensionGenerator]
      1 false = [zero, zero] := by decide

theorem reducing_extension_nonbase_positive :
    evalReducing [add Gates.extensionGenerator Gates.extensionGenerator, Gates.one,
      Gates.extensionGenerator, zero, Gates.one, zero, Gates.extensionGenerator, Gates.one]
      1 true = [zero, zero] := by decide

theorem random_access_nonbase_positive :
    evalRandomAccess [Gates.one, Gates.extensionGenerator, zero, Gates.extensionGenerator, Gates.one]
      [] 0 1 1 0 = [zero, zero, zero] := by decide

end Audit.Wire3.GatesAdditional
