import Audit.Wire3.Gates
import Audit.Wire3.Algebra
import Audit.Wire3.PoseidonConstants

/-!
# Concrete Poseidon gate evaluators (ids 4 and 5)

Source: PoseidonGateExt3.sol, all of evalPoseidonReduced/evalPoseidonMdsReduced
and their private helpers, with the literal PoseidonConstants.sol tables. The
Rust counterparts are gate_ext3.rs::eval_poseidon and eval_poseidon_mds.

The complete 12-coordinate calculation, full/partial rounds, witness wire
substitutions, swap/delta equations, constraint order, and reverse Horner
reduction are executable. No permutation/hash/evaluator observation is used.
State arrays are materialized and have width 12 by construction. The caller
supplies canonical Ext3 limbs, matching Plonky2GateEvaluatorExt3's canonical
scan. Raw list wire reads are totalized outside their index range; checked
entry points enforce the source's minimum 135/48 wire lengths. Metadata and
selector filtering belong to Gates/the complete dispatcher, not this library.

This is a concrete mathematical model, not a Rust/Yul memory or bytecode
refinement proof, Poseidon collision-resistance proof, or PCS soundness proof.
Vanishing alpha-reduction alone is NOT equated with all constraints vanishing.
The formal bounds and lengths below are unconditional deterministic facts;
source-to-model correspondence still requires source/refinement review.
-/
namespace Audit.Wire3.Poseidon
open Verifier
open PoseidonConstants

abbrev Ext2 := Gates.Ext2

def coordinates : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def tailCoordinates : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem coordinates_length : coordinates.length = 12 := rfl
theorem coordinate_membership (i : Fin 12) : i ∈ coordinates := by
  have h : ∀ i : Fin 12, i ∈ coordinates := by decide
  exact h i
theorem coordinates_order : coordinates.map Fin.val = List.range 12 := by decide
theorem tail_coordinates_order : tailCoordinates.map Fin.val = List.range 11 := by decide

structure State where
  data : Array Ext3
  width : data.size = 12

/-- Explicit fixed array also permits kernel evaluation of closed examples. -/
def makeState (f : Fin 12 → Ext3) : State :=
  ⟨#[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11], rfl⟩
def stateAt (s : State) (i : Fin 12) : Ext3 := s.data[i.val]'(by rw [s.width]; exact i.isLt)
def stateList (s : State) : List Ext3 := coordinates.map (stateAt s)
def zeroState : State := makeState (fun _ => zero)

@[simp] theorem at_makeState (f : Fin 12 → Ext3) (i : Fin 12) : stateAt (makeState f) i = f i := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 := by omega
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi
  · have h : i = (0 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (1 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (2 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (3 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (4 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (5 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (6 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (7 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (8 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (9 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (10 : Fin 12) := Fin.ext hi
    subst i
    rfl
  · have h : i = (11 : Fin 12) := Fin.ext hi
    subst i
    rfl

theorem state_list_length (s : State) : (stateList s).length = 12 := by
  simp [stateList, coordinates_length]

def wire (wires : List Ext3) (i : Nat) : Ext3 := Gates.readValue wires i
def wireState (wires : List Ext3) (offset : Nat) : State := makeState (fun i => wire wires (offset + i.val))

/-- Source constant layers update only c0; c1 and c2 are already canonical. -/
def addBase (x : Ext3) (n : Nat) : Ext3 :=
  ⟨⟨Arithmetic.add x.val.c0 n, x.val.c1, x.val.c2⟩,
    Arithmetic.add_canonical _ _, x.property.2.1, x.property.2.2⟩

theorem add_base_is_field_add (x : Ext3) (n : Nat) : addBase x n = add x (Norm.embed n) := by
  apply Subtype.eq
  simp [addBase, add, Norm.embed, Arithmetic.eadd, Arithmetic.fromBase,
    Arithmetic.add, Arithmetic.reduce, Nat.mod_eq_of_lt x.property.2.1,
    Nat.mod_eq_of_lt x.property.2.2]

theorem add_base_zero (x : Ext3) : addBase x 0 = x := by
  rw [add_base_is_field_add]
  exact Algebra.vadd_zero x

def sbox (x : Ext3) : Ext3 :=
  let square := Norm.square x
  let fourth := Norm.square square
  mul (mul x square) fourth

theorem sbox_exact_seventh_power (x : Ext3) :
    sbox x = mul (mul x (mul x x)) (mul (mul x x) (mul x x)) := by
  simp only [sbox, Algebra.norm_square_is_multiplication]

def sboxLayer (state : State) : State := makeState (fun i => sbox (stateAt state i))
def addConstantLayer (state : State) (round : Nat) : State :=
  makeState (fun i => addBase (stateAt state i) (allRoundConstants.getD (round * 12 + i.val) 0))
def partialFirstConstantLayer (state : State) : State :=
  makeState (fun i => addBase (stateAt state i) (partialFirstConstants.getD i.val 0))

def rotated (row i : Fin 12) : Fin 12 := ⟨(i.val + row.val) % 12, Nat.mod_lt _ (by decide)⟩
def tailIndex (i : Fin 11) : Fin 12 := ⟨i.val + 1, by omega⟩

def mdsCirculantRow (state : State) (row : Fin 12) : Ext3 :=
  coordinates.foldl (fun acc i => add acc (scalar (stateAt state (rotated row i)) (mdsCirc.getD i.val 0))) zero

/-- The main gate's sparse diagonal implementation only updates row zero. -/
def mdsRow (state : State) (row : Fin 12) : Ext3 :=
  let acc := mdsCirculantRow state row
  if row.val = 0 then add acc (scalar (stateAt state 0) (mdsDiag.getD 0 0)) else acc

def mdsLayer (state : State) : State := makeState (mdsRow state)

/-- The standalone MDS gate reads every diagonal entry. -/
def mdsGeneralRow (state : State) (row : Fin 12) : Ext3 :=
  add (mdsCirculantRow state row) (scalar (stateAt state row) (mdsDiag.getD row.val 0))

/-- Matrix orientation is source[row-1] * matrix[row-1][column-1]. -/
def mdsPartialInit (state : State) : State := makeState fun column =>
  if column.val = 0 then stateAt state 0 else
    tailCoordinates.foldl (fun acc row => add acc
      (scalar (stateAt state (tailIndex row))
        (partialInitialMatrix.getD (row.val * 11 + (column.val - 1)) 0))) zero

def partialM00 : Nat := Arithmetic.add (mdsCirc.getD 0 0) (mdsDiag.getD 0 0)
theorem partial_m00_exact : partialM00 = 25 := by decide

def mdsPartialFast (state : State) (round : Nat) : State := makeState fun i =>
  if i.val = 0 then
    tailCoordinates.foldl (fun acc j => add acc
      (scalar (stateAt state (tailIndex j)) (partialWHats.getD (round * 11 + j.val) 0)))
      (scalar (stateAt state 0) partialM00)
  else add (scalar (stateAt state 0) (partialVs.getD (round * 11 + (i.val - 1)) 0)) (stateAt state i)

def swapConstraints (wires : List Ext3) : List Ext3 :=
  let swap := wire wires 24
  mul swap (sub swap Norm.one) :: (List.range 4).map fun i =>
    sub (mul swap (sub (wire wires (i + 4)) (wire wires i))) (wire wires (25 + i))

def swapState (wires : List Ext3) : State := makeState fun i =>
  if i.val < 4 then add (wire wires i.val) (wire wires (25 + i.val))
  else if i.val < 8 then sub (wire wires i.val) (wire wires (25 + (i.val - 4)))
  else wire wires i.val

def fullConstraints (wires : List Ext3) (expected : State) (offset : Nat) : List Ext3 :=
  coordinates.map fun i => sub (stateAt expected i) (wire wires (offset + i.val))

structure Trace where
  state : State
  constraints : List Ext3

def fullStep (wires : List Ext3) (constantRound wireStart : Nat) (trace : Trace) : Trace :=
  let expected := addConstantLayer trace.state constantRound
  ⟨mdsLayer (sboxLayer (wireState wires wireStart)),
   trace.constraints ++ fullConstraints wires expected wireStart⟩

def run (step : Nat → Trace → Trace) : Nat → Nat → Trace → Trace
  | _, 0, trace => trace
  | round, count + 1, trace => run step (round + 1) count (step round trace)

/-- Round zero does not consume witness S-box-input wires. Rounds 1,2,3 do. -/
def firstFullRounds (wires : List Ext3) (state : State) : Trace :=
  run (fun round => fullStep wires round (29 + 12 * (round - 1))) 1 3
    ⟨mdsLayer (sboxLayer (addConstantLayer state 0)), []⟩

def partialSboxValue (source : Ext3) (round : Nat) : Ext3 :=
  if round + 1 = 22 then sbox source
  else addBase (sbox source) (partialRoundConstants.getD round 0)

def partialStep (wires : List Ext3) (round : Nat) (trace : Trace) : Trace :=
  let source := wire wires (65 + round)
  let state := makeState (fun i => if i.val = 0 then partialSboxValue source round else stateAt trace.state i)
  ⟨mdsPartialFast state round, trace.constraints ++ [sub (stateAt trace.state 0) source]⟩

def partialRounds (wires : List Ext3) (state : State) : Trace :=
  run (partialStep wires) 0 22 ⟨state, []⟩

def secondFullRounds (wires : List Ext3) (state : State) : Trace :=
  run (fun round => fullStep wires (26 + round) (87 + 12 * round)) 0 4 ⟨state, []⟩

structure Stages where
  first : Trace
  middle : Trace
  second : Trace

def stages (wires : List Ext3) : Stages :=
  let first := firstFullRounds wires (swapState wires)
  let middle := partialRounds wires (mdsPartialInit (partialFirstConstantLayer first.state))
  let second := secondFullRounds wires middle.state
  ⟨first, middle, second⟩

def outputConstraints (wires : List Ext3) (state : State) : List Ext3 := fullConstraints wires state 12

/-- Constraint blocks have lengths 5,36,22,48,12, in this exact order. -/
def evalPoseidon (wires : List Ext3) : List Ext3 :=
  let s := stages wires
  swapConstraints wires ++ s.first.constraints ++ s.middle.constraints ++ s.second.constraints ++
    outputConstraints wires s.second.state

def mdsGateInput (wires : List Ext3) (lane : Fin 2) : State :=
  makeState (fun i => wire wires (2 * i.val + lane.val))

def mdsGateExpected (wires : List Ext3) (row : Fin 12) : Ext2 :=
  ⟨mdsGeneralRow (mdsGateInput wires 0) row, mdsGeneralRow (mdsGateInput wires 1) row⟩

/-- Row-major Ext2 component order. Unlike the Poseidon gate, sign is output-minus-computed. -/
def evalPoseidonMds (wires : List Ext3) : List Ext3 :=
  coordinates.bind fun row =>
    let computed := mdsGateExpected wires row
    [sub (wire wires (2 * (12 + row.val))) computed.c0,
     sub (wire wires (2 * (12 + row.val) + 1)) computed.c1]

def evalPoseidonReduced (wires : List Ext3) (alpha : Ext3) : Option Ext3 :=
  if wires.length < 135 then none else some (Gates.horner (evalPoseidon wires) alpha)

def evalPoseidonMdsReduced (wires : List Ext3) (alpha : Ext3) : Option Ext3 :=
  if wires.length < 48 then none else some (Gates.horner (evalPoseidonMds wires) alpha)

theorem swap_constraints_length (wires : List Ext3) : (swapConstraints wires).length = 5 := by
  simp [swapConstraints, Gates.range_length]

theorem full_constraints_length (wires : List Ext3) (state : State) (offset : Nat) :
    (fullConstraints wires state offset).length = 12 := by
  simp [fullConstraints, coordinates_length]

theorem full_step_length (wires : List Ext3) (constantRound wireStart : Nat) (trace : Trace) :
    (fullStep wires constantRound wireStart trace).constraints.length = trace.constraints.length + 12 := by
  simp [fullStep, full_constraints_length]

theorem partial_step_length (wires : List Ext3) (round : Nat) (trace : Trace) :
    (partialStep wires round trace).constraints.length = trace.constraints.length + 1 := by
  simp [partialStep]

theorem run_constraint_count (step : Nat → Trace → Trace) (increment : Nat)
    (h : ∀ round trace, (step round trace).constraints.length = trace.constraints.length + increment)
    (count round : Nat) (trace : Trace) :
    (run step round count trace).constraints.length = trace.constraints.length + count * increment := by
  induction count generalizing round trace with
  | zero => simp [run]
  | succ count ih =>
    rw [run, ih, h]
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem first_full_constraint_count (wires : List Ext3) (state : State) :
    (firstFullRounds wires state).constraints.length = 36 := by
  unfold firstFullRounds
  rw [run_constraint_count _ 12 (fun _ _ => full_step_length _ _ _ _)]
  rfl

theorem partial_constraint_count (wires : List Ext3) (state : State) :
    (partialRounds wires state).constraints.length = 22 := by
  unfold partialRounds
  rw [run_constraint_count _ 1 (fun _ _ => partial_step_length _ _ _)]
  rfl

theorem second_full_constraint_count (wires : List Ext3) (state : State) :
    (secondFullRounds wires state).constraints.length = 48 := by
  unfold secondFullRounds
  rw [run_constraint_count _ 12 (fun _ _ => full_step_length _ _ _ _)]
  rfl

theorem stages_constraint_counts (wires : List Ext3) :
    (stages wires).first.constraints.length = 36 ∧
    (stages wires).middle.constraints.length = 22 ∧
    (stages wires).second.constraints.length = 48 := by
  exact ⟨first_full_constraint_count _ _, partial_constraint_count _ _, second_full_constraint_count _ _⟩

theorem poseidon_constraint_count (wires : List Ext3) : (evalPoseidon wires).length = 123 := by
  simp only [evalPoseidon, List.length_append, swap_constraints_length, outputConstraints,
    full_constraints_length, (stages_constraint_counts wires).1,
    (stages_constraint_counts wires).2.1, (stages_constraint_counts wires).2.2]

theorem mds_constraint_count (wires : List Ext3) : (evalPoseidonMds wires).length = 24 := by
  simp [evalPoseidonMds, coordinates, List.bind]

theorem poseidon_short_input_rejected (wires : List Ext3) (alpha : Ext3) (h : wires.length < 135) :
    evalPoseidonReduced wires alpha = none := by simp [evalPoseidonReduced, h]

theorem mds_short_input_rejected (wires : List Ext3) (alpha : Ext3) (h : wires.length < 48) :
    evalPoseidonMdsReduced wires alpha = none := by simp [evalPoseidonMdsReduced, h]

theorem poseidon_success_exact (wires : List Ext3) (alpha result : Ext3)
    (h : evalPoseidonReduced wires alpha = some result) :
    135 ≤ wires.length ∧ result = Gates.horner (evalPoseidon wires) alpha := by
  unfold evalPoseidonReduced at h
  split at h
  · contradiction
  · exact ⟨by omega, (Option.some.inj h).symm⟩

theorem mds_success_exact (wires : List Ext3) (alpha result : Ext3)
    (h : evalPoseidonMdsReduced wires alpha = some result) :
    48 ≤ wires.length ∧ result = Gates.horner (evalPoseidonMds wires) alpha := by
  unfold evalPoseidonMdsReduced at h
  split at h
  · contradiction
  · exact ⟨by omega, (Option.some.inj h).symm⟩

def allZero (values : List Ext3) : Bool := values.all (fun x => decide (x = zero))

theorem all_zero_iff (values : List Ext3) :
    allZero values = true ↔ ∀ x ∈ values, x = zero := by simp [allZero, List.all_eq_true]

theorem all_zero_append (a b : List Ext3) :
    allZero (a ++ b) = true ↔ allZero a = true ∧ allZero b = true := by
  simp only [all_zero_iff, List.mem_append, or_imp, forall_and]

theorem full_constraints_zero_iff (wires : List Ext3) (expected : State) (offset : Nat) :
    allZero (fullConstraints wires expected offset) = true ↔
      ∀ i : Fin 12, stateAt expected i = wire wires (offset + i.val) := by
  rw [all_zero_iff]
  constructor
  · intro h i
    apply (Algebra.vsub_eq_zero_iff _ _).mp
    exact h _ (List.mem_map.mpr ⟨i, coordinate_membership i, rfl⟩)
  · intro h value hv
    rcases List.mem_map.mp hv with ⟨i, _, rfl⟩
    exact (Algebra.vsub_eq_zero_iff _ _).mpr (h i)

theorem output_constraints_zero_iff (wires : List Ext3) (state : State) :
    allZero (outputConstraints wires state) = true ↔
      ∀ i : Fin 12, stateAt state i = wire wires (12 + i.val) := full_constraints_zero_iff _ _ _

theorem swap_constraints_zero_iff (wires : List Ext3) :
    allZero (swapConstraints wires) = true ↔
      mul (wire wires 24) (sub (wire wires 24) Norm.one) = zero ∧
      ∀ i, i < 4 → mul (wire wires 24) (sub (wire wires (i + 4)) (wire wires i)) = wire wires (25 + i) := by
  simp only [all_zero_iff, swapConstraints, List.mem_cons, List.mem_map]
  constructor
  · intro h
    refine ⟨h _ (Or.inl rfl), ?_⟩
    intro i hi
    apply (Algebra.vsub_eq_zero_iff _ _).mp
    exact h _ (Or.inr ⟨i, (Gates.range_membership _ _).mpr hi, rfl⟩)
  · rintro ⟨hs, hd⟩ value (hv | ⟨i, hi, hv⟩)
    · simpa only [hv] using hs
    · subst value
      exact (Algebra.vsub_eq_zero_iff _ _).mpr (hd i ((Gates.range_membership _ _).mp hi))

theorem mds_constraints_zero_iff (wires : List Ext3) :
    allZero (evalPoseidonMds wires) = true ↔
      ∀ row : Fin 12,
        wire wires (2 * (12 + row.val)) = (mdsGateExpected wires row).c0 ∧
        wire wires (2 * (12 + row.val) + 1) = (mdsGateExpected wires row).c1 := by
  rw [all_zero_iff]
  constructor
  · intro h row
    constructor
    · apply (Algebra.vsub_eq_zero_iff _ _).mp
      exact h _ (List.mem_bind.mpr ⟨row, coordinate_membership row, by simp⟩)
    · apply (Algebra.vsub_eq_zero_iff _ _).mp
      exact h _ (List.mem_bind.mpr ⟨row, coordinate_membership row, by simp⟩)
  · intro h value hv
    rcases List.mem_bind.mp hv with ⟨row, _, hv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv
    · subst value
      exact (Algebra.vsub_eq_zero_iff _ _).mpr (h row).1
    · subst value
      exact (Algebra.vsub_eq_zero_iff _ _).mpr (h row).2

theorem poseidon_all_blocks_zero_iff (wires : List Ext3) :
    allZero (evalPoseidon wires) = true ↔
      allZero (swapConstraints wires) = true ∧
      allZero (stages wires).first.constraints = true ∧
      allZero (stages wires).middle.constraints = true ∧
      allZero (stages wires).second.constraints = true ∧
      allZero (outputConstraints wires (stages wires).second.state) = true := by
  simp only [evalPoseidon, all_zero_append, and_assoc]

theorem run_preserves_constraint_prefix (step : Nat → Trace → Trace)
    (terms : Nat → Trace → List Ext3)
    (happend : ∀ round trace, (step round trace).constraints = trace.constraints ++ terms round trace)
    (count round : Nat) (trace : Trace) :
    ∃ suffix, (run step round count trace).constraints = trace.constraints ++ suffix := by
  induction count generalizing round trace with
  | zero => exact ⟨[], by simp [run]⟩
  | succ count ih =>
    rcases ih (round + 1) (step round trace) with ⟨suffix, hs⟩
    refine ⟨terms round trace ++ suffix, ?_⟩
    rw [run, hs, happend, List.append_assoc]

/-- Each local equation is checked on the state actually computed by the
    preceding transition. This is an inductive execution relation, not a record
    assuming the desired acceptance conclusions. -/
inductive CheckedRun (step : Nat → Trace → Trace) (terms : Nat → Trace → List Ext3) :
    Nat → Nat → Trace → Trace → Prop where
  | done (round trace) : CheckedRun step terms round 0 trace trace
  | next {round count trace final}
      (localZero : allZero (terms round trace) = true)
      (tail : CheckedRun step terms (round + 1) count (step round trace) final) :
      CheckedRun step terms round (count + 1) trace final

theorem successful_run_has_checked_chain (step : Nat → Trace → Trace)
    (terms : Nat → Trace → List Ext3)
    (happend : ∀ round trace, (step round trace).constraints = trace.constraints ++ terms round trace)
    (count round : Nat) (trace : Trace)
    (hzero : allZero (run step round count trace).constraints = true) :
    CheckedRun step terms round count trace (run step round count trace) := by
  induction count generalizing round trace with
  | zero => exact .done round trace
  | succ count ih =>
    rcases run_preserves_constraint_prefix step terms happend count (round + 1) (step round trace)
      with ⟨suffix, hs⟩
    have hnext : allZero (step round trace).constraints = true :=
      ((all_zero_append _ _).mp (by rw [← hs]; exact hzero)).1
    have hlocal : allZero (terms round trace) = true := by
      rw [happend] at hnext
      exact ((all_zero_append _ _).mp hnext).2
    exact .next hlocal (ih (round + 1) (step round trace) hzero)

theorem full_round_chain_checks_actual_sbox_inputs (wires : List Ext3)
    (constantRound wireStart : Nat → Nat) (count round : Nat) (trace : Trace)
    (hzero : allZero (run (fun r => fullStep wires (constantRound r) (wireStart r)) round count trace).constraints = true) :
    CheckedRun (fun r => fullStep wires (constantRound r) (wireStart r))
      (fun r t => fullConstraints wires (addConstantLayer t.state (constantRound r)) (wireStart r))
      round count trace (run (fun r => fullStep wires (constantRound r) (wireStart r)) round count trace) :=
  successful_run_has_checked_chain
    (fun r => fullStep wires (constantRound r) (wireStart r))
    (fun r t => fullConstraints wires (addConstantLayer t.state (constantRound r)) (wireStart r))
    (fun _ _ => rfl) count round trace hzero

theorem partial_round_chain_checks_actual_sbox_inputs (wires : List Ext3)
    (count round : Nat) (trace : Trace)
    (hzero : allZero (run (partialStep wires) round count trace).constraints = true) :
    CheckedRun (partialStep wires) (fun r t => [sub (stateAt t.state 0) (wire wires (65 + r))])
      round count trace (run (partialStep wires) round count trace) :=
  successful_run_has_checked_chain (partialStep wires)
    (fun r t => [sub (stateAt t.state 0) (wire wires (65 + r))])
    (fun _ _ => rfl) count round trace hzero

theorem final_partial_skips_zero_constant (source : Ext3) :
    partialSboxValue source 21 = sbox source := rfl

theorem partial_step_matches_rust_zero_constant (source : Ext3) (round : Nat) :
    partialSboxValue source round = addBase (sbox source) (partialRoundConstants.getD round 0) := by
  unfold partialSboxValue
  split
  · have hr : round = 21 := by omega
    subst round
    exact (add_base_zero _).symm
  · rfl

theorem fixed_wire_layout_bounds (column : Fin 12) (delta : Fin 4) (firstRound : Nat)
    (hFirst : 1 ≤ firstRound ∧ firstRound < 4) (partialRound : Fin 22) (lastRound : Fin 4) :
    column.val < 135 ∧ 12 + column.val < 135 ∧ 24 < 135 ∧ 25 + delta.val < 135 ∧
    29 + 12 * (firstRound - 1) + column.val < 135 ∧
    65 + partialRound.val < 135 ∧ 87 + 12 * lastRound.val + column.val < 135 := by omega

theorem mds_wire_layout_bounds (row : Fin 12) (lane : Fin 2) :
    2 * row.val + lane.val < 48 ∧ 2 * (12 + row.val) + lane.val < 48 := by omega

theorem all_zero_poseidon_reduction (wires : List Ext3) (alpha : Ext3)
    (hw : 135 ≤ wires.length) (hz : allZero (evalPoseidon wires) = true) :
    evalPoseidonReduced wires alpha = some zero := by
  simp only [evalPoseidonReduced, Nat.not_lt.mpr hw, ↓reduceIte]
  rw [Gates.horner_all_zero _ _ ((all_zero_iff _).mp hz)]

theorem all_zero_mds_reduction (wires : List Ext3) (alpha : Ext3)
    (hw : 48 ≤ wires.length) (hz : allZero (evalPoseidonMds wires) = true) :
    evalPoseidonMdsReduced wires alpha = some zero := by
  simp only [evalPoseidonMdsReduced, Nat.not_lt.mpr hw, ↓reduceIte]
  rw [Gates.horner_all_zero _ _ ((all_zero_iff _).mp hz)]

theorem diagonal_table_lookup (row : Fin 12) :
    mdsDiag.getD row.val 0 = if row.val = 0 then 8 else 0 := by
  have h : ∀ r : Fin 12, mdsDiag.getD r.val 0 = if r.val = 0 then 8 else 0 := by decide
  exact h row

theorem scalar_zero (x : Ext3) : scalar x 0 = zero := by
  apply Subtype.eq
  simp [scalar, Arithmetic.scalar, Arithmetic.mul, Arithmetic.reduce, Arithmetic.zero, zero]

theorem sparse_mds_equals_full_diagonal (state : State) (row : Fin 12) :
    mdsRow state row = mdsGeneralRow state row := by
  unfold mdsRow mdsGeneralRow
  rw [diagonal_table_lookup]
  split
  · have hr : row = 0 := Fin.ext ‹row.val = 0›
    subst row
    rfl
  · simp only [scalar_zero, Algebra.vadd_zero]

/-- Deterministic ordinary witness construction for the zero-input, no-swap
    Poseidon gate. This builds actual intermediate values, not assumed equations.
    It is a local valid-gate example, not an entire PCS proof. -/
structure WitnessTrace where
  state : State
  wires : List Ext3

def runWitness (step : Nat → WitnessTrace → WitnessTrace) : Nat → Nat → WitnessTrace → WitnessTrace
  | _, 0, trace => trace
  | round, count + 1, trace => runWitness step (round + 1) count (step round trace)

def fullWitnessStep (round : Nat) (trace : WitnessTrace) : WitnessTrace :=
  let inputs := addConstantLayer trace.state round
  ⟨mdsLayer (sboxLayer inputs), trace.wires ++ stateList inputs⟩

def partialWitnessStep (round : Nat) (trace : WitnessTrace) : WitnessTrace :=
  let source := stateAt trace.state 0
  let state := makeState (fun i => if i.val = 0 then partialSboxValue source round else stateAt trace.state i)
  ⟨mdsPartialFast state round, trace.wires ++ [source]⟩

def zeroInputWitness : List Ext3 :=
  let first := runWitness fullWitnessStep 1 3
    ⟨mdsLayer (sboxLayer (addConstantLayer zeroState 0)), []⟩
  let middle := runWitness partialWitnessStep 0 22
    ⟨mdsPartialInit (partialFirstConstantLayer first.state), []⟩
  let last := runWitness (fun round => fullWitnessStep (26 + round)) 0 4 ⟨middle.state, []⟩
  List.replicate 12 zero ++ stateList last.state ++ [zero] ++ List.replicate 4 zero ++
    first.wires ++ middle.wires ++ last.wires

theorem witness_run_count (step : Nat → WitnessTrace → WitnessTrace) (increment : Nat)
    (h : ∀ round trace, (step round trace).wires.length = trace.wires.length + increment)
    (count round : Nat) (trace : WitnessTrace) :
    (runWitness step round count trace).wires.length = trace.wires.length + count * increment := by
  induction count generalizing round trace with
  | zero => simp [runWitness]
  | succ count ih =>
    rw [runWitness, ih, h]
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem zero_input_witness_length : zeroInputWitness.length = 135 := by
  have hf : ∀ round trace, (fullWitnessStep round trace).wires.length = trace.wires.length + 12 := by
    intro _ trace
    simp [fullWitnessStep, state_list_length]
  have hp : ∀ round trace, (partialWitnessStep round trace).wires.length = trace.wires.length + 1 := by
    intro _ trace
    simp [partialWitnessStep]
  simp only [zeroInputWitness, List.length_append, List.length_replicate, List.length_cons, List.length_nil,
    state_list_length, witness_run_count _ 12 hf, witness_run_count _ 1 hp,
    witness_run_count _ 12 (fun _ _ => hf _ _)]

/-- A valid all-zero MDS gate, for every reduction challenge. -/
theorem zero_mds_constraints : allZero (evalPoseidonMds (List.replicate 48 zero)) = true := by
  simp only [allZero, evalPoseidonMds, mdsGateExpected, mdsGeneralRow,
    mdsCirculantRow, mdsGateInput, at_makeState]
  decide

theorem zero_mds_success (alpha : Ext3) :
    evalPoseidonMdsReduced (List.replicate 48 zero) alpha = some zero :=
  all_zero_mds_reduction _ _ (by simp) zero_mds_constraints

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem zero_input_poseidon_constraints : allZero (evalPoseidon zeroInputWitness) = true := by decide

/-- A complete valid-gate example for every alpha, with actual nonzero round
    constants, all 30 rounds and all 123 equations. No evaluator observation or
    native_decide is used. This does not assert validity of a full PCS proof. -/
theorem zero_input_poseidon_success (alpha : Ext3) :
    evalPoseidonReduced zeroInputWitness alpha = some zero :=
  all_zero_poseidon_reduction _ _ (by simp [zero_input_witness_length]) zero_input_poseidon_constraints

/-- Existing independent zero-input test vector in
    plonky2/src/hash/poseidon_goldilocks.rs::tests::test_vectors. The fixture's
    outputs were originally calculated with the hadeshash reference implementation. -/
def standardZeroOutput : List Nat :=
  [0x3c18a9786cb0b359, 0xc4055e3364a246c3, 0x7953db0ab48808f4, 0xc71603f33a1144ca,
   0xd7709673896996dc, 0x46a84e87642f44ed, 0xd032648251ee0b3c, 0x1c687363b207df62,
   0xdf8565563e8045fe, 0x40f5b37ff4254dae, 0xd070f637b431067c, 0x1792b1c4342109d7]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem zero_input_matches_standard_output :
    (zeroInputWitness.drop 12).take 12 = standardZeroOutput.map Norm.embed := by decide

end Audit.Wire3.Poseidon
