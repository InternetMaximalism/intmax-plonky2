import Audit.Wire3.GateCosetPolynomial

/-!
ID 4: concrete Poseidon polynomial state/constraint computation. Every literal
table, sparse MDS update, partial matrix orientation, round/wire address and
constraint order follows the current executable Poseidon audit model. Fresh
claimed S-box-input wires are installed before exponentiation; no vanishing
constraint is assumed to do this reset. The same state transitions prove all
constraints have degree at most seven when wire columns are affine.
Metadata/tables/aggregation alpha are fixed; no hash or evaluator oracle,
Boolean swap truth, circuit witness or cryptographic assumption is introduced.
Exact equalities are to the audit executable functions, not Yul/compiler/ABI
refinement, permutation correctness, collision resistance or PCS soundness.
Source: PoseidonGateExt3.sol:31-77,142-500; gate_ext3.rs:737-875.
-/
namespace Audit.Wire3.GatePoseidonPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateMdsPolynomial
open Polynomial

abbrev State := Fin 12 → P
def stateValue (s : State) (x : Element) : Poseidon.State := Poseidon.makeState (fun i => value (s i) x)
def StateBound (s : State) (bound : Nat) : Prop := ∀ i, (s i).natDegree ≤ bound

theorem state_value_at (s : State) (x : Element) (i : Fin 12) :
    Poseidon.stateAt (stateValue s x) i = value (s i) x := Poseidon.at_makeState _ _

noncomputable def wireState (wires : List P) (offset : Nat) : State := fun i => readPoly wires (offset+i.val)
noncomputable def addBasePoly (p : P) (n : Nat) : P := p+C (n : Element)
noncomputable def sboxPoly (p : P) : P := (p*(p*p))*((p*p)*(p*p))
noncomputable def sboxLayer (s : State) : State := fun i => sboxPoly (s i)
noncomputable def addConstantLayer (s : State) (round : Nat) : State := fun i =>
  addBasePoly (s i) (PoseidonConstants.allRoundConstants.getD (round*12+i.val) 0)
noncomputable def partialFirstConstantLayer (s : State) : State := fun i =>
  addBasePoly (s i) (PoseidonConstants.partialFirstConstants.getD i.val 0)

theorem wire_state_actual (wires : List P) (offset : Nat) (x : Element) :
    stateValue (wireState wires offset) x = Poseidon.wireState (columnValues wires x) offset := by
  apply congrArg Poseidon.makeState
  funext i
  exact read_poly_is_actual_read wires (offset+i.val) x
theorem add_base_actual (p : P) (n : Nat) (x : Element) :
    value (addBasePoly p n) x = Poseidon.addBase (value p x) n := by
  rw [Poseidon.add_base_is_field_add]
  simp only [addBasePoly,value_add,value_nat_constant]
  rfl
theorem sbox_actual (p : P) (x : Element) : value (sboxPoly p) x = Poseidon.sbox (value p x) := by
  simp only [sboxPoly,value_mul,Poseidon.sbox_exact_seventh_power]
theorem sbox_layer_actual (s : State) (x : Element) :
    stateValue (sboxLayer s) x = Poseidon.sboxLayer (stateValue s x) := by
  apply congrArg Poseidon.makeState
  funext i
  simp only [sboxLayer,sbox_actual,state_value_at]
theorem constant_layer_actual (s : State) (round : Nat) (x : Element) :
    stateValue (addConstantLayer s round) x = Poseidon.addConstantLayer (stateValue s x) round := by
  apply congrArg Poseidon.makeState
  funext i
  simp only [addConstantLayer,add_base_actual,state_value_at]
theorem partial_first_actual (s : State) (x : Element) :
    stateValue (partialFirstConstantLayer s) x = Poseidon.partialFirstConstantLayer (stateValue s x) := by
  apply congrArg Poseidon.makeState
  funext i
  simp only [partialFirstConstantLayer,add_base_actual,state_value_at]

noncomputable def mdsCirculantRow (s : State) (row : Fin 12) : P :=
  weightedSum Poseidon.coordinates (fun i => s (Poseidon.rotated row i))
    (fun i => PoseidonConstants.mdsCirc.getD i.val 0) 0
noncomputable def mdsRow (s : State) (row : Fin 12) : P :=
  if row.val = 0 then mdsCirculantRow s row + s 0*C (PoseidonConstants.mdsDiag.getD 0 0 : Element)
  else mdsCirculantRow s row
noncomputable def mdsLayer (s : State) : State := mdsRow s
noncomputable def mdsPartialInit (s : State) : State := fun column =>
  if column.val = 0 then s 0 else weightedSum Poseidon.tailCoordinates
    (fun row => s (Poseidon.tailIndex row))
    (fun row => PoseidonConstants.partialInitialMatrix.getD (row.val*11+(column.val-1)) 0) 0
noncomputable def mdsPartialFast (s : State) (round : Nat) : State := fun i =>
  if i.val = 0 then weightedSum Poseidon.tailCoordinates (fun j => s (Poseidon.tailIndex j))
    (fun j => PoseidonConstants.partialWHats.getD (round*11+j.val) 0) (s 0*C (Poseidon.partialM00 : Element))
  else s 0*C (PoseidonConstants.partialVs.getD (round*11+(i.val-1)) 0 : Element)+s i

theorem mds_circulant_actual (s : State) (row : Fin 12) (x : Element) :
    value (mdsCirculantRow s row) x = Poseidon.mdsCirculantRow (stateValue s x) row := by
  simp only [mdsCirculantRow,weighted_sum_eval,value_zero,Poseidon.mdsCirculantRow,state_value_at]
theorem mds_row_actual (s : State) (row : Fin 12) (x : Element) :
    value (mdsRow s row) x = Poseidon.mdsRow (stateValue s x) row := by
  unfold mdsRow Poseidon.mdsRow
  split <;> simp only [value_add,value_scalar,mds_circulant_actual,state_value_at]
theorem mds_layer_actual (s : State) (x : Element) :
    stateValue (mdsLayer s) x = Poseidon.mdsLayer (stateValue s x) := by
  apply congrArg Poseidon.makeState
  funext i
  exact mds_row_actual s i x
theorem mds_partial_init_actual (s : State) (x : Element) :
    stateValue (mdsPartialInit s) x = Poseidon.mdsPartialInit (stateValue s x) := by
  apply congrArg Poseidon.makeState
  funext i
  unfold mdsPartialInit
  split <;> simp only [weighted_sum_eval,value_zero,state_value_at]
theorem mds_partial_fast_actual (s : State) (round : Nat) (x : Element) :
    stateValue (mdsPartialFast s round) x = Poseidon.mdsPartialFast (stateValue s x) round := by
  apply congrArg Poseidon.makeState
  funext i
  unfold mdsPartialFast
  split <;> simp only [weighted_sum_eval,value_scalar,value_add,state_value_at]

noncomputable def swapPolys (wires : List P) : List P :=
  let swap := readPoly wires 24
  swap*(swap-1) :: (List.range 4).map fun i =>
    swap*(readPoly wires (i+4)-readPoly wires i)-readPoly wires (25+i)
noncomputable def swapState (wires : List P) : State := fun i =>
  if i.val < 4 then readPoly wires i.val+readPoly wires (25+i.val)
  else if i.val < 8 then readPoly wires i.val-readPoly wires (25+(i.val-4))
  else readPoly wires i.val
noncomputable def fullPolys (wires : List P) (expected : State) (offset : Nat) : List P :=
  Poseidon.coordinates.map fun i => expected i-readPoly wires (offset+i.val)

theorem swap_polys_actual (wires : List P) (x : Element) :
    columnValues (swapPolys wires) x = Poseidon.swapConstraints (columnValues wires x) := by
  simp only [swapPolys,columnValues,List.map_cons,List.map_map,Function.comp_def,value_mul,value_sub,
    value_one,read_poly_is_actual_read,Poseidon.swapConstraints,Poseidon.wire]
  rfl
theorem swap_state_actual (wires : List P) (x : Element) :
    stateValue (swapState wires) x = Poseidon.swapState (columnValues wires x) := by
  apply congrArg Poseidon.makeState
  funext i
  unfold swapState
  split
  · simp only [value_add,read_poly_is_actual_read,Poseidon.wire]
  · split <;> simp only [value_sub,read_poly_is_actual_read,Poseidon.wire]
theorem full_polys_actual (wires : List P) (expected : State) (offset : Nat) (x : Element) :
    columnValues (fullPolys wires expected offset) x =
      Poseidon.fullConstraints (columnValues wires x) (stateValue expected x) offset := by
  simp only [fullPolys,columnValues,List.map_map,Function.comp_def,value_sub,
    read_poly_is_actual_read,Poseidon.fullConstraints,Poseidon.wire,state_value_at]

structure Trace where
  state : State
  constraints : List P
def traceValue (t : Trace) (x : Element) : Poseidon.Trace := ⟨stateValue t.state x,columnValues t.constraints x⟩
noncomputable def fullStep (wires : List P) (constantRound wireStart : Nat) (t : Trace) : Trace :=
  ⟨mdsLayer (sboxLayer (wireState wires wireStart)),
    t.constraints ++ fullPolys wires (addConstantLayer t.state constantRound) wireStart⟩
noncomputable def partialSboxPoly (source : P) (round : Nat) : P :=
  if round+1=22 then sboxPoly source else
    addBasePoly (sboxPoly source) (PoseidonConstants.partialRoundConstants.getD round 0)
noncomputable def partialStep (wires : List P) (round : Nat) (t : Trace) : Trace :=
  let source := readPoly wires (65+round)
  let state : State := fun i => if i.val=0 then partialSboxPoly source round else t.state i
  ⟨mdsPartialFast state round,t.constraints ++ [t.state 0-source]⟩
noncomputable def run (step : Nat → Trace → Trace) : Nat → Nat → Trace → Trace
  | _,0,t => t
  | round,count+1,t => run step (round+1) count (step round t)

theorem full_step_actual (wires : List P) (constantRound wireStart : Nat) (t : Trace) (x : Element) :
    traceValue (fullStep wires constantRound wireStart t) x =
      Poseidon.fullStep (columnValues wires x) constantRound wireStart (traceValue t x) := by
  simp only [traceValue,fullStep,Poseidon.fullStep,Audit.Wire3.GateCosetPolynomial.column_values_append,
    full_polys_actual,mds_layer_actual,sbox_layer_actual,wire_state_actual,constant_layer_actual]
theorem partial_sbox_actual (source : P) (round : Nat) (x : Element) :
    value (partialSboxPoly source round) x = Poseidon.partialSboxValue (value source x) round := by
  unfold partialSboxPoly Poseidon.partialSboxValue
  split <;> simp only [sbox_actual,add_base_actual]
theorem partial_step_actual (wires : List P) (round : Nat) (t : Trace) (x : Element) :
    traceValue (partialStep wires round t) x =
      Poseidon.partialStep (columnValues wires x) round (traceValue t x) := by
  have hs : stateValue (fun i => if i.val=0 then partialSboxPoly (readPoly wires (65+round)) round else t.state i) x =
      Poseidon.makeState (fun i => if i.val=0 then
        Poseidon.partialSboxValue (Poseidon.wire (columnValues wires x) (65+round)) round
        else Poseidon.stateAt (stateValue t.state x) i) := by
    apply congrArg Poseidon.makeState
    funext i
    split <;> simp_all only [↓reduceIte,partial_sbox_actual,read_poly_is_actual_read,Poseidon.wire,state_value_at]
  simp only [traceValue,partialStep,Poseidon.partialStep,Audit.Wire3.GateCosetPolynomial.column_values_append,
    mds_partial_fast_actual,hs,columnValues,List.map_append,List.map_cons,List.map_nil,value_sub,read_poly_is_actual_read,
    state_value_at,Poseidon.wire]

/-- Generic induction helper; the final concrete bridge discharges this
commutation equation with the literal full/partial step theorems above. -/
theorem run_actual (step : Nat → Trace → Trace) (actualStep : Nat → Poseidon.Trace → Poseidon.Trace)
    (round count : Nat) (t : Trace) (x : Element)
    (hstep : ∀ i s, traceValue (step i s) x = actualStep i (traceValue s x)) :
    traceValue (run step round count t) x = Poseidon.run actualStep round count (traceValue t x) := by
  induction count generalizing round t with
  | zero => rfl
  | succ count ih => rw [run,ih,hstep,Poseidon.run]

noncomputable def firstFullRounds (wires : List P) (s : State) : Trace :=
  run (fun round => fullStep wires round (29+12*(round-1))) 1 3
    ⟨mdsLayer (sboxLayer (addConstantLayer s 0)),[]⟩
noncomputable def partialRounds (wires : List P) (s : State) : Trace := run (partialStep wires) 0 22 ⟨s,[]⟩
noncomputable def secondFullRounds (wires : List P) (s : State) : Trace :=
  run (fun round => fullStep wires (26+round) (87+12*round)) 0 4 ⟨s,[]⟩

theorem first_full_actual (wires : List P) (s : State) (x : Element) :
    traceValue (firstFullRounds wires s) x = Poseidon.firstFullRounds (columnValues wires x) (stateValue s x) := by
  unfold firstFullRounds
  rw [run_actual _ (fun round => Poseidon.fullStep (columnValues wires x) round (29+12*(round-1)))
    1 3 _ x (fun _ _ => full_step_actual _ _ _ _ _)]
  simp only [traceValue,mds_layer_actual,sbox_layer_actual,constant_layer_actual,columnValues,List.map_nil,
    Poseidon.firstFullRounds]
theorem partial_rounds_actual (wires : List P) (s : State) (x : Element) :
    traceValue (partialRounds wires s) x = Poseidon.partialRounds (columnValues wires x) (stateValue s x) := by
  exact run_actual _ (Poseidon.partialStep (columnValues wires x)) 0 22 _ x
    (fun _ _ => partial_step_actual _ _ _ _)
theorem second_full_actual (wires : List P) (s : State) (x : Element) :
    traceValue (secondFullRounds wires s) x = Poseidon.secondFullRounds (columnValues wires x) (stateValue s x) := by
  exact run_actual _ (fun round => Poseidon.fullStep (columnValues wires x) (26+round) (87+12*round))
    0 4 _ x (fun _ _ => full_step_actual _ _ _ _ _)

structure Stages where
  first : Trace
  middle : Trace
  second : Trace
noncomputable def stages (wires : List P) : Stages :=
  let first := firstFullRounds wires (swapState wires)
  let middle := partialRounds wires (mdsPartialInit (partialFirstConstantLayer first.state))
  let second := secondFullRounds wires middle.state
  ⟨first,middle,second⟩
def stagesValue (s : Stages) (x : Element) : Poseidon.Stages :=
  ⟨traceValue s.first x,traceValue s.middle x,traceValue s.second x⟩
noncomputable def poseidonPolys (wires : List P) : List P :=
  let s := stages wires
  swapPolys wires ++ s.first.constraints ++ s.middle.constraints ++ s.second.constraints ++
    fullPolys wires s.second.state 12

theorem stages_actual (wires : List P) (x : Element) : stagesValue (stages wires) x = Poseidon.stages (columnValues wires x) := by
  have hfirst := first_full_actual wires (swapState wires) x
  rw [swap_state_actual] at hfirst
  have hfstate := congrArg Poseidon.Trace.state hfirst
  simp only [traceValue] at hfstate
  have hmid := partial_rounds_actual wires
    (mdsPartialInit (partialFirstConstantLayer (firstFullRounds wires (swapState wires)).state)) x
  rw [mds_partial_init_actual,partial_first_actual,hfstate] at hmid
  have hmstate := congrArg Poseidon.Trace.state hmid
  simp only [traceValue] at hmstate
  have hsecond := second_full_actual wires (partialRounds wires
    (mdsPartialInit (partialFirstConstantLayer (firstFullRounds wires (swapState wires)).state))).state x
  rw [hmstate] at hsecond
  simp only [stagesValue,stages,Poseidon.stages,hfirst,hmid,hsecond]

theorem poseidon_actual (wires : List P) (x : Element) :
    columnValues (poseidonPolys wires) x = Poseidon.evalPoseidon (columnValues wires x) := by
  have h := stages_actual wires x
  have hf := congrArg (fun s : Poseidon.Stages => s.first.constraints) h
  have hm := congrArg (fun s : Poseidon.Stages => s.middle.constraints) h
  have hs := congrArg (fun s : Poseidon.Stages => s.second.constraints) h
  have ht := congrArg (fun s : Poseidon.Stages => s.second.state) h
  simp only [stagesValue,traceValue] at hf hm hs ht
  simp only [poseidonPolys,Audit.Wire3.GateCosetPolynomial.column_values_append,swap_polys_actual,
    full_polys_actual,Poseidon.evalPoseidon,Poseidon.outputConstraints,hf,hm,hs,ht]

theorem poseidon_constraint_count (wires : List P) : (poseidonPolys wires).length = 123 := by
  have h := congrArg List.length (poseidon_actual wires (0 : Element))
  simpa only [column_values_preserve_length,Poseidon.poseidon_constraint_count] using h

theorem add_base_degree (p : P) (n bound : Nat) (hp : p.natDegree ≤ bound) :
    (addBasePoly p n).natDegree ≤ bound := by
  exact (add_degree_bound _ _ bound 0 hp (le_of_eq (natDegree_C _))).trans (by omega)
theorem wire_state_degree (wires : List P) (offset : Nat) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    StateBound (wireState wires offset) 1 := fun _ => read_poly_degree wires 1 _ hw
theorem constant_layer_degree (s : State) (round bound : Nat) (hs : StateBound s bound) :
    StateBound (addConstantLayer s round) bound := fun i => add_base_degree _ _ bound (hs i)
theorem partial_first_degree (s : State) (bound : Nat) (hs : StateBound s bound) :
    StateBound (partialFirstConstantLayer s) bound := fun i => add_base_degree _ _ bound (hs i)
theorem sbox_degree (p : P) (hp : p.natDegree ≤ 1) : (sboxPoly p).natDegree ≤ 7 := by
  have h2 := mul_degree_bound _ _ 1 1 hp hp
  have h3 := mul_degree_bound _ _ 1 2 hp h2
  have h4 := mul_degree_bound _ _ 2 2 h2 h2
  exact mul_degree_bound _ _ 3 4 h3 h4
theorem sbox_layer_degree (s : State) (hs : StateBound s 1) : StateBound (sboxLayer s) 7 :=
  fun i => sbox_degree _ (hs i)

theorem weighted_sum_bound {A : Type} (indices : List A) (f : A → P) (weight : A → Nat)
    (initial : P) (bound : Nat) (hi : initial.natDegree ≤ bound) (hf : ∀ i ∈ indices, (f i).natDegree ≤ bound) :
    (weightedSum indices f weight initial).natDegree ≤ bound := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i rest ih =>
      have hm := mul_degree_bound (f i) (C (weight i : Element)) bound 0 (hf i (by simp)) (le_of_eq (natDegree_C _))
      have hn := add_degree_bound initial _ bound bound hi (by simpa only [Nat.add_zero] using hm)
      exact ih (initial+f i*C (weight i : Element)) (by simpa only [max_self] using hn)
        (fun j hj => hf j (by simp [hj]))

theorem scalar_degree (p : P) (n bound : Nat) (hp : p.natDegree ≤ bound) :
    (p*C (n : Element)).natDegree ≤ bound := by
  simpa only [Nat.add_zero] using mul_degree_bound p (C (n : Element)) bound 0 hp (le_of_eq (natDegree_C _))
theorem mds_circulant_degree (s : State) (row : Fin 12) (bound : Nat) (hs : StateBound s bound) :
    (mdsCirculantRow s row).natDegree ≤ bound := weighted_sum_bound _ _ _ 0 bound (by simp) (fun i _ => hs _)
theorem mds_row_degree (s : State) (row : Fin 12) (bound : Nat) (hs : StateBound s bound) :
    (mdsRow s row).natDegree ≤ bound := by
  unfold mdsRow
  split
  · exact (add_degree_bound _ _ bound bound (mds_circulant_degree s row bound hs)
      (scalar_degree _ _ bound (hs 0))).trans (by omega)
  · exact mds_circulant_degree s row bound hs
theorem mds_layer_degree (s : State) (bound : Nat) (hs : StateBound s bound) :
    StateBound (mdsLayer s) bound := fun i => mds_row_degree s i bound hs
theorem mds_partial_init_degree (s : State) (bound : Nat) (hs : StateBound s bound) :
    StateBound (mdsPartialInit s) bound := by
  intro i
  unfold mdsPartialInit
  split
  · exact hs 0
  · exact weighted_sum_bound _ _ _ 0 bound (by simp) (fun j _ => hs _)
theorem mds_partial_fast_degree (s : State) (round bound : Nat) (hs : StateBound s bound) :
    StateBound (mdsPartialFast s round) bound := by
  intro i
  unfold mdsPartialFast
  split
  · exact weighted_sum_bound _ _ _ _ bound (scalar_degree _ _ bound (hs 0)) (fun j _ => hs _)
  · exact (add_degree_bound _ _ bound bound (scalar_degree _ _ bound (hs 0)) (hs i)).trans (by omega)

theorem swap_state_degree (wires : List P) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) : StateBound (swapState wires) 1 := by
  intro i
  unfold swapState
  split
  · exact add_degree_bound _ _ 1 1 (read_poly_degree wires 1 _ hw) (read_poly_degree wires 1 _ hw)
  · split
    · exact sub_degree_bound _ _ 1 1 (read_poly_degree wires 1 _ hw) (read_poly_degree wires 1 _ hw)
    · exact read_poly_degree wires 1 _ hw
theorem swap_polys_degree (wires : List P) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ swapPolys wires, p.natDegree ≤ 2 := by
  intro p hp
  have hswap := read_poly_degree wires 1 24 hw
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact mul_degree_bound _ _ 1 1 hswap (sub_degree_bound _ _ 1 0 hswap (by simp))
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact sub_degree_bound _ _ 2 1 (mul_degree_bound _ _ 1 1 hswap
      (sub_degree_bound _ _ 1 1 (read_poly_degree wires 1 _ hw) (read_poly_degree wires 1 _ hw)))
      (read_poly_degree wires 1 _ hw)
theorem full_polys_degree (wires : List P) (expected : State) (offset bound : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (he : StateBound expected bound) (hb : 1 ≤ bound) :
    ∀ p ∈ fullPolys wires expected offset, p.natDegree ≤ bound := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (sub_degree_bound _ _ bound 1 (he i) (read_poly_degree wires 1 _ hw)).trans (by omega)

def TraceBound (t : Trace) : Prop := StateBound t.state 7 ∧ ∀ p ∈ t.constraints, p.natDegree ≤ 7
theorem full_step_degree (wires : List P) (constantRound wireStart : Nat) (t : Trace)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (ht : TraceBound t) :
    TraceBound (fullStep wires constantRound wireStart t) := by
  refine ⟨mds_layer_degree _ 7 (sbox_layer_degree _ (wire_state_degree wires wireStart hw)),?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ht.2 p hp
  · exact full_polys_degree wires _ wireStart 7 hw (constant_layer_degree t.state constantRound 7 ht.1) (by decide) p hp
theorem partial_sbox_degree (source : P) (round : Nat) (hs : source.natDegree ≤ 1) :
    (partialSboxPoly source round).natDegree ≤ 7 := by
  unfold partialSboxPoly
  split
  · exact sbox_degree source hs
  · exact add_base_degree _ _ 7 (sbox_degree source hs)
theorem partial_step_degree (wires : List P) (round : Nat) (t : Trace)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (ht : TraceBound t) : TraceBound (partialStep wires round t) := by
  have hsource := read_poly_degree wires 1 (65+round) hw
  let installed : State := fun i => if i.val=0 then partialSboxPoly (readPoly wires (65+round)) round else t.state i
  have hi : StateBound installed 7 := by
    intro i
    dsimp only [installed]
    split
    · exact partial_sbox_degree _ round hsource
    · exact ht.1 i
  refine ⟨mds_partial_fast_degree installed round 7 hi,?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ht.2 p hp
  · simp only [List.mem_singleton] at hp
    subst p
    exact sub_degree_bound _ _ 7 1 (ht.1 0) hsource
theorem run_degree (step : Nat → Trace → Trace) (round count : Nat) (t : Trace)
    (hstep : ∀ i s, TraceBound s → TraceBound (step i s)) (ht : TraceBound t) :
    TraceBound (run step round count t) := by
  induction count generalizing round t with
  | zero => exact ht
  | succ _ ih => exact ih (round+1) (step round t) (hstep round t ht)
theorem first_full_degree (wires : List P) (s : State)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hs : StateBound s 1) : TraceBound (firstFullRounds wires s) :=
  run_degree _ 1 3 _ (fun _ _ h => full_step_degree _ _ _ _ hw h)
    ⟨mds_layer_degree _ 7 (sbox_layer_degree _ (constant_layer_degree s 0 1 hs)),by simp⟩
theorem partial_rounds_degree (wires : List P) (s : State)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hs : StateBound s 7) : TraceBound (partialRounds wires s) :=
  run_degree _ 0 22 _ (fun _ _ h => partial_step_degree _ _ _ hw h) ⟨hs,by simp⟩
theorem second_full_degree (wires : List P) (s : State)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hs : StateBound s 7) : TraceBound (secondFullRounds wires s) :=
  run_degree _ 0 4 _ (fun _ _ h => full_step_degree _ _ _ _ hw h) ⟨hs,by simp⟩
theorem stages_degree (wires : List P) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    TraceBound (stages wires).first ∧ TraceBound (stages wires).middle ∧ TraceBound (stages wires).second := by
  have hf := first_full_degree wires (swapState wires) hw (swap_state_degree wires hw)
  have hm := partial_rounds_degree wires _ hw
    (mds_partial_init_degree _ 7 (partial_first_degree _ 7 hf.1))
  have hs := second_full_degree wires _ hw hm.1
  exact ⟨hf,hm,hs⟩
theorem poseidon_degree (wires : List P) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ poseidonPolys wires, p.natDegree ≤ 7 := by
  have h := stages_degree wires hw
  intro p hp
  simp only [poseidonPolys,List.mem_append] at hp
  rcases hp with (((hp | hp) | hp) | hp) | hp
  · exact (swap_polys_degree wires hw p hp).trans (by decide)
  · exact h.1.2 p hp
  · exact h.2.1.2 p hp
  · exact h.2.2.2 p hp
  · exact full_polys_degree wires _ 12 7 hw h.2.2.1 (by decide) p hp

end Audit.Wire3.GatePoseidonPolynomial
