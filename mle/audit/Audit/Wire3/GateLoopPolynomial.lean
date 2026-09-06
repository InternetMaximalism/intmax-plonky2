import Audit.Wire3.GateCheckedPolynomial

/-!
Concrete polynomial bridges for gate IDs 8,9,10,11. The same literal source
recurrences, constraint order and totalized reads as GatesAdditional are used.
All wire columns have degree at most one; local constants also vary in the
eventual checked wrapper (these four families do not use local constants).
Metadata and integer bases are fixed. The reducing alpha is a WIRE, not the
fixed aggregation alpha. Its accumulator is replaced by the next wire on
EVERY step, independently of constraint satisfaction. No Boolean/range truth,
witness, arbitrary evaluator or declared-degree oracle is assumed.

Source: Plonky2GateEvaluatorExt3.sol:611-799; gate_ext3.rs:923-987.
Exact equalities below are to executable audit functions. Source/Yul/ABI and
overflow refinement, committed-column provenance and cryptographic soundness
are not proved. The full checked configuration/length boundary is retained by
the separate contribution wrapper; low-level totalized reads are not a new
standalone source API. Existing four polynomial candidates remain unchanged.
-/
namespace Audit.Wire3.GateLoopPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateBasicPolynomial
open Polynomial

noncomputable def exponentiationPreviousPoly (wires : List P) (bits i : Nat) : P :=
  if i = 0 then 1 else
    readPoly wires (2+bits+i-1) * readPoly wires (2+bits+i-1)

noncomputable def exponentiationExpectedPoly (wires : List P) (bits i : Nat) : P :=
  exponentiationPreviousPoly wires bits i *
    (readPoly wires (bits-i) * readPoly wires 0 + (1-readPoly wires (bits-i)))

noncomputable def exponentiationPolys (wires : List P) (bits : Nat) : List P :=
  (List.range bits).map (fun i => exponentiationExpectedPoly wires bits i - readPoly wires (2+bits+i)) ++
    [readPoly wires (1+bits)-readPoly wires (2+bits+bits-1)]

theorem exponentiation_previous_actual (wires : List P) (bits i : Nat) (x : Element) :
    value (exponentiationPreviousPoly wires bits i) x =
      GatesAdditional.exponentiationPrevious (columnValues wires x) bits i := by
  unfold exponentiationPreviousPoly GatesAdditional.exponentiationPrevious
  split
  · exact value_one x
  · rw [value_mul,read_poly_is_actual_read,Algebra.norm_square_is_multiplication]

theorem exponentiation_expected_actual (wires : List P) (bits i : Nat) (x : Element) :
    value (exponentiationExpectedPoly wires bits i) x =
      GatesAdditional.exponentiationExpected (columnValues wires x) bits i := by
  simp only [exponentiationExpectedPoly,value_mul,value_add,value_sub,value_one,
    exponentiation_previous_actual,read_poly_is_actual_read,GatesAdditional.exponentiationExpected]

theorem exponentiation_list_actual (wires : List P) (bits : Nat) (x : Element) :
    columnValues (exponentiationPolys wires bits) x =
      GatesAdditional.evalExponentiation (columnValues wires x) bits := by
  simp only [columnValues,exponentiationPolys,GatesAdditional.evalExponentiation,List.map_append,
    List.map_map,List.map_cons,List.map_nil,Function.comp_def,value_sub,
    exponentiation_expected_actual,read_poly_is_actual_read]

theorem exponentiation_previous_degree (wires : List P) (bits i : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    (exponentiationPreviousPoly wires bits i).natDegree ≤ 2 := by
  unfold exponentiationPreviousPoly
  split
  · simp
  · exact mul_degree_bound _ _ 1 1 (read_poly_degree wires 1 _ hw) (read_poly_degree wires 1 _ hw)

theorem exponentiation_expected_degree (wires : List P) (bits i : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    (exponentiationExpectedPoly wires bits i).natDegree ≤ 4 := by
  have hb := read_poly_degree wires 1 (bits-i) hw
  have hm := mul_degree_bound _ _ 1 1 hb (read_poly_degree wires 1 0 hw)
  have hs := sub_degree_bound 1 _ 0 1 (by simp) hb
  have ha := add_degree_bound _ _ 2 1 hm hs
  exact mul_degree_bound _ _ 2 2 (exponentiation_previous_degree wires bits i hw) ha

theorem exponentiation_list_degree (wires : List P) (bits : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ exponentiationPolys wires bits, p.natDegree ≤ 4 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact sub_degree_bound _ _ 4 1 (exponentiation_expected_degree wires bits i hw)
      (read_poly_degree wires 1 _ hw)
  · simp only [List.mem_singleton] at hp
    subst p
    exact (sub_degree_bound _ _ 1 1 (read_poly_degree wires 1 _ hw)
      (read_poly_degree wires 1 _ hw)).trans (by omega)

noncomputable def baseSumValuePoly (wires : List P) (limbs baseValue : Nat) : P :=
  hornerPoly ((List.range limbs).map fun i => readPoly wires (i+1)) (baseValue : Element)

noncomputable def baseSumRangePoly (p : P) (baseValue : Nat) : P :=
  productPoly ((List.range baseValue).map fun v : Nat => p-C (v : Element)) 1

noncomputable def baseSumPolys (wires : List P) (limbs baseValue : Nat) : List P :=
  (baseSumValuePoly wires limbs baseValue-readPoly wires 0) ::
    (List.range limbs).map (fun i => baseSumRangePoly (readPoly wires (i+1)) baseValue)

theorem base_sum_value_actual (wires : List P) (limbs baseValue : Nat) (x : Element) :
    value (baseSumValuePoly wires limbs baseValue) x =
      GatesAdditional.baseSumValue (columnValues wires x) limbs baseValue := by
  simp only [baseSumValuePoly,actual_horner_eval,columnValues,List.map_map,
    Function.comp_def,read_poly_is_actual_read,GatesAdditional.baseSumValue]
  rfl

theorem base_sum_range_actual (p : P) (baseValue : Nat) (x : Element) :
    value (baseSumRangePoly p baseValue) x = GatesAdditional.baseSumRangeProduct (value p x) baseValue := by
  simp only [baseSumRangePoly,actual_product_eval,value_one,columnValues,List.map_map,
    Function.comp_def,value_sub,value_nat_constant,GatesAdditional.baseSumRangeProduct]

theorem base_sum_list_actual (wires : List P) (limbs baseValue : Nat) (x : Element) :
    columnValues (baseSumPolys wires limbs baseValue) x =
      GatesAdditional.evalBaseSum (columnValues wires x) limbs baseValue := by
  simp only [columnValues,baseSumPolys,List.map_cons,List.map_map,Function.comp_def,
    value_sub,base_sum_value_actual,base_sum_range_actual,read_poly_is_actual_read,GatesAdditional.evalBaseSum]

theorem base_sum_value_degree (wires : List P) (limbs baseValue : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) : (baseSumValuePoly wires limbs baseValue).natDegree ≤ 1 := by
  apply fixed_alpha_horner_degree
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact read_poly_degree wires 1 _ hw

theorem base_sum_range_degree (p : P) (baseValue : Nat) (hp : p.natDegree ≤ 1) :
    (baseSumRangePoly p baseValue).natDegree ≤ baseValue := by
  have h := product_poly_degree ((List.range baseValue).map fun v : Nat => p-C (v : Element)) 1 0
    (by simp) (by
      intro q hq
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hq
      exact sub_degree_bound _ _ 1 0 hp (le_of_eq (natDegree_C _)))
  simpa only [baseSumRangePoly,List.length_map,List.length_range,Nat.zero_add] using h

theorem base_sum_list_degree (wires : List P) (limbs baseValue : Nat)
    (hb : 1 ≤ baseValue) (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ baseSumPolys wires limbs baseValue, p.natDegree ≤ baseValue := by
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact (sub_degree_bound _ _ 1 1 (base_sum_value_degree wires limbs baseValue hw)
      (read_poly_degree wires 1 0 hw)).trans hb
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact base_sum_range_degree _ baseValue (read_poly_degree wires 1 _ hw)

noncomputable def pairAddPoly (a b : PairPoly) : PairPoly := ⟨a.c0+b.c0,a.c1+b.c1⟩
noncomputable def pairSubPoly (a b : PairPoly) : PairPoly := ⟨a.c0-b.c0,a.c1-b.c1⟩
def pairPolys (a : PairPoly) : List P := [a.c0,a.c1]

theorem pair_add_actual (a b : PairPoly) (x : Element) :
    pairValue (pairAddPoly a b) x = GatesAdditionalCoset.pairAdd (pairValue a x) (pairValue b x) := by
  simp only [pairValue,pairAddPoly,GatesAdditionalCoset.pairAdd,value_add]

theorem pair_sub_actual (a b : PairPoly) (x : Element) :
    pairValue (pairSubPoly a b) x = GatesAdditionalCoset.pairSub (pairValue a x) (pairValue b x) := by
  simp only [pairValue,pairSubPoly,GatesAdditionalCoset.pairSub,value_sub]

theorem pair_polys_actual (a : PairPoly) (x : Element) :
    columnValues (pairPolys a) x = GatesAdditionalCoset.pairValues (pairValue a x) := rfl

theorem pair_add_degree (a b : PairPoly) (da db : Nat) (ha : PairBound a da) (hb : PairBound b db) :
    PairBound (pairAddPoly a b) (max da db) :=
  ⟨add_degree_bound _ _ da db ha.1 hb.1,add_degree_bound _ _ da db ha.2 hb.2⟩

theorem pair_sub_degree (a b : PairPoly) (da db : Nat) (ha : PairBound a da) (hb : PairBound b db) :
    PairBound (pairSubPoly a b) (max da db) :=
  ⟨sub_degree_bound _ _ da db ha.1 hb.1,sub_degree_bound _ _ da db ha.2 hb.2⟩

theorem pair_polys_degree (a : PairPoly) (bound : Nat) (ha : PairBound a bound) :
    ∀ p ∈ pairPolys a, p.natDegree ≤ bound := by
  intro p hp
  simp only [pairPolys,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact ha.1
  · exact ha.2

noncomputable def reducingCoefficientPoly (wires : List P) (extension : Bool) (i : Nat) : PairPoly :=
  if extension then pairRead wires (6+2*i) else ⟨readPoly wires (6+i),0⟩

noncomputable def reducingNextPoly (wires : List P) (count : Nat) (extension : Bool) (i : Nat) : PairPoly :=
  if i+1=count then pairRead wires 0 else
    pairRead wires (GatesAdditional.accumulatorStart count extension + 2*i)

noncomputable def reducingExpectedPoly (wires : List P) (extension : Bool) (i : Nat)
    (previous : PairPoly) : PairPoly :=
  pairAddPoly (pairMul previous (pairRead wires 2)) (reducingCoefficientPoly wires extension i)

structure ReducingPolyState where
  accumulator : PairPoly
  output : List P

def reducingStateValue (s : ReducingPolyState) (x : Element) : GatesAdditional.ReducingState :=
  ⟨pairValue s.accumulator x,columnValues s.output x⟩

noncomputable def reducingStepPoly (wires : List P) (count : Nat) (extension : Bool) (i : Nat)
    (s : ReducingPolyState) : ReducingPolyState :=
  let next := reducingNextPoly wires count extension i
  ⟨next,s.output ++ pairPolys (pairSubPoly (reducingExpectedPoly wires extension i s.accumulator) next)⟩

noncomputable def runReducingPoly (wires : List P) (count : Nat) (extension : Bool) :
    Nat → Nat → ReducingPolyState → ReducingPolyState
  | _,0,s => s
  | i,remaining+1,s => runReducingPoly wires count extension (i+1) remaining
      (reducingStepPoly wires count extension i s)

noncomputable def reducingPolys (wires : List P) (count : Nat) (extension : Bool) : List P :=
  (runReducingPoly wires count extension 0 count ⟨pairRead wires 4,[]⟩).output

theorem reducing_coefficient_actual (wires : List P) (extension : Bool) (i : Nat) (x : Element) :
    pairValue (reducingCoefficientPoly wires extension i) x =
      GatesAdditional.reducingCoefficient (columnValues wires x) extension i := by
  cases extension
  · simp only [reducingCoefficientPoly,GatesAdditional.reducingCoefficient,
      Bool.false_eq_true,↓reduceIte,pairValue,read_poly_is_actual_read,value_zero]
  · exact pair_read_exact _ _ _

theorem reducing_next_actual (wires : List P) (count : Nat) (extension : Bool) (i : Nat) (x : Element) :
    pairValue (reducingNextPoly wires count extension i) x =
      GatesAdditional.reducingNext (columnValues wires x) count extension i := by
  unfold reducingNextPoly GatesAdditional.reducingNext
  split <;> exact pair_read_exact _ _ _

theorem reducing_expected_actual (wires : List P) (extension : Bool) (i : Nat)
    (previous : PairPoly) (x : Element) :
    pairValue (reducingExpectedPoly wires extension i previous) x =
      GatesAdditional.reducingExpected (columnValues wires x) extension i (pairValue previous x) := by
  simp only [reducingExpectedPoly,pair_add_actual,pair_mul_exact,pair_read_exact,
    reducing_coefficient_actual,GatesAdditional.reducingExpected]

theorem reducing_step_actual (wires : List P) (count : Nat) (extension : Bool) (i : Nat)
    (s : ReducingPolyState) (x : Element) :
    reducingStateValue (reducingStepPoly wires count extension i s) x =
      GatesAdditional.reducingStep (columnValues wires x) count extension i (reducingStateValue s x) := by
  have append_values (a b : List P) : columnValues (a++b) x = columnValues a x ++ columnValues b x :=
    List.map_append _ _ _
  simp only [reducingStateValue,reducingStepPoly,GatesAdditional.reducingStep,
    append_values,pair_polys_actual,pair_sub_actual,reducing_next_actual,reducing_expected_actual]

theorem reducing_run_actual (wires : List P) (count : Nat) (extension : Bool) (i remaining : Nat)
    (s : ReducingPolyState) (x : Element) :
    reducingStateValue (runReducingPoly wires count extension i remaining s) x =
      GatesAdditional.runReducing (columnValues wires x) count extension i remaining (reducingStateValue s x) := by
  induction remaining generalizing i s with
  | zero => rfl
  | succ remaining ih => rw [runReducingPoly,ih,reducing_step_actual,GatesAdditional.runReducing]

theorem reducing_list_actual (wires : List P) (count : Nat) (extension : Bool) (x : Element) :
    columnValues (reducingPolys wires count extension) x =
      GatesAdditional.evalReducing (columnValues wires x) count extension := by
  have h := congrArg GatesAdditional.ReducingState.output
    (reducing_run_actual wires count extension 0 count ⟨pairRead wires 4,[]⟩ x)
  simpa only [reducingStateValue,pair_read_exact,columnValues,List.map_nil,reducingPolys,
    GatesAdditional.evalReducing] using h

theorem reducing_coefficient_degree (wires : List P) (extension : Bool) (i : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) : PairBound (reducingCoefficientPoly wires extension i) 1 := by
  cases extension
  · change (readPoly wires (6+i)).natDegree ≤ 1 ∧ (0 : P).natDegree ≤ 1
    exact ⟨read_poly_degree wires 1 _ hw,by simp⟩
  · exact pair_read_degree wires _ hw

theorem reducing_next_degree (wires : List P) (count : Nat) (extension : Bool) (i : Nat)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) : PairBound (reducingNextPoly wires count extension i) 1 := by
  unfold reducingNextPoly
  split <;> exact pair_read_degree wires _ hw

theorem reducing_expected_degree (wires : List P) (extension : Bool) (i : Nat) (previous : PairPoly)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hp : PairBound previous 1) :
    PairBound (reducingExpectedPoly wires extension i previous) 2 :=
  pair_add_degree _ _ 2 1 (pair_mul_degree _ _ hp (pair_read_degree wires 2 hw))
    (reducing_coefficient_degree wires extension i hw)

/-- The actual assignment, not assumed satisfaction, resets the degree-one
accumulator. All emitted constraints stay degree two at arbitrary loop length. -/
theorem reducing_step_degree (wires : List P) (count : Nat) (extension : Bool) (i : Nat)
    (s : ReducingPolyState) (hw : ∀ p ∈ wires, p.natDegree ≤ 1)
    (ha : PairBound s.accumulator 1) (ho : ∀ p ∈ s.output, p.natDegree ≤ 2) :
    PairBound (reducingStepPoly wires count extension i s).accumulator 1 ∧
      ∀ p ∈ (reducingStepPoly wires count extension i s).output, p.natDegree ≤ 2 := by
  refine ⟨reducing_next_degree wires count extension i hw,?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ho p hp
  · exact pair_polys_degree _ 2 (pair_sub_degree _ _ 2 1
      (reducing_expected_degree wires extension i s.accumulator hw ha)
      (reducing_next_degree wires count extension i hw)) p hp

theorem reducing_run_degree (wires : List P) (count : Nat) (extension : Bool) (i remaining : Nat)
    (s : ReducingPolyState) (hw : ∀ p ∈ wires, p.natDegree ≤ 1)
    (ha : PairBound s.accumulator 1) (ho : ∀ p ∈ s.output, p.natDegree ≤ 2) :
    PairBound (runReducingPoly wires count extension i remaining s).accumulator 1 ∧
      ∀ p ∈ (runReducingPoly wires count extension i remaining s).output, p.natDegree ≤ 2 := by
  induction remaining generalizing i s with
  | zero => exact ⟨ha,ho⟩
  | succ remaining ih =>
      have h := reducing_step_degree wires count extension i s hw ha ho
      exact ih (i+1) (reducingStepPoly wires count extension i s) h.1 h.2

theorem reducing_list_degree (wires : List P) (count : Nat) (extension : Bool)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) :
    ∀ p ∈ reducingPolys wires count extension, p.natDegree ≤ 2 :=
  (reducing_run_degree wires count extension 0 count ⟨pairRead wires 4,[]⟩ hw
    (pair_read_degree wires 4 hw) (by simp)).2

end Audit.Wire3.GateLoopPolynomial
