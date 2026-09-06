import Audit.Wire3.GateTwelvePolynomial

/-!
ID 13: literal coset state/constraint polynomial bridge. The concrete subgroup
and weight tables from GatesAdditionalCoset are used in their original order.
Chunk evaluation uses OLD product. The initial chunk starts at E=0,P=1;
subsequent chunks install claimed E/P wires regardless of constraint truth.
These assignments, not satisfaction assumptions, give the degree bound D.
The exact equalities target existing executable audit functions; source/Yul,
ABI/uint refinement, interpolation truth, MLE provenance and PCS remain open.
Source: CosetInterpolationGateExt3.sol:50-136; gate_ext3.rs:1031-1101.
-/
namespace Audit.Wire3.GateCosetPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateBasicPolynomial
open Audit.Wire3.GateLoopPolynomial Polynomial

noncomputable def pairScalarPoly (a : PairPoly) (s : P) : PairPoly := ⟨a.c0*s,a.c1*s⟩
noncomputable def pairBasePoly (n : Nat) : PairPoly := ⟨C (n : Element),0⟩
noncomputable def pairZeroPoly : PairPoly := ⟨0,0⟩
noncomputable def pairOnePoly : PairPoly := ⟨1,0⟩

theorem pair_scalar_actual (a : PairPoly) (s : P) (x : Element) :
    pairValue (pairScalarPoly a s) x = GatesAdditionalCoset.pairScalar (pairValue a x) (value s x) := by
  simp only [pairScalarPoly,pairValue,GatesAdditionalCoset.pairScalar,value_mul]
theorem pair_base_actual (n : Nat) (x : Element) :
    pairValue (pairBasePoly n) x = ⟨Gates.embed n,Verifier.zero⟩ := by
  simp only [pairBasePoly,pairValue,value_nat_constant,value_zero]
theorem pair_zero_actual (x : Element) : pairValue pairZeroPoly x = GatesAdditionalCoset.pairZero := by
  simp only [pairZeroPoly,pairValue,value_zero,GatesAdditionalCoset.pairZero]
theorem pair_one_actual (x : Element) : pairValue pairOnePoly x = GatesAdditionalCoset.pairOne := by
  simp only [pairOnePoly,pairValue,value_one,value_zero,GatesAdditionalCoset.pairOne]

theorem pair_bound_mono (a : PairPoly) (lo hi : Nat) (h : PairBound a lo) (hle : lo ≤ hi) : PairBound a hi :=
  ⟨h.1.trans hle,h.2.trans hle⟩
theorem pair_mul_degrees (a b : PairPoly) (da db : Nat) (ha : PairBound a da) (hb : PairBound b db) :
    PairBound (pairMul a b) (da+db) := by
  have h00 := mul_degree_bound _ _ da db ha.1 hb.1
  have h11 := mul_degree_bound _ _ da db ha.2 hb.2
  have h7 := mul_degree_bound _ (C (7 : Element)) (da+db) 0 h11 (le_of_eq (natDegree_C _))
  constructor
  · exact (add_degree_bound _ _ (da+db) (da+db) h00 (by simpa only [Nat.add_zero] using h7)).trans (by omega)
  · exact (add_degree_bound _ _ (da+db) (da+db) (mul_degree_bound _ _ da db ha.1 hb.2)
      (mul_degree_bound _ _ da db ha.2 hb.1)).trans (by omega)
theorem pair_scalar_degree (a : PairPoly) (s : P) (da ds : Nat) (ha : PairBound a da) (hs : s.natDegree ≤ ds) :
    PairBound (pairScalarPoly a s) (da+ds) :=
  ⟨mul_degree_bound _ _ da ds ha.1 hs,mul_degree_bound _ _ da ds ha.2 hs⟩
theorem pair_base_degree (n : Nat) : PairBound (pairBasePoly n) 0 := by
  constructor <;> simp [pairBasePoly]

structure State where
  evaluation : PairPoly
  product : PairPoly
  point : PairPoly

def stateValue (s : State) (x : Element) : GatesAdditionalCoset.State :=
  ⟨pairValue s.evaluation x,pairValue s.product x,pairValue s.point x⟩

noncomputable def chunkStep (wires : List P) (bits index : Nat) (s : State) : State :=
  let term := pairSubPoly s.point (pairBasePoly ((GatesAdditionalCoset.subgroupTable bits).getD index 0))
  let weighted := pairScalarPoly (pairRead wires (1+2*index))
    (C ((GatesAdditionalCoset.weightTable bits).getD index 0 : Element))
  ⟨pairAddPoly (pairMul s.evaluation term) (pairMul weighted s.product),pairMul s.product term,s.point⟩

noncomputable def runChunk (wires : List P) (bits : Nat) : Nat → Nat → State → State
  | _,0,s => s
  | index,count+1,s => runChunk wires bits (index+1) count (chunkStep wires bits index s)

theorem chunk_step_actual (wires : List P) (bits index : Nat) (s : State) (x : Element) :
    stateValue (chunkStep wires bits index s) x =
      GatesAdditionalCoset.chunkStep (columnValues wires x) bits index (stateValue s x) := by
  simp only [stateValue,chunkStep,GatesAdditionalCoset.chunkStep,pair_add_actual,pair_mul_exact,
    pair_sub_actual,pair_base_actual,pair_scalar_actual,pair_read_exact,value_nat_constant]

theorem run_chunk_actual (wires : List P) (bits start count : Nat) (s : State) (x : Element) :
    stateValue (runChunk wires bits start count s) x =
      GatesAdditionalCoset.runChunk (columnValues wires x) bits start count (stateValue s x) := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih => rw [runChunk,ih,chunk_step_actual,GatesAdditionalCoset.runChunk]

def StateBound (s : State) (bound : Nat) : Prop :=
  PairBound s.evaluation bound ∧ PairBound s.product bound ∧ PairBound s.point 1

theorem chunk_step_degree (wires : List P) (bits index bound : Nat) (s : State)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hs : StateBound s bound) :
    StateBound (chunkStep wires bits index s) (bound+1) := by
  have ht := pair_sub_degree s.point
    (pairBasePoly ((GatesAdditionalCoset.subgroupTable bits).getD index 0)) 1 0 hs.2.2 (pair_base_degree _)
  have hv := pair_scalar_degree (pairRead wires (1+2*index))
    (C ((GatesAdditionalCoset.weightTable bits).getD index 0 : Element)) 1 0
    (pair_read_degree wires _ hw) (le_of_eq (natDegree_C _))
  have he := pair_mul_degrees _ _ bound 1 hs.1 ht
  have hp := pair_mul_degrees _ _ bound 1 hs.2.1 ht
  have hm := pair_mul_degrees _ _ 1 bound hv hs.2.1
  refine ⟨?_,hp,hs.2.2⟩
  exact pair_bound_mono _ _ _ (pair_add_degree _ _ (bound+1) (1+bound) he hm) (by omega)

theorem run_chunk_degree (wires : List P) (bits start count bound : Nat) (s : State)
    (hw : ∀ p ∈ wires, p.natDegree ≤ 1) (hs : StateBound s bound) :
    StateBound (runChunk wires bits start count s) (bound+count) := by
  induction count generalizing start bound s with
  | zero => simpa only [Nat.add_zero,runChunk] using hs
  | succ count ih =>
      have h := ih (start+1) (bound+1) (chunkStep wires bits start s) (chunk_step_degree wires bits start bound s hw hs)
      simpa only [runChunk,Nat.add_assoc,Nat.add_comm 1] using h

theorem state_bound_mono (s : State) (lo hi : Nat) (h : StateBound s lo) (hle : lo ≤ hi) : StateBound s hi :=
  ⟨pair_bound_mono _ _ _ h.1 hle,pair_bound_mono _ _ _ h.2.1 hle,h.2.2⟩

structure Progress where
  state : State
  constraints : List P

def progressValue (p : Progress) (x : Element) : GatesAdditionalCoset.Progress :=
  ⟨stateValue p.state x,columnValues p.constraints x⟩

noncomputable def intermediateStep (wires : List P) (bits degree i : Nat) (p : Progress) : Progress :=
  let evaluation := pairRead wires (GatesAdditionalCoset.intermediateStart bits+2*i)
  let product := pairRead wires (GatesAdditionalCoset.intermediateStart bits+
    2*GatesAdditionalCoset.intermediates bits degree+2*i)
  let out := p.constraints ++ pairPolys (pairSubPoly evaluation p.state.evaluation) ++
    pairPolys (pairSubPoly product p.state.product)
  let installed : State := ⟨evaluation,product,p.state.point⟩
  ⟨runChunk wires bits (GatesAdditionalCoset.nextChunkStart degree i)
    (GatesAdditionalCoset.nextChunkCount bits degree i) installed,out⟩

noncomputable def runIntermediates (wires : List P) (bits degree : Nat) : Nat → Nat → Progress → Progress
  | _,0,p => p
  | i,count+1,p => runIntermediates wires bits degree (i+1) count (intermediateStep wires bits degree i p)

theorem column_values_append (a b : List P) (x : Element) :
    columnValues (a++b) x = columnValues a x ++ columnValues b x := List.map_append _ _ _

theorem intermediate_step_actual (wires : List P) (bits degree i : Nat) (p : Progress) (x : Element) :
    progressValue (intermediateStep wires bits degree i p) x =
      GatesAdditionalCoset.intermediateStep (columnValues wires x) bits degree i (progressValue p x) := by
  simp only [progressValue,intermediateStep,GatesAdditionalCoset.intermediateStep]
  rw [run_chunk_actual]
  simp only [column_values_append,pair_polys_actual,pair_sub_actual,pair_read_exact,stateValue]

theorem run_intermediates_actual (wires : List P) (bits degree start count : Nat) (p : Progress) (x : Element) :
    progressValue (runIntermediates wires bits degree start count p) x =
      GatesAdditionalCoset.runIntermediates (columnValues wires x) bits degree start count (progressValue p x) := by
  induction count generalizing start p with
  | zero => rfl
  | succ count ih => rw [runIntermediates,ih,intermediate_step_actual,GatesAdditionalCoset.runIntermediates]

def ProgressBound (p : Progress) (bound : Nat) : Prop :=
  StateBound p.state bound ∧ ∀ q ∈ p.constraints, q.natDegree ≤ bound

theorem next_chunk_count_bound (bits degree i : Nat) (hd : 1 ≤ degree) :
    GatesAdditionalCoset.nextChunkCount bits degree i ≤ degree-1 := by
  unfold GatesAdditionalCoset.nextChunkCount
  omega

theorem intermediate_step_degree (wires : List P) (bits degree i : Nat) (p : Progress)
    (hw : ∀ q ∈ wires, q.natDegree ≤ 1) (hd : 2 ≤ degree) (hp : ProgressBound p degree) :
    ProgressBound (intermediateStep wires bits degree i p) degree := by
  have he := pair_read_degree wires (GatesAdditionalCoset.intermediateStart bits+2*i) hw
  have hprod := pair_read_degree wires (GatesAdditionalCoset.intermediateStart bits+
    2*GatesAdditionalCoset.intermediates bits degree+2*i) hw
  have hinit : StateBound ⟨_,_,p.state.point⟩ 1 := ⟨he,hprod,hp.1.2.2⟩
  have hrun := run_chunk_degree wires bits (GatesAdditionalCoset.nextChunkStart degree i)
    (GatesAdditionalCoset.nextChunkCount bits degree i) 1 _ hw hinit
  refine ⟨state_bound_mono _ _ _ hrun (by have := next_chunk_count_bound bits degree i (by omega); omega),?_⟩
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · exact hp.2 q hq
    · exact pair_polys_degree _ degree (pair_bound_mono _ _ _
        (pair_sub_degree _ _ 1 degree he hp.1.1) (by omega)) q hq
  · exact pair_polys_degree _ degree (pair_bound_mono _ _ _
      (pair_sub_degree _ _ 1 degree hprod hp.1.2.1) (by omega)) q hq

theorem run_intermediates_degree (wires : List P) (bits degree start count : Nat) (p : Progress)
    (hw : ∀ q ∈ wires, q.natDegree ≤ 1) (hd : 2 ≤ degree) (hp : ProgressBound p degree) :
    ProgressBound (runIntermediates wires bits degree start count p) degree := by
  induction count generalizing start p with
  | zero => exact hp
  | succ _ ih =>
      exact ih (start+1) (intermediateStep wires bits degree start p)
        (intermediate_step_degree wires bits degree start p hw hd hp)

noncomputable def initialProgress (wires : List P) (bits degree : Nat) : Progress :=
  let evaluationPoint := pairRead wires (1+2*GatesAdditionalCoset.points bits)
  let shifted := pairRead wires (GatesAdditionalCoset.shiftedPointIndex bits degree)
  ⟨runChunk wires bits 0 degree ⟨pairZeroPoly,pairOnePoly,shifted⟩,
    pairPolys (pairSubPoly evaluationPoint (pairScalarPoly shifted (readPoly wires 0)))⟩

noncomputable def cosetPolys (wires : List P) (bits degree : Nat) : List P :=
  let result := runIntermediates wires bits degree 0 (GatesAdditionalCoset.intermediates bits degree)
    (initialProgress wires bits degree)
  result.constraints ++ pairPolys
    (pairSubPoly (pairRead wires (1+2*(GatesAdditionalCoset.points bits+1))) result.state.evaluation)

theorem initial_progress_actual (wires : List P) (bits degree : Nat) (x : Element) :
    progressValue (initialProgress wires bits degree) x =
      ⟨GatesAdditionalCoset.runChunk (columnValues wires x) bits 0 degree
        ⟨GatesAdditionalCoset.pairZero,GatesAdditionalCoset.pairOne,
          Gates.readExt2 (columnValues wires x) (GatesAdditionalCoset.shiftedPointIndex bits degree)⟩,
       GatesAdditionalCoset.pairValues (GatesAdditionalCoset.pairSub
         (Gates.readExt2 (columnValues wires x) (1+2*GatesAdditionalCoset.points bits))
         (GatesAdditionalCoset.pairScalar
           (Gates.readExt2 (columnValues wires x) (GatesAdditionalCoset.shiftedPointIndex bits degree))
           (Gates.readValue (columnValues wires x) 0)))⟩ := by
  simp only [progressValue,initialProgress]
  rw [run_chunk_actual]
  simp only [stateValue,pair_zero_actual,pair_one_actual,pair_polys_actual,pair_sub_actual,
    pair_scalar_actual,pair_read_exact,read_poly_is_actual_read]

theorem coset_actual (wires : List P) (bits degree : Nat) (x : Element) :
    columnValues (cosetPolys wires bits degree) x =
      GatesAdditionalCoset.evaluateUnchecked (columnValues wires x) bits degree := by
  have h := run_intermediates_actual wires bits degree 0 (GatesAdditionalCoset.intermediates bits degree)
    (initialProgress wires bits degree) x
  rw [initial_progress_actual] at h
  have hc := congrArg GatesAdditionalCoset.Progress.constraints h
  have he := congrArg (fun p : GatesAdditionalCoset.Progress => p.state.evaluation) h
  simp only [progressValue,stateValue] at hc he
  simp only [cosetPolys,column_values_append,pair_polys_actual,pair_sub_actual,pair_read_exact,
    GatesAdditionalCoset.evaluateUnchecked,hc,he]

theorem coset_constraint_count (wires : List P) (bits degree : Nat) :
    (cosetPolys wires bits degree).length = GatesAdditionalCoset.constraintCount bits degree := by
  have h := congrArg List.length (coset_actual wires bits degree (0 : Element))
  simpa only [column_values_preserve_length,GatesAdditionalCoset.output_length] using h

theorem initial_progress_degree (wires : List P) (bits degree : Nat)
    (hw : ∀ q ∈ wires, q.natDegree ≤ 1) (hd : 2 ≤ degree) :
    ProgressBound (initialProgress wires bits degree) degree := by
  have hs := pair_read_degree wires (GatesAdditionalCoset.shiftedPointIndex bits degree) hw
  have hzero : PairBound pairZeroPoly 0 := by constructor <;> simp [pairZeroPoly]
  have hone : PairBound pairOnePoly 0 := by constructor <;> simp [pairOnePoly]
  have hi : StateBound ⟨pairZeroPoly,pairOnePoly,pairRead wires (GatesAdditionalCoset.shiftedPointIndex bits degree)⟩ 0 :=
    ⟨hzero,hone,hs⟩
  have hr := run_chunk_degree wires bits 0 degree 0 _ hw hi
  refine ⟨by simpa only [Nat.zero_add] using hr,?_⟩
  exact pair_polys_degree _ degree (pair_bound_mono _ _ _ (pair_sub_degree _ _ 1 2
    (pair_read_degree wires _ hw) (pair_scalar_degree _ _ 1 1 hs (read_poly_degree wires 1 0 hw))) (by omega))

theorem coset_degree (wires : List P) (bits degree : Nat)
    (hw : ∀ q ∈ wires, q.natDegree ≤ 1) (hd : 2 ≤ degree) :
    ∀ q ∈ cosetPolys wires bits degree, q.natDegree ≤ degree := by
  have hp := run_intermediates_degree wires bits degree 0 (GatesAdditionalCoset.intermediates bits degree)
    (initialProgress wires bits degree) hw hd (initial_progress_degree wires bits degree hw hd)
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hp.2 q hq
  · exact pair_polys_degree _ degree (pair_bound_mono _ _ _ (pair_sub_degree _ _ 1 degree
      (pair_read_degree wires _ hw) hp.1.1) (by omega)) q hq

end Audit.Wire3.GateCosetPolynomial
