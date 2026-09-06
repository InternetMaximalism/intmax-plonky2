import Audit.Wire3.GoldilocksExt3Field
import Audit.Wire3.Packed
import Audit.Wire3.NormPolynomial

/-!
Indexed adjacent-pair binding from mle/src/sumcheck/ext3.rs:47-68.
Each RHS is read from the CURRENT buffer before its indexed write; truncation
occurs only after the half-length loop. Validity is the original power-of-two
table invariant, not an extra source runtime check. Low-level zero-totalized
reads are used only with separately proved bounds.
This is a manual functional array model, not Rust compiler/memory refinement.
-/ 
namespace Audit.Wire3.DenseMleIndexed
open Audit.Wire3 GoldilocksExt3Field

def blend (left right challenge : Element) : Element :=
  (1-challenge)*left+challenge*right

theorem blend_equals_line (left right challenge : Element) :
    blend left right challenge = left+challenge*(right-left) := by
  unfold blend
  ring

def step (challenge : Element) (i : Nat) (buffer : List Element) : List Element :=
  buffer.set i (blend (buffer.getD (2*i) 0) (buffer.getD (2*i+1) 0) challenge)

def run (challenge : Element) : Nat → Nat → List Element → List Element
  | _,0,buffer => buffer
  | i,n+1,buffer => run challenge (i+1) n (step challenge i buffer)

def line (original : List Element) (challenge : Element) (i : Nat) : Element :=
  blend (original.getD (2*i) 0) (original.getD (2*i+1) 0) challenge

def Invariant (original buffer : List Element) (challenge : Element) (i : Nat) : Prop :=
  buffer.length = original.length ∧
  (∀ j, j < i → buffer.getD j 0 = line original challenge j) ∧
  (∀ j, i ≤ j → buffer.getD j 0 = original.getD j 0)

theorem start_invariant (original : List Element) (challenge : Element) :
    Invariant original original challenge 0 := ⟨rfl,by omega,by intros; rfl⟩

theorem set_same (buffer : List Element) (i : Nat) (value : Element) (hi : i < buffer.length) :
    (buffer.set i value).getD i 0 = value := by
  simp [List.getElem?_set_eq (by simpa using hi)]

theorem set_other (buffer : List Element) (i j : Nat) (value : Element) (h : i ≠ j) :
    (buffer.set i value).getD j 0 = buffer.getD j 0 := by
  simp [List.getElem?_set_ne h]

theorem step_reads_original (original buffer : List Element) (challenge : Element) (i : Nat)
    (h : Invariant original buffer challenge i) :
    buffer.getD (2*i) 0 = original.getD (2*i) 0 ∧
    buffer.getD (2*i+1) 0 = original.getD (2*i+1) 0 :=
  ⟨h.2.2 _ (by omega),h.2.2 _ (by omega)⟩

theorem step_accesses_in_bounds (original buffer : List Element) (challenge : Element) (i half : Nat)
    (h : Invariant original buffer challenge i) (hlen : original.length = 2*half) (hi : i < half) :
    i < buffer.length ∧ 2*i < buffer.length ∧ 2*i+1 < buffer.length := by
  rw [h.1,hlen]
  omega

theorem step_preserves_invariant (original buffer : List Element) (challenge : Element) (i : Nat)
    (h : Invariant original buffer challenge i) (hi : i < original.length) :
    Invariant original (step challenge i buffer) challenge (i+1) := by
  have reads := step_reads_original original buffer challenge i h
  have hs : step challenge i buffer = buffer.set i (line original challenge i) := by
    simp only [step,reads.1,reads.2,line]
  rw [hs]
  refine ⟨by simp [h.1],?_,?_⟩
  · intro j hj
    by_cases he : i = j
    · subst j
      exact set_same buffer i _ (by rw [h.1]; exact hi)
    · rw [set_other buffer i j _ he]
      exact h.2.1 j (by omega)
  · intro j hj
    rw [set_other buffer i j _ (by omega)]
    exact h.2.2 j (by omega)

theorem run_preserves_invariant (original buffer : List Element) (challenge : Element) (i remaining : Nat)
    (h : Invariant original buffer challenge i) (hcap : i+remaining ≤ original.length) :
    Invariant original (run challenge i remaining buffer) challenge (i+remaining) := by
  induction remaining generalizing i buffer with
  | zero => simpa [run] using h
  | succ n ih =>
      have hs := step_preserves_invariant original buffer challenge i h (by omega)
      simpa only [run,Nat.add_assoc,Nat.add_comm 1 n] using
        ih (step challenge i buffer) (i+1) hs (by omega)

def bindBuffer (original : List Element) (challenge : Element) : List Element :=
  (run challenge 0 (original.length/2) original).take (original.length/2)

theorem bind_buffer_length (original : List Element) (challenge : Element) :
    (bindBuffer original challenge).length = original.length/2 := by
  have h := run_preserves_invariant original original challenge 0 (original.length/2)
    (start_invariant original challenge) (by omega)
  simp only [bindBuffer,List.length_take,h.1]
  exact Nat.min_eq_left (Nat.div_le_self _ _)

theorem bind_buffer_reads_exact_line (original : List Element) (challenge : Element)
    (j : Nat) (hj : j < original.length/2) :
    (bindBuffer original challenge).getD j 0 = line original challenge j := by
  have h := run_preserves_invariant original original challenge 0 (original.length/2)
    (start_invariant original challenge) (by omega)
  have ht : (bindBuffer original challenge).getD j 0 =
      (run challenge 0 (original.length/2) original).getD j 0 := by
    simp [bindBuffer,List.getElem?_take,hj]
  exact ht.trans (h.2.1 j (by omega))

def raw (xs : List Element) : List Arithmetic.Ext3 :=
  xs.map (fun x => x.toVerifier.val)

theorem raw_getD (xs : List Element) (i : Nat) :
    (raw xs).getD i Arithmetic.zero = (xs.getD i 0).toVerifier.val := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [raw,List.map_cons,List.getD_cons_succ] using ih i

theorem blend_is_packed_butterfly (left right challenge : Element) :
    (blend left right challenge).toVerifier.val =
      Arithmetic.butterfly left.toVerifier.val right.toVerifier.val challenge.toVerifier.val := by
  rw [blend_equals_line]
  rfl

theorem binding_is_same_packed_layer (original : List Element) (challenge : Element)
    (half : Nat) (hlen : original.length = 2*half) :
    raw (bindBuffer original challenge) = Packed.layer challenge.toVerifier.val (raw original) := by
  have hl : (raw (bindBuffer original challenge)).length = half := by
    simp only [raw,List.length_map,bind_buffer_length,hlen]
    omega
  have hr : (Packed.layer challenge.toVerifier.val (raw original)).length = half :=
    Packed.layer_even_shape _ _ half (by simpa only [raw,List.length_map] using hlen)
  apply List.ext_get (hl.trans hr.symm)
  intro j hj hk
  have hjhalf : j < original.length/2 := by
    have : j < half := by omega
    rw [hlen]
    omega
  have hd : (raw (bindBuffer original challenge)).getD j Arithmetic.zero =
      (Packed.layer challenge.toVerifier.val (raw original)).getD j Arithmetic.zero := by
    rw [raw_getD,bind_buffer_reads_exact_line original challenge j hjhalf]
    change (line original challenge j).toVerifier.val =
      Packed.lookup (Packed.layer challenge.toVerifier.val (raw original)) j
    rw [Packed.layer_lookup]
    simp only [Packed.tableLayer,Packed.lookup,raw_getD,line,blend_is_packed_butterfly]
  simpa only [List.getD_eq_get _ _ hj,List.getD_eq_get _ _ hk] using hd

def endpoints (original : List Element) (i : Nat) : NormPolynomial.Line :=
  ⟨original.getD (2*i) 0,original.getD (2*i+1) 0⟩

theorem line_is_same_affine_polynomial (original : List Element) (i : Nat) (challenge : Element) :
    line original challenge i = (NormPolynomial.affine (endpoints original i)).eval challenge := by
  rw [NormPolynomial.affine_evaluation]
  exact blend_equals_line _ _ _

theorem bound_cell_is_same_affine_polynomial (original : List Element) (i : Nat) (challenge : Element)
    (hi : i < original.length/2) :
    (bindBuffer original challenge).getD i 0 =
      (NormPolynomial.affine (endpoints original i)).eval challenge := by
  rw [bind_buffer_reads_exact_line original challenge i hi,line_is_same_affine_polynomial]

structure State where
  numVars : Nat
  evaluations : List Element

def Valid (s : State) : Prop := s.evaluations.length = 2^s.numVars

/-- Exactly the source num_vars assertion; validity is a caller invariant,
not a new length check that could hide malformed source execution. -/
def bindVariable (s : State) (challenge : Element) : Option State :=
  if s.numVars = 0 then none else
    some ⟨s.numVars-1,bindBuffer s.evaluations challenge⟩

theorem constant_binding_fails (s : State) (challenge : Element) (h : s.numVars = 0) :
    bindVariable s challenge = none := by simp [bindVariable,h]

theorem positive_binding_exact (s : State) (challenge : Element) (h : 0 < s.numVars) :
    bindVariable s challenge = some ⟨s.numVars-1,bindBuffer s.evaluations challenge⟩ := by
  simp [bindVariable,show s.numVars ≠ 0 by omega]

theorem binding_retains_power_two_shape (s : State) (challenge : Element)
    (hv : Valid s) (hn : 0 < s.numVars) :
    Valid ⟨s.numVars-1,bindBuffer s.evaluations challenge⟩ := by
  change (bindBuffer s.evaluations challenge).length = 2^(s.numVars-1)
  rw [bind_buffer_length,hv]
  obtain ⟨n,hnum⟩ := Nat.exists_eq_succ_of_ne_zero (show s.numVars ≠ 0 by omega)
  simp [hnum,Nat.pow_succ]

theorem valid_each_iteration_reads_in_bounds (s : State) (challenge : Element) (i : Nat)
    (hv : Valid s) (hn : 0 < s.numVars) (hi : i < s.evaluations.length/2) :
    let buffer := run challenge 0 i s.evaluations
    2*i < buffer.length ∧ 2*i+1 < buffer.length ∧
      buffer.getD (2*i) 0 = s.evaluations.getD (2*i) 0 ∧
      buffer.getD (2*i+1) 0 = s.evaluations.getD (2*i+1) 0 := by
  have h := run_preserves_invariant s.evaluations s.evaluations challenge 0 i
    (start_invariant _ _) (by omega)
  simp only [Nat.zero_add] at h
  have hh : s.evaluations.length = 2*(s.evaluations.length/2) := by
    rw [hv]
    obtain ⟨n,hnum⟩ := Nat.exists_eq_succ_of_ne_zero (show s.numVars ≠ 0 by omega)
    simp [hnum,Nat.pow_succ,Nat.mul_comm]
  have bounds := step_accesses_in_bounds s.evaluations _ challenge i (s.evaluations.length/2) h hh hi
  have reads := step_reads_original s.evaluations _ challenge i h
  exact ⟨bounds.2.1,bounds.2.2,reads⟩

theorem successful_binding_shape_and_layer (s t : State) (challenge : Element)
    (hv : Valid s) (h : bindVariable s challenge = some t) :
    Valid t ∧ t.numVars+1=s.numVars ∧
      raw t.evaluations = Packed.layer challenge.toVerifier.val (raw s.evaluations) := by
  unfold bindVariable at h
  split at h
  · simp at h
  · rename_i hn
    cases h
    have hpos : 0 < s.numVars := by omega
    refine ⟨binding_retains_power_two_shape s challenge hv hpos,by dsimp; omega,?_⟩
    apply binding_is_same_packed_layer _ _ (s.evaluations.length/2)
    rw [hv]
    obtain ⟨n,hnum⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [hnum,Nat.pow_succ,Nat.mul_comm]

def bindMany : List Element → State → Option State
  | [],s => some s
  | r::rs,s => do
      let t ← bindVariable s r
      bindMany rs t

theorem all_bindings_execute (s : State) (point : List Element)
    (hv : Valid s) (hwidth : point.length ≤ s.numVars) :
    ∃ t, bindMany point s = some t ∧ Valid t ∧ t.numVars+point.length=s.numVars ∧
      raw t.evaluations = Packed.foldLayers (raw point) (raw s.evaluations) := by
  induction point generalizing s with
  | nil => exact ⟨s,rfl,hv,by simp,rfl⟩
  | cons r rs ih =>
      have hn : 0 < s.numVars := by simpa only [List.length_cons] using Nat.zero_lt_of_lt hwidth
      let next : State := ⟨s.numVars-1,bindBuffer s.evaluations r⟩
      have hb : bindVariable s r = some next := positive_binding_exact s r hn
      have hs := successful_binding_shape_and_layer s next r hv hb
      obtain ⟨t,ht,hvalid,hcount,hraw⟩ := ih next hs.1 (by
        have := hs.2.1
        simp only [List.length_cons] at hwidth
        omega)
      refine ⟨t,?_,hvalid,?_,?_⟩
      · simp only [bindMany,hb,bind,Option.bind,ht]
      · have := hs.2.1
        simp only [List.length_cons]
        omega
      · rw [hraw,hs.2.2]
        rfl

def evaluate (s : State) (point : List Element) : Option Element := do
  if point.length ≠ s.numVars then none else do
    let t ← bindMany point s
    t.evaluations[0]?

theorem evaluate_wrong_width_fails (s : State) (point : List Element)
    (h : point.length ≠ s.numVars) : evaluate s point = none := by simp [evaluate,h]

theorem evaluate_full_table_same_packed_fold (s : State) (point : List Element)
    (hv : Valid s) (hwidth : point.length=s.numVars) :
    ∃ result, evaluate s point = some result ∧
      result.toVerifier.val = Packed.fold (raw s.evaluations) (raw point) := by
  obtain ⟨t,ht,hvalid,hcount,hraw⟩ := all_bindings_execute s point hv (by omega)
  have hn : t.numVars=0 := by omega
  have hlen : t.evaluations.length=1 := by simpa [Valid,hn] using hvalid
  cases he : t.evaluations with
  | nil => simp [he] at hlen
  | cons value rest =>
      have hempty : rest=[] := by simpa [he] using hlen
      subst rest
      refine ⟨value,?_,?_⟩
      · simp [evaluate,hwidth,ht,he]
      · have := congrArg (fun xs : List Arithmetic.Ext3 => xs.getD 0 Arithmetic.zero) hraw
        simpa only [raw,he,List.map_cons,List.map_nil,List.getD_cons_zero,Packed.fold] using this

theorem zero_variable_table_evaluates_without_binding (value : Element) :
    evaluate ⟨0,[value]⟩ [] = some value := rfl

theorem ordinary_two_variable_example :
    evaluate ⟨2,[1,2,3,4]⟩ [0,1] = some (3 : Element) := by decide

end Audit.Wire3.DenseMleIndexed
