import Std
import Mathlib.Data.List.Perm

/-!
# Indexed WHIR quicksort execution: bounded proof checkpoint

The code follows SpongefishWhirVerify.sol:809-833 at becfe98e: middle pivot,
left scan then right scan, right j=0 break, simultaneous-read swap, i++,
post-swap j=0 break, j--, and recursive left range before recursive right.
List get?/set model checked array accesses and indexed overwrites. Fuel errors
belong to this mathematical runner, not to an added production proof guard.
Bounds failures model failed array reads, not accepted out-of-range defaults.

No other sort is substituted for this code. A valid midpoint-started partition
is proved total, preserves every element, and establishes the stated split
inequalities using maintained properties of actual cells. Successful full
recursive runs preserve every element. Whole-quicksort totality, sortedness,
and equality to reference insertionSort are supplied by the separate
consumer WhirQuicksortCorrectness; this module alone does not establish them. Solidity words,
memory, recursion gas, and Nat-to-uint256/source refinement are excluded.
-/
namespace Audit.Wire3.WhirQuicksort

inductive Failure where
  | scanFuel
  | partitionFuel
  | recursionFuel
  | readBounds (index : Nat)
deriving DecidableEq, Repr

@[simp] theorem except_ok_bind {α β : Type} (value : α) (f : α → Except Failure β) :
    ((Except.ok value : Except Failure α) >>= f) = f value := rfl

@[simp] theorem except_error_bind {α β : Type} (err : Failure) (f : α → Except Failure β) :
    ((Except.error err : Except Failure α) >>= f) = .error err := rfl

@[simp] theorem except_pure {α : Type} (value : α) : (pure value : Except Failure α) = .ok value := rfl

structure State where
  buffer : List Nat
  i : Nat
  j : Nat
deriving DecidableEq, Repr

def scanLeft (buffer : List Nat) (pivot : Nat) : Nat → Nat → Except Failure Nat
  | 0, _ => .error .scanFuel
  | fuel+1, i => match buffer[i]? with
    | none => .error (.readBounds i)
    | some value => if value < pivot then scanLeft buffer pivot fuel (i+1) else .ok i

def scanRight (buffer : List Nat) (pivot : Nat) : Nat → Nat → Except Failure Nat
  | 0, _ => .error .scanFuel
  | fuel+1, j => match buffer[j]? with
    | none => .error (.readBounds j)
    | some value => if pivot < value then
        if j = 0 then .ok j else scanRight buffer pivot fuel (j-1)
      else .ok j

/-- Both RHS reads precede both writes, including when i=j. -/
def swapCells (buffer : List Nat) (i j : Nat) : Except Failure (List Nat) :=
  match buffer[i]?, buffer[j]? with
  | some left, some right => .ok ((buffer.set i right).set j left)
  | none, _ => .error (.readBounds i)
  | _, none => .error (.readBounds j)

inductive Transition where
  | finished (state : State)
  | again (state : State)
deriving DecidableEq, Repr

def iteration (pivot scanFuel : Nat) (s : State) : Except Failure Transition := do
  let i ← scanLeft s.buffer pivot scanFuel s.i
  let j ← scanRight s.buffer pivot scanFuel s.j
  if i ≤ j then
    let buffer ← swapCells s.buffer i j
    let i := i+1
    if j = 0 then return .finished ⟨buffer,i,j⟩
    return .again ⟨buffer,i,j-1⟩
  else return .finished ⟨s.buffer,i,j⟩

def partition (pivot scanFuel : Nat) : Nat → State → Except Failure State
  | 0, s => if s.i ≤ s.j then .error .partitionFuel else .ok s
  | fuel+1, s => if s.i ≤ s.j then do
      match ← iteration pivot scanFuel s with
      | .finished result => return result
      | .again next => partition pivot scanFuel fuel next
    else .ok s

def quicksort : Nat → List Nat → Nat → Nat → Except Failure (List Nat)
  | 0, buffer, lo, hi => if hi ≤ lo then .ok buffer else .error .recursionFuel
  | fuel+1, buffer, lo, hi =>
      if hi ≤ lo then .ok buffer else do
      let pivot ← match buffer[(lo+hi)/2]? with
        | none => .error (.readBounds ((lo+hi)/2))
        | some value => .ok value
      let state ← partition pivot (buffer.length+1) (hi-lo+2) ⟨buffer,lo,hi⟩
      let buffer ← if lo < state.j then quicksort fuel state.buffer lo state.j else .ok state.buffer
      if state.i < hi then quicksort fuel buffer state.i hi else .ok buffer

theorem lookup_bounds (xs : List Nat) (index value : Nat) (h : xs[index]? = some value) :
    index < xs.length := (List.getElem?_eq_some.mp h).choose

theorem lookup_value (xs : List Nat) (index value : Nat) (h : xs[index]? = some value) :
    xs.getD index 0 = value := by simp [List.getD_eq_getElem?,h]

theorem lookup_self (xs : List Nat) (index : Nat) (h : index < xs.length) :
    xs[index]? = some (xs.getD index 0) := by
  simp [List.getElem?_eq_getElem h]

theorem scan_left_success (xs : List Nat) (pivot fuel start result : Nat)
    (h : scanLeft xs pivot fuel start = .ok result) :
    start ≤ result ∧ result < xs.length ∧ pivot ≤ xs.getD result 0 ∧
      ∀ index, start ≤ index → index < result → xs.getD index 0 < pivot := by
  induction fuel generalizing start result with
  | zero => simp [scanLeft] at h
  | succ fuel ih =>
      cases hg : xs[start]? with
      | none => simp [scanLeft,hg] at h
      | some value =>
          have hb := lookup_bounds xs start value hg
          have hv := lookup_value xs start value hg
          by_cases hp : value < pivot
          · have hh : scanLeft xs pivot fuel (start+1) = .ok result := by
              simpa [scanLeft,hg,hp] using h
            rcases ih (start+1) result hh with ⟨hr,hb',hv',hprefix⟩
            refine ⟨by omega,hb',hv',?_⟩
            intro index hi hj
            by_cases he : index = start
            · subst index; omega
            · exact hprefix index (by omega) hj
          · have he : start = result := by simpa [scanLeft,hg,hp] using h
            subst result
            exact ⟨Nat.le_refl _,hb,by omega,by intro index hi hj; omega⟩

theorem scan_right_success (xs : List Nat) (pivot fuel start result : Nat)
    (h : scanRight xs pivot fuel start = .ok result) :
    result ≤ start ∧ result < xs.length ∧ (xs.getD result 0 ≤ pivot ∨ result = 0) ∧
      ∀ index, result < index → index ≤ start → pivot < xs.getD index 0 := by
  induction fuel generalizing start result with
  | zero => simp [scanRight] at h
  | succ fuel ih =>
      cases hg : xs[start]? with
      | none => simp [scanRight,hg] at h
      | some value =>
          have hb := lookup_bounds xs start value hg
          have hv := lookup_value xs start value hg
          by_cases hp : pivot < value
          · by_cases hz : start = 0
            · have he : start = result := by
                simpa only [scanRight,hg,if_pos hp,if_pos hz,Except.ok.injEq] using h
              subst result
              exact ⟨Nat.le_refl _,hb,Or.inr hz,by intro index hi hj; omega⟩
            · have hh : scanRight xs pivot fuel (start-1) = .ok result := by
                simpa [scanRight,hg,hp,hz] using h
              rcases ih (start-1) result hh with ⟨hr,hb',hv',hsuffix⟩
              refine ⟨by omega,hb',hv',?_⟩
              intro index hi hj
              by_cases he : index = start
              · subst index; omega
              · exact hsuffix index hi (by omega)
          · have he : start = result := by simpa [scanRight,hg,hp] using h
            subst result
            exact ⟨Nat.le_refl _,hb,Or.inl (by omega),by intro index hi hj; omega⟩

/-- A real in-buffer sentinel proves the left scan cannot run past it. -/
theorem scan_left_has_sentinel (xs : List Nat) (pivot fuel start sentinel : Nat)
    (hs : start ≤ sentinel) (hb : sentinel < xs.length)
    (hp : pivot ≤ xs.getD sentinel 0) (hf : sentinel-start < fuel) :
    ∃ result, scanLeft xs pivot fuel start = .ok result ∧ result ≤ sentinel := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      have hstart : start < xs.length := by omega
      have hg := lookup_self xs start hstart
      by_cases hlt : xs.getD start 0 < pivot
      · have hs' : start+1 ≤ sentinel := by
          by_contra hh
          have he : start = sentinel := by omega
          subst sentinel; omega
        rcases ih (start+1) hs' (by omega) with ⟨result,hr,hbound⟩
        exact ⟨result,by simpa only [scanLeft,hg,if_pos hlt] using hr,hbound⟩
      · exact ⟨start,by simp only [scanLeft,hg,if_neg hlt],hs⟩

/-- A low sentinel likewise excludes the exceptional right-scan stop at zero
with a value above pivot. The result is at or above that sentinel. -/
theorem scan_right_has_sentinel (xs : List Nat) (pivot fuel start sentinel : Nat)
    (hs : sentinel ≤ start) (hb : start < xs.length)
    (hp : xs.getD sentinel 0 ≤ pivot) (hf : start-sentinel < fuel) :
    ∃ result, scanRight xs pivot fuel start = .ok result ∧ sentinel ≤ result ∧
      xs.getD result 0 ≤ pivot := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      have hg := lookup_self xs start hb
      by_cases hlt : pivot < xs.getD start 0
      · have hs' : sentinel ≤ start-1 := by
          by_contra hh
          have he : start = sentinel := by omega
          subst sentinel; omega
        have hz : start ≠ 0 := by
          intro hz; subst start
          have hsent : sentinel = 0 := by omega
          subst sentinel; omega
        rcases ih (start-1) hs' (by omega) (by omega) with ⟨result,hr,hbound,hvalue⟩
        exact ⟨result,by simpa only [scanRight,hg,if_pos hlt,if_neg hz] using hr,hbound,hvalue⟩
      · exact ⟨start,by simp only [scanRight,hg,if_neg hlt],hs,by omega⟩

theorem middle_pivot_bounds (lo hi : Nat) (h : lo ≤ hi) :
    lo ≤ (lo+hi)/2 ∧ (lo+hi)/2 ≤ hi := by omega

/-- No sentinel is assumed here: the source's actual middle pivot supplies
both first-iteration sentinels. It proves both scans succeed in their order. -/
theorem initial_scans_succeed (xs : List Nat) (lo hi : Nat) (hlo : lo ≤ hi)
    (hhi : hi < xs.length) :
    let pivot := xs.getD ((lo+hi)/2) 0
    ∃ left right,
      scanLeft xs pivot (xs.length+1) lo = .ok left ∧
      scanRight xs pivot (xs.length+1) hi = .ok right ∧
      lo ≤ left ∧ left ≤ (lo+hi)/2 ∧ (lo+hi)/2 ≤ right ∧ right ≤ hi ∧
      pivot ≤ xs.getD left 0 ∧ xs.getD right 0 ≤ pivot := by
  have hm := middle_pivot_bounds lo hi hlo
  have hb : (lo+hi)/2 < xs.length := by omega
  rcases scan_left_has_sentinel xs (xs.getD ((lo+hi)/2) 0) (xs.length+1) lo
      ((lo+hi)/2) hm.1 hb (Nat.le_refl _) (by omega) with ⟨left,hl,hlbound⟩
  rcases scan_right_has_sentinel xs (xs.getD ((lo+hi)/2) 0) (xs.length+1) hi
      ((lo+hi)/2) hm.2 hhi (Nat.le_refl _) (by omega) with ⟨right,hr,hrbound,hrvalue⟩
  have hleft := scan_left_success xs _ _ _ _ hl
  have hright := scan_right_success xs _ _ _ _ hr
  exact ⟨left,right,hl,hr,hleft.1,hlbound,hrbound,hright.1,hleft.2.2.1,hrvalue⟩

theorem head_set_perm (xs : List Nat) (index value : Nat) (h : index < xs.length) :
    List.Perm (xs.getD index 0 :: xs.set index value) (value :: xs) := by
  induction xs generalizing index with
  | nil => simp at h
  | cons x xs ih =>
      cases index with
      | zero => exact List.Perm.swap _ _ _
      | succ index =>
          have ht : index < xs.length := by simp only [List.length_cons] at h; omega
          change List.Perm (xs.getD index 0 :: x :: xs.set index value) (value :: x :: xs)
          exact (List.Perm.swap _ _ _).trans ((List.Perm.cons x (ih index ht)).trans
            (List.Perm.swap _ _ _))

theorem indexed_swap_perm (xs : List Nat) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) :
    List.Perm ((xs.set i (xs.getD j 0)).set j (xs.getD i 0)) xs := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact List.Perm.refl _
          | succ j =>
              have ht : j < xs.length := by simp only [List.length_cons] at hj; omega
              exact head_set_perm xs j x ht
      | succ i =>
          cases j with
          | zero =>
              have ht : i < xs.length := by simp only [List.length_cons] at hi; omega
              exact head_set_perm xs i x ht
          | succ j =>
              have hti : i < xs.length := by simp only [List.length_cons] at hi; omega
              have htj : j < xs.length := by simp only [List.length_cons] at hj; omega
              exact List.Perm.cons x (ih i j hti htj)

theorem swap_success_perm (xs result : List Nat) (i j : Nat)
    (h : swapCells xs i j = .ok result) : List.Perm result xs := by
  cases hl : xs[i]? with
  | none => simp [swapCells,hl] at h
  | some left =>
      cases hr : xs[j]? with
      | none => simp [swapCells,hl,hr] at h
      | some right =>
          have he : (xs.set i right).set j left = result := by simpa [swapCells,hl,hr] using h
          rw [← he,← lookup_value xs i left hl,← lookup_value xs j right hr]
          exact indexed_swap_perm xs i j (lookup_bounds xs i left hl) (lookup_bounds xs j right hr)

theorem swap_success_bounds (xs result : List Nat) (i j : Nat)
    (h : swapCells xs i j = .ok result) : i < xs.length ∧ j < xs.length := by
  cases hl : xs[i]? with
  | none => simp [swapCells,hl] at h
  | some left =>
      cases hr : xs[j]? with
      | none => simp [swapCells,hl,hr] at h
      | some right => exact ⟨lookup_bounds xs i left hl,lookup_bounds xs j right hr⟩

theorem getD_set_same (xs : List Nat) (index value : Nat) (h : index < xs.length) :
    (xs.set index value).getD index 0 = value := by
  simp [List.getElem?_set_eq (by simpa using h)]

theorem getD_set_other (xs : List Nat) (write read value : Nat) (h : write ≠ read) :
    (xs.set write value).getD read 0 = xs.getD read 0 := by
  simp [List.getElem?_set_ne h]

theorem overwrite_pair_values (xs : List Nat) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    let out := (xs.set i (xs.getD j 0)).set j (xs.getD i 0)
    out.getD i 0 = xs.getD j 0 ∧ out.getD j 0 = xs.getD i 0 := by
  dsimp
  constructor
  · by_cases he : i = j
    · subst j
      exact getD_set_same _ i _ (by simpa using hi)
    · rw [getD_set_other _ j i _ (Ne.symm he),getD_set_same xs i _ hi]
  · exact getD_set_same _ j _ (by simpa using hj)

theorem swap_in_bounds_executes (xs : List Nat) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    swapCells xs i j = .ok ((xs.set i (xs.getD j 0)).set j (xs.getD i 0)) := by
  simp only [swapCells,lookup_self xs i hi,lookup_self xs j hj]

def Transition.state : Transition → State
  | .finished s => s
  | .again s => s

def Transition.progress (start : Nat) : Transition → Prop
  | .finished s => s.j < s.i
  | .again s => start < s.i

theorem iteration_success_facts (pivot scanFuel : Nat) (s : State) (result : Transition)
    (h : iteration pivot scanFuel s = .ok result) :
    List.Perm result.state.buffer s.buffer ∧ s.i ≤ result.state.i ∧ result.state.j ≤ s.j ∧
      result.state.i ≤ s.buffer.length ∧ result.state.j < s.buffer.length ∧
      result.progress s.i := by
  cases hl : scanLeft s.buffer pivot scanFuel s.i with
  | error err => simp [iteration,hl] at h
  | ok left =>
      cases hr : scanRight s.buffer pivot scanFuel s.j with
      | error err => simp [iteration,hl,hr] at h
      | ok right =>
          have hleft := scan_left_success s.buffer pivot scanFuel s.i left hl
          have hright := scan_right_success s.buffer pivot scanFuel s.j right hr
          by_cases hcross : left ≤ right
          · cases hs : swapCells s.buffer left right with
            | error err => simp [iteration,hl,hr,hcross,hs] at h
            | ok buffer =>
                have hp := swap_success_perm s.buffer buffer left right hs
                by_cases hz : right = 0
                · have he : Transition.finished ⟨buffer,left+1,right⟩ = result := by
                    simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hs,if_pos hz,
                      except_pure,Except.ok.injEq] using h
                  subst result
                  exact ⟨hp,by simp only [Transition.state]; omega,by simp only [Transition.state]; omega,
                    by simp only [Transition.state]; omega,by simp only [Transition.state]; omega,
                    by simp only [Transition.progress]; omega⟩
                · have he : Transition.again ⟨buffer,left+1,right-1⟩ = result := by
                    simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hs,if_neg hz,
                      except_pure,Except.ok.injEq] using h
                  subst result
                  exact ⟨hp,by simp only [Transition.state]; omega,by simp only [Transition.state]; omega,
                    by simp only [Transition.state]; omega,by simp only [Transition.state]; omega,
                    by simp only [Transition.progress]; omega⟩
          · have he : Transition.finished ⟨s.buffer,left,right⟩ = result := by
              simpa only [iteration,hl,hr,except_ok_bind,if_neg hcross,
                except_pure,Except.ok.injEq] using h
            subst result
            exact ⟨List.Perm.refl _,by simp only [Transition.state]; omega,
              by simp only [Transition.state]; omega,by simp only [Transition.state]; omega,
              by simp only [Transition.state]; omega,by simp only [Transition.progress]; omega⟩

/-- Scan sentinels are properties of concrete buffer cells, not assumed
partition sortedness. After a swap the two written cells re-establish them. -/
def Sentinels (pivot hi : Nat) (s : State) : Prop :=
  hi < s.buffer.length ∧ s.i ≤ hi+1 ∧ s.j ≤ hi ∧
    (s.i ≤ s.j →
      (∃ upper, s.i ≤ upper ∧ upper ≤ hi ∧ pivot ≤ s.buffer.getD upper 0) ∧
      (∃ lower, lower ≤ s.j ∧ s.buffer.getD lower 0 ≤ pivot))

theorem initial_sentinels (xs : List Nat) (lo hi : Nat) (hlo : lo ≤ hi)
    (hhi : hi < xs.length) :
    Sentinels (xs.getD ((lo+hi)/2) 0) hi ⟨xs,lo,hi⟩ := by
  have hm := middle_pivot_bounds lo hi hlo
  refine ⟨hhi,by dsimp; omega,Nat.le_refl _,?_⟩
  intro _
  exact ⟨⟨(lo+hi)/2,hm.1,hm.2,Nat.le_refl _⟩,⟨(lo+hi)/2,hm.2,Nat.le_refl _⟩⟩

theorem iteration_total_preserves_sentinels (pivot scanFuel hi : Nat) (s : State)
    (hs : Sentinels pivot hi s) (hactive : s.i ≤ s.j) (hf : s.buffer.length < scanFuel) :
    ∃ result, iteration pivot scanFuel s = .ok result ∧ Sentinels pivot hi result.state := by
  rcases hs with ⟨hhi,_hib,hjb,hpair⟩
  rcases hpair hactive with ⟨⟨upper,hiu,huh,hpu⟩,⟨lower,hlj,hpl⟩⟩
  rcases scan_left_has_sentinel s.buffer pivot scanFuel s.i upper hiu (by omega) hpu
      (by omega) with ⟨left,hleft,hlupper⟩
  rcases scan_right_has_sentinel s.buffer pivot scanFuel s.j lower hlj (by omega) hpl
      (by omega) with ⟨right,hright,_hrlower,hrvalue⟩
  have hlf := scan_left_success s.buffer pivot scanFuel s.i left hleft
  have hrf := scan_right_success s.buffer pivot scanFuel s.j right hright
  by_cases hcross : left ≤ right
  · let out := (s.buffer.set left (s.buffer.getD right 0)).set right (s.buffer.getD left 0)
    have hswap : swapCells s.buffer left right = .ok out :=
      swap_in_bounds_executes s.buffer left right hlf.2.1 hrf.2.1
    have hvalues := overwrite_pair_values s.buffer left right hlf.2.1 hrf.2.1
    have houtlen : out.length = s.buffer.length := by simp [out]
    have hnext : Sentinels pivot hi ⟨out,left+1,right-1⟩ := by
      refine ⟨by dsimp; omega,by dsimp; omega,by dsimp; omega,?_⟩
      intro hn
      change left+1 ≤ right-1 at hn
      refine ⟨⟨right,by dsimp; omega,by omega,?_⟩,
        ⟨left,by dsimp; omega,?_⟩⟩
      · change pivot ≤ out.getD right 0
        rw [hvalues.2]
        exact hlf.2.2.1
      · change out.getD left 0 ≤ pivot
        rw [hvalues.1]
        exact hrvalue
    by_cases hz : right = 0
    · refine ⟨.finished ⟨out,left+1,right⟩,?_,?_⟩
      · simp only [iteration,hleft,hright,except_ok_bind,if_pos hcross,hswap,if_pos hz,except_pure]
      · simpa only [Transition.state,hz,Nat.zero_sub] using hnext
    · refine ⟨.again ⟨out,left+1,right-1⟩,?_,hnext⟩
      simp only [iteration,hleft,hright,except_ok_bind,if_pos hcross,hswap,if_neg hz,except_pure]
  · refine ⟨.finished ⟨s.buffer,left,right⟩,?_,?_⟩
    · simp only [iteration,hleft,hright,except_ok_bind,if_neg hcross,except_pure]
    · refine ⟨hhi,by change left ≤ hi+1; omega,by change right ≤ hi; omega,?_⟩
      intro hh
      change left ≤ right at hh
      exact False.elim (hcross hh)

/-- The full single partition terminates without any scan/bounds/fuel error.
The i-counter grows strictly on every recursive outer iteration, while its
upper bound is the fixed hi+1. Sentinels are re-established by actual writes. -/
theorem partition_total (pivot scanFuel fuel hi : Nat) (s : State)
    (hs : Sentinels pivot hi s) (hscan : s.buffer.length < scanFuel)
    (hf : s.i ≤ s.j → hi+1-s.i < fuel) :
    ∃ result, partition pivot scanFuel fuel s = .ok result := by
  induction fuel generalizing s with
  | zero =>
      have hc : ¬s.i ≤ s.j := by intro ha; have hh := hf ha; omega
      exact ⟨s,by simp [partition,hc]⟩
  | succ fuel ih =>
      by_cases hc : s.i ≤ s.j
      · rcases iteration_total_preserves_sentinels pivot scanFuel hi s hs hc hscan with
          ⟨next,hnext,hsnext⟩
        have hfacts := iteration_success_facts pivot scanFuel s next hnext
        cases next with
        | finished result =>
            exact ⟨result,by simp [partition,hc,hnext]⟩
        | again next =>
            change Sentinels pivot hi next at hsnext
            have hlen : next.buffer.length = s.buffer.length := hfacts.1.length_eq
            have hprogress : s.i < next.i := hfacts.2.2.2.2.2
            rcases ih next hsnext (by omega) (by
              intro hactiveNext
              have hjNext : next.j ≤ hi := hsnext.2.2.1
              have hiNext : next.i ≤ hi := Nat.le_trans hactiveNext hjNext
              have hbound : s.i ≤ hi+1 := hs.2.1
              have h := hf hc
              omega) with ⟨result,hr⟩
            exact ⟨result,by simpa [partition,hc,hnext] using hr⟩
      · exact ⟨s,by simp [partition,hc]⟩

theorem source_partition_total (xs : List Nat) (lo hi : Nat) (hlo : lo ≤ hi)
    (hhi : hi < xs.length) :
    ∃ result,
      partition (xs.getD ((lo+hi)/2) 0) (xs.length+1) (hi-lo+2) ⟨xs,lo,hi⟩ = .ok result := by
  exact partition_total _ _ _ hi _ (initial_sentinels xs lo hi hlo hhi)
    (by dsimp; omega) (by intro _; dsimp; omega)

/-- Already traversed cells on the left are at most the saved pivot;
already traversed cells on the right are at least it. These statements concern
the current overwritten buffer and are established from initially empty ranges. -/
def Classified (pivot lo hi : Nat) (s : State) : Prop :=
  lo ≤ s.i ∧ s.j ≤ hi ∧
  (∀ k, lo ≤ k → k < s.i → k ≤ hi → s.buffer.getD k 0 ≤ pivot) ∧
  (∀ k, lo ≤ k → s.j < k → k ≤ hi → pivot ≤ s.buffer.getD k 0)

theorem initial_classified (xs : List Nat) (pivot lo hi : Nat) :
    Classified pivot lo hi ⟨xs,lo,hi⟩ := by
  refine ⟨Nat.le_refl _,Nat.le_refl _,?_,?_⟩
  · intro k hk hlt _; change k < lo at hlt; omega
  · intro k _ hlt hk; change hi < k at hlt; omega

theorem crossed_scans_classified (pivot lo hi fuel : Nat) (s : State) (left right : Nat)
    (hc : Classified pivot lo hi s)
    (hl : scanLeft s.buffer pivot fuel s.i = .ok left)
    (hr : scanRight s.buffer pivot fuel s.j = .ok right) :
    Classified pivot lo hi ⟨s.buffer,left,right⟩ := by
  have hlf := scan_left_success s.buffer pivot fuel s.i left hl
  have hrf := scan_right_success s.buffer pivot fuel s.j right hr
  rcases hc with ⟨hlo,hhi,hprefix,hsuffix⟩
  refine ⟨by dsimp; omega,by dsimp; omega,?_,?_⟩
  · intro k hkl hklft hkh
    change k < left at hklft
    by_cases hki : k < s.i
    · exact hprefix k hkl hki hkh
    · exact Nat.le_of_lt (hlf.2.2.2 k (by omega) hklft)
  · intro k hkl hkr hkh
    change right < k at hkr
    by_cases hkj : s.j < k
    · exact hsuffix k hkl hkj hkh
    · exact Nat.le_of_lt (hrf.2.2.2 k hkr (by omega))

theorem scanned_swap_classified (pivot lo hi fuel : Nat) (s : State) (left right : Nat)
    (hc : Classified pivot lo hi s)
    (hl : scanLeft s.buffer pivot fuel s.i = .ok left)
    (hr : scanRight s.buffer pivot fuel s.j = .ok right)
    (hrvalue : s.buffer.getD right 0 ≤ pivot) (hcross : left ≤ right) :
    let out := (s.buffer.set left (s.buffer.getD right 0)).set right (s.buffer.getD left 0)
    Classified pivot lo hi ⟨out,left+1,right-1⟩ := by
  dsimp
  have hlf := scan_left_success s.buffer pivot fuel s.i left hl
  have hrf := scan_right_success s.buffer pivot fuel s.j right hr
  have hvalues := overwrite_pair_values s.buffer left right hlf.2.1 hrf.2.1
  rcases hc with ⟨hlo,hhi,hprefix,hsuffix⟩
  refine ⟨by dsimp; omega,by dsimp; omega,?_,?_⟩
  · intro k hkl hkle hkh
    change k < left+1 at hkle
    change ((s.buffer.set left (s.buffer.getD right 0)).set right
      (s.buffer.getD left 0)).getD k 0 ≤ pivot
    by_cases he : k = left
    · subst k; rw [hvalues.1]; exact hrvalue
    · rw [getD_set_other _ right k _ (by omega),getD_set_other _ left k _ (by omega)]
      by_cases hki : k < s.i
      · exact hprefix k hkl hki hkh
      · exact Nat.le_of_lt (hlf.2.2.2 k (by omega) (by omega))
  · intro k hkl hkr hkh
    change right-1 < k at hkr
    change pivot ≤ ((s.buffer.set left (s.buffer.getD right 0)).set right
      (s.buffer.getD left 0)).getD k 0
    by_cases he : k = right
    · subst k; rw [hvalues.2]; exact hlf.2.2.1
    · rw [getD_set_other _ right k _ (by omega),getD_set_other _ left k _ (by omega)]
      by_cases hkj : s.j < k
      · exact hsuffix k hkl hkj hkh
      · exact Nat.le_of_lt (hrf.2.2.2 k (by omega) (by omega))

theorem iteration_success_sentinels (pivot scanFuel hi : Nat) (s : State)
    (result : Transition) (hs : Sentinels pivot hi s) (hactive : s.i ≤ s.j)
    (hf : s.buffer.length < scanFuel) (h : iteration pivot scanFuel s = .ok result) :
    Sentinels pivot hi result.state := by
  rcases iteration_total_preserves_sentinels pivot scanFuel hi s hs hactive hf with ⟨r,hr,hsr⟩
  have he : r = result := Except.ok.inj (hr.symm.trans h)
  simpa only [he] using hsr

theorem iteration_success_classified (pivot scanFuel lo hi : Nat) (s : State)
    (result : Transition) (hs : Sentinels pivot hi s) (hactive : s.i ≤ s.j)
    (hf : s.buffer.length < scanFuel) (hc : Classified pivot lo hi s)
    (h : iteration pivot scanFuel s = .ok result) :
    Classified pivot lo hi result.state := by
  cases hl : scanLeft s.buffer pivot scanFuel s.i with
  | error err => simp [iteration,hl] at h
  | ok left =>
      cases hr : scanRight s.buffer pivot scanFuel s.j with
      | error err => simp [iteration,hl,hr] at h
      | ok right =>
          have hlf := scan_left_success s.buffer pivot scanFuel s.i left hl
          have hrf := scan_right_success s.buffer pivot scanFuel s.j right hr
          obtain ⟨lower,hlower,hvalue⟩ := (hs.2.2.2 hactive).2
          have hj : s.j < s.buffer.length := Nat.lt_of_le_of_lt hs.2.2.1 hs.1
          obtain ⟨r,hr',_,hrv⟩ := scan_right_has_sentinel s.buffer pivot scanFuel s.j lower
            hlower hj hvalue (by omega)
          have he : r = right := Except.ok.inj (hr'.symm.trans hr)
          subst r
          by_cases hcross : left ≤ right
          · let out := (s.buffer.set left (s.buffer.getD right 0)).set right (s.buffer.getD left 0)
            have hswap : swapCells s.buffer left right = .ok out :=
              swap_in_bounds_executes s.buffer left right hlf.2.1 hrf.2.1
            have hcnext := scanned_swap_classified pivot lo hi scanFuel s left right hc hl hr hrv hcross
            by_cases hz : right = 0
            · have he : Transition.finished ⟨out,left+1,right⟩ = result := by
                simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hswap,if_pos hz,
                  except_pure,Except.ok.injEq] using h
              subst result
              simpa only [Transition.state,out,hz,Nat.zero_sub] using hcnext
            · have he : Transition.again ⟨out,left+1,right-1⟩ = result := by
                simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hswap,if_neg hz,
                  except_pure,Except.ok.injEq] using h
              subst result
              exact hcnext
          · have he : Transition.finished ⟨s.buffer,left,right⟩ = result := by
              simpa only [iteration,hl,hr,except_ok_bind,if_neg hcross,
                except_pure,Except.ok.injEq] using h
            subst result
            exact crossed_scans_classified pivot lo hi scanFuel s left right hc hl hr

theorem partition_success_classified (pivot scanFuel fuel lo hi : Nat) (s result : State)
    (hs : Sentinels pivot hi s) (hf : s.buffer.length < scanFuel)
    (hc : Classified pivot lo hi s) (h : partition pivot scanFuel fuel s = .ok result) :
    Classified pivot lo hi result := by
  induction fuel generalizing s result with
  | zero =>
      by_cases ha : s.i ≤ s.j
      · simp [partition,ha] at h
      · have he : s = result := by simpa [partition,ha] using h
        simpa only [← he] using hc
  | succ fuel ih =>
      by_cases ha : s.i ≤ s.j
      · cases hit : iteration pivot scanFuel s with
        | error err => simp [partition,ha,hit] at h
        | ok next =>
            have hcs := iteration_success_classified pivot scanFuel lo hi s next hs ha hf hc hit
            have hsn := iteration_success_sentinels pivot scanFuel hi s next hs ha hf hit
            have hp := (iteration_success_facts pivot scanFuel s next hit).1.length_eq
            cases next with
            | finished next =>
                have he : next = result := by simpa [partition,ha,hit] using h
                simpa only [Transition.state,he] using hcs
            | again next =>
                have hnext : partition pivot scanFuel fuel next = .ok result := by
                  simpa [partition,ha,hit] using h
                exact ih next result hsn (by change next.buffer.length = s.buffer.length at hp; omega) hcs hnext
      · have he : s = result := by simpa [partition,ha] using h
        simpa only [← he] using hc

theorem partition_success_facts (pivot scanFuel fuel : Nat) (s result : State)
    (h : partition pivot scanFuel fuel s = .ok result) :
    List.Perm result.buffer s.buffer ∧ s.i ≤ result.i ∧ result.j ≤ s.j ∧ result.j < result.i := by
  induction fuel generalizing s result with
  | zero =>
      by_cases hc : s.i ≤ s.j
      · simp [partition,hc] at h
      · have he : s = result := by simpa [partition,hc] using h
        subst result
        exact ⟨List.Perm.refl _,Nat.le_refl _,Nat.le_refl _,by omega⟩
  | succ fuel ih =>
      by_cases hc : s.i ≤ s.j
      · cases hit : iteration pivot scanFuel s with
        | error err => simp [partition,hc,hit] at h
        | ok transition =>
            have ht := iteration_success_facts pivot scanFuel s transition hit
            cases transition with
            | finished next =>
                have he : next = result := by simpa [partition,hc,hit] using h
                subst result
                exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.2.2⟩
            | again next =>
                have hn : partition pivot scanFuel fuel next = .ok result := by
                  simpa [partition,hc,hit] using h
                have hh := ih next result hn
                exact ⟨hh.1.trans ht.1,Nat.le_trans ht.2.1 hh.2.1,
                  Nat.le_trans hh.2.2.1 ht.2.2.1,hh.2.2.2⟩
      · have he : s = result := by simpa [partition,hc] using h
        subst result
        exact ⟨List.Perm.refl _,Nat.le_refl _,Nat.le_refl _,by omega⟩

theorem partition_success_length (pivot scanFuel fuel : Nat) (s result : State)
    (h : partition pivot scanFuel fuel s = .ok result) : result.buffer.length = s.buffer.length :=
  (partition_success_facts pivot scanFuel fuel s result h).1.length_eq

theorem partition_success_multiplicities (pivot scanFuel fuel : Nat) (s result : State)
    (h : partition pivot scanFuel fuel s = .ok result) (value : Nat) :
    result.buffer.count value = s.buffer.count value :=
  (partition_success_facts pivot scanFuel fuel s result h).1.countP_eq (fun x => x == value)

theorem partition_success_sentinels (pivot scanFuel fuel hi : Nat) (s result : State)
    (hs : Sentinels pivot hi s) (hf : s.buffer.length < scanFuel)
    (h : partition pivot scanFuel fuel s = .ok result) : Sentinels pivot hi result := by
  induction fuel generalizing s result with
  | zero =>
      by_cases ha : s.i ≤ s.j
      · simp [partition,ha] at h
      · have he : s = result := by simpa [partition,ha] using h
        simpa only [← he] using hs
  | succ fuel ih =>
      by_cases ha : s.i ≤ s.j
      · cases hit : iteration pivot scanFuel s with
        | error err => simp [partition,ha,hit] at h
        | ok next =>
            have hsn := iteration_success_sentinels pivot scanFuel hi s next hs ha hf hit
            have hp := (iteration_success_facts pivot scanFuel s next hit).1.length_eq
            cases next with
            | finished next =>
                have he : next = result := by simpa [partition,ha,hit] using h
                simpa only [Transition.state,he] using hsn
            | again next =>
                have hnext : partition pivot scanFuel fuel next = .ok result := by
                  simpa [partition,ha,hit] using h
                exact ih next result hsn (by change next.buffer.length = s.buffer.length at hp; omega) hnext
      · have he : s = result := by simpa [partition,ha] using h
        simpa only [← he] using hs

/-- Every nonempty, in-bounds source partition succeeds with the explicit
scan and outer-loop budgets. No sortedness or partition relation is assumed. -/
theorem source_partition_spec (xs : List Nat) (lo hi : Nat) (hlo : lo ≤ hi)
    (hhi : hi < xs.length) :
    let pivot := xs.getD ((lo+hi)/2) 0
    ∃ result,
      partition pivot (xs.length+1) (hi-lo+2) ⟨xs,lo,hi⟩ = .ok result ∧
      List.Perm result.buffer xs ∧
      lo ≤ result.i ∧ result.i ≤ hi+1 ∧ result.j ≤ hi ∧ result.j < result.i ∧
      (∀ k, lo ≤ k → k ≤ result.j → result.buffer.getD k 0 ≤ pivot) ∧
      (∀ k, result.i ≤ k → k ≤ hi → pivot ≤ result.buffer.getD k 0) ∧
      (∀ k, lo ≤ k → result.j < k → k < result.i → k ≤ hi →
        result.buffer.getD k 0 = pivot) := by
  dsimp
  obtain ⟨result,hr⟩ := source_partition_total xs lo hi hlo hhi
  have hf := partition_success_facts _ _ _ _ result hr
  have hcl := partition_success_classified _ _ _ lo hi _ result
    (initial_sentinels xs lo hi hlo hhi) (by dsimp; omega)
    (initial_classified xs _ lo hi) hr
  have hsn := partition_success_sentinels _ _ _ hi _ result
    (initial_sentinels xs lo hi hlo hhi) (by dsimp; omega) hr
  refine ⟨result,hr,hf.1,hcl.1,hsn.2.1,hcl.2.1,hf.2.2.2,?_,?_,?_⟩
  · intro k hkl hkj
    exact hcl.2.2.1 k hkl (by omega) (by have hh := hcl.2.1; omega)
  · intro k hki hkh
    exact hcl.2.2.2 k (by have hh := hcl.1; omega) (by omega) hkh
  · intro k hkl hjk hki hkh
    exact Nat.le_antisymm (hcl.2.2.1 k hkl hki hkh) (hcl.2.2.2 k hkl hjk hkh)

def SameOutside (lo hi : Nat) (before after : List Nat) : Prop :=
  ∀ k, k < lo ∨ hi < k → after.getD k 0 = before.getD k 0

theorem swap_success_frame (xs result : List Nat) (lo hi i j : Nat)
    (hli : lo ≤ i) (hij : i ≤ j) (hjh : j ≤ hi)
    (h : swapCells xs i j = .ok result) : SameOutside lo hi xs result := by
  cases hl : xs[i]? with
  | none => simp [swapCells,hl] at h
  | some left =>
      cases hr : xs[j]? with
      | none => simp [swapCells,hl,hr] at h
      | some right =>
          have he : (xs.set i right).set j left = result := by simpa [swapCells,hl,hr] using h
          subst result
          intro k hk
          rw [getD_set_other _ j k _ (by omega),getD_set_other _ i k _ (by omega)]

theorem iteration_success_frame (pivot scanFuel lo hi : Nat) (s : State)
    (result : Transition) (hli : lo ≤ s.i) (hjh : s.j ≤ hi)
    (h : iteration pivot scanFuel s = .ok result) :
    SameOutside lo hi s.buffer result.state.buffer := by
  cases hl : scanLeft s.buffer pivot scanFuel s.i with
  | error err => simp [iteration,hl] at h
  | ok left =>
      cases hr : scanRight s.buffer pivot scanFuel s.j with
      | error err => simp [iteration,hl,hr] at h
      | ok right =>
          have hlf := scan_left_success s.buffer pivot scanFuel s.i left hl
          have hrf := scan_right_success s.buffer pivot scanFuel s.j right hr
          by_cases hcross : left ≤ right
          · cases hswap : swapCells s.buffer left right with
            | error err => simp [iteration,hl,hr,hcross,hswap] at h
            | ok out =>
                have hframe := swap_success_frame s.buffer out lo hi left right
                  (by omega) hcross (by omega) hswap
                by_cases hz : right = 0
                · have he : Transition.finished ⟨out,left+1,right⟩ = result := by
                    simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hswap,if_pos hz,
                      except_pure,Except.ok.injEq] using h
                  subst result; exact hframe
                · have he : Transition.again ⟨out,left+1,right-1⟩ = result := by
                    simpa only [iteration,hl,hr,except_ok_bind,if_pos hcross,hswap,if_neg hz,
                      except_pure,Except.ok.injEq] using h
                  subst result; exact hframe
          · have he : Transition.finished ⟨s.buffer,left,right⟩ = result := by
              simpa only [iteration,hl,hr,except_ok_bind,if_neg hcross,
                except_pure,Except.ok.injEq] using h
            subst result
            exact fun _ _ => rfl

theorem partition_success_frame (pivot scanFuel fuel lo hi : Nat) (s result : State)
    (hli : lo ≤ s.i) (hjh : s.j ≤ hi) (h : partition pivot scanFuel fuel s = .ok result) :
    SameOutside lo hi s.buffer result.buffer := by
  induction fuel generalizing s result with
  | zero =>
      by_cases ha : s.i ≤ s.j
      · simp [partition,ha] at h
      · have he : s = result := by simpa [partition,ha] using h
        subst result; exact fun _ _ => rfl
  | succ fuel ih =>
      by_cases ha : s.i ≤ s.j
      · cases hit : iteration pivot scanFuel s with
        | error err => simp [partition,ha,hit] at h
        | ok next =>
            have hframe := iteration_success_frame pivot scanFuel lo hi s next hli hjh hit
            have hfacts := iteration_success_facts pivot scanFuel s next hit
            cases next with
            | finished next =>
                have he : next = result := by simpa [partition,ha,hit] using h
                simpa only [Transition.state,he] using hframe
            | again next =>
                have hnext : partition pivot scanFuel fuel next = .ok result := by
                  simpa [partition,ha,hit] using h
                have hnlo : lo ≤ next.i := Nat.le_trans hli hfacts.2.1
                have hnhi : next.j ≤ hi := Nat.le_trans hfacts.2.2.1 hjh
                have hnframe := ih next result hnlo hnhi hnext
                exact fun k hk => (hnframe k hk).trans (hframe k hk)
      · have he : s = result := by simpa [partition,ha] using h
        subst result; exact fun _ _ => rfl

/-- Successful recursive execution preserves every element, even though the
full sortedness/totality proof is not claimed by this theorem. -/
theorem quicksort_success_perm (fuel : Nat) (xs result : List Nat) (lo hi : Nat)
    (h : quicksort fuel xs lo hi = .ok result) : List.Perm result xs := by
  induction fuel generalizing xs result lo hi with
  | zero =>
      by_cases hc : hi ≤ lo
      · have he : xs = result := by simpa [quicksort,hc] using h
        subst result; exact List.Perm.refl _
      · simp [quicksort,hc] at h
  | succ fuel ih =>
      by_cases hc : hi ≤ lo
      · have he : xs = result := by simpa [quicksort,hc] using h
        subst result; exact List.Perm.refl _
      · cases hp : xs[(lo+hi)/2]? with
        | none => simp [quicksort,hc,hp] at h
        | some pivot =>
            cases hs : partition pivot (xs.length+1) (hi-lo+2) ⟨xs,lo,hi⟩ with
            | error err => simp [quicksort,hc,hp,hs] at h
            | ok state =>
                have hperm := (partition_success_facts pivot (xs.length+1) (hi-lo+2)
                  ⟨xs,lo,hi⟩ state hs).1
                by_cases hleft : lo < state.j
                · cases hl : quicksort fuel state.buffer lo state.j with
                  | error err => simp [quicksort,hc,hp,hs,hleft,hl] at h
                  | ok buffer =>
                      have hlperm := ih state.buffer buffer lo state.j hl
                      by_cases hright : state.i < hi
                      · have hr : quicksort fuel buffer state.i hi = .ok result := by
                          simpa [quicksort,hc,hp,hs,hleft,hl,hright] using h
                        exact ((ih buffer result state.i hi hr).trans hlperm).trans hperm
                      · have he : buffer = result := by
                          simpa [quicksort,hc,hp,hs,hleft,hl,hright] using h
                        subst result; exact hlperm.trans hperm
                · by_cases hright : state.i < hi
                  · have hr : quicksort fuel state.buffer state.i hi = .ok result := by
                      simpa [quicksort,hc,hp,hs,hleft,hright] using h
                    exact (ih state.buffer result state.i hi hr).trans hperm
                  · have he : state.buffer = result := by
                      simpa [quicksort,hc,hp,hs,hleft,hright] using h
                    subst result; exact hperm

theorem quicksort_success_length (fuel : Nat) (xs result : List Nat) (lo hi : Nat)
    (h : quicksort fuel xs lo hi = .ok result) : result.length = xs.length :=
  (quicksort_success_perm fuel xs result lo hi h).length_eq

theorem quicksort_success_multiplicities (fuel : Nat) (xs result : List Nat) (lo hi value : Nat)
    (h : quicksort fuel xs lo hi = .ok result) : result.count value = xs.count value :=
  (quicksort_success_perm fuel xs result lo hi h).countP_eq (fun x => x == value)

/-- Ordinary executions exercise real scans/swaps/recursion rather than a
reference sort. These finite examples do not replace the general theorems. -/
theorem empty_example : quicksort 0 [] 0 0 = .ok [] := rfl

theorem singleton_example : quicksort 0 [7] 0 0 = .ok [7] := rfl

theorem reversed_example :
    quicksort 8 [5,4,3,2,1] 0 4 = .ok [1,2,3,4,5] := rfl

theorem duplicate_example :
    quicksort 8 [3,1,3,2,1,3] 0 5 = .ok [1,1,2,3,3,3] := rfl

theorem equal_example : quicksort 8 [4,4,4,4] 0 3 = .ok [4,4,4,4] := rfl

theorem subrange_example : quicksort 8 [9,3,2,1,8] 1 3 = .ok [9,1,2,3,8] := rfl

theorem partition_example :
    partition 3 6 6 ⟨[5,1,3,2,4],0,4⟩ = .ok ⟨[2,1,3,5,4],3,1⟩ := rfl

theorem subrange_partition_example :
    partition 2 6 4 ⟨[9,3,2,1,8],1,3⟩ = .ok ⟨[9,1,2,3,8],3,1⟩ := rfl

/-- The right-scan break returns zero even when its cell exceeds pivot.
This helper branch is retained; source_partition_total separately supplies
a genuine low-valued sentinel, so it does not assume this branch is low. -/
theorem right_zero_break_example : scanRight [4] 3 1 0 = .ok 0 := rfl

theorem post_swap_zero_break_example :
    iteration 5 2 ⟨[5],0,0⟩ = .ok (.finished ⟨[5],1,0⟩) := rfl

theorem scan_crossing_example :
    iteration 2 3 ⟨[1,3],0,1⟩ = .ok (.finished ⟨[1,3],1,0⟩) := rfl

theorem scan_fuel_example : scanLeft [1] 2 0 0 = .error .scanFuel := rfl

theorem bounds_example : scanLeft [] 2 1 0 = .error (.readBounds 0) := rfl

theorem partition_fuel_example :
    partition 1 2 0 ⟨[1],0,0⟩ = .error .partitionFuel := rfl

theorem recursion_fuel_example :
    quicksort 0 [2,1] 0 1 = .error .recursionFuel := rfl

end Audit.Wire3.WhirQuicksort
