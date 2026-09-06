import Audit.Wire3.WhirSampling

/-!
# Actual adjacent compaction, separately from sorting

Source: SpongefishWhirVerify.sol at becfe98e, `_sortAndDedupIndices`, specifically its
post-quicksort `write = 1; for (i = 1; i < n; i++)` loop and final length store.
The model reads the CURRENT buffer at i and i-1, compares those values, writes
the current value at write on inequality, increments write, and finally takes
the live prefix. It does not replace the current-buffer reads with an oracle.

The loop fuel is exactly n-1. Bounds below justify every read/write on the
source-initialized trace, so getD's default is not observed on that trace.
An arbitrary State is not claimed to satisfy source array preconditions.
List.set models an indexed overwrite, and List.take models the final logical
length change. Neither models EVM memory words, allocation, ABI, uint256 or
Yul execution. Quicksort and its recursion/swaps remain UNPROVED here.
Agreement with dedupAdjacent needs no sortedness assumption. Sorting is used
only by the separate strict-ascending corollary. Thus unsorted non-adjacent
duplicates are deliberately retained. No full sampling/WHIR/PCS claim follows.
-/
namespace Audit.Wire3.WhirDedup
open Audit.Wire3

structure State where
  buffer : List Nat
  read : Nat
  write : Nat
deriving DecidableEq, Repr

def step (s : State) : State :=
  let value := s.buffer.getD s.read 0
  let previous := s.buffer.getD (s.read - 1) 0
  if value = previous then
    ⟨s.buffer,s.read+1,s.write⟩
  else
    ⟨s.buffer.set s.write value,s.read+1,s.write+1⟩

def loop : Nat → State → State
  | 0, s => s
  | fuel+1, s => loop fuel (step s)

/-- Explicit `i < n` test. `none` means this mathematical runner exhausted
its supplied fuel while the source loop condition was still true; it is not
a new source rejection. Exact source fuel below never returns none. -/
def guardedLoop (n : Nat) : Nat → State → Option State
  | 0, s => if s.read < n then none else some s
  | fuel+1, s => if s.read < n then guardedLoop n fuel (step s) else some s

def initial (xs : List Nat) : State := ⟨xs,1,1⟩

def compact (xs : List Nat) : List Nat :=
  if xs.length ≤ 1 then xs else
  let final := loop (xs.length-1) (initial xs)
  final.buffer.take final.write

theorem step_read (s : State) : (step s).read = s.read+1 := by
  simp only [step]; split <;> rfl

theorem step_length (s : State) : (step s).buffer.length = s.buffer.length := by
  simp only [step]; split <;> simp

theorem step_write_bounds (s : State) :
    s.write ≤ (step s).write ∧ (step s).write ≤ s.write+1 := by
  simp only [step]; split <;> dsimp <;> omega

theorem loop_read_exact (fuel : Nat) (s : State) :
    (loop fuel s).read = s.read+fuel := by
  induction fuel generalizing s with
  | zero => simp [loop]
  | succ fuel ih => rw [loop,ih,step_read]; omega

theorem loop_length (fuel : Nat) (s : State) :
    (loop fuel s).buffer.length = s.buffer.length := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => rw [loop,ih,step_length]

theorem loop_write_bounds (fuel : Nat) (s : State) :
    s.write ≤ (loop fuel s).write ∧ (loop fuel s).write ≤ s.write+fuel := by
  induction fuel generalizing s with
  | zero => simp [loop]
  | succ fuel ih =>
      have h := ih (step s)
      have hs := step_write_bounds s
      simp only [loop]
      omega

theorem guarded_loop_exact_fuel (n fuel : Nat) (s : State)
    (h : s.read+fuel = n) : guardedLoop n fuel s = some (loop fuel s) := by
  induction fuel generalizing s with
  | zero => simp only [Nat.add_zero] at h; simp [guardedLoop,loop,h]
  | succ fuel ih =>
      have hr : s.read < n := by omega
      simp only [guardedLoop,if_pos hr,loop]
      apply ih
      rw [step_read]
      omega

theorem guarded_loop_insufficient_fuel (n fuel : Nat) (s : State)
    (h : s.read+fuel < n) : guardedLoop n fuel s = none := by
  induction fuel generalizing s with
  | zero => simpa [guardedLoop] using h
  | succ fuel ih =>
      have hr : s.read < n := by omega
      simp only [guardedLoop,if_pos hr]
      apply ih
      rw [step_read]
      omega

/-- Both comparison indices and the possible write index are in bounds at
EVERY actual loop iteration; default-valued out-of-range getD is never used. -/
theorem each_source_iteration_in_bounds (xs : List Nat) (fuel : Nat)
    (h : fuel < xs.length-1) :
    let s := loop fuel (initial xs)
    1 ≤ s.write ∧ s.write ≤ s.read ∧
      s.read < s.buffer.length ∧ s.read-1 < s.buffer.length ∧
      s.write < s.buffer.length := by
  have hw := loop_write_bounds fuel (initial xs)
  have hr := loop_read_exact fuel (initial xs)
  have hl := loop_length fuel (initial xs)
  simp only [initial] at *
  omega

theorem nonempty_source_fuel_exact (x : Nat) (rest : List Nat) :
    guardedLoop (x::rest).length ((x::rest).length-1) (initial (x::rest)) =
      some (loop rest.length (initial (x::rest))) := by
  simpa using guarded_loop_exact_fuel (x::rest).length rest.length
    (initial (x::rest)) (by simp [initial,Nat.add_comm])

theorem nonempty_source_final_read (x : Nat) (rest : List Nat) :
    (loop ((x::rest).length-1) (initial (x::rest))).read = (x::rest).length := by
  simp [loop_read_exact,initial,Nat.add_comm]

theorem getD_set_same (xs : List Nat) (i value : Nat) (hi : i < xs.length) :
    (xs.set i value).getD i 0 = value := by
  simp [List.getElem?_set_eq (by simpa using hi)]

theorem getD_set_other (xs : List Nat) (i j value : Nat) (hne : i ≠ j) :
    (xs.set i value).getD j 0 = xs.getD j 0 := by
  simp [List.getElem?_set_ne hne]

/-- A write strictly before a suffix cannot change that suffix. -/
theorem drop_set_before (xs : List Nat) (i cut value : Nat) (hi : i < cut) :
    (xs.set i value).drop cut = xs.drop cut := by
  induction xs generalizing i cut with
  | nil => simp
  | cons x xs ih =>
      cases cut with
      | zero => omega
      | succ cut =>
          cases i with
          | zero => rfl
          | succ i => simpa using ih i cut (by omega)

/-- The written prefix really appends one cell; no abstract output list update. -/
theorem take_set_at_end (xs : List Nat) (i value : Nat) (hi : i < xs.length) :
    (xs.set i value).take (i+1) = xs.take i ++ [value] := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have h : i < xs.length := by simp only [List.length_cons] at hi; omega
          simpa using congrArg (List.cons x) (ih i h)

theorem drop_cons_current (xs : List Nat) (i x : Nat) (rest : List Nat)
    (h : xs.drop i = x :: rest) : xs.getD i 0 = x := by
  have he := congrArg (fun ys : List Nat => ys.getD 0 0) h
  simpa [List.getElem?_drop] using he

theorem drop_cons_next (xs : List Nat) (i x : Nat) (rest : List Nat)
    (h : xs.drop i = x :: rest) : xs.drop (i+1) = rest := by
  have he := congrArg (List.drop 1) h
  simpa [List.drop_drop,Nat.add_comm] using he

/-- This is the overwrite/suffix invariant needed by the next iteration.
If write=read, the overwrite stores the same current value. -/
theorem write_preserves_current (xs : List Nat) (write read x : Nat)
    (hr : read < xs.length) (hx : xs.getD read 0 = x) :
    (xs.set write x).getD read 0 = x := by
  by_cases hw : write = read
  · subst write; exact getD_set_same xs read x hr
  · rw [getD_set_other xs write read x hw,hx]

/-- General execution theorem. The unread suffix and previous cell describe
actual buffer contents; the conclusion is proved from the indexed loop. -/
theorem loop_prefix_exact (unread : List Nat) (s : State) (previous : Nat)
    (hr : 1 ≤ s.read) (hw : s.write ≤ s.read)
    (hsuffix : s.buffer.drop s.read = unread)
    (hprevious : s.buffer.getD (s.read-1) 0 = previous) :
    let final := loop unread.length s
    final.buffer.take final.write =
      s.buffer.take s.write ++ WhirSampling.dedupFrom previous unread := by
  induction unread generalizing s previous with
  | nil => simp [loop,WhirSampling.dedupFrom]
  | cons x rest ih =>
      have hx := drop_cons_current s.buffer s.read x rest hsuffix
      have hrest := drop_cons_next s.buffer s.read x rest hsuffix
      have hlen := congrArg List.length hsuffix
      have hread : s.read < s.buffer.length := by
        simp only [List.length_drop,List.length_cons] at hlen
        omega
      have hwrite : s.write < s.buffer.length := by omega
      by_cases he : x = previous
      · have hstep : step s = ⟨s.buffer,s.read+1,s.write⟩ := by
          unfold step; rw [hx,hprevious]; exact if_pos he
        have hh := ih ⟨s.buffer,s.read+1,s.write⟩ x (by dsimp; omega)
          (by dsimp; omega) hrest (by simpa using hx)
        simpa [List.length_cons,loop,hstep,WhirSampling.dedupFrom,he] using hh
      · have hstep : step s = ⟨s.buffer.set s.write x,s.read+1,s.write+1⟩ := by
          unfold step; rw [hx,hprevious]; exact if_neg he
        have hs : (s.buffer.set s.write x).drop (s.read+1) = rest := by
          rw [drop_set_before s.buffer s.write (s.read+1) x (by omega),hrest]
        have hp : (s.buffer.set s.write x).getD ((s.read+1)-1) 0 = x := by
          simpa using write_preserves_current s.buffer s.write s.read x hread hx
        have hh := ih ⟨s.buffer.set s.write x,s.read+1,s.write+1⟩ x
          (by dsimp; omega) (by dsimp; omega) hs hp
        simpa [List.length_cons,loop,hstep,WhirSampling.dedupFrom,he,
          take_set_at_end s.buffer s.write x hwrite,List.append_assoc] using hh

theorem compact_eq_adjacent_dedup (xs : List Nat) :
    compact xs = WhirSampling.dedupAdjacent xs := by
  cases xs with
  | nil => rfl
  | cons x rest =>
      cases rest with
      | nil => rfl
      | cons y ys =>
          have h := loop_prefix_exact (y::ys) (initial (x::y::ys)) x
            (by simp [initial]) (by simp [initial]) rfl rfl
          simpa [compact,initial,WhirSampling.dedupAdjacent] using h

theorem nonempty_loop_prefix_exact (x : Nat) (rest : List Nat) :
    let final := loop rest.length (initial (x::rest))
    final.buffer.take final.write = WhirSampling.dedupAdjacent (x::rest) := by
  have h := loop_prefix_exact rest (initial (x::rest)) x
    (by simp [initial]) (by simp [initial]) rfl rfl
  simpa [initial,WhirSampling.dedupAdjacent] using h

/-- The final length word equals the length of the reference result. -/
theorem nonempty_final_write_exact (x : Nat) (rest : List Nat) :
    (loop rest.length (initial (x::rest))).write =
      (WhirSampling.dedupAdjacent (x::rest)).length := by
  have h := congrArg List.length (nonempty_loop_prefix_exact x rest)
  have hw := loop_write_bounds rest.length (initial (x::rest))
  have hl := loop_length rest.length (initial (x::rest))
  simp only [List.length_take,initial,List.length_cons] at *
  rw [Nat.min_eq_left (by omega)] at h
  exact h

/-- Explicit condition-testing execution followed by logical length shrinkage. -/
def compactGuarded (xs : List Nat) : Option (List Nat) :=
  if xs.length ≤ 1 then some xs else
    (guardedLoop xs.length (xs.length-1) (initial xs)).map
      (fun s => s.buffer.take s.write)

theorem guarded_compaction_exact (xs : List Nat) :
    compactGuarded xs = some (WhirSampling.dedupAdjacent xs) := by
  cases xs with
  | nil => rfl
  | cons x rest =>
      cases rest with
      | nil => rfl
      | cons y ys =>
          simp only [compactGuarded,List.length_cons]
          rw [if_neg (by omega)]
          have h := nonempty_source_fuel_exact x (y::ys)
          simp only [List.length_cons] at h
          rw [h]
          exact congrArg some (nonempty_loop_prefix_exact x (y::ys))

theorem compact_membership (xs : List Nat) (query : Nat) :
    query ∈ compact xs ↔ query ∈ xs := by
  rw [compact_eq_adjacent_dedup]
  exact WhirSampling.adjacent_dedup_membership xs query

theorem compact_length_bound (xs : List Nat) : (compact xs).length ≤ xs.length := by
  rw [compact_eq_adjacent_dedup]
  exact WhirSampling.adjacent_dedup_length xs

/-- Sortedness enters ONLY here, never in the indexed execution equivalence. -/
theorem sorted_compaction_strict (xs : List Nat) (h : WhirSampling.Nondecreasing xs) :
    WhirSampling.StrictAscending (compact xs) := by
  rw [compact_eq_adjacent_dedup]
  exact WhirSampling.adjacent_dedup_of_sorted_is_strict xs h

theorem empty_compaction : compactGuarded [] = some [] := rfl

theorem singleton_compaction (x : Nat) : compactGuarded [x] = some [x] := rfl

theorem adjacent_duplicates_example :
    compactGuarded [0,0,1,2,2,3,3] = some [0,1,2,3] := by decide

theorem nonadjacent_duplicates_retained_example :
    compactGuarded [2,2,1,2,2,1] = some [2,1,2,1] := by decide

theorem all_equal_example : compactGuarded [5,5,5,5] = some [5] := by decide

theorem all_distinct_example : compactGuarded [0,1,2,3] = some [0,1,2,3] := by decide

theorem ordinary_buffer_and_live_length_example :
    loop 5 (initial [2,2,1,2,2,1]) = ⟨[2,1,2,1,2,1],6,4⟩ := by decide

theorem insufficient_fuel_example :
    guardedLoop 4 2 (initial [0,0,1,1]) = none := by decide

end Audit.Wire3.WhirDedup
