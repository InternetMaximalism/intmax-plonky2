import Audit.Wire3.GateAggregatePolynomial

/-!
Concrete Goldilocks Ext3 algebra for Rust mle/src/gate_ext3.rs:543-608:
`evaluate_gate_constraints_ext3_validated` (doc comment 543, body 544-597;
its filter and slot write loop is 591-594, the indexed write itself 593) and
`aggregate_gate_constraints_ext3` (doc comment 599, body 600-608).

Indexed constraint writes read the CURRENT buffer and update increasing slot
indices. `addIndexed` is the totalized List.set/getD form: out-of-range writes
silently no-op and out-of-range reads default to zero, whereas the source's
`accumulated[slot]` panics. `addIndexedChecked` is the partial form that fails
on the first out-of-range write; it is proved to agree with `addIndexed`
exactly when `index + terms.length ≤ buffer.length`, and to fail otherwise.
Every connection to the source goes through that bound (consumed in
GateSlotCommutation.slotRows), so the totalized truncation is never asserted
to be source behavior.

The lockstep form `addSlots` is proved equal to the indexed execution; it
keeps the full slot buffer, including untouched trailing slots, and its
lookup lemmas are transported to the executed `addIndexed`.
No compiler/usize/ABI refinement or cryptographic property is asserted.
-/
namespace Audit.Wire3.GateSlotAlgebra
open Audit.Wire3 GoldilocksExt3Field

def wrap (xs : List Verifier.Ext3) : List Element := xs.map Element.mk
def unwrap (xs : List Element) : List Verifier.Ext3 := xs.map Element.toVerifier

theorem unwrap_wrap (xs : List Verifier.Ext3) : unwrap (wrap xs) = xs := by
  simp only [unwrap,wrap,List.map_map,Function.comp_def]
  exact List.map_id xs

theorem wrap_length (xs : List Verifier.Ext3) : (wrap xs).length = xs.length := List.length_map _ _

def horner (alpha : Element) : List Element → Element
  | [] => 0
  | term::rest => horner alpha rest * alpha + term

theorem horner_actual (alpha : Element) (terms : List Element) :
    (horner alpha terms).toVerifier = Gates.horner (unwrap terms) alpha.toVerifier := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      simp only [unwrap] at ih
      simp only [horner,unwrap,List.map_cons,Gates.horner_cons,← ih]
      rfl

theorem horner_wrapped_actual (alpha : Element) (terms : List Verifier.Ext3) :
    (horner alpha (wrap terms)).toVerifier = Gates.horner terms alpha.toVerifier := by
  rw [horner_actual,unwrap_wrap]

/-- The source's forward power loop (gate_ext3.rs:601-606): `combined += power*c;
power *= alpha`, starting from `power = 1, combined = 0`. -/
def forward (alpha : Element) : List Element → Element → Element → Element
  | [],_,acc => acc
  | term::rest,power,acc => forward alpha rest (power*alpha) (acc+power*term)

theorem forward_state (alpha : Element) (terms : List Element) (power acc : Element) :
    forward alpha terms power acc = acc + power * horner alpha terms := by
  induction terms generalizing power acc with
  | nil => simp [forward,horner]
  | cons t ts ih => rw [forward,ih,horner]; ring

def powers (alpha : Element) : Nat → List Element → Element
  | _,[] => 0
  | index,term::rest => alpha^index*term+powers alpha (index+1) rest

theorem powers_same_indices (alpha : Element) (terms : List Element) (index : Nat) :
    powers alpha index terms = alpha^index * horner alpha terms := by
  induction terms generalizing index with
  | nil => simp [powers,horner]
  | cons t ts ih => rw [powers,ih,horner,pow_succ]; ring

theorem forward_same_indices (alpha : Element) (terms : List Element) (index : Nat) (acc : Element) :
    forward alpha terms (alpha^index) acc = acc + powers alpha index terms := by
  rw [forward_state,powers_same_indices]

def reduce (alpha : Element) (terms : List Element) : Element := forward alpha terms 1 0

theorem reduce_horner (alpha : Element) (terms : List Element) : reduce alpha terms = horner alpha terms := by
  simp [reduce,forward_state]

theorem reduce_actual_horner (alpha : Element) (terms : List Verifier.Ext3) :
    (reduce alpha (wrap terms)).toVerifier = Gates.horner terms alpha.toVerifier := by
  rw [reduce_horner,horner_wrapped_actual]

/-- Totalized slot loop (gate_ext3.rs:592-593): `accumulated[slot] += filter*value`
with List.set/getD, which no-op/default out of range instead of panicking. -/
def addIndexed (filter : Element) : Nat → List Element → List Element → List Element
  | _,[],buffer => buffer
  | index,term::rest,buffer =>
      addIndexed filter (index+1) rest (buffer.set index (buffer.getD index 0+filter*term))

/-- Partial slot loop: the source's `accumulated[slot]` panic is `none` on the
first write whose index is not below the current buffer length. -/
def addIndexedChecked (filter : Element) : Nat → List Element → List Element → Option (List Element)
  | _,[],buffer => some buffer
  | index,term::rest,buffer =>
      if index < buffer.length then
        addIndexedChecked filter (index+1) rest (buffer.set index (buffer.getD index 0+filter*term))
      else none

def addSlots (filter : Element) : List Element → List Element → List Element
  | [],_ => []
  | buffer,[] => buffer
  | acc::buffer,term::rest => (acc+filter*term)::addSlots filter buffer rest

theorem indexed_length (filter : Element) (index : Nat) (terms buffer : List Element) :
    (addIndexed filter index terms buffer).length = buffer.length := by
  induction terms generalizing index buffer with
  | nil => rfl
  | cons t ts ih => simp only [addIndexed,ih,List.length_set]

theorem indexed_empty_buffer (filter : Element) (index : Nat) (terms : List Element) :
    addIndexed filter index terms [] = [] := by
  induction terms generalizing index with
  | nil => rfl
  | cons t ts ih => simpa only [addIndexed,List.set_nil] using ih (index+1)

theorem indexed_successor_cons (filter : Element) (index : Nat) (terms buffer : List Element) (head : Element) :
    addIndexed filter (index+1) terms (head::buffer) = head::addIndexed filter index terms buffer := by
  induction terms generalizing index buffer with
  | nil => rfl
  | cons t ts ih =>
      simpa only [addIndexed,List.getD_cons_succ,List.set_cons_succ] using
        ih (index+1) (buffer.set index (buffer.getD index 0+filter*t))

theorem indexed_equals_lockstep (filter : Element) (terms buffer : List Element) :
    addIndexed filter 0 terms buffer = addSlots filter buffer terms := by
  induction terms generalizing buffer with
  | nil => cases buffer <;> rfl
  | cons t ts ih =>
      cases buffer with
      | nil => exact indexed_empty_buffer filter 0 (t::ts)
      | cons b bs =>
          simp only [addIndexed,List.getD_cons_zero,List.set_cons_zero,addSlots]
          rw [indexed_successor_cons,ih]

/-- One step of the write loop under the remaining-capacity bound: the current
write index is in range and the bound is re-established for the rest. -/
theorem indexed_step_access_bounded (filter : Element) (index : Nat) (term : Element)
    (rest buffer : List Element) (h : index+(term::rest).length ≤ buffer.length) :
    index < buffer.length ∧ index+1+rest.length ≤
      (buffer.set index (buffer.getD index 0+filter*term)).length := by
  simp only [List.length_cons,List.length_set] at *
  omega

/-- Under the capacity bound every write of the checked loop is in range and
the checked loop returns exactly the totalized execution. -/
theorem indexed_checked_bounded (filter : Element) (index : Nat) (terms buffer : List Element)
    (h : index+terms.length ≤ buffer.length) :
    addIndexedChecked filter index terms buffer = some (addIndexed filter index terms buffer) := by
  induction terms generalizing index buffer with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hlt,hrest⟩ := indexed_step_access_bounded filter index t ts buffer h
      simp only [addIndexedChecked,hlt,↓reduceIte,addIndexed]
      exact ih (index+1) _ hrest

/-- Without the capacity bound the checked loop fails: some write is out of
range. A non-empty term list is required, since an empty loop performs no
write and cannot panic whatever the start index. -/
theorem indexed_checked_overflow (filter : Element) (index : Nat) (terms buffer : List Element)
    (h : buffer.length < index+terms.length) (hne : terms ≠ []) :
    addIndexedChecked filter index terms buffer = none := by
  induction terms generalizing index buffer with
  | nil => exact absurd rfl hne
  | cons t ts ih =>
      simp only [addIndexedChecked]
      split
      · rename_i hlt
        cases ts with
        | nil => simp only [List.length_cons,List.length_nil] at h; omega
        | cons u us =>
            apply ih _ _ _ (by simp)
            simp only [List.length_set,List.length_cons] at *
            omega
      · rfl

/-- At start index 0, the source's write loop for one gate: the checked loop
succeeds exactly under the capacity bound, with the totalized loop's result.
This is the precise relation between the executed model and the panicking
source write `accumulated[slot]`. -/
theorem indexed_checked_exact (filter : Element) (terms buffer : List Element) :
    addIndexedChecked filter 0 terms buffer =
      if terms.length ≤ buffer.length then some (addIndexed filter 0 terms buffer) else none := by
  split
  · exact indexed_checked_bounded filter 0 terms buffer (by simpa using ‹_›)
  · rename_i hgt
    refine indexed_checked_overflow filter 0 terms buffer (by omega) ?_
    intro he
    subst he
    simp at hgt

theorem slots_length (filter : Element) (buffer terms : List Element) :
    (addSlots filter buffer terms).length = buffer.length := by
  rw [← indexed_equals_lockstep,indexed_length]

theorem slots_lookup (filter : Element) (buffer terms : List Element) (index : Nat)
    (hi : index < buffer.length) :
    (addSlots filter buffer terms).getD index 0 = buffer.getD index 0+filter*terms.getD index 0 := by
  induction buffer generalizing terms index with
  | nil => simp at hi
  | cons b bs ih =>
      cases terms with
      | nil => simp [addSlots]
      | cons t ts =>
          cases index with
          | zero => rfl
          | succ index =>
              simpa only [addSlots,List.getD_cons_succ] using ih ts index (by simpa using hi)

theorem slots_preserve_trailing (filter : Element) (buffer terms : List Element) (index : Nat)
    (hi : terms.length ≤ index) :
    (addSlots filter buffer terms).getD index 0 = buffer.getD index 0 := by
  induction buffer generalizing terms index with
  | nil => cases terms <;> rfl
  | cons b bs ih =>
      cases terms with
      | nil => rfl
      | cons t ts =>
          cases index with
          | zero => simp at hi
          | succ index =>
              simpa only [addSlots,List.getD_cons_succ] using ih ts index (by simpa using hi)

/-- Executed-loop form of `slots_lookup`: every in-range slot of the indexed
execution is the old slot plus `filter` times the term at that slot (zero when
the term list is shorter). -/
theorem indexed_lookup (filter : Element) (terms buffer : List Element) (index : Nat)
    (hi : index < buffer.length) :
    (addIndexed filter 0 terms buffer).getD index 0 = buffer.getD index 0+filter*terms.getD index 0 := by
  rw [indexed_equals_lockstep]
  exact slots_lookup filter buffer terms index hi

/-- Executed-loop form of `slots_preserve_trailing`: slots at or beyond the
term count are untouched by the indexed execution. -/
theorem indexed_preserve_trailing (filter : Element) (terms buffer : List Element) (index : Nat)
    (hi : terms.length ≤ index) :
    (addIndexed filter 0 terms buffer).getD index 0 = buffer.getD index 0 := by
  rw [indexed_equals_lockstep]
  exact slots_preserve_trailing filter buffer terms index hi

theorem horner_slots (alpha filter : Element) (buffer terms : List Element)
    (h : terms.length ≤ buffer.length) :
    horner alpha (addSlots filter buffer terms) = horner alpha buffer+filter*horner alpha terms := by
  induction buffer generalizing terms with
  | nil => have ht : terms=[] := List.length_eq_zero.mp (by simpa using h); subst terms; simp [addSlots,horner]
  | cons b bs ih =>
      cases terms with
      | nil => simp [addSlots,horner]
      | cons t ts =>
          simp only [addSlots,horner,ih ts (by simpa using h)]
          ring

theorem reduce_indexed (alpha filter : Element) (buffer terms : List Element)
    (h : terms.length ≤ buffer.length) :
    reduce alpha (addIndexed filter 0 terms buffer) = reduce alpha buffer+filter*reduce alpha terms := by
  simp only [reduce_horner,indexed_equals_lockstep,horner_slots alpha filter buffer terms h]

theorem zero_filter_keeps_buffer (buffer terms : List Element) : addIndexed 0 0 terms buffer=buffer := by
  rw [indexed_equals_lockstep]
  induction buffer generalizing terms with
  | nil => cases terms <;> rfl
  | cons b bs ih => cases terms <;> simp [addSlots,ih]

theorem reduce_zero_padding (alpha : Element) (width : Nat) : reduce alpha (List.replicate width 0)=0 := by
  rw [reduce_horner]
  induction width with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,horner,ih]

theorem ordinary_variable_length_slots :
    addIndexed 7 0 [2,3] [10,20,30] = ([24,41,30] : List Element) := by decide

theorem checked_overflow_fails_concretely :
    addIndexedChecked 7 0 [2,3,4] [10,20] = none := by decide

theorem zero_alpha_selects_first_slot :
    reduce 0 [3,4,5] = (3 : Element) := by decide

end Audit.Wire3.GateSlotAlgebra
