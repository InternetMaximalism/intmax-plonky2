import Audit.Wire3.PiSharedBits

/-!
Concrete row-local public-input cache from OuterLogupExt3Verifier.
Entries retain insertion order, lookup searches newest-to-oldest, duplicates
accumulate in their existing row, and eta is not advanced after the final PI.
The final loop uses the concrete shared-bit equality calculation.
The entries list represents the initialized prefix of the source's count-sized
scratch arrays; allocation and unused capacity are not modeled. The first mask
update computes anchor XOR itself, proved to leave the mask unchanged; Solidity
skips this no-op. The first-cache-row theorem identifies this same anchor.

The input adapter is exactly Norm.targetAt and retains PI order and duplicate
map entries. Bounds/canonicality have the same Norm.shapeValid precondition as
the original direct model; totalized byte/wire reads outside it are not an EVM
decoder or memory-safety claim. No evaluator callback or assumed cache identity
is used. These are deterministic model equivalences, not PCS soundness.
-/
namespace Audit.Wire3.PiCache
open Verifier
open Algebra
open PiSharedBits

structure Entry where
  row : Nat
  amount : Ext3
  deriving DecidableEq

/-- Recursing into the suffix before considering the head searches descending
    indices, exactly the source's decrement-before-test cache lookup. -/
def newestIndex (row : Nat) : List Entry → Option Nat
  | [] => none
  | entry :: rest =>
      match newestIndex row rest with
      | some i => some (i + 1)
      | none => if entry.row = row then some 0 else none

def cachedRowIndex (row : Nat) (entries : List Entry) : Nat × List Entry :=
  match newestIndex row entries with
  | some i => (i, entries)
  | none => (entries.length, entries ++ [⟨row, zero⟩])

def addAt (amount : Ext3) : Nat → List Entry → List Entry
  | _, [] => []
  | 0, entry :: rest => ⟨entry.row, add entry.amount amount⟩ :: rest
  | i + 1, entry :: rest => entry :: addAt amount i rest

def cacheAdd (row : Nat) (amount : Ext3) (entries : List Entry) : List Entry :=
  let registered := cachedRowIndex row entries
  addAt amount registered.1 registered.2

def rowKeys (entries : List Entry) : List Nat := entries.map Entry.row

theorem newest_index_points_to_row (row index : Nat) (entries : List Entry)
    (h : newestIndex row entries = some index) :
    ∃ entry, entries.get? index = some entry ∧ entry.row = row := by
  induction entries generalizing index with
  | nil => simp [newestIndex] at h
  | cons entry rest ih =>
    cases hr : newestIndex row rest with
    | some i =>
      simp only [newestIndex, hr, Option.some.injEq] at h
      subst index
      obtain ⟨found, hf, he⟩ := ih i hr
      exact ⟨found, hf, he⟩
    | none =>
      simp only [newestIndex, hr] at h
      split at h
      · cases h
        exact ⟨entry, rfl, ‹entry.row = row›⟩
      · contradiction

theorem registered_index_points_to_row (row : Nat) (entries : List Entry) :
    ∃ entry, (cachedRowIndex row entries).2.get? (cachedRowIndex row entries).1 = some entry ∧ entry.row = row := by
  cases hi : newestIndex row entries with
  | some i => simpa only [cachedRowIndex, hi] using newest_index_points_to_row row i entries hi
  | none =>
    refine ⟨⟨row, zero⟩, ?_, rfl⟩
    simp [cachedRowIndex, hi]

theorem add_at_preserves_rows (amount : Ext3) (index : Nat) (entries : List Entry) :
    rowKeys (addAt amount index entries) = rowKeys entries := by
  induction entries generalizing index with
  | nil => simp [addAt, rowKeys]
  | cons entry rest ih =>
    cases index with
    | zero => rfl
    | succ index =>
      exact congrArg (List.cons entry.row) (ih index)

theorem cache_add_rows (row : Nat) (amount : Ext3) (entries : List Entry) :
    rowKeys (cacheAdd row amount entries) =
      if (newestIndex row entries).isSome then rowKeys entries else rowKeys entries ++ [row] := by
  unfold cacheAdd
  rw [add_at_preserves_rows]
  cases hi : newestIndex row entries <;> simp [cachedRowIndex, hi, rowKeys]

theorem cache_add_row_membership (row : Nat) (amount : Ext3) (entries : List Entry) (entry : Entry)
    (h : entry ∈ cacheAdd row amount entries) :
    entry.row = row ∨ ∃ old ∈ entries, old.row = entry.row := by
  have hk : entry.row ∈ rowKeys (cacheAdd row amount entries) := List.mem_map.mpr ⟨entry, h, rfl⟩
  rw [cache_add_rows] at hk
  cases hi : newestIndex row entries with
  | some i =>
    simp only [hi, Option.isSome, ↓reduceIte] at hk
    exact Or.inr (List.mem_map.mp hk)
  | none =>
    simp only [hi, Option.isSome, ↓reduceIte, List.mem_append, List.mem_singleton] at hk
    rcases hk with hold | hnew
    · exact Or.inr (List.mem_map.mp hold)
    · exact Or.inl hnew

/-- A right-associated sum used only in proofs of the concrete ordered final
    loop; no equality weight is assumed or supplied as a callback. -/
def weightedSum (point : List Ext3) : List Entry → Ext3
  | [] => zero
  | entry :: rest => add (mul (Norm.booleanRowEq entry.row point) entry.amount) (weightedSum point rest)

theorem weighted_sum_append (point : List Ext3) (a b : List Entry) :
    weightedSum point (a ++ b) = add (weightedSum point a) (weightedSum point b) := by
  induction a with
  | nil => simp [weightedSum, vzero_add]
  | cons entry rest ih => simp [weightedSum, ih, vadd_assoc]

theorem weighted_sum_add_at (point : List Ext3) (entries : List Entry) (index : Nat) (entry : Entry)
    (amount : Ext3) (h : entries.get? index = some entry) :
    weightedSum point (addAt amount index entries) =
      add (weightedSum point entries) (mul (Norm.booleanRowEq entry.row point) amount) := by
  induction entries generalizing index with
  | nil => simp at h
  | cons head rest ih =>
    cases index with
    | zero =>
      cases h
      simp only [addAt, weightedSum, vmul_add]
      simp only [vadd_assoc, vadd_comm, vadd_left_comm]
    | succ index =>
      simp only [addAt, weightedSum]
      rw [ih index h, vadd_assoc]

theorem registering_zero_preserves_sum (point : List Ext3) (row : Nat) (entries : List Entry) :
    weightedSum point (cachedRowIndex row entries).2 = weightedSum point entries := by
  cases hi : newestIndex row entries with
  | some i => simp [cachedRowIndex, hi]
  | none => simp [cachedRowIndex, hi, weighted_sum_append, weightedSum, vmul_zero, vadd_zero]

theorem weighted_sum_cache_add (point : List Ext3) (row : Nat) (amount : Ext3) (entries : List Entry) :
    weightedSum point (cacheAdd row amount entries) =
      add (weightedSum point entries) (mul (Norm.booleanRowEq row point) amount) := by
  obtain ⟨entry, hi, hr⟩ := registered_index_points_to_row row entries
  unfold cacheAdd
  rw [weighted_sum_add_at point _ _ entry amount hi, hr, registering_zero_preserves_sum]

structure CacheState where
  entries : List Entry
  varying : Nat
  etaPower : Ext3

def start : CacheState := ⟨[], 0, Norm.one⟩

def step (wireMap : Bytes) (witness : List Ext3) (anchor : Nat) (eta : Ext3) (hasNext : Bool)
    (pair : Nat × Base) (state : CacheState) : CacheState :=
  let target := Norm.targetAt wireMap pair.1
  let term := sub (witness.getD target.column zero) (Norm.embed pair.2.val)
  ⟨cacheAdd target.row (mul state.etaPower term) state.entries,
   extendMask state.varying anchor target.row,
   if hasNext then mul state.etaPower eta else state.etaPower⟩

def runCache (wireMap : Bytes) (witness : List Ext3) (anchor : Nat) (eta : Ext3) :
    List (Nat × Base) → CacheState → CacheState
  | [], state => state
  | pair :: rest, state => runCache wireMap witness anchor eta rest
      (step wireMap witness anchor eta (!rest.isEmpty) pair state)

def MaskInvariant (anchor : Nat) (state : CacheState) : Prop :=
  ∀ entry ∈ state.entries, ∀ bit, state.varying.testBit bit = false → anchor.testBit bit = entry.row.testBit bit

theorem initial_mask_invariant (anchor : Nat) : MaskInvariant anchor start := by
  simp [MaskInvariant, start]

theorem step_preserves_mask_invariant (wireMap : Bytes) (witness : List Ext3) (anchor : Nat)
    (eta : Ext3) (hasNext : Bool) (pair : Nat × Base) (state : CacheState)
    (h : MaskInvariant anchor state) : MaskInvariant anchor (step wireMap witness anchor eta hasNext pair state) := by
  intro entry he bit hb
  have hm := (extend_mask_false_iff state.varying anchor (Norm.targetAt wireMap pair.1).row bit).mp hb
  rcases cache_add_row_membership _ _ _ entry he with hnew | ⟨old, hold, heq⟩
  · simpa [hnew] using hm.2
  · rw [← heq]
    exact h old hold bit hm.1

theorem run_preserves_mask_invariant (wireMap : Bytes) (witness : List Ext3) (anchor : Nat)
    (eta : Ext3) (pairs : List (Nat × Base)) (state : CacheState) (h : MaskInvariant anchor state) :
    MaskInvariant anchor (runCache wireMap witness anchor eta pairs state) := by
  induction pairs generalizing state with
  | nil => exact h
  | cons pair rest ih =>
    exact ih _ (step_preserves_mask_invariant _ _ _ _ _ _ _ h)

theorem step_sum_matches_direct (wireMap : Bytes) (witness point : List Ext3) (anchor : Nat)
    (eta : Ext3) (hasNext : Bool) (pair : Nat × Base) (state : CacheState) (processed : Nat) :
    weightedSum point (step wireMap witness anchor eta hasNext pair state).entries =
      (Norm.piStep wireMap witness point eta ⟨weightedSum point state.entries, state.etaPower, processed⟩ pair).binding := by
  simp only [step, Norm.piStep, weighted_sum_cache_add]
  rw [← vmul_assoc, vmul_comm (Norm.booleanRowEq _ _) state.etaPower]

set_option maxRecDepth 4096 in
theorem cache_loop_matches_direct (wireMap : Bytes) (witness point : List Ext3) (anchor : Nat)
    (eta : Ext3) (pairs : List (Nat × Base)) (state : CacheState) (direct : Norm.PiState)
    (hbinding : weightedSum point state.entries = direct.binding) (hpower : state.etaPower = direct.etaPower) :
    weightedSum point (runCache wireMap witness anchor eta pairs state).entries =
      (pairs.foldl (Norm.piStep wireMap witness point eta) direct).binding := by
  induction pairs generalizing state direct with
  | nil => exact hbinding
  | cons pair rest ih =>
    rw [runCache, List.foldl_cons]
    have hs := step_sum_matches_direct wireMap witness point anchor eta (!rest.isEmpty) pair state direct.processed
    have he : weightedSum point (step wireMap witness anchor eta (!rest.isEmpty) pair state).entries =
        (Norm.piStep wireMap witness point eta direct pair).binding := by
      simpa [hbinding, hpower] using hs
    cases rest with
    | nil => exact he
    | cons next tail =>
      have hp : (step wireMap witness anchor eta true pair state).etaPower =
          (Norm.piStep wireMap witness point eta direct pair).etaPower := by
        change mul state.etaPower eta = mul direct.etaPower eta
        exact congrArg (fun power => mul power eta) hpower
      have hh := ih (step wireMap witness anchor eta true pair state)
        (Norm.piStep wireMap witness point eta direct pair) he hp
      exact hh

def finish (anchor : Nat) (point : List Ext3) (state : CacheState) : Ext3 :=
  state.entries.foldl (fun binding entry =>
    add binding (mul (factoredEq anchor entry.row point state.varying) entry.amount)) zero

theorem finish_loop_matches_weighted_sum (anchor mask : Nat) (point : List Ext3)
    (entries : List Entry) (initial : Ext3)
    (h : ∀ entry ∈ entries, ∀ bit, mask.testBit bit = false → anchor.testBit bit = entry.row.testBit bit) :
    entries.foldl (fun binding entry => add binding (mul (factoredEq anchor entry.row point mask) entry.amount)) initial =
      add initial (weightedSum point entries) := by
  induction entries generalizing initial with
  | nil => simp [weightedSum, vadd_zero]
  | cons entry rest ih =>
    have he := shared_bit_factoring_exact anchor entry.row point mask (h entry (by simp))
    simp only [List.foldl_cons, he, weightedSum]
    rw [ih _ (by intro e hem; exact h e (by simp [hem])), vadd_assoc]

theorem finish_uses_actual_row_equalities (anchor : Nat) (point : List Ext3) (state : CacheState)
    (h : MaskInvariant anchor state) : finish anchor point state = weightedSum point state.entries := by
  unfold finish
  rw [finish_loop_matches_weighted_sum _ _ _ _ _ h, vzero_add]

def publicInputBinding (c : Config) (terminal : NormTerminalInput) (point : List Ext3) (eta : Ext3) : Ext3 :=
  if terminal.publicInputs.isEmpty then zero else
    let anchor := (Norm.targetAt c.publicInputWireMap 0).row
    finish anchor point (runCache c.publicInputWireMap terminal.witness anchor eta terminal.publicInputs.enum start)

theorem cached_binding_equals_direct_norm (c : Config) (terminal : NormTerminalInput)
    (point : List Ext3) (eta : Ext3) :
    publicInputBinding c terminal point eta = Norm.publicInputBinding c terminal point eta := by
  unfold publicInputBinding
  split
  · have hnil : terminal.publicInputs = [] := by
      cases hp : terminal.publicInputs <;> simp_all
    exact (Norm.public_input_empty_is_zero c terminal point eta hnil).symm
  · rw [finish_uses_actual_row_equalities _ _ _ (run_preserves_mask_invariant _ _ _ _ _ _ (initial_mask_invariant _))]
    exact cache_loop_matches_direct _ _ _ _ _ _ start Norm.piStart rfl rfl

theorem newest_index_none_iff (row : Nat) (entries : List Entry) :
    newestIndex row entries = none ↔ ∀ entry ∈ entries, entry.row ≠ row := by
  induction entries with
  | nil => simp [newestIndex]
  | cons entry rest ih =>
    cases hi : newestIndex row rest with
    | none =>
      have ht := ih.mp hi
      by_cases he : entry.row = row
      · simp [newestIndex, hi, he]
      · simp only [newestIndex, hi, he, ↓reduceIte, true_iff, List.mem_cons, forall_eq_or_imp]
        exact ⟨he, ht⟩
    | some index =>
      have hnot : ¬ ∀ e ∈ rest, e.row ≠ row := by
        intro h
        have hn := ih.mpr h
        rw [hi] at hn
        contradiction
      simp [newestIndex, hi, hnot]

theorem newest_index_has_no_later_match (row index : Nat) (entries : List Entry)
    (h : newestIndex row entries = some index) :
    ∀ j entry, index < j → entries.get? j = some entry → entry.row ≠ row := by
  induction entries generalizing index with
  | nil => simp [newestIndex] at h
  | cons head rest ih =>
    cases hr : newestIndex row rest with
    | some i =>
      simp only [newestIndex, hr, Option.some.injEq] at h
      subst index
      intro j entry hj he
      cases j with
      | zero => omega
      | succ j => exact ih i hr j entry (by omega) he
    | none =>
      simp only [newestIndex, hr] at h
      split at h
      · cases h
        intro j entry hj he
        cases j with
        | zero => omega
        | succ j =>
          apply (newest_index_none_iff row rest).mp hr entry
          exact List.get?_mem (show rest.get? j = some entry from he)
      · contradiction

theorem cache_add_preserves_first_row (row anchor : Nat) (amount : Ext3) (entries : List Entry)
    (h : (rowKeys entries).head? = some anchor) :
    (rowKeys (cacheAdd row amount entries)).head? = some anchor := by
  rw [cache_add_rows]
  split
  · exact h
  · cases hk : rowKeys entries with
    | nil => simp [hk] at h
    | cons first rest => simpa [hk] using h

theorem run_preserves_first_row (wireMap : Bytes) (witness : List Ext3) (anchor : Nat) (eta : Ext3)
    (pairs : List (Nat × Base)) (state : CacheState)
    (h : (rowKeys state.entries).head? = some anchor) :
    (rowKeys (runCache wireMap witness anchor eta pairs state).entries).head? = some anchor := by
  induction pairs generalizing state with
  | nil => exact h
  | cons pair rest ih =>
    apply ih
    exact cache_add_preserves_first_row _ _ _ _ h

theorem first_cached_row_is_first_input_row (wireMap : Bytes) (witness : List Ext3) (eta : Ext3)
    (pair : Nat × Base) (rest : List (Nat × Base)) :
    (rowKeys (runCache wireMap witness (Norm.targetAt wireMap pair.1).row eta (pair :: rest) start).entries).head? =
      some (Norm.targetAt wireMap pair.1).row := by
  rw [runCache]
  exact run_preserves_first_row _ _ _ _ _ _ rfl

theorem first_mask_operation_is_source_noop (wireMap : Bytes) (witness : List Ext3) (eta : Ext3)
    (pair : Nat × Base) (hasNext : Bool) :
    (step wireMap witness (Norm.targetAt wireMap pair.1).row eta hasNext pair start).varying = 0 := by
  exact first_row_mask_unchanged 0 _

theorem cache_mask_is_actual_or_of_xors (wireMap : Bytes) (witness : List Ext3) (anchor : Nat) (eta : Ext3)
    (pairs : List (Nat × Base)) (state : CacheState) :
    (runCache wireMap witness anchor eta pairs state).varying =
      varyingMaskFrom anchor (pairs.map fun pair => (Norm.targetAt wireMap pair.1).row) state.varying := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    rw [runCache, ih]
    rfl

theorem final_eta_update_is_skipped (wireMap : Bytes) (witness : List Ext3) (anchor : Nat) (eta : Ext3)
    (pairs : List (Nat × Base)) (state : CacheState) :
    (runCache wireMap witness anchor eta pairs state).etaPower =
      Norm.multiplyRepeated state.etaPower eta (pairs.length - 1) := by
  induction pairs generalizing state with
  | nil => simp [runCache, Norm.multiplyRepeated]
  | cons pair rest ih =>
    rw [runCache, ih]
    cases rest with
    | nil => rfl
    | cons next tail =>
      simp only [List.length_cons, Nat.add_sub_cancel, step, List.isEmpty, Bool.not_false,
        ↓reduceIte, Norm.multiplyRepeated]

/-- Empty PIs return zero without reading a cache or applying an equality factor. -/
theorem empty_public_inputs (c : Config) (terminal : NormTerminalInput) (point : List Ext3) (eta : Ext3)
    (h : terminal.publicInputs = []) : publicInputBinding c terminal point eta = zero := by
  simp [publicInputBinding, h]

/-- Arbitrary ordering and repeated row/column targets. The third target has a
    non-base witness value, so this is not a base-projection-only example. -/
def exampleMap : Bytes := [2, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0]
def exampleNonbase : Ext3 := ⟨⟨0, 1, 0⟩, by unfold Arithmetic.Canonical; decide⟩
def exampleTerminal : NormTerminalInput :=
  ⟨[], [Norm.embed 7, exampleNonbase], [], [base 3, base 4, base 1, base 2]⟩

def exampleConfig : Config :=
  { testConfig with
    publicInputWireMap := exampleMap, numPublicInputs := 4,
    degreeBits := 2, numRouted := 2, numWires := 2 }
def examplePoint : List Ext3 := [Norm.embed 3, Norm.embed 5]

theorem normal_duplicate_and_unsorted_rows :
    rowKeys (runCache exampleMap exampleTerminal.witness 2 (Norm.embed 2) exampleTerminal.publicInputs.enum start).entries =
      [2, 0, 1] := by decide

theorem newest_search_uses_last_matching_index :
    newestIndex 3 [⟨3, zero⟩, ⟨1, zero⟩, ⟨3, Norm.one⟩] = some 2 := by decide

theorem duplicate_row_accumulation_retains_both_terms (a b : Ext3) :
    cacheAdd 3 b (cacheAdd 3 a []) = [⟨3, add a b⟩] := by
  simp [cacheAdd, cachedRowIndex, newestIndex, addAt, vzero_add]

theorem duplicate_unsorted_example_exact :
    publicInputBinding exampleConfig exampleTerminal examplePoint (Norm.embed 2) =
      Norm.publicInputBinding exampleConfig exampleTerminal examplePoint (Norm.embed 2) :=
  cached_binding_equals_direct_norm _ _ _ _

theorem zero_eta_example_exact :
    publicInputBinding exampleConfig exampleTerminal examplePoint zero =
      Norm.publicInputBinding exampleConfig exampleTerminal examplePoint zero :=
  cached_binding_equals_direct_norm _ _ _ _

theorem duplicate_unsorted_example_value :
    publicInputBinding exampleConfig exampleTerminal examplePoint (Norm.embed 2) =
      add (Norm.embed (modulus - 432)) (scalar exampleNonbase (modulus - 40)) := by decide

theorem zero_eta_keeps_first_input_only :
    publicInputBinding exampleConfig exampleTerminal examplePoint zero = Norm.embed (modulus - 40) := by decide

end Audit.Wire3.PiCache
