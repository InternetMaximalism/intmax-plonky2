import Audit.Wire3.Arithmetic

/-!
Wire-v3 packed constituent folding, based on becfe98e.

`layer`/`foldLayers` specify the ordered _foldFlat loop in PackedClaimExt3.sol:
adjacent even/odd pairs, LSB-first challenges, a missing odd partner is zero.
The proofs relate this sparse implementation to an infinite zero-extended table
and hence to Rust prover_v2::fold_ext3_claim's fully zero-padded table. This is a
functional loop model, not a proof of Yul pointer arithmetic or in-place memory
refinement. Input schema/canonical validation is performed by callers; all
nonempty arithmetic layers produce canonical values even for raw Nat inputs.

`packedPoint` models prover_v2/verifier_v2::packed_ext3_point; `whirPoint` models
commitment/whir_pcs.rs::prove_grouped_with_eval's complete coordinate reversal.
No randomness, binding, cryptographic soundness, primality or EVM equivalence is
assumed or concluded by these deterministic bookkeeping theorems.
-/
namespace Audit.Wire3.Packed
open Audit.Wire3.Arithmetic

def layer (r : Ext3) : List Ext3 → List Ext3
  | [] => []
  | [a] => [butterfly a zero r]
  | a :: b :: rest => butterfly a b r :: layer r rest

def foldLayers : List Ext3 → List Ext3 → List Ext3
  | [], values => values
  | r :: rs, values => foldLayers rs (layer r values)

def fold (values point : List Ext3) : Ext3 := (foldLayers point values).getD 0 zero
def lookup (values : List Ext3) : Nat → Ext3 := fun i => values.getD i zero
def tableLayer (r : Ext3) (t : Nat → Ext3) : Nat → Ext3 :=
  fun i => butterfly (t (2 * i)) (t (2 * i + 1)) r

def tableFold : List Ext3 → (Nat → Ext3) → (Nat → Ext3)
  | [], t => t
  | r :: rs, t => tableFold rs (tableLayer r t)

theorem layer_length (r : Ext3) : ∀ values : List Ext3,
    (layer r values).length = (values.length + 1) / 2
  | [] => rfl
  | [_] => by simp [layer]
  | a :: b :: rest => by
      simp only [layer, List.length_cons, layer_length r rest]
      omega

theorem layer_canonical (r : Ext3) : ∀ (values : List Ext3) (v : Ext3),
    v ∈ layer r values → Canonical v
  | [], _, h => by contradiction
  | [a], _, h => by
      simp only [layer, List.mem_singleton] at h
      subst h
      exact butterfly_canonical _ _ _
  | a :: b :: rest, v, h => by
      simp only [layer, List.mem_cons] at h
      rcases h with h | h
      · subst h
        exact butterfly_canonical _ _ _
      · exact layer_canonical r rest v h

theorem layers_canonical (point values : List Ext3)
    (h : ∀ v ∈ values, Canonical v) : ∀ v ∈ foldLayers point values, Canonical v := by
  induction point generalizing values with
  | nil => exact h
  | cons r _ ih => exact ih (layer r values) (layer_canonical r values)

theorem lookup_canonical (values : List Ext3) (h : ∀ v ∈ values, Canonical v)
    (i : Nat) : Canonical (lookup values i) := by
  induction values generalizing i with
  | nil => exact zero_canonical
  | cons a rest ih =>
      cases i with
      | zero => exact h a (by simp)
      | succ i =>
          exact ih (fun v hv => h v (by simp [hv])) i

theorem fold_canonical (point values : List Ext3)
    (h : ∀ v ∈ values, Canonical v) : Canonical (fold values point) :=
  lookup_canonical _ (layers_canonical point values h) 0

theorem nonempty_point_fold_canonical (r : Ext3) (rs values : List Ext3) :
    Canonical (fold values (r :: rs)) :=
  fold_canonical rs (layer r values) (layer_canonical r values)

theorem layer_lookup (r : Ext3) : ∀ (values : List Ext3) (i : Nat),
    lookup (layer r values) i = tableLayer r (lookup values) i
  | [], i => by simp [lookup, layer, tableLayer, butterfly_zero_pair]
  | [a], 0 => rfl
  | [a], i + 1 => by
      simp [lookup, layer, tableLayer, Nat.mul_succ, Nat.add_assoc, butterfly_zero_pair]
  | a :: b :: rest, 0 => rfl
  | a :: b :: rest, i + 1 => by
      simpa [lookup, layer, tableLayer, Nat.mul_succ, Nat.add_assoc] using
        layer_lookup r rest i

theorem layers_lookup (point values : List Ext3) :
    lookup (foldLayers point values) = tableFold point (lookup values) := by
  induction point generalizing values with
  | nil => rfl
  | cons r rs ih =>
      simp only [foldLayers, tableFold, ih]
      have h : lookup (layer r values) = tableLayer r (lookup values) := by
        funext i
        exact layer_lookup r values i
      rw [h]

theorem replicate_zero_lookup (n i : Nat) :
    lookup (List.replicate n zero) i = zero := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [lookup, List.replicate] using ih i

theorem zero_padding_lookup (values : List Ext3) (padding i : Nat) :
    lookup (values ++ List.replicate padding zero) i = lookup values i := by
  induction values generalizing i with
  | nil => exact replicate_zero_lookup padding i
  | cons a rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [lookup] using ih i

/-- In particular, padding to width.next_power_of_two in Rust does not alter
    the result of the Solidity sparse-prefix algorithm, for any challenge list. -/
theorem sparse_fold_equals_zero_padded_fold (values point : List Ext3) (padding : Nat) :
    fold (values ++ List.replicate padding zero) point = fold values point := by
  change lookup (foldLayers point (values ++ List.replicate padding zero)) 0 =
    lookup (foldLayers point values) 0
  rw [layers_lookup, layers_lookup]
  have h : lookup (values ++ List.replicate padding zero) = lookup values := by
    funext i
    exact zero_padding_lookup values padding i
  rw [h]

def padToCapacity (values : List Ext3) (capacity : Nat) : List Ext3 :=
  values ++ List.replicate (capacity - values.length) zero

theorem padded_capacity_exact (values : List Ext3) (capacity : Nat)
    (h : values.length ≤ capacity) : (padToCapacity values capacity).length = capacity := by
  simp only [padToCapacity, List.length_append, List.length_replicate]
  omega

theorem padded_capacity_fold (values point : List Ext3) (capacity : Nat) :
    fold (padToCapacity values capacity) point = fold values point :=
  sparse_fold_equals_zero_padded_fold values point (capacity - values.length)

theorem layer_even_shape (r : Ext3) (values : List Ext3) (n : Nat)
    (h : values.length = 2 * n) : (layer r values).length = n := by
  rw [layer_length, h]
  omega

theorem full_table_final_shape (point values : List Ext3)
    (h : values.length = 2 ^ point.length) : (foldLayers point values).length = 1 := by
  induction point generalizing values with
  | nil => simpa [foldLayers] using h
  | cons r rs ih =>
      apply ih
      apply layer_even_shape
      simpa [List.length_cons, Nat.pow_succ, Nat.mul_comm] using h

theorem empty_fold (point : List Ext3) : fold [] point = zero := by
  have h : foldLayers point [] = [] := by
    induction point with
    | nil => rfl
    | cons r rs ih => simpa [foldLayers, layer] using ih
  simp [fold, h]

theorem one_bit_exact (a b r : Ext3) : fold [a, b] [r] = butterfly a b r := rfl

theorem two_bits_exact_lsb_first (a b c d r0 r1 : Ext3) :
    fold [a, b, c, d] [r0, r1] =
      butterfly (butterfly a b r0) (butterfly c d r0) r1 := rfl

theorem odd_prefix_exact (a b c r0 r1 : Ext3) :
    fold [a, b, c] [r0, r1] =
      butterfly (butterfly a b r0) (butterfly c zero r0) r1 := rfl

/-- Agreed coordinates on the relevant initial prefix remain agreed after
    folding; changes outside that prefix cannot enter its descendant cells. -/
theorem tableFold_prefix_local (point : List Ext3) (t u : Nat → Ext3) (limit : Nat)
    (h : ∀ i, i < limit * 2 ^ point.length → t i = u i) :
    ∀ i, i < limit → tableFold point t i = tableFold point u i := by
  induction point generalizing t u with
  | nil => simpa [tableFold] using h
  | cons r rs ih =>
      apply ih
      intro i hi
      unfold tableLayer
      have bound : limit * 2 ^ (r :: rs).length = (limit * 2 ^ rs.length) * 2 := by
        simp [List.length_cons, Nat.pow_succ, Nat.mul_assoc]
      rw [h (2 * i) (by rw [bound]; omega), h (2 * i + 1) (by rw [bound]; omega)]

theorem fold_depends_on_exact_input_prefix (point values other : List Ext3)
    (h : ∀ i, i < 2 ^ point.length → lookup values i = lookup other i) :
    fold values point = fold other point := by
  change lookup (foldLayers point values) 0 = lookup (foldLayers point other) 0
  rw [layers_lookup, layers_lookup]
  exact tableFold_prefix_local point _ _ 1 (by simpa using h) 0 (by decide)

def packedPoint (row index : List Ext3) : List Ext3 := row ++ index
def whirPoint (row index : List Ext3) : List Ext3 := (packedPoint row index).reverse

theorem packed_point_length (row index : List Ext3) :
    (packedPoint row index).length = row.length + index.length := by simp [packedPoint]

/-- Whole reversal puts reversed INDEX variables first in WHIR order. -/
theorem whir_point_exact_order (row index : List Ext3) :
    whirPoint row index = index.reverse ++ row.reverse := by
  simp [whirPoint, packedPoint, Nat.add_comm]

theorem whir_point_roundtrip (row index : List Ext3) :
    (whirPoint row index).reverse = packedPoint row index := by simp [whirPoint]

theorem whir_point_length (row index : List Ext3) :
    (whirPoint row index).length = row.length + index.length := by
  simp [whirPoint, packedPoint, Nat.add_comm]

end Audit.Wire3.Packed
