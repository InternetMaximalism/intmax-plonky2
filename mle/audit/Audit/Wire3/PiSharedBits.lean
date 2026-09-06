import Audit.Wire3.Algebra

/-!
Concrete shared-bit public-input equality factoring from
OuterLogupExt3Verifier._publicInputBinding/_eqBooleanRowSelectedBits.
Masks are actual Nat OR/XOR values, not a selection oracle. PI rows decoded by
Norm.targetAt are 16-bit values; hence the source's uint256 bitwise operations
have the same mathematical bit values. Coordinate multiplication uses the same
canonical Ext3 operations as Norm, with proved concrete algebra.

Theorems establish shared/varying factorization and mask membership. They do
not establish EVM memory, parser, circuit witness, or cryptographic soundness.
-/
namespace Audit.Wire3.PiSharedBits
open Verifier
open Algebra

def extendMask (mask anchor row : Nat) : Nat := mask ||| (anchor ^^^ row)
def varyingMaskFrom (anchor : Nat) (rows : List Nat) (initial : Nat) : Nat :=
  rows.foldl (fun mask row => extendMask mask anchor row) initial
def varyingMask (anchor : Nat) (rows : List Nat) : Nat := varyingMaskFrom anchor rows 0

theorem extend_mask_false_iff (mask anchor row bit : Nat) :
    (extendMask mask anchor row).testBit bit = false ↔
      mask.testBit bit = false ∧ anchor.testBit bit = row.testBit bit := by
  simp only [extendMask, Nat.testBit_or, Nat.testBit_xor]
  cases mask.testBit bit <;> cases anchor.testBit bit <;> cases row.testBit bit <;> decide

theorem anchor_xor_self (anchor : Nat) : anchor ^^^ anchor = 0 := by
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [Nat.testBit_xor]
  simp [Nat.testBit_to_div_mod]

theorem first_row_mask_unchanged (mask anchor : Nat) : extendMask mask anchor anchor = mask := by
  simp [extendMask, anchor_xor_self, Nat.or_zero]

theorem varying_mask_false_iff (anchor initial bit : Nat) (rows : List Nat) :
    (varyingMaskFrom anchor rows initial).testBit bit = false ↔
      initial.testBit bit = false ∧ ∀ row ∈ rows, anchor.testBit bit = row.testBit bit := by
  induction rows generalizing initial with
  | nil => simp [varyingMaskFrom]
  | cons row rows ih =>
    change (varyingMaskFrom anchor rows (extendMask initial anchor row)).testBit bit = false ↔ _
    simp only [ih, extend_mask_false_iff,
      List.mem_cons, forall_eq_or_imp, and_assoc]

theorem mask_contains_every_row_difference (anchor bit : Nat) (rows : List Nat) (row : Nat)
    (hr : row ∈ rows) (hm : (varyingMask anchor rows).testBit bit = false) :
    anchor.testBit bit = row.testBit bit :=
  ((varying_mask_false_iff anchor 0 bit rows).mp hm).2 row hr

theorem boolean_factor_uses_actual_bit (row index : Nat) (x : Ext3) :
    Norm.booleanFactor row index x = if row.testBit index then x else sub Norm.one x := by
  have hmod : row / 2 ^ index % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [Nat.testBit_to_div_mod]
  unfold Norm.booleanFactor
  split <;> split <;> simp_all <;> omega

theorem equal_bits_equal_factors (a b index : Nat) (x : Ext3)
    (h : a.testBit index = b.testBit index) :
    Norm.booleanFactor a index x = Norm.booleanFactor b index x := by
  rw [boolean_factor_uses_actual_bit, boolean_factor_uses_actual_bit, h]

/-- Source loop in ascending point-coordinate order, starting with `initial`. -/
def selected (row mask : Nat) (selectVarying : Bool) : List (Nat × Ext3) → Ext3 → Ext3
  | [], initial => initial
  | pair :: rest, initial =>
      selected row mask selectVarying rest
        (if mask.testBit pair.1 = selectVarying then
          mul initial (Norm.booleanFactor row pair.1 pair.2) else initial)

def fullProduct (row : Nat) (coordinates : List (Nat × Ext3)) (initial : Ext3) : Ext3 :=
  coordinates.foldl (fun acc pair => mul acc (Norm.booleanFactor row pair.1 pair.2)) initial

theorem full_product_cons (row : Nat) (pair : Nat × Ext3) (rest : List (Nat × Ext3)) (initial : Ext3) :
    fullProduct row (pair :: rest) initial = fullProduct row rest
      (mul initial (Norm.booleanFactor row pair.1 pair.2)) := rfl

theorem selected_initial_multiplier (row mask : Nat) (selectVarying : Bool)
    (coordinates : List (Nat × Ext3)) (initial : Ext3) :
    selected row mask selectVarying coordinates initial =
      mul initial (selected row mask selectVarying coordinates Norm.one) := by
  induction coordinates generalizing initial with
  | nil => simp [selected, vmul_one]
  | cons pair rest ih =>
    by_cases h : mask.testBit pair.1 = selectVarying
    · simp only [selected, h, ↓reduceIte, vone_mul]
      rw [ih (mul initial _), ih (Norm.booleanFactor row pair.1 pair.2), vmul_assoc]
    · simp only [selected, h, ↓reduceIte]
      exact ih initial

theorem full_product_initial_multiplier (row : Nat) (coordinates : List (Nat × Ext3)) (initial : Ext3) :
    fullProduct row coordinates initial = mul initial (fullProduct row coordinates Norm.one) := by
  induction coordinates generalizing initial with
  | nil => simp [fullProduct, vmul_one]
  | cons pair rest ih =>
    simp only [full_product_cons, vone_mul]
    rw [ih (mul initial _), ih (Norm.booleanFactor row pair.1 pair.2), vmul_assoc]

theorem multiply_middle_commute (a b c : Ext3) : mul a (mul b c) = mul b (mul a c) := by
  rw [← vmul_assoc, vmul_comm a b, vmul_assoc]

theorem selected_partition_product (row mask : Nat) (coordinates : List (Nat × Ext3)) :
    mul (selected row mask false coordinates Norm.one) (selected row mask true coordinates Norm.one) =
      fullProduct row coordinates Norm.one := by
  induction coordinates with
  | nil => simp [selected, fullProduct, vmul_one]
  | cons pair rest ih =>
    cases h : mask.testBit pair.1
    · simp only [selected, h, Bool.false_eq_true, ↓reduceIte, vone_mul,
        full_product_cons]
      rw [selected_initial_multiplier, full_product_initial_multiplier, vmul_assoc, ih]
    · simp only [selected, h, Bool.true_eq_false, ↓reduceIte, vone_mul,
        full_product_cons]
      rw [selected_initial_multiplier row mask true, full_product_initial_multiplier, multiply_middle_commute, ih]

theorem same_shared_bits_same_product (anchor row mask : Nat) (coordinates : List (Nat × Ext3))
    (h : ∀ pair ∈ coordinates, mask.testBit pair.1 = false → anchor.testBit pair.1 = row.testBit pair.1)
    (initial : Ext3) : selected anchor mask false coordinates initial = selected row mask false coordinates initial := by
  induction coordinates generalizing initial with
  | nil => rfl
  | cons pair rest ih =>
    have ht : ∀ p ∈ rest, mask.testBit p.1 = false → anchor.testBit p.1 = row.testBit p.1 := by
      intro p hp
      exact h p (by simp [hp])
    by_cases hm : mask.testBit pair.1 = false
    · have hf := equal_bits_equal_factors anchor row pair.1 pair.2 (h pair (by simp) hm)
      simp only [selected, hm, ↓reduceIte, hf]
      exact ih ht _
    · simp only [selected, hm, ↓reduceIte]
      exact ih ht _

def eqSelectedBits (row : Nat) (point : List Ext3) (mask : Nat) (selectVarying : Bool) (initial : Ext3) : Ext3 :=
  selected row mask selectVarying point.enum initial

def factoredEq (anchor row : Nat) (point : List Ext3) (mask : Nat) : Ext3 :=
  eqSelectedBits row point mask true (eqSelectedBits anchor point mask false Norm.one)

theorem shared_bit_factoring_exact (anchor row : Nat) (point : List Ext3) (mask : Nat)
    (h : ∀ bit, mask.testBit bit = false → anchor.testBit bit = row.testBit bit) :
    factoredEq anchor row point mask = Norm.booleanRowEq row point := by
  unfold factoredEq eqSelectedBits
  rw [same_shared_bits_same_product anchor row mask point.enum (fun pair _ => h pair.1)]
  rw [selected_initial_multiplier, selected_partition_product]
  rfl

theorem actual_varying_mask_factoring (anchor row : Nat) (point : List Ext3) (rows : List Nat)
    (hr : row ∈ rows) : factoredEq anchor row point (varyingMask anchor rows) = Norm.booleanRowEq row point :=
  shared_bit_factoring_exact anchor row point _
    (fun bit hm => mask_contains_every_row_difference anchor bit rows row hr hm)

theorem duplicate_rows_do_not_create_varying_bits (anchor : Nat) (count : Nat) :
    varyingMask anchor (List.replicate count anchor) = 0 := by
  have hf : ∀ initial, varyingMaskFrom anchor (List.replicate count anchor) initial = initial := by
    induction count with
    | zero => intro initial; rfl
    | succ count ih =>
      intro initial
      simp only [List.replicate_succ, varyingMaskFrom, List.foldl_cons, first_row_mask_unchanged]
      exact ih initial
  exact hf 0

end Audit.Wire3.PiSharedBits
