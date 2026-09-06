import Std

/-!
Concrete arithmetic used by the wire-v3 executable audit models.

Source correspondence at becfe98e: `GoldilocksField.sol` reduce/add/sub/mul/neg,
and `spongefish/GoldilocksExt3.sol` fromBaseU256, isZero, eq/isEqual, add, sub,
neg, mul, mulScalarU256 and double_.  These are mathematical Nat operations;
addmod/mulmod are NOT ordinary wrapping uint256 addition/multiplication.  This
file does not prove Yul memory safety, compiler refinement, Goldilocks primality,
irreducibility of X^3-2, or correctness of inverse/exponentiation/evalL0.  Raw
inputs are arbitrary naturals, an overapproximation of uint64/uint256 inputs.
-/
namespace Audit.Wire3.Arithmetic

def modulus : Nat := 18446744069414584321

theorem modulus_positive : 0 < modulus := by decide
theorem modulus_below_u64 : modulus < 2 ^ 64 := by decide

def reduce (a : Nat) : Nat := a % modulus
def add (a b : Nat) : Nat := reduce (a + b)
def sub (a b : Nat) : Nat := reduce (a + (modulus - reduce b))
def mul (a b : Nat) : Nat := reduce (a * b)
def neg (a : Nat) : Nat := if reduce a = 0 then 0 else modulus - reduce a

theorem reduce_canonical (a : Nat) : reduce a < modulus :=
  Nat.mod_lt _ modulus_positive

theorem reduce_fixed {a : Nat} (h : a < modulus) : reduce a = a :=
  Nat.mod_eq_of_lt h

theorem reduce_idempotent (a : Nat) : reduce (reduce a) = reduce a :=
  reduce_fixed (reduce_canonical a)

theorem add_canonical (a b : Nat) : add a b < modulus := reduce_canonical _
theorem sub_canonical (a b : Nat) : sub a b < modulus := reduce_canonical _
theorem mul_canonical (a b : Nat) : mul a b < modulus := reduce_canonical _

theorem neg_canonical (a : Nat) : neg a < modulus := by
  unfold neg
  split
  · exact modulus_positive
  · have := reduce_canonical a
    have := modulus_positive
    omega

theorem sub_negation_operand_does_not_underflow (b : Nat) : reduce b ≤ modulus :=
  Nat.le_of_lt (reduce_canonical b)

theorem add_zero (a : Nat) : add a 0 = reduce a := by simp [add]
theorem mul_zero (a : Nat) : mul a 0 = 0 := by simp [mul, reduce]
theorem zero_mul (a : Nat) : mul 0 a = 0 := by simp [mul, reduce]

structure Ext3 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  deriving DecidableEq, Repr

def Canonical (a : Ext3) : Prop :=
  a.c0 < modulus ∧ a.c1 < modulus ∧ a.c2 < modulus

def zero : Ext3 := ⟨0, 0, 0⟩
def one : Ext3 := ⟨1, 0, 0⟩
def normalize (a : Ext3) : Ext3 := ⟨reduce a.c0, reduce a.c1, reduce a.c2⟩
def fromBase (a : Nat) : Ext3 := ⟨reduce a, 0, 0⟩
def checkedFromBase (a : Nat) : Option Ext3 :=
  if a < modulus then some ⟨a, 0, 0⟩ else none

def eq (a b : Ext3) : Bool := decide (normalize a = normalize b)
def isZero (a : Ext3) : Bool := eq a zero

def eadd (a b : Ext3) : Ext3 := ⟨add a.c0 b.c0, add a.c1 b.c1, add a.c2 b.c2⟩
def esub (a b : Ext3) : Ext3 := ⟨sub a.c0 b.c0, sub a.c1 b.c1, sub a.c2 b.c2⟩
def eneg (a : Ext3) : Ext3 := ⟨neg a.c0, neg a.c1, neg a.c2⟩
def emul (a b : Ext3) : Ext3 :=
  ⟨add (mul a.c0 b.c0) (mul 2 (add (mul a.c1 b.c2) (mul a.c2 b.c1))),
   add (add (mul a.c0 b.c1) (mul a.c1 b.c0)) (mul 2 (mul a.c2 b.c2)),
   add (add (mul a.c0 b.c2) (mul a.c1 b.c1)) (mul a.c2 b.c0)⟩
def scalar (a : Ext3) (s : Nat) : Ext3 :=
  ⟨mul a.c0 (reduce s), mul a.c1 (reduce s), mul a.c2 (reduce s)⟩
def double (a : Ext3) : Ext3 := eadd a a

theorem zero_canonical : Canonical zero := by
  exact ⟨modulus_positive, modulus_positive, modulus_positive⟩

theorem normalize_canonical (a : Ext3) : Canonical (normalize a) :=
  ⟨reduce_canonical _, reduce_canonical _, reduce_canonical _⟩

theorem normalize_fixed {a : Ext3} (h : Canonical a) : normalize a = a := by
  cases a
  simp only [normalize, Canonical] at *
  rw [reduce_fixed h.1, reduce_fixed h.2.1, reduce_fixed h.2.2]

theorem normalize_idempotent (a : Ext3) : normalize (normalize a) = normalize a :=
  normalize_fixed (normalize_canonical a)

theorem normalized_equality_iff (a b : Ext3) :
    eq a b = true ↔ normalize a = normalize b := by simp [eq]

theorem canonical_equality_iff {a b : Ext3} (ha : Canonical a) (hb : Canonical b) :
    eq a b = true ↔ a = b := by
  simp [eq, normalize_fixed ha, normalize_fixed hb]

theorem canonical_zero_iff {a : Ext3} (h : Canonical a) :
    isZero a = true ↔ a = zero := canonical_equality_iff h zero_canonical

theorem checked_base_rejects_noncanonical {a : Nat} (h : modulus ≤ a) :
    checkedFromBase a = none := by simp [checkedFromBase, Nat.not_lt.mpr h]

theorem checked_base_success {a : Nat} {r : Ext3} (h : checkedFromBase a = some r) :
    a < modulus ∧ r = ⟨a, 0, 0⟩ ∧ Canonical r := by
  unfold checkedFromBase at h
  split at h
  · cases h
    exact ⟨‹a < modulus›, rfl, ‹a < modulus›, modulus_positive, modulus_positive⟩
  · contradiction

theorem fromBase_canonical (a : Nat) : Canonical (fromBase a) :=
  ⟨reduce_canonical _, modulus_positive, modulus_positive⟩

theorem eadd_canonical (a b : Ext3) : Canonical (eadd a b) :=
  ⟨add_canonical _ _, add_canonical _ _, add_canonical _ _⟩

theorem esub_canonical (a b : Ext3) : Canonical (esub a b) :=
  ⟨sub_canonical _ _, sub_canonical _ _, sub_canonical _ _⟩

theorem eneg_canonical (a : Ext3) : Canonical (eneg a) :=
  ⟨neg_canonical _, neg_canonical _, neg_canonical _⟩

theorem emul_canonical (a b : Ext3) : Canonical (emul a b) :=
  ⟨add_canonical _ _, add_canonical _ _, add_canonical _ _⟩

theorem scalar_canonical (a : Ext3) (s : Nat) : Canonical (scalar a s) :=
  ⟨mul_canonical _ _, mul_canonical _ _, mul_canonical _ _⟩

theorem double_canonical (a : Ext3) : Canonical (double a) := eadd_canonical _ _

theorem eadd_zero (a : Ext3) : eadd a zero = normalize a := by
  cases a
  simp [eadd, zero, add, normalize]

theorem emul_zero (a : Ext3) : emul a zero = zero := by
  simp [emul, zero, mul, add, reduce]

theorem zero_emul (a : Ext3) : emul zero a = zero := by
  simp [emul, zero, mul, add, reduce]

theorem esub_zero_zero : esub zero zero = zero := by
  simp [esub, zero, sub, reduce]

/-- The same ordered difference-form butterfly as PackedClaimExt3._foldFlat and
    Rust prover_v2::fold_ext3_claim.  No random-challenge soundness is asserted. -/
def butterfly (even odd challenge : Ext3) : Ext3 :=
  eadd even (emul challenge (esub odd even))

theorem butterfly_canonical (even odd challenge : Ext3) :
    Canonical (butterfly even odd challenge) := eadd_canonical _ _

theorem butterfly_zero_pair (challenge : Ext3) : butterfly zero zero challenge = zero := by
  simp [butterfly, esub_zero_zero, emul_zero, eadd_zero, normalize_fixed zero_canonical]

theorem butterfly_zero_challenge {even : Ext3} (h : Canonical even) (odd : Ext3) :
    butterfly even odd zero = even := by
  simp [butterfly, zero_emul, eadd_zero, normalize_fixed h]

end Audit.Wire3.Arithmetic
