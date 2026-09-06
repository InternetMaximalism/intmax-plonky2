import Audit.Wire3.Norm

/-!
Concrete algebra for Arithmetic's modulus 18446744069414584321 and cubic
coordinate multiplication modulo X^3-2. These laws are proved by reducing the
actual Nat modular expressions; no assumed ring-law structure is introduced.
This proves algebra inside the executable models, not primality, irreducibility,
inverse correctness, compiler/Yul refinement, or any probabilistic argument.
-/
namespace Audit.Wire3.Algebra
open Arithmetic

theorem nat_mod_mul_left (a b m : Nat) : (a % m * b) % m = (a * b) % m := by
  calc
    (a % m * b) % m = ((a % m) % m * (b % m)) % m := Nat.mul_mod _ _ _
    _ = (a % m * (b % m)) % m := by rw [Nat.mod_mod]
    _ = (a * b) % m := (Nat.mul_mod _ _ _).symm

theorem nat_mod_mul_right (a b m : Nat) : (a * (b % m)) % m = (a * b) % m := by
  rw [Nat.mul_comm a (b % m), nat_mod_mul_left, Nat.mul_comm b a]

theorem base_add_comm (a b : Nat) : add a b = add b a := by simp [add, Nat.add_comm]

theorem base_add_assoc (a b c : Nat) : add (add a b) c = add a (add b c) := by
  simp [add, reduce, Nat.add_assoc]

theorem base_mul_comm (a b : Nat) : mul a b = mul b a := by simp [mul, Nat.mul_comm]

theorem base_mul_assoc (a b c : Nat) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul, reduce, nat_mod_mul_left, nat_mod_mul_right, Nat.mul_assoc]

theorem base_mul_add (a b c : Nat) : mul a (add b c) = add (mul a b) (mul a c) := by
  simp only [mul, add, reduce, nat_mod_mul_right, Nat.mod_add_mod, Nat.add_mod_mod, Nat.mul_add]

theorem base_add_mul (a b c : Nat) : mul (add a b) c = add (mul a c) (mul b c) := by
  simp only [mul, add, reduce, nat_mod_mul_left, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_mul]

theorem eadd_comm (a b : Ext3) : eadd a b = eadd b a := by
  simp only [eadd, base_add_comm]

theorem eadd_assoc (a b c : Ext3) : eadd (eadd a b) c = eadd a (eadd b c) := by
  simp only [eadd, base_add_assoc]

theorem emul_comm (a b : Ext3) : emul a b = emul b a := by
  simp only [emul, add, mul, reduce, Nat.mod_add_mod, Nat.add_mod_mod,
    nat_mod_mul_left, nat_mod_mul_right]
  congr 1 <;> congr 1 <;> ac_rfl

theorem emul_add (a b c : Ext3) : emul a (eadd b c) = eadd (emul a b) (emul a c) := by
  simp only [emul, eadd, add, mul, reduce, Nat.mod_add_mod, Nat.add_mod_mod,
    nat_mod_mul_left, nat_mod_mul_right]
  congr 1 <;> congr 1 <;> simp only [Nat.mul_add, Nat.add_mul] <;> ac_rfl

theorem eadd_mul (a b c : Ext3) : emul (eadd a b) c = eadd (emul a c) (emul b c) := by
  rw [emul_comm, emul_add, emul_comm c a, emul_comm c b]

theorem emul_assoc (a b c : Ext3) : emul (emul a b) c = emul a (emul b c) := by
  simp only [emul, add, mul, reduce, Nat.mod_add_mod, Nat.add_mod_mod,
    nat_mod_mul_left, nat_mod_mul_right]
  congr 1 <;> congr 1 <;> simp only [Nat.mul_add, Nat.add_mul] <;> ac_rfl

theorem emul_one_normalizes (a : Ext3) : emul a one = normalize a := by
  simp [emul, one, normalize, add, mul, reduce, nat_mod_mul_left, nat_mod_mul_right]

theorem one_emul_normalizes (a : Ext3) : emul one a = normalize a := by
  rw [emul_comm, emul_one_normalizes]

theorem emul_one_of_canonical (a : Ext3) (h : Canonical a) : emul a one = a := by
  rw [emul_one_normalizes, normalize_fixed h]

theorem one_emul_of_canonical (a : Ext3) (h : Canonical a) : emul one a = a := by
  rw [one_emul_normalizes, normalize_fixed h]

theorem nat_four_mul (a : Nat) : 4 * a = a + a + a + a := by omega

theorem norm_square_is_multiplication (a : Verifier.Ext3) : Norm.square a = Verifier.mul a a := by
  apply Subtype.eq
  simp only [Norm.square, Verifier.mul, emul, add, mul, reduce,
    Nat.mod_add_mod, Nat.add_mod_mod, nat_mod_mul_left, nat_mod_mul_right]
  congr 1 <;> congr 1 <;>
    simp only [Nat.two_mul, nat_four_mul, Nat.mul_add, Nat.add_mul] <;> ac_rfl

theorem base_sub_self (a : Nat) : sub a a = 0 := by
  have ha : a % modulus ≤ modulus := Nat.le_of_lt (Nat.mod_lt a modulus_positive)
  change (a + (modulus - a % modulus)) % modulus = 0
  rw [← Nat.mod_add_mod a modulus (modulus - a % modulus)]
  rw [Nat.add_sub_of_le ha, Nat.mod_self]

theorem base_sub_as_add_neg (a b : Nat) : sub a b = add a (neg b) := by
  unfold neg
  split
  · have hb : b % modulus = 0 := ‹reduce b = 0›
    simp [sub, add, reduce, hb]
  · rfl

theorem base_sub_add_cancel (a b : Nat) : add (sub a b) b = reduce a := by
  have hb : b % modulus ≤ modulus := Nat.le_of_lt (Nat.mod_lt b modulus_positive)
  simp only [add, sub, reduce, Nat.mod_add_mod]
  rw [← Nat.add_mod_mod (a + (modulus - b % modulus)) b modulus]
  rw [Nat.add_assoc, Nat.sub_add_cancel hb, Nat.add_mod_right]

theorem esub_self (a : Ext3) : esub a a = zero := by simp [esub, base_sub_self, zero]

theorem esub_as_add_neg (a b : Ext3) : esub a b = eadd a (eneg b) := by
  simp only [esub, eadd, eneg, base_sub_as_add_neg]

theorem esub_add_cancel (a b : Ext3) : eadd (esub a b) b = normalize a := by
  simp only [eadd, esub, normalize, base_sub_add_cancel]

def vneg (a : Verifier.Ext3) : Verifier.Ext3 := ⟨eneg a.val, eneg_canonical _⟩

theorem vadd_comm (a b : Verifier.Ext3) : Verifier.add a b = Verifier.add b a :=
  Subtype.eq (eadd_comm _ _)

theorem vadd_assoc (a b c : Verifier.Ext3) :
    Verifier.add (Verifier.add a b) c = Verifier.add a (Verifier.add b c) :=
  Subtype.eq (eadd_assoc _ _ _)

theorem vadd_left_comm (a b c : Verifier.Ext3) :
    Verifier.add a (Verifier.add b c) = Verifier.add b (Verifier.add a c) := by
  rw [← vadd_assoc, vadd_comm a b, vadd_assoc]

theorem vmul_comm (a b : Verifier.Ext3) : Verifier.mul a b = Verifier.mul b a :=
  Subtype.eq (emul_comm _ _)

theorem vmul_assoc (a b c : Verifier.Ext3) :
    Verifier.mul (Verifier.mul a b) c = Verifier.mul a (Verifier.mul b c) :=
  Subtype.eq (emul_assoc _ _ _)

theorem vmul_add (a b c : Verifier.Ext3) :
    Verifier.mul a (Verifier.add b c) = Verifier.add (Verifier.mul a b) (Verifier.mul a c) :=
  Subtype.eq (emul_add _ _ _)

theorem vadd_mul (a b c : Verifier.Ext3) :
    Verifier.mul (Verifier.add a b) c = Verifier.add (Verifier.mul a c) (Verifier.mul b c) :=
  Subtype.eq (eadd_mul _ _ _)

theorem vadd_zero (a : Verifier.Ext3) : Verifier.add a Verifier.zero = a := by
  apply Subtype.eq
  exact (eadd_zero _).trans (normalize_fixed a.property)

theorem vzero_add (a : Verifier.Ext3) : Verifier.add Verifier.zero a = a := by
  rw [vadd_comm, vadd_zero]

theorem vmul_zero (a : Verifier.Ext3) : Verifier.mul a Verifier.zero = Verifier.zero :=
  Subtype.eq (emul_zero _)

theorem vzero_mul (a : Verifier.Ext3) : Verifier.mul Verifier.zero a = Verifier.zero :=
  Subtype.eq (zero_emul _)

theorem vmul_one (a : Verifier.Ext3) : Verifier.mul a Norm.one = a := by
  apply Subtype.eq
  exact emul_one_of_canonical _ a.property

theorem vone_mul (a : Verifier.Ext3) : Verifier.mul Norm.one a = a := by
  rw [vmul_comm, vmul_one]

theorem vsub_self (a : Verifier.Ext3) : Verifier.sub a a = Verifier.zero :=
  Subtype.eq (esub_self _)

theorem vsub_as_add_neg (a b : Verifier.Ext3) : Verifier.sub a b = Verifier.add a (vneg b) :=
  Subtype.eq (esub_as_add_neg _ _)

theorem vadd_neg_cancel (a : Verifier.Ext3) : Verifier.add a (vneg a) = Verifier.zero := by
  rw [← vsub_as_add_neg, vsub_self]

theorem vneg_add_cancel (a : Verifier.Ext3) : Verifier.add (vneg a) a = Verifier.zero := by
  rw [vadd_comm, vadd_neg_cancel]

theorem vsub_add_cancel (a b : Verifier.Ext3) : Verifier.add (Verifier.sub a b) b = a := by
  apply Subtype.eq
  exact (esub_add_cancel _ _).trans (normalize_fixed a.property)

theorem vadd_left_cancel (a b c : Verifier.Ext3) (h : Verifier.add a b = Verifier.add a c) : b = c := by
  have hh := congrArg (Verifier.add (vneg a)) h
  simpa only [← vadd_assoc, vneg_add_cancel, vzero_add] using hh

theorem vmul_neg (a b : Verifier.Ext3) : Verifier.mul a (vneg b) = vneg (Verifier.mul a b) := by
  apply vadd_left_cancel (Verifier.mul a b)
  rw [← vmul_add, vadd_neg_cancel, vmul_zero, vadd_neg_cancel]

theorem vneg_mul (a b : Verifier.Ext3) : Verifier.mul (vneg a) b = vneg (Verifier.mul a b) := by
  rw [vmul_comm, vmul_neg, vmul_comm b a]

theorem vneg_neg (a : Verifier.Ext3) : vneg (vneg a) = a := by
  apply vadd_left_cancel (vneg a)
  rw [vadd_neg_cancel, vneg_add_cancel]

theorem vmul_sub (a b c : Verifier.Ext3) :
    Verifier.mul a (Verifier.sub b c) = Verifier.sub (Verifier.mul a b) (Verifier.mul a c) := by
  simp only [vsub_as_add_neg, vmul_add, vmul_neg]

theorem vsub_mul (a b c : Verifier.Ext3) :
    Verifier.mul (Verifier.sub a b) c = Verifier.sub (Verifier.mul a c) (Verifier.mul b c) := by
  rw [vmul_comm, vmul_sub, vmul_comm c a, vmul_comm c b]

theorem vneg_zero : vneg Verifier.zero = Verifier.zero := by
  have h := vadd_neg_cancel Verifier.zero
  simpa only [vzero_add] using h

theorem vsub_zero (a : Verifier.Ext3) : Verifier.sub a Verifier.zero = a := by
  rw [vsub_as_add_neg, vneg_zero, vadd_zero]

theorem vneg_add (a b : Verifier.Ext3) : vneg (Verifier.add a b) = Verifier.add (vneg a) (vneg b) := by
  apply vadd_left_cancel (Verifier.add a b)
  rw [vadd_neg_cancel]
  calc
    Verifier.zero = Verifier.add Verifier.zero Verifier.zero := (vadd_zero _).symm
    _ = Verifier.add (Verifier.add a (vneg a)) (Verifier.add b (vneg b)) := by
      rw [vadd_neg_cancel, vadd_neg_cancel]
    _ = Verifier.add (Verifier.add a b) (Verifier.add (vneg a) (vneg b)) := by
      simp only [vadd_assoc]
      rw [← vadd_assoc (vneg a) b, vadd_comm (vneg a) b, vadd_assoc]

theorem norm_eq_factor_matches_product_form (tau x : Verifier.Ext3) :
    Norm.eqFactor tau x = Verifier.add (Verifier.mul tau x)
      (Verifier.mul (Verifier.sub Norm.one tau) (Verifier.sub Norm.one x)) := by
  simp only [Norm.eqFactor, Norm.twice, vsub_as_add_neg, vadd_mul, vmul_add,
    vone_mul, vmul_one, vmul_neg, vneg_mul, vneg_neg, vneg_add]
  simp only [vadd_assoc, vadd_comm, vadd_left_comm]

theorem scalar_as_embedded_mul (x : Verifier.Ext3) (s : Nat) :
    Verifier.scalar x s = Verifier.mul x (Norm.embed s) := by
  apply Subtype.eq
  simp [Verifier.scalar, Verifier.mul, Norm.embed, scalar, emul, fromBase,
    add, mul, reduce, nat_mod_mul_left, nat_mod_mul_right]

theorem embed_base_sub_one (g : Verifier.Base) :
    Norm.embed (add g.val (modulus - 1)) = Verifier.sub (Norm.embed g.val) Norm.one := by
  apply Subtype.eq
  have hOne : 1 % modulus = 1 := by decide
  simp [Norm.embed, Norm.one, Verifier.sub, esub, fromBase, sub, add, reduce, hOne]

theorem norm_subgroup_factor_matches_rust (g : Verifier.Base) (x : Verifier.Ext3) :
    Norm.subgroupFactor g x = Verifier.add (Verifier.sub Norm.one x)
      (Verifier.mul x (Norm.embed g.val)) := by
  rw [Norm.subgroupFactor, scalar_as_embedded_mul, embed_base_sub_one, vmul_sub, vmul_one]
  simp only [vsub_as_add_neg, vadd_assoc, vadd_comm, vadd_left_comm]

theorem norm_eq_loop_matches_rust (tau point : List Verifier.Ext3) :
    Norm.eqEvaluation tau point = (tau.zip point).foldl (fun acc pair =>
      Verifier.mul acc (Verifier.add (Verifier.mul pair.1 pair.2)
        (Verifier.mul (Verifier.sub Norm.one pair.1) (Verifier.sub Norm.one pair.2)))) Norm.one := by
  simp only [Norm.eqEvaluation, Norm.productLoop, norm_eq_factor_matches_product_form]

theorem norm_subgroup_loop_matches_rust (powers : List Verifier.Base) (point : List Verifier.Ext3) :
    Norm.subgroupEvaluation powers point = (powers.zip point).foldl (fun acc pair =>
      Verifier.mul acc (Verifier.add (Verifier.sub Norm.one pair.2)
        (Verifier.mul pair.2 (Norm.embed pair.1.val)))) Norm.one := by
  simp only [Norm.subgroupEvaluation, Norm.productLoop, norm_subgroup_factor_matches_rust]

/-- Distributing a fixed multiplier across an arbitrary ordered accumulator
    is the concrete law needed for row-local PI batching and split WHIR dots. -/
theorem vmul_fold_sum (a : Verifier.Ext3) (xs : List Verifier.Ext3) (initial : Verifier.Ext3) :
    Verifier.mul a (xs.foldl Verifier.add initial) =
      (xs.map (Verifier.mul a)).foldl Verifier.add (Verifier.mul a initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, List.map_cons, vmul_add] using
      (ih (Verifier.add initial x))

theorem vsub_eq_zero_iff (a b : Verifier.Ext3) : Verifier.sub a b = Verifier.zero ↔ a = b := by
  constructor
  · intro h
    have hc := vsub_add_cancel a b
    simpa only [h, vzero_add] using hc.symm
  · intro h
    subst h
    exact vsub_self _

end Audit.Wire3.Algebra
