import Audit.Wire3.GoldilocksNorm

/-!
# A field structure on the actual canonical Ext3 arithmetic

Element is only a wrapper around Verifier.Ext3. Addition, subtraction,
multiplication, negation, zero and one are the existing concrete audit
operations. The totalized inverse executes WhirFinal.inverse and maps its
failure (proved equivalent to zero input) to zero. It does not choose a new
inverse from an existence theorem or transport a field from an unrelated type.

Every ring law comes from the Nat.mod proofs in Audit.Wire3.Algebra. The field
inverse law comes from the concrete norm nonvanishing and executable-inverse
proof. All instances are for this fresh wrapper, not for Verifier.Ext3 itself.
The explicit three-limb equivalence supplies Fintype and cardinality p^3;
the existing base embedding supplies characteristic p. Natural powers are
the ordinary repeated-multiplication operation of these actual field operations.
This is a concrete arithmetic field proof, not compiler/Yul refinement,
a sampled-challenge distribution result, or PCS soundness.
-/
namespace Audit.Wire3.GoldilocksExt3Field
open Audit.Wire3
open GoldilocksNorm
local notation "p" => Arithmetic.modulus

structure Element where
  toVerifier : Verifier.Ext3
  deriving DecidableEq

theorem element_eq (a b : Element) (h : a.toVerifier = b.toVerifier) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance : Zero Element := ⟨⟨Verifier.zero⟩⟩
instance : One Element := ⟨⟨Norm.one⟩⟩
instance : Add Element := ⟨fun a b => ⟨Verifier.add a.toVerifier b.toVerifier⟩⟩
instance : Sub Element := ⟨fun a b => ⟨Verifier.sub a.toVerifier b.toVerifier⟩⟩
instance : Neg Element := ⟨fun a => ⟨Algebra.vneg a.toVerifier⟩⟩
instance : Mul Element := ⟨fun a b => ⟨Verifier.mul a.toVerifier b.toVerifier⟩⟩

theorem zero_exact : (0 : Element).toVerifier = Verifier.zero := rfl
theorem one_exact : (1 : Element).toVerifier = Norm.one := rfl
theorem add_exact (a b : Element) :
    (a + b).toVerifier = Verifier.add a.toVerifier b.toVerifier := rfl
theorem sub_exact (a b : Element) :
    (a - b).toVerifier = Verifier.sub a.toVerifier b.toVerifier := rfl
theorem neg_exact (a : Element) : (-a).toVerifier = Algebra.vneg a.toVerifier := rfl
theorem mul_exact (a b : Element) :
    (a * b).toVerifier = Verifier.mul a.toVerifier b.toVerifier := rfl

theorem embed_succ (n : Nat) : Norm.embed (n + 1) = Verifier.add (Norm.embed n) Norm.one := by
  apply Subtype.eq
  simp [Norm.embed, Norm.one, Verifier.add, Arithmetic.fromBase, Arithmetic.eadd,
    Arithmetic.one, Arithmetic.add, Arithmetic.reduce]

instance instCommRing : CommRing Element where
  zero := 0
  one := 1
  add := (· + ·)
  sub := (· - ·)
  neg := Neg.neg
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast n := ⟨Norm.embed n⟩
  natCast_zero := rfl
  natCast_succ n := congrArg Element.mk (embed_succ n)
  add_assoc a b c := congrArg Element.mk (Algebra.vadd_assoc _ _ _)
  add_comm a b := congrArg Element.mk (Algebra.vadd_comm _ _)
  zero_add a := congrArg Element.mk (Algebra.vzero_add _)
  add_zero a := congrArg Element.mk (Algebra.vadd_zero _)
  add_left_neg a := congrArg Element.mk (Algebra.vneg_add_cancel _)
  sub_eq_add_neg a b := congrArg Element.mk (Algebra.vsub_as_add_neg _ _)
  mul_assoc a b c := congrArg Element.mk (Algebra.vmul_assoc _ _ _)
  mul_comm a b := congrArg Element.mk (Algebra.vmul_comm _ _)
  one_mul a := congrArg Element.mk (Algebra.vone_mul _)
  mul_one a := congrArg Element.mk (Algebra.vmul_one _)
  zero_mul a := congrArg Element.mk (Algebra.vzero_mul _)
  mul_zero a := congrArg Element.mk (Algebra.vmul_zero _)
  left_distrib a b c := congrArg Element.mk (Algebra.vmul_add _ _ _)
  right_distrib a b c := congrArg Element.mk (Algebra.vadd_mul _ _ _)

theorem nat_cast_exact (n : Nat) : (n : Element).toVerifier = Norm.embed n := rfl

theorem raw_zero_iff (a : Element) : a.toVerifier.val = Arithmetic.zero ↔ a = 0 := by
  constructor
  · intro h
    exact element_eq a 0 (Subtype.eq h)
  · rintro rfl
    rfl

/-- This is a dependent match on the actual deterministic Option-returning
algorithm. Proofs only package the successful result's existing canonicality. -/
def actualInverse (a : Element) : Element :=
  match h : WhirFinal.inverse a.toVerifier.val with
  | none => 0
  | some output => ⟨⟨output,FermatBridge.inverse_success_is_canonical _ _ h⟩⟩

instance : Inv Element := ⟨actualInverse⟩

theorem inverse_success_exact (a : Element) (output : Arithmetic.Ext3)
    (h : WhirFinal.inverse a.toVerifier.val = some output) :
    (a⁻¹).toVerifier.val = output := by
  change (actualInverse a).toVerifier.val = output
  unfold actualInverse
  split
  · rename_i hn
    rw [hn] at h
    contradiction
  · rename_i result hs
    exact Option.some.inj (hs.symm.trans h)

theorem inverse_failure_exact (a : Element)
    (h : WhirFinal.inverse a.toVerifier.val = none) : a⁻¹ = 0 := by
  change actualInverse a = 0
  unfold actualInverse
  split
  · rfl
  · rename_i result hs
    rw [hs] at h
    contradiction

theorem actual_inverse_zero : (0 : Element)⁻¹ = 0 := by
  apply inverse_failure_exact
  rfl

theorem actual_mul_inverse (a : Element) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  have hn : a.toVerifier.val ≠ Arithmetic.zero := fun hz => ha ((raw_zero_iff a).mp hz)
  obtain ⟨output,hi,_,hu,_⟩ := nonzero_actual_inverse_exists a.toVerifier hn
  apply element_eq
  apply Subtype.eq
  change Arithmetic.emul a.toVerifier.val (a⁻¹).toVerifier.val = Arithmetic.one
  rw [inverse_success_exact a output hi]
  exact hu

instance : Nontrivial Element := ⟨⟨0,1,by
  intro h
  have hc := congrArg (fun a : Element => a.toVerifier.val.c0) h
  exact Nat.zero_ne_one hc⟩⟩

instance instField : Field Element where
  inv := Inv.inv
  inv_zero := actual_inverse_zero
  mul_inv_cancel := actual_mul_inverse
  nnqsmul := _
  qsmul := _

/-- The Field instance's inverse remains the actual successful execution,
not merely an inverse equal after abstract transport. -/
theorem field_inverse_executes_when_nonzero (a : Element) (ha : a ≠ 0) :
    WhirFinal.inverse a.toVerifier.val = some (a⁻¹).toVerifier.val := by
  have hn : a.toVerifier.val ≠ Arithmetic.zero := fun hz => ha ((raw_zero_iff a).mp hz)
  obtain ⟨output,hi,_,_,_⟩ := nonzero_actual_inverse_exists a.toVerifier hn
  rw [inverse_success_exact a output hi]
  exact hi

theorem field_division_exact (a b : Element) :
    (a / b).toVerifier = Verifier.mul a.toVerifier (actualInverse b).toVerifier := rfl

theorem field_nat_cast_zero_iff (n : Nat) : (n : Element) = 0 ↔ p ∣ n := by
  rw [← raw_zero_iff (n : Element)]
  change Arithmetic.fromBase n = Arithmetic.zero ↔ p ∣ n
  constructor
  · intro h
    exact (Nat.dvd_iff_mod_eq_zero p n).mpr (congrArg Arithmetic.Ext3.c0 h)
  · intro h
    simp only [Arithmetic.fromBase, Arithmetic.reduce, Nat.mod_eq_zero_of_dvd h, Arithmetic.zero]

instance instCharP : CharP Element p := ⟨field_nat_cast_zero_iff⟩

def coordinates (a : Element) : Fin p × Fin p × Fin p :=
  (⟨a.toVerifier.val.c0,a.toVerifier.property.1⟩,
   ⟨a.toVerifier.val.c1,a.toVerifier.property.2.1⟩,
   ⟨a.toVerifier.val.c2,a.toVerifier.property.2.2⟩)

def fromCoordinates (a : Fin p × Fin p × Fin p) : Element :=
  ⟨⟨⟨a.1.val,a.2.1.val,a.2.2.val⟩,a.1.isLt,a.2.1.isLt,a.2.2.isLt⟩⟩

theorem coordinates_roundtrip (a : Element) : fromCoordinates (coordinates a) = a := by
  apply element_eq
  apply Subtype.eq
  rfl

theorem from_coordinates_roundtrip (a : Fin p × Fin p × Fin p) :
    coordinates (fromCoordinates a) = a := rfl

def coordinateEquiv : Element ≃ Fin p × Fin p × Fin p where
  toFun := coordinates
  invFun := fromCoordinates
  left_inv := coordinates_roundtrip
  right_inv := from_coordinates_roundtrip

instance : Fintype Element := Fintype.ofEquiv (Fin p × Fin p × Fin p) coordinateEquiv.symm

theorem cardinality_exact : Fintype.card Element = p ^ 3 := by
  rw [Fintype.card_congr coordinateEquiv]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- Finite-field Frobenius for this actual-operation wrapper, derived from its
constructed Field/Fintype instances. The power is repeated actual multiplication,
not an external extension-field oracle. -/
theorem field_frobenius_cube (a : Element) : a ^ (p ^ 3) = a := by
  have h := FiniteField.pow_card a
  rw [cardinality_exact] at h
  exact h

theorem field_fermat (a : Element) (ha : a ≠ 0) : a ^ (p ^ 3 - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [cardinality_exact] at h
  exact h

def theta : Element := ⟨⟨⟨0,1,0⟩,by decide⟩⟩

theorem theta_cubed_is_two : theta ^ 3 = (2 : Element) := by decide

theorem theta_field_inverse_exact :
    (theta⁻¹).toVerifier.val = ⟨0,0,9223372034707292161⟩ :=
  inverse_success_exact theta _ theta_actual_inverse_executes

end Audit.Wire3.GoldilocksExt3Field
