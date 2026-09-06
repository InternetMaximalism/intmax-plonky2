import Audit.Wire3.Algebra
import Audit.Wire3.WhirFinal

/-!
Concrete cubic formal-coordinate identities for the current norm/logUp models.
Coefficients are the actual canonical Goldilocks Ext3 implementation, not an
assumed commutative-ring parameter. All algebraic laws below originate in the
Nat.mod proofs of Algebra. The additional formal variable T satisfies T^3=2;
it must not be confused with applying a field norm to an off-cube Ext3 value.

These deterministic identities do not establish primality, irreducibility,
nonzero norm for every nonzero input, Fermat inversion, or PCS/FS soundness.
-/
namespace Audit.Wire3.NormIdentity
open Verifier Algebra

local infixl:65 " ⊕ " => Verifier.add
local infixl:65 " ⊖ " => Verifier.sub
local infixl:70 " ⊗ " => Verifier.mul

def formalMultiply (x y : Norm.Coordinates) : Norm.Coordinates :=
  ⟨x.a ⊗ y.a ⊕ Norm.twice (x.b ⊗ y.c ⊕ x.c ⊗ y.b),
   (x.a ⊗ y.b ⊕ x.b ⊗ y.a) ⊕ Norm.twice (x.c ⊗ y.c),
   (x.a ⊗ y.c ⊕ x.b ⊗ y.b) ⊕ x.c ⊗ y.a⟩

def formalScalar (x : Ext3) : Norm.Coordinates := ⟨x, zero, zero⟩

theorem vmul_left_comm (a b c : Ext3) : a ⊗ (b ⊗ c) = b ⊗ (a ⊗ c) := by
  rw [← vmul_assoc, vmul_comm a b, vmul_assoc]

theorem formal_product_scalar_coordinate (v : Norm.Coordinates) :
    (formalMultiply v (Norm.formalAdjugate v)).a = Norm.formalNorm v := by
  simp only [formalMultiply, Norm.formalNorm, Norm.formalNormFromAdjugate]
  rw [vadd_comm (v.b ⊗ (Norm.formalAdjugate v).c) (v.c ⊗ (Norm.formalAdjugate v).b)]

theorem formal_product_linear_coordinate (v : Norm.Coordinates) :
    (formalMultiply v (Norm.formalAdjugate v)).b = zero := by
  let s := (v.a ⊗ Norm.twice (v.c ⊗ v.c)) ⊕
    ((v.b ⊗ (v.a ⊗ v.a)) ⊕ Norm.twice (v.c ⊗ (v.b ⊗ v.b)))
  calc
    (formalMultiply v (Norm.formalAdjugate v)).b = s ⊕ vneg s := by
      simp only [formalMultiply, Norm.formalAdjugate, norm_square_is_multiplication,
        Norm.twice, s, vmul_sub, vsub_mul, vmul_add, vadd_mul,
        vsub_as_add_neg, vneg_add, vmul_neg, vneg_mul]
      simp only [vmul_assoc, vmul_comm, vmul_left_comm,
        vadd_assoc, vadd_comm, vadd_left_comm]
    _ = zero := vadd_neg_cancel s

theorem formal_product_quadratic_coordinate (v : Norm.Coordinates) :
    (formalMultiply v (Norm.formalAdjugate v)).c = zero := by
  let s := (v.a ⊗ (v.b ⊗ v.b)) ⊕
    ((v.b ⊗ Norm.twice (v.c ⊗ v.c)) ⊕ (v.c ⊗ (v.a ⊗ v.a)))
  calc
    (formalMultiply v (Norm.formalAdjugate v)).c = s ⊕ vneg s := by
      simp only [formalMultiply, Norm.formalAdjugate, norm_square_is_multiplication,
        Norm.twice, s, vmul_sub, vsub_mul, vmul_add, vadd_mul,
        vsub_as_add_neg, vneg_add, vmul_neg, vneg_mul]
      simp only [vmul_assoc, vmul_comm, vmul_left_comm,
        vadd_assoc, vadd_comm, vadd_left_comm]
    _ = zero := vadd_neg_cancel s

/-- Nontrivial polynomial adjugate identity at arbitrary off-cube Ext3
    coordinates, without any invertibility assumption. -/
theorem formal_adjugate_identity (v : Norm.Coordinates) :
    formalMultiply v (Norm.formalAdjugate v) = formalScalar (Norm.formalNorm v) := by
  have ha := formal_product_scalar_coordinate v
  have hb := formal_product_linear_coordinate v
  have hc := formal_product_quadratic_coordinate v
  cases h : formalMultiply v (Norm.formalAdjugate v) with
  | mk a b c =>
      simp only [h] at ha hb hc
      subst a; subst b; subst c
      rfl

theorem formal_multiply_comm (x y : Norm.Coordinates) : formalMultiply x y = formalMultiply y x := by
  simp only [formalMultiply, Norm.twice]
  congr 1 <;> simp only [vmul_comm, vadd_assoc, vadd_comm, vadd_left_comm]

theorem formal_adjugate_identity_left (v : Norm.Coordinates) :
    formalMultiply (Norm.formalAdjugate v) v = formalScalar (Norm.formalNorm v) := by
  rw [formal_multiply_comm, formal_adjugate_identity]

/-- Evaluation of the formal variable at the concrete extension generator. -/
def recompose (v : Norm.Coordinates) : Ext3 := Norm.recomposeFormalAdjugate v

theorem recompose_product (x y : Norm.Coordinates) :
    recompose (formalMultiply x y) = recompose x ⊗ recompose y := by
  apply Subtype.eq
  simp only [recompose, formalMultiply, Norm.recomposeFormalAdjugate,
    Norm.timesTheta, Norm.timesThetaSquared, Norm.twice, Verifier.add, Verifier.mul,
    Arithmetic.eadd, Arithmetic.emul, Arithmetic.add, Arithmetic.mul, Arithmetic.reduce,
    Nat.mod_add_mod, Nat.add_mod_mod, nat_mod_mul_left, nat_mod_mul_right]
  congr 1 <;> congr 1 <;> simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul] <;> ac_rfl

theorem recompose_scalar (x : Ext3) : recompose (formalScalar x) = x := by
  have hz : Norm.timesTheta zero = zero := rfl
  have hz2 : Norm.timesThetaSquared zero = zero := rfl
  simp only [recompose, formalScalar, Norm.recomposeFormalAdjugate, hz, hz2, vadd_zero]

theorem recomposed_adjugate_identity (v : Norm.Coordinates) :
    recompose v ⊗ Norm.recomposeFormalAdjugate (Norm.formalAdjugate v) = Norm.formalNorm v := by
  change recompose v ⊗ recompose (Norm.formalAdjugate v) = Norm.formalNorm v
  rw [← recompose_product, formal_adjugate_identity, recompose_scalar]

/-- Sum form (the WHIR final MLE loop) equals the PCS difference-form butterfly
    on canonical values. This statement does not assert random-point binding. -/
theorem sum_difference_butterfly (even odd r : Ext3) :
    Verifier.add (even ⊗ (Norm.one ⊖ r)) (odd ⊗ r) =
      Verifier.add even (r ⊗ (odd ⊖ even)) := by
  simp only [vmul_sub, vmul_one, vsub_as_add_neg, vmul_add, vmul_neg]
  simp only [vmul_comm, vadd_assoc, vadd_comm, vadd_left_comm]

theorem whir_sum_equals_packed_butterfly (even odd r : Arithmetic.Ext3)
    (he : Arithmetic.Canonical even) (ho : Arithmetic.Canonical odd) (hr : Arithmetic.Canonical r) :
    WhirFinal.sumButterfly even odd r = Arithmetic.butterfly even odd r := by
  exact congrArg Subtype.val (sum_difference_butterfly ⟨even, he⟩ ⟨odd, ho⟩ ⟨r, hr⟩)

theorem even_sum_layer_equals_packed_layer (r : Arithmetic.Ext3) (hr : Arithmetic.Canonical r) :
    ∀ (values : List Arithmetic.Ext3), values.length % 2 = 0 →
      (∀ v ∈ values, Arithmetic.Canonical v) → WhirFinal.sumLayer r values = Packed.layer r values
  | [], _, _ => rfl
  | [a], he, _ => by simp at he
  | a :: b :: rest, he, hc => by
      have ha := hc a (by simp)
      have hb := hc b (by simp)
      have hrest : ∀ v ∈ rest, Arithmetic.Canonical v := fun v hv => hc v (by simp [hv])
      have heven : rest.length % 2 = 0 := by simp only [List.length_cons] at he; omega
      rw [WhirFinal.sumLayer, Packed.layer, whir_sum_equals_packed_butterfly a b r ha hb hr,
        even_sum_layer_equals_packed_layer r hr rest heven hrest]

theorem full_sum_layers_equal_packed_layers (point values : List Arithmetic.Ext3)
    (hp : ∀ r ∈ point, Arithmetic.Canonical r) (hv : ∀ v ∈ values, Arithmetic.Canonical v)
    (hs : values.length = 2 ^ point.length) :
    WhirFinal.foldLayers point values = Packed.foldLayers point values := by
  induction point generalizing values with
  | nil => rfl
  | cons r rs ih =>
      have hr := hp r (by simp)
      have ht : ∀ x ∈ rs, Arithmetic.Canonical x := fun x hx => hp x (by simp [hx])
      have hshape : values.length = 2 * 2 ^ rs.length := by
        simpa only [List.length_cons, Nat.pow_succ, Nat.mul_comm] using hs
      have heven : values.length % 2 = 0 := by rw [hshape]; omega
      simp only [WhirFinal.foldLayers, Packed.foldLayers]
      rw [even_sum_layer_equals_packed_layer r hr values heven hv]
      exact ih (Packed.layer r values) ht (Packed.layer_canonical r values)
        (Packed.layer_even_shape r values _ hshape)

theorem final_polynomial_equals_packed_fold (values randomness : List Arithmetic.Ext3)
    (hr : ∀ r ∈ randomness, Arithmetic.Canonical r) (hv : ∀ v ∈ values, Arithmetic.Canonical v)
    (hs : values.length = 2 ^ randomness.length) :
    WhirFinal.finalPolynomial values randomness = Packed.fold values randomness.reverse := by
  unfold WhirFinal.finalPolynomial Packed.fold
  rw [full_sum_layers_equal_packed_layers randomness.reverse values]
  · intro r h
    exact hr r (by simpa using h)
  · exact hv
  · simpa using hs

def liftCoordinates (a : Ext3) : Norm.Coordinates :=
  ⟨Norm.embed a.val.c0, Norm.embed a.val.c1, Norm.embed a.val.c2⟩

theorem recompose_lifted_coordinates (a : Ext3) : recompose (liftCoordinates a) = a := by
  apply Subtype.eq
  have h0 := Nat.mod_eq_of_lt a.property.1
  have h1 := Nat.mod_eq_of_lt a.property.2.1
  have h2 := Nat.mod_eq_of_lt a.property.2.2
  simp [recompose, liftCoordinates, Norm.recomposeFormalAdjugate, Norm.embed,
    Norm.timesTheta, Norm.timesThetaSquared, Verifier.add,
    Arithmetic.fromBase, Arithmetic.eadd, Arithmetic.add, Arithmetic.reduce, h0, h1, h2]

theorem lifted_adjugate_matches_inverse_formula (a : Ext3) :
    (Norm.recomposeFormalAdjugate (Norm.formalAdjugate (liftCoordinates a))).val =
      WhirFinal.adjugate a.val := by
  simp [Norm.recomposeFormalAdjugate, Norm.formalAdjugate, liftCoordinates,
    Norm.embed, Norm.square, Norm.twice, Norm.timesTheta, Norm.timesThetaSquared,
    Verifier.add, Verifier.mul, Verifier.sub, Arithmetic.fromBase,
    Arithmetic.eadd, Arithmetic.emul, Arithmetic.esub, WhirFinal.adjugate,
    Arithmetic.add, Arithmetic.mul, Arithmetic.sub, Arithmetic.reduce,
    nat_mod_mul_left, nat_mod_mul_right, Nat.two_mul]

theorem lifted_norm_matches_inverse_formula (a : Ext3) :
    (Norm.formalNorm (liftCoordinates a)).val = Arithmetic.fromBase (WhirFinal.norm a.val) := by
  simp [Norm.formalNorm, Norm.formalNormFromAdjugate, Norm.formalAdjugate, liftCoordinates,
    Norm.embed, Norm.square, Norm.twice, Verifier.add, Verifier.mul, Verifier.sub,
    Arithmetic.fromBase, Arithmetic.eadd, Arithmetic.emul, Arithmetic.esub,
    WhirFinal.norm, WhirFinal.adjugate,
    Arithmetic.add, Arithmetic.mul, Arithmetic.sub, Arithmetic.reduce,
    nat_mod_mul_left, nat_mod_mul_right, Nat.two_mul]

theorem inverse_adjugate_identity (a : Ext3) :
    Arithmetic.emul a.val (WhirFinal.adjugate a.val) = Arithmetic.fromBase (WhirFinal.norm a.val) := by
  have h := congrArg Subtype.val (recomposed_adjugate_identity (liftCoordinates a))
  change Arithmetic.emul (recompose (liftCoordinates a)).val
    (Norm.recomposeFormalAdjugate (Norm.formalAdjugate (liftCoordinates a))).val =
      (Norm.formalNorm (liftCoordinates a)).val at h
  rw [recompose_lifted_coordinates, lifted_adjugate_matches_inverse_formula,
    lifted_norm_matches_inverse_formula] at h
  exact h

theorem inverse_adjugate_canonical (a : Ext3) : Arithmetic.Canonical (WhirFinal.adjugate a.val) := by
  rw [← lifted_adjugate_matches_inverse_formula a]
  exact (Norm.recomposeFormalAdjugate (Norm.formalAdjugate (liftCoordinates a))).property

theorem embedded_multiplication (a b : Nat) :
    Norm.embed a ⊗ Norm.embed b = Norm.embed (Arithmetic.mul a b) := by
  apply Subtype.eq
  simp [Norm.embed, Verifier.mul, Arithmetic.emul, Arithmetic.fromBase,
    Arithmetic.add, Arithmetic.mul, Arithmetic.reduce, nat_mod_mul_left, nat_mod_mul_right]

theorem inverse_candidate_product (a : Ext3) (n : Nat) :
    Arithmetic.emul a.val (Arithmetic.scalar (WhirFinal.adjugate a.val) n) =
      Arithmetic.fromBase (Arithmetic.mul (WhirFinal.norm a.val) n) := by
  let adj : Ext3 := ⟨WhirFinal.adjugate a.val, inverse_adjugate_canonical a⟩
  have hadj : a ⊗ adj = Norm.embed (WhirFinal.norm a.val) := Subtype.eq (inverse_adjugate_identity a)
  have h : a ⊗ Verifier.scalar adj n = Norm.embed (Arithmetic.mul (WhirFinal.norm a.val) n) := by
    rw [scalar_as_embedded_mul, ← vmul_assoc, hadj, embedded_multiplication]
  exact congrArg Subtype.val h

/-- The actual inverse routine is reduced to its scalar exponentiation result.
    This is NOT the missing Fermat certificate and does not infer that the
    right-hand side is one merely from nonzero input or nonzero norm. -/
theorem inverse_success_reduces_to_scalar_product (a : Ext3) (result : Arithmetic.Ext3)
    (h : WhirFinal.inverse a.val = some result) :
    ∃ n, WhirFinal.modPowLoop 64 (WhirFinal.norm a.val) (Arithmetic.modulus - 2) 1 = some n ∧
      Arithmetic.emul a.val result = Arithmetic.fromBase (Arithmetic.mul (WhirFinal.norm a.val) n) := by
  unfold WhirFinal.inverse at h
  split at h
  · contradiction
  · cases hn : WhirFinal.modPowLoop 64 (WhirFinal.norm a.val) (Arithmetic.modulus - 2) 1 with
    | none => simp [hn] at h
    | some n =>
        simp only [hn, Option.some.injEq] at h
        subst result
        exact ⟨n, rfl, inverse_candidate_product a n⟩

end Audit.Wire3.NormIdentity
