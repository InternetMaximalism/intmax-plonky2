import Audit.Wire3.WhirPolynomial

/-!
# Degree-five norm/logUp row expressions over the actual concrete field

Source: permutation/norm_logup.rs formal_adjugate_from_coords,
formal_norm_from_coords, denominator_coords_ext3, evaluate_target_from_values,
line_value, round_sum_at; Norm.formalAdjugate/formalNorm/denominatorTerms/wireStep.
The variable X is the NEXT single sumcheck coordinate, not an extension limb.
Every already partially-bound MLE contributes low+X*(high-low). Challenges,
their individual embedded base limbs, VK scalars, lambda/eta powers, bound PI
prefix weights and raw public-input values are fixed with respect to X.

The coordinates a,b,c are themselves polynomials over GoldilocksExt3Field.
Their formal cubic algebra is NOT a field: no nonzero formal-norm or inverse
assertion is used. Only the concrete field operations and polynomial laws enter.
Degree <=5 is an upper bound, not exact degree for every chosen input.

The bounded scope is the row formulas and finite sums. Extraction of every
low/high endpoint from the source's mutable arrays, complete PI suffix routing,
interpolation-to-sent-coefficients, circuit truth/individual PI equality,
transcript distributions, source compiler/word/memory refinement and PCS
soundness remain separate obligations.
-/
namespace Audit.Wire3.NormPolynomial
noncomputable section
set_option maxRecDepth 2048
open Audit.Wire3 GoldilocksExt3Field
abbrev Poly := Polynomial Element

def lift (x : Verifier.Ext3) : Element := ⟨x⟩

structure Line where
  low : Element
  high : Element

def affine (a : Line) : Poly := Polynomial.C a.low + Polynomial.X * Polynomial.C (a.high-a.low)

theorem affine_evaluation (a : Line) (x : Element) :
    (affine a).eval x = a.low+x*(a.high-a.low) := by
  simp only [affine,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]

theorem affine_evaluation_actual (a : Line) (x : Element) :
    ((affine a).eval x).toVerifier = Verifier.add a.low.toVerifier
      (Verifier.mul x.toVerifier (Verifier.sub a.high.toVerifier a.low.toVerifier)) := by
  rw [affine_evaluation]
  rfl

theorem affine_degree (a : Line) : (affine a).natDegree ≤ 1 := by
  have hm : (Polynomial.X * Polynomial.C (a.high-a.low)).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_mul_le).trans (by simp)
  exact (Polynomial.natDegree_add_le _ _).trans (by simp only [Polynomial.natDegree_C]; omega)

theorem degree_add {a b : Poly} {n : Nat} (ha : a.natDegree ≤ n) (hb : b.natDegree ≤ n) :
    (a+b).natDegree ≤ n := (Polynomial.natDegree_add_le a b).trans (max_le ha hb)

theorem degree_sub {a b : Poly} {n : Nat} (ha : a.natDegree ≤ n) (hb : b.natDegree ≤ n) :
    (a-b).natDegree ≤ n := (Polynomial.natDegree_sub_le a b).trans (max_le ha hb)

theorem degree_mul {a b : Poly} {n m : Nat} (ha : a.natDegree ≤ n) (hb : b.natDegree ≤ m) :
    (a*b).natDegree ≤ n+m := Polynomial.natDegree_mul_le.trans (Nat.add_le_add ha hb)

theorem degree_fixed_mul (c : Element) {a : Poly} {n : Nat} (ha : a.natDegree ≤ n) :
    (Polynomial.C c*a).natDegree ≤ n := by
  simpa only [Polynomial.natDegree_C,Nat.zero_add] using
    (Polynomial.natDegree_mul_le (p := Polynomial.C c) (q := a)).trans (by simpa using ha)

structure Coordinates where
  a : Poly
  b : Poly
  c : Poly

def evaluateCoordinates (v : Coordinates) (x : Element) : Norm.Coordinates :=
  ⟨(v.a.eval x).toVerifier,(v.b.eval x).toVerifier,(v.c.eval x).toVerifier⟩

def adjugate (v : Coordinates) : Coordinates :=
  ⟨v.a*v.a-(v.b*v.c+v.b*v.c),
   (v.c*v.c+v.c*v.c)-v.a*v.b,
   v.b*v.b-v.a*v.c⟩

def formalNorm (v : Coordinates) : Poly :=
  let s := adjugate v
  v.a*s.a + ((v.c*s.b+v.b*s.c)+(v.c*s.b+v.b*s.c))

theorem adjugate_evaluation_actual (v : Coordinates) (x : Element) :
    evaluateCoordinates (adjugate v) x = Norm.formalAdjugate (evaluateCoordinates v x) := by
  simp only [evaluateCoordinates,adjugate,Norm.formalAdjugate,Algebra.norm_square_is_multiplication,
    Norm.twice,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_add]
  rfl

theorem formal_norm_evaluation_actual (v : Coordinates) (x : Element) :
    ((formalNorm v).eval x).toVerifier = Norm.formalNorm (evaluateCoordinates v x) := by
  have ha := adjugate_evaluation_actual v x
  have h0 := congrArg Norm.Coordinates.a ha
  have h1 := congrArg Norm.Coordinates.b ha
  have h2 := congrArg Norm.Coordinates.c ha
  simp only [evaluateCoordinates] at h0 h1 h2
  simp only [formalNorm,Polynomial.eval_add,Polynomial.eval_mul,add_exact,mul_exact,h0,h1,h2,
    Norm.formalNorm,Norm.formalNormFromAdjugate,Norm.twice,evaluateCoordinates]

def DegreeCoordinates (v : Coordinates) (n : Nat) : Prop :=
  v.a.natDegree ≤ n ∧ v.b.natDegree ≤ n ∧ v.c.natDegree ≤ n

theorem adjugate_degree (v : Coordinates) (hv : DegreeCoordinates v 1) :
    DegreeCoordinates (adjugate v) 2 := by
  rcases hv with ⟨ha,hb,hc⟩
  exact ⟨degree_sub (degree_mul ha ha) (degree_add (degree_mul hb hc) (degree_mul hb hc)),
    degree_sub (degree_add (degree_mul hc hc) (degree_mul hc hc)) (degree_mul ha hb),
    degree_sub (degree_mul hb hb) (degree_mul ha hc)⟩

theorem formal_norm_degree (v : Coordinates) (hv : DegreeCoordinates v 1) :
    (formalNorm v).natDegree ≤ 3 := by
  have hs := adjugate_degree v hv
  exact degree_add (degree_mul hv.1 hs.1)
    (degree_add (degree_add (degree_mul hv.2.2 hs.2.1) (degree_mul hv.2.1 hs.2.2))
      (degree_add (degree_mul hv.2.2 hs.2.1) (degree_mul hv.2.1 hs.2.2)))

def denominator (wire position : Poly) (beta gamma : Verifier.Ext3) : Coordinates :=
  ⟨Polynomial.C (beta.val.c0 : Element) + wire + position * Polynomial.C (gamma.val.c0 : Element),
   Polynomial.C (beta.val.c1 : Element) + position * Polynomial.C (gamma.val.c1 : Element),
   Polynomial.C (beta.val.c2 : Element) + position * Polynomial.C (gamma.val.c2 : Element)⟩

theorem denominator_evaluation_actual (wire position : Poly) (beta gamma : Verifier.Ext3) (x : Element) :
    evaluateCoordinates (denominator wire position beta gamma) x =
      Norm.denominatorCoordinates (wire.eval x).toVerifier (position.eval x).toVerifier beta gamma := by
  simp only [denominator,evaluateCoordinates,Norm.denominatorCoordinates,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Algebra.scalar_as_embedded_mul]
  rfl

theorem denominator_degree (wire position : Poly) (beta gamma : Verifier.Ext3)
    (hw : wire.natDegree ≤ 1) (hp : position.natDegree ≤ 1) :
    DegreeCoordinates (denominator wire position beta gamma) 1 := by
  have hc (n : Nat) : (Polynomial.C (n : Element)).natDegree ≤ 1 := by simp
  have hm (n : Nat) : (position * Polynomial.C (n : Element)).natDegree ≤ 1 := by
    simpa only [Polynomial.natDegree_C,Nat.add_zero] using
      (Polynomial.natDegree_mul_le (p := position) (q := Polynomial.C (n : Element))).trans (by simpa using hp)
  exact ⟨degree_add (degree_add (hc _) hw) (hm _),degree_add (hc _) (hm _),degree_add (hc _) (hm _)⟩

def theta : Element := ⟨⟨⟨0,1,0⟩,by decide⟩⟩
def thetaSquared : Element := ⟨⟨⟨0,0,1⟩,by decide⟩⟩

theorem theta_square_exact : theta*theta = thetaSquared := by decide

theorem theta_multiplication_actual (x : Element) :
    (theta*x).toVerifier = Norm.timesTheta x.toVerifier := by
  apply Subtype.eq
  have hc := x.toVerifier.property
  simp only [theta,mul_exact,Verifier.mul,Arithmetic.emul,Norm.timesTheta,
    Arithmetic.add,Arithmetic.mul,Arithmetic.reduce,Nat.zero_mul,Nat.one_mul,Nat.add_zero,Nat.zero_add,
    Nat.zero_mod,Nat.mod_eq_of_lt hc.1,Nat.mod_eq_of_lt hc.2.1,Nat.mod_eq_of_lt hc.2.2,
    Nat.mul_mod_mod,Nat.two_mul,Nat.mod_mod]

theorem theta_squared_multiplication_actual (x : Element) :
    (thetaSquared*x).toVerifier = Norm.timesThetaSquared x.toVerifier := by
  apply Subtype.eq
  have hc := x.toVerifier.property
  simp only [thetaSquared,mul_exact,Verifier.mul,Arithmetic.emul,Norm.timesThetaSquared,
    Arithmetic.add,Arithmetic.mul,Arithmetic.reduce,Nat.zero_mul,Nat.one_mul,Nat.add_zero,Nat.zero_add,
    Nat.zero_mod,Nat.mod_eq_of_lt hc.1,Nat.mod_eq_of_lt hc.2.1,Nat.mod_eq_of_lt hc.2.2,
    Nat.mul_mod_mod,Nat.two_mul,Nat.mod_mod]

def recompose (v : Coordinates) : Poly :=
  v.a+(Polynomial.C theta*v.b+Polynomial.C thetaSquared*v.c)

theorem recompose_evaluation_actual (v : Coordinates) (x : Element) :
    ((recompose v).eval x).toVerifier = Norm.recomposeFormalAdjugate (evaluateCoordinates v x) := by
  simp only [recompose,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,add_exact,
    theta_multiplication_actual,theta_squared_multiplication_actual,Norm.recomposeFormalAdjugate,evaluateCoordinates]

theorem recompose_adjugate_degree (v : Coordinates) (hv : DegreeCoordinates v 1) :
    (recompose (adjugate v)).natDegree ≤ 2 := by
  have hs := adjugate_degree v hv
  exact degree_add hs.1 (degree_add (degree_fixed_mul _ hs.2.1) (degree_fixed_mul _ hs.2.2))

def helperConstraint (helper : Poly) (v : Coordinates) : Poly := helper*formalNorm v-1

def inverseExpression (helper : Poly) (v : Coordinates) : Poly := helper*recompose (adjugate v)

theorem helper_constraint_degree (helper : Poly) (v : Coordinates)
    (hh : helper.natDegree ≤ 1) (hv : DegreeCoordinates v 1) :
    (helperConstraint helper v).natDegree ≤ 4 :=
  degree_sub (degree_mul hh (formal_norm_degree v hv)) (by simp)

theorem inverse_expression_degree (helper : Poly) (v : Coordinates)
    (hh : helper.natDegree ≤ 1) (hv : DegreeCoordinates v 1) :
    (inverseExpression helper v).natDegree ≤ 3 :=
  degree_mul hh (recompose_adjugate_degree v hv)

theorem helper_constraint_evaluation_actual (helper : Poly) (v : Coordinates) (x : Element) :
    ((helperConstraint helper v).eval x).toVerifier =
      Verifier.sub (Verifier.mul (helper.eval x).toVerifier
        (Norm.formalNorm (evaluateCoordinates v x))) Norm.one := by
  simp only [helperConstraint,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_one,
    sub_exact,mul_exact,one_exact,formal_norm_evaluation_actual]

theorem inverse_expression_evaluation_actual (helper : Poly) (v : Coordinates) (x : Element) :
    ((inverseExpression helper v).eval x).toVerifier =
      Verifier.mul (helper.eval x).toVerifier
        (Norm.recomposeFormalAdjugate (Norm.formalAdjugate (evaluateCoordinates v x))) := by
  simp only [inverseExpression,Polynomial.eval_mul,mul_exact,recompose_evaluation_actual,
    adjugate_evaluation_actual]

/-- Values used by exactly one iteration of `Norm.wireStep`. -/
structure WireValues where
  wire : Verifier.Ext3
  identityPosition : Verifier.Ext3
  sigmaPosition : Verifier.Ext3
  identityHelper : Verifier.Ext3
  sigmaHelper : Verifier.Ext3

def actualContribution (ch : Norm.Challenges) (lambdaPower : Verifier.Ext3)
    (v : WireValues) : Verifier.Ext3 × Verifier.Ext3 :=
  let idTerms := Norm.denominatorTerms v.wire v.identityPosition ch.beta ch.gamma
  let sigmaTerms := Norm.denominatorTerms v.wire v.sigmaPosition ch.beta ch.gamma
  (Verifier.mul lambdaPower (Verifier.add
    (Verifier.sub (Verifier.mul v.identityHelper idTerms.1) Norm.one)
    (Verifier.mul ch.rho (Verifier.sub (Verifier.mul v.sigmaHelper sigmaTerms.1) Norm.one))),
   Verifier.sub (Verifier.mul v.identityHelper idTerms.2) (Verifier.mul v.sigmaHelper sigmaTerms.2))

def actualWireValues (c : Verifier.Config) (t : Verifier.NormTerminalInput)
    (subgroup : Verifier.Ext3) (index : Nat) : WireValues :=
  ⟨t.witness.getD index Verifier.zero,
   Verifier.scalar subgroup ((c.kIs.getD index (Verifier.base 0)).val),
   t.preprocessed.getD (c.numConstants+index) Verifier.zero,
   t.normInverse.getD index Verifier.zero,
   t.normInverse.getD (c.numRouted+index) Verifier.zero⟩

theorem wire_step_contribution_exact (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (subgroup : Verifier.Ext3) (index : Nat) (s : Norm.WireState) :
    ((Norm.wireStep c ch t subgroup index s).helperChecks,
     (Norm.wireStep c ch t subgroup index s).logupSum) =
    (Verifier.add s.helperChecks (actualContribution ch s.lambdaPower (actualWireValues c t subgroup index)).1,
     Verifier.add s.logupSum (actualContribution ch s.lambdaPower (actualWireValues c t subgroup index)).2) := rfl

/-- Five affine MLE slices; `k` and `lambdaPower` are fixed by VK/index/challenges. -/
structure WireLine where
  wire : Line
  sigma : Line
  identityHelper : Line
  sigmaHelper : Line
  k : Nat
  lambdaPower : Element

def identityPosition (subgroup : Line) (w : WireLine) : Poly := affine subgroup*Polynomial.C (w.k : Element)

def identityCoordinates (ch : Norm.Challenges) (subgroup : Line) (w : WireLine) : Coordinates :=
  denominator (affine w.wire) (identityPosition subgroup w) ch.beta ch.gamma

def sigmaCoordinates (ch : Norm.Challenges) (w : WireLine) : Coordinates :=
  denominator (affine w.wire) (affine w.sigma) ch.beta ch.gamma

def helperContribution (ch : Norm.Challenges) (subgroup : Line) (w : WireLine) : Poly :=
  Polynomial.C w.lambdaPower * (helperConstraint (affine w.identityHelper) (identityCoordinates ch subgroup w) +
    Polynomial.C (lift ch.rho) * helperConstraint (affine w.sigmaHelper) (sigmaCoordinates ch w))

def logupContribution (ch : Norm.Challenges) (subgroup : Line) (w : WireLine) : Poly :=
  inverseExpression (affine w.identityHelper) (identityCoordinates ch subgroup w) -
    inverseExpression (affine w.sigmaHelper) (sigmaCoordinates ch w)

def evaluatedWireValues (subgroup : Line) (w : WireLine) (x : Element) : WireValues :=
  ⟨((affine w.wire).eval x).toVerifier,
   Verifier.scalar ((affine subgroup).eval x).toVerifier w.k,
   ((affine w.sigma).eval x).toVerifier,
   ((affine w.identityHelper).eval x).toVerifier,
   ((affine w.sigmaHelper).eval x).toVerifier⟩

theorem identity_position_evaluation_actual (subgroup : Line) (w : WireLine) (x : Element) :
    ((identityPosition subgroup w).eval x).toVerifier =
      Verifier.scalar ((affine subgroup).eval x).toVerifier w.k := by
  simp only [identityPosition,Polynomial.eval_mul,Polynomial.eval_C,mul_exact,nat_cast_exact,
    Algebra.scalar_as_embedded_mul]

theorem identity_coordinates_degree (ch : Norm.Challenges) (subgroup : Line) (w : WireLine) :
    DegreeCoordinates (identityCoordinates ch subgroup w) 1 := by
  apply denominator_degree _ _ _ _ (affine_degree _)
  exact Polynomial.natDegree_mul_le.trans (by simpa [identityPosition] using affine_degree subgroup)

theorem sigma_coordinates_degree (ch : Norm.Challenges) (w : WireLine) :
    DegreeCoordinates (sigmaCoordinates ch w) 1 :=
  denominator_degree _ _ _ _ (affine_degree _) (affine_degree _)

theorem helper_contribution_degree (ch : Norm.Challenges) (subgroup : Line) (w : WireLine) :
    (helperContribution ch subgroup w).natDegree ≤ 4 :=
  degree_fixed_mul _ (degree_add
    (helper_constraint_degree _ _ (affine_degree _) (identity_coordinates_degree ch subgroup w))
    (degree_fixed_mul _ (helper_constraint_degree _ _ (affine_degree _) (sigma_coordinates_degree ch w))))

theorem logup_contribution_degree (ch : Norm.Challenges) (subgroup : Line) (w : WireLine) :
    (logupContribution ch subgroup w).natDegree ≤ 3 :=
  degree_sub
    (inverse_expression_degree _ _ (affine_degree _) (identity_coordinates_degree ch subgroup w))
    (inverse_expression_degree _ _ (affine_degree _) (sigma_coordinates_degree ch w))

theorem contributions_evaluation_actual (ch : Norm.Challenges) (subgroup : Line) (w : WireLine) (x : Element) :
    (((helperContribution ch subgroup w).eval x).toVerifier,
     ((logupContribution ch subgroup w).eval x).toVerifier) =
      actualContribution ch w.lambdaPower.toVerifier (evaluatedWireValues subgroup w x) := by
  simp only [helperContribution,logupContribution,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_add,Polynomial.eval_sub,mul_exact,add_exact,sub_exact,
    helper_constraint_evaluation_actual,inverse_expression_evaluation_actual,
    identityCoordinates,sigmaCoordinates,denominator_evaluation_actual,identity_position_evaluation_actual]
  rfl

/-- The ordered source accumulation, including its actual zero initial value. -/
def sumPolynomials {α : Type} (f : α → Poly) (xs : List α) : Poly :=
  xs.foldl (fun acc a => acc+f a) 0

theorem fold_polynomials_evaluation_actual {α : Type} (f : α → Poly) (xs : List α)
    (initial : Poly) (x : Element) :
    ((xs.foldl (fun acc a => acc+f a) initial).eval x).toVerifier =
      xs.foldl (fun acc a => Verifier.add acc ((f a).eval x).toVerifier) (initial.eval x).toVerifier := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldl_cons,Polynomial.eval_add,add_exact] using ih (initial+f a)

theorem sum_polynomials_evaluation_actual {α : Type} (f : α → Poly) (xs : List α) (x : Element) :
    ((sumPolynomials f xs).eval x).toVerifier =
      xs.foldl (fun acc a => Verifier.add acc ((f a).eval x).toVerifier) Verifier.zero := by
  simpa [sumPolynomials] using fold_polynomials_evaluation_actual f xs 0 x

theorem fold_polynomials_degree {α : Type} (f : α → Poly) (xs : List α) (initial : Poly) (n : Nat)
    (hf : ∀ a ∈ xs, (f a).natDegree ≤ n) (hi : initial.natDegree ≤ n) :
    (xs.foldl (fun acc a => acc+f a) initial).natDegree ≤ n := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons a xs ih =>
    exact ih (initial+f a) (fun b hb => hf b (by simp [hb])) (degree_add hi (hf a (by simp)))

theorem sum_polynomials_degree {α : Type} (f : α → Poly) (xs : List α) (n : Nat)
    (hf : ∀ a ∈ xs, (f a).natDegree ≤ n) : (sumPolynomials f xs).natDegree ≤ n :=
  fold_polynomials_degree f xs 0 n hf (by simp)

structure Row where
  eq : Line
  subgroup : Line
  wires : List WireLine

def rowPolynomial (ch : Norm.Challenges) (row : Row) : Poly :=
  affine row.eq * sumPolynomials (helperContribution ch row.subgroup) row.wires +
    Polynomial.C (lift ch.kappa) * sumPolynomials (logupContribution ch row.subgroup) row.wires

theorem row_degree_five (ch : Norm.Challenges) (row : Row) :
    (rowPolynomial ch row).natDegree ≤ 5 := by
  apply degree_add
  · exact degree_mul (affine_degree _) (sum_polynomials_degree _ _ 4 (fun w _ => helper_contribution_degree ch row.subgroup w))
  · exact (degree_fixed_mul _ (sum_polynomials_degree _ _ 3 (fun w _ => logup_contribution_degree ch row.subgroup w))).trans (by decide)

def actualRowEvaluation (ch : Norm.Challenges) (row : Row) (x : Element) : Verifier.Ext3 :=
  let contributions := fun w => actualContribution ch w.lambdaPower.toVerifier (evaluatedWireValues row.subgroup w x)
  Verifier.add
    (Verifier.mul ((affine row.eq).eval x).toVerifier
      (row.wires.foldl (fun acc w => Verifier.add acc (contributions w).1) Verifier.zero))
    (Verifier.mul ch.kappa
      (row.wires.foldl (fun acc w => Verifier.add acc (contributions w).2) Verifier.zero))

theorem row_evaluation_actual (ch : Norm.Challenges) (row : Row) (x : Element) :
    ((rowPolynomial ch row).eval x).toVerifier = actualRowEvaluation ch row x := by
  have hh (w : WireLine) : ((helperContribution ch row.subgroup w).eval x).toVerifier =
      (actualContribution ch w.lambdaPower.toVerifier (evaluatedWireValues row.subgroup w x)).1 :=
    congrArg Prod.fst (contributions_evaluation_actual ch row.subgroup w x)
  have hl (w : WireLine) : ((logupContribution ch row.subgroup w).eval x).toVerifier =
      (actualContribution ch w.lambdaPower.toVerifier (evaluatedWireValues row.subgroup w x)).2 :=
    congrArg Prod.snd (contributions_evaluation_actual ch row.subgroup w x)
  simp only [rowPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    add_exact,mul_exact,sum_polynomials_evaluation_actual,hh,hl]
  rfl

structure PiLine where
  row : Nat
  boundVariables : Nat
  prefixEq : Element
  etaPower : Element
  publicValue : Verifier.Base
  wire : Line

def piBoolean (a : PiLine) : Poly :=
  if a.row / 2 ^ a.boundVariables % 2 = 0 then 1-Polynomial.X else Polynomial.X

def piPolynomial (a : PiLine) : Poly :=
  Polynomial.C a.etaPower * (Polynomial.C a.prefixEq * piBoolean a) *
    (affine a.wire-Polynomial.C (a.publicValue.val : Element))

theorem pi_boolean_degree (a : PiLine) : (piBoolean a).natDegree ≤ 1 := by
  unfold piBoolean
  split
  · exact degree_sub (by simp) (by simp)
  · simp

theorem pi_boolean_evaluation_actual (a : PiLine) (x : Element) :
    ((piBoolean a).eval x).toVerifier = Norm.booleanFactor a.row a.boundVariables x.toVerifier := by
  unfold piBoolean Norm.booleanFactor
  split <;> simp only [Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,sub_exact,one_exact]

theorem pi_degree_two (a : PiLine) : (piPolynomial a).natDegree ≤ 2 :=
  degree_mul (degree_fixed_mul _ (degree_fixed_mul _ (pi_boolean_degree a)))
    (degree_sub (affine_degree _) (by simp))

def actualPiLineEvaluation (a : PiLine) (x : Element) : Verifier.Ext3 :=
  Verifier.mul (Verifier.mul a.etaPower.toVerifier
    (Verifier.mul a.prefixEq.toVerifier (Norm.booleanFactor a.row a.boundVariables x.toVerifier)))
    (Verifier.sub ((affine a.wire).eval x).toVerifier (Norm.embed a.publicValue.val))

theorem pi_evaluation_actual (a : PiLine) (x : Element) :
    ((piPolynomial a).eval x).toVerifier = actualPiLineEvaluation a x := by
  simp only [piPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,
    mul_exact,sub_exact,nat_cast_exact,pi_boolean_evaluation_actual]
  rfl

/-- Rust sums all suffix targets first, then adds xi times the ordered PI terms. -/
def roundPolynomial (ch : Norm.Challenges) (rows : List Row) (publicTerms : List PiLine) : Poly :=
  sumPolynomials (rowPolynomial ch) rows + Polynomial.C (lift ch.xi) * sumPolynomials piPolynomial publicTerms

theorem round_degree_five (ch : Norm.Challenges) (rows : List Row) (publicTerms : List PiLine) :
    (roundPolynomial ch rows publicTerms).natDegree ≤ 5 :=
  degree_add (sum_polynomials_degree _ _ 5 (fun row _ => row_degree_five ch row))
    ((degree_fixed_mul _ (sum_polynomials_degree _ _ 2 (fun a _ => pi_degree_two a))).trans (by decide))

theorem round_evaluation_actual (ch : Norm.Challenges) (rows : List Row) (publicTerms : List PiLine) (x : Element) :
    ((roundPolynomial ch rows publicTerms).eval x).toVerifier =
      Verifier.add (rows.foldl (fun acc row => Verifier.add acc (actualRowEvaluation ch row x)) Verifier.zero)
        (Verifier.mul ch.xi
          (publicTerms.foldl (fun acc a => Verifier.add acc (actualPiLineEvaluation a x)) Verifier.zero)) := by
  simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,add_exact,mul_exact,
    sum_polynomials_evaluation_actual,row_evaluation_actual,pi_evaluation_actual]
  rfl

theorem lift_repeated_multiplication (initial multiplier : Verifier.Ext3) (n : Nat) :
    lift (Norm.multiplyRepeated initial multiplier n) = lift initial * (lift multiplier)^n := by
  induction n generalizing initial with
  | zero => simp [Norm.multiplyRepeated]
  | succ n ih =>
    rw [Norm.multiplyRepeated,ih]
    change (lift initial*lift multiplier)*(lift multiplier)^n = _
    rw [pow_succ]
    ring

/-- Builds the precise fixed lambda^index weight, not an independent challenge. -/
def withLambdaPower (w : WireLine) (ch : Norm.Challenges) (index : Nat) : WireLine :=
  { w with lambdaPower := (lift ch.lambda)^index }

theorem indexed_lambda_matches_actual_loop (w : WireLine) (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (subgroup : Verifier.Ext3) (index : Nat) :
    (withLambdaPower w ch index).lambdaPower.toVerifier =
      (Norm.runWires c ch t subgroup 0 index Norm.wireStart).lambdaPower := by
  rw [Norm.run_wires_lambda_power]
  have h := lift_repeated_multiplication Norm.one ch.lambda index
  change lift (Norm.multiplyRepeated Norm.one ch.lambda index) = 1*(lift ch.lambda)^index at h
  rw [one_mul] at h
  exact (congrArg Element.toVerifier h).symm

def withEtaPower (a : PiLine) (eta : Verifier.Ext3) (index : Nat) : PiLine :=
  { a with etaPower := (lift eta)^index }

theorem indexed_eta_matches_actual_pi_count (a : PiLine) (eta : Verifier.Ext3)
    (wireMap : Verifier.Bytes) (witness point : List Verifier.Ext3) (pairs : List (Nat × Verifier.Base)) :
    (withEtaPower a eta pairs.length).etaPower.toVerifier =
      (pairs.foldl (Norm.piStep wireMap witness point eta) Norm.piStart).etaPower := by
  rw [Norm.pi_fold_eta_power]
  have h := lift_repeated_multiplication Norm.one eta pairs.length
  change lift (Norm.multiplyRepeated Norm.one eta pairs.length) = 1*(lift eta)^pairs.length at h
  rw [one_mul] at h
  exact (congrArg Element.toVerifier h).symm

/-- A nonconstant formal-coordinate check: the cubic is not replaced by
the actual field norm on the three Element-valued coordinates. -/
theorem pure_coordinate_norm (a : Poly) : formalNorm ⟨a,0,0⟩ = a^3 := by
  simp only [formalNorm,adjugate,mul_zero,zero_mul,add_zero,zero_add,sub_zero]
  ring

/-- The degree-five term really occurs: affine eq and helper, with one
affine formal denominator coordinate. This is an algebraic example, not a
claim that a particular circuit or proof uses these witnesses. -/
theorem fifth_degree_term_example :
    Polynomial.X * helperConstraint Polynomial.X ⟨Polynomial.X,0,0⟩ =
      (Polynomial.X : Poly)^5-Polynomial.X := by
  rw [helperConstraint,pure_coordinate_norm]
  ring

theorem fifth_degree_example_has_degree_five :
    (Polynomial.X * helperConstraint Polynomial.X ⟨Polynomial.X,0,0⟩).natDegree = 5 := by
  rw [fifth_degree_term_example,Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
  simp

theorem empty_round_is_zero (ch : Norm.Challenges) : roundPolynomial ch [] [] = 0 := by
  simp [roundPolynomial,sumPolynomials]

/-- A fixed DIFFERENT six-coefficient message polynomial and the fixed row
polynomial can agree on at most five distinct field points. This is not a
claim that the transcript is uniform or fixes either polynomial in advance. -/
theorem fixed_six_coefficient_message_agreement_bound (ch : Norm.Challenges) (rows : List Row)
    (publicTerms : List PiLine) (coefficients : List Element) (hlen : coefficients.length = 6)
    (hne : roundPolynomial ch rows publicTerms ≠ WhirPolynomial.ofCoefficients coefficients)
    (domain : Finset Element) :
    (WhirPolynomial.agreementPoints (roundPolynomial ch rows publicTerms)
      (WhirPolynomial.ofCoefficients coefficients) domain).card ≤ 5 := by
  apply WhirPolynomial.fixed_polynomial_agreements_le_degree _ _ hne 5
  · exact round_degree_five ch rows publicTerms
  · simpa only [hlen] using WhirPolynomial.degree_bound_including_empty coefficients

end
end Audit.Wire3.NormPolynomial
