import Audit.Wire3.WhirPolynomial

/-!
# Outer MLE coefficient rounds: actual reconstruction and polynomial bridge

Source: OuterLogupExt3Verifier.sol _evaluateExt3RoundDynamic (306–321),
coefficients.rs evaluate_ext3_coefficient_round (77–95), and verifier_v2.rs
preflight/lockstep round update (210–229,281–302). GateExt3ProverState.current_round
in sumcheck/gate_ext3_v2.rs sends coefficients[1..]; this file does NOT prove
that its interpolation equals the intended circuit/gate relation.

The existing Verifier.evaluateRound, including its forward coefficient sum,
the concrete scalar (p+1)/2, and constant-first reverse Horner loop, is retained.
It is NOT the inner WHIR quadratic (which sends c0/c2 and reconstructs c1).
All field values are the constructed GoldilocksExt3Field.Element, wrapping
the actual canonical three-limb arithmetic. No new Field/decoder/evaluator
observation is supplied. The half scalar is proved to be the inverse of two.
The Solidity log lane's fixed-MAX_DEGREE loop agrees with this dynamic loop
only under its existing preflight coefficient-count=5 condition. Generic
roundStep lemmas below concern the executable audit model; they do not remove
that source preflight condition or prove the gate prover's degree correctness.

Root counts concern fixed different claims and fixed coefficient lists at
distinct field points, not genuine circuit truth, adaptive transcript fixedness,
uniform challenges, ROM/Keccak security or full MLE/PCS soundness. The low-level
Rust/EVM/assembly refinement and byte/config provenance remain separate.
-/
namespace Audit.Wire3.OuterRound
open Audit.Wire3 GoldilocksExt3Field WhirPolynomial
set_option maxRecDepth 4096

def half : Element := ((Arithmetic.modulus + 1) / 2 : Nat)

theorem concrete_half_times_two : half * (2 : Element) = 1 := by
  apply element_eq
  apply Subtype.eq
  decide

theorem two_times_concrete_half : (2 : Element) * half = 1 := by
  rw [mul_comm]
  exact concrete_half_times_two

theorem two_ne_zero : (2 : Element) ≠ 0 := by
  intro hz
  have h := concrete_half_times_two
  rw [hz,mul_zero] at h
  exact zero_ne_one h

theorem half_is_actual_inverse_two : half = (2 : Element)⁻¹ := by
  have h := congrArg (fun x : Element => x * (2 : Element)⁻¹) concrete_half_times_two
  simpa only [mul_assoc,mul_inv_cancel two_ne_zero,mul_one,one_mul] using h

def coefficientSum (cs : List Element) : Element := cs.foldl (· + ·) 0

def constantCoefficient (claim : Element) (cs : List Element) : Element :=
  (claim - coefficientSum cs) * half

def coefficients (claim : Element) (cs : List Element) : List Element :=
  constantCoefficient claim cs :: cs

def evaluate (claim : Element) (cs : List Element) (r : Element) : Element :=
  (cs.reverse.foldl (fun acc c => acc * r + c) 0) * r + constantCoefficient claim cs

noncomputable def polynomial (claim : Element) (cs : List Element) : Polynomial Element :=
  WhirPolynomial.ofCoefficients (coefficients claim cs)

theorem source_sum_fold_exact (cs : List Element) (acc : Element) :
    (cs.foldl (· + ·) acc).toVerifier =
      (cs.map Element.toVerifier).foldl Verifier.add acc.toVerifier := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c _ ih => exact ih (acc+c)

theorem source_horner_fold_exact (cs : List Element) (r acc : Element) :
    (cs.foldl (fun a c => a*r+c) acc).toVerifier =
      (cs.map Element.toVerifier).foldl
        (fun a c => Verifier.add (Verifier.mul a r.toVerifier) c) acc.toVerifier := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c _ ih => exact ih (acc*r+c)

theorem actual_constant_coefficient_exact (claim : Element) (cs : List Element) :
    (constantCoefficient claim cs).toVerifier =
      Verifier.scalar
        (Verifier.sub claim.toVerifier ((cs.map Element.toVerifier).foldl Verifier.add Verifier.zero))
        ((Arithmetic.modulus+1)/2) := by
  rw [Algebra.scalar_as_embedded_mul]
  change Verifier.mul (Verifier.sub claim.toVerifier (coefficientSum cs).toVerifier)
      (Norm.embed ((Arithmetic.modulus+1)/2)) = _
  rw [coefficientSum,source_sum_fold_exact]
  rfl

theorem constant_coefficient_is_division_by_two (claim : Element) (cs : List Element) :
    constantCoefficient claim cs = (claim-coefficientSum cs)/2 := by
  rw [constantCoefficient,half_is_actual_inverse_two,div_eq_mul_inv]

theorem actual_evaluate_round_exact (claim : Element) (cs : List Element) (r : Element) :
    (evaluate claim cs r).toVerifier =
      Verifier.evaluateRound claim.toVerifier (cs.map Element.toVerifier) r.toVerifier := by
  unfold evaluate Verifier.evaluateRound
  change Verifier.add
    (Verifier.mul (cs.reverse.foldl (fun a c => a*r+c) 0).toVerifier r.toVerifier)
    (constantCoefficient claim cs).toVerifier = _
  rw [source_horner_fold_exact,actual_constant_coefficient_exact,List.map_reverse]
  rfl

theorem coefficient_polynomial_is_field_horner (cs : List Element) (r : Element) :
    (WhirPolynomial.ofCoefficients cs).eval r =
      cs.reverse.foldl (fun a c => a*r+c) 0 := by
  induction cs with
  | nil => simp [WhirPolynomial.ofCoefficients]
  | cons c cs ih =>
    simp only [WhirPolynomial.ofCoefficients,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_X,Polynomial.eval_C,List.reverse_cons,List.foldl_append,
      List.foldl_cons,List.foldl_nil,ih]

theorem polynomial_eval_exact (claim : Element) (cs : List Element) (r : Element) :
    (polynomial claim cs).eval r = evaluate claim cs r := by
  simp only [polynomial,coefficients,WhirPolynomial.ofCoefficients,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,coefficient_polynomial_is_field_horner]
  rfl

theorem actual_round_is_polynomial_eval (claim : Element) (cs : List Element) (r : Element) :
    Verifier.evaluateRound claim.toVerifier (cs.map Element.toVerifier) r.toVerifier =
      ((polynomial claim cs).eval r).toVerifier := by
  rw [polynomial_eval_exact,actual_evaluate_round_exact]

theorem full_coefficient_count (claim : Element) (cs : List Element) :
    (coefficients claim cs).length = cs.length+1 := rfl

theorem constant_coefficient_position (claim : Element) (cs : List Element) :
    (polynomial claim cs).coeff 0 = constantCoefficient claim cs :=
  WhirPolynomial.coefficient_exact (coefficients claim cs) 0

theorem nonconstant_coefficient_positions (claim : Element) (cs : List Element) (i : Nat) :
    (polynomial claim cs).coeff (i+1) = cs.getD i 0 := by
  exact WhirPolynomial.coefficient_exact (coefficients claim cs) (i+1)

theorem polynomial_degree_at_most_message_length (claim : Element) (cs : List Element) :
    (polynomial claim cs).natDegree ≤ cs.length := by
  have h := WhirPolynomial.degree_bound_including_empty (coefficients claim cs)
  simpa only [full_coefficient_count,Nat.add_sub_cancel] using h

theorem evaluate_at_zero (claim : Element) (cs : List Element) :
    evaluate claim cs 0 = constantCoefficient claim cs := by
  simp [evaluate]

theorem coefficient_sum_fold_eq_list_sum (cs : List Element) (acc : Element) :
    cs.foldl (·+·) acc = acc+cs.sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons,List.sum_cons,ih,add_assoc]

theorem coefficient_sum_eq_list_sum (cs : List Element) : coefficientSum cs = cs.sum := by
  simpa only [coefficientSum,zero_add] using coefficient_sum_fold_eq_list_sum cs 0

theorem evaluate_at_one (claim : Element) (cs : List Element) :
    evaluate claim cs 1 = coefficientSum cs + constantCoefficient claim cs := by
  simp only [evaluate,mul_one]
  rw [show cs.reverse.foldl (fun acc c => acc+c) 0 = coefficientSum cs by
    rw [coefficient_sum_fold_eq_list_sum,List.sum_reverse,zero_add,← coefficient_sum_eq_list_sum]]

theorem endpoint_sum_is_claim (claim : Element) (cs : List Element) :
    evaluate claim cs 0 + evaluate claim cs 1 = claim := by
  rw [evaluate_at_zero,evaluate_at_one,constantCoefficient]
  calc
    (claim-coefficientSum cs)*half +
        (coefficientSum cs+(claim-coefficientSum cs)*half) =
      coefficientSum cs+(claim-coefficientSum cs)*(half*2) := by ring
    _ = claim := by rw [concrete_half_times_two,mul_one]; ring

theorem polynomial_endpoint_sum_is_claim (claim : Element) (cs : List Element) :
    (polynomial claim cs).eval 0 + (polynomial claim cs).eval 1 = claim := by
  simpa only [polynomial_eval_exact] using endpoint_sum_is_claim claim cs

theorem actual_endpoint_sum_is_claim (claim : Element) (cs : List Element) :
    Verifier.add
      (Verifier.evaluateRound claim.toVerifier (cs.map Element.toVerifier) Verifier.zero)
      (Verifier.evaluateRound claim.toVerifier (cs.map Element.toVerifier) Norm.one) = claim.toVerifier := by
  change Verifier.add
    (Verifier.evaluateRound claim.toVerifier (cs.map Element.toVerifier) (0 : Element).toVerifier)
    (Verifier.evaluateRound claim.toVerifier (cs.map Element.toVerifier) (1 : Element).toVerifier) = _
  rw [← actual_evaluate_round_exact,← actual_evaluate_round_exact]
  exact congrArg Element.toVerifier (endpoint_sum_is_claim claim cs)

theorem different_claims_give_different_polynomials (claimA claimB : Element)
    (a b : List Element) (hne : claimA ≠ claimB) : polynomial claimA a ≠ polynomial claimB b := by
  intro he
  apply hne
  rw [← polynomial_endpoint_sum_is_claim claimA a,← polynomial_endpoint_sum_is_claim claimB b,he]

def actualAgreementPoints (claimA claimB : Element) (a b : List Element)
    (domain : Finset Element) : Finset Element := domain.filter (fun r =>
      Verifier.evaluateRound claimA.toVerifier (a.map Element.toVerifier) r.toVerifier =
      Verifier.evaluateRound claimB.toVerifier (b.map Element.toVerifier) r.toVerifier)

theorem actual_agreement_iff_polynomial (claimA claimB : Element) (a b : List Element) (r : Element) :
    Verifier.evaluateRound claimA.toVerifier (a.map Element.toVerifier) r.toVerifier =
      Verifier.evaluateRound claimB.toVerifier (b.map Element.toVerifier) r.toVerifier ↔
    (polynomial claimA a).eval r = (polynomial claimB b).eval r := by
  rw [actual_round_is_polynomial_eval,actual_round_is_polynomial_eval]
  exact ⟨element_eq _ _,congrArg Element.toVerifier⟩

theorem fixed_different_claims_agree_at_most_degree (claimA claimB : Element)
    (a b : List Element) (hne : claimA ≠ claimB) (d : Nat)
    (ha : a.length ≤ d) (hb : b.length ≤ d) (domain : Finset Element) :
    (actualAgreementPoints claimA claimB a b domain).card ≤ d := by
  have he : actualAgreementPoints claimA claimB a b domain =
      WhirPolynomial.agreementPoints (polynomial claimA a) (polynomial claimB b) domain := by
    apply Finset.ext
    intro r
    simp only [actualAgreementPoints,WhirPolynomial.agreementPoints,Finset.mem_filter,
      actual_agreement_iff_polynomial]
  rw [he]
  exact WhirPolynomial.fixed_polynomial_agreements_le_degree _ _
    (different_claims_give_different_polynomials claimA claimB a b hne) d
    ((polynomial_degree_at_most_message_length claimA a).trans ha)
    ((polynomial_degree_at_most_message_length claimB b).trans hb) domain

theorem fixed_different_claims_equal_length_bound (claimA claimB : Element)
    (a b : List Element) (hne : claimA ≠ claimB) (hlen : a.length=b.length) (domain : Finset Element) :
    (actualAgreementPoints claimA claimB a b domain).card ≤ a.length :=
  fixed_different_claims_agree_at_most_degree claimA claimB a b hne a.length
    (Nat.le_refl _) (by omega) domain

def lift (a : Verifier.Ext3) : Element := ⟨a⟩

theorem lift_list_roundtrip (cs : List Verifier.Ext3) :
    (cs.map lift).map Element.toVerifier = cs := by simp [List.map_map,lift,Function.comp_def]

theorem actual_typed_round_is_polynomial_eval (claim r : Verifier.Ext3) (cs : List Verifier.Ext3) :
    Verifier.evaluateRound claim cs r =
      ((polynomial (lift claim) (cs.map lift)).eval (lift r)).toVerifier := by
  simpa only [lift_list_roundtrip,lift] using
    actual_round_is_polynomial_eval (lift claim) (cs.map lift) (lift r)

theorem fixed_different_typed_claims_agreement_bound (claimA claimB : Verifier.Ext3)
    (a b : List Verifier.Ext3) (hne : claimA ≠ claimB) (d : Nat)
    (ha : a.length ≤ d) (hb : b.length ≤ d) (domain : Finset Element) :
    (domain.filter (fun r => Verifier.evaluateRound claimA a r.toVerifier =
      Verifier.evaluateRound claimB b r.toVerifier)).card ≤ d := by
  have hn : lift claimA ≠ lift claimB := fun he => hne (congrArg Element.toVerifier he)
  simpa only [actualAgreementPoints,lift_list_roundtrip,lift] using
    fixed_different_claims_agree_at_most_degree (lift claimA) (lift claimB) (a.map lift) (b.map lift)
      hn d (by simpa using ha) (by simpa using hb) domain

/-- This keeps the exact coupled commit observation and both of its distinct
challenges. It neither invents a second transcript nor asserts its randomness. -/
theorem actual_coupled_round_uses_both_derived_polynomials (commit : Verifier.CommitRound)
    (s : Verifier.RoundState) (m : Verifier.CoupledMessage) :
    let r := commit s.transcript s.roundIndex m.1 m.2
    let next := Verifier.roundStep commit s m
    next.logClaim = ((polynomial (lift s.logClaim) (m.1.map lift)).eval (lift r.log)).toVerifier ∧
    next.gateClaim = ((polynomial (lift s.gateClaim) (m.2.map lift)).eval (lift r.gate)).toVerifier ∧
    next.logPoint = s.logPoint++[r.log] ∧ next.gatePoint = s.gatePoint++[r.gate] ∧
    next.transcript = r.transcript ∧ next.roundIndex=s.roundIndex+1 := by
  dsimp only [Verifier.roundStep]
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · simpa only [lift_list_roundtrip,lift] using
      actual_round_is_polynomial_eval (lift s.logClaim) (m.1.map lift)
        (lift (commit s.transcript s.roundIndex m.1 m.2).log)
  · simpa only [lift_list_roundtrip,lift] using
      actual_round_is_polynomial_eval (lift s.gateClaim) (m.2.map lift)
        (lift (commit s.transcript s.roundIndex m.1 m.2).gate)

/-- claim=17, [a1,a2]=[2,3] reconstructs a0=6 and evaluates to 91 at 5. -/
theorem nonconstant_outer_round_example :
    Verifier.evaluateRound (Norm.embed 17) [Norm.embed 2,Norm.embed 3] (Norm.embed 5) =
      Norm.embed 91 := by decide

theorem empty_message_is_constant_half_claim :
    Verifier.evaluateRound (Norm.embed 10) [] (Norm.embed 123) = Norm.embed 5 := by decide

theorem nonbase_outer_round_example :
    Verifier.evaluateRound ⟨⟨0,10,0⟩,by decide⟩
      [⟨⟨0,2,0⟩,by decide⟩,⟨⟨0,2,0⟩,by decide⟩] (Norm.embed 3) =
      ⟨⟨0,27,0⟩,by decide⟩ := by decide

end Audit.Wire3.OuterRound
