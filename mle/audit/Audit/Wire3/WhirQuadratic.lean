import Audit.Wire3.WhirPolynomial
import Audit.Wire3.Sumcheck

/-!
# Actual WHIR quadratic updates as concrete Goldilocks polynomials

Source: SpongefishWhirVerify.sol `_phaseSumcheck`, lines 424–481: read c0/c2,
PoW, challenge, reconstruct c1 := claim - (c0 + c0 + c2), then Horner
((c2*r + c1)*r + c0). The executable function related here is the EXISTING
WhirFinal.quadratic, including its actual Nat.mod Ext3 arithmetic. Element
only wraps canonical values of that arithmetic; its Field laws are proved,
not assumed. No abstract evaluator replaces the actual update.

The symbolic Polynomial is noncomputable, whereas Message/coefficient
reconstruction/WhirFinal.quadratic remain executable. Bounds concern two
FIXED claim/message pairs and a Finset of DISTINCT field points. They do not
prove transcript fixedness, Fiat–Shamir independence, sampling distribution,
adaptive probability, genuine circuit truth, Merkle/PCS soundness, or
source/Yul/compiler refinement. The optional chain theorem has a visibly
conditional second chain, NOT an assertion that it is a circuit's truth.
-/
namespace Audit.Wire3.WhirQuadratic
open Audit.Wire3 GoldilocksExt3Field WhirPolynomial
open Polynomial

structure Message where
  c0 : Element
  c2 : Element

def Message.toRaw (m : Message) : WhirFinal.RoundMessage := ⟨raw m.c0, raw m.c2⟩

def linearCoefficient (claim : Element) (m : Message) : Element :=
  claim - ((m.c0 + m.c0) + m.c2)

def coefficients (claim : Element) (m : Message) : List Element :=
  [m.c0, linearCoefficient claim m, m.c2]

noncomputable def polynomial (claim : Element) (m : Message) : Polynomial Element :=
  ofCoefficients (coefficients claim m)

def evaluate (claim : Element) (m : Message) (r : Element) : Element :=
  (m.c2 * r + linearCoefficient claim m) * r + m.c0

theorem raw_linear_coefficient_exact (claim : Element) (m : Message) :
    raw (linearCoefficient claim m) = Arithmetic.esub (raw claim)
      (Arithmetic.eadd (Arithmetic.eadd (raw m.c0) (raw m.c0)) (raw m.c2)) := rfl

theorem linear_coefficient_subtraction_form (claim : Element) (m : Message) :
    linearCoefficient claim m = claim - 2 * m.c0 - m.c2 := by
  unfold linearCoefficient
  ring

theorem coefficient_count (claim : Element) (m : Message) :
    (coefficients claim m).length = 3 := rfl

theorem coefficients_are_canonical (claim : Element) (m : Message) :
    ∀ c ∈ (coefficients claim m).map raw, Arithmetic.Canonical c := by
  intro c hc
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  exact raw_canonical a

theorem polynomial_constant_exact (claim : Element) (m : Message) :
    (polynomial claim m).coeff 0 = m.c0 := by
  exact coefficient_exact (coefficients claim m) 0

theorem polynomial_linear_exact (claim : Element) (m : Message) :
    (polynomial claim m).coeff 1 = linearCoefficient claim m := by
  exact coefficient_exact (coefficients claim m) 1

theorem polynomial_quadratic_exact (claim : Element) (m : Message) :
    (polynomial claim m).coeff 2 = m.c2 := by
  exact coefficient_exact (coefficients claim m) 2

theorem polynomial_eval_exact (claim : Element) (m : Message) (r : Element) :
    (polynomial claim m).eval r = evaluate claim m r := by
  simp [polynomial, coefficients, ofCoefficients, evaluate]

/-- Definitionally the existing real update, not an evaluator observation. -/
theorem actual_quadratic_exact (claim : Element) (m : Message) (r : Element) :
    WhirFinal.quadratic (raw claim) m.toRaw (raw r) = raw (evaluate claim m r) := rfl

theorem actual_quadratic_is_polynomial_eval (claim : Element) (m : Message) (r : Element) :
    WhirFinal.quadratic (raw claim) m.toRaw (raw r) =
      raw ((polynomial claim m).eval r) := by
  rw [polynomial_eval_exact]
  exact actual_quadratic_exact claim m r

theorem actual_quadratic_is_same_horner (claim : Element) (m : Message) (r : Element) :
    WhirFinal.quadratic (raw claim) m.toRaw (raw r) =
      WhirTerminal.polynomial ((coefficients claim m).map raw) (raw r) := by
  rw [actual_quadratic_is_polynomial_eval, polynomial, terminal_evaluation_exact]

theorem actual_quadratic_is_canonical (claim : Arithmetic.Ext3)
    (m : WhirFinal.RoundMessage) (r : Arithmetic.Ext3) :
    Arithmetic.Canonical (WhirFinal.quadratic claim m r) :=
  Arithmetic.eadd_canonical _ _

theorem evaluation_at_zero (claim : Element) (m : Message) :
    evaluate claim m 0 = m.c0 := by simp [evaluate]

theorem evaluation_at_one (claim : Element) (m : Message) :
    evaluate claim m 1 = claim - m.c0 := by
  simp only [evaluate, mul_one]
  unfold linearCoefficient
  ring

theorem endpoint_sum_is_claim (claim : Element) (m : Message) :
    evaluate claim m 0 + evaluate claim m 1 = claim := by
  rw [evaluation_at_zero, evaluation_at_one]
  ring

theorem polynomial_endpoint_sum_is_claim (claim : Element) (m : Message) :
    (polynomial claim m).eval 0 + (polynomial claim m).eval 1 = claim := by
  simpa only [polynomial_eval_exact] using endpoint_sum_is_claim claim m

/-- Both raw endpoints, including the real final addition, reconstruct claim. -/
theorem actual_endpoint_sum_is_claim (claim : Element) (m : Message) :
    Arithmetic.eadd
      (WhirFinal.quadratic (raw claim) m.toRaw Arithmetic.zero)
      (WhirFinal.quadratic (raw claim) m.toRaw Arithmetic.one) = raw claim := by
  change Arithmetic.eadd
    (WhirFinal.quadratic (raw claim) m.toRaw (raw (0 : Element)))
    (WhirFinal.quadratic (raw claim) m.toRaw (raw (1 : Element))) = _
  rw [actual_quadratic_exact, actual_quadratic_exact]
  exact congrArg raw (endpoint_sum_is_claim claim m)

theorem polynomial_degree_at_most_two (claim : Element) (m : Message) :
    (polynomial claim m).natDegree ≤ 2 := by
  exact degree_bound_including_empty (coefficients claim m)

theorem different_claims_give_different_polynomials
    (claimA claimB : Element) (a b : Message) (hne : claimA ≠ claimB) :
    polynomial claimA a ≠ polynomial claimB b := by
  intro he
  apply hne
  rw [← polynomial_endpoint_sum_is_claim claimA a,
    ← polynomial_endpoint_sum_is_claim claimB b, he]

def actualAgreementPoints (claimA claimB : Element) (a b : Message)
    (domain : Finset Element) : Finset Element := domain.filter (fun r =>
  WhirFinal.quadratic (raw claimA) a.toRaw (raw r) =
    WhirFinal.quadratic (raw claimB) b.toRaw (raw r))

theorem actual_agreement_iff (claimA claimB : Element) (a b : Message) (r : Element) :
    WhirFinal.quadratic (raw claimA) a.toRaw (raw r) =
      WhirFinal.quadratic (raw claimB) b.toRaw (raw r) ↔
    (polynomial claimA a).eval r = (polynomial claimB b).eval r := by
  rw [actual_quadratic_is_polynomial_eval, actual_quadratic_is_polynomial_eval]
  exact ⟨fun h => raw_injective h, congrArg raw⟩

theorem actual_agreement_points_exact (claimA claimB : Element) (a b : Message)
    (domain : Finset Element) :
    actualAgreementPoints claimA claimB a b domain =
      agreementPoints (polynomial claimA a) (polynomial claimB b) domain := by
  apply Finset.ext
  intro r
  simp only [actualAgreementPoints, agreementPoints, Finset.mem_filter, actual_agreement_iff]

/-- Fixed canonical claim/message pairs with different claims. Finset counts
DISTINCT field points, not repetitions of the same query/challenge. -/
theorem fixed_different_claims_agree_at_most_two (claimA claimB : Element)
    (a b : Message) (hne : claimA ≠ claimB) (domain : Finset Element) :
    (actualAgreementPoints claimA claimB a b domain).card ≤ 2 := by
  rw [actual_agreement_points_exact]
  exact fixed_polynomial_agreements_le_degree _ _
    (different_claims_give_different_polynomials claimA claimB a b hne) 2
    (polynomial_degree_at_most_two claimA a) (polynomial_degree_at_most_two claimB b) domain

def liftMessage (m : WhirFinal.RoundMessage)
    (h0 : Arithmetic.Canonical m.c0) (h2 : Arithmetic.Canonical m.c2) : Message :=
  ⟨⟨⟨m.c0,h0⟩⟩, ⟨⟨m.c2,h2⟩⟩⟩

theorem lifted_message_roundtrip (m : WhirFinal.RoundMessage)
    (h0 : Arithmetic.Canonical m.c0) (h2 : Arithmetic.Canonical m.c2) :
    (liftMessage m h0 h2).toRaw = m := by cases m; rfl

/-- Raw API makes all canonical hypotheses explicit, including the prior
claim. Challenges in domain are canonical because their type is Element. -/
theorem fixed_canonical_raw_quadratics_agree_at_most_two
    (claimA claimB : Arithmetic.Ext3) (a b : WhirFinal.RoundMessage)
    (hA : Arithmetic.Canonical claimA) (hB : Arithmetic.Canonical claimB)
    (ha0 : Arithmetic.Canonical a.c0) (ha2 : Arithmetic.Canonical a.c2)
    (hb0 : Arithmetic.Canonical b.c0) (hb2 : Arithmetic.Canonical b.c2)
    (hne : claimA ≠ claimB) (domain : Finset Element) :
    (domain.filter (fun r => WhirFinal.quadratic claimA a (raw r) =
      WhirFinal.quadratic claimB b (raw r))).card ≤ 2 := by
  have ht : (⟨⟨claimA,hA⟩⟩ : Element) ≠ ⟨⟨claimB,hB⟩⟩ :=
    fun he => hne (congrArg raw he)
  have hb := fixed_different_claims_agree_at_most_two ⟨⟨claimA,hA⟩⟩ ⟨⟨claimB,hB⟩⟩
    (liftMessage a ha0 ha2) (liftMessage b hb0 hb2) ht domain
  simpa only [actualAgreementPoints, lifted_message_roundtrip, raw] using hb

/-- Every actual successful abstract-engine round uses the same messages,
same challenge and same state claim in this concrete polynomial bridge.
The engine's read/PoW/challenge results are retained, not silently replaced. -/
theorem successful_round_uses_derived_polynomial
    (e : WhirFinal.Engine) (threshold : Nat) (bytes : WhirFinal.Bytes)
    (s t : WhirFinal.State) (hs : Arithmetic.Canonical s.sum)
    (h : WhirFinal.roundStep e threshold bytes s = some t) :
    ∃ (m : Message) (afterMessage afterPow : WhirFinal.Cursor)
      (r : Element) (next : WhirFinal.Cursor),
      e.readMessage bytes s.cursor = some (m.toRaw, afterMessage) ∧
      e.checkPow threshold bytes afterMessage = some afterPow ∧
      e.challenge afterPow = some (raw r, next) ∧
      t.cursor = next ∧ t.finalRandomness = s.finalRandomness ++ [raw r] ∧
      t.sum = raw ((polynomial ⟨⟨s.sum,hs⟩⟩ m).eval r) := by
  obtain ⟨m, am, ap, r, next, hm, h0, h2, hp, hr, hc, ht⟩ :=
    WhirFinal.round_step_success e threshold bytes s t h
  refine ⟨liftMessage m h0 h2, am, ap, ⟨⟨r,hc⟩⟩, next, ?_, hp, hr, ?_, ?_, ?_⟩
  · simpa only [lifted_message_roundtrip] using hm
  · rw [ht]; rfl
  · rw [ht]; rfl
  · rw [ht]
    exact actual_quadratic_is_polynomial_eval ⟨⟨s.sum,hs⟩⟩ (liftMessage m h0 h2) ⟨⟨r,hc⟩⟩

/-- Concrete paired round data. The second lane is just another explicit
quadratic: its being the true circuit polynomial is NOT asserted here. -/
structure RoundPair where
  claimA : Element
  claimB : Element
  messageA : Message
  messageB : Message
  challenge : Element

def RoundPair.semantic (q : RoundPair) : Sumcheck.Round Element :=
  ⟨evaluate q.claimA q.messageA, evaluate q.claimB q.messageB, q.challenge⟩

theorem semantic_uses_actual_quadratic (q : RoundPair) (r : Element) :
    raw (q.semantic.message r) = WhirFinal.quadratic (raw q.claimA) q.messageA.toRaw (raw r) ∧
    raw (q.semantic.truth r) = WhirFinal.quadratic (raw q.claimB) q.messageB.toRaw (raw r) :=
  ⟨rfl, rfl⟩

theorem semantic_endpoint_claims (q : RoundPair) :
    q.semantic.message 0 + q.semantic.message 1 = q.claimA ∧
    q.semantic.truth 0 + q.semantic.truth 1 = q.claimB :=
  ⟨endpoint_sum_is_claim _ _, endpoint_sum_is_claim _ _⟩

theorem collision_gives_different_polynomials (q : RoundPair)
    (hc : Sumcheck.EvaluationCollision (0 : Element) 1 q.semantic) :
    polynomial q.claimA q.messageA ≠ polynomial q.claimB q.messageB := by
  intro he
  have hall (x : Element) : q.semantic.message x = q.semantic.truth x := by
    change evaluate _ _ x = evaluate _ _ x
    rw [← polynomial_eval_exact, ← polynomial_eval_exact, he]
  exact hc.1.elim (fun h => h (hall 0)) (fun h => h (hall 1))

theorem collision_is_actual_agreement (q : RoundPair)
    (hc : Sumcheck.EvaluationCollision (0 : Element) 1 q.semantic)
    (domain : Finset Element) (hr : q.challenge ∈ domain) :
    q.challenge ∈ actualAgreementPoints q.claimA q.claimB q.messageA q.messageB domain := by
  apply Finset.mem_filter.mpr
  refine ⟨hr, ?_⟩
  exact congrArg raw hc.2

/-- Deterministic bridge to the existing chain reduction. The two successful
semantic chains and their shared terminal are explicit hypotheses. No claim
that the second chain is genuine circuit truth, and no probability statement.
For the selected fixed pair the bound holds on EVERY distinct-point domain;
membership needs the actual challenge to be in that domain. -/
theorem conditional_chain_mismatch_reduces_to_at_most_two
    (rounds : List RoundPair) (claimed actual terminal : Element)
    (hclaimed : Sumcheck.chain (· + ·) 0 1 false claimed (rounds.map RoundPair.semantic) = some terminal)
    (hcomparison : Sumcheck.chain (· + ·) 0 1 true actual (rounds.map RoundPair.semantic) = some terminal)
    (hne : claimed ≠ actual) :
    ∃ q ∈ rounds,
      Sumcheck.EvaluationCollision (0 : Element) 1 q.semantic ∧
      (∀ domain : Finset Element,
        (actualAgreementPoints q.claimA q.claimB q.messageA q.messageB domain).card ≤ 2 ∧
        (q.challenge ∈ domain → q.challenge ∈
          actualAgreementPoints q.claimA q.claimB q.messageA q.messageB domain)) := by
  obtain ⟨r, hm, hc⟩ := Sumcheck.mismatch_requires_evaluation_collision (· + ·) 0 1
    (rounds.map RoundPair.semantic) claimed actual terminal hclaimed hcomparison hne
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  refine ⟨q, hq, hc, ?_⟩
  intro domain
  refine ⟨?_, collision_is_actual_agreement q hc domain⟩
  rw [actual_agreement_points_exact]
  exact fixed_polynomial_agreements_le_degree _ _ (collision_gives_different_polynomials q hc) 2
    (polynomial_degree_at_most_two _ _) (polynomial_degree_at_most_two _ _) domain

/-- Ordinary nonconstant evaluation: claim=11,c0=2,c2=3 gives c1=4,
so evaluation at r=5 is 3*25+4*5+2=97. -/
theorem actual_nonconstant_quadratic_example :
    WhirFinal.quadratic (Arithmetic.fromBase 11)
      ⟨Arithmetic.fromBase 2, Arithmetic.fromBase 3⟩ (Arithmetic.fromBase 5) =
      Arithmetic.fromBase 97 := by decide

theorem actual_zero_quadratic_example :
    WhirFinal.quadratic Arithmetic.zero ⟨Arithmetic.zero, Arithmetic.zero⟩ Arithmetic.zero =
      Arithmetic.zero := by decide

end Audit.Wire3.WhirQuadratic
