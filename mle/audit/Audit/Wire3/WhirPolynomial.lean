import Audit.Wire3.GoldilocksExt3Field
import Mathlib.Algebra.Polynomial.Roots

/-!
# Concrete WHIR Horner evaluation and fixed-polynomial agreement bounds

WhirTerminal.polynomial is the actual audit function (not evalPolynomial).
It matches GoldilocksExt3.reduceWithPowers, called by
SpongefishWhirVerify._requireFinalOpening: start with zero, read coefficients
from the last index to zero, and update acc := acc * x + coefficient. Thus
the final-vector order is constant coefficient FIRST, not highest-degree first.

Element is the concrete, constructed Goldilocks Ext3 Field. No free Field
parameter or assumed Ext3 field laws occur. Raw coefficient vectors are lifted
only with an explicit canonicality proof for EVERY coefficient; evaluation
points are canonical too. The zero polynomial has natDegree zero in Mathlib;
the empty-list case is handled separately, and length minus one is a Nat bound.

The agreement bound is deterministic, for TWO FIXED distinct polynomials and
DISTINCT field points in a Finset. Same-length distinct vectors imply distinct
polynomials; differing vector lengths alone do not, because trailing zeros do
not change the polynomial. No transcript timing/fixedness, query-map injectivity,
sampling distribution, Fiat-Shamir independence, adaptive-choice probability,
Merkle binding, or full WHIR/PCS soundness is established here.
-/
namespace Audit.Wire3.WhirPolynomial
open Audit.Wire3
open GoldilocksExt3Field
open Polynomial

def raw (a : Element) : Arithmetic.Ext3 := a.toVerifier.val

theorem raw_canonical (a : Element) : Arithmetic.Canonical (raw a) := a.toVerifier.property

theorem raw_injective : Function.Injective raw := by
  intro a b h
  exact element_eq a b (Subtype.eq h)

/-- Constant-first coefficient list, matching the reverse Horner loop.
Mathlib's symbolic Polynomial representation is noncomputable; the source
Horner function being related to it remains the executable audit function. -/
noncomputable def ofCoefficients : List Element → Polynomial Element
  | [] => 0
  | c :: cs => ofCoefficients cs * X + C c

theorem empty_coefficients_polynomial : ofCoefficients [] = 0 := rfl

theorem terminal_horner_cons (c : Arithmetic.Ext3) (cs : List Arithmetic.Ext3)
    (x : Arithmetic.Ext3) :
    WhirTerminal.polynomial (c :: cs) x =
      Arithmetic.eadd (Arithmetic.emul (WhirTerminal.polynomial cs x) x) c := by
  simp only [WhirTerminal.polynomial, List.reverse_cons, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem terminal_empty (x : Arithmetic.Ext3) :
    WhirTerminal.polynomial [] x = Arithmetic.zero := rfl

/-- Evaluating the Mathlib polynomial returns EXACTLY the raw executable
Horner result. Canonicality is carried by every Element in cs and by x. -/
theorem terminal_evaluation_exact (cs : List Element) (x : Element) :
    raw ((ofCoefficients cs).eval x) = WhirTerminal.polynomial (cs.map raw) (raw x) := by
  induction cs with
  | nil => simp only [ofCoefficients, eval_zero, List.map_nil, terminal_empty]; rfl
  | cons c cs ih =>
      rw [ofCoefficients, eval_add, eval_mul, eval_X, eval_C, List.map_cons, terminal_horner_cons]
      change Arithmetic.eadd (Arithmetic.emul (raw ((ofCoefficients cs).eval x)) (raw x)) (raw c) = _
      rw [ih]

def liftCoefficients : (cs : List Arithmetic.Ext3) →
    (∀ c ∈ cs, Arithmetic.Canonical c) → List Element
  | [], _ => []
  | c :: cs, h =>
      ⟨⟨c,h c (by simp)⟩⟩ :: liftCoefficients cs (fun d hd => h d (by simp [hd]))

theorem lifted_coefficients_roundtrip (cs : List Arithmetic.Ext3)
    (hc : ∀ c ∈ cs, Arithmetic.Canonical c) : (liftCoefficients cs hc).map raw = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [liftCoefficients, List.map_cons, raw, ih]

theorem lifted_coefficients_length (cs : List Arithmetic.Ext3)
    (hc : ∀ c ∈ cs, Arithmetic.Canonical c) : (liftCoefficients cs hc).length = cs.length := by
  have h := congrArg List.length (lifted_coefficients_roundtrip cs hc)
  simpa only [List.length_map] using h

theorem canonical_raw_horner_is_polynomial_eval (cs : List Arithmetic.Ext3)
    (hc : ∀ c ∈ cs, Arithmetic.Canonical c) (x : Verifier.Ext3) :
    WhirTerminal.polynomial cs x.val =
      raw ((ofCoefficients (liftCoefficients cs hc)).eval ⟨x⟩) := by
  rw [terminal_evaluation_exact, lifted_coefficients_roundtrip]
  rfl

/-- Each indexed coefficient is preserved, including implicit zeros beyond
the supplied list. This rules out accidentally reversing the polynomial. -/
theorem coefficient_exact (cs : List Element) (n : Nat) :
    (ofCoefficients cs).coeff n = cs.getD n 0 := by
  induction cs generalizing n with
  | nil => simp [ofCoefficients]
  | cons c cs ih =>
      cases n with
      | zero => simp only [ofCoefficients, coeff_add, coeff_mul_X_zero, coeff_C_zero,
          zero_add, List.getD_cons_zero]
      | succ n => simp only [ofCoefficients, coeff_add, coeff_mul_X, coeff_C_succ,
          add_zero, List.getD_cons_succ, ih]

theorem equal_length_coefficient_lists_injective (cs ds : List Element)
    (hlen : cs.length = ds.length) (h : ofCoefficients cs = ofCoefficients ds) : cs = ds := by
  apply List.ext_get hlen
  intro n hn hm
  have hc := congrArg (fun f : Polynomial Element => f.coeff n) h
  dsimp only at hc
  rw [coefficient_exact, coefficient_exact, List.getD_eq_get cs 0 hn,
    List.getD_eq_get ds 0 hm] at hc
  exact hc

theorem degree_bound_including_empty (cs : List Element) :
    (ofCoefficients cs).natDegree ≤ cs.length - 1 := by
  induction cs with
  | nil => simp [ofCoefficients]
  | cons c cs ih =>
      cases cs with
      | nil => simp [ofCoefficients]
      | cons d ds =>
          have ha := natDegree_add_le (ofCoefficients (d :: ds) * X) (C c)
          have hm : (ofCoefficients (d :: ds) * X).natDegree ≤
              (ofCoefficients (d :: ds)).natDegree + 1 := by
            simpa only [natDegree_X] using
              (natDegree_mul_le (p := ofCoefficients (d :: ds)) (q := (X : Polynomial Element)))
          change (ofCoefficients (d :: ds) * X + C c).natDegree ≤ _
          simp only [natDegree_C, List.length_cons] at ha ih ⊢
          omega

def agreementPoints (f g : Polynomial Element) (domain : Finset Element) : Finset Element :=
  domain.filter (fun x => f.eval x = g.eval x)

/-- Fixed, DISTINCT polynomials: every matching point is a root of their
nonzero difference. Domain is a set of distinct points, not a query list. -/
theorem fixed_polynomial_agreements_le_difference_degree (f g : Polynomial Element)
    (hne : f ≠ g) (domain : Finset Element) :
    (agreementPoints f g domain).card ≤ (f - g).natDegree := by
  apply card_le_degree_of_subset_roots
  intro x hx
  have he := (Finset.mem_filter.mp hx).2
  apply (mem_roots (sub_ne_zero.mpr hne)).mpr
  change (f - g).eval x = 0
  rw [eval_sub, he, sub_self]

theorem fixed_polynomial_agreements_le_degree (f g : Polynomial Element)
    (hne : f ≠ g) (d : Nat) (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (domain : Finset Element) : (agreementPoints f g domain).card ≤ d := by
  exact (fixed_polynomial_agreements_le_difference_degree f g hne domain).trans
    ((natDegree_sub_le f g).trans (max_le hf hg))

def terminalAgreementPoints (cs ds : List Element) (domain : Finset Element) : Finset Element :=
  domain.filter (fun x => WhirTerminal.polynomial (cs.map raw) (raw x) =
    WhirTerminal.polynomial (ds.map raw) (raw x))

theorem terminal_agreement_iff (cs ds : List Element) (x : Element) :
    WhirTerminal.polynomial (cs.map raw) (raw x) =
      WhirTerminal.polynomial (ds.map raw) (raw x) ↔
    (ofCoefficients cs).eval x = (ofCoefficients ds).eval x := by
  rw [← terminal_evaluation_exact, ← terminal_evaluation_exact]
  exact ⟨fun h => raw_injective h, congrArg raw⟩

theorem terminal_agreement_points_exact (cs ds : List Element) (domain : Finset Element) :
    terminalAgreementPoints cs ds domain = agreementPoints (ofCoefficients cs) (ofCoefficients ds) domain := by
  apply Finset.ext
  intro x
  simp only [terminalAgreementPoints, agreementPoints, Finset.mem_filter, terminal_agreement_iff]

/-- Practical same-finalSize form: different fixed canonical vectors of the
same length can agree at no more than length-1 distinct field points. -/
theorem fixed_distinct_terminal_vectors_agree_at_most_length_sub_one (cs ds : List Element)
    (hlen : cs.length = ds.length) (hne : cs ≠ ds) (domain : Finset Element) :
    (terminalAgreementPoints cs ds domain).card ≤ cs.length - 1 := by
  rw [terminal_agreement_points_exact]
  apply fixed_polynomial_agreements_le_degree
  · exact fun he => hne (equal_length_coefficient_lists_injective cs ds hlen he)
  · exact degree_bound_including_empty cs
  · simpa only [← hlen] using degree_bound_including_empty ds

def rawTerminalAgreementPoints (cs ds : List Arithmetic.Ext3) (domain : Finset Element) :
    Finset Element := domain.filter (fun x =>
  WhirTerminal.polynomial cs (raw x) = WhirTerminal.polynomial ds (raw x))

theorem lifted_agreement_points_exact (cs ds : List Arithmetic.Ext3)
    (hc : ∀ c ∈ cs, Arithmetic.Canonical c) (hd : ∀ c ∈ ds, Arithmetic.Canonical c)
    (domain : Finset Element) :
    terminalAgreementPoints (liftCoefficients cs hc) (liftCoefficients ds hd) domain =
      rawTerminalAgreementPoints cs ds domain := by
  simp only [terminalAgreementPoints, rawTerminalAgreementPoints, lifted_coefficients_roundtrip]

/-- Direct raw-model form: no unconstrained abstract coefficients are inserted
between the given canonical final vectors and their actual Horner evaluations. -/
theorem fixed_canonical_raw_vectors_agreement_bound (cs ds : List Arithmetic.Ext3)
    (hc : ∀ c ∈ cs, Arithmetic.Canonical c) (hd : ∀ c ∈ ds, Arithmetic.Canonical c)
    (hlen : cs.length = ds.length) (hne : cs ≠ ds) (domain : Finset Element) :
    (rawTerminalAgreementPoints cs ds domain).card ≤ cs.length - 1 := by
  have hl : (liftCoefficients cs hc).length = (liftCoefficients ds hd).length := by
    rw [lifted_coefficients_length, lifted_coefficients_length, hlen]
  have hn : liftCoefficients cs hc ≠ liftCoefficients ds hd := by
    intro h
    have hm := congrArg (List.map raw) h
    rw [lifted_coefficients_roundtrip, lifted_coefficients_roundtrip] at hm
    exact hne hm
  have hb := fixed_distinct_terminal_vectors_agree_at_most_length_sub_one
    (liftCoefficients cs hc) (liftCoefficients ds hd) hl hn domain
  rw [lifted_agreement_points_exact, lifted_coefficients_length] at hb
  exact hb

theorem equal_empty_vectors_match_every_point (domain : Finset Element) :
    terminalAgreementPoints [] [] domain = domain := by
  simp [terminalAgreementPoints]

/-- Empty vs singleton-zero shows why different list lengths alone are not
enough to use the distinct-polynomial bound. -/
theorem trailing_zero_does_not_imply_distinct_polynomials :
    ofCoefficients [] = ofCoefficients [0] := by simp [ofCoefficients]

/-- Nonconstant orientation check: [1,2] at x=3 evaluates to 1+2*3=7,
not the reversed-coefficient expression 2+1*3. -/
theorem actual_horner_coefficient_order_example :
    WhirTerminal.polynomial [Arithmetic.fromBase 1, Arithmetic.fromBase 2]
      (Arithmetic.fromBase 3) = Arithmetic.fromBase 7 := by decide

end Audit.Wire3.WhirPolynomial
