import Std

/-!
# Deterministic sumcheck collision reduction (current audit foundation)

Current Rust `sumcheck/coefficients.rs::evaluate_ext3_coefficient_round` and
Solidity `OuterLogupExt3Verifier` reconstruct the constant coefficient from
the running claim; `verifier_v2.rs` chains the resulting two lanes.

This lemma concerns the resulting *semantic round functions*, not the byte
decoder, Horner assembly, or coefficient reconstruction. Those bridges must
be proved separately. `truth` functions are the honest partial-sum polynomials;
`truthChain` is a hypothesis about them, NOT a check the production verifier
performs. This is a deterministic bad-event reduction, not a probability,
Fiat--Shamir security, or satisfying-witness theorem. No polynomial root bound
is imported or asserted as an axiom.
-/

namespace Audit.Wire3.Sumcheck

structure Round (F : Type) where
  message : F → F
  truth : F → F
  challenge : F

variable {F : Type} [DecidableEq F]

def chain (add : F → F → F) (zero one : F) (honest : Bool)
    (claim : F) : List (Round F) → Option F
  | [] => some claim
  | round :: rest =>
    let polynomial := if honest then round.truth else round.message
    if add (polynomial zero) (polynomial one) = claim then
      chain add zero one honest (polynomial round.challenge) rest
    else none

def EvaluationCollision (zero one : F) (round : Round F) : Prop :=
  (round.message zero ≠ round.truth zero ∨ round.message one ≠ round.truth one) ∧
  round.message round.challenge = round.truth round.challenge

theorem empty_chain (add : F → F → F) (zero one : F) (honest : Bool) (claim : F) :
    chain add zero one honest claim [] = some claim := rfl

theorem successful_cons {add : F → F → F} {zero one claim final : F}
    {honest : Bool} {round : Round F} {rest : List (Round F)}
    (h : chain add zero one honest claim (round :: rest) = some final) :
    let polynomial := if honest then round.truth else round.message
    add (polynomial zero) (polynomial one) = claim ∧
      chain add zero one honest (polynomial round.challenge) rest = some final := by
  cases honest <;> simp only [chain, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
    split at h
  all_goals first | exact ⟨by assumption, h⟩ | contradiction

/-- If a false initial sum reaches the same terminal value as a consistent
honest polynomial chain, one of the *actual supplied challenges* equates
different round functions. The conclusion is derived, not a field of a
verifier-acceptance record. Each lane can instantiate this lemma separately. -/
theorem mismatch_requires_evaluation_collision
    (add : F → F → F) (zero one : F) (rounds : List (Round F)) :
    ∀ claimed actual terminal,
      chain add zero one false claimed rounds = some terminal →
      chain add zero one true actual rounds = some terminal →
      claimed ≠ actual →
      ∃ round ∈ rounds, EvaluationCollision zero one round := by
  induction rounds with
  | nil =>
    intro claimed actual terminal hc ht hne
    simp only [chain, Option.some.injEq] at hc ht
    exact False.elim (hne (hc.trans ht.symm))
  | cons round rest ih =>
    intro claimed actual terminal hc ht hne
    have hc' := successful_cons hc
    have ht' := successful_cons ht
    simp only [Bool.false_eq_true, ↓reduceIte] at hc'
    simp only [↓reduceIte] at ht'
    by_cases he : round.message round.challenge = round.truth round.challenge
    · refine ⟨round, List.mem_cons_self round rest, ?_, he⟩
      by_cases h0 : round.message zero = round.truth zero
      · right
        intro h1
        apply hne
        calc
          claimed = add (round.message zero) (round.message one) := hc'.1.symm
          _ = add (round.truth zero) (round.truth one) := by rw [h0, h1]
          _ = actual := ht'.1
      · exact Or.inl h0
    · obtain ⟨found, hm, hp⟩ := ih _ _ terminal hc'.2 ht'.2 he
      exact ⟨found, List.mem_cons_of_mem round hm, hp⟩

/-- Equivalently, no evaluation collision plus matching terminal values rules
out a false initial sum. No claim is made that collisions have probability 0. -/
theorem no_collision_forces_initial_agreement
    {add : F → F → F} {zero one claimed actual terminal : F}
    {rounds : List (Round F)}
    (hc : chain add zero one false claimed rounds = some terminal)
    (ht : chain add zero one true actual rounds = some terminal)
    (hn : ∀ round ∈ rounds, ¬ EvaluationCollision zero one round) : claimed = actual := by
  by_cases he : claimed = actual
  · exact he
  · obtain ⟨round, hm, hp⟩ := mismatch_requires_evaluation_collision add zero one rounds
      claimed actual terminal hc ht he
    exact False.elim (hn round hm hp)

theorem positive_honest_round :
    chain Nat.add 0 1 false 1
      [⟨fun x => x, fun x => x, 3⟩] = some 3 := rfl

end Audit.Wire3.Sumcheck
