import Audit.Wire3.IntegratedTerminalChain
import Audit.Wire3.OuterChallenge
import Audit.Wire3.WhirRlc
import Audit.Wire3.WhirDomainBridge
import Audit.Wire3.WhirRowBinding

/-!
# Conditional soundness of the wire-v3 verifier under explicit assumptions

This is the audit's stated next step: a QUANTITATIVE soundness statement under
EXPLICITLY NAMED cryptographic assumptions.  It adds no new model: it chains
the adopted DETERMINISTIC identities (`Verifier.verify_success_checks`,
`IntegratedTerminalChain.verify_iff_solidity_order`, `OuterRound`'s round
reconstruction, `OuterClaimChain`'s honest chain, `NormTerminalBinding`'s
terminal identities) with the adopted AGREEMENT-COUNT bounds
(`OuterRound.fixed_different_claims_agree_at_most_degree`,
`OuterChallenge.uniform_tuple_probability_bound`,
`WhirQuadratic`/`WhirRlc`/`WhirDomainBridge`, `Merkle`/`WhirRowBinding`).

What is PROVED here, with no new axiom:

* `chain_separates` / `chain_initial_agreement`: over the challenges an
  execution actually drew, two different initial claims stay different unless
  some round has its agreement bad event.  Purely deterministic.
* `lane_claimed_run` / `log_lane_claimed_run` / `gate_lane_claimed_run`: the
  adopted `Verifier.runRounds` lane claim IS that chain, applied to the lifted
  proof messages at the lifted drawn challenges.
* `honest_truth_run`: the honest chain of the EXTRACTED norm tables, started at
  their Boolean-cube sum `OuterClaimChain.endpointSum`, reaches the adopted
  last-round value `NormDenseRound.roundValue`.
* `norm_terminal_is_honest_last_value`: the verifier's own norm terminal on the
  proof's used claims IS that last-round value, via
  `NormTerminalBinding.last_round_target_is_bound_terminal` and
  `fully_bound_target_is_engine_terminal`.
* `accepted_norm_cube_sum_vanishes` (CORE): acceptance + no outer log bad event
  + the assumptions imply `OuterClaimChain.endpointSum t pr = Verifier.zero`,
  i.e. the extracted tables really satisfy the norm/logUp relation over the
  cube.  That is EXACTLY the `zeroSum` field that
  `IntegratedTerminalChain.HonestNormProver` has to assume, so this theorem
  supplies the audit's missing direction for the norm lane.
* `truth_tail_of_last_round_data`: the honest chain's endpoint IS the adopted
  `roundValue` of the structurally-named last tables at the last drawn
  challenge.  This DERIVES what an earlier draft postulated as a scalar bridge.
* `bad_sets_union_card`, `bad_sets_triple_card_sum`, `bad_sets_uniform_sum`,
  `outer_failure_bound`, `outer_failure_triple_count`: the union bound, as
  counting over `OuterChallenge`'s explicit finite space of 32-byte digest
  triples and as a rational bound under that space's EXPLICIT uniform law.
* `conditional_soundness` (CAPSTONE) and `profile_bound`: the single readable
  statement with the concrete `B` and `N`.

## THE GATE LANE IS NOT PROVED

There is NO gate analogue of `accepted_norm_cube_sum_vanishes`.  Nothing in this
file proves that the gate lane's aggregate sums to zero over the Boolean cube,
and nothing proves that an accepted proof satisfies the circuit's GATE
constraints.  Only the norm/logUp lane is established.

An earlier draft did carry such a theorem.  It was DEGENERATE: its gate round
list and gate cube sum were free parameters with no tie to any gate table, so
setting the round list to `[]` made the honest run invertible in its start value
and the gate assumption satisfiable for ANY accepting proof.  It has been
deleted rather than weakened.  The reason it cannot simply be repaired is that
the adopted gate modules supply no coefficient interpolation, no Boolean-cube
sum, and no round-to-round telescoping lemma (every `bindTables` fact is pinned
to the LAST round), and the gate eq-table's derivation from `gateTau` is
explicitly outside the model.  Section 9's `gate lane is not proved` note gives
the full accounting with module references.

## THE NUMBER `195 * (⌈2^256/p⌉ / 2^256)^3` IS NOT THE SYSTEM'S SOUNDNESS ERROR

It is approximately `2^-184`.  It covers ONLY the outer sumcheck round-agreement
events, counted under the IDEAL uniform law of `OuterChallenge`.  It EXCLUDES the
entire WHIR/Merkle contribution -- proximity/list-decoding, the query-repetition
profile, and Merkle collision resistance -- which is the DOMINANT term.  The
deployed design point is around 100 BITS, not 184.  Quoting this number as the
wire-v3 soundness error would be wrong by roughly eighty bits.

Relatedly, `failure` is a FREE RATIONAL PARAMETER, not a computed probability.
It is only ever bounded ABOVE: assumption 2 bounds `law` above by the ideal
mass and assumption 3 bounds `failure` above by the sum of `law`, so
`failure := 0, law := 0` satisfies both.  NOTHING here lower-bounds `failure`
by any real quantity, so reading it as the real failure probability needs an
external bridge (`real <= sum of law`) that NO field of this structure supplies.

The first and last conjuncts of the capstone are also NEVER COMPOSED.  There is
no probability space over executions in this file and no theorem of the form
`Pr[not BadEventFree] <= failure`.  The counted sets ARE definitionally the sets
`BadEventFree` denies membership in, but the step from "the set is small" to
"the drawn challenge probably missed it" lives entirely in the prose of
assumptions 2 and 3.  So this is a deterministic implication standing beside a
counting bound, not one quantitative soundness statement.

Direction proved and direction NOT proved.  Only ACCEPTANCE -> RELATION is
proved.  The converse (every proof of a true statement is accepted) is the
honest-prover direction; the audit already has it, but only for an honest
prover, as `IntegratedTerminalChain.honest_prover_passes_deterministic_checks`,
and only modulo that theorem's `ObservationOnly` list.  A converse for the
concrete engine would need the WHIR `parseWhir`/`whirTail` observations to be
replaced by a completeness proof of the deployed WHIR verifier; that is not
attempted anywhere in the audit.

The extraction join is OPEN.  No assumption links the committed WHIR columns to
the extracted tables.  ASSUMPTION 17 (`normClaims`) simply POSTULATES, at the
terminal, that the proof's used claims are cells of the extracted tables; an
adversary who can open the commitment to something else is excluded by fiat
there, not by any argument here.

`Assumptions` is NOT shown to be inhabited.  Three individual fields are shown
satisfiable in section 12; the eighteen-field conjunction is not, so the capstone
could be vacuous for some instantiations.

What this is NOT.  It is not a soundness proof of the deployed system.  Every
cryptographic step is an enumerated field of `Assumptions` with a docstring
saying what is assumed and what would prove it.  The probability statement is a
counting statement about the EXPLICIT uniform law of `OuterChallenge`, not about
Keccak; ASSUMPTIONS 1-3 are exactly the bridge from that law to the real
transcript, and they are assumed, not proved.  The Rust/EVM refinement, gas,
exception ordering, and the deployed WHIR profile constants remain outside.
-/

namespace Audit.Wire3.ConditionalSoundness
open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. One executed outer round of one lane -/

structure LaneRound where
  message : List Element
  truth : List Element
  challenge : Element

def claimedRun (a : Element) : List LaneRound → Element
  | [] => a
  | r :: rs => claimedRun (OuterRound.evaluate a r.message r.challenge) rs

def truthRun (b : Element) : List LaneRound → Element
  | [] => b
  | r :: rs => truthRun (OuterRound.evaluate b r.truth r.challenge) rs

/-- BAD EVENT (outer sumcheck round agreement, one lane, one round).  The set
of field points at which the prover's reconstructed round polynomial for the
running claim `a` and the honest round polynomial for the true running claim
`b` take the same value, when the two claims differ.  It is exactly
`OuterChallenge.outerAgreementPoints`, i.e.
`OuterRound.actualAgreementPoints ... Finset.univ`, whose cardinality is
bounded by the ADOPTED counting theorem
`OuterRound.fixed_different_claims_agree_at_most_degree` (at most the message
degree bound `d`), and whose 32-byte-triple mass under the explicit uniform
law is bounded by the ADOPTED `OuterChallenge.uniform_tuple_probability_bound`
/ `OuterChallenge.fixed_different_outer_claims_uniform_bound_explicit`
(`d * (⌈2^256/p⌉ / 2^256)^3`).  Empty when the two claims already agree: there
is then nothing to separate. -/
def roundBadSet (a b : Element) (r : LaneRound) : Finset Element :=
  if a = b then ∅ else OuterChallenge.outerAgreementPoints a b r.message r.truth

/-- The bad event of one round: the challenge actually drawn lies in
`roundBadSet`. -/
def RoundAgreement (a b : Element) (r : LaneRound) : Prop :=
  r.challenge ∈ roundBadSet a b r

theorem round_agreement_of_ne (a b : Element) (r : LaneRound) (hne : a ≠ b)
    (he : (OuterRound.polynomial a r.message).eval r.challenge =
      (OuterRound.polynomial b r.truth).eval r.challenge) : RoundAgreement a b r := by
  simp only [RoundAgreement, roundBadSet, if_neg hne, OuterChallenge.outerAgreementPoints,
    OuterRound.actualAgreementPoints, Finset.mem_filter, Finset.mem_univ, true_and,
    OuterRound.actual_agreement_iff_polynomial]
  exact he

/-- No round of the chain has its bad event. -/
def BadEventFree (a b : Element) : List LaneRound → Prop
  | [] => True
  | r :: rs => ¬ RoundAgreement a b r ∧
      BadEventFree (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs

/-- CORE DETERMINISTIC CHAIN.  Different initial claims stay different for the
whole run as long as no round has its agreement bad event.  Nothing
probabilistic; the challenges are the ones the run actually drew. -/
theorem chain_separates : ∀ (rs : List LaneRound) (a b : Element),
    a ≠ b → BadEventFree a b rs → claimedRun a rs ≠ truthRun b rs
  | [], _, _, hne, _ => hne
  | r :: rs, a, b, hne, hfree => by
      refine chain_separates rs _ _ ?_ hfree.2
      intro he
      refine hfree.1 (round_agreement_of_ne a b r hne ?_)
      rw [OuterRound.polynomial_eval_exact, OuterRound.polynomial_eval_exact]
      exact he

theorem chain_initial_agreement (rs : List LaneRound) (a b : Element)
    (hfree : BadEventFree a b rs) (hend : claimedRun a rs = truthRun b rs) : a = b := by
  by_contra hne
  exact chain_separates rs a b hne hfree hend

/-! ## 2. The lane extracted from the adopted `Verifier.runRounds` execution -/

def lane (commit : Verifier.CommitRound) (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3) :
    List (List Element) → Verifier.RoundState → List Verifier.CoupledMessage → List LaneRound
  | _, _, [] => []
  | truths, s, m :: ms =>
      ⟨(sel m).map OuterRound.lift, truths.headD [],
        OuterRound.lift (pick (commit s.transcript s.roundIndex m.1 m.2))⟩ ::
      lane commit sel pick truths.tail (Verifier.roundStep commit s m) ms

theorem lane_length (commit : Verifier.CommitRound) (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3) :
    ∀ (truths : List (List Element)) (s : Verifier.RoundState) (ms : List Verifier.CoupledMessage),
      (lane commit sel pick truths s ms).length = ms.length
  | _, _, [] => rfl
  | truths, _, _ :: ms => congrArg Nat.succ (lane_length commit sel pick truths.tail _ ms)

theorem lane_messages (commit : Verifier.CommitRound) (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3) :
    ∀ (truths : List (List Element)) (s : Verifier.RoundState) (ms : List Verifier.CoupledMessage)
      (r : LaneRound), r ∈ lane commit sel pick truths s ms →
      ∃ m ∈ ms, r.message = (sel m).map OuterRound.lift
  | _, _, [], r, hr => by simp [lane] at hr
  | truths, s, m :: ms, r, hr => by
      rcases List.mem_cons.mp hr with h | h
      · exact ⟨m, List.mem_cons_self _ _, by rw [h]⟩
      · obtain ⟨m', hm', he⟩ := lane_messages commit sel pick truths.tail _ ms r h
        exact ⟨m', List.mem_cons_of_mem _ hm', he⟩

theorem lane_truths (commit : Verifier.CommitRound) (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3) :
    ∀ (truths : List (List Element)) (s : Verifier.RoundState) (ms : List Verifier.CoupledMessage)
      (r : LaneRound), r ∈ lane commit sel pick truths s ms → r.truth ∈ truths ∨ r.truth = []
  | _, _, [], r, hr => by simp [lane] at hr
  | truths, s, m :: ms, r, hr => by
      rcases List.mem_cons.mp hr with h | h
      · subst h
        cases truths with
        | nil => exact Or.inr rfl
        | cons a as => exact Or.inl (by exact List.mem_cons_self _ _)
      · rcases lane_truths commit sel pick truths.tail _ ms r h with hm | hm
        · left
          cases truths with
          | nil => simp at hm
          | cons a as => exact List.mem_cons_of_mem _ hm
        · exact Or.inr hm

/-- The adopted `Verifier.runRounds` claim of a lane is exactly `claimedRun`
of the lifted messages at the lifted challenges the run actually drew. -/
theorem lane_claimed_run (commit : Verifier.CommitRound)
    (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3)
    (claimOf : Verifier.RoundState → Verifier.Ext3)
    (hstep : ∀ (s : Verifier.RoundState) (m : Verifier.CoupledMessage),
      claimOf (Verifier.roundStep commit s m) =
        Verifier.evaluateRound (claimOf s) (sel m)
          (pick (commit s.transcript s.roundIndex m.1 m.2))) :
    ∀ (ms : List Verifier.CoupledMessage) (truths : List (List Element)) (s : Verifier.RoundState),
      claimOf (Verifier.runRounds commit s ms) =
        (claimedRun (OuterRound.lift (claimOf s)) (lane commit sel pick truths s ms)).toVerifier
  | [], _, _ => rfl
  | m :: ms, truths, s => by
      have ih := lane_claimed_run commit sel pick claimOf hstep ms truths.tail
        (Verifier.roundStep commit s m)
      have hkey : OuterRound.lift (claimOf (Verifier.roundStep commit s m)) =
          OuterRound.evaluate (OuterRound.lift (claimOf s)) ((sel m).map OuterRound.lift)
            (OuterRound.lift (pick (commit s.transcript s.roundIndex m.1 m.2))) := by
        apply GoldilocksExt3Field.element_eq
        rw [hstep s m]
        rw [OuterRound.actual_typed_round_is_polynomial_eval, OuterRound.polynomial_eval_exact]
        rfl
      show claimOf (Verifier.runRounds commit (Verifier.roundStep commit s m) ms) = _
      rw [ih]
      simp only [lane, claimedRun, hkey]

theorem log_lane_claimed_run (commit : Verifier.CommitRound) (truths : List (List Element))
    (s : Verifier.RoundState) (ms : List Verifier.CoupledMessage) :
    (Verifier.runRounds commit s ms).logClaim =
      (claimedRun (OuterRound.lift s.logClaim)
        (lane commit Prod.fst Verifier.RoundChallenges.log truths s ms)).toVerifier :=
  lane_claimed_run commit Prod.fst Verifier.RoundChallenges.log Verifier.RoundState.logClaim
    (fun _ _ => rfl) ms truths s

theorem gate_lane_claimed_run (commit : Verifier.CommitRound) (truths : List (List Element))
    (s : Verifier.RoundState) (ms : List Verifier.CoupledMessage) :
    (Verifier.runRounds commit s ms).gateClaim =
      (claimedRun (OuterRound.lift s.gateClaim)
        (lane commit Prod.snd Verifier.RoundChallenges.gate truths s ms)).toVerifier :=
  lane_claimed_run commit Prod.snd Verifier.RoundChallenges.gate Verifier.RoundState.gateClaim
    (fun _ _ => rfl) ms truths s

/-! ## 3. The honest (truth) chain of the extracted norm tables -/

open NormDenseRound NormTerminalBinding in
/-- The honest round data of the extracted tables along the drawn challenges:
at each round the true message is the adopted `computeRound` of the current
tables, and the tables advance by the adopted `bindTables`. -/
def HonestTruth (pr : Prepared) : Tables → List LaneRound → Prop
  | _, [] => True
  | t, [r] => computeRound t pr = some r.truth ∧ t.remaining = 1
  | t, r :: r2 :: rs => computeRound t pr = some r.truth ∧ 2 ≤ t.remaining ∧
      HonestTruth pr (boundTables t r.challenge) (r2 :: rs)

open NormDenseRound NormTerminalBinding in
/-- The value the honest chain reaches: the adopted `roundValue` of the last
tables at the last drawn challenge (`OuterClaimChain.honest_log_chain`). -/
def truthTail (pr : Prepared) : Tables → List LaneRound → Element
  | t, [] => NormPolynomial.lift (OuterClaimChain.endpointSum t pr)
  | t, [r] => NormPolynomial.lift (roundValue t pr r.challenge)
  | t, r :: r2 :: rs => truthTail pr (boundTables t r.challenge) (r2 :: rs)

open NormDenseRound NormTerminalBinding in
/-- One honest step: the adopted `computeRound` message, reconstructed against
the honest endpoint sum, is the adopted `roundPolynomial`
(`OuterClaimChain.honest_first_message_polynomial`). -/
theorem honest_step_value (pr : Prepared) (t : Tables) (r : LaneRound)
    (h : Shape t pr) (hr : 0 < t.remaining) (hm : computeRound t pr = some r.truth) :
    OuterRound.evaluate (NormPolynomial.lift (OuterClaimChain.endpointSum t pr)) r.truth r.challenge =
      NormPolynomial.lift (roundValue t pr r.challenge) := by
  obtain ⟨message, hcr, _, hpoly⟩ := OuterClaimChain.honest_first_message_polynomial t pr h hr
  have hmsg : message = r.truth := Option.some.inj (hcr.symm.trans hm)
  subst hmsg
  apply GoldilocksExt3Field.element_eq
  rw [← OuterRound.polynomial_eval_exact, hpoly]
  exact round_polynomial_same_ordered_evaluation t pr r.challenge

open NormDenseRound NormTerminalBinding in
/-- The honest chain started from the extracted tables' cube sum
(`OuterClaimChain.endpointSum`) reaches `truthTail`. Deterministic; chained
through `OuterClaimChain.bound_endpoint_sum_is_round_value`. -/
theorem honest_truth_run (pr : Prepared) : ∀ (rs : List LaneRound) (t : Tables),
    Shape t pr → HonestTruth pr t rs →
      truthRun (NormPolynomial.lift (OuterClaimChain.endpointSum t pr)) rs = truthTail pr t rs
  | [], _, _, _ => rfl
  | [r], t, h, hh => by
      have hrem : 0 < t.remaining := by rw [hh.2]; exact Nat.one_pos
      simp only [truthRun, truthTail]
      exact honest_step_value pr t r h hrem hh.1
  | r :: r2 :: rs, t, h, hh => by
      have hrem : 0 < t.remaining := Nat.lt_of_lt_of_le (by decide) hh.2.1
      have hstep := honest_step_value pr t r h hrem hh.1
      have hbound : OuterClaimChain.endpointSum (boundTables t r.challenge) pr =
          roundValue t pr r.challenge :=
        OuterClaimChain.bound_endpoint_sum_is_round_value t pr r.challenge _ h hh.2.1
          (bind_tables_positive t r.challenge hrem)
      have ih := honest_truth_run pr (r2 :: rs) (boundTables t r.challenge)
        (bound_tables_shape t pr r.challenge h hrem) hh.2.2
      simp only [truthRun, truthTail]
      rw [hstep, ← hbound]
      exact ih

open NormDenseRound NormTerminalBinding in
/-- STRUCTURAL DESCRIPTION OF THE LAST ROUND (replaces the old scalar bridge
"ASSUMPTION 10").  `LastRoundData t tLast x rs` says, purely structurally, that
`tLast` is the iterated `NormDenseRound.boundTables` descendant of `t` under the
challenges the run actually drew in all rounds BUT the last, and that `x` is the
LAST drawn challenge.  Nothing about values is asserted: the value equation is
DERIVED from this in `truth_tail_of_last_round_data` below.

The empty lane is `False` on purpose: a lane with no rounds has no last round and
no last challenge, so there is nothing for `tLast` and `x` to name.  This costs
nothing for an accepted proof, because the adopted `Verifier.envelope` guard
forces `0 < degreeBits` and hence a nonempty lane -- see `lanes_nonempty`. -/
def LastRoundData (tLast : Tables) (x : Element) : Tables → List LaneRound → Prop
  | _, [] => False
  | t, [r] => tLast = t ∧ x = r.challenge
  | t, r :: r2 :: rs => LastRoundData tLast x (boundTables t r.challenge) (r2 :: rs)

open NormDenseRound NormTerminalBinding in
/-- The value equation the old ASSUMPTION 10 used to POSTULATE is now PROVED
from the structural `LastRoundData`: if `tLast` really is the iterated bound
descendant and `x` really is the last drawn challenge, then the honest chain's
endpoint `truthTail` IS the adopted `roundValue tLast pr x`.  Purely
definitional; no cryptography, no residue. -/
theorem truth_tail_of_last_round_data (pr : Prepared) (tLast : Tables) (x : Element) :
    ∀ (rs : List LaneRound) (t : Tables), LastRoundData tLast x t rs →
      truthTail pr t rs = NormPolynomial.lift (roundValue tLast pr x)
  | [], _, h => absurd h not_false
  | [r], t, h => by
      simp only [truthTail]
      rw [h.1, h.2]
  | r :: r2 :: rs, t, h =>
      truth_tail_of_last_round_data pr tLast x (r2 :: rs) (boundTables t r.challenge) h

/-! ## 4. Counting the bad events (adopted bounds, explicit finite space) -/

/-- ADOPTED BOUND: `OuterRound.fixed_different_claims_agree_at_most_degree`. -/
theorem round_bad_set_card (a b : Element) (r : LaneRound) (d : Nat)
    (hm : r.message.length ≤ d) (ht : r.truth.length ≤ d) : (roundBadSet a b r).card ≤ d := by
  unfold roundBadSet
  split
  · simp
  · rename_i hne
    exact OuterRound.fixed_different_claims_agree_at_most_degree a b r.message r.truth hne d hm ht
      Finset.univ

/-- ADOPTED BOUND: `OuterChallenge.fixed_point_set_preimage_bound`.  The number
of 32-byte digest TRIPLES whose three modular reductions land in the bad set. -/
theorem round_bad_triples_card (a b : Element) (r : LaneRound) (d : Nat)
    (hm : r.message.length ≤ d) (ht : r.truth.length ≤ d) :
    (OuterChallenge.tupleEvent (roundBadSet a b r)).card ≤ d * OuterChallenge.fiberCeiling ^ 3 :=
  (OuterChallenge.fixed_point_set_preimage_bound (roundBadSet a b r)).trans
    (Nat.mul_le_mul_right _ (round_bad_set_card a b r d hm ht))

/-- ADOPTED BOUND: `OuterChallenge.uniform_tuple_probability_bound`. -/
theorem round_bad_uniform (a b : Element) (r : LaneRound) (d : Nat)
    (hm : r.message.length ≤ d) (ht : r.truth.length ≤ d) :
    OuterChallenge.uniformTupleProbability (roundBadSet a b r) ≤
      (d : ℚ) * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 :=
  OuterChallenge.uniform_tuple_probability_bound _ d (round_bad_set_card a b r d hm ht)

/-- The per-round bad sets along the chain, in execution order. -/
def badSets (a b : Element) : List LaneRound → List (Finset Element)
  | [] => []
  | r :: rs => roundBadSet a b r ::
      badSets (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs

theorem bad_sets_nil (a b : Element) : badSets a b [] = [] := rfl

theorem bad_sets_cons (a b : Element) (r : LaneRound) (rs : List LaneRound) :
    badSets a b (r :: rs) = roundBadSet a b r ::
      badSets (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs := rfl

theorem bad_sets_length : ∀ (a b : Element) (rs : List LaneRound),
    (badSets a b rs).length = rs.length
  | _, _, [] => rfl
  | _, _, _ :: rs => congrArg Nat.succ (bad_sets_length _ _ rs)

/-- COUNTING UNION BOUND (a) : the union of the per-round bad sets, as a subset
of the explicit finite challenge space `Element`, has at most `d * n` points. -/
theorem bad_sets_union_card (d : Nat) : ∀ (a b : Element) (rs : List LaneRound),
    (∀ r ∈ rs, r.message.length ≤ d ∧ r.truth.length ≤ d) →
      ((badSets a b rs).foldr (· ∪ ·) ∅).card ≤ d * rs.length
  | _, _, [], _ => by rw [bad_sets_nil]; simp
  | a, b, r :: rs, hd => by
      have hhead := hd r (List.mem_cons_self _ _)
      have ih := bad_sets_union_card d (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs
        (fun q hq => hd q (List.mem_cons_of_mem _ hq))
      have hcard := round_bad_set_card a b r d hhead.1 hhead.2
      rw [bad_sets_cons, List.foldr_cons, List.length_cons, Nat.mul_succ]
      refine (Finset.card_union_le _ _).trans ?_
      omega

/-- COUNTING UNION BOUND (b) : the number of 32-byte digest triples that make
SOME round fail, summed round by round, is at most `d * n * ⌈2^256/p⌉^3` out of
the `(2^256)^3` triples of `OuterChallenge.digest_tuple_cardinality`.  This is
a statement about the explicit uniform law's finite sample space, NOT about the
real Keccak transcript. -/
theorem bad_sets_triple_card_sum (d : Nat) : ∀ (a b : Element) (rs : List LaneRound),
    (∀ r ∈ rs, r.message.length ≤ d ∧ r.truth.length ≤ d) →
      (((badSets a b rs).map (fun S => (OuterChallenge.tupleEvent S).card)).sum) ≤
        d * rs.length * OuterChallenge.fiberCeiling ^ 3
  | _, _, [], _ => by rw [bad_sets_nil]; simp
  | a, b, r :: rs, hd => by
      have hhead := hd r (List.mem_cons_self _ _)
      have ih := bad_sets_triple_card_sum d (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs
        (fun q hq => hd q (List.mem_cons_of_mem _ hq))
      have hhd := round_bad_triples_card a b r d hhead.1 hhead.2
      rw [bad_sets_cons, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ,
        Nat.add_mul]
      omega

/-- COUNTING UNION BOUND (c) : the sum over rounds of the per-round mass under
the EXPLICIT uniform 32-byte-triple law of `OuterChallenge`. -/
theorem bad_sets_uniform_sum (d : Nat) : ∀ (a b : Element) (rs : List LaneRound),
    (∀ r ∈ rs, r.message.length ≤ d ∧ r.truth.length ≤ d) →
      (((badSets a b rs).map OuterChallenge.uniformTupleProbability).sum) ≤
        ((d * rs.length : Nat) : ℚ) *
          ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3
  | _, _, [], _ => by rw [bad_sets_nil]; simp
  | a, b, r :: rs, hd => by
      have hhead := hd r (List.mem_cons_self _ _)
      have ih := bad_sets_uniform_sum d (OuterRound.evaluate a r.message r.challenge)
        (OuterRound.evaluate b r.truth r.challenge) rs
        (fun q hq => hd q (List.mem_cons_of_mem _ hq))
      have hhd := round_bad_uniform a b r d hhead.1 hhead.2
      rw [bad_sets_cons, List.map_cons, List.sum_cons]
      refine (add_le_add hhd ih).trans (le_of_eq ?_)
      rw [List.length_cons]
      push_cast
      ring

/-! ## 5. The two lanes of an `Integrated.verify` execution -/

def logLaneOf (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) : List LaneRound :=
  lane e.commitRound Prod.fst Verifier.RoundChallenges.log truths
    (Verifier.start (e.initialTranscript c p)) (p.logRounds.zip p.gateRounds)

def gateLaneOf (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) : List LaneRound :=
  lane e.commitRound Prod.snd Verifier.RoundChallenges.gate truths
    (Verifier.start (e.initialTranscript c p)) (p.logRounds.zip p.gateRounds)

theorem derived_log_claim (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) :
    (Verifier.derivedRounds e c p).logClaim = (claimedRun 0 (logLaneOf e c p truths)).toVerifier :=
  log_lane_claimed_run e.commitRound truths (Verifier.start (e.initialTranscript c p))
    (p.logRounds.zip p.gateRounds)

/-- UNUSED BY THE CAPSTONE.  True and deterministic, but with the gate
conclusion deleted nothing consumes it; it is retained as the gate-side twin of
`derived_log_claim` for whoever builds the gate prover chain. -/
theorem derived_gate_claim (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) :
    (Verifier.derivedRounds e c p).gateClaim = (claimedRun 0 (gateLaneOf e c p truths)).toVerifier :=
  gate_lane_claimed_run e.commitRound truths (Verifier.start (e.initialTranscript c p))
    (p.logRounds.zip p.gateRounds)

theorem lane_length_of_shape (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) (hl : p.logRounds.length = c.degreeBits)
    (hg : p.gateRounds.length = c.degreeBits) :
    (logLaneOf e c p truths).length = c.degreeBits ∧
    (gateLaneOf e c p truths).length = c.degreeBits := by
  refine ⟨?_, ?_⟩
  · rw [logLaneOf, lane_length, List.length_zip, hl, hg, Nat.min_self]
  · rw [gateLaneOf, lane_length, List.length_zip, hl, hg, Nat.min_self]

/-- The adopted `Verifier.shape` guard fixes the round counts and every round
message length: five for the log lane, `quotientDegree + 2` for the gate lane. -/
theorem shape_round_lengths (pin : Verifier.Pinned) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Verifier.shape pin c p = true) :
    p.logRounds.length = c.degreeBits ∧ p.gateRounds.length = c.degreeBits ∧
    (∀ r ∈ p.logRounds, r.length = 5) ∧
    (∀ r ∈ p.gateRounds, r.length = c.quotientDegree + 2) := by
  have hd := of_decide_eq_true h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlr, hgr, hla, hga⟩ := hd
  refine ⟨hlr, hgr, ?_, ?_⟩
  · intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp hla r hr)
  · intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp hga r hr)

/-- The adopted `Verifier.envelope` guard bounds the two protocol parameters
that enter the counting bound. -/
theorem envelope_parameter_bounds (c : Verifier.Config) (h : Verifier.envelope c = true) :
    c.degreeBits ≤ 13 ∧ c.quotientDegree + 2 ≤ 10 := by
  have hd := of_decide_eq_true h
  obtain ⟨-, hdb, -, -, -, -, -, -, -, -, -, hqd, -⟩ := hd
  exact ⟨hdb, hqd⟩

/-- The adopted `Verifier.envelope` guard also forces `0 < degreeBits`. -/
theorem envelope_degree_bits_positive (c : Verifier.Config) (h : Verifier.envelope c = true) :
    0 < c.degreeBits := by
  have hd := of_decide_eq_true h
  exact hd.1

/-- Both lanes of an execution that passes `Verifier.shape` and
`Verifier.envelope` are NONEMPTY.  This is what makes the structural
`LastRoundData` (which is `False` on the empty lane) a genuine constraint rather
than a vacuity: for every accepted proof there really is a last round. -/
theorem lanes_nonempty (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) (pin : Verifier.Pinned)
    (hshape : Verifier.shape pin c p = true) (henv : Verifier.envelope c = true) :
    logLaneOf e c p truths ≠ [] ∧ gateLaneOf e c p truths ≠ [] := by
  obtain ⟨hlr, hgr, -, -⟩ := shape_round_lengths pin c p hshape
  obtain ⟨h1, h2⟩ := lane_length_of_shape e c p truths hlr hgr
  have hpos := envelope_degree_bits_positive c henv
  constructor
  · intro hc; rw [hc] at h1; simp at h1; omega
  · intro hc; rw [hc] at h2; simp at h2; omega

theorem log_lane_message_lengths (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) (h : ∀ r ∈ p.logRounds, r.length = 5)
    (r : LaneRound) (hr : r ∈ logLaneOf e c p truths) : r.message.length = 5 := by
  obtain ⟨m, hm, he⟩ := lane_messages e.commitRound Prod.fst Verifier.RoundChallenges.log
    truths (Verifier.start (e.initialTranscript c p)) (p.logRounds.zip p.gateRounds) r hr
  have hmem : m.1 ∈ p.logRounds := by
    have := List.of_mem_zip (l₁ := p.logRounds) (l₂ := p.gateRounds) (a := m.1) (b := m.2)
      (by simpa using hm)
    exact this.1
  rw [he, List.length_map]
  exact h m.1 hmem

theorem gate_lane_message_lengths (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (truths : List (List Element)) (h : ∀ r ∈ p.gateRounds, r.length = c.quotientDegree + 2)
    (r : LaneRound) (hr : r ∈ gateLaneOf e c p truths) :
    r.message.length = c.quotientDegree + 2 := by
  obtain ⟨m, hm, he⟩ := lane_messages e.commitRound Prod.snd Verifier.RoundChallenges.gate
    truths (Verifier.start (e.initialTranscript c p)) (p.logRounds.zip p.gateRounds) r hr
  have hmem : m.2 ∈ p.gateRounds := by
    have := List.of_mem_zip (l₁ := p.logRounds) (l₂ := p.gateRounds) (a := m.1) (b := m.2)
      (by simpa using hm)
    exact this.2
  rw [he, List.length_map]
  exact h m.2 hmem

open NormDenseRound NormTerminalBinding in
/-- Every honest (truth) message of the extracted norm tables has exactly five
coefficients (`NormDenseRound.current_round_coefficients_shaped`). -/
theorem honest_truth_lengths (pr : Prepared) : ∀ (rs : List LaneRound) (t : Tables),
    Shape t pr → HonestTruth pr t rs → ∀ r ∈ rs, r.truth.length = 5
  | [], _, _, _, _, hr => by simp at hr
  | [r], t, h, hh, q, hq => by
      have hrem : 0 < t.remaining := by rw [hh.2]; exact Nat.one_pos
      obtain ⟨_, _, _, hcr, hlen⟩ := current_round_coefficients_shaped t pr h hrem
      have : q = r := by simpa using hq
      subst this
      rw [← Option.some.inj (hcr.symm.trans hh.1)]
      exact hlen
  | r :: r2 :: rs, t, h, hh, q, hq => by
      have hrem : 0 < t.remaining := Nat.lt_of_lt_of_le (by decide) hh.2.1
      rcases List.mem_cons.mp hq with hqe | hqm
      · obtain ⟨_, _, _, hcr, hlen⟩ := current_round_coefficients_shaped t pr h hrem
        subst hqe
        rw [← Option.some.inj (hcr.symm.trans hh.1)]
        exact hlen
      · exact honest_truth_lengths pr (r2 :: rs) (boundTables t r.challenge)
          (bound_tables_shape t pr r.challenge h hrem) hh.2.2 q hqm

/-! ## 6. The WHIR-side bad events

NOTHING IN THIS SECTION IS USED BY THE CAPSTONE.  Every declaration below is a
restatement of an adopted WHIR/Merkle counting bound or binding reduction.  None
of them feeds `accepted_norm_cube_sum_vanishes`, `outer_failure_bound`,
`outer_failure_triple_count` or `conditional_soundness`, and none of their
bounds is aggregated into the `195` of the capstone.  They are kept because they
record, in this file's own vocabulary, the events that the capstone's bound does
NOT cover -- the events that in fact DOMINATE the deployed system's soundness
error.  Read them as a map of the hole, not as part of the argument. -/

/-- BAD EVENT (WHIR inner quadratic round).  Bounded by the ADOPTED
`WhirQuadratic.fixed_different_claims_agree_at_most_two` (at most 2 points) and,
under the explicit uniform 120-byte law, by the ADOPTED
`WhirChallenge.fixed_quadratics_uniform_byte_probability_bound`
(`2 * (⌈2^320/p⌉ / 2^320)^3`). -/
def WhirQuadraticAgreement (claimA claimB : Element) (a b : WhirQuadratic.Message)
    (r : Element) : Prop := r ∈ WhirChallenge.quadraticPoints claimA claimB a b

theorem whir_quadratic_bad_card (claimA claimB : Element) (a b : WhirQuadratic.Message)
    (hne : claimA ≠ claimB) : (WhirChallenge.quadraticPoints claimA claimB a b).card ≤ 2 :=
  WhirQuadratic.fixed_different_claims_agree_at_most_two claimA claimB a b hne Finset.univ

theorem whir_quadratic_uniform (claimA claimB : Element) (a b : WhirQuadratic.Message)
    (hne : claimA ≠ claimB) :
    WhirChallenge.uniformByteProbability (WhirChallenge.quadraticPoints claimA claimB a b) ≤
      2 * ((WhirChallenge.fiberCeiling : ℚ) / (WhirChallenge.wordSize : ℚ)) ^ 3 :=
  WhirChallenge.fixed_quadratics_uniform_byte_probability_bound claimA claimB a b hne

/-- BAD EVENT (WHIR random linear combination).  Bounded by the ADOPTED
`WhirRlc.fixed_different_vectors_agree_at_most_length_sub_one` (at most
`n - 1` points) and, under the explicit uniform 120-byte law, by the ADOPTED
`WhirRlc.fixed_vectors_uniform_120byte_probability_bound`. -/
def WhirRlcAgreement (cs ds : List Verifier.Ext3) (r : Element) : Prop :=
  r ∈ WhirRlc.agreementPoints cs ds Finset.univ

theorem whir_rlc_bad_card (cs ds : List Verifier.Ext3) (hlen : cs.length = ds.length)
    (hne : cs ≠ ds) : (WhirRlc.agreementPoints cs ds Finset.univ).card ≤ cs.length - 1 :=
  WhirRlc.fixed_different_vectors_agree_at_most_length_sub_one cs ds hlen hne Finset.univ

theorem whir_rlc_uniform (cs ds : List Verifier.Ext3) (hlen : cs.length = ds.length)
    (hne : cs ≠ ds) :
    WhirChallenge.uniformByteProbability (WhirRlc.agreementPoints cs ds Finset.univ) ≤
      ((cs.length - 1 : Nat) : ℚ) *
        ((WhirChallenge.fiberCeiling : ℚ) / (WhirChallenge.wordSize : ℚ)) ^ 3 :=
  WhirRlc.fixed_vectors_uniform_120byte_probability_bound cs ds hlen hne

/-- BAD EVENT (WHIR domain-point agreement at the sampled query indices):
every drawn query index is a point where two distinct fixed canonical
coefficient vectors evaluate equally.  Bounded by the ADOPTED
`WhirDomainBridge.fixed_canonical_vectors_agree_at_most_length_sub_one_queries`
(at most `n - 1` of the `2^k` domain indices), so it is IMPOSSIBLE once more
than `n - 1` distinct queries are drawn: no probability is needed. -/
def WhirDomainAgreement (o : WhirIntermediate.OpenParams) (k : Nat)
    (cs ds : List Arithmetic.Ext3) (queries : Finset (Fin (2 ^ k))) : Prop :=
  ∀ index ∈ queries,
    WhirTerminal.polynomial cs (WhirIntermediate.domainPoint o index.val) =
      WhirTerminal.polynomial ds (WhirIntermediate.domainPoint o index.val)

theorem whir_domain_agreement_impossible (o : WhirIntermediate.OpenParams) (k : Nat) (hk : k ≤ 32)
    (hg : o.domainGenerator.val = (GoldilocksDomain.generator k).val)
    (hcoset : 0 < o.cosetSize) (hnum : 0 < o.numCosets) (hsize : o.cosetSize * o.numCosets = 2 ^ k)
    (cs ds : List Arithmetic.Ext3) (hc : ∀ x ∈ cs, Arithmetic.Canonical x)
    (hd : ∀ x ∈ ds, Arithmetic.Canonical x) (hlen : cs.length = ds.length) (hne : cs ≠ ds)
    (queries : Finset (Fin (2 ^ k))) (hq : cs.length - 1 < queries.card) :
    ¬ WhirDomainAgreement o k cs ds queries := by
  intro hall
  obtain ⟨index, hmem, hneq⟩ := WhirDomainBridge.enough_distinct_queries_separate_fixed_vectors
    o k hk hg hcoset hnum hsize cs ds hc hd hlen hne queries hq
  exact hneq (hall index hmem)

/-- BAD EVENT (Merkle / leaf compression collision).  This one has NO counting
bound in the audit: `Merkle.path_collision_exposes_hash_collision` and
`WhirRowBinding.distinct_accepted_dot_values_expose_hash_collision` are
DETERMINISTIC reductions to a CONCRETE unequal pair of hash inputs (two opened
leaf rows, or two 64-byte compression inputs of the two extracted paths).

REMARK ON HONESTY.  The GLOBAL statement `¬ WhirRowBinding.HashCollision hash`
is FALSE for every `hash : Spongefish.Hash`: `Spongefish.Bytes = List UInt8` is
infinite and a digest is 32 bytes, so pigeonhole always supplies a collision.
Assuming it would make every theorem below vacuous.  The assumption such a
field WOULD have to take is `NoCollisionAmong` on the FINITE list of byte
strings an execution actually hashes, which is satisfiable.  No such field
exists here: both hash fields were DELETED, so this definition is used by
nothing in the capstone. -/
def MerkleCollision (hash : Spongefish.Hash) : Prop := WhirRowBinding.HashCollision hash

/-- No two DISTINCT members of a concrete finite list of hash inputs collide.
Unlike global collision freedom this is satisfiable (it holds vacuously on a
singleton list), so assuming it does not trivialise anything. -/
def NoCollisionAmong (hash : Spongefish.Hash) (inputs : List Spongefish.Bytes) : Prop :=
  ∀ a ∈ inputs, ∀ b ∈ inputs, hash a = hash b → a = b

/-- ADOPTED REDUCTION restated (`WhirRowBinding.accepted_decoded_dots_bind_or_collision`):
two accepted openings of the same Merkle root at the same index either give the
SAME decoded dot value, or exhibit the adopted `WhirRowBinding.RowCollision`,
i.e. a concrete unequal pair of actual hash inputs. -/
theorem opened_dot_binds_or_row_collision (hash : Spongefish.Hash) (root : Merkle.Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Spongefish.Bytes) (s t otherS otherT : Spongefish.State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRowBinding.decodedDot weights layout row = some value)
    (hd' : WhirRowBinding.decodedDot weights layout otherRow = some otherValue) :
    value = otherValue ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  WhirRowBinding.accepted_decoded_dots_bind_or_collision hash root depth index indices
    otherIndices layout hints otherHints s t otherS otherT rows otherRows row otherRow weights
    value otherValue h h' hm hm' hd hd'

/-- DEPRECATED / VACUOUS (recorded 2026-09-11). The hypothesis `hfree` negates
`WhirRowBinding.RowCollision`, whose second disjunct (two distinct 64-byte inputs
with equal hash) is a finite pigeonhole tautology, so `hfree` is UNSATISFIABLE and
this theorem, while true, has no instance. It has no consumers in the adopted tree.
Use `OpenedDotBinding.opened_dot_binds_under_no_collision_among`, which assumes
`NoCollisionAmong` on the execution-computed input list instead (the pattern this
file already uses), and see `LocalizedCollisions` for the general finding. -/
theorem no_row_collision_binds_opened_dot (hash : Spongefish.Hash) (root : Merkle.Digest)
    (depth index : Nat) (indices otherIndices : List Nat) (layout : WhirRows.Layout)
    (hints otherHints : Spongefish.Bytes) (s t otherS otherT : Spongefish.State)
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (weights : List Arithmetic.Ext3) (value otherValue : Arithmetic.Ext3)
    (hfree : ¬ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes)
    (h : WhirRows.openGroup hash root depth indices layout hints s = some (rows, t))
    (h' : WhirRows.openGroup hash root depth otherIndices layout otherHints otherS =
      some (otherRows, otherT))
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hd : WhirRowBinding.decodedDot weights layout row = some value)
    (hd' : WhirRowBinding.decodedDot weights layout otherRow = some otherValue) :
    value = otherValue :=
  (opened_dot_binds_or_row_collision hash root depth index indices otherIndices layout hints
    otherHints s t otherS otherT rows otherRows row otherRow weights value otherValue h h' hm hm'
    hd hd').resolve_right hfree

/-! ## 7. The norm terminal bridge (adopted deterministic identities) -/

open NormDenseRound NormTerminalBinding in
/-- ADOPTED CHAIN, no new cryptography: the verifier's own norm terminal
evaluation on the proof's used claims IS the extracted tables' honest last
round value.  Chained through
`NormTerminalBinding.last_round_target_is_bound_terminal` (remaining = 1) and
`NormTerminalBinding.fully_bound_target_is_engine_terminal`.  All remaining
hypotheses are the adopted provenance obligations, listed one by one; they are
fields of `Assumptions` below. -/
theorem norm_terminal_is_honest_last_value (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof)
    (tLast : Tables) (pr : Prepared) (constants extra : List Verifier.Ext3) (x : Element)
    (point : List Verifier.Ext3)
    (hshape : Shape tLast pr) (hrem : tLast.remaining = 1)
    (hc : Compatible c (boundTables tLast x) pr constants) (hlam : LambdaProvenance pr)
    (hmap : WireMapMatches c.publicInputWireMap (boundTables tLast x).bindings)
    (heta : EtaProvenance (NormPolynomial.lift pr.challenges.eta) (boundTables tLast x).bindings)
    (hprefix : PrefixAt point (boundTables tLast x).bindings)
    (heq : (cell (boundTables tLast x).eq).toVerifier = Norm.eqEvaluation pr.challenges.tau point)
    (hsub : (cell (boundTables tLast x).subgroup).toVerifier =
      Norm.subgroupEvaluation c.subgroupPowers point)
    (hi : Norm.challengesFromInitial (e.initialTranscript c p) = pr.challenges)
    (hp : Verifier.normTerminalInput p = toTerminalInput (boundTables tLast x) constants extra) :
    (Integrated.modelEngine e decode).logTerminal c (e.initialTranscript c p) p point =
      roundValue tLast pr x := by
  have h1 := (last_round_target_is_bound_terminal tLast pr x hshape hrem).2
  have hshape' : Shape (boundTables tLast x) pr :=
    bound_tables_shape tLast pr x hshape (by omega)
  have h2 := fully_bound_target_is_engine_terminal e (e.initialTranscript c p) p
    (boundTables tLast x) pr c constants extra point hshape' hc hlam hmap heta hprefix heq hsub hi hp
  exact (Option.some.inj (h2.symm.trans h1))

/-! ## 8. The named cryptographic and extraction assumptions -/

open NormDenseRound NormTerminalBinding in
/-- EVERY assumption this file's soundness statement rests on, as a named,
enumerable `Prop` field.  Nothing is hidden inside a definition: the two
theorems below use exactly these fields plus `Integrated.verify` acceptance and
the explicit "no bad event" hypotheses.

Parameters: the engine/decoder/config/proof of the adopted `Integrated.verify`;
the EXTRACTED norm prover tables `t` (fresh) and `tLast` (one variable left) with
prepared challenges `pr`, the non-routed wire values `extra`, the preprocessed
constants `constants` and the last drawn log challenge `x`; the honest
honest round-message list `logTruths` of the LOG lane, plus the two FREE and
MEANINGLESS gate-lane comparison parameters `gateCompareRounds`/`gateCompare`
(see ASSUMPTION 18 and the `gate lane is not proved` note); an opaque
`fixedness` proposition; a per-round
challenge law `law` and a rational `failure` that assumptions 2-3 (below) bound
ABOVE only.  Neither assumption lower-bounds `failure` by any real quantity.

WHAT IS DELIBERATELY ABSENT.  There is NO field relating the committed WHIR
columns to the extracted tables `t`/`tLast`.  An earlier draft carried two such
fields (a hash-collision-freedom field and a PCS-extractability field producing
`IntegratedTerminalChain.HonestOpenings`); both were DELETED because no proof in
this file ever consumed them, so keeping them would have advertised a link that
the argument does not use.  Consequently THE EXTRACTION JOIN IS OPEN: nothing
here forces the extracted tables to be the ones the prover actually committed
to.  ASSUMPTIONS 15 and 17 below simply POSTULATE, at the terminal, that the
proof's used claims are cells of the extracted tables.  See
`opened_dot_binds_or_row_collision` in section 6 for the adopted Merkle-binding
reduction that a real extractor would have to be built on; it is stated there
and used by nothing in the soundness chain. -/
structure Assumptions (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (c : Verifier.Config) (p : Verifier.Proof)
    (t tLast : Tables) (pr : Prepared) (constants extra : List Verifier.Ext3) (x : Element)
    (logTruths gateCompareRounds : List (List Element))
    (gateCompare : Element) (fixedness : Prop) (law : Finset Element → ℚ) (failure : ℚ) :
    Prop where
  /-- ASSUMPTION 1 (`adaptiveFixedness`).  For every outer round of both lanes
  the compared pair (prover message polynomial, honest round polynomial) is
  determined BEFORE that round's challenge is squeezed.  This is exactly the
  "fixed different claims" hypothesis of the adopted counting theorem
  `OuterRound.fixed_different_claims_agree_at_most_degree`.  NOT PROVED: in the
  executable model the whole `Verifier.Proof` is an input, but the real
  Fiat--Shamir adversary chooses the proof AFTER seeing the transcript that
  determines the challenges.  What would prove it: a rewinding / random-oracle
  programming argument over the adopted `Transcript`/`Spongefish` models. -/
  adaptiveFixedness : fixedness
  /-- ASSUMPTION 2 (`challengeUniform`).  GIVEN fixedness, the real probability
  `law S` that a round's challenge lands in an already-determined set `S` is at
  most the mass of `S` under the EXPLICIT ideal law of `OuterChallenge`: three
  independent uniform 32-byte digests reduced mod p, i.e.
  `OuterChallenge.uniformTupleProbability`, whose bound is
  `d * (⌈2^256/p⌉ / 2^256)^3`.  NOT PROVED: `OuterChallenge` DEFINES this law on
  all triples of 32-byte strings and proves nothing about the deterministic
  Keccak of `Transcript.Hash`.  What would prove it: a random-oracle model for
  the deployed hash plus a domain-separation argument for
  `Transcript.challengeInput`. -/
  challengeUniform : fixedness → ∀ S : Finset Element,
    law S ≤ OuterChallenge.uniformTupleProbability S
  /-- ASSUMPTION 3 (`challengeIndependent`).  The rational `failure` is at most
  the sum of the per-round `law` masses over both lanes.

  WHAT `failure` IS.  It is a FREE RATIONAL PARAMETER of this structure, not a
  probability computed from anything in the model.  This field bounds `failure`
  ABOVE by the sum of `law` over the bad sets, and assumption 2 bounds `law`
  above by the ideal mass; NOTHING bounds `failure` below, so `failure := 0`
  with `law := 0` satisfies both.  Identifying `failure` with the real failure
  probability needs an external bridge that no field here supplies, and
  `law` is likewise an arbitrary `Finset Element -> Q`.  Everything downstream
  (`outer_failure_bound`, `conditional_soundness`'s last conjunct) is therefore
  a statement about whatever `failure` and `law` a user instantiates with, and
  is only as meaningful as this field and ASSUMPTION 2 are true of them.

  NOT PROVED: as a union bound over challenges all derived from one evolving
  transcript it needs the freshness/independence of each squeeze given the
  prefix.  What would prove it: a conditional-probability model over the adopted
  `Transcript` state machine, which the audit does not build (it counts on a
  fixed finite space instead). -/
  challengeIndependent : failure ≤
    ((badSets 0 (NormPolynomial.lift (OuterClaimChain.endpointSum t pr))
      (logLaneOf e c p logTruths)).map law).sum +
    ((badSets 0 gateCompare (gateLaneOf e c p gateCompareRounds)).map law).sum
  /-- ASSUMPTION 4 (`extractedTablesShape`).  The extracted fresh norm tables
  satisfy the adopted `NormDenseRound.Shape`.  NOT PROVED: extraction itself is
  not formalised; this records the shape the extractor must deliver. -/
  extractedTablesShape : Shape t pr
  /-- ASSUMPTION 5 (`extractedTruthChain`).  Along the challenges the run
  actually drew, the honest messages `logTruths` are the adopted
  `NormDenseRound.computeRound` of the successively `bindTables`-bound extracted
  tables, the last of which has one variable left.  NOT PROVED: same extraction
  boundary.  Everything downstream of this field IS proved (`honest_truth_run`,
  `honest_truth_lengths`). -/
  extractedTruthChain : HonestTruth pr t (logLaneOf e c p logTruths)
  /-- ASSUMPTION 6 (`lastTablesShape`). -/
  lastTablesShape : Shape tLast pr
  /-- ASSUMPTION 7 (`lastTablesRemaining`): the extracted last-round tables have
  exactly one variable left, the hypothesis of the adopted
  `NormTerminalBinding.last_round_target_is_bound_terminal`. -/
  lastTablesRemaining : tLast.remaining = 1
  /-- ASSUMPTION 8 (`lastRoundData`): STRUCTURAL.  `tLast` is the iterated
  `NormDenseRound.boundTables` descendant of the extracted tables `t` under the
  challenges the run actually drew in every round but the last, and `x` IS the
  last drawn challenge of the log lane.  This is a statement about the tables and
  the transcript, not an equation between field values: the value equation
  `truthTail pr t (logLaneOf ...) = lift (roundValue tLast pr x)` -- which an
  earlier draft POSTULATED as a scalar bridge -- is DERIVED from this field by
  `truth_tail_of_last_round_data`, with no residue.

  It is a genuine constraint, not a vacuity: `LastRoundData` is `False` on the
  empty lane, and `lanes_nonempty` shows that the adopted `Verifier.shape` and
  `Verifier.envelope` guards force the lane of an accepted proof to be nonempty,
  so a last round always exists.  What is still assumed is only that the
  extraction delivers `t`; GIVEN `t` and the lane, this field pins `tLast` and
  `x` uniquely. -/
  lastRoundData : LastRoundData tLast x t (logLaneOf e c p logTruths)
  /-- ASSUMPTION 9 (`normCompatible`): the adopted `NormTerminalBinding.Compatible`
  VK/configuration correspondence (routed count, constant offset, `kIs`). -/
  normCompatible : Compatible c (boundTables tLast x) pr constants
  /-- ASSUMPTION 10 (`normLambda`): the adopted `LambdaProvenance` (the prepared
  lambda powers really are `lambda^j`). -/
  normLambda : LambdaProvenance pr
  /-- ASSUMPTION 11 (`normWireMap`): the adopted `WireMapMatches` (the public
  input wire-map bytes decode to the bindings' rows and columns). -/
  normWireMap : WireMapMatches c.publicInputWireMap (boundTables tLast x).bindings
  /-- ASSUMPTION 12 (`normEta`): the adopted `EtaProvenance` (the binding weights
  are `eta^i`). -/
  normEta : EtaProvenance (NormPolynomial.lift pr.challenges.eta) (boundTables tLast x).bindings
  /-- ASSUMPTION 13 (`normPrefix`): the adopted `PrefixAt` (the accumulated eq
  prefixes are those of the verifier's log point). -/
  normPrefix : PrefixAt (Verifier.derivedRounds e c p).logPoint (boundTables tLast x).bindings
  /-- ASSUMPTION 14 (`normEqCell`): the fully bound eq cell IS
  `Norm.eqEvaluation tau point`.  NOT PROVED anywhere in the audit: the source's
  `eq_evals_ext3(tau)` table is not modelled. -/
  normEqCell : (cell (boundTables tLast x).eq).toVerifier =
    Norm.eqEvaluation pr.challenges.tau (Verifier.derivedRounds e c p).logPoint
  /-- ASSUMPTION 15 (`normSubgroupCell`): the fully bound subgroup cell IS
  `Norm.subgroupEvaluation` of the VK subgroup powers.  NOT PROVED: the VK
  subgroup table is not modelled. -/
  normSubgroupCell : (cell (boundTables tLast x).subgroup).toVerifier =
    Norm.subgroupEvaluation c.subgroupPowers (Verifier.derivedRounds e c p).logPoint
  /-- ASSUMPTION 16 (`normChallenges`): the transcript's seven log challenges and
  `tau` are the prover's prepared challenges.  NOT PROVED: transcript derivation
  is an `Engine` observation. -/
  normChallenges : Norm.challengesFromInitial (e.initialTranscript c p) = pr.challenges
  /-- ASSUMPTION 17 (`normClaims`): the proof's used log claims ARE the fully
  bound cells of the extracted tables.

  THIS IS THE EXTRACTION JOIN, AND IT IS ASSUMED OUTRIGHT.  An earlier draft's
  docstring claimed this field was "where the PCS-extractability assumption is
  consumed"; that was FALSE, and the PCS field has since been deleted because
  nothing consumed it.  This field is INDEPENDENT: no assumption in this
  structure, and no theorem in this file, connects the values the WHIR/Merkle
  check actually bound to the cells of `tLast`.  The adopted
  `NormTerminalBinding.fully_bound_cells_are_packed_folds` and
  `IntegratedTerminalChain.accepted_whir_claims_are_table_evaluations` are the
  identities a real extractor would have to be threaded through to DISCHARGE
  this field; that threading is not done here.  So an adversary who can open the
  WHIR commitment to something other than `tLast` is not excluded by anything
  below -- only by fiat, here. -/
  normClaims : Verifier.normTerminalInput p =
    toTerminalInput (boundTables tLast x) constants extra
  /-- ASSUMPTION 18 (`gateCompareDegree`): the gate lane's COMPARISON round
  polynomials have at most `quotientDegree + 2` non-constant coefficients, the
  same degree the verifier's `Verifier.shape` guard forces on the prover's own
  messages.

  READ THIS FIELD NARROWLY.  `gateCompareRounds` and `gateCompare` are FREE
  PARAMETERS; no field of this structure relates them to any gate table, gate
  aggregate or Boolean-cube sum, and NO GATE CONCLUSION IS DRAWN ANYWHERE IN
  THIS FILE (see the `gate_lane_is_not_proved` note in section 9).  This field
  therefore does exactly one thing: it supplies the degree side of the COUNTING
  bound `outer_failure_triple_count` / `outer_failure_bound` for the gate lane's
  outer rounds, so that the quoted `195` covers both lanes' agreement events
  rather than only the log lane's.  It is trivially satisfiable
  (`gateCompareRounds := []` makes every `r.truth` empty), which is harmless
  precisely because nothing is concluded from it. -/
  gateCompareDegree :
    ∀ r ∈ gateLaneOf e c p gateCompareRounds, r.truth.length ≤ c.quotientDegree + 2

/-! ## 9. The core conditional soundness theorems -/

section Core
open NormDenseRound NormTerminalBinding
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates}
  {c : Verifier.Config} {p : Verifier.Proof} {t tLast : Tables} {pr : Prepared}
  {constants extra : List Verifier.Ext3} {x : Element}
  {logTruths gateCompareRounds : List (List Element)} {gateCompare : Element} {fixedness : Prop}
  {law : Finset Element → ℚ} {failure : ℚ}

/-- CORE CONDITIONAL SOUNDNESS, NORM/logUp LANE.  If the adopted
`Integrated.verify` accepts, the assumptions hold, and no outer log round has
its agreement bad event, then the EXTRACTED prover tables satisfy the relation
the verifier is checking: their norm/logUp aggregate sums to zero over the
Boolean cube (`OuterClaimChain.endpointSum t pr = Verifier.zero`).  That is
EXACTLY the `zeroSum` field the adopted
`IntegratedTerminalChain.HonestNormProver` has to assume, and by
`OuterClaimChain.chain_initial_claim` it is equivalent to the source's zero
initial claim being in lockstep with the honest prover. -/
theorem accepted_norm_cube_sum_vanishes (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode c p t tLast pr constants extra x logTruths gateCompareRounds
      gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain c p = .ok ())
    (hfree : BadEventFree 0 (NormPolynomial.lift (OuterClaimChain.endpointSum t pr))
      (logLaneOf e c p logTruths)) :
    OuterClaimChain.endpointSum t pr = Verifier.zero := by
  obtain ⟨-, -, -, -, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain c p hacc
  obtain ⟨-, -, -, -, -, -, -, -, -, hlog, -, -⟩ :=
    (IntegratedTerminalChain.verify_iff_solidity_order (Integrated.modelEngine e decode)
      pin chain c p).mp hv
  have hlog' : (Integrated.modelEngine e decode).logTerminal c (e.initialTranscript c p) p
      (Verifier.derivedRounds e c p).logPoint = (Verifier.derivedRounds e c p).logClaim := hlog
  have hbridge := norm_terminal_is_honest_last_value e decode c p tLast pr constants extra x
    (Verifier.derivedRounds e c p).logPoint A.lastTablesShape A.lastTablesRemaining
    A.normCompatible A.normLambda A.normWireMap A.normEta A.normPrefix A.normEqCell
    A.normSubgroupCell A.normChallenges A.normClaims
  have htruth := honest_truth_run pr (logLaneOf e c p logTruths) t A.extractedTablesShape
    A.extractedTruthChain
  have hclaim := derived_log_claim e c p logTruths
  have heq : claimedRun 0 (logLaneOf e c p logTruths) =
      truthRun (NormPolynomial.lift (OuterClaimChain.endpointSum t pr))
        (logLaneOf e c p logTruths) := by
    apply GoldilocksExt3Field.element_eq
    rw [← hclaim, ← hlog', hbridge, htruth, (truth_tail_of_last_round_data pr tLast x _ t A.lastRoundData)]
    rfl
  exact (congrArg Element.toVerifier
    (chain_initial_agreement (logLaneOf e c p logTruths) 0 _ hfree heq)).symm

/-! ### THE GATE LANE IS NOT PROVED

An earlier draft of this file carried a second core theorem,
`accepted_gate_cube_sum_vanishes`, concluding `gateCubeSum = 0` from acceptance,
an assumption `gateTerminalIsHonest`, and gate-lane bad-event-freeness.  IT HAS
BEEN DELETED, because it was DEGENERATE, not merely weak.

Why it was degenerate.  `gateTruths` and `gateCubeSum` were free parameters with
no relation to any gate table, and unlike the norm lane there was no analogue of
the extracted-truth-chain assumption tying `gateTruths` to a computed gate
round list.  Instantiating `gateTruths := []` makes every `r.truth` empty, so
`truthRun b lane` collapses to `b * half ^ degreeBits`, which is INVERTIBLE in
`b`.  An adversary could therefore choose `gateCubeSum` to be the unique
preimage of the verifier's own gate terminal, satisfying `gateTerminalIsHonest`
for ANY accepting proof.  The theorem then restated nothing beyond "the
verifier's gate terminal check passed", while its name and docstring advertised
"the gate constraints are satisfied".  That gap is exactly the kind of claim
this file must not make.

Why it was not repaired HERE.  Repairing it needs a gate analogue of the norm
lane's honest chain, i.e. a definition of the gate cube sum as an actual
Boolean-cube sum of the gate aggregate plus an assumption chaining the gate
round list to it.  When this note was first written the adopted gate modules
could not supply any of the pieces.  THREE OF THE FOUR BLOCKERS ARE NOW GONE,
supplied by the adopted `Audit.Wire3.GateDenseRound`; the fourth remains, and
so does the reason this FILE does not state a gate conclusion.

GONE (per the `GateDenseRound` header):

* The interpolation gap is closed.  `GateDenseRound.computeRound` is the WHOLE
  of gate_ext3_v2.rs `current_round` INCLUDING the interpolation call and the
  dropped constant, built on `GateSlotRound.currentRoundGrid` /
  `currentRoundEvaluations` plus `OuterInterpolationTotal`.  It is the
  `NormDenseRound.computeRound` analogue this note said did not exist, and
  `current_round_coefficients_shaped` fixes the sent message at `degree =
  quotientDegree + 2` entries.
* The Boolean-cube sum now exists.  `GateDenseRound.cubeSum` is the eq-weighted
  all-gates aggregate summed over the cube, and `endpoint_sum_is_cube_sum`
  proves a round's `f(0)+f(1)` IS that cube sum -- the `OuterClaimChain.endpointSum`
  analogue this note said was missing.
* The cross-round endpoint identity now exists and is NOT pinned at the last
  round.  `GateDenseRound.bound_endpoint_sum_is_round_value` /
  `bound_endpoint_sum_is_state_round_value` / `honest_chain_step` prove the NEXT
  tables' `f'(0)+f'(1)` is the CURRENT round value at the drawn challenge, for
  any state with at least two live variables.  (The `TableShape c 1` pinning
  remains only on the last-round `GateTerminalBinding` lemmas, where it belongs.)

STILL OPEN:

* The gate eq-table's derivation from `gateTau` at every row remains outside the
  adopted model: `GateDenseRound`'s own header states that "the eq table's
  provenance from `tau` (`ext3_eq_evals`) is likewise NOT modelled: `eq` is a
  supplied table".  A cube sum weighted by a SUPPLIED eq table can now be
  stated, but it carries no rejection power against a supplier who chooses that
  table, so it is still not the gate relation.
* Extraction is still not formalised, so any gate conclusion would rest on an
  assumed extracted-truth-chain in the same way the norm lane's does, plus the
  same open extraction join (this file's ASSUMPTION 17 for the norm lane).
* `IntegratedTerminalChain.GateChainHypotheses` still CARRIES its `grid` field
  as a hypothesis rather than deriving it; only the reason its docstring gives
  (that no gate prover with coefficient interpolation and `bind_challenge`
  chaining is adopted) has been overtaken by `GateDenseRound`.

CONSEQUENCE, STATED PLAINLY.  Nothing in this file proves that the gate lane's
aggregate sums to zero over the Boolean cube, and nothing in this file proves
that an accepted proof satisfies the circuit's GATE constraints.  Only the
norm/logUp lane conclusion (`accepted_norm_cube_sum_vanishes`) is established.
The gate lane survives below ONLY inside the counting bound, where its outer
rounds contribute agreement events to the `195` total; `gateCompare` and
`gateCompareRounds` remain free parameters there and carry no meaning. -/

/-! ## 10. The union bound -/

theorem sum_map_le (f g : Finset Element → ℚ) (h : ∀ S, f S ≤ g S) :
    ∀ l : List (Finset Element), (l.map f).sum ≤ (l.map g).sum
  | [] => le_refl 0
  | S :: l => by
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h S) (sum_map_le f g h l)

/-- The two lanes' per-round degree bounds, PROVED from the adopted
`Verifier.shape` guard (five log coefficients, `quotientDegree + 2` gate
coefficients), the adopted `NormDenseRound.current_round_coefficients_shaped`
(five honest log coefficients) and ASSUMPTION 18 for the gate lane's free
comparison messages, which carry no meaning. -/
theorem lane_degree_bounds (pin : Verifier.Pinned)
    (A : Assumptions e decode c p t tLast pr constants extra x logTruths gateCompareRounds
      gateCompare fixedness law failure)
    (hshape : Verifier.shape pin c p = true) :
    (∀ r ∈ logLaneOf e c p logTruths, r.message.length ≤ 5 ∧ r.truth.length ≤ 5) ∧
    (∀ r ∈ gateLaneOf e c p gateCompareRounds,
      r.message.length ≤ c.quotientDegree + 2 ∧ r.truth.length ≤ c.quotientDegree + 2) := by
  obtain ⟨-, -, hla, hga⟩ := shape_round_lengths pin c p hshape
  refine ⟨fun r hr => ⟨?_, ?_⟩, fun r hr => ⟨?_, ?_⟩⟩
  · exact le_of_eq (log_lane_message_lengths e c p logTruths hla r hr)
  · exact le_of_eq (honest_truth_lengths pr (logLaneOf e c p logTruths) t A.extractedTablesShape
      A.extractedTruthChain r hr)
  · exact le_of_eq (gate_lane_message_lengths e c p gateCompareRounds hga r hr)
  · exact A.gateCompareDegree r hr

/-- UNION BOUND (probability form).  Under ASSUMPTIONS 1, 2, 3 and 18 the free
rational `failure` is at most the SUM of the adopted per-round bounds, i.e. the
concrete arithmetic expression
`(5 * degreeBits + (quotientDegree + 2) * degreeBits) * (⌈2^256/p⌉ / 2^256)^3`.
Everything except ASSUMPTIONS 1-3 is the adopted counting over
`OuterChallenge`'s explicit finite space of 32-byte digest triples.

`failure` IS NOT "the real failure probability".  It is a free parameter that
ASSUMPTIONS 2 and 3 POSIT to upper-bound the real probability; this theorem
chains those two posits with the counting and asserts nothing about the deployed
transcript.  Nor is the resulting number the system's soundness error: it covers
only the OUTER sumcheck agreement events and excludes the dominant WHIR/Merkle
term -- see `conditional_soundness`. -/
theorem outer_failure_bound (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode c p t tLast pr constants extra x logTruths gateCompareRounds
      gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain c p = .ok ()) :
    failure ≤ ((5 * c.degreeBits + (c.quotientDegree + 2) * c.degreeBits : Nat) : ℚ) *
      ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  obtain ⟨-, -, -, -, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain c p hacc
  obtain ⟨-, -, -, -, hshape, -, -, -, -, -, -, -⟩ :=
    (IntegratedTerminalChain.verify_iff_solidity_order (Integrated.modelEngine e decode)
      pin chain c p).mp hv
  obtain ⟨hlogd, hgated⟩ := lane_degree_bounds pin A hshape
  obtain ⟨hlr, hgr, -, -⟩ := shape_round_lengths pin c p hshape
  obtain ⟨hlen1, -⟩ := lane_length_of_shape e c p (truths := logTruths) hlr hgr
  obtain ⟨-, hlen2'⟩ := lane_length_of_shape e c p (truths := gateCompareRounds) hlr hgr
  have huni := A.challengeUniform A.adaptiveFixedness
  have hb1 := (sum_map_le law OuterChallenge.uniformTupleProbability huni
    (badSets 0 (NormPolynomial.lift (OuterClaimChain.endpointSum t pr))
      (logLaneOf e c p logTruths))).trans
    (bad_sets_uniform_sum 5 _ _ (logLaneOf e c p logTruths) hlogd)
  have hb2 := (sum_map_le law OuterChallenge.uniformTupleProbability huni
    (badSets 0 gateCompare (gateLaneOf e c p gateCompareRounds))).trans
    (bad_sets_uniform_sum (c.quotientDegree + 2) _ _ (gateLaneOf e c p gateCompareRounds) hgated)
  rw [hlen1] at hb1
  rw [hlen2'] at hb2
  refine A.challengeIndependent.trans ((add_le_add hb1 hb2).trans (le_of_eq ?_))
  push_cast
  ring

/-- UNION BOUND (counting form, `B` out of `N`).  The same statement without any
probability: the number of 32-byte digest TRIPLES that make some outer round
fail, counted round by round on `OuterChallenge`'s explicit sample space, is at
most `B`, out of `N = (2^256)^3 = 2^768` triples in total.  This is a counting
statement about that ideal law, NOT about the real Keccak transcript. -/
theorem outer_failure_triple_count (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode c p t tLast pr constants extra x logTruths gateCompareRounds
      gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain c p = .ok ()) :
    (((badSets 0 (NormPolynomial.lift (OuterClaimChain.endpointSum t pr))
        (logLaneOf e c p logTruths)).map
        (fun S => (OuterChallenge.tupleEvent S).card)).sum) +
    (((badSets 0 gateCompare (gateLaneOf e c p gateCompareRounds)).map
        (fun S => (OuterChallenge.tupleEvent S).card)).sum) ≤
      (5 * c.degreeBits + (c.quotientDegree + 2) * c.degreeBits) *
        OuterChallenge.fiberCeiling ^ 3 := by
  obtain ⟨-, -, -, -, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain c p hacc
  obtain ⟨-, -, -, -, hshape, -, -, -, -, -, -, -⟩ :=
    (IntegratedTerminalChain.verify_iff_solidity_order (Integrated.modelEngine e decode)
      pin chain c p).mp hv
  obtain ⟨hlogd, hgated⟩ := lane_degree_bounds pin A hshape
  obtain ⟨hlr, hgr, -, -⟩ := shape_round_lengths pin c p hshape
  obtain ⟨hlen1, -⟩ := lane_length_of_shape e c p (truths := logTruths) hlr hgr
  obtain ⟨-, hlen2⟩ := lane_length_of_shape e c p (truths := gateCompareRounds) hlr hgr
  have hb1 := bad_sets_triple_card_sum 5 0
    (NormPolynomial.lift (OuterClaimChain.endpointSum t pr)) (logLaneOf e c p logTruths) hlogd
  have hb2 := bad_sets_triple_card_sum (c.quotientDegree + 2) 0 gateCompare
    (gateLaneOf e c p gateCompareRounds) hgated
  rw [hlen1] at hb1
  rw [hlen2] at hb2
  refine (Nat.add_le_add hb1 hb2).trans (le_of_eq ?_)
  ring

end Core

/-! ## 11. The single readable statement, and the concrete bound -/

/-- The adopted `Verifier.envelope` guard alone forces the concrete numeric
bound `B ≤ 195` on the number of outer bad points: `degreeBits ≤ 13` rounds per
lane, five log coefficients, `quotientDegree + 2 ≤ 10` gate coefficients. -/
theorem envelope_gives_concrete_bound (c : Verifier.Config) (h : Verifier.envelope c = true) :
    5 * c.degreeBits + (c.quotientDegree + 2) * c.degreeBits ≤ 195 := by
  obtain ⟨hdb, hqd⟩ := envelope_parameter_bounds c h
  have h2 : (c.quotientDegree + 2) * c.degreeBits ≤ 10 * 13 := Nat.mul_le_mul hqd hdb
  omega

/-- `N`: the explicit finite outer challenge space of `OuterChallenge` is the
set of triples of 32-byte digests, of size `2^768`. -/
theorem outer_challenge_space_size : Fintype.card OuterChallenge.DigestTriple = 2 ^ 768 := by
  rw [OuterChallenge.digest_tuple_cardinality, OuterChallenge.word_size_is_256_bits, ← pow_mul]

/-- The per-coordinate mass factor written out: `⌈2^256/p⌉ / 2^256`, the exact
modulo-reduction bias of the adopted `OuterChallenge` reduction. -/
theorem outer_ratio_explicit :
    ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 =
      ((((2 ^ 256 + Arithmetic.modulus - 1) / Arithmetic.modulus : Nat) : ℚ) / (2 : ℚ) ^ 256) ^ 3 := by
  simp only [OuterChallenge.fiberCeiling, WhirChallenge.ceilingQuotient,
    OuterChallenge.word_size_is_256_bits, Nat.cast_pow, Nat.cast_ofNat]

/-- UNUSED BY THE CAPSTONE: an arithmetic sanity check on where `195` comes
from, at the envelope's extremal `degreeBits = 13`, `quotientDegree = 8`. -/
theorem worst_case_outer_bound_value : 5 * 13 + (8 + 2) * 13 = 195 := by norm_num

section Final
open NormDenseRound NormTerminalBinding
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates}
  {c : Verifier.Config} {p : Verifier.Proof} {t tLast : Tables} {pr : Prepared}
  {constants extra : List Verifier.Ext3} {x : Element}
  {logTruths gateCompareRounds : List (List Element)} {gateCompare : Element} {fixedness : Prop}
  {law : Finset Element → ℚ} {failure : ℚ}

/-- CAPSTONE.  Under `Assumptions` (eighteen named fields, all visible), an
accepted `Integrated.verify` proof satisfies the NORM/logUp relation the verifier
checks -- the extracted tables' aggregate sums to zero over the Boolean cube --
unless the log lane hit one of the outer round-agreement bad events, whose total
size is at most `B = 195 * ⌈2^256/p⌉^3` digest triples out of `N = 2^768`.

THE GATE LANE APPEARS ONLY IN THE COUNTING CONJUNCT.  An earlier draft also concluded that the
gate lane's aggregate sums to zero; that conjunct was DEGENERATE and has been
deleted.  See the `gate lane is not proved` note in section 9 for exactly why,
and for the four adopted-module gaps that block a repair.  Nothing here says an
accepted proof satisfies the circuit's GATE constraints.

HOW TO READ `195 * (⌈2^256/p⌉ / 2^256)^3` -- THIS IS NOT THE SYSTEM'S SOUNDNESS
ERROR.  The number is approximately `2^-184`, and it covers ONLY the outer
sumcheck round-agreement events of the two lanes, counted under the IDEAL
uniform law of `OuterChallenge`.  It EXCLUDES the entire WHIR/Merkle
contribution -- proximity/list-decoding, the query-repetition profile, and
Merkle collision resistance -- which is the DOMINANT term: the deployed design
point is around 100 bits, not 184.  Quoting `2^-184` as the wire-v3 soundness
error would be off by roughly eighty bits and is a misuse of this theorem.  The
WHIR-side bad events have their own adopted counting bounds in section 6
(`whir_quadratic_bad_card`, `whir_rlc_bad_card`,
`whir_domain_agreement_impossible`); none of them is aggregated into `B`, and no
assumption in this file excludes them either.

`failure` is a FREE RATIONAL.  It is not a probability computed from anything.
Assumptions 2-3 bound it ABOVE only; nothing bounds it below by a real quantity,
so identifying it with the real failure probability needs an external bridge no
field supplies.  The first and last conjuncts are never composed: there is no
probability space over executions here.  The last conjunct is
therefore a statement about whatever `failure` those assumptions are instantiated
with. -/
theorem conditional_soundness (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode c p t tLast pr constants extra x logTruths gateCompareRounds
      gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain c p = .ok ()) :
    (BadEventFree 0 (NormPolynomial.lift (OuterClaimChain.endpointSum t pr))
        (logLaneOf e c p logTruths) →
        OuterClaimChain.endpointSum t pr = Verifier.zero) ∧
    (((badSets 0 (NormPolynomial.lift (OuterClaimChain.endpointSum t pr))
        (logLaneOf e c p logTruths)).map
        (fun S => (OuterChallenge.tupleEvent S).card)).sum) +
      (((badSets 0 gateCompare (gateLaneOf e c p gateCompareRounds)).map
        (fun S => (OuterChallenge.tupleEvent S).card)).sum) ≤
        195 * OuterChallenge.fiberCeiling ^ 3 ∧
    Fintype.card OuterChallenge.DigestTriple = 2 ^ 768 ∧
    failure ≤ (195 : ℚ) *
      ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  obtain ⟨-, -, -, -, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain c p hacc
  obtain ⟨-, -, henv, -, -, -, -, -, -, -, -, -⟩ :=
    (IntegratedTerminalChain.verify_iff_solidity_order (Integrated.modelEngine e decode)
      pin chain c p).mp hv
  have hB := envelope_gives_concrete_bound c henv
  refine ⟨fun h1 => accepted_norm_cube_sum_vanishes pin chain A hacc h1, ?_,
    outer_challenge_space_size, ?_⟩
  · exact (outer_failure_triple_count pin chain A hacc).trans
      (Nat.mul_le_mul_right _ hB)
  · refine (outer_failure_bound pin chain A hacc).trans ?_
    have hpos : (0 : ℚ) ≤ ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
      positivity
    have hcast : ((5 * c.degreeBits + (c.quotientDegree + 2) * c.degreeBits : Nat) : ℚ) ≤ 195 := by
      exact_mod_cast hB
    exact mul_le_mul_of_nonneg_right hcast hpos

/-- (6) The OUTER bound in the two `Verifier.Config` parameters that carry it.
The audit's Lean modules expose no deployed `WhirParameters.Params` (only test
fixtures), so it is stated symbolically, with the numeric ceiling that the
adopted `Verifier.envelope` guard already forces.

THIS IS NOT "THE BOUND AT THE DEPLOYED PROFILE"; an earlier draft's docstring
called it that, which was misleading.  It bounds `failure`, a free rational, and
it covers ONLY the outer sumcheck agreement events.  The WHIR/Merkle
contribution -- the dominant one, and the one the deployed ~100-bit design point
is actually set by -- does not appear in this expression at all. -/
theorem profile_bound (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode c p t tLast pr constants extra x logTruths gateCompareRounds
      gateCompare fixedness law failure)
    (hacc : Integrated.verify e decode pin chain c p = .ok ()) :
    failure ≤ ((5 * c.degreeBits + (c.quotientDegree + 2) * c.degreeBits : Nat) : ℚ) *
        ((((2 ^ 256 + Arithmetic.modulus - 1) / Arithmetic.modulus : Nat) : ℚ) / (2 : ℚ) ^ 256) ^ 3 ∧
      5 * c.degreeBits + (c.quotientDegree + 2) * c.degreeBits ≤ 195 := by
  obtain ⟨-, -, -, -, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain c p hacc
  obtain ⟨-, -, henv, -, -, -, -, -, -, -, -, -⟩ :=
    (IntegratedTerminalChain.verify_iff_solidity_order (Integrated.modelEngine e decode)
      pin chain c p).mp hv
  refine ⟨?_, envelope_gives_concrete_bound c henv⟩
  rw [← outer_ratio_explicit]
  exact outer_failure_bound pin chain A hacc

end Final

/-! ## 12. Partial non-vacuity checks

WHAT THIS SECTION IS, AND WHAT IT IS NOT.  A statement conditioned on an
unsatisfiable hypothesis proves nothing, so it is worth exhibiting inhabitants
of the individual hypotheses.  The three lemmas below do that for THREE
INDIVIDUAL hypotheses, separately.

THEY DO NOT ESTABLISH THAT `Assumptions` IS INHABITED.  No inhabitation of the
eighteen-field conjunction is constructed anywhere in this file, and none is
claimed.  An earlier draft's section header asserted that "each hypothesis that
could plausibly be contradictory is shown to be satisfiable"; that was FALSE and
has been removed.  Whether the eighteen fields are JOINTLY satisfiable for a
given engine, config and proof is open here, so `conditional_soundness` could in
principle be vacuous for some instantiations.  Constructing a witness would mean
exhibiting a concrete accepting execution together with extracted tables meeting
ASSUMPTIONS 4-17 simultaneously, which is the extraction problem this file
assumes away. -/

/-- The "no bad event" hypothesis is SATISFIABLE.  What is proved is the DIAGONAL
case: when the running claim and the comparison value are the SAME element `a`
and every round's sent message equals its comparison message, every `roundBadSet`
is empty by the `a = b` branch, so `BadEventFree a a rs` holds.

DO NOT OVERREAD THIS.  It does NOT say `BadEventFree` is "satisfied exactly by
the honest prover" (an earlier draft's docstring did, wrongly).  It says nothing
about the OFF-diagonal case `BadEventFree 0 b rs` with `b ≠ 0` that
`accepted_norm_cube_sum_vanishes` is actually applied at, and it is not a
characterisation in either direction: `BadEventFree` also holds in many
dishonest cases, namely whenever the drawn challenges happen to miss the
agreement sets. -/
theorem honest_prover_has_no_bad_events : ∀ (a : Element) (rs : List LaneRound),
    (∀ r ∈ rs, r.message = r.truth) → BadEventFree a a rs
  | _, [], _ => trivial
  | a, r :: rs, h => by
      have hmsg : r.message = r.truth := h r (List.mem_cons_self _ _)
      refine ⟨?_, ?_⟩
      · simp only [RoundAgreement, roundBadSet, if_pos rfl, if_true, Finset.not_mem_empty,
          not_false_iff]
      · rw [hmsg]
        exact honest_prover_has_no_bad_events _ rs (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- NOT AN ASSUMPTION OF THIS FILE ANY MORE.  `NoCollisionAmong` is the shape a
hash-collision-resistance assumption would have to take here -- a statement about
the FINITE list of byte strings an execution actually hashes, unlike the globally
false `¬ MerkleCollision hash`, which pigeonhole refutes for every
`List UInt8 → Digest` and which would make everything vacuous.  It is retained
only to document that distinction and to give `MerkleCollision`'s honesty remark
something to point at.  `Assumptions` no longer has a collision-freedom field:
nothing in the soundness chain consumed one.  This lemma is USED BY NOTHING. -/
theorem no_collision_among_nil (hash : Spongefish.Hash) : NoCollisionAmong hash [] := by
  intro a ha
  simp at ha

/-- ASSUMPTIONS 2 and 3 are SATISFIABLE: the identically zero law is dominated by
the explicit uniform law (`OuterChallenge.uniform_probability_between_zero_and_one`)
and makes the union bound hold with `failure = 0`.  Note what this shows and what
it does not: it shows the two fields are not contradictory WITH EACH OTHER, at a
degenerate instantiation that makes the bound trivially true.  It does not show
they hold for any real transcript. -/
theorem zero_law_satisfies_challenge_uniform (S : Finset Element) :
    (0 : ℚ) ≤ OuterChallenge.uniformTupleProbability S :=
  (OuterChallenge.uniform_probability_between_zero_and_one S).1

theorem zero_law_sum_is_zero : ∀ l : List (Finset Element),
    (l.map (fun _ : Finset Element => (0 : ℚ))).sum = 0
  | [] => rfl
  | _ :: l => by simp [zero_law_sum_is_zero l]

end Audit.Wire3.ConditionalSoundness
