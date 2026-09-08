import Audit.Wire3.GateDenseRound
import Audit.Wire3.ConditionalSoundness

/-!
# The GATE lane's claim chain, terminal bridge and conditional soundness

This module closes, for the GATE lane, the four gaps the review listed between
the adopted `Audit.Wire3.GateDenseRound` (one honest round, end to end) and gate
soundness.  It is the gate counterpart of `Audit.Wire3.OuterClaimChain` (norm
lane multi-round chain) and of `Audit.Wire3.ConditionalSoundness`'s
`accepted_norm_cube_sum_vanishes` (norm lane soundness direction).

Sources reviewed:
* mle/src/verifier_v2.rs 277-301: `gate_final_claim` starts at
  `Field64_3::ZERO`; each round commits BOTH `non_constant` vectors, then
  `evaluate_ext3_coefficient_round` folds the running gate claim and the drawn
  gate challenge is pushed onto `gate_point`;
* mle/src/verifier_v2.rs 422-434: the gate terminal
  `eq(gate_tau, gate_point) * gate_aggregate(witness, preprocessed, pi_hash,
  gate_alpha)` compared against the folded gate claim;
* mle/contracts/src/OuterLogupExt3Verifier.sol 254-322
  (`_verifyCoupledSumchecksUnchecked`): `gateClaim = zero()`, ordered rounds,
  `gatePoint[roundIndex] = roundChallenges.gate`;
* mle/contracts/src/OuterLogupExt3Verifier.sol 211-228: the gate terminal
  comparison;
* mle/src/sumcheck/gate_ext3_v2.rs (read in full, 181 lines): `current_round`
  105-140, `bind_challenge` 142-161, `into_proof_and_point` 163-171.

ADOPTED MODELS REUSED UNCHANGED.  `Verifier.RoundState` / `start` / `roundStep` /
`runRounds` / `derivedRounds` / `gateTerminal` (Verifier.lean 150-182, 386-399);
`GateDenseRound.computeRound` / `stateRound` / `currentRound` / `Consistent` /
`stateRoundElement` / `cubeSum` / `current_round_shaped` /
`sent_round_evaluates_as_verifier` / `bind_challenge_consistent` /
`bound_endpoint_sum_is_state_round_value` / `endpoint_sum_is_cube_sum` /
`current_round_value_sum` / `proof_extraction_exact`;
`GateTerminalBinding.ProverState` / `ProverShape` / `bindChallenge` /
`bindTables` / `Cells` / `CellsMatchClaims` / `boundTerminal` /
`round_value_last_round` / `bound_terminal_is_engine_gate_terminal` /
`intoProofAndPoint`; `OuterRound.evaluate` / `polynomial` /
`actual_evaluate_round_exact`; and, ENTIRELY UNCHANGED and not duplicated,
`ConditionalSoundness.LaneRound` / `lane` / `gateLaneOf` / `claimedRun` /
`truthRun` / `roundBadSet` / `RoundAgreement` / `BadEventFree` / `badSets` /
`chain_initial_agreement` / `derived_gate_claim` / `lanes_nonempty` /
`lane_truths`.  NO second bad-event machinery is introduced.

WHICH OF `ConditionalSoundness`'S COUNTING RESULTS APPLY HERE.  Only the GENERIC
section-4 lemmas -- `round_bad_uniform`, `bad_sets_uniform_sum`,
`bad_sets_union_card` -- apply verbatim: each is universally quantified over an
arbitrary starting claim, an arbitrary lane and an arbitrary degree bound.  The
section-10 results (`outer_failure_bound`, `outer_failure_triple_count`,
`conditional_soundness`, and the `195` appearing in them) DO NOT apply to this
lane: they are stated over `badSets 0 gateCompare (gateLaneOf … gateCompareRounds)`
-- a DIFFERENT starting claim and a DIFFERENT (free, meaningless) truths list --
and their gate half rests on that module's ASSUMPTION 18.  The instantiation for
THIS lane is therefore PERFORMED HERE, in `gate_lane_degree_bounds`,
`gate_lane_bad_set_card_bound` and `gate_lane_bad_set_uniform_bound`, and its
truth-length side condition is PROVED (`assumptions_force_message_lengths`, the
executed `current_round` lengths) rather than assumed.  The resulting GATE-LANE
bound is `(quotientDegree + 2) * degreeBits` bad challenge points, i.e. mass at
most `(quotientDegree + 2) * degreeBits * (⌈2^256/p⌉ / 2^256)^3` under
`OuterChallenge`'s explicit ideal uniform 32-byte-triple law.

No new evaluator, decoder, transcript, interpolation or eq-table model is added,
and nothing is re-proved.

## What is proved

(a) THE MULTI-ROUND INDUCTION, honest prover only.  `honestStep` / `honestRun`
drive the adopted gate prover with the verifier's OWN gate challenge
(`gateChallenge`, the `.gate` field of the actual coupled `commit`) through the
ACTUAL `Verifier.roundStep`.  `honest_step_exact`, `honest_run_exact`,
`honest_gate_chain_step` and `honest_gate_chain` prove that after `i` rounds the
verifier's gate claim IS `stateRoundElement` of the tables after `i` binds at the
verifier's own challenge, and that the final claim is the last round's value.
`honest_extraction_matches_verifier` and `honest_run_is_derived_rounds` prove
`into_proof_and_point` returns exactly the messages fed to `Verifier.runRounds`
and the verifier's `gatePoint`, so the run IS `Verifier.derivedRounds`.
`chain_initial_claim` states the source's ZERO initial gate claim to be in
lockstep with the honest prover IFF the Boolean-cube gate sum is zero -- stated
CONDITIONALLY; zero-ness is never assumed and never asserted.

(b) THE GATE TERMINAL BRIDGE.  `accepted_last_round_value_is_gate_claim` and
`accepted_last_state_value_is_gate_claim`: for an ACCEPTED proof the last gate
round's value at the last challenge IS `Verifier.gateTerminal`'s value, i.e. the
derived `gateClaim`, through the adopted
`GateTerminalBinding.bound_terminal_is_engine_gate_terminal`.  Gate rows, the
public-hash length and configuration validity are DERIVED from acceptance
(`accepted_gate_configuration_valid`), not assumed.

(c) THE SOUNDNESS DIRECTION, the point of the exercise.
`accepted_gate_cube_sum_vanishes`: if `Integrated.verify` ACCEPTS, the eight
named `Assumptions` hold, and NO drawn GATE challenge landed in its round's
agreement set, then A WEIGHTED SUM OVER THE SUPPLIED TABLES VANISHES -- the
extracted gate tables' all-gates aggregate, weighted row by row by the SUPPLIED
eq table, sums to zero over the Boolean cube.  That is NOT the relation the
verifier is checking; see `THE GATE RELATION IS NOT REACHED` and `NO REJECTION
POWER` below.  Every hypothesis is a named visible field with a docstring saying
what it assumes and what would discharge it.

THE EARLIER DEFECT CANNOT RECUR.  `ConditionalSoundness` deleted a gate theorem
whose truths and cube sum were free parameters, so `gateTruths := []` satisfied
it for any accepting proof.  Here the conclusion's cube sum is `cubeSum` of the
state named in assumption 3, and assumption 3 (`TruthChain`) forces every round's
truth to be the executed `stateRound` of a state reached from that state by the
source's own `bindChallenge`.  `truth_chain_lengths` proves every truth has
`quotientDegree + 2` entries and `empty_gate_truths_not_honest` proves the
`gateTruths := []` instantiation is UNSATISFIABLE for any proof passing the
adopted `Verifier.shape` / `Verifier.envelope` guards.

(d) A concrete non-vacuous example on the adopted `GateDenseRound.exampleState`.

## What is NOT proved

* THE GATE RELATION IS NOT REACHED.  `cubeSum = 0` is a statement about the
  EXTRACTED tables weighted by the SUPPLIED eq table.  It does NOT say the
  circuit's gate constraints hold at every row.  Two further steps are needed and
  neither is here: the eq table's provenance from `gateTau` at EVERY row (this
  module's assumption 8 pins only the FULLY BOUND cell, and the adopted
  `EqTableProvenance` covers exactly that cell), and the semantic bridge from
  `GatesComplete.evalCombined` to the gate relation.  The semantic step is a
  separate module and is deliberately not attempted here.
* NO REJECTION POWER AGAINST AN ADVERSARIAL SUPPLIER OF THE STATE.  This is the
  sharp form of the previous bullet and it must be read before any use is made
  of `accepted_gate_cube_sum_vanishes`.  Assumption 8 pins exactly ONE linear
  functional of the eq table: the value of the FULLY BOUND cell.  The weight the
  conclusion sums, the row sum `Σ_rows eq[row]`, is an INDEPENDENT linear
  functional of that same table as soon as `numVars ≥ 1`.  So a supplier free to
  choose `s0` may present an eq table whose bound cell is exactly the required
  `eq(gateTau, gatePoint)` and whose row sum is ZERO; `cubeSum = 0` then holds
  for ANY gate aggregate whatsoever, including one produced by a false witness.
  AS IT STANDS THIS THEOREM THEREFORE REJECTS NOTHING.  It is a statement about
  a supplied state, not a soundness guarantee about the deployed verifier.  Only
  eq-table provenance at EVERY row -- not merely at the bound cell -- would give
  it rejection power, and that provenance is not in this module and not in the
  adopted `EqTableProvenance`.
* THE CONSTRAINT-FREE CONFIGURATION IS A REAL DEGENERACY, EXCLUDED BY HAND.
  `numGateConstraints = 0` passes the adopted `Verifier.envelope` and
  `Gates.envelope` (both only bound it ABOVE, by 123), and the adopted
  `Integrated.exampleConfig` actually sets `numGateConstraints := 0`, so this is
  not hypothetical.  On such a configuration `Gates.validateConfiguration`
  forces every decoded gate to declare zero constraints, every
  `GatesComplete.contribution` is `zero`, and `cubeSum = 0` holds FOR ANY TABLES:
  `constraint_free_cube_sum_vanishes` proves this.  `Assumptions`' field 4
  (`gateConstraintsPositive`, `0 < vc.numGateConstraints`) excludes that regime;
  it is NOT derivable from acceptance, because the deployed guards do not
  require it.
* THE EXTRACTION JOIN IS OPEN, exactly as on the norm side.  Assumption 6
  (`cellsMatchClaims`) POSTULATES that the proof's claimed gate witness and
  constants are the fully bound cells of the extracted tables.  Nothing here
  connects the values the WHIR/Merkle check bound to those cells; an adversary
  who can open the commitment elsewhere is excluded by fiat, not by argument.
* NO PROBABILITY IS COMPUTED.  `BadEventFree` is a hypothesis about the
  challenges the run actually drew.  This module adds NO probability space and
  no Fiat-Shamir/random-oracle argument.  It does instantiate
  `ConditionalSoundness`'s GENERIC section-4 counting lemmas at THIS lane's
  starting claim and truths (`gate_lane_bad_set_card_bound`,
  `gate_lane_bad_set_uniform_bound`), giving `(quotientDegree + 2) * degreeBits`
  bad points under an IDEAL uniform 32-byte-triple law -- a counting statement
  about that law, NOT about the real Keccak transcript, and one that excludes
  the dominant WHIR/Merkle contribution entirely.  That number is NOT
  `ConditionalSoundness`'s `195`, which is a two-lane total for a DIFFERENT
  gate-lane starting claim (`gateCompare`) and a DIFFERENT truths list
  (`gateCompareRounds`).  Neither bound is ever composed with the `BadEventFree`
  hypothesis: no probabilistic soundness statement is made anywhere here.
* `Assumptions` is NOT shown to be inhabited.  Assumption 3 is shown to be
  non-degenerate and two of the eight are shown DISCHARGEABLE in principle from
  adopted provenance modules, but the eight-field conjunction is not exhibited,
  so the theorem could be vacuous for some instantiations.  No accepting
  `Integrated.verify` instance is constructed anywhere.  `example_truth_chain`
  builds a HAND-MADE lane `[⟨m1,m1,2⟩, ⟨m2,m2,3⟩]`, not a `gateLaneOf` lane of
  any execution, so it inhabits `TruthChain` -- it does NOT inhabit assumption 3,
  which is `TruthChain` over a real `gateLaneOf e vc p gateTruths`.
* `TruthChain` records the round TRUTHS in the extracted states' own `rounds`
  field, so `sLast.rounds` is not tied to `p.gateRounds`.  Harmless -- only the
  tables enter the conclusion -- but it is not a claim about the proof's rounds.
* The CONVERSE (every proof of a true gate statement is accepted) is not proved.
* Rust/EVM refinement, gas, exception ordering, `ext3_eq_evals`, the
  base-to-Ext3 transposition and the WHIR profile constants remain outside.
-/

namespace Audit.Wire3.GateClaimChain
open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.GateDenseRound Audit.Wire3.GateTerminalBinding

/-! ## 1. The gate endpoint sum of a prover state -/

def endpointSum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) : Element :=
  stateRoundElement c gates publicHash alpha 0 s + stateRoundElement c gates publicHash alpha 1 s

theorem state_endpoint_sum_is_cube_sum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) (hn : ¬isComplete s) :
    endpointSum c gates publicHash alpha s =
      cubeSum c gates publicHash alpha s.tables (2 ^ s.eq.numVars) := by
  obtain ⟨m, hm⟩ : ∃ m, s.eq.numVars = m + 1 := ⟨s.eq.numVars - 1, by unfold isComplete at hn; omega⟩
  have h : 2 * 2 ^ (s.eq.numVars - 1) = 2 ^ s.eq.numVars := by
    rw [hm, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
  unfold endpointSum stateRoundElement
  rw [GateDenseRound.endpoint_sum_is_cube_sum, h]

/-- The verifier's own `OuterRound.evaluate` on the honest gate message, with the
state's endpoint sum as the running claim, is the state's round value at the
challenge.  HONEST PROVER ONLY. -/
theorem round_evaluate_bridge (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState)
    (message : List Element) (r : Element)
    (hv : Gates.validateConfiguration c gates = some ()) (hc : Consistent c s) (hn : ¬isComplete s)
    (hm : stateRound c gates publicHash alpha s = some message) :
    OuterRound.evaluate (endpointSum c gates publicHash alpha s) message r =
      stateRoundElement c gates publicHash alpha r s := by
  obtain ⟨message', hcr, _, hev⟩ := current_round_shaped c gates publicHash alpha s hv hc hn
  have hmm : message' = message.map Element.toVerifier := by
    have h := hcr
    unfold currentRound at h
    rw [hm, Option.map_some'] at h
    exact (Option.some.inj h).symm
  apply GoldilocksExt3Field.element_eq
  rw [OuterRound.actual_evaluate_round_exact, endpointSum, ← GateDenseRound.add_lift, ← hmm]
  exact hev r

/-- The honest gate message has exactly `quotientDegree + 2` coefficients, the
count `Verifier.shape` forces on the proof's own gate rounds. -/
theorem honest_message_length (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) (message : List Element)
    (hv : Gates.validateConfiguration c gates = some ()) (hc : Consistent c s) (hn : ¬isComplete s)
    (hm : stateRound c gates publicHash alpha s = some message) :
    message.length = c.quotientDegree + 2 := by
  obtain ⟨message', hcr, hlen, _⟩ := current_round_shaped c gates publicHash alpha s hv hc hn
  have hmm : message' = message.map Element.toVerifier := by
    have h := hcr
    unfold currentRound at h
    rw [hm, Option.map_some'] at h
    exact (Option.some.inj h).symm
  rw [hmm, List.length_map] at hlen
  rw [hlen, hc.2.1]

/-! ## 2. (a) The multi-round induction against the verifier's own gate challenges -/

/-- The honest prover's own message exists and has the length `bind_challenge`
re-checks; `currentRound` is that list retyped. -/
theorem state_round_exists (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState)
    (hv : Gates.validateConfiguration c gates = some ()) (hc : Consistent c s) (hn : ¬isComplete s) :
    ∃ message : List Element, stateRound c gates publicHash alpha s = some message ∧
      message.length = c.quotientDegree + 2 ∧
      currentRound c gates publicHash alpha s = some (message.map Element.toVerifier) := by
  obtain ⟨message', hcr, hlen, _⟩ := current_round_shaped c gates publicHash alpha s hv hc hn
  have h := hcr
  unfold currentRound at h
  cases hs : stateRound c gates publicHash alpha s with
  | none => rw [hs, Option.map_none'] at h; exact Option.noConfusion h
  | some message =>
      rw [hs, Option.map_some', Option.some.injEq] at h
      subst h
      rw [List.length_map, hc.2.1] at hlen
      exact ⟨message, rfl, hlen, hcr⟩

/-- verifier_v2.rs:283-287 / OuterLogupExt3Verifier.sol:283-291: the GATE
challenge of this round, as the field element the gate prover binds.  Both
messages are arguments; the log message is supplied externally (this module
models the gate prover, not the log prover). -/
def gateChallenge (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (logMessage : List Verifier.Ext3) (message : List Element) : Element :=
  NormPolynomial.lift
    (commit v.transcript v.roundIndex logMessage (message.map Element.toVerifier)).gate

/-- The coupled message the verifier receives: the externally supplied log
message, and the gate prover's `Ext3CoefficientRound.non_constant`. -/
def coupled (logMessage : List Verifier.Ext3) (message : List Element) : Verifier.CoupledMessage :=
  (logMessage, message.map Element.toVerifier)

theorem gate_challenge_exact (commit : Verifier.CommitRound) (v : Verifier.RoundState)
    (logMessage : List Verifier.Ext3) (message : List Element) :
    (gateChallenge commit v logMessage message).toVerifier =
      (commit v.transcript v.roundIndex (coupled logMessage message).1
        (coupled logMessage message).2).gate := rfl

/-- One lockstep round of the honest gate prover against the ACTUAL verifier
step: `current_round`, the verifier's coupled commit and `Verifier.roundStep`,
then `bind_challenge` with the verifier's OWN gate challenge.  Any prover
failure propagates as `none`; nothing is defaulted. -/
def honestStep (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound)
    (logMessage : List Verifier.Ext3) (v : Verifier.RoundState) (s : ProverState) :
    Option (Verifier.RoundState × ProverState) := do
  let message ← stateRound c gates publicHash alpha s
  let t ← bindChallenge s (message.map Element.toVerifier)
    (gateChallenge commit v logMessage message)
  pure (Verifier.roundStep commit v (coupled logMessage message), t)

/-- The lockstep loop over the externally supplied log messages, one per round
(verifier_v2.rs:281-301 iterates `0..degree_bits`). -/
def honestRun (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound) :
    Verifier.RoundState → ProverState → List (List Verifier.Ext3) →
      Option (Verifier.RoundState × ProverState)
  | v, s, [] => some (v, s)
  | v, s, l :: ls => (honestStep c gates publicHash alpha commit l v s).bind
      (fun q => honestRun c gates publicHash alpha commit q.1 q.2 ls)

theorem honest_run_append (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound)
    (a b : List (List Verifier.Ext3)) :
    ∀ (v : Verifier.RoundState) (s : ProverState) (v' : Verifier.RoundState) (s' : ProverState),
      honestRun c gates publicHash alpha commit v s a = some (v', s') →
      honestRun c gates publicHash alpha commit v s (a ++ b) =
        honestRun c gates publicHash alpha commit v' s' b := by
  induction a with
  | nil =>
      intro v s v' s' h
      simp only [honestRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | cons l a ih =>
      intro v s v' s' h
      simp only [List.cons_append, honestRun] at h ⊢
      cases hs : honestStep c gates publicHash alpha commit l v s with
      | none => rw [hs] at h; exact Option.noConfusion h
      | some q => rw [hs] at h; exact ih _ _ _ _ h

/-- The lockstep invariant: the gate prover state is consistent, and while
rounds remain the verifier's running GATE claim is the honest endpoint sum
`f(0)+f(1)` of the prover's current round. -/
structure Lockstep (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (v : Verifier.RoundState) (s : ProverState) : Prop where
  consistent : Consistent c s
  claim : ¬isComplete s → v.gateClaim = (endpointSum c gates publicHash alpha s).toVerifier

/-- (a) ONE honest gate lockstep step, HONEST PROVER ONLY.  The verifier's new
gate claim is `stateRoundElement s r` for the prover's CURRENT tables and the
verifier's OWN gate challenge `r`; the prover binds exactly that challenge; and
if a further round remains the invariant is re-established by the adopted
`GateDenseRound.bound_endpoint_sum_is_state_round_value`. -/
theorem honest_step_exact (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound)
    (logMessage : List Verifier.Ext3) (v : Verifier.RoundState) (s : ProverState)
    (hv : Gates.validateConfiguration c gates = some ())
    (hl : Lockstep c gates publicHash alpha v s) (hn : ¬isComplete s) :
    ∃ (message : List Element) (t : ProverState),
      stateRound c gates publicHash alpha s = some message ∧
      message.length = c.quotientDegree + 2 ∧
      honestStep c gates publicHash alpha commit logMessage v s =
        some (Verifier.roundStep commit v (coupled logMessage message), t) ∧
      Consistent c t ∧ t.eq.numVars + 1 = s.eq.numVars ∧
      t.rounds = s.rounds ++ [message.map Element.toVerifier] ∧
      t.point = s.point ++ [gateChallenge commit v logMessage message] ∧
      t.tables = bindTables s.tables (gateChallenge commit v logMessage message) ∧
      (Verifier.roundStep commit v (coupled logMessage message)).gateClaim =
        (stateRoundElement c gates publicHash alpha
          (gateChallenge commit v logMessage message) s).toVerifier ∧
      Lockstep c gates publicHash alpha
        (Verifier.roundStep commit v (coupled logMessage message)) t := by
  obtain ⟨message, hsr, hlen, hcr⟩ := state_round_exists c gates publicHash alpha s hv hl.consistent hn
  obtain ⟨message', hcr', -, hev⟩ := current_round_shaped c gates publicHash alpha s hv hl.consistent hn
  have hmm : message' = message.map Element.toVerifier := Option.some.inj (hcr'.symm.trans hcr)
  subst hmm
  have hrlen : (message.map Element.toVerifier).length = s.degree := by
    rw [List.length_map, hlen, hl.consistent.2.1]
  obtain ⟨t, hb, hcons, hnum, _, hrounds, hpoint, htab⟩ :=
    bind_challenge_consistent c s (message.map Element.toVerifier)
      (gateChallenge commit v logMessage message) hl.consistent hn hrlen
  have hstep : honestStep c gates publicHash alpha commit logMessage v s =
      some (Verifier.roundStep commit v (coupled logMessage message), t) := by
    simp only [honestStep, hsr, hb, Option.bind_eq_bind, Option.some_bind, Option.pure_def]
  have hclaim : (Verifier.roundStep commit v (coupled logMessage message)).gateClaim =
      (stateRoundElement c gates publicHash alpha
        (gateChallenge commit v logMessage message) s).toVerifier := by
    show Verifier.evaluateRound v.gateClaim (message.map Element.toVerifier)
      (commit v.transcript v.roundIndex logMessage (message.map Element.toVerifier)).gate = _
    rw [hl.claim hn, endpointSum, ← GateDenseRound.add_lift]
    exact hev (gateChallenge commit v logMessage message)
  refine ⟨message, t, hsr, hlen, hstep, hcons, hnum, hrounds, hpoint, htab, hclaim, hcons, ?_⟩
  intro hn'
  have h2 : 2 ≤ s.eq.numVars := by unfold isComplete at hn'; omega
  rw [hclaim, endpointSum]
  exact congrArg Element.toVerifier
    (GateDenseRound.bound_endpoint_sum_is_state_round_value c gates publicHash alpha s t
      (message.map Element.toVerifier) (gateChallenge commit v logMessage message)
      hl.consistent h2 hb).symm

/-- (a) The WHOLE honest gate lockstep run: it succeeds, the prover's completed
rounds and point grow by exactly the sent messages and the verifier's own gate
challenges, and the verifier state is literally `Verifier.runRounds` on the
coupled messages from the same start state.  HONEST PROVER ONLY. -/
theorem honest_run_exact (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound)
    (hv : Gates.validateConfiguration c gates = some ()) (logs : List (List Verifier.Ext3)) :
    ∀ (v : Verifier.RoundState) (s : ProverState), Lockstep c gates publicHash alpha v s →
      logs.length ≤ s.eq.numVars →
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element))
      (chals : List Element),
      honestRun c gates publicHash alpha commit v s logs = some (v', s') ∧
      Consistent c s' ∧
      s'.rounds = s.rounds ++ sent.map (List.map Element.toVerifier) ∧
      s'.point = s.point ++ chals ∧
      sent.length = logs.length ∧ chals.length = logs.length ∧
      (∀ m ∈ sent, m.length = c.quotientDegree + 2) ∧
      s'.eq.numVars + logs.length = s.eq.numVars ∧
      v' = Verifier.runRounds commit v (logs.zip (sent.map (List.map Element.toVerifier))) ∧
      v'.gatePoint = v.gatePoint ++ chals.map Element.toVerifier ∧
      Lockstep c gates publicHash alpha v' s' := by
  induction logs with
  | nil =>
      intro v s hl _
      exact ⟨v, s, [], [], rfl, hl.consistent, by simp, by simp, rfl, rfl, by simp, by simp, rfl,
        by simp, hl⟩
  | cons l logs ih =>
      intro v s hl hlen
      simp only [List.length_cons] at hlen
      have hn : ¬isComplete s := by unfold isComplete; omega
      obtain ⟨message, s₁, -, hm5, hstep, -, hnum₁, hrounds₁, hpoint₁, -, -, hl₁⟩ :=
        honest_step_exact c gates publicHash alpha commit l v s hv hl hn
      obtain ⟨v', s', sent, chals, hrun, hcons, hrounds, hpoint, hsl, hcl, h5, hrem, hvv, hgp,
        hlock⟩ := ih _ s₁ hl₁ (by omega)
      refine ⟨v', s', message :: sent, gateChallenge commit v l message :: chals, ?_, hcons, ?_, ?_,
        by simp [hsl], by simp [hcl], ?_, ?_, ?_, ?_, hlock⟩
      · simp only [honestRun, hstep, Option.bind_eq_bind, Option.some_bind]
        exact hrun
      · rw [hrounds, hrounds₁, List.map_cons, List.append_assoc]
        rfl
      · rw [hpoint, hpoint₁, List.append_assoc]
        rfl
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hm5
        · exact h5 m hm
      · simp only [List.length_cons]
        omega
      · rw [hvv]
        rfl
      · rw [hgp, List.map_cons, ← List.singleton_append, ← List.append_assoc]
        rfl

/-- (a) "At every step": for any decomposition `pre ++ l :: post` of the log
messages, the honest gate run over `pre` reaches `(vᵢ, sᵢ)` with `sᵢ` holding the
tables after `pre.length` binds, and the next ACTUAL `Verifier.roundStep` sets
the gate claim to the round value of `sᵢ`'s tables at the verifier's own gate
challenge, which the prover then binds.  HONEST PROVER ONLY. -/
theorem honest_gate_chain_step (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound)
    (hv : Gates.validateConfiguration c gates = some ()) (v : Verifier.RoundState) (s : ProverState)
    (hl : Lockstep c gates publicHash alpha v s) (pre : List (List Verifier.Ext3))
    (l : List Verifier.Ext3) (post : List (List Verifier.Ext3))
    (hn : (pre ++ l :: post).length ≤ s.eq.numVars) :
    ∃ (vᵢ : Verifier.RoundState) (sᵢ : ProverState) (message : List Element) (sNext : ProverState),
      honestRun c gates publicHash alpha commit v s pre = some (vᵢ, sᵢ) ∧
      Lockstep c gates publicHash alpha vᵢ sᵢ ∧
      sᵢ.rounds.length = s.rounds.length + pre.length ∧
      sᵢ.eq.numVars + pre.length = s.eq.numVars ∧
      honestStep c gates publicHash alpha commit l vᵢ sᵢ =
        some (Verifier.roundStep commit vᵢ (coupled l message), sNext) ∧
      honestRun c gates publicHash alpha commit v s (pre ++ [l]) =
        some (Verifier.roundStep commit vᵢ (coupled l message), sNext) ∧
      stateRound c gates publicHash alpha sᵢ = some message ∧
      message.length = c.quotientDegree + 2 ∧
      (Verifier.roundStep commit vᵢ (coupled l message)).gateClaim =
        (stateRoundElement c gates publicHash alpha
          (gateChallenge commit vᵢ l message) sᵢ).toVerifier ∧
      sNext.tables = bindTables sᵢ.tables (gateChallenge commit vᵢ l message) ∧
      sNext.point = sᵢ.point ++ [gateChallenge commit vᵢ l message] ∧
      sNext.rounds = sᵢ.rounds ++ [message.map Element.toVerifier] ∧
      Consistent c sNext ∧ sNext.eq.numVars + 1 = sᵢ.eq.numVars := by
  simp only [List.length_append, List.length_cons] at hn
  obtain ⟨vᵢ, sᵢ, sent, chals, hrun, -, hrounds, -, hsl, -, -, hrem, -, -, hlock⟩ :=
    honest_run_exact c gates publicHash alpha commit hv pre v s hl (by omega)
  have hn' : ¬isComplete sᵢ := by unfold isComplete; omega
  obtain ⟨message, sNext, hsr, hm5, hstep, hcons', hnum', hrounds', hpoint', htab, hclaim, _⟩ :=
    honest_step_exact c gates publicHash alpha commit l vᵢ sᵢ hv hlock hn'
  refine ⟨vᵢ, sᵢ, message, sNext, hrun, hlock, ?_, hrem, hstep, ?_, hsr, hm5, hclaim, htab,
    hpoint', hrounds', hcons', hnum'⟩
  · rw [hrounds, List.length_append, List.length_map, hsl]
  · rw [honest_run_append c gates publicHash alpha commit pre [l] v s vᵢ sᵢ hrun]
    simp only [honestRun, hstep, Option.bind_eq_bind, Option.some_bind]

/-- (a) The FINAL gate claim of an honest run over `pre ++ [l]` is the round
value of the tables after `pre.length` binds, at the verifier's last gate
challenge, which is also the last coordinate of both the verifier's `gatePoint`
and the prover's `point`.  HONEST PROVER ONLY. -/
theorem honest_gate_chain (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound)
    (hv : Gates.validateConfiguration c gates = some ()) (v : Verifier.RoundState) (s : ProverState)
    (hl : Lockstep c gates publicHash alpha v s) (pre : List (List Verifier.Ext3))
    (l : List Verifier.Ext3) (hn : pre.length + 1 ≤ s.eq.numVars) :
    ∃ (vLast : Verifier.RoundState) (sLast : ProverState) (message : List Element)
      (sEnd : ProverState),
      honestRun c gates publicHash alpha commit v s pre = some (vLast, sLast) ∧
      honestRun c gates publicHash alpha commit v s (pre ++ [l]) =
        some (Verifier.roundStep commit vLast (coupled l message), sEnd) ∧
      sLast.rounds.length = s.rounds.length + pre.length ∧
      stateRound c gates publicHash alpha sLast = some message ∧
      message.length = c.quotientDegree + 2 ∧
      (Verifier.roundStep commit vLast (coupled l message)).gateClaim =
        (stateRoundElement c gates publicHash alpha
          (gateChallenge commit vLast l message) sLast).toVerifier ∧
      sEnd.point = sLast.point ++ [gateChallenge commit vLast l message] ∧
      (Verifier.roundStep commit vLast (coupled l message)).gatePoint =
        vLast.gatePoint ++ [(gateChallenge commit vLast l message).toVerifier] ∧
      sEnd.rounds = sLast.rounds ++ [message.map Element.toVerifier] ∧
      Consistent c sEnd ∧ sEnd.eq.numVars + pre.length + 1 = s.eq.numVars := by
  have hn' : (pre ++ l :: []).length ≤ s.eq.numVars := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨vᵢ, sᵢ, message, sNext, hrun, _, hlen, hrem, _, hrun', hsr, hm5, hclaim, _, hpt,
    hrounds, hcons, hnum⟩ :=
    honest_gate_chain_step c gates publicHash alpha commit hv v s hl pre l [] hn'
  exact ⟨vᵢ, sᵢ, message, sNext, hrun, hrun', hlen, hsr, hm5, hclaim, hpt, rfl, hrounds, hcons,
    by omega⟩

/-! ### The source's zero initial gate claim -/

/-- verifier_v2.rs:277-278 and OuterLogupExt3Verifier.sol:272-273: the GATE lane
starts from zero with an empty point at round index 0. -/
theorem source_start_gate_claim_zero (i : Verifier.Initial) :
    (Verifier.start i).gateClaim = Verifier.zero ∧ (Verifier.start i).gatePoint = [] ∧
    (Verifier.start i).roundIndex = 0 := ⟨rfl, rfl, rfl⟩

/-- (a) The gate analogue of `OuterClaimChain.chain_initial_claim`.  The source's
ZERO initial gate claim is in lockstep with the honest gate prover's state
exactly when that state's Boolean-cube gate sum is zero.  This does NOT assert
that the cube sum is zero: that is circuit truth, stated here only
CONDITIONALLY.  HONEST PROVER ONLY. -/
theorem chain_initial_claim (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (i : Verifier.Initial) (s : ProverState)
    (hc : Consistent c s) (hn : ¬isComplete s) :
    Lockstep c gates publicHash alpha (Verifier.start i) s ↔
      cubeSum c gates publicHash alpha s.tables (2 ^ s.eq.numVars) = 0 := by
  rw [← state_endpoint_sum_is_cube_sum c gates publicHash alpha s hn]
  constructor
  · intro hl
    have h := hl.claim hn
    apply GoldilocksExt3Field.element_eq
    rw [← h]
    rfl
  · intro hz
    exact ⟨hc, fun _ => by rw [hz]; rfl⟩

/-! ### `into_proof_and_point` returns what the verifier consumed -/

/-- (a) After exactly `eq.numVars` lockstep rounds the gate prover is complete and
`into_proof_and_point` (gate_ext3_v2.rs:163-171) returns precisely the message
list fed to `Verifier.runRounds` and the verifier's gate challenges, in order;
the verifier's `gatePoint` is the same list.  HONEST PROVER ONLY. -/
theorem honest_extraction_matches_verifier (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (commit : Verifier.CommitRound)
    (hv : Gates.validateConfiguration c gates = some ()) (v : Verifier.RoundState) (s : ProverState)
    (hl : Lockstep c gates publicHash alpha v s) (logs : List (List Verifier.Ext3))
    (hn : logs.length = s.eq.numVars) :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element))
      (chals : List Element),
      honestRun c gates publicHash alpha commit v s logs = some (v', s') ∧ isComplete s' ∧
      intoProofAndPoint s' =
        some (s.rounds ++ sent.map (List.map Element.toVerifier), s.point ++ chals) ∧
      sent.length = logs.length ∧ chals.length = logs.length ∧
      (∀ m ∈ sent, m.length = c.quotientDegree + 2) ∧
      v' = Verifier.runRounds commit v (logs.zip (sent.map (List.map Element.toVerifier))) ∧
      v'.gatePoint = v.gatePoint ++ chals.map Element.toVerifier := by
  obtain ⟨v', s', sent, chals, hrun, -, hrounds, hpoint, hsl, hcl, h5, hrem, hvv, hgp, -⟩ :=
    honest_run_exact c gates publicHash alpha commit hv logs v s hl (by omega)
  have hcomplete : isComplete s' := by unfold isComplete; omega
  refine ⟨v', s', sent, chals, hrun, hcomplete, ?_, hsl, hcl, h5, hvv, hgp⟩
  rw [proof_extraction_exact s' hcomplete, hrounds, hpoint]

/-- (a) The gate analogue of `OuterClaimChain.honest_run_is_derived_rounds`.
From a fresh gate prover state and `Verifier.start`: the extracted proof is
exactly the sent gate messages and the verifier's gate point, and
`Verifier.derivedRounds` of any proof whose `logRounds`/`gateRounds` are those
lists IS the lockstep verifier state.  The zero-cube-sum hypothesis is EXPLICIT,
never assumed.  HONEST PROVER ONLY. -/
theorem honest_run_is_derived_rounds (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (s : ProverState)
    (logs : List (List Verifier.Ext3))
    (hv : Gates.validateConfiguration c gates = some ()) (hc : Consistent c s)
    (hr : s.rounds = []) (hp : s.point = [])
    (hz : cubeSum c gates publicHash alpha s.tables (2 ^ s.eq.numVars) = 0)
    (hn : logs.length = s.eq.numVars) (hpos : ¬isComplete s) :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element))
      (chals : List Element),
      honestRun c gates publicHash alpha e.commitRound
        (Verifier.start (e.initialTranscript vc p)) s logs = some (v', s') ∧
      intoProofAndPoint s' = some (sent.map (List.map Element.toVerifier), chals) ∧
      v'.gatePoint = chals.map Element.toVerifier ∧
      (∀ m ∈ sent, m.length = c.quotientDegree + 2) ∧
      (p.logRounds = logs → p.gateRounds = sent.map (List.map Element.toVerifier) →
        Verifier.derivedRounds e vc p = v') := by
  have hl : Lockstep c gates publicHash alpha (Verifier.start (e.initialTranscript vc p)) s :=
    (chain_initial_claim c gates publicHash alpha (e.initialTranscript vc p) s hc hpos).mpr hz
  obtain ⟨v', s', sent, chals, hrun, -, hext, -, -, h5, hvv, hgp⟩ :=
    honest_extraction_matches_verifier c gates publicHash alpha e.commitRound hv _ s hl logs hn
  refine ⟨v', s', sent, chals, hrun, ?_, ?_, h5, fun hlr hgr => ?_⟩
  · rw [hext, hr, hp, List.nil_append, List.nil_append]
  · rw [hgp]; rfl
  · rw [Verifier.derivedRounds, hlr, hgr, hvv]

/-! ## 3. (b) The gate terminal bridge -/

/-- Acceptance of the adopted `Integrated.verify` forces the decoded gate list to
pass `Gates.validateConfiguration` (via `Integrated.gateResult`'s success).
DERIVED, not assumed. -/
theorem accepted_gate_configuration_valid (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (vc : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hd : decode vc.gatesEncoding = some gates) :
    Gates.validateConfiguration (Integrated.gateConfig vc) gates = some () := by
  obtain ⟨-, gate0, -, hg, -, -⟩ :=
    Integrated.accepted_concrete_terminal_equations e decode pin chain vc p hacc
  obtain ⟨gates', hd', -, -, -, -, hv⟩ :=
    Integrated.successful_gate_evaluation_checks_all_metadata decode vc _ _ _ _ gate0 hg
  rw [hd, Option.some.injEq] at hd'
  subst hd'
  exact hv

/-- (b) THE GATE TERMINAL BRIDGE.  If the adopted `Integrated.verify` accepts and
the fully bound cells `k` of the last gate tables match the proof's claimed gate
witness/constants, with the prover's alpha the transcript's `gateAlpha` and the
bound eq cell `eq(gateTau, gatePoint)`, then the LAST ROUND VALUE of those tables
at the last challenge IS the verifier's own derived `gateClaim`.  The metadata
facts (gate rows, public-hash length, configuration validity) are DERIVED from
acceptance; only the correspondences listed as hypotheses are assumed.  This is
the gate analogue of `ConditionalSoundness.norm_terminal_is_honest_last_value`,
and it reaches `Verifier.gateTerminal` through the adopted
`GateTerminalBinding.bound_terminal_is_engine_gate_terminal`. -/
theorem accepted_last_round_value_is_gate_claim (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (vc : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (tLast : GateSuffixPolynomial.Tables) (x : Element) (k : Cells) (alpha : Element)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hd : decode vc.gatesEncoding = some gates)
    (ht : GateSuffixPolynomial.TableShape (Integrated.gateConfig vc) 1 tLast)
    (hbt : bindTables tLast x = k.tables)
    (hk : CellsMatchClaims vc k (gateTerminalInput p))
    (halpha : alpha.toVerifier = (e.initialTranscript vc p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript vc p).gateTau (Verifier.derivedRounds e vc p).gatePoint) :
    GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha x tLast 1 =
      some (Verifier.derivedRounds e vc p).gateClaim := by
  obtain ⟨-, gate0, -, hg, -, hclaim⟩ :=
    Integrated.accepted_concrete_terminal_equations e decode pin chain vc p hacc
  obtain ⟨gates', hd', hr, hp, -, -, hv⟩ :=
    Integrated.successful_gate_evaluation_checks_all_metadata decode vc _ _ _ _ gate0 hg
  rw [hd, Option.some.injEq] at hd'
  subst hd'
  obtain ⟨hw, hc⟩ := cells_lengths _ _ _ _ ht hbt
  obtain ⟨gate, hres, hterm, -⟩ := bound_terminal_is_engine_gate_terminal e decode vc p gates k alpha
    hd hr hp hv hk hw hc halpha heq
  rw [hres, Option.some.injEq] at hg
  subst hg
  rw [round_value_last_round _ gates _ alpha tLast x k ht hbt, hterm, heq]
  exact congrArg some hclaim

/-- (b) The same bridge in field form: the LAST STATE's `stateRoundElement` at the
last challenge lifts to the verifier's derived gate claim. -/
theorem accepted_last_state_value_is_gate_claim (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (vc : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (sLast : ProverState) (x : Element) (k : Cells) (alpha : Element)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hd : decode vc.gatesEncoding = some gates)
    (hs : ProverShape (Integrated.gateConfig vc) 1 sLast)
    (hbt : bindTables sLast.tables x = k.tables)
    (hk : CellsMatchClaims vc k (gateTerminalInput p))
    (halpha : alpha.toVerifier = (e.initialTranscript vc p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript vc p).gateTau (Verifier.derivedRounds e vc p).gatePoint) :
    (stateRoundElement (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha x sLast).toVerifier =
      (Verifier.derivedRounds e vc p).gateClaim := by
  have hnum : sLast.eq.numVars = 1 := hs.2.2.1.2
  have ht : GateSuffixPolynomial.TableShape (Integrated.gateConfig vc) 1 sLast.tables := by
    simpa using shape_gives_table_shape _ 1 sLast hs Nat.one_pos
  have hv := accepted_gate_configuration_valid e decode pin chain vc p gates hacc hd
  have h1 := accepted_last_round_value_is_gate_claim e decode pin chain vc p gates sLast.tables x k
    alpha hacc hd ht hbt hk halpha heq
  have h2 := current_round_value_sum (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha x sLast.tables 1 hv ht
  unfold stateRoundElement
  rw [hnum]
  exact Option.some.inj (h2.symm.trans h1)

/-! ## 4. (c) The SOUNDNESS direction for the gate lane -/

open ConditionalSoundness in
/-- THE GATE HONEST (TRUTH) CHAIN, TIED TO THE EXECUTION.  Along the challenges
the run actually drew, each round's TRUE message is the adopted
`GateDenseRound.stateRound` (= `current_round`, gate_ext3_v2.rs:105-140) of the
current extracted gate prover state, the states advance by the source's own
`GateTerminalBinding.bindChallenge`, and the LAST state and the LAST drawn
challenge are pinned to `sLast` and `x`.

Three properties matter, and they are exactly what the deleted
`accepted_gate_cube_sum_vanishes` of `ConditionalSoundness` lacked:
* the truths are NOT free parameters -- each is forced to be `stateRound` of a
  state reached from `s0` by the execution's own binds;
* the empty lane is `False`, so there is always a last round (and
  `ConditionalSoundness.lanes_nonempty` shows an accepted proof's lane is
  nonempty);
* `[]` truths are IMPOSSIBLE (`truth_chain_lengths` forces every truth to have
  `quotientDegree + 2` entries), so the `gateTruths := []` instantiation that
  made the earlier draft degenerate cannot satisfy this predicate at all
  (`empty_gate_truths_not_honest`). -/
def TruthChain (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element) :
    ProverState → List LaneRound → Prop
  | _, [] => False
  | s, [r] => stateRound c gates publicHash alpha s = some r.truth ∧ s.eq.numVars = 1 ∧
      sLast = s ∧ x = r.challenge
  | s, r :: r2 :: rs => stateRound c gates publicHash alpha s = some r.truth ∧
      2 ≤ s.eq.numVars ∧
      ∃ t, bindChallenge s (r.truth.map Element.toVerifier) r.challenge = some t ∧
        TruthChain c gates publicHash alpha sLast x t (r2 :: rs)

open ConditionalSoundness in
/-- A state carrying a nonempty gate truth chain still has a Boolean variable. -/
theorem truth_chain_incomplete (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element) :
    ∀ (rs : List LaneRound) (s : ProverState),
      TruthChain c gates publicHash alpha sLast x s rs → rs ≠ [] → ¬isComplete s
  | [], _, h, _ => absurd h not_false
  | [_], s, hh, _ => by have := hh.2.1; unfold isComplete; omega
  | _ :: _ :: _, s, hh, _ => by have := hh.2.1; unfold isComplete; omega

open ConditionalSoundness in
/-- The gate prover state stays `Consistent` along the whole truth chain
(`GateDenseRound.bind_challenge_consistent`). -/
theorem truth_chain_consistent (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element)
    (hv : Gates.validateConfiguration c gates = some ()) :
    ∀ (rs : List LaneRound) (s : ProverState), Consistent c s →
      TruthChain c gates publicHash alpha sLast x s rs → Consistent c sLast
  | [], _, _, h => absurd h not_false
  | [_], s, hc, hh => by rw [hh.2.2.1]; exact hc
  | r :: r2 :: rs, s, hc, hh => by
      have hn : ¬isComplete s := by have := hh.2.1; unfold isComplete; omega
      have hlen := honest_message_length c gates publicHash alpha s r.truth hv hc hn hh.1
      obtain ⟨t, hb, hrec⟩ := hh.2.2
      obtain ⟨t', hb', hcons, -, -, -, -, -⟩ := bind_challenge_consistent c s
        (r.truth.map Element.toVerifier) r.challenge hc hn
        (by rw [List.length_map, hlen, hc.2.1])
      have : t' = t := Option.some.inj (hb'.symm.trans hb)
      subst this
      exact truth_chain_consistent c gates publicHash alpha sLast x hv (r2 :: rs) t' hcons hrec

open ConditionalSoundness in
/-- NON-DEGENERACY.  Every TRUE gate message of the chain has exactly
`quotientDegree + 2` coefficients -- the same count `Verifier.shape` forces on
the proof's own gate rounds.  In particular no truth is `[]`. -/
theorem truth_chain_lengths (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element)
    (hv : Gates.validateConfiguration c gates = some ()) :
    ∀ (rs : List LaneRound) (s : ProverState), Consistent c s →
      TruthChain c gates publicHash alpha sLast x s rs →
      ∀ r ∈ rs, r.truth.length = c.quotientDegree + 2
  | [], _, _, h, _, _ => absurd h not_false
  | [r], s, hc, hh, q, hq => by
      have hn : ¬isComplete s := by have := hh.2.1; unfold isComplete; omega
      have : q = r := by simpa using hq
      subst this
      exact honest_message_length c gates publicHash alpha s q.truth hv hc hn hh.1
  | r :: r2 :: rs, s, hc, hh, q, hq => by
      have hn : ¬isComplete s := by have := hh.2.1; unfold isComplete; omega
      have hlen := honest_message_length c gates publicHash alpha s r.truth hv hc hn hh.1
      obtain ⟨t, hb, hrec⟩ := hh.2.2
      obtain ⟨t', hb', hcons, -, -, -, -, -⟩ := bind_challenge_consistent c s
        (r.truth.map Element.toVerifier) r.challenge hc hn
        (by rw [List.length_map, hlen, hc.2.1])
      have hteq : t' = t := Option.some.inj (hb'.symm.trans hb)
      subst hteq
      rcases List.mem_cons.mp hq with rfl | hqm
      · exact hlen
      · exact truth_chain_lengths c gates publicHash alpha sLast x hv (r2 :: rs) t' hcons hrec q hqm

open ConditionalSoundness in
/-- (c) THE MULTI-ROUND INDUCTION IN THE SOUNDNESS DIRECTION.  The honest chain
started at the extracted state's ENDPOINT SUM reaches exactly the last state's
round value at the last drawn challenge.  Deterministic; chained through the
adopted `GateDenseRound.bound_endpoint_sum_is_state_round_value`. -/
theorem truth_chain_run (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element)
    (hv : Gates.validateConfiguration c gates = some ()) :
    ∀ (rs : List LaneRound) (s : ProverState), Consistent c s →
      TruthChain c gates publicHash alpha sLast x s rs →
      truthRun (endpointSum c gates publicHash alpha s) rs =
        stateRoundElement c gates publicHash alpha x sLast
  | [], _, _, h => absurd h not_false
  | [r], s, hc, hh => by
      have hn : ¬isComplete s := by have := hh.2.1; unfold isComplete; omega
      simp only [truthRun]
      rw [round_evaluate_bridge c gates publicHash alpha s r.truth r.challenge hv hc hn hh.1,
        hh.2.2.1, hh.2.2.2]
  | r :: r2 :: rs, s, hc, hh => by
      have hn : ¬isComplete s := by have := hh.2.1; unfold isComplete; omega
      have hlen := honest_message_length c gates publicHash alpha s r.truth hv hc hn hh.1
      obtain ⟨t, hb, hrec⟩ := hh.2.2
      obtain ⟨t', hb', hcons, -, -, -, -, -⟩ := bind_challenge_consistent c s
        (r.truth.map Element.toVerifier) r.challenge hc hn
        (by rw [List.length_map, hlen, hc.2.1])
      have hteq : t' = t := Option.some.inj (hb'.symm.trans hb)
      subst hteq
      have hbound := bound_endpoint_sum_is_state_round_value c gates publicHash alpha s t'
        (r.truth.map Element.toVerifier) r.challenge hc hh.2.1 hb
      have ih := truth_chain_run c gates publicHash alpha sLast x hv (r2 :: rs) t' hcons hrec
      simp only [truthRun]
      rw [round_evaluate_bridge c gates publicHash alpha s r.truth r.challenge hv hc hn hh.1,
        ← hbound]
      exact ih

open ConditionalSoundness in
/-- NON-DEGENERACY.  A gate truth chain over a lane of `n` rounds forces the
extracted state to have EXACTLY `n` live Boolean variables: each non-final round
consumes one (`bind_challenge`), and the final round has exactly one left.  So
the cube the conclusion sums over is not a free choice either. -/
theorem truth_chain_numvars (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element) :
    ∀ (rs : List LaneRound) (s : ProverState),
      TruthChain c gates publicHash alpha sLast x s rs → s.eq.numVars = rs.length
  | [], _, h => absurd h not_false
  | [_], _, hh => hh.2.1
  | r :: r2 :: rs, s, hh => by
      obtain ⟨t, hb, hrec⟩ := hh.2.2
      have hrest := truth_chain_numvars c gates publicHash alpha sLast x (r2 :: rs) t hrec
      have hbv := (bind_challenge_success s t (r.truth.map Element.toVerifier) r.challenge hb).2.1
      have ht : t.eq.numVars = s.eq.numVars - 1 := by
        rw [(bind_variable_success s.eq t.eq r.challenge hbv).2]
      have h2 := hh.2.1
      simp only [List.length_cons] at hrest ⊢
      omega

open ConditionalSoundness in
/-- The chain's pinned last state really has ONE variable left.  This is the
TruthChain base case read off the end of the chain, and it makes the separate
`ProverShape _ 1 sLast` assumption of an earlier draft redundant: together with
`truth_chain_consistent` it derives that shape. -/
theorem truth_chain_last_numvars (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element) :
    ∀ (rs : List LaneRound) (s : ProverState),
      TruthChain c gates publicHash alpha sLast x s rs → sLast.eq.numVars = 1
  | [], _, h => absurd h not_false
  | [_], _, hh => by rw [hh.2.2.1]; exact hh.2.1
  | _ :: r2 :: rs, _, hh => by
      obtain ⟨t, -, hrec⟩ := hh.2.2
      exact truth_chain_last_numvars c gates publicHash alpha sLast x (r2 :: rs) t hrec

open ConditionalSoundness in
/-- The last state's `ProverShape` at one remaining variable, DERIVED from the
truth chain (`truth_chain_consistent` for the shape at `sLast.eq.numVars`,
`truth_chain_last_numvars` for that count being 1).  No separate assumption. -/
theorem truth_chain_last_shape (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (sLast : ProverState) (x : Element)
    (hv : Gates.validateConfiguration c gates = some ()) (rs : List LaneRound) (s : ProverState)
    (hc : Consistent c s) (hh : TruthChain c gates publicHash alpha sLast x s rs) :
    ProverShape c 1 sLast := by
  have hcons := truth_chain_consistent c gates publicHash alpha sLast x hv rs s hc hh
  have hnv := truth_chain_last_numvars c gates publicHash alpha sLast x rs s hh
  rw [← hnv]
  exact hcons.1

/-! ### The CONSTRAINT-FREE CONFIGURATION: a real degeneracy of `cubeSum = 0`

`vc.numGateConstraints = 0` is NOT excluded by the deployed guards.  The adopted
`Verifier.envelope` and `Gates.envelope` only bound it ABOVE (`≤ 123`), and the
adopted `Integrated.exampleConfig` really does set `numGateConstraints := 0`, so
this is a shape a supplier can present, not a hypothetical.  On such a
configuration `Gates.validateConfiguration` pins `numGateConstraints` to the
EXACT maximum of the decoded gates' `numConstraints`
(`Gates.configuration_declares_exact_maximum`), so every gate declares zero
constraints, every `GatesComplete.contribution` is `zero`, `evalCombined` is
`some zero` at every row, and `cubeSum = 0` holds FOR ANY TABLES WHATSOEVER.

The four theorems below PROVE that, so that a reader cannot mistake
`cubeSum = 0` for content in that regime, and `Assumptions`' field 4
(`gateConstraintsPositive`) excludes it. -/

/-- Zero declared gate constraints forces every decoded gate to declare zero
constraints. -/
theorem constraint_free_gates (c : Gates.Config) (gates : List Gates.GateInfo)
    (hv : Gates.validateConfiguration c gates = some ()) (h0 : c.numGateConstraints = 0) :
    ∀ g ∈ gates, g.numConstraints = 0 := by
  have hmax := Gates.configuration_declares_exact_maximum c gates hv
  rw [h0] at hmax
  have key : ∀ (l : List Nat), (l.foldr max 0) = 0 → ∀ n ∈ l, n = 0 := by
    intro l
    induction l with
    | nil => intro _ n hn; exact absurd hn (List.not_mem_nil n)
    | cons a t ih =>
        intro h n hn
        rw [List.foldr_cons] at h
        have h1 := Nat.le_max_left a (t.foldr max 0)
        have h2 := Nat.le_max_right a (t.foldr max 0)
        rcases List.mem_cons.mp hn with rfl | hm
        · omega
        · exact ih (by omega) n hm
  intro g hg
  have := key (gates.map Gates.GateInfo.numConstraints) hmax.symm g.numConstraints
    (List.mem_map_of_mem _ hg)
  exact this

/-- A gate declaring zero constraints contributes `zero` to `combineRows`. -/
theorem constraint_free_contribution (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (alpha : Verifier.Ext3) (h0 : g.numConstraints = 0) (r : Verifier.Ext3)
    (h : GatesComplete.contribution c g wires constants publicHash alpha = some r) :
    r = Verifier.zero := by
  unfold GatesComplete.contribution at h
  dsimp only at h
  split at h
  · exact (Option.some.inj h).symm
  · cases hterms : GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors with
    | none => rw [hterms] at h; simp at h
    | some terms =>
        rw [hterms] at h
        simp only [Option.bind_eq_bind, Option.some_bind] at h
        split at h
        · rename_i hlen
          rw [h0, List.length_eq_zero] at hlen
          subst hlen
          rw [← Option.some.inj h]
          exact Gates.mul_zero _
        · exact h.elim

/-- `combineRows` over gates that all declare zero constraints returns the
accumulator unchanged. -/
theorem constraint_free_combine_rows (c : Gates.Config) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (alpha : Verifier.Ext3) :
    ∀ (gs : List Gates.GateInfo) (acc r : Verifier.Ext3), (∀ g ∈ gs, g.numConstraints = 0) →
      GatesComplete.combineRows c wires constants publicHash alpha gs acc = some r → r = acc
  | [], _, _, _, h => (Option.some.inj h).symm
  | g :: gs, acc, r, h0, h => by
      unfold GatesComplete.combineRows at h
      cases hcon : GatesComplete.contribution c g wires constants publicHash alpha with
      | none => rw [hcon] at h; simp at h
      | some term =>
          rw [hcon] at h
          simp only [Option.bind_eq_bind, Option.some_bind] at h
          have hz : term = Verifier.zero := constraint_free_contribution c g wires constants
            publicHash alpha (h0 g (List.mem_cons_self _ _)) term hcon
          subst hz
          rw [Gates.add_zero] at h
          exact constraint_free_combine_rows c wires constants publicHash alpha gs acc r
            (fun q hq => h0 q (List.mem_cons_of_mem _ hq)) h

/-- On a validated constraint-free configuration the whole gate aggregate is
`zero` at every row, hence every `rowElement` is `0` and the Boolean-cube sum is
`0` FOR ANY TABLES.  THIS IS THE DEGENERACY: without a positivity guard,
`cubeSum = 0` says nothing at all. -/
theorem constraint_free_cube_sum_vanishes (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : GateSuffixPolynomial.Tables)
    (count : Nat) (hv : Gates.validateConfiguration c gates = some ())
    (h0 : c.numGateConstraints = 0) :
    cubeSum c gates publicHash alpha t count = 0 := by
  have hrow : ∀ index : Nat, rowElement c gates publicHash alpha t index = 0 := by
    intro index
    have hterm : rowTerm c gates publicHash alpha t index = none ∨
        rowTerm c gates publicHash alpha t index = some Verifier.zero := by
      unfold rowTerm
      cases he : GatesComplete.evalCombined c gates
          (t.wires.map (fun column => (column.getD index 0).toVerifier))
          (t.constants.map (fun column => (column.getD index 0).toVerifier)) publicHash
          alpha.toVerifier with
      | none => exact Or.inl rfl
      | some gate =>
          have hg : gate = Verifier.zero := by
            unfold GatesComplete.evalCombined at he
            split at he
            · exact he.elim
            · rw [hv] at he
              simp only [Option.bind_eq_bind, Option.some_bind] at he
              exact constraint_free_combine_rows c _ _ publicHash alpha.toVerifier gates
                Verifier.zero gate (constraint_free_gates c gates hv h0) he
          subst hg
          exact Or.inr (congrArg some (Gates.mul_zero _))
    rcases hterm with h | h
    · unfold rowElement
      rw [h]
    · unfold rowElement
      rw [h]
      exact rfl
  unfold cubeSum
  refine List.sum_eq_zero ?_
  intro y hy
  obtain ⟨index, -, rfl⟩ := List.mem_map.mp hy
  exact hrow index

/-! ### The named gate-lane assumptions -/

open ConditionalSoundness in
/-- EVERY assumption the gate-lane soundness theorem rests on, as a named,
enumerable, VISIBLE `Prop` field.  Nothing is hidden in a definition:
`accepted_gate_cube_sum_vanishes` uses exactly these eight fields plus
`Integrated.verify` acceptance and the explicit "no gate bad event"
hypothesis.

Parameters: the engine / gate decoder / config / proof of the adopted
`Integrated.verify`; the decoded `gates`; the EXTRACTED gate prover state `s0`
(fresh, all `degreeBits` variables live) and `sLast` (one variable left); the
last drawn gate challenge `x`; the fully bound `Cells` `k`; the prover's `alpha`;
and the honest round-message list `gateTruths` of the GATE lane.

The gate prover's public-hash function is NOT a parameter: it is fixed to
`publicHashFunction (e.publicInputsHash p.publicInputs)`, the adopted
`Integrated` conversion of the proof's own public-input hash.

WHY THIS CANNOT DEGENERATE THE WAY THE DELETED
`ConditionalSoundness.accepted_gate_cube_sum_vanishes` DID.  There, `gateTruths`
and the gate cube sum were free parameters with no tie to any gate table, so
`gateTruths := []` collapsed the honest run to an invertible map and let an
adversary pick a cube sum matching any accepting proof.  Here the conclusion's
cube sum is `GateDenseRound.cubeSum` of `s0.tables` -- the tables of the state
named in field 3 -- and field 3 forces every round's truth to be
`GateDenseRound.stateRound` of a state reached from `s0` by the execution's OWN
`bindChallenge`.  `truth_chain_lengths` proves every such truth has
`quotientDegree + 2` entries, and `empty_gate_truths_not_honest` proves that the
`gateTruths := []` instantiation makes field 3 UNSATISFIABLE for any proof that
passes the adopted `Verifier.shape` / `Verifier.envelope` guards.

TWO DEGENERACIES REMAIN VISIBLE RATHER THAN HIDDEN.  Field 4 excludes the
constraint-free configuration, on which `cubeSum = 0` is provable for ANY tables
(`constraint_free_cube_sum_vanishes`).  The eq-table freedom is NOT excluded by
any field: field 8 pins one linear functional of the eq table and the conclusion
weighs an independent one, so this conjunction still has NO REJECTION POWER
against an adversarial supplier of `s0` -- see the module header. -/
structure Assumptions (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (vc : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 sLast : ProverState) (x : Element) (k : Cells) (alpha : Element)
    (gateTruths : List (List Element)) : Prop where
  /-- GATE ASSUMPTION 1 (`gatesDecode`).  The configuration's `gatesEncoding`
  bytes decode to `gates`.  NOT PROVED: `Integrated.DecodeGates` is an opaque
  observation of the deployed decoder.  What would prove it: a refinement of the
  Rust/Solidity gate-table decoder against `Gates.GateInfo`. -/
  gatesDecode : decode vc.gatesEncoding = some gates
  /-- GATE ASSUMPTION 2 (`extractedStateConsistent`).  The EXTRACTED fresh gate
  prover state satisfies the adopted `GateDenseRound.Consistent` -- the
  constructor ensures of gate_ext3_v2.rs:70-83 (`ProverShape` at the live
  variable count, `degree = quotientDegree + 2`, paired `rounds`/`point`).
  NOT PROVED: extraction is not formalised; this records the shape the extractor
  must deliver.  Everything downstream of it IS proved
  (`truth_chain_consistent`, `truth_chain_lengths`, `truth_chain_run`). -/
  extractedStateConsistent : Consistent (Integrated.gateConfig vc) s0
  /-- GATE ASSUMPTION 3 (`extractedTruthChain`).  THE TIE TO THE EXECUTION.
  Along the gate challenges the run actually drew, `gateTruths` are the adopted
  `GateDenseRound.stateRound` (= `current_round`) messages of the successively
  `bindChallenge`-bound extracted states, the last of which has one variable
  left and IS `sLast`, whose drawn challenge IS `x`.  NOT PROVED: the same
  extraction boundary as assumption 2 -- nothing here forces the extracted
  tables to be the ones the prover committed to (see the OPEN EXTRACTION JOIN
  note on assumption 6).  It is NOT satisfiable degenerately: see the structure
  docstring and `empty_gate_truths_not_honest`. -/
  extractedTruthChain : TruthChain (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha sLast x s0
    (gateLaneOf e vc p gateTruths)
  /-- GATE ASSUMPTION 4 (`gateConstraintsPositive`).  THE CONFIGURATION DECLARES
  AT LEAST ONE GATE CONSTRAINT.

  WITHOUT THIS FIELD THE CONCLUSION IS CONTENTLESS ON A REAL, REACHABLE SHAPE.
  `numGateConstraints = 0` passes the adopted `Verifier.envelope` and
  `Gates.envelope` -- both only bound it ABOVE, by 123 -- and the adopted
  `Integrated.exampleConfig` actually sets `numGateConstraints := 0`.  On such a
  configuration `Gates.validateConfiguration` forces every decoded gate to
  declare zero constraints, so the gate aggregate is `zero` at every row and
  `cubeSum = 0` holds FOR ANY TABLES WHATSOEVER; that is PROVED here, in
  `constraint_free_cube_sum_vanishes`.  This field excludes that regime.

  NOT PROVED, and NOT derivable from acceptance: the deployed guards do not
  require it.  What would discharge it: a pin on the deployed circuit's
  `numGateConstraints` (part of the hashed gate metadata, `Audit.Impl.SolVerifier`),
  or a `Verifier.envelope` strengthened to demand `0 < numGateConstraints`.

  It is a NECESSARY, NOT A SUFFICIENT, non-degeneracy condition: see the
  eq-table rejection-power note in the module header.

  (The earlier draft's field 4, `lastStateShape : ProverShape _ 1 sLast`, was
  REMOVED as redundant -- `truth_chain_last_shape` derives it from field 3.) -/
  gateConstraintsPositive : 0 < vc.numGateConstraints
  /-- GATE ASSUMPTION 5 (`lastCells`).  STRUCTURAL: `k` really is the cell tuple
  of `sLast`'s tables bound at the last drawn challenge `x`.  This is a
  statement about the tables, not an equation between field values.  It is not a
  vacuity and not a strengthening: the adopted
  `GateTerminalBinding.bound_tables_are_cells` shows such a `k` EXISTS for every
  `TableShape _ 1` table, and `cells_lengths` shows it has the right widths;
  this field only names it. -/
  lastCells : bindTables sLast.tables x = k.tables
  /-- GATE ASSUMPTION 6 (`cellsMatchClaims`).  The adopted
  `GateTerminalBinding.CellsMatchClaims`: the fully bound wire and constant
  cells ARE the proof's claimed `gateWitness` and `gatePreprocessed.take
  numConstants`.

  THIS IS THE EXTRACTION JOIN, AND IT IS ASSUMED OUTRIGHT.  No field of this
  structure and no theorem in this module connects the values the WHIR/Merkle
  check actually bound to the cells of `sLast`.  The adopted
  `IntegratedTerminalChain.accepted_whir_claims_are_table_evaluations` and
  `GateTerminalBinding.bound_gate_columns_are_packed_folds` are the identities a
  real extractor would have to be threaded through to DISCHARGE this field; that
  threading is not done here, exactly as on the norm side
  (`ConditionalSoundness` ASSUMPTION 17). -/
  cellsMatchClaims : CellsMatchClaims vc k (gateTerminalInput p)
  /-- GATE ASSUMPTION 7 (`alphaMatches`).  The gate prover's aggregation
  challenge IS the transcript's `gateAlpha`.  DISCHARGEABLE: the adopted
  `TranscriptProvenance.gate_alpha_element_matches` proves exactly this for the
  derived `gateAlphaElement`; it is left as a field here so that this module
  makes no claim about which transcript observation the deployed prover used. -/
  alphaMatches : alpha.toVerifier = (e.initialTranscript vc p).gateAlpha
  /-- GATE ASSUMPTION 8 (`eqCell`).  The fully bound gate eq cell IS
  `eq(gateTau, gatePoint)`.  DISCHARGEABLE: the adopted
  `EqTableProvenance.GateEqProvenance` plus
  `TranscriptProvenance.gate_eq_cell_of_derived_table` derive this
  from an eq table built by `ext3_eq_evals(gateTau)`; it is a field here because
  this module does not model the eq table's construction. -/
  eqCell : k.eq.toVerifier =
    Norm.eqEvaluation (e.initialTranscript vc p).gateTau (Verifier.derivedRounds e vc p).gatePoint

/-! ### The core gate soundness theorem -/

section Core
open ConditionalSoundness
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState} {x : Element}
  {k : Cells} {alpha : Element} {gateTruths : List (List Element)}

/-- (c) CORE CONDITIONAL SOUNDNESS, GATE LANE.  If the adopted
`Integrated.verify` accepts, the eight named assumptions hold, and NO drawn GATE
challenge landed in its round's agreement set (`ConditionalSoundness.BadEventFree`
over `ConditionalSoundness.badSets`, the SAME machinery the norm lane uses), then
A WEIGHTED SUM OVER THE SUPPLIED TABLES VANISHES: the all-gates aggregate of the
extracted gate tables, weighted row by row by the SUPPLIED eq table, sums to zero
over the Boolean cube.

This is the gate analogue of
`ConditionalSoundness.accepted_norm_cube_sum_vanishes`, and it is exactly the
statement that file's `THE GATE LANE IS NOT PROVED` note says was missing.

WHAT IT DOES NOT SAY.  It does NOT say the extracted gate tables satisfy the
relation the verifier is checking.  `cubeSum = 0` is a statement about the
EXTRACTED tables `s0.tables`, weighted by the SUPPLIED eq table; it does NOT say
the circuit's gate constraints hold at any row, let alone every row.  That step
needs the eq table's provenance from `gateTau` at EVERY row (assumption 8 pins
only the FULLY BOUND cell) together with the semantic bridge from
`GatesComplete.evalCombined` to the gate relation, which is a separate module.
It also does not close the extraction join (assumption 6).

AND IT REJECTS NOTHING AS IT STANDS.  Assumption 8 pins exactly ONE linear
functional of the eq table (the fully bound cell); the weight this conclusion
sums, the row sum of that same table, is an INDEPENDENT linear functional.  A
supplier free to choose `s0` can therefore present an eq table with the required
bound cell and ZERO row sum, making `cubeSum = 0` true for ANY gate aggregate.
Assumption 4 removes ONE degeneracy of this class (the constraint-free
configuration); it is NOT an exhaustive list.  At least one more is known: the
adopted `GatesComplete.contribution` short-circuits to `some zero` whenever the
selector filter is zero, and the selector values are read from the SUPPLIED
constants columns, so a supplier can zero every filter and obtain `cubeSum = 0`
with assumption 4 satisfied.  Read the module header's `NO REJECTION POWER`
note before using this theorem for anything. -/
theorem accepted_gate_cube_sum_vanishes (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode vc p gates s0 sLast x k alpha gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths)) :
    cubeSum (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables
      (2 ^ s0.eq.numVars) = 0 := by
  have hv := accepted_gate_configuration_valid e decode pin chain vc p gates hacc A.gatesDecode
  have hne : gateLaneOf e vc p gateTruths ≠ [] := by
    intro hL
    have h := A.extractedTruthChain
    rw [hL] at h
    exact h
  have hn0 : ¬isComplete s0 := truth_chain_incomplete _ gates _ alpha sLast x _ s0
    A.extractedTruthChain hne
  have htruth := truth_chain_run (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha sLast x hv
    (gateLaneOf e vc p gateTruths) s0 A.extractedStateConsistent A.extractedTruthChain
  have hshapeLast := truth_chain_last_shape (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha sLast x hv
    (gateLaneOf e vc p gateTruths) s0 A.extractedStateConsistent A.extractedTruthChain
  have hbridge := accepted_last_state_value_is_gate_claim e decode pin chain vc p gates sLast x k
    alpha hacc A.gatesDecode hshapeLast A.lastCells A.cellsMatchClaims A.alphaMatches A.eqCell
  have hclaim := derived_gate_claim e vc p gateTruths
  have heq : claimedRun 0 (gateLaneOf e vc p gateTruths) =
      truthRun (endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
        (gateLaneOf e vc p gateTruths) := by
    apply GoldilocksExt3Field.element_eq
    rw [← hclaim, ← hbridge, htruth]
  have h0 := chain_initial_agreement (gateLaneOf e vc p gateTruths) 0 _ hfree heq
  rw [← state_endpoint_sum_is_cube_sum (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0 hn0]
  exact h0.symm

/-- (c) NON-DEGENERACY, POSITIVE FORM.  Under the assumptions, EVERY gate lane
round's true message has the same `quotientDegree + 2` coefficients the
verifier's `Verifier.shape` guard forces on the prover's own gate rounds.  No
truth can be a free or empty list. -/
theorem assumptions_force_message_lengths (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode vc p gates s0 sLast x k alpha gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ()) :
    ∀ r ∈ gateLaneOf e vc p gateTruths, r.truth.length = vc.quotientDegree + 2 :=
  truth_chain_lengths (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha sLast x
    (accepted_gate_configuration_valid e decode pin chain vc p gates hacc A.gatesDecode)
    (gateLaneOf e vc p gateTruths) s0 A.extractedStateConsistent A.extractedTruthChain

/-- The per-round degree bounds of THIS lane, both halves PROVED.  The message
half is the adopted `ConditionalSoundness.gate_lane_message_lengths` applied to
the `Verifier.shape` guard that acceptance implies; the TRUTH half is
`assumptions_force_message_lengths`, i.e. the executed `current_round` lengths --
NOT an assumption.  This is precisely what `ConditionalSoundness` had to POSIT in
its ASSUMPTION 18 (`gateCompareDegree`) for its free comparison messages. -/
theorem gate_lane_degree_bounds (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode vc p gates s0 sLast x k alpha gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hshape : Verifier.shape pin vc p = true) :
    ∀ r ∈ gateLaneOf e vc p gateTruths,
      r.message.length ≤ vc.quotientDegree + 2 ∧ r.truth.length ≤ vc.quotientDegree + 2 := by
  obtain ⟨-, -, -, hga⟩ := shape_round_lengths pin vc p hshape
  intro r hr
  exact ⟨le_of_eq (gate_lane_message_lengths e vc p gateTruths hga r hr),
    le_of_eq (assumptions_force_message_lengths pin chain A hacc r hr)⟩

/-- (c) THE COUNTING BOUND, RE-INSTANTIATED FOR THIS LANE (point-count form).
The GENERIC `ConditionalSoundness.bad_sets_union_card` at THIS lane's starting
claim (`0` against the extracted state's `endpointSum`) and THIS lane's truths:
the union of the per-round agreement sets the run must avoid has at most
`(quotientDegree + 2) * degreeBits` points of the challenge field.

This is NOT `ConditionalSoundness`'s `outer_failure_bound`: that theorem is
stated over `badSets 0 gateCompare (gateLaneOf … gateCompareRounds)`, a DIFFERENT
starting claim and a DIFFERENT (free, meaningless) truths list, and its gate half
rests on that module's ASSUMPTION 18.  Here both degree bounds are proved. -/
theorem gate_lane_bad_set_card_bound (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode vc p gates s0 sLast x k alpha gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hshape : Verifier.shape pin vc p = true) :
    ((badSets 0
      (endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths)).foldr (· ∪ ·) ∅).card ≤
      (vc.quotientDegree + 2) * vc.degreeBits := by
  obtain ⟨hlr, hgr, -, -⟩ := shape_round_lengths pin vc p hshape
  obtain ⟨-, hlen⟩ := lane_length_of_shape e vc p gateTruths hlr hgr
  have hb := bad_sets_union_card (vc.quotientDegree + 2) 0
    (endpointSum (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0) (gateLaneOf e vc p gateTruths)
    (gate_lane_degree_bounds pin chain A hacc hshape)
  rw [hlen] at hb
  exact hb

/-- (c) THE COUNTING BOUND, RE-INSTANTIATED FOR THIS LANE (probability form).
The GENERIC `ConditionalSoundness.bad_sets_uniform_sum` at THIS lane's starting
claim and truths: the round-by-round mass of the agreement events under
`OuterChallenge`'s EXPLICIT uniform 32-byte-triple law is at most
`(quotientDegree + 2) * degreeBits * (⌈2^256/p⌉ / 2^256)^3`.

READ THE SCOPE.  This is an IDEAL-law counting statement about the gate lane's
outer-sumcheck agreement events only.  It says nothing about the real Keccak
transcript, it excludes the dominant WHIR/Merkle contribution entirely, and it is
NEVER composed with `accepted_gate_cube_sum_vanishes`'s `BadEventFree`
hypothesis: no probabilistic soundness statement is made anywhere in this module.
It is also NOT `ConditionalSoundness`'s `195`, which is a two-lane total for a
different gate-lane starting claim and truths list. -/
theorem gate_lane_bad_set_uniform_bound (pin : Verifier.Pinned) (chain : Nat)
    (A : Assumptions e decode vc p gates s0 sLast x k alpha gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hshape : Verifier.shape pin vc p = true) :
    (((badSets 0
      (endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths)).map OuterChallenge.uniformTupleProbability).sum) ≤
      (((vc.quotientDegree + 2) * vc.degreeBits : Nat) : ℚ) *
        ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  obtain ⟨hlr, hgr, -, -⟩ := shape_round_lengths pin vc p hshape
  obtain ⟨-, hlen⟩ := lane_length_of_shape e vc p gateTruths hlr hgr
  have hb := bad_sets_uniform_sum (vc.quotientDegree + 2) 0
    (endpointSum (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0) (gateLaneOf e vc p gateTruths)
    (gate_lane_degree_bounds pin chain A hacc hshape)
  rw [hlen] at hb
  exact hb

/-- NON-DEGENERACY, against the verifier's own round count.  For a proof passing
the adopted `Verifier.shape` guard, the extracted gate state's Boolean cube has
EXACTLY `2 ^ degreeBits` rows: the truth chain's length is the gate lane's, which
`Verifier.shape` fixes to `degreeBits`.  So the conclusion of
`accepted_gate_cube_sum_vanishes` is a statement about the full cube the verifier
actually ran `degreeBits` rounds over, not about some shorter prefix. -/
theorem assumptions_cover_degree_bits (pin : Verifier.Pinned)
    (A : Assumptions e decode vc p gates s0 sLast x k alpha gateTruths)
    (hshape : Verifier.shape pin vc p = true) :
    s0.eq.numVars = vc.degreeBits := by
  obtain ⟨hlr, hgr, -, -⟩ := ConditionalSoundness.shape_round_lengths pin vc p hshape
  obtain ⟨-, hg⟩ := ConditionalSoundness.lane_length_of_shape e vc p gateTruths hlr hgr
  rw [truth_chain_numvars (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha sLast x _ s0
    A.extractedTruthChain, hg]

end Core

/-- (c) NON-DEGENERACY, NEGATIVE FORM.  THE DEFECT CANNOT RECUR.  The
instantiation that made the deleted `ConditionalSoundness` gate theorem
degenerate -- `gateTruths := []`, which makes every lane round's truth the empty
list -- CANNOT satisfy the truth-chain assumption for any proof that passes the
adopted `Verifier.shape` and `Verifier.envelope` guards.  So
`accepted_gate_cube_sum_vanishes` cannot be applied with meaningless truths. -/
theorem empty_gate_truths_not_honest (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (pin : Verifier.Pinned) (gates : List Gates.GateInfo)
    (s0 sLast : ProverState) (x alpha : Element)
    (hv : Gates.validateConfiguration (Integrated.gateConfig vc) gates = some ())
    (hc : Consistent (Integrated.gateConfig vc) s0)
    (hshape : Verifier.shape pin vc p = true) (henv : Verifier.envelope vc = true) :
    ¬ TruthChain (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha sLast x s0
        (ConditionalSoundness.gateLaneOf e vc p []) := by
  intro hh
  obtain ⟨-, hne⟩ := ConditionalSoundness.lanes_nonempty e vc p [] pin hshape henv
  cases hL : ConditionalSoundness.gateLaneOf e vc p [] with
  | nil => exact hne hL
  | cons r rs =>
      have hr : r ∈ ConditionalSoundness.gateLaneOf e vc p [] := by
        rw [hL]; exact List.mem_cons_self _ _
      have h1 := truth_chain_lengths (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha sLast x hv _ s0 hc hh r hr
      have h2 : r.truth = [] := by
        rcases ConditionalSoundness.lane_truths e.commitRound Prod.snd
          Verifier.RoundChallenges.gate [] (Verifier.start (e.initialTranscript vc p))
          (p.logRounds.zip p.gateRounds) r hr with h | h
        · simp at h
        · exact h
      rw [h2, List.length_nil] at h1
      omega

/-! ## 5. (d) A concrete non-vacuous example

The instance is the ALREADY ADOPTED `GateDenseRound.exampleState`: the arithmetic
gate of `Gates.exampleArithmetic` in the validated configuration
`⟨1, 3, 1, 4, 2⟩`, with TWO Boolean variables left, so the chain has two real
rounds.  Every value below is the executed gate evaluator's, not a stand-in.

WHAT THIS EXAMPLE IS NOT.  It does NOT construct an accepting `Integrated.verify`
instance: that needs a full WHIR/Merkle proof, which no module of this audit
builds.  So `accepted_gate_cube_sum_vanishes` is NOT instantiated here; what is
instantiated is every gate-side object it consumes -- the truth chain, its
`truthRun`, the lockstep run against `Verifier.roundStep`/`runRounds`, and the
initial-claim equivalence -- on real computed data.  This example's cube sum is
NONZERO, which is why `example_not_lockstep_with_source_zero` holds: it is a
witness that `chain_initial_claim` has content, not a satisfying instance.

AND `example_truth_chain`'s lane is HAND-MADE.  Its `[⟨m1,m1,2⟩, ⟨m2,m2,3⟩]` is
a literal `List LaneRound`, not `ConditionalSoundness.gateLaneOf e vc p …` of any
execution.  It therefore shows that `TruthChain` is INHABITED on executed data;
it does NOT show that `Assumptions`' field 3 -- `TruthChain` over a real
`gateLaneOf` lane -- is inhabited.  Nothing in this audit exhibits that. -/

/-- The example's endpoint sum is its Boolean-cube gate sum, and it is NONZERO:
nothing below is vacuous. -/
theorem example_endpoint_sum_nonzero :
    endpointSum GateDenseRound.exampleConfig GateDenseRound.exampleGates
      GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha
      GateDenseRound.exampleState ≠ 0 := by
  rw [state_endpoint_sum_is_cube_sum _ _ _ _ _ (by decide)]
  exact GateDenseRound.example_nonzero.2.2.2.1

/-- (d) A REAL two-round gate truth chain over the adopted example: both true
messages are the executed `current_round` of the extracted state, the states
advance by the source's own `bind_challenge`, and the chain's `truthRun` reaches
the last state's round value at the last challenge. -/
theorem example_truth_chain :
    ∃ (m1 m2 : List Element) (s1 : ProverState),
      stateRound GateDenseRound.exampleConfig GateDenseRound.exampleGates
          GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha
          GateDenseRound.exampleState = some m1 ∧
      m1.length = 4 ∧
      bindChallenge GateDenseRound.exampleState (m1.map Element.toVerifier) 2 = some s1 ∧
      s1.eq.numVars = 1 ∧
      stateRound GateDenseRound.exampleConfig GateDenseRound.exampleGates
          GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha s1 = some m2 ∧
      m2.length = 4 ∧
      TruthChain GateDenseRound.exampleConfig GateDenseRound.exampleGates
        GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha s1 3
        GateDenseRound.exampleState [⟨m1, m1, 2⟩, ⟨m2, m2, 3⟩] ∧
      ConditionalSoundness.truthRun
          (endpointSum GateDenseRound.exampleConfig GateDenseRound.exampleGates
            GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha
            GateDenseRound.exampleState) [⟨m1, m1, 2⟩, ⟨m2, m2, 3⟩] =
        stateRoundElement GateDenseRound.exampleConfig GateDenseRound.exampleGates
          GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha 3 s1 ∧
      endpointSum GateDenseRound.exampleConfig GateDenseRound.exampleGates
        GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha
        GateDenseRound.exampleState ≠ 0 := by
  obtain ⟨m1, h1, hl1, -⟩ := state_round_exists GateDenseRound.exampleConfig
    GateDenseRound.exampleGates GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha
    GateDenseRound.exampleState GateDenseRound.example_configuration
    GateDenseRound.example_consistent (by decide)
  obtain ⟨s1, hb, hcons1, hnum1, -, -, -, -⟩ := bind_challenge_consistent
    GateDenseRound.exampleConfig GateDenseRound.exampleState (m1.map Element.toVerifier) 2
    GateDenseRound.example_consistent (by decide) (by rw [List.length_map, hl1]; rfl)
  have hnv1 : s1.eq.numVars = 1 := by
    have : GateDenseRound.exampleState.eq.numVars = 2 := rfl
    omega
  obtain ⟨m2, h2, hl2, -⟩ := state_round_exists GateDenseRound.exampleConfig
    GateDenseRound.exampleGates GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha
    s1 GateDenseRound.example_configuration hcons1 (by unfold isComplete; omega)
  have hchain : TruthChain GateDenseRound.exampleConfig GateDenseRound.exampleGates
      GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha s1 3
      GateDenseRound.exampleState [⟨m1, m1, 2⟩, ⟨m2, m2, 3⟩] :=
    ⟨h1, by decide, s1, hb, h2, hnv1, rfl, rfl⟩
  exact ⟨m1, m2, s1, h1, hl1, hb, hnv1, h2, hl2, hchain,
    truth_chain_run GateDenseRound.exampleConfig GateDenseRound.exampleGates
      GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha s1 3
      GateDenseRound.example_configuration _ GateDenseRound.exampleState
      GateDenseRound.example_consistent hchain,
    example_endpoint_sum_nonzero⟩

/-- A concrete coupled-round observation: constant log and gate challenges. -/
def exampleCommit : Verifier.CommitRound := fun _ _ _ _ => ⟨[], Norm.embed 3, Norm.embed 2⟩

/-- A verifier round state whose running GATE claim is the example's honest
endpoint sum.  It is NOT `Verifier.start`: the example's cube sum is nonzero, so
by `chain_initial_claim` no honest lockstep with the source's ZERO start exists
for this instance (see `example_not_lockstep_with_source_zero`). -/
def exampleStart : Verifier.RoundState :=
  ⟨[], 0, Verifier.zero,
   (endpointSum GateDenseRound.exampleConfig GateDenseRound.exampleGates
     GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha
     GateDenseRound.exampleState).toVerifier, [], []⟩

theorem example_lockstep :
    Lockstep GateDenseRound.exampleConfig GateDenseRound.exampleGates
      GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha exampleStart
      GateDenseRound.exampleState :=
  ⟨GateDenseRound.example_consistent, fun _ => rfl⟩

/-- (d) The lockstep run of (a) executed on the example: two rounds against the
ACTUAL `Verifier.roundStep`, the prover finishes complete, `into_proof_and_point`
returns exactly the messages the verifier consumed and the verifier's own gate
challenges, and the verifier state is literally `Verifier.runRounds`. -/
theorem example_honest_run :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element))
      (chals : List Element),
      honestRun GateDenseRound.exampleConfig GateDenseRound.exampleGates
        GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha exampleCommit exampleStart
        GateDenseRound.exampleState [[], []] = some (v', s') ∧
      isComplete s' ∧
      intoProofAndPoint s' = some (sent.map (List.map Element.toVerifier), chals) ∧
      sent.length = 2 ∧ chals.length = 2 ∧ (∀ m ∈ sent, m.length = 4) ∧
      v' = Verifier.runRounds exampleCommit exampleStart
        (([[], []] : List (List Verifier.Ext3)).zip (sent.map (List.map Element.toVerifier))) ∧
      v'.gatePoint = exampleStart.gatePoint ++ chals.map Element.toVerifier := by
  obtain ⟨v', s', sent, chals, hrun, hcomplete, hext, hsl, hcl, h5, hvv, hgp⟩ :=
    honest_extraction_matches_verifier GateDenseRound.exampleConfig GateDenseRound.exampleGates
      GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha exampleCommit
      GateDenseRound.example_configuration exampleStart GateDenseRound.exampleState
      example_lockstep [[], []] rfl
  exact ⟨v', s', sent, chals, hrun, hcomplete, by simpa using hext, hsl, hcl, h5, hvv, hgp⟩

/-- (d) The initial-claim equivalence has CONTENT: because this instance's gate
cube sum is nonzero, its honest prover is NOT in lockstep with the source's ZERO
initial gate claim.  `chain_initial_claim` is therefore not a tautology. -/
theorem example_not_lockstep_with_source_zero (i : Verifier.Initial) :
    ¬ Lockstep GateDenseRound.exampleConfig GateDenseRound.exampleGates
        GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha (Verifier.start i)
        GateDenseRound.exampleState := by
  intro hl
  exact GateDenseRound.example_nonzero.2.2.2.1
    ((chain_initial_claim GateDenseRound.exampleConfig GateDenseRound.exampleGates
      GateDenseRound.examplePublicHash GateDenseRound.exampleAlpha i GateDenseRound.exampleState
      GateDenseRound.example_consistent (by decide)).mp hl)

end Audit.Wire3.GateClaimChain
