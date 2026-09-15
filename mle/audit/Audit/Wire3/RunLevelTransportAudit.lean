import Audit.Wire3.RawBlockLanes

/-!
# THE RUN-LEVEL TRANSPORT: THE PER-ROUND UNION *IS* THE RUN'S OWN BAD-DRAW EVENT

## THE ONE SENTENCE THIS MODULE IS ABOUT

The adopted `StrategyChainBound` HONESTY (iii) ends:

  "Section 3 is the one-stage form of that transport; the whole-schedule form, and
   therefore the adaptive run-level bound, is NOT proved here."

The adopted `RawBlockLanes` closed the PER-ROUND half of that item -- its
`strategic_raw_full_bad_draw_probability_le` bounds the mass of an event
`rawFullBadEvent` defined directly on the oracle table -- and its HONESTY (vi)
records what was left: "What is bounded below is an event defined directly on the
oracle table, not `runDrawEvent` at a `jointBadEvent`."

THIS MODULE CLOSES THAT REMAINDER, AND IT TURNS OUT NOT TO NEED A WHOLE-SCHEDULE
UNIFORMITY STATEMENT AT ALL.  What it needs is an IDENTIFICATION OF EVENTS, and
the identification is exact:

  `rawFullBadEvent ... = adaptiveRunDrawEvent ...`   (`raw_full_bad_event_is_adaptive_run_draw_event`)

where `adaptiveRunDrawEvent` is the adopted `RandomOracleSqueezes.runDrawEvent`
shape

  `{ T | InstalledRoundCommit.actualDigestDraw (hashOf Q T) c p ∈ JointChallengeSpace.jointBadEvent d ... }`

with the FIXED `Verifier.Proof p` replaced by the proof the strategy actually
submits at the table `T`, and the FIXED lane lists replaced by the lane rounds it
actually plays there.  Both replacements are legitimate because the event is
defined TABLE BY TABLE; they are exactly the replacements the adopted
`ConcreteChainThreading.run_bad_draw_probability_le_birthday` cannot make, because
it quantifies `p` and the two lane lists OUTSIDE the law.

Consequently `adaptive_run_level_bad_draw_probability_le` is the adopted
fixed-prover headline with the fixed data realized:

  `oracleProbability (boundedQueries L) (adaptiveRunDrawEvent ...)`
    `<= ChallengeUnionBound.combinedBound degreeBits q degreeBits constraints`
      `+ (22 + 5 degreeBits) (22 + 5 degreeBits + 1) / 2 / |Block|`,

for EVERY transcript-restricted prover obeying the protocol's causality.

## WHY NO WHOLE-SCHEDULE UNIFORMITY IS NEEDED

`run_level_event_is_a_union_of_one_stage_events` writes the run-level event out:
it is the union, over the coupled rounds, of the two per-round events AT THAT
ROUND'S OWN STAGE, together with the two block-`0` events at the derive stage.
Each summand is measured by the adopted
`OuterLaneTransport.stage_triple_target_mass_le` -- a ONE-STAGE fresh step
conditioned on the chain's no-clash event up to that stage -- and the conditioning
events NEST (`OuterLaneTransport.stage_no_clash_mono`), so ONE clash term pays for
all of them.  A union bound needs the per-summand masses and nothing else; it never
needs the joint law of the whole schedule.  The whole-schedule product law the
adopted header reached for would have been a STRONGER statement than the union
bound consumes, and it is not available by the route this tree has: the adopted
`OuterLaneTransport.StageStable` closure that the exact fibre count rests on is
proved only for the stage's OWN counters (`stage_stable_no_clash`); no adopted
lemma gives closure of the chain's no-clash event up to stage `n` under
overwriting a challenge answer at a stage below `n` (the strategy reads that
answer and the later stage digests move with it), so the `StageStable` route to an
exact product law is not open.  Whether that law holds is NOT settled either way
here: no counterexample table is constructed below, that limitation is recorded
as prose, not as a theorem, and nothing below depends on it either way.

## WHAT IS PROVED

1. THE REALIZED DRAW (section 1).  `realizedDraw` is the point of the adopted
   `JointChallengeSpace.JointSpace` whose coordinates are the digest triples the
   STRATEGY CHAIN actually reads: coupled round `r`'s log and gate triples at the
   adopted `OuterLaneTransport.roundStage r`, counters `0` and `3`, and the gate
   alpha and the whole gate tau column at the adopted
   `ReducedFullTransport.deriveStage`, at the adopted
   `JointChallengeSpace.sourceCounter` labels.
2. THE REALIZED LANE ROUNDS (section 2).  `realizedRounds` is the
   `List ConditionalSoundness.LaneRound` a raw lane produces AT ONE TABLE: round
   `k`'s message and truth at the raw view, and round `k`'s `challenge` field the
   REDUCED triple the run really squeezed.  This is the frozen-lane data of the
   adopted `JointChallengeSpace` instantiated at table-dependent lists.
3. THE PER-ROUND IDENTIFICATION (sections 3 and 4).  `raw_round_is_coord_event`
   identifies the adopted `RawBlockLanes.rawRoundBadEvent` with the adopted
   `JointChallengeSpace.coordEvent` at the realized draw -- the `challenge` field
   is not read by the adopted `ConditionalSoundness.roundBadSet`, so the raw bad
   set and the lane-round bad set are the same `Finset`.
   `lane_event_is_raw_round_union` is the induction over the rounds, and
   `raw_outer_bad_event_is_run_level_event` the resulting `Finset` equality.
4. THE BLOCK-`0` LANES AND THE FULL EVENT (section 5).  `gate_tau_is_run_level` and
   `gate_alpha_is_run_level` identify the adopted
   `ReducedFullTransport.gateTauBadEvent` / `gateAlphaBadEvent` with the tau block
   and the alpha coordinate of the realized draw, and
   `raw_full_bad_event_is_run_level_event` assembles the three.
5. THE TRANSPORT (section 6).  `realizedProof` is the proof object a strategic
   prover submits at one table and `realizedRunProof` is it at the adopted
   `StrategyChainBound.realizedMessages`.  `strategic_base_digest` and
   `strategic_chain_digest` identify the adopted
   `RandomOracleSqueezes.sourceDigest` of the run at THAT proof with the chain's
   own stage digests -- the adopted
   `ConcreteChainThreading.run_round_digest_is_chain_digest` and
   `StrategyChainBound.strategic_prover_chain_is_strategy_chain`,
   `strategic_prover_chain_base` and the adopted
   `OuterInitial.derived_final_digest` -- and
   `realized_draw_is_actual_digest_draw` concludes

     `realizedDraw ... c.degreeBits T`
       `= InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c (realizedRunProof ... T)`,

   coordinate for coordinate.  THE RUN'S OWN DRAW, AT THE PROOF THE PROVER REALLY
   SENT.
6. THE HEADLINES (section 7).  `raw_full_bad_event_is_adaptive_run_draw_event`,
   `adaptive_run_level_bad_draw_probability_le` and the paired
   `strategic_adaptive_run_level_bad_draw_probability_le`, whose lanes are the
   prover's own.
7. NON-VACUITY AND THE CLOSED INSTANCE (sections 8 and 9).
   `realized_draw_at_constant_table_is_constant` computes the realized draw at the
   adopted `BirthdayClashBound.constantTable` -- every coordinate collapses to the
   same triple, which is why `constant_table_outside_the_conditioner` puts that
   table in the complement the birthday term pays for.
   `degree_bits_thirteen_is_satisfiable` records that `c.degreeBits = 13` is
   inhabited by the adopted `ConcreteChainThreading.budgetConfig`, and
   `adaptive_run_level_bound_at_thirteen` is the closed instance at the adopted
   `StrategyChainBound.challengeTruncatedMessage` and its own two raw lanes,

     `<= ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / |Block|`,

   with `adaptive_run_level_bound_at_thirteen_lt_one` recording that it is below
   `1`.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  The fresh-query
lemma the whole argument rests on, the adopted
`BirthdayClashBound.fresh_coordinate_probability`, is the DEFINING property of a
random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed permutation by a table drawn from this law is an assumption with no proof
anywhere in this tree.

(ii) THE PROVER IS TRANSCRIPT-RESTRICTED, AND GRINDING IS EXCLUDED.  A
`StrategyChainBound.Strategy` is handed the stage digests of its own chain and the
oracle's answers at the CHALLENGE inputs of those digests, and nothing else: IT
MAKES NO ORACLE QUERIES OF ITS OWN.  A random-oracle-model Fiat--Shamir prover that
hashes candidate payloads itself and keeps the one whose digest collides --
GRINDING -- is NOT covered by anything below.  Identifying the per-round union with
the run's own draw event changes nothing about that restriction.

(iii) ROUND CAUSALITY IS A HYPOTHESIS, AND IT IS THE PROTOCOL'S.  The adopted
`StrategyChainBound.RoundCausal` and `RawBlockLanes.RawCausal` ask that round `r`'s
message read only the stages up to `22 + 5 r` -- the digest round `r`'s own two
challenges are squeezed from.  A "prover" whose round-`r` message read round `r`'s
own challenge would be reading the future.  Nothing stronger is assumed and nothing
weaker would do.

(iv) THE LANES ARE THE OUTER SUMCHECK LANES PLUS THE ADOPTED BLOCK-`0` ONES, AND
THE INDEX LANES ARE NOT INCLUDED.  The constant is the whole adopted
`ChallengeUnionBound.combinedBound` -- the outer term, the gate tau column and the
gate alpha row union -- AND NO OTHER TERM.  The index lanes of the adopted
`ReducedIndexLanes` are transported in a SIBLING CANDIDATE MODULE, not here; until
that lands, `2 * ChallengeUnionBound.tauTerm indexBits` is NOT part of any constant
below, and neither are the WHIR folding transcript and the Merkle openings, which
are not in `combinedBound` at all.  The joint bad event below is therefore the
OUTER-plus-block-`0` one, and the run's index draws are not among its coordinates:
the adopted `JointChallengeSpace.Draw` has no index coordinate.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The bound is on the mass of
one named event under the oracle law.  The meaning of the per-round bad sets is the
adopted `ConditionalSoundness` one -- GOOD-DRAW-CONDITIONAL, with that module's
assumption list untouched -- and nothing here instantiates it.  The running claims
and the honest round messages are FREE PARAMETERS in every theorem below.  Quoting
the number of section 9 as the wire-v3 soundness error would be wrong.

(vi) NO ADAPTIVE FIAT--SHAMIR SOUNDNESS IS PROVED, AND NO LAW IS ATTACHED TO THE
RUN'S DRAW.  What is proved below is that the mass of the event "the run's own
`actualDigestDraw` lands in the adopted `jointBadEvent` of the messages the prover
actually sent" is small under the ORACLE-TABLE law.  That is NOT the statement
that the run's draw is `JointChallengeSpace.jointProbability`-distributed: the
adopted `JointChallengeSpace.DrawEncodesRun` remains a COORDINATE statement, half
(B) of the Fiat--Shamir reading remains exactly as unformalized as that module's
header says, and the adopted
`RandomOracleSqueezes.run_draw_probability_le_fibrewise` Fubini -- which does not
survive a table-dependent proof -- is NOT used anywhere below.  NOTHING BELOW IS A
CLAIM THAT ADAPTIVE FIAT--SHAMIR SOUNDNESS HAS BEEN ESTABLISHED.

(vii) THE REALIZED PROOF IS A WITNESS, NOT THE WHOLE PROVER.  `realizedProof` is
`{ Verifier.testProof with ... }`: it overrides `circuitDigest`, `publicInputs`,
`preprocessedRoot`, `witnessRoot`, `normInverseRoot`, `logRounds` and `gateRounds`,
and INHERITS `used`, `whirTranscript`, `whirHints`, `protocolVersion` and
`constituentWidth` from the fixture.  So it is NOT a model of an adversary's WHIR
behaviour.  That is sound FOR THE THEOREMS OF THIS MODULE, every one of which reads
the proof only through `Verifier.statement` and `BirthdayClashBound.roundMessages`,
and none of which asserts `Verifier.shape` for it.  IT IS NOT SOUND DOWNSTREAM, AND
THE ADOPTED `AdaptiveAssemblyFailure` BREACHES IT IN TWO SEPARATE WAYS.  FIRST, A
FIXTURE FIELD IS READ: that module's `suppliedCellsAt` reads `p.used` of this
record, so its index bad event depends on a constant the fixture supplies rather
than on anything a prover chooses.  SECOND, THE SHAPE IS ASSERTED: its
`adaptiveAssemblyFailureEvent` has `Integrated.verify ... = Except.ok ()` as a
conjunct, and acceptance subsumes `Verifier.shape pin c p = true`
(`Integrated.lean:59-66`, `Verifier.lean:415`) -- which at the inherited `used`
record forces `numWires = 1`, `numRouted = 0`, `numConstants = 1`
(`Verifier.lean:139-141`, `Verifier.lean:596-600`) and so empties that event at
every other configuration.  ANY DOWNSTREAM MODULE THAT READS A FIXTURE-INHERITED
FIELD OF THIS RECORD, OR THAT ASSERTS SHAPE OR ACCEPTANCE FOR IT, MUST MAKE THAT
FIELD A PARAMETER OR DISCLOSE THE RESULTING VACUITY.  The adopted
`IndexHalfTransport` does the former (`realizedRunProofWith`) and records the
latter.

(viii) THE CONFIGURATION DATA IS FIXED DATA.  `g`, `coeffsOf` and `rows` are bound
OUTSIDE the oracle law in every theorem, and no theorem lets the prover choose them
after seeing a challenge.  The counter labels `0` and `3` for the two coupled
challenges are documented, not derived, for the abstract `Verifier.Engine` the
adopted modules quantify over; this module inherits that caveat.

(ix) DISCLOSED SHAPE NOTES.  `Finset.univ` appears in this module's OWN definitions
(`runLevelOuterEvent`, `runLevelBadEvent`, `adaptiveRunDrawEvent`) and in the
statement of no theorem.  No tactic or term below ever puts `Finset.univ` on `Element`,
on `OuterChallenge.DigestTriple` or on `JointChallengeSpace.JointSpace` in a
position that can be reduced, and no cardinality of `Block`, `Element` or
`OuterChallenge.DigestTriple` is ever evaluated.  This module imports
`Audit.Wire3.RawBlockLanes` and nothing else, and no Mathlib module directly.
-/

namespace Audit.Wire3.RunLevelTransportAudit

open Audit.Wire3
open Audit.Wire3.GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport
open Audit.Wire3.RawBlockLanes

/-! ## 1. THE RUN'S REALIZED DRAW, ON THE ORACLE TABLE -/

def drawStage (d : Nat) : JointChallengeSpace.Draw d → Nat
  | JointChallengeSpace.Draw.gateAlpha => deriveStage
  | JointChallengeSpace.Draw.gateTau _ => deriveStage
  | JointChallengeSpace.Draw.outerLog r => roundStage r.val
  | JointChallengeSpace.Draw.outerGate r => roundStage r.val

def realizedDraw (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) :
    JointChallengeSpace.JointSpace d :=
  fun k => stageTriple L hL e0 strat hb (drawStage d k) (JointChallengeSpace.sourceCounter d k) T

theorem realized_draw_outer_log (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) (r : Fin d) :
    realizedDraw L hL e0 strat hb d T (JointChallengeSpace.Draw.outerLog r)
      = stageTriple L hL e0 strat hb (roundStage r.val) 0 T := rfl

theorem realized_draw_outer_gate (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) (r : Fin d) :
    realizedDraw L hL e0 strat hb d T (JointChallengeSpace.Draw.outerGate r)
      = stageTriple L hL e0 strat hb (roundStage r.val) 3 T := rfl

theorem realized_draw_gate_alpha (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) :
    realizedDraw L hL e0 strat hb d T JointChallengeSpace.Draw.gateAlpha
      = stageTriple L hL e0 strat hb deriveStage (alphaBase d) T := rfl

theorem realized_draw_gate_tau (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) (i : Fin d) :
    realizedDraw L hL e0 strat hb d T (JointChallengeSpace.Draw.gateTau i)
      = stageTriple L hL e0 strat hb deriveStage (tauBase d i.val) T := rfl

theorem realized_draw_log_proj (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) (j : Nat)
    (hj : j < d) :
    realizedDraw L hL e0 strat hb d T (JointChallengeSpace.logProj d j)
      = stageTriple L hL e0 strat hb (roundStage j) 0 T := by
  rw [JointChallengeSpace.logProj_apply d j hj]
  rfl

theorem realized_draw_gate_proj (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (T : OracleTable (boundedQueries L)) (j : Nat)
    (hj : j < d) :
    realizedDraw L hL e0 strat hb d T (JointChallengeSpace.gateProj d j)
      = stageTriple L hL e0 strat hb (roundStage j) 3 T := by
  rw [JointChallengeSpace.gateProj_apply d j hj]
  rfl

/-! ## 2. THE REALIZED LANE ROUNDS -/

def realizedRounds (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) : Nat → Nat → List ConditionalSoundness.LaneRound
  | _, 0 => []
  | k, n + 1 =>
      ⟨lane.message k (tableView L hL e0 strat hb T),
        lane.truth k (tableView L hL e0 strat hb T),
        OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) base T)⟩ ::
        realizedRounds L hL e0 strat hb lane base T (k + 1) n

theorem realized_rounds_cons (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) (k n : Nat) :
    realizedRounds L hL e0 strat hb lane base T k (n + 1)
      = (⟨lane.message k (tableView L hL e0 strat hb T),
          lane.truth k (tableView L hL e0 strat hb T),
          OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) base T)⟩ :
            ConditionalSoundness.LaneRound) ::
          realizedRounds L hL e0 strat hb lane base T (k + 1) n := rfl

theorem realized_rounds_length (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ (n k : Nat), (realizedRounds L hL e0 strat hb lane base T k n).length = n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro k
      rw [realized_rounds_cons, List.length_cons, ih (k + 1)]

theorem realized_rounds_mem (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (bd base : Nat)
    (hbd : RawLaneBounded lane bd) (T : OracleTable (boundedQueries L)) :
    ∀ (n k : Nat), ∀ r ∈ realizedRounds L hL e0 strat hb lane base T k n,
      r.message.length ≤ bd ∧ r.truth.length ≤ bd := by
  intro n
  induction n with
  | zero => intro k r hr; exact absurd hr (List.not_mem_nil r)
  | succ n ih =>
      intro k r hr
      rw [realized_rounds_cons, List.mem_cons] at hr
      rcases hr with hr | hr
      · subst hr
        exact hbd k (tableView L hL e0 strat hb T)
      · exact ih (k + 1) r hr

/-! ## 3. THE PER-ROUND EVENT IS THE COORDINATE EVENT OF THE REALIZED DRAW -/

theorem lane_event_nil (d : Nat) (proj : Nat → JointChallengeSpace.Draw d) (a b : Element)
    (k : Nat) :
    JointChallengeSpace.laneEvent d proj a b [] k
      = (∅ : Finset (JointChallengeSpace.JointSpace d)) := rfl

theorem lane_event_cons (d : Nat) (proj : Nat → JointChallengeSpace.Draw d) (a b : Element)
    (r : ConditionalSoundness.LaneRound) (rs : List ConditionalSoundness.LaneRound) (k : Nat) :
    JointChallengeSpace.laneEvent d proj a b (r :: rs) k
      = JointChallengeSpace.coordEvent d (proj k) (ConditionalSoundness.roundBadSet a b r) ∪
          JointChallengeSpace.laneEvent d proj (OuterRound.evaluate a r.message r.challenge)
            (OuterRound.evaluate b r.truth r.challenge) rs (k + 1) := rfl

theorem mem_raw_round_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base r : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ rawRoundBadEvent L hL e0 strat hb lane base r ↔
      OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage r) base T)
        ∈ rawBadSet L hL e0 strat hb lane base r T := by
  rw [rawRoundBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact JointChallengeSpace.mem_tupleEvent _ _

/-- (3) **ROUND `k`'s RAW EVENT IS THE JOINT COORDINATE EVENT AT THE REALIZED DRAW.** -/
theorem raw_round_is_coord_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (base d : Nat)
    (proj : Nat → JointChallengeSpace.Draw d) (T : OracleTable (boundedQueries L)) (k : Nat)
    (hk : realizedDraw L hL e0 strat hb d T (proj k)
      = stageTriple L hL e0 strat hb (roundStage k) base T) (ch : Element) :
    (realizedDraw L hL e0 strat hb d T ∈
        JointChallengeSpace.coordEvent d (proj k)
          (ConditionalSoundness.roundBadSet (rawClaims L hL e0 strat hb lane base T k).1
            (rawClaims L hL e0 strat hb lane base T k).2
            ⟨lane.message k (tableView L hL e0 strat hb T),
              lane.truth k (tableView L hL e0 strat hb T), ch⟩))
      ↔ T ∈ rawRoundBadEvent L hL e0 strat hb lane base k := by
  rw [JointChallengeSpace.mem_coordEvent, hk, mem_raw_round_bad_event]
  exact Iff.rfl

/-- (3) **THE LANE EVENT AT THE REALIZED LANE ROUNDS IS THE UNION OF THE RAW ROUND
EVENTS.** -/
theorem lane_event_is_raw_round_union (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (base d : Nat)
    (proj : Nat → JointChallengeSpace.Draw d) (T : OracleTable (boundedQueries L))
    (hproj : ∀ j, j < d → realizedDraw L hL e0 strat hb d T (proj j)
      = stageTriple L hL e0 strat hb (roundStage j) base T) :
    ∀ (n k : Nat), k + n ≤ d →
      (realizedDraw L hL e0 strat hb d T ∈
          JointChallengeSpace.laneEvent d proj (rawClaims L hL e0 strat hb lane base T k).1
            (rawClaims L hL e0 strat hb lane base T k).2
            (realizedRounds L hL e0 strat hb lane base T k n) k
        ↔ ∃ i, i < n ∧ T ∈ rawRoundBadEvent L hL e0 strat hb lane base (k + i)) := by
  intro n
  induction n with
  | zero =>
      intro k _
      rw [realizedRounds, lane_event_nil]
      constructor
      · intro h
        exact absurd h (Finset.not_mem_empty _)
      · rintro ⟨i, hi, -⟩
        exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro k hk
      have hkd : k < d := by omega
      have hcl1 : OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T k).1
            (lane.message k (tableView L hL e0 strat hb T))
            (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) base T))
          = (rawClaims L hL e0 strat hb lane base T (k + 1)).1 := rfl
      have hcl2 : OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T k).2
            (lane.truth k (tableView L hL e0 strat hb T))
            (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) base T))
          = (rawClaims L hL e0 strat hb lane base T (k + 1)).2 := rfl
      have hhead := raw_round_is_coord_event L hL e0 strat hb lane base d proj T k
        (hproj k hkd)
        (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) base T))
      have htail := ih (k + 1) (by omega)
      rw [realized_rounds_cons, lane_event_cons]
      show (realizedDraw L hL e0 strat hb d T ∈
          JointChallengeSpace.coordEvent d (proj k)
            (ConditionalSoundness.roundBadSet (rawClaims L hL e0 strat hb lane base T k).1
              (rawClaims L hL e0 strat hb lane base T k).2
              ⟨lane.message k (tableView L hL e0 strat hb T),
                lane.truth k (tableView L hL e0 strat hb T),
                OuterChallenge.reduceTriple
                  (stageTriple L hL e0 strat hb (roundStage k) base T)⟩) ∪
          JointChallengeSpace.laneEvent d proj
            (OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T k).1
              (lane.message k (tableView L hL e0 strat hb T))
              (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) base T)))
            (OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T k).2
              (lane.truth k (tableView L hL e0 strat hb T))
              (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage k) base T)))
            (realizedRounds L hL e0 strat hb lane base T (k + 1) n) (k + 1)) ↔ _
      rw [hcl1, hcl2, Finset.mem_union, hhead, htail]
      constructor
      · rintro (h | ⟨i, hi, hmem⟩)
        · exact ⟨0, Nat.succ_pos n, by rw [Nat.add_zero]; exact h⟩
        · refine ⟨i + 1, by omega, ?_⟩
          rw [show k + (i + 1) = k + 1 + i from by omega]
          exact hmem
      · rintro ⟨i, hi, hmem⟩
        cases i with
        | zero =>
            refine Or.inl ?_
            rw [Nat.add_zero] at hmem
            exact hmem
        | succ i2 =>
            refine Or.inr ⟨i2, by omega, ?_⟩
            rw [show k + 1 + i2 = k + (i2 + 1) from by omega]
            exact hmem

/-! ## 4. THE OUTER EVENT -/

/-- (4) The lane event at the realized rounds, started from the lane's own claims. -/
theorem outer_lane_event_iff (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base d : Nat)
    (proj : Nat → JointChallengeSpace.Draw d) (T : OracleTable (boundedQueries L))
    (hproj : ∀ j, j < d → realizedDraw L hL e0 strat hb d T (proj j)
      = stageTriple L hL e0 strat hb (roundStage j) base T)
    (a b : Element) (ha : lane.claim = a) (hbb : lane.truthClaim = b) :
    (realizedDraw L hL e0 strat hb d T ∈
        JointChallengeSpace.laneEvent d proj a b
          (realizedRounds L hL e0 strat hb lane base T 0 d) 0)
      ↔ ∃ i, i < d ∧ T ∈ rawRoundBadEvent L hL e0 strat hb lane base i := by
  subst ha
  subst hbb
  have h := lane_event_is_raw_round_union L hL e0 strat hb lane base d proj T hproj d 0 (by omega)
  simp only [Nat.zero_add] at h
  exact h

open Classical in
/-- **THE RUN-LEVEL OUTER EVENT.**  The tables at which the RUN'S OWN joint draw --
the digest triples the chain actually squeezes -- lands in the adopted
`JointChallengeSpace.outerEvent` of the lane rounds the prover actually played. -/
noncomputable def runLevelOuterEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane) (d : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => realizedDraw L hL e0 strat hb d T ∈
    JointChallengeSpace.outerEvent d logLane.truthClaim gateLane.truthClaim
      (realizedRounds L hL e0 strat hb logLane 0 T 0 d)
      (realizedRounds L hL e0 strat hb gateLane 3 T 0 d))

open Classical in
theorem mem_run_level_outer_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane) (d : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ runLevelOuterEvent L hL e0 strat hb logLane gateLane d ↔
      realizedDraw L hL e0 strat hb d T ∈
        JointChallengeSpace.outerEvent d logLane.truthClaim gateLane.truthClaim
          (realizedRounds L hL e0 strat hb logLane 0 T 0 d)
          (realizedRounds L hL e0 strat hb gateLane 3 T 0 d) := by
  rw [runLevelOuterEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- (4) **THE RAW OUTER BAD EVENT IS THE RUN-LEVEL OUTER EVENT.**  Finset for
Finset, at every strategy and every pair of raw lanes whose claimed running claim
starts at `0` -- the adopted `JointChallengeSpace.outerEvent` convention. -/
theorem raw_outer_bad_event_is_run_level_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane) (d : Nat)
    (hlc : logLane.claim = 0) (hgc : gateLane.claim = 0) :
    rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      = runLevelOuterEvent L hL e0 strat hb logLane gateLane d := by
  ext T
  rw [mem_run_level_outer_event, JointChallengeSpace.outerEvent, Finset.mem_union,
    outer_lane_event_iff L hL e0 strat hb logLane 0 d (JointChallengeSpace.logProj d) T
      (fun j hj => realized_draw_log_proj L hL e0 strat hb d T j hj) 0 logLane.truthClaim hlc rfl,
    outer_lane_event_iff L hL e0 strat hb gateLane 3 d (JointChallengeSpace.gateProj d) T
      (fun j hj => realized_draw_gate_proj L hL e0 strat hb d T j hj) 0 gateLane.truthClaim hgc rfl,
    rawOuterBadEvent, Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hmem⟩
    rw [Finset.mem_range] at hr
    rw [rawBothBadEvent, Finset.mem_union] at hmem
    rcases hmem with hmem | hmem
    · exact Or.inl ⟨r, hr, hmem⟩
    · exact Or.inr ⟨r, hr, hmem⟩
  · rintro (⟨i, hi, hmem⟩ | ⟨i, hi, hmem⟩)
    · exact ⟨i, Finset.mem_range.mpr hi, Finset.mem_union.mpr (Or.inl hmem)⟩
    · exact ⟨i, Finset.mem_range.mpr hi, Finset.mem_union.mpr (Or.inr hmem)⟩

/-! ## 5. THE BLOCK-`0` LANES AND THE FULL EVENT -/

/-- (5) The adopted gate tau event is the tau block of the realized draw. -/
theorem gate_tau_is_run_level (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d : Nat) (g : Nat → Element)
    (T : OracleTable (boundedQueries L)) :
    realizedDraw L hL e0 strat hb d T ∈ JointChallengeSpace.tauBadEvent d g ↔
      T ∈ gateTauBadEvent L hL e0 strat hb d g := by
  rw [JointChallengeSpace.tauBadEvent, JointChallengeSpace.mem_tauEvent,
    mem_gate_tau_bad_event]
  exact Iff.rfl

/-- (5) The adopted gate alpha event is the alpha coordinate of the realized draw. -/
theorem gate_alpha_is_run_level (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (d rows : Nat) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    realizedDraw L hL e0 strat hb d T ∈ JointChallengeSpace.alphaBadEvent d rows coeffsOf ↔
      T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf := by
  rw [JointChallengeSpace.alphaBadEvent, JointChallengeSpace.mem_coordEvent,
    mem_gate_alpha_bad_event]
  exact Iff.rfl

open Classical in
/-- **THE RUN-LEVEL BAD EVENT.**  The tables at which the run's OWN joint draw lands
in the adopted `JointChallengeSpace.jointBadEvent` of the lane rounds the prover
actually played at that table.  This is the adopted
`RandomOracleSqueezes.runDrawEvent` shape with the FIXED proof and the FIXED lane
lists replaced by their table-dependent realizations. -/
noncomputable def runLevelBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => realizedDraw L hL e0 strat hb d T ∈
    JointChallengeSpace.jointBadEvent d logLane.truthClaim gateLane.truthClaim
      (realizedRounds L hL e0 strat hb logLane 0 T 0 d)
      (realizedRounds L hL e0 strat hb gateLane 3 T 0 d) g rows coeffsOf)

open Classical in
theorem mem_run_level_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ runLevelBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf ↔
      realizedDraw L hL e0 strat hb d T ∈
        JointChallengeSpace.jointBadEvent d logLane.truthClaim gateLane.truthClaim
          (realizedRounds L hL e0 strat hb logLane 0 T 0 d)
          (realizedRounds L hL e0 strat hb gateLane 3 T 0 d) g rows coeffsOf := by
  rw [runLevelBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- (5) **THE HEADLINE IDENTIFICATION.**  The adopted `RawBlockLanes.rawFullBadEvent`
IS, as a `Finset` of oracle tables, the run-level event "the run's joint draw lands
in the joint bad event of the lane rounds the prover actually played".  The
per-round union on the table and the disjunction on the adopted
`JointChallengeSpace.JointSpace` are the same set. -/
theorem raw_full_bad_event_is_run_level_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hlc : logLane.claim = 0) (hgc : gateLane.claim = 0) :
    rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
      = runLevelBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf := by
  ext T
  rw [mem_raw_full_bad_event, mem_run_level_bad_event, JointChallengeSpace.mem_jointBadEvent,
    ← gate_tau_is_run_level L hL e0 strat hb d g T,
    ← gate_alpha_is_run_level L hL e0 strat hb d rows coeffsOf T,
    ← mem_run_level_outer_event L hL e0 strat hb logLane gateLane d T,
    ← raw_outer_bad_event_is_run_level_event L hL e0 strat hb logLane gateLane d hlc hgc]

/-! ## 6. THE TRANSPORT: THE REALIZED DRAW IS THE RUN'S `actualDigestDraw` -/

theorem zip_map_fst_snd : ∀ (ms : List Verifier.CoupledMessage),
    (ms.map Prod.fst).zip (ms.map Prod.snd) = ms
  | [] => rfl
  | m :: ms => by
      show (m.1, m.2) :: (ms.map Prod.fst).zip (ms.map Prod.snd) = m :: ms
      rw [zip_map_fst_snd ms]

/-- **THE PROOF OBJECT A STRATEGIC PROVER SUBMITS AT ONE TABLE.**  The adopted
`Verifier.testProof` carrying the statement `s` and the coupled messages `ms`; the
fields no transcript frame of the outer chain reads are the adopted witness's. -/
def realizedProof (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) : Verifier.Proof :=
  { Verifier.testProof with
      circuitDigest := s.circuitDigest, publicInputs := s.publicInputs,
      preprocessedRoot := s.preprocessedRoot, witnessRoot := s.witnessRoot,
      normInverseRoot := s.normInverseRoot,
      logRounds := ms.map Prod.fst, gateRounds := ms.map Prod.snd }

theorem realized_proof_statement (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) :
    Verifier.statement (realizedProof s ms) = s := rfl

theorem realized_proof_round_messages (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) : roundMessages (realizedProof s ms) = ms :=
  zip_map_fst_snd ms

/-- **THE PROOF THE STRATEGIC PROVER ACTUALLY SUBMITS AT THE TABLE `T`.**  Its
round messages are the adopted `StrategyChainBound.realizedMessages` -- a
TABLE-DEPENDENT list, which is exactly what the adopted fixed-prover theorems
cannot quantify inside the law. -/
def realizedRunProof (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) : Verifier.Proof :=
  realizedProof s (realizedMessages L hL c s S hb N T)

theorem realized_run_proof_round_messages (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    roundMessages (realizedRunProof L hL c s S hb N T)
      = realizedMessages L hL c s S hb N T :=
  realized_proof_round_messages s _

theorem realized_run_proof_length (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    (roundMessages (realizedRunProof L hL c s S hb N T)).length = N := by
  rw [realized_run_proof_round_messages, realized_messages_length]

/-- The chain model does not see which proof of the same statement and the same
messages it is run at, and it does not see which proof of the length budget it is
handed. -/
theorem frame_state_congr (L : Nat) (e0 : Transcript.Digest)
    (sh1 sh2 : Nat → Transcript.Byte × Transcript.Bytes) (h : sh1 = sh2)
    (h1 : ∀ k, 61 + (sh1 k).2.length ≤ L) (h2 : ∀ k, 61 + (sh2 k).2.length ≤ L)
    (k : Nat) (T : OracleTable (boundedQueries L)) :
    frameState L e0 sh1 h1 k T = frameState L e0 sh2 h2 k T := by
  subst h
  rfl

theorem realized_run_proof_shape (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    prefixRoundShape c (Verifier.statement (realizedRunProof L hL c s S hb N T))
        (roundMessages (realizedRunProof L hL c s S hb N T))
      = prefixRoundShape c s (realizedMessages L hL c s S hb N T) := by
  rw [realized_run_proof_round_messages]
  rfl

theorem realized_run_proof_hlen (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ k, 61 + (prefixRoundShape c (Verifier.statement (realizedRunProof L hL c s S hb N T))
      (roundMessages (realizedRunProof L hL c s S hb N T)) k).2.length ≤ L := by
  rw [realized_run_proof_round_messages]
  exact strategic_hlen_of_bounded L hL c s S hb N T

/-- (6) **THE RUN'S RELATION-STATE DIGEST IS THE CHAIN'S STAGE-`22` DIGEST.**  The
adopted `StrategyChainBound.strategic_prover_chain_base` and the adopted
`OuterInitial.derived_final_digest`: the alpha and tau squeezes are taken from the
same digest the twenty-two prefix frames end at. -/
theorem strategic_base_digest (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    InstalledRoundCommit.actualBase (hashOf (boundedQueries L) T) c
        (realizedRunProof L hL c s S hb N T)
      = strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb deriveStage T := by
  rw [deriveStage, strategic_prover_chain_base L hL c s S hb hS N T]
  exact (OuterInitial.derived_final_digest (hashOf (boundedQueries L) T) c s).symm

/-- (6) **THE RUN'S ROUND-`r` SQUEEZE SOURCE IS THE CHAIN'S STAGE-`roundStage r`
DIGEST**, at the proof the strategy actually submits.  This is the adopted
`ConcreteChainThreading.run_round_digest_is_chain_digest` composed with the adopted
`StrategyChainBound.strategic_prover_chain_is_strategy_chain`, at a
TABLE-DEPENDENT proof. -/
theorem strategic_chain_digest (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (T : OracleTable (boundedQueries L)) (r : Fin c.degreeBits) :
    RandomOracleSqueezes.sourceDigest (hashOf (boundedQueries L) T) c
        (realizedRunProof L hL c s S hb c.degreeBits T) (JointChallengeSpace.Draw.outerLog r)
      = strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (roundStage r.val) T := by
  rw [ConcreteChainThreading.run_round_digest_is_chain_digest L c
      (realizedRunProof L hL c s S hb c.degreeBits T)
      (realized_run_proof_hlen L hL c s S hb c.degreeBits T)
      (realized_run_proof_length L hL c s S hb c.degreeBits T) T r,
    strategic_prover_chain_is_strategy_chain L hL c s S hb hS c.degreeBits T
      (roundStage r.val) (by rw [roundStage]; have := r.isLt; omega)]
  exact frame_state_congr L OuterInitial.zeroDigest _ _
    (realized_run_proof_shape L hL c s S hb c.degreeBits T) _ _ _ T

/-- (6) **THE HEADLINE TRANSPORT.**  The realized draw of section 1 IS the adopted
`InstalledRoundCommit.actualDigestDraw` of the run at the proof the strategic
prover actually submits at that table.  Every coordinate: the two coupled-round
triples at the round's own commit digest, the gate alpha and the whole gate tau
column at the relation-state digest, all at the adopted
`JointChallengeSpace.sourceCounter` labels. -/
theorem realized_draw_is_actual_digest_draw (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (T : OracleTable (boundedQueries L)) :
    realizedDraw L hL OuterInitial.zeroDigest (strategicShape c s S) hb c.degreeBits T
      = InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
          (realizedRunProof L hL c s S hb c.degreeBits T) := by
  funext k
  cases k with
  | gateAlpha =>
      have h1 : realizedDraw L hL OuterInitial.zeroDigest (strategicShape c s S) hb
            c.degreeBits T JointChallengeSpace.Draw.gateAlpha
          = stageTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hb deriveStage
              (alphaBase c.degreeBits) T := rfl
      have h2 : InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
            (realizedRunProof L hL c s S hb c.degreeBits T) JointChallengeSpace.Draw.gateAlpha
          = OuterChallenge.actualDigests (hashOf (boundedQueries L) T)
              ⟨InstalledRoundCommit.actualBase (hashOf (boundedQueries L) T) c
                (realizedRunProof L hL c s S hb c.degreeBits T), alphaBase c.degreeBits⟩ := rfl
      rw [h1, h2, stage_triple_is_actual_digests,
        strategic_base_digest L hL c s S hb hS c.degreeBits T]
  | gateTau i =>
      have h1 : realizedDraw L hL OuterInitial.zeroDigest (strategicShape c s S) hb
            c.degreeBits T (JointChallengeSpace.Draw.gateTau i)
          = stageTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hb deriveStage
              (tauBase c.degreeBits i.val) T := rfl
      have h2 : InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
            (realizedRunProof L hL c s S hb c.degreeBits T)
            (JointChallengeSpace.Draw.gateTau i)
          = OuterChallenge.actualDigests (hashOf (boundedQueries L) T)
              ⟨InstalledRoundCommit.actualBase (hashOf (boundedQueries L) T) c
                (realizedRunProof L hL c s S hb c.degreeBits T),
                tauBase c.degreeBits i.val⟩ := rfl
      rw [h1, h2, stage_triple_is_actual_digests,
        strategic_base_digest L hL c s S hb hS c.degreeBits T]
  | outerLog r =>
      have h1 : realizedDraw L hL OuterInitial.zeroDigest (strategicShape c s S) hb
            c.degreeBits T (JointChallengeSpace.Draw.outerLog r)
          = stageTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hb
              (roundStage r.val) 0 T := rfl
      have h2 : InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
            (realizedRunProof L hL c s S hb c.degreeBits T)
            (JointChallengeSpace.Draw.outerLog r)
          = OuterChallenge.actualDigests (hashOf (boundedQueries L) T)
              ⟨RandomOracleSqueezes.sourceDigest (hashOf (boundedQueries L) T) c
                (realizedRunProof L hL c s S hb c.degreeBits T)
                (JointChallengeSpace.Draw.outerLog r), 0⟩ := rfl
      rw [h1, h2, stage_triple_is_actual_digests,
        strategic_chain_digest L hL c s S hb hS T r]
  | outerGate r =>
      have h1 : realizedDraw L hL OuterInitial.zeroDigest (strategicShape c s S) hb
            c.degreeBits T (JointChallengeSpace.Draw.outerGate r)
          = stageTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hb
              (roundStage r.val) 3 T := rfl
      have h2 : InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
            (realizedRunProof L hL c s S hb c.degreeBits T)
            (JointChallengeSpace.Draw.outerGate r)
          = OuterChallenge.actualDigests (hashOf (boundedQueries L) T)
              ⟨RandomOracleSqueezes.sourceDigest (hashOf (boundedQueries L) T) c
                (realizedRunProof L hL c s S hb c.degreeBits T)
                (JointChallengeSpace.Draw.outerLog r), 3⟩ := rfl
      rw [h1, h2, stage_triple_is_actual_digests,
        strategic_chain_digest L hL c s S hb hS T r]

/-! ## 7. THE ADAPTIVE RUN-LEVEL BOUND -/

open Classical in
/-- **THE ADAPTIVE RUN-LEVEL BAD-DRAW EVENT.**  Literally the adopted
`RandomOracleSqueezes.runDrawEvent` -- "the run's own joint draw lands in the joint
bad event" -- with the FIXED `Verifier.Proof` replaced by the proof the strategy
actually submits at that table and the FIXED lane lists replaced by the lane rounds
it actually plays there.  Both replacements are legitimate because the event is
defined table by table. -/
noncomputable def adaptiveRunDrawEvent (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (logLane gateLane : RawLane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
        (realizedRunProof L hL c s S hb c.degreeBits T)
      ∈ JointChallengeSpace.jointBadEvent c.degreeBits logLane.truthClaim gateLane.truthClaim
          (realizedRounds L hL OuterInitial.zeroDigest (strategicShape c s S) hb logLane 0 T 0
            c.degreeBits)
          (realizedRounds L hL OuterInitial.zeroDigest (strategicShape c s S) hb gateLane 3 T 0
            c.degreeBits) g rows coeffsOf)

open Classical in
theorem mem_adaptive_run_draw_event (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (logLane gateLane : RawLane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ adaptiveRunDrawEvent L hL c s S hb logLane gateLane rows g coeffsOf ↔
      InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c
          (realizedRunProof L hL c s S hb c.degreeBits T)
        ∈ JointChallengeSpace.jointBadEvent c.degreeBits logLane.truthClaim gateLane.truthClaim
            (realizedRounds L hL OuterInitial.zeroDigest (strategicShape c s S) hb logLane 0 T 0
              c.degreeBits)
            (realizedRounds L hL OuterInitial.zeroDigest (strategicShape c s S) hb gateLane 3 T 0
              c.degreeBits) g rows coeffsOf := by
  rw [adaptiveRunDrawEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- (7) The run-level event of section 5 and the `actualDigestDraw` event are the
same `Finset`, by the transport of section 6. -/
theorem adaptive_run_draw_event_is_run_level_event (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (logLane gateLane : RawLane) (rows : Nat) (g : Nat → Element)
    (coeffsOf : Nat → List Element) :
    adaptiveRunDrawEvent L hL c s S hb logLane gateLane rows g coeffsOf
      = runLevelBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb logLane gateLane
          c.degreeBits rows g coeffsOf := by
  ext T
  rw [mem_adaptive_run_draw_event, mem_run_level_bad_event,
    ← realized_draw_is_actual_digest_draw L hL c s S hb hS T]

/-- (7) **THE RAW FULL BAD EVENT IS THE RUN'S OWN BAD-DRAW EVENT.**  This is the
answer to the run-level question: the per-round union on the oracle table that the
adopted `RawBlockLanes` bounds IS the event "the run's joint draw lands in the
joint bad event of the messages the prover actually sent". -/
theorem raw_full_bad_event_is_adaptive_run_draw_event (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (logLane gateLane : RawLane) (rows : Nat) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (hlc : logLane.claim = 0) (hgc : gateLane.claim = 0) :
    rawFullBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb logLane gateLane
        c.degreeBits rows g coeffsOf
      = adaptiveRunDrawEvent L hL c s S hb logLane gateLane rows g coeffsOf := by
  rw [adaptive_run_draw_event_is_run_level_event L hL c s S hb hS logLane gateLane rows g coeffsOf,
    raw_full_bad_event_is_run_level_event L hL OuterInitial.zeroDigest (strategicShape c s S) hb
      logLane gateLane c.degreeBits rows g coeffsOf hlc hgc]

/-- (7) **THE ADAPTIVE RUN-LEVEL BOUND.**  The same statement form as the adopted
fixed-prover `ConcreteChainThreading.run_bad_draw_probability_le_birthday` -- the
run's own `actualDigestDraw` weighed against the adopted
`JointChallengeSpace.jointBadEvent` -- with the FIXED proof and the FIXED lane
lists replaced by the ones the prover realizes at each table.  READ THE HONESTY
HEADER: the index lanes are not in the constant, the prover is
transcript-restricted, and this is the random-oracle model. -/
theorem adaptive_run_level_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (logLane gateLane : RawLane) (hlcau : RawLaneCausal logLane)
    (hgcau : RawLaneCausal gateLane) (hlc : logLane.claim = 0) (hgc : gateLane.claim = 0)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * c.degreeBits < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (adaptiveRunDrawEvent L hL c s S hb logLane gateLane (2 ^ c.degreeBits) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + ((22 + 5 * c.degreeBits : Nat) : ℚ) * (((22 + 5 * c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  rw [← raw_full_bad_event_is_adaptive_run_draw_event L hL c s S hb hS logLane gateLane
    (2 ^ c.degreeBits) g coeffsOf hlc hgc]
  exact raw_full_bad_draw_probability_le_combined L hL OuterInitial.zeroDigest
    (strategicShape c s S) hb logLane gateLane hlcau hgcau c.degreeBits q constraints g coeffsOf
    hdu hlog hgate hclen

/-- (7) **THE PAIRED FORM.**  The lanes are the prover's OWN, built from the
strategy by the adopted `RawBlockLanes.rawLogLaneOfStrategy` /
`rawGateLaneOfStrategy`, with the claimed running claim at the adopted `0`. -/
theorem strategic_adaptive_run_level_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hb : StrategyBounded L (strategicShape c s S))
    (trlog trgate : Nat → (Nat → Nat → Block) → List Element)
    (htrlog : RawCausal trlog) (htrgate : RawCausal trgate) (b1 b2 : Element)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * c.degreeBits < Transcript.u64Limit)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (trlog r ch).length ≤ 5)
    (hlengate : ∀ (r : Nat) (ch : Nat → Nat → Block), (trgate r ch).length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (adaptiveRunDrawEvent L hL c s S hb (rawLogLaneOfStrategy S trlog 0 b1)
          (rawGateLaneOfStrategy S trgate 0 b2) (2 ^ c.degreeBits) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + ((22 + 5 * c.degreeBits : Nat) : ℚ) * (((22 + 5 * c.degreeBits : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  adaptive_run_level_bad_draw_probability_le L hL c s S hb hS
    (rawLogLaneOfStrategy S trlog 0 b1) (rawGateLaneOfStrategy S trgate 0 b2)
    (raw_log_lane_causal S hS trlog htrlog 0 b1) (raw_gate_lane_causal S hS trgate htrgate 0 b2)
    rfl rfl q constraints g coeffsOf hdu
    (raw_log_lane_bounded S trlog 0 b1 5 hSlog hlenlog)
    (raw_gate_lane_bounded S trgate 0 b2 (q + 2) hSgate hlengate) hclen

/-! ## 8. WHAT THE WHOLE-SCHEDULE FORM WOULD HAVE BEEN FOR -/

/-- (8) **THE RUN-LEVEL EVENT IS A UNION OF ONE-STAGE EVENTS.**  Written out: the
adaptive run-level bad-draw event of section 7 is the union, over the coupled
rounds, of the two per-round events at THAT ROUND'S OWN STAGE, together with the
two block-`0` events at the derive stage.  Every summand is measured by the adopted
`OuterLaneTransport.stage_triple_target_mass_le` -- a ONE-STAGE fresh step,
conditioned on the chain's no-clash event up to that stage -- and the events nest,
so one clash term pays for all of them.  NO STATEMENT ABOUT THE JOINT LAW OF THE
WHOLE SCHEDULE IS USED ANYWHERE ABOVE, and the bound of section 7 does not become
weaker for the want of one. -/
theorem run_level_event_is_a_union_of_one_stage_events (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (logLane gateLane : RawLane) (rows : Nat) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (hlc : logLane.claim = 0) (hgc : gateLane.claim = 0) :
    adaptiveRunDrawEvent L hL c s S hb logLane gateLane rows g coeffsOf
      = ((Finset.range c.degreeBits).biUnion (fun r =>
            rawBothBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb
              logLane gateLane r)
          ∪ gateTauBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb
              c.degreeBits g)
        ∪ gateAlphaBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb
            c.degreeBits rows coeffsOf := by
  rw [← raw_full_bad_event_is_adaptive_run_draw_event L hL c s S hb hS logLane gateLane rows g
    coeffsOf hlc hgc]
  rfl

/-! ## 9. NON-VACUITY, AND THE CLOSED INSTANCE -/

/-- (9) **THE TEST AT THE ADOPTED CONSTANT TABLE.**  Every coordinate of the
realized draw collapses to one triple there -- the schedule is maximally
non-injective -- which is exactly why the adopted
`StrategyChainBound.constant_table_strategy_clashes` puts that table in the chain's
clash event and why the birthday term of section 7 is not measuring an empty
complement. -/
theorem realized_draw_at_constant_table (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat)
    (k : JointChallengeSpace.Draw d) :
    realizedDraw L hL e0 strat hb d (constantTable L) k
      = (OuterChallenge.digestBlock OuterInitial.zeroDigest,
          OuterChallenge.digestBlock OuterInitial.zeroDigest,
          OuterChallenge.digestBlock OuterInitial.zeroDigest) := rfl

theorem realized_draw_at_constant_table_is_constant (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat) (d : Nat) :
    realizedDraw L hL e0 strat hb d (constantTable L)
      = (fun _ => (OuterChallenge.digestBlock OuterInitial.zeroDigest,
          OuterChallenge.digestBlock OuterInitial.zeroDigest,
          OuterChallenge.digestBlock OuterInitial.zeroDigest)) := rfl

/-- (9) **AND THAT TABLE IS OUTSIDE THE CONDITIONER.**  The complement term of
section 7 -- the adopted birthday count -- is therefore not measuring an empty set:
the adopted `StrategyChainBound.constant_table_strategy_clashes`, read at the
adopted `OuterLaneTransport.stageNoClash`. -/
theorem constant_table_outside_the_conditioner (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (n : Nat) (hn : 2 ≤ n) :
    constantTable L ∈ (stageNoClash L hL e0 strat hb n)ᶜ :=
  constant_table_strategy_clashes L hL e0 strat hb n hn

/-- (9) `c.degreeBits = 13` is not a vacuous hypothesis: the adopted
`ConcreteChainThreading.budgetConfig` is such a config. -/
theorem degree_bits_thirteen_is_satisfiable :
    ConcreteChainThreading.budgetConfig.degreeBits = 13 := rfl

/-- (9) **THE CLOSED ADAPTIVE RUN-LEVEL INSTANCE.**  At the envelope's thirteen
coupled rounds, for the adopted `StrategyChainBound.challengeTruncatedMessage` --
a prover whose round message is a real function of the raw challenge blocks it has
read -- and for THAT PROVER'S OWN two raw lanes, the mass of the RUN'S OWN
`actualDigestDraw` landing in the adopted `jointBadEvent` of the lane rounds it
really played is at most the adopted `combinedBound 13 8 13 123` plus the adopted
`3828 / |Block|`.  Neither the length budget nor `64 <= L` is a hypothesis. -/
theorem adaptive_run_level_bound_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (hd : c.degreeBits = 13) (m : Verifier.CoupledMessage)
    (b1 b2 : Element) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (adaptiveRunDrawEvent L (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth 0 b1)
          (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth 0 b2)
          (2 ^ c.degreeBits) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) := by
  have h := strategic_adaptive_run_level_bad_draw_probability_le L
    (Nat.le_trans (by omega) hLq) c s (challengeTruncatedMessage m)
    (challenge_truncated_round_causal m)
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    rawZeroTruth rawZeroTruth raw_zero_truth_causal raw_zero_truth_causal b1 b2 8 123 g coeffsOf
    (by rw [hd]; exact thirteen_counter_budget)
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    (raw_zero_truth_length 5) (raw_zero_truth_length (8 + 2))
    (fun i hi => hclen i (by rw [hd] at hi; exact hi))
  have harith : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  refine le_trans h (le_of_eq ?_)
  rw [hd, harith]

/-- (9) **THE CLOSED BOUND IS A REAL NUMBER STRICTLY BELOW `1`**, by the adopted
evaluation.  `Fintype.card Block` is never evaluated.  READ HONESTY (v): THIS IS
NOT THE PROTOCOL'S SOUNDNESS ERROR. -/
theorem adaptive_run_level_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) < 1 :=
  raw_full_bound_at_thirteen_lt_one

end Audit.Wire3.RunLevelTransportAudit
