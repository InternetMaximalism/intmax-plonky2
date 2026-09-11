import Audit.Wire3.ReducedFullTransport

/-!
# RAW-BLOCK LANES: THE ADAPTIVE UNION BOUND WITHOUT THE REDUCED-HISTORY RESTRICTION

## WHAT THIS MODULE PROVES, AND WHAT IT DOES NOT -- READ THIS FIRST

The adopted `OuterLaneTransport` proves the per-round adaptive union bound -- SCB
HONESTY (iii), in which ROUND `r`'s BAD SET IS BUILT FROM THE MESSAGE THE PROVER
ITSELF CHOSE -- only for its section-8 `ReducedStrategy` subclass, and its header
says why: an `OuterSequentialConditioning.Lane`'s round message is
`Lane.message : List Element -> List Element`, applied to the REDUCED
round-challenge prefix, while a `StrategyChainBound.Strategy`'s round message is a
function of the RAW 32-byte answers at EVERY stage and EVERY counter.  Two
obstructions are named there, DOMAIN and LOSS, and both are real.

THIS MODULE REMOVES THE RESTRICTION.  The observation is that BOTH obstructions are
obstructions to FACTORING A RAW MESSAGE THROUGH A LANE'S ARGUMENT, and NEITHER is
an obstruction to the diagonal fresh step.  The adopted
`OuterLaneTransport.stage_triple_target_card` asks of round `r`'s target exactly
one thing: that the three stage-`roundStage r` challenge answers it is tested
against cannot move it.  That is the protocol's own causality -- the adopted
`StrategyChainBound.RoundCausal`, "round `r`'s message reads only the stages up to
`22 + 5 r`" -- and the raw-versus-reduced distinction is IRRELEVANT to it.  The
reduced restriction entered the adopted development through the PAIRING WITH AN
OSC LANE and through nothing else.

So `RawLane` (section 2) carries the STRATEGY's own domain:
`message : Nat -> (Nat -> Nat -> Block) -> List Element`.  Round `r`'s running
claims advance by the ADOPTED `OuterRound.evaluate` at the REDUCED challenge --
which is the only thing the verifier ever evaluates a round polynomial at -- while
the MESSAGE fed to it is raw.  The bad set is the ADOPTED
`ConditionalSoundness.roundBadSet` and its cardinality bound is the ADOPTED
`ConditionalSoundness.round_bad_triples_card`; no new counting is invented
anywhere below.  `rawLogLaneOfStrategy` / `rawGateLaneOfStrategy` (section 7) are
the `laneOfStrategy` the adopted header says does not exist -- for `RawLane` it is
a one-line definition -- and `raw_log_lane_message_is_realized` proves that the
lane's round-`r` message IS the message the strategic prover really emits at that
table.

## WHAT IS PROVED

1. THE RAW VIEW AND ITS INVARIANCE (sections 1 and 3).  `tableView` is the
   `Nat -> Nat -> Block` the adopted `Strategy` is handed, read off the table at
   the adopted `challengeSel`.  `table_view_reassign_lower` is the adopted
   `OuterLaneTransport.challenge_answer_reassign_lower` AT ALL COUNTERS AT ONCE,
   and `raw_outer_state_reassign` is the raw replacement for the adopted
   `outer_state_reassign`: the running claims before round `r` are a function of
   the answers at STRICTLY EARLIER stage digests, so round `r`'s own challenge
   answers cannot move them.  `raw_target_reassign` upgrades this to the target
   and -- unlike the adopted gate-lane version -- holds for EVERY counter of the
   round's stage, not only the lane's own three, because causality alone gives it.
2. THE PER-ROUND MASS (section 4).  `raw_round_mass_le` is the ADOPTED
   `OuterLaneTransport.stage_triple_target_mass_le` -- the diagonal fresh step,
   the honest technical core, adopted verbatim -- at the raw target, with the
   ADOPTED per-round cardinality bound `bd * fiberCeiling ^ 3`.
3. THE UNION AND THE HEADLINE (sections 5 and 6).
   `raw_outer_bad_draw_probability_le`:

     `oracleProbability (boundedQueries L) (rawOuterBadEvent L hL e0 strat hb logLane gateLane d)`
       `<= ChallengeUnionBound.outerTerm d q`
          `+ (22 + 5 d) (22 + 5 d + 1) / 2 / |Block|`

   for EVERY `StrategyChainBound.Strategy` and EVERY pair of RAW lanes obeying the
   protocol's causality and the adopted degree bounds.
   `strategic_raw_outer_bad_draw_probability_le` is the PAIRED form: the strategy
   is `strategicShape c s S` for an arbitrary `RoundCausal S` and the lanes are ITS
   OWN, so this closes the PER-ROUND-DECOMPOSITION half of SCB HONESTY (iii) at
   the `combinedBound` lanes, for every transcript-restricted prover that obeys
   the protocol's causality; the run-level transport named in that item's last
   sentence is carried out in the adopted `RunLevelTransportAudit` for the paired
   form (`strategicShape c s S`, `RoundCausal S`, claimed start `0`), which
   identifies this event with the run's own `actualDigestDraw` bad-draw event at
   the realized proof (see (vi)).  NO REDUCED-HISTORY RESTRICTION REMAINS on
   this half.
4. THE ADOPTED SUBCLASS IS AN INSTANCE (section 8).  `raw_log_target_of_reduced`
   and `raw_gate_target_of_reduced` prove that at a `ReducedStrategy` the raw
   target IS the adopted `OuterLaneTransport.logTarget` / `gateTarget`, SET FOR
   SET, and `raw_outer_bad_event_of_reduced` that the two bad EVENTS are the same
   `Finset`.  So the adopted section 8 is a special case of this module at truth
   functions obeying the protocol's causality: the adopted lanes are instantiated
   at `reducedTruthMessage tr`, which drops the round's own log challenge at the
   gate coordinate; an adopted gate truth reading that entry is not an instance
   (the message side is exact, since `reducedGateMessage` already takes the even
   prefix).  Note also that the raw gate lane cannot read round `r`'s own log
   challenge at all (`RoundCausal` excludes `roundStage r`), which is exactly why
   `raw_target_reassign` holds at every counter without the adopted
   `stage_triple_reassign_same`: the raw lane matches the deployed adversary.
5. THE FULL `combinedBound` CONSTANT (section 9).
   `raw_full_bad_draw_probability_le_combined` adds the ADOPTED
   `ReducedFullTransport.gateTauBadEvent` and `gateAlphaBadEvent`, REUSED VERBATIM:
   as that module's header records, their bad sets are indexed by `g`, `rows` and
   `coeffsOf` alone -- FIXED DATA that mentions no round message, no lane and no
   table -- so nothing about them changes when the outer lanes stop factoring
   through the reduced history.  The no-clash events nest, so ONE clash term pays
   for all three summands.  `strategic_raw_full_bad_draw_probability_le` is the
   paired form.
6. NON-DEGENERACY AND THE CLOSED INSTANCE (section 10).
   `separated_raw_target_zero_nonempty` exhibits a raw lane whose round-`0` target
   is INHABITED, at every strategy and every table -- including the adopted
   `BirthdayClashBound.constantTable`
   (`separated_raw_target_zero_nonempty_at_constant_table`) -- so the per-round
   bound of section 4 is not a bound on an empty set.
   `truncated_gate_lane_is_not_reduced_history` is the demonstration the module
   exists for: for the adopted `StrategyChainBound.challengeTruncatedMessage` --
   the very prover the adopted `OuterLaneTransport` header names as unpairable --
   two raw views that agree at EVERY round stage, so that the adopted
   `reducedHistory` cannot tell them apart, give DIFFERENT round-`0` gate
   messages.  `raw_bound_at_thirteen` and `raw_full_bound_at_thirteen` are the
   closed instances AT THAT PROVER AND ITS OWN LANES, at the envelope's thirteen
   coupled rounds, with neither `StrategyBounded` nor `64 <= L` nor the counter
   budget left as a hypothesis (the adopted prefix budget `hpre` and envelope
   budget `hLq` remain, as in every adopted closed instance):

     `<= ChallengeUnionBound.outerTerm 13 8 + 3828 / |Block|`,
     `<= ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / |Block|`,

   and `raw_bound_at_thirteen_lt_one` / `raw_full_bound_at_thirteen_lt_one` record
   that both are strictly below `1`.

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
MAKES NO ORACLE QUERIES OF ITS OWN.  A random-oracle-model Fiat--Shamir prover
that hashes candidate payloads itself and keeps the one whose digest collides --
GRINDING -- is NOT covered by anything below.  The adopted `GrindingQueryBound`,
`GrindingLinearBound` and `GrindingGraphBound` cover only such a prover's CHAIN
term, never the per-round decomposition proved here.  WIDENING THE MESSAGE'S
DOMAIN FROM THE REDUCED HISTORY TO THE RAW BLOCKS IS NOT THE SAME AS ALLOWING
OWN QUERIES, and this module does not touch that second restriction.

(iii) ROUND CAUSALITY IS A HYPOTHESIS, AND IT IS THE PROTOCOL'S.  `RawCausal`
asks that round `r`'s message read only the stages up to `22 + 5 r` -- the digest
round `r`'s own two challenges are squeezed from, by the adopted
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`.  A
"prover" whose round-`r` message read round `r`'s own challenge would be reading
the future, and no bound of this shape can hold for it.  This is the adopted
`StrategyChainBound.RoundCausal` unchanged; nothing stronger is assumed and
nothing weaker would do.

(iv) THE LANES ARE THE OUTER SUMCHECK LANES PLUS THE ADOPTED BLOCK-`0` ONES, AND
THE INDEX LANES ARE NOT INCLUDED.  Section 6's constant is
`ChallengeUnionBound.outerTerm degreeBits quotientDegree` and section 9's is the
whole adopted `ChallengeUnionBound.combinedBound` -- the outer term, the gate tau
column and the gate alpha row union -- AND NO OTHER TERM.  THE INDEX LANES OF THE
ADOPTED `ReducedIndexLanes` ARE NOT TRANSPORTED HERE.  Nothing mathematical blocks
it: that module's `extendedShape`, `realizedClaims`, `realized_history_reassign`
and `realized_claims_reassign` are all stated over its `ReducedStrategy R` and its
`UsedClaimsStrategy U : List Element -> Verifier.UsedClaims`, and the raw
analogues -- a `rawExtendedShape` built from `strategicShape c s S`, a
`U : (Nat -> Nat -> Block) -> Verifier.UsedClaims` read at stages up to
`22 + 5 d`, and `table_view_reassign_lower` in place of `outer_history_reassign`
(round stages and the derive stage are all strictly below
`indexStage d = 22 + 5 d + 8`) -- would go through the same way.  What blocks it
is WORK, not mathematics: the whole of that module's sections 5 to 9 -- the
extended length budget, `extended_strat_shape_is_claim_shape`,
`extended_stage_is_index_digest`, the two invariances and the density form of the
joint index peel -- must be re-derived at the raw domain, and none of it is
reusable as stated.  UNTIL THAT IS DONE, `2 * ChallengeUnionBound.tauTerm
indexBits` IS NOT PART OF ANY CONSTANT BELOW, and neither are the WHIR folding
transcript and the Merkle openings, which are not in `combinedBound` at all.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The bound is on the mass
of one named event under the oracle law.  The meaning of the per-round bad sets is
the adopted `ConditionalSoundness` one -- GOOD-DRAW-CONDITIONAL, with that
module's assumption list untouched -- and nothing here instantiates it.  The
running claims and the honest round messages are FREE PARAMETERS in every theorem
below, exactly as in the adopted `ConditionalSoundness` model; that is the right
statement and not a weakening, because a round at which the prover is HONEST has
an EMPTY bad set (the adopted `roundBadSet` takes its diagonal branch when the two
claims agree).  Quoting the numbers of section 10 as the wire-v3 soundness error
would be wrong.

(vi) THE FIAT--SHAMIR HALF IS UNTOUCHED, AND NO ADAPTIVE FIAT--SHAMIR SOUNDNESS IS
PROVED.  The adopted `RandomOracleSqueezes.run_draw_probability_le_fibrewise`
bounds a run's whole bad-draw mass for a FIXED proof by a Fubini over frame
fibres; that argument does not survive a table-dependent proof and is not repeated
here.  What is bounded below is an event defined directly on the oracle table.  It is
not the adopted `RandomOracleSqueezes.runDrawEvent`, which quantifies its
`Verifier.Proof` and its two lane lists OUTSIDE the law; for the paired form
(`strategicShape c s S`, `RoundCausal S`, claimed start `0`) the adopted
`RunLevelTransportAudit` proves that `rawFullBadEvent` IS that event once the
proof and the lane lists are replaced, table by table, by the ones this prover
realizes -- `raw_full_bad_event_is_adaptive_run_draw_event` -- so the run-level
transport named in item 3's last clause is no longer open at these lanes for
that form (the bounds at an arbitrary `Strategy` carry no such identification).  The reading that THE RUN'S ENCODING DRAW IS
DISTRIBUTED BY `jointProbability` remains exactly as unformalized as the adopted
`JointChallengeSpace.DrawEncodesRun` header says.  NOTHING BELOW IS A CLAIM THAT
ADAPTIVE FIAT--SHAMIR SOUNDNESS HAS BEEN ESTABLISHED.

(vii) THE CONFIGURATION DATA IS FIXED DATA.  `g`, `coeffsOf`, `rows` and
`constraints` of section 9 are bound OUTSIDE the oracle law in every theorem, and
no theorem lets the prover choose them after seeing a challenge.  That they are
the DEPLOYED run's tables is the adopted `CommitmentOrder` reading, INHERITED
UNCHANGED and not strengthened here.  The counter labels `0` and `3` for the two
coupled challenges are documented, not derived, for the abstract `Verifier.Engine`
the adopted modules quantify over; this module inherits that caveat too.

(viii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's
OWN definitions (`rawRoundBadEvent`, `rawFullBadEvent` through the adopted
`ReducedFullTransport` events it unions) and nowhere else.  NO TACTIC OR TERM
BELOW EVER PUTS `Finset.univ` ON `Element` OR ON `OuterChallenge.DigestTriple` IN A
POSITION THAT CAN BE REDUCED, and that is a hard constraint rather than a
preference: the adopted `Fintype` instances of those two types are built from
`Fin` equivalences of astronomical size, so any `whnf` reaching them diverges
(this module carries no `set_option maxRecDepth`).  It is why
`raw_target_zero_nonempty_of_agreement` is stated over an ABSTRACT `RawLane` and
concludes `Finset.Nonempty` rather than a bare membership at a concrete lane --
at concrete claims the adopted `roundBadSet`'s `if a = b` becomes reducible and the
unifier walks into `Finset.univ` on `Element` -- and why every digest-level
membership goes through the adopted `JointChallengeSpace.mem_tupleEvent`.  The
same rule forbids a tactic from seeing `Fintype.card Block`,
`Fintype.card Element` or `Fintype.card OuterChallenge.DigestTriple` in a `Nat`
arithmetic goal; no such cardinality is ever evaluated below.  This module imports
`Audit.Wire3.ReducedFullTransport` and nothing else, and no Mathlib module
directly.
-/

namespace Audit.Wire3.RawBlockLanes

open Audit.Wire3
open Audit.Wire3.GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport

/-! ## 1. THE RAW CHALLENGE VIEW OF AN ORACLE TABLE -/

/-- **THE RAW 32-BYTE ANSWER AT EVERY STAGE AND EVERY COUNTER OF A STRATEGY
CHAIN.**  This is the argument the adopted `StrategyChainBound.Strategy` is
handed, read off the table: stage `j`, counter `cnt`, the table's value at the
adopted `challengeSel`.  NOTHING IS REDUCED HERE -- no `OuterChallenge.reduceTriple`,
no restriction to counters below `6`, no restriction to round stages. -/
def tableView (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L)) :
    Nat → Nat → Block :=
  fun j cnt => T (challengeSel L hL e0 strat hb j cnt T)

/-- (1) **OVERWRITING A STAGE-`j` CHALLENGE ANSWER LEAVES THE WHOLE RAW VIEW OF
EVERY EARLIER STAGE ALONE** -- every counter of it, not just the six the reduced
history uses.  The adopted `OuterLaneTransport.challenge_answer_reassign_lower`,
taken at all counters at once. -/
theorem table_view_reassign_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block)
    (i : Nat) (hi : i < j) :
    tableView L hL e0 strat hb (reassign T (challengeSel L hL e0 strat hb j c T) b) i
      = tableView L hL e0 strat hb T i := by
  funext cnt
  exact challenge_answer_reassign_lower L hL e0 strat hb j c T hT b i hi cnt

/-! ## 2. A RAW LANE -/

/-- **ONE RAW-BLOCK LANE OF AN ADAPTIVE PROVER.**  Round `r`'s message and the
honest round `r` message are functions of the RAW challenge view
`Nat -> Nat -> Block` -- every stage, every counter -- rather than of the reduced
round-challenge list an `OuterSequentialConditioning.Lane` is handed.  `claim` and
`truthClaim` are the initial running claims of the adopted
`ConditionalSoundness.claimedRun` / `truthRun` recursions, exactly as for a
`Lane`.

THE DOMAIN IS THE WHOLE POINT.  The adopted
`OuterLaneTransport` header's `laneOfStrategy` paragraph names two obstructions to
pairing a `StrategyChainBound.Strategy` with a `Lane`: DOMAIN (raw blocks at all
stages and counters against reduced round values) and LOSS
(`OuterChallenge.reduceTriple` is not injective).  Both are obstructions to
factoring a raw message through a `Lane`'s argument; NEITHER is an obstruction to
the diagonal fresh step, which asks only that round `r`'s message not read round
`r`'s own challenge answers.  This structure has the strategy's own domain, so the
pairing is a definition rather than a theorem. -/
structure RawLane where
  message : Nat → (Nat → Nat → Block) → List Element
  truth : Nat → (Nat → Nat → Block) → List Element
  claim : Element
  truthClaim : Element

/-- **THE PROTOCOL'S CAUSALITY, ON THE RAW VIEW.**  Round `r`'s message reads only
the stages up to `22 + 5 r` -- the digest round `r`'s own two challenges are
squeezed from, by the adopted
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`.
This is the adopted `StrategyChainBound.RoundCausal` verbatim, at a
`List Element`-valued function instead of a `Verifier.CoupledMessage`-valued
one. -/
def RawCausal (f : Nat → (Nat → Nat → Block) → List Element) : Prop :=
  ∀ (r : Nat) (ch1 ch2 : Nat → Nat → Block),
    (∀ j, j ≤ 22 + 5 * r → ch1 j = ch2 j) → f r ch1 = f r ch2

/-- Both halves of a raw lane obey the protocol's causality. -/
def RawLaneCausal (lane : RawLane) : Prop :=
  RawCausal lane.message ∧ RawCausal lane.truth

/-- THE ADOPTED DEGREE BOUND, uniform over every raw view the prover may see: the
adopted `ConditionalSoundness.lane_degree_bounds` value `5` on the log lane and
`quotientDegree + 2` on the gate lane. -/
def RawLaneBounded (lane : RawLane) (b : Nat) : Prop :=
  ∀ (r : Nat) (ch : Nat → Nat → Block),
    (lane.message r ch).length ≤ b ∧ (lane.truth r ch).length ≤ b

/-- **THE RUNNING CLAIMS BEFORE ROUND `r`, AT ONE TABLE.**  The claim advances by
the ADOPTED `OuterRound.evaluate` at the REDUCED challenge
`OuterChallenge.reduceTriple` of the realized digest triple -- which is the only
thing the verifier ever evaluates the round polynomial at (the adopted
`OuterChallenge` / `OuterRound` reading) -- while the MESSAGE fed to it is the raw
one.  `base` selects the lane's own counters at the round stage: `0` for the log
lane and `3` for the gate lane, the adopted
`JointChallengeSpace.sourceCounter` values. -/
def rawClaims (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) : Nat → Element × Element
  | 0 => (lane.claim, lane.truthClaim)
  | r + 1 =>
      (OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T r).1
          (lane.message r (tableView L hL e0 strat hb T))
          (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage r) base T)),
       OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T r).2
          (lane.truth r (tableView L hL e0 strat hb T))
          (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage r) base T)))

theorem raw_claims_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) (r : Nat) :
    rawClaims L hL e0 strat hb lane base T (r + 1)
      = (OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T r).1
            (lane.message r (tableView L hL e0 strat hb T))
            (OuterChallenge.reduceTriple (stageTriple L hL e0 strat hb (roundStage r) base T)),
         OuterRound.evaluate (rawClaims L hL e0 strat hb lane base T r).2
            (lane.truth r (tableView L hL e0 strat hb T))
            (OuterChallenge.reduceTriple
              (stageTriple L hL e0 strat hb (roundStage r) base T))) := rfl

/-- **ROUND `r`'s RAW BAD SET, AT THE FIELD LEVEL.**  The ADOPTED
`ConditionalSoundness.roundBadSet` at the running claims and at the message the
raw lane chose after seeing the raw view.  The `challenge` field of the adopted
`LaneRound` is not read by `roundBadSet`, so `0` is put there, exactly as the
adopted `OuterSequentialConditioning.Lane.badSet` does. -/
noncomputable def rawBadSet (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base r : Nat)
    (T : OracleTable (boundedQueries L)) : Finset Element :=
  ConditionalSoundness.roundBadSet (rawClaims L hL e0 strat hb lane base T r).1
    (rawClaims L hL e0 strat hb lane base T r).2
    ⟨lane.message r (tableView L hL e0 strat hb T),
     lane.truth r (tableView L hL e0 strat hb T), 0⟩

/-- **AND ON THE DIGEST-TRIPLE ALPHABET**, through the ADOPTED
`OuterChallenge.tupleEvent` pullback along `reduceTriple`.  THIS IS WHERE THE
RAW-VERSUS-REDUCED ASYMMETRY LIVES AND WHY IT IS HARMLESS: the membership TEST is
at the reduced challenge, because that is the only thing the verifier evaluates
at; the message that BUILDS the set is raw. -/
noncomputable def rawTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (base r : Nat)
    (T : OracleTable (boundedQueries L)) : Finset OuterChallenge.DigestTriple :=
  OuterChallenge.tupleEvent (rawBadSet L hL e0 strat hb lane base r T)

/-- (2) **THE ADOPTED PER-ROUND CARDINALITY BOUND, REUSED VERBATIM.**  The adopted
`ConditionalSoundness.round_bad_triples_card`: at most `b` field points by the
adopted `round_bad_set_card`, each with at most
`OuterChallenge.fiberCeiling ^ 3` digest triples above it by the adopted
`OuterChallenge.fixed_point_set_preimage_bound`.  NO CARDINALITY IS EVALUATED. -/
theorem raw_target_card_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (bd : Nat) (hbd : RawLaneBounded lane bd)
    (base r : Nat) (T : OracleTable (boundedQueries L)) :
    (rawTarget L hL e0 strat hb lane base r T).card ≤ bd * OuterChallenge.fiberCeiling ^ 3 :=
  ConditionalSoundness.round_bad_triples_card _ _ _ bd
    (hbd r (tableView L hL e0 strat hb T)).1 (hbd r (tableView L hL e0 strat hb T)).2

/-! ## 3. THE STATE BEFORE ROUND `r` IS NOT MOVED BY ROUND `r`'s OWN ANSWERS -/

/-- (3) A raw-causal function does not see the stage-`j` challenge answers, for any
`j` strictly above `22 + 5 r`.  This is the raw analogue of the adopted
`OuterLaneTransport.reduced_history_congr`, and it is where `RawCausal` is used. -/
theorem raw_causal_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (f : Nat → (Nat → Nat → Block) → List Element)
    (hf : RawCausal f) (r j c : Nat) (hj : 22 + 5 * r < j)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block) :
    f r (tableView L hL e0 strat hb (reassign T (challengeSel L hL e0 strat hb j c T) b))
      = f r (tableView L hL e0 strat hb T) :=
  hf r _ _ (fun i hi => table_view_reassign_lower L hL e0 strat hb j c T hT b i (by omega))

/-- (3) **THE RAW STATE BEFORE ROUND `r` IS A FUNCTION OF STRICTLY EARLIER STAGES
ONLY.**  This is the raw replacement for the adopted
`OuterLaneTransport.outer_state_reassign`, and it holds for the SAME reason: round
`i < r` reads the raw view at the stages up to `22 + 5 i`, and absorbs the reduced
challenge read at stage `roundStage i`, ALL of which are strictly below `j`.  THE
RAW-VERSUS-REDUCED DISTINCTION IS IRRELEVANT TO THIS STATEMENT -- that is the
observation the whole module rests on. -/
theorem raw_outer_state_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane)
    (hcau : RawLaneCausal lane) (base j c : Nat) (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block) :
    ∀ rr : Nat, (∀ i, i < rr → roundStage i < j) →
      rawClaims L hL e0 strat hb lane base
          (reassign T (challengeSel L hL e0 strat hb j c T) b) rr
        = rawClaims L hL e0 strat hb lane base T rr := by
  intro rr
  induction rr with
  | zero => intro _; rfl
  | succ r2 ih =>
      intro hlt
      have hprev := ih (fun i hi => hlt i (by omega))
      have hr2 : roundStage r2 < j := hlt r2 (by omega)
      have hr2b : 22 + 5 * r2 < j := by rw [roundStage] at hr2; omega
      have hmsg := raw_causal_reassign L hL e0 strat hb lane.message hcau.1 r2 j c hr2b T hT b
      have htr := raw_causal_reassign L hL e0 strat hb lane.truth hcau.2 r2 j c hr2b T hT b
      have htrip : stageTriple L hL e0 strat hb (roundStage r2) base
            (reassign T (challengeSel L hL e0 strat hb j c T) b)
          = stageTriple L hL e0 strat hb (roundStage r2) base T :=
        stage_triple_reassign_lower L hL e0 strat hb j c (roundStage r2) base hr2 T hT b
      rw [raw_claims_succ, raw_claims_succ, hprev, hmsg, htr, htrip]

/-- (3) **ROUND `r`'s RAW BAD SET IS UNMOVED BY EVERY ONE OF ROUND `r`'s OWN
CHALLENGE ANSWERS.**  Not only by the three counters of its own lane: by ANY
counter at the round's stage.  This is the hypothesis the adopted
`OuterLaneTransport.stage_triple_target_card` diagonal step asks for, and it is
discharged from causality alone. -/
theorem raw_target_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (hcau : RawLaneCausal lane) (base r c : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL e0 strat hb (roundStage r)) (b : Block) :
    rawTarget L hL e0 strat hb lane base r
        (reassign T (challengeSel L hL e0 strat hb (roundStage r) c T) b)
      = rawTarget L hL e0 strat hb lane base r T := by
  have hrb : 22 + 5 * r < roundStage r := by rw [roundStage]; omega
  have hmsg := raw_causal_reassign L hL e0 strat hb lane.message hcau.1 r (roundStage r) c hrb
    T hT b
  have htr := raw_causal_reassign L hL e0 strat hb lane.truth hcau.2 r (roundStage r) c hrb T hT b
  have hst := raw_outer_state_reassign L hL e0 strat hb lane hcau base (roundStage r) c T hT b r
    (fun i hi => round_stage_lt i r hi)
  rw [rawTarget, rawTarget, rawBadSet, rawBadSet, hst, hmsg, htr]

/-! ## 4. THE PER-ROUND MASS -/

/-- (4) **ROUND `r`'s RAW MASS, AT EITHER LANE.**  Conditioned on the chain's
no-clash event up to round `r`'s own stage, the lane's own challenge triple of
round `r` lands in the bad set ITS OWN RAW HISTORY has chosen with mass at most
`bd * ceil ^ 3 / |DigestTriple|`.  The adopted
`OuterLaneTransport.stage_triple_target_mass_le` at the raw target. -/
theorem raw_round_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (lane : RawLane) (hcau : RawLaneCausal lane) (bd : Nat)
    (hbd : RawLaneBounded lane bd) (base : Nat) (hbase : base + 2 < Transcript.u64Limit)
    (r : Nat) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb (roundStage r)).filter
          (fun T => stageTriple L hL e0 strat hb (roundStage r) base T
            ∈ rawTarget L hL e0 strat hb lane base r T))
      ≤ ((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  stage_triple_target_mass_le L hL e0 strat hb (roundStage r) base hbase
    (stageNoClash L hL e0 strat hb (roundStage r))
    (stage_stable_no_clash L hL e0 strat hb (roundStage r) (tripleCounters base))
    (rawTarget L hL e0 strat hb lane base r)
    (fun T hT c _ b => raw_target_reassign L hL e0 strat hb lane hcau base r c T hT b)
    (bd * OuterChallenge.fiberCeiling ^ 3)
    (fun T _ => raw_target_card_le L hL e0 strat hb lane bd hbd base r T)

/-! ## 5. THE EVENTS AND THE UNION OVER THE ROUNDS -/

/-- THE EVENT THAT COUPLED ROUND `r`'s OWN CHALLENGE TRIPLE, AT COUNTER `base`,
LANDS IN THE BAD SET THE RAW LANE HAS CHOSEN FOR IT. -/
noncomputable def rawRoundBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (base r : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => stageTriple L hL e0 strat hb (roundStage r) base T
    ∈ rawTarget L hL e0 strat hb lane base r T)

/-- Round `r` agrees on either raw lane: the log lane at counters `0, 1, 2` and
the gate lane at counters `3, 4, 5` of the SAME stage digest. -/
noncomputable def rawBothBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane) (r : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  rawRoundBadEvent L hL e0 strat hb logLane 0 r ∪ rawRoundBadEvent L hL e0 strat hb gateLane 3 r

/-- **THE RAW OUTER BAD EVENT ON THE ORACLE TABLE.**  Some coupled round of either
RAW lane agrees. -/
noncomputable def rawOuterBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane) (d : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  (Finset.range d).biUnion (fun r => rawBothBadEvent L hL e0 strat hb logLane gateLane r)

theorem raw_outer_bad_event_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane) :
    rawOuterBadEvent L hL e0 strat hb logLane gateLane 0
      = (∅ : Finset (OracleTable (boundedQueries L))) := by
  rw [rawOuterBadEvent, Finset.range_zero, Finset.biUnion_empty]

/-- (5) On the no-clash event, round `r`'s raw bad event is covered by the two
FIXED-STAGE events of section 4: the adopted
`OuterLaneTransport.stage_no_clash_mono` nests the conditioning events. -/
theorem raw_round_inter_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane) (n r : Nat)
    (hr : roundStage r ≤ n) :
    rawBothBadEvent L hL e0 strat hb logLane gateLane r ∩ stageNoClash L hL e0 strat hb n
      ⊆ ((stageNoClash L hL e0 strat hb (roundStage r)).filter
            (fun T => stageTriple L hL e0 strat hb (roundStage r) 0 T
              ∈ rawTarget L hL e0 strat hb logLane 0 r T))
        ∪ ((stageNoClash L hL e0 strat hb (roundStage r)).filter
            (fun T => stageTriple L hL e0 strat hb (roundStage r) 3 T
              ∈ rawTarget L hL e0 strat hb gateLane 3 r T)) := by
  rw [rawBothBadEvent, Finset.union_inter_distrib_right, rawRoundBadEvent, rawRoundBadEvent]
  exact Finset.union_subset_union
    (univ_filter_inter_subset _ _ _ (stage_no_clash_mono L hL e0 strat hb (roundStage r) n hr))
    (univ_filter_inter_subset _ _ _ (stage_no_clash_mono L hL e0 strat hb (roundStage r) n hr))

/-- (5) **THE UNION OVER THE ROUNDS, ON THE NO-CLASH EVENT.**  Each summand is a
fixed-stage statement by the nesting, and each is the diagonal bound of
section 4. -/
theorem raw_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane) (bl bg : Nat)
    (hlog : RawLaneBounded logLane bl) (hgate : RawLaneBounded gateLane bg) (n : Nat) :
    ∀ k : Nat, (∀ r, r < k → roundStage r ≤ n) →
      oracleProbability (boundedQueries L)
          (rawOuterBadEvent L hL e0 strat hb logLane gateLane k
            ∩ stageNoClash L hL e0 strat hb n)
        ≤ (k : ℚ) * (((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [raw_outer_bad_event_zero, Finset.empty_inter, oracle_probability_empty,
        Nat.cast_zero, zero_mul]
  | succ k2 ih =>
      intro hk
      have hk2 : ∀ r, r < k2 → roundStage r ≤ n := fun r hr => hk r (by omega)
      have hkk : roundStage k2 ≤ n := hk k2 (by omega)
      have hsplit : rawOuterBadEvent L hL e0 strat hb logLane gateLane (k2 + 1)
            ∩ stageNoClash L hL e0 strat hb n
          = (rawBothBadEvent L hL e0 strat hb logLane gateLane k2
              ∩ stageNoClash L hL e0 strat hb n)
            ∪ (rawOuterBadEvent L hL e0 strat hb logLane gateLane k2
              ∩ stageNoClash L hL e0 strat hb n) := by
        rw [rawOuterBadEvent, rawOuterBadEvent, Finset.range_succ,
          Finset.biUnion_insert, Finset.union_inter_distrib_right]
      have hround : oracleProbability (boundedQueries L)
          (rawBothBadEvent L hL e0 strat hb logLane gateLane k2
            ∩ stageNoClash L hL e0 strat hb n)
          ≤ ((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
        refine le_trans (oracle_probability_mono (boundedQueries L) _ _
          (raw_round_inter_subset L hL e0 strat hb logLane gateLane n k2 hkk)) ?_
        refine le_trans (oracle_probability_union_le (boundedQueries L) _ _) ?_
        exact add_le_add
          (raw_round_mass_le L hL e0 strat hb logLane hlcau bl hlog 0
            (small_counter_lt 2 (by omega)) k2)
          (raw_round_mass_le L hL e0 strat hb gateLane hgcau bg hgate 3
            (small_counter_lt 5 (by omega)) k2)
      have hsum : ((k2 + 1 : Nat) : ℚ) * (((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ))
          = (((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ))
            + (k2 : ℚ) * (((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)) := by
        push_cast
        ring
      rw [hsplit, hsum]
      exact le_trans (oracle_probability_union_le (boundedQueries L) _ _)
        (add_le_add hround (ih hk2))

/-! ## 6. THE HEADLINE FOR RAW LANES -/

/-- (6) **THE RAW OUTER BAD-DRAW BOUND.**  Under the random-oracle counting law on
`RandomOracleSqueezes.OracleTable (boundedQueries L)`, for EVERY
transcript-restricted adaptive prover -- every `StrategyChainBound.Strategy` -- and
EVERY pair of RAW lanes that obey the protocol's causality and the adopted degree
bounds, the mass of the event that some coupled round of either raw lane agrees is
at most the adopted `ChallengeUnionBound.outerTerm degreeBits quotientDegree` plus
the chain's own clash mass.

THE RESTRICTION THE ADOPTED `OuterLaneTransport` SECTION 8 CARRIES IS GONE.  A raw
lane's round message is a function of the raw 32-byte answers at EVERY stage and
EVERY counter; no `OuterChallenge.reduceTriple` factorization is asked for, and no
restriction to counters below `6` or to round stages.  READ THE HONESTY HEADER:
this is the outer part of `combinedBound` only, the prover makes no oracle queries
of its own, and this is not the system's soundness error. -/
theorem raw_outer_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane) (d q : Nat)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2)) :
    oracleProbability (boundedQueries L)
        (rawOuterBadEvent L hL e0 strat hb logLane gateLane d)
      ≤ ChallengeUnionBound.outerTerm d q
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl (rawOuterBadEvent L hL e0 strat hb logLane gateLane d)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hunion := oracle_probability_union_le (boundedQueries L)
    (rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hround := raw_no_clash_mass_le L hL e0 strat hb logLane gateLane hlcau hgcau 5 (q + 2)
    hlog hgate (22 + 5 * d) d (fun r hr => round_stage_le r d hr)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
      ≤ ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL e0 strat hb (22 + 5 * d)
  have hterm : (d : ℚ) * (((5 * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
        / (Fintype.card OuterChallenge.DigestTriple : ℚ)
      + (((q + 2) * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
        / (Fintype.card OuterChallenge.DigestTriple : ℚ))
      = ChallengeUnionBound.outerTerm d q := round_terms_sum d q
  rw [hterm] at hround
  linarith

/-! ## 7. THE PAIRING: A RAW LANE OF THE STRATEGY'S OWN MESSAGES -/

/-- **THE LOG LANE OF A RAW STRATEGY.**  Its round-`r` message IS the log cell the
adopted `StrategyChainBound.strategicShape` prover emits at round `r`, lifted to
`Element` by the adopted `OuterRound.lift`.  THIS DEFINITION IS THE POINT OF THE
MODULE: the adopted `OuterLaneTransport` header explains that no such function
exists into `OuterSequentialConditioning.Lane`, for two reasons that are both
about the LANE's argument being the reduced round-challenge list.  Into `RawLane`
it is a one-line definition, because a `RawLane` has the STRATEGY's own domain. -/
def rawLogLaneOfStrategy (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (a b : Element) : RawLane where
  message := fun r ch => (S r ch).1.map OuterRound.lift
  truth := tr
  claim := a
  truthClaim := b

/-- The same for the GATE cell. -/
def rawGateLaneOfStrategy (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (a b : Element) : RawLane where
  message := fun r ch => (S r ch).2.map OuterRound.lift
  truth := tr
  claim := a
  truthClaim := b

/-- (7) **THE ADOPTED `RoundCausal` IS EXACTLY `RawCausal` OF THE LIFTED LOG
CELL.**  No extra restriction is imposed on the prover: the protocol's own
causality is all that is used. -/
theorem raw_log_lane_causal (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (tr : Nat → (Nat → Nat → Block) → List Element) (htr : RawCausal tr)
    (a b : Element) : RawLaneCausal (rawLogLaneOfStrategy S tr a b) := by
  refine ⟨fun r ch1 ch2 h => ?_, htr⟩
  show (S r ch1).1.map OuterRound.lift = (S r ch2).1.map OuterRound.lift
  rw [hS r ch1 ch2 h]

theorem raw_gate_lane_causal (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (tr : Nat → (Nat → Nat → Block) → List Element) (htr : RawCausal tr)
    (a b : Element) : RawLaneCausal (rawGateLaneOfStrategy S tr a b) := by
  refine ⟨fun r ch1 ch2 h => ?_, htr⟩
  show (S r ch1).2.map OuterRound.lift = (S r ch2).2.map OuterRound.lift
  rw [hS r ch1 ch2 h]

theorem raw_log_lane_bounded (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (a b : Element) (bd : Nat)
    (hS : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ bd)
    (htr : ∀ (r : Nat) (ch : Nat → Nat → Block), (tr r ch).length ≤ bd) :
    RawLaneBounded (rawLogLaneOfStrategy S tr a b) bd := by
  refine fun r ch => ⟨?_, htr r ch⟩
  show ((S r ch).1.map OuterRound.lift).length ≤ bd
  rw [List.length_map]
  exact hS r ch

theorem raw_gate_lane_bounded (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (tr : Nat → (Nat → Nat → Block) → List Element) (a b : Element) (bd : Nat)
    (hS : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ bd)
    (htr : ∀ (r : Nat) (ch : Nat → Nat → Block), (tr r ch).length ≤ bd) :
    RawLaneBounded (rawGateLaneOfStrategy S tr a b) bd := by
  refine fun r ch => ⟨?_, htr r ch⟩
  show ((S r ch).2.map OuterRound.lift).length ≤ bd
  rw [List.length_map]
  exact hS r ch

/-- (7) **THE RAW VIEW IS WHAT THE STRATEGIC PROVER READS.**  At every stage the
adopted `RoundCausal` lets round `r` look at, the adopted
`StrategyChainBound.strategicChallenges` and `tableView` are the same function.
The adopted `strategic_challenges_is_sel`, at all counters at once. -/
theorem strategic_challenges_is_table_view (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (r : Nat)
    (T : OracleTable (boundedQueries L)) (j : Nat) (hj : j ≤ 22 + 5 * r) :
    strategicChallenges L hL c s S hb r T j
      = tableView L hL OuterInitial.zeroDigest (strategicShape c s S) hb T j := by
  funext cnt
  exact strategic_challenges_is_sel L hL c s S hb r T j cnt hj

/-- (7) **ROUND `r`'s RAW-LANE MESSAGE IS THE MESSAGE THE PROVER REALLY EMITS.**
This is the pairing the adopted `OuterLaneTransport` has only for its
`ReducedStrategy` subclass, here for EVERY `RoundCausal` strategy. -/
theorem raw_log_lane_message_is_realized (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (hb : StrategyBounded L (strategicShape c s S))
    (tr : Nat → (Nat → Nat → Block) → List Element) (a b : Element) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    (rawLogLaneOfStrategy S tr a b).message r
        (tableView L hL OuterInitial.zeroDigest (strategicShape c s S) hb T)
      = (S r (strategicChallenges L hL c s S hb r T)).1.map OuterRound.lift := by
  show (S r (tableView L hL OuterInitial.zeroDigest (strategicShape c s S) hb T)).1.map
      OuterRound.lift = _
  rw [hS r _ (strategicChallenges L hL c s S hb r T)
    (fun j hj => (strategic_challenges_is_table_view L hL c s S hb r T j hj).symm)]

/-- (7) The same for the GATE cell. -/
theorem raw_gate_lane_message_is_realized (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hS : RoundCausal S) (hb : StrategyBounded L (strategicShape c s S))
    (tr : Nat → (Nat → Nat → Block) → List Element) (a b : Element) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    (rawGateLaneOfStrategy S tr a b).message r
        (tableView L hL OuterInitial.zeroDigest (strategicShape c s S) hb T)
      = (S r (strategicChallenges L hL c s S hb r T)).2.map OuterRound.lift := by
  show (S r (tableView L hL OuterInitial.zeroDigest (strategicShape c s S) hb T)).2.map
      OuterRound.lift = _
  rw [hS r _ (strategicChallenges L hL c s S hb r T)
    (fun j hj => (strategic_challenges_is_table_view L hL c s S hb r T j hj).symm)]

/-- (7) **THE PER-ROUND-DECOMPOSITION HALF OF SCB HONESTY (iii), CLOSED AT THE
`combinedBound` LANES FOR EVERY TRANSCRIPT-RESTRICTED PROVER THAT OBEYS THE
PROTOCOL'S CAUSALITY** (the run-level transport of that item's last sentence
remains open, see HONESTY (vi)).  The strategy is `strategicShape c s S` and the
two raw lanes are ITS OWN (`raw_log_lane_message_is_realized` and its gate twin),
so round `r`'s bad set is built from the message THE PROVER CHOSE after seeing the
RAW blocks of every earlier stage -- the full 256-bit challenge blocks, the
counters at and above `6`, and the non-round stages included.  NO
REDUCED-HISTORY RESTRICTION REMAINS.

The honest round messages `trlog`, `trgate` and the two pairs of running claims
are free parameters subject to the adopted degree bounds, exactly as in the
adopted `ConditionalSoundness` model: the bad set of a round at which the prover
is HONEST is EMPTY (the adopted `roundBadSet` takes its diagonal branch when the
two claims agree), so quantifying over them is the right statement and not a
weakening.  READ THE HONESTY HEADER. -/
theorem strategic_raw_outer_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hb : StrategyBounded L (strategicShape c s S))
    (trlog trgate : Nat → (Nat → Nat → Block) → List Element)
    (htrlog : RawCausal trlog) (htrgate : RawCausal trgate)
    (a1 b1 a2 b2 : Element) (d q : Nat)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (trlog r ch).length ≤ 5)
    (hlengate : ∀ (r : Nat) (ch : Nat → Nat → Block), (trgate r ch).length ≤ q + 2) :
    oracleProbability (boundedQueries L)
        (rawOuterBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (rawLogLaneOfStrategy S trlog a1 b1) (rawGateLaneOfStrategy S trgate a2 b2) d)
      ≤ ChallengeUnionBound.outerTerm d q
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  raw_outer_bad_draw_probability_le L hL OuterInitial.zeroDigest (strategicShape c s S) hb
    (rawLogLaneOfStrategy S trlog a1 b1) (rawGateLaneOfStrategy S trgate a2 b2)
    (raw_log_lane_causal S hS trlog htrlog a1 b1) (raw_gate_lane_causal S hS trgate htrgate a2 b2)
    d q (raw_log_lane_bounded S trlog a1 b1 5 hSlog hlenlog)
    (raw_gate_lane_bounded S trgate a2 b2 (q + 2) hSgate hlengate)

/-! ## 8. THE ADOPTED REDUCED-HISTORY CASE IS AN INSTANCE OF THIS ONE -/

/-- (8) The raw view of a table, reduced round by round, IS the adopted
`OuterLaneTransport.outerHistory` the lanes read.  The adopted
`reduced_history_is_outer_history`, whose hypothesis holds by definition here. -/
theorem reduced_history_of_table_view (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L))
    (n : Nat) :
    reducedHistory (tableView L hL e0 strat hb T) n = outerHistory L hL e0 strat hb T n :=
  reduced_history_is_outer_history L hL e0 strat hb T (tableView L hL e0 strat hb T) n
    (fun _ _ _ => rfl)

/-- (8) The adopted `laneStep` at a lane that OWNS the coordinate. -/
theorem lane_step_claim_active (lg : Lane) (ds : OuterChallenge.DigestTriple)
    (h : lg.ownsNext = true) :
    (laneStep lg ds).claim
      = OuterRound.evaluate lg.claim (lg.message []) (OuterChallenge.reduceTriple ds) := by
  show (if lg.ownsNext then OuterRound.evaluate lg.claim (lg.message [])
      (OuterChallenge.reduceTriple ds) else lg.claim) = _
  rw [h]
  rfl

theorem lane_step_truth_claim_active (lg : Lane) (ds : OuterChallenge.DigestTriple)
    (h : lg.ownsNext = true) :
    (laneStep lg ds).truthClaim
      = OuterRound.evaluate lg.truthClaim (lg.truth []) (OuterChallenge.reduceTriple ds) := by
  show (if lg.ownsNext then OuterRound.evaluate lg.truthClaim (lg.truth [])
      (OuterChallenge.reduceTriple ds) else lg.truthClaim) = _
  rw [h]
  rfl

/-- (8) And at a lane that does NOT own it: the running claims stand still. -/
theorem lane_step_claim_inactive (lg : Lane) (ds : OuterChallenge.DigestTriple)
    (h : lg.ownsNext = false) : (laneStep lg ds).claim = lg.claim := by
  show (if lg.ownsNext then OuterRound.evaluate lg.claim (lg.message [])
      (OuterChallenge.reduceTriple ds) else lg.claim) = _
  rw [h]
  rfl

theorem lane_step_truth_claim_inactive (lg : Lane) (ds : OuterChallenge.DigestTriple)
    (h : lg.ownsNext = false) : (laneStep lg ds).truthClaim = lg.truthClaim := by
  show (if lg.ownsNext then OuterRound.evaluate lg.truthClaim (lg.truth [])
      (OuterChallenge.reduceTriple ds) else lg.truthClaim) = _
  rw [h]
  rfl

/-- (8) The adopted `OuterLaneTransport.outer_state_message` for the HONEST round
message, by the same induction: the adopted `Lane.step` treats `truth` exactly as
it treats `message`. -/
theorem outer_state_truth (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (T : OracleTable (boundedQueries L)) :
    ∀ (r : Nat) (xs : List Element),
      (outerState L hL e0 strat hb logLane gateLane T r).1.truth xs
          = logLane.truth (outerHistory L hL e0 strat hb T r ++ xs) ∧
        (outerState L hL e0 strat hb logLane gateLane T r).2.truth xs
          = gateLane.truth (outerHistory L hL e0 strat hb T r ++ xs) := by
  intro r
  induction r with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ r2 ih =>
      intro xs
      have hsplit : outerHistory L hL e0 strat hb T (r2 + 1) ++ xs
          = outerHistory L hL e0 strat hb T r2
            ++ (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r2 T)
                :: OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb r2 T) :: xs) := by
        rw [outer_history_succ, List.append_assoc]
        rfl
      refine ⟨?_, ?_⟩
      · show (outerState L hL e0 strat hb logLane gateLane T r2).1.truth
            (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r2 T)
              :: OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb r2 T) :: xs)
          = logLane.truth (outerHistory L hL e0 strat hb T (r2 + 1) ++ xs)
        rw [(ih _).1, hsplit]
      · show (outerState L hL e0 strat hb logLane gateLane T r2).2.truth
            (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r2 T)
              :: OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb r2 T) :: xs)
          = gateLane.truth (outerHistory L hL e0 strat hb T (r2 + 1) ++ xs)
        rw [(ih _).2, hsplit]

/-- **THE HONEST ROUND MESSAGE OF A REDUCED-HISTORY MODEL, AS A `Lane` TRUTH.**
The adopted `OuterLaneTransport.reducedGateMessage` trick, at the honest side: the
prefix a GATE coordinate is handed has `2 r + 1` entries and the `take` drops the
round's own log challenge, so the honest round-`r` message is a function of the
rounds BEFORE `r` at both coordinates.  The adopted `logLaneOfReduced` /
`gateLaneOfReduced` quantify over an arbitrary truth function, so this is a
legitimate instance of them. -/
def reducedTruthMessage (tr : Nat → List Element → List Element)
    (xs : List Element) : List Element :=
  tr (xs.length / 2) (xs.take (2 * (xs.length / 2)))

theorem reduced_truth_message_bounded (tr : Nat → List Element → List Element) (bd : Nat)
    (h : ∀ (r : Nat) (xs : List Element), (tr r xs).length ≤ bd) (xs : List Element) :
    (reducedTruthMessage tr xs).length ≤ bd := h _ _

/-- **THE RAW LOG LANE OF A REDUCED-HISTORY PROVER.**  Its message factors through
the adopted `OuterLaneTransport.reducedHistory`, which is exactly what makes it a
member of the adopted section-8 subclass. -/
def rawLogLaneOfReduced (R : ReducedStrategy) (tr : Nat → List Element → List Element)
    (a b : Element) : RawLane where
  message := fun r ch => (R r (reducedHistory ch r)).1.map OuterRound.lift
  truth := fun r ch => tr r (reducedHistory ch r)
  claim := a
  truthClaim := b

def rawGateLaneOfReduced (R : ReducedStrategy) (tr : Nat → List Element → List Element)
    (a b : Element) : RawLane where
  message := fun r ch => (R r (reducedHistory ch r)).2.map OuterRound.lift
  truth := fun r ch => tr r (reducedHistory ch r)
  claim := a
  truthClaim := b

/-- (8) A reduced-history lane obeys the protocol's causality, by the adopted
`OuterLaneTransport.reduced_history_congr`: the largest round stage it reads is
`roundStage (r - 1) = 22 + 5 r`. -/
theorem raw_reduced_causal (f : Nat → List Element → List Element) :
    RawCausal (fun r ch => f r (reducedHistory ch r)) := by
  intro r ch1 ch2 h
  show f r (reducedHistory ch1 r) = f r (reducedHistory ch2 r)
  rw [reduced_history_congr ch1 ch2 r (fun i hi => h (roundStage i) (by rw [roundStage]; omega))]

theorem raw_log_lane_of_reduced_causal (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) :
    RawLaneCausal (rawLogLaneOfReduced R tr a b) :=
  ⟨raw_reduced_causal (fun r xs => (R r xs).1.map OuterRound.lift), raw_reduced_causal tr⟩

theorem raw_gate_lane_of_reduced_causal (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) :
    RawLaneCausal (rawGateLaneOfReduced R tr a b) :=
  ⟨raw_reduced_causal (fun r xs => (R r xs).2.map OuterRound.lift), raw_reduced_causal tr⟩

/-- (8) ROUND `r`'s LOG MESSAGE OF THE ADOPTED LANE, read off the state. -/
theorem log_state_message_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (gateLane : Lane)
    (T : OracleTable (boundedQueries L)) (r : Nat) :
    (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
        gateLane T r).1.message []
      = (R r (outerHistory L hL e0 strat hb T r)).1.map OuterRound.lift := by
  have hlen := outer_history_length L hL e0 strat hb T r
  rw [(outer_state_message L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
    gateLane T r []).1, List.append_nil]
  show ((R ((outerHistory L hL e0 strat hb T r).length / 2)
      ((outerHistory L hL e0 strat hb T r).take
        (2 * ((outerHistory L hL e0 strat hb T r).length / 2)))).1.map OuterRound.lift) = _
  rw [hlen, Nat.mul_div_cancel_left r (by omega), ← hlen, take_own_length]

theorem log_state_truth_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (gateLane : Lane)
    (T : OracleTable (boundedQueries L)) (r : Nat) :
    (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
        gateLane T r).1.truth []
      = tr r (outerHistory L hL e0 strat hb T r) := by
  have hlen := outer_history_length L hL e0 strat hb T r
  rw [(outer_state_truth L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
    gateLane T r []).1, List.append_nil]
  show tr ((outerHistory L hL e0 strat hb T r).length / 2)
      ((outerHistory L hL e0 strat hb T r).take
        (2 * ((outerHistory L hL e0 strat hb T r).length / 2))) = _
  rw [hlen, Nat.mul_div_cancel_left r (by omega), ← hlen, take_own_length]

/-- (8) ROUND `r`'s GATE MESSAGE OF THE ADOPTED LANE, at the state the adopted
`gateTarget` reads it from: after the round's own LOG triple has been absorbed.
The `take` of the adopted `reducedGateMessage` drops that entry again. -/
theorem gate_state_message_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (logLane : Lane)
    (T : OracleTable (boundedQueries L)) (r : Nat) :
    (laneStep (outerState L hL e0 strat hb logLane
        (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
      (logTriple L hL e0 strat hb r T)).message []
      = (R r (outerHistory L hL e0 strat hb T r)).2.map OuterRound.lift := by
  have hlen := outer_history_length L hL e0 strat hb T r
  have hlen2 : (outerHistory L hL e0 strat hb T r
      ++ [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T)]).length = 2 * r + 1 := by
    rw [List.length_append, hlen]
    rfl
  show (outerState L hL e0 strat hb logLane
      (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2.message
      [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T)] = _
  rw [(outer_state_message L hL e0 strat hb logLane
    (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r
    [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T)]).2]
  show ((R (( _ : List Element).length / 2) _).2.map OuterRound.lift) = _
  rw [hlen2, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero,
    show 2 * r = (outerHistory L hL e0 strat hb T r).length from hlen.symm, take_length_append]

theorem gate_state_truth_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (logLane : Lane)
    (T : OracleTable (boundedQueries L)) (r : Nat) :
    (laneStep (outerState L hL e0 strat hb logLane
        (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
      (logTriple L hL e0 strat hb r T)).truth []
      = tr r (outerHistory L hL e0 strat hb T r) := by
  have hlen := outer_history_length L hL e0 strat hb T r
  have hlen2 : (outerHistory L hL e0 strat hb T r
      ++ [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T)]).length = 2 * r + 1 := by
    rw [List.length_append, hlen]
    rfl
  show (outerState L hL e0 strat hb logLane
      (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2.truth
      [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T)] = _
  rw [(outer_state_truth L hL e0 strat hb logLane
    (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r
    [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T)]).2]
  show tr (( _ : List Element).length / 2) _ = _
  rw [hlen2, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero,
    show 2 * r = (outerHistory L hL e0 strat hb T r).length from hlen.symm, take_length_append]

/-- (8) **THE TWO RUNNING-CLAIM RECURSIONS AGREE, ON THE LOG LANE.**  The adopted
`laneStep` advances the log lane at the round's LOG coordinate and stands still at
its GATE coordinate (`outer_state_log_owns`), which is exactly the `rawClaims`
recursion at `base = 0`. -/
theorem log_claims_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (gateLane : Lane)
    (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat,
      ((outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
            gateLane T r).1.claim,
        (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
            gateLane T r).1.truthClaim)
        = rawClaims L hL e0 strat hb (rawLogLaneOfReduced R tr a b) 0 T r := by
  intro r
  induction r with
  | zero => rfl
  | succ r2 ih =>
      have hown : (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
          gateLane T r2).1.ownsNext = true :=
        outer_state_log_owns L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
          gateLane T r2
      have hoff : (laneStep (outerState L hL e0 strat hb
          (logLaneOfReduced R (reducedTruthMessage tr) a b) gateLane T r2).1
          (logTriple L hL e0 strat hb r2 T)).ownsNext = false := by
        rw [laneStep_active, hown]
        rfl
      have hmsg := log_state_message_of_reduced L hL e0 strat hb R tr a b gateLane T r2
      have htr := log_state_truth_of_reduced L hL e0 strat hb R tr a b gateLane T r2
      have hhist := reduced_history_of_table_view L hL e0 strat hb T r2
      show ((laneStep (laneStep (outerState L hL e0 strat hb
              (logLaneOfReduced R (reducedTruthMessage tr) a b) gateLane T r2).1
            (logTriple L hL e0 strat hb r2 T)) (gateTriple L hL e0 strat hb r2 T)).claim,
          (laneStep (laneStep (outerState L hL e0 strat hb
              (logLaneOfReduced R (reducedTruthMessage tr) a b) gateLane T r2).1
            (logTriple L hL e0 strat hb r2 T)) (gateTriple L hL e0 strat hb r2 T)).truthClaim)
        = rawClaims L hL e0 strat hb (rawLogLaneOfReduced R tr a b) 0 T (r2 + 1)
      rw [lane_step_claim_inactive _ _ hoff, lane_step_truth_claim_inactive _ _ hoff,
        lane_step_claim_active _ _ hown, lane_step_truth_claim_active _ _ hown, hmsg, htr,
        raw_claims_succ, ← ih]
      show (OuterRound.evaluate _ _ _, OuterRound.evaluate _ _ _)
        = (OuterRound.evaluate _ ((R r2 (reducedHistory
              (tableView L hL e0 strat hb T) r2)).1.map OuterRound.lift) _,
           OuterRound.evaluate _ (tr r2 (reducedHistory (tableView L hL e0 strat hb T) r2)) _)
      rw [hhist]
      rfl

/-- (8) **AND ON THE GATE LANE**, at `base = 3`: the adopted `laneStep` stands
still at the round's LOG coordinate and advances at its GATE coordinate
(`outer_state_gate_owns`). -/
theorem gate_claims_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (logLane : Lane)
    (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat,
      ((outerState L hL e0 strat hb logLane
            (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2.claim,
        (outerState L hL e0 strat hb logLane
            (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2.truthClaim)
        = rawClaims L hL e0 strat hb (rawGateLaneOfReduced R tr a b) 3 T r := by
  intro r
  induction r with
  | zero => rfl
  | succ r2 ih =>
      have hoff : (outerState L hL e0 strat hb logLane
          (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r2).2.ownsNext = false := by
        have hgen : ∀ n : Nat, (outerState L hL e0 strat hb logLane
            (gateLaneOfReduced R (reducedTruthMessage tr) a b) T n).2.ownsNext = false := by
          intro n
          induction n with
          | zero => rfl
          | succ n2 ihn =>
              show (laneStep (laneStep (outerState L hL e0 strat hb logLane
                  (gateLaneOfReduced R (reducedTruthMessage tr) a b) T n2).2
                (logTriple L hL e0 strat hb n2 T))
                (gateTriple L hL e0 strat hb n2 T)).ownsNext = false
              rw [laneStep_active, laneStep_active, ihn]
              rfl
        exact hgen r2
      have hown : (laneStep (outerState L hL e0 strat hb logLane
          (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r2).2
          (logTriple L hL e0 strat hb r2 T)).ownsNext = true := by
        rw [laneStep_active, hoff]
        rfl
      have hmsg := gate_state_message_of_reduced L hL e0 strat hb R tr a b logLane T r2
      have htr := gate_state_truth_of_reduced L hL e0 strat hb R tr a b logLane T r2
      have hhist := reduced_history_of_table_view L hL e0 strat hb T r2
      show ((laneStep (laneStep (outerState L hL e0 strat hb logLane
              (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r2).2
            (logTriple L hL e0 strat hb r2 T)) (gateTriple L hL e0 strat hb r2 T)).claim,
          (laneStep (laneStep (outerState L hL e0 strat hb logLane
              (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r2).2
            (logTriple L hL e0 strat hb r2 T)) (gateTriple L hL e0 strat hb r2 T)).truthClaim)
        = rawClaims L hL e0 strat hb (rawGateLaneOfReduced R tr a b) 3 T (r2 + 1)
      rw [lane_step_claim_active _ _ hown, lane_step_truth_claim_active _ _ hown,
        lane_step_claim_inactive _ _ hoff, lane_step_truth_claim_inactive _ _ hoff,
        hmsg, htr, raw_claims_succ, ← ih]
      show (OuterRound.evaluate _ _ _, OuterRound.evaluate _ _ _)
        = (OuterRound.evaluate _ ((R r2 (reducedHistory
              (tableView L hL e0 strat hb T) r2)).2.map OuterRound.lift) _,
           OuterRound.evaluate _ (tr r2 (reducedHistory (tableView L hL e0 strat hb T) r2)) _)
      rw [hhist]
      rfl

/-- (8) **THE RAW TARGET AND THE ADOPTED LANE TARGET ARE THE SAME SET**, at the
reduced pairing. -/
theorem raw_log_target_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (gateLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    rawTarget L hL e0 strat hb (rawLogLaneOfReduced R tr a b) 0 r T
      = logTarget L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
          gateLane r T := by
  have hown : (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
      gateLane T r).1.ownsNext = true :=
    outer_state_log_owns L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
      gateLane T r
  have hcl := log_claims_of_reduced L hL e0 strat hb R tr a b gateLane T r
  have hc1 : (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
      gateLane T r).1.claim
      = (rawClaims L hL e0 strat hb (rawLogLaneOfReduced R tr a b) 0 T r).1 :=
    congrArg Prod.fst hcl
  have hc2 : (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
      gateLane T r).1.truthClaim
      = (rawClaims L hL e0 strat hb (rawLogLaneOfReduced R tr a b) 0 T r).2 :=
    congrArg Prod.snd hcl
  have hmsg := log_state_message_of_reduced L hL e0 strat hb R tr a b gateLane T r
  have htr := log_state_truth_of_reduced L hL e0 strat hb R tr a b gateLane T r
  have hhist := reduced_history_of_table_view L hL e0 strat hb T r
  have hrawmsg : (rawLogLaneOfReduced R tr a b).message r (tableView L hL e0 strat hb T)
      = (R r (outerHistory L hL e0 strat hb T r)).1.map OuterRound.lift := by
    show (R r (reducedHistory (tableView L hL e0 strat hb T) r)).1.map OuterRound.lift = _
    rw [hhist]
  have hrawtr : (rawLogLaneOfReduced R tr a b).truth r (tableView L hL e0 strat hb T)
      = tr r (outerHistory L hL e0 strat hb T r) := by
    show tr r (reducedHistory (tableView L hL e0 strat hb T) r) = _
    rw [hhist]
  have hbad : (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
        gateLane T r).1.badSet
      = ConditionalSoundness.roundBadSet
          (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
            gateLane T r).1.claim
          (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
            gateLane T r).1.truthClaim
          ⟨(outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
              gateLane T r).1.message [],
            (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
              gateLane T r).1.truth [], 0⟩ := by
    show (if (outerState L hL e0 strat hb (logLaneOfReduced R (reducedTruthMessage tr) a b)
        gateLane T r).1.ownsNext then ConditionalSoundness.roundBadSet _ _ ⟨_, _, 0⟩ else ∅) = _
    rw [hown, if_pos rfl]
  rw [logTarget, laneBad, rawTarget, rawBadSet, hbad, hmsg, htr, hc1, hc2, hrawmsg, hrawtr]

theorem raw_gate_target_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (tr : Nat → List Element → List Element) (a b : Element) (logLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    rawTarget L hL e0 strat hb (rawGateLaneOfReduced R tr a b) 3 r T
      = gateTarget L hL e0 strat hb logLane
          (gateLaneOfReduced R (reducedTruthMessage tr) a b) r T := by
  have hoff : (outerState L hL e0 strat hb logLane
      (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2.ownsNext = false := by
    have hgen : ∀ n : Nat, (outerState L hL e0 strat hb logLane
        (gateLaneOfReduced R (reducedTruthMessage tr) a b) T n).2.ownsNext = false := by
      intro n
      induction n with
      | zero => rfl
      | succ n2 ihn =>
          show (laneStep (laneStep (outerState L hL e0 strat hb logLane
              (gateLaneOfReduced R (reducedTruthMessage tr) a b) T n2).2
            (logTriple L hL e0 strat hb n2 T))
            (gateTriple L hL e0 strat hb n2 T)).ownsNext = false
          rw [laneStep_active, laneStep_active, ihn]
          rfl
    exact hgen r
  have hown : (laneStep (outerState L hL e0 strat hb logLane
      (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
      (logTriple L hL e0 strat hb r T)).ownsNext = true := by
    rw [laneStep_active, hoff]
    rfl
  have hcl := gate_claims_of_reduced L hL e0 strat hb R tr a b logLane T r
  have hc1 : (outerState L hL e0 strat hb logLane
      (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2.claim
      = (rawClaims L hL e0 strat hb (rawGateLaneOfReduced R tr a b) 3 T r).1 :=
    congrArg Prod.fst hcl
  have hc2 : (outerState L hL e0 strat hb logLane
      (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2.truthClaim
      = (rawClaims L hL e0 strat hb (rawGateLaneOfReduced R tr a b) 3 T r).2 :=
    congrArg Prod.snd hcl
  have hmsg := gate_state_message_of_reduced L hL e0 strat hb R tr a b logLane T r
  have htr := gate_state_truth_of_reduced L hL e0 strat hb R tr a b logLane T r
  have hhist := reduced_history_of_table_view L hL e0 strat hb T r
  have hrawmsg : (rawGateLaneOfReduced R tr a b).message r (tableView L hL e0 strat hb T)
      = (R r (outerHistory L hL e0 strat hb T r)).2.map OuterRound.lift := by
    show (R r (reducedHistory (tableView L hL e0 strat hb T) r)).2.map OuterRound.lift = _
    rw [hhist]
  have hrawtr : (rawGateLaneOfReduced R tr a b).truth r (tableView L hL e0 strat hb T)
      = tr r (outerHistory L hL e0 strat hb T r) := by
    show tr r (reducedHistory (tableView L hL e0 strat hb T) r) = _
    rw [hhist]
  have hbad : (laneStep (outerState L hL e0 strat hb logLane
        (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
        (logTriple L hL e0 strat hb r T)).badSet
      = ConditionalSoundness.roundBadSet
          (laneStep (outerState L hL e0 strat hb logLane
            (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
            (logTriple L hL e0 strat hb r T)).claim
          (laneStep (outerState L hL e0 strat hb logLane
            (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
            (logTriple L hL e0 strat hb r T)).truthClaim
          ⟨(laneStep (outerState L hL e0 strat hb logLane
              (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
              (logTriple L hL e0 strat hb r T)).message [],
            (laneStep (outerState L hL e0 strat hb logLane
              (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
              (logTriple L hL e0 strat hb r T)).truth [], 0⟩ := by
    show (if (laneStep (outerState L hL e0 strat hb logLane
        (gateLaneOfReduced R (reducedTruthMessage tr) a b) T r).2
        (logTriple L hL e0 strat hb r T)).ownsNext then
      ConditionalSoundness.roundBadSet _ _ ⟨_, _, 0⟩ else ∅) = _
    rw [hown, if_pos rfl]
  rw [gateTarget, laneBad, rawTarget, rawBadSet, hbad, hmsg, htr,
    lane_step_claim_inactive _ _ hoff, lane_step_truth_claim_inactive _ _ hoff,
    hc1, hc2, hrawmsg, hrawtr]

/-- (8) The adopted `logTriple` and `gateTriple` ARE the stage triples at the
lane counters `0` and `3` of the round's own stage -- the shape sections 1 to 7
are written in. -/
theorem log_triple_is_stage_triple (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    logTriple L hL e0 strat hb r T = stageTriple L hL e0 strat hb (roundStage r) 0 T := rfl

theorem gate_triple_is_stage_triple (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    gateTriple L hL e0 strat hb r T = stageTriple L hL e0 strat hb (roundStage r) 3 T := rfl

/-- (8) **THE EVENTS COINCIDE.**  On the reduced-history subclass the raw machinery
of sections 1 to 7 bounds THE VERY SAME EVENT the adopted
`OuterLaneTransport.reduced_outer_lane_bad_draw_probability_le` bounds, so the
adopted section 8 is a special case of this module and nothing has been weakened
in getting here. -/
theorem raw_outer_bad_event_of_reduced (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (R : ReducedStrategy)
    (trlog trgate : Nat → List Element → List Element) (a1 b1 a2 b2 : Element) (d : Nat) :
    rawOuterBadEvent L hL e0 strat hb (rawLogLaneOfReduced R trlog a1 b1)
        (rawGateLaneOfReduced R trgate a2 b2) d
      = outerLaneBadEvent L hL e0 strat hb
          (logLaneOfReduced R (reducedTruthMessage trlog) a1 b1)
          (gateLaneOfReduced R (reducedTruthMessage trgate) a2 b2) d := by
  rw [rawOuterBadEvent, outerLaneBadEvent]
  refine Finset.biUnion_congr rfl (fun r _ => ?_)
  rw [rawBothBadEvent, roundBadEvent]
  refine congrArg₂ (fun x y => x ∪ y) ?_ ?_
  · rw [rawRoundBadEvent, roundLogBadEvent]
    refine Finset.ext (fun T => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [raw_log_target_of_reduced L hL e0 strat hb R trlog a1 b1
      (gateLaneOfReduced R (reducedTruthMessage trgate) a2 b2) r T,
      log_triple_is_stage_triple L hL e0 strat hb r T]
  · rw [rawRoundBadEvent, roundGateBadEvent]
    refine Finset.ext (fun T => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [raw_gate_target_of_reduced L hL e0 strat hb R trgate a2 b2
      (logLaneOfReduced R (reducedTruthMessage trlog) a1 b1) r T,
      gate_triple_is_stage_triple L hL e0 strat hb r T]

/-! ## 9. THE FULL `combinedBound` CONSTANT FOR RAW LANES -/

/-- **THE FULL BAD EVENT AT RAW LANES.**  The two RAW outer lanes, the adopted
`ReducedFullTransport.gateTauBadEvent` and the adopted
`ReducedFullTransport.gateAlphaBadEvent`.  The tau and alpha events are the
adopted ones REUSED VERBATIM: as that module's header records, their bad sets are
indexed by `g`, `rows` and `coeffsOf` alone -- FIXED DATA, bound outside the
oracle law, mentioning no round message, no lane and no table -- so nothing about
them changes when the outer lanes stop factoring through the reduced history. -/
noncomputable def rawFullBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  (rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      ∪ gateTauBadEvent L hL e0 strat hb d g)
    ∪ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf

theorem mem_raw_full_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (d rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf ↔
      (T ∈ rawOuterBadEvent L hL e0 strat hb logLane gateLane d ∨
        T ∈ gateTauBadEvent L hL e0 strat hb d g ∨
        T ∈ gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf) := by
  simp only [rawFullBadEvent, Finset.mem_union, or_assoc]

open Classical in
/-- (9) **THE FULL BAD-DRAW BOUND AT RAW LANES.**  The three masses are conditioned
on NESTED no-clash events -- `22 + 5 d` for the rounds, `22` for the block-`0`
squeezes, and the adopted `OuterLaneTransport.stage_no_clash_mono` puts the former
inside the latter -- so ONE complement term pays for all three, exactly as in the
adopted `ReducedFullTransport.full_bad_draw_probability_le`. -/
theorem raw_full_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (d q rows constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hnest : stageNoClash L hL e0 strat hb (22 + 5 * d)
      ⊆ stageNoClash L hL e0 strat hb deriveStage :=
    stage_no_clash_mono L hL e0 strat hb deriveStage (22 + 5 * d) (by rw [deriveStage]; omega)
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hsplit : rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)
      = ((rawOuterBadEvent L hL e0 strat hb logLane gateLane d
            ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
          ∪ (gateTauBadEvent L hL e0 strat hb d g
            ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)))
        ∪ (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
            ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)) := by
    rw [rawFullBadEvent, Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
  have hu2 : oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL e0 strat hb logLane gateLane d rows g coeffsOf
          ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
      ≤ oracleProbability (boundedQueries L)
          ((rawOuterBadEvent L hL e0 strat hb logLane gateLane d
              ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
            ∪ (gateTauBadEvent L hL e0 strat hb d g
              ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)))
        + oracleProbability (boundedQueries L)
            (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
              ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)) := by
    rw [hsplit]
    exact oracle_probability_union_le (boundedQueries L) _ _
  have hu3 := oracle_probability_union_le (boundedQueries L)
    (rawOuterBadEvent L hL e0 strat hb logLane gateLane d
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    (gateTauBadEvent L hL e0 strat hb d g ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
  have houter := raw_no_clash_mass_le L hL e0 strat hb logLane gateLane hlcau hgcau 5 (q + 2)
    hlog hgate (22 + 5 * d) d (fun r hr => round_stage_le r d hr)
  rw [round_terms_sum d q] at houter
  have htausub : gateTauBadEvent L hL e0 strat hb d g
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)
      ⊆ (stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          tauRead L hL e0 strat hb d T ∈ ChallengeUnionBound.productEvent d
            (ZeroCheckSemantics.zeroCheckBadSet d g)) := by
    rw [gateTauBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have htau : oracleProbability (boundedQueries L)
      (gateTauBadEvent L hL e0 strat hb d g ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
      ≤ ChallengeUnionBound.tauTerm d :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ htausub)
      (gate_tau_no_clash_mass_le L hL e0 strat hb d g hdu)
  have halphasub : gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d)
      ⊆ (stageNoClash L hL e0 strat hb deriveStage).filter (fun T =>
          stageTriple L hL e0 strat hb deriveStage (alphaBase d) T
            ∈ OuterChallenge.tupleEvent
                (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)) := by
    rw [gateAlphaBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have halpha : oracleProbability (boundedQueries L)
      (gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf
        ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
      ≤ ChallengeUnionBound.alphaTerm rows constraints :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ halphasub)
      (gate_alpha_no_clash_mass_le L hL e0 strat hb d rows constraints coeffsOf hdu hclen)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
      ≤ ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL e0 strat hb (22 + 5 * d)
  linarith

/-- (9) **THE SAME, WITH THE CONSTANT READ OFF AS THE ADOPTED `combinedBound`.**
At `rows = 2 ^ degreeBits` the three terms ARE
`ChallengeUnionBound.combinedBound degreeBits quotientDegree degreeBits constraints`,
term for term, with nothing added and nothing dropped -- and now for RAW lanes. -/
theorem raw_full_bad_draw_probability_le_combined (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : RawLane) (hlcau : RawLaneCausal logLane)
    (hgcau : RawLaneCausal gateLane) (d q constraints : Nat) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : RawLaneBounded logLane 5) (hgate : RawLaneBounded gateLane (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL e0 strat hb logLane gateLane d (2 ^ d) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := raw_full_bad_draw_probability_le L hL e0 strat hb logLane gateLane hlcau hgcau
    d q (2 ^ d) constraints g coeffsOf hdu hlog hgate hclen
  rw [ChallengeUnionBound.combinedBound]
  exact h

/-- (9) **THE FULL `combinedBound` CONSTANT FOR A PROVER THAT READS RAW BLOCKS.**
The strategy is `strategicShape c s S` for an arbitrary `RoundCausal S`, the two
outer lanes are ITS OWN, and the constant is the WHOLE adopted
`ChallengeUnionBound.combinedBound d q d constraints` plus ONE chain clash term.
READ THE HONESTY HEADER: the index lanes are NOT included. -/
theorem strategic_raw_full_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (hS : RoundCausal S)
    (hb : StrategyBounded L (strategicShape c s S))
    (trlog trgate : Nat → (Nat → Nat → Block) → List Element)
    (htrlog : RawCausal trlog) (htrgate : RawCausal trgate)
    (a1 b1 a2 b2 : Element) (d q constraints : Nat) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hSlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hSgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ q + 2)
    (hlenlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (trlog r ch).length ≤ 5)
    (hlengate : ∀ (r : Nat) (ch : Nat → Nat → Block), (trgate r ch).length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (rawLogLaneOfStrategy S trlog a1 b1) (rawGateLaneOfStrategy S trgate a2 b2)
          d (2 ^ d) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  raw_full_bad_draw_probability_le_combined L hL OuterInitial.zeroDigest (strategicShape c s S) hb
    (rawLogLaneOfStrategy S trlog a1 b1) (rawGateLaneOfStrategy S trgate a2 b2)
    (raw_log_lane_causal S hS trlog htrlog a1 b1) (raw_gate_lane_causal S hS trgate htrgate a2 b2)
    d q constraints g coeffsOf hdu
    (raw_log_lane_bounded S trlog a1 b1 5 hSlog hlenlog)
    (raw_gate_lane_bounded S trgate a2 b2 (q + 2) hSgate hlengate) hclen

/-! ## 10. NON-DEGENERACY, A GENUINELY RAW PROVER, AND THE CLOSED INSTANCE -/

/-- THE HONEST ROUND MESSAGE OF A PROVER THAT HAS NOTHING TO SAY: the constant
empty list.  It obeys the protocol's causality and every degree bound, so the
`trlog` / `trgate` hypotheses of sections 7 and 9 are DISCHARGEABLE and the closed
instances below leave nothing open. -/
def rawZeroTruth : Nat → (Nat → Nat → Block) → List Element := fun _ _ => []

theorem raw_zero_truth_causal : RawCausal rawZeroTruth := fun _ _ _ _ => rfl

theorem raw_zero_truth_length (bd : Nat) (r : Nat) (ch : Nat → Nat → Block) :
    (rawZeroTruth r ch).length ≤ bd := Nat.zero_le _

/-- (10) **A ROUND-`0` RAW TARGET IS INHABITED WHEN THE TWO CLAIMS DIFFER AND THE
TWO ROUND POLYNOMIALS MEET.**  The adopted
`ConditionalSoundness.round_agreement_of_ne` at the `challenge` field the adopted
`roundBadSet` does not look at, pushed to the digest alphabet by the adopted
`JointChallengeSpace.mem_tupleEvent`.  Stated over an ABSTRACT lane, as the adopted
`OuterLaneTransport.lane_bad_set_mem_of_agreement` is, so that no tactic is ever
asked to decide an equality of two concrete `Element`s: the adopted `Fintype`
instance on `Element` is a `Fin` equivalence of astronomical size, so a `whnf`
that gets past the adopted `roundBadSet`'s `if a = b` diverges.  This is the
adopted `OuterLaneTransport` HONESTY (vii) constraint, and it is a hard one. -/
theorem raw_target_zero_nonempty_of_agreement (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (lane : RawLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) (ds : OuterChallenge.DigestTriple)
    (hne : lane.claim ≠ lane.truthClaim)
    (he : (OuterRound.polynomial lane.claim
            (lane.message 0 (tableView L hL e0 strat hb T))).eval
          (OuterChallenge.reduceTriple ds)
        = (OuterRound.polynomial lane.truthClaim
            (lane.truth 0 (tableView L hL e0 strat hb T))).eval
          (OuterChallenge.reduceTriple ds)) :
    (rawTarget L hL e0 strat hb lane base 0 T).Nonempty := by
  have hc1 : (rawClaims L hL e0 strat hb lane base T 0).1 = lane.claim := rfl
  have hc2 : (rawClaims L hL e0 strat hb lane base T 0).2 = lane.truthClaim := rfl
  refine ⟨ds, ?_⟩
  rw [rawTarget, JointChallengeSpace.mem_tupleEvent, rawBadSet, hc1, hc2]
  exact ConditionalSoundness.round_agreement_of_ne lane.claim lane.truthClaim
    ⟨lane.message 0 (tableView L hL e0 strat hb T),
      lane.truth 0 (tableView L hL e0 strat hb T), OuterChallenge.reduceTriple ds⟩ hne he

/-- **A RAW LANE WHOSE ROUND-`0` BAD SET IS PROVABLY INHABITED.**  Its running claim
and the honest running claim DIFFER (`1` against `0`), so the adopted
`ConditionalSoundness.roundBadSet` does NOT take its diagonal branch, and its round
message `[1]` against the honest `[]` makes the two adopted round polynomials MEET
AT THE FIELD ZERO -- the adopted `OuterLaneTransport.separated_lane_agrees_at_zero`,
whose data this lane repeats at the raw domain. -/
def separatedRawLane : RawLane where
  message := fun _ _ => [1]
  truth := fun _ _ => []
  claim := 1
  truthClaim := 0

theorem separated_raw_lane_causal : RawLaneCausal separatedRawLane :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem separated_raw_lane_bounded : RawLaneBounded separatedRawLane 5 := by
  refine fun _ _ => ⟨?_, Nat.zero_le _⟩
  show ([(1 : Element)]).length ≤ 5
  decide

theorem separated_raw_lane_claims_differ :
    separatedRawLane.claim ≠ separatedRawLane.truthClaim := by
  show (1 : Element) ≠ 0
  exact fun h => zero_ne_one h.symm

theorem separated_raw_lane_agrees_at_zero (ch : Nat → Nat → Block) :
    (OuterRound.polynomial separatedRawLane.claim (separatedRawLane.message 0 ch)).eval
        (OuterChallenge.reduceTriple zeroDigestTriple)
      = (OuterRound.polynomial separatedRawLane.truthClaim (separatedRawLane.truth 0 ch)).eval
        (OuterChallenge.reduceTriple zeroDigestTriple) := separated_lane_agrees_at_zero

/-- (10) **SO THE PER-ROUND BOUND OF SECTION 4 IS NOT A BOUND ON AN EMPTY SET.**
Round `0`'s raw target of that lane contains the adopted
`OuterLaneTransport.zeroDigestTriple`, at EVERY strategy, EVERY counter base and
EVERY table. -/
theorem separated_raw_target_zero_nonempty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (base : Nat)
    (T : OracleTable (boundedQueries L)) :
    (rawTarget L hL e0 strat hb separatedRawLane base 0 T).Nonempty :=
  raw_target_zero_nonempty_of_agreement L hL e0 strat hb separatedRawLane base T
    zeroDigestTriple separated_raw_lane_claims_differ
    (separated_raw_lane_agrees_at_zero (tableView L hL e0 strat hb T))

/-- (10) **THE RAW VIEW AT THE ADOPTED `BirthdayClashBound.constantTable`.**  That
table answers every query with the adopted `OuterInitial.zeroDigest`, so the raw
view of sections 1 to 9 is that block at every stage and every counter.  This is
the concrete table the adopted `StrategyChainBound.constant_table_strategy_clashes`
uses, and section 2's machinery is defined at it. -/
theorem table_view_at_constant_table (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j cnt : Nat) :
    tableView L hL e0 strat hb (constantTable L) j cnt
      = OuterChallenge.digestBlock OuterInitial.zeroDigest := rfl

/-- (10) **AND THE INHABITED ROUND-`0` TARGET AT THAT CONCRETE TABLE.** -/
theorem separated_raw_target_zero_nonempty_at_constant_table (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat) (base : Nat) :
    (rawTarget L hL e0 strat hb separatedRawLane base 0 (constantTable L)).Nonempty :=
  separated_raw_target_zero_nonempty L hL e0 strat hb base (constantTable L)

/-- THE BLOCK WHOSE LITTLE-ENDIAN VALUE IS `1`, the companion of the adopted
`OuterLaneTransport.zeroDigestBlock`. -/
def oneDigestBlock : Block := ⟨Transcript.le 32 1, Transcript.le_length 32 1⟩

/-- A RAW CHALLENGE VIEW THAT DIFFERS FROM THE ALL-ZERO ONE AT STAGE `22` ALONE --
a stage which is NOT `roundStage i` for any `i`, since the round stages start at
`roundStage 0 = 27`. -/
def probeView (bl : Block) : Nat → Nat → Block :=
  fun j _ => if j = 22 then bl else zeroDigestBlock

theorem probe_view_agrees_at_round_stages (bl1 bl2 : Block) (i : Nat) :
    probeView bl1 (roundStage i) = probeView bl2 (roundStage i) := by
  funext _
  show (if roundStage i = 22 then bl1 else zeroDigestBlock)
    = (if roundStage i = 22 then bl2 else zeroDigestBlock)
  rw [if_neg (by rw [roundStage]; omega), if_neg (by rw [roundStage]; omega)]

/-- (10) **THE PAIRED LANE OF A GENUINELY RAW-BLOCK-READING PROVER.**  The adopted
`StrategyChainBound.challengeTruncatedMessage` is the prover the adopted
`OuterLaneTransport` header names as failing BOTH obstructions to a `Lane`
pairing: it reads stage `22 + 5 r`, which at `r = 0` is STAGE `22` and not a round
stage, and it reads the block through `Transcript.fromLe`, i.e. its full 256-bit
value.  Here is that fact as a theorem: two raw views that agree at EVERY round
stage -- so the adopted `OuterLaneTransport.reducedHistory` cannot tell them apart
-- give DIFFERENT round-`0` gate messages.  ITS LANE IS NONETHELESS BUILT, AND
BOUNDED, BY SECTIONS 7 AND 9. -/
theorem truncated_gate_lane_is_not_reduced_history (m : Verifier.CoupledMessage)
    (hm : m.2 ≠ []) (tr : Nat → (Nat → Nat → Block) → List Element) (a b : Element) :
    (rawGateLaneOfStrategy (challengeTruncatedMessage m) tr a b).message 0
        (probeView zeroDigestBlock)
      ≠ (rawGateLaneOfStrategy (challengeTruncatedMessage m) tr a b).message 0
          (probeView oneDigestBlock) := by
  have h0 : Transcript.fromLe (Transcript.le 32 0) = 0 :=
    Transcript.fromLe_le_roundtrip 32 0 (small_lt_byte_power 0 (by norm_num))
  have h1 : Transcript.fromLe (Transcript.le 32 1) = 1 :=
    Transcript.fromLe_le_roundtrip 32 1 (small_lt_byte_power 1 (by norm_num))
  intro hEq
  have h2 : (m.2.take (Transcript.fromLe (Transcript.le 32 0))).map OuterRound.lift
      = (m.2.take (Transcript.fromLe (Transcript.le 32 1))).map OuterRound.lift := hEq
  rw [h0, h1] at h2
  cases hmc : m.2 with
  | nil => exact hm hmc
  | cons x rest =>
      rw [hmc] at h2
      exact List.noConfusion (h2 : ([] : List Element) = [OuterRound.lift x])

/-- (10) **THE CLOSED INSTANCE FOR A RAW-BLOCK-READING PROVER, OUTER LANES.**  At
the envelope's thirteen coupled rounds, for the adopted
`StrategyChainBound.challengeTruncatedMessage` -- the very prover the adopted
`OuterLaneTransport` could not pair with a `Lane` -- and for THAT PROVER'S OWN two
raw lanes, the outer bad-draw mass is at most the adopted `outerTerm 13 8` plus
the adopted `3828 / |Block|`.  Neither the length budget nor `64 <= L` is a
hypothesis. -/
theorem raw_bound_at_thirteen (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (a1 b1 a2 b2 : Element)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2) (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (rawOuterBadEvent L (Nat.le_trans (by omega) hLq) OuterInitial.zeroDigest
          (strategicShape c s (challengeTruncatedMessage m))
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
          (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2) 13)
      ≤ ChallengeUnionBound.outerTerm 13 8 + 3828 / (Fintype.card Block : ℚ) := by
  have h := strategic_raw_outer_bad_draw_probability_le L (Nat.le_trans (by omega) hLq) c s
    (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    rawZeroTruth rawZeroTruth raw_zero_truth_causal raw_zero_truth_causal a1 b1 a2 b2 13 8
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    (raw_zero_truth_length 5) (raw_zero_truth_length (8 + 2))
  have harith : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  rw [harith] at h
  exact h

/-- (10) **AND WITH THE WHOLE `combinedBound`.**  The same prover, the same two raw
lanes, the adopted gate tau column and the adopted gate alpha row union added:
`ChallengeUnionBound.combinedBound 13 8 13 123` plus the adopted
`3828 / |Block|`. -/
theorem raw_full_bound_at_thirteen (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (a1 b1 a2 b2 : Element) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L (Nat.le_trans (by omega) hLq) OuterInitial.zeroDigest
          (strategicShape c s (challengeTruncatedMessage m))
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          (rawLogLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a1 b1)
          (rawGateLaneOfStrategy (challengeTruncatedMessage m) rawZeroTruth a2 b2)
          13 (2 ^ 13) g coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) := by
  have h := strategic_raw_full_bad_draw_probability_le L (Nat.le_trans (by omega) hLq) c s
    (challengeTruncatedMessage m) (challenge_truncated_round_causal m)
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    rawZeroTruth rawZeroTruth raw_zero_truth_causal raw_zero_truth_causal a1 b1 a2 b2
    13 8 123 g coeffsOf thirteen_counter_budget
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hmlog)
    (fun r ch => Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hmgate)
    (raw_zero_truth_length 5) (raw_zero_truth_length (8 + 2)) hclen
  have harith : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  rw [harith] at h
  exact h

/-- (10) **THE CLOSED BOUNDS ARE REAL NUMBERS STRICTLY BELOW `1`**, by the adopted
evaluations.  `Fintype.card Block` is never evaluated: it enters only through the
adopted lemmas.  READ HONESTY (v): THIS IS NOT THE PROTOCOL'S SOUNDNESS ERROR. -/
theorem raw_bound_at_thirteen_lt_one :
    ChallengeUnionBound.outerTerm 13 8 + 3828 / (Fintype.card Block : ℚ) < 1 :=
  outer_lane_bound_at_thirteen_lt_one

theorem raw_full_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) < 1 :=
  reduced_full_bound_at_thirteen_lt_one

end Audit.Wire3.RawBlockLanes
