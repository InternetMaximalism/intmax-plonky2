import Audit.Wire3.StrategyChainBound
import Audit.Wire3.OuterSequentialConditioning

/-!
# TRANSPORTING THE OUTER LANES' PER-ROUND CONDITIONING TO THE ORACLE TABLE

## WHAT THIS MODULE PROVES, AND WHAT IT DOES NOT -- READ THIS FIRST

The headline `outer_lane_bad_draw_probability_le` bounds, under the
random-oracle counting law on
`RandomOracleSqueezes.OracleTable (boundedQueries L)`, the mass of the event that
one of TWO INDEPENDENTLY QUANTIFIED `OuterSequentialConditioning.Lane`s has its
per-round bad set caught by the corresponding challenge triple OF A
STRATEGY-DRIVEN CHAIN.  The chain is the adopted
`StrategyChainBound.Strategy`'s own; the bad sets are the adopted lanes'.  THE
TWO ARE NOT THE SAME OBJECT AND NOTHING BELOW IDENTIFIES THEM.

A `Lane`'s round message is `Lane.message : List Element -> List Element`
applied to the REDUCED challenge prefix -- the `2 r` field elements
`OuterChallenge.reduceTriple` produces from the six counters of each of the
earlier `r` round stages (`outer_state_message`).  A `Strategy`'s round message
is a function of the RAW blocks `Nat -> Nat -> Block` at every stage and every
counter.  What the theorem transports is therefore PREFIX-DEPENDENT LANE
TRANSPORT: OSC's prefix-dependent per-round conditioning, carried from the ideal
`JointChallengeSpace.JointSpace` to the oracle table along a strategy-driven
chain.

SCB HONESTY (iii) -- the per-round decomposition in which ROUND `r`'s BAD SET IS
DETERMINED BY THE MESSAGE THE STRATEGY ITSELF CHOOSES -- IS THEREFORE NOT CLOSED
BY THIS MODULE.  Section 8 closes it for a SUBCLASS of strategies and for that
subclass only; see `REDUCED-HISTORY SUBCLASS` below.

## WHY `laneOfStrategy` IS NOT CONSTRUCTIBLE FOR A GENERAL `Strategy`

There is no function taking a `Strategy` to the `Lane` whose round messages are
that strategy's realized messages, for two independent reasons.

* DOMAIN.  A `Strategy` is handed `ch : Nat -> Nat -> Block`: the RAW 32-byte
  answer at EVERY stage `j` and EVERY counter `cnt`.  That includes the
  twenty-two relation-prefix stages, the four non-challenge frames of each
  round's absorb, and every counter at or above `6`.  A `Lane` is handed a
  `List Element` which, by `outer_state_message`, contains NOTHING BUT the
  reductions of counters `0, 1, 2, 3, 4, 5` at the round stages
  `roundStage i = 22 + (5 i + 5)`.  Most of the strategy's domain is simply
  absent from the lane's.
* LOSS.  Even a strategy that reads only those six counters at only those stages
  need not factor through the lane's argument, because
  `OuterChallenge.reduceTriple` is NOT injective: it maps the whole digest-triple
  alphabet onto `Element`, with fibres of size about
  `OuterChallenge.fiberCeiling ^ 3` (the adopted
  `OuterChallenge.fixed_point_set_preimage_bound` is exactly the statement that
  those fibres are that big).  A strategy may read the raw block and the lane
  cannot recover it.

THE CLOSED INSTANCE'S OWN STRATEGY FAILS BOTH.  The adopted
`StrategyChainBound.challengeTruncatedMessage` is
`fun m r ch => (m.1, m.2.take (Transcript.fromLe (ch (22 + 5 * r) 0).val))`.  It
reads stage `22 + 5 * r` at counter `0`; at `r = 0` that is STAGE `22`, which is
not `roundStage i` for any `i` (the round stages start at `roundStage 0 = 27`),
so that block is not in the lane's argument at all.  And it reads the block
through `Transcript.fromLe`, i.e. its full 256-bit value, so `List.take n` does
not factor through `reduceTriple` even where the stages do line up.  In the
closed instance of section 7 the prover's message therefore never enters any bad
set: the bad sets are `echoLane`'s and `coEchoLane`'s.

## WHAT IS PROVED

1. THE DIAGONAL FRESH STEP (sections 1 and 2).  SCB's section 3 conditions on ONE
   event and prescribes a CONSTANT set of answers; a per-round bad set is not
   constant -- it is whatever the history has made it.  `stage_peel_card` is the
   adopted `BirthdayClashBound.adaptive_fresh_step_card` at a singleton target
   with the conditioning event a PARAMETER (`StageStable`), `stage_triple_fibre_card`
   peels the three counters of one scheduled draw, and `stage_triple_target_card`
   is the diagonal statement: the conditioning event is partitioned by the VALUE
   of the target, the target is constant on each block of that partition, and

     `|{T in A | triple T in targ T}| * |DigestTriple| <= m * |A|`

   whenever `targ` never has more than `m` points and is unmoved by the three
   answers it is tested against.  `stage_triple_target_mass_le` is the mass form
   and `strategy_challenge_diagonal_fresh_uniform` the one-counter form: the
   adopted `adaptive_fresh_step` ALREADY allows a table-dependent target, and
   what the transport supplies is the proof that a lane's round bad set meets its
   hypothesis.  THIS IS THE HONEST TECHNICAL CORE OF THE MODULE and it is
   independent of whose messages the bad sets come from.
2. THE ROUND SCHEDULE (section 3).  `roundStage r = 22 + (5 r + 5)` is the stage
   the adopted `ConcreteChainThreading.run_round_digest_is_chain_digest` reads
   round `r`'s two challenges from; `logTriple` and `gateTriple` are the stage
   triples at the adopted `JointChallengeSpace.sourceCounter` values `0` and `3`.
   `outerState` drives the ADOPTED `OuterSequentialConditioning.laneStep` by the
   REALIZED triples in the adopted interleaved order, and `outer_state_reassign`
   is the transported `PrefixDependent`: the lane state before round `r` is a
   function of the answers at STRICTLY EARLIER stage digests, so round `r`'s own
   challenge answers cannot move it.  `log_target_reassign` and
   `gate_target_reassign` discharge the diagonal hypothesis for the two lanes.
3. THE UNION OVER THE ROUNDS (section 4).  The no-clash events are NESTED
   (`stage_no_clash_mono`), which makes each summand a FIXED-STAGE statement, and
   each is section 2's diagonal bound with the ADOPTED per-round cardinality
   bounds (`OuterSequentialConditioning.laneBad_card_le`, i.e. the adopted
   `ConditionalSoundness.round_bad_set_card` -- `5` on the log lane and
   `quotientDegree + 2` on the gate lane -- composed with the adopted
   `OuterChallenge.fixed_point_set_preimage_bound`).  `round_terms_sum` collects
   them into the EXACT adopted constant `ChallengeUnionBound.outerTerm`.
4. THE HEADLINE (section 5).  `outer_lane_bad_draw_probability_le`:

     `oracleProbability (boundedQueries L) (outerLaneBadEvent L hL e0 strat hb logLane gateLane d)`
       `<= ChallengeUnionBound.outerTerm d q`
          `+ (22 + 5 d) (22 + 5 d + 1) / 2 / |Block|`

   for EVERY `Strategy` and EVERY pair of lanes meeting the adopted degree
   bounds, THE TWO QUANTIFIED SEPARATELY.  The second term is the adopted
   `StrategyChainBound.strategy_chain_clash_probability_le`.
5. THE TRIPLES ARE THE RUN'S OWN DRAW (section 6).
   `strategic_run_log_draw_is_log_triple` and its gate twin identify the CHALLENGE
   TRIPLES bounded in section 4 with the adopted
   `InstalledRoundCommit.actualDigestDraw` at `Draw.outerLog r` and
   `Draw.outerGate r`, for a proof record carrying the messages the strategy
   really produced at that table; `realized_proof_witness` exhibits such a record,
   so those hypotheses are not vacuous.  THE MESSAGES ARE NOT IDENTIFIED -- only
   the challenges.
6. EMPTINESS, NON-EMPTINESS AND THE CLOSED INSTANCE (section 7).  A round's bad
   set CAN be empty: the adopted `ConditionalSoundness.roundBadSet a b r` is `∅`
   whenever `a = b`, and in the closed instance below it IS empty at the log
   lane's rounds `0` and `1` and at the gate lane's round `0`
   (`closed_log_target_zero_empty`, `closed_log_target_one_empty`,
   `closed_gate_target_zero_empty`), because `echoLane` and `coEchoLane` start
   with `claim = truthClaim = 0`.  `ownsNext = true` does NOT by itself make a bad
   set non-empty.  `separatedLane` is a lane at which round `0`'s bad set is
   PROVABLY NON-EMPTY (`separated_lane_round_zero_target_nonempty`: the all-zero
   digest triple is in it), so the per-round bound of section 4 is not a bound on
   an empty set in general.  `outer_lane_bound_at_thirteen` is the closed instance
   at the envelope's thirteen coupled rounds for the strategic prover of the
   adopted `StrategyChainBound.challengeTruncatedMessage`, with neither the length
   budget nor `64 <= L` left as a hypothesis:

     `<= ChallengeUnionBound.outerTerm 13 8 + 3828 / |Block|`,

   and `outer_lane_bound_at_thirteen_lt_one` records that this is strictly below
   `1`.  THE CLOSED INSTANCE CERTIFIES DISCHARGEABILITY OF THE HYPOTHESES, NOT
   THAT ANY BAD SET IT MENTIONS IS INHABITED.
7. THE REDUCED-HISTORY SUBCLASS (section 8).  `ReducedStrategy` is a prover whose
   round message is a function OF THE REDUCED ROUND-CHALLENGE HISTORY ALONE --
   exactly the argument a `Lane` is handed.  `strategyOfReduced` embeds it into
   the adopted `Strategy` (through the adopted `strategicShape`) and
   `logLaneOfReduced` / `gateLaneOfReduced` build the matching lanes.
   `log_lane_of_reduced_message_is_realized` and its gate twin PROVE that the
   lane's round-`r` message IS the strategy's realized round-`r` message, lifted
   by the adopted `OuterRound.lift`.  `reduced_outer_lane_bad_draw_probability_le`
   is the headline at that pairing: FOR THIS SUBCLASS IT IS A GENUINE ADAPTIVE
   UNION BOUND, i.e. SCB HONESTY (iii) for reduced-history provers.
   `previousChallengeMessage` is a non-trivial member -- its gate cell really
   depends on a reduced challenge it has read
   (`previous_challenge_message_depends`) -- and
   `previous_challenge_bound_at_thirteen` is its closed instance.
   RAW-BLOCK-READING STRATEGIES REMAIN OPEN.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  The fresh-query
lemma the whole argument rests on, the adopted
`BirthdayClashBound.fresh_coordinate_probability`, is the DEFINING property of a
random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed permutation by a table drawn from this law is an assumption with no
proof anywhere in this tree.

(ii) THE PROVER IS TRANSCRIPT-RESTRICTED, AND GRINDING IS EXCLUDED.  A
`StrategyChainBound.Strategy` is handed the stage digests of its own chain and
the oracle's answers at the CHALLENGE inputs of those digests, and nothing else:
IT MAKES NO ORACLE QUERIES OF ITS OWN.  A random-oracle-model Fiat--Shamir prover
that hashes candidate payloads itself and keeps the one whose digest collides --
GRINDING -- is NOT covered by anything below; the adopted `GrindingQueryBound`
covers only such a prover's CHAIN term, not the per-round decomposition proved
here.

(iii) THE LANE AND THE STRATEGY ARE PAIRED ONLY IN SECTION 8.  This is the
module's central limitation and it is restated here in full.  Sections 1 to 7
quantify over every `Strategy` and every pair of `Lane`s SEPARATELY.  A round's
bad set there is the LANE's, built from `Lane.message` applied to the reduced
challenge prefix; the strategy enters only by driving the chain whose stage
digests the challenge triples are read at.  So the event bounded is "the
strategy's realized challenges land in a fixed prefix-dependent family's bad
sets", NOT "the strategy's own messages are caught".  Section 8 repairs this for
`ReducedStrategy` only, and the paragraph WHY `laneOfStrategy` IS NOT
CONSTRUCTIBLE above says exactly why it cannot be repaired for a general
`Strategy`.  In particular, taking the bound of section 5 or 7 as a soundness
statement about an arbitrary adaptive prover would be WRONG.

(iv) THE LANES ARE THE OUTER SUMCHECK LANES, AND THE CONSTANT IS THE OUTER PART
OF `combinedBound` ONLY.  The additive constant of section 5 is
`ChallengeUnionBound.outerTerm degreeBits quotientDegree` -- that summand of
`ChallengeUnionBound.combinedBound` AND NO OTHER.  The `tauTerm` (the gate tau
zero-check column) and the `alphaTerm` (the gate alpha row union) are NOT
re-derived for an adaptive prover here: the adopted `CommitmentOrder` pins their
indices to material absorbed before these squeezes, so a prefix-frozen family is
the right model for them, but transporting THEIR masses to the oracle table is
not done below.  The index lanes, the WHIR folding transcript and the Merkle
openings are not in `combinedBound` at all and are excluded a fortiori.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The bound is on the mass
of one named event under the oracle law.  `outerTerm` covers the outer
round-agreement event alone; the deployed profile's design point is around a
hundred bits, and quoting the numbers of section 7 as the wire-v3 soundness error
would be wrong.  The meaning of the per-round bad sets is the adopted
`ConditionalSoundness` one -- GOOD-DRAW-CONDITIONAL, with that module's
assumption list untouched -- and nothing here instantiates it.

(vi) WHAT IS STILL MISSING FOR A RUN-LEVEL ADAPTIVE STATEMENT.  The adopted
`RandomOracleSqueezes.run_draw_probability_le_fibrewise` bounds the run's WHOLE
bad-draw mass for a FIXED proof by a Fubini over frame fibres; that argument does
not survive a table-dependent proof, and it is not repeated here.  What section 5 bounds is an event defined directly on the oracle table.  It is
NOT the adopted `RandomOracleSqueezes.runDrawEvent`, whose `Verifier.Proof` and
whose two lane lists are quantified OUTSIDE the law.  For the reduced-subclass
headline `reduced_outer_lane_bad_draw_probability_le` (outer event, claimed start
`0`), the adopted `RunLevelTransportAudit` (through `RawBlockLanes`'s
`raw_outer_bad_event_of_reduced`) shows it IS the same event once that proof and
those lists are replaced, table by table, by the ones the prover realizes there;
for the general section-5 headline at an arbitrary `Strategy` and `Lane` no such
identification exists.  The Fiat--Shamir half -- that the run's encoding draw is
`jointProbability`-distributed -- remains exactly as unformalized as the adopted
`JointChallengeSpace.DrawEncodesRun` header says, and nothing below is a claim
that Fiat--Shamir soundness has been established for an adaptive prover.

(vii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's
OWN definitions (`roundLogBadEvent`, `roundGateBadEvent`) and in the statement of
the generic helper `univ_filter_inter_subset`, which is quantified over an
ABSTRACT finite type and mentions no protocol object.  NO TACTIC OR TERM BELOW
EVER PUTS `Finset.univ` ON `Element` OR ON `OuterChallenge.DigestTriple` IN A
POSITION THAT CAN BE REDUCED.  That is a hard constraint, not a preference: the
adopted `Fintype` instances of those two types are built from `Fin` equivalences
of astronomical size, so any `whnf` reaching them diverges (this module carries
no `set_option maxRecDepth`, unlike the adopted modules it imports).  It is why
section 7 states its non-emptiness results as `Finset.Nonempty` rather than as a
bare membership at a concrete lane, why every digest-level membership goes
through the adopted `JointChallengeSpace.mem_tupleEvent`, and why
`tuple_event_empty` is proved from the adopted
`OuterChallenge.fixed_point_set_preimage_bound` -- a CARDINALITY bound -- rather
than by extensionality.  The same rule forbids a tactic from seeing
`Fintype.card Block` or `Fintype.card Element` in a `Nat` arithmetic goal:
`peel_three` does the only exponent bookkeeping and is stated over abstract
naturals.  Memberships over the table space are manipulated through `Finset`
equalities and generic helpers rather than pointwise.
-/

namespace Audit.Wire3.OuterLaneTransport

open Audit.Wire3
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound

/-! ## 1. THE DIAGONAL FRESH STEP: A TARGET THAT DEPENDS ON THE HISTORY -/

/-- The chain's no-clash event up to stage `j`, the conditioning event of the
adopted `StrategyChainBound` section 3. -/
def stageNoClash (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) : Finset (OracleTable (boundedQueries L)) :=
  noClash (strategySel L hL e0 strat hb) (avoidBase e0) j

/-- (1) The no-clash events are NESTED: a table whose first `n` stages do not
clash does not clash in its first `j ≤ n` stages either.  This is what turns each
round's step below into a FIXED-STAGE statement. -/
theorem stage_no_clash_mono (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j n : Nat) (h : j ≤ n) :
    stageNoClash L hL e0 strat hb n ⊆ stageNoClash L hL e0 strat hb j := by
  intro T hT
  rw [stageNoClash, mem_no_clash] at hT
  rw [stageNoClash, mem_no_clash]
  exact ⟨fun r s hrs hsj => hT.1 r s hrs (lt_of_lt_of_le hsj h),
    fun s hsj => hT.2 s (lt_of_lt_of_le hsj h)⟩

/-- **A CONDITIONING EVENT THE STAGE-`j` CHALLENGE ANSWERS CANNOT MOVE.**  `A`
sits inside the chain's no-clash event up to stage `j` and is closed under
overwriting the table at the stage-`j` challenge query of any counter in `C`.
The no-clash event itself is the basic example (`stage_stable_no_clash`); the
events used below are cut out of it BY THE HISTORY, which is exactly what the
adopted `StrategyChainBound` section 3 does not condition on. -/
def StageStable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (C : Finset Nat)
    (A : Finset (OracleTable (boundedQueries L))) : Prop :=
  (∀ T ∈ A, T ∈ stageNoClash L hL e0 strat hb j) ∧
  (∀ T ∈ A, ∀ c ∈ C, ∀ b : Block,
    reassign T (challengeSel L hL e0 strat hb j c T) b ∈ A)

/-- (1) Stability at a counter set gives stability at any subset of it. -/
theorem stage_stable_mono (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (C D : Finset Nat) (hCD : C ⊆ D)
    (A : Finset (OracleTable (boundedQueries L)))
    (h : StageStable L hL e0 strat hb j D A) : StageStable L hL e0 strat hb j C A :=
  ⟨h.1, fun T hT c hc b => h.2 T hT c (hCD hc) b⟩

/-- (1) The no-clash event is stage-stable, at every counter set: the adopted
`StrategyChainBound.no_clash_challenge_reassign`. -/
theorem stage_stable_no_clash (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (C : Finset Nat) :
    StageStable L hL e0 strat hb j C (stageNoClash L hL e0 strat hb j) :=
  ⟨fun _ hT => hT, fun T hT c _ b => no_clash_challenge_reassign L hL e0 strat hb j c T hT b⟩

/-- (1) A stage-stable event stays stage-stable when it is cut down by a
predicate the stage-`j` challenge answers cannot move. -/
theorem stage_stable_filter (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (C : Finset Nat)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : StageStable L hL e0 strat hb j C A)
    (P : OracleTable (boundedQueries L) → Prop) [DecidablePred P]
    (hP : ∀ T ∈ A, ∀ c ∈ C, ∀ b : Block,
      (P (reassign T (challengeSel L hL e0 strat hb j c T) b) ↔ P T)) :
    StageStable L hL e0 strat hb j C (A.filter P) := by
  refine ⟨fun T hT => hA.1 T (Finset.mem_filter.mp hT).1, fun T hT c hc b => ?_⟩
  obtain ⟨hTA, hTP⟩ := Finset.mem_filter.mp hT
  exact Finset.mem_filter.mpr ⟨hA.2 T hTA c hc b, (hP T hTA c hc b).mpr hTP⟩

/-- (1) **ONE PEELED COUNTER, AS AN EXACT COUNT.**  Exactly a `1 / |Block|` share
of a stage-stable conditioning event answers a prescribed block at the stage-`j`
challenge query of counter `a`.  This is the adopted
`BirthdayClashBound.adaptive_fresh_step_card` at a singleton target, with the
conditioning event a parameter. -/
theorem stage_peel_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j a : Nat)
    (A : Finset (OracleTable (boundedQueries L)))
    (hsub : ∀ T ∈ A, T ∈ stageNoClash L hL e0 strat hb j)
    (hclosed : ∀ T ∈ A, ∀ b : Block, reassign T (challengeSel L hL e0 strat hb j a T) b ∈ A)
    (b0 : Block) :
    (A.filter (fun T => T (challengeSel L hL e0 strat hb j a T) = b0)).card
        * Fintype.card Block = A.card := by
  have hfresh : FreshStep (boundedQueries L) A (challengeSel L hL e0 strat hb j a)
      (fun _ => ({b0} : Finset Block)) :=
    ⟨fun T hT b => hclosed T hT b,
     fun T hT b => challenge_sel_stable L hL e0 strat hb j a a T (hsub T hT) b,
     fun _ _ _ => rfl⟩
  have hcard := adaptive_fresh_step_card hfresh
  have hsum : ∑ _U in A, ({b0} : Finset Block).card = A.card := by
    rw [Finset.sum_const, Finset.card_singleton, smul_eq_mul, Nat.mul_one]
  rw [hsum] at hcard
  have hset : A.filter (fun T => T (challengeSel L hL e0 strat hb j a T) = b0)
      = A.filter (fun T =>
          T (challengeSel L hL e0 strat hb j a T) ∈ ({b0} : Finset Block)) := by
    apply Finset.ext
    intro T
    constructor
    · intro hT
      obtain ⟨hTA, hTv⟩ := Finset.mem_filter.mp hT
      exact Finset.mem_filter.mpr ⟨hTA, Finset.mem_singleton.mpr hTv⟩
    · intro hT
      obtain ⟨hTA, hTv⟩ := Finset.mem_filter.mp hT
      exact Finset.mem_filter.mpr ⟨hTA, Finset.mem_singleton.mp hTv⟩
  rw [hset]
  exact hcard

/-- (1) **OVERWRITING ONE STAGE-`j` CHALLENGE ANSWER LEAVES THE OTHER COUNTERS OF
THE SAME STAGE ALONE.**  Two counters below the adopted `Transcript.u64Limit` at
one digest are two different queries (the adopted
`StrategyChainBound.challenge_sel_ne_of_counter`), and the stage-`j` query itself
does not move (the adopted `challenge_sel_stable`). -/
theorem stage_answer_reassign_ne (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c c2 : Nat)
    (hc : c < Transcript.u64Limit) (hc2 : c2 < Transcript.u64Limit) (hne : c2 ≠ c)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j)
    (b : Block) :
    (reassign T (challengeSel L hL e0 strat hb j c T) b)
        (challengeSel L hL e0 strat hb j c2
          (reassign T (challengeSel L hL e0 strat hb j c T) b))
      = T (challengeSel L hL e0 strat hb j c2 T) := by
  rw [challenge_sel_stable L hL e0 strat hb j c c2 T hT b]
  exact reassign_off T _ _ b
    (challenge_sel_ne_of_counter L hL e0 strat hb j c2 c hc2 hc hne T)

/-- The three counters one scheduled draw is squeezed at: the adopted
`JointChallengeSpace.sourceCounter` of the draw and its two successors, exactly
the offsets of the adopted `RandomOracleSqueezes.squeezeInputAt`. -/
def tripleCounters (base : Nat) : Finset Nat := {base, base + 1, base + 2}

theorem mem_triple_counters (base c : Nat) :
    c ∈ tripleCounters base ↔ (c = base ∨ c = base + 1 ∨ c = base + 2) := by
  rw [tripleCounters, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]

/-- **THE DIGEST TRIPLE THE RUN READS AT STAGE `j` FROM COUNTER `base`.**  The
adopted `OuterChallenge.actualDigests` at the chain's own stage-`j` digest, read
off the table rather than off a hash (`stage_triple_is_actual_digests`). -/
def stageTriple (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j base : Nat) (T : OracleTable (boundedQueries L)) :
    OuterChallenge.DigestTriple :=
  (T (challengeSel L hL e0 strat hb j base T),
   T (challengeSel L hL e0 strat hb j (base + 1) T),
   T (challengeSel L hL e0 strat hb j (base + 2) T))

theorem stage_triple_eq_iff (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j base : Nat) (T : OracleTable (boundedQueries L))
    (ds : OuterChallenge.DigestTriple) :
    stageTriple L hL e0 strat hb j base T = ds ↔
      (T (challengeSel L hL e0 strat hb j base T) = ds.1 ∧
        T (challengeSel L hL e0 strat hb j (base + 1) T) = ds.2.1 ∧
        T (challengeSel L hL e0 strat hb j (base + 2) T) = ds.2.2) := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2) h⟩
  · intro h
    show ((T (challengeSel L hL e0 strat hb j base T),
      T (challengeSel L hL e0 strat hb j (base + 1) T),
      T (challengeSel L hL e0 strat hb j (base + 2) T)) : OuterChallenge.DigestTriple) = ds
    rw [h.1, h.2.1, h.2.2]

/-- (1) The digest-triple alphabet has `|Block| ^ 3` points, symbolically: the
adopted `OuterChallenge.digest_tuple_cardinality` and the adopted
`RandomOracleSqueezes.block_card_eq_word_size`.  No cardinality is ever
evaluated. -/
theorem digest_triple_card_as_blocks :
    Fintype.card OuterChallenge.DigestTriple = Fintype.card Block ^ 3 := by
  rw [OuterChallenge.digest_tuple_cardinality, block_card_eq_word_size]

/-- (1) Three peels, chained.  Stated over ABSTRACT naturals so that no tactic
ever sees `Fintype.card Block`. -/
theorem peel_three (x3 x2 x1 x0 cb : Nat) (h2 : x3 * cb = x2) (h1 : x2 * cb = x1)
    (h0 : x1 * cb = x0) : x3 * cb ^ 3 = x0 := by
  have hpow : cb ^ 3 = cb * cb * cb := by ring
  rw [hpow, ← Nat.mul_assoc, ← Nat.mul_assoc, h2, h1, h0]

/-- (1) **THE JOINT FIBRE COUNT AT ONE SCHEDULED DRAW.**  Conditioned on any
stage-stable event, each of the `|Block| ^ 3` digest triples is read at the
stage-`j` counters `base, base + 1, base + 2` by exactly a
`1 / |Block| ^ 3` share of it.  Three peels of `stage_peel_card`; the
prescriptions already made survive each later peel because two counters at one
digest are two different queries. -/
theorem stage_triple_fibre_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j base : Nat)
    (hbase : base + 2 < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : StageStable L hL e0 strat hb j (tripleCounters base) A)
    (ds : OuterChallenge.DigestTriple) :
    (A.filter (fun T => stageTriple L hL e0 strat hb j base T = ds)).card
        * Fintype.card OuterChallenge.DigestTriple = A.card := by
  have hu0 : base < Transcript.u64Limit := by omega
  have hu1 : base + 1 < Transcript.u64Limit := by omega
  have hm0 : base ∈ tripleCounters base :=
    (mem_triple_counters base base).mpr (Or.inl rfl)
  have hm1 : base + 1 ∈ tripleCounters base :=
    (mem_triple_counters base (base + 1)).mpr (Or.inr (Or.inl rfl))
  have hm2 : base + 2 ∈ tripleCounters base :=
    (mem_triple_counters base (base + 2)).mpr (Or.inr (Or.inr rfl))
  have hsubA : ∀ T ∈ A, T ∈ stageNoClash L hL e0 strat hb j := hA.1
  have hA1sub : ∀ T ∈ A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1),
      T ∈ stageNoClash L hL e0 strat hb j :=
    fun T hT => hsubA T (Finset.mem_filter.mp hT).1
  have hA1closed : ∀ T ∈ A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1),
      ∀ b : Block,
        reassign T (challengeSel L hL e0 strat hb j (base + 1) T) b
          ∈ A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1) := by
    intro T hT b
    obtain ⟨hTA, hTv⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨hA.2 T hTA (base + 1) hm1 b, ?_⟩
    rw [stage_answer_reassign_ne L hL e0 strat hb j (base + 1) base hu1 hu0 (by omega) T
      (hsubA T hTA) b]
    exact hTv
  have hA2sub : ∀ T ∈ (A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1)).filter
        (fun T => T (challengeSel L hL e0 strat hb j (base + 1) T) = ds.2.1),
      T ∈ stageNoClash L hL e0 strat hb j :=
    fun T hT => hA1sub T (Finset.mem_filter.mp hT).1
  have hA2closed : ∀ T ∈ (A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1)).filter
        (fun T => T (challengeSel L hL e0 strat hb j (base + 1) T) = ds.2.1),
      ∀ b : Block,
        reassign T (challengeSel L hL e0 strat hb j (base + 2) T) b
          ∈ (A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1)).filter
              (fun T => T (challengeSel L hL e0 strat hb j (base + 1) T) = ds.2.1) := by
    intro T hT b
    obtain ⟨hT1, hTv1⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTA, hTv0⟩ := Finset.mem_filter.mp hT1
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hA.2 T hTA (base + 2) hm2 b, ?_⟩, ?_⟩
    · rw [stage_answer_reassign_ne L hL e0 strat hb j (base + 2) base hbase hu0 (by omega) T
        (hsubA T hTA) b]
      exact hTv0
    · rw [stage_answer_reassign_ne L hL e0 strat hb j (base + 2) (base + 1) hbase hu1 (by omega) T
        (hsubA T hTA) b]
      exact hTv1
  have h0 := stage_peel_card L hL e0 strat hb j base A hsubA
    (fun T hT b => hA.2 T hT base hm0 b) ds.1
  have h1 := stage_peel_card L hL e0 strat hb j (base + 1)
    (A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1))
    hA1sub hA1closed ds.2.1
  have h2 := stage_peel_card L hL e0 strat hb j (base + 2)
    ((A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1)).filter
      (fun T => T (challengeSel L hL e0 strat hb j (base + 1) T) = ds.2.1))
    hA2sub hA2closed ds.2.2
  have hset : A.filter (fun T => stageTriple L hL e0 strat hb j base T = ds)
      = ((A.filter (fun T => T (challengeSel L hL e0 strat hb j base T) = ds.1)).filter
          (fun T => T (challengeSel L hL e0 strat hb j (base + 1) T) = ds.2.1)).filter
          (fun T => T (challengeSel L hL e0 strat hb j (base + 2) T) = ds.2.2) := by
    apply Finset.ext
    intro T
    constructor
    · intro hT
      obtain ⟨hTA, hTv⟩ := Finset.mem_filter.mp hT
      obtain ⟨hv0, hv1, hv2⟩ := (stage_triple_eq_iff L hL e0 strat hb j base T ds).mp hTv
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hTA, hv0⟩, hv1⟩,
        hv2⟩
    · intro hT
      obtain ⟨hT2, hv2⟩ := Finset.mem_filter.mp hT
      obtain ⟨hT1, hv1⟩ := Finset.mem_filter.mp hT2
      obtain ⟨hTA, hv0⟩ := Finset.mem_filter.mp hT1
      exact Finset.mem_filter.mpr
        ⟨hTA, (stage_triple_eq_iff L hL e0 strat hb j base T ds).mpr ⟨hv0, hv1, hv2⟩⟩
  rw [hset, digest_triple_card_as_blocks]
  exact peel_three _ _ _ _ (Fintype.card Block) h2 h1 h0

/-! ## 2. THE DIAGONAL BOUND: THE BAD SET IS A FUNCTION OF THE HISTORY -/

/-- (2) **THE DIAGONAL BOUND AT ONE SCHEDULED DRAW, COUNTING FORM.**  The bad set
`targ T` is NOT a constant of the experiment: it is whatever the history has made
it at the table `T`.  What is asked of it is only that the three stage-`j`
challenge answers it is tested against cannot move it -- which is exactly what
"the message is chosen before the challenge is squeezed" means.  The count is
then the same as for a constant target: the conditioning event is partitioned by
the VALUE of `targ`, the target is constant on each block of that partition, and
`stage_triple_fibre_card` applies there. -/
theorem stage_triple_target_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j base : Nat)
    (hbase : base + 2 < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : StageStable L hL e0 strat hb j (tripleCounters base) A)
    (targ : OracleTable (boundedQueries L) → Finset OuterChallenge.DigestTriple)
    (hinv : ∀ T ∈ A, ∀ c ∈ tripleCounters base, ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = targ T)
    (m : Nat) (hm : ∀ T ∈ A, (targ T).card ≤ m) :
    (A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).card
        * Fintype.card OuterChallenge.DigestTriple ≤ m * A.card := by
  have hfib1 : (A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).card
      = ∑ S in A.image targ,
          ((A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).filter
            (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun x hx => Finset.mem_image_of_mem targ (Finset.mem_filter.mp hx).1)
  have hfib2 : A.card = ∑ S in A.image targ, (A.filter (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem targ hx)
  have key : ∀ S ∈ A.image targ,
      ((A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).filter
          (fun T => targ T = S)).card * Fintype.card OuterChallenge.DigestTriple
        ≤ m * (A.filter (fun T => targ T = S)).card := by
    intro S hS
    obtain ⟨T0, hT0A, hT0⟩ := Finset.mem_image.mp hS
    have hScard : S.card ≤ m := by
      rw [← hT0]
      exact hm T0 hT0A
    have hAS : StageStable L hL e0 strat hb j (tripleCounters base)
        (A.filter (fun T => targ T = S)) := by
      refine stage_stable_filter L hL e0 strat hb j (tripleCounters base) A hA
        (fun T => targ T = S) (fun T hT c hc b => ?_)
      show targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = S ↔ targ T = S
      rw [hinv T hT c hc b]
    have hEq : (A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).filter
          (fun T => targ T = S)
        = (A.filter (fun T => targ T = S)).filter
            (fun T => stageTriple L hL e0 strat hb j base T ∈ S) := by
      apply Finset.ext
      intro T
      constructor
      · intro hT
        obtain ⟨hT1, hTS⟩ := Finset.mem_filter.mp hT
        obtain ⟨hTA, hTd⟩ := Finset.mem_filter.mp hT1
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hTA, hTS⟩, hTS ▸ hTd⟩
      · intro hT
        obtain ⟨hT1, hTd⟩ := Finset.mem_filter.mp hT
        obtain ⟨hTA, hTS⟩ := Finset.mem_filter.mp hT1
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hTA, hTS ▸ hTd⟩, hTS⟩
    have hinner : ∀ ds ∈ S,
        (((A.filter (fun T => targ T = S)).filter
            (fun T => stageTriple L hL e0 strat hb j base T ∈ S)).filter
          (fun T => stageTriple L hL e0 strat hb j base T = ds)).card
        = ((A.filter (fun T => targ T = S)).filter
            (fun T => stageTriple L hL e0 strat hb j base T = ds)).card := by
      intro ds hds
      congr 1
      apply Finset.ext
      intro T
      constructor
      · intro hT
        obtain ⟨hT1, hTe⟩ := Finset.mem_filter.mp hT
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hT1).1, hTe⟩
      · intro hT
        obtain ⟨hT1, hTe⟩ := Finset.mem_filter.mp hT
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hT1, hTe ▸ hds⟩, hTe⟩
    have hsplit : ((A.filter (fun T => targ T = S)).filter
          (fun T => stageTriple L hL e0 strat hb j base T ∈ S)).card
        = ∑ ds in S, ((A.filter (fun T => targ T = S)).filter
            (fun T => stageTriple L hL e0 strat hb j base T = ds)).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun T => stageTriple L hL e0 strat hb j base T) (t := S)
        (fun x hx => (Finset.mem_filter.mp hx).2)]
      exact Finset.sum_congr rfl hinner
    rw [hEq, hsplit, Finset.sum_mul,
      Finset.sum_congr rfl (fun ds _ =>
        stage_triple_fibre_card L hL e0 strat hb j base hbase
          (A.filter (fun T => targ T = S)) hAS ds),
      Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hScard
  calc (A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).card
          * Fintype.card OuterChallenge.DigestTriple
      = ∑ S in A.image targ,
          ((A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).filter
            (fun T => targ T = S)).card * Fintype.card OuterChallenge.DigestTriple := by
        rw [hfib1, Finset.sum_mul]
    _ ≤ ∑ S in A.image targ, m * (A.filter (fun T => targ T = S)).card :=
        Finset.sum_le_sum key
    _ = m * A.card := by rw [← Finset.mul_sum, ← hfib2]

/-- (2) **THE DIAGONAL BOUND AT ONE SCHEDULED DRAW, AS A MASS.**  Under the
random-oracle counting law, the mass of the event that the digest triple read at
stage `j` from counter `base` lands in ITS OWN HISTORY'S bad set is at most
`m / |DigestTriple|`, whenever that bad set never has more than `m` points. -/
theorem stage_triple_target_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j base : Nat)
    (hbase : base + 2 < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : StageStable L hL e0 strat hb j (tripleCounters base) A)
    (targ : OracleTable (boundedQueries L) → Finset OuterChallenge.DigestTriple)
    (hinv : ∀ T ∈ A, ∀ c ∈ tripleCounters base, ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = targ T)
    (m : Nat) (hm : ∀ T ∈ A, (targ T).card ≤ m) :
    oracleProbability (boundedQueries L)
        (A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T))
      ≤ (m : ℚ) / (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
  have hcard := stage_triple_target_card L hL e0 strat hb j base hbase A hA targ hinv m hm
  have hAle : A.card ≤ Fintype.card (OracleTable (boundedQueries L)) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_univ A
  have hnat : (A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).card
      * Fintype.card OuterChallenge.DigestTriple
      ≤ m * Fintype.card (OracleTable (boundedQueries L)) :=
    le_trans hcard (Nat.mul_le_mul_left m hAle)
  have hQ : ((A.filter (fun T => stageTriple L hL e0 strat hb j base T ∈ targ T)).card : ℚ)
      * (Fintype.card OuterChallenge.DigestTriple : ℚ)
      ≤ (m : ℚ) * (Fintype.card (OracleTable (boundedQueries L)) : ℚ) := by
    exact_mod_cast hnat
  have hD : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
    exact_mod_cast JointChallengeSpace.digest_triple_card_pos
  rw [oracleProbability, div_le_div_iff (oracle_card_cast_pos (boundedQueries L)) hD]
  exact hQ

/-- (2) **THE DIAGONAL FRESH STEP AT ONE COUNTER.**  The single-counter form of
the same fact, and the precise sense in which the adopted
`BirthdayClashBound.adaptive_fresh_step` already allows a target that MOVES WITH
THE TABLE: all it asks is that the target be unmoved by the answer it is tested
against, which for the stage-`j` challenge query of a strategy chain is the
statement that the round's message was chosen before the round's challenge was
squeezed.  The adopted `StrategyChainBound.strategy_challenge_fresh_uniform` is
the special case of a CONSTANT target (and is then an equality). -/
theorem strategy_challenge_diagonal_fresh_uniform (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat)
    (targ : OracleTable (boundedQueries L) → Finset Block)
    (hinv : ∀ T ∈ stageNoClash L hL e0 strat hb j, ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = targ T)
    (m : Nat) (hm : ∀ T ∈ stageNoClash L hL e0 strat hb j, (targ T).card ≤ m) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb j).filter
          (fun T => T (challengeSel L hL e0 strat hb j c T) ∈ targ T))
      ≤ (m : ℚ) / (Fintype.card Block : ℚ)
        * oracleProbability (boundedQueries L) (stageNoClash L hL e0 strat hb j) :=
  adaptive_fresh_step
    ⟨fun T hT b => no_clash_challenge_reassign L hL e0 strat hb j c T hT b,
     fun T hT b => challenge_sel_stable L hL e0 strat hb j c c T hT b,
     fun T hT b => hinv T hT b⟩ m hm

/-! ## 3. THE OUTER ROUND SCHEDULE ON THE ORACLE TABLE -/

open Audit.Wire3.OuterSequentialConditioning

/-- Counters `0` to `5` are below the adopted `Transcript.u64Limit`, so the six
challenge queries of one round are six different queries. -/
theorem small_counter_lt (c : Nat) (h : c ≤ 5) : c < Transcript.u64Limit := by
  rw [Transcript.u64Limit]
  omega

/-- **THE STAGE ROUND `r`'s TWO CHALLENGES ARE SQUEEZED FROM.**  The chain's
state after the twenty-two relation-prefix frames and the five frames of each of
the rounds `0, …, r`: the adopted
`ConcreteChainThreading.run_round_digest_is_chain_digest` reads the adopted
`RandomOracleSqueezes.sourceDigest` of BOTH `Draw.outerLog r` and
`Draw.outerGate r` off exactly this stage. -/
def roundStage (r : Nat) : Nat := 22 + (5 * r + 5)

theorem round_stage_lt (r s : Nat) (h : r < s) : roundStage r < roundStage s := by
  rw [roundStage, roundStage]
  omega

theorem round_stage_le (r d : Nat) (h : r < d) : roundStage r ≤ 22 + 5 * d := by
  rw [roundStage]
  omega

/-- The digest triple of round `r`'s LOG lane: the adopted
`JointChallengeSpace.sourceCounter` of `Draw.outerLog r` is `0`. -/
def logTriple (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (r : Nat) (T : OracleTable (boundedQueries L)) :
    OuterChallenge.DigestTriple :=
  stageTriple L hL e0 strat hb (roundStage r) 0 T

/-- The digest triple of round `r`'s GATE lane: the adopted
`JointChallengeSpace.sourceCounter` of `Draw.outerGate r` is `3`, at the SAME
digest. -/
def gateTriple (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (r : Nat) (T : OracleTable (boundedQueries L)) :
    OuterChallenge.DigestTriple :=
  stageTriple L hL e0 strat hb (roundStage r) 3 T

/-- (3) **OVERWRITING A STAGE-`j` CHALLENGE ANSWER LEAVES EVERY EARLIER STAGE'S
CHALLENGE ANSWERS ALONE.**  The adopted
`StrategyChainBound.strategy_state_challenge_stable` moves no earlier digest and
the adopted `challenge_at_reassign_challenge` moves no earlier answer. -/
theorem challenge_answer_reassign_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block)
    (i : Nat) (hi : i < j) (c2 : Nat) :
    (reassign T (challengeSel L hL e0 strat hb j c T) b)
        (challengeSel L hL e0 strat hb i c2
          (reassign T (challengeSel L hL e0 strat hb j c T) b))
      = T (challengeSel L hL e0 strat hb i c2 T) := by
  have hst : strategyFrameState L hL e0 strat hb i
        (reassign T (challengeSel L hL e0 strat hb j c T) b)
      = strategyFrameState L hL e0 strat hb i T :=
    strategy_state_challenge_stable L hL e0 strat hb j c T hT b j (le_refl j) i (le_of_lt hi)
  have hsel : challengeSel L hL e0 strat hb i c2
        (reassign T (challengeSel L hL e0 strat hb j c T) b)
      = challengeSel L hL e0 strat hb i c2 T := by
    apply Subtype.ext
    show Transcript.challengeInput (strategyFrameState L hL e0 strat hb i
        (reassign T (challengeSel L hL e0 strat hb j c T) b)) c2
      = Transcript.challengeInput (strategyFrameState L hL e0 strat hb i T) c2
    rw [hst]
  rw [hsel]
  exact challenge_at_reassign_challenge L hL e0 strat hb j c T hT b i hi c2

/-- (3) The same, for a whole earlier digest triple. -/
theorem stage_triple_reassign_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c i base : Nat) (hi : i < j)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block) :
    stageTriple L hL e0 strat hb i base
        (reassign T (challengeSel L hL e0 strat hb j c T) b)
      = stageTriple L hL e0 strat hb i base T := by
  rw [stageTriple, stageTriple,
    challenge_answer_reassign_lower L hL e0 strat hb j c T hT b i hi base,
    challenge_answer_reassign_lower L hL e0 strat hb j c T hT b i hi (base + 1),
    challenge_answer_reassign_lower L hL e0 strat hb j c T hT b i hi (base + 2)]

/-- (3) **THE OTHER LANE'S TRIPLE AT THE SAME STAGE IS ALSO LEFT ALONE.**  The
gate lane's three counters are `3, 4, 5` and the log lane's are `0, 1, 2`; six
different counters at one digest are six different queries. -/
theorem stage_triple_reassign_same (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j base c : Nat)
    (hc : c < Transcript.u64Limit) (hbase : base + 2 < Transcript.u64Limit)
    (hne : c ∉ tripleCounters base)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block) :
    stageTriple L hL e0 strat hb j base
        (reassign T (challengeSel L hL e0 strat hb j c T) b)
      = stageTriple L hL e0 strat hb j base T := by
  have h0 : base ≠ c := fun h => hne (h ▸ (mem_triple_counters base base).mpr (Or.inl rfl))
  have h1 : base + 1 ≠ c :=
    fun h => hne (h ▸ (mem_triple_counters base (base + 1)).mpr (Or.inr (Or.inl rfl)))
  have h2 : base + 2 ≠ c :=
    fun h => hne (h ▸ (mem_triple_counters base (base + 2)).mpr (Or.inr (Or.inr rfl)))
  rw [stageTriple, stageTriple,
    stage_answer_reassign_ne L hL e0 strat hb j c base hc (by omega) h0 T hT b,
    stage_answer_reassign_ne L hL e0 strat hb j c (base + 1) hc (by omega) h1 T hT b,
    stage_answer_reassign_ne L hL e0 strat hb j c (base + 2) hc hbase h2 T hT b]

/-- **THE TWO LANE STATES AFTER `r` COUPLED ROUNDS, AT ONE TABLE.**  Both lanes
absorb every realized challenge, in the adopted interleaved order
`log 0, gate 0, log 1, gate 1, …` of `OuterSequentialConditioning.outerCoords`,
through the ADOPTED `OuterSequentialConditioning.laneStep`.  What varies from the
adopted ideal-model walk is that the challenges absorbed are the ORACLE's answers
at the chain's own stage digests, so the state is a function OF THE TABLE. -/
noncomputable def outerState (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (T : OracleTable (boundedQueries L)) : Nat → Lane × Lane
  | 0 => (logLane, gateLane)
  | r + 1 =>
      (laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane T r).1
          (logTriple L hL e0 strat hb r T)) (gateTriple L hL e0 strat hb r T),
       laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane T r).2
          (logTriple L hL e0 strat hb r T)) (gateTriple L hL e0 strat hb r T))

/-- ROUND `r`'s LOG-LANE BAD SET, as the history has made it: the ADOPTED
`OuterSequentialConditioning.laneBad` at the state the realized challenges of the
rounds before `r` have driven the lane to. -/
noncomputable def logTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) : Finset OuterChallenge.DigestTriple :=
  laneBad (outerState L hL e0 strat hb logLane gateLane T r).1

/-- ROUND `r`'s GATE-LANE BAD SET: the gate lane has additionally absorbed round
`r`'s own LOG challenge, which is the adopted interleaved order and models an
adversary at least as strong as the deployed one (both challenges of a round come
from the same commit, so the real prover cannot see the log challenge first). -/
noncomputable def gateTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) : Finset OuterChallenge.DigestTriple :=
  laneBad (laneStep (outerState L hL e0 strat hb logLane gateLane T r).2
    (logTriple L hL e0 strat hb r T))

/-- (3) **THE STATE BEFORE ROUND `r` IS NOT MOVED BY ROUND `r`'s OWN CHALLENGE
ANSWERS.**  This is the transported form of the adopted
`OuterSequentialConditioning.PrefixDependent`: the prefix the lane has read is
made of the answers at STRICTLY EARLIER stage digests. -/
theorem outer_state_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane) (j c : Nat)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block) :
    ∀ rr : Nat, (∀ i, i < rr → roundStage i < j) →
      outerState L hL e0 strat hb logLane gateLane
          (reassign T (challengeSel L hL e0 strat hb j c T) b) rr
        = outerState L hL e0 strat hb logLane gateLane T rr := by
  intro rr
  induction rr with
  | zero => intro _; rfl
  | succ r2 ih =>
      intro hlt
      have hprev := ih (fun i hi => hlt i (by omega))
      have hr2 : roundStage r2 < j := hlt r2 (by omega)
      have hlog : logTriple L hL e0 strat hb r2
            (reassign T (challengeSel L hL e0 strat hb j c T) b)
          = logTriple L hL e0 strat hb r2 T :=
        stage_triple_reassign_lower L hL e0 strat hb j c (roundStage r2) 0 hr2 T hT b
      have hgate : gateTriple L hL e0 strat hb r2
            (reassign T (challengeSel L hL e0 strat hb j c T) b)
          = gateTriple L hL e0 strat hb r2 T :=
        stage_triple_reassign_lower L hL e0 strat hb j c (roundStage r2) 3 hr2 T hT b
      show (laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane
              (reassign T (challengeSel L hL e0 strat hb j c T) b) r2).1
            (logTriple L hL e0 strat hb r2
              (reassign T (challengeSel L hL e0 strat hb j c T) b)))
            (gateTriple L hL e0 strat hb r2
              (reassign T (challengeSel L hL e0 strat hb j c T) b)),
          laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane
              (reassign T (challengeSel L hL e0 strat hb j c T) b) r2).2
            (logTriple L hL e0 strat hb r2
              (reassign T (challengeSel L hL e0 strat hb j c T) b)))
            (gateTriple L hL e0 strat hb r2
              (reassign T (challengeSel L hL e0 strat hb j c T) b)))
        = (laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane T r2).1
            (logTriple L hL e0 strat hb r2 T)) (gateTriple L hL e0 strat hb r2 T),
          laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane T r2).2
            (logTriple L hL e0 strat hb r2 T)) (gateTriple L hL e0 strat hb r2 T))
      rw [hprev, hlog, hgate]

/-- (3) ROUND `r`'s LOG BAD SET IS UNMOVED BY ROUND `r`'s LOG CHALLENGE ANSWERS:
the hypothesis the diagonal bound of section 2 asks for. -/
theorem log_target_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane) (r c : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL e0 strat hb (roundStage r)) (b : Block) :
    logTarget L hL e0 strat hb logLane gateLane r
        (reassign T (challengeSel L hL e0 strat hb (roundStage r) c T) b)
      = logTarget L hL e0 strat hb logLane gateLane r T := by
  rw [logTarget, logTarget,
    outer_state_reassign L hL e0 strat hb logLane gateLane (roundStage r) c T hT b r
      (fun i hi => round_stage_lt i r hi)]

/-- (3) ROUND `r`'s GATE BAD SET IS UNMOVED BY ROUND `r`'s GATE CHALLENGE
ANSWERS: the state before the round is unmoved, and so is the LOG triple the gate
lane has already absorbed, because counters `0, 1, 2` are not counters
`3, 4, 5`. -/
theorem gate_target_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane) (r c : Nat)
    (hc : c ∈ tripleCounters 3) (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL e0 strat hb (roundStage r)) (b : Block) :
    gateTarget L hL e0 strat hb logLane gateLane r
        (reassign T (challengeSel L hL e0 strat hb (roundStage r) c T) b)
      = gateTarget L hL e0 strat hb logLane gateLane r T := by
  have hcle : c ≤ 5 := by
    rcases (mem_triple_counters 3 c).mp hc with h | h | h <;> omega
  have hnot : c ∉ tripleCounters 0 := by
    intro hmem
    rcases (mem_triple_counters 0 c).mp hmem with h | h | h <;>
      rcases (mem_triple_counters 3 c).mp hc with h2 | h2 | h2 <;> omega
  have hlog : logTriple L hL e0 strat hb r
        (reassign T (challengeSel L hL e0 strat hb (roundStage r) c T) b)
      = logTriple L hL e0 strat hb r T :=
    stage_triple_reassign_same L hL e0 strat hb (roundStage r) 0 c
      (small_counter_lt c hcle) (small_counter_lt 2 (by omega)) hnot T hT b
  rw [gateTarget, gateTarget, hlog,
    outer_state_reassign L hL e0 strat hb logLane gateLane (roundStage r) c T hT b r
      (fun i hi => round_stage_lt i r hi)]

/-- (3) The adopted degree bound is preserved along the walk, for the log lane. -/
theorem outer_state_log_bounded (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) (bd : Nat)
    (hbd : logLane.Bounded bd) (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat, (outerState L hL e0 strat hb logLane gateLane T r).1.Bounded bd := by
  intro r
  induction r with
  | zero => exact hbd
  | succ r2 ih =>
      exact laneStep_bounded _ bd (laneStep_bounded _ bd ih _) _

/-- (3) The same for the gate lane. -/
theorem outer_state_gate_bounded (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) (bd : Nat)
    (hbd : gateLane.Bounded bd) (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat, (outerState L hL e0 strat hb logLane gateLane T r).2.Bounded bd := by
  intro r
  induction r with
  | zero => exact hbd
  | succ r2 ih =>
      exact laneStep_bounded _ bd (laneStep_bounded _ bd ih _) _

/-- (3) **THE LOG LANE OWNS EVERY ROUND'S LOG COORDINATE.**  Two `laneStep`s per
round flip the phase bit twice, so a log lane that starts with `ownsNext = true`
owns its coordinate at every round.  THIS DOES NOT SAY THE ROUND'S BAD SET IS
NON-EMPTY: the adopted `OuterSequentialConditioning.Lane.badSet` is the adopted
`ConditionalSoundness.roundBadSet L.claim L.truthClaim _`, which is `∅` whenever
`L.claim = L.truthClaim` however the phase bit stands.  Section 7 exhibits both
cases. -/
theorem outer_state_log_owns (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat, (outerState L hL e0 strat hb logLane gateLane T r).1.ownsNext
      = logLane.ownsNext := by
  intro r
  induction r with
  | zero => rfl
  | succ r2 ih =>
      show (laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane T r2).1
          (logTriple L hL e0 strat hb r2 T)) (gateTriple L hL e0 strat hb r2 T)).ownsNext
        = logLane.ownsNext
      rw [laneStep_active, laneStep_active, ih, Bool.not_not]

/-- (3) **THE GATE LANE OWNS EVERY ROUND'S GATE COORDINATE**, when it starts with
`ownsNext = false`: after the round's log triple it has flipped an odd number of
times. -/
theorem outer_state_gate_owns (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat, (laneStep (outerState L hL e0 strat hb logLane gateLane T r).2
        (logTriple L hL e0 strat hb r T)).ownsNext = ! gateLane.ownsNext := by
  intro r
  have hgen : ∀ r2 : Nat,
      (outerState L hL e0 strat hb logLane gateLane T r2).2.ownsNext = gateLane.ownsNext := by
    intro r2
    induction r2 with
    | zero => rfl
    | succ r3 ih =>
        show (laneStep (laneStep (outerState L hL e0 strat hb logLane gateLane T r3).2
            (logTriple L hL e0 strat hb r3 T)) (gateTriple L hL e0 strat hb r3 T)).ownsNext
          = gateLane.ownsNext
        rw [laneStep_active, laneStep_active, ih, Bool.not_not]
  rw [laneStep_active, hgen r]

/-! ## 4. THE PER-ROUND MASS AND THE UNION OVER THE ROUNDS -/

/-- (4) **ROUND `r`'s LOG-LANE MASS.**  Conditioned on the chain's no-clash event
up to round `r`'s own stage, the log challenge of round `r` lands in the bad set
ITS OWN HISTORY has chosen with mass at most `b * ceil ^ 3 / |DigestTriple|`. -/
theorem round_log_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane) (bd : Nat)
    (hbd : logLane.Bounded bd) (r : Nat) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb (roundStage r)).filter
          (fun T => logTriple L hL e0 strat hb r T
            ∈ logTarget L hL e0 strat hb logLane gateLane r T))
      ≤ ((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  stage_triple_target_mass_le L hL e0 strat hb (roundStage r) 0
    (small_counter_lt 2 (by omega)) (stageNoClash L hL e0 strat hb (roundStage r))
    (stage_stable_no_clash L hL e0 strat hb (roundStage r) (tripleCounters 0))
    (logTarget L hL e0 strat hb logLane gateLane r)
    (fun T hT _ _ b => log_target_reassign L hL e0 strat hb logLane gateLane r _ T hT b)
    (bd * OuterChallenge.fiberCeiling ^ 3)
    (fun T _ => laneBad_card_le _ bd
      (outer_state_log_bounded L hL e0 strat hb logLane gateLane bd hbd T r))

/-- (4) **ROUND `r`'s GATE-LANE MASS**, at the SAME stage digest and the counters
`3, 4, 5`. -/
theorem round_gate_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane) (bd : Nat)
    (hbd : gateLane.Bounded bd) (r : Nat) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL e0 strat hb (roundStage r)).filter
          (fun T => gateTriple L hL e0 strat hb r T
            ∈ gateTarget L hL e0 strat hb logLane gateLane r T))
      ≤ ((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  stage_triple_target_mass_le L hL e0 strat hb (roundStage r) 3
    (small_counter_lt 5 (by omega)) (stageNoClash L hL e0 strat hb (roundStage r))
    (stage_stable_no_clash L hL e0 strat hb (roundStage r) (tripleCounters 3))
    (gateTarget L hL e0 strat hb logLane gateLane r)
    (fun T hT c hc b => gate_target_reassign L hL e0 strat hb logLane gateLane r c hc T hT b)
    (bd * OuterChallenge.fiberCeiling ^ 3)
    (fun T _ => laneBad_card_le _ bd (laneStep_bounded _ bd
      (outer_state_gate_bounded L hL e0 strat hb logLane gateLane bd hbd T r) _))

/-- (4) A GENERIC CUT-DOWN, stated over an abstract finite type so that no
membership over the table space is ever elaborated at a free table: the part of a
cylinder that lies in `A` lies in the `B`-cylinder whenever `A` is inside `B`. -/
theorem univ_filter_inter_subset {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (p : alpha → Prop) [DecidablePred p] (A B : Finset alpha) (h : A ⊆ B) :
    (Finset.univ.filter p) ∩ A ⊆ B.filter p := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  exact Finset.mem_filter.mpr ⟨h hx2, (Finset.mem_filter.mp hx1).2⟩

/-- (4) THE GENERIC SPLIT ON A CONDITIONING EVENT, again over an abstract finite
type: every point of `E` either lies in `A` or in its complement. -/
theorem subset_inter_union_compl {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (E A : Finset alpha) : E ⊆ (E ∩ A) ∪ Aᶜ := by
  intro x hx
  by_cases hA : x ∈ A
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hA⟩)
  · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hA)

/-- THE EVENT THAT COUPLED ROUND `r`'s LOG CHALLENGE AGREES WITH THE LOG LANE:
the round's own log triple, read off the STRATEGY's chain, lands in the bad set
the LANE's prefix-dependent message function has chosen for it. -/
noncomputable def roundLogBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) (r : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    logTriple L hL e0 strat hb r T ∈ logTarget L hL e0 strat hb logLane gateLane r T)

/-- The same for round `r`'s GATE challenge. -/
noncomputable def roundGateBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) (r : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    gateTriple L hL e0 strat hb r T ∈ gateTarget L hL e0 strat hb logLane gateLane r T)

/-- THE EVENT THAT COUPLED ROUND `r` AGREES, ON EITHER LANE. -/
noncomputable def roundBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) (r : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  roundLogBadEvent L hL e0 strat hb logLane gateLane r
    ∪ roundGateBadEvent L hL e0 strat hb logLane gateLane r

/-- **THE OUTER LANE BAD EVENT ON THE ORACLE TABLE.**  Some coupled round of
either outer LANE agrees.  This is the transported form of the adopted
`OuterSequentialConditioning.adaptiveOuterEvent`: the same lane machinery and the
same bad sets, but the challenges are the ORACLE's answers at the chain's own
stage digests rather than the coordinates of an ideal product space.  The lanes
are quantified independently of `strat`; their round messages are functions of
the REDUCED challenge prefix (`outer_state_message`), not of the strategy. -/
noncomputable def outerLaneBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) (d : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  (Finset.range d).biUnion (fun r => roundBadEvent L hL e0 strat hb logLane gateLane r)

theorem outer_lane_bad_event_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) :
    outerLaneBadEvent L hL e0 strat hb logLane gateLane 0
      = (∅ : Finset (OracleTable (boundedQueries L))) := by
  rw [outerLaneBadEvent, Finset.range_zero, Finset.biUnion_empty]

theorem oracle_probability_empty (Q : Finset Transcript.Bytes) :
    oracleProbability Q (∅ : Finset (OracleTable Q)) = 0 := by
  rw [oracleProbability, Finset.card_empty, Nat.cast_zero, zero_div]

/-- (4) On the no-clash event, round `r`'s bad event is covered by the two
FIXED-STAGE events of `round_log_mass_le` and `round_gate_mass_le`: the no-clash
event up to the last stage is contained in the no-clash event up to round `r`'s
own stage (`stage_no_clash_mono`). -/
theorem round_bad_inter_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane) (n r : Nat)
    (hr : roundStage r ≤ n) :
    roundBadEvent L hL e0 strat hb logLane gateLane r ∩ stageNoClash L hL e0 strat hb n
      ⊆ ((stageNoClash L hL e0 strat hb (roundStage r)).filter
            (fun T => logTriple L hL e0 strat hb r T
              ∈ logTarget L hL e0 strat hb logLane gateLane r T))
        ∪ ((stageNoClash L hL e0 strat hb (roundStage r)).filter
            (fun T => gateTriple L hL e0 strat hb r T
              ∈ gateTarget L hL e0 strat hb logLane gateLane r T)) := by
  rw [roundBadEvent, Finset.union_inter_distrib_right, roundLogBadEvent, roundGateBadEvent]
  exact Finset.union_subset_union
    (univ_filter_inter_subset _ _ _ (stage_no_clash_mono L hL e0 strat hb (roundStage r) n hr))
    (univ_filter_inter_subset _ _ _ (stage_no_clash_mono L hL e0 strat hb (roundStage r) n hr))

/-- (4) **THE UNION OVER THE ROUNDS, ON THE NO-CLASH EVENT.**  The nesting of the
no-clash events makes every summand a fixed-stage statement, and each is the
diagonal bound of section 2 at that stage. -/
theorem outer_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (bl bg : Nat) (hlog : logLane.Bounded bl) (hgate : gateLane.Bounded bg) (n : Nat) :
    ∀ k : Nat, (∀ r, r < k → roundStage r ≤ n) →
      oracleProbability (boundedQueries L)
          (outerLaneBadEvent L hL e0 strat hb logLane gateLane k
            ∩ stageNoClash L hL e0 strat hb n)
        ≤ (k : ℚ) * (((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [outer_lane_bad_event_zero, Finset.empty_inter, oracle_probability_empty,
        Nat.cast_zero, zero_mul]
  | succ k2 ih =>
      intro hk
      have hk2 : ∀ r, r < k2 → roundStage r ≤ n := fun r hr => hk r (by omega)
      have hkk : roundStage k2 ≤ n := hk k2 (by omega)
      have hsplit : outerLaneBadEvent L hL e0 strat hb logLane gateLane (k2 + 1)
            ∩ stageNoClash L hL e0 strat hb n
          = (roundBadEvent L hL e0 strat hb logLane gateLane k2
              ∩ stageNoClash L hL e0 strat hb n)
            ∪ (outerLaneBadEvent L hL e0 strat hb logLane gateLane k2
              ∩ stageNoClash L hL e0 strat hb n) := by
        rw [outerLaneBadEvent, outerLaneBadEvent, Finset.range_succ,
          Finset.biUnion_insert, Finset.union_inter_distrib_right]
      have hround : oracleProbability (boundedQueries L)
          (roundBadEvent L hL e0 strat hb logLane gateLane k2
            ∩ stageNoClash L hL e0 strat hb n)
          ≤ ((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
        refine le_trans (oracle_probability_mono (boundedQueries L) _ _
          (round_bad_inter_subset L hL e0 strat hb logLane gateLane n k2 hkk)) ?_
        refine le_trans (oracle_probability_union_le (boundedQueries L) _ _) ?_
        exact add_le_add (round_log_mass_le L hL e0 strat hb logLane gateLane bl hlog k2)
          (round_gate_mass_le L hL e0 strat hb logLane gateLane bg hgate k2)
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

/-- (4) The per-round fibre mass in the adopted digest-ratio form: no cardinality
is evaluated, the adopted `OuterChallenge.digest_tuple_cardinality` is all that is
used. -/
theorem fibre_mass_eq (bd : Nat) :
    ((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
        / (Fintype.card OuterChallenge.DigestTriple : ℚ)
      = (bd : ℚ) * ((OuterChallenge.fiberCeiling : ℚ) / (OuterChallenge.wordSize : ℚ)) ^ 3 := by
  rw [OuterChallenge.digest_tuple_cardinality, div_pow]
  push_cast
  rw [mul_div_assoc]

/-- (4) **THE ROUND TERMS SUM TO THE ADOPTED `outerTerm`.**  `5 * degreeBits` for
the log lane and `(quotientDegree + 2) * degreeBits` for the gate lane, times the
cubed digest ratio -- the SAME number the adopted
`OuterSequentialConditioning.adaptive_outer_event_mass_le` gets in the ideal
model. -/
theorem round_terms_sum (d q : Nat) :
    (d : ℚ) * (((5 * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ)
        + (((q + 2) * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ))
      = ChallengeUnionBound.outerTerm d q := by
  rw [fibre_mass_eq, fibre_mass_eq, ChallengeUnionBound.outerTerm]
  push_cast
  ring

/-! ## 5. THE HEADLINE: PREFIX-DEPENDENT LANE TRANSPORT -/

/-- (5) **THE OUTER LANE BAD-DRAW BOUND.**  Under the random-oracle counting law
on `OracleTable (boundedQueries L)`, for EVERY transcript-restricted adaptive
prover -- every `StrategyChainBound.Strategy` -- and EVERY pair of
`OuterSequentialConditioning.Lane`s meeting the adopted degree bounds, the mass
of the event that some coupled round of either OUTER LANE agrees is at most

* the OUTER part of the adopted `ChallengeUnionBound.combinedBound`, namely
  `ChallengeUnionBound.outerTerm degreeBits quotientDegree`
  (`5 * degreeBits + (quotientDegree + 2) * degreeBits` field points, each of
  digest mass `(ceil / 2 ^ 256) ^ 3`) -- and NOTHING ELSE of `combinedBound`: the
  gate tau term and the gate alpha term are NOT covered, and neither is the
  index-lane, WHIR or Merkle part of the protocol, which is not in
  `combinedBound` at all; plus
* the chain's own clash mass `n (n + 1) / 2 / |Block|` at `n = 22 + 5 d` stages,
  the adopted `StrategyChainBound.strategy_chain_clash_probability_le`.

**WHOSE BAD SETS THESE ARE.**  Round `r`'s bad set is the LANE's: the adopted
`laneBad` of the state `logLane` / `gateLane` has been driven to by the realized
reduced challenges of the earlier rounds.  `strat` and the lanes are quantified
SEPARATELY, and the lane's `message` is its own function of the reduced challenge
prefix (`outer_state_message`), NOT the strategy's realized message.  So this is
the transport of OSC's PREFIX-DEPENDENT per-round conditioning from the ideal
`JointChallengeSpace.JointSpace` to the oracle table along a strategy-driven
chain; IT IS NOT THE ADAPTIVE UNION BOUND OF SCB HONESTY (iii), in which round
`r`'s bad set is determined by the message THE STRATEGY chooses.  Section 8
proves that statement for the `ReducedStrategy` subclass and for no other
strategy.  Read HONESTY (iii) of the header before quoting this. -/
theorem outer_lane_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (logLane gateLane : Lane) (d q : Nat)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2)) :
    oracleProbability (boundedQueries L)
        (outerLaneBadEvent L hL e0 strat hb logLane gateLane d)
      ≤ ChallengeUnionBound.outerTerm d q
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl (outerLaneBadEvent L hL e0 strat hb logLane gateLane d)
      (stageNoClash L hL e0 strat hb (22 + 5 * d)))
  have hunion := oracle_probability_union_le (boundedQueries L)
    (outerLaneBadEvent L hL e0 strat hb logLane gateLane d
      ∩ stageNoClash L hL e0 strat hb (22 + 5 * d))
    ((stageNoClash L hL e0 strat hb (22 + 5 * d))ᶜ)
  have hround := outer_no_clash_mass_le L hL e0 strat hb logLane gateLane 5 (q + 2)
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

/-! ## 6. THE TRIPLES BOUNDED ABOVE ARE THE RUN'S OWN DRAW -/

/-- (6) **THE STAGE TRIPLE IS THE ADOPTED `OuterChallenge.actualDigests`** at the
chain's own stage digest: nothing is re-modelled, the table's three answers ARE
the three block digests the run squeezes. -/
theorem stage_triple_is_actual_digests (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j base : Nat)
    (T : OracleTable (boundedQueries L)) :
    stageTriple L hL e0 strat hb j base T
      = OuterChallenge.actualDigests (hashOf (boundedQueries L) T)
          ⟨strategyFrameState L hL e0 strat hb j T, base⟩ := by
  have hcomp : ∀ ctr : Nat, OuterChallenge.digestBlock ((hashOf (boundedQueries L) T)
        (Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) ctr))
      = T (challengeSel L hL e0 strat hb j ctr T) := by
    intro ctr
    rw [show Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) ctr
        = (challengeSel L hL e0 strat hb j ctr T).val from rfl,
      hash_of_at, digest_block_block_digest]
  show (T (challengeSel L hL e0 strat hb j base T),
      T (challengeSel L hL e0 strat hb j (base + 1) T),
      T (challengeSel L hL e0 strat hb j (base + 2) T))
    = (OuterChallenge.digestBlock ((hashOf (boundedQueries L) T)
        (Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) base)),
      OuterChallenge.digestBlock ((hashOf (boundedQueries L) T)
        (Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) (base + 1))),
      OuterChallenge.digestBlock ((hashOf (boundedQueries L) T)
        (Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) (base + 2))))
  rw [hcomp base, hcomp (base + 1), hcomp (base + 2)]

/-- (6) The adopted `BirthdayClashBound.frameState` depends on its length proof
only through proof irrelevance, so equal shapes give equal chains. -/
theorem frame_state_shape_congr (L : Nat) (e0 : Transcript.Digest)
    (sh1 sh2 : Nat → Transcript.Byte × Transcript.Bytes) (heq : sh1 = sh2)
    (h1 : ∀ k, 61 + (sh1 k).2.length ≤ L) (h2 : ∀ k, 61 + (sh2 k).2.length ≤ L)
    (k : Nat) (T : OracleTable (boundedQueries L)) :
    frameState L e0 sh1 h1 k T = frameState L e0 sh2 h2 k T := by
  subst heq
  rfl

/-- (6) **THE DIGEST ROUND `r`'s CHALLENGES ARE SQUEEZED FROM IS THE STRATEGY
CHAIN'S STAGE `22 + 5 r + 5`.**  The adopted
`ConcreteChainThreading.run_round_digest_is_chain_digest` for the proof the
strategy actually produced at this table, carried onto the strategy chain by the
adopted `StrategyChainBound.strategic_prover_chain_is_strategy_chain`. -/
theorem strategic_source_digest_is_stage_digest (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (p : Verifier.Proof) (T : OracleTable (boundedQueries L))
    (hstat : Verifier.statement p = s)
    (hmsgs : roundMessages p = realizedMessages L hL c s S hb c.degreeBits T)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) (r : Fin c.degreeBits) :
    RandomOracleSqueezes.sourceDigest (hashOf (boundedQueries L) T) c p
        (JointChallengeSpace.Draw.outerLog r)
      = strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (roundStage r.val) T := by
  have hshape : prefixRoundShape c (Verifier.statement p) (roundMessages p)
      = prefixRoundShape c s (realizedMessages L hL c s S hb c.degreeBits T) := by
    rw [hstat, hmsgs]
  have hr : 22 + (5 * r.val + 5) ≤ 22 + 5 * c.degreeBits := by
    have := r.isLt
    omega
  rw [ConcreteChainThreading.run_round_digest_is_chain_digest L c p hlen hmlen T r,
    frame_state_shape_congr L OuterInitial.zeroDigest _ _ hshape hlen
      (strategic_hlen_of_bounded L hL c s S hb c.degreeBits T) (22 + (5 * r.val + 5)) T,
    ← strategic_prover_chain_is_strategy_chain L hL c s S hb hS c.degreeBits T
      (22 + (5 * r.val + 5)) hr, roundStage]

/-- (6) **THE LOG TRIPLE BOUNDED IN SECTION 4 IS THE RUN'S OWN `Draw.outerLog r`
COORDINATE**, at the proof the strategy produced at this table: the adopted
`InstalledRoundCommit.actualDigestDraw`, coordinate by coordinate. -/
theorem strategic_run_log_draw_is_log_triple (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (p : Verifier.Proof) (T : OracleTable (boundedQueries L))
    (hstat : Verifier.statement p = s)
    (hmsgs : roundMessages p = realizedMessages L hL c s S hb c.degreeBits T)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) (r : Fin c.degreeBits) :
    InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c p
        (JointChallengeSpace.Draw.outerLog r)
      = logTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hb r.val T := by
  rw [logTriple, stage_triple_is_actual_digests,
    ← strategic_source_digest_is_stage_digest L hL c s S hb hS p T hstat hmsgs hlen hmlen r]
  rfl

/-- (6) The same for the GATE lane: the adopted `sourceDigest` sends
`Draw.outerGate r` to the same stage digest and the adopted
`JointChallengeSpace.sourceCounter` sends it to counter `3`. -/
theorem strategic_run_gate_draw_is_gate_triple (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S)
    (p : Verifier.Proof) (T : OracleTable (boundedQueries L))
    (hstat : Verifier.statement p = s)
    (hmsgs : roundMessages p = realizedMessages L hL c s S hb c.degreeBits T)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) (r : Fin c.degreeBits) :
    InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c p
        (JointChallengeSpace.Draw.outerGate r)
      = gateTriple L hL OuterInitial.zeroDigest (strategicShape c s S) hb r.val T := by
  have hsrc : RandomOracleSqueezes.sourceDigest (hashOf (boundedQueries L) T) c p
      (JointChallengeSpace.Draw.outerGate r)
      = strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (roundStage r.val) T :=
    strategic_source_digest_is_stage_digest L hL c s S hb hS p T hstat hmsgs hlen hmlen r
  rw [gateTriple, stage_triple_is_actual_digests, ← hsrc]
  rfl

/-- A proof record carrying a prescribed statement and a prescribed coupled-message
list: the witness that the hypotheses `hstat`, `hmsgs`, `hmlen` and `hlen` of the
two bridge theorems are satisfiable, at the messages the strategy really produced
at the table. -/
def realizedProof (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) :
    Verifier.Proof :=
  { Verifier.testProof with
      circuitDigest := s.circuitDigest, publicInputs := s.publicInputs,
      preprocessedRoot := s.preprocessedRoot, witnessRoot := s.witnessRoot,
      normInverseRoot := s.normInverseRoot,
      logRounds := ms.map Prod.fst, gateRounds := ms.map Prod.snd }

theorem realized_proof_statement (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) : Verifier.statement (realizedProof s ms) = s := rfl

theorem zip_map_fst_snd : ∀ ms : List Verifier.CoupledMessage,
    (ms.map Prod.fst).zip (ms.map Prod.snd) = ms
  | [] => rfl
  | m :: ms => by
      have h := zip_map_fst_snd ms
      show (m.1, m.2) :: (ms.map Prod.fst).zip (ms.map Prod.snd) = m :: ms
      rw [h]

theorem realized_proof_messages (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) :
    roundMessages (realizedProof s ms) = ms := zip_map_fst_snd ms

/-- (6) **THE BRIDGE'S HYPOTHESES ARE SATISFIABLE**, at every table and every
strategic prover: the proof carrying the realized messages has the right
statement, the right messages, the right number of them, and the length budget
the adopted `StrategyChainBound.strategic_hlen_of_bounded` supplies. -/
theorem realized_proof_witness (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (T : OracleTable (boundedQueries L)) :
    Verifier.statement
        (realizedProof s (realizedMessages L hL c s S hb c.degreeBits T)) = s ∧
      roundMessages (realizedProof s (realizedMessages L hL c s S hb c.degreeBits T))
          = realizedMessages L hL c s S hb c.degreeBits T ∧
      (roundMessages
          (realizedProof s (realizedMessages L hL c s S hb c.degreeBits T))).length
          = c.degreeBits ∧
      ∀ k, 61 + (prefixRoundShape c
          (Verifier.statement (realizedProof s (realizedMessages L hL c s S hb c.degreeBits T)))
          (roundMessages (realizedProof s (realizedMessages L hL c s S hb c.degreeBits T)))
          k).2.length ≤ L := by
  refine ⟨realized_proof_statement _ _, realized_proof_messages _ _, ?_, ?_⟩
  · rw [realized_proof_messages, realized_messages_length]
  · rw [realized_proof_statement, realized_proof_messages]
    exact strategic_hlen_of_bounded L hL c s S hb c.degreeBits T

/-! ## 7. EMPTY AND NON-EMPTY ROUND BAD SETS, AND THE CLOSED INSTANCE -/

/-- A GATE lane that genuinely reads its prefix -- it echoes the FIRST realized
challenge -- and starts on the ODD coordinates of the adopted interleaved
schedule.  The adopted `OuterSequentialConditioning.echoLane` is its log-lane
counterpart, so neither lane hypothesis of section 5 is vacuous.  Its prefix is
the REDUCED challenge prefix, not the strategy's message history: see the
header. -/
def coEchoLane : Lane where
  message := fun xs => xs.take 1
  truth := fun _ => []
  claim := 0
  truthClaim := 0
  ownsNext := false

theorem co_echo_lane_bounded (q : Nat) : coEchoLane.Bounded (q + 2) := by
  intro xs
  refine ⟨?_, Nat.zero_le _⟩
  show (xs.take 1).length ≤ q + 2
  rw [List.length_take]
  exact le_trans (Nat.min_le_left _ _) (by omega)

theorem co_echo_lane_reads_its_prefix (x : GoldilocksExt3Field.Element)
    (xs : List GoldilocksExt3Field.Element) : coEchoLane.message (x :: xs) = [x] := rfl

theorem echo_lane_owns : echoLane.ownsNext = true := rfl

theorem co_echo_lane_owns : coEchoLane.ownsNext = false := rfl

/-- (7) **A LANE'S ROUND BAD SET IS INHABITED WHEN ITS TWO CLAIMS DIFFER AND ITS
TWO ROUND POLYNOMIALS MEET.**  Stated for an ABSTRACT lane: the adopted
`ConditionalSoundness.round_agreement_of_ne`, at the adopted
`OuterSequentialConditioning.Lane.badSet`'s own `LaneRound` (whose `challenge`
field the adopted `roundBadSet` does not read). -/
theorem lane_bad_set_mem_of_agreement (lg : Lane) (x : GoldilocksExt3Field.Element)
    (hown : lg.ownsNext = true) (hne : lg.claim ≠ lg.truthClaim)
    (he : (OuterRound.polynomial lg.claim (lg.message [])).eval x
      = (OuterRound.polynomial lg.truthClaim (lg.truth [])).eval x) :
    x ∈ lg.badSet := by
  have hmem : x ∈ ConditionalSoundness.roundBadSet lg.claim lg.truthClaim
      ⟨lg.message [], lg.truth [], (0 : GoldilocksExt3Field.Element)⟩ :=
    ConditionalSoundness.round_agreement_of_ne lg.claim lg.truthClaim
      ⟨lg.message [], lg.truth [], x⟩ hne he
  show x ∈ (if lg.ownsNext then ConditionalSoundness.roundBadSet lg.claim lg.truthClaim
      ⟨lg.message [], lg.truth [], (0 : GoldilocksExt3Field.Element)⟩ else ∅)
  simp only [hown, if_true]
  exact hmem

/-- (7) The same at the DIGEST-TRIPLE level, through the adopted
`JointChallengeSpace.mem_tupleEvent`: a triple whose reduction is such a meeting
point puts the adopted `laneBad` in `Finset.Nonempty`. -/
theorem lane_bad_nonempty_of_agreement (lg : Lane) (ds : OuterChallenge.DigestTriple)
    (hown : lg.ownsNext = true) (hne : lg.claim ≠ lg.truthClaim)
    (he : (OuterRound.polynomial lg.claim (lg.message [])).eval (OuterChallenge.reduceTriple ds)
      = (OuterRound.polynomial lg.truthClaim (lg.truth [])).eval
          (OuterChallenge.reduceTriple ds)) :
    (laneBad lg).Nonempty := by
  refine ⟨ds, ?_⟩
  rw [laneBad, JointChallengeSpace.mem_tupleEvent]
  exact lane_bad_set_mem_of_agreement lg (OuterChallenge.reduceTriple ds) hown hne he

/-- THE ALL-ZERO DIGEST BLOCK: the adopted `Transcript.le 32 0`, thirty-two zero
bytes, a `OuterChallenge.DigestBlock` by the adopted `Transcript.le_length`. -/
def zeroDigestBlock : OuterChallenge.DigestBlock :=
  ⟨Transcript.le 32 0, Transcript.le_length 32 0⟩

/-- The digest triple all three of whose blocks are that one. -/
def zeroDigestTriple : OuterChallenge.DigestTriple :=
  (zeroDigestBlock, zeroDigestBlock, zeroDigestBlock)

/-- (7) ITS REDUCTION IS THE FIELD ZERO, through the adopted
`Transcript.fromLe_le_roundtrip` and the adopted
`RandomOracleSqueezes.small_lt_byte_power`. -/
theorem reduce_zero_digest_triple :
    OuterChallenge.reduceTriple zeroDigestTriple = (0 : GoldilocksExt3Field.Element) := by
  have h : Transcript.fromLe (Transcript.le 32 0) = 0 :=
    Transcript.fromLe_le_roundtrip 32 0 (small_lt_byte_power 0 (by norm_num))
  apply GoldilocksExt3Field.element_eq
  apply Subtype.eq
  show (⟨Transcript.fromLe (Transcript.le 32 0) % Arithmetic.modulus,
      Transcript.fromLe (Transcript.le 32 0) % Arithmetic.modulus,
      Transcript.fromLe (Transcript.le 32 0) % Arithmetic.modulus⟩ : Arithmetic.Ext3)
    = Arithmetic.zero
  rw [h, Nat.zero_mod]
  rfl

/-- **A LOG LANE WHOSE ROUND-ZERO BAD SET IS PROVABLY NON-EMPTY.**  Its running
claim and the honest running claim DIFFER (`1` against `0`), so the adopted
`ConditionalSoundness.roundBadSet` does NOT take its diagonal branch, and its
round message `[1]` against the honest `[]` makes the two adopted round
polynomials MEET AT THE FIELD ZERO: both adopted
`OuterRound.constantCoefficient`s are `0`, one as `(1 - 1) * half` and the other
as `(0 - 0) * half`.  `echoLane` is exactly what this is not: it starts with
`claim = truthClaim = 0`, and the adopted `roundBadSet` is `∅` on that
diagonal. -/
def separatedLane : Lane where
  message := fun _ => [1]
  truth := fun _ => []
  claim := 1
  truthClaim := 0
  ownsNext := true

theorem separated_lane_bounded : separatedLane.Bounded 5 := by
  intro xs
  refine ⟨?_, Nat.zero_le _⟩
  show ([(1 : GoldilocksExt3Field.Element)]).length ≤ 5
  decide

theorem separated_lane_owns : separatedLane.ownsNext = true := rfl

theorem separated_lane_claims_differ : separatedLane.claim ≠ separatedLane.truthClaim := by
  show (1 : GoldilocksExt3Field.Element) ≠ 0
  exact fun h => zero_ne_one h.symm

theorem separated_lane_agrees_at_zero :
    (OuterRound.polynomial separatedLane.claim (separatedLane.message [])).eval
        (OuterChallenge.reduceTriple zeroDigestTriple)
      = (OuterRound.polynomial separatedLane.truthClaim (separatedLane.truth [])).eval
        (OuterChallenge.reduceTriple zeroDigestTriple) := by
  rw [reduce_zero_digest_triple]
  show (OuterRound.polynomial (1 : GoldilocksExt3Field.Element) [1]).eval 0
    = (OuterRound.polynomial (0 : GoldilocksExt3Field.Element) []).eval 0
  rw [OuterRound.polynomial_eval_exact, OuterRound.polynomial_eval_exact]
  apply GoldilocksExt3Field.element_eq
  apply Subtype.eq
  decide

/-- (7) **THE ROUND BAD SET OF THAT LANE IS NOT EMPTY.** -/
theorem separated_lane_bad_nonempty : (laneBad separatedLane).Nonempty :=
  lane_bad_nonempty_of_agreement separatedLane zeroDigestTriple separated_lane_owns
    separated_lane_claims_differ separated_lane_agrees_at_zero

/-- (7) **AND SO ROUND ZERO'S LOG TARGET IS NOT EMPTY**, for EVERY strategy,
every gate lane and every table: `logTarget … 0` is the adopted `laneBad` of the
INPUT log lane.  THIS IS WHAT MAKES THE PER-ROUND BOUND OF SECTION 4 A
NON-TRIVIAL STATEMENT AT SOME LANE; `outer_state_log_owns` on its own does
NOT. -/
theorem separated_lane_round_zero_target_nonempty (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : Strategy) (hb : StrategyBounded L strat)
    (gateLane : Lane) (T : OracleTable (boundedQueries L)) :
    (logTarget L hL e0 strat hb separatedLane gateLane 0 T).Nonempty :=
  separated_lane_bad_nonempty

/-- (7) The adopted `OuterChallenge.tupleEvent` of the empty point set is empty:
the adopted `OuterChallenge.fixed_point_set_preimage_bound` at `∅`.  (This is the
same route the adopted `OuterSequentialConditioning.laneBad_card_of_inactive`
takes, and it is taken for the same reason: no tactic may enumerate
`Finset.univ` on `DigestTriple`.) -/
theorem tuple_event_empty :
    OuterChallenge.tupleEvent (∅ : Finset GoldilocksExt3Field.Element)
      = (∅ : Finset OuterChallenge.DigestTriple) := by
  have hb := OuterChallenge.fixed_point_set_preimage_bound
    (∅ : Finset GoldilocksExt3Field.Element)
  rw [Finset.card_empty, Nat.zero_mul] at hb
  exact Finset.card_eq_zero.mp (Nat.le_zero.mp hb)

/-- (7) **AND A ROUND'S BAD SET CAN BE EMPTY.**  In the closed instance below,
round `0`'s LOG bad set is empty: `echoLane` starts with
`claim = truthClaim = 0`, so the adopted `ConditionalSoundness.roundBadSet` takes
its diagonal branch, whatever the phase bit says. -/
theorem closed_log_bad_set_zero_empty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    (outerState L hL e0 strat hb echoLane coEchoLane T 0).1.badSet
      = (∅ : Finset GoldilocksExt3Field.Element) := by
  show (if true then ConditionalSoundness.roundBadSet (0 : GoldilocksExt3Field.Element) 0 _
      else ∅) = ∅
  rw [if_pos rfl, ConditionalSoundness.roundBadSet, if_pos rfl]

/-- (7) **AND SO IS ROUND `1`'s.**  Round `0`'s message of `echoLane` is the
EMPTY list (`[].take 1 = []`), so round `0` advances the two running claims by
the SAME adopted `OuterRound.evaluate` and they are still equal at round `1`. -/
theorem closed_log_bad_set_one_empty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    (outerState L hL e0 strat hb echoLane coEchoLane T 1).1.badSet
      = (∅ : Finset GoldilocksExt3Field.Element) := by
  show (if true then ConditionalSoundness.roundBadSet
      (OuterRound.evaluate 0 [] (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb 0 T)))
      (OuterRound.evaluate 0 [] (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb 0 T)))
      _ else ∅) = ∅
  rw [if_pos rfl, ConditionalSoundness.roundBadSet, if_pos rfl]

/-- (7) **AND SO IS THE GATE LANE'S ROUND `0`.** -/
theorem closed_gate_bad_set_zero_empty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    (laneStep (outerState L hL e0 strat hb echoLane coEchoLane T 0).2
        (logTriple L hL e0 strat hb 0 T)).badSet
      = (∅ : Finset GoldilocksExt3Field.Element) := by
  show (if true then ConditionalSoundness.roundBadSet (0 : GoldilocksExt3Field.Element) 0 _
      else ∅) = ∅
  rw [if_pos rfl, ConditionalSoundness.roundBadSet, if_pos rfl]

/-- (7) **THE DIGEST-LEVEL CONSEQUENCE, ROUND BY ROUND.**  In the closed instance
the LOG target is EMPTY at rounds `0` and `1` and the GATE target is EMPTY at
round `0`.  So AT THAT INSTANCE the per-round bound of section 4 is, at those
rounds, a bound on an empty set: the closed instance certifies that the module's
hypotheses are DISCHARGEABLE, NOT that the events it bounds are inhabited.  For
an inhabited round bad set see `separated_lane_round_zero_target_nonempty`.
Whether the closed instance's bad sets are non-empty at rounds `2` and beyond --
where the two running claims do part company -- is NOT settled here. -/
theorem closed_log_target_zero_empty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    logTarget L hL e0 strat hb echoLane coEchoLane 0 T
      = (∅ : Finset OuterChallenge.DigestTriple) := by
  rw [logTarget, laneBad, closed_log_bad_set_zero_empty L hL e0 strat hb T]
  exact tuple_event_empty

theorem closed_log_target_one_empty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    logTarget L hL e0 strat hb echoLane coEchoLane 1 T
      = (∅ : Finset OuterChallenge.DigestTriple) := by
  rw [logTarget, laneBad, closed_log_bad_set_one_empty L hL e0 strat hb T]
  exact tuple_event_empty

theorem closed_gate_target_zero_empty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    gateTarget L hL e0 strat hb echoLane coEchoLane 0 T
      = (∅ : Finset OuterChallenge.DigestTriple) := by
  rw [gateTarget, laneBad, closed_gate_bad_set_zero_empty L hL e0 strat hb T]
  exact tuple_event_empty

/-- (7) **THE LOG LANE OWNS EVERY ROUND OF THE CLOSED INSTANCE.**  THIS IS A
STATEMENT ABOUT THE PHASE BIT AND NOTHING ELSE.  It does NOT say any round's bad
set is non-empty: `closed_log_target_zero_empty` and
`closed_log_target_one_empty` show two of this very instance's log bad sets are
EMPTY.  For a lane whose round bad set is provably non-empty see
`separated_lane_round_zero_target_nonempty`. -/
theorem closed_lanes_log_owns (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L))
    (r : Nat) : (outerState L hL e0 strat hb echoLane coEchoLane T r).1.ownsNext = true := by
  rw [outer_state_log_owns L hL e0 strat hb echoLane coEchoLane T r, echo_lane_owns]

/-- (7) **AND SO DOES THE GATE LANE, AT ITS OWN COORDINATE** -- again a
statement about the phase bit only (`closed_gate_target_zero_empty`). -/
theorem closed_lanes_gate_owns (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L))
    (r : Nat) :
    (laneStep (outerState L hL e0 strat hb echoLane coEchoLane T r).2
      (logTriple L hL e0 strat hb r T)).ownsNext = true := by
  rw [outer_state_gate_owns L hL e0 strat hb echoLane coEchoLane T r, co_echo_lane_owns]
  rfl

/-- (7) **THE CLOSED INSTANCE.**  At the envelope's thirteen coupled rounds, for
the strategic prover of the adopted
`StrategyChainBound.challengeTruncatedMessage` -- whose round message is a real
function of the challenge answers it has read and which obeys the protocol's
causality -- and for two lanes that genuinely read the reduced challenge prefix,
the outer lane bad-draw mass is at most the adopted `outerTerm 13 8` plus the
adopted `3828 / |Block|`.  Neither `hb` nor `64 ≤ L` is a hypothesis: both are
discharged from the adopted prefix bound and the adopted degree bounds.

**READ THIS WITH THE HEADER.**  The strategy and the lanes here are still
UNPAIRED: `challengeTruncatedMessage` reads the RAW block at stage `22 + 5 * r`,
counter `0`, through `Transcript.fromLe`, and `echoLane` / `coEchoLane` read the
REDUCED round challenges -- the prover's own message never enters either bad set.
And the bad sets caught here are in part EMPTY: `closed_log_target_zero_empty`,
`closed_log_target_one_empty` and `closed_gate_target_zero_empty`.  WHAT THIS
INSTANCE CERTIFIES IS THAT EVERY HYPOTHESIS OF SECTION 5 IS DISCHARGEABLE AT A
CONCRETE CONFIGURATION, and nothing more. -/
theorem outer_lane_bound_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2) (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (outerLaneBadEvent L (Nat.le_trans (by omega) hLq) OuterInitial.zeroDigest
          (strategicShape c s (challengeTruncatedMessage m))
          (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
          echoLane coEchoLane 13)
      ≤ ChallengeUnionBound.outerTerm 13 8 + 3828 / (Fintype.card Block : ℚ) := by
  have h := outer_lane_bad_draw_probability_le L (Nat.le_trans (by omega) hLq)
    OuterInitial.zeroDigest (strategicShape c s (challengeTruncatedMessage m))
    (challenge_truncated_strategic_bounded L c s m 8 hpre hmlog hmgate hLq)
    echoLane coEchoLane 13 8 echoLane_bounded (co_echo_lane_bounded 8)
  have harith : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  rw [harith] at h
  exact h

/-- (7) **THE CLOSED BOUND IS A REAL NUMBER STRICTLY BELOW `1`.**  The adopted
digest-ratio evaluation puts the outer term at most `2 ^ (-172)` and the adopted
`ConcreteChainThreading.birthday_term_le_two_pow_neg` puts the chain term at most
`2 ^ (-244)`.  `Fintype.card Block` is never evaluated: it enters only through the
adopted lemma.  Read HONESTY (v): this is NOT the protocol's soundness error. -/
theorem outer_lane_bound_at_thirteen_lt_one :
    ChallengeUnionBound.outerTerm 13 8 + 3828 / (Fintype.card Block : ℚ) < 1 := by
  have h1 : ChallengeUnionBound.outerTerm 13 8 ≤ (1 : ℚ) / 2 ^ 172 := by
    rw [ChallengeUnionBound.outerTerm, ChallengeUnionBound.digest_ratio_explicit]
    norm_num [Arithmetic.modulus]
  have h2 : (3828 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 244 :=
    ConcreteChainThreading.birthday_term_le_two_pow_neg
  have h3 : (1 : ℚ) / 2 ^ 172 + 1 / 2 ^ 244 < 1 := by norm_num
  linarith


/-! ## 8. THE REDUCED-HISTORY SUBCLASS: A GENUINE ADAPTIVE UNION BOUND -/

/-- **THE REDUCED ROUND-CHALLENGE HISTORY OF THE FIRST `r` ROUNDS**, exactly as a
`Lane` sees it: OLDEST FIRST, the log challenge of a round before its gate
challenge, each the adopted `OuterChallenge.reduceTriple` of the three blocks at
counters `0, 1, 2` (log) and `3, 4, 5` (gate) of the round's own stage. -/
def reducedHistory (ch : Nat → Nat → Block) : Nat → List GoldilocksExt3Field.Element
  | 0 => []
  | r + 1 =>
      reducedHistory ch r
        ++ [OuterChallenge.reduceTriple
              (ch (roundStage r) 0, ch (roundStage r) 1, ch (roundStage r) 2),
            OuterChallenge.reduceTriple
              (ch (roundStage r) 3, ch (roundStage r) 4, ch (roundStage r) 5)]

theorem reduced_history_succ (ch : Nat → Nat → Block) (r : Nat) :
    reducedHistory ch (r + 1)
      = reducedHistory ch r
        ++ [OuterChallenge.reduceTriple
              (ch (roundStage r) 0, ch (roundStage r) 1, ch (roundStage r) 2),
            OuterChallenge.reduceTriple
              (ch (roundStage r) 3, ch (roundStage r) 4, ch (roundStage r) 5)] := rfl

/-- **A REDUCED-HISTORY PROVER.**  Its round `r` message is a function of the
reduced round-challenge history of the rounds before `r` AND OF NOTHING ELSE --
no raw block, no counter above `5`, no stage that is not a round stage.  This is
exactly the domain a `Lane` has, which is why the pairing of section 8 works and
the general one of sections 1 to 7 cannot (see the header). -/
def ReducedStrategy : Type :=
  Nat → List GoldilocksExt3Field.Element → Verifier.CoupledMessage

/-- The adopted `StrategyChainBound.strategicShape` round-message function of a
reduced-history prover: read counters `0` to `5` at the round stages, reduce, and
apply. -/
def reducedRoundMessage (R : ReducedStrategy) :
    Nat → (Nat → Nat → Block) → Verifier.CoupledMessage :=
  fun r ch => R r (reducedHistory ch r)

/-- **THE EMBEDDING INTO THE ADOPTED `Strategy`.** -/
def strategyOfReduced (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy) :
    Strategy :=
  strategicShape c s (reducedRoundMessage R)

/-- (8) The reduced history reads the round stages of the EARLIER rounds only. -/
theorem reduced_history_congr (ch1 ch2 : Nat → Nat → Block) :
    ∀ n : Nat, (∀ i, i < n → ch1 (roundStage i) = ch2 (roundStage i)) →
      reducedHistory ch1 n = reducedHistory ch2 n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n2 ih =>
      intro h
      rw [reduced_history_succ, reduced_history_succ, ih (fun i hi => h i (by omega)),
        h n2 (by omega)]

/-- (8) **A REDUCED-HISTORY PROVER OBEYS THE PROTOCOL'S CAUSALITY.**  Round `r`
reads the stages `roundStage i = 22 + (5 i + 5)` for `i < r`, and the largest of
them is `roundStage (r - 1) = 22 + 5 r`, which is exactly what the adopted
`StrategyChainBound.RoundCausal` allows. -/
theorem reduced_round_causal (R : ReducedStrategy) : RoundCausal (reducedRoundMessage R) := by
  intro r ch1 ch2 h
  show R r (reducedHistory ch1 r) = R r (reducedHistory ch2 r)
  rw [reduced_history_congr ch1 ch2 r (fun i hi => h (roundStage i) (by rw [roundStage]; omega))]

/-- (8) The length budget of a reduced-history prover, through the adopted
`StrategyChainBound.strategic_shape_bounded`. -/
theorem strategy_of_reduced_bounded (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (R : ReducedStrategy) (q : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hlog : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).1.length ≤ 5)
    (hgate : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).2.length ≤ q + 2)
    (hL : 189 + 24 * q ≤ L) :
    StrategyBounded L (strategyOfReduced c s R) :=
  strategic_shape_bounded L c s (reducedRoundMessage R) q hpre
    (fun r ch => hlog r (reducedHistory ch r)) (fun r ch => hgate r (reducedHistory ch r)) hL

/-- **THE REDUCED CHALLENGE PREFIX THE LANES ACTUALLY READ AT ONE TABLE**: the
reductions of the realized log and gate triples of the rounds before `r`, oldest
first. -/
def outerHistory (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L)) :
    Nat → List GoldilocksExt3Field.Element
  | 0 => []
  | r + 1 =>
      outerHistory L hL e0 strat hb T r
        ++ [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T),
            OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb r T)]

theorem outer_history_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L)) (r : Nat) :
    outerHistory L hL e0 strat hb T (r + 1)
      = outerHistory L hL e0 strat hb T r
        ++ [OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r T),
            OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb r T)] := rfl

theorem outer_history_length (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat, (outerHistory L hL e0 strat hb T r).length = 2 * r := by
  intro r
  induction r with
  | zero => rfl
  | succ r2 ih =>
      rw [outer_history_succ, List.length_append, ih]
      rfl

/-- (8) A list is what `take` of its own length returns, and an appended list is
what `take` of the first summand's length returns.  Proved here so that no
Mathlib name is depended on. -/
theorem take_length_append (xs ys : List GoldilocksExt3Field.Element) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x xs2 ih =>
      show x :: (xs2 ++ ys).take xs2.length = x :: xs2
      rw [ih]

theorem take_own_length (xs : List GoldilocksExt3Field.Element) : xs.take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x xs2 ih =>
      show x :: xs2.take xs2.length = x :: xs2
      rw [ih]

/-- (8) **THE LANE STATE'S MESSAGE FUNCTION IS THE INPUT LANE'S, APPLIED TO THE
REDUCED PREFIX.**  This is the precise sense in which a `Lane`'s round message
reads the reduced challenge prefix and nothing else -- the fact the header's
`laneOfStrategy` paragraph rests on. -/
theorem outer_state_message (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (logLane gateLane : Lane)
    (T : OracleTable (boundedQueries L)) :
    ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element),
      (outerState L hL e0 strat hb logLane gateLane T r).1.message xs
          = logLane.message (outerHistory L hL e0 strat hb T r ++ xs) ∧
        (outerState L hL e0 strat hb logLane gateLane T r).2.message xs
          = gateLane.message (outerHistory L hL e0 strat hb T r ++ xs) := by
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
      · show (outerState L hL e0 strat hb logLane gateLane T r2).1.message
            (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r2 T)
              :: OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb r2 T) :: xs)
          = logLane.message (outerHistory L hL e0 strat hb T (r2 + 1) ++ xs)
        rw [(ih _).1, hsplit]
      · show (outerState L hL e0 strat hb logLane gateLane T r2).2.message
            (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb r2 T)
              :: OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb r2 T) :: xs)
          = gateLane.message (outerHistory L hL e0 strat hb T (r2 + 1) ++ xs)
        rw [(ih _).2, hsplit]

/-- (8) **THE REDUCED HISTORY A REDUCED-HISTORY PROVER READS IS THE LANES' OWN
PREFIX.**  Whenever the challenge function the prover is handed agrees with the
table at the round stages of the earlier rounds -- which the adopted
`StrategyChainBound.strategic_challenges_is_sel` supplies -- the two histories are
the same list. -/
theorem reduced_history_is_outer_history (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L))
    (ch : Nat → Nat → Block) :
    ∀ n : Nat, (∀ i, i < n → ∀ cnt, ch (roundStage i) cnt
        = T (challengeSel L hL e0 strat hb (roundStage i) cnt T)) →
      reducedHistory ch n = outerHistory L hL e0 strat hb T n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n2 ih =>
      intro h
      rw [reduced_history_succ, outer_history_succ, ih (fun i hi cnt => h i (by omega) cnt),
        h n2 (by omega) 0, h n2 (by omega) 1, h n2 (by omega) 2,
        h n2 (by omega) 3, h n2 (by omega) 4, h n2 (by omega) 5]
      rfl

/-- (8) The instance of the previous lemma the pairing needs: at a strategic
prover the challenge function of round `r` IS the table at every round stage
before `r`. -/
theorem reduced_history_at_strategic (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    reducedHistory (strategicChallenges L hL c s (reducedRoundMessage R) hb r T) r
      = outerHistory L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r := by
  refine reduced_history_is_outer_history L hL OuterInitial.zeroDigest
    (strategyOfReduced c s R) hb T _ r (fun i hi cnt => ?_)
  exact strategic_challenges_is_sel L hL c s (reducedRoundMessage R) hb r T (roundStage i) cnt
    (by rw [roundStage]; omega)

/-- THE LOG LANE OF A REDUCED-HISTORY PROVER: its round message IS the prover's,
lifted to `Element` by the adopted `OuterRound.lift`.  The prefix it is handed at
round `r` has `2 r` entries (`outer_history_length`), which is how the round index
is recovered. -/
def reducedLogMessage (R : ReducedStrategy) (xs : List GoldilocksExt3Field.Element) :
    List GoldilocksExt3Field.Element :=
  (R (xs.length / 2) (xs.take (2 * (xs.length / 2)))).1.map OuterRound.lift

/-- The same for the gate cell.  At a GATE coordinate the prefix has `2 r + 1`
entries -- the round's own log challenge has already been absorbed -- and the
`take` drops it, so the gate message of round `r` is a function of the rounds
BEFORE `r` only, as the adopted `RoundCausal` demands. -/
def reducedGateMessage (R : ReducedStrategy) (xs : List GoldilocksExt3Field.Element) :
    List GoldilocksExt3Field.Element :=
  (R (xs.length / 2) (xs.take (2 * (xs.length / 2)))).2.map OuterRound.lift

def logLaneOfReduced (R : ReducedStrategy)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element) : Lane where
  message := reducedLogMessage R
  truth := tr
  claim := a
  truthClaim := b
  ownsNext := true

def gateLaneOfReduced (R : ReducedStrategy)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element) : Lane where
  message := reducedGateMessage R
  truth := tr
  claim := a
  truthClaim := b
  ownsNext := false

theorem log_lane_of_reduced_bounded (R : ReducedStrategy)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element) (bd : Nat)
    (hR : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).1.length ≤ bd)
    (htr : ∀ xs, (tr xs).length ≤ bd) : (logLaneOfReduced R tr a b).Bounded bd := by
  intro xs
  refine ⟨?_, htr xs⟩
  show ((R (xs.length / 2) (xs.take (2 * (xs.length / 2)))).1.map OuterRound.lift).length ≤ bd
  rw [List.length_map]
  exact hR _ _

theorem gate_lane_of_reduced_bounded (R : ReducedStrategy)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element) (bd : Nat)
    (hR : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).2.length ≤ bd)
    (htr : ∀ xs, (tr xs).length ≤ bd) : (gateLaneOfReduced R tr a b).Bounded bd := by
  intro xs
  refine ⟨?_, htr xs⟩
  show ((R (xs.length / 2) (xs.take (2 * (xs.length / 2)))).2.map OuterRound.lift).length ≤ bd
  rw [List.length_map]
  exact hR _ _

/-- (8) **THE LOG LANE'S ROUND-`r` MESSAGE IS THE PROVER'S REALIZED ROUND-`r` LOG
MESSAGE.**  This is the pairing sections 1 to 7 do not have: the left-hand side
is the message the LANE's bad set at round `r` is built from (the adopted
`Lane.badSet` reads `message []` at the state of `outerState … r`), and the
right-hand side is the log cell the STRATEGY really emits at that table, lifted
by the adopted `OuterRound.lift`. -/
theorem log_lane_of_reduced_message_is_realized (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (gateLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    (outerState L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
        (logLaneOfReduced R tr a b) gateLane T r).1.message []
      = (reducedRoundMessage R r
          (strategicChallenges L hL c s (reducedRoundMessage R) hb r T)).1.map OuterRound.lift := by
  have hlen := outer_history_length L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r
  have hstate := (outer_state_message L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
    (logLaneOfReduced R tr a b) gateLane T r []).1
  rw [hstate, List.append_nil]
  show ((R ((outerHistory L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r).length / 2)
      ((outerHistory L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r).take
        (2 * ((outerHistory L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r).length
          / 2)))).1.map OuterRound.lift)
    = (R r (reducedHistory (strategicChallenges L hL c s (reducedRoundMessage R) hb r T) r)).1.map
        OuterRound.lift
  rw [hlen, Nat.mul_div_cancel_left r (by omega), ← hlen, take_own_length,
    reduced_history_at_strategic L hL c s R hb r T]

/-- (8) **AND THE GATE LANE'S ROUND-`r` MESSAGE IS THE PROVER'S REALIZED ROUND-`r`
GATE MESSAGE**, at the state the adopted `gateTarget` reads it from: after the
round's own LOG triple has been absorbed. -/
theorem gate_lane_of_reduced_message_is_realized (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (logLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    (laneStep (outerState L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
        logLane (gateLaneOfReduced R tr a b) T r).2
      (logTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb r T)).message []
      = (reducedRoundMessage R r
          (strategicChallenges L hL c s (reducedRoundMessage R) hb r T)).2.map OuterRound.lift := by
  have hlen := outer_history_length L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r
  have hstate := (outer_state_message L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
    logLane (gateLaneOfReduced R tr a b) T r
    [OuterChallenge.reduceTriple
      (logTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb r T)]).2
  show (outerState L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
      logLane (gateLaneOfReduced R tr a b) T r).2.message
      [OuterChallenge.reduceTriple
        (logTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb r T)]
    = (R r (reducedHistory (strategicChallenges L hL c s (reducedRoundMessage R) hb r T) r)).2.map
        OuterRound.lift
  rw [hstate]
  have hlen2 : (outerHistory L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r
      ++ [OuterChallenge.reduceTriple
        (logTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb r T)]).length
      = 2 * r + 1 := by
    rw [List.length_append, hlen]
    rfl
  show ((R (( _ : List GoldilocksExt3Field.Element).length / 2) _).2.map OuterRound.lift) = _
  rw [hlen2, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  rw [show 2 * r
      = (outerHistory L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb T r).length
      from hlen.symm, take_length_append,
    reduced_history_at_strategic L hL c s R hb r T]

/-- (8) **THE HEADLINE FOR THE REDUCED-HISTORY SUBCLASS: SCB HONESTY (iii), FOR
THESE PROVERS.**  The strategy is `strategyOfReduced c s R` and the lanes are ITS
OWN (`log_lane_of_reduced_message_is_realized` and its gate twin), so round `r`'s
bad set is built from the message THE PROVER CHOSE after seeing the reduced
challenges of the earlier rounds.  For this subclass the bound below IS the
adaptive union bound the adopted `StrategyChainBound` HONESTY (iii) asks for.
RAW-BLOCK-READING STRATEGIES ARE NOT COVERED: see the header. -/
theorem reduced_outer_lane_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (trlog trgate : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a1 b1 a2 b2 : GoldilocksExt3Field.Element)
    (hb : StrategyBounded L (strategyOfReduced c s R)) (d q : Nat)
    (hRlog : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).1.length ≤ 5)
    (hRgate : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).2.length ≤ q + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ q + 2) :
    oracleProbability (boundedQueries L)
        (outerLaneBadEvent L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
          (logLaneOfReduced R trlog a1 b1) (gateLaneOfReduced R trgate a2 b2) d)
      ≤ ChallengeUnionBound.outerTerm d q
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  outer_lane_bad_draw_probability_le L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hb
    (logLaneOfReduced R trlog a1 b1) (gateLaneOfReduced R trgate a2 b2) d q
    (log_lane_of_reduced_bounded R trlog a1 b1 5 hRlog htrlog)
    (gate_lane_of_reduced_bounded R trgate a2 b2 (q + 2) hRgate htrgate)

/-- **A NON-TRIVIAL REDUCED-HISTORY PROVER.**  Its gate cell is kept or dropped
according to the value of ROUND `0`'S REDUCED LOG CHALLENGE -- the head of the
history in the adopted oldest-first order, read at every round `r >= 1` (an
earlier round's challenge, not the immediately previous one).  So this is not a fixed prover dressed up: two histories differing at that
entry give different messages (`previous_challenge_message_depends`). -/
def previousChallengeMessage (m : Verifier.CoupledMessage) : ReducedStrategy :=
  fun _ xs => (m.1, if xs.headD 0 = 0 then [] else m.2)

theorem previous_challenge_message_log (m : Verifier.CoupledMessage) (r : Nat)
    (xs : List GoldilocksExt3Field.Element) :
    (previousChallengeMessage m r xs).1 = m.1 := rfl

theorem previous_challenge_message_log_length (m : Verifier.CoupledMessage) (bd : Nat)
    (h : m.1.length ≤ bd) (r : Nat) (xs : List GoldilocksExt3Field.Element) :
    (previousChallengeMessage m r xs).1.length ≤ bd := h

theorem previous_challenge_message_gate_length (m : Verifier.CoupledMessage) (bd : Nat)
    (h : m.2.length ≤ bd) (r : Nat) (xs : List GoldilocksExt3Field.Element) :
    (previousChallengeMessage m r xs).2.length ≤ bd := by
  show (if xs.headD 0 = 0 then [] else m.2).length ≤ bd
  by_cases hx : xs.headD 0 = (0 : GoldilocksExt3Field.Element)
  · rw [if_pos hx]
    exact Nat.zero_le _
  · rw [if_neg hx]
    exact h

/-- (8) **IT REALLY READS THE PREVIOUS CHALLENGE.**  At the history whose first
entry is `0` the gate cell is empty; at the history whose first entry is `1` it is
`m.2`.  So `previousChallengeMessage m` is not constant in its history argument as
soon as `m.2` is not empty. -/
theorem previous_challenge_message_depends (m : Verifier.CoupledMessage) (hm : m.2 ≠ [])
    (r : Nat) :
    previousChallengeMessage m r [(0 : GoldilocksExt3Field.Element)]
      ≠ previousChallengeMessage m r [(1 : GoldilocksExt3Field.Element)] := by
  intro h
  have h2 : (if ([(0 : GoldilocksExt3Field.Element)].headD 0) = 0 then [] else m.2)
      = (if ([(1 : GoldilocksExt3Field.Element)].headD 0) = 0 then [] else m.2) :=
    congrArg Prod.snd h
  have hz0 : ([(0 : GoldilocksExt3Field.Element)].headD 0) = 0 := rfl
  have hz1 : ¬ (([(1 : GoldilocksExt3Field.Element)].headD 0) = 0) := by
    intro hz
    exact zero_ne_one (show (0 : GoldilocksExt3Field.Element) = 1 from hz.symm)
  rw [if_pos hz0, if_neg hz1] at h2
  exact hm h2.symm

/-- (8) **THE CLOSED INSTANCE OF THE SUBCLASS**, at the envelope's thirteen
coupled rounds: for the reduced-history prover above and the lanes IT DETERMINES,
the outer lane bad-draw mass is at most the adopted `outerTerm 13 8` plus the
adopted `3828 / |Block|`.  The two running claims are free parameters, as in the
adopted `ConditionalSoundness` model; the honest round messages `trlog`,
`trgate` are free subject to the adopted degree bounds. -/
theorem previous_challenge_bound_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage)
    (trlog trgate : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a1 b1 a2 b2 : GoldilocksExt3Field.Element)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ 8 + 2)
    (hLq : 189 + 24 * 8 ≤ L) :
    oracleProbability (boundedQueries L)
        (outerLaneBadEvent L (Nat.le_trans (by omega) hLq) OuterInitial.zeroDigest
          (strategyOfReduced c s (previousChallengeMessage m))
          (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
          (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
          (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2) 13)
      ≤ ChallengeUnionBound.outerTerm 13 8 + 3828 / (Fintype.card Block : ℚ) := by
  have h := reduced_outer_lane_bad_draw_probability_le L (Nat.le_trans (by omega) hLq) c s
    (previousChallengeMessage m) trlog trgate a1 b1 a2 b2
    (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
    13 8 (previous_challenge_message_log_length m 5 hmlog)
    (previous_challenge_message_gate_length m (8 + 2) hmgate) htrlog htrgate
  have harith : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  rw [harith] at h
  exact h

end Audit.Wire3.OuterLaneTransport
