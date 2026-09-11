import Audit.Wire3.GrindingQueryBound
import Audit.Wire3.RawBlockLanes

/-!
# THE UNION BOUND ALONG A GRINDING CHAIN, FOR PROBE-AND-CHALLENGE-CAUSAL LANES

## The gap this module addresses

`GrindingQueryBound` (GQB) extends the adopted chain bound to a prover that makes
`q` FRAME PROBES of its own at every stage, and bounds the CHAIN'S CLASH EVENT for
it by `N (N + 1) / 2 / |Block|` at `N = (q + 1) n`.  Its HONESTY (iii) names what
that leaves out:

  "THE UNION BOUND FOR A GRINDING PROVER IS NOT DELIVERED. ... section 3
   discharges the clash term for a grinding prover, and the `combinedBound` half
   ... is NOT re-derived here, for a grinding prover or for any other.  Nothing
   below aggregates into a run-level statement."

`RawBlockLanes` (RBL) delivers that other half -- `combinedBound` plus one clash
term -- but only for a `StrategyChainBound.Strategy`, a TRANSCRIPT-RESTRICTED
prover that makes no oracle queries at all.  THIS MODULE JOINS THE TWO: it proves
the `combinedBound` half along a GRINDING chain, and adds GQB's clash term, for a
prover with `q` own queries per stage.

## What is proved

1. THE CHALLENGE LAYER OVER AN ABSTRACT CHAIN (sections 1 and 2).  The adopted
   `OuterLaneTransport` peel machinery -- `stage_peel_card`,
   `stage_triple_fibre_card`, `stage_triple_target_card`,
   `stage_triple_target_mass_le` -- and the adopted `ReducedFullTransport` tau
   column count are stated at `StrategyChainBound.challengeSel`, the challenge
   query of a TRANSCRIPT-RESTRICTED chain, and a grinding chain is not one of
   those (GQB `probe_grinder_is_not_transcript_restricted`).  Sections 1 and 2
   restate that counting over an ABSTRACT stage-digest family
   `st : Nat -> OracleTable -> Digest`, with the two facts the adopted proofs
   actually use -- the stage-`j` digest is unmoved by its own challenge answers
   (`ChainStable`), and two counters at one digest are two different queries --
   as HYPOTHESES.  `chain_triple_target_mass_le` and `chain_tau_target_mass_le`
   are the results.  Nothing about a strategy is used.
2. THE GRINDING CHAIN'S CHALLENGE CELLS (section 3).  `ChallengeRestricted` says
   the stage-`k` probe and absorb read the challenge oracle only at the stage
   digests `0, …, k` -- exactly what the adopted `StrategyChainBound.Strategy` is
   handed.  Under it, `grind_run_ans_challenge_stable` runs the causal induction
   over ALL `j (q + 1)` positions before stage `j` -- probes included -- and
   `grind_state_challenge_stable` concludes that the stage digests up to `j` do
   not move when a stage-`j` challenge answer is overwritten, on the chain's
   no-clash event.  `grind_no_clash_chain_stable_all` is section 1's hypothesis,
   discharged.
3. THE LANES OF A GRINDING RUN, AT THE GRINDER'S OWN DOMAIN (sections 4 to 6).
   `grindTableView` is the raw 32-byte challenge view of a grinding run at every
   stage and every counter, and `grindRunView` is the run's OWN ANSWER LIST --
   every probe answer and every absorb answer, at every position of the
   interleaved sequence.  `GrindLane` WIDENS the adopted `RawBlockLanes.RawLane`
   by that second argument:
   `message : Nat -> (Nat -> Block) -> (Nat -> Nat -> Block) -> List Element`,
   so a round message may be a function of the prover's PROBE ANSWERS, which no
   `RawLane` can be.  `GrindCausal` is the adopted `RawCausal` clause plus the
   run-side clause, and `grind_lane_of_raw_lane_causal` lifts every adopted raw
   lane into the wider class.  `grind_run_view_reassign_lower` is what the
   widening costs and it is free: a probe answer is a FRAME cell, and
   `grind_run_ans_challenge_stable` already proves the frame cells before stage
   `j` are unmoved by a stage-`j` CHALLENGE cell.  `grind_raw_target_reassign` is
   the diagonal invariance -- round `r`'s bad set is unmoved by ANY counter of
   round `r`'s own stage -- and `grinding_outer_bad_draw_probability_le` is the
   union over the rounds: `ChallengeUnionBound.outerTerm d q` plus the grinding
   chain's clash mass.  `probeReadingLane` is a lane that genuinely reads the
   prover's probe answers (`probe_reading_lane_reads_probes`), at the very cell
   the adopted `probeGrinder`'s own absorb reads
   (`probe_grinder_absorb_is_run_cell`).
4. THE BLOCK-0 LANES AND THE HEADLINE (sections 7 and 8).  The gate tau column
   and the gate alpha triple at the derive digest, at targets that are FIXED
   DATA, give the adopted `tauTerm` and `alphaTerm`; the three masses are
   conditioned on NESTED no-clash events, so ONE clash term pays for all three.
   `grinding_union_bad_draw_probability_le_combined`:

     `oracleProbability (boundedQueries L) (grindingFullBadEvent …)`
       `<= ChallengeUnionBound.combinedBound d q d constraints`
          `+ N (N + 1) / 2 / |Block|`,  `N = (22 + 5 d) (q + 1)`.

   THE CLASH CONSTANT IS `N (N + 1) / 2` AT `N = (22 + 5 d) (q + 1)`, GQB's, and
   it is the only place the probe budget `q` enters.
5. THE CLOSED INSTANCE (section 9).  At the envelope's thirteen rounds, for the
   adopted `GrindingQueryBound.probeGrinder` -- which reads its absorb off its
   first probe's answer, and which GQB proves is NOT a transcript-restricted
   prover -- and `separatedGrindLane`, the adopted `separatedRawLane` lifted, on
   both outer lanes, whose round-`0` target is provably inhabited:
   `combinedBound 13 8 13 123 + 4161109737606900 / |Block|` at `q = 2 ^ 20`, and
   `grinding_union_bound_at_thirteen_many_probes_lt_one` puts it below `1`.
6. THE ATTACK THE RESTRICTION EXCLUDES (section 10).  `GrindingRoundTargetInvariant`
   names the one property the diagonal step needs.  `echoGrinder` probes a payload
   and then absorbs it -- the query pattern EVERY grinder uses -- and
   `echo_grinder_pre_read_mass_one` shows the PRE-READ EVENT (some position before
   stage `k`'s absorb already answers the stage-`k + 1` digest, at which round
   `k + 1`'s challenges are squeezed) is then the WHOLE TABLE SPACE: mass exactly
   `1`.  `preReadGrinder` ACTS on such a read: it is `echoGrinder`'s query pattern
   with a SELECTOR absorb -- it evaluates the challenge oracle at the digest of
   its own probe-`0` answer and absorbs that probe's payload exactly when the
   answer it read is `preReadTarget`, a different payload otherwise.
   `pre_read_grinder_absorb_is_probe_when_favourable` shows that on the
   favourable branch the absorb asks the probe's own byte string, so the chain's
   next digest IS the digest whose challenges were pre-read; and
   `pre_read_grinder_not_challenge_restricted` shows it is a legal
   `GrindingStrategy` that the hypothesis of sections 5 to 8 excludes.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every statement below is about
the uniform counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`
-- one independent uniform block per byte string of length at most `L`.  The
fresh-step lemma everything rests on, the adopted
`BirthdayClashBound.adaptive_fresh_step_card`, is the DEFINING property of a
random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed Keccak by a table drawn from this law is an assumption with no proof
anywhere in this tree.

(ii) THE PROVER MAY PROBE FREELY AND MAY NOT PRE-READ CHALLENGES.  The prover of
sections 5 to 9 is a GQB `GrindingStrategy`: at every stage it issues `q` frame
queries of its own, at ANY digest, with ANY tag and ANY payload, chosen
adaptively from the whole history, and its absorb is a function of their answers.
That is a LARGER CLASS than the adopted `RawBlockLanes` covers, in both
directions of the comparison: `grinding_of_strategy_challenge_restricted` shows
EVERY adopted `StrategyChainBound.Strategy`, lifted by the adopted
`grindingOfStrategy`, satisfies the hypothesis, and
`probe_grinder_challenge_restricted` together with the adopted
`probe_grinder_is_not_transcript_restricted` exhibits a prover that satisfies it
and is NOT such a lift.  IT IS NOT CLAIMED THAT THIS SUBSUMES RBL's THEOREM: the
`q = 0` identity of `grindingFullBadEvent` with the adopted `rawFullBadEvent` is
not proved anywhere in this tree.  What is ASSUMED of the prover is
`ChallengeRestricted`: its challenge reads are at its own stage digests
`0, …, k` at stage `k`.

THIS ASSUMPTION IS NOT COSMETIC AND IT IS NOT DISCHARGED.  GQB's model hands
every strategy the challenge oracle IN FULL, at every digest, free of charge --
GQB HONESTY (iv), and for the CLASH event that is genuinely free.  For the UNION
bound it is not: a prover that evaluates the challenge oracle at the digest of a
PROBE ANSWER, and then ABSORBS THAT PROBE'S PAYLOAD WHEN AND ONLY WHEN THE ANSWER
IS FAVOURABLE, has chosen the round's message AFTER reading the round's
challenges, and round `r`'s bad set then MOVES when round `r`'s own challenge
cells are reassigned -- the diagonal step's hypothesis
`GrindingRoundTargetInvariant` fails.  `preReadGrinder` is that prover, written
out as exactly such a selector; nothing below bounds its bad-draw mass, and the
constant such a prover should pay -- roughly `q + 1` tries at each round's
challenge -- is NOT proved anywhere in this tree.

(iii) AND THE PRE-READ EVENT CANNOT BE CONDITIONED AWAY.  The natural repair is
to put the pre-read into the conditioning event and charge it a small mass, as
the chain's clash event is charged.  `echo_grinder_pre_read_mass_one` refutes
that: for a prover that probes a payload and then absorbs it -- the pattern every
grinder uses -- the pre-read event is the WHOLE table space.  Nor does GQB's
repeat-tolerant birthday bound reach it: `distinct_answer_clash_probability_le`
charges only pairs of positions that asked DIFFERENT byte strings, and the
probe-then-absorb pair asks the SAME one, which is exactly the case that theorem
deliberately excludes.  So the restriction of (ii) is where the line is drawn,
and drawing it elsewhere is open work, not a rewording.

(iv) THE OUTER LANES AND THE BLOCK-0 LANES ONLY.  What is bounded is
`grindingFullBadEvent`: the two OUTER sumcheck lanes over `d` coupled rounds, the
gate tau column and the gate alpha triple at the derive digest.  The INDEX lanes,
the WHIR folding transcript and the Merkle openings are NOT covered -- they are
not in `ChallengeUnionBound.combinedBound` at all -- and no round schedule is
threaded onto the grinding chain here, as the adopted
`RunLevelTransportAudit` does for a transcript-restricted prover.

(v) WHOSE BAD SETS THESE ARE -- AND WHY THE TITLE SAYS "PROBE-AND-CHALLENGE-
CAUSAL LANES".  Round `r`'s target is the LANE's, built from the message that
lane chose after seeing the grinding run's own answers and its raw challenge
view; the grinding strategy and the lanes are quantified SEPARATELY, exactly as
in the adopted `RawBlockLanes` sections 2 to 6.  Section 7 of that module pairs a
lane with a strategy's own realized messages; NO SUCH PAIRING IS PROVED HERE for
a grinding prover, so nothing below says the lanes carry the grinder's own round
messages.  The gate tau and gate alpha targets are FIXED DATA, bound outside the
oracle law.

BE PRECISE ABOUT WHAT THAT COSTS.  The adopted `RawLane.message` has domain
`Nat -> (Nat -> Nat -> Block) -> List Element`: a round message there is a
function of the CHALLENGE VIEW ALONE, and a grinder's message depends on its
PROBE ANSWERS, which is not of that type.  Sections 5 to 8 therefore DO NOT use
`RawLane`.

THE WIDENING IS DONE; THE PAIRING IS NOT.  `GrindLane` of section 5 has domain
`Nat -> (Nat -> Block) -> (Nat -> Nat -> Block) -> List Element`: the round
index, the RUN'S OWN ANSWERS -- probe answers included -- and the challenge view.
Sections 5 to 8 are proved at that domain, so the headline below is a bound for
lanes whose round messages read the prover's probes; `probeReadingLane` is such a
lane, `probe_reading_lane_reads_probes` shows it is not a lifted `RawLane` in
disguise, and `probe_grinder_absorb_is_run_cell` shows the cell it reads is the
cell the adopted `probeGrinder`'s own absorb reads.  WHAT IS STILL MISSING is the
PAIRING: a `grindLaneOfGrinder g` whose round-`r` message is literally `g`'s
stage-`22 + 5 r` absorb payload as a `List Element`.  Two things it would need
are absent here -- a bytes-to-elements decoder for the payload, and a truncation
of the unrestricted stage-digest argument the adopted `GrindingStrategy.absorb`
is handed (the run supplies a constant beyond the current stage, but the lane's
abstract argument does not).  So nothing below says the bad sets carry the
grinder's own messages; it says the lanes may now READ WHAT THE GRINDER READ.

(vi) THE LENGTH BUDGET AND THE COUNTER BUDGET ARE HYPOTHESES.
`GrindingBounded L g` is the adopted GQB budget; `12 + 6 d < Transcript.u64Limit`
is the adopted counter budget, discharged at `d = 13` by the adopted
`ReducedFullTransport.thirteen_counter_budget`.  `q` is a PARAMETER, not a cap:
nothing below says a real prover is limited to `q` queries, and the instance at
`q = 2 ^ 20` is an illustration of the arithmetic.

(vii) THE CLASH TERM IS GQB's, AND IT IS LOOSE IN `q`.  `N (N + 1) / 2` at
`N = (22 + 5 d) (q + 1)` is the ALL-PAIRS bound of GQB, quadratic in the probe
budget; GQB HONESTY (ii) records that a linear-in-`q` bound looks reachable and
is not proved.  Nothing here improves it.

(viii) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The bounds are on the
mass of one named event under the oracle law.  No extractor, no knowledge
soundness and no adaptive Fiat--Shamir soundness statement is proved or implied;
the design point of the deployed profile is about a hundred bits and nothing
below aggregates into a soundness statement for the protocol.

(ix) `Finset.univ` APPEARS ONLY IN THIS MODULE'S OWN EVENT DEFINITIONS --
`grindRawRoundBadEvent`, `grindGateAlphaBadEvent`, `grindGateTauBadEvent`,
`grindingPreReadEvent` -- where it cuts a cylinder out of the table space, exactly
as the adopted `RawBlockLanes.rawRoundBadEvent` and
`ReducedFullTransport.gateAlphaBadEvent` do -- and in `oracle_probability_univ`
and `echo_grinder_pre_read_event_is_everything`, where it IS the whole table
space and is the content of the statement.  No cardinality of `Element`,
`Block` or `OuterChallenge.DigestTriple` is ever evaluated numerically or handed
to a `ring` or `omega` goal; `Fintype.card Block` enters only through the adopted
`RandomOracleSqueezes.block_card`.
-/

namespace Audit.Wire3.GrindingUnionBound

open Audit.Wire3
open Audit.Wire3.GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport
open Audit.Wire3.RawBlockLanes
open Audit.Wire3.GrindingQueryBound

/-! ## 1. THE CHALLENGE LAYER OVER AN ABSTRACT STAGE-DIGEST FAMILY -/

/-- **THE STAGE-`j` CHALLENGE QUERY OF AN ABSTRACT CHAIN.**  `st j T` is the
digest a chain has reached after `j` stages at the table `T`; the run squeezes the
stage-`j` challenge of counter `c` at `Transcript.challengeInput (st j T) c`.  The
adopted `StrategyChainBound.challengeSel` is the case `st = strategyFrameState`;
the grinding chain of section 3 is the case `st = GrindingQueryBound.grindState`,
which is NOT of that form. -/
def chainChallengeSel (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j c : Nat)
    (T : OracleTable (boundedQueries L)) : { x : Transcript.Bytes // x ∈ boundedQueries L } :=
  ⟨Transcript.challengeInput (st j T) c, bounded_queries_challenge L hL _ c⟩

/-- (1) The stage-`j` challenge query itself does not move when a stage-`j`
challenge answer is overwritten, PROVIDED the stage-`j` digest does not. -/
theorem chain_sel_stable_at (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j a c : Nat)
    (T : OracleTable (boundedQueries L)) (b : Block)
    (hst : st j (reassign T (chainChallengeSel L hL st j a T) b) = st j T) :
    chainChallengeSel L hL st j c (reassign T (chainChallengeSel L hL st j a T) b)
      = chainChallengeSel L hL st j c T := by
  apply Subtype.ext
  show Transcript.challengeInput
      (st j (reassign T (chainChallengeSel L hL st j a T) b)) c
    = Transcript.challengeInput (st j T) c
  rw [hst]

/-- (1) Two challenge queries at one digest and different counters below the
adopted `Transcript.u64Limit` are two different queries. -/
theorem chain_sel_ne_of_counter (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j c1 c2 : Nat)
    (h1 : c1 < Transcript.u64Limit) (h2 : c2 < Transcript.u64Limit) (hne : c1 ≠ c2)
    (T : OracleTable (boundedQueries L)) :
    chainChallengeSel L hL st j c1 T ≠ chainChallengeSel L hL st j c2 T := by
  intro h
  exact hne (challenge_input_injective _ _ _ _ h1 h2 (congrArg Subtype.val h)).2

/-- (1) Overwriting the stage-`j` challenge answer of counter `a` leaves the other
counters of the same stage alone. -/
theorem chain_answer_reassign_ne (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j a c2 : Nat)
    (ha : a < Transcript.u64Limit) (h2 : c2 < Transcript.u64Limit) (hne : c2 ≠ a)
    (T : OracleTable (boundedQueries L)) (b : Block)
    (hst : st j (reassign T (chainChallengeSel L hL st j a T) b) = st j T) :
    (reassign T (chainChallengeSel L hL st j a T) b)
        (chainChallengeSel L hL st j c2 (reassign T (chainChallengeSel L hL st j a T) b))
      = T (chainChallengeSel L hL st j c2 T) := by
  rw [chain_sel_stable_at L hL st j a c2 T b hst]
  exact reassign_off T _ _ b (chain_sel_ne_of_counter L hL st j c2 a h2 ha hne T)

/-- **A CONDITIONING EVENT THE STAGE-`j` CHALLENGE ANSWERS CANNOT MOVE.**  The
abstract form of the adopted `OuterLaneTransport.StageStable`: on `A`, the
stage-`j` DIGEST is unmoved by overwriting the table at any stage-`j` challenge
query of a counter in `C`, and `A` itself is closed under that overwriting.  The
adopted version asks instead that `A` sit inside the chain's no-clash event and
derives the digest clause from the adopted
`StrategyChainBound.strategy_state_challenge_stable`; making that clause a
hypothesis is what lets the same counting serve a chain the adopted module does
not cover. -/
def ChainStable (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j : Nat) (C : Finset Nat)
    (A : Finset (OracleTable (boundedQueries L))) : Prop :=
  (∀ T ∈ A, ∀ c ∈ C, ∀ b : Block,
      st j (reassign T (chainChallengeSel L hL st j c T) b) = st j T) ∧
  (∀ T ∈ A, ∀ c ∈ C, ∀ b : Block, reassign T (chainChallengeSel L hL st j c T) b ∈ A)

/-- (1) Stability at a counter set gives stability at any subset of it. -/
theorem chain_stable_mono (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j : Nat) (C D : Finset Nat)
    (hCD : C ⊆ D) (A : Finset (OracleTable (boundedQueries L)))
    (h : ChainStable L hL st j D A) : ChainStable L hL st j C A :=
  ⟨fun T hT c hc b => h.1 T hT c (hCD hc) b, fun T hT c hc b => h.2 T hT c (hCD hc) b⟩

/-- (1) A stable event stays stable when it is cut down by a predicate the
stage-`j` challenge answers cannot move. -/
theorem chain_stable_filter (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j : Nat) (C : Finset Nat)
    (A : Finset (OracleTable (boundedQueries L))) (hA : ChainStable L hL st j C A)
    (P : OracleTable (boundedQueries L) → Prop) [DecidablePred P]
    (hP : ∀ T ∈ A, ∀ c ∈ C, ∀ b : Block,
      (P (reassign T (chainChallengeSel L hL st j c T) b) ↔ P T)) :
    ChainStable L hL st j C (A.filter P) := by
  refine ⟨fun T hT c hc b => hA.1 T (Finset.mem_filter.mp hT).1 c hc b, fun T hT c hc b => ?_⟩
  obtain ⟨hTA, hTP⟩ := Finset.mem_filter.mp hT
  exact Finset.mem_filter.mpr ⟨hA.2 T hTA c hc b, (hP T hTA c hc b).mpr hTP⟩

/-- (1) **ONE PEELED COUNTER, AS AN EXACT COUNT.**  Exactly a `1 / |Block|` share
of a stable conditioning event answers a prescribed block at the stage-`j`
challenge query of counter `a`.  The adopted
`BirthdayClashBound.adaptive_fresh_step_card` at a singleton target, with the
conditioning event and the chain both parameters. -/
theorem chain_peel_card (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j a : Nat)
    (A : Finset (OracleTable (boundedQueries L)))
    (hstab : ∀ T ∈ A, ∀ b : Block,
      st j (reassign T (chainChallengeSel L hL st j a T) b) = st j T)
    (hclosed : ∀ T ∈ A, ∀ b : Block, reassign T (chainChallengeSel L hL st j a T) b ∈ A)
    (b0 : Block) :
    (A.filter (fun T => T (chainChallengeSel L hL st j a T) = b0)).card
        * Fintype.card Block = A.card := by
  have hfresh : FreshStep (boundedQueries L) A (chainChallengeSel L hL st j a)
      (fun _ => ({b0} : Finset Block)) :=
    ⟨fun T hT b => hclosed T hT b,
     fun T hT b => chain_sel_stable_at L hL st j a a T b (hstab T hT b),
     fun _ _ _ => rfl⟩
  have hcard := adaptive_fresh_step_card hfresh
  have hsum : ∑ _U in A, ({b0} : Finset Block).card = A.card := by
    rw [Finset.sum_const, Finset.card_singleton, smul_eq_mul, Nat.mul_one]
  rw [hsum] at hcard
  have hset : A.filter (fun T => T (chainChallengeSel L hL st j a T) = b0)
      = A.filter (fun T =>
          T (chainChallengeSel L hL st j a T) ∈ ({b0} : Finset Block)) := by
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

/-- **THE DIGEST TRIPLE READ AT STAGE `j` FROM COUNTER `base`.**  The abstract
form of the adopted `OuterLaneTransport.stageTriple`. -/
def chainTriple (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j base : Nat)
    (T : OracleTable (boundedQueries L)) : OuterChallenge.DigestTriple :=
  (T (chainChallengeSel L hL st j base T),
   T (chainChallengeSel L hL st j (base + 1) T),
   T (chainChallengeSel L hL st j (base + 2) T))

theorem chain_triple_eq_iff (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j base : Nat)
    (T : OracleTable (boundedQueries L)) (ds : OuterChallenge.DigestTriple) :
    chainTriple L hL st j base T = ds ↔
      (T (chainChallengeSel L hL st j base T) = ds.1 ∧
        T (chainChallengeSel L hL st j (base + 1) T) = ds.2.1 ∧
        T (chainChallengeSel L hL st j (base + 2) T) = ds.2.2) := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2) h⟩
  · intro h
    show ((T (chainChallengeSel L hL st j base T),
      T (chainChallengeSel L hL st j (base + 1) T),
      T (chainChallengeSel L hL st j (base + 2) T)) : OuterChallenge.DigestTriple) = ds
    rw [h.1, h.2.1, h.2.2]

/-- (1) **THE TRIPLE AT ANOTHER COUNTER BLOCK OF THE SAME STAGE IS LEFT ALONE.**
The abstract form of the adopted `OuterLaneTransport.stage_triple_reassign_same`. -/
theorem chain_triple_reassign_same (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j base c : Nat)
    (hcu : c < Transcript.u64Limit) (hbase : base + 2 < Transcript.u64Limit)
    (hne : c ∉ tripleCounters base) (T : OracleTable (boundedQueries L)) (b : Block)
    (hst : st j (reassign T (chainChallengeSel L hL st j c T) b) = st j T) :
    chainTriple L hL st j base (reassign T (chainChallengeSel L hL st j c T) b)
      = chainTriple L hL st j base T := by
  have h0 : base ≠ c := fun h => hne (h ▸ (mem_triple_counters base base).mpr (Or.inl rfl))
  have h1 : base + 1 ≠ c :=
    fun h => hne (h ▸ (mem_triple_counters base (base + 1)).mpr (Or.inr (Or.inl rfl)))
  have h2 : base + 2 ≠ c :=
    fun h => hne (h ▸ (mem_triple_counters base (base + 2)).mpr (Or.inr (Or.inr rfl)))
  rw [chainTriple, chainTriple,
    chain_answer_reassign_ne L hL st j c base hcu (by omega) h0 T b hst,
    chain_answer_reassign_ne L hL st j c (base + 1) hcu (by omega) h1 T b hst,
    chain_answer_reassign_ne L hL st j c (base + 2) hcu hbase h2 T b hst]

/-- (1) **THE JOINT FIBRE COUNT AT ONE SCHEDULED DRAW.**  Conditioned on any
stable event, each of the `|Block| ^ 3` digest triples is read at the stage-`j`
counters `base, base + 1, base + 2` by exactly a `1 / |Block| ^ 3` share of it.
Three peels of `chain_peel_card`. -/
theorem chain_triple_fibre_card (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j base : Nat)
    (hbase : base + 2 < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : ChainStable L hL st j (tripleCounters base) A) (ds : OuterChallenge.DigestTriple) :
    (A.filter (fun T => chainTriple L hL st j base T = ds)).card
        * Fintype.card OuterChallenge.DigestTriple = A.card := by
  have hu0 : base < Transcript.u64Limit := by omega
  have hu1 : base + 1 < Transcript.u64Limit := by omega
  have hm0 : base ∈ tripleCounters base :=
    (mem_triple_counters base base).mpr (Or.inl rfl)
  have hm1 : base + 1 ∈ tripleCounters base :=
    (mem_triple_counters base (base + 1)).mpr (Or.inr (Or.inl rfl))
  have hm2 : base + 2 ∈ tripleCounters base :=
    (mem_triple_counters base (base + 2)).mpr (Or.inr (Or.inr rfl))
  have hA1stab : ∀ T ∈ A.filter (fun T => T (chainChallengeSel L hL st j base T) = ds.1),
      ∀ b : Block,
        st j (reassign T (chainChallengeSel L hL st j (base + 1) T) b) = st j T :=
    fun T hT b => hA.1 T (Finset.mem_filter.mp hT).1 (base + 1) hm1 b
  have hA1closed : ∀ T ∈ A.filter (fun T => T (chainChallengeSel L hL st j base T) = ds.1),
      ∀ b : Block,
        reassign T (chainChallengeSel L hL st j (base + 1) T) b
          ∈ A.filter (fun T => T (chainChallengeSel L hL st j base T) = ds.1) := by
    intro T hT b
    obtain ⟨hTA, hTv⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨hA.2 T hTA (base + 1) hm1 b, ?_⟩
    rw [chain_answer_reassign_ne L hL st j (base + 1) base hu1 hu0 (by omega) T b
      (hA.1 T hTA (base + 1) hm1 b)]
    exact hTv
  have hA2stab : ∀ T ∈ (A.filter
        (fun T => T (chainChallengeSel L hL st j base T) = ds.1)).filter
        (fun T => T (chainChallengeSel L hL st j (base + 1) T) = ds.2.1),
      ∀ b : Block,
        st j (reassign T (chainChallengeSel L hL st j (base + 2) T) b) = st j T :=
    fun T hT b =>
      hA.1 T (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).1 (base + 2) hm2 b
  have hA2closed : ∀ T ∈ (A.filter
        (fun T => T (chainChallengeSel L hL st j base T) = ds.1)).filter
        (fun T => T (chainChallengeSel L hL st j (base + 1) T) = ds.2.1),
      ∀ b : Block,
        reassign T (chainChallengeSel L hL st j (base + 2) T) b
          ∈ (A.filter (fun T => T (chainChallengeSel L hL st j base T) = ds.1)).filter
              (fun T => T (chainChallengeSel L hL st j (base + 1) T) = ds.2.1) := by
    intro T hT b
    obtain ⟨hT1, hTv1⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTA, hTv0⟩ := Finset.mem_filter.mp hT1
    have hstab2 := hA.1 T hTA (base + 2) hm2 b
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hA.2 T hTA (base + 2) hm2 b, ?_⟩, ?_⟩
    · rw [chain_answer_reassign_ne L hL st j (base + 2) base hbase hu0 (by omega) T b hstab2]
      exact hTv0
    · rw [chain_answer_reassign_ne L hL st j (base + 2) (base + 1) hbase hu1 (by omega) T b
        hstab2]
      exact hTv1
  have h0 := chain_peel_card L hL st j base A
    (fun T hT b => hA.1 T hT base hm0 b) (fun T hT b => hA.2 T hT base hm0 b) ds.1
  have h1 := chain_peel_card L hL st j (base + 1)
    (A.filter (fun T => T (chainChallengeSel L hL st j base T) = ds.1))
    hA1stab hA1closed ds.2.1
  have h2 := chain_peel_card L hL st j (base + 2)
    ((A.filter (fun T => T (chainChallengeSel L hL st j base T) = ds.1)).filter
      (fun T => T (chainChallengeSel L hL st j (base + 1) T) = ds.2.1))
    hA2stab hA2closed ds.2.2
  have hset : A.filter (fun T => chainTriple L hL st j base T = ds)
      = ((A.filter (fun T => T (chainChallengeSel L hL st j base T) = ds.1)).filter
          (fun T => T (chainChallengeSel L hL st j (base + 1) T) = ds.2.1)).filter
          (fun T => T (chainChallengeSel L hL st j (base + 2) T) = ds.2.2) := by
    apply Finset.ext
    intro T
    constructor
    · intro hT
      obtain ⟨hTA, hTv⟩ := Finset.mem_filter.mp hT
      obtain ⟨hv0, hv1, hv2⟩ := (chain_triple_eq_iff L hL st j base T ds).mp hTv
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hTA, hv0⟩, hv1⟩, hv2⟩
    · intro hT
      obtain ⟨hT2, hv2⟩ := Finset.mem_filter.mp hT
      obtain ⟨hT1, hv1⟩ := Finset.mem_filter.mp hT2
      obtain ⟨hTA, hv0⟩ := Finset.mem_filter.mp hT1
      exact Finset.mem_filter.mpr
        ⟨hTA, (chain_triple_eq_iff L hL st j base T ds).mpr ⟨hv0, hv1, hv2⟩⟩
  rw [hset, digest_triple_card_as_blocks]
  exact peel_three _ _ _ _ (Fintype.card Block) h2 h1 h0

/-- (1) **THE DIAGONAL BOUND AT ONE SCHEDULED DRAW, COUNTING FORM.**  The target
`targ T` is whatever the history has made it at the table `T`; what is asked of it
is only that the three stage-`j` challenge answers it is tested against cannot
move it.  The abstract form of the adopted
`OuterLaneTransport.stage_triple_target_card`. -/
theorem chain_triple_target_card (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j base : Nat)
    (hbase : base + 2 < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : ChainStable L hL st j (tripleCounters base) A)
    (targ : OracleTable (boundedQueries L) → Finset OuterChallenge.DigestTriple)
    (hinv : ∀ T ∈ A, ∀ c ∈ tripleCounters base, ∀ b : Block,
      targ (reassign T (chainChallengeSel L hL st j c T) b) = targ T)
    (m : Nat) (hm : ∀ T ∈ A, (targ T).card ≤ m) :
    (A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).card
        * Fintype.card OuterChallenge.DigestTriple ≤ m * A.card := by
  have hfib1 : (A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).card
      = ∑ S in A.image targ,
          ((A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).filter
            (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun x hx => Finset.mem_image_of_mem targ (Finset.mem_filter.mp hx).1)
  have hfib2 : A.card = ∑ S in A.image targ, (A.filter (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem targ hx)
  have key : ∀ S ∈ A.image targ,
      ((A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).filter
          (fun T => targ T = S)).card * Fintype.card OuterChallenge.DigestTriple
        ≤ m * (A.filter (fun T => targ T = S)).card := by
    intro S hS
    obtain ⟨T0, hT0A, hT0⟩ := Finset.mem_image.mp hS
    have hScard : S.card ≤ m := by
      rw [← hT0]
      exact hm T0 hT0A
    have hAS : ChainStable L hL st j (tripleCounters base) (A.filter (fun T => targ T = S)) := by
      refine chain_stable_filter L hL st j (tripleCounters base) A hA
        (fun T => targ T = S) (fun T hT c hc b => ?_)
      show targ (reassign T (chainChallengeSel L hL st j c T) b) = S ↔ targ T = S
      rw [hinv T hT c hc b]
    have hEq : (A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).filter
          (fun T => targ T = S)
        = (A.filter (fun T => targ T = S)).filter
            (fun T => chainTriple L hL st j base T ∈ S) := by
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
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hTA, hTS ▸ hTd⟩, hTS⟩
    have hinner : ∀ ds ∈ S,
        (((A.filter (fun T => targ T = S)).filter
            (fun T => chainTriple L hL st j base T ∈ S)).filter
          (fun T => chainTriple L hL st j base T = ds)).card
        = ((A.filter (fun T => targ T = S)).filter
            (fun T => chainTriple L hL st j base T = ds)).card := by
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
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hT1, hTe ▸ hds⟩, hTe⟩
    have hsplit : ((A.filter (fun T => targ T = S)).filter
          (fun T => chainTriple L hL st j base T ∈ S)).card
        = ∑ ds in S, ((A.filter (fun T => targ T = S)).filter
            (fun T => chainTriple L hL st j base T = ds)).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun T => chainTriple L hL st j base T) (t := S)
        (fun x hx => (Finset.mem_filter.mp hx).2)]
      exact Finset.sum_congr rfl hinner
    rw [hEq, hsplit, Finset.sum_mul,
      Finset.sum_congr rfl (fun ds _ =>
        chain_triple_fibre_card L hL st j base hbase (A.filter (fun T => targ T = S)) hAS ds),
      Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hScard
  calc (A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).card
          * Fintype.card OuterChallenge.DigestTriple
      = ∑ S in A.image targ,
          ((A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).filter
            (fun T => targ T = S)).card * Fintype.card OuterChallenge.DigestTriple := by
        rw [hfib1, Finset.sum_mul]
    _ ≤ ∑ S in A.image targ, m * (A.filter (fun T => targ T = S)).card :=
        Finset.sum_le_sum key
    _ = m * A.card := by rw [← Finset.mul_sum, ← hfib2]

/-- (1) **THE DIAGONAL BOUND AT ONE SCHEDULED DRAW, AS A MASS.**  The abstract
form of the adopted `OuterLaneTransport.stage_triple_target_mass_le`. -/
theorem chain_triple_target_mass_le (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j base : Nat)
    (hbase : base + 2 < Transcript.u64Limit)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : ChainStable L hL st j (tripleCounters base) A)
    (targ : OracleTable (boundedQueries L) → Finset OuterChallenge.DigestTriple)
    (hinv : ∀ T ∈ A, ∀ c ∈ tripleCounters base, ∀ b : Block,
      targ (reassign T (chainChallengeSel L hL st j c T) b) = targ T)
    (m : Nat) (hm : ∀ T ∈ A, (targ T).card ≤ m) :
    oracleProbability (boundedQueries L)
        (A.filter (fun T => chainTriple L hL st j base T ∈ targ T))
      ≤ (m : ℚ) / (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
  have hcard := chain_triple_target_card L hL st j base hbase A hA targ hinv m hm
  have hAle : A.card ≤ Fintype.card (OracleTable (boundedQueries L)) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_univ A
  have hnat : (A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).card
      * Fintype.card OuterChallenge.DigestTriple
      ≤ m * Fintype.card (OracleTable (boundedQueries L)) :=
    le_trans hcard (Nat.mul_le_mul_left m hAle)
  have hQ : ((A.filter (fun T => chainTriple L hL st j base T ∈ targ T)).card : ℚ)
      * (Fintype.card OuterChallenge.DigestTriple : ℚ)
      ≤ (m : ℚ) * (Fintype.card (OracleTable (boundedQueries L)) : ℚ) := by
    exact_mod_cast hnat
  have hD : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
    exact_mod_cast JointChallengeSpace.digest_triple_card_pos
  rw [oracleProbability, div_le_div_iff (oracle_card_cast_pos (boundedQueries L)) hD]
  exact hQ

/-! ## 2. THE TAU COLUMN OVER AN ABSTRACT CHAIN -/

/-- **STABILITY AT EVERY COUNTER.**  The conditioning events used at the derive
digest are stable at all of the `d` tau blocks at once, so the counter set is
quantified rather than fixed. -/
def ChainStableAll (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j : Nat)
    (A : Finset (OracleTable (boundedQueries L))) : Prop :=
  (∀ T ∈ A, ∀ c : Nat, ∀ b : Block,
      st j (reassign T (chainChallengeSel L hL st j c T) b) = st j T) ∧
  (∀ T ∈ A, ∀ c : Nat, ∀ b : Block, reassign T (chainChallengeSel L hL st j c T) b ∈ A)

theorem chain_stable_of_all (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j : Nat) (C : Finset Nat)
    (A : Finset (OracleTable (boundedQueries L))) (hA : ChainStableAll L hL st j A) :
    ChainStable L hL st j C A :=
  ⟨fun T hT c _ b => hA.1 T hT c b, fun T hT c _ b => hA.2 T hT c b⟩

/-- **THE TAU COLUMN THE CHAIN READS AT STAGE `j`**: coordinate `i` is the digest
triple at the counters `tauBase d i, +1, +2`.  The abstract form of the adopted
`ReducedFullTransport.tauRead`. -/
def chainTauRead (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (T : OracleTable (boundedQueries L)) : ChallengeUnionBound.TripleTuple d :=
  fun i => chainTriple L hL st j (tauBase d i.val) T

/-- The prescribed-prefix fibre of a conditioning event: the tables whose first
`n` tau coordinates take the prescribed values. -/
noncomputable def chainTauFibre (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : Nat → OuterChallenge.DigestTriple) :
    Nat → Finset (OracleTable (boundedQueries L))
  | 0 => A
  | n + 1 =>
      (chainTauFibre L hL st j d A t n).filter
        (fun T => chainTriple L hL st j (tauBase d n) T = t n)

theorem chain_tau_fibre_zero (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : Nat → OuterChallenge.DigestTriple) :
    chainTauFibre L hL st j d A t 0 = A := rfl

theorem chain_tau_fibre_succ (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : Nat → OuterChallenge.DigestTriple)
    (n : Nat) :
    chainTauFibre L hL st j d A t (n + 1)
      = (chainTauFibre L hL st j d A t n).filter
          (fun T => chainTriple L hL st j (tauBase d n) T = t n) := rfl

theorem mem_chain_tau_fibre (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : Nat → OuterChallenge.DigestTriple) :
    ∀ (n : Nat) (T : OracleTable (boundedQueries L)),
      T ∈ chainTauFibre L hL st j d A t n ↔
        (T ∈ A ∧ ∀ i, i < n → chainTriple L hL st j (tauBase d i) T = t i) := by
  intro n
  induction n with
  | zero =>
      intro T
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun h => h.1⟩
  | succ n2 ih =>
      intro T
      rw [chain_tau_fibre_succ, Finset.mem_filter, ih T]
      constructor
      · rintro ⟨⟨hT, hall⟩, hlast⟩
        refine ⟨hT, fun i hi => ?_⟩
        rcases Nat.lt_or_ge i n2 with h | h
        · exact hall i h
        · have hie : i = n2 := by omega
          rw [hie]
          exact hlast
      · rintro ⟨hT, hall⟩
        exact ⟨⟨hT, fun i hi => hall i (by omega)⟩, hall n2 (by omega)⟩

/-- (2) **THE FIBRE IS STABLE AT EVERY LATER TAU BLOCK.**  The prescriptions
already made are at counters `tauBase d i` with `i < m`, and the three counters of
block `m` are different queries at the same digest. -/
theorem chain_tau_fibre_stable (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (hA : ChainStableAll L hL st j A)
    (t : Nat → OuterChallenge.DigestTriple) (hdu : 12 + 6 * d < Transcript.u64Limit) :
    ∀ n m : Nat, n ≤ m → m < d →
      ChainStable L hL st j (tripleCounters (tauBase d m)) (chainTauFibre L hL st j d A t n) := by
  intro n
  induction n with
  | zero =>
      intro m _ _
      exact chain_stable_of_all L hL st j (tripleCounters (tauBase d m)) A hA
  | succ n2 ih =>
      intro m hnm hmd
      have hprev := ih m (by omega) hmd
      rw [chain_tau_fibre_succ]
      refine chain_stable_filter L hL st j (tripleCounters (tauBase d m))
        (chainTauFibre L hL st j d A t n2) hprev
        (fun T => chainTriple L hL st j (tauBase d n2) T = t n2) (fun T hT c hc b => ?_)
      show chainTriple L hL st j (tauBase d n2)
            (reassign T (chainChallengeSel L hL st j c T) b) = t n2
        ↔ chainTriple L hL st j (tauBase d n2) T = t n2
      rw [chain_triple_reassign_same L hL st j (tauBase d n2) c
        (tau_counter_mem_lt d m c hmd hc hdu) (tau_counter_lt d n2 (by omega) hdu)
        (tau_counters_disjoint d n2 m c (by omega) hc) T b (hprev.1 T hT c hc b)]

/-- (2) **THE JOINT FIBRE COUNT OVER THE WHOLE TAU COLUMN.**  `d` applications of
`chain_triple_fibre_card`, with the adopted `ReducedFullTransport.peel_pow` doing
the exponent bookkeeping over abstract naturals. -/
theorem chain_tau_fibre_card (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (hA : ChainStableAll L hL st j A)
    (t : Nat → OuterChallenge.DigestTriple) (hdu : 12 + 6 * d < Transcript.u64Limit) :
    ∀ n : Nat, n ≤ d →
      (chainTauFibre L hL st j d A t n).card * Fintype.card OuterChallenge.DigestTriple ^ n
        = A.card := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [chain_tau_fibre_zero, pow_zero, Nat.mul_one]
  | succ n2 ih =>
      intro hn
      have hstep : (chainTauFibre L hL st j d A t (n2 + 1)).card
            * Fintype.card OuterChallenge.DigestTriple
          = (chainTauFibre L hL st j d A t n2).card :=
        chain_triple_fibre_card L hL st j (tauBase d n2)
          (tau_counter_lt d n2 (by omega) hdu) (chainTauFibre L hL st j d A t n2)
          (chain_tau_fibre_stable L hL st j d A hA t hdu n2 n2 (le_refl n2) (by omega)) (t n2)
      exact (peel_pow _ _ _ n2 hstep).trans (ih (by omega))

theorem chain_tau_fibre_at_extend (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (t : ChallengeUnionBound.TripleTuple d)
    (T : OracleTable (boundedQueries L)) :
    T ∈ chainTauFibre L hL st j d A (tauExtend d t) d ↔
      (T ∈ A ∧ chainTauRead L hL st j d T = t) := by
  rw [mem_chain_tau_fibre]
  constructor
  · rintro ⟨hT, hall⟩
    refine ⟨hT, ?_⟩
    funext i
    show chainTriple L hL st j (tauBase d i.val) T = t i
    rw [hall i.val i.isLt, tau_extend_apply d t i.val i.isLt]
  · rintro ⟨hT, hread⟩
    refine ⟨hT, fun i hi => ?_⟩
    rw [tau_extend_apply d t i hi, ← hread]
    rfl

open Classical in
/-- (2) **THE TARGET COUNT OVER THE TAU COLUMN.**  For a set `S` of tau tuples --
fixed data, bound outside the law -- exactly `|S|` fibres are caught. -/
theorem chain_tau_target_card (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (hA : ChainStableAll L hL st j A)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (S : Finset (ChallengeUnionBound.TripleTuple d)) :
    ((A.filter (fun T => chainTauRead L hL st j d T ∈ S)).card)
        * Fintype.card OuterChallenge.DigestTriple ^ d = S.card * A.card := by
  have hfib : (A.filter (fun T => chainTauRead L hL st j d T ∈ S)).card
      = ∑ t in S, ((A.filter (fun T => chainTauRead L hL st j d T ∈ S)).filter
          (fun T => chainTauRead L hL st j d T = t)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => (Finset.mem_filter.mp hx).2)
  have key : ∀ t ∈ S,
      ((A.filter (fun T => chainTauRead L hL st j d T ∈ S)).filter
          (fun T => chainTauRead L hL st j d T = t)).card
        * Fintype.card OuterChallenge.DigestTriple ^ d = A.card := by
    intro t ht
    have hset : (A.filter (fun T => chainTauRead L hL st j d T ∈ S)).filter
          (fun T => chainTauRead L hL st j d T = t)
        = chainTauFibre L hL st j d A (tauExtend d t) d := by
      apply Finset.ext
      intro T
      rw [chain_tau_fibre_at_extend, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hT, -⟩, hEq⟩
        exact ⟨hT, hEq⟩
      · rintro ⟨hT, hEq⟩
        exact ⟨⟨hT, hEq ▸ ht⟩, hEq⟩
    rw [hset]
    exact chain_tau_fibre_card L hL st j d A hA (tauExtend d t) hdu d (le_refl d)
  rw [hfib, Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

open Classical in
/-- (2) **THE TARGET MASS OVER THE TAU COLUMN.**  The abstract form of the adopted
`ReducedFullTransport.tau_target_mass_le`. -/
theorem chain_tau_target_mass_le (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j d : Nat)
    (A : Finset (OracleTable (boundedQueries L))) (hA : ChainStableAll L hL st j A)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (S : Finset (ChallengeUnionBound.TripleTuple d)) :
    oracleProbability (boundedQueries L)
        (A.filter (fun T => chainTauRead L hL st j d T ∈ S))
      ≤ (S.card : ℚ) / (Fintype.card (ChallengeUnionBound.TripleTuple d) : ℚ) := by
  have hcard := chain_tau_target_card L hL st j d A hA hdu S
  have hAle : A.card ≤ Fintype.card (OracleTable (boundedQueries L)) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_univ _
  have hnat : (A.filter (fun T => chainTauRead L hL st j d T ∈ S)).card
      * Fintype.card OuterChallenge.DigestTriple ^ d
      ≤ S.card * Fintype.card (OracleTable (boundedQueries L)) := by
    rw [hcard]
    exact Nat.mul_le_mul_left _ hAle
  have hQ : ((A.filter (fun T => chainTauRead L hL st j d T ∈ S)).card : ℚ)
      * ((Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d)
      ≤ (S.card : ℚ) * (Fintype.card (OracleTable (boundedQueries L)) : ℚ) := by
    exact_mod_cast hnat
  have hD : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ d := by
    have h1 : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
      exact_mod_cast JointChallengeSpace.digest_triple_card_pos
    exact pow_pos h1 d
  rw [triple_tuple_card_as_triples, Nat.cast_pow, oracleProbability,
    div_le_div_iff (oracle_card_cast_pos (boundedQueries L)) hD]
  exact hQ

/-! ## 3. THE GRINDING CHAIN'S CHALLENGE CELLS -/

/-- **A GRINDING PROVER THAT READS THE CHALLENGE ORACLE AT ITS OWN PAST STAGE
DIGESTS.**  The adopted `GrindingQueryBound.GrindingStrategy` hands the prover the
WHOLE challenge oracle `ch : Digest -> Nat -> Block`, at every digest whatsoever;
this predicate says the stage-`k` probe and the stage-`k` absorb depend on `ch`
only through its values at the stage digests `h 0, …, h k` -- exactly what the
adopted `StrategyChainBound.Strategy` is handed, and no more.  Probes are NOT
restricted: the prover still issues `q` frame queries of its own at every stage,
at any digest, with any tag and any payload, and its absorb is still a function of
their answers.

WHAT THIS EXCLUDES, AND WHY IT HAS TO BE EXCLUDED, is section 10: a prover that
evaluates `ch` at the digest of a PROBE ANSWER has read the challenges of a digest
its chain has not reached yet, and if it then absorbs that probed payload it has
chosen the round's message AFTER seeing the round's challenges.  That is the
grinding attack on Fiat--Shamir challenges, and no conditioning event of the
adopted machinery charges it -- see HONESTY (ii) and (iii). -/
def ChallengeRestricted (g : GrindingStrategy) : Prop :=
  (∀ (k i : Nat) (h : Nat → Transcript.Digest)
      (ch1 ch2 : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block),
      (∀ j, j ≤ k → ch1 (h j) = ch2 (h j)) →
        g.probe k i h ch1 pa = g.probe k i h ch2 pa) ∧
  (∀ (k : Nat) (h : Nat → Transcript.Digest)
      (ch1 ch2 : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block),
      (∀ j, j ≤ k → ch1 (h j) = ch2 (h j)) → g.absorb k h ch1 pa = g.absorb k h ch2 pa)

/-- (3) **EVERY ADOPTED TRANSCRIPT-RESTRICTED PROVER, LIFTED, IS
CHALLENGE-RESTRICTED.**  The adopted `GrindingQueryBound.grindingOfStrategy` reads
the challenge oracle only at `h (min j k)`, a stage digest at or below its own
stage, so the hypothesis of sections 5 to 8 holds for it -- for EVERY adopted
`StrategyChainBound.Strategy`, with no side condition.  Together with
`probe_grinder_challenge_restricted` and the adopted
`GrindingQueryBound.probe_grinder_is_not_transcript_restricted` (a
challenge-restricted grinder that is NOT the lift of any adopted strategy), this
is what justifies calling the class of provers covered below LARGER than the
adopted `RawBlockLanes` one: containment in one direction, a witness outside in
the other.

WHAT IT IS NOT.  It is NOT a proof that the bound below SUBSUMES the adopted
`RawBlockLanes` theorem.  Subsumption would additionally need
`grindingFullBadEvent` at `q = 0` and `grindingOfStrategy strat` to be the adopted
`RawBlockLanes.rawFullBadEvent` at `strat`, as sets; that identity is NOT proved
anywhere in this tree, and nothing below asserts it. -/
theorem grinding_of_strategy_challenge_restricted (strat : StrategyChainBound.Strategy) :
    ChallengeRestricted (grindingOfStrategy strat) := by
  refine ⟨fun _ _ _ _ _ _ _ => rfl, fun k h ch1 ch2 _ hch => ?_⟩
  show strat k (fun j => h (min j k)) (fun j c => ch1 (h (min j k)) c)
    = strat k (fun j => h (min j k)) (fun j c => ch2 (h (min j k)) c)
  congr 1
  funext j c
  exact congrFun (hch (min j k) (Nat.min_le_right j k)) c

/-- (3) A challenge-restricted strategy's query at position `m` is a function of
the challenge answers at the stage digests up to `m`'s own stage. -/
theorem grind_query_challenge_congr (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (hcr : ChallengeRestricted g) (a : Nat → Block)
    (ch1 ch2 : Transcript.Digest → Nat → Block) (m : Nat)
    (hch : ∀ i, i ≤ m / (q + 1) → ch1 (stateOf e0 q a i) = ch2 (stateOf e0 q a i)) :
    grindQuery e0 q g a ch1 m = grindQuery e0 q g a ch2 m := by
  unfold grindQuery
  split
  · exact hcr.1 _ _ _ _ _ _ hch
  · exact congrArg (fun z => (stateOf e0 q a (m / (q + 1)), z)) (hcr.2 _ _ _ _ _ hch)

/-- (3) The positive form of the adopted `GrindingQueryBound.grindingNoClash`. -/
theorem mem_grind_no_clash (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ grindingNoClash L hL e0 q g hb n ↔
      ∀ r s : Nat, r < s → s ≤ n →
        grindState L hL e0 q g hb r T ≠ grindState L hL e0 q g hb s T := by
  constructor
  · intro hT r s hrs hsn heq
    have hc : T ∈ (grindingNoClash L hL e0 q g hb n)ᶜ :=
      (mem_grinding_clash_event L hL e0 q g hb n T).mpr ⟨r, s, hrs, hsn, heq⟩
    exact absurd hT (Finset.mem_compl.mp hc)
  · intro h
    by_contra hT
    have hc : T ∈ grindingClashEvent L hL e0 q g hb n := Finset.mem_compl.mpr hT
    obtain ⟨r, s, hrs, hsn, heq⟩ := (mem_grinding_clash_event L hL e0 q g hb n T).mp hc
    exact h r s hrs hsn heq

/-- (3) The no-clash events are NESTED. -/
theorem grind_no_clash_mono (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (j n : Nat) (hjn : j ≤ n) :
    grindingNoClash L hL e0 q g hb n ⊆ grindingNoClash L hL e0 q g hb j := by
  intro T hT
  rw [mem_grind_no_clash] at hT
  rw [mem_grind_no_clash]
  exact fun r s hrs hsj => hT r s hrs (le_trans hsj hjn)

/-- (3) Overwriting the table at a query that is not a given challenge input
leaves that challenge answer alone. -/
theorem challenge_at_reassign_ne (L : Nat) (hL : 64 ≤ L) (T : OracleTable (boundedQueries L))
    (qq : { x : Transcript.Bytes // x ∈ boundedQueries L }) (b : Block)
    (e : Transcript.Digest) (c : Nat)
    (hne : qq.val ≠ Transcript.challengeInput e c) :
    StrategyChainBound.challengeAt L hL (reassign T qq b) e c
      = StrategyChainBound.challengeAt L hL T e c := by
  show (reassign T qq b) ⟨Transcript.challengeInput e c, bounded_queries_challenge L hL e c⟩
    = T ⟨Transcript.challengeInput e c, bounded_queries_challenge L hL e c⟩
  exact reassign_off T qq _ b (fun h => hne (congrArg Subtype.val h).symm)

/-- (3) **THE CHALLENGE ANSWERS AT EVERY EARLIER STAGE DIGEST ARE LEFT ALONE.**
On the chain's no-clash event a stage `i < j` carries a digest different from
stage `j`'s, and a different digest gives a different challenge input. -/
theorem grind_challenges_reassign_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (j c i : Nat) (hij : i < j)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ grindingNoClash L hL e0 q g hb j)
    (b : Block) :
    challengesOf L hL
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
        (grindState L hL e0 q g hb i T)
      = challengesOf L hL T (grindState L hL e0 q g hb i T) := by
  funext c2
  refine challenge_at_reassign_ne L hL T _ b _ c2 ?_
  intro hv
  exact (mem_grind_no_clash L hL e0 q g hb j T).mp hT i j hij (le_refl j)
    (StrategyChainBound.challenge_input_digest_eq _ _ _ _ hv.symm)

/-- (3) **THE RUN UP TO THE STAGE-`j` ABSORB DOES NOT LOOK AT THE STAGE-`j`
CHALLENGE ANSWERS.**  Every position before stage `j` is a probe or an absorb of a
stage `k < j`; its frame is not a challenge input at all, and -- this is where
`ChallengeRestricted` is used -- its challenge reads are at the stage digests
`0, …, k`, all of which the no-clash event separates from stage `j`'s. -/
theorem grind_run_ans_challenge_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (j c : Nat) (T : OracleTable (boundedQueries L))
    (hT : T ∈ grindingNoClash L hL e0 q g hb j) (b : Block) :
    ∀ m : Nat, m ≤ j * (q + 1) →
      runAns L hL e0 q g hb m
          (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
        = runAns L hL e0 q g hb m T := by
  intro m
  induction m with
  | zero => intro _; funext m2; rfl
  | succ m2 ih =>
      intro hm
      have hprev := ih (by omega)
      have hmlt : m2 < j * (q + 1) := by omega
      have hkj : m2 / (q + 1) < j := Nat.div_lt_of_lt_mul (by
        rw [Nat.mul_comm] at hmlt
        exact hmlt)
      have hkle : m2 / (q + 1) * (q + 1) ≤ m2 := Nat.div_mul_le_self m2 (q + 1)
      have hstate : ∀ i, i ≤ m2 / (q + 1) →
          stateOf e0 q (runAns L hL e0 q g hb m2 T) i = grindState L hL e0 q g hb i T := by
        intro i hi
        refine state_of_run_ans_le L hL e0 q g hb m2 i (fun i2 hi2 => ?_) T
        have hi2le : i2 + 1 ≤ m2 / (q + 1) := by omega
        have hmul : (i2 + 1) * (q + 1) ≤ m2 / (q + 1) * (q + 1) :=
          Nat.mul_le_mul_right _ hi2le
        have hexp : (i2 + 1) * (q + 1) = i2 * (q + 1) + (q + 1) := by ring
        rw [slotPos]
        omega
      have hch : ∀ i, i ≤ m2 / (q + 1) →
          challengesOf L hL
              (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
              (stateOf e0 q (runAns L hL e0 q g hb m2 T) i)
            = challengesOf L hL T (stateOf e0 q (runAns L hL e0 q g hb m2 T) i) := by
        intro i hi
        rw [hstate i hi]
        exact grind_challenges_reassign_lower L hL e0 q g hb j c i (by omega) T hT b
      have hsel : grindSelSeq L hL e0 q g hb m2
            (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
          = grindSelSeq L hL e0 q g hb m2 T := by
        apply Subtype.ext
        show grindBytes e0 q g (runAns L hL e0 q g hb m2
              (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b))
            (challengesOf L hL
              (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)) m2
          = grindBytes e0 q g (runAns L hL e0 q g hb m2 T) (challengesOf L hL T) m2
        rw [hprev]
        unfold grindBytes
        rw [grind_query_challenge_congr e0 q g hcr (runAns L hL e0 q g hb m2 T) _ _ m2 hch]
      funext m3
      rw [run_ans_succ, run_ans_succ, hsel, hprev]
      by_cases h3 : m3 = m2
      · rw [if_pos h3, if_pos h3]
        refine reassign_off T _ _ b ?_
        intro hEq
        exact frame_ne_challenge_input _ _ _ _ _ (congrArg Subtype.val hEq)
      · rw [if_neg h3, if_neg h3]

/-- (3) **THE STAGE DIGESTS UP TO STAGE `j` ARE NOT MOVED BY THE STAGE-`j`
CHALLENGE ANSWERS.**  The grinding analogue of the adopted
`StrategyChainBound.strategy_state_challenge_stable`, which is the precise sense
in which round `j`'s message is fixed BEFORE round `j`'s challenges are
squeezed. -/
theorem grind_state_challenge_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (j c : Nat) (T : OracleTable (boundedQueries L))
    (hT : T ∈ grindingNoClash L hL e0 q g hb j) (b : Block) :
    ∀ i : Nat, i ≤ j →
      grindState L hL e0 q g hb i
          (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
        = grindState L hL e0 q g hb i T := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i2 =>
      have hmlt : slotPos q i2 q < j * (q + 1) := by
        have h1 : (i2 + 1) * (q + 1) ≤ j * (q + 1) := Nat.mul_le_mul_right _ hi
        have hexp : (i2 + 1) * (q + 1) = i2 * (q + 1) + (q + 1) := by ring
        rw [slotPos]
        omega
      have hsucc := grind_run_ans_challenge_stable L hL e0 q g hb hcr j c T hT b
        (slotPos q i2 q + 1) (by omega)
      have hval := congrFun hsucc (slotPos q i2 q)
      rw [run_ans_succ, run_ans_succ, if_pos rfl, if_pos rfl] at hval
      show blockDigest (_) = blockDigest (_)
      exact congrArg blockDigest hval

/-- (3) **THE CHAIN'S NO-CLASH EVENT IS STABLE AT EVERY STAGE-`j` COUNTER.**  This
is the conditioning event of every bound below. -/
theorem grind_no_clash_chain_stable_all (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (j : Nat) :
    ChainStableAll L hL (grindState L hL e0 q g hb) j (grindingNoClash L hL e0 q g hb j) := by
  refine ⟨fun T hT c b => grind_state_challenge_stable L hL e0 q g hb hcr j c T hT b j
      (le_refl j), fun T hT c b => ?_⟩
  rw [mem_grind_no_clash]
  intro r s hrs hsj
  rw [grind_state_challenge_stable L hL e0 q g hb hcr j c T hT b r (by omega),
    grind_state_challenge_stable L hL e0 q g hb hcr j c T hT b s hsj]
  exact (mem_grind_no_clash L hL e0 q g hb j T).mp hT r s hrs hsj

/-! ## 4. THE RAW CHALLENGE VIEW OF A GRINDING RUN -/

/-- **THE RAW 32-BYTE ANSWER AT EVERY STAGE AND EVERY COUNTER OF A GRINDING
RUN.**  The adopted `RawBlockLanes.tableView`, over the grinding chain's stage
digests instead of a transcript-restricted strategy's.  NOTHING IS REDUCED: no
`OuterChallenge.reduceTriple`, no restriction to counters below `6` or to round
stages. -/
def grindTableView (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (T : OracleTable (boundedQueries L)) :
    Nat → Nat → Block :=
  fun i cnt => T (chainChallengeSel L hL (grindState L hL e0 q g hb) i cnt T)

/-- (4) An earlier stage's challenge query is a different query from a stage-`j`
one, on the chain's no-clash event. -/
theorem grind_challenge_sel_ne_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (j c i cnt : Nat) (hij : i < j)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ grindingNoClash L hL e0 q g hb j) :
    chainChallengeSel L hL (grindState L hL e0 q g hb) i cnt T
      ≠ chainChallengeSel L hL (grindState L hL e0 q g hb) j c T := by
  intro hEq
  exact (mem_grind_no_clash L hL e0 q g hb j T).mp hT i j hij (le_refl j)
    (StrategyChainBound.challenge_input_digest_eq _ _ _ _ (congrArg Subtype.val hEq))

/-- (4) **OVERWRITING A STAGE-`j` CHALLENGE ANSWER LEAVES THE WHOLE RAW VIEW OF
EVERY EARLIER STAGE ALONE** -- every counter of it.  The grinding analogue of the
adopted `RawBlockLanes.table_view_reassign_lower`. -/
theorem grind_table_view_reassign_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (j c : Nat) (T : OracleTable (boundedQueries L))
    (hT : T ∈ grindingNoClash L hL e0 q g hb j) (b : Block) (i : Nat) (hi : i < j) :
    grindTableView L hL e0 q g hb
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b) i
      = grindTableView L hL e0 q g hb T i := by
  funext cnt
  have hst : chainChallengeSel L hL (grindState L hL e0 q g hb) i cnt
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
      = chainChallengeSel L hL (grindState L hL e0 q g hb) i cnt T := by
    apply Subtype.ext
    show Transcript.challengeInput (grindState L hL e0 q g hb i
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)) cnt
      = Transcript.challengeInput (grindState L hL e0 q g hb i T) cnt
    rw [grind_state_challenge_stable L hL e0 q g hb hcr j c T hT b i (by omega)]
  show (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
      (chainChallengeSel L hL (grindState L hL e0 q g hb) i cnt
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b))
    = T (chainChallengeSel L hL (grindState L hL e0 q g hb) i cnt T)
  rw [hst]
  exact reassign_off T _ _ b (grind_challenge_sel_ne_lower L hL e0 q g hb j c i cnt hi T hT)

/-- (4) The same, for a whole earlier digest triple. -/
theorem grind_triple_reassign_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (j c i base : Nat) (hi : i < j) (T : OracleTable (boundedQueries L))
    (hT : T ∈ grindingNoClash L hL e0 q g hb j) (b : Block) :
    chainTriple L hL (grindState L hL e0 q g hb) i base
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
      = chainTriple L hL (grindState L hL e0 q g hb) i base T := by
  have hview := grind_table_view_reassign_lower L hL e0 q g hb hcr j c T hT b i hi
  have h0 : (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
        (chainChallengeSel L hL (grindState L hL e0 q g hb) i base
          (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b))
      = T (chainChallengeSel L hL (grindState L hL e0 q g hb) i base T) := congrFun hview base
  have h1 : (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
        (chainChallengeSel L hL (grindState L hL e0 q g hb) i (base + 1)
          (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b))
      = T (chainChallengeSel L hL (grindState L hL e0 q g hb) i (base + 1) T) :=
    congrFun hview (base + 1)
  have h2 : (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b)
        (chainChallengeSel L hL (grindState L hL e0 q g hb) i (base + 2)
          (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b))
      = T (chainChallengeSel L hL (grindState L hL e0 q g hb) i (base + 2) T) :=
    congrFun hview (base + 2)
  show ((_, _, _) : OuterChallenge.DigestTriple) = (_, _, _)
  rw [h0, h1, h2]

/-! ## 5. A LANE DRIVEN BY A GRINDING RUN, AT THE GRINDER'S OWN DOMAIN -/

/-- **THE RUN'S OWN ANSWER LIST, AS A FUNCTION OF THE TABLE.**  `grindRunView … T m`
is the block the oracle returned at position `m` of the single interleaved
probe/absorb sequence: the prover's PROBE ANSWERS, and its absorb answers, exactly
as it saw them. -/
def grindRunView (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (T : OracleTable (boundedQueries L)) :
    Nat → Block :=
  fun m => T (grindSelSeq L hL e0 q g hb m T)

/-- (5) **THE RUN'S ANSWERS BEFORE STAGE `j` ARE UNMOVED BY A STAGE-`j` CHALLENGE
ANSWER.**  Every position of the sequence asks a FRAME, never a challenge input,
and `grind_run_ans_challenge_stable` already carries the causal induction over all
`j (q + 1)` of them; this reads that induction off at one position. -/
theorem grind_run_view_reassign_lower (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (j c : Nat) (T : OracleTable (boundedQueries L))
    (hT : T ∈ grindingNoClash L hL e0 q g hb j) (b : Block) (m : Nat) (hm : m < j * (q + 1)) :
    grindRunView L hL e0 q g hb
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b) m
      = grindRunView L hL e0 q g hb T m := by
  have h := grind_run_ans_challenge_stable L hL e0 q g hb hcr j c T hT b (m + 1) (by omega)
  have hv := congrFun h m
  rw [run_ans_succ, run_ans_succ, if_pos rfl, if_pos rfl] at hv
  exact hv

/-- **A LANE WHOSE ROUND MESSAGE MAY READ THE PROVER'S OWN PROBE ANSWERS.**  The
adopted `RawBlockLanes.RawLane` has message domain
`Nat -> (Nat -> Nat -> Block) -> List Element`: the raw CHALLENGE VIEW, and
nothing else.  A grinding prover's round message is a function of its PROBE
ANSWERS too, and a function of probe answers is not of that type, so no `RawLane`
can carry one.  `GrindLane` widens the domain by the run's own answer list:

  `message : Nat -> (Nat -> Block) -> (Nat -> Nat -> Block) -> List Element`

the round index, the answers the run has collected at every position of the
interleaved sequence, and the raw challenge view.  `claim` and `truthClaim` are
the initial running claims of the adopted `ConditionalSoundness.claimedRun` /
`truthRun` recursions, exactly as for the adopted `RawLane`.

THE DIAGONAL STEP SURVIVES THE WIDENING, and that is the point of it: a probe
answer is the table's value at a FRAME cell, and `grind_run_view_reassign_lower`
shows every such cell before the round's stage is unmoved when the round's own
CHALLENGE cells are reassigned.  So a message that reads the prover's probe
answers still cannot read the challenges it is about to be tested against. -/
structure GrindLane where
  message : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element
  truth : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element
  claim : Element
  truthClaim : Element

/-- **THE PROTOCOL'S CAUSALITY, WIDENED.**  Round `r`'s message reads the challenge
view only up to stage `22 + 5 r` -- the adopted `RawBlockLanes.RawCausal` clause,
verbatim -- and reads the run's answers only at the `(22 + 5 r + 1) (q + 1)`
positions of stages `≤ 22 + 5 r`.  That is a cut STRICTLY BELOW the round's
challenge stage `roundStage r = 22 + 5 r + 5`: it does not model a prover that
interleaves probes between the round's five frames and picks later frames'
payloads after them.  A looser cut at `(roundStage r) (q + 1)` (every frame cell
strictly before the round's challenge digest) would also be sound for the
diagonal step, since `grind_run_view_reassign_lower` only needs `22 + 5 r < j`. -/
def GrindCausal (q : Nat)
    (f : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) : Prop :=
  ∀ (r : Nat) (a1 a2 : Nat → Block) (ch1 ch2 : Nat → Nat → Block),
    (∀ m, m < (22 + 5 * r + 1) * (q + 1) → a1 m = a2 m) →
    (∀ j, j ≤ 22 + 5 * r → ch1 j = ch2 j) → f r a1 ch1 = f r a2 ch2

/-- Both halves of a grind lane obey the widened causality. -/
def GrindLaneCausal (q : Nat) (lane : GrindLane) : Prop :=
  GrindCausal q lane.message ∧ GrindCausal q lane.truth

/-- THE ADOPTED DEGREE BOUND, uniform over every run view and every challenge view
the prover may see. -/
def GrindLaneBounded (lane : GrindLane) (b : Nat) : Prop :=
  ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block),
    (lane.message r a ch).length ≤ b ∧ (lane.truth r a ch).length ≤ b

/-- **EVERY ADOPTED RAW LANE IS A GRIND LANE**, one that reads the run's answers
not at all.  So the widened headline of section 8 covers everything the narrow
one would have. -/
def grindLaneOfRawLane (lane : RawLane) : GrindLane where
  message := fun r _ ch => lane.message r ch
  truth := fun r _ ch => lane.truth r ch
  claim := lane.claim
  truthClaim := lane.truthClaim

theorem grind_lane_of_raw_lane_causal (q : Nat) (lane : RawLane) (h : RawLaneCausal lane) :
    GrindLaneCausal q (grindLaneOfRawLane lane) :=
  ⟨fun r _ _ ch1 ch2 _ hch => h.1 r ch1 ch2 hch,
   fun r _ _ ch1 ch2 _ hch => h.2 r ch1 ch2 hch⟩

theorem grind_lane_of_raw_lane_bounded (lane : RawLane) (b : Nat)
    (h : RawLaneBounded lane b) : GrindLaneBounded (grindLaneOfRawLane lane) b :=
  fun r _ ch => h r ch

/-- **A LANE THAT ACTUALLY READS THE PROVER'S PROBE ANSWERS.**  Its round-`r`
message is selected by the answer to PROBE `0` OF STAGE `22 + 5 r` -- a cell of
the run that the adopted `RawLane` domain cannot mention at all -- while its
claims repeat the adopted `RawBlockLanes.separatedRawLane` data.  It is causal and
bounded, so the bound of section 8 applies to it; this is the widening, exhibited
rather than asserted. -/
def probeReadingLane (q : Nat) : GrindLane where
  message := fun r a _ =>
    if a (slotPos q (22 + 5 * r) 0) = zeroDigestBlock then [1] else [1, 1]
  truth := fun _ _ _ => []
  claim := 1
  truthClaim := 0

theorem probe_reading_lane_causal (q : Nat) : GrindLaneCausal q (probeReadingLane q) := by
  classical
  refine ⟨fun r a1 a2 _ _ ha _ => ?_, fun _ _ _ _ _ _ _ => rfl⟩
  have hexp : (22 + 5 * r + 1) * (q + 1) = (22 + 5 * r) * (q + 1) + (q + 1) := by ring
  have hpos : slotPos q (22 + 5 * r) 0 < (22 + 5 * r + 1) * (q + 1) := by
    rw [slotPos]
    omega
  show (if a1 (slotPos q (22 + 5 * r) 0) = zeroDigestBlock then [(1 : Element)] else [1, 1])
    = (if a2 (slotPos q (22 + 5 * r) 0) = zeroDigestBlock then [(1 : Element)] else [1, 1])
  rw [ha (slotPos q (22 + 5 * r) 0) hpos]

theorem probe_reading_lane_bounded (q : Nat) : GrindLaneBounded (probeReadingLane q) 5 := by
  classical
  refine fun r a _ => ⟨?_, Nat.zero_le _⟩
  show (if a (slotPos q (22 + 5 * r) 0) = zeroDigestBlock then [(1 : Element)]
    else [1, 1]).length ≤ 5
  by_cases h : a (slotPos q (22 + 5 * r) 0) = zeroDigestBlock
  · rw [if_pos h]
    decide
  · rw [if_neg h]
    decide

/-- (5) **AND IT GENUINELY READS THEM.**  Two runs that differ only in the answer
to probe `0` of stage `22` give that lane DIFFERENT round-`0` messages, at the
same challenge view.  The adopted `RawBlockLanes.RawLane` cannot express this
dependence, which is exactly why the domain had to be widened. -/
theorem probe_reading_lane_reads_probes (q : Nat) :
    ∃ (a1 a2 : Nat → Block) (ch : Nat → Nat → Block),
      (probeReadingLane q).message 0 a1 ch ≠ (probeReadingLane q).message 0 a2 ch := by
  classical
  have hne : oneDigestBlock ≠ zeroDigestBlock := by
    intro h
    have hv : Transcript.le 32 1 = Transcript.le 32 0 := congrArg Subtype.val h
    have h10 : (1 : Nat) = 0 :=
      Transcript.le_injective_bounded 32 1 0 (small_lt_byte_power 1 (by norm_num))
        (small_lt_byte_power 0 (by norm_num)) hv
    omega
  refine ⟨fun _ => zeroDigestBlock, fun _ => oneDigestBlock, fun _ _ => zeroDigestBlock, ?_⟩
  show (if zeroDigestBlock = zeroDigestBlock then [(1 : Element)] else [1, 1])
    ≠ (if oneDigestBlock = zeroDigestBlock then [(1 : Element)] else [1, 1])
  rw [if_pos rfl, if_neg hne]
  exact fun h => List.noConfusion h (fun _ h2 => List.noConfusion h2)

/-- (5) **AND THE CELL IT READS IS THE CELL THE GRINDER'S OWN ABSORB READS.**  The
adopted `GrindingQueryBound.probeGrinder`'s stage-`k` absorb payload is the
thirty-two bytes of the run's answer at position `slotPos q k 0` -- PROBE `0` OF
STAGE `k` -- and `probeReadingLane q`'s round-`r` message is selected by that same
answer at `k = 22 + 5 r`.  So the widened domain reaches the data a grinder's own
round message is built from; the adopted `RawLane` domain cannot mention it.  What
is still NOT built here is a `grindLaneOfGrinder` carrying that payload as a
`List Element`: see HONESTY (v). -/
theorem probe_grinder_absorb_is_run_cell (q k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (a : Nat → Block) :
    probeGrinder.absorb k h ch (probeAnsOf q a) = (0, (a (slotPos q k 0)).val) := rfl

/-- **THE RUNNING CLAIMS BEFORE ROUND `r`, AT ONE TABLE, ALONG A GRINDING
CHAIN.**  The adopted `RawBlockLanes.rawClaims`, with the grinding chain's stage
digests supplying the challenge triples and the raw view, and with the lane's
message handed the RUN'S OWN ANSWERS as well. -/
def grindRawClaims (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) : Nat → Element × Element
  | 0 => (lane.claim, lane.truthClaim)
  | r + 1 =>
      (OuterRound.evaluate (grindRawClaims L hL e0 q g hb lane base T r).1
          (lane.message r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T))
          (OuterChallenge.reduceTriple (chainTriple L hL (grindState L hL e0 q g hb)
            (roundStage r) base T)),
       OuterRound.evaluate (grindRawClaims L hL e0 q g hb lane base T r).2
          (lane.truth r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T))
          (OuterChallenge.reduceTriple (chainTriple L hL (grindState L hL e0 q g hb)
            (roundStage r) base T)))

theorem grind_raw_claims_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane) (base : Nat)
    (T : OracleTable (boundedQueries L)) (r : Nat) :
    grindRawClaims L hL e0 q g hb lane base T (r + 1)
      = (OuterRound.evaluate (grindRawClaims L hL e0 q g hb lane base T r).1
            (lane.message r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T))
            (OuterChallenge.reduceTriple (chainTriple L hL (grindState L hL e0 q g hb)
              (roundStage r) base T)),
         OuterRound.evaluate (grindRawClaims L hL e0 q g hb lane base T r).2
            (lane.truth r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T))
            (OuterChallenge.reduceTriple (chainTriple L hL (grindState L hL e0 q g hb)
              (roundStage r) base T))) := rfl

/-- **ROUND `r`'s RAW BAD SET ALONG A GRINDING CHAIN**, the adopted
`ConditionalSoundness.roundBadSet` at the running claims and at the message the
lane chose after seeing the grinding run's own answers and its raw challenge
view. -/
noncomputable def grindRawBadSet (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane) (base r : Nat)
    (T : OracleTable (boundedQueries L)) : Finset Element :=
  ConditionalSoundness.roundBadSet (grindRawClaims L hL e0 q g hb lane base T r).1
    (grindRawClaims L hL e0 q g hb lane base T r).2
    ⟨lane.message r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T),
     lane.truth r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T), 0⟩

/-- **AND ON THE DIGEST-TRIPLE ALPHABET**, through the adopted
`OuterChallenge.tupleEvent` pullback along `reduceTriple`. -/
noncomputable def grindRawTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane) (base r : Nat)
    (T : OracleTable (boundedQueries L)) : Finset OuterChallenge.DigestTriple :=
  OuterChallenge.tupleEvent (grindRawBadSet L hL e0 q g hb lane base r T)

/-- (5) **THE ADOPTED PER-ROUND CARDINALITY BOUND, REUSED VERBATIM.**  No
cardinality is evaluated. -/
theorem grind_raw_target_card_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane) (bd : Nat)
    (hbd : GrindLaneBounded lane bd) (base r : Nat) (T : OracleTable (boundedQueries L)) :
    (grindRawTarget L hL e0 q g hb lane base r T).card
      ≤ bd * OuterChallenge.fiberCeiling ^ 3 :=
  ConditionalSoundness.round_bad_triples_card _ _ _ bd
    (hbd r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T)).1
    (hbd r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T)).2

/-- (5) **A GRIND-CAUSAL FUNCTION DOES NOT SEE THE STAGE-`j` CHALLENGE ANSWERS**,
for any `j` strictly above `22 + 5 r` -- NOT EVEN THROUGH ITS PROBE-ANSWER
ARGUMENT.  The challenge half is `grind_table_view_reassign_lower`; the run half
is `grind_run_view_reassign_lower`, and it is what the widened domain costs. -/
theorem grind_raw_causal_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (f : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (hf : GrindCausal q f) (r j c : Nat) (hj : 22 + 5 * r < j) (T : OracleTable (boundedQueries L))
    (hT : T ∈ grindingNoClash L hL e0 q g hb j) (b : Block) :
    f r (grindRunView L hL e0 q g hb
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b))
      (grindTableView L hL e0 q g hb
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b))
      = f r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T) := by
  have hjm : (22 + 5 * r + 1) * (q + 1) ≤ j * (q + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  exact hf r _ _ _ _
    (fun m hm => grind_run_view_reassign_lower L hL e0 q g hb hcr j c T hT b m (by omega))
    (fun i hi => grind_table_view_reassign_lower L hL e0 q g hb hcr j c T hT b i (by omega))

/-- (5) **THE RAW STATE BEFORE ROUND `r` IS A FUNCTION OF STRICTLY EARLIER STAGES
ONLY.**  The grinding analogue of the adopted
`RawBlockLanes.raw_outer_state_reassign`. -/
theorem grind_raw_state_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (lane : GrindLane) (hcau : GrindLaneCausal q lane) (base j c : Nat)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ grindingNoClash L hL e0 q g hb j)
    (b : Block) :
    ∀ rr : Nat, (∀ i, i < rr → roundStage i < j) →
      grindRawClaims L hL e0 q g hb lane base
          (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) j c T) b) rr
        = grindRawClaims L hL e0 q g hb lane base T rr := by
  intro rr
  induction rr with
  | zero => intro _; rfl
  | succ r2 ih =>
      intro hlt
      have hprev := ih (fun i hi => hlt i (by omega))
      have hr2 : roundStage r2 < j := hlt r2 (by omega)
      have hr2b : 22 + 5 * r2 < j := by rw [roundStage] at hr2; omega
      have hmsg := grind_raw_causal_reassign L hL e0 q g hb hcr lane.message hcau.1 r2 j c
        hr2b T hT b
      have htr := grind_raw_causal_reassign L hL e0 q g hb hcr lane.truth hcau.2 r2 j c
        hr2b T hT b
      have htrip := grind_triple_reassign_lower L hL e0 q g hb hcr j c (roundStage r2) base
        hr2 T hT b
      rw [grind_raw_claims_succ, grind_raw_claims_succ, hprev, hmsg, htr, htrip]

/-- (5) **ROUND `r`'s RAW BAD SET IS UNMOVED BY EVERY ONE OF ROUND `r`'s OWN
CHALLENGE ANSWERS.**  Not only by the three counters of its own lane: by ANY
counter at the round's stage.  This is the diagonal hypothesis of section 1, and
for a grinding prover it is discharged from `ChallengeRestricted` and the chain's
no-clash event -- see section 10 for what happens without the former. -/
theorem grind_raw_target_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (lane : GrindLane) (hcau : GrindLaneCausal q lane) (base r c : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ grindingNoClash L hL e0 q g hb (roundStage r)) (b : Block) :
    grindRawTarget L hL e0 q g hb lane base r
        (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) (roundStage r) c T) b)
      = grindRawTarget L hL e0 q g hb lane base r T := by
  have hrb : 22 + 5 * r < roundStage r := by rw [roundStage]; omega
  have hmsg := grind_raw_causal_reassign L hL e0 q g hb hcr lane.message hcau.1 r
    (roundStage r) c hrb T hT b
  have htr := grind_raw_causal_reassign L hL e0 q g hb hcr lane.truth hcau.2 r
    (roundStage r) c hrb T hT b
  have hst := grind_raw_state_reassign L hL e0 q g hb hcr lane hcau base (roundStage r) c T hT b
    r (fun i hi => round_stage_lt i r hi)
  rw [grindRawTarget, grindRawTarget, grindRawBadSet, grindRawBadSet, hst, hmsg, htr]

/-- (5) **ROUND `r`'s RAW MASS, AT EITHER LANE, FOR A GRINDING PROVER.**
Conditioned on the grinding chain's no-clash event up to round `r`'s own stage,
the lane's own challenge triple of round `r` lands in the bad set ITS OWN RAW
HISTORY has chosen with mass at most `bd * ceil ^ 3 / |DigestTriple|`.  Section
1's diagonal step at the grinding chain. -/
theorem grind_raw_round_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (lane : GrindLane) (hcau : GrindLaneCausal q lane) (bd : Nat) (hbd : GrindLaneBounded lane bd)
    (base : Nat) (hbase : base + 2 < Transcript.u64Limit) (r : Nat) :
    oracleProbability (boundedQueries L)
        ((grindingNoClash L hL e0 q g hb (roundStage r)).filter
          (fun T => chainTriple L hL (grindState L hL e0 q g hb) (roundStage r) base T
            ∈ grindRawTarget L hL e0 q g hb lane base r T))
      ≤ ((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  chain_triple_target_mass_le L hL (grindState L hL e0 q g hb) (roundStage r) base hbase
    (grindingNoClash L hL e0 q g hb (roundStage r))
    (chain_stable_of_all L hL (grindState L hL e0 q g hb) (roundStage r) (tripleCounters base)
      (grindingNoClash L hL e0 q g hb (roundStage r))
      (grind_no_clash_chain_stable_all L hL e0 q g hb hcr (roundStage r)))
    (grindRawTarget L hL e0 q g hb lane base r)
    (fun T hT c _ b => grind_raw_target_reassign L hL e0 q g hb hcr lane hcau base r c T hT b)
    (bd * OuterChallenge.fiberCeiling ^ 3)
    (fun T _ => grind_raw_target_card_le L hL e0 q g hb lane bd hbd base r T)

/-! ## 6. THE EVENTS AND THE UNION OVER THE ROUNDS -/

open Classical in
/-- THE EVENT THAT COUPLED ROUND `r`'s OWN CHALLENGE TRIPLE, AT COUNTER `base`,
LANDS IN THE BAD SET THE LANE HAS CHOSEN FOR IT, along a grinding chain.
`Finset.univ` is used here, as in the adopted
`RawBlockLanes.rawRoundBadEvent`, to cut the cylinder out of the table space. -/
noncomputable def grindRawRoundBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane) (base r : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    chainTriple L hL (grindState L hL e0 q g hb) (roundStage r) base T
      ∈ grindRawTarget L hL e0 q g hb lane base r T)

open Classical in
/-- Round `r` agrees on either lane: the log lane at counters `0, 1, 2` and
the gate lane at counters `3, 4, 5` of the SAME stage digest. -/
noncomputable def grindRawBothBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (logLane gateLane : GrindLane) (r : Nat) : Finset (OracleTable (boundedQueries L)) :=
  grindRawRoundBadEvent L hL e0 q g hb logLane 0 r
    ∪ grindRawRoundBadEvent L hL e0 q g hb gateLane 3 r

open Classical in
/-- **THE RAW OUTER BAD EVENT OF A GRINDING RUN.**  Some coupled round of either
lane agrees. -/
noncomputable def grindRawOuterBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (logLane gateLane : GrindLane) (d : Nat) : Finset (OracleTable (boundedQueries L)) :=
  (Finset.range d).biUnion (fun r => grindRawBothBadEvent L hL e0 q g hb logLane gateLane r)

theorem grind_raw_outer_bad_event_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (logLane gateLane : GrindLane) :
    grindRawOuterBadEvent L hL e0 q g hb logLane gateLane 0
      = (∅ : Finset (OracleTable (boundedQueries L))) := by
  rw [grindRawOuterBadEvent, Finset.range_zero, Finset.biUnion_empty]

/-- (6) On the no-clash event, round `r`'s raw bad event is covered by the two
FIXED-STAGE events of section 5: the no-clash events are nested. -/
theorem grind_raw_round_inter_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (logLane gateLane : GrindLane) (n r : Nat)
    (hr : roundStage r ≤ n) :
    grindRawBothBadEvent L hL e0 q g hb logLane gateLane r ∩ grindingNoClash L hL e0 q g hb n
      ⊆ ((grindingNoClash L hL e0 q g hb (roundStage r)).filter
            (fun T => chainTriple L hL (grindState L hL e0 q g hb) (roundStage r) 0 T
              ∈ grindRawTarget L hL e0 q g hb logLane 0 r T))
        ∪ ((grindingNoClash L hL e0 q g hb (roundStage r)).filter
            (fun T => chainTriple L hL (grindState L hL e0 q g hb) (roundStage r) 3 T
              ∈ grindRawTarget L hL e0 q g hb gateLane 3 r T)) := by
  rw [grindRawBothBadEvent, Finset.union_inter_distrib_right, grindRawRoundBadEvent,
    grindRawRoundBadEvent]
  exact Finset.union_subset_union
    (univ_filter_inter_subset _ _ _ (grind_no_clash_mono L hL e0 q g hb (roundStage r) n hr))
    (univ_filter_inter_subset _ _ _ (grind_no_clash_mono L hL e0 q g hb (roundStage r) n hr))

/-- (6) **THE UNION OVER THE ROUNDS, ON THE GRINDING CHAIN'S NO-CLASH EVENT.** -/
theorem grind_raw_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (logLane gateLane : GrindLane) (hlcau : GrindLaneCausal q logLane)
    (hgcau : GrindLaneCausal q gateLane) (bl bg : Nat) (hlog : GrindLaneBounded logLane bl)
    (hgate : GrindLaneBounded gateLane bg) (n : Nat) :
    ∀ k : Nat, (∀ r, r < k → roundStage r ≤ n) →
      oracleProbability (boundedQueries L)
          (grindRawOuterBadEvent L hL e0 q g hb logLane gateLane k
            ∩ grindingNoClash L hL e0 q g hb n)
        ≤ (k : ℚ) * (((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [grind_raw_outer_bad_event_zero, Finset.empty_inter, oracle_probability_empty,
        Nat.cast_zero, zero_mul]
  | succ k2 ih =>
      intro hk
      have hk2 : ∀ r, r < k2 → roundStage r ≤ n := fun r hr => hk r (by omega)
      have hkk : roundStage k2 ≤ n := hk k2 (by omega)
      have hsplit : grindRawOuterBadEvent L hL e0 q g hb logLane gateLane (k2 + 1)
            ∩ grindingNoClash L hL e0 q g hb n
          = (grindRawBothBadEvent L hL e0 q g hb logLane gateLane k2
              ∩ grindingNoClash L hL e0 q g hb n)
            ∪ (grindRawOuterBadEvent L hL e0 q g hb logLane gateLane k2
              ∩ grindingNoClash L hL e0 q g hb n) := by
        rw [grindRawOuterBadEvent, grindRawOuterBadEvent, Finset.range_succ,
          Finset.biUnion_insert, Finset.union_inter_distrib_right]
      have hround : oracleProbability (boundedQueries L)
          (grindRawBothBadEvent L hL e0 q g hb logLane gateLane k2
            ∩ grindingNoClash L hL e0 q g hb n)
          ≤ ((bl * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ)
            + ((bg * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
              / (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
        refine le_trans (oracle_probability_mono (boundedQueries L) _ _
          (grind_raw_round_inter_subset L hL e0 q g hb logLane gateLane n k2 hkk)) ?_
        refine le_trans (oracle_probability_union_le (boundedQueries L) _ _) ?_
        exact add_le_add
          (grind_raw_round_mass_le L hL e0 q g hb hcr logLane hlcau bl hlog 0
            (small_counter_lt 2 (by omega)) k2)
          (grind_raw_round_mass_le L hL e0 q g hb hcr gateLane hgcau bg hgate 3
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

/-- (6) **THE OUTER HALF OF THE UNION BOUND, FOR A GRINDING PROVER.**  The mass of
the event that some coupled round of either lane agrees, for a prover that
issues `q` frame probes of its own at every stage and reads the challenge oracle
at its own past stage digests, is at most the adopted
`ChallengeUnionBound.outerTerm degreeBits quotientDegree` plus the GRINDING
chain's clash mass at `N = (22 + 5 d) (q + 1)` oracle answers. -/
theorem grinding_outer_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g) (logLane gateLane : GrindLane)
    (hlcau : GrindLaneCausal q logLane) (hgcau : GrindLaneCausal q gateLane) (d quo : Nat)
    (hlog : GrindLaneBounded logLane 5) (hgate : GrindLaneBounded gateLane (quo + 2)) :
    oracleProbability (boundedQueries L)
        (grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d)
      ≤ ChallengeUnionBound.outerTerm d quo
        + (((22 + 5 * d) * (q + 1) : Nat) : ℚ) * ((((22 + 5 * d) * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl (grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d)
      (grindingNoClash L hL e0 q g hb (22 + 5 * d)))
  have hunion := oracle_probability_union_le (boundedQueries L)
    (grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d
      ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
    ((grindingNoClash L hL e0 q g hb (22 + 5 * d))ᶜ)
  have hround := grind_raw_no_clash_mass_le L hL e0 q g hb hcr logLane gateLane hlcau hgcau
    5 (quo + 2) hlog hgate (22 + 5 * d) d (fun r hr => round_stage_le r d hr)
  have hclash : oracleProbability (boundedQueries L)
      ((grindingNoClash L hL e0 q g hb (22 + 5 * d))ᶜ)
      ≤ (((22 + 5 * d) * (q + 1) : Nat) : ℚ) * ((((22 + 5 * d) * (q + 1) : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    grinding_chain_clash_probability_le L hL e0 q g hb (22 + 5 * d)
  have hterm : (d : ℚ) * (((5 * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
        / (Fintype.card OuterChallenge.DigestTriple : ℚ)
      + (((quo + 2) * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
        / (Fintype.card OuterChallenge.DigestTriple : ℚ))
      = ChallengeUnionBound.outerTerm d quo := round_terms_sum d quo
  rw [hterm] at hround
  linarith

/-! ## 7. THE BLOCK-0 LANES: GATE TAU AND GATE ALPHA AT THE DERIVE DIGEST -/

/-- **THE GATE TAU COLUMN A GRINDING RUN READS AT THE DERIVE DIGEST.** -/
def grindTauRead (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (d : Nat)
    (T : OracleTable (boundedQueries L)) : ChallengeUnionBound.TripleTuple d :=
  chainTauRead L hL (grindState L hL e0 q g hb) deriveStage d T

open Classical in
/-- **THE GATE ALPHA BAD EVENT OF A GRINDING RUN.**  `rows` and `coeffsOf` are
bound OUTSIDE the oracle law, exactly as in the adopted
`ReducedFullTransport.gateAlphaBadEvent`: the target is FIXED DATA, not a function
of the table or of the prover's messages. -/
noncomputable def grindGateAlphaBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (d rows : Nat)
    (coeffsOf : Nat → List Element) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    chainTriple L hL (grindState L hL e0 q g hb) deriveStage (alphaBase d) T
      ∈ OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf))

open Classical in
/-- **THE GATE TAU BAD EVENT OF A GRINDING RUN.** -/
noncomputable def grindGateTauBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (d : Nat)
    (gv : Nat → Element) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    grindTauRead L hL e0 q g hb d T ∈ ChallengeUnionBound.productEvent d
      (ZeroCheckSemantics.zeroCheckBadSet d gv))

/-- (7) **THE GATE ALPHA MASS, CONDITIONED ON THE GRINDING CHAIN'S NO-CLASH
EVENT.**  Section 1's diagonal step at a CONSTANT target, composed with the
adopted `ChallengeUnionBound.alpha_union_mass_bound`. -/
theorem grind_gate_alpha_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (d rows constraints : Nat) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        ((grindingNoClash L hL e0 q g hb deriveStage).filter (fun T =>
          chainTriple L hL (grindState L hL e0 q g hb) deriveStage (alphaBase d) T
            ∈ OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)))
      ≤ ChallengeUnionBound.alphaTerm rows constraints := by
  have hmass := chain_triple_target_mass_le L hL (grindState L hL e0 q g hb) deriveStage
    (alphaBase d) (alpha_counter_lt d hdu) (grindingNoClash L hL e0 q g hb deriveStage)
    (chain_stable_of_all L hL (grindState L hL e0 q g hb) deriveStage
      (tripleCounters (alphaBase d)) (grindingNoClash L hL e0 q g hb deriveStage)
      (grind_no_clash_chain_stable_all L hL e0 q g hb hcr deriveStage))
    (fun _ => OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf))
    (fun _ _ _ _ _ => rfl)
    (OuterChallenge.tupleEvent (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)).card
    (fun _ _ => le_refl _)
  have hdef : (((OuterChallenge.tupleEvent
        (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)).card : ℚ)
      / (Fintype.card OuterChallenge.DigestTriple : ℚ))
      = OuterChallenge.uniformTupleProbability
          (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf) := rfl
  rw [hdef] at hmass
  exact hmass.trans
    (ChallengeUnionBound.alpha_union_mass_bound rows constraints coeffsOf hclen)

open Classical in
/-- (7) **THE GATE TAU MASS, CONDITIONED ON THE GRINDING CHAIN'S NO-CLASH
EVENT.**  Section 2's column count at the grinding chain, composed with the
adopted `ChallengeUnionBound.tau_product_mass_bound`. -/
theorem grind_gate_tau_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hcr : ChallengeRestricted g)
    (d : Nat) (gv : Nat → Element) (hdu : 12 + 6 * d < Transcript.u64Limit) :
    oracleProbability (boundedQueries L)
        ((grindingNoClash L hL e0 q g hb deriveStage).filter (fun T =>
          grindTauRead L hL e0 q g hb d T ∈ ChallengeUnionBound.productEvent d
            (ZeroCheckSemantics.zeroCheckBadSet d gv)))
      ≤ ChallengeUnionBound.tauTerm d := by
  have hmass := chain_tau_target_mass_le L hL (grindState L hL e0 q g hb) deriveStage d
    (grindingNoClash L hL e0 q g hb deriveStage)
    (grind_no_clash_chain_stable_all L hL e0 q g hb hcr deriveStage) hdu
    (ChallengeUnionBound.productEvent d (ZeroCheckSemantics.zeroCheckBadSet d gv))
  have hdef : (((ChallengeUnionBound.productEvent d
        (ZeroCheckSemantics.zeroCheckBadSet d gv)).card : ℚ)
      / (Fintype.card (ChallengeUnionBound.TripleTuple d) : ℚ))
      = ChallengeUnionBound.uniformProductProbability d
          (ZeroCheckSemantics.zeroCheckBadSet d gv) := rfl
  rw [hdef] at hmass
  exact hmass.trans (ChallengeUnionBound.tau_product_mass_bound d gv)

/-! ## 8. THE UNION BOUND FOR A GRINDING PROVER -/

open Classical in
/-- **THE FULL BAD EVENT OF A GRINDING RUN**: some coupled round of either OUTER
lane agrees, OR the gate tau column at the derive digest lands in the adopted
zero-check bad set, OR the gate alpha does in the adopted row union.  The
association is the adopted `JointChallengeSpace.jointBadEvent`'s. -/
noncomputable def grindingFullBadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (logLane gateLane : GrindLane)
    (d rows : Nat) (gv : Nat → Element) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  (grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d
      ∪ grindGateTauBadEvent L hL e0 q g hb d gv)
    ∪ grindGateAlphaBadEvent L hL e0 q g hb d rows coeffsOf

open Classical in
theorem mem_grinding_full_bad_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (logLane gateLane : GrindLane)
    (d rows : Nat) (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ grindingFullBadEvent L hL e0 q g hb logLane gateLane d rows gv coeffsOf ↔
      (T ∈ grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d ∨
        T ∈ grindGateTauBadEvent L hL e0 q g hb d gv ∨
        T ∈ grindGateAlphaBadEvent L hL e0 q g hb d rows coeffsOf) := by
  simp only [grindingFullBadEvent, Finset.mem_union, or_assoc]

open Classical in
/-- (8) **THE UNION BOUND FOR A GRINDING PROVER.**  Under the random-oracle
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`, for EVERY
grinding prover that issues `q` frame probes of its own at every stage and reads
the challenge oracle at its own past stage digests, and EVERY pair of GRIND lanes
obeying the protocol's causality and the adopted degree bounds, the mass of

  `outer bad  ∪  gate tau bad  ∪  gate alpha bad`

is at most the adopted `ChallengeUnionBound` terms plus ONE clash term, the
GRINDING chain's, at `N = (22 + 5 d) (q + 1)` oracle answers.  The three masses
are conditioned on NESTED no-clash events, so one complement term pays for all
three.  READ THE HONESTY HEADER. -/
theorem grinding_union_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g) (logLane gateLane : GrindLane)
    (hlcau : GrindLaneCausal q logLane) (hgcau : GrindLaneCausal q gateLane)
    (d quo rows constraints : Nat) (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hlog : GrindLaneBounded logLane 5)
    (hgate : GrindLaneBounded gateLane (quo + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L hL e0 q g hb logLane gateLane d rows gv coeffsOf)
      ≤ ChallengeUnionBound.outerTerm d quo + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints
        + (((22 + 5 * d) * (q + 1) : Nat) : ℚ) * ((((22 + 5 * d) * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hnest : grindingNoClash L hL e0 q g hb (22 + 5 * d)
      ⊆ grindingNoClash L hL e0 q g hb deriveStage :=
    grind_no_clash_mono L hL e0 q g hb deriveStage (22 + 5 * d) (by rw [deriveStage]; omega)
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (grindingFullBadEvent L hL e0 q g hb logLane gateLane d rows gv coeffsOf)
      (grindingNoClash L hL e0 q g hb (22 + 5 * d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (grindingFullBadEvent L hL e0 q g hb logLane gateLane d rows gv coeffsOf
      ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
    ((grindingNoClash L hL e0 q g hb (22 + 5 * d))ᶜ)
  have hsplit : grindingFullBadEvent L hL e0 q g hb logLane gateLane d rows gv coeffsOf
        ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d)
      = ((grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d
            ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
          ∪ (grindGateTauBadEvent L hL e0 q g hb d gv
            ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d)))
        ∪ (grindGateAlphaBadEvent L hL e0 q g hb d rows coeffsOf
            ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d)) := by
    rw [grindingFullBadEvent, Finset.union_inter_distrib_right,
      Finset.union_inter_distrib_right]
  have hu2 : oracleProbability (boundedQueries L)
        (grindingFullBadEvent L hL e0 q g hb logLane gateLane d rows gv coeffsOf
          ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
      ≤ oracleProbability (boundedQueries L)
          ((grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d
              ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
            ∪ (grindGateTauBadEvent L hL e0 q g hb d gv
              ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d)))
        + oracleProbability (boundedQueries L)
            (grindGateAlphaBadEvent L hL e0 q g hb d rows coeffsOf
              ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d)) := by
    rw [hsplit]
    exact oracle_probability_union_le (boundedQueries L) _ _
  have hu3 := oracle_probability_union_le (boundedQueries L)
    (grindRawOuterBadEvent L hL e0 q g hb logLane gateLane d
      ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
    (grindGateTauBadEvent L hL e0 q g hb d gv ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
  have houter := grind_raw_no_clash_mass_le L hL e0 q g hb hcr logLane gateLane hlcau hgcau
    5 (quo + 2) hlog hgate (22 + 5 * d) d (fun r hr => round_stage_le r d hr)
  rw [round_terms_sum d quo] at houter
  have htausub : grindGateTauBadEvent L hL e0 q g hb d gv
        ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d)
      ⊆ (grindingNoClash L hL e0 q g hb deriveStage).filter (fun T =>
          grindTauRead L hL e0 q g hb d T ∈ ChallengeUnionBound.productEvent d
            (ZeroCheckSemantics.zeroCheckBadSet d gv)) := by
    rw [grindGateTauBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have htau : oracleProbability (boundedQueries L)
      (grindGateTauBadEvent L hL e0 q g hb d gv
        ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
      ≤ ChallengeUnionBound.tauTerm d :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ htausub)
      (grind_gate_tau_no_clash_mass_le L hL e0 q g hb hcr d gv hdu)
  have halphasub : grindGateAlphaBadEvent L hL e0 q g hb d rows coeffsOf
        ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d)
      ⊆ (grindingNoClash L hL e0 q g hb deriveStage).filter (fun T =>
          chainTriple L hL (grindState L hL e0 q g hb) deriveStage (alphaBase d) T
            ∈ OuterChallenge.tupleEvent
                (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)) := by
    rw [grindGateAlphaBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have halpha : oracleProbability (boundedQueries L)
      (grindGateAlphaBadEvent L hL e0 q g hb d rows coeffsOf
        ∩ grindingNoClash L hL e0 q g hb (22 + 5 * d))
      ≤ ChallengeUnionBound.alphaTerm rows constraints :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ halphasub)
      (grind_gate_alpha_no_clash_mass_le L hL e0 q g hb hcr d rows constraints coeffsOf hdu
        hclen)
  have hclash : oracleProbability (boundedQueries L)
      ((grindingNoClash L hL e0 q g hb (22 + 5 * d))ᶜ)
      ≤ (((22 + 5 * d) * (q + 1) : Nat) : ℚ) * ((((22 + 5 * d) * (q + 1) : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    grinding_chain_clash_probability_le L hL e0 q g hb (22 + 5 * d)
  linarith

open Classical in
/-- (8) **THE SAME, WITH THE CONSTANT READ OFF AS THE ADOPTED `combinedBound`.**
At `rows = 2 ^ degreeBits` the three terms ARE
`ChallengeUnionBound.combinedBound degreeBits quotientDegree degreeBits constraints`,
term for term, with nothing added and nothing dropped -- and now for a prover with
`q` ORACLE QUERIES OF ITS OWN PER STAGE.  The clash constant is the adopted
`GrindingQueryBound` one, `N (N + 1) / 2` at `N = (22 + 5 d) (q + 1)`. -/
theorem grinding_union_bad_draw_probability_le_combined (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g) (logLane gateLane : GrindLane)
    (hlcau : GrindLaneCausal q logLane) (hgcau : GrindLaneCausal q gateLane)
    (d quo constraints : Nat) (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hlog : GrindLaneBounded logLane 5)
    (hgate : GrindLaneBounded gateLane (quo + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L hL e0 q g hb logLane gateLane d (2 ^ d) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d quo d constraints
        + (((22 + 5 * d) * (q + 1) : Nat) : ℚ) * ((((22 + 5 * d) * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := grinding_union_bad_draw_probability_le L hL e0 q g hb hcr logLane gateLane hlcau
    hgcau d quo (2 ^ d) constraints gv coeffsOf hdu hlog hgate hclen
  rw [ChallengeUnionBound.combinedBound]
  exact h

/-! ## 9. A PROBE-READING PROVER, AND THE CLOSED INSTANCE

WHAT THIS SECTION IS AND IS NOT.  `probeGrinder` MAKES `q` ORACLE QUERIES PER
STAGE AND READS THEM -- that is what puts it outside the adopted
`StrategyChainBound.Strategy` class -- but it does not SEARCH: it keeps probe `0`
whatever the answers are, so it is an instance of the arithmetic, not a
demonstration that grinding buys anything.  Likewise the adopted
`separatedRawLane` is a CONSTANT lane, and the numbers below are the closed form
of the bound at `d = 13`, not a measured attack success.  A prover that genuinely
selects on what it read is `preReadGrinder` of section 10, and it is exactly the
prover the hypothesis excludes. -/

/-- (9) **THE ADOPTED `GrindingQueryBound.probeGrinder` IS CHALLENGE-RESTRICTED.**
It probes at its own current digest and absorbs a payload it READS OFF ITS FIRST
PROBE'S ANSWER; it never consults the challenge oracle at all, so the hypothesis
of sections 5 to 8 holds vacuously.  The adopted
`GrindingQueryBound.probe_grinder_is_not_transcript_restricted` says it is NOT a
`StrategyChainBound.Strategy`.  With
`grinding_of_strategy_challenge_restricted` -- every adopted strategy, lifted, IS
challenge-restricted -- that is containment in one direction and a witness
outside in the other, which is the whole content of "a larger class of
strategies than the adopted `RawBlockLanes` one".  It is NOT a claim that the
bound below subsumes the adopted `RawBlockLanes` theorem; see section 3. -/
theorem probe_grinder_challenge_restricted : ChallengeRestricted probeGrinder :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem grind_lane_bounded_mono (lane : GrindLane) (b1 b2 : Nat) (h : b1 ≤ b2)
    (hbd : GrindLaneBounded lane b1) : GrindLaneBounded lane b2 :=
  fun r a ch => ⟨le_trans (hbd r a ch).1 h, le_trans (hbd r a ch).2 h⟩

/-- (9) **A ROUND-`0` RAW TARGET ALONG A GRINDING CHAIN IS INHABITED WHEN THE TWO
CLAIMS DIFFER AND THE TWO ROUND POLYNOMIALS MEET.**  The adopted
`ConditionalSoundness.round_agreement_of_ne`, pushed to the digest alphabet by the
adopted `JointChallengeSpace.mem_tupleEvent`.  Stated over an ABSTRACT lane, as
the adopted `RawBlockLanes.raw_target_zero_nonempty_of_agreement` is. -/
theorem grind_raw_target_zero_nonempty_of_agreement (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (lane : GrindLane) (base : Nat) (T : OracleTable (boundedQueries L))
    (ds : OuterChallenge.DigestTriple) (hne : lane.claim ≠ lane.truthClaim)
    (he : (OuterRound.polynomial lane.claim
            (lane.message 0 (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T))).eval
          (OuterChallenge.reduceTriple ds)
        = (OuterRound.polynomial lane.truthClaim
            (lane.truth 0 (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T))).eval
          (OuterChallenge.reduceTriple ds)) :
    (grindRawTarget L hL e0 q g hb lane base 0 T).Nonempty := by
  have hc1 : (grindRawClaims L hL e0 q g hb lane base T 0).1 = lane.claim := rfl
  have hc2 : (grindRawClaims L hL e0 q g hb lane base T 0).2 = lane.truthClaim := rfl
  refine ⟨ds, ?_⟩
  rw [grindRawTarget, JointChallengeSpace.mem_tupleEvent, grindRawBadSet, hc1, hc2]
  exact ConditionalSoundness.round_agreement_of_ne lane.claim lane.truthClaim
    ⟨lane.message 0 (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T),
      lane.truth 0 (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T),
      OuterChallenge.reduceTriple ds⟩ hne he

/-- (9) **THE ADOPTED `RawBlockLanes.separatedRawLane`, AS A GRIND LANE**, reading
the prover's probe answers not at all. -/
def separatedGrindLane : GrindLane := grindLaneOfRawLane separatedRawLane

theorem separated_grind_lane_causal (q : Nat) : GrindLaneCausal q separatedGrindLane :=
  grind_lane_of_raw_lane_causal q separatedRawLane separated_raw_lane_causal

theorem separated_grind_lane_bounded : GrindLaneBounded separatedGrindLane 5 :=
  grind_lane_of_raw_lane_bounded separatedRawLane 5 separated_raw_lane_bounded

/-- (9) **SO THE PER-ROUND BOUND OF SECTION 5 IS NOT A BOUND ON AN EMPTY SET.**
That lane's round-`0` target contains the adopted
`OuterLaneTransport.zeroDigestTriple`, at EVERY grinding strategy, EVERY counter
base and EVERY table. -/
theorem grind_separated_raw_target_zero_nonempty (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (base : Nat) (T : OracleTable (boundedQueries L)) :
    (grindRawTarget L hL e0 q g hb separatedGrindLane base 0 T).Nonempty :=
  grind_raw_target_zero_nonempty_of_agreement L hL e0 q g hb separatedGrindLane base T
    zeroDigestTriple separated_raw_lane_claims_differ
    (separated_raw_lane_agrees_at_zero (grindTableView L hL e0 q g hb T))

open Classical in
/-- (9) **THE CLOSED INSTANCE AT THE ENVELOPE, FOR A PROBE-READING PROVER.**
Thirteen coupled rounds, the adopted `probeGrinder` with `q` frame probes of its
own at every one of the `22 + 5 * 13 = 87` stages -- a prover that READS its
probe answers but does not SEARCH them -- and `separatedGrindLane`, the adopted
`separatedRawLane` lifted, a CONSTANT lane, on both outer lanes, whose round-`0`
target is provably inhabited.
This is an instance of the arithmetic; it is not evidence about what a grinding
prover achieves.  The constant is the whole adopted
`ChallengeUnionBound.combinedBound 13 8 13 123` plus the grinding chain's clash
mass at `N = 87 (q + 1)`. -/
theorem grinding_union_bound_at_thirteen (L : Nat) (hL : 93 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L (Nat.le_trans (by norm_num) hL) e0 q probeGrinder
          (probe_grinder_bounded L hL) separatedGrindLane separatedGrindLane 13 (2 ^ 13)
          gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + ((87 * (q + 1) : Nat) : ℚ) * (((87 * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := grinding_union_bad_draw_probability_le_combined L (Nat.le_trans (by norm_num) hL)
    e0 q probeGrinder (probe_grinder_bounded L hL) probe_grinder_challenge_restricted
    separatedGrindLane separatedGrindLane (separated_grind_lane_causal q)
    (separated_grind_lane_causal q)
    13 8 123 gv coeffsOf thirteen_counter_budget separated_grind_lane_bounded
    (grind_lane_bounded_mono separatedGrindLane 5 (8 + 2) (by omega)
      separated_grind_lane_bounded)
    hclen
  have harith : ((22 + 5 * 13) * (q + 1) : Nat) = 87 * (q + 1) := by omega
  rw [harith] at h
  exact h

open Classical in
/-- (9) **A MILLION PROBES PER STAGE.**  At `q = 2 ^ 20` the grinder reads
`87 * (2 ^ 20 + 1) = 91226199` oracle answers and the clash numerator is
`4161109737606900`, the adopted
`GrindingQueryBound.grinding_chain_clash_at_eighty_seven_many_probes` numeral. -/
theorem grinding_union_bound_at_thirteen_many_probes (L : Nat) (hL : 93 ≤ L)
    (e0 : Transcript.Digest) (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L (Nat.le_trans (by norm_num) hL) e0 1048576 probeGrinder
          (probe_grinder_bounded L hL) separatedGrindLane separatedGrindLane 13 (2 ^ 13)
          gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + (4161109737606900 : ℚ) / (Fintype.card Block : ℚ) := by
  have h := grinding_union_bound_at_thirteen L hL e0 1048576 gv coeffsOf hclen
  rw [show ((87 * (1048576 + 1) : Nat) : ℚ) * (((87 * (1048576 + 1) : Nat) : ℚ) + 1) / 2
    = (4161109737606900 : ℚ) from by norm_num] at h
  exact h

/-- (9) The clash numerator at a million probes per stage is below `2 ^ (-200)`.
`Fintype.card Block` is written as `2 ^ 256` through the adopted
`RandomOracleSqueezes.block_card`; no cardinality is evaluated as a numeral. -/
theorem many_probes_clash_tiny :
    (4161109737606900 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / (2 : ℚ) ^ 200 := by
  have hn : (4161109737606900 : Nat) * 2 ^ 200 ≤ Fintype.card Block := by
    rw [block_card_two_pow]
    calc (4161109737606900 : Nat) * 2 ^ 200 ≤ 2 ^ 56 * 2 ^ 200 :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ 256 := by rw [← pow_add]
  have hq : (4161109737606900 : ℚ) * (2 : ℚ) ^ 200 ≤ (Fintype.card Block : ℚ) := by
    exact_mod_cast hn
  rw [div_le_div_iff block_card_cast_pos (by positivity), one_mul]
  exact hq

/-- (9) **THE CLOSED BOUND IS A REAL NUMBER STRICTLY BELOW `1`, AT A MILLION
PROBES PER STAGE.**  The adopted
`ChallengeUnionBound.combined_bound_at_extremes_numeric` gives `2 ^ (-172)` for
the challenge terms.  READ HONESTY (viii): THIS IS NOT THE PROTOCOL'S SOUNDNESS
ERROR. -/
theorem grinding_union_bound_at_thirteen_many_probes_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123
        + (4161109737606900 : ℚ) / (Fintype.card Block : ℚ) < 1 := by
  have h1 := ChallengeUnionBound.combined_bound_at_extremes_numeric
  have h2 := many_probes_clash_tiny
  have h3 : (1 : ℚ) / 2 ^ 172 + 1 / (2 : ℚ) ^ 200 < 1 := by norm_num
  linarith

/-! ## 10. THE ATTACK THE CHALLENGE RESTRICTION EXCLUDES -/

/-- **THE INVARIANCE THE DIAGONAL STEP NEEDS, NAMED.**  Round `r`'s bad set -- the
set the round's own challenge triple is tested against -- must not move when the
round's own challenge cells are reassigned.  This is the formal content of "the
round's message was chosen before the round's challenge was squeezed", and
`grind_round_target_invariant_of_challenge_restricted` discharges it from
`ChallengeRestricted` and the chain's no-clash event. -/
def GrindingRoundTargetInvariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane) (base r : Nat) : Prop :=
  ∀ (c : Nat) (T : OracleTable (boundedQueries L)),
    T ∈ grindingNoClash L hL e0 q g hb (roundStage r) → ∀ b : Block,
      grindRawTarget L hL e0 q g hb lane base r
          (reassign T (chainChallengeSel L hL (grindState L hL e0 q g hb) (roundStage r) c T) b)
        = grindRawTarget L hL e0 q g hb lane base r T

theorem grind_round_target_invariant_of_challenge_restricted (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g) (lane : GrindLane) (hcau : GrindLaneCausal q lane)
    (base r : Nat) :
    GrindingRoundTargetInvariant L hL e0 q g hb lane base r :=
  fun c T hT b => grind_raw_target_reassign L hL e0 q g hb hcr lane hcau base r c T hT b

/-- **A PROVER THAT PROBES A PAYLOAD AND THEN ABSORBS IT.**  At stage `k` it
probes `Transcript.frame` at its own current digest with tag `1` and the eight
little-endian bytes of the probe index, and its absorb is the tag and payload of
PROBE `0`.  Its absorb does not itself act on what it learned; the point of it is
the QUERY PATTERN, which is the one every grinder uses and which
`preReadGrinder` below turns into an attack. -/
def echoGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun _ _ _ _ => (1, Transcript.le 8 0)

theorem echo_grinder_bounded (L : Nat) (hL : 69 ≤ L) : GrindingBounded L echoGrinder := by
  constructor
  · intro _ i _ _ _
    show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · intro _ _ _ _
    show 61 + (Transcript.le 8 0).length ≤ L
    rw [Transcript.le_length]
    omega

/-- (10) **THE STAGE-`k` PROBE `0` AND THE STAGE-`k` ABSORB ARE THE SAME QUERY.**
Both are `Transcript.frame` at the chain's stage-`k` digest with tag `1` and
payload `Transcript.le 8 0`.  This is the repeat the adopted
`GrindingQueryBound.distinctClashEvent` DELIBERATELY EXCLUDES, and it is not an
accident of this strategy: a grinder probes candidates and then absorbs one. -/
theorem echo_grinder_probe_is_absorb (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (hb : GrindingBounded L echoGrinder) (hq : 0 < q) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    grindSelSeq L hL e0 q echoGrinder hb (slotPos q k 0) T
      = grindSelSeq L hL e0 q echoGrinder hb (slotPos q k q) T := by
  apply Subtype.ext
  have hq1 : grindQuery e0 q echoGrinder
        (runAns L hL e0 q echoGrinder hb (slotPos q k 0) T) (challengesOf L hL T)
        (slotPos q k 0)
      = (grindState L hL e0 q echoGrinder hb k T, 1, Transcript.le 8 0) := by
    unfold grindQuery
    rw [slot_pos_mod q k 0 (Nat.zero_le q), slot_pos_div q k 0 (Nat.zero_le q), if_pos hq]
    show (stateOf e0 q (runAns L hL e0 q echoGrinder hb (slotPos q k 0) T) k, 1,
      Transcript.le 8 0) = _
    rw [state_of_run_ans_le L hL e0 q echoGrinder hb (slotPos q k 0) k (fun i2 hi2 => ?_) T]
    have hexp : (i2 + 1) * (q + 1) = i2 * (q + 1) + (q + 1) := by ring
    rw [slotPos, slotPos, hi2]
    omega
  have hq2 : grindQuery e0 q echoGrinder
        (runAns L hL e0 q echoGrinder hb (slotPos q k q) T) (challengesOf L hL T)
        (slotPos q k q)
      = (grindState L hL e0 q echoGrinder hb k T, 1, Transcript.le 8 0) := by
    rw [grind_query_absorb]
    show (stateOf e0 q (runAns L hL e0 q echoGrinder hb (slotPos q k q) T) k,
      ((1 : Transcript.Byte), Transcript.le 8 0)) = _
    rw [state_of_run_ans_at L hL e0 q echoGrinder hb k k (le_refl k) T]
  show grindBytes e0 q echoGrinder (runAns L hL e0 q echoGrinder hb (slotPos q k 0) T)
      (challengesOf L hL T) (slotPos q k 0)
    = grindBytes e0 q echoGrinder (runAns L hL e0 q echoGrinder hb (slotPos q k q) T)
      (challengesOf L hL T) (slotPos q k q)
  unfold grindBytes
  rw [hq1, hq2]

open Classical in
/-- **THE PRE-READ EVENT.**  Some position `m` STRICTLY BEFORE stage `k`'s absorb
is already answered by the block whose digest is stage `k + 1`'s -- the digest
round `k + 1`'s challenges are squeezed at.  The prover is handed
`GrindingQueryBound.challengesOf` IN FULL, at every digest, so at position `m` it
may read those challenges, and it still has its stage-`k` absorb to choose.  That
is grinding ON THE FIAT--SHAMIR CHALLENGES.

`Finset.univ` is used here to cut the event out of the table space, as the adopted
event definitions do. -/
noncomputable def grindingPreReadEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ∃ k ∈ Finset.range n, ∃ m ∈ Finset.range (slotPos q k q),
    blockDigest (T (grindSelSeq L hL e0 q g hb m T))
      = grindState L hL e0 q g hb (k + 1) T)

/-- (10) The echo grinder's stage-`k` probe `0` already answers the stage-`k + 1`
digest, at EVERY table. -/
theorem echo_grinder_probe_answer_is_next_state (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (hb : GrindingBounded L echoGrinder) (hq : 0 < q)
    (k : Nat) (T : OracleTable (boundedQueries L)) :
    blockDigest (T (grindSelSeq L hL e0 q echoGrinder hb (slotPos q k 0) T))
      = grindState L hL e0 q echoGrinder hb (k + 1) T := by
  rw [echo_grinder_probe_is_absorb L hL e0 q hb hq k T]
  rfl

theorem oracle_probability_univ (Q : Finset Transcript.Bytes) :
    oracleProbability Q (Finset.univ : Finset (OracleTable Q)) = 1 := by
  rw [oracleProbability, Finset.card_univ]
  exact div_self (ne_of_gt (oracle_card_cast_pos Q))

open Classical in
/-- (10) **THE PRE-READ EVENT HAS MASS `1` FOR A PROBE-THEN-ABSORB PROVER.**  It is
the WHOLE table space.  So the pre-read event CANNOT be conditioned away the way
the chain's clash event is: there is no small bound to be had on it, and the
adopted `GrindingQueryBound.distinct_answer_clash_probability_le` does not bound it
either -- that theorem charges only pairs of positions asking DIFFERENT byte
strings, and the probe-then-absorb pair asks the SAME one. -/
theorem echo_grinder_pre_read_event_is_everything (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (hb : GrindingBounded L echoGrinder) (hq : 0 < q)
    (n : Nat) (hn : 0 < n) :
    grindingPreReadEvent L hL e0 q echoGrinder hb n
      = (Finset.univ : Finset (OracleTable (boundedQueries L))) := by
  apply Finset.eq_univ_of_forall
  intro T
  rw [grindingPreReadEvent, Finset.mem_filter]
  refine ⟨Finset.mem_univ T, 0, Finset.mem_range.mpr hn, slotPos q 0 0, ?_, ?_⟩
  · refine Finset.mem_range.mpr ?_
    rw [slotPos, slotPos]
    omega
  · exact echo_grinder_probe_answer_is_next_state L hL e0 q hb hq 0 T

open Classical in
theorem echo_grinder_pre_read_mass_one (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L echoGrinder) (hq : 0 < q) (n : Nat) (hn : 0 < n) :
    oracleProbability (boundedQueries L) (grindingPreReadEvent L hL e0 q echoGrinder hb n)
      = 1 := by
  rw [echo_grinder_pre_read_event_is_everything L hL e0 q hb hq n hn]
  exact oracle_probability_univ (boundedQueries L)

/-- The one block the challenge-grinding prover below is searching for.  Any
fixed block would serve; this is the adopted
`OuterChallenge.digestBlock OuterInitial.zeroDigest`. -/
def preReadTarget : Block := OuterChallenge.digestBlock OuterInitial.zeroDigest

/-- **A PROVER THAT GRINDS ON THE CHALLENGES.**  It probes exactly as `echoGrinder`
does -- `Transcript.frame` at its own current digest, tag `1`, payload
`Transcript.le 8 i` -- and then its absorb is a SELECTOR on a challenge it has
PRE-READ: it evaluates the challenge oracle at `blockDigest (pa k 0)`, the digest
of its own stage-`k` probe-`0` ANSWER, and absorbs the payload of that very probe
(`Transcript.le 8 0`, tag `1`) exactly when the answer it read is
`preReadTarget`, and a DIFFERENT payload (`Transcript.le 8 1`) otherwise.

SO THE CHAIN ADVANCES TO THE PRE-READ DIGEST EXACTLY ON THE FAVOURABLE READ.  On
the favourable branch the absorb's byte string IS the probe-`0` byte string
(`pre_read_grinder_absorb_is_probe_when_favourable`), so the stage-`k + 1` digest
is `blockDigest` of the probe-`0` answer -- the digest whose challenges the prover
already looked at before choosing the absorb.  That is grinding on the
Fiat--Shamir challenges: in general, with `q` probes the prover gets `q`
independent draws at the next round's challenge and keeps a favourable one; this
selector tests ONE such draw (probe `0`) and absorbs `le 8 1` otherwise.

This is a perfectly legal `GrindingQueryBound.GrindingStrategy`: the adopted model
hands every strategy the whole challenge oracle at every digest. -/
def preReadGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun k _ ch pa =>
    (1, if ch (blockDigest (pa k 0)) 0 = preReadTarget then Transcript.le 8 0
        else Transcript.le 8 1)

theorem pre_read_grinder_bounded (L : Nat) (hL : 69 ≤ L) : GrindingBounded L preReadGrinder := by
  classical
  constructor
  · intro _ i _ _ _
    show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · intro k _ ch pa
    show 61 + (if ch (blockDigest (pa k 0)) 0 = preReadTarget then Transcript.le 8 0
      else Transcript.le 8 1).length ≤ L
    by_cases hf : ch (blockDigest (pa k 0)) 0 = preReadTarget
    · rw [if_pos hf, Transcript.le_length]
      omega
    · rw [if_neg hf, Transcript.le_length]
      omega

/-- (10) **ON THE FAVOURABLE READ THE ABSORB ASKS THE PROBE'S OWN BYTE STRING.**
When the challenge the prover pre-read at `blockDigest` of its stage-`k` probe-`0`
answer is `preReadTarget`, the stage-`k` absorb query and the stage-`k` probe-`0`
query are THE SAME byte string, so the stage-`k + 1` digest of the chain is
`blockDigest` of that probe's answer: the round whose challenges were pre-read is
the round the chain actually reaches.  Contrast `echoGrinder`, which reaches that
digest unconditionally but never reads a challenge. -/
theorem pre_read_grinder_absorb_is_probe_when_favourable (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (hb : GrindingBounded L preReadGrinder) (hq : 0 < q)
    (k : Nat) (T : OracleTable (boundedQueries L))
    (hfav : challengesOf L hL T
        (blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 0) T))) 0
      = preReadTarget) :
    grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k q) T
      = grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 0) T := by
  classical
  apply Subtype.ext
  have hlt : slotPos q k 0 < slotPos q k q := by
    rw [slotPos, slotPos]
    omega
  have hpa : runAns L hL e0 q preReadGrinder hb (slotPos q k q) T (slotPos q k 0)
      = T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 0) T) := by
    rw [run_ans_eq, if_pos hlt]
  have hq2 : grindQuery e0 q preReadGrinder
        (runAns L hL e0 q preReadGrinder hb (slotPos q k q) T) (challengesOf L hL T)
        (slotPos q k q)
      = (grindState L hL e0 q preReadGrinder hb k T, 1, Transcript.le 8 0) := by
    rw [grind_query_absorb]
    show (stateOf e0 q (runAns L hL e0 q preReadGrinder hb (slotPos q k q) T) k,
      ((1 : Transcript.Byte),
        if challengesOf L hL T
            (blockDigest (runAns L hL e0 q preReadGrinder hb (slotPos q k q) T
              (slotPos q k 0))) 0 = preReadTarget
          then Transcript.le 8 0 else Transcript.le 8 1)) = _
    rw [state_of_run_ans_at L hL e0 q preReadGrinder hb k k (le_refl k) T, hpa, if_pos hfav]
  have hq1 : grindQuery e0 q preReadGrinder
        (runAns L hL e0 q preReadGrinder hb (slotPos q k 0) T) (challengesOf L hL T)
        (slotPos q k 0)
      = (grindState L hL e0 q preReadGrinder hb k T, 1, Transcript.le 8 0) := by
    unfold grindQuery
    rw [slot_pos_mod q k 0 (Nat.zero_le q), slot_pos_div q k 0 (Nat.zero_le q), if_pos hq]
    show (stateOf e0 q (runAns L hL e0 q preReadGrinder hb (slotPos q k 0) T) k, 1,
      Transcript.le 8 0) = _
    rw [state_of_run_ans_le L hL e0 q preReadGrinder hb (slotPos q k 0) k
      (fun i2 hi2 => ?_) T]
    have hexp : (i2 + 1) * (q + 1) = i2 * (q + 1) + (q + 1) := by ring
    rw [slotPos, slotPos, hi2]
    omega
  show grindBytes e0 q preReadGrinder
      (runAns L hL e0 q preReadGrinder hb (slotPos q k q) T)
      (challengesOf L hL T) (slotPos q k q)
    = grindBytes e0 q preReadGrinder
      (runAns L hL e0 q preReadGrinder hb (slotPos q k 0) T)
      (challengesOf L hL T) (slotPos q k 0)
  unfold grindBytes
  rw [hq1, hq2]

/-- (10) **THE CHALLENGE-GRINDING PROVER IS NOT CHALLENGE-RESTRICTED.**  Two
challenge oracles that agree at every stage digest the strategy is handed drive
the selector to DIFFERENT branches, and so to different absorb payloads, because
the selector reads the oracle somewhere else -- at the digest of a probe answer.
So the hypothesis of sections 5 to 8 is a genuine restriction on the prover, and
this is the prover it excludes: the union bound above DOES NOT COVER IT, and
nothing here bounds its bad-draw mass. -/
theorem pre_read_grinder_not_challenge_restricted : ¬ ChallengeRestricted preReadGrinder := by
  classical
  intro hcr
  obtain ⟨b2, hne⟩ :=
    Fintype.exists_ne_of_one_lt_card (block_card_gt_small 1 (by norm_num)) preReadTarget
  have hdne : blockDigest b2 ≠ blockDigest preReadTarget := by
    intro h
    exact hne (Subtype.ext (congrArg Transcript.Digest.bytes h))
  have hagree : ∀ j, j ≤ 0 →
      (fun (_ : Transcript.Digest) (_ : Nat) => preReadTarget)
          ((fun _ => blockDigest preReadTarget) j)
        = (fun (e : Transcript.Digest) (_ : Nat) =>
            if e = blockDigest preReadTarget then preReadTarget else b2)
          ((fun _ => blockDigest preReadTarget) j) := by
    intro j _
    funext _c
    show preReadTarget
      = if blockDigest preReadTarget = blockDigest preReadTarget then preReadTarget else b2
    rw [if_pos rfl]
  have hEq := hcr.2 0 (fun _ => blockDigest preReadTarget) (fun _ _ => preReadTarget)
    (fun e _ => if e = blockDigest preReadTarget then preReadTarget else b2)
    (fun _ _ => b2) hagree
  have hLeft : preReadGrinder.absorb 0 (fun _ => blockDigest preReadTarget)
      (fun _ _ => preReadTarget) (fun _ _ => b2) = (1, Transcript.le 8 0) := by
    show ((1 : Transcript.Byte),
      if preReadTarget = preReadTarget then Transcript.le 8 0 else Transcript.le 8 1)
      = ((1 : Transcript.Byte), Transcript.le 8 0)
    rw [if_pos rfl]
  have hRight : preReadGrinder.absorb 0 (fun _ => blockDigest preReadTarget)
      (fun e _ => if e = blockDigest preReadTarget then preReadTarget else b2)
      (fun _ _ => b2) = (1, Transcript.le 8 1) := by
    show ((1 : Transcript.Byte),
      if (if blockDigest b2 = blockDigest preReadTarget then preReadTarget else b2)
          = preReadTarget then Transcript.le 8 0 else Transcript.le 8 1)
      = ((1 : Transcript.Byte), Transcript.le 8 1)
    rw [if_neg hdne, if_neg hne]
  rw [hLeft, hRight] at hEq
  have hle : Transcript.le 8 0 = Transcript.le 8 1 := congrArg Prod.snd hEq
  have h01 : (0 : Nat) = 1 :=
    Transcript.le_injective_bounded 8 0 1 (by norm_num) (by norm_num) hle
  omega

end Audit.Wire3.GrindingUnionBound
