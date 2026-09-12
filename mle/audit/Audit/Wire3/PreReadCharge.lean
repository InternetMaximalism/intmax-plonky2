import Audit.Wire3.GrindingUnionBound

/-!
# CHARGING THE PROBE, NOT THE ABSORB: THE PRE-READ GRINDER'S PER-ROUND MASS

## The gap this module addresses

`GrindingUnionBound` (GUB) delivers the union bound along a grinding chain under
one hypothesis, `ChallengeRestricted`: the prover reads the Fiat--Shamir challenge
oracle only at its own past stage digests.  Its section 10 exhibits the prover the
hypothesis excludes -- `preReadGrinder`, which reads the challenge oracle at the
digest of its own PROBE ANSWER and then absorbs that probe's payload when the
challenge it read is favourable -- and records that

* `pre_read_grinder_not_challenge_restricted`: the attacker is outside the class;
* `echo_grinder_pre_read_mass_one`: the natural repair, conditioning on the
  complement of a "the prover read the round's challenge first" event, is refuted,
  because a probe-then-absorb prover asks the SAME byte string twice and the
  adopted `GrindingQueryBound.distinct_answer_clash_probability_le` deliberately
  charges only pairs of positions asking DIFFERENT strings;
* and that nothing in that tree bounds the excluded prover's bad-draw mass.

THIS MODULE CHARGES THE PROBE INSTEAD OF THE ABSORB.  The attack succeeds only if
some probe's answer digest carries a favourable challenge, so the object to be
bounded is not the absorb (a repeat, uncharged by construction) but the `q`
PROBES, each of which asks a byte string the run has not asked before and
therefore draws a FRESH oracle answer.  Conditioned on the probe's answer digest
being separated from the digests the run has already produced, the three challenge
cells at that digest are cells the conditioning event cannot move, and the adopted
`GrindingUnionBound.chain_triple_target_mass_le` -- which is stated over an
ABSTRACT stage-digest family `st : Nat -> OracleTable -> Digest`, not over the
chain -- applies verbatim at the family `fun _ T => probeDigestAt ... k i T`.
Summing over the `q` probes of the round's stage and the absorb multiplies the
per-round term by `q + 1`.  That is an UPPER bound only: no matching lower bound
is proved anywhere below, and nothing here says `q + 1` is what grinding costs.

## The prover class

Two hypotheses replace `ChallengeRestricted`, and `preReadGrinder` satisfies both:

* `ProbeHistoryOnly g` -- the probes are a function of the stage index, the probe
  index and the stage digests; they do not read the challenge oracle and they do
  not read earlier probe answers.  `preReadGrinder.probe k i h _ _ = (h k, 1,
  Transcript.le 8 i)` satisfies it, as does `echoGrinder`'s and the adopted
  `GrindingQueryBound.grindingOfStrategy`'s.
* `AbsorbPreReadOnly q g` -- the ABSORB may read the challenge oracle at its own
  stage digests `h 0, …, h k` AND at the digests `blockDigest (pa k i)` of its own
  stage's probe answers, and nowhere else.  This is exactly the pre-read channel:
  the absorb is allowed to look at the challenges of a digest the chain has not
  reached, provided that digest is one its own probes just produced.
  `preReadGrinder` satisfies it (it reads `ch (blockDigest (pa k 0)) 0`), and
  `GrindingUnionBound.pre_read_grinder_not_challenge_restricted` is the adopted
  proof that this class is NOT inside GUB's.

So the class is not a restriction of GUB's class: it is a different one, and the
prover GUB excludes lies in it.  `grinding_of_strategy_probe_history_only` and
`grinding_of_strategy_absorb_pre_read_only` put every adopted
`StrategyChainBound.Strategy`, lifted, in it as well.

## What is proved

1. THE PROBE DIGEST FAMILY (section 1).  `probeAnswerAt … k i T` is the oracle's
   answer at probe `i` of stage `k`, `probeDigestAt` its `blockDigest`, and
   `probeDigestFam` the constant abstract digest family GUB's section 1 is
   quantified over.  `probe_digest_at_absorb` records that the family at the
   absorb slot `i = q` IS the chain's next stage digest, which is the sense in
   which "the round the prover reaches" is one of the digests it probed.
2. THE PROBE-SEPARATION EVENT (section 3).  `probeFresh … k i` is the event that
   probe `i` of stage `k` produced a digest different from every stage digest up
   to `k` and from every earlier probe's digest.  Every clash it excludes is a
   collision between two positions of the interleaved sequence, which the adopted
   `GrindingQueryBound.grinding_chain_clash_probability_le` charges at
   `N (N + 1) / 2 / |Block|` with `N = n (q + 1)` -- `pre_read_separation_charged`
   (section 7) establishes every PROBE slot's separation from the complements of
   those two adopted events, so the conditioning is charged, not assumed away.
   `pre_read_absorb_digest_charged` (section 7) is the DICHOTOMY at the absorb
   slot, with no hypothesis on which branch the prover takes: on the same two
   adopted events, either the absorb slot is itself separated, or the digest round
   `k + 1`'s challenges are squeezed at is the digest of one of the stage's `q`
   probes AND that probe's slot is separated.  Either way the realized round
   digest sits in a slot section 6 charges; that is the general form of "charging
   the probes charges the attack", replacing the favourable-branch statement
   `pre_read_grinder_round_digest_is_probe_digest`.
3. THE TWO-STEP FRESH PEEL (sections 3 and 4).  `pre_read_run_ans_stable` is the
   causal induction: on `probeFresh … k i`, overwriting the table at ANY challenge
   input of the probed digest leaves every answer of the run up to and including
   probe `i` of stage `k` exactly where it was.  That is where
   `AbsorbPreReadOnly` is used and where the separation clauses are consumed:
   an earlier absorb reads the challenge oracle only at digests the event
   separates from the probed one.  `pre_read_chain_stable_all` packages it as
   GUB's `ChainStableAll`, and `pre_read_probe_mass_le` is then GUB's
   `chain_triple_target_mass_le` at the probe digest family:

     `oracleProbability Q ((probeFresh … k i).filter (fun T =>`
       `chainTriple L hL (probeDigestFam … k i) 0 base T ∈ targ T))`
       `≤ m / |DigestTriple|`

   for any target family the conditioning event cannot move, of size at most `m`.
   THIS IS THE ITEM THE HEADER PROMISED: the challenge triple at a probed digest
   is uniform on the separation event, so one probe buys one draw, not a free one.
4. THE CANDIDATE BAD SETS AND THE `(q + 1)` FACTOR (sections 5 and 6).  A
   `CandidateFamily` is a map `r i ↦` the round-`r` message the prover would
   submit if it kept probe `i`; `preReadCandTarget` is the adopted
   `ConditionalSoundness.roundBadSet` at that candidate, pulled back to digest
   triples by the adopted `OuterChallenge.tupleEvent`, and
   `pre_read_cand_target_reassign` proves it is unmoved by the probed digest's own
   challenge cells -- the candidates are fixed before the probe answers arrive.
   The causality asked of a candidate is `CandidateProbeCausal`, the LOOSE cut:
   the run's answers up to the candidate's OWN slot `slotPos (probeStage r) i` and
   the challenge view up to stage `probeStage r = 26 + 5 r`.  That is the cut the
   stability lemmas `pre_read_run_view_stable` and `pre_read_table_view_stable`
   support, and it covers everything `ProbeHistoryOnly` lets a stage-`26 + 5 r`
   probe payload depend on.  `CandidateCausal`, which inherits GUB's `GrindCausal`
   cut (`(22 + 5 r + 1) (q + 1)` answers, challenge view to stage `22 + 5 r`), is
   strictly tighter and is included by `candidate_probe_causal_of_causal`.  The
   LANE's own message and truth still carry GUB's cut, because
   `pre_read_raw_claims_stable` runs the adopted `GrindLaneCausal` unchanged.
   `pre_read_round_mass_le` sums the `q` probes and the absorb:

     `≤ ((q + 1) * (bd * fiberCeiling ^ 3)) / |DigestTriple|`,

   and `pre_read_outer_mass_le` sums the rounds to `(q + 1) * outerTerm d quo`.
5. THE CLOSED INSTANCE (section 8).  At the envelope `d = 13`, `quo = 8` and
   `q = 2 ^ 20`, `pre_read_outer_bound_at_thirteen_many_probes_lt_one` gives a
   constant below one, and `pre_read_grinder_in_class` puts the attacker of GUB's
   section 10 inside the class the bound is stated for.

## HONESTY

(i) RANDOM ORACLE, NOT KECCAK.  Every statement is about a uniformly random table
on `boundedQueries L`; no property of the deployed permutation is used or implied.

(ii) THE PROVER MODEL IS THE ADOPTED `GrindingQueryBound.GrindingStrategy`: `q`
frame-shaped probes per stage and one absorb, sequenced by the adopted `slotPos`.
The two hypotheses of section 2 are hypotheses, not theorems, and they are
SATISFIED BY `preReadGrinder` and `echoGrinder` -- each is exhibited, so nothing
below is vacuous.  They are also strictly weaker than the adopted
`GrindingUnionBound.ChallengeRestricted` in the direction that matters: the prover
that hypothesis excludes is in this class, by the adopted
`pre_read_grinder_not_challenge_restricted`.  They are NOT weaker in every
direction: a prover whose PROBES read the challenge oracle, or whose absorb reads
it at a digest neither its own chain nor its own stage's probes produced, is in
neither class.

(iii) WHAT THE `(q + 1)` COVERS.  It covers the pre-read channel: the round's
challenge triple is read at a digest the prover probed, and each of the `q + 1`
slots of the round's stage is charged one per-round term.  It does NOT cover a
prover that probes across stages and pairs a probe of stage `k` with an absorb of
stage `k' ≠ k`; `AbsorbPreReadOnly` confines the absorb's pre-read to its OWN
stage's probes, and `probeFresh` separates only the digests that confinement
needs.

(iv) THE PAIRING IS STILL OPEN, AND THE OBSTRUCTION IS STRUCTURAL, NOT ONLY A
MISSING DECODER.  The lane's round message and the candidate family are quantified
SEPARATELY from the strategy: no `grindLaneOfGrinder` carrying the grinder's
realized absorb payload as a `List Element` is built here, and GUB's HONESTY (v)
reason -- no bytes-to-elements decoder for the payload -- still applies.  BUT A
DECODER WOULD NOT SUFFICE, and this module makes the reason precise.

The adopted `GrindingUnionBound.GrindLane` hands `message` and `truth` exactly two
views: `grindRunView` (the frame ANSWERS of the interleaved sequence) and
`grindTableView`, which is the challenge oracle AT STAGE DIGESTS ONLY,
`fun j cnt => T (chainChallengeSel … (grindState …) j cnt T)`.  The pre-read
grinder's absorb reads `challengesOf T (probeDigestAt … k 0 T) 0`.  On the
UNFAVOURABLE branch that is a cell at a digest which is no stage digest at all --
on `probeFresh` it is separated from every one of them -- so no `grindTableView`
argument can present it.  On the FAVOURABLE branch the absorb repeats probe `0`,
so the digest IS `grindState … (roundStage r) T` and the cell is
`grindTableView T (roundStage r) 0`; but `roundStage r = 27 + 5 r` lies ABOVE
`GrindCausal`'s cut `j ≤ 22 + 5 r`, so no `GrindLaneCausal` lane may read it
either.  Hence, even given a decoder,

  (i) NO `GrindLane` CAN CARRY THE GRINDER'S REALIZED ROUND MESSAGE, and
  (ii) NO `GrindLaneCausal` LANE CAN CARRY THE REALIZED RUNNING CLAIMS at rounds
       `< r` -- and `preReadCandTarget` takes those claims from `lane.message`
       through `grindRawClaims`, so the candidate family repairs round `r`'s OWN
       message and nothing else.

A genuine pre-read run's claims would need a SELECTED-CANDIDATE RECURSION over the
full `challengesOf` oracle -- claims at round `r` built from whichever candidate
each earlier round's absorb actually selected, with the selection reading
challenges at probe digests.  Nothing below builds that.  The machinery would go
through: `probeFresh` separates earlier probe digests and stage digests, which is
what such a recursion's diagonal step needs; but it is not built, and until it is,
the theorems say "for every candidate family the history fixes before the probe,
the probed challenge misses its bad set", NOT "the grinder's own realized message
and claims miss theirs".

(v) OUTER SUMCHECK LANES ONLY.  The block-0 gate tau and gate alpha lanes, the
index lanes, WHIR folding and the Merkle openings are not covered; no round
schedule is threaded onto the grinding chain.

(vi) THE SEPARATION EVENT IS CHARGED BY THE ADOPTED ALL-PAIRS TERM AND BY NOTHING
SHARPER, AND ONLY AT THE PROBE SLOTS.  `pre_read_separation_charged` derives
`probeFresh … k i` for `i < q` from the adopted `grindingNoClash` and
`distinctNoClash` events, whose complements the adopted
`grinding_chain_clash_probability_le` and `distinct_answer_clash_probability_le`
bound at `N (N + 1) / 2 / |Block|` with `N = n (q + 1)` -- quadratic in `q`, and
no better constant is proved.  IT IS NOT PROVED FOR THE ABSORB SLOT `i = q`, and
it is false there for a probe-then-absorb prover: the absorb repeats a probe's
byte string, so the two slots share a digest and the separation fails.
`pre_read_repeat_digest_eq` and `pre_read_grinder_round_digest_is_probe_digest`
say what happens instead -- the round's realized digest is then the repeated
PROBE's digest, which is a slot section 6 does charge, and
`pre_read_absorb_digest_charged` is the general dichotomy: on the same two events
either the absorb slot IS separated or the round's digest is a separated probe
slot's.  So the "+1" slot is the FRESH-ABSORB case only.  It is uncharged, and for
the two provers exhibited it is EMPTY: `pre_read_absorb_slot_never_fresh` (at
`q ≥ 2`, either branch) and `echo_absorb_slot_never_fresh` (at `q ≥ 1`) show their
absorb always repeats a probe of its own stage, so slot `q`'s term of
`preReadRoundEvent` is the mass of the empty set for them and the "+1" buys
nothing there.  No theorem below adds the clash constant and the
`(q + 1) outerTerm` into one number.  The probe budget `q` is a parameter, never a
cap, and `q + 1` is an upper factor with no matching lower bound.

(vii) NOT A SOUNDNESS ERROR AND NOT ADAPTIVE FIAT--SHAMIR SOUNDNESS.  The masses
below are the masses of specific bad-draw events along a grinding chain in the
random oracle model.  They are not the system's soundness error, they do not
aggregate into one, and no statement below is or implies an adaptive
Fiat--Shamir soundness theorem for the protocol.

(viii) `Finset.univ` APPEARS IN EXACTLY ONE DEFINITION OF THIS MODULE,
`probeFresh`, where it cuts a cylinder out of the table space exactly as the
adopted `RawBlockLanes.rawRoundBadEvent` and
`GrindingUnionBound.grindRawRoundBadEvent` do; every other event below is a
`filter` or a `biUnion` of it.  No cardinality of `Element`, `Block` or
`OuterChallenge.DigestTriple` is evaluated numerically or handed to a `ring` or
`omega` goal: the only `ring` goals of this module are over abstract rational
variables, and `Fintype.card OuterChallenge.DigestTriple` never appears in one.
-/

namespace Audit.Wire3.PreReadCharge

open Audit.Wire3
open Audit.Wire3.GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport
open Audit.Wire3.RawBlockLanes
open Audit.Wire3.GrindingQueryBound
open Audit.Wire3.GrindingUnionBound

/-! ## 1. THE PROBE DIGEST FAMILY -/

/-- **THE ORACLE'S ANSWER TO PROBE `i` OF STAGE `k`.**  Position `slotPos q k i`
of the adopted interleaved sequence, read at the table `T`. -/
def probeAnswerAt (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k i : Nat)
    (T : OracleTable (boundedQueries L)) : Block :=
  T (grindSelSeq L hL e0 q g hb (slotPos q k i) T)

/-- **THE DIGEST OF THAT ANSWER.**  This is the digest the pre-read prover
evaluates the challenge oracle at: the adopted
`GrindingUnionBound.preReadGrinder` reads `ch (blockDigest (pa k 0)) 0`. -/
def probeDigestAt (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k i : Nat)
    (T : OracleTable (boundedQueries L)) : Transcript.Digest :=
  blockDigest (probeAnswerAt L hL e0 q g hb k i T)

/-- **THE PROBE DIGEST AS AN ABSTRACT DIGEST FAMILY.**  The adopted
`GrindingUnionBound.chainChallengeSel` and everything built on it are quantified
over a family `Nat -> OracleTable -> Digest`; this one is constant in the stage
argument, because the challenge cells charged below all sit at ONE digest. -/
def probeDigestFam (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k i : Nat) :
    Nat → OracleTable (boundedQueries L) → Transcript.Digest :=
  fun _ T => probeDigestAt L hL e0 q g hb k i T

/-- (1) **THE ABSORB SLOT OF STAGE `k` CARRIES THE CHAIN'S NEXT DIGEST.**  Slot `q`
of stage `k` is the absorb, so the family at that slot IS `grindState (k + 1)`:
the digest round `k + 1`'s challenges are squeezed at is one of the digests the
stage produced.  This is why charging the probes charges the attack. -/
theorem probe_digest_at_absorb (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    probeDigestAt L hL e0 q g hb k q T = grindState L hL e0 q g hb (k + 1) T := rfl

/-- (1) The challenge query the family names is the challenge input at the probed
digest. -/
theorem pre_read_sel_val (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k i j c : Nat)
    (T : OracleTable (boundedQueries L)) :
    (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) j c T).val
      = Transcript.challengeInput (probeDigestAt L hL e0 q g hb k i T) c := rfl

/-! ## 2. THE PROVER CLASS: HISTORY-ONLY PROBES, PRE-READING ABSORBS -/

/-- **THE PROBES ARE A FUNCTION OF THE STAGE DIGESTS ALONE.**  Probe `i` of stage
`k` may be framed at any digest the prover computes from `h`, with any tag and
payload, but it reads neither the challenge oracle nor the earlier probe answers.
The adopted `GrindingUnionBound.preReadGrinder` and `echoGrinder` satisfy this,
and so does the adopted `GrindingQueryBound.grindingOfStrategy`. -/
def ProbeHistoryOnly (g : GrindingStrategy) : Prop :=
  ∀ (k i : Nat) (h : Nat → Transcript.Digest)
      (ch1 ch2 : Transcript.Digest → Nat → Block) (pa1 pa2 : Nat → Nat → Block),
    g.probe k i h ch1 pa1 = g.probe k i h ch2 pa2

/-- **THE ABSORB MAY PRE-READ ITS OWN STAGE'S PROBES.**  Stage `k`'s absorb
depends on the challenge oracle only through its values at the stage digests
`h 0, …, h k` -- what the adopted `StrategyChainBound.Strategy` is handed -- AND at
the digests `blockDigest (pa k i)` of the `q` probe answers of ITS OWN STAGE.  The
second clause is the pre-read channel, and it is what the adopted
`GrindingUnionBound.ChallengeRestricted` forbids: with it the absorb is allowed to
choose the round's message after looking at the challenges of a digest the chain
has not reached. -/
def AbsorbPreReadOnly (q : Nat) (g : GrindingStrategy) : Prop :=
  ∀ (k : Nat) (h : Nat → Transcript.Digest)
      (ch1 ch2 : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block),
    (∀ j, j ≤ k → ch1 (h j) = ch2 (h j)) →
    (∀ i, i < q → ch1 (blockDigest (pa k i)) = ch2 (blockDigest (pa k i))) →
      g.absorb k h ch1 pa = g.absorb k h ch2 pa

/-- (2) **THE ATTACKER GUB EXCLUDES IS IN THIS CLASS: PROBES.** -/
theorem pre_read_grinder_probe_history_only : ProbeHistoryOnly preReadGrinder :=
  fun _ _ _ _ _ _ _ => rfl

/-- (2) **THE ATTACKER GUB EXCLUDES IS IN THIS CLASS: ABSORB.**  Its absorb reads
the challenge oracle at exactly one digest, `blockDigest (pa k 0)`, and slot `0`
is a probe as soon as there is one. -/
theorem pre_read_grinder_absorb_pre_read_only (q : Nat) (hq : 0 < q) :
    AbsorbPreReadOnly q preReadGrinder := by
  classical
  intro k h ch1 ch2 pa _ hpa
  show ((1 : Transcript.Byte),
      if ch1 (blockDigest (pa k 0)) 0 = preReadTarget then Transcript.le 8 0
      else Transcript.le 8 1)
    = ((1 : Transcript.Byte),
      if ch2 (blockDigest (pa k 0)) 0 = preReadTarget then Transcript.le 8 0
      else Transcript.le 8 1)
  rw [congrFun (hpa 0 hq) 0]

/-- (2) The echo prover of GUB's section 10 is in the class too. -/
theorem echo_grinder_probe_history_only : ProbeHistoryOnly echoGrinder :=
  fun _ _ _ _ _ _ _ => rfl

theorem echo_grinder_absorb_pre_read_only (q : Nat) : AbsorbPreReadOnly q echoGrinder :=
  fun _ _ _ _ _ _ _ => rfl

/-- (2) **EVERY ADOPTED TRANSCRIPT-RESTRICTED PROVER, LIFTED, IS IN THE CLASS.**
Its probes are the constant `(h 0, 0, [])` and its absorb reads the challenge
oracle at `h (min j k)` only, a stage digest at or below its own stage. -/
theorem grinding_of_strategy_probe_history_only (strat : StrategyChainBound.Strategy) :
    ProbeHistoryOnly (grindingOfStrategy strat) :=
  fun _ _ _ _ _ _ _ => rfl

theorem grinding_of_strategy_absorb_pre_read_only (q : Nat)
    (strat : StrategyChainBound.Strategy) :
    AbsorbPreReadOnly q (grindingOfStrategy strat) := by
  intro k h ch1 ch2 _ hch _
  show strat k (fun j => h (min j k)) (fun j c => ch1 (h (min j k)) c)
    = strat k (fun j => h (min j k)) (fun j c => ch2 (h (min j k)) c)
  congr 1
  funext j c
  exact congrFun (hch (min j k) (Nat.min_le_right j k)) c

/-! ## 3. THE SEPARATION EVENT AND THE RUN'S STABILITY -/

open Classical in
/-- **PROBE `i` OF STAGE `k` PRODUCED A DIGEST NOBODY ELSE PRODUCED.**  Its answer
digest differs from every stage digest of stages `0, …, k` and from every probe
digest of every earlier stage.  `Finset.univ` cuts the cylinder out of the table
space, as the adopted event definitions do.

EVERY CLASH THIS EVENT EXCLUDES IS CHARGED: `pre_read_separation_charged` shows
this event is implied by the adopted `GrindingQueryBound` no-clash events of the
run's own interleaved sequence (`grindingNoClash` and `distinctNoClash`), whose
complements the adopted `grinding_chain_clash_probability_le` and
`distinct_answer_clash_probability_le` bound at `N (N + 1) / 2 / |Block|`. -/
noncomputable def probeFresh (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k i : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    (∀ j, j ≤ k → grindState L hL e0 q g hb j T ≠ probeDigestAt L hL e0 q g hb k i T) ∧
    (∀ k2 i2, i2 < q → slotPos q k2 i2 < slotPos q k i →
      probeDigestAt L hL e0 q g hb k2 i2 T ≠ probeDigestAt L hL e0 q g hb k i T))

theorem mem_probe_fresh (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k i : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ probeFresh L hL e0 q g hb k i ↔
      ((∀ j, j ≤ k → grindState L hL e0 q g hb j T ≠ probeDigestAt L hL e0 q g hb k i T) ∧
       (∀ k2 i2, i2 < q → slotPos q k2 i2 < slotPos q k i →
         probeDigestAt L hL e0 q g hb k2 i2 T ≠ probeDigestAt L hL e0 q g hb k i T)) := by
  classical
  rw [probeFresh, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ T, h⟩⟩

/-- (3) Overwriting the table at a challenge input of one digest leaves the whole
challenge oracle at every OTHER digest alone.  The adopted
`StrategyChainBound.challenge_input_digest_eq` is what separates them. -/
theorem challenges_of_reassign_digest_ne (L : Nat) (hL : 64 ≤ L)
    (T : OracleTable (boundedQueries L)) (d : Transcript.Digest) (c : Nat) (b : Block)
    (e : Transcript.Digest) (hne : e ≠ d) :
    challengesOf L hL
        (reassign T ⟨Transcript.challengeInput d c, bounded_queries_challenge L hL d c⟩ b) e
      = challengesOf L hL T e := by
  funext c2
  show (reassign T ⟨Transcript.challengeInput d c, bounded_queries_challenge L hL d c⟩ b)
      ⟨Transcript.challengeInput e c2, bounded_queries_challenge L hL e c2⟩
    = T ⟨Transcript.challengeInput e c2, bounded_queries_challenge L hL e c2⟩
  refine reassign_off T _ _ b ?_
  intro hEq
  exact hne (StrategyChainBound.challenge_input_digest_eq _ _ _ _ (congrArg Subtype.val hEq))

/-- (3) **THE RUN UP TO PROBE `i` OF STAGE `k` DOES NOT LOOK AT THE CHALLENGES OF
THE DIGEST THAT PROBE PRODUCES.**  The causal induction over all `slotPos q k i`
earlier positions.  Every position asks a FRAME, never a challenge input, so the
answer cells are untouched; a PROBE reads no challenge at all
(`ProbeHistoryOnly`); an earlier ABSORB reads the challenge oracle only at its own
stage digests and at its own stage's probe digests (`AbsorbPreReadOnly`), and the
separation event puts all of those away from the probed digest.

This is the FIRST of the two peels the header promises: it is what makes the three
challenge cells at the probed digest cells the conditioning event cannot move. -/
theorem pre_read_run_ans_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) :
    ∀ m : Nat, m ≤ slotPos q k i + 1 →
      runAns L hL e0 q g hb m
          (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
        = runAns L hL e0 q g hb m T := by
  classical
  obtain ⟨hst, hpr⟩ := (mem_probe_fresh L hL e0 q g hb k i T).mp hT
  intro m
  induction m with
  | zero => intro _; funext m2; rfl
  | succ m2 ih =>
      intro hm
      have hprev := ih (by omega)
      have hmlt : m2 ≤ slotPos q k i := by omega
      have hsel : grindSelSeq L hL e0 q g hb m2
            (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
          = grindSelSeq L hL e0 q g hb m2 T := by
        apply Subtype.ext
        show grindBytes e0 q g (runAns L hL e0 q g hb m2
              (reassign T (chainChallengeSel L hL
                (probeDigestFam L hL e0 q g hb k i) 0 c T) b))
            (challengesOf L hL (reassign T (chainChallengeSel L hL
              (probeDigestFam L hL e0 q g hb k i) 0 c T) b)) m2
          = grindBytes e0 q g (runAns L hL e0 q g hb m2 T) (challengesOf L hL T) m2
        rw [hprev]
        unfold grindBytes
        have hq : grindQuery e0 q g (runAns L hL e0 q g hb m2 T)
              (challengesOf L hL (reassign T (chainChallengeSel L hL
                (probeDigestFam L hL e0 q g hb k i) 0 c T) b)) m2
            = grindQuery e0 q g (runAns L hL e0 q g hb m2 T) (challengesOf L hL T) m2 := by
          unfold grindQuery
          by_cases hpb : m2 % (q + 1) < q
          · rw [if_pos hpb, if_pos hpb]
            exact hpo _ _ _ _ _ _ _
          · rw [if_neg hpb, if_neg hpb]
            have hmod : m2 % (q + 1) = q := by
              have := Nat.mod_lt m2 (show 0 < q + 1 by omega)
              omega
            have hdm : (q + 1) * (m2 / (q + 1)) + m2 % (q + 1) = m2 :=
              Nat.div_add_mod m2 (q + 1)
            have hcomm : (q + 1) * (m2 / (q + 1)) = m2 / (q + 1) * (q + 1) :=
              Nat.mul_comm _ _
            have hslot : m2 ≤ k * (q + 1) + i := hmlt
            have hexpk : (k + 1) * (q + 1) = k * (q + 1) + (q + 1) := by ring
            have hkey : m2 / (q + 1) ≤ k := by
              by_contra hcon
              have hge : (k + 1) * (q + 1) ≤ m2 / (q + 1) * (q + 1) :=
                Nat.mul_le_mul_right _ (by omega)
              omega
            refine congrArg (fun z => (stateOf e0 q (runAns L hL e0 q g hb m2 T)
              (m2 / (q + 1)), z)) ?_
            refine hab (m2 / (q + 1)) (stateOf e0 q (runAns L hL e0 q g hb m2 T)) _ _
              (probeAnsOf q (runAns L hL e0 q g hb m2 T)) ?_ ?_
            · intro j hj
              have hstate : stateOf e0 q (runAns L hL e0 q g hb m2 T) j
                  = grindState L hL e0 q g hb j T := by
                refine state_of_run_ans_le L hL e0 q g hb m2 j (fun j2 hj2 => ?_) T
                rw [slotPos]
                have hjle : j2 + 1 ≤ m2 / (q + 1) := by omega
                have hmul : (j2 + 1) * (q + 1) ≤ m2 / (q + 1) * (q + 1) :=
                  Nat.mul_le_mul_right _ hjle
                have hexp : (j2 + 1) * (q + 1) = j2 * (q + 1) + (q + 1) := by ring
                omega
              rw [hstate]
              exact challenges_of_reassign_digest_ne L hL T _ c b _
                (hst j (le_trans hj hkey))
            · intro i2 hi2
              have hpos : slotPos q (m2 / (q + 1)) i2 < m2 := by
                rw [slotPos]
                omega
              have hans : probeAnsOf q (runAns L hL e0 q g hb m2 T) (m2 / (q + 1)) i2
                  = probeAnswerAt L hL e0 q g hb (m2 / (q + 1)) i2 T := by
                show runAns L hL e0 q g hb m2 T (slotPos q (m2 / (q + 1)) i2) = _
                rw [run_ans_eq, if_pos hpos]
                rfl
              rw [hans]
              exact challenges_of_reassign_digest_ne L hL T _ c b _
                (hpr (m2 / (q + 1)) i2 hi2 (lt_of_lt_of_le hpos hmlt))
        rw [hq]
      funext m3
      rw [run_ans_succ, run_ans_succ, hsel, hprev]
      by_cases h3 : m3 = m2
      · rw [if_pos h3, if_pos h3]
        refine reassign_off T _ _ b ?_
        intro hEq
        exact frame_ne_challenge_input _ _ _ _ _ (congrArg Subtype.val hEq)
      · rw [if_neg h3, if_neg h3]

/-- (3) One answer of the run, read off the stability induction. -/
theorem pre_read_chain_val_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) (p : Nat) (hp : p ≤ slotPos q k i) :
    (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
        (grindSelSeq L hL e0 q g hb p
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb k i) 0 c T) b))
      = T (grindSelSeq L hL e0 q g hb p T) := by
  have h := pre_read_run_ans_stable L hL e0 q g hb hpo hab k i c hi T hT b (p + 1) (by omega)
  have hv := congrFun h p
  rw [run_ans_succ, run_ans_succ, if_pos rfl, if_pos rfl] at hv
  exact hv

/-- (3) The stage digests up to `k` are unmoved by the probed digest's challenge
cells. -/
theorem pre_read_state_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) (j : Nat) (hj : j ≤ k) :
    grindState L hL e0 q g hb j
        (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
      = grindState L hL e0 q g hb j T := by
  cases j with
  | zero => rfl
  | succ j2 =>
      have hp : slotPos q j2 q ≤ slotPos q k i := by
        rw [slotPos, slotPos]
        have hmul : (j2 + 1) * (q + 1) ≤ k * (q + 1) := Nat.mul_le_mul_right _ hj
        have hexp : (j2 + 1) * (q + 1) = j2 * (q + 1) + (q + 1) := by ring
        omega
      show blockDigest (_) = blockDigest (_)
      exact congrArg blockDigest
        (pre_read_chain_val_stable L hL e0 q g hb hpo hab k i c hi T hT b (slotPos q j2 q) hp)

/-- (3) Every probe digest at or before probe `i` of stage `k` -- the probed digest
itself included -- is unmoved. -/
theorem pre_read_probe_digest_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) (k2 i2 : Nat) (hp : slotPos q k2 i2 ≤ slotPos q k i) :
    probeDigestAt L hL e0 q g hb k2 i2
        (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
      = probeDigestAt L hL e0 q g hb k2 i2 T :=
  congrArg blockDigest
    (pre_read_chain_val_stable L hL e0 q g hb hpo hab k i c hi T hT b (slotPos q k2 i2) hp)

/-- (3) **THE SEPARATION EVENT IS STABLE AT EVERY COUNTER OF THE PROBED DIGEST.**
GUB's `ChainStableAll` at the probe digest family: the family does not move, and
the event is closed under the overwriting.  This is the hypothesis GUB's abstract
counting layer asks for, discharged here WITHOUT `ChallengeRestricted`. -/
theorem pre_read_chain_stable_all (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i : Nat) (hi : i ≤ q) :
    ChainStableAll L hL (probeDigestFam L hL e0 q g hb k i) 0
      (probeFresh L hL e0 q g hb k i) := by
  classical
  have hself : slotPos q k i ≤ slotPos q k i := le_refl _
  refine ⟨fun T hT c b => ?_, fun T hT c b => ?_⟩
  · exact pre_read_probe_digest_stable L hL e0 q g hb hpo hab k i c hi T hT b k i hself
  · obtain ⟨hst, hpr⟩ := (mem_probe_fresh L hL e0 q g hb k i T).mp hT
    have hd := pre_read_probe_digest_stable L hL e0 q g hb hpo hab k i c hi T hT b k i hself
    rw [mem_probe_fresh]
    refine ⟨fun j hj => ?_, fun k2 i2 hk2 hi2 => ?_⟩
    · rw [pre_read_state_stable L hL e0 q g hb hpo hab k i c hi T hT b j hj, hd]
      exact hst j hj
    · have hp : slotPos q k2 i2 ≤ slotPos q k i := le_of_lt hi2
      rw [pre_read_probe_digest_stable L hL e0 q g hb hpo hab k i c hi T hT b k2 i2 hp, hd]
      exact hpr k2 i2 hk2 hi2

/-! ## 4. THE FRESH STEP AT THE PROBE -/

/-- (4) **THE CHALLENGE TRIPLE AT A PROBED DIGEST IS UNIFORM ON THE SEPARATION
EVENT.**  For ANY target family the probed digest's own challenge cells cannot
move, of size at most `m`, the triple read at the probed digest lands in it with
mass at most `m / |DigestTriple|`.

This is the second peel, and the theorem the module exists for: ONE PROBE BUYS ONE
DRAW.  The adopted `GrindingUnionBound.chain_triple_target_mass_le` is applied at
the abstract family `probeDigestFam`, which is not the grinding chain and which
the adopted module never instantiates. -/
theorem pre_read_probe_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i : Nat) (hi : i ≤ q) (base : Nat)
    (hbase : base + 2 < Transcript.u64Limit)
    (targ : OracleTable (boundedQueries L) → Finset OuterChallenge.DigestTriple)
    (hinv : ∀ T ∈ probeFresh L hL e0 q g hb k i, ∀ c ∈ tripleCounters base, ∀ b : Block,
      targ (reassign T (chainChallengeSel L hL
        (probeDigestFam L hL e0 q g hb k i) 0 c T) b) = targ T)
    (m : Nat) (hm : ∀ T ∈ probeFresh L hL e0 q g hb k i, (targ T).card ≤ m) :
    oracleProbability (boundedQueries L)
        ((probeFresh L hL e0 q g hb k i).filter (fun T =>
          chainTriple L hL (probeDigestFam L hL e0 q g hb k i) 0 base T ∈ targ T))
      ≤ (m : ℚ) / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  chain_triple_target_mass_le L hL (probeDigestFam L hL e0 q g hb k i) 0 base hbase
    (probeFresh L hL e0 q g hb k i)
    (chain_stable_of_all L hL (probeDigestFam L hL e0 q g hb k i) 0 (tripleCounters base)
      (probeFresh L hL e0 q g hb k i)
      (pre_read_chain_stable_all L hL e0 q g hb hpo hab k i hi))
    targ hinv m hm

/-! ## 5. THE ROUND'S PROBED DIGESTS, AND THE LANE DATA THEY CANNOT MOVE -/

/-- **THE STAGE WHOSE `q + 1` SLOTS CARRY ROUND `r`'s CHALLENGE DIGEST.**  The
adopted `OuterLaneTransport.roundStage r` is the stage round `r`'s challenge
triple is squeezed at, and `probeStage r + 1 = roundStage r`: it is stage
`probeStage r`'s ABSORB that advances the chain to that digest.  So slot `q` of
stage `probeStage r` is the digest round `r` is actually squeezed at
(`probe_digest_at_round_stage`), and the other `q` slots are the digests the
prover probed at that stage and could have absorbed instead. -/
def probeStage (r : Nat) : Nat := 26 + 5 * r

theorem probe_stage_succ (r : Nat) : probeStage r + 1 = roundStage r := by
  rw [probeStage, roundStage]
  omega

/-- (5) **SLOT `q` OF THE PROBE STAGE IS ROUND `r`'s OWN CHALLENGE DIGEST.** -/
theorem probe_digest_at_round_stage (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    probeDigestAt L hL e0 q g hb (probeStage r) q T
      = grindState L hL e0 q g hb (roundStage r) T := by
  rw [probe_digest_at_absorb, probe_stage_succ]

theorem round_stage_le_probe_stage (r2 r : Nat) (h : r2 < r) : roundStage r2 ≤ probeStage r := by
  rw [roundStage, probeStage]
  omega

theorem message_stage_le_probe_stage (r : Nat) : 22 + 5 * r ≤ probeStage r := by
  rw [probeStage]
  omega

theorem grind_run_view_val (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (T : OracleTable (boundedQueries L))
    (m : Nat) :
    grindRunView L hL e0 q g hb T m = T (grindSelSeq L hL e0 q g hb m T) := rfl

theorem grind_table_view_val (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (T : OracleTable (boundedQueries L))
    (j cnt : Nat) :
    grindTableView L hL e0 q g hb T j cnt
      = T (chainChallengeSel L hL (grindState L hL e0 q g hb) j cnt T) := rfl

theorem chain_triple_val (L : Nat) (hL : 64 ≤ L)
    (st : Nat → OracleTable (boundedQueries L) → Transcript.Digest) (j base : Nat)
    (T : OracleTable (boundedQueries L)) :
    chainTriple L hL st j base T
      = (T (chainChallengeSel L hL st j base T),
         T (chainChallengeSel L hL st j (base + 1) T),
         T (chainChallengeSel L hL st j (base + 2) T)) := rfl

/-- (5) **THE RUN'S ANSWERS UP TO THE PROBED SLOT ARE UNMOVED.**  The run half of
the diagonal step, at the widened lane domain of the adopted
`GrindingUnionBound.GrindLane`. -/
theorem pre_read_run_view_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) (m : Nat) (hm : m ≤ slotPos q k i) :
    grindRunView L hL e0 q g hb
        (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b) m
      = grindRunView L hL e0 q g hb T m :=
  pre_read_chain_val_stable L hL e0 q g hb hpo hab k i c hi T hT b m hm

/-- (5) **THE CHALLENGE CELL OF A STAGE AT OR BELOW `k` IS UNMOVED.**  The
separation event puts every such stage digest away from the probed digest, so the
cell the run reads there is a different cell from the one overwritten. -/
theorem pre_read_challenge_cell_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) (j : Nat) (hj : j ≤ k) (cnt : Nat) :
    (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
        (chainChallengeSel L hL (grindState L hL e0 q g hb) j cnt
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb k i) 0 c T) b))
      = T (chainChallengeSel L hL (grindState L hL e0 q g hb) j cnt T) := by
  obtain ⟨hst, -⟩ := (mem_probe_fresh L hL e0 q g hb k i T).mp hT
  have hs := pre_read_state_stable L hL e0 q g hb hpo hab k i c hi T hT b j hj
  have hsel : chainChallengeSel L hL (grindState L hL e0 q g hb) j cnt
        (reassign T (chainChallengeSel L hL
          (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
      = chainChallengeSel L hL (grindState L hL e0 q g hb) j cnt T :=
    Subtype.ext (congrArg (fun d => Transcript.challengeInput d cnt) hs)
  rw [hsel]
  refine reassign_off T _ _ b ?_
  intro hEq
  exact hst j hj
    (StrategyChainBound.challenge_input_digest_eq _ _ _ _ (congrArg Subtype.val hEq))

theorem pre_read_table_view_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) (j : Nat) (hj : j ≤ k) :
    grindTableView L hL e0 q g hb
        (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b) j
      = grindTableView L hL e0 q g hb T j :=
  funext (fun cnt =>
    pre_read_challenge_cell_stable L hL e0 q g hb hpo hab k i c hi T hT b j hj cnt)

theorem pre_read_triple_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (k i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ probeFresh L hL e0 q g hb k i)
    (b : Block) (j : Nat) (hj : j ≤ k) (base : Nat) :
    chainTriple L hL (grindState L hL e0 q g hb) j base
        (reassign T (chainChallengeSel L hL (probeDigestFam L hL e0 q g hb k i) 0 c T) b)
      = chainTriple L hL (grindState L hL e0 q g hb) j base T := by
  rw [chain_triple_val, chain_triple_val,
    pre_read_challenge_cell_stable L hL e0 q g hb hpo hab k i c hi T hT b j hj base,
    pre_read_challenge_cell_stable L hL e0 q g hb hpo hab k i c hi T hT b j hj (base + 1),
    pre_read_challenge_cell_stable L hL e0 q g hb hpo hab k i c hi T hT b j hj (base + 2)]

/-- (5) **THE RUNNING CLAIMS BEFORE A ROUND ARE UNMOVED BY THE PROBED DIGEST'S
CHALLENGE CELLS.**  The grinding analogue of the adopted
`GrindingUnionBound.grind_raw_state_reassign`, at the probe digest family instead
of the chain. -/
theorem pre_read_raw_claims_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (lane : GrindLane) (hcau : GrindLaneCausal q lane)
    (base k i c : Nat) (hi : i ≤ q) (T : OracleTable (boundedQueries L))
    (hT : T ∈ probeFresh L hL e0 q g hb k i) (b : Block) :
    ∀ rr : Nat, (∀ r2, r2 < rr → roundStage r2 ≤ k) →
      grindRawClaims L hL e0 q g hb lane base
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb k i) 0 c T) b) rr
        = grindRawClaims L hL e0 q g hb lane base T rr := by
  intro rr
  induction rr with
  | zero => intro _; rfl
  | succ r2 ih =>
      intro hlt
      have hprev := ih (fun r3 hr3 => hlt r3 (by omega))
      have hr2 : roundStage r2 ≤ k := hlt r2 (by omega)
      have hr2b : 22 + 5 * r2 + 5 ≤ k := by rw [roundStage] at hr2; omega
      have hcut : (22 + 5 * r2 + 1) * (q + 1) ≤ slotPos q k i := by
        have h1 : (22 + 5 * r2 + 1) * (q + 1) ≤ k * (q + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [slotPos]
        omega
      have hrun : ∀ m, m < (22 + 5 * r2 + 1) * (q + 1) →
          grindRunView L hL e0 q g hb
              (reassign T (chainChallengeSel L hL
                (probeDigestFam L hL e0 q g hb k i) 0 c T) b) m
            = grindRunView L hL e0 q g hb T m :=
        fun m hm => pre_read_run_view_stable L hL e0 q g hb hpo hab k i c hi T hT b m
          (le_of_lt (lt_of_lt_of_le hm hcut))
      have htab : ∀ j, j ≤ 22 + 5 * r2 →
          grindTableView L hL e0 q g hb
              (reassign T (chainChallengeSel L hL
                (probeDigestFam L hL e0 q g hb k i) 0 c T) b) j
            = grindTableView L hL e0 q g hb T j :=
        fun j hj => pre_read_table_view_stable L hL e0 q g hb hpo hab k i c hi T hT b j
          (by omega)
      have hmsg := hcau.1 r2 _ _ _ _ hrun htab
      have htr := hcau.2 r2 _ _ _ _ hrun htab
      have htrip := pre_read_triple_stable L hL e0 q g hb hpo hab k i c hi T hT b
        (roundStage r2) hr2 base
      rw [grind_raw_claims_succ, grind_raw_claims_succ, hprev, hmsg, htr, htrip]

/-- **THE CANDIDATE ROUND MESSAGES.**  `cand r i` is the round-`r` message the
prover would submit if it kept probe `i` of the round's probe stage.  The
candidates are functions of the SAME data the lane's own message is: the run's
answers below the round's cut and the challenge view below the round's stage.
That is the formal content of "the candidate payloads are chosen before the probe
answers come back": nothing in a candidate can depend on the challenge triple it
is about to be tested against. -/
def CandidateCausal (q : Nat)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) : Prop :=
  ∀ i : Nat, GrindCausal q (fun r => cand r i)

/-- The adopted degree bound, uniform over the candidates. -/
def CandidateBounded
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (bd : Nat) : Prop :=
  ∀ (r i : Nat) (a : Nat → Block) (ch : Nat → Nat → Block), (cand r i a ch).length ≤ bd

/-- **THE LOOSER CUT: A CANDIDATE MAY READ EVERYTHING ITS OWN SLOT HAS SEEN.**
`CandidateCausal` inherits the adopted `GrindingUnionBound.GrindCausal` cut -- run
answers below `(22 + 5 r + 1) (q + 1)` and challenge view up to stage `22 + 5 r`
-- which is STRICTLY TIGHTER than what `ProbeHistoryOnly` permits a stage-`26 + 5
r` probe payload to depend on.  This predicate is the cut the stability lemmas
actually support: the run's answers up to the candidate's OWN slot
`slotPos q (probeStage r) i` (`pre_read_run_view_stable`) and the challenge view
up to stage `probeStage r` (`pre_read_table_view_stable`).  It is a WEAKER
requirement, so the class of candidate families covered is strictly larger;
`candidate_probe_causal_of_causal` is the inclusion, and section 6 is stated at
this cut throughout. -/
def CandidateProbeCausal (q : Nat)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) : Prop :=
  ∀ (r i : Nat) (a1 a2 : Nat → Block) (ch1 ch2 : Nat → Nat → Block),
    (∀ m, m ≤ slotPos q (probeStage r) i → a1 m = a2 m) →
    (∀ j, j ≤ probeStage r → ch1 j = ch2 j) → cand r i a1 ch1 = cand r i a2 ch2

/-- (5) **THE TIGHT CUT IMPLIES THE LOOSE ONE.**  Everything stated at
`CandidateCausal` -- `laneCandidates` included -- is covered by the loose cut. -/
theorem candidate_probe_causal_of_causal (q : Nat)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (h : CandidateCausal q cand) : CandidateProbeCausal q cand := by
  intro r i a1 a2 ch1 ch2 ha hch
  have hcut : (22 + 5 * r + 1) * (q + 1) ≤ slotPos q (probeStage r) i := by
    have h1 : (22 + 5 * r + 1) * (q + 1) ≤ probeStage r * (q + 1) :=
      Nat.mul_le_mul_right _ (by rw [probeStage]; omega)
    rw [slotPos]
    omega
  exact h i r a1 a2 ch1 ch2 (fun m hm => ha m (by omega))
    (fun j hj => hch j (le_trans hj (message_stage_le_probe_stage r)))

/-- **EVERY LANE SUPPLIES A CANDIDATE FAMILY**: the constant one, which submits
the lane's own round message whatever the probe.  It witnesses that the two
hypotheses above are satisfiable together with any lane's. -/
def laneCandidates (lane : GrindLane) :
    Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  fun r _ a ch => lane.message r a ch

theorem lane_candidates_causal (q : Nat) (lane : GrindLane) (h : GrindLaneCausal q lane) :
    CandidateCausal q (laneCandidates lane) :=
  fun _ r a1 a2 ch1 ch2 ha hch => h.1 r a1 a2 ch1 ch2 ha hch

theorem lane_candidates_bounded (lane : GrindLane) (bd : Nat) (h : GrindLaneBounded lane bd) :
    CandidateBounded (laneCandidates lane) bd :=
  fun r _ a ch => (h r a ch).1

/-- **ROUND `r`'s BAD SET AT THE CANDIDATE PROBE `i` CARRIES.**  The adopted
`ConditionalSoundness.roundBadSet` at the running claims the lane's own history
has produced and at the candidate message, pulled back to digest triples by the
adopted `OuterChallenge.tupleEvent`. -/
noncomputable def preReadCandTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (base r i : Nat) (T : OracleTable (boundedQueries L)) : Finset OuterChallenge.DigestTriple :=
  OuterChallenge.tupleEvent
    (ConditionalSoundness.roundBadSet (grindRawClaims L hL e0 q g hb lane base T r).1
      (grindRawClaims L hL e0 q g hb lane base T r).2
      ⟨cand r i (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T),
       lane.truth r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T), 0⟩)

/-- (5) **THE ADOPTED PER-ROUND CARDINALITY BOUND, REUSED VERBATIM.** -/
theorem pre_read_cand_target_card_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (bd : Nat)
    (hlb : GrindLaneBounded lane bd) (hcb : CandidateBounded cand bd) (base r i : Nat)
    (T : OracleTable (boundedQueries L)) :
    (preReadCandTarget L hL e0 q g hb lane cand base r i T).card
      ≤ bd * OuterChallenge.fiberCeiling ^ 3 :=
  ConditionalSoundness.round_bad_triples_card _ _ _ bd
    (hcb r i (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T))
    (hlb r (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T)).2

/-- (5) **THE CANDIDATE BAD SET IS UNMOVED BY THE PROBED DIGEST'S OWN CHALLENGE
CELLS.**  This is the diagonal hypothesis, at the probe digest family: the
candidate the prover would submit if it kept probe `i` is fixed before the
challenge at that probe's digest is looked at. -/
theorem pre_read_cand_target_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (lane : GrindLane) (hcau : GrindLaneCausal q lane)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (hccau : CandidateProbeCausal q cand) (base r i c : Nat) (hi : i ≤ q)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ probeFresh L hL e0 q g hb (probeStage r) i) (b : Block) :
    preReadCandTarget L hL e0 q g hb lane cand base r i
        (reassign T (chainChallengeSel L hL
          (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 c T) b)
      = preReadCandTarget L hL e0 q g hb lane cand base r i T := by
  have hcut : (22 + 5 * r + 1) * (q + 1) ≤ slotPos q (probeStage r) i := by
    have h1 : (22 + 5 * r + 1) * (q + 1) ≤ probeStage r * (q + 1) :=
      Nat.mul_le_mul_right _ (by rw [probeStage]; omega)
    rw [slotPos]
    omega
  have hrun : ∀ m, m < (22 + 5 * r + 1) * (q + 1) →
      grindRunView L hL e0 q g hb
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 c T) b) m
        = grindRunView L hL e0 q g hb T m :=
    fun m hm => pre_read_run_view_stable L hL e0 q g hb hpo hab (probeStage r) i c hi T hT b m
      (le_of_lt (lt_of_lt_of_le hm hcut))
  have htab : ∀ j, j ≤ 22 + 5 * r →
      grindTableView L hL e0 q g hb
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 c T) b) j
        = grindTableView L hL e0 q g hb T j :=
    fun j hj => pre_read_table_view_stable L hL e0 q g hb hpo hab (probeStage r) i c hi T hT b j
      (le_trans hj (message_stage_le_probe_stage r))
  have hclaims := pre_read_raw_claims_stable L hL e0 q g hb hpo hab lane hcau base
    (probeStage r) i c hi T hT b r (fun r2 hr2 => round_stage_le_probe_stage r2 r hr2)
  have hrunslot : ∀ m, m ≤ slotPos q (probeStage r) i →
      grindRunView L hL e0 q g hb
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 c T) b) m
        = grindRunView L hL e0 q g hb T m :=
    fun m hm => pre_read_run_view_stable L hL e0 q g hb hpo hab (probeStage r) i c hi T hT b m hm
  have htabstage : ∀ j, j ≤ probeStage r →
      grindTableView L hL e0 q g hb
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 c T) b) j
        = grindTableView L hL e0 q g hb T j :=
    fun j hj => pre_read_table_view_stable L hL e0 q g hb hpo hab (probeStage r) i c hi T hT b j hj
  have hcandeq : cand r i
        (grindRunView L hL e0 q g hb
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 c T) b))
        (grindTableView L hL e0 q g hb
          (reassign T (chainChallengeSel L hL
            (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 c T) b))
      = cand r i (grindRunView L hL e0 q g hb T) (grindTableView L hL e0 q g hb T) :=
    hccau r i _ _ _ _ hrunslot htabstage
  have htr := hcau.2 r _ _ _ _ hrun htab
  rw [preReadCandTarget, preReadCandTarget, hclaims, hcandeq, htr]

/-! ## 6. THE PER-ROUND MASS AND THE `(q + 1)` FACTOR -/

open Classical in
/-- **ONE SLOT'S PRE-READ EVENT.**  The challenge triple at the digest of slot `i`
of round `r`'s probe stage lands in the bad set of the candidate that slot
carries, on the separation event of that slot.  `Finset.univ` enters through
`probeFresh`. -/
noncomputable def preReadProbeEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (base r i : Nat) : Finset (OracleTable (boundedQueries L)) :=
  (probeFresh L hL e0 q g hb (probeStage r) i).filter (fun T =>
    chainTriple L hL (probeDigestFam L hL e0 q g hb (probeStage r) i) 0 base T
      ∈ preReadCandTarget L hL e0 q g hb lane cand base r i T)

/-- (6) **ONE SLOT COSTS ONE PER-ROUND TERM.**  The adopted per-round quotient
`bd * fiberCeiling ^ 3 / |DigestTriple|`, for a digest the prover PROBED. -/
theorem pre_read_probe_event_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (lane : GrindLane) (hcau : GrindLaneCausal q lane)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (hccau : CandidateProbeCausal q cand) (bd : Nat) (hlb : GrindLaneBounded lane bd)
    (hcb : CandidateBounded cand bd) (base : Nat) (hbase : base + 2 < Transcript.u64Limit)
    (r i : Nat) (hi : i ≤ q) :
    oracleProbability (boundedQueries L)
        (preReadProbeEvent L hL e0 q g hb lane cand base r i)
      ≤ ((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  pre_read_probe_mass_le L hL e0 q g hb hpo hab (probeStage r) i hi base hbase
    (preReadCandTarget L hL e0 q g hb lane cand base r i)
    (fun T hT c _ b => pre_read_cand_target_reassign L hL e0 q g hb hpo hab lane hcau cand
      hccau base r i c hi T hT b)
    (bd * OuterChallenge.fiberCeiling ^ 3)
    (fun T _ => pre_read_cand_target_card_le L hL e0 q g hb lane cand bd hlb hcb base r i T)

/-- (6) A finite union bound over an indexed family, by induction on the range. -/
theorem oracle_probability_range_bi_union_le (Q : Finset Transcript.Bytes)
    (E : Nat → Finset (OracleTable Q)) (t : ℚ) :
    ∀ n : Nat, (∀ i, i < n → oracleProbability Q (E i) ≤ t) →
      oracleProbability Q ((Finset.range n).biUnion E) ≤ (n : ℚ) * t := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [Finset.range_zero, Finset.biUnion_empty, oracle_probability_empty, Nat.cast_zero,
        zero_mul]
  | succ n2 ih =>
      intro h
      rw [Finset.range_succ, Finset.biUnion_insert]
      refine le_trans (oracle_probability_union_le Q _ _) ?_
      have hcast : ((n2 + 1 : Nat) : ℚ) * t = t + (n2 : ℚ) * t := by push_cast; ring
      rw [hcast]
      exact add_le_add (h n2 (by omega)) (ih (fun i hi => h i (by omega)))

theorem digest_triple_term_nonneg (m : Nat) :
    (0 : ℚ) ≤ (m : ℚ) / (Fintype.card OuterChallenge.DigestTriple : ℚ) :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

open Classical in
/-- **ROUND `r`'s PRE-READ EVENT.**  Some slot of round `r`'s probe stage -- one of
the `q` probes, or the absorb, which by `probe_digest_at_round_stage` is the
digest round `r`'s challenges are really squeezed at -- has its own challenge
triple in the bad set of the candidate it carries. -/
noncomputable def preReadRoundEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (lane : GrindLane)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (base r : Nat) : Finset (OracleTable (boundedQueries L)) :=
  (Finset.range (q + 1)).biUnion
    (fun i => preReadProbeEvent L hL e0 q g hb lane cand base r i)

/-- (6) **THE PER-ROUND MASS IS `(q + 1)` TIMES THE ADOPTED PER-ROUND TERM.**
This is the headline shape: grinding with `q` probes per stage costs the round's
term a factor `q + 1`, and no more. -/
theorem pre_read_round_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (lane : GrindLane) (hcau : GrindLaneCausal q lane)
    (cand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (hccau : CandidateProbeCausal q cand) (bd : Nat) (hlb : GrindLaneBounded lane bd)
    (hcb : CandidateBounded cand bd) (base : Nat) (hbase : base + 2 < Transcript.u64Limit)
    (r : Nat) :
    oracleProbability (boundedQueries L)
        (preReadRoundEvent L hL e0 q g hb lane cand base r)
      ≤ ((q + 1 : Nat) : ℚ) * (((bd * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
          / (Fintype.card OuterChallenge.DigestTriple : ℚ)) :=
  oracle_probability_range_bi_union_le (boundedQueries L) _ _ (q + 1)
    (fun i hi => pre_read_probe_event_mass_le L hL e0 q g hb hpo hab lane hcau cand hccau bd
      hlb hcb base hbase r i (by omega))

open Classical in
/-- Round `r` pre-read on either outer lane: the log lane at counters `0, 1, 2`
and the gate lane at counters `3, 4, 5` of the same probed digest. -/
noncomputable def preReadBothEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (logLane gateLane : GrindLane)
    (logCand gateCand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (r : Nat) : Finset (OracleTable (boundedQueries L)) :=
  preReadRoundEvent L hL e0 q g hb logLane logCand 0 r
    ∪ preReadRoundEvent L hL e0 q g hb gateLane gateCand 3 r

open Classical in
/-- The union over the first `n` rounds. -/
noncomputable def preReadOuterEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (logLane gateLane : GrindLane)
    (logCand gateCand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (n : Nat) : Finset (OracleTable (boundedQueries L)) :=
  (Finset.range n).biUnion
    (fun r => preReadBothEvent L hL e0 q g hb logLane gateLane logCand gateCand r)

/-- (6) **THE OUTER PRE-READ MASS: `(q + 1)` TIMES THE ADOPTED `outerTerm`.**
For a prover whose probes are history-only and whose absorb MAY pre-read the
challenge oracle at its own stage's probe digests -- the channel the adopted
`GrindingUnionBound.ChallengeRestricted` forbids and `preReadGrinder` exploits --
the mass of the event that some round of either outer lane sees a probed challenge
triple in its candidate's bad set is at most `(q + 1) * outerTerm d quo`.

NO CLASH TERM APPEARS HERE because no chain no-clash event is conditioned on: the
conditioning is `probeFresh`, the separation of the PROBED digest, and section 7
charges it separately.  The two are not added into one constant anywhere below. -/
theorem pre_read_outer_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hpo : ProbeHistoryOnly g)
    (hab : AbsorbPreReadOnly q g) (logLane gateLane : GrindLane)
    (hlcau : GrindLaneCausal q logLane) (hgcau : GrindLaneCausal q gateLane)
    (logCand gateCand : Nat → Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (hlccau : CandidateProbeCausal q logCand) (hgccau : CandidateProbeCausal q gateCand)
    (d quo : Nat) (hlog : GrindLaneBounded logLane 5) (hlogc : CandidateBounded logCand 5)
    (hgate : GrindLaneBounded gateLane (quo + 2))
    (hgatec : CandidateBounded gateCand (quo + 2)) :
    oracleProbability (boundedQueries L)
        (preReadOuterEvent L hL e0 q g hb logLane gateLane logCand gateCand d)
      ≤ ((q + 1 : Nat) : ℚ) * ChallengeUnionBound.outerTerm d quo := by
  have hround : ∀ r, oracleProbability (boundedQueries L)
      (preReadBothEvent L hL e0 q g hb logLane gateLane logCand gateCand r)
      ≤ ((q + 1 : Nat) : ℚ) * (((5 * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
            / (Fintype.card OuterChallenge.DigestTriple : ℚ))
        + ((q + 1 : Nat) : ℚ) * ((((quo + 2) * OuterChallenge.fiberCeiling ^ 3 : Nat) : ℚ)
            / (Fintype.card OuterChallenge.DigestTriple : ℚ)) := by
    intro r
    refine le_trans (oracle_probability_union_le (boundedQueries L) _ _) (add_le_add ?_ ?_)
    · exact pre_read_round_mass_le L hL e0 q g hb hpo hab logLane hlcau logCand hlccau 5
        hlog hlogc 0 (small_counter_lt 2 (by omega)) r
    · exact pre_read_round_mass_le L hL e0 q g hb hpo hab gateLane hgcau gateCand hgccau
        (quo + 2) hgate hgatec 3 (small_counter_lt 5 (by omega)) r
  have hsum := oracle_probability_range_bi_union_le (boundedQueries L)
    (fun r => preReadBothEvent L hL e0 q g hb logLane gateLane logCand gateCand r) _
    d (fun r _ => hround r)
  refine le_trans hsum (le_of_eq ?_)
  have hgen : ∀ A B : ℚ,
      (d : ℚ) * (((q + 1 : Nat) : ℚ) * A + ((q + 1 : Nat) : ℚ) * B)
        = ((q + 1 : Nat) : ℚ) * ((d : ℚ) * (A + B)) := by
    intro A B
    ring
  rw [hgen, round_terms_sum d quo]

/-! ## 7. THE SEPARATION EVENT IS CHARGED -/

/-- **THE PROBES ARE FRAMED AT THE RUN'S OWN CURRENT STAGE DIGEST.**  The adopted
`GrindingQueryBound.grind_absorb_frame` says this of the ABSORB; a general probe
may be framed anywhere, and `GrindingUnionBound.preReadGrinder` and `echoGrinder`
frame theirs at `h k`.  It is what turns a collision between two slots of
different stages into a collision of two STAGE DIGESTS, which the adopted chain
clash event charges. -/
def StageFramedProbes (g : GrindingStrategy) : Prop :=
  ∀ (k i : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (g.probe k i h ch pa).1 = h k

theorem pre_read_grinder_stage_framed : StageFramedProbes preReadGrinder :=
  fun _ _ _ _ _ => rfl

theorem echo_grinder_stage_framed : StageFramedProbes echoGrinder :=
  fun _ _ _ _ _ => rfl

/-- **TWO SLOTS OF THE SAME STAGE ASK DIFFERENT BYTE STRINGS.**  Stated at the
level of the RUN, because that is what the charging argument needs and because a
prover's probe payloads may in principle depend on its history.  It is a property
of the prover, not an event: `pre_read_grinder_run_probes_distinct` establishes it
for the attacker of GUB's section 10 at every table. -/
def RunProbesDistinct (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) : Prop :=
  ∀ (k i1 i2 : Nat) (T : OracleTable (boundedQueries L)), i1 < q → i2 < q → i1 ≠ i2 →
    grindSelSeq L hL e0 q g hb (slotPos q k i1) T
      ≠ grindSelSeq L hL e0 q g hb (slotPos q k i2) T

/-- (7) **SLOT `i` OF STAGE `k`, FOR A SLOT THAT IS A PROBE.**  The query is framed
at the chain's own stage-`k` digest, with the tag and payload the prover chose.
For the absorb slot this is the adopted `GrindingQueryBound.grind_absorb_frame`. -/
theorem pre_read_position_frame (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hsf : StageFramedProbes g) (k i : Nat)
    (hi : i ≤ q) (T : OracleTable (boundedQueries L)) :
    ∃ (t : Transcript.Byte) (p : Transcript.Bytes),
      (grindSelSeq L hL e0 q g hb (slotPos q k i) T).val
        = Transcript.frame (grindState L hL e0 q g hb k T) t p := by
  by_cases hiq : i = q
  · rw [hiq]
    exact grind_absorb_frame L hL e0 q g hb k T
  · have hilt : i < q := by omega
    have hstate : stateOf e0 q (runAns L hL e0 q g hb (slotPos q k i) T) k
        = grindState L hL e0 q g hb k T := by
      refine state_of_run_ans_le L hL e0 q g hb (slotPos q k i) k (fun j2 hj2 => ?_) T
      have hkk : k * (q + 1) = (j2 + 1) * (q + 1) := by rw [hj2]
      have hexp : (j2 + 1) * (q + 1) = j2 * (q + 1) + (q + 1) := by ring
      rw [slotPos, slotPos]
      omega
    have hq1 : (grindQuery e0 q g (runAns L hL e0 q g hb (slotPos q k i) T)
          (challengesOf L hL T) (slotPos q k i)).1 = grindState L hL e0 q g hb k T := by
      unfold grindQuery
      rw [slot_pos_mod q k i hi, slot_pos_div q k i hi, if_pos hilt, hsf k i _ _ _]
      exact hstate
    exact ⟨_, _, congrArg (fun d => Transcript.frame d _ _) hq1⟩

theorem block_digest_inj (b1 b2 : Block) (h : blockDigest b1 = blockDigest b2) : b1 = b2 :=
  Subtype.ext (congrArg Transcript.Digest.bytes h)

/-- (7) **A SLOT OF AN EARLIER STAGE ASKS A DIFFERENT BYTE STRING.**  Both slots
are framed at their own stage's digest (`pre_read_position_frame`), so equal byte
strings would make the two STAGE digests equal by the adopted
`CommitmentOrder.frame_injective`, which the adopted `grindingNoClash` excludes.
This is the cross-stage half of both charging theorems below. -/
theorem pre_read_cross_stage_sel_ne (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hsf : StageFramedProbes g)
    (n k i : Nat) (hi : i ≤ q) (hk : k < n) (T : OracleTable (boundedQueries L))
    (hnc : T ∈ grindingNoClash L hL e0 q g hb n) (k2 i2 : Nat) (hi2 : i2 ≤ q) (hk2 : k2 < k) :
    grindSelSeq L hL e0 q g hb (slotPos q k2 i2) T
      ≠ grindSelSeq L hL e0 q g hb (slotPos q k i) T := by
  intro heq
  have hnc2 := (mem_grind_no_clash L hL e0 q g hb n T).mp hnc
  obtain ⟨t1, p1, h1⟩ := pre_read_position_frame L hL e0 q g hb hsf k2 i2 hi2 T
  obtain ⟨t2, p2, h2⟩ := pre_read_position_frame L hL e0 q g hb hsf k i hi T
  have hval : Transcript.frame (grindState L hL e0 q g hb k2 T) t1 p1
      = Transcript.frame (grindState L hL e0 q g hb k T) t2 p2 := by
    rw [← h1, ← h2, heq]
  exact hnc2 k2 k hk2 (by omega) (CommitmentOrder.frame_injective _ _ _ _ _ _ hval).1

/-- (7) **NO STAGE DIGEST UP TO `k` IS THE DIGEST OF SLOT `i` OF STAGE `k`.**  The
first clause of `probeFresh`, at EVERY slot of the stage, the absorb slot `i = q`
included: an answer equal to the initial digest's block is excluded by the
`avoidBase` clause of the adopted `distinctNoClash`, and an answer equal to an
earlier stage's advancing answer is a repeat of a string that clause forbids,
hence a cross-stage collision `pre_read_cross_stage_sel_ne` excludes. -/
theorem pre_read_stage_digest_ne (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hsf : StageFramedProbes g)
    (n k i : Nat) (hi : i ≤ q) (hk : k < n) (T : OracleTable (boundedQueries L))
    (hnc : T ∈ grindingNoClash L hL e0 q g hb n)
    (hdnc : T ∈ distinctNoClash (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1))) :
    ∀ j, j ≤ k → grindState L hL e0 q g hb j T ≠ probeDigestAt L hL e0 q g hb k i T := by
  classical
  obtain ⟨hd1, hd2⟩ :=
    (mem_distinct_no_clash (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) T).mp hdnc
  have hexpk : (k + 1) * (q + 1) = k * (q + 1) + (q + 1) := by ring
  have hkn : (k + 1) * (q + 1) ≤ n * (q + 1) := Nat.mul_le_mul_right _ (by omega)
  have hslotlt : slotPos q k i < n * (q + 1) := by
    rw [slotPos]
    omega
  intro j hj heq
  cases j with
  | zero =>
      refine hd2 (slotPos q k i) hslotlt ?_
      rw [avoidBase, Finset.mem_singleton]
      have hrw : OuterChallenge.digestBlock (grindState L hL e0 q g hb 0 T)
          = T (grindSelSeq L hL e0 q g hb (slotPos q k i) T) := by
        rw [heq]
        rfl
      exact hrw.symm
  | succ j2 =>
      have hlt : slotPos q j2 q < slotPos q k i := by
        have hjm : (j2 + 1) * (q + 1) ≤ k * (q + 1) := Nat.mul_le_mul_right _ hj
        have hexpj : (j2 + 1) * (q + 1) = j2 * (q + 1) + (q + 1) := by ring
        rw [slotPos, slotPos]
        omega
      have hvaleq : chainVal (grindSelSeq L hL e0 q g hb) (slotPos q j2 q) T
          = chainVal (grindSelSeq L hL e0 q g hb) (slotPos q k i) T :=
        block_digest_inj _ _ heq
      have hsel : grindSelSeq L hL e0 q g hb (slotPos q j2 q) T
          = grindSelSeq L hL e0 q g hb (slotPos q k i) T := by
        by_contra hne
        exact hd1 (slotPos q j2 q) (slotPos q k i) hlt hslotlt hne hvaleq
      exact pre_read_cross_stage_sel_ne L hL e0 q g hb hsf n k i hi hk T hnc j2 q
        (le_refl q) (by omega) hsel

/-- (7) **THE SEPARATION EVENT IS CHARGED BY THE ADOPTED CLASH EVENTS.**  On the
adopted `GrindingQueryBound.grindingNoClash` of the chain's first `n` stages and
the adopted `distinctNoClash` of the run's first `n (q + 1)` positions -- the two
events whose complements `grinding_chain_clash_probability_le` and
`distinct_answer_clash_probability_le` bound at `N (N + 1) / 2 / |Block|` with
`N = n (q + 1)` -- EVERY probe slot's separation event holds.  So section 6's
conditioning is not an assumption: it is the complement of a charged event.

The ABSORB slot `i = q` is deliberately excluded.  A probe-then-absorb prover asks
its absorb's byte string twice, so the absorb slot's digest may equal a probe
slot's and the separation fails there -- the adopted
`GrindingUnionBound.echo_grinder_pre_read_mass_one` is exactly that phenomenon.
`pre_read_repeat_digest_eq` shows what happens instead: the absorb slot then
carries the digest of the probe slot it repeated, and section 6 charges THAT
slot. -/
theorem pre_read_separation_charged (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hsf : StageFramedProbes g)
    (hrd : RunProbesDistinct L hL e0 q g hb) (n k i : Nat) (hi : i < q) (hk : k < n)
    (T : OracleTable (boundedQueries L))
    (hnc : T ∈ grindingNoClash L hL e0 q g hb n)
    (hdnc : T ∈ distinctNoClash (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1))) :
    T ∈ probeFresh L hL e0 q g hb k i := by
  classical
  obtain ⟨hd1, -⟩ :=
    (mem_distinct_no_clash (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) T).mp hdnc
  have hexpk : (k + 1) * (q + 1) = k * (q + 1) + (q + 1) := by ring
  have hkn : (k + 1) * (q + 1) ≤ n * (q + 1) := Nat.mul_le_mul_right _ (by omega)
  have hslotlt : slotPos q k i < n * (q + 1) := by
    rw [slotPos]
    omega
  rw [mem_probe_fresh]
  refine ⟨pre_read_stage_digest_ne L hL e0 q g hb hsf n k i (le_of_lt hi) hk T hnc hdnc, ?_⟩
  intro k2 i2 hi2 hpos heq
  have hvaleq : chainVal (grindSelSeq L hL e0 q g hb) (slotPos q k2 i2) T
      = chainVal (grindSelSeq L hL e0 q g hb) (slotPos q k i) T :=
    block_digest_inj _ _ heq
  have hsel : grindSelSeq L hL e0 q g hb (slotPos q k2 i2) T
      = grindSelSeq L hL e0 q g hb (slotPos q k i) T := by
    by_contra hne
    exact hd1 (slotPos q k2 i2) (slotPos q k i) hpos hslotlt hne hvaleq
  rcases Nat.lt_trichotomy k2 k with hk2 | hk2 | hk2
  · exact pre_read_cross_stage_sel_ne L hL e0 q g hb hsf n k i (le_of_lt hi) hk T hnc k2 i2
      (le_of_lt hi2) hk2 hsel
  · subst hk2
    have hine : i2 ≠ i := by
      intro hii
      rw [hii] at hpos
      exact absurd hpos (lt_irrefl _)
    exact hrd k2 i2 i T hi2 hi hine hsel
  · rw [slotPos, slotPos] at hpos
    have hge : (k + 1) * (q + 1) ≤ k2 * (q + 1) := Nat.mul_le_mul_right _ (by omega)
    omega

/-- (7) **THE GENERAL DICHOTOMY AT THE ABSORB SLOT: THE ROUND'S DIGEST IS ALWAYS A
CHARGED SLOT'S DIGEST.**  On the SAME two adopted clash-free events, and with no
hypothesis on which branch the prover takes, EITHER the absorb slot of stage `k`
is itself separated -- so section 6 charges it as the `(q + 1)`-th term -- OR the
digest round `k + 1`'s challenges are squeezed at IS the digest of one of the
stage's `q` probes, AND that probe's slot is separated, so section 6 charges THAT
term.  Either way the realized round digest sits in a slot the per-round mass
bound covers, which is the general form of "charging the probes charges the
attack": no favourable-branch hypothesis, no property of the payloads beyond
`StageFramedProbes` and `RunProbesDistinct`.

The proof is the dichotomy the reviewer asked for: a repeat of some same-stage
probe digest is the second alternative outright; otherwise the first clause of
`probeFresh` at slot `q` is `pre_read_stage_digest_ne`, and its second clause
splits by `Nat.lt_trichotomy` into a cross-stage collision
(`pre_read_cross_stage_sel_ne`, excluded by `grindingNoClash` through the adopted
`frame_injective`), the same-stage case (excluded by the branch hypothesis) and a
later stage (excluded by position arithmetic). -/
theorem pre_read_absorb_digest_charged (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hsf : StageFramedProbes g)
    (hrd : RunProbesDistinct L hL e0 q g hb) (n k : Nat) (hk : k < n)
    (T : OracleTable (boundedQueries L))
    (hnc : T ∈ grindingNoClash L hL e0 q g hb n)
    (hdnc : T ∈ distinctNoClash (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1))) :
    T ∈ probeFresh L hL e0 q g hb k q ∨
      ∃ i, i < q ∧
        grindState L hL e0 q g hb (k + 1) T = probeDigestAt L hL e0 q g hb k i T ∧
        T ∈ probeFresh L hL e0 q g hb k i := by
  classical
  by_cases hrep : ∃ i, i < q ∧
      probeDigestAt L hL e0 q g hb k i T = probeDigestAt L hL e0 q g hb k q T
  · obtain ⟨i, hi, heq⟩ := hrep
    exact Or.inr ⟨i, hi, (probe_digest_at_absorb L hL e0 q g hb k T).symm.trans heq.symm,
      pre_read_separation_charged L hL e0 q g hb hsf hrd n k i hi hk T hnc hdnc⟩
  · refine Or.inl ?_
    obtain ⟨hd1, -⟩ :=
      (mem_distinct_no_clash (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) T).mp hdnc
    have hexpk : (k + 1) * (q + 1) = k * (q + 1) + (q + 1) := by ring
    have hkn : (k + 1) * (q + 1) ≤ n * (q + 1) := Nat.mul_le_mul_right _ (by omega)
    have hslotlt : slotPos q k q < n * (q + 1) := by
      rw [slotPos]
      omega
    rw [mem_probe_fresh]
    refine ⟨pre_read_stage_digest_ne L hL e0 q g hb hsf n k q (le_refl q) hk T hnc hdnc, ?_⟩
    intro k2 i2 hi2 hpos heq
    have hvaleq : chainVal (grindSelSeq L hL e0 q g hb) (slotPos q k2 i2) T
        = chainVal (grindSelSeq L hL e0 q g hb) (slotPos q k q) T :=
      block_digest_inj _ _ heq
    have hsel : grindSelSeq L hL e0 q g hb (slotPos q k2 i2) T
        = grindSelSeq L hL e0 q g hb (slotPos q k q) T := by
      by_contra hne
      exact hd1 (slotPos q k2 i2) (slotPos q k q) hpos hslotlt hne hvaleq
    rcases Nat.lt_trichotomy k2 k with hk2 | hk2 | hk2
    · exact pre_read_cross_stage_sel_ne L hL e0 q g hb hsf n k q (le_refl q) hk T hnc k2 i2
        (le_of_lt hi2) hk2 hsel
    · subst hk2
      exact hrep ⟨i2, hi2, heq⟩
    · rw [slotPos, slotPos] at hpos
      have hge : (k + 1) * (q + 1) ≤ k2 * (q + 1) := Nat.mul_le_mul_right _ (by omega)
      omega

/-- (7) **WHEN THE ABSORB REPEATS A PROBE, THE ROUND'S DIGEST IS THAT PROBE'S.**
Two slots of one stage that ask the same byte string produce the same digest, so
if the absorb echoes probe `i` then round `k + 1`'s challenge digest IS slot `i`'s
digest, and slot `i`'s term in `preReadRoundEvent` is the one that carries the
round.  Nothing is lost by excluding the absorb slot from section 7's charging. -/
theorem pre_read_repeat_digest_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k i : Nat)
    (T : OracleTable (boundedQueries L))
    (hrep : grindSelSeq L hL e0 q g hb (slotPos q k q) T
      = grindSelSeq L hL e0 q g hb (slotPos q k i) T) :
    grindState L hL e0 q g hb (k + 1) T = probeDigestAt L hL e0 q g hb k i T :=
  congrArg (fun s => blockDigest (T s)) hrep

/-- (7) **THE ATTACK BRANCH, SPELLED OUT.**  When the pre-read grinder's stage-`k`
read at the digest of its own probe-`0` answer is favourable, the adopted
`GrindingUnionBound.pre_read_grinder_absorb_is_probe_when_favourable` makes the
absorb repeat probe `0`, and then the digest round `k + 1`'s challenges are
squeezed at IS probe `0`'s digest.  So charging probe `0` charges the attack. -/
theorem pre_read_grinder_round_digest_is_probe_digest (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (hb : GrindingBounded L preReadGrinder) (hq : 0 < q)
    (k : Nat) (T : OracleTable (boundedQueries L))
    (hfav : challengesOf L hL T
        (blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 0) T))) 0
      = preReadTarget) :
    grindState L hL e0 q preReadGrinder hb (k + 1) T
      = probeDigestAt L hL e0 q preReadGrinder hb k 0 T :=
  pre_read_repeat_digest_eq L hL e0 q preReadGrinder hb k 0 T
    (pre_read_grinder_absorb_is_probe_when_favourable L hL e0 q hb hq k T hfav)

/-- (7) **THE PRE-READ GRINDER'S STAGE-`k` PROBE `i` ASKS `frame (state k) 1 (le 8 i)`.** -/
theorem pre_read_grinder_probe_sel_val (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L preReadGrinder) (k i : Nat) (hi : i < q)
    (T : OracleTable (boundedQueries L)) :
    (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k i) T).val
      = Transcript.frame (grindState L hL e0 q preReadGrinder hb k T) 1 (Transcript.le 8 i) := by
  have hstate : stateOf e0 q (runAns L hL e0 q preReadGrinder hb (slotPos q k i) T) k
      = grindState L hL e0 q preReadGrinder hb k T := by
    refine state_of_run_ans_le L hL e0 q preReadGrinder hb (slotPos q k i) k
      (fun j2 hj2 => ?_) T
    have hkk : k * (q + 1) = (j2 + 1) * (q + 1) := by rw [hj2]
    have hexp : (j2 + 1) * (q + 1) = j2 * (q + 1) + (q + 1) := by ring
    rw [slotPos, slotPos]
    omega
  have hq1 : grindQuery e0 q preReadGrinder
        (runAns L hL e0 q preReadGrinder hb (slotPos q k i) T) (challengesOf L hL T)
        (slotPos q k i)
      = (grindState L hL e0 q preReadGrinder hb k T, 1, Transcript.le 8 i) := by
    unfold grindQuery
    rw [slot_pos_mod q k i (le_of_lt hi), slot_pos_div q k i (le_of_lt hi), if_pos hi]
    show (stateOf e0 q (runAns L hL e0 q preReadGrinder hb (slotPos q k i) T) k, 1,
      Transcript.le 8 i) = _
    rw [hstate]
  show Transcript.frame (grindQuery e0 q preReadGrinder
      (runAns L hL e0 q preReadGrinder hb (slotPos q k i) T) (challengesOf L hL T)
      (slotPos q k i)).1 _ _ = _
  rw [hq1]

/-- (7) **THE ATTACKER'S SLOTS ARE DISTINCT QUERIES WITHIN A STAGE**, as long as the
probe budget fits in the eight-byte payload the adopted prover uses. -/
theorem pre_read_grinder_run_probes_distinct (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L preReadGrinder) (hqb : q ≤ 256 ^ 8) :
    RunProbesDistinct L hL e0 q preReadGrinder hb := by
  intro k i1 i2 T h1 h2 hne heq
  have hval : Transcript.frame (grindState L hL e0 q preReadGrinder hb k T) 1
        (Transcript.le 8 i1)
      = Transcript.frame (grindState L hL e0 q preReadGrinder hb k T) 1
        (Transcript.le 8 i2) := by
    rw [← pre_read_grinder_probe_sel_val L hL e0 q hb k i1 h1 T,
      ← pre_read_grinder_probe_sel_val L hL e0 q hb k i2 h2 T, heq]
  exact hne (Transcript.le_injective_bounded 8 i1 i2 (lt_of_lt_of_le h1 hqb)
    (lt_of_lt_of_le h2 hqb) (CommitmentOrder.frame_injective _ _ _ _ _ _ hval).2.2)

/-- (7) **THE UNFAVOURABLE BRANCH REPEATS PROBE `1`.**  When the pre-read grinder's
stage-`k` read at its probe-`0` answer's digest is NOT the target, its absorb asks
`frame (state k) 1 (le 8 1)` -- probe `1`'s byte string.  So at `q ≥ 2` the
attacker's absorb is a repeat on BOTH branches, not only on the favourable one
`pre_read_grinder_absorb_is_probe_when_favourable` covers. -/
theorem pre_read_grinder_absorb_is_probe_one_when_unfavourable (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (hb : GrindingBounded L preReadGrinder) (hq : 1 < q)
    (k : Nat) (T : OracleTable (boundedQueries L))
    (hunf : challengesOf L hL T
        (blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 0) T))) 0
      ≠ preReadTarget) :
    grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k q) T
      = grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 1) T := by
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
      = (grindState L hL e0 q preReadGrinder hb k T, 1, Transcript.le 8 1) := by
    rw [grind_query_absorb]
    show (stateOf e0 q (runAns L hL e0 q preReadGrinder hb (slotPos q k q) T) k,
      ((1 : Transcript.Byte),
        if challengesOf L hL T
            (blockDigest (runAns L hL e0 q preReadGrinder hb (slotPos q k q) T
              (slotPos q k 0))) 0 = preReadTarget
          then Transcript.le 8 0 else Transcript.le 8 1)) = _
    rw [state_of_run_ans_at L hL e0 q preReadGrinder hb k k (le_refl k) T, hpa, if_neg hunf]
  have hq1 : grindQuery e0 q preReadGrinder
        (runAns L hL e0 q preReadGrinder hb (slotPos q k 1) T) (challengesOf L hL T)
        (slotPos q k 1)
      = (grindState L hL e0 q preReadGrinder hb k T, 1, Transcript.le 8 1) := by
    unfold grindQuery
    rw [slot_pos_mod q k 1 (by omega), slot_pos_div q k 1 (by omega), if_pos hq]
    show (stateOf e0 q (runAns L hL e0 q preReadGrinder hb (slotPos q k 1) T) k, 1,
      Transcript.le 8 1) = _
    rw [state_of_run_ans_le L hL e0 q preReadGrinder hb (slotPos q k 1) k
      (fun i2 hi2 => ?_) T]
    have hexp : (i2 + 1) * (q + 1) = i2 * (q + 1) + (q + 1) := by ring
    rw [slotPos, slotPos, hi2]
    omega
  show grindBytes e0 q preReadGrinder
      (runAns L hL e0 q preReadGrinder hb (slotPos q k q) T)
      (challengesOf L hL T) (slotPos q k q)
    = grindBytes e0 q preReadGrinder
      (runAns L hL e0 q preReadGrinder hb (slotPos q k 1) T)
      (challengesOf L hL T) (slotPos q k 1)
  unfold grindBytes
  rw [hq1, hq2]

/-- (7) **THE `(q + 1)`-TH SLOT'S EVENT IS EMPTY FOR THE ATTACKER AT `q ≥ 2`.**  At
every table the pre-read grinder's absorb repeats probe `0` (favourable) or probe
`1` (unfavourable), so the absorb slot always shares a digest with an earlier slot
of its own stage and the second clause of `probeFresh` fails.  The `(q + 1)`-th
term of `preReadRoundEvent` is therefore the mass of the EMPTY set for this
prover: the "+1" slot is the FRESH-ABSORB case, and this attacker never realizes
it.  It is not charged by section 7 either -- `pre_read_separation_charged` is
stated for `i < q` -- and `pre_read_absorb_digest_charged` is what covers the
general prover instead. -/
theorem pre_read_absorb_slot_never_fresh (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L preReadGrinder) (hq : 1 < q) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∉ probeFresh L hL e0 q preReadGrinder hb k q := by
  classical
  intro hT
  obtain ⟨-, hpr⟩ := (mem_probe_fresh L hL e0 q preReadGrinder hb k q T).mp hT
  by_cases hfav : challengesOf L hL T
      (blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 0) T))) 0
      = preReadTarget
  · have hlt : slotPos q k 0 < slotPos q k q := by
      rw [slotPos, slotPos]
      omega
    refine hpr k 0 (by omega) hlt ?_
    show blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 0) T))
      = blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k q) T))
    rw [pre_read_grinder_absorb_is_probe_when_favourable L hL e0 q hb (by omega) k T hfav]
  · have hlt : slotPos q k 1 < slotPos q k q := by
      rw [slotPos, slotPos]
      omega
    refine hpr k 1 hq hlt ?_
    show blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k 1) T))
      = blockDigest (T (grindSelSeq L hL e0 q preReadGrinder hb (slotPos q k q) T))
    rw [pre_read_grinder_absorb_is_probe_one_when_unfavourable L hL e0 q hb hq k T hfav]

/-- (7) **AND IT IS EMPTY FOR THE ECHO GRINDER AT `q ≥ 1`.**  The echo prover's
absorb asks probe `0`'s byte string unconditionally (adopted
`GrindingUnionBound.echo_grinder_probe_is_absorb`), so its absorb slot is never
separated either. -/
theorem echo_absorb_slot_never_fresh (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L echoGrinder) (hq : 0 < q) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∉ probeFresh L hL e0 q echoGrinder hb k q := by
  intro hT
  obtain ⟨-, hpr⟩ := (mem_probe_fresh L hL e0 q echoGrinder hb k q T).mp hT
  have hlt : slotPos q k 0 < slotPos q k q := by
    rw [slotPos, slotPos]
    omega
  refine hpr k 0 hq hlt ?_
  show blockDigest (T (grindSelSeq L hL e0 q echoGrinder hb (slotPos q k 0) T))
    = blockDigest (T (grindSelSeq L hL e0 q echoGrinder hb (slotPos q k q) T))
  rw [echo_grinder_probe_is_absorb L hL e0 q hb hq k T]

/-! ## 8. THE CLOSED INSTANCE AT THE ENVELOPE -/

theorem outer_term_nonneg (d quo : Nat) : (0 : ℚ) ≤ ChallengeUnionBound.outerTerm d quo := by
  rw [ChallengeUnionBound.outerTerm]
  exact mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) 3)

/-- (8) The adopted outer term at the envelope, evaluated by rational arithmetic
on `Arithmetic.modulus` and `2 ^ 256`.  No `decide`, no cardinality of `Element`,
`Block` or `OuterChallenge.DigestTriple`. -/
theorem outer_term_at_thirteen_numeric :
    ChallengeUnionBound.outerTerm 13 8 ≤ (1 : ℚ) / 2 ^ 172 := by
  rw [ChallengeUnionBound.outerTerm, ChallengeUnionBound.digest_ratio_explicit]
  norm_num [Arithmetic.modulus]

/-- (8) **A MILLION PROBES PER STAGE STILL LEAVE THE OUTER PRE-READ CONSTANT
TINY.**  `(2 ^ 20 + 1) * outerTerm 13 8` is below `2 ^ (-151)`. -/
theorem pre_read_many_probes_outer_tiny :
    ((2 ^ 20 + 1 : Nat) : ℚ) * ChallengeUnionBound.outerTerm 13 8 ≤ (1 : ℚ) / 2 ^ 151 := by
  refine le_trans (mul_le_mul_of_nonneg_left outer_term_at_thirteen_numeric
    (Nat.cast_nonneg _)) ?_
  push_cast
  norm_num

theorem pre_read_many_probes_outer_lt_one :
    ((2 ^ 20 + 1 : Nat) : ℚ) * ChallengeUnionBound.outerTerm 13 8 < 1 :=
  lt_of_le_of_lt pre_read_many_probes_outer_tiny (by norm_num)

/-- (8) **THE ATTACKER OF GUB'S SECTION 10 IS IN THE CLASS.** -/
theorem pre_read_grinder_in_class (q : Nat) (hq : 0 < q) :
    ProbeHistoryOnly preReadGrinder ∧ AbsorbPreReadOnly q preReadGrinder :=
  ⟨pre_read_grinder_probe_history_only, pre_read_grinder_absorb_pre_read_only q hq⟩

/-- (8) **THE CLOSED INSTANCE.**  At the envelope's thirteen outer rounds, with
`q = 2 ^ 20` probes per stage, for the PRE-READ GRINDER itself -- the prover the
adopted `GrindingUnionBound.pre_read_grinder_not_challenge_restricted` proves is
outside GUB's class -- and with the adopted `separatedGrindLane` on both outer
lanes and its own message as the candidate family, the outer pre-read mass is at
most `(2 ^ 20 + 1) * outerTerm 13 8`.

THIS INSTANCE IS ARITHMETIC, NOT EVIDENCE.  `separatedGrindLane` is a constant
lane and `laneCandidates` submits the same message whatever the probe, so the
prover is not being made to search anything; what the instance shows is that the
`(q + 1)` factor does not spoil the envelope's margin. -/
theorem pre_read_outer_bound_at_thirteen_many_probes (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (hb : GrindingBounded L preReadGrinder) :
    oracleProbability (boundedQueries L)
        (preReadOuterEvent L hL e0 (2 ^ 20) preReadGrinder hb separatedGrindLane
          separatedGrindLane (laneCandidates separatedGrindLane)
          (laneCandidates separatedGrindLane) 13)
      ≤ ((2 ^ 20 + 1 : Nat) : ℚ) * ChallengeUnionBound.outerTerm 13 8 :=
  pre_read_outer_mass_le L hL e0 (2 ^ 20) preReadGrinder hb
    pre_read_grinder_probe_history_only
    (pre_read_grinder_absorb_pre_read_only (2 ^ 20) (by norm_num))
    separatedGrindLane separatedGrindLane
    (separated_grind_lane_causal (2 ^ 20)) (separated_grind_lane_causal (2 ^ 20))
    (laneCandidates separatedGrindLane) (laneCandidates separatedGrindLane)
    (candidate_probe_causal_of_causal (2 ^ 20) (laneCandidates separatedGrindLane)
      (lane_candidates_causal (2 ^ 20) separatedGrindLane
        (separated_grind_lane_causal (2 ^ 20))))
    (candidate_probe_causal_of_causal (2 ^ 20) (laneCandidates separatedGrindLane)
      (lane_candidates_causal (2 ^ 20) separatedGrindLane
        (separated_grind_lane_causal (2 ^ 20))))
    13 8 separated_grind_lane_bounded
    (lane_candidates_bounded separatedGrindLane 5 separated_grind_lane_bounded)
    (grind_lane_bounded_mono separatedGrindLane 5 10 (by norm_num)
      separated_grind_lane_bounded)
    (lane_candidates_bounded separatedGrindLane 10
      (grind_lane_bounded_mono separatedGrindLane 5 10 (by norm_num)
        separated_grind_lane_bounded))

/-- (8) **AND THAT CONSTANT IS BELOW ONE.** -/
theorem pre_read_outer_bound_at_thirteen_many_probes_lt_one (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (hb : GrindingBounded L preReadGrinder) :
    oracleProbability (boundedQueries L)
        (preReadOuterEvent L hL e0 (2 ^ 20) preReadGrinder hb separatedGrindLane
          separatedGrindLane (laneCandidates separatedGrindLane)
          (laneCandidates separatedGrindLane) 13)
      < 1 :=
  lt_of_le_of_lt (pre_read_outer_bound_at_thirteen_many_probes L hL e0 hb)
    pre_read_many_probes_outer_lt_one

end Audit.Wire3.PreReadCharge
