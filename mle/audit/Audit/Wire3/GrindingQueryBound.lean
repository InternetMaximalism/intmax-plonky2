import Audit.Wire3.StrategyChainBound

/-!
# COUNTING THE PROVER'S OWN QUERIES: A GRINDING PROVER'S CHAIN

## The gap this module addresses

`StrategyChainBound` removes the fixed-prover restriction from the chain's clash
event: its `strategy_chain_clash_probability_le` bounds that event by
`n (n + 1) / 2 / |Block|` for EVERY `Strategy`, a prover that composes the next
absorb out of the stage digests and the challenge answers at them.  Its
HONESTY (vii) names exactly what that still leaves out:

  "A `Strategy` IS A TRANSCRIPT-RESTRICTED ADAPTIVE PROVER: IT MAKES NO ORACLE
   QUERIES OF ITS OWN. ... A random-oracle-model Fiat--Shamir prover may do more:
   it may itself query `T` at `Transcript.frame (stage k digest) tag p_i` for `q`
   candidate payloads `p_i`, compare the answers against digests it has already
   seen, and submit the payload whose digest collides -- GRINDING.  That attacker
   is NOT a `Strategy` and is NOT covered by anything below ... A query-counting
   extension would have to add the prover's own queries to the read set of the
   table -- that is, replace the two arguments of `Strategy` by an oracle
   interface and count the queries -- and none of that is here."

THIS MODULE IS THAT EXTENSION, FOR THE CHAIN'S CLASH EVENT.  A `GrindingStrategy`
makes `q` PROBE queries of its own at every stage, sequentially adaptive, and
chooses the stage's absorb after reading all of their answers.  All
`N = (q + 1) n` queries the run reads -- the probes and the absorbs -- are
sequenced into ONE causal sequence, and the chain's clash mass comes out as

  `N (N + 1) / 2 / |Block|`,

the SAME shape as the transcript-restricted bound with `n` replaced by the
prover's total query count.  At `q = 0` the numeral is the adopted one:
`3828 / |Block|` at the envelope's `22 + 5 * 13 = 87` stages.

THIS BOUND IS LOOSE IN `q`, AND THE LOOSENESS IS ACKNOWLEDGED, NOT HIDDEN.  Its
leading term is `n^2 (q + 1)^2 / 2`, QUADRATIC in the probe budget, because it is
the ALL-PAIRS birthday bound over the whole interleaved sequence: it charges
every pair of the `N` positions, including pairs of two PROBE answers, which no
stage clash of the chain needs.  A stage clash needs a fresh answer to land on
one of the at most `n + 1` STATE digests, so a bound of order
`(q + 1) n (n + 1) / 2 / |Block|` -- linear in `q` -- looks reachable by
replacing the all-pairs target `BirthdayClashBound.chainTarget` with the set of
ABSORB answers.  It is NOT proved here; see the follow-up note at the end of
HONESTY (ii).  The adopted `StrategyChainBound` HONESTY (vii) phrases the
expected cost of grinding as a clash mass that "scales like `q * n / |Block|`";
that phrasing is a HEURISTIC about the shape of the threat, and what is proved
below is the all-pairs bound `N (N + 1) / 2 / |Block|` with `N = n (q + 1)`,
which is LARGER.  Nothing below should be read as delivering the heuristic.

## Why the adopted `Causal` cannot be used, and what replaces it

`BirthdayClashBound.Causal` asks for two things of a query sequence: that every
query be a function of the answers before it, and that position `k`'s query be
FRESH -- different from every earlier position's -- on the good event.  A
grinding sequence cannot supply the second clause, and not by accident: grinding
IS re-asking.  A prover that probes `frame (state k) tag p` and then absorbs that
same payload queries the same byte string twice, and two positions that asked the
same string of course receive the same answer.

Section 1 therefore replaces `Causal` by `FreshCausal` -- the stability clause
alone, required only where position `m`'s query is a NEW string -- and re-runs the
fresh-query induction with the FRESHNESS events as the conditioning events
instead of the no-clash events.  The event bounded is correspondingly the honest
one: two positions asking DIFFERENT byte strings received equal answers.  The
repeats are pushed down by a first-occurrence argument
(`distinct_clash_succ_subset`), not assumed away.  `causal_of_fresh_causal`
records that `FreshCausal` plus the missing freshness clause is `Causal`, so
nothing the adopted modules prove from `Causal` is weakened.

## What is proved

1. THE REPEAT-TOLERANT BIRTHDAY BOUND (section 1).  `freshAt sel m` is the event
   that position `m` asks a string no earlier position asked; `FreshCausal sel`
   is causality on those events; `distinctClashEvent sel avoid n` is the event
   that two positions asking DIFFERENT strings answered alike, or that some
   answer landed in `avoid`.  `fresh_step_of_fresh_causal` is the adopted
   `BirthdayClashBound.FreshStep` at a fresh position, and
   `distinct_answer_clash_probability_le`:

     `oracleProbability Q (distinctClashEvent sel avoid n)`
       `<= (n |avoid| + n (n - 1) / 2) / |Block|`,

   with NO hypothesis beyond `FreshCausal`.  `distinct_clash_subset_clash`
   records that this is a bound on a SMALLER event than the adopted
   `(noClash sel avoid n)ᶜ`: the pairs whose two positions asked the same string
   are excluded, as they must be.
2. THE INTERLEAVED CAUSAL SEQUENCE (section 2).  `GrindingStrategy` has two
   fields: `probe k i h ch pa`, the `i`-th probe of stage `k`, a frame query at a
   digest, tag and payload THE PROVER CHOOSES from the stage digests `h`, the
   CHALLENGE ORACLE `ch` -- `ch e c` is the oracle's answer at the challenge
   input of an ARBITRARY digest `e`, not only at the chain's own digests -- and
   the probe answers `pa` of every probe already issued, at this stage and at
   every earlier one; and `absorb k h ch pa`, the tag and payload of the
   stage-`k` frame, chosen after all `q` probe answers of stage `k` are in.
   `slotPos q k i = k (q + 1) + i` interleaves them: `runAns m T` is the answer
   list truncated at `m`, built by structural recursion so that a query at
   position `m` can read only the answers strictly before it, and
   `grindSelSeq m T` is the query at position `m`.
   `grinding_sequence_fresh_causal` is `FreshCausal` for it, WITH NO HYPOTHESIS
   ON THE STRATEGY BEYOND THE LENGTH BUDGET `GrindingBounded`.  The challenge
   reads stay outside the sequence -- at every digest, free of charge -- because
   every query IN the sequence is a frame and the adopted
   `RandomOracleSqueezes.frame_ne_challenge_input` separates frames from
   challenge inputs; `challengesOf` is the whole challenge oracle and
   `challenges_of_reassign` is its stability.
3. THE CHAIN CLASH BOUND FOR GRINDING (section 3).  `grindState k T` is the
   chain; `grind_absorb_frame` says the stage-`k` absorb is framed at the
   stage-`k` digest, and `grinding_clash_aux` turns a stage clash into a pair of
   DISTINCT queries with equal answers by induction on the later stage of the
   clash -- if the two absorbs are the same byte string then, by the adopted
   `CommitmentOrder.frame_injective`, the two incoming digests were already
   equal.  `grinding_chain_clash_probability_le`:

     `oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)`
       `<= (n (q + 1)) (n (q + 1) + 1) / 2 / |Block|`.

4. THE TRANSCRIPT-RESTRICTED PROVER IS THE CASE `q = 0` (section 4).
   `grindingOfStrategy strat` is the probe-free grinding strategy of an adopted
   `StrategyChainBound.Strategy`, and `grinding_chain_of_strategy_chain` proves,
   TABLE BY TABLE,

     `grindState L hL e0 0 (grindingOfStrategy strat) hb k T`
       `= StrategyChainBound.strategyFrameState L hL e0 strat hb k T`,

   with `grinding_sel_of_strategy_sel` the same for the stage query.  So every
   statement here specialises to the adopted transcript-restricted one, and
   `grinding_chain_clash_at_eighty_seven_no_probes` gives back the adopted
   numeral `3828 / |Block|`.
5. WHAT GRINDING BUYS, AND THE CLOSED INSTANCES (section 5).
   `constant_table_grinding_clashes` shows the clash event is not empty.
   `probeGrinder` probes `frame` at its own current digest with tag `1` and the
   eight little-endian bytes of the probe index, and absorbs a payload IT READS
   OFF ITS FIRST PROBE'S ANSWER; `grinding_strategy_reads_probes` proves its
   absorb is a real function of the probe answers, which
   `grinding_of_strategy_ignores_probes` shows no `q = 0` strategy's is, whence
   `probe_grinder_is_not_transcript_restricted`.  At the level of the RUN,
   `probe_grinder_chain_differs` produces, for EVERY
   `StrategyChainBound.Strategy`, a table at which the grinder's stage-`1` digest
   differs from that strategy's -- using the adopted
   `StrategyChainBound.strategy_sel_stable_gen` to see that a transcript-restricted
   prover's first query is blind to every frame answer.
   `probe_grinder_chain_clash_probability_le` is section 3's bound for the
   grinder.  `grinding_chain_clash_at_eighty_seven` is the closed form at the
   envelope's `87` stages as a function of `q`, and at `q = 2 ^ 20` --
   `87 * (2 ^ 20 + 1) = 91226199` oracle answers --
   `grinding_chain_clash_at_eighty_seven_many_probes` gives
   `4161109737606900 / |Block|` and
   `grinding_chain_clash_at_eighty_seven_many_probes_tiny` records that this is
   below `2 ^ (-200)`.  `Fintype.card Block` is never evaluated: it is written as
   `2 ^ 256` through the adopted `RandomOracleSqueezes.block_card`.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every statement below is about
the uniform counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`
-- one independent uniform block per byte string of length at most `L`.  The
fresh-query lemma the whole induction rests on, the adopted
`BirthdayClashBound.fresh_coordinate_probability`, is the DEFINING property of a
random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed Keccak by a table drawn from this law is an assumption with no proof
anywhere in this tree.

(ii) THIS BOUNDS THE CHAIN'S CLASH EVENT, FOR A PROVER WITH `q` OWN QUERIES PER
STAGE.  The budget is PER STAGE, not per run: a strategy at `n` stages with `q`
probes each reads `N = (q + 1) n` answers, and that `N` is what enters the bound.
Every headline is a bound on, or a fact about, `grindingClashEvent` -- the event
that two of the chain's stage digests coincide, or that one of them is the digest
the chain started from -- FOR THE CHAIN'S CLASH EVENT.  IT IS NOT A BOUND ON THE
RUN'S BAD-DRAW MASS FOR A GRINDING PROVER.

AND IT IS LOOSE IN `q`, BY ABOUT A FACTOR `q + 1`.  The bound charges all
`N (N + 1) / 2` pairs of the interleaved sequence, probe-probe pairs included; a
stage clash only ever needs a fresh answer to land on one of the at most `n + 1`
STATE digests, which would give order `(q + 1) n (n + 1) / 2 / |Block|`.  THAT
TIGHTER THEOREM IS A FOLLOW-UP, NOT A RESULT OF THIS MODULE, and it is not a
one-line change: it needs the target family
`BirthdayClashBound.chainTarget sel avoid m` -- the blocks of ALL earlier
positions -- replaced by the blocks of the earlier ABSORB positions, and the
first-occurrence step `distinct_clash_succ_subset` does not survive that
replacement unchanged.  Pushing a repeated position `n` down to its first
occurrence `c` replaces the pair `(r, n)` by a pair drawn from `{r, c}`, and when
it was `n` that was the absorb, neither member of the new pair need be one, so
the event "one of the two positions is an absorb" is not preserved by the
induction as stated.  Until that is worked out, the quadratic bound below is what
is proved, and the closed instances at `q = 2 ^ 20` are instances of IT.

(iii) THE UNION BOUND FOR A GRINDING PROVER IS NOT DELIVERED.  This is the same
transport gap as `StrategyChainBound` HONESTY (iii), unchanged.  The adopted
`RandomOracleSqueezes.run_bad_draw_probability_le_fibrewise` splits the run's
bad-draw mass into `ChallengeUnionBound.combinedBound` plus the clash term;
section 3 discharges the clash term for a grinding prover, and the
`combinedBound` half -- the per-round decomposition of
`JointChallengeSpace.jointBadEvent` under the conditioning of
`StrategyChainBound` section 3 -- is NOT re-derived here, for a grinding prover
or for any other.  Nothing below aggregates into a run-level statement.

(iv) THE SEQUENCE POSITIONS ARE FRAME QUERIES; THE CHALLENGE READS ARE FREE AND
UNRESTRICTED.  The restriction the model places is on what occupies a POSITION of
the counted sequence: a probe is `Transcript.frame d t p`, with the digest `d`,
the tag `t` and the payload `p` all chosen by the prover, adaptively, from the
whole history -- but it is a FRAME.  That is what lets the causality argument
overwrite a sequence answer without disturbing a challenge answer, by the adopted
`RandomOracleSqueezes.frame_ne_challenge_input`, and it fails the moment a
COUNTED POSITION is allowed to be a challenge input.

It does NOT follow that the prover may not read the challenge oracle where it
likes.  It may, at zero cost, and it does: `challengesOf L hL T` is the FULL
function `fun e c => StrategyChainBound.challengeAt L hL T e c`, handed to every
probe and every absorb, and the prover may evaluate it at ANY digest `e`
whatsoever -- digests off its own chain, digests it invented, digests no run ever
reaches.  The reason this is free is `challenges_of_reassign`: the adopted
`StrategyChainBound.challenge_at_reassign_frame` is already quantified over every
digest `e`, so overwriting one sequence answer moves NONE of those reads, and the
`FreshCausal` induction never notices them.  Handing the prover the challenge
oracle in full therefore costs the clash bound nothing and raises no position
count.  AN EARLIER DRAFT OF THIS NOTE CLAIMED THE OPPOSITE -- that modelling
challenge-input probes "would raise the position count and therefore the bound".
That was wrong for the clash event, and it is corrected here.

Where grinding ON CHALLENGES would actually matter is the UNDELIVERED half:
the union bound of HONESTY (iii).  `ChallengeUnionBound.combinedBound` is a bound
on the per-round challenge draws, and a prover that hashes candidate digests to
search for a favourable CHALLENGE is exactly the threat there -- its query count
must enter that bound, and nothing below does that.  The clash event of section 3
is simply not the place where challenge grinding bites; the union bound is, and
it is not re-derived here for a grinding prover.

(v) THE NUMBER OF PROBES IS A PARAMETER, NOT A CAP.  `q` is quantified in every
statement; nothing below says a real prover is limited to `q` queries, and
nothing below is an argument that `q` is small.  The closed instance at
`q = 2 ^ 20` is an illustration of the arithmetic, not a claim about any attacker.

(vi) THE LENGTH BUDGET IS A HYPOTHESIS.  `GrindingBounded L g` says every payload
the strategy can ever emit -- probe or absorb, at every history -- fits
`boundedQueries L`.  It is the adopted `StrategyChainBound.StrategyBounded`
quantified over the probes as well, and it is discharged here only for
`grindingOfStrategy` (from the adopted budget) and for `probeGrinder` (at
`93 <= L`).

(vii) THE LANES ARE THE OUTER SUMCHECK LANES.  The index lanes, the WHIR folding
transcript and the Merkle openings are NOT covered, and no round schedule is
threaded onto the chain here: section 4 of `StrategyChainBound` does that for a
transcript-restricted prover and its analogue for a grinding prover is not
below.

(viii) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The bounds here are on
the mass of one named event under the oracle law.  The design point of the
deployed profile is about a hundred bits; nothing below aggregates into a
soundness statement for the protocol.

(ix) WHAT `probe_grinder_chain_differs` DOES AND DOES NOT SAY.  It exhibits, for
each transcript-restricted strategy, ONE table separating the two chains at stage
`1`.  It does not say the grinder's clash mass is LARGER than a
transcript-restricted prover's -- no lower bound on any clash mass is proved
anywhere below -- only that the class of provers section 3 covers is strictly
larger than the class `StrategyChainBound` covers.
-/

namespace Audit.Wire3.GrindingQueryBound

open Audit.Wire3
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound

/-! ## 1. A QUERY SEQUENCE THAT MAY REPEAT ITSELF -/

/-- **POSITION `m` OF THE SEQUENCE ASKS A QUESTION NOBODY ASKED BEFORE.**  The
event that the byte string queried at position `m` differs from the byte string
queried at every earlier position.  A grinding prover DOES repeat itself -- it
probes a candidate frame and then absorbs it -- so this event cannot be dropped,
and it is exactly the conditioning event under which position `m` is a fresh
oracle coordinate. -/
def freshAt {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (m : Nat) :
    Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => ∀ i ∈ Finset.range m, sel i T ≠ sel m T)

theorem mem_fresh_at {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (m : Nat)
    (T : OracleTable Q) :
    T ∈ freshAt sel m ↔ ∀ i, i < m → sel i T ≠ sel m T := by
  simp only [freshAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]

/-- **CAUSALITY AT THE FRESH POSITIONS.**  Every query up to position `m` is a
function of the answers BEFORE position `m`: overwriting the answer at position
`m`'s own query changes none of them.  This is required only where position `m`
is fresh, and that is not a weakening -- if an earlier position asked the SAME
string then overwriting its answer really does change the run, and the causal
hypothesis of `BirthdayClashBound.Causal` is simply false for such a table.

`Causal` asks for the same stability plus the FRESHNESS of every stage on the
good event; a grinding sequence cannot supply the second clause, because the
absorbed frame is by design one of the strings the prover has already probed. -/
def FreshCausal {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) : Prop :=
  ∀ (m : Nat) (T : OracleTable Q), T ∈ freshAt sel m → ∀ (b : Block) (j : Nat), j ≤ m →
    sel j (reassign T (sel m T) b) = sel j T

/-- (1) `FreshCausal` IS THE WEAKER HALF OF `Causal`.  Given the missing
freshness clause -- no earlier stage ever repeats the stage-`k` query on the good
event -- a `FreshCausal` sequence is `BirthdayClashBound.Causal`, so nothing
proved from `Causal` in the adopted modules is lost. -/
theorem causal_of_fresh_causal {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (hc : FreshCausal sel)
    (avoid : Finset Block) (n : Nat)
    (hne : ∀ k, k < n → ∀ j, j < k → ∀ T ∈ noClash sel avoid k, sel j T ≠ sel k T) :
    Causal sel avoid n := by
  refine ⟨fun k hk j hj T hT b => ?_, fun k hk j hj T hT => hne k hk j hj T hT⟩
  refine hc k T ((mem_fresh_at sel k T).mpr (fun i hi => hne k hk i hi T hT)) b j hj

/-- (1) A fresh position stays fresh when its own answer is overwritten. -/
theorem fresh_at_reassign {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (hc : FreshCausal sel)
    (m : Nat) (T : OracleTable Q) (hT : T ∈ freshAt sel m) (b : Block) :
    reassign T (sel m T) b ∈ freshAt sel m := by
  rw [mem_fresh_at]
  intro i hi
  rw [hc m T hT b i (le_of_lt hi), hc m T hT b m (le_refl m)]
  exact (mem_fresh_at sel m T).mp hT i hi

/-- (1) An earlier block is unchanged when a fresh position's answer is
overwritten. -/
theorem chain_val_fresh_stable {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (hc : FreshCausal sel)
    (m : Nat) (T : OracleTable Q) (hT : T ∈ freshAt sel m) (b : Block) (j : Nat) (hj : j < m) :
    chainVal sel j (reassign T (sel m T) b) = chainVal sel j T := by
  show (reassign T (sel m T) b) (sel j (reassign T (sel m T) b)) = T (sel j T)
  rw [hc m T hT b j (le_of_lt hj)]
  exact reassign_off T (sel m T) (sel j T) b ((mem_fresh_at sel m T).mp hT j hj)

/-- (1) **A FRESH POSITION IS AN ADAPTIVE FRESH ORACLE STEP.**  The adopted
`BirthdayClashBound.FreshStep`, with the conditioning event "position `m` is a
new string" in place of "the chain has not clashed yet". -/
theorem fresh_step_of_fresh_causal {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (hc : FreshCausal sel)
    (avoid : Finset Block) (m : Nat) :
    FreshStep Q (freshAt sel m) (sel m) (chainTarget sel avoid m) := by
  refine ⟨fun T hT b => fresh_at_reassign hc m T hT b,
    fun T hT b => hc m T hT b m (le_refl m), fun T hT b => ?_⟩
  refine congrArg (fun z => avoid ∪ z) (Finset.image_congr ?_)
  intro j hj
  exact chain_val_fresh_stable hc m T hT b j (Finset.mem_range.mp hj)

/-- (1) The mass of "the fresh position `m` answers a block already seen, or a
forbidden one". -/
theorem fresh_step_bound {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (hc : FreshCausal sel)
    (avoid : Finset Block) (m : Nat) :
    oracleProbability Q
        ((freshAt sel m).filter (fun T => chainVal sel m T ∈ chainTarget sel avoid m T))
      ≤ ((avoid.card : ℚ) + (m : ℚ)) / (Fintype.card Block : ℚ) := by
  have h := adaptive_fresh_step_abs (fresh_step_of_fresh_causal hc avoid m) (avoid.card + m)
    (fun T _ => chain_target_card_le sel avoid m T)
  rw [Nat.cast_add] at h
  exact h

/-- **THE GOOD EVENT OF A SEQUENCE THAT MAY REPEAT ITSELF.**  Two positions that
asked the SAME byte string of course receive the same answer, and that is no
collision at all; the event below therefore asks only that two positions asking
DIFFERENT strings answer differently, and that no answer lands in `avoid`. -/
def distinctNoClash {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T =>
    (∀ r ∈ Finset.range n, ∀ s ∈ Finset.range n, r < s →
      sel r T ≠ sel s T → chainVal sel r T ≠ chainVal sel s T) ∧
    (∀ s ∈ Finset.range n, chainVal sel s T ∉ avoid))

/-- The complement: two DISTINCT queries of the sequence received equal answers,
or some answer landed in `avoid`. -/
def distinctClashEvent {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) : Finset (OracleTable Q) :=
  (distinctNoClash sel avoid n)ᶜ

theorem mem_distinct_no_clash {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) (T : OracleTable Q) :
    T ∈ distinctNoClash sel avoid n ↔
      (∀ r s : Nat, r < s → s < n → sel r T ≠ sel s T →
        chainVal sel r T ≠ chainVal sel s T) ∧
      (∀ s : Nat, s < n → chainVal sel s T ∉ avoid) := by
  simp only [distinctNoClash, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun r s hrs hsn => h1 r (lt_trans hrs hsn) s hsn hrs, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun r _ s hsn hrs => h1 r s hrs hsn, h2⟩

theorem mem_distinct_clash_event {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) (T : OracleTable Q) :
    T ∈ distinctClashEvent sel avoid n ↔
      (∃ r s : Nat, r < s ∧ s < n ∧ sel r T ≠ sel s T ∧
        chainVal sel r T = chainVal sel s T) ∨
      (∃ s : Nat, s < n ∧ chainVal sel s T ∈ avoid) := by
  rw [distinctClashEvent, Finset.mem_compl, mem_distinct_no_clash, not_and_or]
  constructor
  · rintro (h | h)
    · push_neg at h
      obtain ⟨r, s, hrs, hsn, hne, heq⟩ := h
      exact Or.inl ⟨r, s, hrs, hsn, hne, heq⟩
    · push_neg at h
      obtain ⟨s, hsn, hin⟩ := h
      exact Or.inr ⟨s, hsn, hin⟩
  · rintro (⟨r, s, hrs, hsn, hne, heq⟩ | ⟨s, hsn, hin⟩)
    · refine Or.inl ?_
      push_neg
      exact ⟨r, s, hrs, hsn, hne, heq⟩
    · refine Or.inr ?_
      push_neg
      exact ⟨s, hsn, hin⟩

theorem distinct_clash_event_zero {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) :
    distinctClashEvent sel avoid 0 = (∅ : Finset (OracleTable Q)) := by
  apply Finset.ext
  intro T
  rw [mem_distinct_clash_event]
  simp only [Finset.not_mem_empty, iff_false, not_or, not_exists]
  exact ⟨fun r => by rintro s ⟨-, hs, -, -⟩; omega, fun s => by rintro ⟨hs, -⟩; omega⟩

/-- (1) **THE FIRST-OCCURRENCE STEP.**  A distinct-query collision inside the
first `n + 1` positions is either one inside the first `n`, or one whose later
member is position `n` ITSELF AND FRESH.  The repeats are pushed down: if
position `n` repeats an earlier position `c`, then `c` carries the same answer
and the collision is witnessed below `n`. -/
theorem distinct_clash_succ_subset {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) :
    distinctClashEvent sel avoid (n + 1) ⊆
      distinctClashEvent sel avoid n ∪
        (freshAt sel n).filter (fun T => chainVal sel n T ∈ chainTarget sel avoid n T) := by
  intro T hT
  rcases (mem_distinct_clash_event sel avoid (n + 1) T).mp hT with
    ⟨r, s, hrs, hsn, hne, heq⟩ | ⟨s, hsn, hin⟩
  · rcases Nat.lt_or_ge s n with hlt | hge
    · exact Finset.mem_union_left _
        ((mem_distinct_clash_event sel avoid n T).mpr (Or.inl ⟨r, s, hrs, hlt, hne, heq⟩))
    · have hsn2 : s = n := by omega
      subst hsn2
      by_cases hf : T ∈ freshAt sel s
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf, ?_⟩)
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hrs, heq⟩)
      · rw [mem_fresh_at] at hf
        push_neg at hf
        obtain ⟨c, hcs, hceq⟩ := hf
        have hvc : chainVal sel c T = chainVal sel s T := by
          show T (sel c T) = T (sel s T)
          rw [hceq]
        have hnec : sel r T ≠ sel c T := by rw [hceq]; exact hne
        refine Finset.mem_union_left _ ((mem_distinct_clash_event sel avoid s T).mpr (Or.inl ?_))
        rcases Nat.lt_trichotomy r c with hlt | he | hgt
        · exact ⟨r, c, hlt, hcs, hnec, heq.trans hvc.symm⟩
        · exact absurd (congrArg (fun z => sel z T) he) hnec
        · exact ⟨c, r, hgt, hrs, fun hx => hnec hx.symm, hvc.trans heq.symm⟩
  · rcases Nat.lt_or_ge s n with hlt | hge
    · exact Finset.mem_union_left _
        ((mem_distinct_clash_event sel avoid n T).mpr (Or.inr ⟨s, hlt, hin⟩))
    · have hsn2 : s = n := by omega
      subst hsn2
      by_cases hf : T ∈ freshAt sel s
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hf, Finset.mem_union_left _ hin⟩)
      · rw [mem_fresh_at] at hf
        push_neg at hf
        obtain ⟨c, hcs, hceq⟩ := hf
        have hvc : chainVal sel c T = chainVal sel s T := by
          show T (sel c T) = T (sel s T)
          rw [hceq]
        exact Finset.mem_union_left _
          ((mem_distinct_clash_event sel avoid s T).mpr (Or.inr ⟨c, hcs, hvc ▸ hin⟩))

theorem distinct_clash_probability_le_sum {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (hc : FreshCausal sel)
    (avoid : Finset Block) (n : Nat) :
    oracleProbability Q (distinctClashEvent sel avoid n)
      ≤ ∑ k in Finset.range n, ((avoid.card : ℚ) + (k : ℚ)) / (Fintype.card Block : ℚ) := by
  induction n with
  | zero =>
      rw [distinct_clash_event_zero, Finset.range_zero, Finset.sum_empty, oracleProbability,
        Finset.card_empty, Nat.cast_zero, zero_div]
  | succ k ih =>
      calc oracleProbability Q (distinctClashEvent sel avoid (k + 1))
          ≤ oracleProbability Q (distinctClashEvent sel avoid k ∪
              (freshAt sel k).filter
                (fun T => chainVal sel k T ∈ chainTarget sel avoid k T)) :=
            oracle_probability_mono Q _ _ (distinct_clash_succ_subset sel avoid k)
        _ ≤ oracleProbability Q (distinctClashEvent sel avoid k)
              + oracleProbability Q ((freshAt sel k).filter
                  (fun T => chainVal sel k T ∈ chainTarget sel avoid k T)) :=
            oracle_probability_union_le Q _ _
        _ ≤ (∑ j in Finset.range k,
              ((avoid.card : ℚ) + (j : ℚ)) / (Fintype.card Block : ℚ))
              + ((avoid.card : ℚ) + (k : ℚ)) / (Fintype.card Block : ℚ) :=
            add_le_add ih (fresh_step_bound hc avoid k)
        _ = ∑ j in Finset.range (k + 1),
              ((avoid.card : ℚ) + (j : ℚ)) / (Fintype.card Block : ℚ) :=
            (Finset.sum_range_succ _ _).symm

/-- (1) **THE BIRTHDAY BOUND FOR A SEQUENCE THAT MAY REPEAT ITSELF.**  The mass
of the event that two positions asking DIFFERENT byte strings received equal
answers, or that some answer landed in `avoid`, is at most
`n |avoid| + n (n - 1) / 2` over the block space.  The adopted
`BirthdayClashBound.chain_clash_probability_le` is the same bound under the
stronger hypothesis `Causal`; the point of this one is that the conditioning
events are the FRESHNESS events, which a grinding prover's sequence does satisfy
while `Causal` it does not. -/
theorem distinct_answer_clash_probability_le {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (hc : FreshCausal sel)
    (avoid : Finset Block) (n : Nat) :
    oracleProbability Q (distinctClashEvent sel avoid n)
      ≤ ((n : ℚ) * (avoid.card : ℚ) + (n : ℚ) * ((n : ℚ) - 1) / 2)
        / (Fintype.card Block : ℚ) := by
  rw [← sum_range_div_closed (avoid.card : ℚ) n]
  exact distinct_clash_probability_le_sum hc avoid n

/-- (1) The event bounded above is CONTAINED in the adopted
`BirthdayClashBound.noClash` complement: it is the smaller event, because the
pairs whose two positions asked the same string are excluded from it.  Nothing
here re-proves the adopted bound on the larger event. -/
theorem distinct_clash_subset_clash {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) :
    distinctClashEvent sel avoid n ⊆ (noClash sel avoid n)ᶜ := by
  intro T hT
  rw [mem_clash_event]
  rcases (mem_distinct_clash_event sel avoid n T).mp hT with
    ⟨r, s, hrs, hsn, -, heq⟩ | ⟨s, hsn, hin⟩
  · exact Or.inl ⟨r, s, hrs, hsn, heq⟩
  · exact Or.inr ⟨s, hsn, hin⟩


/-! ## 2. THE GRINDING STRATEGY AND ITS INTERLEAVED QUERY SEQUENCE -/

/-- **A GRINDING STRATEGY.**  At stage `k` the prover first issues `q` PROBES of
its own and then the stage's absorb.

`probe k i h ch pa` is the `i`-th probe of stage `k`: a frame query
`Transcript.frame d t p` at a digest `d`, a tag `t` and a payload `p` THE PROVER
CHOOSES, given the stage digests `h`, the CHALLENGE ORACLE `ch` -- the oracle's
answer `ch e c` at the challenge input of ANY digest `e`, not only at the chain's
own stage digests -- and the answers `pa` of the probes already issued, at this
stage and at every earlier stage.  `absorb k h ch pa` is the tag and payload of
the stage-`k` frame, chosen from the same history AFTER all `q` probe answers of
stage `k` are in.

The challenge argument is a function of a DIGEST, not of a stage index: the
prover may read the challenge oracle at arbitrary inputs of its own choosing, and
that costs the clash bound nothing, because the stability lemma the causality
argument uses -- the adopted
`StrategyChainBound.challenge_at_reassign_frame` -- is already quantified over
every digest.  See HONESTY (iv).

A `StrategyChainBound.Strategy` is the case `q = 0` (`grindingOfStrategy`): it
never probes, and it reads `ch` only at the digests of its own truncated
history. -/
structure GrindingStrategy where
  probe : Nat → Nat → (Nat → Transcript.Digest) → (Transcript.Digest → Nat → Block) →
    (Nat → Nat → Block) → Transcript.Digest × Transcript.Byte × Transcript.Bytes
  absorb : Nat → (Nat → Transcript.Digest) → (Transcript.Digest → Nat → Block) →
    (Nat → Nat → Block) → Transcript.Byte × Transcript.Bytes

/-- The length budget, exactly the adopted `StrategyChainBound.StrategyBounded`
quantified over the probes as well: every payload the strategy can ever emit,
probe or absorb, fits the query set `boundedQueries L`.

The quantification is over ALL histories, including probe-answer lists `pa`
evaluated at slots the run never reaches; that is stronger than the run needs and
harmless -- a budget that holds at every history in particular holds at the ones
the run produces. -/
def GrindingBounded (L : Nat) (g : GrindingStrategy) : Prop :=
  (∀ (k i : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), 61 + (g.probe k i h ch pa).2.2.length ≤ L) ∧
  (∀ (k : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), 61 + (g.absorb k h ch pa).2.length ≤ L)

/-- The position, in the single interleaved sequence, of slot `i` of stage `k`:
each stage occupies `q + 1` positions, the `q` probes and then the absorb. -/
def slotPos (q k i : Nat) : Nat := k * (q + 1) + i

theorem slot_pos_div (q k i : Nat) (hi : i ≤ q) : slotPos q k i / (q + 1) = k := by
  rw [slotPos, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos q),
    Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem slot_pos_mod (q k i : Nat) (hi : i ≤ q) : slotPos q k i % (q + 1) = i := by
  rw [slotPos, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem slot_pos_mono (q : Nat) {j k : Nat} (h : j < k) : slotPos q j q < slotPos q k q := by
  simp only [slotPos]
  exact Nat.add_lt_add_right (mul_lt_mul_of_pos_right h (Nat.succ_pos q)) q

theorem slot_pos_lt_of_le (q n k : Nat) (h : k + 1 ≤ n) : slotPos q k q < n * (q + 1) := by
  have h2 : (k + 1) * (q + 1) ≤ n * (q + 1) := Nat.mul_le_mul_right _ h
  have he : (k + 1) * (q + 1) = k * (q + 1) + (q + 1) := by ring
  simp only [slotPos]
  omega

/-- The stage digests read off the answer list: stage `0` is the base digest and
stage `k + 1` is the digest of the answer at the absorb position of stage `k`. -/
def stateOf (e0 : Transcript.Digest) (q : Nat) (a : Nat → Block) : Nat → Transcript.Digest
  | 0 => e0
  | k + 1 => blockDigest (a (slotPos q k q))

/-- The probe answers read off the answer list.

ALIASING, STATED.  `probeAnsOf q a k i` is defined for EVERY `i`, not only for
`i < q`, and the slot arithmetic makes some of those indices alias other stages:
`probeAnsOf q a k q` is `a (slotPos q k q)`, the stage-`k` ABSORB answer (the same
block `stateOf` takes the stage-`k + 1` digest from), and `probeAnsOf q a k i` for
`i > q` is the answer at a position of a LATER stage.  This is harmless, and not
by convention: the answer list a query reads is `runAns ... m T`, which is the
constant `OuterChallenge.digestBlock e0` at every index `≥ m` (`run_ans_eq`), so
every aliased slot at or beyond the current position reads that constant and
nothing of the future leaks.  Nothing below depends on `probeAnsOf` outside
`i < q`; the aliasing is an artefact of totality, not an information channel. -/
def probeAnsOf (q : Nat) (a : Nat → Block) : Nat → Nat → Block :=
  fun k i => a (slotPos q k i)

/-- **THE QUERY AT POSITION `m`**, as a digest, a tag and a payload.  Position
`m` belongs to stage `m / (q + 1)`; it is a probe when its slot `m % (q + 1)` is
below `q` and the stage's absorb when the slot is `q`.  An absorb is framed at
the CHAIN'S OWN current digest; a probe may be framed at any digest the prover
likes. -/
def grindQuery (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (a : Nat → Block) (ch : Transcript.Digest → Nat → Block) (m : Nat) :
    Transcript.Digest × Transcript.Byte × Transcript.Bytes :=
  if m % (q + 1) < q then
    g.probe (m / (q + 1)) (m % (q + 1)) (stateOf e0 q a) ch (probeAnsOf q a)
  else
    (stateOf e0 q a (m / (q + 1)), g.absorb (m / (q + 1)) (stateOf e0 q a) ch (probeAnsOf q a))

/-- Every query of the sequence, probe or absorb, is a FRAME query.  That is the
one restriction placed on the probes; see HONESTY (iv). -/
def grindBytes (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (a : Nat → Block) (ch : Transcript.Digest → Nat → Block) (m : Nat) : Transcript.Bytes :=
  Transcript.frame (grindQuery e0 q g a ch m).1 (grindQuery e0 q g a ch m).2.1
    (grindQuery e0 q g a ch m).2.2

theorem grind_bytes_mem (L : Nat) (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (hb : GrindingBounded L g) (a : Nat → Block) (ch : Transcript.Digest → Nat → Block)
    (m : Nat) : grindBytes e0 q g a ch m ∈ boundedQueries L := by
  refine bounded_queries_frame L _ _ _ ?_
  show 61 + (grindQuery e0 q g a ch m).2.2.length ≤ L
  unfold grindQuery
  split
  · exact hb.1 _ _ _ _ _
  · exact hb.2 _ _ _ _

def grindSel (L : Nat) (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (hb : GrindingBounded L g) (a : Nat → Block) (ch : Transcript.Digest → Nat → Block)
    (m : Nat) : { x : Transcript.Bytes // x ∈ boundedQueries L } :=
  ⟨grindBytes e0 q g a ch m, grind_bytes_mem L e0 q g hb a ch m⟩

/-- **THE WHOLE CHALLENGE ORACLE.**  The prover is handed the adopted
`StrategyChainBound.challengeAt` AT EVERY DIGEST, not only at the digests of its
own chain: `challengesOf L hL T e c` is the oracle's answer at
`Transcript.challengeInput e c` for an arbitrary `e` the prover picks.

This is strictly more than a `StrategyChainBound.Strategy` is given, and it is
free for the clash bound: the definition does not mention the answer list at all,
so overwriting one sequence answer cannot move it, and
`challenges_of_reassign` is immediate from the adopted
`StrategyChainBound.challenge_at_reassign_frame`, which is already quantified
over every digest.  Grinding ON CHALLENGES is therefore not excluded here -- it
is simply not what the chain's clash event is about; see HONESTY (iv). -/
def challengesOf (L : Nat) (hL : 64 ≤ L) (T : OracleTable (boundedQueries L)) :
    Transcript.Digest → Nat → Block :=
  fun e c => StrategyChainBound.challengeAt L hL T e c

/-- **THE ANSWER LIST AFTER `m` POSITIONS.**  `runAns m T m2` is the answer at
position `m2` when `m2 < m`, and a constant otherwise: a query issued at position
`m` can be built only out of the answers STRICTLY BEFORE it.  Causality is in the
type, by structural recursion, exactly as `StrategyChainBound.stratHist` puts it
there for a transcript-restricted strategy. -/
def runAns (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (hb : GrindingBounded L g) :
    Nat → OracleTable (boundedQueries L) → Nat → Block
  | 0, _, _ => OuterChallenge.digestBlock e0
  | m + 1, T, m2 =>
      if m2 = m then
        T (grindSel L e0 q g hb (runAns L hL e0 q g hb m T) (challengesOf L hL T) m)
      else runAns L hL e0 q g hb m T m2

/-- **THE QUERY AT POSITION `m` OF THE RUN.**  The single interleaved causal
sequence of deliverable 1: at stage `k` the `q` probes and then the absorb. -/
def grindSelSeq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) : { x : Transcript.Bytes // x ∈ boundedQueries L } :=
  grindSel L e0 q g hb (runAns L hL e0 q g hb m T) (challengesOf L hL T) m

theorem run_ans_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) (m2 : Nat) :
    runAns L hL e0 q g hb (m + 1) T m2
      = if m2 = m then T (grindSelSeq L hL e0 q g hb m T)
        else runAns L hL e0 q g hb m T m2 := rfl

/-- (2) **THE ANSWER LIST IS THE TRUNCATED RUN.**  Stated, not assumed. -/
theorem run_ans_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) :
    ∀ (m : Nat) (T : OracleTable (boundedQueries L)) (m2 : Nat),
      runAns L hL e0 q g hb m T m2
        = if m2 < m then T (grindSelSeq L hL e0 q g hb m2 T)
          else OuterChallenge.digestBlock e0 := by
  intro m
  induction m with
  | zero => intro T m2; rw [if_neg (Nat.not_lt_zero m2)]; rfl
  | succ k ih =>
      intro T m2
      rw [run_ans_succ]
      by_cases h : m2 = k
      · subst h
        rw [if_pos rfl, if_pos (Nat.lt_succ_self m2)]
      · rw [if_neg h, ih T m2]
        by_cases h2 : m2 < k
        · rw [if_pos h2, if_pos (by omega : m2 < k + 1)]
        · rw [if_neg h2, if_neg (by omega : ¬ (m2 < k + 1))]

/-- **THE STATE DIGEST AFTER `k` STAGES OF A GRINDING RUN.** -/
def grindState (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) :
    Nat → OracleTable (boundedQueries L) → Transcript.Digest
  | 0, _ => e0
  | k + 1, T => blockDigest (T (grindSelSeq L hL e0 q g hb (slotPos q k q) T))

theorem grind_state_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    grindState L hL e0 q g hb (k + 1) T
      = blockDigest (chainVal (grindSelSeq L hL e0 q g hb) (slotPos q k q) T) := rfl

theorem grind_state_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (T : OracleTable (boundedQueries L)) :
    grindState L hL e0 q g hb 0 T = e0 := rfl

/-- (2) The history the strategy reads at position `m` reports the real stage
digest of every stage whose absorb is already answered. -/
theorem state_of_run_ans (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m k : Nat)
    (hk : slotPos q k q < m) (T : OracleTable (boundedQueries L)) :
    stateOf e0 q (runAns L hL e0 q g hb m T) (k + 1)
      = grindState L hL e0 q g hb (k + 1) T := by
  show blockDigest (runAns L hL e0 q g hb m T (slotPos q k q)) = _
  rw [run_ans_eq, if_pos hk]
  rfl

theorem state_of_run_ans_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m j : Nat)
    (hj : ∀ j2, j = j2 + 1 → slotPos q j2 q < m) (T : OracleTable (boundedQueries L)) :
    stateOf e0 q (runAns L hL e0 q g hb m T) j = grindState L hL e0 q g hb j T := by
  cases j with
  | zero => rfl
  | succ j2 => exact state_of_run_ans L hL e0 q g hb m j2 (hj j2 rfl) T

/-- (2) At the absorb position of stage `k` the strategy reads the true stage
digest of every stage at or below `k`. -/
theorem state_of_run_ans_at (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k j : Nat) (hj : j ≤ k)
    (T : OracleTable (boundedQueries L)) :
    stateOf e0 q (runAns L hL e0 q g hb (slotPos q k q) T) j
      = grindState L hL e0 q g hb j T := by
  refine state_of_run_ans_le L hL e0 q g hb (slotPos q k q) j ?_ T
  intro j2 hj2
  exact slot_pos_mono q (by omega)

/-- (2) **OVERWRITING ONE ANSWER LEAVES EVERY CHALLENGE ANSWER ALONE.**  Every
query of the sequence is a frame, and the adopted
`RandomOracleSqueezes.frame_ne_challenge_input` separates frames from challenge
inputs.  This is what lets the challenge reads stay OUTSIDE the sequence. -/
theorem challenge_at_reassign_grind (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) (b : Block) (e : Transcript.Digest) (c : Nat) :
    StrategyChainBound.challengeAt L hL
        (reassign T (grindSelSeq L hL e0 q g hb m T) b) e c
      = StrategyChainBound.challengeAt L hL T e c :=
  StrategyChainBound.challenge_at_reassign_frame L hL T
    (grindSelSeq L hL e0 q g hb m T) _ _ _ rfl b e c

/-- (2) **THE WHOLE CHALLENGE ORACLE IS UNTOUCHED BY OVERWRITING A SEQUENCE
ANSWER.**  Not just the challenge reads at the chain's own stage digests: the
reads at EVERY digest, because the adopted
`StrategyChainBound.challenge_at_reassign_frame` is quantified over every digest.
This is why handing the prover challenge reads at arbitrary inputs costs the
clash bound nothing -- see HONESTY (iv). -/
theorem challenges_of_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) (b : Block) :
    challengesOf L hL (reassign T (grindSelSeq L hL e0 q g hb m T) b)
      = challengesOf L hL T := by
  funext e c
  exact challenge_at_reassign_grind L hL e0 q g hb m T b e c

/-- (2) The query at a position is a function of the answer list and of the
challenge answers, and of nothing else. -/
theorem grind_sel_seq_congr (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (i : Nat)
    (T1 T2 : OracleTable (boundedQueries L))
    (ha : runAns L hL e0 q g hb i T1 = runAns L hL e0 q g hb i T2)
    (hch : challengesOf L hL T1 = challengesOf L hL T2) :
    grindSelSeq L hL e0 q g hb i T1 = grindSelSeq L hL e0 q g hb i T2 := by
  show grindSel L e0 q g hb (runAns L hL e0 q g hb i T1) (challengesOf L hL T1) i = _
  rw [ha, hch]
  rfl

/-- (2) **OVERWRITING THE ANSWER AT A FRESH POSITION CHANGES NO EARLIER
ANSWER.** -/
theorem run_ans_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ freshAt (grindSelSeq L hL e0 q g hb) m) (b : Block) :
    ∀ j, j ≤ m →
      runAns L hL e0 q g hb j (reassign T (grindSelSeq L hL e0 q g hb m T) b)
        = runAns L hL e0 q g hb j T := by
  intro j
  induction j with
  | zero => intro _; funext m2; rfl
  | succ i ih =>
      intro hi
      have hih := ih (by omega)
      have hsel : grindSelSeq L hL e0 q g hb i
            (reassign T (grindSelSeq L hL e0 q g hb m T) b)
          = grindSelSeq L hL e0 q g hb i T :=
        grind_sel_seq_congr L hL e0 q g hb i _ T hih
          (challenges_of_reassign L hL e0 q g hb m T b)
      funext m2
      rw [run_ans_succ, run_ans_succ, hsel, hih]
      by_cases h : m2 = i
      · rw [if_pos h, if_pos h]
        exact reassign_off T _ _ b ((mem_fresh_at _ m T).mp hT i (by omega))
      · rw [if_neg h, if_neg h]

/-- (1) **THE INTERLEAVED SEQUENCE IS CAUSAL AT ITS FRESH POSITIONS.**  Every
query the run reads -- the `q` probes of every stage and the stage's own absorb --
is a function of the answers strictly before it.  There is no hypothesis on the
grinding strategy BEYOND THE LENGTH BUDGET `hb : GrindingBounded L g`, which is
what makes the emitted strings members of `boundedQueries L` and is a genuine
hypothesis on `g`: subject to it, the probes may be framed at any digest, with
any tag and any payload, chosen adaptively from the whole history, and the
challenge oracle may be read at any digest at all. -/
theorem grinding_sequence_fresh_causal (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) :
    FreshCausal (grindSelSeq L hL e0 q g hb) := by
  intro m T hT b j hj
  exact grind_sel_seq_congr L hL e0 q g hb j _ T
    (run_ans_reassign L hL e0 q g hb m T hT b j hj)
    (challenges_of_reassign L hL e0 q g hb m T b)


/-! ## 3. THE CHAIN'S CLASH BOUND FOR A GRINDING PROVER -/

theorem grind_query_absorb (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (a : Nat → Block) (ch : Transcript.Digest → Nat → Block) (k : Nat) :
    grindQuery e0 q g a ch (slotPos q k q)
      = (stateOf e0 q a k, g.absorb k (stateOf e0 q a) ch (probeAnsOf q a)) := by
  unfold grindQuery
  rw [slot_pos_mod q k q (le_refl q), slot_pos_div q k q (le_refl q), if_neg (lt_irrefl q)]

theorem grind_query_absorb_digest (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    (grindQuery e0 q g (runAns L hL e0 q g hb (slotPos q k q) T)
        (challengesOf L hL T) (slotPos q k q)).1
      = grindState L hL e0 q g hb k T := by
  rw [grind_query_absorb]
  exact state_of_run_ans_at L hL e0 q g hb k k (le_refl k) T

/-- (3) **THE ABSORB OF STAGE `k` IS FRAMED AT THE CHAIN'S OWN STAGE-`k`
DIGEST.**  This is the one place the stage structure is used: it is what turns a
clash of two stage digests into a pair of DISTINCT queries with equal answers. -/
theorem grind_absorb_frame (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∃ (t : Transcript.Byte) (p : Transcript.Bytes),
      (grindSelSeq L hL e0 q g hb (slotPos q k q) T).val
        = Transcript.frame (grindState L hL e0 q g hb k T) t p :=
  ⟨_, _, congrArg (fun d => Transcript.frame d _ _)
    (grind_query_absorb_digest L hL e0 q g hb k T)⟩

theorem digest_block_inj (d e : Transcript.Digest)
    (h : OuterChallenge.digestBlock d = OuterChallenge.digestBlock e) : d = e := by
  have h2 := congrArg blockDigest h
  rwa [block_digest_digest_block, block_digest_digest_block] at h2

open Classical in
/-- The good event of the grinding CHAIN: its first `n + 1` stage digests -- the
base digest included -- are pairwise distinct. -/
noncomputable def grindingNoClash (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ∀ r ∈ Finset.range (n + 1), ∀ s ∈ Finset.range (n + 1), r < s →
    OuterChallenge.digestBlock (grindState L hL e0 q g hb r T)
      ≠ OuterChallenge.digestBlock (grindState L hL e0 q g hb s T))

/-- The event that the grinding chain clashes within its first `n` stages. -/
noncomputable def grindingClashEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  (grindingNoClash L hL e0 q g hb n)ᶜ

theorem mem_grinding_clash_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ grindingClashEvent L hL e0 q g hb n ↔
      ∃ r s : Nat, r < s ∧ s ≤ n ∧
        grindState L hL e0 q g hb r T = grindState L hL e0 q g hb s T := by
  have hiff : T ∈ grindingNoClash L hL e0 q g hb n ↔
      ∀ r, r < n + 1 → ∀ s, s < n + 1 → r < s →
        OuterChallenge.digestBlock (grindState L hL e0 q g hb r T)
          ≠ OuterChallenge.digestBlock (grindState L hL e0 q g hb s T) := by
    simp only [grindingNoClash, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  rw [grindingClashEvent, Finset.mem_compl, hiff]
  push_neg
  constructor
  · rintro ⟨r, -, s, hs, hrs, heq⟩
    exact ⟨r, s, hrs, by omega, digest_block_inj _ _ heq⟩
  · rintro ⟨r, s, hrs, hsn, heq⟩
    exact ⟨r, by omega, s, by omega, hrs, congrArg OuterChallenge.digestBlock heq⟩

/-- (3) **A STAGE CLASH IS A COLLISION BETWEEN TWO DISTINCT QUERIES.**  Induction
on the LATER stage of the clash: the absorbs of stages `r` and `s` are frames at
the stage-`r` and stage-`s` digests, so if the two queries are the same byte
string then the two digests were already equal -- an earlier clash -- and if they
are different byte strings then they are a pair of distinct queries with equal
answers.  A clash with stage `0` is an answer landing on the base block. -/
theorem grinding_clash_aux (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ s : Nat, s ≤ n → ∀ r : Nat, r < s →
      grindState L hL e0 q g hb r T = grindState L hL e0 q g hb s T →
      T ∈ distinctClashEvent (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro hsn r hrs heq
      obtain ⟨s2, rfl⟩ : ∃ s2, s = s2 + 1 := ⟨s - 1, by omega⟩
      have hps : slotPos q s2 q < n * (q + 1) := slot_pos_lt_of_le q n s2 hsn
      cases r with
      | zero =>
          refine (mem_distinct_clash_event _ _ _ T).mpr (Or.inr ⟨slotPos q s2 q, hps, ?_⟩)
          rw [avoidBase, Finset.mem_singleton]
          exact (congrArg OuterChallenge.digestBlock heq).symm
      | succ r2 =>
          have hpr : slotPos q r2 q < slotPos q s2 q := slot_pos_mono q (by omega)
          have hval : chainVal (grindSelSeq L hL e0 q g hb) (slotPos q r2 q) T
              = chainVal (grindSelSeq L hL e0 q g hb) (slotPos q s2 q) T :=
            congrArg OuterChallenge.digestBlock heq
          by_cases hq : grindSelSeq L hL e0 q g hb (slotPos q r2 q) T
              = grindSelSeq L hL e0 q g hb (slotPos q s2 q) T
          · obtain ⟨t1, p1, h1⟩ := grind_absorb_frame L hL e0 q g hb r2 T
            obtain ⟨t2, p2, h2⟩ := grind_absorb_frame L hL e0 q g hb s2 T
            have hfr : Transcript.frame (grindState L hL e0 q g hb r2 T) t1 p1
                = Transcript.frame (grindState L hL e0 q g hb s2 T) t2 p2 := by
              rw [← h1, ← h2, hq]
            obtain ⟨hst, -, -⟩ := CommitmentOrder.frame_injective _ _ _ _ _ _ hfr
            exact ih s2 (Nat.lt_succ_self s2) (by omega) r2 (by omega) hst
          · exact (mem_distinct_clash_event _ _ _ T).mpr
              (Or.inl ⟨slotPos q r2 q, slotPos q s2 q, hpr, hps, hq, hval⟩)

/-- (3) **THE CHAIN'S CLASH EVENT SITS INSIDE THE SEQUENCE'S DISTINCT-QUERY
COLLISION EVENT**, at `(q + 1) n` positions. -/
theorem grinding_clash_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    grindingClashEvent L hL e0 q g hb n
      ⊆ distinctClashEvent (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) := by
  intro T hT
  obtain ⟨r, s, hrs, hsn, heq⟩ := (mem_grinding_clash_event L hL e0 q g hb n T).mp hT
  exact grinding_clash_aux L hL e0 q g hb n T s hsn r hrs heq

/-- (3) **THE BIRTHDAY BOUND FOR A GRINDING PROVER, FOR THE CHAIN'S CLASH
EVENT.**  With `q` probes of its own at every one of `n` stages, the prover reads
`N = (q + 1) n` oracle answers, and the mass of the event that two of its chain's
stage digests coincide -- or that one of them is the digest the chain started
from -- is at most `N (N + 1) / 2` over the block space.

At `q = 0` this is the adopted `StrategyChainBound.strategy_chain_clash_probability_le`;
every extra probe the prover makes enters the bound exactly as one more position
of the sequence, which is the query-counting extension HONESTY (vii) of that
module asks for. -/
theorem grinding_chain_clash_probability_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)
      ≤ ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) := by
  refine le_trans (oracle_probability_mono _ _ _ (grinding_clash_subset L hL e0 q g hb n)) ?_
  have h := distinct_answer_clash_probability_le
    (grinding_sequence_fresh_causal L hL e0 q g hb) (avoidBase e0) (n * (q + 1))
  rw [avoid_base_card] at h
  have hrw : ((n * (q + 1) : Nat) : ℚ) * ((1 : Nat) : ℚ)
      + ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) - 1) / 2
      = ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2 := by
    push_cast
    ring
  rw [hrw] at h
  exact h


/-! ## 4. A TRANSCRIPT-RESTRICTED PROVER IS THE CASE `q = 0` -/

theorem slot_pos_zero (k : Nat) : slotPos 0 k 0 = k := by
  simp only [slotPos, Nat.zero_add, Nat.mul_one, Nat.add_zero]

theorem grind_bytes_of_query (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (a : Nat → Block) (ch : Transcript.Digest → Nat → Block) (m : Nat) (d : Transcript.Digest)
    (tp : Transcript.Byte × Transcript.Bytes)
    (h : grindQuery e0 q g a ch m = (d, tp)) :
    grindBytes e0 q g a ch m = Transcript.frame d tp.1 tp.2 := by
  unfold grindBytes
  rw [h]

/-- **THE ADOPTED `StrategyChainBound.Strategy`, AS A GRINDING STRATEGY WITH NO
PROBES.**  Its absorb reads the history TRUNCATED at its own stage -- exactly the
adopted `stratHist` -- and ignores the probe answers, which at `q = 0` do not
exist.  It reads the challenge oracle only at the digests of that truncated
history, `ch (h (min j k))`, which is precisely the third argument a
`StrategyChainBound.Strategy` is handed: the generalisation of `challengesOf` to
arbitrary digests adds nothing at `q = 0`, and the identity of section 4 goes
through table by table. -/
def grindingOfStrategy (strat : StrategyChainBound.Strategy) : GrindingStrategy where
  probe := fun _ _ h _ _ => (h 0, 0, [])
  absorb := fun k h ch _ => strat k (fun j => h (min j k)) (fun j c => ch (h (min j k)) c)

theorem grinding_of_strategy_bounded (L : Nat) (hL : 64 ≤ L)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat) :
    GrindingBounded L (grindingOfStrategy strat) := by
  refine ⟨fun _ _ _ _ _ => ?_,
    fun k h ch _ => hb k (fun j => h (min j k)) (fun j c => ch (h (min j k)) c)⟩
  show 61 + ([] : Transcript.Bytes).length ≤ L
  simp only [List.length_nil]
  omega

/-- (4) A probe-free strategy does not read the probe answers, so no `q = 0`
strategy is the grinder of section 5. -/
theorem grinding_of_strategy_ignores_probes (strat : StrategyChainBound.Strategy)
    (k : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
    (pa1 pa2 : Nat → Nat → Block) :
    (grindingOfStrategy strat).absorb k h ch pa1 = (grindingOfStrategy strat).absorb k h ch pa2 :=
  rfl

theorem state_of_run_ans_zero_q (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k j : Nat) (hj : j ≤ k)
    (T : OracleTable (boundedQueries L)) :
    stateOf e0 0 (runAns L hL e0 0 g hb k T) j = grindState L hL e0 0 g hb j T := by
  have h := state_of_run_ans_at L hL e0 0 g hb k j hj T
  rwa [slot_pos_zero] at h

/-- (4) The absorb of `grindingOfStrategy strat` at stage `k` IS the adopted
`StrategyChainBound.stratShapeAt`. -/
theorem grinding_absorb_of_strategy (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (k : Nat) (T : OracleTable (boundedQueries L)) (a : Nat → Block) (pa : Nat → Nat → Block)
    (hst : ∀ j, j ≤ k →
      stateOf e0 0 a j = StrategyChainBound.strategyFrameState L hL e0 strat hb j T) :
    (grindingOfStrategy strat).absorb k (stateOf e0 0 a) (challengesOf L hL T) pa
      = StrategyChainBound.stratShapeAt L hL e0 strat hb k T := by
  have hmin : ∀ j, stateOf e0 0 a (min j k)
      = StrategyChainBound.stratHist L hL e0 strat hb k T j := by
    intro j
    rw [StrategyChainBound.strat_hist_eq]
    exact hst (min j k) (Nat.min_le_right j k)
  have h1 : (fun j => stateOf e0 0 a (min j k))
      = StrategyChainBound.stratHist L hL e0 strat hb k T := funext hmin
  have h2 : (fun j c => challengesOf L hL T (stateOf e0 0 a (min j k)) c)
      = (fun j c => StrategyChainBound.challengeAt L hL T
          (StrategyChainBound.stratHist L hL e0 strat hb k T j) c) := by
    funext j c
    show StrategyChainBound.challengeAt L hL T (stateOf e0 0 a (min j k)) c = _
    rw [hmin j]
  show strat k (fun j => stateOf e0 0 a (min j k))
      (fun j c => challengesOf L hL T (stateOf e0 0 a (min j k)) c) = _
  rw [h1, h2]
  rfl

theorem grind_query_of_strategy (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (k : Nat) (T : OracleTable (boundedQueries L))
    (hst : ∀ j, j ≤ k →
      grindState L hL e0 0 (grindingOfStrategy strat)
          (grinding_of_strategy_bounded L hL strat hb) j T
        = StrategyChainBound.strategyFrameState L hL e0 strat hb j T) :
    grindQuery e0 0 (grindingOfStrategy strat)
        (runAns L hL e0 0 (grindingOfStrategy strat)
          (grinding_of_strategy_bounded L hL strat hb) k T)
        (challengesOf L hL T) k
      = (StrategyChainBound.strategyFrameState L hL e0 strat hb k T,
         StrategyChainBound.stratShapeAt L hL e0 strat hb k T) := by
  have ha : ∀ j, j ≤ k →
      stateOf e0 0 (runAns L hL e0 0 (grindingOfStrategy strat)
          (grinding_of_strategy_bounded L hL strat hb) k T) j
        = StrategyChainBound.strategyFrameState L hL e0 strat hb j T := by
    intro j hj
    exact (state_of_run_ans_zero_q L hL e0 (grindingOfStrategy strat)
      (grinding_of_strategy_bounded L hL strat hb) k j hj T).trans (hst j hj)
  have hq := grind_query_absorb e0 0 (grindingOfStrategy strat)
    (runAns L hL e0 0 (grindingOfStrategy strat)
      (grinding_of_strategy_bounded L hL strat hb) k T)
    (challengesOf L hL T) k
  rw [slot_pos_zero] at hq
  rw [hq, ha k (le_refl k),
    grinding_absorb_of_strategy L hL e0 strat hb k T _ _ ha]

/-- (4) The stage-`k` query of the `q = 0` run IS the adopted
`StrategyChainBound.strategySel`. -/
theorem grinding_sel_of_strategy_sel (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (k : Nat) (T : OracleTable (boundedQueries L))
    (hst : ∀ j, j ≤ k →
      grindState L hL e0 0 (grindingOfStrategy strat)
          (grinding_of_strategy_bounded L hL strat hb) j T
        = StrategyChainBound.strategyFrameState L hL e0 strat hb j T) :
    grindSelSeq L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) k T
      = StrategyChainBound.strategySel L hL e0 strat hb k T :=
  Subtype.ext (grind_bytes_of_query e0 0 (grindingOfStrategy strat) _ _ k _ _
    (grind_query_of_strategy L hL e0 strat hb k T hst))

/-- (4) **THE TRANSCRIPT-RESTRICTED CHAIN IS THE GRINDING CHAIN WITH NO
PROBES.**  Table by table, the `q = 0` grinding chain of `grindingOfStrategy strat`
IS the adopted `StrategyChainBound.strategyFrameState` of `strat`, so every
statement of this module specialises to the adopted transcript-restricted
one. -/
theorem grinding_chain_of_strategy_chain (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    ∀ k, grindState L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) k T
      = StrategyChainBound.strategyFrameState L hL e0 strat hb k T := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      cases k with
      | zero => rfl
      | succ k2 =>
          have hst : ∀ j, j ≤ k2 →
              grindState L hL e0 0 (grindingOfStrategy strat)
                  (grinding_of_strategy_bounded L hL strat hb) j T
                = StrategyChainBound.strategyFrameState L hL e0 strat hb j T :=
            fun j hj => ih j (by omega)
          have hsel := grinding_sel_of_strategy_sel L hL e0 strat hb k2 T hst
          show blockDigest (T (grindSelSeq L hL e0 0 (grindingOfStrategy strat)
              (grinding_of_strategy_bounded L hL strat hb) (slotPos 0 k2 0) T))
            = StrategyChainBound.strategyFrameState L hL e0 strat hb (k2 + 1) T
          rw [slot_pos_zero, hsel, StrategyChainBound.strategy_state_succ]
          rfl


/-! ## 5. WHAT GRINDING BUYS, AND THE CLOSED INSTANCES -/

theorem constant_table_grinding_state (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat) :
    grindState L hL e0 q g hb (k + 1) (constantTable L) = OuterInitial.zeroDigest := rfl

/-- (5) **THE CLASH EVENT IS NOT EMPTY.**  The constant table clashes at once, so
section 3 does not bound an empty event. -/
theorem constant_table_grinding_clashes (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) (hn : 2 ≤ n) :
    constantTable L ∈ grindingClashEvent L hL e0 q g hb n := by
  rw [mem_grinding_clash_event]
  refine ⟨1, 2, by omega, hn, ?_⟩
  rw [constant_table_grinding_state L hL e0 q g hb 0,
    constant_table_grinding_state L hL e0 q g hb 1]

/-- **A PROVER THAT GRINDS.**  At stage `k` it probes `Transcript.frame` at its
own current digest with tag `1` and the eight little-endian bytes of the probe
index, and then ABSORBS a payload IT READS OFF ITS FIRST PROBE'S ANSWER: the
thirty-two bytes of the block the oracle returned at probe `0`.  Its absorb is
therefore a genuine function of its own query answers, which no
`StrategyChainBound.Strategy` can be -- see `grinding_strategy_reads_probes` and
`probe_grinder_is_not_transcript_restricted`. -/
def probeGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun k _ _ pa => (0, (pa k 0).val)

theorem probe_grinder_bounded (L : Nat) (hL : 93 ≤ L) : GrindingBounded L probeGrinder := by
  constructor
  · intro _ i _ _ _
    show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · intro k _ _ pa
    show 61 + (pa k 0).val.length ≤ L
    rw [(pa k 0).property]
    omega

/-- (5) **THE GRINDER READS ITS PROBE ANSWERS.**  Two probe-answer histories that
differ give different absorbs, at the same stage digests and the same challenge
answers. -/
theorem grinding_strategy_reads_probes :
    ∃ (k : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
        (pa1 pa2 : Nat → Nat → Block),
      probeGrinder.absorb k h ch pa1 ≠ probeGrinder.absorb k h ch pa2 := by
  refine ⟨0, fun _ => OuterInitial.zeroDigest,
    fun _ _ => OuterChallenge.digestBlock (indexDigest 0),
    fun _ _ => OuterChallenge.digestBlock (indexDigest 0),
    fun _ _ => OuterChallenge.digestBlock (indexDigest 1), ?_⟩
  intro hEq
  have hle : Transcript.le 32 0 = Transcript.le 32 1 := congrArg Prod.snd hEq
  exact absurd (Transcript.le_injective_bounded 32 0 1
    (small_lt_byte_power 0 (by norm_num)) (small_lt_byte_power 1 (by norm_num)) hle) (by decide)

/-- (5) **THE GRINDER IS NOT A TRANSCRIPT-RESTRICTED PROVER.**  No
`StrategyChainBound.Strategy` produces it, because a probe-free absorb cannot
depend on the probe answers. -/
theorem probe_grinder_is_not_transcript_restricted (strat : StrategyChainBound.Strategy) :
    probeGrinder ≠ grindingOfStrategy strat := by
  intro h
  obtain ⟨k, hh, ch, pa1, pa2, hne⟩ := grinding_strategy_reads_probes
  refine hne ?_
  rw [h]
  exact grinding_of_strategy_ignores_probes strat k hh ch pa1 pa2

/-- (5) **SECTION 3'S BOUND APPLIES TO THE GRINDER.** -/
theorem probe_grinder_chain_clash_probability_le (L : Nat) (hL : 93 ≤ L)
    (e0 : Transcript.Digest) (q n : Nat) :
    oracleProbability (boundedQueries L)
        (grindingClashEvent L (Nat.le_trans (by norm_num) hL) e0 q probeGrinder
          (probe_grinder_bounded L hL) n)
      ≤ ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) :=
  grinding_chain_clash_probability_le L (Nat.le_trans (by norm_num) hL) e0 q probeGrinder
    (probe_grinder_bounded L hL) n

/-- (5) **THE CLOSED FORM AT THE ENVELOPE'S `22 + 5 * 13 = 87` STAGES, AS A
FUNCTION OF THE PROBE BUDGET `q`.**  `Fintype.card Block` is never evaluated. -/
theorem grinding_chain_clash_at_eighty_seven (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb 87)
      ≤ ((87 * (q + 1) : Nat) : ℚ) * (((87 * (q + 1) : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) :=
  grinding_chain_clash_probability_le L hL e0 q g hb 87

/-- (5) **AT `q = 0` THE NUMERAL IS THE ADOPTED ONE.**  `3828 / |Block|`, exactly
`StrategyChainBound.strategy_chain_clash_at_eighty_seven` and the adopted
`BirthdayClashBound.prefix_round_digest_clash_mass_at_thirteen`. -/
theorem grinding_chain_clash_at_eighty_seven_no_probes (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (g : GrindingStrategy) (hb : GrindingBounded L g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 0 g hb 87)
      ≤ (3828 : ℚ) / (Fintype.card Block : ℚ) := by
  have h := grinding_chain_clash_probability_le L hL e0 0 g hb 87
  rw [show ((87 * (0 + 1) : Nat) : ℚ) * (((87 * (0 + 1) : Nat) : ℚ) + 1) / 2 = (3828 : ℚ)
    from by norm_num] at h
  exact h

/-- (5) **A MILLION PROBES PER STAGE.**  At `q = 2 ^ 20` the envelope's chain
reads `87 * (2 ^ 20 + 1) = 91226199` oracle answers and the clash numerator is
`4161109737606900`. -/
theorem grinding_chain_clash_at_eighty_seven_many_probes (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (g : GrindingStrategy) (hb : GrindingBounded L g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 1048576 g hb 87)
      ≤ (4161109737606900 : ℚ) / (Fintype.card Block : ℚ) := by
  have h := grinding_chain_clash_probability_le L hL e0 1048576 g hb 87
  rw [show ((87 * (1048576 + 1) : Nat) : ℚ) * (((87 * (1048576 + 1) : Nat) : ℚ) + 1) / 2
    = (4161109737606900 : ℚ) from by norm_num] at h
  exact h

theorem block_card_two_pow : Fintype.card Block = 2 ^ 256 := by
  have h : (256 : Nat) ^ 32 = 2 ^ 256 := by
    show (2 ^ 8 : Nat) ^ 32 = 2 ^ 256
    rw [← pow_mul]
  rw [block_card, h]

/-- (5) **A MILLION PROBES PER STAGE STILL LEAVE THE CHAIN'S CLASH MASS BELOW
`2 ^ (-200)`.**  The block space is written as `2 ^ 256` through the adopted
`RandomOracleSqueezes.block_card`; no cardinality is evaluated as a numeral. -/
theorem grinding_chain_clash_at_eighty_seven_many_probes_tiny (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (g : GrindingStrategy) (hb : GrindingBounded L g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 1048576 g hb 87)
      ≤ 1 / (2 : ℚ) ^ 200 := by
  refine le_trans (grinding_chain_clash_at_eighty_seven_many_probes L hL e0 g hb) ?_
  have hn : (4161109737606900 : Nat) * 2 ^ 200 ≤ Fintype.card Block := by
    rw [block_card_two_pow]
    calc (4161109737606900 : Nat) * 2 ^ 200 ≤ 2 ^ 56 * 2 ^ 200 :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ 256 := by rw [← pow_add]
  have hq : (4161109737606900 : ℚ) * (2 : ℚ) ^ 200 ≤ (Fintype.card Block : ℚ) := by
    exact_mod_cast hn
  rw [div_le_div_iff block_card_cast_pos (by positivity), one_mul]
  exact hq


/-- (5) At one probe per stage, the stage-`0` probe of the grinder is the FIXED
frame `Transcript.frame e0 1 (Transcript.le 8 0)`: it reads nothing. -/
theorem probe_grinder_sel_zero_val (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (hb : GrindingBounded L probeGrinder) (T : OracleTable (boundedQueries L)) :
    (grindSelSeq L hL e0 1 probeGrinder hb 0 T).val
      = Transcript.frame e0 1 (Transcript.le 8 0) := rfl

/-- (5) The stage-`0` ABSORB of the grinder is framed at the base digest with a
payload READ OFF THE PROBE'S ANSWER. -/
theorem probe_grinder_sel_one_val (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (hb : GrindingBounded L probeGrinder) (T : OracleTable (boundedQueries L)) :
    (grindSelSeq L hL e0 1 probeGrinder hb 1 T).val
      = Transcript.frame e0 0 (T (grindSelSeq L hL e0 1 probeGrinder hb 0 T)).val := rfl

theorem probe_grinder_state_one (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (hb : GrindingBounded L probeGrinder) (T : OracleTable (boundedQueries L)) :
    grindState L hL e0 1 probeGrinder hb 1 T
      = blockDigest (T (grindSelSeq L hL e0 1 probeGrinder hb 1 T)) := rfl

theorem probe_grinder_sel_zero_const (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (hb : GrindingBounded L probeGrinder) (T1 T2 : OracleTable (boundedQueries L)) :
    grindSelSeq L hL e0 1 probeGrinder hb 0 T1 = grindSelSeq L hL e0 1 probeGrinder hb 0 T2 :=
  Subtype.ext ((probe_grinder_sel_zero_val L hL e0 hb T1).trans
    (probe_grinder_sel_zero_val L hL e0 hb T2).symm)

theorem probe_grinder_sel_ne (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (hb : GrindingBounded L probeGrinder) (T : OracleTable (boundedQueries L)) :
    grindSelSeq L hL e0 1 probeGrinder hb 0 T ≠ grindSelSeq L hL e0 1 probeGrinder hb 1 T := by
  intro h
  have hv := congrArg Subtype.val h
  rw [probe_grinder_sel_zero_val, probe_grinder_sel_one_val] at hv
  obtain ⟨-, ht, -⟩ := CommitmentOrder.frame_injective _ _ _ _ _ _ hv
  exact absurd ht (by decide)

/-- (5) **A TRANSCRIPT-RESTRICTED PROVER'S FIRST QUERY IS BLIND TO EVERY FRAME
ANSWER.**  The adopted `StrategyChainBound.strategy_sel_stable_gen` at stage `0`:
overwriting the table at ANY frame leaves the stage-`0` query alone, because a
`Strategy` reads only the base digest and the challenge answers at it. -/
theorem strategy_sel_zero_frame_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (T : OracleTable (boundedQueries L))
    (qq : { x : Transcript.Bytes // x ∈ boundedQueries L }) (dg : Transcript.Digest)
    (t : Transcript.Byte) (pl : Transcript.Bytes) (hq : qq.val = Transcript.frame dg t pl)
    (b : Block) :
    StrategyChainBound.strategySel L hL e0 strat hb 0 (reassign T qq b)
      = StrategyChainBound.strategySel L hL e0 strat hb 0 T := by
  refine StrategyChainBound.strategy_sel_stable_gen L hL e0 strat hb 0 T (reassign T qq b)
    (fun i hi => ?_) (fun i _ c => ?_)
  · have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    rw [StrategyChainBound.strategy_state_zero, StrategyChainBound.strategy_state_zero]
  · exact StrategyChainBound.challenge_at_reassign_frame L hL T qq dg t pl hq b _ c

/-- (5) **THE GRINDER'S CHAIN IS NOT ANY TRANSCRIPT-RESTRICTED CHAIN.**  For
EVERY `StrategyChainBound.Strategy` there is a table at which the grinder's
stage-`1` digest differs from that strategy's, so the separation is not only at
the level of the strategy function: the runs themselves differ. -/
theorem probe_grinder_chain_differs (L : Nat) (hL : 64 ≤ L) (hL2 : 93 ≤ L)
    (e0 : Transcript.Digest) (strat : StrategyChainBound.Strategy)
    (hb : StrategyChainBound.StrategyBounded L strat) :
    ∃ T : OracleTable (boundedQueries L),
      grindState L hL e0 1 probeGrinder (probe_grinder_bounded L hL2) 1 T
        ≠ StrategyChainBound.strategyFrameState L hL e0 strat hb 1 T := by
  have hG := probe_grinder_bounded L hL2
  have hcard : 1 < Fintype.card Block := block_card_gt_small 1 (by norm_num)
  have hex : ∀ x : Block, ∃ y : Block, y ≠ x := fun x =>
    Fintype.exists_ne_of_one_lt_card hcard x
  have key : ∀ T : OracleTable (boundedQueries L),
      grindSelSeq L hL e0 1 probeGrinder hG 1 T
          ≠ StrategyChainBound.strategySel L hL e0 strat hb 0 T →
      ∃ T2 : OracleTable (boundedQueries L),
        grindState L hL e0 1 probeGrinder hG 1 T2
          ≠ StrategyChainBound.strategyFrameState L hL e0 strat hb 1 T2 := by
    intro T hne
    obtain ⟨b, hbne⟩ := hex (T (StrategyChainBound.strategySel L hL e0 strat hb 0 T))
    refine ⟨reassign T (grindSelSeq L hL e0 1 probeGrinder hG 1 T) b, ?_⟩
    have hprobe : grindSelSeq L hL e0 1 probeGrinder hG 0
          (reassign T (grindSelSeq L hL e0 1 probeGrinder hG 1 T) b)
        = grindSelSeq L hL e0 1 probeGrinder hG 0 T :=
      probe_grinder_sel_zero_const L hL e0 hG _ T
    have hoff : (reassign T (grindSelSeq L hL e0 1 probeGrinder hG 1 T) b)
          (grindSelSeq L hL e0 1 probeGrinder hG 0 T)
        = T (grindSelSeq L hL e0 1 probeGrinder hG 0 T) :=
      reassign_off T _ _ b (probe_grinder_sel_ne L hL e0 hG T)
    have habs : grindSelSeq L hL e0 1 probeGrinder hG 1
          (reassign T (grindSelSeq L hL e0 1 probeGrinder hG 1 T) b)
        = grindSelSeq L hL e0 1 probeGrinder hG 1 T := by
      refine Subtype.ext ?_
      rw [probe_grinder_sel_one_val, probe_grinder_sel_one_val, hprobe, hoff]
    have hqs : StrategyChainBound.strategySel L hL e0 strat hb 0
          (reassign T (grindSelSeq L hL e0 1 probeGrinder hG 1 T) b)
        = StrategyChainBound.strategySel L hL e0 strat hb 0 T :=
      strategy_sel_zero_frame_stable L hL e0 strat hb T
        (grindSelSeq L hL e0 1 probeGrinder hG 1 T) e0 0
        (T (grindSelSeq L hL e0 1 probeGrinder hG 0 T)).val
        (probe_grinder_sel_one_val L hL e0 hG T) b
    rw [probe_grinder_state_one, habs, reassign_at,
      StrategyChainBound.strategy_state_succ]
    show blockDigest b
      ≠ blockDigest ((reassign T (grindSelSeq L hL e0 1 probeGrinder hG 1 T) b)
          (StrategyChainBound.strategySel L hL e0 strat hb 0
            (reassign T (grindSelSeq L hL e0 1 probeGrinder hG 1 T) b)))
    rw [hqs, reassign_off T _ _ b (Ne.symm hne)]
    intro hd
    exact hbne (congrArg OuterChallenge.digestBlock hd)
  by_cases h0 : grindSelSeq L hL e0 1 probeGrinder hG 1 (constantTable L)
      ≠ StrategyChainBound.strategySel L hL e0 strat hb 0 (constantTable L)
  · exact key (constantTable L) h0
  · rw [not_not] at h0
    obtain ⟨b2, hb2⟩ := hex (constantTable L (grindSelSeq L hL e0 1 probeGrinder hG 0
      (constantTable L)))
    refine key (reassign (constantTable L)
      (grindSelSeq L hL e0 1 probeGrinder hG 0 (constantTable L)) b2) ?_
    have hprobe : grindSelSeq L hL e0 1 probeGrinder hG 0
          (reassign (constantTable L)
            (grindSelSeq L hL e0 1 probeGrinder hG 0 (constantTable L)) b2)
        = grindSelSeq L hL e0 1 probeGrinder hG 0 (constantTable L) :=
      probe_grinder_sel_zero_const L hL e0 hG _ (constantTable L)
    have hqs : StrategyChainBound.strategySel L hL e0 strat hb 0
          (reassign (constantTable L)
            (grindSelSeq L hL e0 1 probeGrinder hG 0 (constantTable L)) b2)
        = StrategyChainBound.strategySel L hL e0 strat hb 0 (constantTable L) :=
      strategy_sel_zero_frame_stable L hL e0 strat hb (constantTable L)
        (grindSelSeq L hL e0 1 probeGrinder hG 0 (constantTable L)) e0 1
        (Transcript.le 8 0) (probe_grinder_sel_zero_val L hL e0 hG (constantTable L)) b2
    rw [hqs, ← h0]
    intro hEq
    have hv := congrArg Subtype.val hEq
    rw [probe_grinder_sel_one_val, probe_grinder_sel_one_val, hprobe,
      reassign_at] at hv
    obtain ⟨-, -, hp⟩ := CommitmentOrder.frame_injective _ _ _ _ _ _ hv
    exact hb2 (Subtype.ext hp)

end Audit.Wire3.GrindingQueryBound
