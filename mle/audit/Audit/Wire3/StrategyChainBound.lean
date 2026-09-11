import Audit.Wire3.ConcreteChainThreading

/-!
# THE FRESH-QUERY INDUCTION AGAINST A STRATEGY, NOT AGAINST A LIST

## The gap this module addresses

`BirthdayClashBound` proves the birthday bound
`frame_chain_clash_probability_le` for the frame chain of a FIXED SHAPE
`shape : Nat -> Transcript.Byte x Transcript.Bytes`: the tag and the payload of
every absorb are chosen before the table is sampled.  `ConcreteChainThreading`
threads that chain onto the run's own commit chain, and its HONESTY (ii) names
what that costs:

  "`p` is a `Verifier.Proof` quantified OUTSIDE the law: `roundMessages p` are
   fixed before the table `T` is sampled.  In the real protocol the prover
   chooses round `r + 1`'s messages AFTER seeing round `r`'s challenges, so an
   adaptive prover is NOT covered.  Extending the argument to an adaptive prover
   means re-running the fresh-query induction against a strategy, not against a
   list, and none of that is here."

THIS MODULE RE-RUNS THAT INDUCTION AGAINST A STRATEGY, FOR THE CHAIN'S CLASH
EVENT.  A strategy is a function of the HISTORY -- the stage digests produced so
far, and the oracle's answers at the CHALLENGE inputs of those digests -- to the
next frame's tag and payload.  The fixed-shape chain is the special case of a
strategy that ignores its history.  The birthday bound comes out with the SAME
constant: `n (n + 1) / 2 / |Block|`, and at the envelope's `22 + 5 * 13 = 87`
stages the same numeral `3828 / |Block|` that
`BirthdayClashBound.prefix_round_digest_clash_mass_at_thirteen` gives for a fixed
prover -- now for EVERY strategy at once.

## What is proved

1. THE STRATEGY CHAIN (section 1).  `Strategy` is
   `Nat -> (Nat -> Transcript.Digest) -> (Nat -> Nat -> Block) ->
    Transcript.Byte x Transcript.Bytes`: at stage `k` the strategy is handed the
   stage digests and, for each earlier stage `j` and each counter `c`, the
   oracle's answer at `Transcript.challengeInput (stage j digest) c`.  That is
   exactly the information the verifier's transcript gives the prover when it
   composes round `r + 1`'s message: the challenges of the rounds already
   committed.  It is NOT everything a random-oracle-model prover may compute --
   a `Strategy` makes NO ORACLE QUERIES OF ITS OWN; see HONESTY (vii).
   `stratHist` builds the history by structural recursion, truncating indices
   above the current stage (`strat_hist_eq`: the history reports
   `strategyFrameState (min j k)`), so a strategy CANNOT read a digest that does
   not exist yet -- causality is built into the type, not assumed.
   `strategyFrameState` is the chain, `strategySel` its stage-`k` frame query,
   and `strategy_chain_of_fixed_shape` proves

     `strategyFrameState L hL e0 (constStrategy shape) hb k T = frameState L e0 shape hlen k T`,

   so every fixed-prover statement of `BirthdayClashBound` is an instance.
2. THE BIRTHDAY BOUND FOR A STRATEGY (section 2).  `strategy_chain_causal` is
   `BirthdayClashBound.Causal` for the strategy chain, with NO hypothesis on the
   strategy, and `strategy_chain_clash_probability_le`:

     `oracleProbability (boundedQueries L) (strategyClashEvent L hL e0 strat hb n)`
       `<= n (n + 1) / 2 / |Block|`.

   The two new ingredients over `frame_chain_causal` are (a) the stage-`j` frame
   query now depends on the table through the CHALLENGE answers at earlier
   digests as well as through the earlier frame answers, and (b) a challenge
   input is never a frame input -- the adopted
   `RandomOracleSqueezes.frame_ne_challenge_input` -- so overwriting a frame
   answer leaves every challenge answer, hence every earlier payload, alone.
   `strategy_state_distinct` is the digests-are-pairwise-distinct form of the
   good event and `strategy_clash_event_mem` spells the clash event out.
3. THE FRESH-UNIFORM CHALLENGE LEMMA (section 3).  The ingredient an adaptive
   union bound needs: conditioned on THE NO-CLASH EVENT up to stage `j`, the
   answers at `Transcript.challengeInput (stage j digest) c` are UNIFORM.  The
   conditioning is on ONE EVENT, not on the history's sigma-algebra: the
   history-fibre form -- conditioning on a prescribed value of every frame answer
   below `j` and of every challenge answer at the digests below `j` -- is NOT
   stated anywhere below, though it would follow from the same `FreshStep`
   lemmas.  `adaptive_fresh_step_uniform` is the exact-equality form of the adopted
   `adaptive_fresh_step` at a constant target;
   `strategy_challenge_fresh_uniform` is the single-counter statement

     `P(noClash j ∩ {T | T (challengeInput (digest j T) c) ∈ S}) = |S| / |Block| * P(noClash j)`,

   and `strategy_challenge_joint_uniform` is the joint statement over a finite
   set `C` of counters below the adopted `Transcript.u64Limit`:

     `P(challengeFibre j C w) = P(noClash j) / |Block| ^ |C|`.

   This is the adaptive analogue of the adopted
   `RandomOracleSqueezes.draw_at_fixed_digests_is_uniform`, whose block digests
   are quantified OUTSIDE the law; here the digest is the chain's own, and the
   conditioning event is the chain's own no-clash event.  The reason the argument
   goes through is exactly the hypothesis of the adopted `adaptive_fresh_step`:
   the digest at stage `j` is formed BEFORE those challenge inputs are read, and
   no earlier query is one of them, because two different digests give different
   challenge inputs (`challenge_input_digest_eq`) and a frame is never a
   challenge input.
4. THE STRATEGIC OUTER PROVER (section 4).  `strategicShape c s S` is the
   strategy that plays the adopted twenty-two-frame relation prefix and then, per
   coupled round `r`, the five frames of a message `S r` CHOSEN FROM THE
   CHALLENGE HISTORY.  `RoundCausal` is the protocol restriction that round `r`'s
   message reads only the history up to stage `22 + 5 r` -- the digest its own
   challenges are squeezed from.  `strategic_prover_chain_is_strategy_chain`
   identifies the strategy chain, TABLE BY TABLE, with the fixed-shape chain of
   the messages the strategy actually produced at that table
   (`realizedMessages`), and `strategic_prover_chain_is_the_run_chain` carries
   that through the adopted `InstalledRoundCommit.concreteFinal`, reusing
   `ConcreteChainThreading.concrete_final_take_succ`:

     `strategyFrameState L hL zeroDigest (strategicShape c s S) hb (22 + 5 r) T`
       `= (concreteFinal (hashOf (boundedQueries L) T) (derive ... ).state 0`
           `((realizedMessages ... N T).take r)).digest`.

   The per-table identity is exactly why the FIXED-prover bound does not already
   cover an adaptive prover: `realizedMessages ... N T` varies with the table, and
   `ConcreteChainThreading.run_clash_probability_le` quantifies its message list
   outside the law.  Section 2's bound is uniform in the strategy and therefore
   does cover it.  `strategic_shape_bounded` DISCHARGES the length budget for a
   strategic prover from the adopted degree bounds, and `strategic_hlen_of_bounded`
   shows the fixed-shape chain's `hlen` is not an extra hypothesis at all: it
   follows from `StrategyBounded` alone, so the four threading theorems carry no
   length hypothesis.  What section 4 does NOT deliver is item (iii) of HONESTY.
5. NON-VACUITY (section 5).  `constant_table_strategy_clashes`: the constant
   table is in the clash event of EVERY strategy, so section 2 does not bound an
   empty event.  `firstChallengeStrategy` is a strategy whose payload IS the
   bytes of the challenge block read at its own current digest;
   `first_challenge_strategy_is_not_constant` proves it is not any fixed shape,
   `first_challenge_strategy_bounded` discharges its length budget at `93 <= L`,
   and `first_challenge_chain_clash_probability_le` is section 2's bound for it.
   `strategy_chain_clash_at_eighty_seven` is the closed instance at the
   envelope's `22 + 5 * 13 = 87` stages,

     `<= 3828 / |Block|`,

   the SAME constant the fixed prover gets, and
   `strategy_clash_bound_at_eighty_seven_lt_one` records that it is below `1`.
   `challengeTruncatedMessage` is a strategic OUTER prover whose round message is
   a real function of the challenge answers it has read
   (`challenge_truncated_message_depends`) and which obeys `RoundCausal`
   (`challenge_truncated_round_causal`); `adaptive_strategic_chain_clash_at_thirteen`
   is the closed instance for it in which NEITHER `hb` NOR `64 <= L` is a
   hypothesis -- both are discharged from the adopted prefix bound and the adopted
   degree bounds.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every statement below is about
the uniform counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`
-- one independent uniform block per byte string of length at most `L`.  Nothing
here is a property of Keccak, of the Solidity or Rust transcript, or of any
deterministic function.  The fresh-query lemma the whole induction rests on --
the adopted `BirthdayClashBound.fresh_coordinate_probability` -- says a fresh
query's answer is uniform given everything else, which is the DEFINING property
of a random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed hash by a table drawn from this law is an assumption with no proof
anywhere in this tree.

(ii) WHAT THE ADAPTIVITY HERE COVERS, AND WHAT IT DOES NOT.  This module removes
the fixed-prover restriction from THE CHAIN'S CLASH EVENT ONLY.  Every headline
below is a bound on, or a fact about, `strategyClashEvent` -- the event that two
of the chain's stage digests coincide or that one returns to the base digest --
FOR THE CHAIN'S CLASH EVENT.  IT IS NOT A BOUND ON THE RUN'S BAD-DRAW MASS FOR AN
ADAPTIVE PROVER.

(iii) WHAT REMAINS FOR THE ADAPTIVE UNION BOUND, PRECISELY.  The adopted
`RandomOracleSqueezes.run_bad_draw_probability_le_fibrewise` splits the run's
bad-draw mass into `ChallengeUnionBound.combinedBound` plus the clash term, and
`ConcreteChainThreading.run_bad_draw_probability_le_birthday` discharges the
clash term FOR A FIXED PROVER.  For a strategic prover, section 2 discharges the
clash term again, uniformly in the strategy -- but the `combinedBound` half is
NOT re-derived here.  What it needs is the per-round decomposition of
`JointChallengeSpace.jointBadEvent` under the conditioning of section 3:
conditioned on the history up to stage `22 + 5 r`, round `r`'s bad set is
determined by round `r`'s message, which the strategy chooses BEFORE the two
challenges of round `r` are read, and the rounds are then summed.  The adopted
`OuterSequentialConditioning` ALREADY PROVES EXACTLY THAT DECOMPOSITION IN THE
IDEAL MODEL -- `PrefixDependent`, `walk_union_mass_bound`,
`adaptive_union_mass_bound`, `adaptive_outer_event_mass_le` and
`adaptive_joint_union_bound`, with `frozen_is_adaptive_special_case` and
`joint_union_bound_recovered` recovering the adopted frozen family -- but it
proves it by COUNTING ON THE ADOPTED FINITE `JointChallengeSpace.JointSpace`,
not on `OracleTable (boundedQueries L)`.  The missing step is the transport: an
oracle-table analogue of
`RandomOracleSqueezes.draw_at_fixed_digests_is_uniform` in which the digests are
the strategy chain's own.  Section 3 is the one-stage form of that transport; the
whole-schedule form, and therefore the adaptive run-level bound, is NOT proved
here.

(iv) THE LANES ARE THE OUTER SUMCHECK LANES.  The index lanes, the WHIR folding
transcript and the Merkle openings are NOT covered.  The chain modelled in
section 4 is the twenty-two relation-prefix frames plus the five frames per
coupled round, and nothing else of the run is threaded.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The bounds here are on
the mass of one named event under the oracle law.  The design point of the
deployed profile is about a hundred bits; nothing below aggregates into a
soundness statement for the protocol.

(vi) THE LENGTH BUDGET IS A HYPOTHESIS.  `StrategyBounded L strat` says every
payload the strategy can EVER emit, at every history, fits the query set
`boundedQueries L`.  For a strategy whose payloads are field vectors this is the
same arithmetic side condition `ConcreteChainThreading.LengthBudget` collects for
a fixed prover, now quantified over the strategy's whole range; section 4
discharges it for `strategicShape` from the adopted degree bounds
(`strategic_shape_bounded`) and section 5 for `firstChallengeStrategy` at
`93 <= L`.

(vii) A `Strategy` IS A TRANSCRIPT-RESTRICTED ADAPTIVE PROVER: IT MAKES NO ORACLE
QUERIES OF ITS OWN.  The only table values a `Strategy` is handed are the ones the
verifier's transcript would hand it -- the stage digests of its own chain and the
oracle's answers at the CHALLENGE inputs of those digests.  A random-oracle-model
Fiat--Shamir prover may do more: it may itself query `T` at
`Transcript.frame (stage k digest) tag p_i` for `q` candidate payloads `p_i`,
compare the answers against digests it has already seen, and submit the payload
whose digest collides -- GRINDING.  That attacker is NOT a `Strategy` and is NOT
covered by anything below: its clash mass scales like `q * n / |Block|`, with its
own query count `q`, not like the `n (n + 1) / 2 / |Block|` proved here.  A
query-counting extension would have to add the prover's own queries to the read
set of the table -- that is, replace the two arguments of `Strategy` by an oracle
interface and count the queries -- and none of that is here.  Concretely, the
freshness step `strategy_sel_ne` claims the stage-`k` frame query is new only
relative to the chain's OWN earlier queries; a grinding prover's queries are not
in that list.
-/

namespace Audit.Wire3.StrategyChainBound

open Audit.Wire3
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound

/-! ## 1. THE STRATEGY CHAIN -/

/-- The oracle's answer at the challenge input of a digest.  This is the only
thing the strategy is allowed to read besides the digests themselves: the
adopted `Transcript.challengeInput` is the string every squeeze is taken at, and
it always has length `64` (`BirthdayClashBound.challenge_input_length`), so it is
always in `boundedQueries L` once `64 <= L`. -/
def challengeAt (L : Nat) (hL : 64 ≤ L) (T : OracleTable (boundedQueries L))
    (e : Transcript.Digest) (c : Nat) : Block :=
  T ⟨Transcript.challengeInput e c, bounded_queries_challenge L hL e c⟩

/-- **A STRATEGY: A TRANSCRIPT-RESTRICTED ADAPTIVE PROVER.**  At stage `k` it is
handed the stage digests and the oracle's answers at the challenge inputs of those
digests, and returns the tag and the payload of the next absorb.  A fixed prover
is the special case that ignores both (`constStrategy`); a Fiat--Shamir prover
that composes round `r + 1`'s message out of round `r`'s challenges is the case
that reads the THIRD argument.

What a `Strategy` may NOT do is query the table itself.  A random-oracle-model
prover that hashes `q` candidate payloads of its own and keeps the one whose
frame digest collides with a digest it has already seen -- GRINDING -- is not of
this type, and its clash mass grows with its query count.  See HONESTY (vii). -/
def Strategy : Type :=
  Nat → (Nat → Transcript.Digest) → (Nat → Nat → Block) → Transcript.Byte × Transcript.Bytes

/-- The length budget: every payload the strategy can ever emit fits the query
set.  Quantified over the whole range of the strategy, not over one run. -/
def StrategyBounded (L : Nat) (strat : Strategy) : Prop :=
  ∀ (k : Nat) (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block),
    61 + (strat k h ch).2.length ≤ L

/-- **THE HISTORY AT STAGE `k`.**  `stratHist ... k T j` is the digest of stage
`j` for `j <= k`, and the digest of stage `k` beyond that: a strategy cannot read
a digest that has not been produced yet.  The truncation is what makes the
recursion structural, and `strat_hist_eq` states it exactly. -/
def stratHist (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) :
    Nat → OracleTable (boundedQueries L) → Nat → Transcript.Digest
  | 0, _, _ => e0
  | k + 1, T, j =>
      if j ≤ k then stratHist L hL e0 strat hb k T j
      else
        blockDigest (T ⟨Transcript.frame (stratHist L hL e0 strat hb k T k)
            (strat k (stratHist L hL e0 strat hb k T)
              (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c)).1
            (strat k (stratHist L hL e0 strat hb k T)
              (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c)).2,
          bounded_queries_frame L _ _ _
            (hb k (stratHist L hL e0 strat hb k T)
              (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c))⟩)

theorem strat_hist_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) (j : Nat) :
    stratHist L hL e0 strat hb (k + 1) T j
      = if j ≤ k then stratHist L hL e0 strat hb k T j
        else
          blockDigest (T ⟨Transcript.frame (stratHist L hL e0 strat hb k T k)
              (strat k (stratHist L hL e0 strat hb k T)
                (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c)).1
              (strat k (stratHist L hL e0 strat hb k T)
                (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c)).2,
            bounded_queries_frame L _ _ _
              (hb k (stratHist L hL e0 strat hb k T)
                (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c))⟩) := rfl

/-- **THE STATE DIGEST AFTER `k` STAGES OF A STRATEGY CHAIN.** -/
def strategyFrameState (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) :
    Transcript.Digest :=
  stratHist L hL e0 strat hb k T k

/-- The tag and payload the strategy plays at stage `k`. -/
def stratShapeAt (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) :
    Transcript.Byte × Transcript.Bytes :=
  strat k (stratHist L hL e0 strat hb k T)
    (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c)

/-- The stage-`k` frame query of a strategy chain. -/
def strategySel (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) :
    { x : Transcript.Bytes // x ∈ boundedQueries L } :=
  ⟨Transcript.frame (strategyFrameState L hL e0 strat hb k T)
      (stratShapeAt L hL e0 strat hb k T).1 (stratShapeAt L hL e0 strat hb k T).2,
    bounded_queries_frame L _ _ _
      (hb k (stratHist L hL e0 strat hb k T)
        (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb k T i) c))⟩

theorem strategy_state_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) :
    strategyFrameState L hL e0 strat hb (k + 1) T
      = blockDigest (chainVal (strategySel L hL e0 strat hb) k T) := by
  show stratHist L hL e0 strat hb (k + 1) T (k + 1) = _
  rw [strat_hist_succ, if_neg (Nat.not_succ_le_self k)]
  rfl

theorem strategy_state_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L)) :
    strategyFrameState L hL e0 strat hb 0 T = e0 := rfl

/-- (1) **THE HISTORY IS THE TRUNCATED CHAIN.**  Stated, not assumed: the
strategy at stage `k` sees `strategyFrameState (min j k)`, so it reads exactly the
digests produced at or before its own stage. -/
theorem strat_hist_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) :
    ∀ (k : Nat) (T : OracleTable (boundedQueries L)) (j : Nat),
      stratHist L hL e0 strat hb k T j
        = strategyFrameState L hL e0 strat hb (min j k) T := by
  intro k
  induction k with
  | zero => intro T j; rw [Nat.min_zero]; rfl
  | succ m ih =>
      intro T j
      rw [strat_hist_succ]
      by_cases hj : j ≤ m
      · rw [if_pos hj, ih T j, Nat.min_eq_left hj, Nat.min_eq_left (by omega : j ≤ m + 1)]
      · rw [if_neg hj, Nat.min_eq_right (by omega : m + 1 ≤ j)]
        exact (strategy_state_succ L hL e0 strat hb m T).symm

theorem strat_hist_of_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) (j : Nat)
    (hj : j ≤ k) :
    stratHist L hL e0 strat hb k T j = strategyFrameState L hL e0 strat hb j T := by
  rw [strat_hist_eq, Nat.min_eq_left hj]

/-- (1) Two tables whose chains agree up to stage `k` give the strategy the SAME
history at stage `k`.  This is the workhorse of every stability proof below. -/
theorem strat_hist_congr (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T1 T2 : OracleTable (boundedQueries L))
    (h : ∀ i, i ≤ k → strategyFrameState L hL e0 strat hb i T1
      = strategyFrameState L hL e0 strat hb i T2) :
    stratHist L hL e0 strat hb k T1 = stratHist L hL e0 strat hb k T2 := by
  funext j
  rw [strat_hist_eq, strat_hist_eq]
  exact h (min j k) (Nat.min_le_right j k)

/-- The history as a plain function of the chain, with no recursion left. -/
def strategyHist (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) :
    Nat → Transcript.Digest :=
  fun j => strategyFrameState L hL e0 strat hb (min j k) T

theorem strategy_hist_is_hist (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k : Nat) (T : OracleTable (boundedQueries L)) :
    stratHist L hL e0 strat hb k T = strategyHist L hL e0 strat hb k T :=
  funext (strat_hist_eq L hL e0 strat hb k T)

/-- The strategy that ignores its history: a FIXED prover. -/
def constStrategy (shape : Nat → Transcript.Byte × Transcript.Bytes) : Strategy :=
  fun k _ _ => shape k

theorem const_strategy_bounded (L : Nat) (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) : StrategyBounded L (constStrategy shape) :=
  fun k _ _ => hlen k

/-- (1) **THE FIXED-SHAPE CHAIN IS THE SPECIAL CASE.**  The adopted
`BirthdayClashBound.frameState` is the strategy chain of `constStrategy`, so
every statement below specializes to the adopted fixed-prover chain. -/
theorem strategy_chain_of_fixed_shape (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    strategyFrameState L hL e0 (constStrategy shape) (const_strategy_bounded L shape hlen) k T
      = frameState L e0 shape hlen k T := by
  induction k with
  | zero => rfl
  | succ m ih =>
      rw [strategy_state_succ, frame_state_succ]
      refine congrArg blockDigest (congrArg T (Subtype.ext ?_))
      show Transcript.frame
          (strategyFrameState L hL e0 (constStrategy shape)
            (const_strategy_bounded L shape hlen) m T) (shape m).1 (shape m).2
        = Transcript.frame (frameState L e0 shape hlen m T) (shape m).1 (shape m).2
      rw [ih]

/-- (1) The same, for the stage query. -/
theorem strategy_sel_of_fixed_shape (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    strategySel L hL e0 (constStrategy shape) (const_strategy_bounded L shape hlen) k T
      = frameSel L e0 shape hlen k T := by
  apply Subtype.ext
  show Transcript.frame
      (strategyFrameState L hL e0 (constStrategy shape)
        (const_strategy_bounded L shape hlen) k T) (shape k).1 (shape k).2
    = Transcript.frame (frameState L e0 shape hlen k T) (shape k).1 (shape k).2
  rw [strategy_chain_of_fixed_shape]

/-! ## 2. THE BIRTHDAY BOUND FOR A STRATEGY -/

/-- (2) **OVERWRITING A FRAME ANSWER LEAVES EVERY CHALLENGE ANSWER ALONE.**  The
adopted `RandomOracleSqueezes.frame_ne_challenge_input`: the two families of
oracle inputs are disjoint, because `Transcript.framePrefix` and
`Transcript.challengePrefix` differ at byte `15`.  This is what lets the chain's
payloads depend on challenge answers without breaking the fresh-query induction
over the frame answers. -/
theorem challenge_at_reassign_frame (L : Nat) (hL : 64 ≤ L) (T : OracleTable (boundedQueries L))
    (q : { x : Transcript.Bytes // x ∈ boundedQueries L }) (dg : Transcript.Digest)
    (t : Transcript.Byte) (pl : Transcript.Bytes) (hq : q.val = Transcript.frame dg t pl)
    (b : Block) (e : Transcript.Digest) (c : Nat) :
    challengeAt L hL (reassign T q b) e c = challengeAt L hL T e c := by
  show (reassign T q b) ⟨Transcript.challengeInput e c, bounded_queries_challenge L hL e c⟩
    = T ⟨Transcript.challengeInput e c, bounded_queries_challenge L hL e c⟩
  refine reassign_off T q _ b ?_
  intro hEq
  have hv : Transcript.challengeInput e c = Transcript.frame dg t pl := by
    rw [← hq]
    exact congrArg Subtype.val hEq
  exact frame_ne_challenge_input dg e t pl c hv.symm

theorem challenge_at_reassign_sel (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (k : Nat)
    (T : OracleTable (boundedQueries L)) (b : Block) (e : Transcript.Digest) (c : Nat) :
    challengeAt L hL (reassign T (strategySel L hL e0 strat hb k T) b) e c
      = challengeAt L hL T e c :=
  challenge_at_reassign_frame L hL T (strategySel L hL e0 strat hb k T) _ _ _ rfl b e c

/-- (2) **THE STAGE QUERY IS A FUNCTION OF THE CHAIN BELOW IT.**  Pure
computation, no probability and no good event: if two tables' chains agree up to
stage `j` AND they answer alike at the challenge inputs of those digests, their
stage-`j` frame queries agree.  Those are exactly the two things the payload
reads. -/
theorem strategy_sel_stable_gen (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j : Nat)
    (T T2 : OracleTable (boundedQueries L))
    (hst : ∀ i, i ≤ j →
      strategyFrameState L hL e0 strat hb i T2 = strategyFrameState L hL e0 strat hb i T)
    (hch : ∀ i, i ≤ j → ∀ c : Nat,
      challengeAt L hL T2 (strategyFrameState L hL e0 strat hb i T) c
        = challengeAt L hL T (strategyFrameState L hL e0 strat hb i T) c) :
    strategySel L hL e0 strat hb j T2 = strategySel L hL e0 strat hb j T := by
  have hh : stratHist L hL e0 strat hb j T2 = stratHist L hL e0 strat hb j T :=
    strat_hist_congr L hL e0 strat hb j T2 T hst
  have hsh : stratShapeAt L hL e0 strat hb j T2 = stratShapeAt L hL e0 strat hb j T := by
    show strat j (stratHist L hL e0 strat hb j T2)
        (fun i c => challengeAt L hL T2 (stratHist L hL e0 strat hb j T2 i) c)
      = strat j (stratHist L hL e0 strat hb j T)
        (fun i c => challengeAt L hL T (stratHist L hL e0 strat hb j T i) c)
    rw [hh]
    refine congrArg (strat j (stratHist L hL e0 strat hb j T))
      (funext fun i => funext fun c => ?_)
    rw [strat_hist_eq]
    exact hch (min i j) (Nat.min_le_right i j) c
  apply Subtype.ext
  show Transcript.frame (strategyFrameState L hL e0 strat hb j T2)
      (stratShapeAt L hL e0 strat hb j T2).1 (stratShapeAt L hL e0 strat hb j T2).2
    = Transcript.frame (strategyFrameState L hL e0 strat hb j T)
      (stratShapeAt L hL e0 strat hb j T).1 (stratShapeAt L hL e0 strat hb j T).2
  rw [hsh, hst j (le_refl j)]

/-- (2) The frame-reassignment instance of `strategy_sel_stable_gen`. -/
theorem strategy_sel_stable_of (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (k j : Nat)
    (T : OracleTable (boundedQueries L)) (b : Block)
    (hst : ∀ i, i ≤ j →
      strategyFrameState L hL e0 strat hb i
          (reassign T (strategySel L hL e0 strat hb k T) b)
        = strategyFrameState L hL e0 strat hb i T) :
    strategySel L hL e0 strat hb j (reassign T (strategySel L hL e0 strat hb k T) b)
      = strategySel L hL e0 strat hb j T :=
  strategy_sel_stable_gen L hL e0 strat hb j T _ hst
    (fun _ _ c => challenge_at_reassign_sel L hL e0 strat hb k T b _ c)

/-- (2) **EVERY STAGE OF A STRATEGY CHAIN IS FRESH ON THE GOOD EVENT.**  Exactly
the adopted `BirthdayClashBound.frame_sel_ne`, with no hypothesis on the
strategy: two stages carry different incoming digests as soon as the chain has
not clashed and has not returned to its base, and the adopted
`CommitmentOrder.frame_injective` turns that into distinct queries. -/
theorem strategy_sel_ne (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (k j : Nat) (hj : j < k)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) k) :
    strategySel L hL e0 strat hb j T ≠ strategySel L hL e0 strat hb k T := by
  intro hEq
  obtain ⟨h1, h2⟩ :=
    (mem_no_clash (strategySel L hL e0 strat hb) (avoidBase e0) k T).mp hT
  obtain ⟨hst, -, -⟩ := CommitmentOrder.frame_injective _ _ _ _ _ _ (congrArg Subtype.val hEq)
  obtain ⟨k2, rfl⟩ : ∃ k2, k = k2 + 1 := ⟨k - 1, by omega⟩
  cases j with
  | zero =>
      refine h2 k2 (by omega) ?_
      rw [avoidBase, Finset.mem_singleton]
      rw [strategy_state_succ] at hst
      exact (congrArg OuterChallenge.digestBlock hst).symm
  | succ j2 =>
      rw [strategy_state_succ, strategy_state_succ] at hst
      exact h1 j2 k2 (by omega) (by omega) (congrArg OuterChallenge.digestBlock hst)

/-- (2) **OVERWRITING THE STAGE-`k` ANSWER CHANGES NO EARLIER DIGEST.** -/
theorem strategy_state_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (k : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) k) (b : Block) :
    ∀ j, j ≤ k → ∀ i, i ≤ j →
      strategyFrameState L hL e0 strat hb i
          (reassign T (strategySel L hL e0 strat hb k T) b)
        = strategyFrameState L hL e0 strat hb i T := by
  intro j
  induction j with
  | zero =>
      intro _ i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      rfl
  | succ m ih =>
      intro hm i hi
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · exact ih (by omega) i (by omega)
      · have hie : i = m + 1 := by omega
        subst hie
        have hst : ∀ i2, i2 ≤ m →
            strategyFrameState L hL e0 strat hb i2
                (reassign T (strategySel L hL e0 strat hb k T) b)
              = strategyFrameState L hL e0 strat hb i2 T :=
          fun i2 hi2 => ih (by omega) i2 hi2
        have hsel := strategy_sel_stable_of L hL e0 strat hb k m T b hst
        rw [strategy_state_succ, strategy_state_succ]
        show blockDigest ((reassign T (strategySel L hL e0 strat hb k T) b)
            (strategySel L hL e0 strat hb m
              (reassign T (strategySel L hL e0 strat hb k T) b)))
          = blockDigest (T (strategySel L hL e0 strat hb m T))
        rw [hsel]
        exact congrArg blockDigest (reassign_off T _ _ b
          (strategy_sel_ne L hL e0 strat hb k m (by omega) T hT))

/-- (2) **A STRATEGY CHAIN IS CAUSAL AND FRESH.**  The adopted
`BirthdayClashBound.Causal`, for a chain whose queries depend on the table
through the earlier frame answers AND through the challenge answers at the
earlier digests.  No hypothesis on the strategy. -/
theorem strategy_chain_causal (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (n : Nat) :
    Causal (strategySel L hL e0 strat hb) (avoidBase e0) n := by
  constructor
  · intro k _ j hj T hT b
    exact strategy_sel_stable_of L hL e0 strat hb k j T b
      (fun i hi => strategy_state_stable L hL e0 strat hb k T hT b j hj i hi)
  · intro k _ j hj T hT
    exact strategy_sel_ne L hL e0 strat hb k j hj T hT

/-- The event that the strategy chain clashes within its first `n` stages. -/
def strategyClashEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (n : Nat) : Finset (OracleTable (boundedQueries L)) :=
  (noClash (strategySel L hL e0 strat hb) (avoidBase e0) n)ᶜ

/-- (2) **THE STAGE DIGESTS ARE PAIRWISE DISTINCT ON THE GOOD EVENT.** -/
theorem strategy_state_distinct (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (n : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) n)
    (i j : Nat) (hij : i < j) (hj : j ≤ n) :
    strategyFrameState L hL e0 strat hb i T ≠ strategyFrameState L hL e0 strat hb j T := by
  intro heq
  obtain ⟨h1, h2⟩ :=
    (mem_no_clash (strategySel L hL e0 strat hb) (avoidBase e0) n T).mp hT
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  cases i with
  | zero =>
      refine h2 b (by omega) ?_
      rw [avoidBase, Finset.mem_singleton]
      rw [strategy_state_succ] at heq
      exact (congrArg OuterChallenge.digestBlock heq).symm
  | succ a =>
      rw [strategy_state_succ, strategy_state_succ] at heq
      exact h1 a b (by omega) (by omega) (congrArg OuterChallenge.digestBlock heq)

/-- (2) **THE CLASH EVENT, SPELLED OUT IN THE DIGESTS.**  `T` is in the clash
event exactly when two of the chain's first `n + 1` stage digests -- the base
digest included -- coincide. -/
theorem strategy_clash_event_mem (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (n : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ strategyClashEvent L hL e0 strat hb n ↔
      ∃ r s : Nat, r < s ∧ s ≤ n ∧
        strategyFrameState L hL e0 strat hb r T = strategyFrameState L hL e0 strat hb s T := by
  constructor
  · intro h
    rcases (mem_clash_event (strategySel L hL e0 strat hb) (avoidBase e0) n T).mp h with
      ⟨r, s, hrs, hsn, heq⟩ | ⟨s, hsn, hin⟩
    · refine ⟨r + 1, s + 1, by omega, by omega, ?_⟩
      rw [strategy_state_succ, strategy_state_succ]
      exact congrArg blockDigest heq
    · refine ⟨0, s + 1, by omega, by omega, ?_⟩
      rw [avoidBase, Finset.mem_singleton] at hin
      rw [strategy_state_succ, hin]
      exact (block_digest_digest_block e0).symm
  · rintro ⟨r, s, hrs, hsn, heq⟩
    by_contra hnot
    rw [strategyClashEvent, Finset.not_mem_compl] at hnot
    exact strategy_state_distinct L hL e0 strat hb n T hnot r s hrs hsn heq

/-- (2) **THE BIRTHDAY BOUND FOR A STRATEGY CHAIN, FOR THE CHAIN'S CLASH EVENT.**
Under the random-oracle counting law on `boundedQueries L`, the mass of the event
that two of the chain's first `n` state digests coincide -- or that one of them is
the digest the chain started from -- is at most `n (n + 1) / 2` over the block
space, FOR EVERY STRATEGY, with the strategy quantified OUTSIDE the law but its
MESSAGES chosen inside it.

This is the adopted `BirthdayClashBound.frame_chain_clash_probability_le` with the
fixed-shape restriction removed.  The constant is unchanged. -/
theorem strategy_chain_clash_probability_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (n : Nat) :
    oracleProbability (boundedQueries L) (strategyClashEvent L hL e0 strat hb n)
      ≤ (n : ℚ) * ((n : ℚ) + 1) / 2 / (Fintype.card Block : ℚ) := by
  have h := chain_clash_probability_le (strategySel L hL e0 strat hb) (avoidBase e0) n
    (strategy_chain_causal L hL e0 strat hb n)
  rw [avoid_base_card] at h
  have hrw : ((n : ℚ) * ((1 : Nat) : ℚ) + (n : ℚ) * ((n : ℚ) - 1) / 2)
      = (n : ℚ) * ((n : ℚ) + 1) / 2 := by
    push_cast
    ring
  rw [hrw] at h
  exact h

/-- (2) Below `|Block|` the good event is not empty: tables whose whole strategy
chain is pairwise distinct exist, at every `n <= 361`. -/
theorem strategy_chain_no_clash_nonempty (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (n : Nat)
    (hn : n * (n + 1) < 2 * 65536) :
    (noClash (strategySel L hL e0 strat hb) (avoidBase e0) n).Nonempty := by
  refine no_clash_nonempty (strategySel L hL e0 strat hb) (avoidBase e0) n
    (strategy_chain_causal L hL e0 strat hb n) ?_
  rw [avoid_base_card, div_lt_one block_card_cast_pos]
  have hbb : ((n * (n + 1) : Nat) : ℚ) < 2 * 65536 := by exact_mod_cast hn
  have hcn : 65536 ≤ Fintype.card Block := block_card_gt_small 65535 (by norm_num)
  have hc : (65536 : ℚ) ≤ (Fintype.card Block : ℚ) := by exact_mod_cast hcn
  have hrw : (n : ℚ) * ((1 : Nat) : ℚ) + (n : ℚ) * ((n : ℚ) - 1) / 2
      = ((n * (n + 1) : Nat) : ℚ) / 2 := by
    push_cast
    ring
  rw [hrw]
  linarith

/-! ## 3. THE FRESH-UNIFORM CHALLENGE LEMMA -/

/-- (3) **THE STATE DIGEST OF A CHALLENGE INPUT IS UNAMBIGUOUS, AT EVERY
COUNTER.**  The first half of the adopted
`RandomOracleSqueezes.challenge_input_injective`, without its counter bounds:
`Transcript.digestBytes` occupies a fixed thirty-two-byte slot and
`Transcript.le 8` a fixed eight-byte one, so the digest can be read off the
string whatever the counters are.  This is what makes a challenge query at one
stage digest a DIFFERENT query from a challenge query at another. -/
theorem challenge_input_digest_eq (d e : Transcript.Digest) (i j : Nat)
    (h : Transcript.challengeInput d i = Transcript.challengeInput e j) : d = e := by
  simp only [Transcript.challengeInput, List.append_assoc] at h
  have h1 := List.append_cancel_left h
  have hlen : (Transcript.digestBytes d).length = (Transcript.digestBytes e).length := by
    simp only [Transcript.digestBytes, d.length_eq, e.length_eq]
  obtain ⟨hd, -⟩ := List.append_inj h1 hlen
  cases d
  cases e
  simpa only [Transcript.Digest.mk.injEq] using hd

/-- The stage-`j` challenge query at counter `c`: the string the run squeezes
round `j`'s challenge from, at the chain's own stage-`j` digest. -/
def challengeSel (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j c : Nat) (T : OracleTable (boundedQueries L)) :
    { x : Transcript.Bytes // x ∈ boundedQueries L } :=
  ⟨Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) c,
    bounded_queries_challenge L hL _ c⟩

theorem challenge_at_is_sel (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j c : Nat) (T : OracleTable (boundedQueries L)) :
    challengeAt L hL T (strategyFrameState L hL e0 strat hb j T) c
      = T (challengeSel L hL e0 strat hb j c T) := rfl

/-- (3) A frame query is never a challenge query. -/
theorem strategy_sel_ne_challenge_sel (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (m j c : Nat)
    (T : OracleTable (boundedQueries L)) :
    strategySel L hL e0 strat hb m T ≠ challengeSel L hL e0 strat hb j c T := by
  intro h
  exact frame_ne_challenge_input _ _ _ _ _ (congrArg Subtype.val h)

/-- (3) Two challenge queries at the SAME digest and different counters below the
adopted `Transcript.u64Limit` are different queries. -/
theorem challenge_sel_ne_of_counter (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c1 c2 : Nat)
    (h1 : c1 < Transcript.u64Limit) (h2 : c2 < Transcript.u64Limit) (hne : c1 ≠ c2)
    (T : OracleTable (boundedQueries L)) :
    challengeSel L hL e0 strat hb j c1 T ≠ challengeSel L hL e0 strat hb j c2 T := by
  intro h
  exact hne (challenge_input_injective _ _ _ _ h1 h2 (congrArg Subtype.val h)).2

/-- (3) **OVERWRITING THE STAGE-`j` CHALLENGE ANSWER LEAVES EVERY EARLIER
CHALLENGE ANSWER ALONE**, on the good event: an earlier stage carries a different
digest there (`strategy_state_distinct`), and a different digest gives a
different challenge input (`challenge_input_digest_eq`). -/
theorem challenge_at_reassign_challenge (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) j) (b : Block)
    (i : Nat) (hi : i < j) (c2 : Nat) :
    challengeAt L hL (reassign T (challengeSel L hL e0 strat hb j c T) b)
        (strategyFrameState L hL e0 strat hb i T) c2
      = challengeAt L hL T (strategyFrameState L hL e0 strat hb i T) c2 := by
  show (reassign T (challengeSel L hL e0 strat hb j c T) b)
      ⟨Transcript.challengeInput (strategyFrameState L hL e0 strat hb i T) c2,
        bounded_queries_challenge L hL _ c2⟩
    = T ⟨Transcript.challengeInput (strategyFrameState L hL e0 strat hb i T) c2,
        bounded_queries_challenge L hL _ c2⟩
  refine reassign_off T _ _ b ?_
  intro hEq
  have hv : Transcript.challengeInput (strategyFrameState L hL e0 strat hb i T) c2
      = Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) c :=
    congrArg Subtype.val hEq
  exact strategy_state_distinct L hL e0 strat hb j T hT i j hi (le_refl j)
    (challenge_input_digest_eq _ _ _ _ hv)

/-- (3) **THE HISTORY UP TO STAGE `j` DOES NOT LOOK AT THE STAGE-`j` CHALLENGE
ANSWERS.**  This is the precise sense in which the digest is formed BEFORE its own
challenges are read, and it is exactly the hypothesis the adopted
`BirthdayClashBound.adaptive_fresh_step` needs. -/
theorem strategy_state_challenge_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) j) (b : Block) :
    ∀ m, m ≤ j → ∀ i, i ≤ m →
      strategyFrameState L hL e0 strat hb i
          (reassign T (challengeSel L hL e0 strat hb j c T) b)
        = strategyFrameState L hL e0 strat hb i T := by
  intro m
  induction m with
  | zero =>
      intro _ i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      rfl
  | succ m2 ih =>
      intro hm i hi
      rcases Nat.lt_or_ge i (m2 + 1) with hlt | hge
      · exact ih (by omega) i (by omega)
      · have hie : i = m2 + 1 := by omega
        subst hie
        have hst : ∀ i2, i2 ≤ m2 →
            strategyFrameState L hL e0 strat hb i2
                (reassign T (challengeSel L hL e0 strat hb j c T) b)
              = strategyFrameState L hL e0 strat hb i2 T :=
          fun i2 hi2 => ih (by omega) i2 hi2
        have hsel := strategy_sel_stable_gen L hL e0 strat hb m2 T _ hst
          (fun i2 hi2 c3 =>
            challenge_at_reassign_challenge L hL e0 strat hb j c T hT b i2 (by omega) c3)
        rw [strategy_state_succ, strategy_state_succ]
        show blockDigest ((reassign T (challengeSel L hL e0 strat hb j c T) b)
            (strategySel L hL e0 strat hb m2
              (reassign T (challengeSel L hL e0 strat hb j c T) b)))
          = blockDigest (T (strategySel L hL e0 strat hb m2 T))
        rw [hsel]
        exact congrArg blockDigest (reassign_off T _ _ b
          (strategy_sel_ne_challenge_sel L hL e0 strat hb m2 j c T))

/-- (3) The stage-`j` challenge query itself does not move when its own answer is
overwritten -- condition (2) of the adopted `FreshStep`. -/
theorem challenge_sel_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j a c : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) j) (b : Block) :
    challengeSel L hL e0 strat hb j c
        (reassign T (challengeSel L hL e0 strat hb j a T) b)
      = challengeSel L hL e0 strat hb j c T := by
  apply Subtype.ext
  show Transcript.challengeInput (strategyFrameState L hL e0 strat hb j
      (reassign T (challengeSel L hL e0 strat hb j a T) b)) c
    = Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) c
  rw [strategy_state_challenge_stable L hL e0 strat hb j a T hT b j (le_refl j) j (le_refl j)]

/-- (3) The no-clash event up to stage `j` is invariant under overwriting a
stage-`j` challenge answer -- condition (1) of the adopted `FreshStep`. -/
theorem no_clash_challenge_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) j) (b : Block) :
    reassign T (challengeSel L hL e0 strat hb j c T) b
      ∈ noClash (strategySel L hL e0 strat hb) (avoidBase e0) j := by
  obtain ⟨hT1, hT2⟩ :=
    (mem_no_clash (strategySel L hL e0 strat hb) (avoidBase e0) j T).mp hT
  have hstab := strategy_state_challenge_stable L hL e0 strat hb j c T hT b
  have hval : ∀ s, s < j →
      chainVal (strategySel L hL e0 strat hb) s
          (reassign T (challengeSel L hL e0 strat hb j c T) b)
        = chainVal (strategySel L hL e0 strat hb) s T := by
    intro s hs
    have hsel := strategy_sel_stable_gen L hL e0 strat hb s T _
      (fun i hi => hstab s (le_of_lt hs) i hi)
      (fun i hi c3 =>
        challenge_at_reassign_challenge L hL e0 strat hb j c T hT b i (by omega) c3)
    show (reassign T (challengeSel L hL e0 strat hb j c T) b)
        (strategySel L hL e0 strat hb s
          (reassign T (challengeSel L hL e0 strat hb j c T) b))
      = T (strategySel L hL e0 strat hb s T)
    rw [hsel]
    exact reassign_off T _ _ b (strategy_sel_ne_challenge_sel L hL e0 strat hb s j c T)
  rw [mem_no_clash]
  refine ⟨fun r s hrs hsj => ?_, fun s hsj => ?_⟩
  · rw [hval r (by omega), hval s hsj]
    exact hT1 r s hrs hsj
  · rw [hval s hsj]
    exact hT2 s hsj

/-- (3) **THE ADAPTIVE FRESH STEP AT A CONSTANT TARGET, AS AN EQUALITY.**  The
adopted `BirthdayClashBound.adaptive_fresh_step` is an inequality because its
target set may vary with the table; at a constant target the adopted
`adaptive_fresh_step_card` is already an exact count, and the mass is exactly
`|S| / |Block|` of the conditioning event.  THIS IS UNIFORMITY. -/
theorem adaptive_fresh_step_uniform {Q : Finset Transcript.Bytes} {A : Finset (OracleTable Q)}
    {sel : OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} (S : Finset Block)
    (h : FreshStep Q A sel (fun _ => S)) :
    oracleProbability Q (A.filter (fun T => T (sel T) ∈ S))
      = (S.card : ℚ) / (Fintype.card Block : ℚ) * oracleProbability Q A := by
  have h2 := adaptive_fresh_step_card h
  simp only [Finset.sum_const, smul_eq_mul] at h2
  have hc : ((A.filter (fun T => T (sel T) ∈ S)).card : ℚ) * (Fintype.card Block : ℚ)
      = (S.card : ℚ) * (A.card : ℚ) := by
    have h3 : (A.filter (fun T => T (sel T) ∈ S)).card * Fintype.card Block
        = S.card * A.card := by
      rw [h2, Nat.mul_comm]
    exact_mod_cast h3
  rw [oracleProbability, oracleProbability, div_mul_div_comm,
    div_eq_div_iff (oracle_card_cast_pos Q).ne'
      (mul_ne_zero block_card_cast_ne (oracle_card_cast_pos Q).ne')]
  linear_combination (Fintype.card (OracleTable Q) : ℚ) * hc

/-- (3) **THE STAGE-`j` CHALLENGE QUERY IS AN ADAPTIVE FRESH STEP.** -/
theorem strategy_challenge_fresh_step (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat) (S : Finset Block) :
    FreshStep (boundedQueries L) (noClash (strategySel L hL e0 strat hb) (avoidBase e0) j)
      (challengeSel L hL e0 strat hb j c) (fun _ => S) :=
  ⟨fun T hT b => no_clash_challenge_reassign L hL e0 strat hb j c T hT b,
   fun T hT b => challenge_sel_stable L hL e0 strat hb j c c T hT b,
   fun _ _ _ => rfl⟩

/-- (3) **THE FRESH-UNIFORM CHALLENGE LEMMA, ONE COUNTER.**  Conditioned on the
no-clash event up to stage `j`, the answer at the stage-`j` challenge input is
UNIFORM on `Block`.

The conditioning is on THAT ONE EVENT, and on nothing else: it is not a
conditioning on the history's sigma-algebra.  The history-fibre form -- the same
statement conditioned on a prescribed value of every frame answer below `j` and
of every challenge answer at the digests below `j` -- is NOT stated here, though
it would follow from the same `FreshStep` lemmas.

This is the adaptive analogue of the adopted
`RandomOracleSqueezes.draw_at_fixed_digests_is_uniform`: there the block digests
are quantified OUTSIDE the law, here the digest is the chain's own. -/
theorem strategy_challenge_fresh_uniform (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j c : Nat) (S : Finset Block) :
    oracleProbability (boundedQueries L)
        ((noClash (strategySel L hL e0 strat hb) (avoidBase e0) j).filter
          (fun T => T (challengeSel L hL e0 strat hb j c T) ∈ S))
      = (S.card : ℚ) / (Fintype.card Block : ℚ)
        * oracleProbability (boundedQueries L)
            (noClash (strategySel L hL e0 strat hb) (avoidBase e0) j) :=
  adaptive_fresh_step_uniform S (strategy_challenge_fresh_step L hL e0 strat hb j c S)

open Classical in
/-- The fibre of the no-clash event on which the stage-`j` challenge answers at a
finite set `C` of counters take the prescribed values `w`. -/
noncomputable def challengeFibre (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j : Nat) (C : Finset Nat)
    (w : Nat → Block) : Finset (OracleTable (boundedQueries L)) :=
  (noClash (strategySel L hL e0 strat hb) (avoidBase e0) j).filter
    (fun T => ∀ c ∈ C, T (challengeSel L hL e0 strat hb j c T) = w c)

/-- (3) **THE FRESH-UNIFORM CHALLENGE LEMMA, JOINTLY OVER A FINITE COUNTER SET.**
Conditioned on the chain's no-clash event up to stage `j`, the stage-`j`
challenge answers at any finite set of counters below the adopted
`Transcript.u64Limit` are JOINTLY uniform: every prescription `w` has mass
`1 / |Block| ^ |C|` of the conditioning event.

The induction peels one counter at a time; the peeled coordinate is fresh because
the digest does not depend on its own challenge answers
(`strategy_state_challenge_stable`) and because different counters at the same
digest are different queries (`challenge_sel_ne_of_counter`). -/
theorem strategy_challenge_joint_uniform (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j : Nat) (w : Nat → Block) :
    ∀ C : Finset Nat, (∀ c ∈ C, c < Transcript.u64Limit) →
      oracleProbability (boundedQueries L) (challengeFibre L hL e0 strat hb j C w)
        = oracleProbability (boundedQueries L)
            (noClash (strategySel L hL e0 strat hb) (avoidBase e0) j)
          / (Fintype.card Block : ℚ) ^ C.card := by
  intro C
  induction C using Finset.induction_on with
  | empty =>
      intro _
      have hset : challengeFibre L hL e0 strat hb j ∅ w
          = noClash (strategySel L hL e0 strat hb) (avoidBase e0) j := by
        rw [challengeFibre]
        exact Finset.filter_true_of_mem
          (fun _ _ c hc => absurd hc (Finset.not_mem_empty c))
      rw [hset, Finset.card_empty, pow_zero, div_one]
  | @insert a C0 ha ih =>
      intro hC
      have hCa : a < Transcript.u64Limit := hC a (Finset.mem_insert_self a C0)
      have hC0 : ∀ c ∈ C0, c < Transcript.u64Limit :=
        fun c hc => hC c (Finset.mem_insert_of_mem hc)
      have hset : challengeFibre L hL e0 strat hb j (insert a C0) w
          = (challengeFibre L hL e0 strat hb j C0 w).filter
              (fun T => T (challengeSel L hL e0 strat hb j a T) ∈ ({w a} : Finset Block)) := by
        apply Finset.ext
        intro T
        simp only [challengeFibre, Finset.mem_filter, Finset.forall_mem_insert,
          Finset.mem_singleton]
        tauto
      have hfresh : FreshStep (boundedQueries L) (challengeFibre L hL e0 strat hb j C0 w)
          (challengeSel L hL e0 strat hb j a) (fun _ => ({w a} : Finset Block)) := by
        refine ⟨fun T hT b => ?_, fun T hT b => ?_, fun _ _ _ => rfl⟩
        · obtain ⟨hTn, hTf⟩ := Finset.mem_filter.mp hT
          refine Finset.mem_filter.mpr
            ⟨no_clash_challenge_reassign L hL e0 strat hb j a T hTn b, ?_⟩
          intro c hc
          rw [challenge_sel_stable L hL e0 strat hb j a c T hTn b]
          rw [reassign_off T _ _ b
            (challenge_sel_ne_of_counter L hL e0 strat hb j c a (hC0 c hc) hCa
              (fun hca => ha (hca ▸ hc)) T)]
          exact hTf c hc
        · exact challenge_sel_stable L hL e0 strat hb j a a T
            (Finset.mem_filter.mp hT).1 b
      rw [hset, adaptive_fresh_step_uniform _ hfresh, ih hC0,
        Finset.card_singleton, Finset.card_insert_of_not_mem ha, Nat.cast_one, pow_succ,
        div_mul_eq_mul_div, one_mul, div_div]

/-! ## 4. THE STRATEGIC OUTER PROVER -/

/-- The five frames of one coupled round, as a function of the round's MESSAGE
rather than of a message list.  `round_shape_at_is_msg` is the identification
with the adopted `BirthdayClashBound.roundShapeAt`, hence with the adopted
`InstalledRoundCommit.roundFrames`: nothing is re-serialized. -/
def roundShapeMsg (m : Verifier.CoupledMessage) (i : Nat) :
    Nat → Transcript.Byte × Transcript.Bytes
  | 0 => (1, Transcript.ascii "outer-sumcheck-lockstep-round-v3")
  | 1 => (2, Transcript.le 8 i)
  | 2 => (6, OuterAdapter.encodedVec m.1)
  | 3 => (6, OuterAdapter.encodedVec m.2)
  | _ => (1, Transcript.ascii "outer-sumcheck-lockstep-challenges-v3")

theorem round_shape_at_is_msg (ms : List Verifier.CoupledMessage) (i j : Nat) :
    roundShapeAt ms i j = roundShapeMsg ((ms.get? i).getD ([], [])) i j := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | (_ + 4) => rfl

/-- (4) **THE FIVE PAYLOADS OF ONE ROUND, BOUNDED.**  Two domain separators of
`32` and `37` bytes, the eight-byte round counter, and the two message cells,
whose lengths are `8 + 24 * length` by the adopted
`OuterAdapter.encoded_vector_length`.  This is the per-message form of the
adopted `BirthdayClashBound.round_shape_payload_bound_at_envelope`, which is
stated for a message LIST. -/
theorem round_shape_msg_payload_bound (L : Nat) (m : Verifier.CoupledMessage)
    (h98 : 98 ≤ L) (hlog : 69 + 24 * m.1.length ≤ L) (hgate : 69 + 24 * m.2.length ≤ L)
    (i j : Nat) :
    61 + (roundShapeMsg m i j).2.length ≤ L := by
  have hr : (Transcript.ascii "outer-sumcheck-lockstep-round-v3").length = 32 := by decide
  have hc : (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3").length = 37 := by decide
  match j with
  | 0 =>
      show 61 + (Transcript.ascii "outer-sumcheck-lockstep-round-v3").length ≤ L
      omega
  | 1 =>
      show 61 + (Transcript.le 8 i).length ≤ L
      rw [Transcript.le_length]
      omega
  | 2 =>
      show 61 + (OuterAdapter.encodedVec m.1).length ≤ L
      rw [OuterAdapter.encoded_vector_length]
      omega
  | 3 =>
      show 61 + (OuterAdapter.encodedVec m.2).length ≤ L
      rw [OuterAdapter.encoded_vector_length]
      omega
  | (_ + 4) =>
      show 61 + (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3").length ≤ L
      omega

/-- **THE STRATEGIC OUTER PROVER.**  The adopted twenty-two-frame relation
prefix, and then, for coupled round `r`, the five frames of the message
`S r ch` -- a message the prover COMPOSES OUT OF THE CHALLENGE ANSWERS it has
already seen.  The history argument is discarded: only the challenge answers
matter, and the digests they are read at are supplied by the chain itself. -/
def strategicShape (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) : Strategy :=
  fun k _ ch =>
    if k < 22 then messageShape (CommitmentOrder.gateChallengeFrames c s) k
    else roundShapeMsg (S ((k - 22) / 5) ch) ((k - 22) / 5) ((k - 22) % 5)

theorem strategic_shape_apply (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (k : Nat)
    (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    strategicShape c s S k h ch
      = if k < 22 then messageShape (CommitmentOrder.gateChallengeFrames c s) k
        else roundShapeMsg (S ((k - 22) / 5) ch) ((k - 22) / 5) ((k - 22) % 5) := rfl

/-- (4) **THE LENGTH BUDGET OF A STRATEGIC OUTER PROVER, DISCHARGED.**  HONESTY
(vi) says `StrategyBounded` is a hypothesis; for the strategic prover it is not a
bare hypothesis but the SAME arithmetic the adopted
`ConcreteChainThreading.LengthBudget` collects for a fixed prover.  The twenty-two
prefix payloads are the adopted `ConcreteChainThreading.prefix_message_payload_bound`
(the proof's and the config's own data); the round payloads are the adopted degree
bounds -- `5` cells on the log lane and `quotientDegree + 2` on the gate lane --
now quantified over EVERY challenge history the strategy may see, which is exactly
what adaptivity costs.  `189 + 24 * quotientDegree <= L` is the adopted envelope
budget of `BirthdayClashBound.round_shape_payload_bound_at_envelope`. -/
theorem strategic_shape_bounded (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) (quotientDegree : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hlog : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).1.length ≤ 5)
    (hgate : ∀ (r : Nat) (ch : Nat → Nat → Block), (S r ch).2.length ≤ quotientDegree + 2)
    (hL : 189 + 24 * quotientDegree ≤ L) :
    StrategyBounded L (strategicShape c s S) := by
  intro k h ch
  rw [strategic_shape_apply]
  by_cases hk : k < 22
  · rw [if_pos hk]
    exact hpre k hk
  · rw [if_neg hk]
    have h1 : (S ((k - 22) / 5) ch).1.length ≤ 5 := hlog _ _
    have h2 : (S ((k - 22) / 5) ch).2.length ≤ quotientDegree + 2 := hgate _ _
    exact round_shape_msg_payload_bound L (S ((k - 22) / 5) ch) (by omega) (by omega)
      (by omega) _ _

/-- **THE PROTOCOL RESTRICTION ON A STRATEGIC PROVER.**  Round `r`'s message reads
only the challenge answers at the digests of the stages up to `22 + 5 r` -- the
digest round `r`'s own two challenges are squeezed from, by the adopted
`OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`.
The chain bound of section 2 needs NO such restriction; it is needed only to
identify the five frames of a round with ONE message. -/
def RoundCausal (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage) : Prop :=
  ∀ (r : Nat) (ch1 ch2 : Nat → Nat → Block),
    (∀ j, j ≤ 22 + 5 * r → ch1 j = ch2 j) → S r ch1 = S r ch2

/-- The challenge answers round `r` of a strategic prover reads, at one table. -/
def strategicChallenges (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (r : Nat)
    (T : OracleTable (boundedQueries L)) : Nat → Nat → Block :=
  fun j cnt => challengeAt L hL T
    (strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
      (min j (22 + 5 * r)) T) cnt

/-- (4) **WHAT THE STRATEGIC PROVER READS ARE EXACTLY THE QUERIES SECTION 3
BOUNDS.**  Round `r`'s reads at a stage `j <= 22 + 5 r` are the table's values at
`challengeSel ... j cnt` -- the very queries `strategy_challenge_fresh_uniform`
and `strategy_challenge_joint_uniform` prove uniform on the no-clash event. -/
theorem strategic_challenges_is_sel (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (r : Nat)
    (T : OracleTable (boundedQueries L)) (j cnt : Nat) (hj : j ≤ 22 + 5 * r) :
    strategicChallenges L hL c s S hb r T j cnt
      = T (challengeSel L hL OuterInitial.zeroDigest (strategicShape c s S) hb j cnt T) := by
  show challengeAt L hL T (strategyFrameState L hL OuterInitial.zeroDigest
      (strategicShape c s S) hb (min j (22 + 5 * r)) T) cnt = _
  rw [Nat.min_eq_left hj]
  exact challenge_at_is_sel L hL OuterInitial.zeroDigest (strategicShape c s S) hb j cnt T

/-- The first `n` messages of a function of the round index, as a list. -/
def messagesFrom (f : Nat → Verifier.CoupledMessage) (i : Nat) :
    Nat → List Verifier.CoupledMessage
  | 0 => []
  | n + 1 => f i :: messagesFrom f (i + 1) n

theorem messages_from_length (f : Nat → Verifier.CoupledMessage) :
    ∀ (i n : Nat), (messagesFrom f i n).length = n
  | _, 0 => rfl
  | i, n + 1 => by
      show (messagesFrom f (i + 1) n).length + 1 = n + 1
      rw [messages_from_length f (i + 1) n]

theorem messages_from_get (f : Nat → Verifier.CoupledMessage) :
    ∀ (i n r : Nat), r < n → (messagesFrom f i n).get? r = some (f (i + r))
  | _, 0, _, hr => absurd hr (Nat.not_lt_zero _)
  | _, _ + 1, 0, _ => rfl
  | i, n + 1, r + 1, hr => by
      show (messagesFrom f (i + 1) n).get? r = some (f (i + (r + 1)))
      rw [messages_from_get f (i + 1) n r (by omega),
        show i + 1 + r = i + (r + 1) from by omega]

theorem messages_from_get_none (f : Nat → Verifier.CoupledMessage) :
    ∀ (i n r : Nat), n ≤ r → (messagesFrom f i n).get? r = none
  | _, 0, _, _ => rfl
  | _, _ + 1, 0, hr => absurd hr (by omega)
  | i, n + 1, r + 1, hr => by
      show (messagesFrom f (i + 1) n).get? r = none
      exact messages_from_get_none f (i + 1) n r (by omega)

/-- **THE MESSAGES A STRATEGIC PROVER ACTUALLY PRODUCES AT ONE TABLE.**  This list
is a function of `T`: that is exactly the difference from a fixed prover, whose
message list is quantified outside the law. -/
def realizedMessages (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) : List Verifier.CoupledMessage :=
  messagesFrom (fun r => S r (strategicChallenges L hL c s S hb r T)) 0 N

theorem realized_messages_length (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    (realizedMessages L hL c s S hb N T).length = N :=
  messages_from_length _ 0 N

theorem realized_messages_get (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) (r : Nat) (hr : r < N) :
    (realizedMessages L hL c s S hb N T).get? r
      = some (S r (strategicChallenges L hL c s S hb r T)) := by
  rw [realizedMessages, messages_from_get _ 0 N r hr, Nat.zero_add]

theorem realized_messages_get_none (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) (r : Nat) (hr : N ≤ r) :
    (realizedMessages L hL c s S hb N T).get? r = none :=
  messages_from_get_none _ 0 N r hr

/-- (4) **THE FIXED-SHAPE CHAIN'S LENGTH HYPOTHESIS IS ALREADY IN
`StrategyBounded`.**  The `hlen` argument every chain theorem of the adopted
`BirthdayClashBound` carries is not an extra assumption for a strategic prover: it
is derivable from `hb` alone, at the realized messages of any table.  The prefix
frames and the frames of the rounds the strategy actually plays are `hb`'s own
instances; past the end of the list the shape is the empty message, whose widest
payload is the `37`-byte round separator, and `98 <= L` is itself an instance of
`hb`. -/
theorem strategic_hlen_of_bounded (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ k, 61 + (prefixRoundShape c s (realizedMessages L hL c s S hb N T) k).2.length ≤ L := by
  have h98 : 98 ≤ L := by
    have h := hb 26 (fun _ => OuterInitial.zeroDigest)
      (fun _ _ => OuterChallenge.digestBlock (indexDigest 0))
    rw [strategic_shape_apply, if_neg (by omega : ¬ (26 < 22))] at h
    have hc : (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3").length = 37 := by decide
    have h2 : 61 + (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3").length ≤ L := h
    omega
  intro k
  by_cases hk : k < 22
  · rw [prefix_round_shape_prefix c s _ k hk]
    have h := hb k (fun _ => OuterInitial.zeroDigest)
      (fun _ _ => OuterChallenge.digestBlock (indexDigest 0))
    rw [strategic_shape_apply, if_pos hk] at h
    exact h
  · rw [prefixRoundShape, if_neg hk, roundShape, round_shape_at_is_msg]
    by_cases hr : (k - 22) / 5 < N
    · rw [realized_messages_get L hL c s S hb N T _ hr]
      have h := hb k (stratHist L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T)
        (strategicChallenges L hL c s S hb ((k - 22) / 5) T)
      rw [strategic_shape_apply, if_neg hk] at h
      exact h
    · rw [realized_messages_get_none L hL c s S hb N T _ (by omega)]
      have he1 : (([], []) : Verifier.CoupledMessage).1.length = 0 := rfl
      have he2 : (([], []) : Verifier.CoupledMessage).2.length = 0 := rfl
      exact round_shape_msg_payload_bound L ([], []) h98 (by omega) (by omega) _ _

theorem strat_shape_at_strategic (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    stratShapeAt L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T
      = strategicShape c s S k
          (stratHist L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T)
          (fun i cnt => challengeAt L hL T
            (stratHist L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T i) cnt) :=
  rfl

/-- (4) **THE STRATEGIC SHAPE IS THE FIXED SHAPE OF THE REALIZED MESSAGES.**  At
one table, stage `k` of the strategic prover plays the very frame the adopted
`BirthdayClashBound.prefixRoundShape` plays for the message list the strategy
produced at that table.  `RoundCausal` is what makes the five stages of a round
agree on ONE message. -/
theorem strategic_shape_agrees (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S) (N : Nat)
    (T : OracleTable (boundedQueries L)) (k : Nat) (hk : k < 22 + 5 * N) :
    stratShapeAt L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T
      = prefixRoundShape c s (realizedMessages L hL c s S hb N T) k := by
  rw [strat_shape_at_strategic, strategic_shape_apply]
  by_cases hk22 : k < 22
  · rw [if_pos hk22, prefix_round_shape_prefix c s _ k hk22]
  · rw [if_neg hk22, prefixRoundShape, if_neg hk22, roundShape, round_shape_at_is_msg]
    have hr : (k - 22) / 5 < N := by omega
    have hmsg : ((realizedMessages L hL c s S hb N T).get? ((k - 22) / 5)).getD ([], [])
        = S ((k - 22) / 5) (fun i cnt => challengeAt L hL T
            (stratHist L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T i) cnt) := by
      rw [realized_messages_get L hL c s S hb N T _ hr]
      show S ((k - 22) / 5) (strategicChallenges L hL c s S hb ((k - 22) / 5) T) = _
      refine hS ((k - 22) / 5) _ _ (fun j hj => ?_)
      funext cnt
      show challengeAt L hL T (strategyFrameState L hL OuterInitial.zeroDigest
          (strategicShape c s S) hb (min j (22 + 5 * ((k - 22) / 5))) T) cnt
        = challengeAt L hL T (stratHist L hL OuterInitial.zeroDigest
          (strategicShape c s S) hb k T j) cnt
      rw [strat_hist_of_le L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T j
          (by omega),
        Nat.min_eq_left hj]
    rw [hmsg]

/-- (4) **THE STRATEGIC PROVER'S CHAIN IS A STRATEGY CHAIN, AND, TABLE BY TABLE,
IT IS THE FIXED-SHAPE CHAIN OF THE MESSAGES IT PRODUCED.**

This identity is why the fixed-prover bound does NOT already cover an adaptive
prover: `realizedMessages L hL c s S hb N T` VARIES WITH THE TABLE, whereas the
adopted `ConcreteChainThreading.run_clash_probability_le` quantifies its message
list outside the law.  Section 2's bound is uniform in the strategy and does
cover it. -/
theorem strategic_prover_chain_is_strategy_chain (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement)
    (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ k, k ≤ 22 + 5 * N →
      strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb k T
        = frameState L OuterInitial.zeroDigest
            (prefixRoundShape c s (realizedMessages L hL c s S hb N T))
            (strategic_hlen_of_bounded L hL c s S hb N T) k T := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      rw [strategy_state_succ, frame_state_succ]
      refine congrArg blockDigest (congrArg T (Subtype.ext ?_))
      show Transcript.frame
          (strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb m T)
          (stratShapeAt L hL OuterInitial.zeroDigest (strategicShape c s S) hb m T).1
          (stratShapeAt L hL OuterInitial.zeroDigest (strategicShape c s S) hb m T).2
        = Transcript.frame
          (frameState L OuterInitial.zeroDigest
            (prefixRoundShape c s (realizedMessages L hL c s S hb N T))
            (strategic_hlen_of_bounded L hL c s S hb N T) m T)
          (prefixRoundShape c s (realizedMessages L hL c s S hb N T) m).1
          (prefixRoundShape c s (realizedMessages L hL c s S hb N T) m).2
      rw [ih (by omega), strategic_shape_agrees L hL c s S hb hS N T m (by omega)]

/-- (4) **THE CHAIN REACHES THE ADOPTED `OuterInitial.derive` DIGEST.** -/
theorem strategic_prover_chain_base (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb 22 T
      = (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state.digest := by
  rw [strategic_prover_chain_is_strategy_chain L hL c s S hb hS N T 22 (by omega),
    prefix_state_is_derive_digest]

/-- (4) **FIVE STAGES OF THE STRATEGIC CHAIN ARE ONE ADOPTED COUPLED ROUND**, at
the message the strategy chose from the challenge history. -/
theorem strategic_prover_chain_step (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S) (N : Nat)
    (T : OracleTable (boundedQueries L)) (r : Nat) (hr : r < N) :
    strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
        (22 + (5 * r + 5)) T
      = stageFive (hashOf (boundedQueries L) T)
          (strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
            (22 + 5 * r) T) r (S r (strategicChallenges L hL c s S hb r T)) := by
  rw [strategic_prover_chain_is_strategy_chain L hL c s S hb hS N T (22 + (5 * r + 5))
      (by omega),
    strategic_prover_chain_is_strategy_chain L hL c s S hb hS N T (22 + 5 * r) (by omega),
    prefix_round_chain_step, realized_messages_get L hL c s S hb N T r hr]
  rfl

/-- (4) **THE STRATEGIC PROVER'S CHAIN IS THE RUN'S OWN COMMIT CHAIN.**  The
adopted `InstalledRoundCommit.concreteFinal` of the messages the strategy
produced, from the adopted `OuterInitial.derive` state.  This is
`ConcreteChainThreading.chain_model_is_the_run_chain` for a strategic prover; the
list bookkeeping is the adopted
`ConcreteChainThreading.concrete_final_take_succ`, which is already general in the
message list. -/
theorem strategic_prover_chain_is_the_run_chain (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) (hS : RoundCausal S) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ r, r ≤ N →
      strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (22 + 5 * r) T
        = (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)
            (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state 0
            ((realizedMessages L hL c s S hb N T).take r)).digest := by
  intro r
  induction r with
  | zero =>
      intro _
      rw [show 22 + 5 * 0 = 22 from by omega,
        strategic_prover_chain_base L hL c s S hb hS N T]
      rfl
  | succ r2 ih =>
      intro hr2
      have hr : r2 < (realizedMessages L hL c s S hb N T).length := by
        rw [realized_messages_length]
        omega
      rw [ConcreteChainThreading.concrete_final_take_succ (hashOf (boundedQueries L) T)
          (realizedMessages L hL c s S hb N T) _ 0 r2 hr]
      show strategyFrameState L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (22 + 5 * (r2 + 1)) T
        = (OuterAdapter.roundCommitted (hashOf (boundedQueries L) T)
            (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)
              (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state 0
              ((realizedMessages L hL c s S hb N T).take r2)) (0 + r2)
            (((realizedMessages L hL c s S hb N T).get? r2).getD ([], [])).1
            (((realizedMessages L hL c s S hb N T).get? r2).getD ([], [])).2).digest
      rw [round_commit_is_stage_five, Nat.zero_add, ← ih (by omega),
        realized_messages_get L hL c s S hb N T r2 (by omega),
        show 22 + 5 * (r2 + 1) = 22 + (5 * r2 + 5) from by omega,
        strategic_prover_chain_step L hL c s S hb hS N T r2 (by omega)]
      rfl

/-! ## 5. NON-VACUITY, AND THE CLOSED INSTANCE -/

/-- (5) The adopted `BirthdayClashBound.constantTable` drives EVERY strategy
chain to the same digest at every stage. -/
theorem constant_table_strategy_state (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (k : Nat) :
    strategyFrameState L hL e0 strat hb (k + 1) (constantTable L) = OuterInitial.zeroDigest := by
  rw [strategy_state_succ]
  exact block_digest_digest_block OuterInitial.zeroDigest

/-- (5) **THE CLASH EVENT IS NOT EMPTY, FOR EVERY STRATEGY.**  So section 2 does
not bound an empty event, and the conditioning events of section 3 are the
complements of a genuinely inhabited one. -/
theorem constant_table_strategy_clashes (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (n : Nat) (hn : 2 ≤ n) :
    constantTable L ∈ strategyClashEvent L hL e0 strat hb n := by
  rw [strategyClashEvent, mem_clash_event]
  refine Or.inl ⟨0, 1, by omega, by omega, ?_⟩
  have h0 : blockDigest (chainVal (strategySel L hL e0 strat hb) 0 (constantTable L))
      = blockDigest (chainVal (strategySel L hL e0 strat hb) 1 (constantTable L)) := by
    rw [← strategy_state_succ, ← strategy_state_succ,
      constant_table_strategy_state L hL e0 strat hb 0,
      constant_table_strategy_state L hL e0 strat hb 1]
  exact congrArg OuterChallenge.digestBlock h0

/-- **A STRATEGY THAT GENUINELY READS THE ORACLE.**  Its payload at stage `k` IS
the thirty-two bytes of the challenge block the oracle answers at the stage-`k`
digest and counter `0`.  It is not a fixed shape for any choice of `shape`
(`first_challenge_strategy_is_not_constant`), and its chain is bounded all the
same. -/
def firstChallengeStrategy : Strategy :=
  fun k _ ch => (1, (ch k 0).val)

theorem first_challenge_strategy_bounded (L : Nat) (hL : 93 ≤ L) :
    StrategyBounded L firstChallengeStrategy := by
  intro k h ch
  have h32 : (ch k 0).val.length = 32 := (ch k 0).property
  show 61 + (ch k 0).val.length ≤ L
  omega

/-- (5) **IT IS NOT A FIXED PROVER.**  No `shape` reproduces it: two histories
whose challenge answers differ give different payloads, by the adopted
`Transcript.le_injective_bounded` through
`RandomOracleSqueezes.indexDigest`. -/
theorem first_challenge_strategy_is_not_constant
    (shape : Nat → Transcript.Byte × Transcript.Bytes) :
    firstChallengeStrategy ≠ constStrategy shape := by
  intro h
  have h0 := congrFun (congrFun (congrFun h 0) (fun _ => OuterInitial.zeroDigest))
    (fun _ _ => OuterChallenge.digestBlock (indexDigest 0))
  have h1 := congrFun (congrFun (congrFun h 0) (fun _ => OuterInitial.zeroDigest))
    (fun _ _ => OuterChallenge.digestBlock (indexDigest 1))
  have hle : Transcript.le 32 0 = Transcript.le 32 1 := congrArg Prod.snd (h0.trans h1.symm)
  exact absurd (Transcript.le_injective_bounded 32 0 1
    (small_lt_byte_power 0 (by norm_num)) (small_lt_byte_power 1 (by norm_num)) hle) (by decide)

/-- (5) **THE BOUND FOR THAT STRATEGY**, for the chain's clash event.  The query
bound `64 <= L` is not a separate hypothesis: it is implied by the payload budget
`93 <= L` this strategy needs. -/
theorem first_challenge_chain_clash_probability_le (L : Nat) (hL2 : 93 ≤ L)
    (e0 : Transcript.Digest) (n : Nat) :
    oracleProbability (boundedQueries L)
        (strategyClashEvent L (Nat.le_trans (by norm_num) hL2) e0 firstChallengeStrategy
          (first_challenge_strategy_bounded L hL2) n)
      ≤ (n : ℚ) * ((n : ℚ) + 1) / 2 / (Fintype.card Block : ℚ) :=
  strategy_chain_clash_probability_le L (Nat.le_trans (by norm_num) hL2) e0
    firstChallengeStrategy (first_challenge_strategy_bounded L hL2) n

/-- (5) **THE CLOSED INSTANCE.**  At the envelope's `22 + 5 * 13 = 87` stages --
the twenty-two relation-prefix frames and five frames for each of thirteen
coupled rounds -- the chain's clash mass is at most `3828 / |Block|`, FOR THE
CHAIN'S CLASH EVENT and FOR EVERY STRATEGY.  This is the SAME constant the
adopted `BirthdayClashBound.prefix_round_digest_clash_mass_at_thirteen` gives for
a fixed prover.  `Fintype.card Block` is never evaluated. -/
theorem strategy_chain_clash_at_eighty_seven (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) :
    oracleProbability (boundedQueries L) (strategyClashEvent L hL e0 strat hb 87)
      ≤ (3828 : ℚ) / (Fintype.card Block : ℚ) := by
  have h := strategy_chain_clash_probability_le L hL e0 strat hb 87
  rw [show ((87 : Nat) : ℚ) * (((87 : Nat) : ℚ) + 1) / 2 = (3828 : ℚ) from by norm_num] at h
  exact h

/-- (5) The closed instance for a STRATEGIC OUTER PROVER at the envelope's
thirteen coupled rounds. -/
theorem strategic_prover_chain_clash_at_thirteen (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (S : Nat → (Nat → Nat → Block) → Verifier.CoupledMessage)
    (hb : StrategyBounded L (strategicShape c s S)) :
    oracleProbability (boundedQueries L)
        (strategyClashEvent L hL OuterInitial.zeroDigest (strategicShape c s S) hb
          (22 + 5 * 13))
      ≤ (3828 : ℚ) / (Fintype.card Block : ℚ) := by
  rw [show 22 + 5 * 13 = 87 from by omega]
  exact strategy_chain_clash_at_eighty_seven L hL OuterInitial.zeroDigest
    (strategicShape c s S) hb

/-- **AN ADAPTIVE ROUND MESSAGE.**  Round `r`'s gate-lane cell is the prefix of
`m.2` whose LENGTH the prover reads off round `r`'s own challenge block: the
adopted `Transcript.fromLe` of the thirty-two bytes the oracle answers at counter
`0` of the stage-`22 + 5 r` digest.  The message is therefore a genuine function
of the challenge history -- `challenge_truncated_message_depends` -- while both of
its cells stay inside the adopted degree bounds, and nothing is re-serialized:
the five frames are still `roundShapeMsg`. -/
def challengeTruncatedMessage (m : Verifier.CoupledMessage) (r : Nat)
    (ch : Nat → Nat → Block) : Verifier.CoupledMessage :=
  (m.1, m.2.take (Transcript.fromLe (ch (22 + 5 * r) 0).val))

/-- (5) It obeys the protocol's causality: round `r` reads only stage `22 + 5 r`. -/
theorem challenge_truncated_round_causal (m : Verifier.CoupledMessage) :
    RoundCausal (challengeTruncatedMessage m) := by
  intro r ch1 ch2 h
  show (m.1, m.2.take (Transcript.fromLe (ch1 (22 + 5 * r) 0).val))
    = (m.1, m.2.take (Transcript.fromLe (ch2 (22 + 5 * r) 0).val))
  rw [h (22 + 5 * r) (le_refl (22 + 5 * r))]

/-- (5) Both cells stay inside the cells of `m`, at every challenge history. -/
theorem challenge_truncated_message_lengths (m : Verifier.CoupledMessage) (r : Nat)
    (ch : Nat → Nat → Block) :
    (challengeTruncatedMessage m r ch).1.length = m.1.length ∧
      (challengeTruncatedMessage m r ch).2.length ≤ m.2.length := by
  refine ⟨rfl, ?_⟩
  show (m.2.take (Transcript.fromLe (ch (22 + 5 * r) 0).val)).length ≤ m.2.length
  rw [List.length_take]
  exact Nat.min_le_right _ _

/-- (5) **IT IS GENUINELY ADAPTIVE.**  Two challenge histories that differ at
round `r`'s own digest give DIFFERENT messages, as soon as the gate-lane cell is
not empty: the adopted `Transcript.fromLe_le_roundtrip` separates the two index
digests' blocks at `0` and `1`. -/
theorem challenge_truncated_message_depends (m : Verifier.CoupledMessage)
    (hm : m.2 ≠ []) (r : Nat) :
    challengeTruncatedMessage m r (fun _ _ => OuterChallenge.digestBlock (indexDigest 0))
      ≠ challengeTruncatedMessage m r
          (fun _ _ => OuterChallenge.digestBlock (indexDigest 1)) := by
  have h0 : Transcript.fromLe (Transcript.le 32 0) = 0 :=
    Transcript.fromLe_le_roundtrip 32 0 (small_lt_byte_power 0 (by norm_num))
  have h1 : Transcript.fromLe (Transcript.le 32 1) = 1 :=
    Transcript.fromLe_le_roundtrip 32 1 (small_lt_byte_power 1 (by norm_num))
  intro h
  have h2 : m.2.take (Transcript.fromLe (Transcript.le 32 0))
      = m.2.take (Transcript.fromLe (Transcript.le 32 1)) := congrArg Prod.snd h
  rw [h0, h1] at h2
  cases hmc : m.2 with
  | nil => exact hm hmc
  | cons a rest =>
      rw [hmc] at h2
      exact List.noConfusion (h2 : ([] : List Verifier.Ext3) = [a])

/-- (5) **ITS LENGTH BUDGET, DISCHARGED.**  Not a hypothesis: the adopted prefix
bound plus the adopted degree bounds on the two cells of `m`. -/
theorem challenge_truncated_strategic_bounded (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (quotientDegree : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hlog : m.1.length ≤ 5) (hgate : m.2.length ≤ quotientDegree + 2)
    (hLq : 189 + 24 * quotientDegree ≤ L) :
    StrategyBounded L (strategicShape c s (challengeTruncatedMessage m)) :=
  strategic_shape_bounded L c s (challengeTruncatedMessage m) quotientDegree hpre
    (fun r ch => by
      rw [(challenge_truncated_message_lengths m r ch).1]
      exact hlog)
    (fun r ch =>
      Nat.le_trans (challenge_truncated_message_lengths m r ch).2 hgate)
    hLq

/-- (5) **THE CLOSED INSTANCE FOR A GENUINELY ADAPTIVE STRATEGIC PROVER, WITH THE
LENGTH BUDGET DISCHARGED.**  `hb` is not a hypothesis here and neither is
`64 <= L`: the first is `challenge_truncated_strategic_bounded`, built from the
adopted prefix bound and the adopted degree bounds, and the second follows from
the envelope budget.  The prover's round messages are a real function of the
challenge answers it has read (`challenge_truncated_message_depends`) and it obeys
the protocol's causality (`challenge_truncated_round_causal`), so the whole of
section 4 applies to it.  Its chain's clash mass at the envelope's thirteen
coupled rounds is the SAME `3828 / |Block|` a fixed prover gets. -/
theorem adaptive_strategic_chain_clash_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (quotientDegree : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hlog : m.1.length ≤ 5) (hgate : m.2.length ≤ quotientDegree + 2)
    (hLq : 189 + 24 * quotientDegree ≤ L) :
    oracleProbability (boundedQueries L)
        (strategyClashEvent L (Nat.le_trans (by omega) hLq) OuterInitial.zeroDigest
          (strategicShape c s (challengeTruncatedMessage m))
          (challenge_truncated_strategic_bounded L c s m quotientDegree hpre hlog hgate hLq)
          (22 + 5 * 13))
      ≤ (3828 : ℚ) / (Fintype.card Block : ℚ) :=
  strategic_prover_chain_clash_at_thirteen L (Nat.le_trans (by omega) hLq) c s
    (challengeTruncatedMessage m)
    (challenge_truncated_strategic_bounded L c s m quotientDegree hpre hlog hgate hLq)

/-- (5) The closed bound is a real number strictly below `1`: the adopted
`BirthdayClashBound.prefix_round_digest_clash_bound_lt_one`, which uses only
`3828 < 65536 = 256 ^ 2 <= 256 ^ 32`. -/
theorem strategy_clash_bound_at_eighty_seven_lt_one :
    (3828 : ℚ) / (Fintype.card Block : ℚ) < 1 :=
  prefix_round_digest_clash_bound_lt_one

end Audit.Wire3.StrategyChainBound
