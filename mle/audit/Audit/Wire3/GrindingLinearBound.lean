import Audit.Wire3.GrindingQueryBound

/-!
# A CLASH BOUND LINEAR IN THE GRINDING BUDGET

## The gap this module addresses

`GrindingQueryBound` (GQB) bounds the chain's clash mass for a prover that makes
`q` PROBE queries of its own at each of `n` stages by the ALL-PAIRS birthday
bound over the whole interleaved sequence of `N = (q + 1) n` positions:

  `grinding_chain_clash_probability_le`:
    `oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)`
      `<= N (N + 1) / 2 / |Block|`,   `N = n (q + 1)`,

whose leading term is `n^2 (q + 1)^2 / 2`, QUADRATIC in the probe budget.  Its
own HONESTY (ii) says why that is loose and what should replace it: a stage clash
needs a FRESH answer to land on one of the at most `n + 1` STATE digests, so a
target of `n + 1` blocks per position, not `N` of them, should do -- and it names
the obstruction met when the target is cut down to the ABSORB answers: the
first-occurrence push-down `distinct_clash_succ_subset` replaces a pair `(r, n)`
by a pair drawn from `{r, c}`, and the side condition "one of the two positions is
an absorb" does not survive that.

THIS MODULE CARRIES OUT THE REPLACEMENT, AND THE OBSTRUCTION IS AVOIDED THE WAY
GQB SUGGESTS: the first-occurrence step is stated on the QUERY STRING and not on
the position's role (`exists_first_occurrence`), the counting is redone with a
POSITION-DEPENDENT target (`stateTarget`), and the containment is proved by strong
induction on the later stage of the clash (`clash_state_hit_aux`).  The constant
that comes out is

  `(q + 1) n (n + 1) / 2 / |Block|`,

LINEAR in `q`, EQUAL to GQB's constant at `q = 0` and never larger
(`linear_constant_at_no_probes`, `linear_constant_le_all_pairs_constant`).

IT IS NOT PROVED FOR EVERY GRINDING STRATEGY.  It is proved for the runs that are
STATE-FRAMED, and that restriction is the honest residue of this module; see
HONESTY (ii), which says exactly what it excludes, why the argument needs it, and
what it would take to remove it.  Nothing here weakens GQB: its quadratic bound
remains the one that holds with no such restriction.

## What is proved

1. THE STATE TARGET AND ITS SIZE (section 1).  `stateTarget ... m T` is the set of
   BLOCKS of the stage digests the chain has already formed by position `m` --
   `grindState 0 T = e0` included -- and its size is at most
   `m / (q + 1) + 1 <= n + 1`, not `m`.  `grind_state_reassign` is its stability:
   those digests are read off answers STRICTLY BEFORE `m`, so overwriting the
   answer at a fresh position `m` does not move them, which is the third clause of
   the adopted `BirthdayClashBound.FreshStep`.  `state_target_fresh_step` is that
   `FreshStep` and `state_target_step_bound` the resulting mass
   `(m / (q + 1) + 1) / |Block|` for one position.  This is the
   "table-dependent target invariant under reassigning the query" the adopted
   step already allows; no new probabilistic lemma is introduced anywhere below.
2. THE STATE-TARGETED EVENT AND ITS LINEAR MASS (section 2).  `stateHitEvent` is
   the union over the `N` positions of "position `m` asked a NEW byte string and
   its answer was the block of a stage digest already formed".  Summing the
   per-position masses over the positions of `n` stages gives the triangular count
   `two_mul_sum_slot_card`: the `q + 1` positions of stage `j` each carry at most
   `j + 1`, so

     `state_hit_probability_le`:
       `oracleProbability (boundedQueries L) (stateHitEvent ... (n (q + 1)))`
         `<= (q + 1) n (n + 1) / 2 / |Block|`.

   `constant_table_state_hit` shows this event is not empty.
3. EVERY STAGE CLASH OF A STATE-FRAMED RUN IS A STATE HIT (section 3).
   `exists_first_occurrence` pushes any position down to the FIRST position asking
   its byte string, which is fresh -- the repeat push-down, on STRINGS.
   `frameDigestAt m T` is the digest position `m` frames at, and
   `frame_digest_at_congr` says two positions asking the same string frame at the
   same digest (the adopted `CommitmentOrder.frame_injective`).  `StateFramed` is
   the run-level condition of HONESTY (ii).  `clash_state_hit_aux` is the
   induction: with `S` the absorb position of the clash's later stage and `c` the
   first position asking `S`'s string, either the earlier stage's absorb position
   is already below `c` -- and then `c`'s answer IS the block of a stage digest
   formed before `c`, a state hit -- or it is not, and then `c`, which frames where
   `S` frames, frames by `StateFramed` at a stage digest of index at most the
   earlier stage's, which is a clash with a STRICTLY SMALLER later stage.
4. THE LINEAR BOUND (section 4).  `StateFramedProbes g` is the strategy-level
   condition "every probe frames at one of the stage digests the run has already
   reached"; `state_framed_of_probes` turns it into `StateFramed` at every table
   and `grinding_chain_clash_probability_le_linear` is the headline.
   `state_framed_no_probes` observes that at `q = 0` every position is an absorb,
   so `grinding_chain_clash_probability_le_linear_no_probes` has NO hypothesis on
   the strategy at all and its constant is the adopted `n (n + 1) / 2`.
   `grinding_chain_clash_probability_le_linear_residual` is the unconditional
   bookkeeping: for EVERY grinding strategy the clash mass is at most the linear
   constant plus the mass of `offStateFrameEvent`, the tables the containment does
   not reach.  That second term is NOT bounded anywhere below, and for a strategy
   that frames an absorbed string off the chain it is all but a negligible set of
   tables (those where the off-chain digest happens to equal an already formed
   state); the inequality is then true and essentially empty.  It is stated to make the gap explicit, not
   to close it.
5. THE CLOSED INSTANCES (section 5).  `probe_grinder_state_framed`: GQB's
   `probeGrinder`, which probes at its own current stage digest, IS state-framed,
   so `probe_grinder_chain_clash_probability_le_linear` applies to it, and
   `probe_grinder_clash_event_not_empty` records that the event it bounds is not
   empty.  `grinding_of_strategy_state_framed` does the same for every probe-free
   strategy of an adopted `StrategyChainBound.Strategy`.  At the envelope's
   `22 + 5 * 13 = 87` stages: `3828 / |Block|` at `q = 0` (the adopted numeral) and
   `4013952756 / |Block|` at `q = 2 ^ 20`, where GQB's all-pairs bound gives
   `4161109737606900 / |Block|` -- smaller by about the probe budget itself --
   and `grinding_chain_clash_at_eighty_seven_many_probes_linear_tiny` puts that
   below `2 ^ (-220)`.  `Fintype.card Block` is never evaluated: it is written as
   `2 ^ 256` through the adopted `RandomOracleSqueezes.block_card`.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every statement below is about
the uniform counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`
-- one independent uniform block per byte string of length at most `L`.  The
fresh-query lemma the induction rests on, the adopted
`BirthdayClashBound.fresh_coordinate_probability`, is the DEFINING property of a
random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed Keccak by a table drawn from this law is an assumption with no proof
anywhere in this tree.

(ii) THE LINEAR CONSTANT IS PROVED FOR STATE-FRAMED RUNS, NOT FOR EVERY GRINDING
STRATEGY, AND THIS IS THE MODULE'S ONE REAL RESTRICTION.  `StateFramed` asks: every
position that asks a byte string SOME ABSORB AT OR AFTER IT (within the counted
positions) ALSO ASKS must frame at one of the stage digests the chain has ALREADY
formed by that position.  Absorbs
satisfy it by construction, and a probe whose string is never absorbed is
unconstrained -- it may frame at any digest whatsoever.  What is excluded is a
probe that frames at a digest the chain has not yet produced AND whose string is
later absorbed.

That exclusion is not cosmetic.  A prover may probe `frame(e0, t, p)`, read the
answer, form the digest of that answer WITHOUT ABSORBING IT, probe a frame at that
digest, and so simulate a whole chain -- or a whole TREE of candidate chains --
inside its probe budget, looking for two simulated states that coincide, and only
then replay the winning path through its absorbs.  Against such a prover the
argument of section 3 does not close: the two colliding answers may both be
probes, and the position charged for the collision is then framed at a digest
that only a later absorb makes a state.  Bounding that prover needs a count over
the prover's whole query GRAPH with the path length capped at `n`, which is a
different argument from the one below and is NOT here.  What IS here for that
prover is GQB's quadratic bound, which holds for it, and
`grinding_chain_clash_probability_le_linear_residual`, which names the missing
mass without bounding it.

(iii) THIS BOUNDS THE CHAIN'S CLASH EVENT ONLY.  The event is GQB's
`grindingClashEvent`: two of the chain's stage digests coincide, or one of them is
the digest the chain started from.  IT IS NOT A BOUND ON THE RUN'S BAD-DRAW MASS
FOR A GRINDING PROVER.  THE UNION BOUND FOR A GRINDING PROVER IS NOT DELIVERED:
the adopted `RandomOracleSqueezes.run_bad_draw_probability_le_fibrewise` splits
that mass into `ChallengeUnionBound.combinedBound` plus the clash term, and only
the clash term is touched here, exactly as in GQB HONESTY (iii).  Nothing below
aggregates into a run-level statement.

(iv) THE SEQUENCE POSITIONS ARE FRAME QUERIES; THE CHALLENGE READS ARE FREE.  This
is GQB's model, imported unchanged and not re-derived: a counted position is a
`Transcript.frame` with the digest, tag and payload all chosen by the prover,
while the challenge oracle is handed to it IN FULL, at every digest, at no cost to
the count -- see GQB HONESTY (iv).  A counted position may not be a challenge
input, and grinding ON CHALLENGES is a threat to the union bound of (iii), which
is not re-derived here.

(v) THE CONSTANT, EXACTLY, AND HOW IT COMPARES.  What is proved is
`(q + 1) n (n + 1) / 2 / |Block|` and nothing smaller.  Against GQB's all-pairs
`n (q + 1) (n (q + 1) + 1) / 2 / |Block|` it is EQUAL at `q = 0` and never larger
(both proved: `linear_constant_at_no_probes`,
`linear_constant_le_all_pairs_constant`), and at `n = 87, q = 2 ^ 20` it is
`4013952756` against `4161109737606900`.  Against the HEURISTIC of the adopted
`StrategyChainBound` HONESTY (vii), which phrases the expected cost of grinding as
a clash mass that "scales like `q * n / |Block|`", IT IS LARGER BY ABOUT `n / 2`:
the count below charges every one of the `n (q + 1)` positions with a target of up
to `n + 1` blocks, which is `q n^2 / 2` and not `q n`.  Nothing below delivers the
heuristic, and the honest reading of the proved constant is "linear in `q`,
quadratic in `n`".

(vi) THE NUMBER OF PROBES IS A PARAMETER, NOT A CAP, AND THE LENGTH BUDGET IS A
HYPOTHESIS.  `q` is quantified in every statement; the instance at `q = 2 ^ 20` is
an illustration of the arithmetic, not a claim about any attacker.
`GrindingBounded L g` is GQB's budget, discharged here only where GQB discharges
it -- for `probeGrinder` at `93 <= L` and for `grindingOfStrategy`.

(vii) THE LANES ARE THE OUTER SUMCHECK LANES.  The index lanes, the WHIR folding
transcript and the Merkle openings are NOT covered, and no round schedule is
threaded onto the chain here.

(viii) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The bounds here are on
the mass of one named event under the oracle law.  The design point of the
deployed profile is about a hundred bits; nothing below aggregates into a
soundness statement for the protocol.
-/

namespace Audit.Wire3.GrindingLinearBound

open Audit.Wire3
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.GrindingQueryBound

/-! ## 1. THE STATE TARGET OF A POSITION -/

/-- The stage digests whose absorb position is below `m`, as blocks. -/
def stateTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) : Finset Block :=
  (Finset.range (m / (q + 1) + 1)).image
    (fun k => OuterChallenge.digestBlock (grindState L hL e0 q g hb k T))

theorem state_target_card_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) :
    (stateTarget L hL e0 q g hb m T).card ≤ m / (q + 1) + 1 :=
  le_trans Finset.card_image_le (le_of_eq (Finset.card_range _))

theorem mem_state_target (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) (k : Nat) (hk : k ≤ m / (q + 1)) (b : Block)
    (h : OuterChallenge.digestBlock (grindState L hL e0 q g hb k T) = b) :
    b ∈ stateTarget L hL e0 q g hb m T :=
  Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), h⟩

/-- An absorb position of a stage at or below `m / (q + 1)` is below `m`. -/
theorem slot_pos_lt_of_div (q m j : Nat) (h : j + 1 ≤ m / (q + 1)) : slotPos q j q < m := by
  have h1 := slot_pos_lt_of_le q (m / (q + 1)) j h
  have h2 := Nat.div_mul_le_self m (q + 1)
  omega

/-- (1) The stage digests formed before `m` do not move when the answer at a fresh
position `m` is overwritten. -/
theorem grind_state_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ freshAt (grindSelSeq L hL e0 q g hb) m) (b : Block) (k : Nat)
    (hk : k ≤ m / (q + 1)) :
    grindState L hL e0 q g hb k
        (reassign T (grindSelSeq L hL e0 q g hb m T) b)
      = grindState L hL e0 q g hb k T := by
  cases k with
  | zero => rfl
  | succ k2 =>
      have hlt : slotPos q k2 q < m := slot_pos_lt_of_div q m k2 hk
      exact congrArg blockDigest
        (chain_val_fresh_stable (grinding_sequence_fresh_causal L hL e0 q g hb) m T hT b
          (slotPos q k2 q) hlt)

/-- (1) **A FRESH POSITION AIMED AT THE STATE DIGESTS.**  The adopted
`BirthdayClashBound.FreshStep` with the position-dependent target `stateTarget`:
the blocks of the stage digests already formed. -/
theorem state_target_fresh_step (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat) :
    FreshStep (boundedQueries L) (freshAt (grindSelSeq L hL e0 q g hb) m)
      (grindSelSeq L hL e0 q g hb m) (stateTarget L hL e0 q g hb m) := by
  have hc := grinding_sequence_fresh_causal L hL e0 q g hb
  refine ⟨fun T hT b => fresh_at_reassign hc m T hT b,
    fun T hT b => hc m T hT b m (le_refl m), fun T hT b => ?_⟩
  refine Finset.image_congr ?_
  intro k hk
  have hk2 : k ≤ m / (q + 1) := by
    have := Finset.mem_range.mp hk
    omega
  exact congrArg OuterChallenge.digestBlock
    (grind_state_reassign L hL e0 q g hb m T hT b k hk2)

/-- (1) The mass of "the fresh position `m` answers the block of a stage digest
already formed". -/
theorem state_target_step_bound (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat) :
    oracleProbability (boundedQueries L)
        ((freshAt (grindSelSeq L hL e0 q g hb) m).filter
          (fun T => chainVal (grindSelSeq L hL e0 q g hb) m T ∈ stateTarget L hL e0 q g hb m T))
      ≤ ((m / (q + 1) + 1 : Nat) : ℚ) / (Fintype.card Block : ℚ) :=
  adaptive_fresh_step_abs (state_target_fresh_step L hL e0 q g hb m) (m / (q + 1) + 1)
    (fun T _ => state_target_card_le L hL e0 q g hb m T)

/-! ## 2. THE STATE-TARGETED EVENT AND ITS LINEAR MASS -/

/-- **THE STATE-TARGETED EVENT.**  Some position below `N` asked a NEW byte string
and its answer was the block of a stage digest already formed. -/
def stateHitEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) :
    Nat → Finset (OracleTable (boundedQueries L))
  | 0 => ∅
  | m + 1 =>
      stateHitEvent L hL e0 q g hb m ∪
        (freshAt (grindSelSeq L hL e0 q g hb) m).filter
          (fun T => chainVal (grindSelSeq L hL e0 q g hb) m T ∈ stateTarget L hL e0 q g hb m T)

theorem state_hit_event_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat) :
    stateHitEvent L hL e0 q g hb (m + 1)
      = stateHitEvent L hL e0 q g hb m ∪
        (freshAt (grindSelSeq L hL e0 q g hb) m).filter
          (fun T => chainVal (grindSelSeq L hL e0 q g hb) m T ∈ stateTarget L hL e0 q g hb m T) :=
  rfl

theorem mem_state_hit_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N m : Nat) (hm : m < N)
    (T : OracleTable (boundedQueries L))
    (hf : T ∈ freshAt (grindSelSeq L hL e0 q g hb) m)
    (hv : chainVal (grindSelSeq L hL e0 q g hb) m T ∈ stateTarget L hL e0 q g hb m T) :
    T ∈ stateHitEvent L hL e0 q g hb N := by
  induction N with
  | zero => exact absurd hm (Nat.not_lt_zero m)
  | succ k ih =>
      rw [state_hit_event_succ]
      rcases Nat.lt_or_ge m k with h | h
      · exact Finset.mem_union_left _ (ih h)
      · have hmk : m = k := by omega
        subst hmk
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf, hv⟩)

theorem state_hit_probability_le_sum (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat) :
    oracleProbability (boundedQueries L) (stateHitEvent L hL e0 q g hb N)
      ≤ ∑ m in Finset.range N, ((m / (q + 1) + 1 : Nat) : ℚ) / (Fintype.card Block : ℚ) := by
  induction N with
  | zero =>
      rw [show stateHitEvent L hL e0 q g hb 0 = (∅ : Finset (OracleTable (boundedQueries L)))
          from rfl, Finset.range_zero, Finset.sum_empty, oracleProbability, Finset.card_empty,
        Nat.cast_zero, zero_div]
  | succ k ih =>
      rw [state_hit_event_succ]
      calc oracleProbability (boundedQueries L)
              (stateHitEvent L hL e0 q g hb k ∪
                (freshAt (grindSelSeq L hL e0 q g hb) k).filter
                  (fun T => chainVal (grindSelSeq L hL e0 q g hb) k T
                    ∈ stateTarget L hL e0 q g hb k T))
          ≤ oracleProbability (boundedQueries L) (stateHitEvent L hL e0 q g hb k)
              + oracleProbability (boundedQueries L)
                  ((freshAt (grindSelSeq L hL e0 q g hb) k).filter
                    (fun T => chainVal (grindSelSeq L hL e0 q g hb) k T
                      ∈ stateTarget L hL e0 q g hb k T)) :=
            oracle_probability_union_le _ _ _
        _ ≤ (∑ m in Finset.range k, ((m / (q + 1) + 1 : Nat) : ℚ) / (Fintype.card Block : ℚ))
              + ((k / (q + 1) + 1 : Nat) : ℚ) / (Fintype.card Block : ℚ) :=
            add_le_add ih (state_target_step_bound L hL e0 q g hb k)
        _ = ∑ m in Finset.range (k + 1),
              ((m / (q + 1) + 1 : Nat) : ℚ) / (Fintype.card Block : ℚ) :=
            (Finset.sum_range_succ _ _).symm

/-- (2) **THE TRIANGULAR COUNT.**  The `q + 1` positions of stage `j` each carry a
target of at most `j + 1` blocks, so the `n (q + 1)` positions carry
`(q + 1) n (n + 1) / 2` in total. -/
theorem two_mul_sum_slot_card (q n : Nat) :
    2 * (∑ m in Finset.range (n * (q + 1)), (m / (q + 1) + 1)) = (q + 1) * (n * (n + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hsplit : (k + 1) * (q + 1) = k * (q + 1) + (q + 1) := by ring
      have hblock : ∑ i in Finset.range (q + 1), ((k * (q + 1) + i) / (q + 1) + 1)
          = (q + 1) * (k + 1) := by
        have hterm : ∀ i ∈ Finset.range (q + 1), (k * (q + 1) + i) / (q + 1) + 1 = k + 1 := by
          intro i hi
          have hiq : i ≤ q := by
            have := Finset.mem_range.mp hi
            omega
          have hd := slot_pos_div q k i hiq
          simp only [slotPos] at hd
          rw [hd]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
      rw [hsplit, Finset.sum_range_add, hblock, Nat.mul_add, ih]
      ring

theorem sum_slot_card_rat (q n : Nat) :
    ∑ m in Finset.range (n * (q + 1)), ((m / (q + 1) + 1 : Nat) : ℚ)
      = (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2 := by
  have h := two_mul_sum_slot_card q n
  have hcast : ((2 * (∑ m in Finset.range (n * (q + 1)), (m / (q + 1) + 1)) : Nat) : ℚ)
      = (((q + 1) * (n * (n + 1)) : Nat) : ℚ) := congrArg (fun z : Nat => (z : ℚ)) h
  rw [Nat.cast_mul, Nat.cast_sum] at hcast
  push_cast at hcast ⊢
  linarith

/-- (2) **THE LINEAR MASS OF THE STATE-TARGETED EVENT.**  Over the `n (q + 1)`
positions of a grinding run, the mass of "some fresh position answered a stage
digest already formed" is at most `(q + 1) n (n + 1) / 2` over the block space --
LINEAR in the probe budget `q`. -/
theorem state_hit_probability_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    oracleProbability (boundedQueries L) (stateHitEvent L hL e0 q g hb (n * (q + 1)))
      ≤ (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ) := by
  refine le_trans (state_hit_probability_le_sum L hL e0 q g hb (n * (q + 1))) ?_
  rw [← Finset.sum_div, sum_slot_card_rat q n]

/-! ## 3. EVERY STAGE CLASH OF A STATE-FRAMED RUN IS A STATE HIT -/

/-- (3) **THE FIRST OCCURRENCE OF A QUERY STRING.**  Every position repeats a
FRESH position that asked the same byte string -- itself, if it is fresh.  This is
the first-occurrence push-down of `GrindingQueryBound.distinct_clash_succ_subset`,
stated on the STRING and not on the position's role, which is what lets the role
survive it: the repeated string, not the repeating position, is what the counting
below looks at. -/
theorem exists_first_occurrence {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (T : OracleTable Q)
    (m : Nat) : ∃ c, c ≤ m ∧ sel c T = sel m T ∧ T ∈ freshAt sel c := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      by_cases hf : T ∈ freshAt sel m
      · exact ⟨m, le_refl m, rfl, hf⟩
      · rw [mem_fresh_at] at hf
        push_neg at hf
        obtain ⟨i, hi, heq⟩ := hf
        obtain ⟨c, hc, hceq, hcf⟩ := ih i hi
        exact ⟨c, by omega, hceq.trans heq, hcf⟩

/-- **THE DIGEST POSITION `m` FRAMES AT.**  Every query of the sequence is a frame
(`GrindingQueryBound` HONESTY (iv)); this is the digest of that frame, a function
of the answers strictly before `m`. -/
def frameDigestAt (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) : Transcript.Digest :=
  (grindQuery e0 q g (runAns L hL e0 q g hb m T) (challengesOf L hL T) m).1

theorem grind_sel_seq_frame (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∃ (t : Transcript.Byte) (p : Transcript.Bytes),
      (grindSelSeq L hL e0 q g hb m T).val
        = Transcript.frame (frameDigestAt L hL e0 q g hb m T) t p :=
  ⟨_, _, rfl⟩

/-- (3) Two positions that asked the SAME byte string framed at the same digest. -/
theorem frame_digest_at_congr (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (c m : Nat)
    (T : OracleTable (boundedQueries L))
    (h : grindSelSeq L hL e0 q g hb c T = grindSelSeq L hL e0 q g hb m T) :
    frameDigestAt L hL e0 q g hb c T = frameDigestAt L hL e0 q g hb m T := by
  obtain ⟨t1, p1, h1⟩ := grind_sel_seq_frame L hL e0 q g hb c T
  obtain ⟨t2, p2, h2⟩ := grind_sel_seq_frame L hL e0 q g hb m T
  have hfr : Transcript.frame (frameDigestAt L hL e0 q g hb c T) t1 p1
      = Transcript.frame (frameDigestAt L hL e0 q g hb m T) t2 p2 := by
    rw [← h1, ← h2, h]
  exact (CommitmentOrder.frame_injective _ _ _ _ _ _ hfr).1

/-- (3) The absorb of stage `k` frames at the stage-`k` digest. -/
theorem frame_digest_at_absorb (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    frameDigestAt L hL e0 q g hb (slotPos q k q) T = grindState L hL e0 q g hb k T :=
  grind_query_absorb_digest L hL e0 q g hb k T

/-- **A STATE-FRAMED RUN.**  Every position that asks a byte string SOME ABSORB AT
OR AFTER IT (within the counted positions) ALSO ASKS frames at a stage digest of
the chain ALREADY FORMED -- one of
the `m / (q + 1) + 1` digests the run has reached by position `m`.

The absorbs themselves satisfy this by construction; what the condition
constrains is a PROBE WHOSE STRING IS LATER ABSORBED, and it is exactly what the
counting of section 2 needs, because it forbids such a probe from framing at a
digest that only a LATER answer of the run produces.  A probe whose string is
never absorbed is unconstrained: it may frame wherever the prover likes.  See
HONESTY (ii). -/
def StateFramed (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) : Prop :=
  ∀ m, m < N →
    (∃ k, m ≤ slotPos q k q ∧ slotPos q k q < N ∧
      grindSelSeq L hL e0 q g hb m T = grindSelSeq L hL e0 q g hb (slotPos q k q) T) →
    ∃ j, j ≤ m / (q + 1) ∧
      frameDigestAt L hL e0 q g hb m T = grindState L hL e0 q g hb j T

/-- (3) **A STAGE CLASH OF A STATE-FRAMED RUN IS A FRESH POSITION ANSWERING AN
EARLIER STAGE DIGEST.**  Strong induction on the LATER stage of the clash.  Let
`S` be the absorb position of that stage and `c` the FIRST position asking `S`'s
byte string -- fresh, with the same answer.  Either the earlier stage's absorb
position is already below `c`, and then `c`'s answer is the block of a stage
digest formed before `c`; or it is not, and then `c` -- which frames where `S`
frames, at the digest of the stage before the later one -- frames, by
`StateFramed`, at a stage digest of index at most the earlier stage's, which is a
clash with a SMALLER later stage. -/
theorem clash_state_hit_aux (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L))
    (hsf : StateFramed L hL e0 q g hb (n * (q + 1)) T) :
    ∀ s : Nat, s ≤ n → ∀ r : Nat, r < s →
      grindState L hL e0 q g hb r T = grindState L hL e0 q g hb s T →
      T ∈ stateHitEvent L hL e0 q g hb (n * (q + 1)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro hsn r hrs heq
      obtain ⟨s2, rfl⟩ : ∃ s2, s = s2 + 1 := ⟨s - 1, by omega⟩
      have hS : slotPos q s2 q < n * (q + 1) := slot_pos_lt_of_le q n s2 hsn
      obtain ⟨c, hcS, hcsel, hcf⟩ :=
        exists_first_occurrence (grindSelSeq L hL e0 q g hb) T (slotPos q s2 q)
      have hcN : c < n * (q + 1) := lt_of_le_of_lt hcS hS
      have hval : chainVal (grindSelSeq L hL e0 q g hb) c T
          = chainVal (grindSelSeq L hL e0 q g hb) (slotPos q s2 q) T := by
        show T (grindSelSeq L hL e0 q g hb c T) = T (grindSelSeq L hL e0 q g hb (slotPos q s2 q) T)
        rw [hcsel]
      cases r with
      | zero =>
          refine mem_state_hit_event L hL e0 q g hb (n * (q + 1)) c hcN T hcf ?_
          refine mem_state_target L hL e0 q g hb c T 0 (Nat.zero_le _) _ ?_
          rw [hval]
          exact congrArg OuterChallenge.digestBlock heq
      | succ r2 =>
          rcases Nat.lt_or_ge (slotPos q r2 q) c with hPc | hcP
          · refine mem_state_hit_event L hL e0 q g hb (n * (q + 1)) c hcN T hcf ?_
            have hmul : (r2 + 1) * (q + 1) ≤ c := by
              have he : (r2 + 1) * (q + 1) = r2 * (q + 1) + (q + 1) := by ring
              simp only [slotPos] at hPc
              omega
            have hk : r2 + 1 ≤ c / (q + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr hmul
            refine mem_state_target L hL e0 q g hb c T (r2 + 1) hk _ ?_
            rw [hval]
            exact congrArg OuterChallenge.digestBlock heq
          · obtain ⟨j, hj, hjeq⟩ := hsf c hcN ⟨s2, hcS, hS, hcsel⟩
            have hdiv : c / (q + 1) ≤ r2 := by
              have h1 : c / (q + 1) ≤ (slotPos q r2 q) / (q + 1) := Nat.div_le_div_right hcP
              rwa [slot_pos_div q r2 q (le_refl q)] at h1
            have hfd : frameDigestAt L hL e0 q g hb c T = grindState L hL e0 q g hb s2 T := by
              rw [frame_digest_at_congr L hL e0 q g hb c (slotPos q s2 q) T hcsel,
                frame_digest_at_absorb]
            exact ih s2 (Nat.lt_succ_self s2) (by omega) j (by omega) (hjeq.symm.trans hfd)

/-- (3) **THE CHAIN'S CLASH EVENT, ON THE STATE-FRAMED TABLES, SITS INSIDE THE
STATE-TARGETED EVENT.**  No hypothesis on the strategy: the condition is on the
RUN. -/
theorem grinding_clash_state_framed_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L))
    (hsf : StateFramed L hL e0 q g hb (n * (q + 1)) T)
    (hT : T ∈ grindingClashEvent L hL e0 q g hb n) :
    T ∈ stateHitEvent L hL e0 q g hb (n * (q + 1)) := by
  obtain ⟨r, s, hrs, hsn, heq⟩ := (mem_grinding_clash_event L hL e0 q g hb n T).mp hT
  exact clash_state_hit_aux L hL e0 q g hb n T hsf s hsn r hrs heq

/-! ## 4. THE LINEAR BOUND -/

/-- **A STATE-FRAMED GRINDING STRATEGY.**  Every probe frames at one of the stage
digests the run has already reached.  The absorbs are state-framed by
construction, so this is the whole condition; it is a RESTRICTION on the prover
class, stated here and discharged in section 5 for the grinder of
`GrindingQueryBound` and for every probe-free strategy. -/
def StateFramedProbes (g : GrindingStrategy) : Prop :=
  ∀ (k i : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), ∃ j, j ≤ k ∧ (g.probe k i h ch pa).1 = h j

/-- (4) A state-framed strategy produces a state-framed run, at every table. -/
theorem state_framed_of_probes (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (hp : StateFramedProbes g) (N : Nat)
    (T : OracleTable (boundedQueries L)) : StateFramed L hL e0 q g hb N T := by
  intro m _ _
  by_cases hprobe : m % (q + 1) < q
  · obtain ⟨j, hj, hje⟩ := hp (m / (q + 1)) (m % (q + 1))
      (stateOf e0 q (runAns L hL e0 q g hb m T)) (challengesOf L hL T)
      (probeAnsOf q (runAns L hL e0 q g hb m T))
    refine ⟨j, hj, ?_⟩
    have hq : frameDigestAt L hL e0 q g hb m T
        = stateOf e0 q (runAns L hL e0 q g hb m T) j := by
      show (grindQuery e0 q g (runAns L hL e0 q g hb m T) (challengesOf L hL T) m).1 = _
      unfold grindQuery
      rw [if_pos hprobe, hje]
    rw [hq]
    refine state_of_run_ans_le L hL e0 q g hb m j ?_ T
    intro j2 hj2
    refine slot_pos_lt_of_div q m j2 ?_
    rw [← hj2]
    exact hj
  · refine ⟨m / (q + 1), le_refl _, ?_⟩
    have hq : frameDigestAt L hL e0 q g hb m T
        = stateOf e0 q (runAns L hL e0 q g hb m T) (m / (q + 1)) := by
      show (grindQuery e0 q g (runAns L hL e0 q g hb m T) (challengesOf L hL T) m).1 = _
      unfold grindQuery
      rw [if_neg hprobe]
    rw [hq]
    exact state_of_run_ans_le L hL e0 q g hb m (m / (q + 1))
      (fun j2 hj2 => slot_pos_lt_of_div q m j2 (le_of_eq hj2.symm)) T

/-- (4) **A PROBE-FREE RUN IS STATE-FRAMED, WHATEVER THE STRATEGY.**  At `q = 0`
every position is an absorb, and an absorb frames at the chain's own current
digest.  So section 4's bound at `q = 0` carries NO hypothesis on the strategy. -/
theorem state_framed_no_probes (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) : StateFramed L hL e0 0 g hb N T := by
  intro m _ _
  refine ⟨m / (0 + 1), le_refl _, ?_⟩
  have hq : frameDigestAt L hL e0 0 g hb m T
      = stateOf e0 0 (runAns L hL e0 0 g hb m T) (m / (0 + 1)) := by
    show (grindQuery e0 0 g (runAns L hL e0 0 g hb m T) (challengesOf L hL T) m).1 = _
    unfold grindQuery
    rw [if_neg (by omega : ¬ (m % (0 + 1) < 0))]
  rw [hq]
  exact state_of_run_ans_le L hL e0 0 g hb m (m / (0 + 1))
    (fun j2 hj2 => slot_pos_lt_of_div 0 m j2 (le_of_eq hj2.symm)) T

/-- **THE HEADLINE.**  For a STATE-FRAMED grinding strategy with `q` probes at
every one of `n` stages, the mass of the event that two of the chain's stage
digests coincide -- or that one of them is the digest the chain started from -- is
at most

  `(q + 1) n (n + 1) / 2 / |Block|`,

LINEAR in the probe budget `q`, where
`GrindingQueryBound.grinding_chain_clash_probability_le` gives the all-pairs
`n (q + 1) (n (q + 1) + 1) / 2 / |Block|`, quadratic in `q`.  At `q = 0` the two
constants are equal (`linear_constant_at_no_probes`). -/
theorem grinding_chain_clash_probability_le_linear (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hp : StateFramedProbes g) (n : Nat) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)
      ≤ (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ) := by
  refine le_trans (oracle_probability_mono _ _ _ ?_) (state_hit_probability_le L hL e0 q g hb n)
  intro T hT
  exact grinding_clash_state_framed_subset L hL e0 q g hb n T
    (state_framed_of_probes L hL e0 q g hb hp (n * (q + 1)) T) hT

open Classical in
/-- The tables the containment of section 3 does not reach: those at which some
position of the run frames at a digest the chain has NOT yet produced.  See
HONESTY (ii). -/
noncomputable def offStateFrameEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ¬ StateFramed L hL e0 q g hb N T)

theorem mem_off_state_frame_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ offStateFrameEvent L hL e0 q g hb N ↔ ¬ StateFramed L hL e0 q g hb N T := by
  simp only [offStateFrameEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- (4) **THE UNCONDITIONAL DECOMPOSITION.**  For EVERY grinding strategy, the
chain's clash mass is at most the linear constant plus the mass of the tables at
which some position frames off the chain's own formed digests.  Nothing below
bounds that second term; `state_framed_of_probes` makes it EMPTY for a
state-framed strategy, and `state_framed_no_probes` makes it empty at `q = 0`. -/
theorem grinding_chain_clash_probability_le_linear_residual (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (n : Nat) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)
      ≤ (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ)
        + oracleProbability (boundedQueries L)
            (offStateFrameEvent L hL e0 q g hb (n * (q + 1))) := by
  have hsub : grindingClashEvent L hL e0 q g hb n
      ⊆ stateHitEvent L hL e0 q g hb (n * (q + 1))
        ∪ offStateFrameEvent L hL e0 q g hb (n * (q + 1)) := by
    intro T hT
    by_cases hsf : StateFramed L hL e0 q g hb (n * (q + 1)) T
    · exact Finset.mem_union_left _
        (grinding_clash_state_framed_subset L hL e0 q g hb n T hsf hT)
    · exact Finset.mem_union_right _
        ((mem_off_state_frame_event L hL e0 q g hb (n * (q + 1)) T).mpr hsf)
  refine le_trans (oracle_probability_mono _ _ _ hsub) ?_
  refine le_trans (oracle_probability_union_le _ _ _) ?_
  exact add_le_add_right (state_hit_probability_le L hL e0 q g hb n) _

/-- (4) **AT `q = 0` THE BOUND IS UNCONDITIONAL.**  No hypothesis on the strategy
at all, and the constant is `n (n + 1) / 2`, the adopted one. -/
theorem grinding_chain_clash_probability_le_linear_no_probes (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 0 g hb n)
      ≤ ((n * (n + 1) : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ) := by
  have h : oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 0 g hb n)
      ≤ (((0 + 1) * (n * (n + 1)) : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ) := by
    refine le_trans (oracle_probability_mono _ _ _ ?_)
      (state_hit_probability_le L hL e0 0 g hb n)
    intro T hT
    exact grinding_clash_state_framed_subset L hL e0 0 g hb n T
      (state_framed_no_probes L hL e0 g hb (n * (0 + 1)) T) hT
  rwa [show (((0 + 1) * (n * (n + 1)) : Nat) : ℚ) = ((n * (n + 1) : Nat) : ℚ) from by
    push_cast; ring] at h

/-! ## 5. HOW THE CONSTANT COMPARES, AND THE CLOSED INSTANCES -/

/-- (5) **AT `q = 0` THE LINEAR CONSTANT IS THE ALL-PAIRS CONSTANT.**  Nothing is
lost at the probe-free end: both are `n (n + 1) / 2`. -/
theorem linear_constant_at_no_probes (n : Nat) :
    (((0 + 1) * (n * (n + 1)) : Nat) : ℚ) / 2
      = ((n * (0 + 1) : Nat) : ℚ) * (((n * (0 + 1) : Nat) : ℚ) + 1) / 2 := by
  push_cast
  ring

/-- (5) **AND IT IS NEVER LARGER.**  For every `q` and `n` the linear constant is
at most the all-pairs constant of `GrindingQueryBound`. -/
theorem linear_constant_le_all_pairs_constant (q n : Nat) :
    (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2
      ≤ ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2 := by
  have h0 : n * 1 ≤ n * (q + 1) := Nat.mul_le_mul (le_refl n) (by omega)
  have h1 : n + 1 ≤ n * (q + 1) + 1 := by
    rw [Nat.mul_one] at h0
    omega
  have hnat : (q + 1) * (n * (n + 1)) ≤ (n * (q + 1)) * (n * (q + 1) + 1) := by
    calc (q + 1) * (n * (n + 1)) = (n * (q + 1)) * (n + 1) := by ring
      _ ≤ (n * (q + 1)) * (n * (q + 1) + 1) := Nat.mul_le_mul (le_refl _) h1
  have hcast : (((q + 1) * (n * (n + 1)) : Nat) : ℚ)
      ≤ (((n * (q + 1)) * (n * (q + 1) + 1) : Nat) : ℚ) := by exact_mod_cast hnat
  push_cast at hcast ⊢
  linarith

/-- (5) **THE GRINDER OF `GrindingQueryBound` IS STATE-FRAMED.**  It probes at its
own current stage digest, so the headline applies to it. -/
theorem probe_grinder_state_framed : StateFramedProbes probeGrinder :=
  fun k _ _ _ _ => ⟨k, le_refl k, rfl⟩

/-- (5) So is the probe-free strategy of an adopted `StrategyChainBound.Strategy`:
its (unused) probe frames at the base digest. -/
theorem grinding_of_strategy_state_framed (strat : StrategyChainBound.Strategy) :
    StateFramedProbes (grindingOfStrategy strat) :=
  fun k _ _ _ _ => ⟨0, Nat.zero_le k, rfl⟩

/-- (5) **THE LINEAR BOUND FOR THE GRINDER.** -/
theorem probe_grinder_chain_clash_probability_le_linear (L : Nat) (hL : 93 ≤ L)
    (e0 : Transcript.Digest) (q n : Nat) :
    oracleProbability (boundedQueries L)
        (grindingClashEvent L (Nat.le_trans (by norm_num) hL) e0 q probeGrinder
          (probe_grinder_bounded L hL) n)
      ≤ (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ) :=
  grinding_chain_clash_probability_le_linear L (Nat.le_trans (by norm_num) hL) e0 q probeGrinder
    (probe_grinder_bounded L hL) probe_grinder_state_framed n

/-- (5) **THE CLOSED FORM AT THE ENVELOPE'S `22 + 5 * 13 = 87` STAGES**, as a
function of the probe budget. -/
theorem grinding_chain_clash_at_eighty_seven_linear (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hp : StateFramedProbes g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb 87)
      ≤ (((q + 1) * 7656 : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ) := by
  have h := grinding_chain_clash_probability_le_linear L hL e0 q g hb hp 87
  rwa [show (((q + 1) * (87 * (87 + 1)) : Nat) : ℚ) = (((q + 1) * 7656 : Nat) : ℚ) from by
    norm_num] at h

/-- (5) **AT `q = 0` THE NUMERAL IS THE ADOPTED ONE**, `3828 / |Block|`, with no
hypothesis on the strategy. -/
theorem grinding_chain_clash_at_eighty_seven_linear_no_probes (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (g : GrindingStrategy) (hb : GrindingBounded L g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 0 g hb 87)
      ≤ (3828 : ℚ) / (Fintype.card Block : ℚ) := by
  have h := grinding_chain_clash_probability_le_linear_no_probes L hL e0 g hb 87
  rwa [show ((87 * (87 + 1) : Nat) : ℚ) / 2 = (3828 : ℚ) from by norm_num] at h

/-- (5) **A MILLION PROBES PER STAGE, LINEARLY.**  At `q = 2 ^ 20` and `n = 87` the
numerator is `4013952756`, where the all-pairs bound of `GrindingQueryBound` gives
`4161109737606900`: a factor of about a million, the probe budget itself. -/
theorem grinding_chain_clash_at_eighty_seven_many_probes_linear (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hp : StateFramedProbes g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 1048576 g hb 87)
      ≤ (4013952756 : ℚ) / (Fintype.card Block : ℚ) := by
  have h := grinding_chain_clash_probability_le_linear L hL e0 1048576 g hb hp 87
  rwa [show (((1048576 + 1) * (87 * (87 + 1)) : Nat) : ℚ) / 2 = (4013952756 : ℚ) from by
    norm_num] at h

/-- (5) **AND THAT IS BELOW `2 ^ (-220)`.**  `Fintype.card Block` is written as
`2 ^ 256` through the adopted `RandomOracleSqueezes.block_card`; no cardinality is
evaluated as a numeral. -/
theorem grinding_chain_clash_at_eighty_seven_many_probes_linear_tiny (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hp : StateFramedProbes g) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 1048576 g hb 87)
      ≤ 1 / (2 : ℚ) ^ 220 := by
  refine le_trans
    (grinding_chain_clash_at_eighty_seven_many_probes_linear L hL e0 g hb hp) ?_
  have hn : (4013952756 : Nat) * 2 ^ 220 ≤ Fintype.card Block := by
    rw [block_card_two_pow]
    calc (4013952756 : Nat) * 2 ^ 220 ≤ 2 ^ 36 * 2 ^ 220 :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ 256 := by rw [← pow_add]
  have hq : (4013952756 : ℚ) * (2 : ℚ) ^ 220 ≤ (Fintype.card Block : ℚ) := by exact_mod_cast hn
  rw [div_le_div_iff block_card_cast_pos (by positivity), one_mul]
  exact hq

/-- (5) **THE STATE-TARGETED EVENT IS NOT EMPTY.**  The constant table answers the
base block at position `0`, which is the stage-`0` digest's block, so section 2
does not bound an empty event. -/
theorem constant_table_state_hit (L : Nat) (hL : 64 ≤ L) (q : Nat) (g : GrindingStrategy)
    (hb : GrindingBounded L g) (N : Nat) (hN : 1 ≤ N) :
    constantTable L ∈ stateHitEvent L hL OuterInitial.zeroDigest q g hb N := by
  refine mem_state_hit_event L hL OuterInitial.zeroDigest q g hb N 0 (by omega) _ ?_ ?_
  · rw [mem_fresh_at]
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact mem_state_target L hL OuterInitial.zeroDigest q g hb 0 _ 0 (Nat.zero_le _) _ rfl

/-- (5) **AND NEITHER IS THE CHAIN'S CLASH EVENT THE BOUND SPEAKS OF**, for the
grinder of `GrindingQueryBound` at the tables the headline is quantified over. -/
theorem probe_grinder_clash_event_not_empty (L : Nat) (hL : 93 ≤ L) (q n : Nat) (hn : 2 ≤ n) :
    constantTable L ∈ grindingClashEvent L (Nat.le_trans (by norm_num) hL)
      OuterInitial.zeroDigest q probeGrinder (probe_grinder_bounded L hL) n :=
  constant_table_grinding_clashes L (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q
    probeGrinder (probe_grinder_bounded L hL) n hn

end Audit.Wire3.GrindingLinearBound
