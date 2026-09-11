import Audit.Wire3.GrindingLinearBound

/-!
# THE GRINDING PROVER'S DIGEST GRAPH, AND WHY IT DOES NOT BEAT THE ALL-PAIRS COUNT

## The gap this module addresses

Two bounds on the chain's clash mass for a prover that makes `q` probe queries of
its own at each of `n` stages are adopted, and they do not agree:

* `GrindingQueryBound.grinding_chain_clash_probability_le`, the ALL-PAIRS bound
  `N (N + 1) / 2 / |Block|` with `N = (q + 1) n`, QUADRATIC in the probe budget,
  for EVERY grinding strategy;
* `GrindingLinearBound.grinding_chain_clash_probability_le_linear`, the LINEAR
  `(q + 1) n (n + 1) / 2 / |Block|`, for STATE-FRAMED strategies only.

`GrindingLinearBound` HONESTY (ii) names the prover the linear bound excludes: one
that probes `frame(e0, t, p)`, forms the digest of the answer WITHOUT absorbing
it, probes at that digest, and so simulates a whole chain -- or a tree of
candidate chains -- inside its probe budget, replaying the winning path through
its absorbs afterwards.  Against it the two colliding answers may both be probes,
and the position charged frames at a digest only a LATER absorb makes a state.
That module says bounding this prover needs "a count over the prover's whole query
GRAPH with the path length capped at `n`".

THIS MODULE BUILDS THAT GRAPH AND CARRIES OUT THAT COUNT.  THE ANSWER IS NEGATIVE,
AND THAT IS THE RESULT: the graph refinement is a legitimate charging scheme, it
is proved sound for a class of provers STRICTLY LARGER than the state-framed one,
and the constant it delivers is exactly `GrindingQueryBound`'s all-pairs constant
-- because against the chain-simulating prover the refinement drops nothing.  No
numeric improvement for the general grinding prover is claimed anywhere below, and
none is proved.  What IS delivered is the UNIFIED CHARGING THEOREM that has both
adopted bounds as instances, the graph instance as a third, and the precise
statement of what the chain simulator does to it.

## What is proved

1. THE DIGEST GRAPH AND THE ABSORB PATH (section 1).  `answerDigestAt m T` is the
   digest of position `m`'s answer and `GrindingLinearBound.frameDigestAt m T` the
   digest it frames at; `GraphEdge ... N T d e` is "some position below `N` frames
   at `d` and answers a block whose digest is `e`", and `ReachIn ... N T k d` is
   "`d` is reachable from `e0` in at most `k` such edges" -- `k` the PATH LENGTH
   CAP, `N` the EDGE BUDGET, both monotone (`reach_in_mono_depth`,
   `reach_in_mono_edges`).  `absorb_path_graph_edge` is the chain's own path: the
   stage-`k` absorb is an edge from `grindState k` to `grindState (k + 1)`, so
   `state_reach_in` puts every stage digest at depth exactly its stage index.
   `OnAbsorbPath q n m` names the `n` absorb positions.
2. A STAGE CLASH IS A COLLISION OF TWO POSITIONS ON THE ABSORB PATH (section 2).
   `pathClashEvent` asks of the ABSORB positions of two stages below `n` what
   `GrindingQueryBound.distinctClashEvent` asks of any two of the `N` positions,
   and `grinding_clash_subset_path` proves the containment for EVERY strategy,
   with no state-framing hypothesis: the induction of `grinding_clash_aux` with
   the positions kept.  `path_clash_subset_distinct_clash` RECORDS THE INCLUSION
   the other way: this event is a subset of the one GQB charges -- every pair with
   a probe in it is dropped.  So the EVENT is strictly refined; the COUNT is what
   sections 3 to 6 are about.
3. THE UNIFIED CHARGE (section 3).  `ReassignInvariant E` is the one property the
   adopted `BirthdayClashBound.FreshStep` needs of an eligibility assignment:
   overwriting a FRESH position's own answer does not move its eligible set.
   `eligibleHitEvent E N` is "some fresh position's answer landed in its eligible
   set", and `grinding_clash_le_eligible_sum` is the headline: a
   reassign-invariant `E` with `(E m T).card ≤ c m`, plus a containment of the
   clash event in `eligibleHitEvent E N`, bounds the clash mass by
   `(∑_{m < N} c m) / |Block|`.
4. THE TWO ADOPTED BOUNDS ARE TWO INSTANCES (section 4).
   `grinding_clash_all_pairs_via_eligible`: `E = chainTarget`, `c m = 1 + m`, sum
   `N (N + 1) / 2`, no hypothesis -- GQB's constant, with the containment proved by
   pushing BOTH colliding positions down to the first occurrences of their query
   strings (`all_pairs_clash_subset`).  `grinding_clash_linear_via_eligible`:
   `E = stateTarget`, `c m = m / (q + 1) + 1`, sum `(q + 1) n (n + 1) / 2` under
   `StateFramedProbes` -- GLB's constant, through `eligible_hit_event_state`, which
   says GLB's `stateHitEvent` IS this module's eligible-hit event at that `E`.
   The two adopted bounds differ in nothing but the eligibility assignment.
5. THE GRAPH INSTANCE (section 5).  `reachTarget m T` is the base block together
   with those earlier answers whose digest is REACHABLE from `e0` along the edges
   laid down before `m`.  It is reassign-invariant (`reach_in_reassign`,
   `reach_target_reassign_invariant`) -- the edge budget `m` is what makes that
   true, and a target built from the WHOLE run's edges would not be.  `GraphFramed`
   is the prover-side condition it needs: every position frames at a node the run
   has already reached.  `graph_clash_subset` is the containment and
   `grinding_clash_graph_le` the resulting bound: `N (N + 1) / 2 / |Block|`, the
   ALL-PAIRS constant.  `graph_framed_of_state_framed_probes` shows every
   state-framed run is graph-framed, so the class covered here is at least as
   large as GLB's -- and section 6 shows it is strictly larger.
6. THE CHAIN-SIMULATING PROVER (section 6).  `chainSimulator q` is the prover GLB
   HONESTY (ii) describes, written down: probe `0` of a stage frames at the stage
   digest, probe `i + 1` frames at the DIGEST OF PROBE `i`'S ANSWER
   (`chain_simulator_probe_succ_frame`, `chain_simulator_probe_graph_edge`), and
   the absorb takes the payload of the probe whose answer digest hit a stage digest
   already formed, the last probe's payload otherwise (`simHitIndex`).
   `chain_simulator_not_state_framed` puts it outside GLB's class;
   `chain_simulator_graph_framed` puts it inside section 5's.  And then the point:
   `chain_simulator_every_earlier_answer_eligible` and
   `chain_simulator_reach_target_eq` prove that for this prover the graph-refined
   target IS the all-pairs target, position by position -- the filter removes
   NOTHING, because the simulator's probes chain and its whole query history hangs
   off `e0` as one connected piece of graph.  The per-position charge the scheme
   supplies at position `m` is therefore `1 + m`, not `m / (q + 1) + 1`, and
   `linear_constant_lt_all_pairs_constant` records that the two sums are not equal:
   for `q ≥ 1`, `n ≥ 1` the linear constant is STRICTLY smaller than what this
   charging scheme sums to.
7. THE CLOSED INSTANCES AND THE CONSTANT TABLE (section 7).
   `probe_grinder_graph_framed`; `chain_simulator_graph_clash_le`, section 5's
   bound at a strategy GLB does not cover; the non-emptiness tests
   `constant_table_path_clash`, `constant_table_chain_simulator_clashes` and
   `constant_table_reach_target_hit`; and at the envelope's `22 + 5 * 13 = 87`
   stages with `q = 2 ^ 20` probes per stage the numeral `4161109737606900 / |Block|`
   -- `GrindingQueryBound`'s, unchanged -- and
   `chain_simulator_clash_at_eighty_seven_many_probes_tiny`, which puts it below
   `2 ^ (-200)`.  `Fintype.card Block` is never evaluated: it is written as
   `2 ^ 256` through the adopted `RandomOracleSqueezes.block_card`.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every statement below is about
the uniform counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)`
-- one independent uniform block per byte string of length at most `L`.  The
fresh-query lemma everything rests on, the adopted
`BirthdayClashBound.fresh_coordinate_probability`, is the DEFINING property of a
random table and is false, as a theorem, for any fixed hash.  Replacing the
deployed Keccak by a table drawn from this law is an assumption with no proof
anywhere in this tree.

(ii) NO NEW NUMERIC BOUND IS PROVED.  `grinding_clash_graph_le`'s constant is
`GrindingQueryBound`'s all-pairs constant, not smaller by any amount.  The value of
the module is the unified charging theorem, the strictly larger prover class the
all-pairs constant is now proved for by a graph argument, and the TIGHTNESS
OBSERVATION: section 6 exhibits a concrete prover for which the graph-refined
eligible set is the whole all-pairs set.  Nothing here is an impossibility claim
about all proofs.  `chain_simulator_reach_target_eq` is a statement about THE
CHARGING SETS OF THIS SCHEME and nothing else: it says that this scheme, applied to
this prover, charges `1 + m` at position `m`, and
`linear_constant_lt_all_pairs_constant` that the sum of those charges is strictly
above the linear constant.  A different argument -- one that does not charge a
fresh position against a set of blocks at all -- is not excluded by anything below,
and no lower bound on any clash mass is proved anywhere here.

(iii) WHAT THE PATH LENGTH CAP DOES AND DOES NOT DO.  The absorb path has at most
`n` edges, and section 2 proves the clash is a collision of two positions ON IT.
That does NOT cap the depth at which a probe's answer sits in the graph: within a
SINGLE stage the simulator's `q` probes lay down a path of `q` edges
(`chain_simulator_probe_graph_edge`), so with `q ≥ n` the prover reaches depth `n`
without absorbing anything.  This is why `reachTarget` is stated with the depth cap
equal to the position index rather than to `n`: a cap of `n` would not be sound for
the containment, since the colliding partner may sit deeper.  A refinement that
uses the cap `n` would need to know that a node deeper than `n` cannot end up on
the absorb path, and that is exactly what is NOT true: the prover chooses its
absorbs after seeing the answers, and may absorb a payload whose answer it first
saw at depth `q`.

(iv) `GraphFramed` IS STILL A HYPOTHESIS, AND IT IS NOT EMPTY OF CONTENT.  It
excludes a prover that frames at a digest it never obtained from the oracle -- one
that writes down 32 arbitrary bytes and frames there.  Such a prover is covered by
`GrindingQueryBound`'s bound, which has no framing hypothesis at all, and is NOT
covered by `grinding_clash_graph_le`.  It is satisfiable: `probe_grinder_graph_framed`
and `chain_simulator_graph_framed` discharge it, and
`graph_framed_of_state_framed_probes` discharges it for every strategy
`GrindingLinearBound` covers.

(v) THE CHAIN CLASH EVENT ONLY, AND THE PROBES ARE FRAME-SHAPED.  What is bounded is
`GrindingQueryBound.grindingClashEvent`: two of the chain's first `n + 1` stage
digests coincide.  This is one named event of the transcript chain and NOT the
protocol's soundness error; nothing below aggregates into a soundness statement.
The probes remain FRAME queries at a digest, a tag and a payload the prover chooses,
exactly as `GrindingQueryBound` HONESTY (iv) sets out; grinding on the CHALLENGE
inputs is outside this event, and the challenge oracle is handed to the prover at
every digest free of charge.

(vi) THE SIMULATOR IS ONE STRATEGY, NOT THE WORST ONE.  `chainSimulator` chains its
probes linearly; the TREE of candidate chains GLB HONESTY (ii) also mentions is not
written down here, and no claim is made that the linear chain is the best use of a
probe budget.  For the tightness observation a single prover that defeats the
refinement suffices, and this is one.
-/

namespace Audit.Wire3.GrindingGraphBound

open Audit.Wire3
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.GrindingQueryBound
open Audit.Wire3.GrindingLinearBound

/-! ## 1. THE DIGEST GRAPH AND THE ABSORB PATH -/

/-- **THE NODE POSITION `m` PRODUCES.**  The digest of the block the oracle
answered at position `m`.  Together with `GrindingLinearBound.frameDigestAt m`,
the digest position `m` FRAMES at, it is the edge position `m` contributes to the
digest graph. -/
def answerDigestAt (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) : Transcript.Digest :=
  blockDigest (chainVal (grindSelSeq L hL e0 q g hb) m T)

/-- **THE DIGEST GRAPH'S EDGE RELATION.**  There is an edge `d -> e` when some
position below `N` frames at `d` and its answer has digest `e`.  Nodes are
digests; the node set the run can reach is generated from `e0` by these edges. -/
def GraphEdge (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) (d e : Transcript.Digest) : Prop :=
  ∃ m, m < N ∧ frameDigestAt L hL e0 q g hb m T = d ∧ answerDigestAt L hL e0 q g hb m T = e

/-- **REACHABLE FROM `e0` IN AT MOST `k` EDGES**, using only the edges of the
positions below `N`.  `ReachIn ... N T k d` is the node predicate the graph
refinement charges against: `k` is the PATH LENGTH CAP and `N` the edge budget. -/
def ReachIn (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) : Nat → Transcript.Digest → Prop
  | 0, d => d = e0
  | k + 1, d =>
      ReachIn L hL e0 q g hb N T k d ∨
        ∃ m, m < N ∧ ReachIn L hL e0 q g hb N T k (frameDigestAt L hL e0 q g hb m T) ∧
          answerDigestAt L hL e0 q g hb m T = d

theorem reach_in_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    ReachIn L hL e0 q g hb N T 0 e0 := rfl

theorem reach_in_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) (k : Nat) (d : Transcript.Digest) :
    ReachIn L hL e0 q g hb N T (k + 1) d ↔
      (ReachIn L hL e0 q g hb N T k d ∨
        ∃ m, m < N ∧ ReachIn L hL e0 q g hb N T k (frameDigestAt L hL e0 q g hb m T) ∧
          answerDigestAt L hL e0 q g hb m T = d) := Iff.rfl

/-- (1) A longer path cap reaches at least as much. -/
theorem reach_in_mono_depth (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) (d : Transcript.Digest) :
    ∀ k2 k : Nat, k ≤ k2 → ReachIn L hL e0 q g hb N T k d → ReachIn L hL e0 q g hb N T k2 d := by
  intro k2
  induction k2 with
  | zero => intro k hk h; rw [Nat.le_zero.mp hk] at h; exact h
  | succ j ih =>
      intro k hk h
      rcases Nat.lt_or_ge k (j + 1) with hlt | hge
      · exact Or.inl (ih k (by omega) h)
      · have : k = j + 1 := by omega
        rw [this] at h
        exact h

/-- (1) A larger edge budget reaches at least as much. -/
theorem reach_in_mono_edges (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N N2 : Nat) (hN : N ≤ N2)
    (T : OracleTable (boundedQueries L)) :
    ∀ (k : Nat) (d : Transcript.Digest),
      ReachIn L hL e0 q g hb N T k d → ReachIn L hL e0 q g hb N2 T k d := by
  intro k
  induction k with
  | zero => intro d h; exact h
  | succ j ih =>
      intro d h
      rcases h with h | ⟨m, hm, hfr, hans⟩
      · exact Or.inl (ih d h)
      · exact Or.inr ⟨m, lt_of_lt_of_le hm hN, ih _ hfr, hans⟩

/-- (1) One edge extends a path: if position `m`'s frame digest is reachable in
`k` edges then its answer digest is reachable in `k + 1`. -/
theorem reach_in_step (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) (k m : Nat) (hm : m < N)
    (h : ReachIn L hL e0 q g hb N T k (frameDigestAt L hL e0 q g hb m T)) :
    ReachIn L hL e0 q g hb N T (k + 1) (answerDigestAt L hL e0 q g hb m T) :=
  Or.inr ⟨m, hm, h, rfl⟩

/-- (1) An EDGE of the digest graph extends a path by one. -/
theorem reach_in_of_graph_edge (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) (k : Nat) (d e : Transcript.Digest)
    (hE : GraphEdge L hL e0 q g hb N T d e) (h : ReachIn L hL e0 q g hb N T k d) :
    ReachIn L hL e0 q g hb N T (k + 1) e := by
  obtain ⟨m, hm, hfr, hans⟩ := hE
  refine Or.inr ⟨m, hm, ?_, hans⟩
  rw [hfr]
  exact h

/-- (1) **THE ABSORB PATH'S EDGES.**  The absorb of stage `k` frames at the
stage-`k` digest and its answer digest IS the stage-`k + 1` digest: the chain's
stage digests are the nodes of a path in the digest graph whose edges are the
`n` absorb positions. -/
theorem absorb_answer_digest (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    answerDigestAt L hL e0 q g hb (slotPos q k q) T = grindState L hL e0 q g hb (k + 1) T := rfl

theorem absorb_frame_digest (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    frameDigestAt L hL e0 q g hb (slotPos q k q) T = grindState L hL e0 q g hb k T :=
  frame_digest_at_absorb L hL e0 q g hb k T

/-- (1) **THE ABSORB PATH'S STEPS ARE EDGES.**  The absorb of stage `k` is an edge
of the digest graph from the stage-`k` digest to the stage-`k + 1` digest. -/
theorem absorb_path_graph_edge (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) (k : Nat) (hk : slotPos q k q < N) :
    GraphEdge L hL e0 q g hb N T (grindState L hL e0 q g hb k T)
      (grindState L hL e0 q g hb (k + 1) T) :=
  ⟨slotPos q k q, hk, absorb_frame_digest L hL e0 q g hb k T,
    absorb_answer_digest L hL e0 q g hb k T⟩

/-- (1) **THE ABSORB PATH IS A PATH.**  `grindState k` is a node reachable from
`e0` in exactly `k` edges, for every strategy and every table, provided the `k`
absorb positions are inside the edge budget. -/
theorem state_reach_in (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ k : Nat, (∀ j, j < k → slotPos q j q < N) →
      ReachIn L hL e0 q g hb N T k (grindState L hL e0 q g hb k T) := by
  intro k
  induction k with
  | zero => intro _; exact reach_in_zero L hL e0 q g hb N T
  | succ j ih =>
      intro hj
      have hstep : ReachIn L hL e0 q g hb N T (j + 1)
          (answerDigestAt L hL e0 q g hb (slotPos q j q) T) := by
        refine reach_in_step L hL e0 q g hb N T j (slotPos q j q) (hj j (Nat.lt_succ_self j)) ?_
        rw [absorb_frame_digest]
        exact ih (fun i hi => hj i (by omega))
      rwa [absorb_answer_digest] at hstep

/-- **THE POSITIONS OF THE ABSORB PATH.**  The `n` absorb positions of the first
`n` stages: the edges whose nodes are the chain's stage digests. -/
def OnAbsorbPath (q n m : Nat) : Prop := ∃ k, k < n ∧ m = slotPos q k q

theorem on_absorb_path_lt (q n m : Nat) (h : OnAbsorbPath q n m) : m < n * (q + 1) := by
  obtain ⟨k, hk, rfl⟩ := h
  exact slot_pos_lt_of_le q n k hk

/-- (1) The absorb path has `n` edges, one per stage, and its nodes are the
`n + 1` stage digests -- all of them reachable from `e0`. -/
theorem absorb_path_node_reach (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L)) (k : Nat) (hk : k ≤ n) :
    ReachIn L hL e0 q g hb (n * (q + 1)) T k (grindState L hL e0 q g hb k T) :=
  state_reach_in L hL e0 q g hb (n * (q + 1)) T k
    (fun j hj => slot_pos_lt_of_le q n j (by omega))

/-! ## 2. A STAGE CLASH IS A COLLISION OF TWO POSITIONS ON THE ABSORB PATH -/

open Classical in
/-- **THE PATH-COLLISION EVENT.**  Two ABSORB positions of stages below `n` asked
DIFFERENT byte strings and were answered alike, or one of them was answered the
base block.  Both colliding positions lie on the absorb path; `GrindingQueryBound`'s
`distinctClashEvent` asks the same of ANY two of the `n (q + 1)` positions. -/
noncomputable def pathClashEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    (∃ r s : Nat, r < s ∧ s < n ∧
        grindSelSeq L hL e0 q g hb (slotPos q r q) T
            ≠ grindSelSeq L hL e0 q g hb (slotPos q s q) T ∧
        chainVal (grindSelSeq L hL e0 q g hb) (slotPos q r q) T
          = chainVal (grindSelSeq L hL e0 q g hb) (slotPos q s q) T) ∨
    (∃ s : Nat, s < n ∧
      chainVal (grindSelSeq L hL e0 q g hb) (slotPos q s q) T ∈ avoidBase e0))

theorem mem_path_clash_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L)) :
    T ∈ pathClashEvent L hL e0 q g hb n ↔
      (∃ r s : Nat, r < s ∧ s < n ∧
          grindSelSeq L hL e0 q g hb (slotPos q r q) T
              ≠ grindSelSeq L hL e0 q g hb (slotPos q s q) T ∧
          chainVal (grindSelSeq L hL e0 q g hb) (slotPos q r q) T
            = chainVal (grindSelSeq L hL e0 q g hb) (slotPos q s q) T) ∨
      (∃ s : Nat, s < n ∧
        chainVal (grindSelSeq L hL e0 q g hb) (slotPos q s q) T ∈ avoidBase e0) := by
  simp only [pathClashEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- (2) The induction of `GrindingQueryBound.grinding_clash_aux` with the
POSITIONS kept: the two colliding queries it produces are the absorbs of two
stages below `n`, never probes. -/
theorem grinding_clash_path_aux (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ s : Nat, s ≤ n → ∀ r : Nat, r < s →
      grindState L hL e0 q g hb r T = grindState L hL e0 q g hb s T →
      T ∈ pathClashEvent L hL e0 q g hb n := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro hsn r hrs heq
      obtain ⟨s2, rfl⟩ : ∃ s2, s = s2 + 1 := ⟨s - 1, by omega⟩
      have hs2 : s2 < n := by omega
      cases r with
      | zero =>
          refine (mem_path_clash_event L hL e0 q g hb n T).mpr (Or.inr ⟨s2, hs2, ?_⟩)
          rw [avoidBase, Finset.mem_singleton]
          exact (congrArg OuterChallenge.digestBlock heq).symm
      | succ r2 =>
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
          · exact (mem_path_clash_event L hL e0 q g hb n T).mpr
              (Or.inl ⟨r2, s2, by omega, hs2, hq, hval⟩)

/-- (2) **THE HEADLINE OF SECTION 2.**  Every stage clash of a grinding run --
for EVERY strategy, with no state-framing hypothesis -- is a collision between
two positions that BOTH lie on the absorb path, or an absorb-path answer landing
on the base block. -/
theorem grinding_clash_subset_path (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    grindingClashEvent L hL e0 q g hb n ⊆ pathClashEvent L hL e0 q g hb n := by
  intro T hT
  obtain ⟨r, s, hrs, hsn, heq⟩ := (mem_grinding_clash_event L hL e0 q g hb n T).mp hT
  exact grinding_clash_path_aux L hL e0 q g hb n T s hsn r hrs heq

/-- (2) **THE INCLUSION, RECORDED.**  The path-collision event is a SUBSET of the
all-pairs event `GrindingQueryBound.distinctClashEvent` that GQB's bound charges:
the pairs with a probe in them are dropped.  So section 2 strictly refines the
EVENT; what it does not by itself refine is the COUNT, which is what sections 3
to 5 are about. -/
theorem path_clash_subset_distinct_clash (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    pathClashEvent L hL e0 q g hb n
      ⊆ distinctClashEvent (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) := by
  intro T hT
  rcases (mem_path_clash_event L hL e0 q g hb n T).mp hT with
    ⟨r, s, hrs, hsn, hne, hval⟩ | ⟨s, hsn, hin⟩
  · exact (mem_distinct_clash_event _ _ _ T).mpr
      (Or.inl ⟨slotPos q r q, slotPos q s q, slot_pos_mono q hrs,
        slot_pos_lt_of_le q n s hsn, hne, hval⟩)
  · exact (mem_distinct_clash_event _ _ _ T).mpr
      (Or.inr ⟨slotPos q s q, slot_pos_lt_of_le q n s hsn, hin⟩)

/-- (2) The two colliding positions of a path collision are absorb positions of
stages below `n`. -/
theorem path_clash_positions_on_path (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ pathClashEvent L hL e0 q g hb n) :
    ∃ m1 m2 : Nat, OnAbsorbPath q n m1 ∧ OnAbsorbPath q n m2 ∧
      chainVal (grindSelSeq L hL e0 q g hb) m1 T
        = chainVal (grindSelSeq L hL e0 q g hb) m2 T := by
  rcases (mem_path_clash_event L hL e0 q g hb n T).mp hT with
    ⟨r, s, hrs, hsn, -, hval⟩ | ⟨s, hsn, -⟩
  · exact ⟨slotPos q r q, slotPos q s q, ⟨r, by omega, rfl⟩, ⟨s, hsn, rfl⟩, hval⟩
  · exact ⟨slotPos q s q, slotPos q s q, ⟨s, hsn, rfl⟩, ⟨s, hsn, rfl⟩, rfl⟩

/-- (2) **THE PATH-COLLISION EVENT IS NOT EMPTY.**  The constant table answers the
base block at every position, so the stage-`0` absorb already lands on it. -/
theorem constant_table_path_clash (L : Nat) (hL : 64 ≤ L) (q : Nat) (g : GrindingStrategy)
    (hb : GrindingBounded L g) (n : Nat) (hn : 1 ≤ n) :
    constantTable L ∈ pathClashEvent L hL OuterInitial.zeroDigest q g hb n := by
  refine (mem_path_clash_event L hL OuterInitial.zeroDigest q g hb n _).mpr (Or.inr ⟨0, hn, ?_⟩)
  rw [avoidBase, Finset.mem_singleton]
  rfl

/-! ## 3. THE UNIFIED CHARGE: A FRESH POSITION AGAINST ITS ELIGIBLE SET -/

/-- **AN ELIGIBILITY ASSIGNMENT THAT THE FRESH-QUERY STEP ACCEPTS.**  `E m T` is
the set of blocks position `m` is charged against.  The one thing the adopted
`BirthdayClashBound.FreshStep` demands of it is that overwriting the answer at a
FRESH position `m` does not move `E m` -- that it is read off the answers strictly
before `m`. -/
def ReassignInvariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block) : Prop :=
  ∀ (m : Nat) (T : OracleTable (boundedQueries L)),
    T ∈ freshAt (grindSelSeq L hL e0 q g hb) m → ∀ b : Block,
      E m (reassign T (grindSelSeq L hL e0 q g hb m T) b) = E m T

/-- **THE ELIGIBLE-HIT EVENT.**  Some position below `N` asked a NEW byte string
and its answer landed in that position's eligible set. -/
def eligibleHitEvent (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block) :
    Nat → Finset (OracleTable (boundedQueries L))
  | 0 => ∅
  | m + 1 =>
      eligibleHitEvent L hL e0 q g hb E m ∪
        (freshAt (grindSelSeq L hL e0 q g hb) m).filter
          (fun T => chainVal (grindSelSeq L hL e0 q g hb) m T ∈ E m T)

theorem eligible_hit_event_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block) (m : Nat) :
    eligibleHitEvent L hL e0 q g hb E (m + 1)
      = eligibleHitEvent L hL e0 q g hb E m ∪
        (freshAt (grindSelSeq L hL e0 q g hb) m).filter
          (fun T => chainVal (grindSelSeq L hL e0 q g hb) m T ∈ E m T) := rfl

theorem mem_eligible_hit_event (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block) (N m : Nat) (hm : m < N)
    (T : OracleTable (boundedQueries L))
    (hf : T ∈ freshAt (grindSelSeq L hL e0 q g hb) m)
    (hv : chainVal (grindSelSeq L hL e0 q g hb) m T ∈ E m T) :
    T ∈ eligibleHitEvent L hL e0 q g hb E N := by
  induction N with
  | zero => exact absurd hm (Nat.not_lt_zero m)
  | succ k ih =>
      rw [eligible_hit_event_succ]
      rcases Nat.lt_or_ge m k with h | h
      · exact Finset.mem_union_left _ (ih h)
      · have hmk : m = k := by omega
        subst hmk
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf, hv⟩)

/-- (3) A reassign-invariant eligibility assignment makes every position an
adaptive fresh oracle step, in the sense of the adopted
`BirthdayClashBound.FreshStep`. -/
theorem eligible_fresh_step (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block)
    (hinv : ReassignInvariant L hL e0 q g hb E) (m : Nat) :
    FreshStep (boundedQueries L) (freshAt (grindSelSeq L hL e0 q g hb) m)
      (grindSelSeq L hL e0 q g hb m) (E m) := by
  have hc := grinding_sequence_fresh_causal L hL e0 q g hb
  exact ⟨fun T hT b => fresh_at_reassign hc m T hT b,
    fun T hT b => hc m T hT b m (le_refl m), fun T hT b => hinv m T hT b⟩

/-- (3) The mass of one position's eligible hit, at a cardinality budget `c m`. -/
theorem eligible_step_bound (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block)
    (hinv : ReassignInvariant L hL e0 q g hb E) (c : Nat → Nat)
    (hcard : ∀ (m : Nat) (T : OracleTable (boundedQueries L)), (E m T).card ≤ c m) (m : Nat) :
    oracleProbability (boundedQueries L)
        ((freshAt (grindSelSeq L hL e0 q g hb) m).filter
          (fun T => chainVal (grindSelSeq L hL e0 q g hb) m T ∈ E m T))
      ≤ ((c m : Nat) : ℚ) / (Fintype.card Block : ℚ) :=
  adaptive_fresh_step_abs (eligible_fresh_step L hL e0 q g hb E hinv m) (c m)
    (fun T _ => hcard m T)

/-- (3) The union bound over the positions. -/
theorem eligible_hit_probability_le_sum (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block)
    (hinv : ReassignInvariant L hL e0 q g hb E) (c : Nat → Nat)
    (hcard : ∀ (m : Nat) (T : OracleTable (boundedQueries L)), (E m T).card ≤ c m) (N : Nat) :
    oracleProbability (boundedQueries L) (eligibleHitEvent L hL e0 q g hb E N)
      ≤ ∑ m in Finset.range N, ((c m : Nat) : ℚ) / (Fintype.card Block : ℚ) := by
  induction N with
  | zero =>
      rw [show eligibleHitEvent L hL e0 q g hb E 0
            = (∅ : Finset (OracleTable (boundedQueries L))) from rfl,
        Finset.range_zero, Finset.sum_empty, oracleProbability, Finset.card_empty,
        Nat.cast_zero, zero_div]
  | succ k ih =>
      rw [eligible_hit_event_succ]
      refine le_trans (oracle_probability_union_le _ _ _) ?_
      refine le_trans (add_le_add ih
        (eligible_step_bound L hL e0 q g hb E hinv c hcard k)) ?_
      exact le_of_eq (Finset.sum_range_succ _ _).symm

/-- **THE UNIFIED CHARGING THEOREM.**  Let `E` assign to every position a set of
blocks which is READ OFF THE ANSWERS BEFORE IT (`ReassignInvariant`) and has at
most `c m` elements, and suppose the chain's clash event is contained in the
event that some fresh position's answer landed in its own eligible set.  Then the
clash mass is at most `(∑_{m < N} c m) / |Block|`.

This is the one counting engine behind both adopted bounds: `GrindingQueryBound`'s
all-pairs constant is the instance `E = chainTarget`, `c m = 1 + m`, and
`GrindingLinearBound`'s linear constant is the instance `E = stateTarget`,
`c m = m / (q + 1) + 1`.  A third instance -- the digest graph's reachable set --
is section 4's, and the chain simulator of section 5 is what shows it collapses
to the first. -/
theorem grinding_clash_le_eligible_sum (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (E : Nat → OracleTable (boundedQueries L) → Finset Block)
    (hinv : ReassignInvariant L hL e0 q g hb E) (c : Nat → Nat)
    (hcard : ∀ (m : Nat) (T : OracleTable (boundedQueries L)), (E m T).card ≤ c m)
    (hsub : grindingClashEvent L hL e0 q g hb n
      ⊆ eligibleHitEvent L hL e0 q g hb E (n * (q + 1))) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)
      ≤ (∑ m in Finset.range (n * (q + 1)), ((c m : Nat) : ℚ)) / (Fintype.card Block : ℚ) := by
  refine le_trans (oracle_probability_mono _ _ _ hsub) ?_
  refine le_trans (eligible_hit_probability_le_sum L hL e0 q g hb E hinv c hcard (n * (q + 1))) ?_
  exact le_of_eq (Finset.sum_div _ _ _).symm


/-! ## 4. THE TWO ADOPTED BOUNDS ARE TWO INSTANCES -/

/-- (4) The all-pairs target of `GrindingQueryBound` -- the base block together
with every earlier answer -- is reassign-invariant.  This is the third clause of
the adopted `GrindingQueryBound.fresh_step_of_fresh_causal`. -/
theorem all_pairs_reassign_invariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) :
    ReassignInvariant L hL e0 q g hb
      (chainTarget (grindSelSeq L hL e0 q g hb) (avoidBase e0)) :=
  fun m T hT b =>
    (fresh_step_of_fresh_causal (grinding_sequence_fresh_causal L hL e0 q g hb)
      (avoidBase e0) m).2.2 T hT b

/-- (4) And it has at most `1 + m` elements at position `m`. -/
theorem all_pairs_card_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) :
    (chainTarget (grindSelSeq L hL e0 q g hb) (avoidBase e0) m T).card ≤ 1 + m := by
  have h := chain_target_card_le (grindSelSeq L hL e0 q g hb) (avoidBase e0) m T
  rwa [avoid_base_card] at h

/-- (4) **THE ALL-PAIRS CONTAINMENT, WITH BOTH POSITIONS PUSHED DOWN.**  Every
stage clash puts a FRESH position's answer into that position's all-pairs target:
take the first occurrences `cr`, `cs` of the two colliding query strings -- both
fresh, with the same answers as the positions they repeat, and distinct because
the two strings are -- and charge the LATER of the two.  No hypothesis on the
strategy. -/
theorem all_pairs_clash_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    grindingClashEvent L hL e0 q g hb n
      ⊆ eligibleHitEvent L hL e0 q g hb
          (chainTarget (grindSelSeq L hL e0 q g hb) (avoidBase e0)) (n * (q + 1)) := by
  intro T hT
  have hd : T ∈ distinctClashEvent (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) :=
    grinding_clash_subset L hL e0 q g hb n hT
  rcases (mem_distinct_clash_event _ _ _ T).mp hd with ⟨r, s, hrs, hsn, hne, hval⟩ | ⟨s, hsn, hin⟩
  · obtain ⟨cr, hcrle, hcrsel, hcrf⟩ := exists_first_occurrence (grindSelSeq L hL e0 q g hb) T r
    obtain ⟨cs, hcsle, hcssel, hcsf⟩ := exists_first_occurrence (grindSelSeq L hL e0 q g hb) T s
    have hvr : chainVal (grindSelSeq L hL e0 q g hb) cr T
        = chainVal (grindSelSeq L hL e0 q g hb) r T := by
      show T (grindSelSeq L hL e0 q g hb cr T) = T (grindSelSeq L hL e0 q g hb r T)
      rw [hcrsel]
    have hvs : chainVal (grindSelSeq L hL e0 q g hb) cs T
        = chainVal (grindSelSeq L hL e0 q g hb) s T := by
      show T (grindSelSeq L hL e0 q g hb cs T) = T (grindSelSeq L hL e0 q g hb s T)
      rw [hcssel]
    have hne2 : cr ≠ cs := by
      intro h
      subst h
      exact hne (hcrsel.symm.trans hcssel)
    have hvv : chainVal (grindSelSeq L hL e0 q g hb) cr T
        = chainVal (grindSelSeq L hL e0 q g hb) cs T := hvr.trans (hval.trans hvs.symm)
    rcases Nat.lt_or_ge cr cs with hlt | hge
    · refine mem_eligible_hit_event L hL e0 q g hb _ (n * (q + 1)) cs (by omega) T hcsf ?_
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨cr, Finset.mem_range.mpr hlt, hvv⟩)
    · refine mem_eligible_hit_event L hL e0 q g hb _ (n * (q + 1)) cr (by omega) T hcrf ?_
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨cs, Finset.mem_range.mpr (by omega), hvv.symm⟩)
  · obtain ⟨c, hcle, hcsel, hcf⟩ := exists_first_occurrence (grindSelSeq L hL e0 q g hb) T s
    have hv : chainVal (grindSelSeq L hL e0 q g hb) c T
        = chainVal (grindSelSeq L hL e0 q g hb) s T := by
      show T (grindSelSeq L hL e0 q g hb c T) = T (grindSelSeq L hL e0 q g hb s T)
      rw [hcsel]
    refine mem_eligible_hit_event L hL e0 q g hb _ (n * (q + 1)) c (by omega) T hcf ?_
    refine Finset.mem_union_left _ ?_
    rw [hv]
    exact hin

theorem two_mul_sum_succ (N : Nat) : 2 * (∑ m in Finset.range N, (1 + m)) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

theorem sum_succ_rat (N : Nat) :
    ∑ m in Finset.range N, ((1 + m : Nat) : ℚ) = ((N * (N + 1) : Nat) : ℚ) / 2 := by
  have h := two_mul_sum_succ N
  have hcast : ((2 * (∑ m in Finset.range N, (1 + m)) : Nat) : ℚ)
      = ((N * (N + 1) : Nat) : ℚ) := congrArg (fun z : Nat => (z : ℚ)) h
  rw [Nat.cast_mul, Nat.cast_sum] at hcast
  push_cast at hcast ⊢
  linarith

/-- (4) **INSTANCE ONE: `GrindingQueryBound`'S ALL-PAIRS CONSTANT.**  The unified
charge with `E = chainTarget`, `c m = 1 + m`, gives back
`N (N + 1) / 2 / |Block|`, `N = n (q + 1)`, with no hypothesis on the strategy --
the adopted `GrindingQueryBound.grinding_chain_clash_probability_le`. -/
theorem grinding_clash_all_pairs_via_eligible (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)
      ≤ ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) := by
  have h := grinding_clash_le_eligible_sum L hL e0 q g hb n
    (chainTarget (grindSelSeq L hL e0 q g hb) (avoidBase e0))
    (all_pairs_reassign_invariant L hL e0 q g hb) (fun m => 1 + m)
    (fun m T => all_pairs_card_le L hL e0 q g hb m T)
    (all_pairs_clash_subset L hL e0 q g hb n)
  rw [sum_succ_rat] at h
  refine le_trans h (le_of_eq ?_)
  push_cast
  ring

/-- (4) The state target of `GrindingLinearBound` is reassign-invariant: its third
clause again. -/
theorem state_reassign_invariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) :
    ReassignInvariant L hL e0 q g hb (stateTarget L hL e0 q g hb) :=
  fun m T hT b => (state_target_fresh_step L hL e0 q g hb m).2.2 T hT b

/-- (4) The eligible-hit event of the state target IS the adopted
`GrindingLinearBound.stateHitEvent`. -/
theorem eligible_hit_event_state (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat) :
    eligibleHitEvent L hL e0 q g hb (stateTarget L hL e0 q g hb) N
      = stateHitEvent L hL e0 q g hb N := by
  induction N with
  | zero => rfl
  | succ k ih => rw [eligible_hit_event_succ, state_hit_event_succ, ih]

/-- (4) **INSTANCE TWO: `GrindingLinearBound`'S LINEAR CONSTANT.**  The unified
charge with `E = stateTarget`, `c m = m / (q + 1) + 1`, gives back
`(q + 1) n (n + 1) / 2 / |Block|` for a STATE-FRAMED strategy -- the adopted
`GrindingLinearBound.grinding_chain_clash_probability_le_linear`.  The two adopted
bounds differ only in the eligibility assignment. -/
theorem grinding_clash_linear_via_eligible (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hp : StateFramedProbes g)
    (n : Nat) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)
      ≤ (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2 / (Fintype.card Block : ℚ) := by
  have hsub : grindingClashEvent L hL e0 q g hb n
      ⊆ eligibleHitEvent L hL e0 q g hb (stateTarget L hL e0 q g hb) (n * (q + 1)) := by
    rw [eligible_hit_event_state]
    intro T hT
    exact grinding_clash_state_framed_subset L hL e0 q g hb n T
      (state_framed_of_probes L hL e0 q g hb hp (n * (q + 1)) T) hT
  have h := grinding_clash_le_eligible_sum L hL e0 q g hb n (stateTarget L hL e0 q g hb)
    (state_reassign_invariant L hL e0 q g hb) (fun m => m / (q + 1) + 1)
    (fun m T => state_target_card_le L hL e0 q g hb m T) hsub
  rwa [sum_slot_card_rat q n] at h


/-! ## 5. THE GRAPH INSTANCE: CHARGING AGAINST THE REACHABLE NODES -/

open Classical

/-- (5) Overwriting a fresh position's answer moves no earlier position's frame
digest: the query at an earlier position is a function of the earlier answers and
of the challenge oracle, and neither moves. -/
theorem frame_digest_at_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ freshAt (grindSelSeq L hL e0 q g hb) m) (b : Block) (j : Nat) (hj : j ≤ m) :
    frameDigestAt L hL e0 q g hb j (reassign T (grindSelSeq L hL e0 q g hb m T) b)
      = frameDigestAt L hL e0 q g hb j T := by
  show (grindQuery e0 q g
      (runAns L hL e0 q g hb j (reassign T (grindSelSeq L hL e0 q g hb m T) b))
      (challengesOf L hL (reassign T (grindSelSeq L hL e0 q g hb m T) b)) j).1 = _
  rw [run_ans_reassign L hL e0 q g hb m T hT b j hj,
    challenges_of_reassign L hL e0 q g hb m T b]
  rfl

/-- (5) Nor any earlier position's answer digest. -/
theorem answer_digest_at_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ freshAt (grindSelSeq L hL e0 q g hb) m) (b : Block) (j : Nat) (hj : j < m) :
    answerDigestAt L hL e0 q g hb j (reassign T (grindSelSeq L hL e0 q g hb m T) b)
      = answerDigestAt L hL e0 q g hb j T :=
  congrArg blockDigest
    (chain_val_fresh_stable (grinding_sequence_fresh_causal L hL e0 q g hb) m T hT b j hj)

/-- (5) **THE GRAPH BUILT OUT OF THE EDGES BEFORE `m` IS REASSIGN-INVARIANT.**  Its
nodes are read off answers strictly before `m`, so overwriting position `m`'s own
answer leaves the reachable set alone -- which is what makes a graph-refined
target a legal fresh-step target at all. -/
theorem reach_in_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ freshAt (grindSelSeq L hL e0 q g hb) m) (b : Block) :
    ∀ (k : Nat) (d : Transcript.Digest),
      ReachIn L hL e0 q g hb m (reassign T (grindSelSeq L hL e0 q g hb m T) b) k d ↔
        ReachIn L hL e0 q g hb m T k d := by
  intro k
  induction k with
  | zero => intro d; exact Iff.rfl
  | succ j ih =>
      intro d
      constructor
      · rintro (h | ⟨m2, hm2, hfr, hans⟩)
        · exact Or.inl ((ih d).mp h)
        · refine Or.inr ⟨m2, hm2, ?_, ?_⟩
          · have h2 := (ih _).mp hfr
            rwa [frame_digest_at_reassign L hL e0 q g hb m T hT b m2 (le_of_lt hm2)] at h2
          · rwa [answer_digest_at_reassign L hL e0 q g hb m T hT b m2 hm2] at hans
      · rintro (h | ⟨m2, hm2, hfr, hans⟩)
        · exact Or.inl ((ih d).mpr h)
        · refine Or.inr ⟨m2, hm2, ?_, ?_⟩
          · refine (ih _).mpr ?_
            rwa [frame_digest_at_reassign L hL e0 q g hb m T hT b m2 (le_of_lt hm2)]
          · rwa [answer_digest_at_reassign L hL e0 q g hb m T hT b m2 hm2]

/-- **THE GRAPH-REFINED ELIGIBLE SET.**  The base block, together with those
earlier answers whose digest is a node REACHABLE FROM `e0` along the edges the run
has already laid down -- at most `m` of them, and a path of at most `m` edges.
This is the refinement the question asks for: charge position `m` not against
every earlier answer but only against the ones that sit in the graph the prover
has actually built. -/
noncomputable def reachTarget (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) : Finset Block :=
  avoidBase e0 ∪
    ((Finset.range m).image (fun j => chainVal (grindSelSeq L hL e0 q g hb) j T)).filter
      (fun b => ReachIn L hL e0 q g hb m T m (blockDigest b))

theorem reach_target_card_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat)
    (T : OracleTable (boundedQueries L)) :
    (reachTarget L hL e0 q g hb m T).card ≤ 1 + m := by
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [avoid_base_card]
  refine Nat.add_le_add_left ?_ 1
  exact le_trans (Finset.card_filter_le _ _) (le_trans Finset.card_image_le
    (le_of_eq (Finset.card_range m)))

/-- (5) The graph-refined target is reassign-invariant, so the unified charge
accepts it. -/
theorem reach_target_reassign_invariant (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) :
    ReassignInvariant L hL e0 q g hb (reachTarget L hL e0 q g hb) := by
  intro m T hT b
  have himg : ((Finset.range m).image
        (fun j => chainVal (grindSelSeq L hL e0 q g hb) j
          (reassign T (grindSelSeq L hL e0 q g hb m T) b)))
      = (Finset.range m).image (fun j => chainVal (grindSelSeq L hL e0 q g hb) j T) := by
    refine Finset.image_congr ?_
    intro j hj
    exact chain_val_fresh_stable (grinding_sequence_fresh_causal L hL e0 q g hb) m T hT b j
      (Finset.mem_range.mp hj)
  show avoidBase e0 ∪ _ = avoidBase e0 ∪ _
  rw [himg]
  refine congrArg (fun z => avoidBase e0 ∪ z) (Finset.filter_congr ?_)
  intro b2 _
  exact reach_in_reassign L hL e0 q g hb m T hT b m (blockDigest b2)

/-- **A GRAPH-FRAMED RUN.**  Every position frames at a digest the run can REACH
from `e0` along the edges of the positions before it.  This is strictly weaker
than `GrindingLinearBound.StateFramed`: a probe may frame at the digest of another
PROBE's answer, which no absorb ever made a state, as long as that digest is in
the graph.  Framing at a digest pulled out of nowhere is what it excludes. -/
def GraphFramed (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) : Prop :=
  ∀ m, m < N → ReachIn L hL e0 q g hb m T m (frameDigestAt L hL e0 q g hb m T)

/-- (5) In a graph-framed run every position's ANSWER digest is a node too. -/
theorem graph_framed_answer_reach (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat)
    (T : OracleTable (boundedQueries L)) (hgf : GraphFramed L hL e0 q g hb N T) (m : Nat)
    (hm : m < N) :
    ReachIn L hL e0 q g hb (m + 1) T (m + 1) (answerDigestAt L hL e0 q g hb m T) :=
  reach_in_step L hL e0 q g hb (m + 1) T m m (Nat.lt_succ_self m)
    (reach_in_mono_edges L hL e0 q g hb m (m + 1) (Nat.le_succ m) T m _ (hgf m hm))

/-- (5) **THE GRAPH CONTAINMENT.**  For a graph-framed run every stage clash puts a
fresh position's answer into that position's REACHABLE target.  The proof is the
all-pairs push-down of section 4 with one extra step: the partner's answer digest
is a node, reachable in at most as many edges as the charged position has behind
it. -/
theorem graph_clash_subset (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (hgf : ∀ T : OracleTable (boundedQueries L), GraphFramed L hL e0 q g hb (n * (q + 1)) T) :
    grindingClashEvent L hL e0 q g hb n
      ⊆ eligibleHitEvent L hL e0 q g hb (reachTarget L hL e0 q g hb) (n * (q + 1)) := by
  intro T hT
  have hd : T ∈ distinctClashEvent (grindSelSeq L hL e0 q g hb) (avoidBase e0) (n * (q + 1)) :=
    grinding_clash_subset L hL e0 q g hb n hT
  have hcharge : ∀ c1 c2 : Nat, c1 < c2 → c2 < n * (q + 1) →
      T ∈ freshAt (grindSelSeq L hL e0 q g hb) c2 →
      chainVal (grindSelSeq L hL e0 q g hb) c1 T
        = chainVal (grindSelSeq L hL e0 q g hb) c2 T →
      T ∈ eligibleHitEvent L hL e0 q g hb (reachTarget L hL e0 q g hb) (n * (q + 1)) := by
    intro c1 c2 h12 h2N hf hv
    refine mem_eligible_hit_event L hL e0 q g hb _ (n * (q + 1)) c2 h2N T hf ?_
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_image.mpr ⟨c1, Finset.mem_range.mpr h12, hv⟩
    · have hreach := graph_framed_answer_reach L hL e0 q g hb (n * (q + 1)) T (hgf T) c1
        (lt_trans h12 h2N)
      have hreach2 := reach_in_mono_edges L hL e0 q g hb (c1 + 1) c2 h12 T (c1 + 1) _ hreach
      have hreach3 := reach_in_mono_depth L hL e0 q g hb c2 T _ c2 (c1 + 1) h12 hreach2
      show ReachIn L hL e0 q g hb c2 T c2
        (blockDigest (chainVal (grindSelSeq L hL e0 q g hb) c2 T))
      rw [← hv]
      exact hreach3
  rcases (mem_distinct_clash_event _ _ _ T).mp hd with ⟨r, s, hrs, hsn, hne, hval⟩ | ⟨s, hsn, hin⟩
  · obtain ⟨cr, hcrle, hcrsel, hcrf⟩ := exists_first_occurrence (grindSelSeq L hL e0 q g hb) T r
    obtain ⟨cs, hcsle, hcssel, hcsf⟩ := exists_first_occurrence (grindSelSeq L hL e0 q g hb) T s
    have hvr : chainVal (grindSelSeq L hL e0 q g hb) cr T
        = chainVal (grindSelSeq L hL e0 q g hb) r T := by
      show T (grindSelSeq L hL e0 q g hb cr T) = T (grindSelSeq L hL e0 q g hb r T)
      rw [hcrsel]
    have hvs : chainVal (grindSelSeq L hL e0 q g hb) cs T
        = chainVal (grindSelSeq L hL e0 q g hb) s T := by
      show T (grindSelSeq L hL e0 q g hb cs T) = T (grindSelSeq L hL e0 q g hb s T)
      rw [hcssel]
    have hne2 : cr ≠ cs := by
      intro h
      subst h
      exact hne (hcrsel.symm.trans hcssel)
    have hvv : chainVal (grindSelSeq L hL e0 q g hb) cr T
        = chainVal (grindSelSeq L hL e0 q g hb) cs T := hvr.trans (hval.trans hvs.symm)
    rcases Nat.lt_or_ge cr cs with hlt | hge
    · exact hcharge cr cs hlt (by omega) hcsf hvv
    · exact hcharge cs cr (by omega) (by omega) hcrf hvv.symm
  · obtain ⟨c, hcle, hcsel, hcf⟩ := exists_first_occurrence (grindSelSeq L hL e0 q g hb) T s
    have hv : chainVal (grindSelSeq L hL e0 q g hb) c T
        = chainVal (grindSelSeq L hL e0 q g hb) s T := by
      show T (grindSelSeq L hL e0 q g hb c T) = T (grindSelSeq L hL e0 q g hb s T)
      rw [hcsel]
    refine mem_eligible_hit_event L hL e0 q g hb _ (n * (q + 1)) c (by omega) T hcf ?_
    refine Finset.mem_union_left _ ?_
    rw [hv]
    exact hin

/-- **INSTANCE THREE: THE GRAPH REFINEMENT, AND WHAT IT GIVES.**  For a
graph-framed run -- no state-framing anywhere -- the unified charge against the
REACHABLE nodes gives `N (N + 1) / 2 / |Block|`, `N = n (q + 1)`: exactly
`GrindingQueryBound`'s all-pairs constant, NOT `GrindingLinearBound`'s linear one.
The refinement is real at the level of the SET being charged -- unreachable
answers are dropped -- and section 6 shows that for the chain-simulating prover
nothing is dropped at all. -/
theorem grinding_clash_graph_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (n : Nat)
    (hgf : ∀ T : OracleTable (boundedQueries L), GraphFramed L hL e0 q g hb (n * (q + 1)) T) :
    oracleProbability (boundedQueries L) (grindingClashEvent L hL e0 q g hb n)
      ≤ ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) := by
  have h := grinding_clash_le_eligible_sum L hL e0 q g hb n (reachTarget L hL e0 q g hb)
    (reach_target_reassign_invariant L hL e0 q g hb) (fun m => 1 + m)
    (fun m T => reach_target_card_le L hL e0 q g hb m T)
    (graph_clash_subset L hL e0 q g hb n hgf)
  rw [sum_succ_rat] at h
  refine le_trans h (le_of_eq ?_)
  push_cast
  ring

/-- (5) The frame digest of EVERY position of a state-framed run is a stage digest
already formed.  This is the body of `GrindingLinearBound.state_framed_of_probes`
without its run-level hypothesis. -/
theorem frame_digest_of_state_framed_probes (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hp : StateFramedProbes g)
    (m : Nat) (T : OracleTable (boundedQueries L)) :
    ∃ j, j ≤ m / (q + 1) ∧
      frameDigestAt L hL e0 q g hb m T = grindState L hL e0 q g hb j T := by
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

/-- (5) **EVERY STATE-FRAMED RUN IS GRAPH-FRAMED.**  The stage digests are nodes of
the absorb path, so `GraphFramed` holds of every strategy `GrindingLinearBound`
covers -- and of more, as section 6's chain simulator shows. -/
theorem graph_framed_of_state_framed_probes (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (hp : StateFramedProbes g)
    (N : Nat) (T : OracleTable (boundedQueries L)) : GraphFramed L hL e0 q g hb N T := by
  intro m _
  obtain ⟨j, hj, hje⟩ := frame_digest_of_state_framed_probes L hL e0 q g hb hp m T
  have hjm : j ≤ m := le_trans hj (Nat.div_le_self m (q + 1))
  have hreach : ReachIn L hL e0 q g hb m T j (grindState L hL e0 q g hb j T) := by
    refine state_reach_in L hL e0 q g hb m T j ?_
    intro i hi
    exact slot_pos_lt_of_div q m i (by omega)
  rw [hje]
  exact reach_in_mono_depth L hL e0 q g hb m T _ m j hjm hreach


/-! ## 6. THE CHAIN-SIMULATING PROVER -/

/-- (6) **THE ABSORB OF ANY STRATEGY FRAMES AT THE STAGE DIGEST**, written at a
position given by its slot rather than by `slotPos`. -/
theorem absorb_position_frame (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (m : Nat) (hm : m % (q + 1) = q)
    (T : OracleTable (boundedQueries L)) :
    frameDigestAt L hL e0 q g hb m T = grindState L hL e0 q g hb (m / (q + 1)) T := by
  show (grindQuery e0 q g (runAns L hL e0 q g hb m T) (challengesOf L hL T) m).1 = _
  unfold grindQuery
  rw [hm, if_neg (lt_irrefl q)]
  show stateOf e0 q (runAns L hL e0 q g hb m T) (m / (q + 1)) = _
  exact state_of_run_ans_le L hL e0 q g hb m (m / (q + 1))
    (fun j2 hj2 => slot_pos_lt_of_div q m j2 (le_of_eq hj2.symm)) T

/-- The probe index the simulator absorbs: the largest `i` below the scan bound
whose answer digest is one of the stage digests already formed, and the FALLBACK
-- the last probe -- when there is none. -/
noncomputable def simHitIndex (k : Nat) (h : Nat → Transcript.Digest)
    (pa : Nat → Nat → Block) (fallback : Nat) : Nat → Nat
  | 0 => fallback
  | i + 1 =>
      if (∃ j, j ≤ k ∧ blockDigest (pa k i) = h j) then i
      else simHitIndex k h pa fallback i

/-- **THE CHAIN SIMULATOR.**  At every stage it chains its probes: probe `0`
frames at the stage digest the run has reached, and probe `i + 1` frames at the
DIGEST OF PROBE `i`'S ANSWER -- a digest no absorb has made a state.  It then
absorbs the payload of the probe whose answer digest hit a stage digest already
formed, and the last probe's payload when none did.  This is the shape of the
prover `GrindingLinearBound` HONESTY (ii) names as the one its argument excludes.
NOTE: the absorb's payload choice is decorative for everything proved below --
the absorb frames at the STAGE digest with payload `le 8 idx`, so it repeats a
probe's byte string only when `idx = 0`; the simulator does not reproduce the
simulated chain's answers, and the tightness result uses only the frame chaining
of the probes. -/
noncomputable def chainSimulator (q : Nat) : GrindingStrategy where
  probe := fun k i h _ pa =>
    ((match i with
      | 0 => h k
      | i2 + 1 => blockDigest (pa k i2)), 1, Transcript.le 8 i)
  absorb := fun k h _ pa => (1, Transcript.le 8 (simHitIndex k h pa (q - 1) q))

theorem chain_simulator_bounded (L q : Nat) (hL : 69 ≤ L) :
    GrindingBounded L (chainSimulator q) := by
  constructor
  · intro _ i _ _ _
    show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · intro k h _ pa
    show 61 + (Transcript.le 8 (simHitIndex k h pa (q - 1) q)).length ≤ L
    rw [Transcript.le_length]
    omega

/-- (6) The simulator's FIRST probe of a stage frames at the stage digest. -/
theorem chain_simulator_probe_zero_frame (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hq : 1 ≤ q) (hb : GrindingBounded L (chainSimulator q)) (m : Nat)
    (hm : m % (q + 1) = 0) (T : OracleTable (boundedQueries L)) :
    frameDigestAt L hL e0 q (chainSimulator q) hb m T
      = grindState L hL e0 q (chainSimulator q) hb (m / (q + 1)) T := by
  show (grindQuery e0 q (chainSimulator q) (runAns L hL e0 q (chainSimulator q) hb m T)
    (challengesOf L hL T) m).1 = _
  unfold grindQuery
  rw [hm, if_pos (show 0 < q from hq)]
  show stateOf e0 q (runAns L hL e0 q (chainSimulator q) hb m T) (m / (q + 1)) = _
  exact state_of_run_ans_le L hL e0 q (chainSimulator q) hb m (m / (q + 1))
    (fun j2 hj2 => slot_pos_lt_of_div q m j2 (le_of_eq hj2.symm)) T

/-- (6) **THE PROBE CHAIN.**  The simulator's probe `i + 1` of a stage frames at
the digest of the PRECEDING POSITION'S ANSWER: consecutive probes are consecutive
edges of the digest graph, and a stage's `q` probes lay down a path of `q` edges
without absorbing anything. -/
theorem chain_simulator_probe_succ_frame (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L (chainSimulator q)) (m i : Nat)
    (hm : m % (q + 1) = i + 1) (hi : i + 1 < q) (T : OracleTable (boundedQueries L)) :
    frameDigestAt L hL e0 q (chainSimulator q) hb m T
      = answerDigestAt L hL e0 q (chainSimulator q) hb (m - 1) T := by
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, Nat.zero_mod] at hm
    exact absurd hm.symm (Nat.succ_ne_zero i)
  have hd : m / (q + 1) * (q + 1) + m % (q + 1) = m := Nat.div_add_mod' m (q + 1)
  rw [hm] at hd
  have hpos : slotPos q (m / (q + 1)) i = m - 1 := by
    simp only [slotPos]
    omega
  show (grindQuery e0 q (chainSimulator q) (runAns L hL e0 q (chainSimulator q) hb m T)
    (challengesOf L hL T) m).1 = _
  unfold grindQuery
  rw [hm, if_pos hi]
  show blockDigest (probeAnsOf q (runAns L hL e0 q (chainSimulator q) hb m T)
    (m / (q + 1)) i) = _
  show blockDigest (runAns L hL e0 q (chainSimulator q) hb m T
    (slotPos q (m / (q + 1)) i)) = _
  rw [hpos, run_ans_eq, if_pos (by omega : m - 1 < m)]
  rfl

/-- (6) Consecutive probes of the simulator are consecutive EDGES of the digest
graph: within one stage the `q` probes lay down a path of `q` edges, so the path
length cap `n` of the absorb path does not cap the probe graph's depth. -/
theorem chain_simulator_probe_graph_edge (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L (chainSimulator q)) (N m i : Nat)
    (hm : m % (q + 1) = i + 1) (hi : i + 1 < q) (hmN : m < N)
    (T : OracleTable (boundedQueries L)) :
    GraphEdge L hL e0 q (chainSimulator q) hb N T
      (answerDigestAt L hL e0 q (chainSimulator q) hb (m - 1) T)
      (answerDigestAt L hL e0 q (chainSimulator q) hb m T) :=
  ⟨m, hmN, chain_simulator_probe_succ_frame L hL e0 q hb m i hm hi T, rfl⟩

/-- (6) **THE SIMULATOR IS GRAPH-FRAMED.**  Every position of its run -- probe or
absorb -- frames at a node the run has already reached from `e0`, so the graph
instance of section 5 applies to it.  Strong induction on the position: an absorb
and a stage's first probe frame at a stage digest, a node of the absorb path, and
a later probe frames at the answer digest of the position just before it. -/
theorem chain_simulator_graph_framed (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L (chainSimulator q)) (N : Nat)
    (T : OracleTable (boundedQueries L)) :
    GraphFramed L hL e0 q (chainSimulator q) hb N T := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro hmN
      have hstate : ∀ j, j < m / (q + 1) → slotPos q j q < m :=
        fun j hj => slot_pos_lt_of_div q m j (by omega)
      have hreach : ReachIn L hL e0 q (chainSimulator q) hb m T (m / (q + 1))
          (grindState L hL e0 q (chainSimulator q) hb (m / (q + 1)) T) :=
        state_reach_in L hL e0 q (chainSimulator q) hb m T (m / (q + 1)) hstate
      have hdivm : m / (q + 1) ≤ m := Nat.div_le_self m (q + 1)
      by_cases hprobe : m % (q + 1) < q
      · cases hi : m % (q + 1) with
        | zero =>
            rw [chain_simulator_probe_zero_frame L hL e0 q (by omega) hb m hi T]
            exact reach_in_mono_depth L hL e0 q (chainSimulator q) hb m T _ m (m / (q + 1))
              hdivm hreach
        | succ i2 =>
            have hi2 : i2 + 1 < q := by omega
            have hm0 : 0 < m := by
              rcases Nat.eq_zero_or_pos m with h | h
              · rw [h, Nat.zero_mod] at hi
                exact absurd hi.symm (Nat.succ_ne_zero i2)
              · exact h
            rw [chain_simulator_probe_succ_frame L hL e0 q hb m i2 hi hi2 T]
            have hprev := ih (m - 1) (by omega) (by omega)
            have hprev2 := reach_in_mono_edges L hL e0 q (chainSimulator q) hb (m - 1) m
              (by omega) T (m - 1) _ hprev
            have hstep := reach_in_step L hL e0 q (chainSimulator q) hb m T (m - 1) (m - 1)
              (by omega) hprev2
            rwa [show m - 1 + 1 = m from by omega] at hstep
      · have hmod : m % (q + 1) < q + 1 := Nat.mod_lt m (Nat.succ_pos q)
        rw [absorb_position_frame L hL e0 q (chainSimulator q) hb m (by omega) T]
        exact reach_in_mono_depth L hL e0 q (chainSimulator q) hb m T _ m (m / (q + 1))
          hdivm hreach

/-- (6) **THE SIMULATOR IS NOT STATE-FRAMED.**  Its second probe frames at the
digest of its first probe's answer, which is no stage digest: the strategy class
of `GrindingLinearBound` does not contain it, while the graph-framed class of
section 5 does.  The separation is at the PREDICATE level and holds for every
`q`; at the run level the second probe only executes when `q ≥ 2`. -/
theorem chain_simulator_not_state_framed (q : Nat) : ¬ StateFramedProbes (chainSimulator q) := by
  intro hp
  obtain ⟨j, -, hje⟩ := hp 0 1 (fun _ => indexDigest 0)
    (fun _ _ => OuterChallenge.digestBlock (indexDigest 0))
    (fun _ _ => OuterChallenge.digestBlock (indexDigest 1))
  have heq : indexDigest 1 = indexDigest 0 := hje
  exact absurd (index_digest_injective 1 0 (by norm_num) (by norm_num) heq) (by decide)

/-- (6) **THE GRAPH REFINEMENT DROPS NOTHING AGAINST THE SIMULATOR.**  Every
answer of every earlier position is in the charged position's REACHABLE set: the
simulator's probes chain, so its whole query history is one connected piece of
graph hanging off `e0`. -/
theorem chain_simulator_every_earlier_answer_eligible (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (hb : GrindingBounded L (chainSimulator q)) (m j : Nat)
    (hj : j < m) (T : OracleTable (boundedQueries L)) :
    chainVal (grindSelSeq L hL e0 q (chainSimulator q) hb) j T
      ∈ reachTarget L hL e0 q (chainSimulator q) hb m T := by
  refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
    ⟨j, Finset.mem_range.mpr hj, rfl⟩, ?_⟩)
  have hreach := graph_framed_answer_reach L hL e0 q (chainSimulator q) hb m T
    (chain_simulator_graph_framed L hL e0 q hb m T) j hj
  have hreach2 := reach_in_mono_edges L hL e0 q (chainSimulator q) hb (j + 1) m
    (by omega) T (j + 1) _ hreach
  exact reach_in_mono_depth L hL e0 q (chainSimulator q) hb m T _ m (j + 1) (by omega) hreach2

/-- (6) **SO THE GRAPH-REFINED TARGET IS THE ALL-PAIRS TARGET, POSITION BY
POSITION.**  For the chain simulator `reachTarget m T` is literally
`chainTarget m T`: the filter that the graph refinement adds removes nothing, and
the per-position charge the scheme supplies at position `m` is `1 + m`, not
`m / (q + 1) + 1`. -/
theorem chain_simulator_reach_target_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (hb : GrindingBounded L (chainSimulator q)) (m : Nat)
    (T : OracleTable (boundedQueries L)) :
    reachTarget L hL e0 q (chainSimulator q) hb m T
      = chainTarget (grindSelSeq L hL e0 q (chainSimulator q) hb) (avoidBase e0) m T := by
  refine congrArg (fun z => avoidBase e0 ∪ z) (Finset.filter_true_of_mem ?_)
  intro b hb2
  obtain ⟨j, hjr, hjb⟩ := Finset.mem_image.mp hb2
  have hj : j < m := Finset.mem_range.mp hjr
  have hmem := chain_simulator_every_earlier_answer_eligible L hL e0 q hb m j hj T
  rw [reachTarget] at hmem
  rcases Finset.mem_union.mp hmem with - | hfil
  · have hreach := graph_framed_answer_reach L hL e0 q (chainSimulator q) hb m T
      (chain_simulator_graph_framed L hL e0 q hb m T) j hj
    have hreach2 := reach_in_mono_edges L hL e0 q (chainSimulator q) hb (j + 1) m
      (by omega) T (j + 1) _ hreach
    have hreach3 := reach_in_mono_depth L hL e0 q (chainSimulator q) hb m T _ m (j + 1)
      (by omega) hreach2
    rw [← hjb]
    exact hreach3
  · rw [← hjb]
    exact (Finset.mem_filter.mp hfil).2

/-- (6) **THE CHARGE THE SCHEME SUPPLIES CANNOT REACH THE LINEAR CONSTANT.**  For
`q ≥ 1` and `n ≥ 1` the linear constant of `GrindingLinearBound` is STRICTLY below
the all-pairs constant that the graph charge sums to, so no rearrangement of the
per-position charges of section 5 produces `GrindingLinearBound`'s bound for the
simulator: the two constants are not equal, and the charge is the larger one. -/
theorem linear_constant_lt_all_pairs_constant (q n : Nat) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (((q + 1) * (n * (n + 1)) : Nat) : ℚ) / 2
      < ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2 := by
  have h2 : n * 2 ≤ n * (q + 1) := Nat.mul_le_mul (le_refl n) (by omega)
  have h4 : n + 1 ≤ n * (q + 1) := by omega
  have hpos : 0 < n * (q + 1) := by omega
  have hA : (q + 1) * (n * (n + 1)) = (n * (q + 1)) * (n + 1) := by ring
  have hB : (n * (q + 1)) * (n * (q + 1) + 1)
      = (n * (q + 1)) * (n * (q + 1)) + n * (q + 1) := by ring
  have hC : (n * (q + 1)) * (n + 1) ≤ (n * (q + 1)) * (n * (q + 1)) :=
    Nat.mul_le_mul (le_refl _) h4
  have hnat : (q + 1) * (n * (n + 1)) < (n * (q + 1)) * (n * (q + 1) + 1) := by omega
  have hcast : (((q + 1) * (n * (n + 1)) : Nat) : ℚ)
      < (((n * (q + 1)) * (n * (q + 1) + 1) : Nat) : ℚ) := by exact_mod_cast hnat
  push_cast at hcast ⊢
  linarith


/-! ## 7. THE CLOSED INSTANCES AND THE CONSTANT TABLE -/

/-- (7) `GrindingQueryBound`'s grinder is graph-framed: it is state-framed, and
every state-framed run is. -/
theorem probe_grinder_graph_framed (L : Nat) (hL : 93 ≤ L) (e0 : Transcript.Digest) (q N : Nat)
    (T : OracleTable (boundedQueries L)) :
    GraphFramed L (Nat.le_trans (by norm_num) hL) e0 q probeGrinder
      (probe_grinder_bounded L hL) N T :=
  graph_framed_of_state_framed_probes L (Nat.le_trans (by norm_num) hL) e0 q probeGrinder
    (probe_grinder_bounded L hL) probe_grinder_state_framed N T

/-- (7) **THE GRAPH BOUND FOR THE CHAIN SIMULATOR.**  A closed instance of
section 5's headline at a strategy `GrindingLinearBound` does NOT cover
(`chain_simulator_not_state_framed`).  The constant is the all-pairs one; this is
the module's honest answer to "can the graph refinement beat it" -- for this
prover, no. -/
theorem chain_simulator_graph_clash_le (L : Nat) (hL : 69 ≤ L) (e0 : Transcript.Digest)
    (q n : Nat) :
    oracleProbability (boundedQueries L)
        (grindingClashEvent L (Nat.le_trans (by norm_num) hL) e0 q (chainSimulator q)
          (chain_simulator_bounded L q hL) n)
      ≤ ((n * (q + 1) : Nat) : ℚ) * (((n * (q + 1) : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) :=
  grinding_clash_graph_le L (Nat.le_trans (by norm_num) hL) e0 q (chainSimulator q)
    (chain_simulator_bounded L q hL) n
    (fun T => chain_simulator_graph_framed L (Nat.le_trans (by norm_num) hL) e0 q
      (chain_simulator_bounded L q hL) (n * (q + 1)) T)

/-- (7) **THE CHAIN SIMULATOR'S CLASH EVENT IS NOT EMPTY**, at the constant
table. -/
theorem constant_table_chain_simulator_clashes (L : Nat) (hL : 69 ≤ L) (q n : Nat) (hn : 2 ≤ n) :
    constantTable L ∈ grindingClashEvent L (Nat.le_trans (by norm_num) hL)
      OuterInitial.zeroDigest q (chainSimulator q) (chain_simulator_bounded L q hL) n :=
  constant_table_grinding_clashes L (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q
    (chainSimulator q) (chain_simulator_bounded L q hL) n hn

/-- (7) **AND NEITHER IS THE GRAPH INSTANCE'S ELIGIBLE-HIT EVENT.**  At the
constant table position `0` is fresh and its answer is the base block, which is in
every position's reachable target. -/
theorem constant_table_reach_target_hit (L : Nat) (hL : 64 ≤ L) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (N : Nat) (hN : 1 ≤ N) :
    constantTable L ∈ eligibleHitEvent L hL OuterInitial.zeroDigest q g hb
      (reachTarget L hL OuterInitial.zeroDigest q g hb) N := by
  refine mem_eligible_hit_event L hL OuterInitial.zeroDigest q g hb _ N 0 (by omega) _ ?_ ?_
  · rw [mem_fresh_at]
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · refine Finset.mem_union_left _ ?_
    rw [avoidBase, Finset.mem_singleton]
    rfl

/-- (7) **THE CLOSED FORM AT THE ENVELOPE'S `22 + 5 * 13 = 87` STAGES**, for the
chain simulator with a million probes per stage: the all-pairs numeral of
`GrindingQueryBound`, which the graph refinement does not improve. -/
theorem chain_simulator_clash_at_eighty_seven_many_probes (L : Nat) (hL : 69 ≤ L)
    (e0 : Transcript.Digest) :
    oracleProbability (boundedQueries L)
        (grindingClashEvent L (Nat.le_trans (by norm_num) hL) e0 1048576
          (chainSimulator 1048576) (chain_simulator_bounded L 1048576 hL) 87)
      ≤ (4161109737606900 : ℚ) / (Fintype.card Block : ℚ) := by
  have h := chain_simulator_graph_clash_le L hL e0 1048576 87
  rwa [show ((87 * (1048576 + 1) : Nat) : ℚ) * (((87 * (1048576 + 1) : Nat) : ℚ) + 1) / 2
      = (4161109737606900 : ℚ) from by norm_num] at h

/-- (7) **AND IT IS BELOW `2 ^ (-200)`.**  `Fintype.card Block` is never evaluated
as a numeral: it is written as `2 ^ 256` through the adopted
`RandomOracleSqueezes.block_card`. -/
theorem chain_simulator_clash_at_eighty_seven_many_probes_tiny (L : Nat) (hL : 69 ≤ L)
    (e0 : Transcript.Digest) :
    oracleProbability (boundedQueries L)
        (grindingClashEvent L (Nat.le_trans (by norm_num) hL) e0 1048576
          (chainSimulator 1048576) (chain_simulator_bounded L 1048576 hL) 87)
      ≤ 1 / (2 : ℚ) ^ 200 := by
  refine le_trans (chain_simulator_clash_at_eighty_seven_many_probes L hL e0) ?_
  have hn : (4161109737606900 : Nat) * 2 ^ 200 ≤ Fintype.card Block := by
    rw [block_card_two_pow]
    calc (4161109737606900 : Nat) * 2 ^ 200 ≤ 2 ^ 56 * 2 ^ 200 :=
          Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ 256 := by rw [← pow_add]
  have hq : (4161109737606900 : ℚ) * (2 : ℚ) ^ 200 ≤ (Fintype.card Block : ℚ) := by
    exact_mod_cast hn
  rw [div_le_div_iff block_card_cast_pos (by positivity), one_mul]
  exact hq

end Audit.Wire3.GrindingGraphBound
