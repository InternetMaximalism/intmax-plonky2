import Audit.Wire3.ReducedIndexLanes
import Audit.Wire3.TwoStageConditionalCount

/-!
# THE EXPLICIT ENGINE'S OWN INDEX BAD EVENT, FOR THE REDUCED ADAPTIVE PROVER

## WHAT THIS MODULE PROVES, AND WHAT IT DOES NOT -- READ THIS FIRST

The adopted `ReducedIndexLanes` (RIL) bounds, for the reduced-history adaptive
prover with a history-dependent used-claims choice `U`, the mass of

  `ReducedFullTransport.fullBadEvent  UNION  RIL.indexBadEvent`

by `ChallengeUnionBound.combinedBound d q d constraints + 2 * tauTerm indexBits`
plus the chain's own clash term at `22 + 5 d + 8` stages.  Its HONESTY (iii) says
in as many words that the COMMITTED cell family in that index summand is a
PARAMETER `committed : List Element -> List Element`, not a derivation, and lists
exactly what a transfer to the EXPLICIT ENGINE'S OWN index bad event would need:

> a prefix-congruence lemma between the `extendedShape` chain and the
> `strategyOfReduced` chain (equal stage digests up to `22 + 5 d`), the adopted
> `OuterLaneTransport.strategic_run_log_draw_is_log_triple` / `_gate_` at
> `realizedProof`, the adopted
> `TwoStageConditionalCount.row_point_is_outer_draw_function` [...] and the
> standing assumption [...] that the extracted columns are FIXED DATA.
> NO THEOREM BELOW PERFORMS THAT TRANSFER.

THIS MODULE PERFORMS THAT TRANSFER.  `committed_is_history_function` proves that
at the realized proof of the reduced adaptive prover the engine's committed
family IS `committedOf cols cellIndex` applied to the run's own reduced history,
at every table; `engine_index_bad_event_eq` then identifies the EXPLICIT ENGINE'S
OWN index bad event -- the adopted `SoundnessAssembly.indexBadEvent` at the run's
supplied and committed cells, evaluated at the adopted
`SoundnessAssembly.actualIndexDraw` -- with RIL's `indexBadEvent` at
`committed := committedOf cols cellIndex`, SET FOR SET.  The headline
`reduced_engine_index_bad_draw_probability_le` is then RIL's constant at the
engine's own event, and
`reduced_engine_index_bad_draw_probability_le_all_cells` pays
`5 * (2 * tauTerm indexBits)` for all five bound cells under ONE clash term.

## WHAT IS PROVED

1. TWO STRATEGIES THAT AGREE BELOW A STAGE (section 1).  The adopted
   `StrategyChainBound.strat_hist_congr` is a SAME-STRATEGY / TWO-TABLES
   statement.  `strat_hist_of_agree` is the TWO-STRATEGIES / SAME-TABLE version
   RIL's HONESTY (iii) asks for: two strategies agreeing on every stage `< n`
   have the same history, the same stage digests, the same challenge queries and
   the same stage triples at every stage `<= n`.
2. THE EXTENDED CHAIN BELOW THE CLAIM FRAMES (section 2).  `extendedShape` and
   `strategyOfReduced` agree on stages `< 22 + 5 d` by the adopted
   `ReducedIndexLanes.extended_shape_round`, so every round stage
   `roundStage r <= 22 + 5 d` carries the same log and gate triples on both
   chains.  This is the prefix congruence.
3. THE REALIZED HISTORY, ENTRY BY ENTRY (sections 3 and 4).
   `outer_history_get_log` / `_gate` read the adopted
   `OuterLaneTransport.outerHistory` off its own recursion: round `r`'s log
   reduction is entry `2 r`, its gate reduction entry `2 r + 1` -- the even/odd
   bookkeeping the transfer needs.  `rowFromHistory` is the row point as a
   function of that list alone, `cellOffset` being `0` for the three log cells
   and `1` for the two gate cells.
4. THE REALIZED RUN RECORD (section 5).  The adopted
   `OuterLaneTransport.realizedProof` does NOT set `used`; the engine's index bad
   event reads exactly that field, so `realizedUsedProof` writes the realized
   claims into it and `realizedRun` is the run record of the reduced adaptive
   prover at one table.  Its statement, its messages, their number and the
   adopted length budget are all discharged, not assumed.
   `run_log_draw_is_history_entry` / `_gate_` compose the adopted
   `strategic_run_log_draw_is_log_triple` with section 2 and section 3: the run's
   own `JointChallengeSpace.Draw.outerLog r` coordinate IS entry `2 r` of the
   extended chain's realized history.
5. THE COMMITTED CELLS (section 6).  `lift_cell_row_is_row_from_history` proves
   the engine's row point at the realized proof equals `rowFromHistory`, entry by
   entry, from the adopted
   `TwoStageConditionalCount.row_point_is_outer_draw_function` and section 5;
   `committed_is_history_function` applies the extracted columns to it.
6. THE INDEX DIGEST AND THE INDEX DRAW (section 7).
   `extended_rounds_state_is_run_digest` discharges the chain-model hypothesis
   `hst` of the adopted `ReducedIndexLanes.extended_stage_is_index_digest` AT THE
   SNAPSHOT THE ADOPTED `SoundnessAssembly.actualIndexDraw` NAMES -- the adopted
   `InstalledRoundCommit.concreteFinal` of the run's own messages -- rather than
   at the chain's own placeholder state, using the adopted
   `ConcreteChainThreading.chain_model_is_the_run_chain` at `r = degreeBits`.
   `run_index_draw_is_index_read` is then the adopted
   `ReducedIndexLanes.index_read_is_actual_index_draw` read backwards: the
   engine's own index draw at the realized proof IS the extended chain's index
   column.
7. THE EVENT IDENTIFICATION AND THE HEADLINE (section 8).
   `guarded_is_assembly_index_bad_event` shows the adopted
   `IndexLanesOracle.guardedIndexBadEvent` IS the adopted
   `SoundnessAssembly.indexBadEvent`, branch for branch;
   `engine_index_target_is_reduced_target` composes it with the supplied-cell
   projection and section 6; `engine_index_bad_event_eq` is the resulting Finset
   equality and `reduced_engine_index_bad_draw_probability_le` the headline.
8. ALL FIVE BOUND CELLS (section 9).  `full_bad_no_clash_mass_le` isolates the
   outer, tau and alpha masses at the chain's full conditioning stage so that
   five index summands can be added under ONE complement term, giving
   `combinedBound + 5 * (2 * tauTerm indexBits) + one clash term`.
9. THE GUARD, NON-VACUITY AND THE CLOSED INSTANCE (sections 10 and 11).
   `engine_index_bad_event_at_honest_cells` shows the engine's event is EMPTY
   when the columns open to the supplied cells, so nothing below bounds the whole
   table space by fiat; `envelope_config_hypotheses` discharges the two new
   configuration equations at a concrete `envelopeConfig`;
   `engine_index_bound_at_thirteen` and its five-cell twin are the closed
   instances, both strictly below `1`.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  The fresh-query
lemma everything rests on is the DEFINING property of a random table and is
false, as a theorem, for any fixed hash.  Replacing the deployed permutation by a
table drawn from this law is an assumption with no proof anywhere in this tree.

(ii) THE PROVER IS TRANSCRIPT-RESTRICTED AND REDUCED-HISTORY; GRINDING AND
RAW-BLOCK STRATEGIES ARE EXCLUDED.  Exactly the adopted
`ReducedIndexLanes` HONESTY (ii) class, unchanged and not widened: the round
messages are functions of the reduced round-challenge history alone, the used
claims a function of the reduced history of all `d` rounds, and the twenty-two
relation-prefix frames are the adopted `CommitmentOrder.gateChallengeFrames`, so
the commitments are fixed before the chain.  A random-oracle-model prover that
hashes candidate payloads itself and keeps a colliding one -- GRINDING -- is NOT
covered, and raw-block-reading strategies remain open.

(iii) THE ENGINE IS EVALUATED AT THE REALIZED PROOF, AND THE EXTRACTED COLUMNS
ARE FIXED DATA.  `realizedRun` is a `Verifier.Proof` carrying the messages the
strategy produced at the table and the claims the used-claims choice picked at
the run's own reduced history.  NOTHING BELOW SAYS THAT RECORD IS ACCEPTED, or
that an accepted proof exists; `Integrated.verify` is never invoked.  The
extracted columns `cols`, like the adopted `g` and `coeffsOf`, are UNIVERSALLY
QUANTIFIED FIXED DATA -- THREE ASSUMPTIONS, NOT ONE: `cols` and `coeffsOf` are
functions of the extracted tables alone, and "fixed data" for them is the adopted
open `CommitmentOrder.CommittedTables` join (the extractor's round-one-opening
argument must drop out); `g` additionally reads the block-0 gate alpha, so for the
ENGINE'S OWN `g` the fixed-`g` tau summand is a SLICE AT ONE ALPHA and its diagonal
over alpha is not proved in this tree -- and are NOT identified with the deployed
committed tables
anywhere: that identification is the adopted `CommitmentOrder` reading together
with that module's own open `CommittedTables` extraction join, which this module
INHERITS unchanged and does not strengthen.  What section 6 removes is the
MODELLING step -- RIL's `committed` parameter -- not that join.  `RowPointFixed`
is NOT assumed: the committed family genuinely moves with the table, through the
history, and the diagonal count of the adopted RIL section 4 is what pays for it.

(iv) THE LANES COVERED ARE THE OUTER SUMCHECK LANES, THE TWO BLOCK-`0` GATE LANES
AND THE INDEX LANES.  THE WHIR FOLDING TRANSCRIPT AND THE MERKLE OPENINGS ARE
EXCLUDED A FORTIORI: they are not in the adopted `combinedBound` at all, and
proximity / list decoding, the query-repetition profile and Merkle collision
resistance contribute nothing here.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The constant covers the
outer sumcheck round-agreement events, the gate tau multilinear zero check, the
gate alpha zero check and the bound cells' index-point agreement.  It EXCLUDES
the entire WHIR/Merkle contribution, which is the DOMINANT term.  The deployed
design point is around a hundred bits.  Quoting the numbers of section 11 as the
wire-v3 soundness error would be wrong by roughly seventy bits.  The meaning of
the per-round bad sets remains the adopted `ConditionalSoundness` one --
GOOD-DRAW-CONDITIONAL, with that module's assumption list untouched -- and the
adopted `SoundnessAssembly.explicit_good_draw_assembly` conclusion is likewise a
CONDITIONAL shape; nothing here instantiates either, and ACCEPTANCE IS NEVER
EXHIBITED.

(vi) NO ADAPTIVE FIAT--SHAMIR SOUNDNESS IS CLAIMED.  What is bounded is the mass
of one named event defined directly on the oracle table.  The Fiat--Shamir half
-- that the run's encoding draw is `JointChallengeSpace.jointProbability`-
distributed, and that the index draw is
`IndexPointZeroCheck.indexProbability`-distributed -- remains exactly as
unformalized as the adopted `JointChallengeSpace.DrawEncodesRun` and
`IndexPointZeroCheck` headers say.  `engineIndexBadEvent` is this module's OWN
table-level event; it is NOT the adopted `RandomOracleSqueezes.runDrawEvent`, and
no theorem below identifies the two.  What IS identified is the SET, the DIGEST
and the DRAW.

(vii) RESIDUES.  R1b of the adopted residue list -- the identification of the
extracted columns with the deployed committed tables -- is untouched and remains
open.  The adopted `ReducedIndexLanes` HONESTY (vii) chain-model residue is
DISCHARGED for the realized run by `extended_rounds_state_is_run_digest`, which
proves the post-rounds snapshot IS the chain's stage-`22 + 5 d` digest; what is
still nobody's theorem is any statement that the deployed transcript state at that
point is that snapshot.  The clash term remains the adopted
`StrategyChainBound.strategy_chain_clash_probability_le` at `22 + 5 d + 8`
stages, an event about THIS chain's stage digests.  The hypothesis `hdeg :
c.degreeBits = d` ties the configuration's round count to the chain's; it is
discharged at `envelopeConfig` and at the closed instances, never left dangling.
The prefix-payload hypothesis `hpre` of section 11 is the adopted
`ReducedIndexLanes.full_index_bound_at_thirteen` one, verbatim and no weaker.

(viii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's
OWN definition `engineIndexBadEvent` and, through the generic lemmas
`Finset.mem_univ` / the adopted `OuterLaneTransport.univ_filter_inter_subset`, in
a few proofs; no tactic or term below ever puts `Finset.univ` on `Element`, on
`OuterChallenge.DigestTriple` or on `InstalledIndexSampler.IndexSpace` in a
position that can be reduced, and no `Nat` arithmetic tactic below is ever shown a
`Fintype.card` of any of them.  `Fintype.card Block` enters only through the
adopted named lemmas `ReducedIndexLanes.index_birthday_term_le_two_pow_neg` and
`block_card_ge_index_birthday_scale`, and is never evaluated.  `open Classical in`
is used for the declarations whose statements mention `Finset` membership over the
index space or over the table space, exactly as the adopted `ReducedIndexLanes`
does and for the same reason.  Memberships over the table space are manipulated
through `Finset` equalities and the adopted generic helpers.  The list lemmas
`get_append_left`, `get_append_at` and `get_append_at_succ` are proved here by
induction rather than imported, in the style of the adopted
`OuterLaneTransport.take_length_append`.
-/

namespace Audit.Wire3.ReducedEngineIndex

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.IndexLanesOracle
open Audit.Wire3.ReducedIndexLanes

/-! ## 1. TWO STRATEGIES THAT AGREE BELOW A STAGE -/

def AgreeBelow (s1 s2 : Strategy) (n : Nat) : Prop :=
  ∀ k, k < n → ∀ (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block), s1 k h ch = s2 k h ch

theorem strat_hist_of_agree (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (s1 s2 : Strategy) (hb1 : StrategyBounded L s1) (hb2 : StrategyBounded L s2)
    (n : Nat) (hag : AgreeBelow s1 s2 n) (T : OracleTable (boundedQueries L)) :
    ∀ j, j ≤ n → stratHist L hL e0 s1 hb1 j T = stratHist L hL e0 s2 hb2 j T := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      have hH := ih (by omega)
      funext i
      rw [strat_hist_succ, strat_hist_succ, hH]
      by_cases hi : i ≤ m
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        refine congrArg blockDigest (congrArg T (Subtype.ext ?_))
        show Transcript.frame (stratHist L hL e0 s2 hb2 m T m)
            (s1 m (stratHist L hL e0 s2 hb2 m T)
              (fun i2 cc => challengeAt L hL T (stratHist L hL e0 s2 hb2 m T i2) cc)).1
            (s1 m (stratHist L hL e0 s2 hb2 m T)
              (fun i2 cc => challengeAt L hL T (stratHist L hL e0 s2 hb2 m T i2) cc)).2
          = Transcript.frame (stratHist L hL e0 s2 hb2 m T m)
            (s2 m (stratHist L hL e0 s2 hb2 m T)
              (fun i2 cc => challengeAt L hL T (stratHist L hL e0 s2 hb2 m T i2) cc)).1
            (s2 m (stratHist L hL e0 s2 hb2 m T)
              (fun i2 cc => challengeAt L hL T (stratHist L hL e0 s2 hb2 m T i2) cc)).2
        rw [hag m hmn]

theorem strategy_frame_state_of_agree (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (s1 s2 : Strategy) (hb1 : StrategyBounded L s1) (hb2 : StrategyBounded L s2)
    (n : Nat) (hag : AgreeBelow s1 s2 n) (T : OracleTable (boundedQueries L))
    (j : Nat) (hj : j ≤ n) :
    strategyFrameState L hL e0 s1 hb1 j T = strategyFrameState L hL e0 s2 hb2 j T := by
  show stratHist L hL e0 s1 hb1 j T j = stratHist L hL e0 s2 hb2 j T j
  rw [strat_hist_of_agree L hL e0 s1 s2 hb1 hb2 n hag T j hj]

theorem challenge_sel_of_agree (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (s1 s2 : Strategy) (hb1 : StrategyBounded L s1) (hb2 : StrategyBounded L s2)
    (n : Nat) (hag : AgreeBelow s1 s2 n) (T : OracleTable (boundedQueries L))
    (j cnt : Nat) (hj : j ≤ n) :
    challengeSel L hL e0 s1 hb1 j cnt T = challengeSel L hL e0 s2 hb2 j cnt T := by
  apply Subtype.ext
  show Transcript.challengeInput (strategyFrameState L hL e0 s1 hb1 j T) cnt
    = Transcript.challengeInput (strategyFrameState L hL e0 s2 hb2 j T) cnt
  rw [strategy_frame_state_of_agree L hL e0 s1 s2 hb1 hb2 n hag T j hj]

theorem stage_triple_of_agree (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (s1 s2 : Strategy) (hb1 : StrategyBounded L s1) (hb2 : StrategyBounded L s2)
    (n : Nat) (hag : AgreeBelow s1 s2 n) (T : OracleTable (boundedQueries L))
    (j base : Nat) (hj : j ≤ n) :
    stageTriple L hL e0 s1 hb1 j base T = stageTriple L hL e0 s2 hb2 j base T := by
  rw [stageTriple, stageTriple,
    challenge_sel_of_agree L hL e0 s1 s2 hb1 hb2 n hag T j base hj,
    challenge_sel_of_agree L hL e0 s1 s2 hb1 hb2 n hag T j (base + 1) hj,
    challenge_sel_of_agree L hL e0 s1 s2 hb1 hb2 n hag T j (base + 2) hj]

/-! ## 2. THE EXTENDED CHAIN AGREES WITH THE REDUCED CHAIN BELOW THE CLAIM FRAMES -/

theorem extended_agrees_below (c : Verifier.Config) (s : Verifier.Statement)
    (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat) :
    AgreeBelow (extendedShape c s R U d) (strategyOfReduced c s R) (22 + 5 * d) :=
  fun k hk h ch => extended_shape_round c s R U d k hk h ch

theorem extended_state_eq_reduced (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) (j : Nat) (hj : j ≤ 22 + 5 * d) :
    strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE j T
      = strategyFrameState L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hbR j T :=
  strategy_frame_state_of_agree L hL OuterInitial.zeroDigest _ _ hbE hbR (22 + 5 * d)
    (extended_agrees_below c s R U d) T j hj

theorem extended_log_triple_eq (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) (r : Nat) (hr : r < d) :
    logTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE r T
      = logTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hbR r T :=
  stage_triple_of_agree L hL OuterInitial.zeroDigest _ _ hbE hbR (22 + 5 * d)
    (extended_agrees_below c s R U d) T (roundStage r) 0 (by rw [roundStage]; omega)

theorem extended_gate_triple_eq (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) (r : Nat) (hr : r < d) :
    gateTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE r T
      = gateTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hbR r T :=
  stage_triple_of_agree L hL OuterInitial.zeroDigest _ _ hbE hbR (22 + 5 * d)
    (extended_agrees_below c s R U d) T (roundStage r) 3 (by rw [roundStage]; omega)

/-! ## 3. THE ENTRIES OF THE REALIZED HISTORY -/

theorem get_append_left (ys : List Element) :
    ∀ (xs : List Element) (k : Nat), k < xs.length → (xs ++ ys).get? k = xs.get? k := by
  intro xs
  induction xs with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons x xs2 ih =>
      intro k hk
      cases k with
      | zero => rfl
      | succ k2 =>
          have h2 : k2 < xs2.length := by
            have h3 := hk
            rw [List.length_cons] at h3
            omega
          exact ih k2 h2

theorem get_append_at (ys : List Element) :
    ∀ xs : List Element, (xs ++ ys).get? xs.length = ys.get? 0 := by
  intro xs
  induction xs with
  | nil => rfl
  | cons _x _xs2 ih => exact ih

theorem get_append_at_succ (ys : List Element) :
    ∀ xs : List Element, (xs ++ ys).get? (xs.length + 1) = ys.get? 1 := by
  intro xs
  induction xs with
  | nil => rfl
  | cons _x _xs2 ih => exact ih

theorem outer_history_get_log (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L)) :
    ∀ (n k : Nat), k < n →
      (outerHistory L hL e0 strat hb T n).get? (2 * k)
        = some (OuterChallenge.reduceTriple (logTriple L hL e0 strat hb k T)) := by
  intro n
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
      intro k hk
      rw [outer_history_succ]
      by_cases hkm : k < m
      · rw [get_append_left _ _ (2 * k)
          (by rw [outer_history_length]; omega)]
        exact ih k hkm
      · have hke : k = m := by omega
        subst hke
        rw [show 2 * k = (outerHistory L hL e0 strat hb T k).length from
            (by rw [outer_history_length]),
          get_append_at]
        rfl

theorem outer_history_get_gate (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (T : OracleTable (boundedQueries L)) :
    ∀ (n k : Nat), k < n →
      (outerHistory L hL e0 strat hb T n).get? (2 * k + 1)
        = some (OuterChallenge.reduceTriple (gateTriple L hL e0 strat hb k T)) := by
  intro n
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
      intro k hk
      rw [outer_history_succ]
      by_cases hkm : k < m
      · rw [get_append_left _ _ (2 * k + 1)
          (by rw [outer_history_length]; omega)]
        exact ih k hkm
      · have hke : k = m := by omega
        subst hke
        rw [show 2 * k + 1 = (outerHistory L hL e0 strat hb T k).length + 1 from
            (by rw [outer_history_length]),
          get_append_at_succ]
        rfl

/-! ## 4. THE ROW POINT READ OFF THE HISTORY -/

def cellOffset : Fin 5 → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 1

def rowFromHistory (cellIndex : Fin 5) (xs : List Element) : List Element :=
  (List.range (xs.length / 2)).map (fun r => (xs.get? (2 * r + cellOffset cellIndex)).getD 0)

theorem row_from_history_length (cellIndex : Fin 5) (xs : List Element) :
    (rowFromHistory cellIndex xs).length = xs.length / 2 := by
  rw [rowFromHistory, List.length_map, List.length_range]

theorem row_from_history_get (cellIndex : Fin 5) (xs : List Element) (k : Nat)
    (hk : k < xs.length / 2) :
    (rowFromHistory cellIndex xs).get? k
      = some ((xs.get? (2 * k + cellOffset cellIndex)).getD 0) := by
  rw [rowFromHistory, List.get?_eq_getElem?, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem row_from_history_get_none (cellIndex : Fin 5) (xs : List Element) (k : Nat)
    (hk : xs.length / 2 ≤ k) : (rowFromHistory cellIndex xs).get? k = none := by
  rw [List.get?_eq_none]
  rw [row_from_history_length]
  exact hk

/-! ## 5. THE REALIZED RUN OF THE REDUCED ADAPTIVE PROVER -/

/-- The adopted `OuterLaneTransport.realizedProof` with the used claims the
prover really opened written into the `used` field.  The adopted witness does not
set `used`, and the explicit engine's index bad event reads exactly that field. -/
def realizedUsedProof (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (u : Verifier.UsedClaims) : Verifier.Proof :=
  { realizedProof s ms with used := u }

theorem realized_used_proof_statement (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) :
    Verifier.statement (realizedUsedProof s ms u) = s := rfl

theorem realized_used_proof_messages (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) :
    roundMessages (realizedUsedProof s ms u) = ms := realized_proof_messages s ms

theorem realized_used_proof_used (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) :
    (realizedUsedProof s ms u).used = u := rfl

/-- **THE RUN RECORD OF THE REDUCED ADAPTIVE PROVER AT ONE TABLE**: the messages
the reduced round-message choice produced and the claims the used-claims choice
picked at the run's own reduced history. -/
def realizedRun (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) : Verifier.Proof :=
  realizedUsedProof s (realizedMessages L hL c s (reducedRoundMessage R) hbR c.degreeBits T)
    (realizedClaims L hL c s R U d hbE T)

theorem realized_run_statement (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) :
    Verifier.statement (realizedRun L hL c s R U d hbE hbR T) = s := rfl

theorem realized_run_messages (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) :
    roundMessages (realizedRun L hL c s R U d hbE hbR T)
      = realizedMessages L hL c s (reducedRoundMessage R) hbR c.degreeBits T :=
  realized_used_proof_messages _ _ _

theorem realized_run_used (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) :
    (realizedRun L hL c s R U d hbE hbR T).used = realizedClaims L hL c s R U d hbE T := rfl

theorem realized_run_messages_length (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) :
    (roundMessages (realizedRun L hL c s R U d hbE hbR T)).length = c.degreeBits := by
  rw [realized_run_messages, realized_messages_length]

theorem realized_run_length_budget (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) :
    ∀ k, 61 + (prefixRoundShape c
        (Verifier.statement (realizedRun L hL c s R U d hbE hbR T))
        (roundMessages (realizedRun L hL c s R U d hbE hbR T)) k).2.length ≤ L := by
  rw [realized_run_statement, realized_run_messages]
  exact strategic_hlen_of_bounded L hL c s (reducedRoundMessage R) hbR c.degreeBits T

/-! ### 5.1 The run's outer-draw coordinates are the realized history's entries -/

theorem run_log_draw_is_history_entry (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) (hdeg : c.degreeBits = d)
    (r : Nat) (hr : r < c.degreeBits) :
    OuterChallenge.reduceTriple (InstalledRoundCommit.actualDigestDraw
        (hashOf (boundedQueries L) T) c (realizedRun L hL c s R U d hbE hbR T)
        (JointChallengeSpace.Draw.outerLog ⟨r, hr⟩))
      = ((outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d).get?
          (2 * r)).getD 0 := by
  have h1 := strategic_run_log_draw_is_log_triple L hL c s (reducedRoundMessage R) hbR
    (reduced_round_causal R) (realizedRun L hL c s R U d hbE hbR T) T
    (realized_run_statement L hL c s R U d hbE hbR T)
    (realized_run_messages L hL c s R U d hbE hbR T)
    (realized_run_length_budget L hL c s R U d hbE hbR T)
    (realized_run_messages_length L hL c s R U d hbE hbR T) ⟨r, hr⟩
  have h2 : logTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hbR r T
      = logTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE r T :=
    (extended_log_triple_eq L hL c s R U d hbE hbR T r (by omega)).symm
  rw [h1.trans h2, outer_history_get_log L hL OuterInitial.zeroDigest
    (extendedShape c s R U d) hbE T d r (by omega)]
  rfl

theorem run_gate_draw_is_history_entry (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (T : OracleTable (boundedQueries L)) (hdeg : c.degreeBits = d)
    (r : Nat) (hr : r < c.degreeBits) :
    OuterChallenge.reduceTriple (InstalledRoundCommit.actualDigestDraw
        (hashOf (boundedQueries L) T) c (realizedRun L hL c s R U d hbE hbR T)
        (JointChallengeSpace.Draw.outerGate ⟨r, hr⟩))
      = ((outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d).get?
          (2 * r + 1)).getD 0 := by
  have h1 := strategic_run_gate_draw_is_gate_triple L hL c s (reducedRoundMessage R) hbR
    (reduced_round_causal R) (realizedRun L hL c s R U d hbE hbR T) T
    (realized_run_statement L hL c s R U d hbE hbR T)
    (realized_run_messages L hL c s R U d hbE hbR T)
    (realized_run_length_budget L hL c s R U d hbE hbR T)
    (realized_run_messages_length L hL c s R U d hbE hbR T) ⟨r, hr⟩
  have h2 : gateTriple L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hbR r T
      = gateTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE r T :=
    (extended_gate_triple_eq L hL c s R U d hbE hbR T r (by omega)).symm
  rw [h1.trans h2, outer_history_get_gate L hL OuterInitial.zeroDigest
    (extendedShape c s R U d) hbE T d r (by omega)]
  rfl

/-! ## 6. THE COMMITTED CELLS ARE A FUNCTION OF THE REDUCED HISTORY -/

theorem lift_get (xs : List Verifier.Ext3) (k : Nat) :
    (OpenedClaimFold.lift xs).get? k = (xs.get? k).map Element.mk := by
  rw [OpenedClaimFold.lift, List.get?_eq_getElem?, List.get?_eq_getElem?, List.getElem?_map]

/-- **THE ROW POINT OF THE EXPLICIT ENGINE AT THE REALIZED PROOF IS READ OFF THE
REDUCED HISTORY.**  Entry `r` of the adopted `OpenedClaimFold.cellRow` is the
adopted `TwoStageConditionalCount.rowCoord` coordinate of the run's own outer
draw; at the realized run that coordinate is the extended chain's own round
triple, which is entry `2 r` (log cells) or `2 r + 1` (gate cells) of the adopted
`OuterLaneTransport.outerHistory`. -/
theorem lift_cell_row_is_row_from_history (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5)
    (T : OracleTable (boundedQueries L)) :
    OpenedClaimFold.lift (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
          (hashOf (boundedQueries L) T) khash P c₀) c
          (realizedRun L hL c s R U d hbE hbR T)) cellIndex)
      = rowFromHistory cellIndex
          (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d) := by
  have hmlen := realized_run_messages_length L hL c s R U d hbE hbR T
  have hxlen : (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d).length
      = 2 * d := outer_history_length L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d
  have hhalf : (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T
        d).length / 2 = d := by
    rw [hxlen]; omega
  have hrowlen : (OpenedClaimFold.cellRow (Verifier.derivedRounds
        (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀) c
        (realizedRun L hL c s R U d hbE hbR T)) cellIndex).length = c.degreeBits := by
    rw [TwoStageConditionalCount.cell_row_length gdec hash khash P c₀ c
      (realizedRun L hL c s R U d hbE hbR T) cellIndex (hashOf (boundedQueries L) T)]
    exact hmlen
  refine List.ext_get? (fun k => ?_)
  by_cases hk : k < c.degreeBits
  · rw [lift_get, TwoStageConditionalCount.row_point_is_outer_draw_function gdec hash
      (hashOf (boundedQueries L) T) khash P c₀ c (realizedRun L hL c s R U d hbE hbR T) hdb
      hmlen cellIndex k hk,
      row_from_history_get cellIndex _ k (by rw [hhalf]; omega)]
    fin_cases cellIndex
    · exact congrArg some (run_log_draw_is_history_entry L hL c s R U d hbE hbR T hdeg k hk)
    · exact congrArg some (run_log_draw_is_history_entry L hL c s R U d hbE hbR T hdeg k hk)
    · exact congrArg some (run_log_draw_is_history_entry L hL c s R U d hbE hbR T hdeg k hk)
    · exact congrArg some (run_gate_draw_is_history_entry L hL c s R U d hbE hbR T hdeg k hk)
    · exact congrArg some (run_gate_draw_is_history_entry L hL c s R U d hbE hbR T hdeg k hk)
  · rw [List.get?_eq_none.mpr
        (by rw [OpenedClaimFold.lift, List.length_map, hrowlen]; omega),
      row_from_history_get_none cellIndex _ k (by rw [hhalf]; omega)]

/-- **THE COMMITTED CELL FAMILY AS A FUNCTION OF THE REDUCED HISTORY.**  The
extracted columns are FIXED DATA -- the standing assumption the adopted
`ReducedIndexLanes` HONESTY (ii)/(iii) makes for `g` and `coeffsOf`, which for
`cols` and `coeffsOf` is the adopted open `CommitmentOrder.CommittedTables` join
(the extractor's round-one-opening argument must drop out) and for `g` is that
join PLUS a fixed gate alpha, `g` being a function of the block-0 alpha cell -- and
the
row point they are evaluated at is read off the history, so the whole family is. -/
def committedOf (cols : Fin 5 → List (List Element)) (cellIndex : Fin 5)
    (xs : List Element) : List Element :=
  IndexPointZeroCheck.openedCells (cols cellIndex) (rowFromHistory cellIndex xs)

/-- (6) **THE TRANSFER THE ADOPTED HONESTY (iii) ASKED FOR.**  At the realized
proof of the reduced adaptive prover the explicit engine's COMMITTED cells are
`committedOf cols cellIndex` applied to the run's own reduced history, at every
table.  This is what licenses instantiating the adopted
`ReducedIndexLanes.full_index_bad_draw_probability_le_combined` at
`committed := committedOf cols cellIndex`. -/
theorem committed_is_history_function (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (T : OracleTable (boundedQueries L)) :
    IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
            (hashOf (boundedQueries L) T) khash P c₀) c
            (realizedRun L hL c s R U d hbE hbR T)) cellIndex))
      = committedOf cols cellIndex
          (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d) :=
  congrArg (IndexPointZeroCheck.openedCells (cols cellIndex))
    (lift_cell_row_is_row_from_history gdec hash khash P c₀ L hL c s R U d hbE hbR hdeg hdb
      cellIndex T)

/-! ## 7. THE INDEX DIGEST AND THE INDEX DRAW OF THE REALIZED RUN -/

/-- (7) **THE EXTENDED CHAIN'S POST-ROUNDS DIGEST IS THE RUN'S OWN POST-ROUNDS
DIGEST.**  The adopted `ConcreteChainThreading.chain_model_is_the_run_chain` at
`r = degreeBits`, carried onto the extended chain by section 2 and the adopted
`StrategyChainBound.strategic_prover_chain_is_strategy_chain`.  This discharges
the chain-model hypothesis `hst` of the adopted
`ReducedIndexLanes.extended_stage_is_index_digest` AT THE SNAPSHOT THE ADOPTED
`SoundnessAssembly.actualIndexDraw` USES, rather than at the chain's own. -/
theorem extended_rounds_state_is_run_digest (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R)) (hdeg : c.degreeBits = d)
    (T : OracleTable (boundedQueries L)) :
    (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)
        (OuterInitial.derive (hashOf (boundedQueries L) T) c
          (Verifier.statement (realizedRun L hL c s R U d hbE hbR T))).state 0
        ((realizedRun L hL c s R U d hbE hbR T).logRounds.zip
          (realizedRun L hL c s R U d hbE hbR T).gateRounds)).digest
      = strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
          (22 + 5 * d) T := by
  have hmlen := realized_run_messages_length L hL c s R U d hbE hbR T
  have hbud := realized_run_length_budget L hL c s R U d hbE hbR T
  have hshape : prefixRoundShape c (Verifier.statement (realizedRun L hL c s R U d hbE hbR T))
        (roundMessages (realizedRun L hL c s R U d hbE hbR T))
      = prefixRoundShape c s
          (realizedMessages L hL c s (reducedRoundMessage R) hbR c.degreeBits T) := by
    rw [realized_run_statement, realized_run_messages]
  have h1 : strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
        (22 + 5 * d) T
      = strategyFrameState L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hbR
        (22 + 5 * d) T :=
    extended_state_eq_reduced L hL c s R U d hbE hbR T (22 + 5 * d) (Nat.le_refl _)
  have h2 : strategyFrameState L hL OuterInitial.zeroDigest (strategyOfReduced c s R) hbR
        (22 + 5 * d) T
      = frameState L OuterInitial.zeroDigest
          (prefixRoundShape c s
            (realizedMessages L hL c s (reducedRoundMessage R) hbR c.degreeBits T))
          (strategic_hlen_of_bounded L hL c s (reducedRoundMessage R) hbR c.degreeBits T)
          (22 + 5 * d) T := by
    rw [← hdeg]
    exact strategic_prover_chain_is_strategy_chain L hL c s (reducedRoundMessage R) hbR
      (reduced_round_causal R) c.degreeBits T (22 + 5 * c.degreeBits) (Nat.le_refl _)
  have h3 : frameState L OuterInitial.zeroDigest
        (prefixRoundShape c (Verifier.statement (realizedRun L hL c s R U d hbE hbR T))
          (roundMessages (realizedRun L hL c s R U d hbE hbR T))) hbud (22 + 5 * d) T
      = frameState L OuterInitial.zeroDigest
        (prefixRoundShape c s
          (realizedMessages L hL c s (reducedRoundMessage R) hbR c.degreeBits T))
        (strategic_hlen_of_bounded L hL c s (reducedRoundMessage R) hbR c.degreeBits T)
        (22 + 5 * d) T :=
    frame_state_shape_congr L OuterInitial.zeroDigest _ _ hshape hbud
      (strategic_hlen_of_bounded L hL c s (reducedRoundMessage R) hbR c.degreeBits T)
      (22 + 5 * d) T
  have h4 := ConcreteChainThreading.chain_model_is_the_run_chain L c
    (realizedRun L hL c s R U d hbE hbR T) hbud T c.degreeBits (Nat.le_of_eq hmlen.symm)
  have hstage : 22 + 5 * d = 22 + 5 * c.degreeBits := by omega
  rw [h1, h2, ← h3, hstage, h4,
    show (roundMessages (realizedRun L hL c s R U d hbE hbR T)).take c.degreeBits
      = roundMessages (realizedRun L hL c s R U d hbE hbR T) from by
        rw [← hmlen, List.take_length]]
  rfl

/-- (7) **THE EXPLICIT ENGINE'S OWN INDEX DRAW AT THE REALIZED PROOF IS THE
EXTENDED CHAIN'S INDEX COLUMN.**  The adopted
`ReducedIndexLanes.index_read_is_actual_index_draw` at the snapshot the adopted
`SoundnessAssembly.actualIndexDraw` names, which the previous theorem supplies. -/
theorem run_index_draw_is_index_read (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R)) (hdeg : c.degreeBits = d)
    (T : OracleTable (boundedQueries L)) :
    SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
        (realizedRun L hL c s R U d hbE hbR T)
      = indexRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d)
          c.indexBits T :=
  (index_read_is_actual_index_draw L hL c s R U d c.indexBits hbE T
    (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)
      (OuterInitial.derive (hashOf (boundedQueries L) T) c
        (Verifier.statement (realizedRun L hL c s R U d hbE hbR T))).state 0
      ((realizedRun L hL c s R U d hbE hbR T).logRounds.zip
        (realizedRun L hL c s R U d hbE hbR T).gateRounds))
    (extended_rounds_state_is_run_digest L hL c s R U d hbE hbR hdeg T)).symm

/-! ## 8. THE EXPLICIT ENGINE'S OWN INDEX BAD EVENT -/

/-- The adopted `IndexLanesOracle.guardedIndexBadEvent` IS the adopted
`SoundnessAssembly.indexBadEvent`, guard branch for guard branch. -/
theorem guarded_is_assembly_index_bad_event (bits : Nat) (a b : List Element) :
    guardedIndexBadEvent bits a b = SoundnessAssembly.indexBadEvent bits a b := by
  by_cases h : IndexPointZeroCheck.CellsDifferOnCube bits a b
  · rw [guarded_index_bad_event_of_differ bits a b h,
      SoundnessAssembly.index_bad_event_of_differ bits a b h]
  · rw [guarded_index_bad_event_of_cube_agreement bits a b h,
      SoundnessAssembly.index_bad_event_of_cube_agreement bits a b h]

/-- (8) **THE EXPLICIT ENGINE'S INDEX BAD SET AT THE REALIZED PROOF IS THE
ADOPTED `ReducedIndexLanes.indexBadTarget` AT `committedOf`.**  Both cell
families are read off the reduced history: the supplied one by the adopted
`ReducedIndexLanes.used_cell_is_bound_cell` and the definition of
`realizedClaims`, the committed one by `committed_is_history_function`. -/
theorem engine_index_target_is_reduced_target (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (T : OracleTable (boundedQueries L)) :
    SoundnessAssembly.indexBadEvent c.indexBits
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell
          (realizedRun L hL c s R U d hbE hbR T).used
          (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
            (hashOf (boundedQueries L) T) khash P c₀) c
            (realizedRun L hL c s R U d hbE hbR T)) cellIndex).1)
        (IndexPointZeroCheck.openedCells (cols cellIndex)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow
            (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c
              (realizedRun L hL c s R U d hbE hbR T)) cellIndex)))
      = indexBadTarget c.indexBits U cellIndex (committedOf cols cellIndex)
          (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d) := by
  rw [← guarded_is_assembly_index_bad_event, indexBadTarget, used_cell_is_bound_cell,
    committed_is_history_function gdec hash khash P c₀ L hL c s R U d hbE hbR hdeg hdb
      cellIndex cols T]
  rfl

open Classical in
/-- **THE EXPLICIT ENGINE'S OWN INDEX BAD EVENT ON THE ORACLE TABLE**, at the
realized proof of the reduced adaptive prover: the run's own adopted
`SoundnessAssembly.actualIndexDraw` lands in the adopted
`SoundnessAssembly.indexBadEvent` built from the run's own supplied and committed
cells.  `Finset.univ` here is this module's own (see HONESTY (viii)). -/
noncomputable def engineIndexBadEvent (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R)) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c
        (realizedRun L hL c s R U d hbE hbR T)
      ∈ SoundnessAssembly.indexBadEvent c.indexBits
          (OpenedClaimFold.lift (OpenedClaimFold.boundCell
            (realizedRun L hL c s R U d hbE hbR T).used
            (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c
              (realizedRun L hL c s R U d hbE hbR T)) cellIndex).1)
          (IndexPointZeroCheck.openedCells (cols cellIndex)
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow
              (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
                (hashOf (boundedQueries L) T) khash P c₀) c
                (realizedRun L hL c s R U d hbE hbR T)) cellIndex))))

open Classical in
/-- (8) **THE ENGINE'S OWN INDEX BAD EVENT IS THE ADOPTED
`ReducedIndexLanes.indexBadEvent` AT `committed := committedOf cols cellIndex`.**
Set for set, on the nose. -/
theorem engine_index_bad_event_eq (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR cellIndex cols
      = indexBadEvent L hL c s R U d c.indexBits hbE cellIndex (committedOf cols cellIndex) := by
  refine Finset.ext (fun T => ?_)
  rw [engineIndexBadEvent, Finset.mem_filter, mem_index_bad_event]
  simp only [Finset.mem_univ, true_and]
  rw [run_index_draw_is_index_read L hL c s R U d hbE hbR hdeg T,
    engine_index_target_is_reduced_target gdec hash khash P c₀ L hL c s R U d hbE hbR hdeg hdb
      cellIndex cols T]

open Classical in
/-- **THE UNION THIS MODULE BOUNDS**: the adopted
`ReducedFullTransport.fullBadEvent` at the extended prover's own chain, union the
EXPLICIT ENGINE'S OWN index bad event at the realized proof. -/
noncomputable def fullEngineIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R)) (logLane gateLane : Lane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  ReducedFullTransport.fullBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
      logLane gateLane d rows g coeffsOf
    ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR cellIndex cols

open Classical in
theorem full_engine_index_bad_event_eq (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (logLane gateLane : Lane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    fullEngineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR logLane gateLane rows g
        coeffsOf cellIndex cols
      = fullIndexBadEvent L hL c s R U d c.indexBits hbE logLane gateLane rows g coeffsOf
          cellIndex (committedOf cols cellIndex) := by
  rw [fullEngineIndexBadEvent, fullIndexBadEvent,
    engine_index_bad_event_eq gdec hash khash P c₀ L hL c s R U d hbE hbR hdeg hdb cellIndex cols]

open Classical in
/-- (8) **THE HEADLINE.**  For the reduced-history adaptive prover with a
history-dependent used-claims choice, the mass of the adopted
`ReducedFullTransport.fullBadEvent` UNION THE EXPLICIT ENGINE'S OWN index bad
event at the realized proof is at most

  `combinedBound d q d constraints + 2 * tauTerm c.indexBits + one clash term`.

The index summand is no longer stated at a modelled `committed` parameter: it is
the engine's own committed family, which `committed_is_history_function` PROVES
is a function of the reduced history once the extracted columns are fixed data.

READ THE HONESTY HEADER: this is a good-draw-conditional statement about ONE
named event on the oracle table, not the system's soundness error, and no
adaptive Fiat--Shamir soundness is claimed. -/
theorem reduced_engine_index_bad_draw_probability_le (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (logLane gateLane : Lane)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (fullEngineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR logLane gateLane
          (2 ^ d) g coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  rw [full_engine_index_bad_event_eq gdec hash khash P c₀ L hL c s R U d hbE hbR hdeg hdb
    logLane gateLane (2 ^ d) g coeffsOf cellIndex cols]
  exact full_index_bad_draw_probability_le_combined L hL c s R U d c.indexBits hbE logLane
    gateLane q constraints g coeffsOf cellIndex (committedOf cols cellIndex) hdu hbu hlog hgate
    hclen

/-! ## 9. ALL FIVE BOUND CELLS -/

open Classical in
/-- (9) A two-set union intersected with a conditioning event splits. -/
theorem inter_union_mass_le (L : Nat) (A B N : Finset (OracleTable (boundedQueries L))) :
    oracleProbability (boundedQueries L) ((A ∪ B) ∩ N)
      ≤ oracleProbability (boundedQueries L) (A ∩ N)
        + oracleProbability (boundedQueries L) (B ∩ N) := by
  rw [Finset.union_inter_distrib_right]
  exact oracle_probability_union_le (boundedQueries L) _ _

open Classical in
/-- (9) **THE OUTER, TAU AND ALPHA MASSES AT THE LARGER CONDITIONING STAGE.**
The first three summands of the adopted
`ReducedIndexLanes.full_index_bad_draw_probability_le`, isolated so that more
than one index summand can be added to them under ONE complement term. -/
theorem full_bad_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d)) (logLane gateLane : Lane)
    (q rows constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (ReducedFullTransport.fullBadEvent L hL OuterInitial.zeroDigest
            (extendedShape c s R U d) hbE logLane gateLane d rows g coeffsOf
          ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
              (indexStage d))
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints := by
  have hnest : stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
        (indexStage d)
      ⊆ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
        ReducedFullTransport.deriveStage :=
    stage_no_clash_mono L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
      ReducedFullTransport.deriveStage (indexStage d)
      (le_of_lt (derive_stage_lt_index_stage d))
  have hu3 := inter_union_mass_le L
    (outerLaneBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
      logLane gateLane d
      ∪ ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hbE d g)
    (ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
      (extendedShape c s R U d) hbE d rows coeffsOf)
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
  have hu4 := inter_union_mass_le L
    (outerLaneBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
      logLane gateLane d)
    (ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
      (extendedShape c s R U d) hbE d g)
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
  have houter := outer_no_clash_mass_le L hL OuterInitial.zeroDigest (extendedShape c s R U d)
    hbE logLane gateLane 5 (q + 2) hlog hgate (indexStage d) d
    (fun r hr => le_of_lt (round_stage_lt_index_stage r d hr))
  rw [round_terms_sum d q] at houter
  have htausub : ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hbE d g
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d)
      ⊆ (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
          ReducedFullTransport.deriveStage).filter (fun T =>
          ReducedFullTransport.tauRead L hL OuterInitial.zeroDigest (extendedShape c s R U d)
              hbE d T
            ∈ ChallengeUnionBound.productEvent d (ZeroCheckSemantics.zeroCheckBadSet d g)) := by
    rw [ReducedFullTransport.gateTauBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have htau : oracleProbability (boundedQueries L)
      (ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
          (extendedShape c s R U d) hbE d g
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
            (indexStage d))
      ≤ ChallengeUnionBound.tauTerm d :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ htausub)
      (ReducedFullTransport.gate_tau_no_clash_mass_le L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hbE d g hdu)
  have halphasub : ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hbE d rows coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d)
      ⊆ (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
          ReducedFullTransport.deriveStage).filter (fun T =>
          stageTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
              ReducedFullTransport.deriveStage (ReducedFullTransport.alphaBase d) T
            ∈ OuterChallenge.tupleEvent
                (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)) := by
    rw [ReducedFullTransport.gateAlphaBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have halpha : oracleProbability (boundedQueries L)
      (ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
          (extendedShape c s R U d) hbE d rows coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
            (indexStage d))
      ≤ ChallengeUnionBound.alphaTerm rows constraints :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ halphasub)
      (ReducedFullTransport.gate_alpha_no_clash_mass_le L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hbE d rows constraints coeffsOf hdu hclen)
  rw [ReducedFullTransport.fullBadEvent]
  linarith

open Classical in
/-- (9) One cell's index mass, at the conditioning event of the whole chain. -/
theorem index_bad_event_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d)) (cellIndex : Fin 5)
    (committed : List Element → List Element)
    (hbu : 6 * bits ≤ Transcript.u64Limit) :
    oracleProbability (boundedQueries L)
        (indexBadEvent L hL c s R U d bits hbE cellIndex committed
          ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
              (indexStage d))
      ≤ 2 * ChallengeUnionBound.tauTerm bits := by
  have hsub : indexBadEvent L hL c s R U d bits hbE cellIndex committed
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d)
      ⊆ (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
          (indexStage d)).filter (fun T =>
          indexRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
              (indexStage d) bits T
            ∈ indexBadTarget bits U cellIndex committed
                (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T
                  d)) := by
    rw [indexBadEvent]
    exact univ_filter_inter_subset _ _ _ (fun T hT => hT)
  exact le_trans (oracle_probability_mono (boundedQueries L) _ _ hsub)
    (index_bad_no_clash_mass_le L hL c s R U d bits hbE cellIndex committed hbu)

open Classical in
/-- **THE FIVE BOUND CELLS' ENGINE INDEX BAD EVENTS, UNIONED.**  The adopted
`SoundnessAssembly.explicit_good_draw_assembly` takes its index hypothesis at ONE
`cellIndex`; the five cells each need one. -/
noncomputable def allCellsEngineIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  (((engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 0 cols
    ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 1 cols)
    ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 2 cols)
    ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 3 cols)
    ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 4 cols

open Classical in
/-- **THE UNION OVER ALL FIVE BOUND CELLS.** -/
noncomputable def fullAllCellsEngineIndexBadEvent (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R)) (logLane gateLane : Lane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  ReducedFullTransport.fullBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
      logLane gateLane d rows g coeffsOf
    ∪ allCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR cols

open Classical in
/-- (9) **THE HEADLINE, AT ALL FIVE BOUND CELLS.**  Five index summands, ONE
clash term: all six masses are conditioned on the SAME no-clash event of the
extended chain at its full `22 + 5 d + 8` stages.

  `<= combinedBound d q d constraints + 5 * (2 * tauTerm c.indexBits) + clash`.

READ THE HONESTY HEADER. -/
theorem reduced_engine_index_bad_draw_probability_le_all_cells (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (logLane gateLane : Lane)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element))
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * c.indexBits ≤ Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (fullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR logLane
          gateLane (2 ^ d) g coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 5 * (2 * ChallengeUnionBound.tauTerm c.indexBits)
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hcell : ∀ i : Fin 5,
      engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR i cols
        = indexBadEvent L hL c s R U d c.indexBits hbE i (committedOf cols i) :=
    fun i => engine_index_bad_event_eq gdec hash khash P c₀ L hL c s R U d hbE hbR hdeg hdb i cols
  have hidx : ∀ i : Fin 5, oracleProbability (boundedQueries L)
      (engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR i cols
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
            (indexStage d))
      ≤ 2 * ChallengeUnionBound.tauTerm c.indexBits := by
    intro i
    rw [hcell i]
    exact index_bad_event_no_clash_mass_le L hL c s R U d c.indexBits hbE i
      (committedOf cols i) hbu
  have hfull := full_bad_no_clash_mass_le L hL c s R U d hbE logLane gateLane q (2 ^ d)
    constraints g coeffsOf hdu hlog hgate hclen
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (fullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR logLane
        gateLane (2 ^ d) g coeffsOf cols)
      (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (fullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR logLane
      gateLane (2 ^ d) g coeffsOf cols
      ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
    ((stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))ᶜ)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE
        (indexStage d))ᶜ)
      ≤ ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (extendedShape c s R U d) hbE (indexStage d)
  have hs1 := inter_union_mass_le L
    (ReducedFullTransport.fullBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d)
      hbE logLane gateLane d (2 ^ d) g coeffsOf)
    (allCellsEngineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR cols)
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
  have hs2 := inter_union_mass_le L
    (((engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 0 cols
      ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 1 cols)
      ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 2 cols)
      ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 3 cols)
    (engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 4 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
  have hs3 := inter_union_mass_le L
    ((engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 0 cols
      ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 1 cols)
      ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 2 cols)
    (engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 3 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
  have hs4 := inter_union_mass_le L
    (engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 0 cols
      ∪ engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 1 cols)
    (engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 2 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
  have hs5 := inter_union_mass_le L
    (engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 0 cols)
    (engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR 1 cols)
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE (indexStage d))
  have h0 := hidx 0
  have h1 := hidx 1
  have h2 := hidx 2
  have h3 := hidx 3
  have h4 := hidx 4
  rw [ChallengeUnionBound.combinedBound]
  rw [fullAllCellsEngineIndexBadEvent, allCellsEngineIndexBadEvent] at hmono hu1 ⊢
  rw [allCellsEngineIndexBadEvent] at hs1
  linarith

/-! ## 10. THE SUPPLIED CELLS, THE GUARD, AND NON-VACUITY -/

/-- (10) **THE SUPPLIED CELLS AT THE REALIZED PROOF ARE THE PROVER'S OWN CHOICE.**
The adopted `ReducedIndexLanes.used_cell_is_bound_cell` at the realized run: the
adopted `OpenedClaimFold.boundCell`'s first component reads `used` alone, and at
the realized run `used` IS the used-claims choice at the reduced history. -/
theorem supplied_cell_at_realized_proof (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R)) (idx : Verifier.IndexPoints)
    (cellIndex : Fin 5) (T : OracleTable (boundedQueries L)) :
    (OpenedClaimFold.boundCell (realizedRun L hL c s R U d hbE hbR T).used idx cellIndex).1
      = usedCell (U (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d))
          cellIndex :=
  used_cell_is_bound_cell _ idx cellIndex

open Classical in
/-- (10) **THE GUARD BITES ON THE ENGINE'S OWN EVENT.**  If the extracted columns
open at the row point to exactly the cells the prover supplied, the engine's index
bad event is EMPTY -- so the bound below is not a bound on the whole table space
by fiat, and the hypothesis "the index draw misses it" is not refutable. -/
theorem engine_index_bad_event_at_honest_cells (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d))
    (hbR : StrategyBounded L (strategyOfReduced c s R))
    (hdeg : c.degreeBits = d) (hdb : c.degreeBits ≤ 13) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element))
    (hhon : ∀ xs, committedOf cols cellIndex xs
      = OpenedClaimFold.lift (usedCell (U xs) cellIndex)) :
    engineIndexBadEvent gdec hash khash P c₀ L hL c s R U d hbE hbR cellIndex cols = ∅ := by
  rw [engine_index_bad_event_eq gdec hash khash P c₀ L hL c s R U d hbE hbR hdeg hdb cellIndex
    cols]
  refine Finset.eq_empty_of_forall_not_mem (fun T hT => ?_)
  rw [mem_index_bad_event, index_bad_target_at_honest_cells c.indexBits U cellIndex
    (committedOf cols cellIndex) _ (hhon _)] at hT
  exact absurd hT (Finset.not_mem_empty _)

/-- (10) The row point read off the realized history really has `d` entries -- the
transfer is not about an empty row. -/
theorem realized_row_from_history_length (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hbE : StrategyBounded L (extendedShape c s R U d)) (cellIndex : Fin 5)
    (T : OracleTable (boundedQueries L)) :
    (rowFromHistory cellIndex
        (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d)).length
      = d := by
  rw [row_from_history_length,
    outer_history_length L hL OuterInitial.zeroDigest (extendedShape c s R U d) hbE T d]
  omega

/-- A configuration at the envelope of the closed instance below: thirteen coupled
rounds, eight index bits, `quotientDegree = 8`, `numGateConstraints = 123`. -/
def envelopeConfig : Verifier.Config :=
  { Verifier.testConfig with
      degreeBits := 13
      indexBits := 8
      quotientDegree := 8
      numGateConstraints := 123 }

/-- (10) **THE NEW SIDE CONDITIONS ARE SATISFIED AT THE ENVELOPE.**  `hdeg`,
`hdb` and `hbu` of the headline, and the adopted round budget, all hold at
`envelopeConfig` -- so no hypothesis below is vacuous. -/
theorem envelope_config_hypotheses :
    envelopeConfig.degreeBits = 13 ∧ envelopeConfig.indexBits = 8 ∧
      envelopeConfig.degreeBits ≤ 13 ∧
      6 * envelopeConfig.indexBits ≤ Transcript.u64Limit ∧
      12 + 6 * 13 < Transcript.u64Limit := by
  refine ⟨rfl, rfl, by rw [show envelopeConfig.degreeBits = 13 from rfl], ?_, ?_⟩
  · rw [show envelopeConfig.indexBits = 8 from rfl]
    exact eight_index_counter_budget
  · rw [Transcript.u64Limit]
    omega

/-! ## 11. THE CLOSED INSTANCE AT THIRTEEN ROUNDS AND EIGHT INDEX BITS -/

open Classical in
/-- (11) **THE CLOSED INSTANCE.**  Thirteen coupled rounds, `quotientDegree = 8`,
`numGateConstraints = 123`, `indexBits = 8`, the adopted non-trivial
`OuterLaneTransport.previousChallengeMessage` as the round-message choice and an
arbitrary used-claims choice `U`, at ONE bound cell.  The index summand is the
EXPLICIT ENGINE'S OWN index bad event at the realized proof.

  `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`.

The remaining hypotheses are the adopted
`ReducedIndexLanes.full_index_bound_at_thirteen` ones, unchanged, plus the two
configuration equations `envelope_config_hypotheses` discharges.

READ THE HONESTY HEADER: THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem engine_index_bound_at_thirteen (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (U : UsedClaimsStrategy) (W : Nat)
    (trlog trgate : List Element → List Element)
    (a1 b1 a2 b2 : Element) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hU : UsedClaimsBounded W U) (hLq : 189 + 24 * 8 ≤ L) (hLW : 69 + 24 * W ≤ L)
    (hdom : 86 ≤ L) :
    oracleProbability (boundedQueries L)
        (fullEngineIndexBadEvent gdec hash khash P c₀ L (Nat.le_trans (by omega) hLq) c s
          (previousChallengeMessage m) U 13
          (extended_shape_bounded L c s (previousChallengeMessage m) U 13 8 W hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hU hLq hLW hdom)
          (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
          (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
          (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
          (2 ^ 13) g coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 2 * ChallengeUnionBound.tauTerm 8 + 4560 / (Fintype.card Block : ℚ) := by
  have h := reduced_engine_index_bad_draw_probability_le gdec hash khash P c₀ L
    (Nat.le_trans (by omega) hLq) c s (previousChallengeMessage m) U 13
    (extended_shape_bounded L c s (previousChallengeMessage m) U 13 8 W hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hU hLq hLW hdom)
    (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
    hc13 (by omega)
    (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
    (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
    8 123 g coeffsOf cellIndex cols ReducedFullTransport.thirteen_counter_budget
    (by rw [hcidx]; exact eight_index_counter_budget)
    (log_lane_of_reduced_bounded (previousChallengeMessage m) trlog a1 b1 5
      (previous_challenge_message_log_length m 5 hmlog) htrlog)
    (gate_lane_of_reduced_bounded (previousChallengeMessage m) trgate a2 b2 (8 + 2)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) htrgate) hclen
  rw [hcidx] at h
  have harith : ((indexStage 13 : Nat) : ℚ) * (((indexStage 13 : Nat) : ℚ) + 1) / 2
      = 4560 := by
    rw [index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (11) The closed constant is strictly below `1`; inherited verbatim from the
adopted `ReducedIndexLanes.full_index_bound_at_thirteen_lt_one`. -/
theorem engine_index_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) < 1 :=
  full_index_bound_at_thirteen_lt_one

open Classical in
/-- (11) **THE CLOSED INSTANCE AT ALL FIVE BOUND CELLS.**  Same envelope, five
index summands, one clash term:

  `<= combinedBound 13 8 13 123 + 5 * (2 * tauTerm 8) + 4560 / |Block|`. -/
theorem engine_index_bound_at_thirteen_all_cells (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (m : Verifier.CoupledMessage) (U : UsedClaimsStrategy) (W : Nat)
    (trlog trgate : List Element → List Element)
    (a1 b1 a2 b2 : Element) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cols : Fin 5 → List (List Element))
    (hc13 : c.degreeBits = 13) (hcidx : c.indexBits = 8)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hU : UsedClaimsBounded W U) (hLq : 189 + 24 * 8 ≤ L) (hLW : 69 + 24 * W ≤ L)
    (hdom : 86 ≤ L) :
    oracleProbability (boundedQueries L)
        (fullAllCellsEngineIndexBadEvent gdec hash khash P c₀ L (Nat.le_trans (by omega) hLq) c s
          (previousChallengeMessage m) U 13
          (extended_shape_bounded L c s (previousChallengeMessage m) U 13 8 W hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hU hLq hLW hdom)
          (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
          (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
          (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
          (2 ^ 13) g coeffsOf cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 5 * (2 * ChallengeUnionBound.tauTerm 8) + 4560 / (Fintype.card Block : ℚ) := by
  have h := reduced_engine_index_bad_draw_probability_le_all_cells gdec hash khash P c₀ L
    (Nat.le_trans (by omega) hLq) c s (previousChallengeMessage m) U 13
    (extended_shape_bounded L c s (previousChallengeMessage m) U 13 8 W hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hU hLq hLW hdom)
    (strategy_of_reduced_bounded L c s (previousChallengeMessage m) 8 hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hLq)
    hc13 (by omega)
    (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
    (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
    8 123 g coeffsOf cols ReducedFullTransport.thirteen_counter_budget
    (by rw [hcidx]; exact eight_index_counter_budget)
    (log_lane_of_reduced_bounded (previousChallengeMessage m) trlog a1 b1 5
      (previous_challenge_message_log_length m 5 hmlog) htrlog)
    (gate_lane_of_reduced_bounded (previousChallengeMessage m) trgate a2 b2 (8 + 2)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) htrgate) hclen
  rw [hcidx] at h
  have harith : ((indexStage 13 : Nat) : ℚ) * (((indexStage 13 : Nat) : ℚ) + 1) / 2
      = 4560 := by
    rw [index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (11) And the five-cell constant is still strictly below `1`: the adopted
three-term envelope is at most `2 ^ (-172)`, five index terms at most
`5 / 2 ^ 185`, the clash term at most `2 ^ (-243)`.  `Fintype.card Block` is never
evaluated.  READ THE HONESTY HEADER. -/
theorem engine_index_bound_at_thirteen_all_cells_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 5 * (2 * ChallengeUnionBound.tauTerm 8)
        + 4560 / (Fintype.card Block : ℚ) < 1 := by
  have h1 : ChallengeUnionBound.combinedBound 13 8 13 123 ≤ (1 : ℚ) / 2 ^ 172 :=
    ChallengeUnionBound.combined_bound_at_extremes_numeric
  have h2 : 2 * ChallengeUnionBound.tauTerm 8 ≤ (1 : ℚ) / 2 ^ 185 := index_term_at_eight_numeric
  have h3 : (4560 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 243 :=
    index_birthday_term_le_two_pow_neg
  have h4 : (1 : ℚ) / 2 ^ 172 + 5 * (1 / 2 ^ 185) + 1 / 2 ^ 243 < 1 := by norm_num
  linarith

end Audit.Wire3.ReducedEngineIndex
