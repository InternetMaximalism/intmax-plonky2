import Audit.Wire3.ReducedFullTransport
import Audit.Wire3.IndexLanesOracle
import Audit.Wire3.OpenedClaimFold

/-!
# THE INDEX LANES FOR THE REDUCED-HISTORY ADAPTIVE PROVER

## WHAT THIS MODULE PROVES, AND WHAT IT DOES NOT -- READ THIS FIRST

The adopted `ReducedFullTransport.reduced_full_bad_draw_probability_le` bounds, for
the REDUCED-HISTORY subclass of transcript-restricted adaptive provers, the mass of
the union of the two outer sumcheck lanes, the gate tau column and the gate alpha
row union by the whole adopted `ChallengeUnionBound.combinedBound`, plus the
chain's own clash term at `22 + 5 d` stages.  Its HONESTY (iii) records exactly
what is missing and WHY:

> THE INDEX LANES ARE NOT INCLUDED. [...] The index bad sets are indexed by the
> run's USED CLAIMS, which the adopted `InstalledIndexSampler.indexDigest` absorbs
> AFTER the coupled rounds; for an adaptive prover those claims are functions of
> the round messages, hence of the table, so the target is NOT fixed data and the
> constant-target lemma does not apply.  What WOULD apply is the adopted
> `OuterLaneTransport.stage_triple_target_mass_le` in its DIAGONAL form [...]
> Proving that invariance, and a uniform cardinality bound on the index bad set
> over the conditioning event, is exactly the work NOT done below.

THIS MODULE DOES THAT WORK, for a prover that chooses its used claims as a
function of the reduced round-challenge history.  The headline
`full_index_bad_draw_probability_le_combined` bounds the mass of the union of

* the adopted `ReducedFullTransport.fullBadEvent` -- outer lanes, gate tau, gate
  alpha -- at the extended prover's own chain, and
* the index bad event at the REALIZED used claims,

by `ChallengeUnionBound.combinedBound d q d constraints
+ 2 * ChallengeUnionBound.tauTerm indexBits
+ (22 + 5 d + 8) (22 + 5 d + 9) / 2 / |Block|`.

The clash term is ONE term, not four: the four no-clash events are the SAME one,
the chain's at its full `22 + 5 d + 8` stages, and the adopted
`OuterLaneTransport.stage_no_clash_mono` puts it inside the block-`0` one.

## WHAT THE USED-CLAIMS CHOICE MAY READ -- THE MODEL, EXACTLY

`UsedClaimsStrategy` is `List Element -> Verifier.UsedClaims`.  The extended
prover of `extendedShape c s R U d` plays

* the adopted twenty-two relation-prefix frames of
  `CommitmentOrder.gateChallengeFrames c s` (stages `0 .. 21`);
* the adopted `StrategyChainBound.roundShapeMsg` five frames of the round message
  `R r xs` for each coupled round `r < d`, where `xs` is the adopted
  `OuterLaneTransport.reducedHistory` of the rounds before `r`
  (stages `22 .. 22 + 5 d - 1`);
* the adopted `InstalledIndexSampler.claimFrames` EIGHT frames of `U xs`, where
  `xs` is the adopted `reducedHistory` of ALL `d` rounds
  (stages `22 + 5 d .. 22 + 5 d + 7`).

So `U` is handed EXACTLY the `2 d` field elements
`OuterChallenge.reduceTriple (ch (roundStage r) 0, +1, +2)` and
`OuterChallenge.reduceTriple (ch (roundStage r) 3, +4, +5)` for `r < d`, oldest
first -- the log challenge of a round before its gate challenge -- and NOTHING
else.  It does not see a raw block, a counter above `5`, a stage that is not a
round stage, the relation prefix digests, or any answer at the index digest
itself.  `realized_history_length` says that list has `2 d` entries at every
table, and `history_claims_depends` exhibits a `U` that is non-constant on lists
of exactly that length, so the model is not vacuously satisfied by constant
choices.  The prover therefore picks its opened claims AFTER seeing every round
challenge and BEFORE the index squeezes, which is the adversarial order the
adopted HONESTY (iii) names.

## WHAT IS PROVED

1. THE INDEX STAGE AND ITS COUNTERS (section 1).  `indexStage d = 22 + 5 d + 8` is
   the stage the index lanes are squeezed at.  `indexBlockBase n = 3 n` is block
   `n`'s base counter and `index_block_base_is_index_counter` PROVES that the
   `2 * indexBits` blocks are exactly the adopted
   `InstalledIndexSampler.indexCounter` values -- `3 i` on the log lane and
   `3 * indexBits + 3 i` on the gate lane -- rather than asserting it.
   `index_counters_disjoint` is the separation the peel needs.
2. THE JOINT PEEL (sections 2 and 3).  The adopted
   `IndexPointZeroCheck.cellAgreementSet` is NOT a product of per-coordinate sets,
   so the whole `6 * indexBits`-counter block must be peeled JOINTLY, exactly as
   the adopted `ReducedFullTransport` peels the `3 d` tau counters.  `idxFibre`
   prescribes the first `n` index triples ON AN ARBITRARY STAGE-STABLE
   CONDITIONING EVENT `A` -- that generality is what the diagonal argument needs,
   and is the one place this differs from the adopted tau peel, which fixes
   `A = stageNoClash` -- `idx_fibre_stable` shows a prescription already made is
   unmoved by a LATER block's answers, and `idx_fibre_card` peels the blocks one
   at a time, giving the EXACT count `|fibre| * |DigestTriple| ^ n = |A|`.
   `idx_target_card` sums that over a constant target.
3. THE DIAGONAL BOUND (section 4).  `idx_diagonal_card` partitions `A` by the
   VALUE of a MOVING target `targ`, applies section 3 on each block, and gets
   `|{T : read T ∈ targ T}| * |DigestTriple| ^ (2 indexBits) ≤ bnd * |A|`.
   `idx_diagonal_mass_le` divides.  `idx_diagonal_mass_le_density` is the form the
   index lanes actually need: what is known about the adopted
   `IndexLanesOracle.guardedIndexBadEvent` is not a CARDINALITY but a DENSITY, so
   the uniform `Nat` bound the count needs is extracted as the maximum over the
   finitely many values `targ` takes on `A`.
4. THE EXTENDED STRATEGY AND ITS CHAIN (sections 5 and 6).  `extendedShape` is a
   `StrategyChainBound.Strategy`, so every adopted strategy-chain lemma applies to
   it unchanged; `extended_shape_bounded` discharges its length budget from the
   adopted `OuterLaneTransport.strategy_of_reduced_bounded` and the adopted
   `IndexLanesOracle.claim_shape_payload_bound`.
   `extended_strat_shape_is_claim_shape` proves that the eight frames past the
   rounds ARE the adopted `claimShapeAt` of the claims the prover chose at the
   run's OWN reduced history, and `extended_stage_is_index_digest` proves that the
   chain's stage-`22 + 5 d + 8` digest IS
   `InstalledIndexSampler.indexDigest (hashOf ... T) st (U (realized history))`.
   That is the adopted `IndexLanesOracle.index_state_is_index_digest` for an
   ADAPTIVE prover: there `u` is fixed data outside the table, here it is a
   function OF the table.
5. THE INVARIANCE (section 7).  `realized_history_reassign` and
   `realized_claims_reassign`: overwriting an answer at the stage-`22 + 5 d + 8`
   CHALLENGE queries moves neither the reduced history nor the chosen claims,
   because every entry of that history is a digest triple at a ROUND stage and
   round stages are strictly below the index stage (the adopted
   `OuterLaneTransport.stage_triple_reassign_lower`).  THIS IS THE PRECISE SENSE
   IN WHICH THE PROVER HAS COMMITTED TO ITS CLAIMS BEFORE THE INDEX CHALLENGES
   ARE SQUEEZED, and it is what the adopted HONESTY (iii) asked for.
   `index_bad_no_clash_mass_le` then composes sections 4 and 7 with the adopted
   `IndexLanesOracle.guarded_index_bad_event_mass_le` and reaches
   `2 * ChallengeUnionBound.tauTerm indexBits`.
6. THE UNION (section 8).  `full_index_bad_draw_probability_le` runs the adopted
   `ReducedFullTransport` union at the LARGER conditioning stage and adds the
   index summand; `full_index_bad_draw_probability_le_combined` reads the first
   three constants off as the adopted `combinedBound`.
7. THE OUTER PAIRING AT THE EXTENDED PROVER (section 9).
   `extended_log_lane_message_is_realized` and its gate twin are the adopted
   `OuterLaneTransport.log_lane_of_reduced_message_is_realized` re-proved at the
   extended strategy: the eight claim frames sit strictly after every round stage,
   so the pairing of the adopted section 8 is untouched by them and round `r`'s
   outer bad set is still built from the message THE PROVER CHOSE.
   `index_bad_target_of_differ` / `index_bad_target_at_honest_cells` show the
   adopted guard really bites in both directions.
8. THE CLOSED INSTANCE (section 10).  `full_index_bound_at_thirteen` is thirteen
   coupled rounds, `quotientDegree = 8`, `numGateConstraints = 123`,
   `indexBits = 8`, at the adopted non-trivial
   `OuterLaneTransport.previousChallengeMessage` and an arbitrary used-claims
   choice, with neither counter budget left as a hypothesis:

     `<= ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * tauTerm 8
        + 4560 / |Block|`,

   and `full_index_bound_at_thirteen_lt_one` records that this is strictly below
   `1`.  `4560 / |Block|` is the adopted
   `IndexLanesOracle.extended_digest_clash_mass_at_thirteen` numeral.
   READ HONESTY (v): THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR.
9. THE COLUMN READ IS THE SAMPLER'S OWN DRAW (section 11).
   `index_read_is_actual_index_draw`: the `2 * indexBits` digest triples the chain
   reads at the index stage ARE the adopted
   `InstalledIndexSampler.actualIndexDraw` at the adopted `indexDigest` of the
   realized claims.  Nothing is re-modelled.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Every mass below is the uniform
counting law on `RandomOracleSqueezes.OracleTable (boundedQueries L)` -- one
independent uniform block per byte string of length at most `L`.  The fresh-query
lemma everything rests on, the adopted
`BirthdayClashBound.fresh_coordinate_probability` reached through the adopted
`OuterLaneTransport.stage_triple_fibre_card`, is the DEFINING property of a random
table and is false, as a theorem, for any fixed hash.  Replacing the deployed
permutation by a table drawn from this law is an assumption with no proof anywhere
in this tree.

(ii) THE PROVER IS TRANSCRIPT-RESTRICTED AND REDUCED-HISTORY; GRINDING AND
RAW-BLOCK STRATEGIES ARE EXCLUDED.  A `StrategyChainBound.Strategy` is handed the
stage digests of its own chain and the oracle's answers at the CHALLENGE inputs of
those digests, and makes no oracle queries of its own; a random-oracle-model
Fiat--Shamir prover that hashes candidate payloads itself and keeps the one whose
digest collides -- GRINDING -- is NOT covered, and its clash mass grows with its
query count.  Sections 5 to 11 restrict further: the round messages are functions
of the REDUCED round-challenge history alone and the used claims are a function of
the reduced history of all `d` rounds, as spelled out above.  RAW-BLOCK-READING
STRATEGIES REMAIN OPEN, for the reason the adopted `OuterLaneTransport` header's
`laneOfStrategy` paragraph gives.  The twenty-two prefix frames are the adopted
`gateChallengeFrames c s`: the commitment roots live in the statement `s` and are
FIXED BEFORE the chain, so this prover cannot choose its commitments adaptively --
which is also why the adopted `g` and `coeffsOf` are legitimately fixed data in the
gate summands this module imports unchanged.

(iii) THE COMMITTED CELLS AT THE ROW POINT ARE A MODEL, NOT A DERIVATION.  The
adopted `SoundnessAssembly.indexBadEvent` is indexed by TWO cell families: the
SUPPLIED cells, which `used_cell_is_bound_cell` PROVES are a projection of
`p.used` alone -- the adopted `OpenedClaimFold.boundCell`'s first component does
not read the index points -- and the COMMITTED cells, the extracted columns
evaluated at the bound cell's ROW POINT.  In this module the committed family is
the PARAMETER `committed : List Element -> List Element`, a function of the same
reduced history.  WHAT JUSTIFIES THAT SHAPE, AND WHAT DOES NOT:

  * The adopted `TwoStageConditionalCount.row_point_is_outer_draw_function` and
    `row_point_determined_by_outer_draw` say the row point of every bound cell is
    a function of the run's own outer draw, entry by entry -- and the outer draw
    is exactly the reduced round-challenge history, by the adopted
    `OuterLaneTransport.reduced_history_is_outer_history`.  That is the shape
    assumed here.
  * BUT THOSE ARE FIXED-PROVER STATEMENTS.  They are stated for a FIXED
    `p : Verifier.Proof` with the side condition `(roundMessages p).length =
    c.degreeBits`, and for the explicit engine.  Transferring them to the reduced
    ADAPTIVE prover needs: a prefix-congruence lemma between the `extendedShape`
    chain and the `strategyOfReduced` chain (equal stage digests up to `22 + 5 d`),
    the adopted `OuterLaneTransport.strategic_run_log_draw_is_log_triple` /
    `_gate_` at `realizedProof`, the adopted
    `TwoStageConditionalCount.row_point_is_outer_draw_function` (that module is NOT
    in this module's import closure), and the standing assumption -- the same one
    (ii) already makes for `g` and `coeffsOf` -- that the extracted columns are
    FIXED DATA; `RowPointFixed` (constancy across all hashes) is NOT required,
    because the `committed` parameter is quantified universally and the real
    committed cells are literally a function of the reduced history once the
    columns are fixed.  NO THEOREM BELOW PERFORMS THAT TRANSFER.  The `committed` parameter is where the transfer would land,
    and the bound below is exactly as strong as that modelling step.
  * `g`, `coeffsOf` and the committed columns are NOT identified with the deployed
    tables anywhere.  That identification is the adopted `CommitmentOrder` reading
    together with that module's own open `CommittedTables` extraction join; this
    module INHERITS it unchanged and does not strengthen it.

(iv) THE LANES COVERED ARE THE OUTER SUMCHECK LANES, THE TWO BLOCK-`0` GATE LANES
AND THE INDEX LANES, AT ONE BOUND CELL.  The index summand is stated at ONE
`cellIndex : Fin 5`; the adopted `SoundnessAssembly` has five bound cells, and
five applications would cost `5 * 2 * tauTerm indexBits`, not `2 * tauTerm
indexBits`.  No theorem below takes that union.  THE WHIR FOLDING TRANSCRIPT AND
THE MERKLE OPENINGS ARE EXCLUDED A FORTIORI: they are not in the adopted
`combinedBound` at all, and proximity / list decoding, the query-repetition profile
and Merkle collision resistance contribute nothing here.

(v) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  The constant covers (a)
the outer sumcheck round-agreement events, (b) the gate tau multilinear zero check,
(c) the gate alpha zero check and (d) one bound cell's index-point agreement.  It
EXCLUDES the entire WHIR/Merkle contribution, which is the DOMINANT term.  The
deployed design point is around a hundred bits.  Quoting the number of section 10
as the wire-v3 soundness error would be wrong by roughly seventy bits.  The meaning
of the per-round bad sets remains the adopted `ConditionalSoundness` one --
GOOD-DRAW-CONDITIONAL, with that module's assumption list untouched -- and nothing
here instantiates it.

(vi) NO ADAPTIVE FIAT--SHAMIR SOUNDNESS IS CLAIMED.  What is bounded is the mass of
one named event defined directly on the oracle table.  The Fiat--Shamir half --
that the run's encoding draw is `JointChallengeSpace.jointProbability`-distributed,
and that the index draw is `IndexPointZeroCheck.indexProbability`-distributed --
remains exactly as unformalized as the adopted `JointChallengeSpace.DrawEncodesRun`
and `IndexPointZeroCheck` headers say, and nothing below is a claim that
Fiat--Shamir soundness has been established for an adaptive prover.  In particular
`indexBadEvent` is this module's OWN table-level event; it is NOT the adopted
`RandomOracleSqueezes.runDrawEvent` at the adopted `SoundnessAssembly.indexBadEvent`,
and no theorem below identifies the two.  What IS identified is the SET
(`indexBadTarget` is the adopted `IndexLanesOracle.guardedIndexBadEvent`, guard for
guard), the DIGEST (section 6) and the DRAW (section 11).

(vii) CHAIN-MODEL RESIDUES, INHERITED AND NEW.  `extended_stage_is_index_digest`
carries the same explicit hypothesis `hst` the adopted
`IndexLanesOracle.index_state_is_index_digest` carries -- that the post-rounds
snapshot's digest is the chain's digest after `22 + 5 d` stages -- and it is
satisfiable by the chain's own state
(`extended_index_state_hypothesis_is_satisfiable`).  The LIST BOOKKEEPING that this
stage is position `d` of the adopted `InstalledRoundCommit.concreteChain` is still
nobody's theorem.  The clash term is the adopted
`StrategyChainBound.strategy_chain_clash_probability_le` at `22 + 5 d + 8` stages,
which is an event about THIS chain's stage digests, not syntactically the adopted
`IndexLanesOracle.extendedDigestClashEvent`; the two carry the same numeral.

(viii) DISCLOSED TACTIC AND SHAPE NOTES.  `Finset.univ` appears in this module's
OWN definitions (`indexBadEvent`) and, through the generic lemmas
`Finset.mem_univ` / `Finset.card_univ` on `OracleTable`, in a few proofs; no tactic
or term below ever puts `Finset.univ` on `Element`, on
`OuterChallenge.DigestTriple`, on `InstalledIndexSampler.IndexSpace` or on
`ChallengeUnionBound.TripleTuple` in a position that can be reduced, and no `Nat`
arithmetic tactic below is ever shown a `Fintype.card` of any of them -- the
adopted `ReducedFullTransport.peel_pow` does the only exponent bookkeeping and is
stated over ABSTRACT naturals.  `index_space_card_as_triples` is proved from the
adopted `InstalledIndexSampler.index_space_card` and the adopted
`OuterChallenge.digest_tuple_cardinality` rather than by unfolding a `Fintype`
instance.  `open Classical in` is used for the declarations whose statements
mention membership in a `Finset (InstalledIndexSampler.IndexSpace bits)`, exactly
as the adopted `IndexLanesOracle` does and for the same reason.  Memberships over
the table space are manipulated through `Finset` equalities and the adopted generic
helpers `OuterLaneTransport.univ_filter_inter_subset` and `subset_inter_union_compl`.
No tuple `Finset` is ever instantiated at a literal size.  The counter budget
`6 * indexBits <= Transcript.u64Limit` is a hypothesis, discharged at
`indexBits = 8` by `eight_index_counter_budget`.
-/

namespace Audit.Wire3.ReducedIndexLanes

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterSequentialConditioning
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.IndexLanesOracle

/-! ## 1. THE INDEX STAGE AND ITS COUNTERS -/

def indexStage (d : Nat) : Nat := 22 + 5 * d + 8

theorem round_stage_lt_index_stage (r d : Nat) (h : r < d) : roundStage r < indexStage d := by
  rw [roundStage, indexStage]
  omega

theorem derive_stage_lt_index_stage (d : Nat) :
    ReducedFullTransport.deriveStage < indexStage d := by
  rw [ReducedFullTransport.deriveStage, indexStage]
  omega

theorem rounds_stage_le_index_stage (d : Nat) : 22 + 5 * d ≤ indexStage d := by
  rw [indexStage]; omega

/-- Block `n`'s base counter at the index digest. -/
def indexBlockBase (n : Nat) : Nat := 3 * n

/-- The position of an index draw in the `2 * bits` blocks. -/
def indexIdx (bits : Nat) : InstalledIndexSampler.IndexDraw bits → Nat
  | InstalledIndexSampler.IndexDraw.log i => i.val
  | InstalledIndexSampler.IndexDraw.gate i => bits + i.val

theorem index_block_base_is_index_counter (bits : Nat)
    (k : InstalledIndexSampler.IndexDraw bits) :
    indexBlockBase (indexIdx bits k) = InstalledIndexSampler.indexCounter bits k := by
  cases k with
  | log i => rfl
  | gate i =>
      show 3 * (bits + i.val) = 3 * bits + 3 * i.val
      omega

theorem index_idx_lt (bits : Nat) (k : InstalledIndexSampler.IndexDraw bits) :
    indexIdx bits k < 2 * bits := by
  cases k with
  | log i => have := i.isLt; show i.val < 2 * bits; omega
  | gate i => have := i.isLt; show bits + i.val < 2 * bits; omega

theorem exists_index_draw (bits n : Nat) (h : n < 2 * bits) :
    ∃ k : InstalledIndexSampler.IndexDraw bits, indexIdx bits k = n := by
  by_cases hn : n < bits
  · exact ⟨InstalledIndexSampler.IndexDraw.log ⟨n, hn⟩, rfl⟩
  · refine ⟨InstalledIndexSampler.IndexDraw.gate ⟨n - bits, by omega⟩, ?_⟩
    show bits + (n - bits) = n
    omega

theorem index_counter_lt (nb m : Nat) (hm : m < nb) (hnb : 3 * nb ≤ Transcript.u64Limit) :
    indexBlockBase m + 2 < Transcript.u64Limit := by
  rw [indexBlockBase]; omega

theorem index_counter_mem_lt (nb m c : Nat) (hm : m < nb) (hc : c ∈ tripleCounters (indexBlockBase m))
    (hnb : 3 * nb ≤ Transcript.u64Limit) : c < Transcript.u64Limit := by
  rcases (mem_triple_counters (indexBlockBase m) c).mp hc with h | h | h <;>
    (rw [h, indexBlockBase]; omega)

theorem index_counters_disjoint (n m c : Nat) (hnm : n < m)
    (hc : c ∈ tripleCounters (indexBlockBase m)) : c ∉ tripleCounters (indexBlockBase n) := by
  intro hc2
  rcases (mem_triple_counters (indexBlockBase m) c).mp hc with h | h | h <;>
    rcases (mem_triple_counters (indexBlockBase n) c).mp hc2 with h2 | h2 | h2 <;>
    · rw [h, indexBlockBase, indexBlockBase] at h2
      omega

/-- The alphabet of the index space, symbolically. -/
theorem index_space_card_as_triples (bits : Nat) :
    Fintype.card (InstalledIndexSampler.IndexSpace bits)
      = Fintype.card OuterChallenge.DigestTriple ^ (2 * bits) := by
  rw [InstalledIndexSampler.index_space_card, OuterChallenge.digest_tuple_cardinality]


/-! ## 2. THE JOINT PEEL OVER THE INDEX BLOCK -/

/-- The prescribed-prefix fibre of a conditioning event `A`: the tables whose
first `n` index triples at stage `j` take the prescribed values. -/
noncomputable def idxFibre (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) : Nat → Finset (OracleTable (boundedQueries L))
  | 0 => A
  | n + 1 =>
      (idxFibre L hL e0 strat hb j A t n).filter
        (fun T => stageTriple L hL e0 strat hb j (indexBlockBase n) T = t n)

theorem idx_fibre_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) : idxFibre L hL e0 strat hb j A t 0 = A := rfl

theorem idx_fibre_succ (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) (n : Nat) :
    idxFibre L hL e0 strat hb j A t (n + 1)
      = (idxFibre L hL e0 strat hb j A t n).filter
          (fun T => stageTriple L hL e0 strat hb j (indexBlockBase n) T = t n) := rfl

theorem mem_idx_fibre (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (t : Nat → OuterChallenge.DigestTriple) :
    ∀ (n : Nat) (T : OracleTable (boundedQueries L)),
      T ∈ idxFibre L hL e0 strat hb j A t n ↔
        (T ∈ A ∧ ∀ i, i < n →
          stageTriple L hL e0 strat hb j (indexBlockBase i) T = t i) := by
  intro n
  induction n with
  | zero =>
      intro T
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun h => h.1⟩
  | succ n2 ih =>
      intro T
      rw [idx_fibre_succ, Finset.mem_filter, ih T]
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

/-- (2) **THE FIBRE IS STAGE-STABLE AT EVERY LATER INDEX BLOCK.**  The three
counters of block `m` are different queries at the same digest from those of every
earlier block (`index_counters_disjoint`), so the prescriptions already made are
unmoved -- the adopted `OuterLaneTransport.stage_triple_reassign_same`. -/
theorem idx_fibre_stable (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j nb : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < nb → StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m)) A)
    (t : Nat → OuterChallenge.DigestTriple) (hnb : 3 * nb ≤ Transcript.u64Limit) :
    ∀ n m : Nat, n ≤ m → m < nb →
      StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m))
        (idxFibre L hL e0 strat hb j A t n) := by
  intro n
  induction n with
  | zero => intro m _ hmd; exact hA m hmd
  | succ n2 ih =>
      intro m hnm hmd
      have hprev := ih m (by omega) hmd
      rw [idx_fibre_succ]
      refine stage_stable_filter L hL e0 strat hb j (tripleCounters (indexBlockBase m))
        (idxFibre L hL e0 strat hb j A t n2) hprev
        (fun T => stageTriple L hL e0 strat hb j (indexBlockBase n2) T = t n2)
        (fun T hT c hc b => ?_)
      show stageTriple L hL e0 strat hb j (indexBlockBase n2)
            (reassign T (challengeSel L hL e0 strat hb j c T) b) = t n2
        ↔ stageTriple L hL e0 strat hb j (indexBlockBase n2) T = t n2
      rw [stage_triple_reassign_same L hL e0 strat hb j (indexBlockBase n2) c
        (index_counter_mem_lt nb m c hmd hc hnb)
        (index_counter_lt nb n2 (by omega) hnb)
        (index_counters_disjoint n2 m c (by omega) hc) T (hprev.1 T hT) b]

/-- (2) **THE JOINT FIBRE COUNT OVER THE WHOLE INDEX BLOCK.**  `n` applications of
the adopted `OuterLaneTransport.stage_triple_fibre_card`, with the adopted
`ReducedFullTransport.peel_pow` doing the exponent bookkeeping over ABSTRACT
naturals. -/
theorem idx_fibre_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j nb : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < nb → StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m)) A)
    (t : Nat → OuterChallenge.DigestTriple) (hnb : 3 * nb ≤ Transcript.u64Limit) :
    ∀ n : Nat, n ≤ nb →
      (idxFibre L hL e0 strat hb j A t n).card
          * Fintype.card OuterChallenge.DigestTriple ^ n
        = A.card := by
  intro n
  induction n with
  | zero => intro _; rw [idx_fibre_zero, pow_zero, Nat.mul_one]
  | succ n2 ih =>
      intro hn
      have hstep : (idxFibre L hL e0 strat hb j A t (n2 + 1)).card
            * Fintype.card OuterChallenge.DigestTriple
          = (idxFibre L hL e0 strat hb j A t n2).card :=
        stage_triple_fibre_card L hL e0 strat hb j (indexBlockBase n2)
          (index_counter_lt nb n2 (by omega) hnb) (idxFibre L hL e0 strat hb j A t n2)
          (idx_fibre_stable L hL e0 strat hb j nb A hA t hnb n2 n2 (le_refl n2) (by omega)) (t n2)
      exact (ReducedFullTransport.peel_pow _ _ _ n2 hstep).trans (ih (by omega))

/-! ## 3. THE INDEX COLUMN THE CHAIN READS, AND THE CONSTANT-TARGET COUNT -/

/-- **THE INDEX COLUMN THE CHAIN READS AT STAGE `j`**: coordinate `k` is the
digest triple at the stage-`j` counters `indexCounter bits k, +1, +2`, which is
exactly the adopted `InstalledIndexSampler.indexCounter` block
(`index_block_base_is_index_counter`). -/
def indexRead (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j bits : Nat) (T : OracleTable (boundedQueries L)) :
    InstalledIndexSampler.IndexSpace bits :=
  fun k => stageTriple L hL e0 strat hb j (indexBlockBase (indexIdx bits k)) T

theorem index_read_at_counter (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j bits : Nat) (T : OracleTable (boundedQueries L))
    (k : InstalledIndexSampler.IndexDraw bits) :
    indexRead L hL e0 strat hb j bits T k
      = stageTriple L hL e0 strat hb j (InstalledIndexSampler.indexCounter bits k) T := by
  show stageTriple L hL e0 strat hb j (indexBlockBase (indexIdx bits k)) T = _
  rw [index_block_base_is_index_counter]

/-- A total prescription extending one index point; the adopted
`OuterLaneTransport.zeroDigestTriple` fills the unused positions. -/
def idxExtend (bits : Nat) (w : InstalledIndexSampler.IndexSpace bits) :
    Nat → OuterChallenge.DigestTriple :=
  fun n => if h : n < bits then w (InstalledIndexSampler.IndexDraw.log ⟨n, h⟩)
    else if h2 : n - bits < bits then w (InstalledIndexSampler.IndexDraw.gate ⟨n - bits, h2⟩)
    else zeroDigestTriple

theorem idx_extend_at_idx (bits : Nat) (w : InstalledIndexSampler.IndexSpace bits)
    (k : InstalledIndexSampler.IndexDraw bits) : idxExtend bits w (indexIdx bits k) = w k := by
  cases k with
  | log i =>
      show (if h : i.val < bits then w (InstalledIndexSampler.IndexDraw.log ⟨i.val, h⟩)
        else if h2 : i.val - bits < bits then
          w (InstalledIndexSampler.IndexDraw.gate ⟨i.val - bits, h2⟩)
        else zeroDigestTriple) = w (InstalledIndexSampler.IndexDraw.log i)
      rw [dif_pos i.isLt]
  | gate i =>
      have hi := i.isLt
      have h1 : ¬ (bits + i.val < bits) := by omega
      have h2 : bits + i.val - bits < bits := by omega
      show (if h : bits + i.val < bits then w (InstalledIndexSampler.IndexDraw.log ⟨bits + i.val, h⟩)
        else if h2 : bits + i.val - bits < bits then
          w (InstalledIndexSampler.IndexDraw.gate ⟨bits + i.val - bits, h2⟩)
        else zeroDigestTriple) = w (InstalledIndexSampler.IndexDraw.gate i)
      rw [dif_neg h1, dif_pos h2]
      have hval : bits + i.val - bits = i.val := by omega
      exact congrArg (fun z => w (InstalledIndexSampler.IndexDraw.gate z)) (Fin.ext hval)

/-- (3) The whole-block fibre is exactly the set of tables of `A` that read `w`. -/
theorem idx_fibre_at_extend (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j bits : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (w : InstalledIndexSampler.IndexSpace bits) (T : OracleTable (boundedQueries L)) :
    T ∈ idxFibre L hL e0 strat hb j A (idxExtend bits w) (2 * bits) ↔
      (T ∈ A ∧ indexRead L hL e0 strat hb j bits T = w) := by
  rw [mem_idx_fibre]
  constructor
  · rintro ⟨hT, hall⟩
    refine ⟨hT, ?_⟩
    funext k
    show stageTriple L hL e0 strat hb j (indexBlockBase (indexIdx bits k)) T = w k
    rw [hall (indexIdx bits k) (index_idx_lt bits k), idx_extend_at_idx bits w k]
  · rintro ⟨hT, hread⟩
    refine ⟨hT, fun i hi => ?_⟩
    obtain ⟨k, hk⟩ := exists_index_draw bits i hi
    rw [← hk, idx_extend_at_idx bits w k, ← hread]
    rfl

open Classical in
/-- (3) **THE CONSTANT-TARGET COUNT OVER THE INDEX BLOCK.**  For a set `S` of
index points -- fixed data -- exactly `|S|` fibres of `A` are caught. -/
theorem idx_target_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j bits : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < 2 * bits →
      StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m)) A)
    (hnb : 6 * bits ≤ Transcript.u64Limit)
    (S : Finset (InstalledIndexSampler.IndexSpace bits)) :
    (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ S)).card
        * Fintype.card OuterChallenge.DigestTriple ^ (2 * bits)
      = S.card * A.card := by
  have hnb2 : 3 * (2 * bits) ≤ Transcript.u64Limit := by omega
  have hfib : (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ S)).card
      = ∑ w in S, ((A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ S)).filter
          (fun T => indexRead L hL e0 strat hb j bits T = w)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => (Finset.mem_filter.mp hx).2)
  have key : ∀ w ∈ S,
      ((A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ S)).filter
          (fun T => indexRead L hL e0 strat hb j bits T = w)).card
          * Fintype.card OuterChallenge.DigestTriple ^ (2 * bits)
        = A.card := by
    intro w hw
    have hset : (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ S)).filter
          (fun T => indexRead L hL e0 strat hb j bits T = w)
        = idxFibre L hL e0 strat hb j A (idxExtend bits w) (2 * bits) := by
      apply Finset.ext
      intro T
      rw [idx_fibre_at_extend, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hT, -⟩, hEq⟩
        exact ⟨hT, hEq⟩
      · rintro ⟨hT, hEq⟩
        exact ⟨⟨hT, hEq ▸ hw⟩, hEq⟩
    rw [hset]
    exact idx_fibre_card L hL e0 strat hb j (2 * bits) A hA (idxExtend bits w) hnb2
      (2 * bits) (le_refl _)
  rw [hfib, Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

/-! ## 4. THE DIAGONAL BOUND OVER THE WHOLE INDEX BLOCK -/

open Classical in
/-- (4) **THE DIAGONAL COUNT.**  The target `targ T` is NOT fixed data: it is
whatever the history has made it at the table `T`.  All that is asked of it is
that the `6 * bits` stage-`j` challenge answers it is tested against cannot move
it.  The conditioning event is partitioned by the VALUE of `targ`, the target is
constant on each block of that partition, and `idx_target_card` applies there --
the adopted `OuterLaneTransport.stage_triple_target_card` argument, run over the
whole `2 * bits`-coordinate block rather than one scheduled draw. -/
theorem idx_diagonal_card (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j bits : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < 2 * bits →
      StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m)) A)
    (hnb : 6 * bits ≤ Transcript.u64Limit)
    (targ : OracleTable (boundedQueries L) → Finset (InstalledIndexSampler.IndexSpace bits))
    (hinv : ∀ T ∈ A, ∀ m, m < 2 * bits → ∀ c ∈ tripleCounters (indexBlockBase m), ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = targ T)
    (bnd : Nat) (hbnd : ∀ T ∈ A, (targ T).card ≤ bnd) :
    (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).card
        * Fintype.card OuterChallenge.DigestTriple ^ (2 * bits)
      ≤ bnd * A.card := by
  have hfib1 : (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).card
      = ∑ S in A.image targ,
          ((A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).filter
            (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun x hx => Finset.mem_image_of_mem targ (Finset.mem_filter.mp hx).1)
  have hfib2 : A.card = ∑ S in A.image targ, (A.filter (fun T => targ T = S)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem targ hx)
  have key : ∀ S ∈ A.image targ,
      ((A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).filter
          (fun T => targ T = S)).card * Fintype.card OuterChallenge.DigestTriple ^ (2 * bits)
        ≤ bnd * (A.filter (fun T => targ T = S)).card := by
    intro S hS
    obtain ⟨T0, hT0A, hT0⟩ := Finset.mem_image.mp hS
    have hScard : S.card ≤ bnd := by
      rw [← hT0]
      exact hbnd T0 hT0A
    have hAS : ∀ m, m < 2 * bits →
        StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m))
          (A.filter (fun T => targ T = S)) := by
      intro m hm
      refine stage_stable_filter L hL e0 strat hb j (tripleCounters (indexBlockBase m)) A
        (hA m hm) (fun T => targ T = S) (fun T hT c hc b => ?_)
      show targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = S ↔ targ T = S
      rw [hinv T hT m hm c hc b]
    have hEq : (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).filter
          (fun T => targ T = S)
        = (A.filter (fun T => targ T = S)).filter
            (fun T => indexRead L hL e0 strat hb j bits T ∈ S) := by
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
    rw [hEq, idx_target_card L hL e0 strat hb j bits (A.filter (fun T => targ T = S)) hAS hnb S]
    exact Nat.mul_le_mul_right _ hScard
  calc (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).card
          * Fintype.card OuterChallenge.DigestTriple ^ (2 * bits)
      = ∑ S in A.image targ,
          ((A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).filter
            (fun T => targ T = S)).card * Fintype.card OuterChallenge.DigestTriple ^ (2 * bits) := by
        rw [hfib1, Finset.sum_mul]
    _ ≤ ∑ S in A.image targ, bnd * (A.filter (fun T => targ T = S)).card :=
        Finset.sum_le_sum key
    _ = bnd * A.card := by rw [← Finset.mul_sum, ← hfib2]

open Classical in
/-- (4) **THE DIAGONAL BOUND AS A MASS**, at a uniform `Nat` bound on the target's
size. -/
theorem idx_diagonal_mass_le (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (strat : Strategy)
    (hb : StrategyBounded L strat) (j bits : Nat) (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < 2 * bits →
      StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m)) A)
    (hnb : 6 * bits ≤ Transcript.u64Limit)
    (targ : OracleTable (boundedQueries L) → Finset (InstalledIndexSampler.IndexSpace bits))
    (hinv : ∀ T ∈ A, ∀ m, m < 2 * bits → ∀ c ∈ tripleCounters (indexBlockBase m), ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = targ T)
    (bnd : Nat) (hbnd : ∀ T ∈ A, (targ T).card ≤ bnd) :
    oracleProbability (boundedQueries L)
        (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T))
      ≤ (bnd : ℚ) / (Fintype.card (InstalledIndexSampler.IndexSpace bits) : ℚ) := by
  have hcard := idx_diagonal_card L hL e0 strat hb j bits A hA hnb targ hinv bnd hbnd
  have hAle : A.card ≤ Fintype.card (OracleTable (boundedQueries L)) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_univ A
  have hnat : (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).card
      * Fintype.card OuterChallenge.DigestTriple ^ (2 * bits)
      ≤ bnd * Fintype.card (OracleTable (boundedQueries L)) :=
    le_trans hcard (Nat.mul_le_mul_left bnd hAle)
  have hQ : ((A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)).card : ℚ)
      * ((Fintype.card OuterChallenge.DigestTriple : ℚ) ^ (2 * bits))
      ≤ (bnd : ℚ) * (Fintype.card (OracleTable (boundedQueries L)) : ℚ) := by
    exact_mod_cast hnat
  have hD : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) ^ (2 * bits) := by
    have h1 : (0 : ℚ) < (Fintype.card OuterChallenge.DigestTriple : ℚ) := by
      exact_mod_cast JointChallengeSpace.digest_triple_card_pos
    exact pow_pos h1 (2 * bits)
  rw [index_space_card_as_triples, Nat.cast_pow, oracleProbability,
    div_le_div_iff (oracle_card_cast_pos (boundedQueries L)) hD]
  exact hQ

open Classical in
/-- (4) **THE DIAGONAL BOUND AT A UNIFORM DENSITY.**  The form the index lanes
need: the target may move with the table, and what is known about it is not a
cardinality but a DENSITY -- the adopted `IndexPointZeroCheck.indexProbability` of
each of its values is at most `beta`.  The uniform `Nat` bound the count needs is
extracted from the finitely many values `targ` takes on `A`. -/
theorem idx_diagonal_mass_le_density (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j bits : Nat)
    (A : Finset (OracleTable (boundedQueries L)))
    (hA : ∀ m, m < 2 * bits →
      StageStable L hL e0 strat hb j (tripleCounters (indexBlockBase m)) A)
    (hnb : 6 * bits ≤ Transcript.u64Limit)
    (targ : OracleTable (boundedQueries L) → Finset (InstalledIndexSampler.IndexSpace bits))
    (hinv : ∀ T ∈ A, ∀ m, m < 2 * bits → ∀ c ∈ tripleCounters (indexBlockBase m), ∀ b : Block,
      targ (reassign T (challengeSel L hL e0 strat hb j c T) b) = targ T)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hdens : ∀ T ∈ A, IndexPointZeroCheck.indexProbability bits (targ T) ≤ beta) :
    oracleProbability (boundedQueries L)
        (A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T))
      ≤ beta := by
  rcases Finset.eq_empty_or_nonempty A with hAe | hAne
  · have hEmpty : A.filter (fun T => indexRead L hL e0 strat hb j bits T ∈ targ T)
        = (∅ : Finset (OracleTable (boundedQueries L))) := by
      rw [hAe, Finset.filter_empty]
    rw [hEmpty, oracle_probability_empty]
    exact hbeta
  · have himg : (A.image (fun T => (targ T).card)).Nonempty := hAne.image _
    have hmem : (A.image (fun T => (targ T).card)).max' himg
        ∈ A.image (fun T => (targ T).card) := Finset.max'_mem _ himg
    obtain ⟨T0, hT0A, hT0⟩ := Finset.mem_image.mp hmem
    have hbnd : ∀ T ∈ A, (targ T).card ≤ (A.image (fun T => (targ T).card)).max' himg :=
      fun T hT => Finset.le_max' (A.image (fun T => (targ T).card)) ((targ T).card)
        (Finset.mem_image_of_mem (fun T => (targ T).card) hT)
    have hmass := idx_diagonal_mass_le L hL e0 strat hb j bits A hA hnb targ hinv
      ((A.image (fun T => (targ T).card)).max' himg) hbnd
    have hval : (((A.image (fun T => (targ T).card)).max' himg : Nat) : ℚ)
        / (Fintype.card (InstalledIndexSampler.IndexSpace bits) : ℚ) ≤ beta := by
      have h0 := hdens T0 hT0A
      rw [IndexPointZeroCheck.indexProbability, hT0] at h0
      exact h0
    exact hmass.trans hval

/-! ## 5. THE EXTENDED STRATEGY: A HISTORY-DEPENDENT USED-CLAIMS CHOICE -/

/-- **A USED-CLAIMS CHOICE.**  The prover picks the claims it opens as a function
of the REDUCED round-challenge history of ALL `d` coupled rounds -- that is, after
seeing every round challenge, and before the index squeezes are taken.  It reads
NOTHING else: no raw block, no counter above `5`, no stage that is not a round
stage, and in particular no answer at the index digest itself. -/
def UsedClaimsStrategy : Type := List GoldilocksExt3Field.Element → Verifier.UsedClaims

/-- The width budget of a used-claims choice, quantified over EVERY history it
may see -- which is what adaptivity costs, exactly as the adopted
`StrategyChainBound.strategic_shape_bounded` quantifies the round messages. -/
def UsedClaimsBounded (W : Nat) (U : UsedClaimsStrategy) : Prop :=
  ∀ xs, (U xs).logPreprocessed.length ≤ W ∧ (U xs).logWitness.length ≤ W ∧
    (U xs).logNormInverse.length ≤ W ∧ (U xs).gatePreprocessed.length ≤ W ∧
    (U xs).gateWitness.length ≤ W

/-- **THE EXTENDED STRATEGIC SHAPE.**  The adopted
`OuterLaneTransport.strategyOfReduced` for the first `22 + 5 d` stages, and then
the EIGHT adopted `InstalledIndexSampler.claimFrames` of the claims the prover
chooses at the realized reduced history.  This is a
`StrategyChainBound.Strategy`, so every lemma of the adopted strategy-chain
machinery applies to it unchanged. -/
def extendedShape (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat) : Strategy :=
  fun k h ch =>
    if k < 22 + 5 * d then strategyOfReduced c s R k h ch
    else claimShapeAt (U (reducedHistory ch d)) (k - (22 + 5 * d))

theorem extended_shape_apply (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d k : Nat) (h : Nat → Transcript.Digest)
    (ch : Nat → Nat → Block) :
    extendedShape c s R U d k h ch
      = if k < 22 + 5 * d then strategyOfReduced c s R k h ch
        else claimShapeAt (U (reducedHistory ch d)) (k - (22 + 5 * d)) := rfl

theorem extended_shape_round (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d k : Nat) (hk : k < 22 + 5 * d) (h : Nat → Transcript.Digest)
    (ch : Nat → Nat → Block) :
    extendedShape c s R U d k h ch = strategyOfReduced c s R k h ch := if_pos hk

theorem extended_shape_claim (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d i : Nat) (h : Nat → Transcript.Digest)
    (ch : Nat → Nat → Block) :
    extendedShape c s R U d (22 + 5 * d + i) h ch
      = claimShapeAt (U (reducedHistory ch d)) i := by
  rw [extended_shape_apply, if_neg (by omega),
    show 22 + 5 * d + i - (22 + 5 * d) = i from by omega]

/-- (5) **THE LENGTH BUDGET OF THE EXTENDED PROVER, DISCHARGED.**  The first
`22 + 5 d` stages are the adopted
`OuterLaneTransport.strategy_of_reduced_bounded`; the last eight are the adopted
`IndexLanesOracle.claim_shape_payload_bound`, quantified over every history. -/
theorem extended_shape_bounded (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (R : ReducedStrategy) (U : UsedClaimsStrategy) (d q W : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hRlog : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).1.length ≤ 5)
    (hRgate : ∀ (r : Nat) (xs : List GoldilocksExt3Field.Element), (R r xs).2.length ≤ q + 2)
    (hU : UsedClaimsBounded W U) (hLq : 189 + 24 * q ≤ L) (hLW : 69 + 24 * W ≤ L)
    (hdom : 86 ≤ L) :
    StrategyBounded L (extendedShape c s R U d) := by
  intro k h ch
  rw [extended_shape_apply]
  by_cases hk : k < 22 + 5 * d
  · rw [if_pos hk]
    exact strategy_of_reduced_bounded L c s R q hpre hRlog hRgate hLq k h ch
  · rw [if_neg hk]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hU (reducedHistory ch d)
    exact claim_shape_payload_bound L W (U (reducedHistory ch d)) h1 h2 h3 h4 h5 hLW hdom
      (k - (22 + 5 * d))

/-- **THE USED CLAIMS THE EXTENDED PROVER REALLY PLAYS AT ONE TABLE**: its choice
at the reduced history the run's own round challenges make. -/
def realizedClaims (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d))
    (T : OracleTable (boundedQueries L)) : Verifier.UsedClaims :=
  U (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d)

/-- (5) **THE EIGHT FRAMES BEYOND THE ROUNDS ARE THE CLAIM FRAMES OF THE REALIZED
CLAIMS.**  At stage `22 + 5 d + i` the extended strategy plays the adopted
`IndexLanesOracle.claimShapeAt` of the claims it chose at the run's own reduced
history: the history it is handed there reads only the round stages, all of which
are at or below stage `22 + 5 d`. -/
theorem extended_strat_shape_is_claim_shape (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (T : OracleTable (boundedQueries L))
    (i : Nat) :
    stratShapeAt L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (22 + 5 * d + i) T
      = claimShapeAt (realizedClaims L hL c s R U d hb T) i := by
  show extendedShape c s R U d (22 + 5 * d + i)
      (stratHist L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (22 + 5 * d + i) T)
      (fun i2 cnt => challengeAt L hL T
        (stratHist L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (22 + 5 * d + i) T i2) cnt)
    = claimShapeAt (realizedClaims L hL c s R U d hb T) i
  rw [extended_shape_claim]
  refine congrArg (fun u => claimShapeAt u i) (congrArg U ?_)
  refine reduced_history_is_outer_history L hL OuterInitial.zeroDigest
    (extendedShape c s R U d) hb T _ d (fun i2 hi2 cnt => ?_)
  have hle : roundStage i2 ≤ 22 + 5 * d + i := by rw [roundStage]; omega
  rw [strat_hist_eq L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
    (22 + 5 * d + i) T (roundStage i2), Nat.min_eq_left hle]
  exact challenge_at_is_sel L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
    (roundStage i2) cnt T

/-! ## 6. THE EXTENDED CHAIN'S STAGE-`22 + 5 d + 8` DIGEST IS THE INDEX DIGEST -/

/-- (6) The extended chain, past the rounds, IS the adopted
`BirthdayClashBound.foldDigest` of the eight claim frames. -/
theorem extended_state_fold (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config) (s : Verifier.Statement)
    (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (T : OracleTable (boundedQueries L)) :
    ∀ j : Nat,
      strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (22 + 5 * d + j) T
        = foldDigest (hashOf (boundedQueries L) T)
            (strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              (22 + 5 * d) T)
            (claimShapeAt (realizedClaims L hL c s R U d hb T)) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j2 ih =>
      show strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (22 + 5 * d + j2 + 1) T = _
      rw [strategy_state_succ L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        (22 + 5 * d + j2) T]
      show blockDigest (T (strategySel L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (22 + 5 * d + j2) T))
        = (hashOf (boundedQueries L) T) (Transcript.frame
            (foldDigest (hashOf (boundedQueries L) T)
              (strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
                (22 + 5 * d) T)
              (claimShapeAt (realizedClaims L hL c s R U d hb T)) j2)
            (claimShapeAt (realizedClaims L hL c s R U d hb T) j2).1
            (claimShapeAt (realizedClaims L hL c s R U d hb T) j2).2)
      rw [← hash_of_at (boundedQueries L) T
        (strategySel L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (22 + 5 * d + j2) T)]
      show (hashOf (boundedQueries L) T) (Transcript.frame
          (strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
            (22 + 5 * d + j2) T)
          (stratShapeAt L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
            (22 + 5 * d + j2) T).1
          (stratShapeAt L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
            (22 + 5 * d + j2) T).2) = _
      rw [ih, extended_strat_shape_is_claim_shape L hL c s R U d hb T j2]

/-- (6) **THE HEADLINE IDENTIFICATION.**  The extended chain's digest after
`22 + 5 d + 8` stages IS the adopted `InstalledIndexSampler.indexDigest` at the
USED CLAIMS THE PROVER REALLY PLAYED -- the ones it chose after seeing all `d`
round challenges.  This is the adopted `IndexLanesOracle.index_state_is_index_digest`
for an ADAPTIVE prover: there the claims `u` are fixed data outside the table,
here they are a function OF the table through the realized round challenges.

The hypothesis `hst` is the same chain-model identification the adopted module
takes, and it is satisfiable by the chain's own state
(`extended_index_state_hypothesis_is_satisfiable`). -/
theorem extended_stage_is_index_digest (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (T : OracleTable (boundedQueries L))
    (st : Transcript.State)
    (hst : st.digest = strategyFrameState L hL OuterInitial.zeroDigest
      (extendedShape c s R U d) hb (22 + 5 * d) T) :
    strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        (indexStage d) T
      = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st
          (realizedClaims L hL c s R U d hb T) := by
  have hfold := extended_state_fold L hL c s R U d hb T 8
  have habs := fold_digest_absorb (hashOf (boundedQueries L) T)
    (InstalledIndexSampler.claimFrames (realizedClaims L hL c s R U d hb T))
    (strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (22 + 5 * d) T)
    (claimShapeAt (realizedClaims L hL c s R U d hb T)) (fun j _ => rfl)
  have hcf : (InstalledIndexSampler.claimFrames
      (realizedClaims L hL c s R U d hb T)).length = 8 := rfl
  rw [hcf] at habs
  have hstep : strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (indexStage d) T
      = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T)
          ⟨strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
            (22 + 5 * d) T, 0⟩ (realizedClaims L hL c s R U d hb T) := by
    show strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        (22 + 5 * d + 8) T = _
    rw [hfold, habs]
    rfl
  rw [hstep]
  exact index_digest_congr (hashOf (boundedQueries L) T) _ st
    (realizedClaims L hL c s R U d hb T) hst.symm

/-- (6) The chain-model hypothesis is satisfiable: the chain's own post-rounds
state is a snapshot with that digest. -/
theorem extended_index_state_hypothesis_is_satisfiable (L : Nat) (hL : 64 ≤ L)
    (c : Verifier.Config) (s : Verifier.Statement) (R : ReducedStrategy)
    (U : UsedClaimsStrategy) (d : Nat) (hb : StrategyBounded L (extendedShape c s R U d))
    (T : OracleTable (boundedQueries L)) :
    ∃ st : Transcript.State,
      st.digest = strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        (22 + 5 * d) T ∧
      strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (indexStage d) T
        = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st
            (realizedClaims L hL c s R U d hb T) :=
  ⟨⟨strategyFrameState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (22 + 5 * d) T, 0⟩, rfl,
    extended_stage_is_index_digest L hL c s R U d hb T _ rfl⟩

/-! ## 7. THE INVARIANCE: THE INDEX TARGET IS FIXED BEFORE THE INDEX SQUEEZES -/

/-- (7) **THE REDUCED HISTORY IS NOT MOVED BY A LATER STAGE'S CHALLENGE ANSWERS.**
Each of its entries is a digest triple at a ROUND stage, and the adopted
`OuterLaneTransport.stage_triple_reassign_lower` says a strictly earlier stage's
triples do not move when a later stage's challenge answer is overwritten. -/
theorem outer_history_reassign (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : Strategy) (hb : StrategyBounded L strat) (j cc : Nat)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ stageNoClash L hL e0 strat hb j) (b : Block) :
    ∀ r : Nat, (∀ i, i < r → roundStage i < j) →
      outerHistory L hL e0 strat hb (reassign T (challengeSel L hL e0 strat hb j cc T) b) r
        = outerHistory L hL e0 strat hb T r := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r2 ih =>
      intro hr
      have hlt : roundStage r2 < j := hr r2 (by omega)
      have hlog : logTriple L hL e0 strat hb r2
            (reassign T (challengeSel L hL e0 strat hb j cc T) b)
          = logTriple L hL e0 strat hb r2 T :=
        stage_triple_reassign_lower L hL e0 strat hb j cc (roundStage r2) 0 hlt T hT b
      have hgate : gateTriple L hL e0 strat hb r2
            (reassign T (challengeSel L hL e0 strat hb j cc T) b)
          = gateTriple L hL e0 strat hb r2 T :=
        stage_triple_reassign_lower L hL e0 strat hb j cc (roundStage r2) 3 hlt T hT b
      rw [outer_history_succ, outer_history_succ, ih (fun i hi => hr i (by omega)), hlog, hgate]

/-- (7) The same at the index stage, for the whole `d`-round history. -/
theorem realized_history_reassign (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d cc : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (indexStage d)) (b : Block) :
    outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        (reassign T (challengeSel L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (indexStage d) cc T) b) d
      = outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d :=
  outer_history_reassign L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
    (indexStage d) cc T hT b d (fun i hi => round_stage_lt_index_stage i d hi)

/-- (7) Hence the realized USED CLAIMS are not moved either: the prover has
committed to them before the index digest's own challenges are squeezed. -/
theorem realized_claims_reassign (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d cc : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (T : OracleTable (boundedQueries L))
    (hT : T ∈ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (indexStage d)) (b : Block) :
    realizedClaims L hL c s R U d hb
        (reassign T (challengeSel L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (indexStage d) cc T) b)
      = realizedClaims L hL c s R U d hb T :=
  congrArg U (realized_history_reassign L hL c s R U d cc hb T hT b)

/-! ### 7.1 The two cell families of the index bad set -/

/-- The five SUPPLIED cell families of a used-claims record, in the adopted
`OpenedClaimFold.boundCell` order. -/
def usedCell (u : Verifier.UsedClaims) : Fin 5 → List Verifier.Ext3
  | 0 => u.logPreprocessed
  | 1 => u.logWitness
  | 2 => u.logNormInverse
  | 3 => u.gatePreprocessed
  | 4 => u.gateWitness

/-- (7) **THE SUPPLIED CELLS ARE A PROJECTION OF THE USED CLAIMS ALONE.**  The
adopted `OpenedClaimFold.boundCell`'s FIRST component -- the family the adopted
`SoundnessAssembly.indexBadEvent` calls `suppliedCells` -- does not read the index
points at all.  So a used-claims choice determines it. -/
theorem used_cell_is_bound_cell (u : Verifier.UsedClaims) (idx : Verifier.IndexPoints)
    (i : Fin 5) : (OpenedClaimFold.boundCell u idx i).1 = usedCell u i := by
  fin_cases i <;> rfl

/-- **THE INDEX BAD SET THE RUN'S OWN HISTORY PICKS OUT.**  The adopted
`IndexLanesOracle.guardedIndexBadEvent` -- which is the adopted
`SoundnessAssembly.indexBadEvent`, guard for guard -- at the supplied cells the
prover's used-claims choice determines and at a committed family `committed`,
both read off the REDUCED ROUND-CHALLENGE HISTORY and nothing else. -/
noncomputable def indexBadTarget (bits : Nat) (U : UsedClaimsStrategy) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (xs : List GoldilocksExt3Field.Element) :
    Finset (InstalledIndexSampler.IndexSpace bits) :=
  guardedIndexBadEvent bits (OpenedClaimFold.lift (usedCell (U xs) cellIndex)) (committed xs)

open Classical in
/-- **THE INDEX BAD EVENT ON THE ORACLE TABLE**, at the realized claims.  Unlike
the adopted `ReducedFullTransport` gate lanes this target is NOT fixed data: it
moves with the table, through the realized reduced history.  `Finset.univ` here is
this module's own (see HONESTY (viii)). -/
noncomputable def indexBadEvent (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    indexRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d) bits T
      ∈ indexBadTarget bits U cellIndex committed
          (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d))

open Classical in
theorem mem_index_bad_event (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ indexBadEvent L hL c s R U d bits hb cellIndex committed ↔
      indexRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d) bits T
        ∈ indexBadTarget bits U cellIndex committed
            (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d) := by
  rw [indexBadEvent, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

open Classical in
/-- (7) **THE INDEX-LANE MASS FOR THE REDUCED ADAPTIVE PROVER.**  Conditioned on
the extended chain's own no-clash event at stage `22 + 5 d + 8`, the mass of the
event that the realized index draw lands in the bad set THE RUN'S OWN HISTORY
picked out is at most `2 * ChallengeUnionBound.tauTerm indexBits` -- exactly the
constant the adopted `IndexLanesOracle.guarded_index_bad_event_mass_le` gets for a
FIXED proof record.

This is the diagonal step the adopted `ReducedFullTransport` HONESTY (iii) says is
missing: the target moves with the table, and what makes the count go through is
`realized_claims_reassign` -- the claims and the row point are settled before the
index digest's own challenge cells are read. -/
theorem index_bad_no_clash_mass_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (hbu : 6 * bits ≤ Transcript.u64Limit) :
    oracleProbability (boundedQueries L)
        ((stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
            (indexStage d)).filter (fun T =>
          indexRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              (indexStage d) bits T
            ∈ indexBadTarget bits U cellIndex committed
                (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d)))
      ≤ 2 * ChallengeUnionBound.tauTerm bits := by
  refine idx_diagonal_mass_le_density L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
    (indexStage d) bits
    (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
    (fun m _ => stage_stable_no_clash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (indexStage d) (tripleCounters (indexBlockBase m))) hbu
    (fun T => indexBadTarget bits U cellIndex committed
      (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d))
    (fun T hT m _ cc _ b => ?_) (2 * ChallengeUnionBound.tauTerm bits) ?_ (fun T _ => ?_)
  · exact congrArg (indexBadTarget bits U cellIndex committed)
      (realized_history_reassign L hL c s R U d cc hb T hT b)
  · have h := tau_term_nonneg bits
    linarith
  · exact guarded_index_bad_event_mass_le bits
      (OpenedClaimFold.lift (usedCell (U (outerHistory L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hb T d)) cellIndex))
      (committed (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d))

/-! ## 8. THE UNION: THE FULL `combinedBound` PLUS THE INDEX TERM -/

open Classical in
/-- **THE FULL BAD EVENT WITH THE INDEX LANES INCLUDED**: the adopted
`ReducedFullTransport.fullBadEvent` -- some coupled round of either OUTER lane
agrees, or the gate tau column lands in the adopted zero-check bad set, or the
gate alpha lands in the adopted row union -- OR the realized index draw lands in
the bad set the run's own history picked out. -/
noncomputable def fullIndexBadEvent (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (logLane gateLane : Lane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element) :
    Finset (OracleTable (boundedQueries L)) :=
  ReducedFullTransport.fullBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      logLane gateLane d rows g coeffsOf
    ∪ indexBadEvent L hL c s R U d bits hb cellIndex committed

open Classical in
theorem mem_full_index_bad_event (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (logLane gateLane : Lane)
    (rows : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (T : OracleTable (boundedQueries L)) :
    T ∈ fullIndexBadEvent L hL c s R U d bits hb logLane gateLane rows g coeffsOf cellIndex
        committed ↔
      (T ∈ ReducedFullTransport.fullBadEvent L hL OuterInitial.zeroDigest
          (extendedShape c s R U d) hb logLane gateLane d rows g coeffsOf ∨
        T ∈ indexBadEvent L hL c s R U d bits hb cellIndex committed) := by
  rw [fullIndexBadEvent, Finset.mem_union]

open Classical in
/-- (8) **THE FULL BOUND, WITH THE INDEX LANES.**  The four masses are conditioned
on the SAME no-clash event, that of the chain at its full `22 + 5 d + 8` stages;
the adopted `OuterLaneTransport.stage_no_clash_mono` puts it inside the block-`0`
one, so ONE complement term pays for all four.  The constant is the WHOLE adopted
`ChallengeUnionBound.combinedBound d q d constraints`, plus
`2 * ChallengeUnionBound.tauTerm indexBits`, plus that one clash term.

READ HONESTY (v): THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem full_index_bad_draw_probability_le (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (logLane gateLane : Lane)
    (q rows constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * bits ≤ Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < rows → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (fullIndexBadEvent L hL c s R U d bits hb logLane gateLane rows g coeffsOf cellIndex
          committed)
      ≤ ChallengeUnionBound.outerTerm d q + ChallengeUnionBound.tauTerm d
        + ChallengeUnionBound.alphaTerm rows constraints
        + 2 * ChallengeUnionBound.tauTerm bits
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have hnest : stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        (indexStage d)
      ⊆ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        ReducedFullTransport.deriveStage :=
    stage_no_clash_mono L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      ReducedFullTransport.deriveStage (indexStage d)
      (le_of_lt (derive_stage_lt_index_stage d))
  have hmono := oracle_probability_mono (boundedQueries L) _ _
    (subset_inter_union_compl
      (fullIndexBadEvent L hL c s R U d bits hb logLane gateLane rows g coeffsOf cellIndex
        committed)
      (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d)))
  have hu1 := oracle_probability_union_le (boundedQueries L)
    (fullIndexBadEvent L hL c s R U d bits hb logLane gateLane rows g coeffsOf cellIndex committed
      ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
    ((stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))ᶜ)
  have hsplit : fullIndexBadEvent L hL c s R U d bits hb logLane gateLane rows g coeffsOf
          cellIndex committed
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d)
      = (((outerLaneBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              logLane gateLane d
            ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              (indexStage d))
          ∪ (ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
              (extendedShape c s R U d) hb d g
            ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              (indexStage d)))
        ∪ (ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
              (extendedShape c s R U d) hb d rows coeffsOf
            ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              (indexStage d)))
        ∪ (indexBadEvent L hL c s R U d bits hb cellIndex committed
            ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              (indexStage d)) := by
    rw [fullIndexBadEvent, ReducedFullTransport.fullBadEvent,
      Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
      Finset.union_inter_distrib_right]
  have hu2 : oracleProbability (boundedQueries L)
        (fullIndexBadEvent L hL c s R U d bits hb logLane gateLane rows g coeffsOf cellIndex
            committed
          ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
      ≤ oracleProbability (boundedQueries L)
          (((outerLaneBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
                logLane gateLane d
              ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
                (indexStage d))
            ∪ (ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
                (extendedShape c s R U d) hb d g
              ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
                (indexStage d)))
          ∪ (ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
                (extendedShape c s R U d) hb d rows coeffsOf
              ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
                (indexStage d)))
        + oracleProbability (boundedQueries L)
            (indexBadEvent L hL c s R U d bits hb cellIndex committed
              ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
                (indexStage d)) := by
    rw [hsplit]
    exact oracle_probability_union_le (boundedQueries L) _ _
  have hu3 := oracle_probability_union_le (boundedQueries L)
    ((outerLaneBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        logLane gateLane d
      ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
      ∪ (ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
          (extendedShape c s R U d) hb d g
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d)))
    (ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hb d rows coeffsOf
      ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
  have hu4 := oracle_probability_union_le (boundedQueries L)
    (outerLaneBadEvent L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        logLane gateLane d
      ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
    (ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hb d g
      ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
  have houter := outer_no_clash_mass_le L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
    logLane gateLane 5 (q + 2) hlog hgate (indexStage d) d
    (fun r hr => le_of_lt (round_stage_lt_index_stage r d hr))
  rw [round_terms_sum d q] at houter
  have htausub : ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hb d g
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d)
      ⊆ (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          ReducedFullTransport.deriveStage).filter (fun T =>
          ReducedFullTransport.tauRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              d T
            ∈ ChallengeUnionBound.productEvent d (ZeroCheckSemantics.zeroCheckBadSet d g)) := by
    rw [ReducedFullTransport.gateTauBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have htau : oracleProbability (boundedQueries L)
      (ReducedFullTransport.gateTauBadEvent L hL OuterInitial.zeroDigest
          (extendedShape c s R U d) hb d g
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
      ≤ ChallengeUnionBound.tauTerm d :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ htausub)
      (ReducedFullTransport.gate_tau_no_clash_mass_le L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hb d g hdu)
  have halphasub : ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hb d rows coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d)
      ⊆ (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          ReducedFullTransport.deriveStage).filter (fun T =>
          stageTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              ReducedFullTransport.deriveStage (ReducedFullTransport.alphaBase d) T
            ∈ OuterChallenge.tupleEvent
                (ChallengeUnionBound.alphaUnionBadSet rows coeffsOf)) := by
    rw [ReducedFullTransport.gateAlphaBadEvent]
    exact univ_filter_inter_subset _ _ _ hnest
  have halpha : oracleProbability (boundedQueries L)
      (ReducedFullTransport.gateAlphaBadEvent L hL OuterInitial.zeroDigest
          (extendedShape c s R U d) hb d rows coeffsOf
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
      ≤ ChallengeUnionBound.alphaTerm rows constraints :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ halphasub)
      (ReducedFullTransport.gate_alpha_no_clash_mass_le L hL OuterInitial.zeroDigest
        (extendedShape c s R U d) hb d rows constraints coeffsOf hdu hclen)
  have hidxsub : indexBadEvent L hL c s R U d bits hb cellIndex committed
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d)
      ⊆ (stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
          (indexStage d)).filter (fun T =>
          indexRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
              (indexStage d) bits T
            ∈ indexBadTarget bits U cellIndex committed
                (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d)) := by
    rw [indexBadEvent]
    exact univ_filter_inter_subset _ _ _ (fun T hT => hT)
  have hidx : oracleProbability (boundedQueries L)
      (indexBadEvent L hL c s R U d bits hb cellIndex committed
        ∩ stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))
      ≤ 2 * ChallengeUnionBound.tauTerm bits :=
    le_trans (oracle_probability_mono (boundedQueries L) _ _ hidxsub)
      (index_bad_no_clash_mass_le L hL c s R U d bits hb cellIndex committed hbu)
  have hclash : oracleProbability (boundedQueries L)
      ((stageNoClash L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d))ᶜ)
      ≤ ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
    strategy_chain_clash_probability_le L hL OuterInitial.zeroDigest
      (extendedShape c s R U d) hb (indexStage d)
  linarith

open Classical in
/-- (8) **THE SAME, WITH THE CONSTANT READ OFF AS THE ADOPTED `combinedBound`
PLUS THE INDEX TERM.**  At `rows = 2 ^ degreeBits` the first three summands ARE
`ChallengeUnionBound.combinedBound degreeBits quotientDegree degreeBits
constraints`, term for term. -/
theorem full_index_bad_draw_probability_le_combined (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (logLane gateLane : Lane)
    (q constraints : Nat) (g : Nat → Element) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hbu : 6 * bits ≤ Transcript.u64Limit)
    (hlog : logLane.Bounded 5) (hgate : gateLane.Bounded (q + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (fullIndexBadEvent L hL c s R U d bits hb logLane gateLane (2 ^ d) g coeffsOf cellIndex
          committed)
      ≤ ChallengeUnionBound.combinedBound d q d constraints
        + 2 * ChallengeUnionBound.tauTerm bits
        + ((indexStage d : Nat) : ℚ) * (((indexStage d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := full_index_bad_draw_probability_le L hL c s R U d bits hb logLane gateLane q (2 ^ d)
    constraints g coeffsOf cellIndex committed hdu hbu hlog hgate hclen
  rw [ChallengeUnionBound.combinedBound]
  exact h

/-! ## 9. THE OUTER PAIRING AT THE EXTENDED PROVER -/

/-- (9) **THE LOG LANE'S ROUND-`r` MESSAGE IS THE EXTENDED PROVER'S REALIZED
ROUND-`r` LOG MESSAGE.**  The adopted
`OuterLaneTransport.log_lane_of_reduced_message_is_realized`, at the EXTENDED
strategy: the eight claim frames sit strictly after every round stage, so the
pairing the adopted section 8 proves is untouched by them. -/
theorem extended_log_lane_message_is_realized (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element)
    (hb : StrategyBounded L (extendedShape c s R U d)) (gateLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    (outerState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        (logLaneOfReduced R tr a b) gateLane T r).1.message []
      = (R r (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r)).1.map
          OuterRound.lift := by
  have hlen := outer_history_length L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r
  have hstate := (outer_state_message L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
    (logLaneOfReduced R tr a b) gateLane T r []).1
  rw [hstate, List.append_nil]
  show ((R ((outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r).length / 2)
      ((outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r).take
        (2 * ((outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r).length
          / 2)))).1.map OuterRound.lift)
    = (R r (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r)).1.map
        OuterRound.lift
  rw [hlen, Nat.mul_div_cancel_left r (by omega), ← hlen, take_own_length]

/-- (9) **AND THE GATE LANE'S**, at the state the adopted
`OuterLaneTransport.gateTarget` reads it from: after the round's own LOG triple
has been absorbed. -/
theorem extended_gate_lane_message_is_realized (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (tr : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a b : GoldilocksExt3Field.Element)
    (hb : StrategyBounded L (extendedShape c s R U d)) (logLane : Lane) (r : Nat)
    (T : OracleTable (boundedQueries L)) :
    (laneStep (outerState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
        logLane (gateLaneOfReduced R tr a b) T r).2
      (logTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb r T)).message []
      = (R r (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r)).2.map
          OuterRound.lift := by
  have hlen := outer_history_length L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r
  have hstate := (outer_state_message L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
    logLane (gateLaneOfReduced R tr a b) T r
    [OuterChallenge.reduceTriple
      (logTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb r T)]).2
  show (outerState L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      logLane (gateLaneOfReduced R tr a b) T r).2.message
      [OuterChallenge.reduceTriple
        (logTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb r T)]
    = (R r (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r)).2.map
        OuterRound.lift
  rw [hstate]
  have hlen2 : (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r
      ++ [OuterChallenge.reduceTriple
        (logTriple L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb r T)]).length
      = 2 * r + 1 := by
    rw [List.length_append, hlen]
    rfl
  show ((R (( _ : List GoldilocksExt3Field.Element).length / 2) _).2.map OuterRound.lift) = _
  rw [hlen2, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  rw [show 2 * r
      = (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T r).length
      from hlen.symm, take_length_append]

/-- (9) The length of the history the used-claims choice is handed: `2 d`, the
whole reduced round-challenge history. -/
theorem realized_history_length (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (T : OracleTable (boundedQueries L)) :
    (outerHistory L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d).length
      = 2 * d :=
  outer_history_length L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb T d

/-! ### 9.1 The guard bites -/

/-- (9) On the branch where the supplied and committed families DIFFER on the
index cube the target is the plain union of the two adopted per-lane agreement
pullbacks: the bound is not a bound on the empty set by fiat. -/
theorem index_bad_target_of_differ (bits : Nat) (U : UsedClaimsStrategy) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (xs : List GoldilocksExt3Field.Element)
    (h : IndexPointZeroCheck.CellsDifferOnCube bits
      (OpenedClaimFold.lift (usedCell (U xs) cellIndex)) (committed xs)) :
    indexBadTarget bits U cellIndex committed xs
      = IndexPointZeroCheck.logAgreementEvent bits
          (OpenedClaimFold.lift (usedCell (U xs) cellIndex)) (committed xs)
        ∪ IndexPointZeroCheck.gateAgreementEvent bits
          (OpenedClaimFold.lift (usedCell (U xs) cellIndex)) (committed xs) :=
  guarded_index_bad_event_of_differ bits _ _ h

/-- (9) And on the branch where the prover supplies exactly the committed family
the target is EMPTY -- the adopted guard, which is what stops the unguarded union
from being the whole index space. -/
theorem index_bad_target_at_honest_cells (bits : Nat) (U : UsedClaimsStrategy)
    (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (xs : List GoldilocksExt3Field.Element)
    (h : committed xs = OpenedClaimFold.lift (usedCell (U xs) cellIndex)) :
    indexBadTarget bits U cellIndex committed xs = ∅ := by
  rw [indexBadTarget, h]
  exact guarded_index_bad_event_of_equal_cells bits _

/-! ## 10. THE CLOSED INSTANCE AT THIRTEEN ROUNDS AND EIGHT INDEX BITS -/

theorem eight_index_counter_budget : 6 * 8 ≤ Transcript.u64Limit := by
  rw [Transcript.u64Limit]
  omega

theorem index_stage_thirteen : indexStage 13 = 95 := rfl

/-- (10) `4560 * 2 ^ 243` fits inside the block space: `4560 < 2 ^ 13` and
`|Block| = 256 ^ 32 = 2 ^ 256` by the adopted `RandomOracleSqueezes.block_card`.
The cardinal is never evaluated -- only `Nat` power laws are used. -/
theorem block_card_ge_index_birthday_scale : 4560 * 2 ^ 243 ≤ Fintype.card Block := by
  have hb : (256 : Nat) = 2 ^ 8 := by norm_num
  have hp : (256 : Nat) ^ 32 = 2 ^ 256 := by
    conv_lhs => rw [hb]
    rw [← pow_mul]
  rw [block_card, hp]
  calc (4560 : Nat) * 2 ^ 243 ≤ 2 ^ 13 * 2 ^ 243 := Nat.mul_le_mul (by norm_num) (Nat.le_refl _)
    _ = 2 ^ 256 := by rw [← pow_add]

/-- (10) **THE EXTENDED CHAIN'S BIRTHDAY TERM, SYMBOLICALLY**: `4560 / |Block|`,
the adopted `IndexLanesOracle.extended_digest_clash_mass_at_thirteen` constant, is
at most `2 ^ (-243)`.  NOT a claim about keccak. -/
theorem index_birthday_term_le_two_pow_neg :
    (4560 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 243 := by
  rw [div_le_div_iff block_card_cast_pos (by positivity), one_mul]
  exact_mod_cast block_card_ge_index_birthday_scale

/-- (10) **THE INDEX TERM AT EIGHT INDEX BITS, EVALUATED.**  Exact rational
arithmetic on the adopted `ChallengeUnionBound.tau_term_explicit` -- no `decide`,
no floating point.  READ HONESTY (v): `2 ^ (-185)` IS NOT A SOUNDNESS ERROR. -/
theorem index_term_at_eight_numeric :
    2 * ChallengeUnionBound.tauTerm 8 ≤ (1 : ℚ) / 2 ^ 185 := by
  rw [ChallengeUnionBound.tau_term_explicit]
  norm_num [Arithmetic.modulus]

/-- **A NON-TRIVIAL USED-CLAIMS CHOICE**: the prover opens `u0` or `u1` according
to the OLDEST reduced round challenge it saw.  This is a genuine function of the
history, not a constant, and `history_claims_depends` exhibits its dependence at a
history of the length the run really hands it. -/
def historyClaims (u0 u1 : Verifier.UsedClaims) : UsedClaimsStrategy :=
  fun xs => if xs.headD 0 = 0 then u0 else u1

theorem history_claims_bounded (u0 u1 : Verifier.UsedClaims) (W : Nat)
    (h0 : u0.logPreprocessed.length ≤ W ∧ u0.logWitness.length ≤ W ∧
      u0.logNormInverse.length ≤ W ∧ u0.gatePreprocessed.length ≤ W ∧
      u0.gateWitness.length ≤ W)
    (h1 : u1.logPreprocessed.length ≤ W ∧ u1.logWitness.length ≤ W ∧
      u1.logNormInverse.length ≤ W ∧ u1.gatePreprocessed.length ≤ W ∧
      u1.gateWitness.length ≤ W) :
    UsedClaimsBounded W (historyClaims u0 u1) := by
  intro xs
  by_cases h : xs.headD 0 = (0 : GoldilocksExt3Field.Element)
  · have hs : historyClaims u0 u1 xs = u0 := by
      show (if xs.headD 0 = 0 then u0 else u1) = u0
      rw [if_pos h]
    rw [hs]
    exact h0
  · have hs : historyClaims u0 u1 xs = u1 := by
      show (if xs.headD 0 = 0 then u0 else u1) = u1
      rw [if_neg h]
    rw [hs]
    exact h1

/-- (10) **THE USED-CLAIMS CHOICE IS NON-CONSTANT ON THE HISTORIES IT IS REALLY
HANDED.**  `realized_history_length` says that history has `2 d` entries; at
`d = 13` the two witnesses below have exactly `26`. -/
theorem history_claims_depends (u0 u1 : Verifier.UsedClaims) (hne : u0 ≠ u1)
    (y : GoldilocksExt3Field.Element) :
    (((0 : GoldilocksExt3Field.Element) :: List.replicate 25 y).length = 2 * 13) ∧
      historyClaims u0 u1 ((0 : GoldilocksExt3Field.Element) :: List.replicate 25 y)
        ≠ historyClaims u0 u1 ((1 : GoldilocksExt3Field.Element) :: List.replicate 25 y) := by
  refine ⟨?_, ?_⟩
  · rw [List.length_cons, List.length_replicate]
  · have hz0 : (((0 : GoldilocksExt3Field.Element) :: List.replicate 25 y).headD 0) = 0 := rfl
    have hz1 : ¬ ((((1 : GoldilocksExt3Field.Element) :: List.replicate 25 y).headD 0) = 0) := by
      intro hz
      exact zero_ne_one (show (0 : GoldilocksExt3Field.Element) = 1 from hz.symm)
    show (if (((0 : GoldilocksExt3Field.Element) :: List.replicate 25 y).headD 0) = 0 then u0
        else u1)
      ≠ (if (((1 : GoldilocksExt3Field.Element) :: List.replicate 25 y).headD 0) = 0 then u0
        else u1)
    rw [if_pos hz0, if_neg hz1]
    exact hne

open Classical in
/-- (10) **THE CLOSED INSTANCE**: thirteen coupled rounds, `quotientDegree = 8`,
`numGateConstraints = 123`, `indexBits = 8`, the adopted non-trivial
`OuterLaneTransport.previousChallengeMessage` as the round-message choice and an
arbitrary used-claims choice `U`.  Neither the counter budget of the block-`0`
lanes nor that of the index lanes is left as a hypothesis.

  `<= combinedBound 13 8 13 123 + 2 * tauTerm 8 + 4560 / |Block|`.

READ HONESTY (v): THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR. -/
theorem full_index_bound_at_thirteen (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (m : Verifier.CoupledMessage) (U : UsedClaimsStrategy) (W : Nat)
    (trlog trgate : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (a1 b1 a2 b2 : GoldilocksExt3Field.Element) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (committed : List GoldilocksExt3Field.Element → List GoldilocksExt3Field.Element)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hmlog : m.1.length ≤ 5) (hmgate : m.2.length ≤ 8 + 2)
    (htrlog : ∀ xs, (trlog xs).length ≤ 5) (htrgate : ∀ xs, (trgate xs).length ≤ 8 + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123)
    (hU : UsedClaimsBounded W U) (hLq : 189 + 24 * 8 ≤ L) (hLW : 69 + 24 * W ≤ L)
    (hdom : 86 ≤ L) :
    oracleProbability (boundedQueries L)
        (fullIndexBadEvent L (Nat.le_trans (by omega) hLq) c s (previousChallengeMessage m) U
          13 8
          (extended_shape_bounded L c s (previousChallengeMessage m) U 13 8 W hpre
            (previous_challenge_message_log_length m 5 hmlog)
            (previous_challenge_message_gate_length m (8 + 2) hmgate) hU hLq hLW hdom)
          (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
          (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
          (2 ^ 13) g coeffsOf cellIndex committed)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + 2 * ChallengeUnionBound.tauTerm 8 + 4560 / (Fintype.card Block : ℚ) := by
  have h := full_index_bad_draw_probability_le_combined L (Nat.le_trans (by omega) hLq) c s
    (previousChallengeMessage m) U 13 8
    (extended_shape_bounded L c s (previousChallengeMessage m) U 13 8 W hpre
      (previous_challenge_message_log_length m 5 hmlog)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) hU hLq hLW hdom)
    (logLaneOfReduced (previousChallengeMessage m) trlog a1 b1)
    (gateLaneOfReduced (previousChallengeMessage m) trgate a2 b2)
    8 123 g coeffsOf cellIndex committed ReducedFullTransport.thirteen_counter_budget
    eight_index_counter_budget
    (log_lane_of_reduced_bounded (previousChallengeMessage m) trlog a1 b1 5
      (previous_challenge_message_log_length m 5 hmlog) htrlog)
    (gate_lane_of_reduced_bounded (previousChallengeMessage m) trgate a2 b2 (8 + 2)
      (previous_challenge_message_gate_length m (8 + 2) hmgate) htrgate) hclen
  have harith : ((indexStage 13 : Nat) : ℚ) * (((indexStage 13 : Nat) : ℚ) + 1) / 2
      = 4560 := by
    rw [index_stage_thirteen]
    norm_num
  rw [harith] at h
  exact h

/-- (10) **AND THE CLOSED CONSTANT IS STRICTLY BELOW `1`.**  The adopted
`ChallengeUnionBound.combined_bound_at_extremes_numeric` puts the three-term
envelope at most `2 ^ (-172)`, `index_term_at_eight_numeric` puts the index term
at most `2 ^ (-185)` and `index_birthday_term_le_two_pow_neg` puts the extended
chain's clash term at most `2 ^ (-243)`.  `Fintype.card Block` is never evaluated:
it enters only through the named lemma.  READ HONESTY (v). -/
theorem full_index_bound_at_thirteen_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) < 1 := by
  have h1 : ChallengeUnionBound.combinedBound 13 8 13 123 ≤ (1 : ℚ) / 2 ^ 172 :=
    ChallengeUnionBound.combined_bound_at_extremes_numeric
  have h2 : 2 * ChallengeUnionBound.tauTerm 8 ≤ (1 : ℚ) / 2 ^ 185 := index_term_at_eight_numeric
  have h3 : (4560 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 243 :=
    index_birthday_term_le_two_pow_neg
  have h4 : (1 : ℚ) / 2 ^ 172 + 1 / 2 ^ 185 + 1 / 2 ^ 243 < 1 := by norm_num
  linarith

/-! ## 11. THE COLUMN READ IS THE ADOPTED SAMPLER'S OWN DRAW -/

/-- (11) **THE INDEX COLUMN THE EXTENDED CHAIN READS IS THE ADOPTED
`InstalledIndexSampler.actualIndexDraw`**, at the index digest of the claims the
prover really played.  Nothing is re-modelled: the table's three answers at the
adopted `InstalledIndexSampler.indexCounter` block of the stage-`22 + 5 d + 8`
digest ARE the three block digests the installed sampler squeezes, by the adopted
`OuterLaneTransport.stage_triple_is_actual_digests` and section 6's digest
identification. -/
theorem index_read_is_actual_index_draw (L : Nat) (hL : 64 ≤ L) (c : Verifier.Config)
    (s : Verifier.Statement) (R : ReducedStrategy) (U : UsedClaimsStrategy) (d bits : Nat)
    (hb : StrategyBounded L (extendedShape c s R U d)) (T : OracleTable (boundedQueries L))
    (st : Transcript.State)
    (hst : st.digest = strategyFrameState L hL OuterInitial.zeroDigest
      (extendedShape c s R U d) hb (22 + 5 * d) T) :
    indexRead L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb (indexStage d) bits T
      = InstalledIndexSampler.actualIndexDraw (hashOf (boundedQueries L) T)
          (InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st
            (realizedClaims L hL c s R U d hb T)) bits := by
  funext k
  rw [index_read_at_counter L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (indexStage d) bits T k,
    stage_triple_is_actual_digests L hL OuterInitial.zeroDigest (extendedShape c s R U d) hb
      (indexStage d) (InstalledIndexSampler.indexCounter bits k) T,
    extended_stage_is_index_digest L hL c s R U d hb T st hst]
  rfl

end Audit.Wire3.ReducedIndexLanes
