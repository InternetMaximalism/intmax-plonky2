import Audit.Wire3.TwoStageConditionalCount

/-!
# `Audit.Wire3.IndexStageFinerSplit` -- the finer table split, and the index stage

**WHAT THIS MODULE ADDS.**  `Audit.Wire3.TwoStageConditionalCount` (TSCC)
discharges the OUTER stage of `Audit.Wire3.RunLevelUnionBound`'s (RLUB) two-stage
contract and carries the INDEX stage as the named hypothesis `RowPointFixed`,
whose scope is narrow by construction: it can hold only where every committed
column's multilinear extension is CONSTANT along the realized row points.  TSCC's
HONESTY (6) states the missing step as a THREE-STEP CONTRACT -- the finer split of
the oracle table, the two-group count at RLUB's combined selector, and the frame
fibre Fubini around it.  **This module builds all three and ELIMINATES THE
`RowPointFixed` HYPOTHESIS BY COUNTING.**  The predicate `RowPointFixed` is NOT
proved -- it is FALSE at a non-constant committed column -- and nothing below
claims it; what is removed is the need to assume it.

* **The split (sections 1-3).**  `frame_fibre_card` is the frame-fibre peel with
  BOTH the table event and its fibres abstract.  `run_index_diagonal_fibre_count_le`
  is the diagonal analogue of RLUB's `run_index_fibre_count`: on a fibre where
  RLUB's `runCombinedSchedule` is injective -- off `runCombinedNonInjectiveEvent`,
  by `run_combined_schedule_injective_off_clash` -- the outer cells `K1` and the
  index cells `K2` are DISJOINT, so the adopted `RandomOracleSqueezes.restrict_ratio`
  at the COMBINED selector `Sum.elim selJ selI` makes the pair (outer draw, index
  draw) jointly uniform on `K1 ⊕ K2 → Block`, and TSCC's
  `product_diagonal_card_le` counts the diagonal group by group.
  `run_union_diagonal_probability_le_fibrewise` runs the Fubini around it:
  RLUB's own fibrewise bound with the index half allowed to depend on the run's
  OWN outer draw, at the SAME single additive chain term.
* **The index stage (sections 4-5).**  `rowPointOf` reads the row point off a
  point of the joint space through TSCC's `rowCoord`; `cell_row_is_row_point_of`
  identifies it with the engine's row point at every hash (TSCC's
  `row_point_is_outer_draw_function`, assembled); `index_bad_event_at_is_index_bad_at`
  turns the engine's whole hash-indexed index family into `indexBadAt` at the
  run's own outer draw, and `index_bad_at_mass_le` weighs EVERY member of that
  family by `2 * ChallengeUnionBound.tauTerm c.indexBits` through the adopted
  `IndexLanesOracle.guarded_index_bad_event_mass_le`.  `run_index_stage_mass_le`
  is the headline: the mass of the tables whose own index draw lands in the
  engine's own index bad event -- committed cells evaluated at the row point the
  table's own outer draw determines -- is at most `2 * tauTerm c.indexBits` plus
  ILO's one chain-clash term.  **No `RowPointFixed`.**
* **The payoff (sections 6-7).**  `assembly_failure_mass_le_unconditional` and its
  birthday and `degreeBits = 13` forms carry NO `RowPointFixed` and NO constraint
  on the committed columns `cols` at all, and section 7 discharges every
  hypothesis at TSCC's `liveProof` -- RLUB's closed witness with one NON-ZERO used
  cell per bound cell -- with the right-hand side below `1` and a table on which
  the assembly does not fail.  The guard is live along the WHOLE diagonal at one
  constant committed column (`live_index_guard_is_live_at_every_outer_draw`), so
  the index half is not killed by its guard there.

## HONESTY -- read before quoting anything below

1. **RANDOM ORACLE MODEL, NOT KECCAK.**  The law is the uniform counting measure
   on `RandomOracleSqueezes.OracleTable (BirthdayClashBound.boundedQueries L)`,
   inherited from RLUB and TSCC.  Nothing here is a statement about the deployed
   permutation, no reduction to any keccak assumption is claimed, and no keccak
   cryptanalysis is cited.
2. **FIXED (NON-ADAPTIVE) PROVER.**  `p : Verifier.Proof` and `p.used` are
   quantified OUTSIDE the law.  An adaptive prover is NOT covered, here or
   anywhere in this tree.  Every headline below -- the fibre counts, the Fubini,
   `run_index_stage_mass_le`, and every `assembly_failure_mass_le_unconditional`
   form -- holds *for a fixed (non-adaptive) prover under the random oracle
   model*, and that qualification is part of the claim, not a caveat bolted on
   afterwards.  Eliminating the `RowPointFixed` hypothesis by counting removes a
   CONDITIONING hypothesis; it does not widen the prover model by one inch.
3. **SCOPE: OUTER SUMCHECK + INDEX LANES ONLY.**  Twenty-two relation-prefix
   frames, five frames per coupled round, eight used-claim frames.  WHIR folding
   and Merkle openings are EXCLUDED, exactly as `ChallengeUnionBound.combinedBound`
   excludes them.
4. **THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.**  The deployed profile's
   design point is about a hundred bits and the dominant terms are the excluded
   WHIR/Merkle ones.  Quoting `combinedBound + 2 * tauTerm + chain term` as the
   wire-v3 soundness error would be wrong by a wide margin.  **No sentence in this
   module says soundness is proved.**
5. **WHAT THE ASSEMBLY CONCLUSION IS.**  `RunLevelUnionBound.assemblyFailureEvent`
   is the failure of the adopted `SoundnessAssembly.explicit_good_draw_assembly`
   conclusion -- good-draw-CONDITIONAL constraint vanishing at every row, the cell
   identification, the pinned WHIR parameters, and the `core c = core c₀` /
   `KhashCollision` disjunction.  It is NOT circuit truth.  **Residue R1b is still
   assumed inside `SoundnessAssembly.AssemblyResidue`** and is not discharged
   here.  **ACCEPTANCE IS NEVER EXHIBITED**: no run of `Integrated.verify`
   returning `Except.ok ()` is constructed anywhere in this tree, so the failure
   event's hypotheses are not shown to be reachable by a real accepted
   transcript; that residue is inherited unchanged from `SoundnessAssembly`, RLUB
   and TSCC.
6. **WHAT ELIMINATING THE `RowPointFixed` HYPOTHESIS BY COUNTING DOES AND DOES
   NOT BUY.**  It removes the one hypothesis of TSCC's payoffs that was not known
   to be satisfiable at a non-constant committed column, and it removes it by
   COUNTING, not by assuming: the index draw is uniform at each FIXED outer draw
   because the two squeeze families land on disjoint oracle cells off the chain
   clash.  The predicate itself is NOT established -- at a non-constant committed
   column `RowPointFixed` is false, and no theorem here asserts it.  It buys
   nothing else.  The constant is TSCC's, term for term; the prover model is TSCC's; the
   conclusion being weighed is `SoundnessAssembly`'s; and residues R1b and
   never-exhibited acceptance are untouched.
7. **THE ADDITIVE TERM IS THE CHAIN MODEL'S.**  It is ILO's
   `extendedDigestClashEvent`, and its identification with the run's own block and
   index digests is CCT's and ILO's, not this module's:
   `ConcreteChainThreading.run_round_digest_is_chain_digest`,
   `IndexLanesOracle.extended_prefix_agrees` and RLUB's section 1.  Those
   identifications are adopted here unexamined.
8. **LENGTH BUDGETS, INHERITED.**  RLUB's HONESTY (7) and (8) are unchanged,
   including the fact that the closed `L = 381` budget admits only claims of width
   at most THIRTEEN, while the deployed `indexBits = 8` claims can be two hundred
   fifty-six wide.  The closed instance of section 7 is a SATISFIABILITY WITNESS
   at width one, not the deployed configuration; only the deployment data
   `(gdec, hash, khash, P, c₀)` and the call data stay free there.
9. **WHAT IS STILL OPEN, NAMED.**  The `cols` of the payoff are arbitrary, but
   nothing here shows that the adopted guard `IndexPointZeroCheck.CellsDifferOnCube`
   is live at a NON-CONSTANT committed column: `live_index_guard_is_live_at_every_outer_draw`
   is proved at ONE CONSTANT column only.  A dead guard makes the index event
   empty and `2 * tauTerm` pure slack; it never makes the bound false.

## Tactic note

No `set_option` is used, so the elaborator's default recursion budget applies.
As TSCC warns, a membership `w ∈ E` in an event built from `Finset.univ.filter`
over these spaces cannot be transported by `exact` at the default budget, and an
event supplied as a VARIABLE does not beta-reduce, so its decidability instance
does not match a concrete one syntactically.  Both hazards are routed around the
same way: `frame_fibre_card` takes its table event AND its fibre family as
abstract `Finset`s described by membership equivalences, and every other bridge
(`run_union_diagonal_subset_at`, `index_bad_event_at_is_index_bad_at`,
`assembly_failure_subset_diagonal`) is stated with the families abstract and
proved by Finset equalities.  `decide`, `native_decide`, `sorry`, `admit` and
`axiom` do not occur; `Fintype.card Element` and `Fintype.card Block` are never
evaluated.

## `Finset.univ`, disclosed

`Finset.univ` occurs in this module's OWN definition `runUnionDiagonalEvent`, and
in the fibre-count statements `run_index_diagonal_fibre_count_le` and
`run_union_diagonal_fibre_count_le`, where the filtered `Finset.univ` over
`ChallengeHalf (boundedQueries L) → Block` is the fibre's counting domain -- the
same use RLUB makes in `run_index_fibre_count` and `run_union_fibre_count_le`.
It occurs once more INDIRECTLY, in `runIndexStageEvent`, a wrapper around RLUB's
`runUnionBadEventAt`.  No tactic ever enumerates any of them.
-/

namespace Audit.Wire3.IndexStageFinerSplit

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound

/-! ## 0. THE TWO-GROUP DIAGONAL, MEMBERSHIP FORM -/

section General

variable {K1 K2 B : Type} [Fintype K1] [DecidableEq K1] [Fintype K2] [DecidableEq K2]
  [Fintype B] [DecidableEq B]

theorem mem_product_diagonal_event
    (F : (K1 → B) → Finset (K2 → B)) (z : K1 ⊕ K2 → B) :
    z ∈ TwoStageConditionalCount.productDiagonalEvent F
      ↔ (fun k => z (Sum.inr k)) ∈ F (fun k => z (Sum.inl k)) := by
  classical
  simp only [TwoStageConditionalCount.productDiagonalEvent, Finset.mem_filter, Finset.mem_univ,
    true_and]

end General

/-! ## 1. THE FRAME-FIBRE DECOMPOSITION OF AN ARBITRARY TABLE EVENT -/

open Classical in
/-- (1) **EVERY EVENT ON TABLES IS THE SUM OF ITS FRAME FIBRES.**  RLUB runs this
peel twice inside `run_union_draw_probability_le_fibrewise`, once for each of its
two events; it is stated once here, with BOTH the table event and its fibres
ABSTRACT and described by membership equivalences, because this module needs it
twice and because abstract events keep the elaborator away from memberships in
filtered events.  `Finset.univ` is the counting domain of the peel, exactly as in
RLUB. -/
theorem frame_fibre_card (L : Nat) (E : Finset (OracleTable (boundedQueries L)))
    (Pred : OracleTable (boundedQueries L) → Prop) (hE : ∀ T, T ∈ E ↔ Pred T)
    (Efib : (FrameHalf (boundedQueries L) → Block)
      → Finset (ChallengeHalf (boundedQueries L) → Block))
    (hEfib : ∀ (f : FrameHalf (boundedQueries L) → Block)
      (g : ChallengeHalf (boundedQueries L) → Block),
      g ∈ Efib f ↔ Pred ((frameSplit (boundedQueries L)).symm (g, f))) :
    E.card = ∑ f : FrameHalf (boundedQueries L) → Block, (Efib f).card := by
  classical
  have h1 : E
      = Finset.univ.filter (fun T : OracleTable (boundedQueries L) =>
          (fun z : (ChallengeHalf (boundedQueries L) → Block)
              × (FrameHalf (boundedQueries L) → Block) =>
            Pred ((frameSplit (boundedQueries L)).symm z)) (frameSplit (boundedQueries L) T)) := by
    apply Finset.ext
    intro T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact hE T
  have h2 : ∀ f : FrameHalf (boundedQueries L) → Block, Efib f
      = Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          Pred ((frameSplit (boundedQueries L)).symm (g, f))) := by
    intro f
    apply Finset.ext
    intro g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hEfib f g
  rw [h1, WhirChallenge.equiv_event_card (frameSplit (boundedQueries L))
      (fun z : (ChallengeHalf (boundedQueries L) → Block)
          × (FrameHalf (boundedQueries L) → Block) =>
        Pred ((frameSplit (boundedQueries L)).symm z)),
    Finset.card_filter, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl (fun f _ => by rw [h2 f, Finset.card_filter])

/-! ## 2. THE DIAGONAL COUNT INSIDE ONE FRAME FIBRE -/

/-- (2) A per-index-point mass bound, in card form. -/
theorem index_preimage_card_le (bits : Nat)
    (E : Finset (InstalledIndexSampler.IndexSpace bits)) (boundI : ℚ)
    (hb : IndexPointZeroCheck.indexProbability bits E ≤ boundI) :
    ((IndexLanesOracle.indexBundlePreimage bits E).card : ℚ)
      ≤ boundI * (Fintype.card (InstalledIndexSampler.IndexDraw bits × Fin 3 → Block) : ℚ) := by
  have hpos := IndexLanesOracle.index_space_card_cast_pos bits
  have hcard : (Fintype.card (InstalledIndexSampler.IndexDraw bits × Fin 3 → Block) : ℚ)
      = (Fintype.card (InstalledIndexSampler.IndexSpace bits) : ℚ) := by
    rw [IndexLanesOracle.index_space_card_as_blocks, Fintype.card_fun,
      IndexLanesOracle.index_schedule_card]
    push_cast
    rfl
  rw [IndexLanesOracle.index_bundle_preimage_card, hcard]
  rw [IndexPointZeroCheck.indexProbability, div_le_iff hpos] at hb
  exact hb

open Classical in
/-- (2) **THE DIAGONAL INDEX COUNT ON ONE GOOD FIBRE.**  The diagonal analogue of
RLUB's `run_index_fibre_count`: the target event is allowed to depend on the
fibre's OUTER draw.  Off RLUB's clash the COMBINED selector -- outer cells and
index cells together -- is injective into the challenge half, so the adopted
`restrict_ratio` at that selector makes the PAIR (outer draw, index draw)
jointly uniform on the product, and TSCC's `product_diagonal_card_le` counts the
diagonal group by group.  `Finset.univ` is the fibre's counting domain, the same
use RLUB makes. -/
theorem run_index_diagonal_fibre_count_le (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hL : 64 ≤ L)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (FI : JointChallengeSpace.JointSpace c.degreeBits →
      Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (boundI : ℚ)
    (hb : ∀ u, IndexPointZeroCheck.indexProbability c.indexBits (FI u) ≤ boundI)
    (f : FrameHalf (boundedQueries L) → Block) (b0 : Block)
    (hinj : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      Function.Injective (RunLevelUnionBound.runCombinedSchedule L c p
        ((frameSplit (boundedQueries L)).symm (g, f)))) :
    ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p
          ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card : ℚ)
      ≤ boundI * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) := by
  classical
  set dig := sourceDigest (hashOf (boundedQueries L)
    ((frameSplit (boundedQueries L)).symm ((fun _ => b0), f))) c p with hdigdef
  set e := RunLevelUnionBound.runIndexDigest (hashOf (boundedQueries L)
    ((frameSplit (boundedQueries L)).symm ((fun _ => b0), f))) c p with hedef
  have hmemJ : ∀ (k : JointChallengeSpace.Draw c.degreeBits) (j : Fin 3),
      squeezeInputAt c.degreeBits dig k j ∈ boundedQueries L :=
    fun _ _ => bounded_queries_challenge L hL _ _
  have hmemI : ∀ (k : InstalledIndexSampler.IndexDraw c.indexBits) (j : Fin 3),
      IndexLanesOracle.indexSqueezeInputAt c.indexBits e k j ∈ boundedQueries L :=
    fun _ _ => bounded_queries_challenge L hL _ _
  set selJ : JointChallengeSpace.Draw c.degreeBits × Fin 3 → ChallengeHalf (boundedQueries L) :=
    fun kj => ⟨⟨squeezeInputAt c.degreeBits dig kj.1 kj.2, hmemJ kj.1 kj.2⟩,
      challenge_input_shaped _ _⟩
  set selI : InstalledIndexSampler.IndexDraw c.indexBits × Fin 3
      → ChallengeHalf (boundedQueries L) :=
    fun kj => ⟨⟨IndexLanesOracle.indexSqueezeInputAt c.indexBits e kj.1 kj.2, hmemI kj.1 kj.2⟩,
      challenge_input_shaped _ _⟩
  have hselCinj : Function.Injective (Sum.elim selJ selI) := by
    intro a b hab
    refine hinj (fun _ => b0) ?_
    cases a <;> cases b <;> exact congrArg (fun z => z.val.val) hab
  have hdrawJ : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p
        = bundleEquiv c.degreeBits (fun kj => g (selJ kj)) := by
    intro g
    rw [actual_digest_draw_is_draw_at_digests,
      RunLevelUnionBound.run_source_digest_fibre_const L c p f g (fun _ => b0), ← hdigdef,
      draw_at_digests_is_encoded (boundedQueries L) c.degreeBits dig
        (fun kj => (selJ kj).val) (fun k j => rfl)]
    unfold encodedDraw
    exact congrArg (bundleEquiv c.degreeBits)
      (funext fun kj => RunLevelUnionBound.frame_split_challenge L g f (selJ kj))
  have hdrawI : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p
        = IndexLanesOracle.indexBundleEquiv c.indexBits (fun kj => g (selI kj)) := by
    intro g
    rw [RunLevelUnionBound.assembly_index_draw_is_at_run_index_digest,
      RunLevelUnionBound.run_index_digest_fibre_const L c p hlenI hlenP hmlen f g (fun _ => b0),
      ← hedef,
      IndexLanesOracle.index_draw_at_digest_is_encoded (boundedQueries L) c.indexBits e
        (fun kj => (selI kj).val) (fun k j => rfl)]
    unfold IndexLanesOracle.indexEncodedDraw
    exact congrArg (IndexLanesOracle.indexBundleEquiv c.indexBits)
      (funext fun kj => RunLevelUnionBound.frame_split_challenge L g f (selI kj))
  set F : (JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block)
      → Finset (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3 → Block) :=
    fun u => IndexLanesOracle.indexBundlePreimage c.indexBits (FI (bundleEquiv c.degreeBits u))
    with hFdef
  have hset : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p
          ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p)))
      = restrictAt (Sum.elim selJ selI) (TwoStageConditionalCount.productDiagonalEvent F) := by
    apply Finset.ext
    intro g
    rw [Finset.mem_filter, restrictAt, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, mem_product_diagonal_event, Sum.elim_inl, Sum.elim_inr,
      hFdef, IndexLanesOracle.indexBundlePreimage, Finset.mem_filter, hdrawI g, hdrawJ g]
  have hbu : ∀ u : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block,
      ((F u).card : ℚ)
        ≤ boundI * (Fintype.card (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3
          → Block) : ℚ) :=
    fun u => index_preimage_card_le c.indexBits _ boundI (hb (bundleEquiv c.degreeBits u))
  have hDcard := TwoStageConditionalCount.product_diagonal_card_le F boundI hbu
  have hratio := restrict_ratio (Sum.elim selJ selI) hselCinj
    (TwoStageConditionalCount.productDiagonalEvent F)
  have hbpos : (0 : ℚ) < (Fintype.card Block : ℚ) := by exact_mod_cast block_card_pos
  have hcardfun : (Fintype.card ((JointChallengeSpace.Draw c.degreeBits × Fin 3)
        ⊕ (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3) → Block) : ℚ)
      = (Fintype.card Block : ℚ) ^ Fintype.card ((JointChallengeSpace.Draw c.degreeBits × Fin 3)
        ⊕ (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3)) := by
    rw [Fintype.card_fun]
    push_cast
    rfl
  have hpow : (0 : ℚ) < (Fintype.card Block : ℚ)
      ^ Fintype.card ((JointChallengeSpace.Draw c.degreeBits × Fin 3)
        ⊕ (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3)) := pow_pos hbpos _
  rw [hcardfun] at hDcard
  rw [hset]
  refine le_of_mul_le_mul_right ?_ hpow
  rw [hratio]
  calc ((TwoStageConditionalCount.productDiagonalEvent F).card : ℚ)
        * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ)
      ≤ (boundI * (Fintype.card Block : ℚ)
          ^ Fintype.card ((JointChallengeSpace.Draw c.degreeBits × Fin 3)
            ⊕ (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3)))
          * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) :=
        mul_le_mul_of_nonneg_right hDcard (Nat.cast_nonneg _)
    _ = boundI * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ)
          * (Fintype.card Block : ℚ)
          ^ Fintype.card ((JointChallengeSpace.Draw c.degreeBits × Fin 3)
            ⊕ (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3)) := by ring


/-! ## 3. THE RUN-LEVEL DIAGONAL EVENT AND ITS FUBINI -/

open Classical in
/-- THE RUN-LEVEL DIAGONAL UNION EVENT.  The tables whose OWN outer draw lands in
the fixed `EJ`, or whose OWN index draw lands in the member of the family `FI`
selected by that same table's OWN outer draw.  Both draws are the adopted
`InstalledRoundCommit.actualDigestDraw` and `SoundnessAssembly.actualIndexDraw`,
read at the table's own hash; nothing is conditioned and nothing is quantified
outside the law.  RLUB's `runUnionBadEvent` is the special case of a CONSTANT
`FI`. -/
noncomputable def runUnionDiagonalEvent (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (FI : JointChallengeSpace.JointSpace c.degreeBits →
      Finset (InstalledIndexSampler.IndexSpace c.indexBits)) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c p ∈ EJ
      ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c p
          ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c p))

open Classical in
/-- (3) **THE FIBRE BOUND FOR THE DIAGONAL UNION.**  On a fibre whose combined
schedule is injective the outer half is exactly its ideal mass
(RLUB's `run_joint_fibre_count`) and the diagonal index half is at most `boundI`
(section 2); on any other fibre the whole fibre is in the exceptional count. -/
theorem run_union_diagonal_fibre_count_le (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hL : 64 ≤ L)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (FI : JointChallengeSpace.JointSpace c.degreeBits →
      Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (boundI : ℚ)
    (hb : ∀ u, IndexPointZeroCheck.indexProbability c.indexBits (FI u) ≤ boundI)
    (b0 : Block) (f : FrameHalf (boundedQueries L) → Block) :
    ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card : ℚ)
      ≤ (JointChallengeSpace.jointProbability c.degreeBits EJ + boundI)
          * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ)
        + ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
            ¬ Function.Injective (RunLevelUnionBound.runCombinedSchedule L c p
              ((frameSplit (boundedQueries L)).symm (g, f))))).card : ℚ) := by
  classical
  have hbnn : (0 : ℚ) ≤ boundI :=
    le_trans (RunLevelUnionBound.index_probability_nonneg c.indexBits _)
      (hb (bundleEquiv c.degreeBits (fun _ => b0)))
  have hcardle : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card
      ≤ (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ)).card
        + (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    exact hx
  have hcardleq : ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card : ℚ)
      ≤ ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ)).card : ℚ)
        + ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card : ℚ) := by
    exact_mod_cast hcardle
  by_cases hinj : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      Function.Injective (RunLevelUnionBound.runCombinedSchedule L c p
        ((frameSplit (boundedQueries L)).symm (g, f)))
  · rw [RunLevelUnionBound.run_joint_fibre_count L c p hL EJ f b0 hinj] at hcardleq
    have hidx := run_index_diagonal_fibre_count_le L c p hL hlenI hlenP hmlen FI boundI hb f b0 hinj
    rw [add_mul]
    linarith
  · push_neg at hinj
    obtain ⟨g0, hg0⟩ := hinj
    have hb2 : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        ¬ Function.Injective (RunLevelUnionBound.runCombinedSchedule L c p
          ((frameSplit (boundedQueries L)).symm (g, f))))) = Finset.univ := by
      apply Finset.ext
      intro g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [RunLevelUnionBound.run_combined_schedule_fibre_const L c p hlenI hlenP hmlen f g g0]
      exact hg0
    rw [hb2, Finset.card_univ]
    have hle : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card
        ≤ Fintype.card (ChallengeHalf (boundedQueries L) → Block) := by
      rw [← Finset.card_univ]
      exact Finset.card_filter_le _ _
    have hlec : ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p))).card : ℚ)
        ≤ (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) := by
      exact_mod_cast hle
    have hjp := JointChallengeSpace.joint_probability_nonneg c.degreeBits EJ
    have hNnn : (0 : ℚ) ≤ (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) :=
      Nat.cast_nonneg _
    have hpos := mul_nonneg (add_nonneg hjp hbnn) hNnn
    linarith

/-- (3) **THE RUN-LEVEL FUBINI FOR THE DIAGONAL UNION, for a fixed (non-adaptive)
prover under the random oracle model.**  RLUB's
`run_union_draw_probability_le_fibrewise` with the index half allowed to depend
on the run's own outer draw.  The price is the SAME single additive term -- the
mass of the fibres where the run's combined schedule is not injective -- because
the count of section 2 uses exactly that injectivity. -/
theorem run_union_diagonal_probability_le_fibrewise (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hL : 64 ≤ L)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (FI : JointChallengeSpace.JointSpace c.degreeBits →
      Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (boundI : ℚ)
    (hb : ∀ u, IndexPointZeroCheck.indexProbability c.indexBits (FI u) ≤ boundI) :
    oracleProbability (boundedQueries L) (runUnionDiagonalEvent L c p EJ FI)
      ≤ JointChallengeSpace.jointProbability c.degreeBits EJ + boundI
        + oracleProbability (boundedQueries L)
            (RunLevelUnionBound.runCombinedNonInjectiveEvent L c p) := by
  classical
  obtain ⟨b0⟩ := Fintype.card_pos_iff.mp block_card_pos
  haveI : Nonempty (ChallengeHalf (boundedQueries L) → Block) := ⟨fun _ => b0⟩
  haveI : Nonempty (FrameHalf (boundedQueries L) → Block) := ⟨fun _ => b0⟩
  have hA := frame_fibre_card L (runUnionDiagonalEvent L c p EJ FI)
    (fun T : OracleTable (boundedQueries L) =>
      InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c p ∈ EJ
        ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c p))
    (fun T => by
      simp only [runUnionDiagonalEvent, Finset.mem_filter, Finset.mem_univ, true_and])
    (fun f => Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p
            ∈ FI (InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
              ((frameSplit (boundedQueries L)).symm (g, f))) c p)))
    (fun f g => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  have hB := frame_fibre_card L (RunLevelUnionBound.runCombinedNonInjectiveEvent L c p)
    (fun T : OracleTable (boundedQueries L) =>
      ¬ Function.Injective (RunLevelUnionBound.runCombinedSchedule L c p T))
    (fun T => by
      simp only [RunLevelUnionBound.runCombinedNonInjectiveEvent, Finset.mem_filter,
        Finset.mem_univ, true_and])
    (fun f => Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        ¬ Function.Injective (RunLevelUnionBound.runCombinedSchedule L c p
          ((frameSplit (boundedQueries L)).symm (g, f)))))
    (fun f g => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  have htot : Fintype.card (OracleTable (boundedQueries L))
      = Fintype.card (ChallengeHalf (boundedQueries L) → Block)
        * Fintype.card (FrameHalf (boundedQueries L) → Block) := by
    rw [Fintype.card_congr (frameSplit (boundedQueries L)), Fintype.card_prod]
  have hNpos : (0 : ℚ) < (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := ChallengeHalf (boundedQueries L) → Block)
  have hMpos : (0 : ℚ) < (Fintype.card (FrameHalf (boundedQueries L) → Block) : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := FrameHalf (boundedQueries L) → Block)
  have hNM : (0 : ℚ) < (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ)
      * (Fintype.card (FrameHalf (boundedQueries L) → Block) : ℚ) := mul_pos hNpos hMpos
  rw [oracleProbability, oracleProbability, hA, hB, htot]
  push_cast
  rw [div_le_iff hNM, add_mul, div_mul_cancel₀ _ hNM.ne']
  refine le_trans (Finset.sum_le_sum
    (fun f _ => run_union_diagonal_fibre_count_le L c p hL hlenI hlenP hmlen EJ FI boundI hb b0 f))
    (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring


/-! ## 4. THE INDEX BAD EVENT AS A FUNCTION OF THE RUN'S OWN OUTER DRAW

TSCC section 5.1 proves that two hashes with the same outer draw have the same
row point.  What the diagonal count needs is the FUNCTION itself, so that the
family `FI` of section 3 can be written down: `rowPointOf` reads the row point
off a point of the joint space, coordinate by coordinate, through TSCC's
`rowCoord`. -/

/-- THE ROW POINT OF A BOUND CELL, READ OFF A POINT OF THE JOINT SPACE. -/
def rowPointOf (d : Nat) (cellIndex : Fin 5) (u : JointChallengeSpace.JointSpace d) :
    List Verifier.Ext3 :=
  List.ofFn (fun r : Fin d =>
    (OuterChallenge.reduceTriple (u (TwoStageConditionalCount.rowCoord d cellIndex r))).toVerifier)

theorem row_point_of_length (d : Nat) (cellIndex : Fin 5)
    (u : JointChallengeSpace.JointSpace d) : (rowPointOf d cellIndex u).length = d := by
  rw [rowPointOf, List.length_ofFn]

/-- (4) **THE ENGINE'S ROW POINT IS `rowPointOf` AT THE RUN'S OWN OUTER DRAW.**
TSCC's `row_point_is_outer_draw_function` entry by entry, assembled into a list
equality.  Only the envelope's `hdb` and the round count `hmlen` are used; no
acceptance is assumed. -/
theorem cell_row_is_row_point_of (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (th : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) (hmlen : (roundMessages p).length = c.degreeBits)
    (cellIndex : Fin 5) :
    OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p) cellIndex
      = rowPointOf c.degreeBits cellIndex (InstalledRoundCommit.actualDigestDraw th c p) := by
  have hz : (p.logRounds.zip p.gateRounds).length = c.degreeBits := hmlen
  have hl := (TwoStageConditionalCount.cell_row_length gdec hash khash P c₀ c p cellIndex th).trans
    hz
  have hr := row_point_of_length c.degreeBits cellIndex
    (InstalledRoundCommit.actualDigestDraw th c p)
  refine List.ext_get? (fun k => ?_)
  by_cases hk : k < c.degreeBits
  · rw [TwoStageConditionalCount.row_point_is_outer_draw_function gdec hash th khash P c₀ c p hdb
      hmlen cellIndex k hk, rowPointOf, List.get?_eq_getElem?, List.getElem?_ofFn,
      List.ofFnNthVal, dif_pos hk]
  · rw [List.get?_eq_none.mpr (by omega), List.get?_eq_none.mpr (by omega)]

/-- THE INDEX BAD EVENT AT AN OUTER DRAW.  The adopted
`IndexLanesOracle.guardedIndexBadEvent` whose COMMITTED cells are the opened
cells at the row point `u` determines.  Legitimate as a function of `u` by
section 4's `cell_row_is_row_point_of`; the SUPPLIED cells do not move with the
hash at all (TSCC's `supplied_cells_index_free`). -/
noncomputable def indexBadAt (c : Verifier.Config) (p : Verifier.Proof) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (idx0 : Verifier.IndexPoints)
    (u : JointChallengeSpace.JointSpace c.degreeBits) :
    Finset (InstalledIndexSampler.IndexSpace c.indexBits) :=
  IndexLanesOracle.guardedIndexBadEvent c.indexBits
    (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx0 cellIndex).1)
    (IndexPointZeroCheck.openedCells (cols cellIndex)
      (OpenedClaimFold.lift (rowPointOf c.degreeBits cellIndex u)))

/-- (4) **THE ENGINE'S WHOLE HASH-INDEXED INDEX FAMILY IS `indexBadAt` AT THE
RUN'S OWN OUTER DRAW.**  This is TSCC's `index_bad_event_at_is_constant` with the
`RowPointFixed` hypothesis REPLACED by the outer draw: no cell family is claimed
to be constant, only to be a function of a quantity the diagonal count conditions
on. -/
theorem index_bad_event_at_is_index_bad_at (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (idx0 : Verifier.IndexPoints)
    (hdb : c.degreeBits ≤ 13) (hmlen : (roundMessages p).length = c.degreeBits)
    (th : Transcript.Hash) :
    SoundnessAssembly.indexBadEvent c.indexBits
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
          (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
          cellIndex).1)
        (IndexPointZeroCheck.openedCells (cols cellIndex)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow
            (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
            cellIndex)))
      = indexBadAt c p cellIndex cols idx0 (InstalledRoundCommit.actualDigestDraw th c p) := by
  rw [cell_row_is_row_point_of gdec hash th khash P c₀ c p hdb hmlen cellIndex,
    TwoStageConditionalCount.supplied_cells_index_free p.used
      (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash th khash P c₀) c p) idx0
      cellIndex]
  rfl

/-- (4) **THE PER-OUTER-DRAW MASS BOUND.**  At EVERY outer draw the index event is
one adopted guarded event, so the adopted
`IndexLanesOracle.guarded_index_bad_event_mass_le` applies with no side
condition. -/
theorem index_bad_at_mass_le (c : Verifier.Config) (p : Verifier.Proof) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (idx0 : Verifier.IndexPoints)
    (u : JointChallengeSpace.JointSpace c.degreeBits) :
    IndexPointZeroCheck.indexProbability c.indexBits (indexBadAt c p cellIndex cols idx0 u)
      ≤ 2 * ChallengeUnionBound.tauTerm c.indexBits :=
  IndexLanesOracle.guarded_index_bad_event_mass_le c.indexBits _ _

/-- (4) **THE BRIDGE FROM THE HASH-INDEXED EVENT TO THE DIAGONAL EVENT.**  TSCC's
`run_union_diagonal_subset` with the index half diagonalized as well: the outer
family is read at the hash's own alpha coordinate and the index family at the
hash's own WHOLE outer draw.  Both families are abstract, so nothing about the
engine is unfolded here. -/
theorem run_union_diagonal_subset_at (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (F : OuterChallenge.DigestTriple → Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (FI : JointChallengeSpace.JointSpace c.degreeBits →
      Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (EJat : Transcript.Hash → Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EIat : Transcript.Hash → Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (hJ : ∀ th, EJat th
      = F (InstalledRoundCommit.actualDigestDraw th c p JointChallengeSpace.Draw.gateAlpha))
    (hI : ∀ th, EIat th = FI (InstalledRoundCommit.actualDigestDraw th c p)) :
    RunLevelUnionBound.runUnionBadEventAt L c p EJat EIat
      ⊆ runUnionDiagonalEvent L c p
          (TwoStageConditionalCount.diagonalEvent JointChallengeSpace.Draw.gateAlpha F) FI := by
  classical
  intro T hT
  rw [RunLevelUnionBound.runUnionBadEventAt, Finset.mem_filter] at hT
  rw [runUnionDiagonalEvent, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases hT.2 with h | h
  · rw [hJ, TwoStageConditionalCount.sa_draw_is_run_draw] at h
    left
    rw [TwoStageConditionalCount.mem_diagonalEvent]
    exact h
  · rw [hI] at h
    exact Or.inr h

/-! ## 5. STAGE B, DISCHARGED -/

theorem joint_probability_empty (d : Nat) :
    JointChallengeSpace.jointProbability d (∅ : Finset (JointChallengeSpace.JointSpace d)) = 0 := by
  rw [JointChallengeSpace.jointProbability, Finset.card_empty, Nat.cast_zero, zero_div]

open Classical in
/-- **THE TRANSPORTED STAGE-B EVENT.**  The tables on which the run's OWN index
draw lands in the explicit engine's OWN adopted `SoundnessAssembly.indexBadEvent`,
both read at the TABLE'S own hash -- so the committed cells move with the hash
exactly as they do in RLUB's `assembly_failure_subset_run_union`.  Its outer half
is empty, so it weighs the index lane alone. -/
noncomputable def runIndexStageEvent (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) :
    Finset (OracleTable (boundedQueries L)) :=
  RunLevelUnionBound.runUnionBadEventAt L c p
    (fun _ => (∅ : Finset (JointChallengeSpace.JointSpace c.degreeBits)))
    (fun th => SoundnessAssembly.indexBadEvent c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
        (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
        cellIndex).1)
      (IndexPointZeroCheck.openedCells (cols cellIndex)
        (OpenedClaimFold.lift (OpenedClaimFold.cellRow
          (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
          cellIndex))))

/-- (5) **STAGE B, FOR A FIXED (NON-ADAPTIVE) PROVER UNDER THE RANDOM ORACLE
MODEL.**  The mass of the tables whose own index draw lands in the engine's own
index bad event -- the committed cells evaluated at the row point the table's own
outer draw determines -- is at most `2 * ChallengeUnionBound.tauTerm c.indexBits`
plus ILO's one chain-clash term.  **NO `RowPointFixed`**: the conditioning is
done by the finer split of sections 1-3 rather than assumed.  No index point is
taken as a parameter: the `idx0` fed to `indexBadAt` inside the proof is erased
again by TSCC's `supplied_cells_index_free`, so any one will do and the fixed
`⟨[], []⟩` is used. -/
theorem run_index_stage_mass_le (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (hL : 64 ≤ L) (hdb : c.degreeBits ≤ 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) :
    oracleProbability (boundedQueries L)
        (runIndexStageEvent L gdec hash khash P c₀ c p cellIndex cols)
      ≤ 2 * ChallengeUnionBound.tauTerm c.indexBits
        + oracleProbability (boundedQueries L)
            (IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
              (roundMessages p) p.used c.degreeBits hlenI) := by
  have idx0 : Verifier.IndexPoints := ⟨[], []⟩
  have hsub := oracle_probability_mono (boundedQueries L) _ _
    (run_union_diagonal_subset_at L c p
      (fun _ => (∅ : Finset (JointChallengeSpace.JointSpace c.degreeBits)))
      (indexBadAt c p cellIndex cols idx0) _ _ (fun _ => rfl)
      (fun th => index_bad_event_at_is_index_bad_at gdec hash khash P c₀ c p cellIndex cols idx0
        hdb hmlen th))
  have h0 := run_union_diagonal_probability_le_fibrewise L c p hL hlenI hlenP hmlen
    (TwoStageConditionalCount.diagonalEvent JointChallengeSpace.Draw.gateAlpha
      (fun _ => (∅ : Finset (JointChallengeSpace.JointSpace c.degreeBits))))
    (indexBadAt c p cellIndex cols idx0) (2 * ChallengeUnionBound.tauTerm c.indexBits)
    (index_bad_at_mass_le c p cellIndex cols idx0)
  have h1 : JointChallengeSpace.jointProbability c.degreeBits
      (TwoStageConditionalCount.diagonalEvent JointChallengeSpace.Draw.gateAlpha
        (fun _ => (∅ : Finset (JointChallengeSpace.JointSpace c.degreeBits)))) = 0 := by
    rw [TwoStageConditionalCount.diagonal_const]
    exact joint_probability_empty c.degreeBits
  have h3 := oracle_probability_mono (boundedQueries L) _ _
    (RunLevelUnionBound.run_combined_non_injective_subset_clash L c p hL hdb hbb hlenI hlenP hmlen)
  rw [runIndexStageEvent]
  linarith


/-! ## 6. THE PAYOFF: THE ASSEMBLY'S MASS WITHOUT `RowPointFixed` -/

/-- (6) **THE ASSEMBLY'S FAILURE SET SITS INSIDE ONE DIAGONAL EVENT.**  TSCC's
`assembly_failure_subset_two_stage` with `RowPointFixed` removed: the index half
is no longer required to be constant, only to be the function of the run's own
outer draw that section 4 exhibits. -/
theorem assembly_failure_subset_diagonal (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (hdb : c.degreeBits ≤ 13)
    (hmlen : (roundMessages p).length = c.degreeBits) :
    RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post gate
        s0 sLast xg cells gateTruths coeffsOf cellIndex cols
      ⊆ runUnionDiagonalEvent L c p
          (TwoStageConditionalCount.outerDiagonalEvent
            (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p (pre ++ gate :: post) s0
            logTruths gateTruths t pr coeffsOf)
          (indexBadAt c p cellIndex cols idx0) :=
  (RunLevelUnionBound.assembly_failure_subset_run_union L gdec hash khash P c₀ pin chain c p wq
      pre post gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols).trans
    (run_union_diagonal_subset_at L c p _ _ _ _
      (fun th => TwoStageConditionalCount.explicit_outer_bad_event_is_the_family gdec hash khash P
        c₀ th0 c p (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf th)
      (fun th => index_bad_event_at_is_index_bad_at gdec hash khash P c₀ c p cellIndex cols idx0
        hdb hmlen th))

/-- (6) **THE TWO-STAGE MASS BOUND FOR THE EXPLICIT ENGINE'S ASSEMBLY, WITH NO
`RowPointFixed` HYPOTHESIS**, for a fixed (non-adaptive) prover under the random
oracle model.  Stage A is TSCC's `run_outer_stage_mass_le` constant; Stage B is
section 5; the chain term is ILO's, unchanged.  Every hypothesis is of a shape
already adopted elsewhere in this tree. -/
theorem assembly_failure_mass_le_unconditional (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (q constraints : Nat)
    (hL : 64 ≤ L) (hdb : c.degreeBits ≤ 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf
      (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf
      (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p gateTruths,
      r.message.length ≤ q + 2 ∧ r.truth.length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + oracleProbability (boundedQueries L)
            (IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
              (roundMessages p) p.used c.degreeBits hlenI) := by
  have hsub := oracle_probability_mono (boundedQueries L) _ _
    (assembly_failure_subset_diagonal L gdec hash khash P c₀ pin chain c p wq pre post gate s0
      sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols th0 idx0 hdb hmlen)
  have h0 := run_union_diagonal_probability_le_fibrewise L c p hL hlenI hlenP hmlen
    (TwoStageConditionalCount.outerDiagonalEvent
      (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p (pre ++ gate :: post) s0 logTruths
      gateTruths t pr coeffsOf)
    (indexBadAt c p cellIndex cols idx0) (2 * ChallengeUnionBound.tauTerm c.indexBits)
    (index_bad_at_mass_le c p cellIndex cols idx0)
  have h1 := TwoStageConditionalCount.stage_a_mass_le
    (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p q constraints (pre ++ gate :: post) s0
    logTruths gateTruths t pr coeffsOf hlogDeg hgateDeg hclen
  have h3 := oracle_probability_mono (boundedQueries L) _ _
    (RunLevelUnionBound.run_combined_non_injective_subset_clash L c p hL hdb hbb hlenI hlenP hmlen)
  linarith

/-- (6) **THE SAME BOUND WITH THE CLASH TERM REPLACED BY ILO'S BIRTHDAY COUNT**,
for a fixed (non-adaptive) prover under the random oracle model.  No
probabilistic side condition remains. -/
theorem assembly_failure_mass_le_unconditional_birthday (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (q constraints : Nat)
    (hL : 64 ≤ L) (hdb : c.degreeBits ≤ 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf
      (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf
      (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p gateTruths,
      r.message.length ≤ q + 2 ∧ r.truth.length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((22 + 5 * c.degreeBits + 8 : Nat) : ℚ)
            * (((22 + 5 * c.degreeBits + 8 : Nat) : ℚ) + 1) / 2 / (Fintype.card Block : ℚ) := by
  have h := assembly_failure_mass_le_unconditional L gdec hash khash P c₀ pin chain c p wq pre post
    gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols th0 idx0 q constraints
    hL hdb hbb hlenI hlenP hmlen hlogDeg hgateDeg hclen
  have hc := IndexLanesOracle.extended_digest_clash_mass_le L c (Verifier.statement p)
    (roundMessages p) p.used c.degreeBits hlenI
  linarith

/-- (6) **AT THE ENVELOPE'S `degreeBits = 13`**, for a fixed (non-adaptive)
prover under the random oracle model: ninety-five chain stages, so
`4560 / |Block|`. -/
theorem assembly_failure_mass_le_unconditional_at_thirteen (L : Nat)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (constraints : Nat)
    (hL : 64 ≤ L) (hd : c.degreeBits = 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf
      (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf
      (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p gateTruths,
      r.message.length ≤ 10 ∧ r.truth.length ≤ 10)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits 8 c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits + 4560 / (Fintype.card Block : ℚ) := by
  have h := assembly_failure_mass_le_unconditional_birthday L gdec hash khash P c₀ pin chain c p wq
    pre post gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols th0 idx0 8
    constraints hL (by omega) hbb hlenI hlenP hmlen hlogDeg hgateDeg hclen
  have hnum : ((22 + 5 * c.degreeBits + 8 : Nat) : ℚ)
      * (((22 + 5 * c.degreeBits + 8 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [hd]
    norm_num
  rw [hnum] at h
  exact h


/-! ## 7. A CLOSED INSTANCE AT THE LIVE WITNESS, AND NON-VACUITY -/

/-- (7) The committed family of ONE CONSTANT column of the row's width is `[v]` at
EVERY outer draw -- the analogue, now as a function of the draw rather than a
hypothesis, of TSCC's `row_point_fixed_at_constant_column`. -/
theorem opened_cells_at_constant_column (d : Nat) (cellIndex : Fin 5) (v : Element)
    (u : JointChallengeSpace.JointSpace d) :
    IndexPointZeroCheck.openedCells [List.replicate (2 ^ d) v]
        (OpenedClaimFold.lift (rowPointOf d cellIndex u)) = [v] := by
  simp only [IndexPointZeroCheck.openedCells, List.map_cons, List.map_nil]
  have hlen : (OpenedClaimFold.lift (rowPointOf d cellIndex u)).length = d := by
    rw [OpenedClaimFold.lift, List.length_map, row_point_of_length]
  have hext : ∀ tau : List Element, tau.length = d →
      ZeroCheckSemantics.extension (List.replicate (2 ^ d) v) tau = v := by
    intro tau htau
    rw [← htau]
    exact TwoStageConditionalCount.extension_const v tau
  rw [hext _ hlen]

/-- (7) So a supplied family that differs on the cube from `[v]` differs from the
committed family AT EVERY OUTER DRAW: the adopted guard is live along the whole
diagonal, not just at one point of it. -/
theorem guard_live_at_constant_column_at_every_outer_draw (bits d : Nat) (cellIndex : Fin 5)
    (supplied : List Element) (v : Element)
    (hs : IndexPointZeroCheck.CellsDifferOnCube bits supplied [v])
    (u : JointChallengeSpace.JointSpace d) :
    IndexPointZeroCheck.CellsDifferOnCube bits supplied
      (IndexPointZeroCheck.openedCells [List.replicate (2 ^ d) v]
        (OpenedClaimFold.lift (rowPointOf d cellIndex u))) := by
  rw [opened_cells_at_constant_column]
  exact hs

/-- (7) **THE GUARD IS LIVE AT TSCC'S `liveProof`, AT EVERY OUTER DRAW.**  The
supplied cell is `⟨x⟩` at every one of the five bound cells, so as soon as
`⟨x⟩ ≠ v` the index half of the closed bound below is a guarded event whose guard
fires -- at every point of the diagonal the count of section 2 ranges over. -/
theorem live_index_guard_is_live_at_every_outer_draw (x : Verifier.Ext3) (v : Element)
    (idx0 : Verifier.IndexPoints) (cellIndex : Fin 5) (hxv : (⟨x⟩ : Element) ≠ v)
    (u : JointChallengeSpace.JointSpace RunLevelUnionBound.unionConfig.degreeBits) :
    IndexPointZeroCheck.CellsDifferOnCube 8
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell (TwoStageConditionalCount.liveProof x).used
        idx0 cellIndex).1)
      (IndexPointZeroCheck.openedCells
        [List.replicate (2 ^ RunLevelUnionBound.unionConfig.degreeBits) v]
        (OpenedClaimFold.lift
          (rowPointOf RunLevelUnionBound.unionConfig.degreeBits cellIndex u))) :=
  guard_live_at_constant_column_at_every_outer_draw 8 _ cellIndex _ v
    (TwoStageConditionalCount.live_index_guard_is_live x v idx0 cellIndex hxv) u

/-- (7) **THE CLOSED BOUND, WITH NO `RowPointFixed` AND NO CONSTRAINT ON THE
COMMITTED COLUMNS**, for a fixed (non-adaptive) prover under the random oracle
model.  Every hypothesis of section 6 is discharged at TSCC's
`liveProof` -- RLUB's closed witness with one NON-ZERO used cell per bound cell,
so the index guard is live (`live_index_guard_is_live_at_every_outer_draw`) --
and `cols` is ARBITRARY: the committed columns need not be constant, need not be
known, and need not make any family constant in the hash.  Only the deployment
data `(gdec, hash, khash, P, c₀)` and the call data stay free, exactly as in
RLUB's and TSCC's own closed statements. -/
theorem assembly_failure_at_the_envelope_unconditional (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (th0 : Transcript.Hash) (idx0 : Verifier.IndexPoints) (x : Verifier.Ext3) :
    oracleProbability (boundedQueries 381)
        (RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
          RunLevelUnionBound.unionConfig (TwoStageConditionalCount.liveProof x) wq pre post gate s0
          sLast xg cells [] (fun _ => []) cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) := by
  have h := assembly_failure_mass_le_unconditional_at_thirteen 381 gdec hash khash P c₀ pin chain
    RunLevelUnionBound.unionConfig (TwoStageConditionalCount.liveProof x) wq pre post gate s0 sLast
    xg cells [] [] t pr (fun _ => []) cellIndex cols th0 idx0 123 (by norm_num)
    RunLevelUnionBound.union_config_degree (le_of_eq RunLevelUnionBound.union_config_index)
    (TwoStageConditionalCount.live_length_budget_extended x)
    (TwoStageConditionalCount.live_length_budget_chain x)
    (TwoStageConditionalCount.live_round_count x)
    (TwoStageConditionalCount.live_log_lane_degree x
      (SoundnessAssembly.engine gdec hash th0 khash P c₀))
    (TwoStageConditionalCount.live_gate_lane_degree x
      (SoundnessAssembly.engine gdec hash th0 khash P c₀))
    (fun _ _ => Nat.zero_le 123)
  rw [RunLevelUnionBound.union_config_degree, RunLevelUnionBound.union_config_index] at h
  exact h

/-- (7) **THE CLOSED STATEMENT IS NOT THE VACUOUS `≤ 1`.**  The bound it pairs
with holds for a fixed (non-adaptive) prover under the random oracle model, and
the right-hand side is RLUB's own, reused through TSCC's
`two_stage_closed_bound_lt_one`. -/
theorem assembly_failure_at_the_envelope_unconditional_is_not_vacuous
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (th0 : Transcript.Hash) (idx0 : Verifier.IndexPoints) (x : Verifier.Ext3) :
    oracleProbability (boundedQueries 381)
          (RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
            RunLevelUnionBound.unionConfig (TwoStageConditionalCount.liveProof x) wq pre post gate
            s0 sLast xg cells [] (fun _ => []) cellIndex cols)
        ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
          + 4560 / (Fintype.card Block : ℚ)
      ∧ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
          + 4560 / (Fintype.card Block : ℚ) < 1 :=
  ⟨assembly_failure_at_the_envelope_unconditional gdec hash khash P c₀ pin chain wq pre post gate
    s0 sLast xg cells t pr cellIndex cols th0 idx0 x,
   TwoStageConditionalCount.two_stage_closed_bound_lt_one⟩

/-- (7) **AND IT IS DISCHARGEABLE: A TABLE ON WHICH THE ASSEMBLY DOES NOT FAIL
EXISTS**, at the live witness and at arbitrary committed columns.  It comes from
a mass below `1` that holds for a fixed (non-adaptive) prover under the random
oracle model. -/
theorem assembly_good_table_exists_unconditional (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat)
    (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (cols : Fin 5 → List (List Element))
    (th0 : Transcript.Hash) (idx0 : Verifier.IndexPoints) (x : Verifier.Ext3) :
    ∃ T, T ∉ RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
      RunLevelUnionBound.unionConfig (TwoStageConditionalCount.liveProof x) wq pre post gate s0
      sLast xg cells [] (fun _ => []) cellIndex cols :=
  RunLevelUnionBound.exists_good_table_of_mass_lt_one _ _
    (lt_of_le_of_lt (assembly_failure_at_the_envelope_unconditional gdec hash khash P c₀ pin chain
      wq pre post gate s0 sLast xg cells t pr cellIndex cols th0 idx0 x)
      TwoStageConditionalCount.two_stage_closed_bound_lt_one)

end Audit.Wire3.IndexStageFinerSplit
