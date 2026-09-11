import Audit.Wire3.RunLevelUnionBound

/-!
# `Audit.Wire3.TwoStageConditionalCount` -- the alpha-conditioned outer stage

**WHAT THIS MODULE ADDS.**  `Audit.Wire3.RunLevelUnionBound` (RLUB) proves
`assembly_failure_subset_run_union`: the tables on which the adopted
`SoundnessAssembly.explicit_good_draw_assembly` conclusion can fail lie in a
HASH-INDEXED event `runUnionBadEventAt`.  RLUB proves NO mass bound for that
event, and its section 4.3 states the missing step as a contract: a TWO-STAGE
CONDITIONAL COUNT for a fixed prover.  This module discharges the OUTER stage of
that contract in full and names the index stage's conditioning explicitly.

* **Stage A (sections 1-3).**  The adopted `SoundnessAssembly.outerBadEvent`
  depends on the hash ONLY through `TranscriptProvenance.gateAlphaElement`
  (`outer_bad_event_depends_on_alpha_only`), and -- the step RLUB's contract did
  not mention -- the EXPLICIT ENGINE'S own hash-dependence is absorbed as well
  (`outer_bad_at_engine_congr`): the two lanes' round messages and truths are
  read off the PROOF, not off the transcript, and the adopted
  `AdaptiveAgreementFamily.frozenLane` reads no `challenge` field.  The gate
  alpha IS one coordinate of the run's own outer draw
  (`alpha_is_the_alpha_coordinate`, unconditional), so the honest object is the
  DIAGONAL event `outerDiagonalEvent` -- the points that lie in the engine's bad
  set AT THEIR OWN ALPHA COORDINATE -- and `stage_a_mass_le` weighs it by the
  adopted `ChallengeUnionBound.combinedBound`, the SAME constant the
  prefix-frozen `JointChallengeSpace.joint_union_bound` and the adopted
  `OuterSequentialConditioning.adaptive_joint_union_bound` get.  Conditioning on
  the alpha costs nothing.
* **Transport (section 4).**  Because the diagonal is a FIXED `Finset` on the
  adopted joint space, RLUB's own fixed-event Fubini applies to it verbatim; no
  new fibre machinery is built.  `run_outer_stage_mass_le` is the headline:
  the mass of the tables whose OWN outer draw lands in the engine's OWN outer bad
  event -- engine and alpha both moving with the table's hash -- is at most
  `combinedBound` plus ILO's one chain-clash term.  Its `hlogDeg` / `hgateDeg`
  hypotheses are ENGINE-FREE (`log_lane_degree_engine_congr`,
  `gate_lane_degree_engine_congr`): they may be checked at any engine at all.
* **Stage B (section 5) is NOT a conditional count.**  Read HONESTY (6).  Both
  dependence facts ARE delivered: section 5.1's
  `row_point_is_outer_draw_function` / `row_point_determined_by_outer_draw` show
  the bound cells' row point is a function of the run's own outer draw.
* **Payoff (sections 6-7).**  `assembly_failure_mass_le` and its birthday and
  envelope forms, plus a closed instance whose right-hand side is below `1` and
  a table on which the assembly does not fail.
* **Section 8** records that the closed instance of section 7 inherits RLUB's
  own index degeneracy (`union_index_half_is_empty`) and gives a second closed
  instance, at `liveProof`, whose index guard IS live whenever the supplied
  cell differs from the committed constant (`⟨x⟩ ≠ v`).

## HONESTY -- read before quoting anything below

1. **RANDOM ORACLE MODEL, NOT KECCAK.**  The law is the uniform counting measure
   on `RandomOracleSqueezes.OracleTable (BirthdayClashBound.boundedQueries L)`,
   inherited from RLUB.  Nothing here is a statement about the deployed
   permutation, no reduction to any keccak assumption is claimed, and no keccak
   cryptanalysis is cited.  The joint-space law is likewise the adopted uniform
   counting measure written down by hand.
2. **FIXED (NON-ADAPTIVE) PROVER.**  `p : Verifier.Proof` and `p.used` are
   quantified OUTSIDE the law.  An adaptive prover is NOT covered, here or
   anywhere in this tree.  Every headline below -- Stage A's mass, the transport,
   and every `assembly_failure_mass_le` form -- holds *for a fixed
   (non-adaptive) prover under the random oracle model*, and that qualification
   is part of the claim, not a caveat bolted on afterwards.
3. **SCOPE: OUTER SUMCHECK + INDEX LANES ONLY.**  Twenty-two relation-prefix
   frames, five frames per coupled round, eight used-claim frames.  WHIR folding
   and Merkle openings are EXCLUDED, exactly as `ChallengeUnionBound.combinedBound`
   excludes them.
4. **THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.**  The deployed
   profile's design point is about a hundred bits and the dominant terms are the
   excluded WHIR/Merkle ones.  Quoting `combinedBound + 2 * tauTerm + chain term`
   as the wire-v3 soundness error would be wrong by a wide margin.  **No sentence
   in this module says soundness is proved.**
5. **WHAT THE ASSEMBLY CONCLUSION IS.**  `RunLevelUnionBound.assemblyFailureEvent`
   is the failure of the adopted `SoundnessAssembly.explicit_good_draw_assembly`
   conclusion -- good-draw-conditional constraint vanishing at every row, the
   cell identification, the pinned WHIR parameters, and the
   `core c = core c₀` / `KhashCollision` disjunction.  It is NOT circuit truth.
   **Residue R1b is still assumed inside `SoundnessAssembly.AssemblyResidue`**
   and is not discharged here.  **ACCEPTANCE IS NEVER EXHIBITED**: no run of
   `Integrated.verify` returning `Except.ok ()` is constructed anywhere in this
   tree, so the failure event's hypotheses are not shown to be reachable by a
   real accepted transcript; that residue is inherited unchanged from
   `SoundnessAssembly` and RLUB.
6. **STAGE B IS PARTIAL, AND HERE IS EXACTLY WHAT IS AND IS NOT DELIVERED.**
   * DELIVERED, unconditionally: the dependence facts.
     `supplied_cells_index_free` -- the supplied cells
     `OpenedClaimFold.boundCell p.used idx cellIndex` do not depend on the index
     points at all; `index_bad_event_depends_on_row_point_only` -- two round
     states with the same `OpenedClaimFold.cellRow` give the SAME adopted
     `SoundnessAssembly.indexBadEvent`; and (section 5.1, at the explicit engine,
     under the envelope's `hdb` and the round count `hmlen` alone)
     `row_point_is_outer_draw_function` -- entry `r` of every bound cell's row
     point IS the reduction of the `rowCoord` coordinate of the run's own outer
     draw `InstalledRoundCommit.actualDigestDraw`, whence
     `row_point_determined_by_outer_draw`: two hashes with the SAME outer draw
     have the SAME row point.  That is dependence fact (ii) in full, in the form
     RLUB's contract states it.
   * DELIVERED, as an explicitly named hypothesis: `RowPointFixed`, which says
     the engine's COMMITTED cell family takes ONE value at every hash.  It is the
     exact content of "condition on the outer draw" at this cell, and under it
     `index_bad_event_at_is_constant` turns the hash-indexed index family into
     ONE adopted `IndexLanesOracle.guardedIndexBadEvent`, whose mass is at most
     `2 * ChallengeUnionBound.tauTerm` by the adopted
     `IndexLanesOracle.guarded_index_bad_event_mass_le`.
   * **NOT DELIVERED: the conditional count that would DISCHARGE
     `RowPointFixed`.**  The contract asked for a split of the oracle table
     finer than `RandomOracleSqueezes.frameSplit` -- frame half, outer challenge
     cells, index challenge cells -- so that the run's index digest AND the outer
     draw are fixed on the finer fibre and the index draw is uniform there.  That
     split is NOT built here, and THAT -- not any missing dependence fact -- is
     the whole residual obstruction.  What is missing, precisely: the fibre of
     `RandomOracleSqueezes.frameSplit` refined by fixing the challenge half on
     the OUTER schedule's cells only; the disjointness of those cells from the
     INDEX schedule's cells, which off RLUB's `runCombinedNonInjectiveEvent` is
     exactly `RunLevelUnionBound.run_combined_schedule_injective_off_clash`; and
     the adopted `RandomOracleSqueezes.restrict_ratio` at the COMBINED selector,
     which would make the pair (outer draw, index draw) jointly uniform on the
     product and hence the index draw uniform at each FIXED outer draw.  The
     COUNTING half of that argument IS delivered here, in the abstract, by
     section 0's `product_diagonal_card` / `product_diagonal_card_le`.  What is
     not delivered is its instantiation at RLUB's `runCombinedSchedule`, with the
     frame-fibre Fubini of `run_union_draw_probability_le_fibrewise` around it;
     that would give `P[index draw ∈ indexBadAt (outer draw)] ≤ 2 * tauTerm +
     P[clash]` with NO `RowPointFixed` hypothesis.  Until it is built every
     payoff below carries `RowPointFixed` visibly.
   * **SATISFIABILITY AND SCOPE OF `RowPointFixed`, stated precisely.**  Two
     witnesses.  `row_point_fixed_at_empty_columns`: a cell with NO committed
     columns (`cols cellIndex = []`), where the committed family is the empty
     list at every hash.  `row_point_fixed_at_constant_column`: a cell committing
     ONE CONSTANT column of the row's width, where the committed family is `[v]`
     at every hash, for every `v` -- a genuinely non-degenerate cell.  The
     adopted guard `IndexPointZeroCheck.CellsDifferOnCube` is live at both
     (`index_guard_is_live`, `guard_live_at_constant_column`), so the index event
     is not killed by its guard there.  **THE SCOPE IS NARROW, AND THE REASON IS
     STRUCTURAL.**  The committed cell is the multilinear extension of the column
     AT THE HASH-DEPENDENT ROW POINT, and `RowPointFixed` quantifies over ALL
     hashes; so it can hold only where each committed column's extension is
     CONSTANT along the realized row points.  At a NON-CONSTANT witness column it
     is expected to be FALSE, and it is not proved for one anywhere here.  Every
     payoff theorem below therefore covers CONSTANT committed columns only, until
     the finer split above is built.  Nothing more than that is claimed.
7. **STAGE A DOES NOT INSTANTIATE `OuterSequentialConditioning.PrefixDependent`,
   AND HERE IS WHY.**  That predicate is stated for `Fin m → A` coordinates, and
   the adopted joint space is `JointChallengeSpace.Draw d → DigestTriple`; the
   adopted `adaptive_union_mass_bound` is not available at this index type.  What
   IS used is the same Fubini peel that theorem is built from -- the adopted
   `OuterSequentialConditioning.invariant_fiber_card` -- as the ONE-COORDINATE
   conditional count `diagonal_mass_le` of section 0, together with the adopted
   per-alpha bounds `OuterSequentialConditioning.adaptive_outer_event_mass_le`
   (the coupled-round half) and `JointChallengeSpace.tau_bad_event_mass_le` (the
   tau half), which are themselves proved by sequential conditioning.  The
   adopted `adaptive_joint_union_bound` is NOT applied as a whole, because its
   third summand -- `JointChallengeSpace.alphaBadEvent` -- is a cylinder ON the
   alpha coordinate and therefore cannot be conditioned on it; that summand is
   left undiagonalized and weighed by the adopted
   `JointChallengeSpace.alpha_bad_event_mass_le`.  **The constant is unchanged**:
   `ChallengeUnionBound.combinedBound degreeBits q degreeBits constraints`, term
   for term.
8. **CHAIN-MODEL AND LENGTH-BUDGET RESIDUES, INHERITED.**  The additive clash
   term is ILO's `extendedDigestClashEvent`; its identification with the run's
   own digests is CCT's and ILO's, and RLUB's HONESTY (7) and (8) -- including
   the fact that `L = 381` admits only claims of width at most thirteen, while
   the deployed `indexBits = 8` claims can be two hundred fifty-six wide -- are
   unchanged.
9. **THE CLOSED INSTANCES ARE SATISFIABILITY WITNESSES, NOT THE DEPLOYED RUN.**
   Section 7 discharges every hypothesis of section 6 at RLUB's `unionConfig` /
   `unionProof` with empty truth lists, empty constraint coefficients and a cell
   with no committed columns.  Only the deployment data `(gdec, hash, khash, P,
   c₀)` and the call data stay free.  It shows the bound has content and is
   dischargeable; it does not describe the deployed configuration.  **THAT FIRST
   INSTANCE INHERITS RLUB'S OWN INDEX DEGENERACY**, and section 8 says so as a
   theorem rather than leaving it to be discovered: `unionProof.used` supplies
   only zeros (`union_supplied_cells_zero`), so against no committed columns the
   adopted guard fires and the index half is the EMPTY event
   (`union_index_half_is_empty`) -- `2 * ChallengeUnionBound.tauTerm 8` is pure
   slack there, and `index_guard_is_live` concerns an `x ≠ 0` that witness never
   supplies.  Section 8's second closed instance, at `liveProof` (the same config
   and the same thirteen coupled rounds, one non-zero cell per used claim) with
   one CONSTANT committed column, has the same right-hand side and a guard that
   is live exactly when `⟨x⟩ ≠ v` (at `⟨x⟩ = v` it is dead, as for the old witness)
   (`live_index_guard_is_live`, `assembly_failure_at_the_envelope_live`).  Every
   length budget RLUB discharges is re-discharged there at the same width one.

## Tactic note

No `set_option` is used, so the elaborator's default recursion budget applies.
The adopted `JointChallengeSpace`, `ChallengeUnionBound`,
`OuterSequentialConditioning` and `AdaptiveAgreementFamily` all raise
`maxRecDepth`, and at the default budget a membership `w ∈ E` in an event built
from `Finset.univ.filter` over the joint space cannot be transported by `exact`.
Every such step here is therefore routed through a FINSET EQUALITY (`rfl` or
`rw`) or through a general lemma whose events are abstract variables; that is why
section 3 splits `outerDiagonalEvent` by `outer_diagonal_eq` rather than by a
membership argument, and why `run_union_diagonal_subset` is stated with the two
families abstract.  `decide`, `native_decide`, `sorry`, `admit` and `axiom` do
not occur; `Fintype.card Element` and `Fintype.card Block` are never evaluated.

## `Finset.univ`, disclosed

`Finset.univ` occurs in this module's OWN definitions `diagonalEvent` and
`productDiagonalEvent`, and in the statements of the fibre-count lemmas
`diagonal_card_mul` and `product_diagonal_card`, where `∑ a : A` and
`∑ u : K1 → B` are the counting domains of the two Fubini peels.  It occurs once
more INDIRECTLY, in `runOuterStageEvent`, which is a wrapper around RLUB's
`runUnionBadEventAt` and inherits that definition's own
`Finset.univ.filter` over `OracleTable (boundedQueries L)`.  That is the same use
RLUB makes in its own fibre-count lemmas.  No tactic ever enumerates any of
them.
-/

namespace Audit.Wire3.TwoStageConditionalCount

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound

/-! ## 0. THE GENERAL CONDITIONAL COUNTS

Two of them: the ONE-COORDINATE count (`diagonal_mass_le`), where the family is
indexed by a coordinate the events themselves read -- which is why the cylinder
hypothesis `hinv` is load-bearing there -- and the TWO-GROUP count
(`product_diagonal_card_le`), where the indexing coordinates and the counted
coordinates are DISJOINT and no invariance hypothesis is needed.  Stage A uses
the first; the second is the counting core the finer table split of section 5
would use, and is stated here in the abstract only.  -/

section General

variable {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

open Classical in
/-- THE DIAGONAL EVENT of a family indexed by ONE coordinate of the draw itself. -/
noncomputable def diagonalEvent (k : ι) (F : A → Finset (ι → A)) : Finset (ι → A) :=
  Finset.univ.filter (fun w => w ∈ F (w k))

theorem mem_diagonalEvent (k : ι) (F : A → Finset (ι → A)) (w : ι → A) :
    w ∈ diagonalEvent k F ↔ w ∈ F (w k) := by
  classical
  simp only [diagonalEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- (0) THE FIBRE COUNT. -/
theorem diagonal_card_mul (k : ι) (F : A → Finset (ι → A))
    (hinv : ∀ (a : A) (w : ι → A) (b : A), Function.update w k b ∈ F a ↔ w ∈ F a) :
    (diagonalEvent k F).card * Fintype.card A = ∑ a : A, (F a).card := by
  classical
  have hfib : ∀ a : A,
      ((diagonalEvent k F).filter (fun w => w k = a)).card * Fintype.card A = (F a).card := by
    intro a
    have heq : (diagonalEvent k F).filter (fun w => w k = a)
        = (F a).filter (fun w => w k = a) := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, mem_diagonalEvent]
      constructor
      · rintro ⟨hw, hk⟩
        refine ⟨?_, hk⟩
        rw [hk] at hw
        exact hw
      · rintro ⟨hw, hk⟩
        refine ⟨?_, hk⟩
        rw [hk]
        exact hw
    rw [heq]
    exact OuterSequentialConditioning.invariant_fiber_card k (F a) (hinv a) a
  have hsum : (diagonalEvent k F).card
      = ∑ a : A, ((diagonalEvent k F).filter (fun w => w k = a)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun w : ι → A => w k)
      (t := (Finset.univ : Finset A)) (fun x _ => Finset.mem_univ _)
  rw [hsum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun a _ => hfib a)

/-- (0) **THE ONE-COORDINATE CONDITIONAL COUNT, MASS FORM.** -/
theorem diagonal_mass_le (k : ι) (F : A → Finset (ι → A)) (bound : ℚ)
    (hinv : ∀ (a : A) (w : ι → A) (b : A), Function.update w k b ∈ F a ↔ w ∈ F a)
    (hb : ∀ a : A, OuterSequentialConditioning.uniformMass (F a) ≤ bound)
    (hA : 0 < Fintype.card A) :
    OuterSequentialConditioning.uniformMass (diagonalEvent k F) ≤ bound := by
  classical
  have hN : 0 < Fintype.card (ι → A) := by
    rw [Fintype.card_fun]
    exact pow_pos hA _
  have hNQ : (0 : ℚ) < (Fintype.card (ι → A) : ℚ) := by exact_mod_cast hN
  have hAQ : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast hA
  have hcards : ∀ a : A, ((F a).card : ℚ) ≤ bound * (Fintype.card (ι → A) : ℚ) := by
    intro a
    have h := hb a
    rw [OuterSequentialConditioning.uniformMass, div_le_iff hNQ] at h
    exact h
  have hkey : ((diagonalEvent k F).card : ℚ) * (Fintype.card A : ℚ)
      = ∑ a : A, ((F a).card : ℚ) := by
    have h := diagonal_card_mul k F hinv
    have h2 : (((diagonalEvent k F).card * Fintype.card A : Nat) : ℚ)
        = ((∑ a : A, (F a).card : Nat) : ℚ) := by exact_mod_cast congrArg (fun n : Nat => n) h
    push_cast at h2
    exact h2
  have hle : ∑ a : A, ((F a).card : ℚ)
      ≤ (bound * (Fintype.card (ι → A) : ℚ)) * (Fintype.card A : ℚ) := by
    calc ∑ a : A, ((F a).card : ℚ)
        ≤ ∑ _a : A, bound * (Fintype.card (ι → A) : ℚ) :=
          Finset.sum_le_sum (fun a _ => hcards a)
      _ = (Fintype.card A : ℚ) * (bound * (Fintype.card (ι → A) : ℚ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (bound * (Fintype.card (ι → A) : ℚ)) * (Fintype.card A : ℚ) := by ring
  have hmul : ((diagonalEvent k F).card : ℚ) * (Fintype.card A : ℚ)
      ≤ (bound * (Fintype.card (ι → A) : ℚ)) * (Fintype.card A : ℚ) := by
    rw [hkey]; exact hle
  rw [OuterSequentialConditioning.uniformMass, div_le_iff hNQ]
  exact le_of_mul_le_mul_right hmul hAQ

/-- (0) THE DIAGONAL OF A UNION FAMILY IS THE UNION OF THE DIAGONALS. -/
theorem diagonal_union (k : ι) (F G : A → Finset (ι → A)) :
    diagonalEvent k (fun a => F a ∪ G a) = diagonalEvent k F ∪ diagonalEvent k G := by
  classical
  apply Finset.ext
  intro w
  rw [Finset.mem_union, mem_diagonalEvent, mem_diagonalEvent, mem_diagonalEvent]
  exact Finset.mem_union

/-- (0) THE DIAGONAL OF A CONSTANT FAMILY IS THAT CONSTANT. -/
theorem diagonal_const (k : ι) (B : Finset (ι → A)) : diagonalEvent k (fun _ => B) = B := by
  classical
  apply Finset.ext
  intro w
  exact mem_diagonalEvent k (fun _ => B) w

end General

section Product

variable {K1 K2 B : Type} [Fintype K1] [DecidableEq K1] [Fintype K2] [DecidableEq K2]
  [Fintype B] [DecidableEq B]

open Classical in
/-- THE TWO-GROUP DIAGONAL EVENT: the maps whose SECOND group of coordinates
lands in a family indexed by what the map does on the FIRST group.  This is the
shape the finer table split of section 5 needs -- first group the outer challenge
cells, second group the index challenge cells. -/
noncomputable def productDiagonalEvent (F : (K1 → B) → Finset (K2 → B)) :
    Finset (K1 ⊕ K2 → B) :=
  Finset.univ.filter (fun z => (fun k => z (Sum.inr k)) ∈ F (fun k => z (Sum.inl k)))

/-- (0) **THE TWO-GROUP CONDITIONAL COUNT.**  Disjoint coordinate groups are
independent, so the diagonal over a family indexed by the first group is counted
group by group. -/
theorem product_diagonal_card (F : (K1 → B) → Finset (K2 → B)) :
    (productDiagonalEvent F).card = ∑ u : K1 → B, (F u).card := by
  classical
  have he : productDiagonalEvent F = Finset.univ.filter (fun z : K1 ⊕ K2 → B =>
      (fun q : (K1 → B) × (K2 → B) => q.2 ∈ F q.1)
        (Equiv.sumArrowEquivProdArrow K1 K2 B z)) := by
    apply Finset.ext
    intro z
    simp only [productDiagonalEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.sumArrowEquivProdArrow]
    exact Iff.rfl
  rw [he, WhirChallenge.equiv_event_card (Equiv.sumArrowEquivProdArrow K1 K2 B)
    (fun q : (K1 → B) × (K2 → B) => q.2 ∈ F q.1),
    Finset.card_eq_sum_card_fiberwise (f := fun q : (K1 → B) × (K2 → B) => q.1)
      (t := (Finset.univ : Finset (K1 → B))) (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  refine Finset.card_bij (fun q _ => q.2) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have h1 := hq.1
    rw [hq.2] at h1
    exact h1
  · intro q1 hq1 q2 hq2 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
    exact Prod.ext (hq1.2.trans hq2.2.symm) h2
  · intro w hw
    refine ⟨(u, w), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hw, trivial⟩

/-- (0) **THE TWO-GROUP CONDITIONAL COUNT, MASS FORM.**  If every member of the
family is small, so is the diagonal -- with NO invariance hypothesis, because the
two groups of coordinates are disjoint rather than shared. -/
theorem product_diagonal_card_le (F : (K1 → B) → Finset (K2 → B)) (bound : ℚ)
    (hb : ∀ u : K1 → B, ((F u).card : ℚ) ≤ bound * (Fintype.card (K2 → B) : ℚ)) :
    ((productDiagonalEvent F).card : ℚ) ≤ bound * (Fintype.card (K1 ⊕ K2 → B) : ℚ) := by
  classical
  have hcard : ((productDiagonalEvent F).card : ℚ) = ∑ u : K1 → B, ((F u).card : ℚ) := by
    rw [product_diagonal_card]
    push_cast
    rfl
  have hsplit : (Fintype.card (K1 ⊕ K2 → B) : ℚ)
      = (Fintype.card (K1 → B) : ℚ) * (Fintype.card (K2 → B) : ℚ) := by
    rw [Fintype.card_congr (Equiv.sumArrowEquivProdArrow K1 K2 B), Fintype.card_prod]
    push_cast
    rfl
  rw [hcard, hsplit]
  calc ∑ u : K1 → B, ((F u).card : ℚ)
      ≤ ∑ _u : K1 → B, bound * (Fintype.card (K2 → B) : ℚ) :=
        Finset.sum_le_sum (fun u _ => hb u)
    _ = (Fintype.card (K1 → B) : ℚ) * (bound * (Fintype.card (K2 → B) : ℚ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = bound * ((Fintype.card (K1 → B) : ℚ) * (Fintype.card (K2 → B) : ℚ)) := by ring

end Product

/-! ## 1. The gate alpha IS a coordinate of the run's own outer draw -/

/-- (1) **THE ALPHA COORDINATE, UNCONDITIONALLY.** -/
theorem alpha_is_the_alpha_coordinate (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    TranscriptProvenance.gateAlphaElement thash c p
      = OuterChallenge.reduceTriple
          (SoundnessAssembly.actualDigestDraw thash c p JointChallengeSpace.Draw.gateAlpha) := by
  show OuterRound.lift (TranscriptProvenance.derived thash c p).gateAlpha = _
  rw [TranscriptProvenance.derived, OuterInitial.gate_alpha_follows_log_tau]
  exact rfl

/-- (1) The same at the name RLUB's fixed-event union uses. -/
theorem alpha_is_the_alpha_coordinate_run (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    TranscriptProvenance.gateAlphaElement thash c p
      = OuterChallenge.reduceTriple
          (InstalledRoundCommit.actualDigestDraw thash c p JointChallengeSpace.Draw.gateAlpha) :=
  alpha_is_the_alpha_coordinate thash c p

/-- (1) The two names of the run's outer draw agree. -/
theorem sa_draw_is_run_draw (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    SoundnessAssembly.actualDigestDraw thash c p
      = InstalledRoundCommit.actualDigestDraw thash c p := rfl

/-- (1) The alpha coordinate is NOT one of the outer coupled-round coordinates. -/
theorem gate_alpha_not_outer_coordinate (d : Nat) :
    (JointChallengeSpace.Draw.gateAlpha : JointChallengeSpace.Draw d)
      ∉ OuterSequentialConditioning.outerCoords d := by
  intro hx
  obtain ⟨i, -, hi, h⟩ := OuterSequentialConditioning.mem_roundCoords d d 0 _ hx
  rw [Nat.zero_add] at hi
  rcases h with h | h
  · rw [JointChallengeSpace.logProj_apply d i hi] at h
    exact JointChallengeSpace.Draw.noConfusion h
  · rw [JointChallengeSpace.gateProj_apply d i hi] at h
    exact JointChallengeSpace.Draw.noConfusion h

theorem gate_tau_ne_gate_alpha (d : Nat) (i : Fin d) :
    (JointChallengeSpace.Draw.gateTau i : JointChallengeSpace.Draw d)
      ≠ JointChallengeSpace.Draw.gateAlpha :=
  fun h => JointChallengeSpace.Draw.noConfusion h


/-! ## 2. THE ENGINE'S OUTER BAD EVENT DEPENDS ON THE HASH ONLY THROUGH THE ALPHA -/

/-- (2) The MESSAGE and TRUTH lists of the adopted `ConditionalSoundness.lane`
do not depend on the commit function, the challenge selector, or the incoming
round state: they are read off the proof's coupled messages and the supplied
truth lists.  Only the `challenge` field reads the transcript, and the adopted
`AdaptiveAgreementFamily.frozenLane` never reads it. -/
theorem lane_message_truth_congr (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (commit commit' : Verifier.CommitRound)
    (pick pick' : Verifier.RoundChallenges → Verifier.Ext3) :
    ∀ (ms : List Verifier.CoupledMessage) (truths : List (List Element))
      (s s' : Verifier.RoundState) (k : Nat),
      ((ConditionalSoundness.lane commit sel pick truths s ms).get? k).map
          ConditionalSoundness.LaneRound.message
        = ((ConditionalSoundness.lane commit' sel pick' truths s' ms).get? k).map
          ConditionalSoundness.LaneRound.message
      ∧ ((ConditionalSoundness.lane commit sel pick truths s ms).get? k).map
          ConditionalSoundness.LaneRound.truth
        = ((ConditionalSoundness.lane commit' sel pick' truths s' ms).get? k).map
          ConditionalSoundness.LaneRound.truth
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | _ :: _, _, _, _, 0 => ⟨rfl, rfl⟩
  | m :: ms, truths, s, s', k + 1 =>
      lane_message_truth_congr sel commit commit' pick pick' ms truths.tail
        (Verifier.roundStep commit s m) (Verifier.roundStep commit' s' m) k

/-- (2) THE DEGREE BOUND IS A STATEMENT ABOUT THE PROOF, NOT ABOUT THE ENGINE.
The same recursion: `message` and `truth` are read off the coupled messages and
the supplied truth lists, so a width bound along one lane execution is a width
bound along every other. -/
theorem lane_degree_bound_congr (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (commit commit' : Verifier.CommitRound)
    (pick pick' : Verifier.RoundChallenges → Verifier.Ext3) (n : Nat) :
    ∀ (ms : List Verifier.CoupledMessage) (truths : List (List Element))
      (s s' : Verifier.RoundState),
      (∀ r ∈ ConditionalSoundness.lane commit sel pick truths s ms,
        r.message.length ≤ n ∧ r.truth.length ≤ n) →
      ∀ r ∈ ConditionalSoundness.lane commit' sel pick' truths s' ms,
        r.message.length ≤ n ∧ r.truth.length ≤ n
  | [], _, _, _, _, _, hr => absurd hr (List.not_mem_nil _)
  | m :: ms, truths, s, s', h, r, hr => by
      rcases List.mem_cons.mp hr with h1 | h1
      · subst h1
        have hcons : ConditionalSoundness.lane commit sel pick truths s (m :: ms)
            = ⟨(sel m).map OuterRound.lift, truths.headD [],
                OuterRound.lift (pick (commit s.transcript s.roundIndex m.1 m.2))⟩ ::
              ConditionalSoundness.lane commit sel pick truths.tail
                (Verifier.roundStep commit s m) ms := rfl
        refine h ⟨(sel m).map OuterRound.lift, truths.headD [],
          OuterRound.lift (pick (commit s.transcript s.roundIndex m.1 m.2))⟩ ?_
        rw [hcons]
        exact List.mem_cons_self _ _
      · exact lane_degree_bound_congr sel commit commit' pick pick' n ms truths.tail
          (Verifier.roundStep commit s m) (Verifier.roundStep commit' s' m)
          (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) r h1

/-- (2) **THE LOG-LANE DEGREE HYPOTHESIS IS ENGINE-FREE.**  The `hlogDeg`
hypothesis carried by every mass bound below may therefore be checked at ANY
engine; it is a statement about the proof alone. -/
theorem log_lane_degree_engine_congr (E E' : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (logTruths : List (List Element)) (n : Nat)
    (h : ∀ r ∈ ConditionalSoundness.logLaneOf E c p logTruths,
      r.message.length ≤ n ∧ r.truth.length ≤ n) :
    ∀ r ∈ ConditionalSoundness.logLaneOf E' c p logTruths,
      r.message.length ≤ n ∧ r.truth.length ≤ n :=
  lane_degree_bound_congr Prod.fst E.commitRound E'.commitRound Verifier.RoundChallenges.log
    Verifier.RoundChallenges.log n (p.logRounds.zip p.gateRounds) logTruths
    (Verifier.start (E.initialTranscript c p)) (Verifier.start (E'.initialTranscript c p)) h

/-- (2) **THE GATE-LANE DEGREE HYPOTHESIS IS ENGINE-FREE**, by the same
recursion. -/
theorem gate_lane_degree_engine_congr (E E' : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gateTruths : List (List Element)) (n : Nat)
    (h : ∀ r ∈ ConditionalSoundness.gateLaneOf E c p gateTruths,
      r.message.length ≤ n ∧ r.truth.length ≤ n) :
    ∀ r ∈ ConditionalSoundness.gateLaneOf E' c p gateTruths,
      r.message.length ≤ n ∧ r.truth.length ≤ n :=
  lane_degree_bound_congr Prod.snd E.commitRound E'.commitRound Verifier.RoundChallenges.gate
    Verifier.RoundChallenges.gate n (p.logRounds.zip p.gateRounds) gateTruths
    (Verifier.start (E.initialTranscript c p)) (Verifier.start (E'.initialTranscript c p)) h

/-- (2) Two lane executions with the same messages and truths freeze to the SAME
adopted `Lane`. -/
theorem frozen_lane_congr (rs rs' : List ConditionalSoundness.LaneRound) (a b : Element)
    (own : Bool)
    (hm : ∀ k, (rs.get? k).map ConditionalSoundness.LaneRound.message
      = (rs'.get? k).map ConditionalSoundness.LaneRound.message)
    (ht : ∀ k, (rs.get? k).map ConditionalSoundness.LaneRound.truth
      = (rs'.get? k).map ConditionalSoundness.LaneRound.truth) :
    AdaptiveAgreementFamily.frozenLane rs a b own
      = AdaptiveAgreementFamily.frozenLane rs' a b own := by
  refine AdaptiveAgreementFamily.lane_eq _ _ ?_ ?_ rfl rfl rfl
  · funext xs
    show (((rs.get? _).map ConditionalSoundness.LaneRound.message).getD []) = _
    rw [hm]
    rfl
  · funext xs
    show (((rs.get? _).map ConditionalSoundness.LaneRound.truth).getD []) = _
    rw [ht]
    rfl

/-- (2) The adopted `SoundnessAssembly.logLane` is the SAME `Lane` at every
engine. -/
theorem log_lane_engine_congr (E E' : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (logTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) :
    SoundnessAssembly.logLane E c p logTruths t pr
      = SoundnessAssembly.logLane E' c p logTruths t pr :=
  frozen_lane_congr _ _ _ _ _
    (fun k => (lane_message_truth_congr Prod.fst E.commitRound E'.commitRound
      Verifier.RoundChallenges.log Verifier.RoundChallenges.log (p.logRounds.zip p.gateRounds)
      logTruths (Verifier.start (E.initialTranscript c p))
      (Verifier.start (E'.initialTranscript c p)) k).1)
    (fun k => (lane_message_truth_congr Prod.fst E.commitRound E'.commitRound
      Verifier.RoundChallenges.log Verifier.RoundChallenges.log (p.logRounds.zip p.gateRounds)
      logTruths (Verifier.start (E.initialTranscript c p))
      (Verifier.start (E'.initialTranscript c p)) k).2)

/-- THE GATE `Lane` WITH THE ALPHA SUPPLIED AS DATA. -/
noncomputable def gateLaneAt (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (gateTruths : List (List Element)) (alpha : Element) : OuterSequentialConditioning.Lane :=
  AdaptiveAgreementFamily.frozenLane (ConditionalSoundness.gateLaneOf E c p gateTruths) 0
    (GateClaimChain.endpointSum (Integrated.gateConfig c) gates
      (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs)) alpha s0) false

theorem gate_lane_is_gate_lane_at (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (gateTruths : List (List Element)) :
    SoundnessAssembly.gateLane thash E c p gates s0 gateTruths
      = gateLaneAt E c p gates s0 gateTruths
          (TranscriptProvenance.gateAlphaElement thash c p) := rfl

/-- (2) The gate `Lane` at a FIXED alpha is the same at two engines that hash the
public inputs alike. -/
theorem gate_lane_at_engine_congr (E E' : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (gateTruths : List (List Element)) (alpha : Element)
    (hph : E.publicInputsHash p.publicInputs = E'.publicInputsHash p.publicInputs) :
    gateLaneAt E c p gates s0 gateTruths alpha = gateLaneAt E' c p gates s0 gateTruths alpha := by
  rw [gateLaneAt, gateLaneAt, hph]
  exact frozen_lane_congr _ _ _ _ _
    (fun k => (lane_message_truth_congr Prod.snd E.commitRound E'.commitRound
      Verifier.RoundChallenges.gate Verifier.RoundChallenges.gate (p.logRounds.zip p.gateRounds)
      gateTruths (Verifier.start (E.initialTranscript c p))
      (Verifier.start (E'.initialTranscript c p)) k).1)
    (fun k => (lane_message_truth_congr Prod.snd E.commitRound E'.commitRound
      Verifier.RoundChallenges.gate Verifier.RoundChallenges.gate (p.logRounds.zip p.gateRounds)
      gateTruths (Verifier.start (E.initialTranscript c p))
      (Verifier.start (E'.initialTranscript c p)) k).2)

/-- THE TAU ZERO-CHECK VALUE with the alpha supplied as DATA. -/
def gateValueAt (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState) (alpha : Element) :
    Nat → Element :=
  ZeroCheckSemantics.gateValue (Integrated.gateConfig c) gates
    (GateTerminalBinding.publicHashFunction (E.publicInputsHash p.publicInputs)) alpha s0.tables

/-- **THE ALPHA-INDEXED OUTER BAD FAMILY.**  The adopted
`SoundnessAssembly.outerBadEvent` with the hash replaced by the one field of it
that event reads: the gate alpha. -/
noncomputable def outerBadAt (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (alpha : Element) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  OuterSequentialConditioning.adaptiveJointBadEvent c.degreeBits
    (SoundnessAssembly.logLane E c p logTruths t pr)
    (gateLaneAt E c p gates s0 gateTruths alpha)
    (gateValueAt E c p gates s0 alpha) (2 ^ c.degreeBits) coeffsOf

/-- (2) THE ADOPTED EVENT IS THE FAMILY AT THE RUN'S OWN ALPHA. -/
theorem outer_bad_event_is_outer_bad_at (thash : Transcript.Hash) (E : Verifier.Engine)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    SoundnessAssembly.outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf
      = outerBadAt E c p gates s0 logTruths gateTruths t pr coeffsOf
          (TranscriptProvenance.gateAlphaElement thash c p) := rfl

/-- (2) **`outerBadEvent` DEPENDS ON THE HASH ONLY THROUGH THE GATE ALPHA**, at
fixed engine data.  Formalizes dependence fact (i) of the contract. -/
theorem outer_bad_event_depends_on_alpha_only (thash thash' : Transcript.Hash)
    (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (h : TranscriptProvenance.gateAlphaElement thash c p
      = TranscriptProvenance.gateAlphaElement thash' c p) :
    SoundnessAssembly.outerBadEvent thash E c p gates s0 logTruths gateTruths t pr coeffsOf
      = SoundnessAssembly.outerBadEvent thash' E c p gates s0 logTruths gateTruths t pr coeffsOf := by
  rw [outer_bad_event_is_outer_bad_at, outer_bad_event_is_outer_bad_at, h]

/-- (2) **THE ENGINE'S OWN HASH-DEPENDENCE IS ABSORBED TOO.**  Two engines that
hash the public inputs alike give the SAME alpha-indexed family: the round
messages and truths of both lanes are read off the proof, not off the
transcript. -/
theorem outer_bad_at_engine_congr (E E' : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (alpha : Element)
    (hph : E.publicInputsHash p.publicInputs = E'.publicInputsHash p.publicInputs) :
    outerBadAt E c p gates s0 logTruths gateTruths t pr coeffsOf alpha
      = outerBadAt E' c p gates s0 logTruths gateTruths t pr coeffsOf alpha := by
  rw [outerBadAt, outerBadAt, log_lane_engine_congr E E' c p logTruths t pr,
    gate_lane_at_engine_congr E E' c p gates s0 gateTruths alpha hph, gateValueAt, gateValueAt, hph]

/-- (2) **AT THE EXPLICIT ENGINE, THE WHOLE HASH-DEPENDENCE OF THE ADOPTED OUTER
BAD EVENT IS THE ALPHA.**  The engine moves with the hash, and that movement is
absorbed: `th0` is an arbitrary reference hash and the right-hand side does not
depend on which one is chosen (`outer_bad_at_engine_congr`, since the explicit
engine's `publicInputsHash` is the constant
`PublicInputHashBinding.hashNoPad`). -/
theorem explicit_outer_bad_event_is_outer_bad_at (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash th0 : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    SoundnessAssembly.outerBadEvent thash (SoundnessAssembly.engine gdec hash thash khash P c₀)
        c p gates s0 logTruths gateTruths t pr coeffsOf
      = outerBadAt (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p gates s0 logTruths
          gateTruths t pr coeffsOf (TranscriptProvenance.gateAlphaElement thash c p) := by
  rw [outer_bad_event_is_outer_bad_at]
  exact outer_bad_at_engine_congr _ _ c p gates s0 logTruths gateTruths t pr coeffsOf _ rfl



/-! ## 3. STAGE A: THE ALPHA-CONDITIONED OUTER MASS -/

/-- (3) The adaptive outer lane event never reads the alpha coordinate. -/
theorem adaptive_lane_event_alpha_invariant (d : Nat) (L : OuterSequentialConditioning.Lane)
    (w : JointChallengeSpace.JointSpace d) (b : OuterChallenge.DigestTriple) :
    Function.update w JointChallengeSpace.Draw.gateAlpha b
        ∈ OuterSequentialConditioning.adaptiveLaneEvent d L
      ↔ w ∈ OuterSequentialConditioning.adaptiveLaneEvent d L :=
  OuterSequentialConditioning.adaptiveEvent_update_of_not_mem OuterSequentialConditioning.laneBad
    OuterSequentialConditioning.laneStep JointChallengeSpace.Draw.gateAlpha
    (OuterSequentialConditioning.outerCoords d) (gate_alpha_not_outer_coordinate d) L w b

/-- (3) Neither half of the adopted adaptive outer event reads the alpha
coordinate. -/
theorem adaptive_outer_event_alpha_invariant (d : Nat)
    (L1 L2 : OuterSequentialConditioning.Lane) (w : JointChallengeSpace.JointSpace d)
    (b : OuterChallenge.DigestTriple) :
    Function.update w JointChallengeSpace.Draw.gateAlpha b
        ∈ OuterSequentialConditioning.adaptiveOuterEvent d L1 L2
      ↔ w ∈ OuterSequentialConditioning.adaptiveOuterEvent d L1 L2 := by
  show Function.update w JointChallengeSpace.Draw.gateAlpha b
      ∈ (OuterSequentialConditioning.adaptiveLaneEvent d L1
        ∪ OuterSequentialConditioning.adaptiveLaneEvent d L2)
    ↔ w ∈ (OuterSequentialConditioning.adaptiveLaneEvent d L1
        ∪ OuterSequentialConditioning.adaptiveLaneEvent d L2)
  rw [Finset.mem_union, Finset.mem_union]
  exact or_congr (adaptive_lane_event_alpha_invariant d L1 w b)
    (adaptive_lane_event_alpha_invariant d L2 w b)

/-- (3) The adopted gate tau event never reads the alpha coordinate either. -/
theorem tau_bad_event_alpha_invariant (d : Nat) (g : Nat → Element)
    (w : JointChallengeSpace.JointSpace d) (b : OuterChallenge.DigestTriple) :
    Function.update w JointChallengeSpace.Draw.gateAlpha b ∈ JointChallengeSpace.tauBadEvent d g
      ↔ w ∈ JointChallengeSpace.tauBadEvent d g := by
  have h : JointChallengeSpace.tauReduction d
        (Function.update w JointChallengeSpace.Draw.gateAlpha b)
      = JointChallengeSpace.tauReduction d w := by
    funext i
    show OuterChallenge.reduceTriple _ = OuterChallenge.reduceTriple _
    rw [Function.update_noteq (gate_tau_ne_gate_alpha d i)]
  rw [JointChallengeSpace.tauBadEvent, JointChallengeSpace.mem_tauEvent,
    JointChallengeSpace.mem_tauEvent, h]

/-- THE ALPHA-INDEXED ADAPTIVE OUTER FAMILY, as a function of the alpha
COORDINATE of the draw. -/
noncomputable def outerRoundFamily (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (ds : OuterChallenge.DigestTriple) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  OuterSequentialConditioning.adaptiveOuterEvent c.degreeBits
    (SoundnessAssembly.logLane E c p logTruths t pr)
    (gateLaneAt E c p gates s0 gateTruths (OuterChallenge.reduceTriple ds))

/-- THE ALPHA-INDEXED GATE TAU FAMILY. -/
noncomputable def tauFamily (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (ds : OuterChallenge.DigestTriple) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  JointChallengeSpace.tauBadEvent c.degreeBits
    (gateValueAt E c p gates s0 (OuterChallenge.reduceTriple ds))

/-- THE ALPHA-INDEXED FULL OUTER BAD FAMILY. -/
noncomputable def outerBadFamily (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (ds : OuterChallenge.DigestTriple) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  outerBadAt E c p gates s0 logTruths gateTruths t pr coeffsOf (OuterChallenge.reduceTriple ds)

/-- THE ALPHA-COORDINATE FAMILY, which does NOT depend on the alpha VALUE. -/
noncomputable def alphaFamily (c : Verifier.Config) (coeffsOf : Nat → List Element) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  JointChallengeSpace.alphaBadEvent c.degreeBits (2 ^ c.degreeBits) coeffsOf

/-- THE DIAGONAL of the adaptive outer coupled-round family. -/
noncomputable def outerRoundDiagonal (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) : Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  diagonalEvent JointChallengeSpace.Draw.gateAlpha
    (outerRoundFamily E c p gates s0 logTruths gateTruths t pr)

/-- THE DIAGONAL of the adopted gate tau family. -/
noncomputable def tauDiagonal (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  diagonalEvent JointChallengeSpace.Draw.gateAlpha (tauFamily E c p gates s0)

/-- **THE STAGE-A EVENT**: the points of the adopted ONE joint space that lie in
the engine's outer bad set AT THEIR OWN ALPHA COORDINATE. -/
noncomputable def outerDiagonalEvent (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    Finset (JointChallengeSpace.JointSpace c.degreeBits) :=
  diagonalEvent JointChallengeSpace.Draw.gateAlpha
    (outerBadFamily E c p gates s0 logTruths gateTruths t pr coeffsOf)

/-- (3) THE ALPHA-INDEXED FAMILY IS THE UNION OF ITS THREE PARTS.  The adopted
`OuterSequentialConditioning.adaptiveJointBadEvent` is that union by
definition. -/
theorem outer_bad_family_eq (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    (fun ds => (outerRoundFamily E c p gates s0 logTruths gateTruths t pr ds
        ∪ tauFamily E c p gates s0 ds) ∪ (fun _ => alphaFamily c coeffsOf) ds)
      = outerBadFamily E c p gates s0 logTruths gateTruths t pr coeffsOf := rfl

/-- (3) **THE THREE-WAY SPLIT OF THE STAGE-A EVENT.**  The alpha family is NOT
diagonalized -- it does not depend on the alpha VALUE at all, only on the alpha
COORDINATE -- so the adopted `JointChallengeSpace.alpha_bad_event_mass_le` weighs
it unchanged. -/
theorem outer_diagonal_eq (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    outerDiagonalEvent E c p gates s0 logTruths gateTruths t pr coeffsOf
      = (outerRoundDiagonal E c p gates s0 logTruths gateTruths t pr
          ∪ tauDiagonal E c p gates s0) ∪ alphaFamily c coeffsOf := by
  rw [outerDiagonalEvent, ← outer_bad_family_eq E c p gates s0 logTruths gateTruths t pr coeffsOf,
    diagonal_union, diagonal_union, diagonal_const, outerRoundDiagonal, tauDiagonal]

/-- (3) THE COUPLED-ROUND HALF OF STAGE A. -/
theorem outer_round_diagonal_mass_le (E : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (q : Nat) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf E c p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf E c p gateTruths,
      r.message.length ≤ q + 2 ∧ r.truth.length ≤ q + 2) :
    JointChallengeSpace.jointProbability c.degreeBits
        (outerRoundDiagonal E c p gates s0 logTruths gateTruths t pr)
      ≤ ChallengeUnionBound.outerTerm c.degreeBits q := by
  rw [OuterSequentialConditioning.jointProbability_eq_uniformMass, outerRoundDiagonal]
  refine diagonal_mass_le _ _ _ ?_ ?_ JointChallengeSpace.digest_triple_card_pos
  · intro a w b
    exact adaptive_outer_event_alpha_invariant _ _ _ w b
  · intro a
    rw [← OuterSequentialConditioning.jointProbability_eq_uniformMass]
    exact OuterSequentialConditioning.adaptive_outer_event_mass_le c.degreeBits q _ _
      (SoundnessAssembly.frozen_lane_bounded _ _ _ _ 5 hlogDeg) rfl
      (SoundnessAssembly.frozen_lane_bounded _ _ _ _ (q + 2) hgateDeg) rfl

/-- (3) THE TAU HALF OF STAGE A. -/
theorem tau_diagonal_mass_le (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState) :
    JointChallengeSpace.jointProbability c.degreeBits (tauDiagonal E c p gates s0)
      ≤ ChallengeUnionBound.tauTerm c.degreeBits := by
  rw [OuterSequentialConditioning.jointProbability_eq_uniformMass, tauDiagonal]
  refine diagonal_mass_le _ _ _ (fun a w b => tau_bad_event_alpha_invariant _ _ _ _) ?_
    JointChallengeSpace.digest_triple_card_pos
  intro a
  rw [← OuterSequentialConditioning.jointProbability_eq_uniformMass]
  exact JointChallengeSpace.tau_bad_event_mass_le c.degreeBits _

/-- (3) **STAGE A.  THE ALPHA-CONDITIONED OUTER DIAGONAL HAS MASS AT MOST THE
ADOPTED `combinedBound`** -- the SAME constant the prefix-frozen
`JointChallengeSpace.joint_union_bound` and the adopted
`OuterSequentialConditioning.adaptive_joint_union_bound` get.  Nothing is lost by
conditioning on the alpha. -/
theorem stage_a_mass_le (E : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (q constraints : Nat) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (hlogDeg : ∀ r ∈ ConditionalSoundness.logLaneOf E c p logTruths,
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ ConditionalSoundness.gateLaneOf E c p gateTruths,
      r.message.length ≤ q + 2 ∧ r.truth.length ≤ q + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    JointChallengeSpace.jointProbability c.degreeBits
        (outerDiagonalEvent E c p gates s0 logTruths gateTruths t pr coeffsOf)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints := by
  rw [outer_diagonal_eq, alphaFamily, ChallengeUnionBound.combinedBound]
  have h1 := outer_round_diagonal_mass_le E c p q gates s0 logTruths gateTruths t pr hlogDeg
    hgateDeg
  have h2 := tau_diagonal_mass_le E c p gates s0
  have h3 := JointChallengeSpace.alpha_bad_event_mass_le c.degreeBits (2 ^ c.degreeBits)
    constraints coeffsOf hclen
  have hu1 := JointChallengeSpace.joint_probability_union_le c.degreeBits
    (outerRoundDiagonal E c p gates s0 logTruths gateTruths t pr ∪ tauDiagonal E c p gates s0)
    (JointChallengeSpace.alphaBadEvent c.degreeBits (2 ^ c.degreeBits) coeffsOf)
  have hu2 := JointChallengeSpace.joint_probability_union_le c.degreeBits
    (outerRoundDiagonal E c p gates s0 logTruths gateTruths t pr) (tauDiagonal E c p gates s0)
  linarith



/-! ## 4. TRANSPORT OF STAGE A ONTO THE ORACLE TABLE -/

/-- (4) **THE BRIDGE FROM THE HASH-INDEXED EVENT TO A FIXED PAIR.**  Stated with
the two families ABSTRACT, so that nothing about the engine is unfolded here: if
the outer family at every hash IS the fixed alpha-indexed family read at that
hash's OWN alpha coordinate, and the index family is constant, then RLUB's
hash-indexed union event sits inside RLUB's FIXED-event union at the DIAGONAL. -/
theorem run_union_diagonal_subset (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (F : OuterChallenge.DigestTriple → Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EJat : Transcript.Hash → Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EIat : Transcript.Hash → Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (EI0 : Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (hJ : ∀ th, EJat th
      = F (InstalledRoundCommit.actualDigestDraw th c p JointChallengeSpace.Draw.gateAlpha))
    (hI : ∀ th, EIat th = EI0) :
    RunLevelUnionBound.runUnionBadEventAt L c p EJat EIat
      ⊆ RunLevelUnionBound.runUnionBadEvent L c p
          (diagonalEvent JointChallengeSpace.Draw.gateAlpha F) EI0 := by
  classical
  intro T hT
  rw [RunLevelUnionBound.runUnionBadEventAt, Finset.mem_filter] at hT
  rw [RunLevelUnionBound.runUnionBadEvent, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases hT.2 with h | h
  · rw [hJ, sa_draw_is_run_draw] at h
    left
    rw [mem_diagonalEvent]
    exact h
  · rw [hI] at h
    exact Or.inr h

/-- (4) **THE ENGINE'S OWN OUTER BAD EVENT IS THE ALPHA-INDEXED FAMILY READ AT
THE RUN'S OWN ALPHA COORDINATE.**  A Finset equality, with no hypothesis: the
engine's hash-dependence is absorbed by section 2 and the alpha's by section 1. -/
theorem explicit_outer_bad_event_is_the_family (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (th0 : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 : GateTerminalBinding.ProverState) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (thash : Transcript.Hash) :
    SoundnessAssembly.outerBadEvent thash (SoundnessAssembly.engine gdec hash thash khash P c₀)
        c p gates s0 logTruths gateTruths t pr coeffsOf
      = outerBadFamily (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p gates s0 logTruths
          gateTruths t pr coeffsOf
          (InstalledRoundCommit.actualDigestDraw thash c p JointChallengeSpace.Draw.gateAlpha) := by
  rw [explicit_outer_bad_event_is_outer_bad_at gdec hash thash th0 khash P c₀ c p gates s0
    logTruths gateTruths t pr coeffsOf, outerBadFamily, ← alpha_is_the_alpha_coordinate_run]


/-- (4) The empty index event carries no mass. -/
theorem index_probability_empty (bits : Nat) :
    IndexPointZeroCheck.indexProbability bits (∅ : Finset (InstalledIndexSampler.IndexSpace bits))
      = 0 := by
  rw [IndexPointZeroCheck.indexProbability, Finset.card_empty, Nat.cast_zero, zero_div]

open Classical in
/-- **THE TRANSPORTED STAGE-A EVENT.**  The tables on which the run's OWN outer
draw lands in the explicit engine's OWN outer bad event, both read at the
TABLE'S own hash.  Its index half is empty, so it weighs the outer lane alone. -/
noncomputable def runOuterStageEvent (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) :
    Finset (OracleTable (boundedQueries L)) :=
  RunLevelUnionBound.runUnionBadEventAt L c p
    (fun th => SoundnessAssembly.outerBadEvent th
      (SoundnessAssembly.engine gdec hash th khash P c₀) c p gates s0 logTruths gateTruths t pr
      coeffsOf)
    (fun _ => (∅ : Finset (InstalledIndexSampler.IndexSpace c.indexBits)))

/-- (4) **THE TRANSPORT OF STAGE A ONTO THE ORACLE TABLE**, for a fixed
(non-adaptive) prover under the random oracle model: the mass of the tables whose
own outer draw lands in the engine's own outer bad event -- at the table's own
hash, engine and alpha both moving with it -- is at most the STAGE-A constant
plus ILO's one chain-clash term. -/
theorem run_outer_stage_mass_le (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (c : Verifier.Config)
    (p : Verifier.Proof) (gates : List Gates.GateInfo) (s0 : GateTerminalBinding.ProverState)
    (logTruths gateTruths : List (List Element)) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element) (th0 : Transcript.Hash)
    (q constraints : Nat)
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
        (runOuterStageEvent L gdec hash khash P c₀ c p gates s0 logTruths gateTruths t pr coeffsOf)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + oracleProbability (boundedQueries L)
            (IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
              (roundMessages p) p.used c.degreeBits hlenI) := by
  have hsub := oracle_probability_mono (boundedQueries L) _ _
    (run_union_diagonal_subset L c p
      (outerBadFamily (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p gates s0 logTruths
        gateTruths t pr coeffsOf) _ _ (∅ : Finset (InstalledIndexSampler.IndexSpace c.indexBits))
      (fun th => explicit_outer_bad_event_is_the_family gdec hash khash P c₀ th0 c p gates s0
        logTruths gateTruths t pr coeffsOf th) (fun _ => rfl))
  have h0 := RunLevelUnionBound.run_union_draw_probability_le_fibrewise L c p hL hlenI hlenP hmlen
    (diagonalEvent JointChallengeSpace.Draw.gateAlpha
      (outerBadFamily (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p gates s0 logTruths
        gateTruths t pr coeffsOf))
    (∅ : Finset (InstalledIndexSampler.IndexSpace c.indexBits))
  have h1 := stage_a_mass_le (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p q constraints
    gates s0 logTruths gateTruths t pr coeffsOf hlogDeg hgateDeg hclen
  have h2 := index_probability_empty c.indexBits
  have h3 := oracle_probability_mono (boundedQueries L) _ _
    (RunLevelUnionBound.run_combined_non_injective_subset_clash L c p hL hdb hbb hlenI hlenP hmlen)
  rw [runOuterStageEvent]
  rw [outerDiagonalEvent] at h1
  linarith


/-! ## 5. STAGE B: THE INDEX EVENT CONDITIONED ON THE OUTER DRAW

Section 5.1 completes RLUB's dependence fact (ii): the row point of every bound
cell is a function of the run's OWN outer draw, entry by entry.  The conditioning
itself is still carried as the named hypothesis `RowPointFixed` of section 5.2.

**THE CONTRACT FOR THE FOLLOW-UP MODULE**, stated so that it can be picked up
without re-deriving anything here.  Let `f` range over
`RandomOracleSqueezes.FrameHalf (boundedQueries L) → Block` and `g` over the
challenge half, as in RLUB's `run_union_fibre_count_le`.  On a fibre where RLUB's
`runCombinedSchedule L c p` is injective -- off `runCombinedNonInjectiveEvent`,
by `run_combined_schedule_injective_off_clash` -- the outer schedule's cells and
the index schedule's cells are DISJOINT, so `restrict_ratio` at the COMBINED
selector makes `(outer draw, index draw)` jointly uniform on the product.  The
follow-up module must (i) build that combined selector into
`ChallengeHalf (boundedQueries L)` exactly as `run_joint_fibre_count` and
`run_index_fibre_count` build their two, (ii) apply this module's
`product_diagonal_card_le` with `K1` the outer schedule's index type, `K2` the
index schedule's, and `F u` the index bad event AT the outer draw encoded by `u`
-- whose per-`u` mass is at most `2 * ChallengeUnionBound.tauTerm c.indexBits` by
the adopted `IndexLanesOracle.guarded_index_bad_event_mass_le`, the row point
being a function of that outer draw by section 5.1 -- and (iii) run the frame
fibre Fubini of `run_union_draw_probability_le_fibrewise` around it.  The
conclusion would be `P[index draw ∈ indexBadAt (outer draw)] ≤
2 * tauTerm + P[clash]` with NO `RowPointFixed` hypothesis, and would replace
that hypothesis in every payoff of sections 6-8.  None of (i)-(iii) is done
here. -/

/-- (5) **THE SUPPLIED CELLS DO NOT DEPEND ON THE INDEX POINTS AT ALL.** -/
theorem supplied_cells_index_free (u : Verifier.UsedClaims) (idx idx' : Verifier.IndexPoints)
    (i : Fin 5) :
    (OpenedClaimFold.boundCell u idx i).1 = (OpenedClaimFold.boundCell u idx' i).1 := by
  fin_cases i <;> rfl

/-- (5) **THE INDEX BAD EVENT DEPENDS ON THE ROUND STATE ONLY THROUGH THE ROW
POINT.**  Dependence fact (ii) of the contract, as a Finset equality. -/
theorem index_bad_event_depends_on_row_point_only (bits : Nat) (u : Verifier.UsedClaims)
    (idx idx' : Verifier.IndexPoints) (s s' : Verifier.RoundState) (cellIndex : Fin 5)
    (cols : List (List Element))
    (h : OpenedClaimFold.cellRow s cellIndex = OpenedClaimFold.cellRow s' cellIndex) :
    SoundnessAssembly.indexBadEvent bits
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell u idx cellIndex).1)
        (IndexPointZeroCheck.openedCells cols
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow s cellIndex)))
      = SoundnessAssembly.indexBadEvent bits
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell u idx' cellIndex).1)
        (IndexPointZeroCheck.openedCells cols
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow s' cellIndex))) := by
  rw [h, supplied_cells_index_free u idx idx' cellIndex]

/-! ### 5.1 THE ROW POINT IS A FUNCTION OF THE RUN'S OWN OUTER DRAW -/

/-- (5) The row point has the SAME length at every hash: the number of coupled
rounds of the (fixed) proof. -/
theorem cell_row_length (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ c : Verifier.Config) (p : Verifier.Proof) (cellIndex : Fin 5) (th : Transcript.Hash) :
    (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
        cellIndex).length
      = (p.logRounds.zip p.gateRounds).length := by
  have h := Verifier.runRounds_lengths
    (SoundnessAssembly.engine gdec hash th khash P c₀).commitRound
    (Verifier.start ((SoundnessAssembly.engine gdec hash th khash P c₀).initialTranscript c p))
    (p.logRounds.zip p.gateRounds)
  fin_cases cellIndex
  · show (Verifier.derivedRounds _ _ _).logPoint.length = _
    exact h.2.1.trans (Nat.zero_add _)
  · show (Verifier.derivedRounds _ _ _).logPoint.length = _
    exact h.2.1.trans (Nat.zero_add _)
  · show (Verifier.derivedRounds _ _ _).logPoint.length = _
    exact h.2.1.trans (Nat.zero_add _)
  · show (Verifier.derivedRounds _ _ _).gatePoint.length = _
    exact h.2.2.trans (Nat.zero_add _)
  · show (Verifier.derivedRounds _ _ _).gatePoint.length = _
    exact h.2.2.trans (Nat.zero_add _)

/-- (5) The explicit engine's LOG row point IS the adopted
`InstalledRoundCommit.actualChain` read through `logChallengeOf`.  The only
hypothesis is the envelope's `hdb`; no acceptance is assumed. -/
theorem explicit_log_point_is_chain (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (th : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) :
    (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p).logPoint
      = (InstalledRoundCommit.actualChain th c p).map (InstalledRoundCommit.logChallengeOf th) :=
  (ComposedEngine.composed_round_digests_chain_after_prefix
    (ExplicitEngine.explicitBase hash khash P c₀) gdec hash th P c₀ c p hdb).2.2.2.2.1

/-- (5) The same for the GATE row point. -/
theorem explicit_gate_point_is_chain (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (th : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) :
    (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p).gatePoint
      = (InstalledRoundCommit.actualChain th c p).map (InstalledRoundCommit.gateChallengeOf th) :=
  (ComposedEngine.composed_round_digests_chain_after_prefix
    (ExplicitEngine.explicitBase hash khash P c₀) gdec hash th P c₀ c p hdb).2.2.2.2.2

/-- (5) **ENTRY `r` OF THE LOG ROW POINT IS THE `outerLog r` COORDINATE OF THE
RUN'S OWN OUTER DRAW.** -/
theorem log_point_entry_is_outer_draw (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (th : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) (hmlen : (roundMessages p).length = c.degreeBits)
    (r : Nat) (hr : r < c.degreeBits) :
    (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p).logPoint.get?
        r
      = some ((OuterChallenge.reduceTriple
          (InstalledRoundCommit.actualDigestDraw th c p
            (JointChallengeSpace.Draw.outerLog ⟨r, hr⟩))).toVerifier) := by
  rw [explicit_log_point_is_chain gdec hash th khash P c₀ c p hdb]
  have hz : (p.logRounds.zip p.gateRounds).length = c.degreeBits := hmlen
  have hlen : r < (InstalledRoundCommit.actualChain th c p).length := by
    rw [InstalledRoundCommit.actualChain, InstalledRoundCommit.concrete_chain_length, hz]
    exact hr
  rw [List.get?_eq_getElem?, List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some']
  show some (InstalledRoundCommit.logChallengeOf th _)
    = some (InstalledRoundCommit.logChallengeOf th
        (((InstalledRoundCommit.actualChain th c p).get? r).getD
          (InstalledRoundCommit.actualBase th c p)))
  rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hlen]
  rfl

/-- (5) **ENTRY `r` OF THE GATE ROW POINT IS THE `outerGate r` COORDINATE.** -/
theorem gate_point_entry_is_outer_draw (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (th : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) (hmlen : (roundMessages p).length = c.degreeBits)
    (r : Nat) (hr : r < c.degreeBits) :
    (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p).gatePoint.get?
        r
      = some ((OuterChallenge.reduceTriple
          (InstalledRoundCommit.actualDigestDraw th c p
            (JointChallengeSpace.Draw.outerGate ⟨r, hr⟩))).toVerifier) := by
  rw [explicit_gate_point_is_chain gdec hash th khash P c₀ c p hdb]
  have hz : (p.logRounds.zip p.gateRounds).length = c.degreeBits := hmlen
  have hlen : r < (InstalledRoundCommit.actualChain th c p).length := by
    rw [InstalledRoundCommit.actualChain, InstalledRoundCommit.concrete_chain_length, hz]
    exact hr
  rw [List.get?_eq_getElem?, List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some']
  show some (InstalledRoundCommit.gateChallengeOf th _)
    = some (InstalledRoundCommit.gateChallengeOf th
        (((InstalledRoundCommit.actualChain th c p).get? r).getD
          (InstalledRoundCommit.actualBase th c p)))
  rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hlen]
  rfl

/-- THE OUTER-DRAW COORDINATE each bound cell's row point entry reads: the three
log cells read `outerLog`, the two gate cells `outerGate`. -/
def rowCoord (d : Nat) : Fin 5 → Fin d → JointChallengeSpace.Draw d
  | 0, r => JointChallengeSpace.Draw.outerLog r
  | 1, r => JointChallengeSpace.Draw.outerLog r
  | 2, r => JointChallengeSpace.Draw.outerLog r
  | 3, r => JointChallengeSpace.Draw.outerGate r
  | 4, r => JointChallengeSpace.Draw.outerGate r

/-- (5) **THE ROW POINT OF EVERY BOUND CELL IS A FUNCTION OF THE RUN'S OWN OUTER
DRAW, ENTRY BY ENTRY.**  This completes dependence fact (ii) of RLUB's contract:
`Verifier.start` reads only `i.transcript`, so the initial transcript's log-tau
column does NOT enter the row point; what does enter is exactly the coupled-round
coordinates of the adopted `InstalledRoundCommit.actualDigestDraw`. -/
theorem row_point_is_outer_draw_function (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (th : Transcript.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (hdb : c.degreeBits ≤ 13) (hmlen : (roundMessages p).length = c.degreeBits)
    (cellIndex : Fin 5) (r : Nat) (hr : r < c.degreeBits) :
    (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
        cellIndex).get? r
      = some ((OuterChallenge.reduceTriple
          (InstalledRoundCommit.actualDigestDraw th c p
            (rowCoord c.degreeBits cellIndex ⟨r, hr⟩))).toVerifier) := by
  fin_cases cellIndex
  · exact log_point_entry_is_outer_draw gdec hash th khash P c₀ c p hdb hmlen r hr
  · exact log_point_entry_is_outer_draw gdec hash th khash P c₀ c p hdb hmlen r hr
  · exact log_point_entry_is_outer_draw gdec hash th khash P c₀ c p hdb hmlen r hr
  · exact gate_point_entry_is_outer_draw gdec hash th khash P c₀ c p hdb hmlen r hr
  · exact gate_point_entry_is_outer_draw gdec hash th khash P c₀ c p hdb hmlen r hr

/-- (5) **TWO HASHES WITH THE SAME OUTER DRAW HAVE THE SAME ROW POINT**, as whole
lists.  Dependence fact (ii), in the form RLUB's contract states it. -/
theorem row_point_determined_by_outer_draw (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (th th' : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ c : Verifier.Config) (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (hdraw : InstalledRoundCommit.actualDigestDraw th c p
      = InstalledRoundCommit.actualDigestDraw th' c p) (cellIndex : Fin 5) :
    OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p) cellIndex
      = OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th' khash P c₀) c p)
        cellIndex := by
  have hz : (p.logRounds.zip p.gateRounds).length = c.degreeBits := hmlen
  have hl := (cell_row_length gdec hash khash P c₀ c p cellIndex th).trans hz
  have hl' := (cell_row_length gdec hash khash P c₀ c p cellIndex th').trans hz
  refine List.ext_get? (fun k => ?_)
  by_cases hk : k < c.degreeBits
  · rw [row_point_is_outer_draw_function gdec hash th khash P c₀ c p hdb hmlen cellIndex k hk,
      row_point_is_outer_draw_function gdec hash th' khash P c₀ c p hdb hmlen cellIndex k hk,
      hdraw]
  · rw [List.get?_eq_none.mpr (by omega), List.get?_eq_none.mpr (by omega)]

/-- THE STAGE-B CONDITIONING, NAMED.  `RowPointFixed` says the engine's COMMITTED
cell family -- the only part of the adopted `SoundnessAssembly.indexBadEvent`
that moves with the hash -- takes one value at every hash.  It is the exact
content of "condition on the outer draw" at this cell, and section 5's
`row_point_fixed_at_empty_columns` exhibits a run at which it holds. -/
def RowPointFixed (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ c : Verifier.Config) (p : Verifier.Proof) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (committed0 : List Element) : Prop :=
  ∀ th : Transcript.Hash, IndexPointZeroCheck.openedCells (cols cellIndex)
      (OpenedClaimFold.lift (OpenedClaimFold.cellRow
        (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
        cellIndex)) = committed0

/-- (5) Under `RowPointFixed` the engine's whole index family is ONE fixed
adopted `IndexLanesOracle.guardedIndexBadEvent`. -/
theorem index_bad_event_at_is_constant (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ c : Verifier.Config) (p : Verifier.Proof) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) (committed0 : List Element)
    (idx0 : Verifier.IndexPoints)
    (hrow : RowPointFixed gdec hash khash P c₀ c p cellIndex cols committed0)
    (th : Transcript.Hash) :
    SoundnessAssembly.indexBadEvent c.indexBits
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
          (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
          cellIndex).1)
        (IndexPointZeroCheck.openedCells (cols cellIndex)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow
            (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
            cellIndex)))
      = IndexLanesOracle.guardedIndexBadEvent c.indexBits
          (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx0 cellIndex).1) committed0 := by
  rw [hrow th, supplied_cells_index_free p.used
    (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash th khash P c₀) c p) idx0 cellIndex]
  rfl

/-- (5) **`RowPointFixed` IS SATISFIABLE**: at a cell with no committed columns
the committed family is the empty list at every hash. -/
theorem row_point_fixed_at_empty_columns (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (cellIndex : Fin 5) :
    RowPointFixed gdec hash khash P c₀ c p cellIndex (fun _ => []) [] := fun _ => rfl

/-- (5) Shift lemma for the adopted eq weights: reading bits from `j + 1` on `i`
is reading bits from `j` on `i / 2`. -/
theorem rowProdFrom_succ :
    ∀ (rest : List Element) (j i : Nat),
      EqTableProvenance.rowProdFrom (j + 1) rest i = EqTableProvenance.rowProdFrom j rest (i / 2)
  | [], _, _ => rfl
  | t :: rest, j, i => by
      show EqTableProvenance.bitFactor t (j + 1) i
          * EqTableProvenance.rowProdFrom (j + 1 + 1) rest i
        = EqTableProvenance.bitFactor t j (i / 2)
          * EqTableProvenance.rowProdFrom (j + 1) rest (i / 2)
      rw [rowProdFrom_succ rest (j + 1) i]
      congr 1
      unfold EqTableProvenance.bitFactor
      rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm (2 ^ j) 2]

/-- (5) A sum over an even range, paired. -/
theorem list_sum_range_two_mul (g : Nat → Element) :
    ∀ N : Nat, ((List.range (2 * N)).map g).sum
      = ((List.range N).map (fun m => g (2 * m) + g (2 * m + 1))).sum
  | 0 => rfl
  | N + 1 => by
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ,
        List.map_append, List.map_append, List.sum_append, List.sum_append,
        list_sum_range_two_mul g N, List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring

/-- (5) The adopted eq weights sum to `1` over the cube. -/
theorem sum_rowProd :
    ∀ tau : List Element,
      ((List.range (2 ^ tau.length)).map (fun i => EqTableProvenance.rowProdFrom 0 tau i)).sum = 1
  | [] => by
      have h1 : List.range (2 ^ ([] : List Element).length) = [0] := rfl
      rw [h1]
      simp [EqTableProvenance.rowProdFrom]
  | t :: rest => by
      rw [List.length_cons, pow_succ, mul_comm, list_sum_range_two_mul]
      have hterm : ∀ m : Nat,
          EqTableProvenance.rowProdFrom 0 (t :: rest) (2 * m)
            + EqTableProvenance.rowProdFrom 0 (t :: rest) (2 * m + 1)
          = EqTableProvenance.rowProdFrom 0 rest m := by
        intro m
        show EqTableProvenance.bitFactor t 0 (2 * m)
              * EqTableProvenance.rowProdFrom (0 + 1) rest (2 * m)
            + EqTableProvenance.bitFactor t 0 (2 * m + 1)
              * EqTableProvenance.rowProdFrom (0 + 1) rest (2 * m + 1)
          = EqTableProvenance.rowProdFrom 0 rest m
        rw [rowProdFrom_succ, rowProdFrom_succ]
        have h1 : 2 * m / 2 = m := by omega
        have h2 : (2 * m + 1) / 2 = m := by omega
        rw [h1, h2]
        unfold EqTableProvenance.bitFactor
        rw [pow_zero, Nat.div_one, Nat.div_one]
        have h3 : 2 * m % 2 = 0 := by omega
        have h4 : (2 * m + 1) % 2 = 1 := by omega
        rw [h3, h4]
        simp only [if_true, one_ne_zero, if_false]
        ring
      rw [List.map_congr_left (fun m _ => hterm m)]
      exact sum_rowProd rest

/-- (5) The adopted multilinear extension of a CONSTANT column of the row's width
is that constant, at EVERY row point. -/
theorem extension_const (v : Element) (tau : List Element) :
    ZeroCheckSemantics.extension (List.replicate (2 ^ tau.length) v) tau = v := by
  unfold ZeroCheckSemantics.extension ZeroCheckSemantics.extensionOf
  have hcong : ∀ i ∈ List.range (2 ^ tau.length),
      EqTableProvenance.rowProdFrom 0 tau i * (List.replicate (2 ^ tau.length) v).getD i 0
        = v * EqTableProvenance.rowProdFrom 0 tau i := by
    intro i hi
    rw [List.getD_eq_getElem?, List.getElem?_replicate_of_lt (List.mem_range.mp hi)]
    simp only [Option.getD_some]
    ring
  rw [List.map_congr_left hcong, ZeroCheckSemantics.sum_map_mul_left, sum_rowProd, mul_one]

/-- (5) **`RowPointFixed` AT A NON-DEGENERATE CELL.**  One CONSTANT committed
column of the row's width: the committed family is `[v]` at every hash, for every
`v`.  Unlike `row_point_fixed_at_empty_columns` this cell really does commit a
column, and the guard below is live against it.  It also delimits the SCOPE:
because the committed cell is the extension of the column AT THE HASH-DEPENDENT
ROW POINT and `th` ranges over ALL hashes, `RowPointFixed` can hold only where
each column's extension is constant along the realized row points -- for a
non-constant witness column it is expected to FAIL. -/
theorem row_point_fixed_at_constant_column (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ c : Verifier.Config) (p : Verifier.Proof)
    (cellIndex : Fin 5) (v : Element) :
    RowPointFixed gdec hash khash P c₀ c p cellIndex
      (fun _ => [List.replicate (2 ^ (p.logRounds.zip p.gateRounds).length) v]) [v] := by
  intro th
  show IndexPointZeroCheck.openedCells _ _ = _
  simp only [IndexPointZeroCheck.openedCells, List.map_cons, List.map_nil]
  have hlen : (OpenedClaimFold.lift (OpenedClaimFold.cellRow
      (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
      cellIndex)).length = (p.logRounds.zip p.gateRounds).length := by
    rw [OpenedClaimFold.lift, List.length_map]
    exact cell_row_length gdec hash khash P c₀ c p cellIndex th
  rw [← hlen, extension_const]

/-- (5) **AND THE GUARD IS LIVE AT THAT CELL TOO**: a supplied cell differing from
the constant `v` already differs on the index cube. -/
theorem guard_live_at_constant_column (bits : Nat) (x v : Element) (hxv : x ≠ v) :
    IndexPointZeroCheck.CellsDifferOnCube bits [x] [v] :=
  ⟨0, pow_pos (by norm_num) bits, by simpa using hxv⟩

/-- (5) **AND THE GUARD IS LIVE THERE**: with no committed columns, a single
NON-ZERO supplied cell already differs on the index cube, so the adopted
`IndexLanesOracle.guardedIndexBadEvent` is NOT killed by its guard.  Read the
hypothesis: this says nothing about a witness whose supplied cells are all zero,
and RLUB's closed witness is exactly such a one -- section 7's closed instance
therefore still has RLUB's HONESTY (9) degeneracy (`union_index_half_is_empty`).
The witness that does supply a non-zero cell is section 8's `liveProof`. -/
theorem index_guard_is_live (bits : Nat) (x : Element) (hx : x ≠ 0) :
    IndexPointZeroCheck.CellsDifferOnCube bits [x] [] :=
  ⟨0, pow_pos (by norm_num) bits, by simpa using hx⟩

/-! ## 6. THE PAYOFF -/

/-- (6) **THE ASSEMBLY'S FAILURE SET SITS INSIDE ONE FIXED PAIR OF EVENTS.** -/
theorem assembly_failure_subset_two_stage (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (committed0 : List Element)
    (hrow : RowPointFixed gdec hash khash P c₀ c p cellIndex cols committed0) :
    RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post gate
        s0 sLast xg cells gateTruths coeffsOf cellIndex cols
      ⊆ RunLevelUnionBound.runUnionBadEvent L c p
          (outerDiagonalEvent (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p
            (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf)
          (IndexLanesOracle.guardedIndexBadEvent c.indexBits
            (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx0 cellIndex).1)
            committed0) :=
  (RunLevelUnionBound.assembly_failure_subset_run_union L gdec hash khash P c₀ pin chain c p wq
      pre post gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols).trans
    (run_union_diagonal_subset L c p _ _ _ _
      (fun th => explicit_outer_bad_event_is_the_family gdec hash khash P c₀ th0 c p
        (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf th)
      (fun th => index_bad_event_at_is_constant gdec hash khash P c₀ c p cellIndex cols
        committed0 idx0 hrow th))

/-- (6) **THE TWO-STAGE MASS BOUND FOR THE EXPLICIT ENGINE'S ASSEMBLY**, for a
fixed (non-adaptive) prover under the random oracle model. -/
theorem assembly_failure_mass_le (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (committed0 : List Element) (q constraints : Nat)
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
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints)
    (hrow : RowPointFixed gdec hash khash P c₀ c p cellIndex cols committed0) :
    oracleProbability (boundedQueries L)
        (RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + oracleProbability (boundedQueries L)
            (IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
              (roundMessages p) p.used c.degreeBits hlenI) := by
  have hsub := oracle_probability_mono (boundedQueries L) _ _
    (assembly_failure_subset_two_stage L gdec hash khash P c₀ pin chain c p wq pre post gate s0
      sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols th0 idx0 committed0 hrow)
  have h0 := RunLevelUnionBound.run_union_draw_probability_le_fibrewise L c p hL hlenI hlenP hmlen
    (outerDiagonalEvent (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p
      (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf)
    (IndexLanesOracle.guardedIndexBadEvent c.indexBits
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx0 cellIndex).1) committed0)
  have h1 := stage_a_mass_le (SoundnessAssembly.engine gdec hash th0 khash P c₀) c p q constraints
    (pre ++ gate :: post) s0 logTruths gateTruths t pr coeffsOf hlogDeg hgateDeg hclen
  have h2 := IndexLanesOracle.guarded_index_bad_event_mass_le c.indexBits
    (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx0 cellIndex).1) committed0
  have h3 := oracle_probability_mono (boundedQueries L) _ _
    (RunLevelUnionBound.run_combined_non_injective_subset_clash L c p hL hdb hbb hlenI hlenP hmlen)
  linarith



/-- (6) **THE SAME BOUND WITH THE CLASH TERM REPLACED BY ILO'S BIRTHDAY COUNT.**
No probabilistic side condition remains. -/
theorem assembly_failure_mass_le_birthday (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (committed0 : List Element) (q constraints : Nat)
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
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints)
    (hrow : RowPointFixed gdec hash khash P c₀ c p cellIndex cols committed0) :
    oracleProbability (boundedQueries L)
        (RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits q c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((22 + 5 * c.degreeBits + 8 : Nat) : ℚ)
            * (((22 + 5 * c.degreeBits + 8 : Nat) : ℚ) + 1) / 2 / (Fintype.card Block : ℚ) := by
  have h := assembly_failure_mass_le L gdec hash khash P c₀ pin chain c p wq pre post gate s0
    sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols th0 idx0 committed0 q
    constraints hL hdb hbb hlenI hlenP hmlen hlogDeg hgateDeg hclen hrow
  have hc := IndexLanesOracle.extended_digest_clash_mass_le L c (Verifier.statement p)
    (roundMessages p) p.used c.degreeBits hlenI
  linarith

/-- (6) **AT THE ENVELOPE'S `degreeBits = 13`**: ninety-five chain stages, so
`4560 / |Block|`. -/
theorem assembly_failure_mass_le_at_thirteen (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared) (coeffsOf : Nat → List Element)
    (cellIndex : Fin 5) (cols : Fin 5 → List (List Element)) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (committed0 : List Element) (constraints : Nat)
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
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints)
    (hrow : RowPointFixed gdec hash khash P c₀ c p cellIndex cols committed0) :
    oracleProbability (boundedQueries L)
        (RunLevelUnionBound.assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post
          gate s0 sLast xg cells gateTruths coeffsOf cellIndex cols)
      ≤ ChallengeUnionBound.combinedBound c.degreeBits 8 c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits + 4560 / (Fintype.card Block : ℚ) := by
  have h := assembly_failure_mass_le_birthday L gdec hash khash P c₀ pin chain c p wq pre post
    gate s0 sLast xg cells logTruths gateTruths t pr coeffsOf cellIndex cols th0 idx0 committed0
    8 constraints hL (by omega) hbb hlenI hlenP hmlen hlogDeg hgateDeg hclen hrow
  have hnum : ((22 + 5 * c.degreeBits + 8 : Nat) : ℚ)
      * (((22 + 5 * c.degreeBits + 8 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [hd]
    norm_num
  rw [hnum] at h
  exact h

/-! ## 7. A CLOSED INSTANCE AND NON-VACUITY -/

/-- (7) Along a lane execution with EMPTY truth lists, the adopted degree bounds
are exactly the proof's own message widths.  Only the `message` and `truth`
fields are read by the adopted `AdaptiveAgreementFamily.frozenLane`. -/
theorem lane_degree_bound_nil (commit : Verifier.CommitRound)
    (sel : Verifier.CoupledMessage → List Verifier.Ext3)
    (pick : Verifier.RoundChallenges → Verifier.Ext3) (n : Nat) :
    ∀ (ms : List Verifier.CoupledMessage) (s : Verifier.RoundState),
      (∀ m ∈ ms, (sel m).length ≤ n) →
      ∀ r ∈ ConditionalSoundness.lane commit sel pick [] s ms,
        r.message.length ≤ n ∧ r.truth.length ≤ n
  | [], _, _, _, hr => absurd hr (List.not_mem_nil _)
  | m :: ms, s, hm, r, hr => by
      rcases List.mem_cons.mp hr with h | h
      · subst h
        refine ⟨?_, ?_⟩
        · show ((sel m).map OuterRound.lift).length ≤ n
          rw [List.length_map]
          exact hm m (List.mem_cons_self _ _)
        · show (([] : List (List Element)).headD []).length ≤ n
          exact Nat.zero_le n
      · exact lane_degree_bound_nil commit sel pick n ms (Verifier.roundStep commit s m)
          (fun m' hm' => hm m' (List.mem_cons_of_mem _ hm')) r h

/-- (7) The closed witness's coupled messages are five log coefficients and three
gate coefficients per round. -/
theorem union_round_message_widths :
    ∀ m ∈ roundMessages RunLevelUnionBound.unionProof,
      (Prod.fst m).length ≤ 5 ∧ (Prod.snd m).length ≤ 10 := by
  intro m hm
  rw [RunLevelUnionBound.unionProof, ConcreteChainThreading.budget_round_messages] at hm
  rw [List.eq_of_mem_replicate hm]
  exact ⟨by rw [ConcreteChainThreading.budgetRound, List.length_replicate], by
    rw [ConcreteChainThreading.budgetRound, List.length_replicate]
    omega⟩

/-- (7) The adopted log-lane degree bound holds at the closed witness, with no
truth lists supplied. -/
theorem union_log_lane_degree (E : Verifier.Engine) :
    ∀ r ∈ ConditionalSoundness.logLaneOf E RunLevelUnionBound.unionConfig
      RunLevelUnionBound.unionProof [],
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5 :=
  lane_degree_bound_nil E.commitRound Prod.fst Verifier.RoundChallenges.log 5
    (roundMessages RunLevelUnionBound.unionProof) _
    (fun m hm => (union_round_message_widths m hm).1)

/-- (7) The adopted gate-lane degree bound at the closed witness's
`quotientDegree = 8`. -/
theorem union_gate_lane_degree (E : Verifier.Engine) :
    ∀ r ∈ ConditionalSoundness.gateLaneOf E RunLevelUnionBound.unionConfig
      RunLevelUnionBound.unionProof [],
      r.message.length ≤ 10 ∧ r.truth.length ≤ 10 :=
  lane_degree_bound_nil E.commitRound Prod.snd Verifier.RoundChallenges.gate 10
    (roundMessages RunLevelUnionBound.unionProof) _
    (fun m hm => (union_round_message_widths m hm).2)

/-- (7) **THE CLOSED BOUND.**  Every hypothesis of section 6 is discharged at
RLUB's closed witness: the query budget, both chain length budgets, the round
count, the two envelope parameters, the degree bounds (section 7), the
constraint-width bound at the empty coefficient family, and `RowPointFixed` at a
cell with no committed columns.  Only the deployment data
`(gdec, hash, khash, P, c₀)` and the call data stay free, exactly as in RLUB's
own closed statement.  **ITS INDEX HALF IS DEGENERATE**, exactly as RLUB's is:
zero supplied cells against no committed columns, so `union_index_half_is_empty`
of section 8 says the index event here is `∅` and `2 * tauTerm 8` is slack.
Section 8's `assembly_failure_at_the_envelope_live` is the same bound at a
witness whose index guard is live whenever `⟨x⟩ ≠ v`. -/
theorem assembly_failure_at_the_envelope (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) :
    oracleProbability (boundedQueries 381)
        (RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
          RunLevelUnionBound.unionConfig RunLevelUnionBound.unionProof wq pre post gate s0 sLast
          xg cells [] (fun _ => []) cellIndex (fun _ => []))
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) := by
  have h := assembly_failure_mass_le_at_thirteen 381 gdec hash khash P c₀ pin chain
    RunLevelUnionBound.unionConfig RunLevelUnionBound.unionProof wq pre post gate s0 sLast xg
    cells [] [] t pr (fun _ => []) cellIndex (fun _ => []) th0 idx0 [] 123
    (by norm_num) RunLevelUnionBound.union_config_degree (le_of_eq
      RunLevelUnionBound.union_config_index)
    RunLevelUnionBound.union_length_budget_extended RunLevelUnionBound.union_length_budget_chain
    RunLevelUnionBound.union_round_count
    (union_log_lane_degree (SoundnessAssembly.engine gdec hash th0 khash P c₀))
    (union_gate_lane_degree (SoundnessAssembly.engine gdec hash th0 khash P c₀))
    (fun _ _ => Nat.zero_le 123)
    (row_point_fixed_at_empty_columns gdec hash khash P c₀ RunLevelUnionBound.unionConfig
      RunLevelUnionBound.unionProof cellIndex)
  rw [RunLevelUnionBound.union_config_degree, RunLevelUnionBound.union_config_index] at h
  exact h

/-- (7) The closed right-hand side is strictly below `1`.  Inherited verbatim
from RLUB. -/
theorem two_stage_closed_bound_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
      + 4560 / (Fintype.card Block : ℚ) < 1 :=
  RunLevelUnionBound.run_union_closed_bound_lt_one

/-- (7) **THE CLOSED STATEMENT IS NOT THE VACUOUS `≤ 1`.** -/
theorem assembly_failure_at_the_envelope_is_not_vacuous (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) :
    oracleProbability (boundedQueries 381)
        (RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
          RunLevelUnionBound.unionConfig RunLevelUnionBound.unionProof wq pre post gate s0 sLast
          xg cells [] (fun _ => []) cellIndex (fun _ => []))
        ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
          + 4560 / (Fintype.card Block : ℚ)
      ∧ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
          + 4560 / (Fintype.card Block : ℚ) < 1 :=
  ⟨assembly_failure_at_the_envelope gdec hash khash P c₀ pin chain wq pre post gate s0 sLast xg
    cells t pr cellIndex th0 idx0, two_stage_closed_bound_lt_one⟩

/-- (7) **THE CLOSED BOUND IS DISCHARGEABLE: A TABLE ON WHICH THE ASSEMBLY DOES
NOT FAIL EXISTS.** -/
theorem assembly_good_table_exists_at_the_envelope (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) :
    ∃ T, T ∉ RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
      RunLevelUnionBound.unionConfig RunLevelUnionBound.unionProof wq pre post gate s0 sLast xg
      cells [] (fun _ => []) cellIndex (fun _ => []) :=
  RunLevelUnionBound.exists_good_table_of_mass_lt_one _ _
    (lt_of_le_of_lt (assembly_failure_at_the_envelope gdec hash khash P c₀ pin chain wq pre post
      gate s0 sLast xg cells t pr cellIndex th0 idx0) two_stage_closed_bound_lt_one)


/-! ## 8. THE CLOSED INSTANCE'S INDEX HALF, AND A WITNESS WHOSE GUARD IS LIVE -/

/-- (8) RLUB's closed witness supplies only ZERO cells: its `used` claims are the
adopted test claims, every entry `Verifier.zero`. -/
theorem union_supplied_cells_zero (cellIndex : Fin 5) (idx0 : Verifier.IndexPoints) (j : Nat) :
    (OpenedClaimFold.lift (OpenedClaimFold.boundCell RunLevelUnionBound.unionProof.used idx0
      cellIndex).1).getD j 0 = 0 := by
  fin_cases cellIndex <;> cases j <;> rfl

/-- (8) **SO THE INDEX HALF OF `assembly_failure_at_the_envelope` IS THE EMPTY
EVENT**, exactly RLUB's own HONESTY (9) degeneracy: zero supplied cells against
no committed columns do not differ on the cube, the adopted guard fires, and
`2 * ChallengeUnionBound.tauTerm 8` is pure slack there.  `index_guard_is_live`
concerns an `x ≠ 0` that witness never supplies; the witness below does. -/
theorem union_index_half_is_empty (cellIndex : Fin 5) (idx0 : Verifier.IndexPoints) :
    IndexLanesOracle.guardedIndexBadEvent 8
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell RunLevelUnionBound.unionProof.used idx0
          cellIndex).1) []
      = ∅ := by
  rw [IndexLanesOracle.guardedIndexBadEvent, if_neg]
  rintro ⟨j, -, hne⟩
  apply hne
  rw [union_supplied_cells_zero]
  rfl

/-- RLUB'S CLOSED WITNESS WITH A NON-ZERO USED CELL.  Only the `used` claims
change, and only in their VALUES: all five stay one cell wide, so every length
budget RLUB discharges at `L = 381` is unchanged (`W = 1`, and `69 + 24 * W ≤ 381`
admits width up to thirteen).  The statement, the public inputs, the roots and
the thirteen coupled rounds are RLUB's. -/
def liveProof (x : Verifier.Ext3) : Verifier.Proof :=
  { RunLevelUnionBound.unionProof with used := ⟨[x], [x], [x], [x], [x]⟩ }

/-- (8) The coupled messages are untouched. -/
theorem live_round_messages (x : Verifier.Ext3) :
    roundMessages (liveProof x) = roundMessages RunLevelUnionBound.unionProof := rfl

/-- (8) So the round count is RLUB's. -/
theorem live_round_count (x : Verifier.Ext3) :
    (roundMessages (liveProof x)).length = RunLevelUnionBound.unionConfig.degreeBits :=
  RunLevelUnionBound.union_round_count

/-- (8) And the chain length budget is RLUB's: it reads the statement and the
coupled messages, neither of which changed. -/
theorem live_length_budget_chain (x : Verifier.Ext3) :
    ∀ k, 61 + (prefixRoundShape RunLevelUnionBound.unionConfig (Verifier.statement (liveProof x))
      (roundMessages (liveProof x)) k).2.length ≤ 381 :=
  RunLevelUnionBound.union_length_budget_chain

/-- (8) The EXTENDED budget does read `used`, and is re-discharged here at the
same width `W = 1`. -/
theorem live_length_budget_extended (x : Verifier.Ext3) :
    ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape RunLevelUnionBound.unionConfig
      (Verifier.statement (liveProof x)) (roundMessages (liveProof x)) (liveProof x).used
      RunLevelUnionBound.unionConfig.degreeBits k).2.length ≤ 381 :=
  RunLevelUnionBound.length_budget_extended_chain 381 RunLevelUnionBound.unionConfig (liveProof x)
    8 1 RunLevelUnionBound.union_length_budget (Nat.le_refl 1) (Nat.le_refl 1) (Nat.le_refl 1)
    (Nat.le_refl 1) (Nat.le_refl 1) (by norm_num)

/-- (8) The log-lane degree bound at the live witness. -/
theorem live_log_lane_degree (x : Verifier.Ext3) (E : Verifier.Engine) :
    ∀ r ∈ ConditionalSoundness.logLaneOf E RunLevelUnionBound.unionConfig (liveProof x) [],
      r.message.length ≤ 5 ∧ r.truth.length ≤ 5 :=
  lane_degree_bound_nil E.commitRound Prod.fst Verifier.RoundChallenges.log 5
    (roundMessages (liveProof x)) _
    (fun m hm => (union_round_message_widths m hm).1)

/-- (8) The gate-lane degree bound at the live witness. -/
theorem live_gate_lane_degree (x : Verifier.Ext3) (E : Verifier.Engine) :
    ∀ r ∈ ConditionalSoundness.gateLaneOf E RunLevelUnionBound.unionConfig (liveProof x) [],
      r.message.length ≤ 10 ∧ r.truth.length ≤ 10 :=
  lane_degree_bound_nil E.commitRound Prod.snd Verifier.RoundChallenges.gate 10
    (roundMessages (liveProof x)) _
    (fun m hm => (union_round_message_widths m hm).2)

/-- (8) `RowPointFixed` at the live witness, with ONE CONSTANT COMMITTED COLUMN of
the row's width -- thirteen coupled rounds, so `2 ^ 13` entries. -/
theorem live_row_point_fixed (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : SoundnessAssembly.Profile)
    (c₀ : Verifier.Config) (x : Verifier.Ext3) (v : Element) (cellIndex : Fin 5) :
    RowPointFixed gdec hash khash P c₀ RunLevelUnionBound.unionConfig (liveProof x) cellIndex
      (fun _ => [List.replicate (2 ^ 13) v]) [v] :=
  row_point_fixed_at_constant_column gdec hash khash P c₀ RunLevelUnionBound.unionConfig
    (liveProof x) cellIndex v

/-- (8) **AND THE GUARD IS LIVE AT THE LIVE WITNESS**: the supplied cell is
`⟨x⟩` at every one of the five bound cells, so it differs on the index cube from
the committed `[v]` as soon as `⟨x⟩ ≠ v`.  The index half of the bound below is
therefore NOT the empty event. -/
theorem live_index_guard_is_live (x : Verifier.Ext3) (v : Element) (idx0 : Verifier.IndexPoints)
    (cellIndex : Fin 5) (hxv : (⟨x⟩ : Element) ≠ v) :
    IndexPointZeroCheck.CellsDifferOnCube 8
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell (liveProof x).used idx0 cellIndex).1)
      [v] := by
  refine ⟨0, pow_pos (by norm_num) 8, ?_⟩
  fin_cases cellIndex <;> exact hxv

/-- (8) **THE CLOSED BOUND AT THE LIVE WITNESS.**  Same right-hand side as
`assembly_failure_at_the_envelope`, same discharged hypotheses -- but the index
half is a guarded event whose guard is live when `⟨x⟩ ≠ v` (`live_index_guard_is_live`;
at `⟨x⟩ = v` it is dead) rather
than the empty event of `union_index_half_is_empty`. -/
theorem assembly_failure_at_the_envelope_live (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (x : Verifier.Ext3) (v : Element) :
    oracleProbability (boundedQueries 381)
        (RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
          RunLevelUnionBound.unionConfig (liveProof x) wq pre post gate s0 sLast
          xg cells [] (fun _ => []) cellIndex (fun _ => [List.replicate (2 ^ 13) v]))
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) := by
  have h := assembly_failure_mass_le_at_thirteen 381 gdec hash khash P c₀ pin chain
    RunLevelUnionBound.unionConfig (liveProof x) wq pre post gate s0 sLast xg
    cells [] [] t pr (fun _ => []) cellIndex (fun _ => [List.replicate (2 ^ 13) v]) th0 idx0 [v]
    123 (by norm_num) RunLevelUnionBound.union_config_degree
    (le_of_eq RunLevelUnionBound.union_config_index)
    (live_length_budget_extended x) (live_length_budget_chain x) (live_round_count x)
    (live_log_lane_degree x (SoundnessAssembly.engine gdec hash th0 khash P c₀))
    (live_gate_lane_degree x (SoundnessAssembly.engine gdec hash th0 khash P c₀))
    (fun _ _ => Nat.zero_le 123)
    (live_row_point_fixed gdec hash khash P c₀ x v cellIndex)
  rw [RunLevelUnionBound.union_config_degree, RunLevelUnionBound.union_config_index] at h
  exact h

/-- (8) **AND IT IS DISCHARGEABLE**: a table on which the assembly does not fail
exists at the live witness too. -/
theorem assembly_good_table_exists_at_the_envelope_live (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (wq : SoundnessAssembly.VkParams) (pre post : List Gates.GateInfo)
    (gate : Gates.GateInfo) (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (t : NormDenseRound.Tables)
    (pr : NormDenseRound.Prepared) (cellIndex : Fin 5) (th0 : Transcript.Hash)
    (idx0 : Verifier.IndexPoints) (x : Verifier.Ext3) (v : Element) :
    ∃ T, T ∉ RunLevelUnionBound.assemblyFailureEvent 381 gdec hash khash P c₀ pin chain
      RunLevelUnionBound.unionConfig (liveProof x) wq pre post gate s0 sLast xg
      cells [] (fun _ => []) cellIndex (fun _ => [List.replicate (2 ^ 13) v]) :=
  RunLevelUnionBound.exists_good_table_of_mass_lt_one _ _
    (lt_of_le_of_lt (assembly_failure_at_the_envelope_live gdec hash khash P c₀ pin chain wq pre
      post gate s0 sLast xg cells t pr cellIndex th0 idx0 x v) two_stage_closed_bound_lt_one)


end Audit.Wire3.TwoStageConditionalCount
