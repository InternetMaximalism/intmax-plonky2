import Audit.Wire3.GatePointZeroCheck
import Audit.Wire3.InstalledIndexSampler

/-!
# The index-point zero check: the R3 dichotomy: per-column identification off a bounded index-point set (modulo the agreement set, at a common width; R1b fold-level and R2 untouched)

## The gap this module closes

The adopted `Audit.Wire3.InstalledWhirTail` records, in its header, that its
residue **R1b as formulated subsumes R3**:

> `OpeningBinding.OpensCommittedTable` is `IntegratedTerminalChain.HonestOpenings`,
> whose `opened` field is PER COLUMN. ... The WHIR claim itself binds strictly
> less: only `Connections.packedFold cells (Verifier.width c) idx`, one field
> element per cell. `TailExtractsFoldLevel` below is that weaker, R3-free shape.
> ... Where per-column identification comes from in the DEPLOYED protocol is an
> OBSERVATION here, not a theorem: the index point is sampled AFTER the cells are
> committed to the outer transcript.

The adopted `Audit.Wire3.InstalledIndexSampler` turned the ORDERING half of that
observation into theorems (`sampled_indices_absorb_used_claims`,
`index_points_are_space_coordinates`, `per_column_identification_hook`) and
recorded, in as many words, what was still missing:

> The PROBABILISTIC step -- that a FORGED cell family cannot survive a freshly
> sampled index point, i.e. that agreement of the folds at a random index point
> forces agreement of the cells -- is NOT proved, here or in the adopted tree.

THAT STEP IS WHAT THIS MODULE SUPPLIES, and nothing else.  It is supplied the
same way the adopted `Audit.Wire3.GatePointZeroCheck` supplied the gate-point
residue: Schwartz--Zippel on the evaluation point, through the adopted
`ZeroCheckSemantics` count, on an explicit uniform law.

## WHAT IS PROVED

1. **THE BRIDGE** (§1).  `packedFold_eq_extension`: for `cells.length ≤ 2 ^
   idx.length`, the adopted packed fold `Packed.fold (raw cells) (raw idx)` --
   the executable Solidity `_foldFlat` / Rust `fold_ext3_claim` the expected
   claims are built from -- IS the adopted multilinear extension
   `ZeroCheckSemantics.extension cells idx`, whose weights are the entries of the
   real `ext3_eq_evals` table (`ZeroCheckSemantics.extensionOf_uses_eq_table`).
   No new evaluation function is introduced: the proof composes the adopted
   `NormTerminalBinding.bound_column_is_packed_fold` with the adopted
   `GatePointZeroCheck.cell_bindColumn_eq_extension`, at the `pack_mles` zero
   padding `padCells`, which BOTH sides ignore (`extension_padCells`,
   `fold_padCells`).  `connections_packedFold_eq_extension` is the same identity
   for `Connections.packedFold`.

2. **THE AGREEMENT SET IS A VANISHING SET** (§3).  `cellAgreementSet indexBits
   cells cells'` is the set of index points at which the two cell families have
   the same packed fold (`mem_cellAgreementSet_packedFold` says so through the
   bridge).  `cellAgreementSet_eq_vanishingSet` proves it is exactly the adopted
   `ZeroCheckSemantics.vanishingSet` of the difference family, so
   `vanishing_card_bound` / `vanishing_density_bound` apply verbatim: at most
   `indexBits * |F|^(indexBits-1)` of the `|F|^indexBits` points, density at most
   `indexBits / |F|`, `|F| = p^3`.  `cell_agreement_mass_bound` puts that on the
   adopted `ChallengeUnionBound.uniformProductProbability` and gets the adopted
   `ChallengeUnionBound.tauTerm indexBits` -- literally the tau term, because
   this and the tau zero check are the same Schwartz--Zippel statement about
   different value families.

   `cellsDifferOnCube_of_ne` needs only a COMMON width that FITS the cube
   (`≤ 2 ^ indexBits`), not the exact cube width the adopted
   `GatePointZeroCheck.columnsDifferOnCube_of_ne` needs, because both families
   are zero-padded INTO the cube rather than truncated at it.

3. **THE R3 THEOREM** (§6).  `fold_level_gives_per_column_off_bad_set`: from the
   FOLD-LEVEL relation alone -- the claimed packed fold of the SUPPLIED cells
   equals the packed fold of the COMMITTED per-column openings, which is exactly
   what `InstalledWhirTail.TailExtractsFoldLevel` delivers through
   `OpenedClaimFold.CellOpensFullTable` -- either the supplied family IS the
   committed per-column opening family (PER-COLUMN IDENTIFICATION, i.e. the
   `opened` field of `HonestOpenings`, recovered instead of assumed), or the
   run's index point landed in that pair's agreement set, whose size is bounded
   as in (2).  `per_column_identification_off_bad_set` is the off-bad-set
   corollary, `opened_field_of_cells_eq` puts the conclusion in the adopted
   field's shape, and `run_fold_level_gives_per_column_off_bad_set` (§7) states
   it at a bound cell of a run, covering BOTH index lanes at once because
   `OpenedClaimFold.boundCell` pairs cells `0, 1, 2` with `idx.log` and cells
   `3, 4` with `idx.gate` (`bound_cell_index_lane`).

   The SUPPLIED family's fit in the index cube is DERIVED, not assumed:
   `bound_cell_supplied_width_le` reads it off `Verifier.shape` and the
   envelope's own `width c ≤ 2 ^ c.indexBits`.

4. **THE UNIFORM LAW ON THE ADOPTED INDEX SPACE** (§8).  The agreement set is
   pulled back to the LOG and GATE coordinates of
   `InstalledIndexSampler.IndexSpace indexBits` -- the space that module built
   precisely because `JointChallengeSpace.Draw` stops before the index block.
   `log_index_event_mass` / `gate_index_event_mass` prove the pullback mass
   EQUALS the adopted product mass (the same cylinder split
   `JointChallengeSpace.tau_event_mass` performs), hence
   `log_index_agreement_mass_bound` / `gate_index_agreement_mass_bound` at the
   adopted `tauTerm`.  `log_index_point_off_agreement_of_draw` /
   `gate_index_point_off_agreement_of_draw` transport a good draw to the `hgood`
   the R3 theorem consumes, and `sampled_lanes_are_draw_coordinates` records that
   the adopted sampler's own lanes ARE such coordinates.

5. **DICHOTOMY HONESTY** (§4).  `agreement_set_of_equal_extensions`: for two cell
   families of the SAME width, at most the index capacity, the agreement set is
   everything EXACTLY when the two LISTS are equal.  So **the residue class of
   "different cell lists with the same packed-fold polynomial" is EMPTY** at a
   common width; the unequal-width case (identification up to trailing zeros)
   remains RES-2 and is covered by the padded variant
   `fold_level_gives_padded_identification_off_bad_set`.  This is unlike the
   gate-point case, where no such injectivity was available.
   `padding_hides_unequal_widths` shows where it would fail: `[1]` and `[1, 0]`
   are different lists with the same fold everywhere, so the COMMON-WIDTH
   hypothesis is load-bearing and is carried explicitly by every theorem of §6.

## WHAT IS **NOT** PROVED

* **R1b AT THE FOLD LEVEL IS UNTOUCHED.**  `hfold` (equivalently
  `OpenedClaimFold.CellOpensFullTable`, equivalently
  `InstalledWhirTail.TailExtractsFoldLevel`) is a HYPOTHESIS here exactly as it
  is an assumption there.  This module removes R3 FROM R1b; it does not prove
  R1b.  WHIR proximity, list decoding, query repetition and sumcheck soundness
  are all still absent from this audit.
* **R2 IS UNTOUCHED.**  `OpeningBinding.OpensCommittedTable` remains a visible
  hypothesis: binding is not extraction.
* **NO PROBABILITY OVER RUNS.**  The index point is DERIVED from the run's own
  transcript by `Verifier.derivedIndices`; it is not sampled.  Every bound here
  is the mass of an explicit event on an EXPLICIT finite uniform law
  (`ChallengeUnionBound.uniformProductProbability`, `indexProbability` over
  `InstalledIndexSampler.IndexSpace`), exactly as the adopted
  `OuterChallenge.uniformTupleProbability` is.  Nothing connects either law to
  the deployed Keccak sponge.
* **ADAPTIVITY: HALF (A) ONLY** (§9).  The transcript ORDER half is adopted and
  is collected here (`supplied_cells_fixed_before_index_squeeze`,
  `bound_cell_is_an_absorbed_claim_frame`): all five supplied cell lists are
  absorbed into the digest the index lanes are squeezed from, and no other state
  and claims vector reaches that digest without an EXHIBITED transcript
  collision.  **HALF (B) IS NOT FORMALIZED**: nothing turns "absorbed first" into
  "chosen first" against a Fiat--Shamir adversary.  There is no random oracle, no
  distribution on `thash`, and no extraction argument anywhere in this audit.
  The dichotomy of §6 is about a FIXED pair of families.
* **ONE CELL AT A TIME.**  The theorems are indexed by ONE bound cell `i : Fin 5`.
  No union over the five cells is taken; an honest multi-cell bound would be five
  times this one (and the five cells share only two index lanes, which this
  module does not exploit).
* **MERKLE / HASH.**  Nothing here is about the PCS or about hash security.  The
  only cryptographic object that appears is the EXHIBITED
  `CommitmentOrder.TranscriptCollision` disjunct of §9, which is a conclusion,
  never a hypothesis.
* **THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR.**  `tauTerm indexBits` is the mass
  of ONE event on ONE explicit law.  It is not composed with the adopted union
  bound into a soundness statement, and no soundness theorem exists in this
  audit.  The wire-v3 WHIR profile this sits next to is the ~100-bit design
  point; no "125" is claimed anywhere.

## RESIDUES OF THIS MODULE

* **RES-1 (adaptivity half (B))**: above.  The families are quantified over, not
  extracted.
* **RES-2 (common width)**: the SUPPLIED family's width is pinned by
  `Verifier.shape`; the COMMITTED family's width is whatever the extractor
  produced, so `hcolsW` is a genuine hypothesis of §6.  Without it the recovered
  identification is only up to trailing zeros
  (`padding_hides_unequal_widths`).  WITH a common width RES-2 is EMPTY:
  `agreement_set_of_equal_extensions` says the two lists are then equal on the
  nose.  WITHOUT it, the `hcolsW`-free
  `fold_level_gives_padded_identification_off_bad_set` still recovers the
  identification AT THE INDEX CAPACITY -- `padCells` of the two families are
  equal, i.e. the families agree up to trailing zeros -- from the adopted
  `HonestOpenings.capacity` alone (`≤ 2 ^ indexBits`, which is all that field
  gives).  So RES-2 costs a consumer exactly the trailing zeros and nothing
  more.
* **RES-3 (one cell)**: above.
* **RES-4 (index block label)**: inherited from the adopted
  `InstalledIndexSampler` -- the `degreeBits + 1` block label of
  `indexSchedulePosition` is DOCUMENTED against the source order, not derived for
  an abstract `Verifier.Engine`.  This module uses only the COORDINATE side
  (`index_points_are_space_coordinates`), which is derived for every hash.

## DEGENERACY NOTES

* Equal families make §6 vacuous, not false: the agreement set is then all of
  `Finset.univ` (`agreement_set_of_equal_cells`), so `hgood` cannot hold
  (`no_point_off_agreement_at_equal_cells`).
* `indexBits = 0` makes the bound TRIVIAL: `ChallengeUnionBound.tauTerm 0 = 0`
  (adopted `GatePointZeroCheck.tauTerm_zero`).  That is consistent: with an empty
  index point a family of width `2 ^ 0 = 1` is a single cell, "differ on the
  cube" is "differ at index `0`", and the fold IS that cell, so the agreement set
  really is empty.  The envelope allows `indexBits = 0` only when
  `width c ≤ 1`.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Audit.Wire3.IndexPointZeroCheck

open Audit.Wire3 GoldilocksExt3Field

/-! ## 0. Zero padding is invisible to the adopted extension -/

theorem getD_replicate_zero (k i : Nat) :
    (List.replicate k (0 : Element)).getD i 0 = 0 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.replicate, List.getD_cons_succ] using ih i

theorem getD_append_replicate_zero (xs : List Element) (k i : Nat) :
    (xs ++ List.replicate k (0 : Element)).getD i 0 = xs.getD i 0 := by
  induction xs generalizing i with
  | nil => exact getD_replicate_zero k i
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- The zero padding `prover_v2::pack_mles` applies to the constituent group:
the cell list is filled out to the index capacity `2 ^ indexBits` with zeros.
At the FOLD level this is exactly the image of the zero COLUMNS the adopted
`OpenedClaimFold.paddedTable` appends, because a zero column folds to zero
(`OpenedClaimFold.fold_zero_column`). -/
def padCells (cells : List Element) (indexBits : Nat) : List Element :=
  cells ++ List.replicate (2 ^ indexBits - cells.length) 0

theorem padCells_length (cells : List Element) (indexBits : Nat)
    (h : cells.length ≤ 2 ^ indexBits) : (padCells cells indexBits).length = 2 ^ indexBits := by
  simp only [padCells, List.length_append, List.length_replicate]
  omega

/-- Padding with zeros does not move the adopted extension: it reads the column
through `getD`, which already zero-totalizes. -/
theorem extension_padCells (cells : List Element) (indexBits : Nat) (tau : List Element) :
    ZeroCheckSemantics.extension (padCells cells indexBits) tau
      = ZeroCheckSemantics.extension cells tau := by
  simp only [ZeroCheckSemantics.extension, ZeroCheckSemantics.extensionOf, padCells]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i _
  rw [getD_append_replicate_zero]

theorem raw_padCells (cells : List Element) (indexBits : Nat) :
    DenseMleIndexed.raw (padCells cells indexBits)
      = DenseMleIndexed.raw cells
        ++ List.replicate (2 ^ indexBits - cells.length) Arithmetic.zero := by
  rw [padCells, OpenedClaimFold.raw_append, OpenedClaimFold.raw_zero_column]

/-- Padding with zeros does not move the adopted sparse fold either
(`Packed.sparse_fold_equals_zero_padded_fold`). -/
theorem fold_padCells (cells : List Element) (indexBits : Nat) (idx : List Element) :
    Packed.fold (DenseMleIndexed.raw (padCells cells indexBits)) (DenseMleIndexed.raw idx)
      = Packed.fold (DenseMleIndexed.raw cells) (DenseMleIndexed.raw idx) := by
  rw [raw_padCells]
  exact Packed.sparse_fold_equals_zero_padded_fold _ _ _

/-! ## 1. THE BRIDGE -/

/-- **THE BRIDGE.**  The adopted packed fold of a cell list at an index point IS
the adopted multilinear extension of that cell list, zero-padded to the index
capacity, at the same point. -/
theorem packedFold_eq_extension (cells idx : List Element)
    (hcap : cells.length ≤ 2 ^ idx.length) :
    Packed.fold (DenseMleIndexed.raw cells) (DenseMleIndexed.raw idx)
      = (ZeroCheckSemantics.extension cells idx).toVerifier.val := by
  have hlen : (padCells cells idx.length).length = 2 ^ idx.length :=
    padCells_length cells idx.length hcap
  have hpack := (NormTerminalBinding.bound_column_is_packed_fold
    (padCells cells idx.length) idx idx.length hlen rfl).2.2
  have hext := GatePointZeroCheck.cell_bindColumn_eq_extension_of_width idx
    (padCells cells idx.length) hlen
  rw [← fold_padCells cells idx.length idx, ← hpack, hext, extension_padCells]

/-- The same bridge for the verifier's concrete `Connections.packedFold`. -/
theorem connections_packedFold_eq_extension (cells idx : List Verifier.Ext3) (width : Nat)
    (hcap : cells.length ≤ 2 ^ idx.length) :
    Connections.packedFold cells width idx
      = (ZeroCheckSemantics.extension (OpenedClaimFold.lift cells)
          (OpenedClaimFold.lift idx)).toVerifier := by
  apply Subtype.eq
  rw [Connections.packedFold_exact, ← OpenedClaimFold.raw_lift, ← OpenedClaimFold.raw_lift]
  exact packedFold_eq_extension (OpenedClaimFold.lift cells) (OpenedClaimFold.lift idx)
    (by simpa only [OpenedClaimFold.lift, List.length_map] using hcap)

/-! ## 2. Index points as tuples -/

/-- The tuple of an index-point list at a declared width.  `ZeroCheckSemantics.tupleOf`
carries the list's own length in its type; the runs downstream carry
`idx.length = c.indexBits` as a separate equation, so this zero-totalized form
is the one that composes. -/
def tupleAt (n : Nat) (tau : List Element) : ZeroCheckSemantics.Tuple n :=
  fun i => tau.getD i.val 0

theorem tupleAt_eq_tupleOf (tau : List Element) :
    tupleAt tau.length tau = ZeroCheckSemantics.tupleOf tau := by
  funext i
  exact List.getD_eq_get tau 0 i.isLt

theorem ofFn_tupleAt_self (tau : List Element) : List.ofFn (tupleAt tau.length tau) = tau := by
  rw [tupleAt_eq_tupleOf]
  exact ZeroCheckSemantics.ofFn_tupleOf tau

theorem ofFn_tupleAt (n : Nat) (tau : List Element) (h : tau.length = n) :
    List.ofFn (tupleAt n tau) = tau := by
  subst h
  exact ofFn_tupleAt_self tau

/-! ## 3. THE CELL AGREEMENT SET AND ITS SCHWARTZ--ZIPPEL BOUND -/

/-- The two cell families have the same packed fold at this index point. -/
def CellsAgree (cells cells' point : List Element) : Prop :=
  ZeroCheckSemantics.extension cells point = ZeroCheckSemantics.extension cells' point

/-- The DIFFERENCE cell family, as a value family on the index cube. -/
def diffCells (cells cells' : List Element) : Nat → Element :=
  fun i => cells.getD i 0 - cells'.getD i 0

/-- **THE CELL AGREEMENT SET**: the index points, as `indexBits`-coordinate
tuples, at which a supplied cell family and a committed cell family have the
SAME packed fold.  By the bridge of §1 this is exactly the set of index points
at which a per-column forgery is invisible to the WHIR claim. -/
def cellAgreementSet (indexBits : Nat) (cells cells' : List Element) :
    Finset (ZeroCheckSemantics.Tuple indexBits) :=
  Finset.univ.filter (fun r => ZeroCheckSemantics.extension cells (List.ofFn r)
    = ZeroCheckSemantics.extension cells' (List.ofFn r))

theorem mem_cellAgreementSet (indexBits : Nat) (cells cells' : List Element)
    (r : ZeroCheckSemantics.Tuple indexBits) :
    r ∈ cellAgreementSet indexBits cells cells' ↔ CellsAgree cells cells' (List.ofFn r) := by
  simp only [cellAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and, CellsAgree]

theorem mem_cellAgreementSet_tupleAt (indexBits : Nat) (cells cells' point : List Element)
    (h : point.length = indexBits) :
    tupleAt indexBits point ∈ cellAgreementSet indexBits cells cells'
      ↔ CellsAgree cells cells' point := by
  rw [mem_cellAgreementSet, ofFn_tupleAt indexBits point h]

/-- The agreement set, read through the bridge: it is the set of index points at
which the two cell families' ADOPTED PACKED FOLDS coincide.  This is the form
the WHIR claim actually constrains. -/
theorem mem_cellAgreementSet_packedFold (indexBits : Nat) (cells cells' point : List Element)
    (h : point.length = indexBits) (hcap : cells.length ≤ 2 ^ indexBits)
    (hcap' : cells'.length ≤ 2 ^ indexBits) :
    tupleAt indexBits point ∈ cellAgreementSet indexBits cells cells'
      ↔ Packed.fold (DenseMleIndexed.raw cells) (DenseMleIndexed.raw point)
        = Packed.fold (DenseMleIndexed.raw cells') (DenseMleIndexed.raw point) := by
  rw [mem_cellAgreementSet_tupleAt indexBits cells cells' point h]
  rw [packedFold_eq_extension cells point (by rw [h]; exact hcap),
    packedFold_eq_extension cells' point (by rw [h]; exact hcap')]
  constructor
  · intro hag
    exact congrArg (fun x : Element => x.toVerifier.val) hag
  · intro hag
    exact GoldilocksExt3Field.element_eq _ _ (Subtype.eq hag)

/-- **THE AGREEMENT SET IS THE VANISHING SET OF THE DIFFERENCE FAMILY**, so the
adopted `ZeroCheckSemantics` counting machinery applies verbatim. -/
theorem cellAgreementSet_eq_vanishingSet (indexBits : Nat) (cells cells' : List Element) :
    cellAgreementSet indexBits cells cells'
      = ZeroCheckSemantics.vanishingSet indexBits (diffCells cells cells') := by
  apply Finset.ext
  intro r
  rw [mem_cellAgreementSet, ZeroCheckSemantics.mem_vanishingSet]
  have hsub : ZeroCheckSemantics.extensionOf (diffCells cells cells') (List.ofFn r)
      = ZeroCheckSemantics.extension cells (List.ofFn r)
        - ZeroCheckSemantics.extension cells' (List.ofFn r) :=
    GatePointZeroCheck.extensionOf_sub (fun i => cells.getD i 0) (fun i => cells'.getD i 0)
      (List.ofFn r)
  rw [hsub, sub_eq_zero]
  exact Iff.rfl

/-- The shape of "the cell families differ" the count needs: they differ at some
index of the index cube. -/
def CellsDifferOnCube (indexBits : Nat) (cells cells' : List Element) : Prop :=
  ∃ j, j < 2 ^ indexBits ∧ cells.getD j 0 ≠ cells'.getD j 0

/-- **List inequality at a COMMON width that FITS the cube IS
`CellsDifferOnCube`.**

This is strictly weaker than the hypothesis the adopted
`GatePointZeroCheck.columnsDifferOnCube_of_ne` needs.  There both columns had to
have length EXACTLY `2 ^ n`, because a column longer than the cube can differ
only above it.  Here both families are SHORTER than (or equal to) the cube and
are zero-padded INTO it, so a common length `≤ 2 ^ indexBits` suffices: the
differing position is already a cube index.

The COMMON length is still needed.  `padding_hides_unequal_widths` below shows
what goes wrong without it. -/
theorem cellsDifferOnCube_of_ne (indexBits : Nat) (cells cells' : List Element)
    (hlen : cells.length = cells'.length) (hcap : cells.length ≤ 2 ^ indexBits)
    (hne : cells ≠ cells') : CellsDifferOnCube indexBits cells cells' := by
  obtain ⟨j, hj, hne'⟩ := GatePointZeroCheck.exists_differing_index cells cells' hlen hne
  exact ⟨j, lt_of_lt_of_le hj hcap, hne'⟩

theorem diffCells_ne_zero (indexBits : Nat) (cells cells' : List Element)
    (h : CellsDifferOnCube indexBits cells cells') :
    ∃ j, j < 2 ^ indexBits ∧ diffCells cells cells' j ≠ 0 := by
  obtain ⟨j, hj, hne⟩ := h
  exact ⟨j, hj, sub_ne_zero.mpr hne⟩

/-- **THE COUNT.**  Two cell families that differ somewhere on the index cube
agree at at most `indexBits * |F|^(indexBits-1)` of the `|F|^indexBits` index
points, written without `Nat` subtraction.  `|F| = p^3` is never evaluated. -/
theorem cellAgreement_card_bound (indexBits : Nat) (cells cells' : List Element)
    (h : CellsDifferOnCube indexBits cells cells') :
    (cellAgreementSet indexBits cells cells').card * Fintype.card Element
      ≤ indexBits * Fintype.card Element ^ indexBits := by
  rw [cellAgreementSet_eq_vanishingSet]
  exact ZeroCheckSemantics.vanishing_card_bound indexBits (diffCells cells cells')
    (diffCells_ne_zero indexBits cells cells' h)

/-- **THE DENSITY.**  The same count as a density: at most `indexBits / |F|`. -/
theorem cellAgreement_density_bound (indexBits : Nat) (cells cells' : List Element)
    (h : CellsDifferOnCube indexBits cells cells') :
    ((cellAgreementSet indexBits cells cells').card : ℚ)
        / ((Fintype.card Element : ℚ) ^ indexBits)
      ≤ (indexBits : ℚ) / (Fintype.card Element : ℚ) := by
  rw [cellAgreementSet_eq_vanishingSet]
  exact ZeroCheckSemantics.vanishing_density_bound indexBits (diffCells cells cells')
    (diffCells_ne_zero indexBits cells cells' h)

theorem cellAgreementSet_eq_zeroCheckBadSet (indexBits : Nat) (cells cells' : List Element)
    (h : CellsDifferOnCube indexBits cells cells') :
    cellAgreementSet indexBits cells cells'
      = ZeroCheckSemantics.zeroCheckBadSet indexBits (diffCells cells cells') := by
  have hnot : ¬ ZeroCheckSemantics.CubeZero indexBits (diffCells cells cells') := by
    obtain ⟨j, hj, hne⟩ := diffCells_ne_zero indexBits cells cells' h
    intro hz
    exact hne (hz j hj)
  rw [ZeroCheckSemantics.zeroCheckBadSet_of_not_cube_zero indexBits _ hnot,
    cellAgreementSet_eq_vanishingSet]

/-- **THE MASS, ON THE ADOPTED PRODUCT LAW.**  On the SAME explicit uniform law
the adopted `ChallengeUnionBound` puts on an `n`-coordinate challenge column, the
mass of the index points at which a forged cell family is invisible is at most
the adopted `ChallengeUnionBound.tauTerm indexBits`.  It is LITERALLY the tau
term: this and the tau zero check are the same Schwartz--Zippel statement about
different value families.

NOT a probability over runs; see the header. -/
theorem cell_agreement_mass_bound (indexBits : Nat) (cells cells' : List Element)
    (h : CellsDifferOnCube indexBits cells cells') :
    ChallengeUnionBound.uniformProductProbability indexBits
        (cellAgreementSet indexBits cells cells')
      ≤ ChallengeUnionBound.tauTerm indexBits := by
  rw [cellAgreementSet_eq_zeroCheckBadSet indexBits cells cells' h]
  exact ChallengeUnionBound.tau_product_mass_bound indexBits (diffCells cells cells')

/-! ## 4. DICHOTOMY HONESTY: when is the agreement set EVERYTHING? -/

/-- Two families agreeing on the whole index cube have the same extension at
every point (adopted `GatePointZeroCheck.extensionOf_congr`). -/
theorem extension_congr_on_cube (cells cells' tau : List Element)
    (h : ∀ i, i < 2 ^ tau.length → cells.getD i 0 = cells'.getD i 0) :
    ZeroCheckSemantics.extension cells tau = ZeroCheckSemantics.extension cells' tau :=
  GatePointZeroCheck.extensionOf_congr _ _ tau h

/-- **THE AGREEMENT SET IS EVERYTHING EXACTLY WHEN THE PADDED FAMILIES AGREE ON
THE CUBE.**  Forward: evaluate at the adopted Boolean points
(`ZeroCheckSemantics.extension_at_boolean_point`); backward:
`extension_congr_on_cube`. -/
theorem cellAgreementSet_eq_univ_iff_cube_agreement (indexBits : Nat) (cells cells' : List Element) :
    cellAgreementSet indexBits cells cells' = Finset.univ
      ↔ ∀ j, j < 2 ^ indexBits → cells.getD j 0 = cells'.getD j 0 := by
  constructor
  · intro h j hj
    have hmem : tupleAt indexBits (ZeroCheckSemantics.boolPoint indexBits j)
        ∈ cellAgreementSet indexBits cells cells' := by
      rw [h]
      exact Finset.mem_univ _
    rw [mem_cellAgreementSet_tupleAt indexBits cells cells' _
      (ZeroCheckSemantics.boolPoint_length indexBits j)] at hmem
    have hc := hmem
    unfold CellsAgree at hc
    rw [ZeroCheckSemantics.extension_at_boolean_point cells indexBits j hj,
      ZeroCheckSemantics.extension_at_boolean_point cells' indexBits j hj] at hc
    exact hc
  · intro h
    apply Finset.ext
    intro r
    rw [mem_cellAgreementSet]
    refine iff_of_true ?_ (Finset.mem_univ r)
    refine extension_congr_on_cube cells cells' (List.ofFn r) ?_
    intro i hi
    exact h i (by simpa only [List.length_ofFn] using hi)

/-- **VACUITY AT EQUAL FAMILIES.**  Nothing is ever `decide`d over a tuple
`Finset`: the membership predicate reduces to `x = x`. -/
theorem agreement_set_of_equal_cells (indexBits : Nat) (cells : List Element) :
    cellAgreementSet indexBits cells cells = Finset.univ := by
  apply Finset.ext
  intro r
  simp only [mem_cellAgreementSet, Finset.mem_univ, iff_true, CellsAgree]

theorem no_point_off_agreement_at_equal_cells (indexBits : Nat) (cells : List Element)
    (t : ZeroCheckSemantics.Tuple indexBits) : t ∈ cellAgreementSet indexBits cells cells := by
  rw [agreement_set_of_equal_cells]
  exact Finset.mem_univ t

/-- Cube agreement of two families of the SAME length that FITS the cube forces
list equality: the zero padding cannot hide anything. -/
theorem cells_eq_of_cube_agreement (indexBits : Nat) (cells cells' : List Element)
    (hlen : cells.length = cells'.length) (hcap : cells.length ≤ 2 ^ indexBits)
    (h : ∀ j, j < 2 ^ indexBits → cells.getD j 0 = cells'.getD j 0) : cells = cells' := by
  apply List.ext_get hlen
  intro j hj hk
  have hd := h j (lt_of_lt_of_le hj hcap)
  rw [List.getD_eq_get cells 0 hj, List.getD_eq_get cells' 0 hk] at hd
  exact hd

/-- **THE RESIDUE CLASS OF DELIVERABLE 5 IS EMPTY AT A COMMON WIDTH.**

For two cell families of the SAME length, at most the index capacity
`2 ^ indexBits`, the agreement set is everything EXACTLY when the two lists are
equal.  So there is NO family of "different cell lists with the same packed-fold
polynomial" to hand on to residue R2: at a common width the multilinear
extension is injective on the cube values, and the cube values ARE the list.

This is UNLIKE the gate-point case of the adopted
`GatePointZeroCheck.agreement_set_of_equal_columns`, where equality of the two
columns was the only recorded degeneracy but no injectivity statement was
available, because the columns there are not required to share a width. -/
theorem agreement_set_of_equal_extensions (indexBits : Nat) (cells cells' : List Element)
    (hlen : cells.length = cells'.length) (hcap : cells.length ≤ 2 ^ indexBits) :
    cellAgreementSet indexBits cells cells' = Finset.univ ↔ cells = cells' := by
  constructor
  · intro h
    exact cells_eq_of_cube_agreement indexBits cells cells' hlen hcap
      ((cellAgreementSet_eq_univ_iff_cube_agreement indexBits cells cells').mp h)
  · intro h
    subst h
    exact agreement_set_of_equal_cells indexBits cells

/-- **WHERE THE RESIDUE CLASS WOULD BE NON-EMPTY: UNEQUAL WIDTHS.**  `[1]` and
`[1, 0]` are DIFFERENT lists with the SAME packed fold at every index point of a
one-variable index cube, because the second is the first plus one trailing zero
and the padding is exactly what `getD` supplies anyway.  So the common-width
hypothesis of `agreement_set_of_equal_extensions` is not decoration: without it
the residue class is inhabited, and what a consumer recovers off the bad set is
the family only UP TO trailing zeros.

`Verifier.shape` pins the supplied cell counts and hence the supplied width; the
COMMITTED family's width is whatever the extractor produced, which is why the
§6 theorems carry the common-width equation explicitly. -/
theorem padding_hides_unequal_widths :
    cellAgreementSet 1 [1] [1, 0] = Finset.univ ∧ ([1] : List Element) ≠ [1, 0] := by
  refine ⟨(cellAgreementSet_eq_univ_iff_cube_agreement 1 [1] [1, 0]).mpr ?_, ?_⟩
  · intro j hj
    interval_cases j
    · rfl
    · rfl
  · intro h
    exact absurd (congrArg List.length h) (by decide)

/-! ## 5. THE COMMITTED CELL FAMILY -/

/-- The committed cell family at the Element level: the per-column row openings
of the extracted columns, written with the adopted extension instead of the
adopted fold.  `raw_openedCells` proves the two are the same list. -/
def openedCells (cols : List (List Element)) (row : List Element) : List Element :=
  cols.map (fun c => ZeroCheckSemantics.extension c row)

theorem openedCells_length (cols : List (List Element)) (row : List Element) :
    (openedCells cols row).length = cols.length := List.length_map _ _

/-- The adopted `OpenedClaimFold.rowOpenings` IS the raw image of `openedCells`,
column by column, by the bridge of §1 at the ROW point.  Each committed column
is a FULL table for the row point, so the bridge's capacity hypothesis is an
equality here. -/
theorem raw_openedCells (cols : List (List Element)) (row : List Element)
    (hc : ∀ c ∈ cols, c.length = 2 ^ row.length) :
    DenseMleIndexed.raw (openedCells cols row) = OpenedClaimFold.rowOpenings cols row := by
  show (cols.map (fun c => ZeroCheckSemantics.extension c row)).map
      (fun x => x.toVerifier.val) = _
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro c hcm
  exact (packedFold_eq_extension c row (le_of_eq (hc c hcm))).symm

/-- The value a fold-level opening pins down: the packed fold of the COMMITTED
per-column openings at the index point IS the extension of the committed cell
family there. -/
theorem committed_claim_is_extension (cols : List (List Element)) (row idx : List Element)
    (hc : ∀ c ∈ cols, c.length = 2 ^ row.length) (hw : cols.length ≤ 2 ^ idx.length) :
    Packed.fold (OpenedClaimFold.rowOpenings cols row) (DenseMleIndexed.raw idx)
      = (ZeroCheckSemantics.extension (openedCells cols row) idx).toVerifier.val := by
  rw [← raw_openedCells cols row hc]
  exact packedFold_eq_extension (openedCells cols row) idx
    (by rw [openedCells_length]; exact hw)

/-! ## 6. THE R3 THEOREM -/

/-- **A CELL FORGERY OUTSIDE THE BAD SET IS VISIBLE IN THE CLAIM.**  The bridge
of §1 read contrapositively: an index point off the agreement set forces the two
claimed packed folds apart, so a single WHIR claim cannot be the fold of both
cell families.  This is the step that replaces "the cells were identified per
column" by "the index point missed an explicitly bounded set". -/
theorem column_forgery_forces_fold_mismatch_off_bad_set (indexBits : Nat)
    (cells idx : List Verifier.Ext3) (cols : List (List Element)) (row : List Element)
    (hidx : idx.length = indexBits)
    (hc : ∀ col ∈ cols, col.length = 2 ^ row.length)
    (hcapCells : cells.length ≤ 2 ^ indexBits) (hcapCols : cols.length ≤ 2 ^ indexBits)
    (hpoint : tupleAt indexBits (OpenedClaimFold.lift idx)
      ∉ cellAgreementSet indexBits (OpenedClaimFold.lift cells) (openedCells cols row)) :
    Packed.fold (cells.map Subtype.val) (DenseMleIndexed.raw (OpenedClaimFold.lift idx))
      ≠ Packed.fold (OpenedClaimFold.rowOpenings cols row)
          (DenseMleIndexed.raw (OpenedClaimFold.lift idx)) := by
  have hlift : (OpenedClaimFold.lift idx).length = indexBits := by
    simpa only [OpenedClaimFold.lift, List.length_map] using hidx
  intro hfold
  refine hpoint ?_
  rw [mem_cellAgreementSet_packedFold indexBits _ _ _ hlift
    (by simpa only [OpenedClaimFold.lift, List.length_map] using hcapCells)
    (by rw [openedCells_length]; exact hcapCols)]
  rw [OpenedClaimFold.raw_lift, raw_openedCells cols row hc]
  exact hfold

/-- **THE R3 THEOREM.  The fold-level opening relation gives PER-COLUMN
identification off an explicitly bounded set of index points.**

HYPOTHESES, exactly.
* `hidx`: the index point has the configuration's `indexBits` coordinates.  For
  an accepted run this is conjuncts 8-9 of `Verifier.verify_success_checks`
  (`Verifier.lean` 459, the two conjuncts at lines 465-466) and, with
  `sampleIndices` installed, the adopted
  `InstalledIndexSampler.index_lanes_have_index_bits_length`.
* `hc`: every extracted column of this cell's group is a full table for the row
  point — adopted field `full` of `IntegratedTerminalChain.HonestOpenings`.
* `hcellsW` / `hcolsW`: the supplied cell list and the extracted column family
  have the SAME width.  The supplied side is pinned by `Verifier.shape`; the
  committed side is whatever the extractor produced, so this is a genuine
  hypothesis — and it is needed, by `padding_hides_unequal_widths`.
* `hcap`: `width ≤ 2 ^ indexBits` — the envelope's own capacity clause
  (`Verifier.envelope`, `Verifier.lean` 104), which is also adopted field
  `capacity` of `HonestOpenings`.
* `hfold`: THE FOLD-LEVEL RELATION.  The claimed packed fold of the SUPPLIED
  cells at the index point equals the packed fold of the COMMITTED per-column
  openings there.  This is exactly what `InstalledWhirTail.TailExtractsFoldLevel`
  delivers through `OpenedClaimFold.CellOpensFullTable`
  (`fold_level_claim_of_cell_opens` below turns one into the other), and it is
  strictly weaker than the `opened` field of `HonestOpenings`.

CONCLUSION.  Either the supplied cell family IS the committed per-column opening
family — per-column identification, the `opened` field of `HonestOpenings`,
recovered rather than assumed — or the run's own index point landed in the
agreement set of the two families, a set with at most
`indexBits * |F|^(indexBits-1)` of the `|F|^indexBits` points
(`cellAgreement_density_bound`: density at most `indexBits / |F|`,
`|F| = p^3`).

WHICH RESIDUE THIS REMOVES: **R3 (per-column identification), modulo that bad
set**, for one bound cell.  WHICH REMAIN: **R1b at the fold level** (`hfold` is
an assumption here, exactly as `TailExtractsFoldLevel` is an assumption there),
**R2** (`OpensCommittedTable` is still a visible hypothesis: binding is not
extraction), the unformalized half (B) of adaptivity, WHIR/Merkle proximity and
hash security.  The bound is the mass of ONE event on ONE explicit law; it is
NOT the deployed system's soundness error. -/
theorem fold_level_gives_per_column_off_bad_set (indexBits width : Nat)
    (cells idx : List Verifier.Ext3) (cols : List (List Element)) (row : List Element)
    (hidx : idx.length = indexBits)
    (hc : ∀ col ∈ cols, col.length = 2 ^ row.length)
    (hcellsW : cells.length = width) (hcolsW : cols.length = width)
    (hcap : width ≤ 2 ^ indexBits)
    (hfold : Packed.fold (cells.map Subtype.val) (DenseMleIndexed.raw (OpenedClaimFold.lift idx))
      = Packed.fold (OpenedClaimFold.rowOpenings cols row)
          (DenseMleIndexed.raw (OpenedClaimFold.lift idx))) :
    OpenedClaimFold.lift cells = openedCells cols row
      ∨ (CellsDifferOnCube indexBits (OpenedClaimFold.lift cells) (openedCells cols row)
          ∧ tupleAt indexBits (OpenedClaimFold.lift idx)
              ∈ cellAgreementSet indexBits (OpenedClaimFold.lift cells) (openedCells cols row)
          ∧ (cellAgreementSet indexBits (OpenedClaimFold.lift cells)
                (openedCells cols row)).card * Fintype.card Element
              ≤ indexBits * Fintype.card Element ^ indexBits) := by
  have hlenCells : (OpenedClaimFold.lift cells).length = width := by
    simpa only [OpenedClaimFold.lift, List.length_map] using hcellsW
  have hlenCols : (openedCells cols row).length = width := by
    rw [openedCells_length]; exact hcolsW
  have hlift : (OpenedClaimFold.lift idx).length = indexBits := by
    simpa only [OpenedClaimFold.lift, List.length_map] using hidx
  by_cases heq : OpenedClaimFold.lift cells = openedCells cols row
  · exact Or.inl heq
  · have hdiff : CellsDifferOnCube indexBits (OpenedClaimFold.lift cells) (openedCells cols row) :=
      cellsDifferOnCube_of_ne indexBits _ _ (by rw [hlenCells, hlenCols])
        (by rw [hlenCells]; exact hcap) heq
    refine Or.inr ⟨hdiff, ?_, cellAgreement_card_bound indexBits _ _ hdiff⟩
    rw [mem_cellAgreementSet_packedFold indexBits _ _ _ hlift
      (by rw [hlenCells]; exact hcap) (by rw [hlenCols]; exact hcap)]
    rw [OpenedClaimFold.raw_lift, raw_openedCells cols row hc]
    exact hfold

/-- The recovered per-column identification, in the ADOPTED shape: field
`opened` of `IntegratedTerminalChain.HonestOpenings`. -/
theorem opened_field_of_cells_eq (cells : List Verifier.Ext3) (cols : List (List Element))
    (row : List Element) (hc : ∀ col ∈ cols, col.length = 2 ^ row.length)
    (h : OpenedClaimFold.lift cells = openedCells cols row) :
    cells.map Subtype.val = OpenedClaimFold.rowOpenings cols row := by
  have := congrArg DenseMleIndexed.raw h
  rwa [OpenedClaimFold.raw_lift, raw_openedCells cols row hc] at this

/-- The clean off-bad-set corollary: outside the agreement set the fold-level
relation IS the per-column relation. -/
theorem per_column_identification_off_bad_set (indexBits width : Nat)
    (cells idx : List Verifier.Ext3) (cols : List (List Element)) (row : List Element)
    (hidx : idx.length = indexBits)
    (hc : ∀ col ∈ cols, col.length = 2 ^ row.length)
    (hcellsW : cells.length = width) (hcolsW : cols.length = width)
    (hcap : width ≤ 2 ^ indexBits)
    (hfold : Packed.fold (cells.map Subtype.val) (DenseMleIndexed.raw (OpenedClaimFold.lift idx))
      = Packed.fold (OpenedClaimFold.rowOpenings cols row)
          (DenseMleIndexed.raw (OpenedClaimFold.lift idx)))
    (hgood : tupleAt indexBits (OpenedClaimFold.lift idx)
      ∉ cellAgreementSet indexBits (OpenedClaimFold.lift cells) (openedCells cols row)) :
    cells.map Subtype.val = OpenedClaimFold.rowOpenings cols row := by
  rcases fold_level_gives_per_column_off_bad_set indexBits width cells idx cols row hidx hc
    hcellsW hcolsW hcap hfold with h | ⟨_, hmem, _⟩
  · exact opened_field_of_cells_eq cells cols row hc h
  · exact absurd hmem hgood

/-- **THE R3 DICHOTOMY WITHOUT `hcolsW`: IDENTIFICATION UP TO TRAILING ZEROS.**

`fold_level_gives_per_column_off_bad_set` needs the two families to share a
width (`hcellsW` / `hcolsW`).  The supplied side is pinned by `Verifier.shape`,
but the COMMITTED side is whatever the extractor produced, and the adopted
`IntegratedTerminalChain.HonestOpenings` gives only `capacity`:
`(cols i).length ≤ 2 ^ (boundCell p.used idx i).2.length`.  That is a `≤`, never
an `=` — which is exactly residue RES-2.

THIS VARIANT DISCHARGES RES-2 FOR CONSUMERS UP TO TRAILING ZEROS.  It assumes
only the two CAPACITY bounds -- `cells.length ≤ 2 ^ indexBits` and
`cols.length ≤ 2 ^ indexBits`, i.e. `HonestOpenings.capacity` directly -- and
concludes the same dichotomy with the identification stated at the INDEX
CAPACITY: `padCells` of the supplied family equals `padCells` of the committed
family, both lists of length exactly `2 ^ indexBits`.

HOW MUCH WEAKER IS THAT?  Exactly trailing zeros, and nothing else:
`padCells a indexBits = padCells b indexBits` says `a` and `b` agree at every
index of the cube (`getD_append_replicate_zero`), so they are the same family
padded to the same capacity.  Two consequences, stated precisely.
* WITH a common width the two conclusions COINCIDE and RES-2 is EMPTY: at a
  common width `≤ 2 ^ indexBits`, `cells_eq_of_cube_agreement` upgrades cube
  agreement to list equality, which is what
  `fold_level_gives_per_column_off_bad_set` returns.
* WITHOUT a common width they do NOT coincide, and the gap is inhabited:
  `padding_hides_unequal_widths` exhibits `[1]` and `[1, 0]`, different lists
  with equal `padCells` at `indexBits = 1`.  So this conclusion is the STRONGEST
  one available from `capacity` alone.

The bad-set disjunct is unchanged: the same agreement set, the same
`indexBits * |F|^(indexBits-1)` count.  R1b at the fold level (`hfold`) and R2
are untouched here as everywhere in §6. -/
theorem fold_level_gives_padded_identification_off_bad_set (indexBits : Nat)
    (cells idx : List Verifier.Ext3) (cols : List (List Element)) (row : List Element)
    (hidx : idx.length = indexBits)
    (hc : ∀ col ∈ cols, col.length = 2 ^ row.length)
    (hcellsCap : cells.length ≤ 2 ^ indexBits) (hcolsCap : cols.length ≤ 2 ^ indexBits)
    (hfold : Packed.fold (cells.map Subtype.val) (DenseMleIndexed.raw (OpenedClaimFold.lift idx))
      = Packed.fold (OpenedClaimFold.rowOpenings cols row)
          (DenseMleIndexed.raw (OpenedClaimFold.lift idx))) :
    padCells (OpenedClaimFold.lift cells) indexBits
        = padCells (openedCells cols row) indexBits
      ∨ (CellsDifferOnCube indexBits (OpenedClaimFold.lift cells) (openedCells cols row)
          ∧ tupleAt indexBits (OpenedClaimFold.lift idx)
              ∈ cellAgreementSet indexBits (OpenedClaimFold.lift cells) (openedCells cols row)
          ∧ (cellAgreementSet indexBits (OpenedClaimFold.lift cells)
                (openedCells cols row)).card * Fintype.card Element
              ≤ indexBits * Fintype.card Element ^ indexBits) := by
  have hlenCells : (OpenedClaimFold.lift cells).length ≤ 2 ^ indexBits := by
    simpa only [OpenedClaimFold.lift, List.length_map] using hcellsCap
  have hlenCols : (openedCells cols row).length ≤ 2 ^ indexBits := by
    rw [openedCells_length]; exact hcolsCap
  have hpadCells : (padCells (OpenedClaimFold.lift cells) indexBits).length = 2 ^ indexBits :=
    padCells_length _ _ hlenCells
  have hpadCols : (padCells (openedCells cols row) indexBits).length = 2 ^ indexBits :=
    padCells_length _ _ hlenCols
  have hlift : (OpenedClaimFold.lift idx).length = indexBits := by
    simpa only [OpenedClaimFold.lift, List.length_map] using hidx
  by_cases heq : padCells (OpenedClaimFold.lift cells) indexBits
      = padCells (openedCells cols row) indexBits
  · exact Or.inl heq
  · have hdiffPad : CellsDifferOnCube indexBits (padCells (OpenedClaimFold.lift cells) indexBits)
        (padCells (openedCells cols row) indexBits) :=
      cellsDifferOnCube_of_ne indexBits _ _ (by rw [hpadCells, hpadCols])
        (le_of_eq hpadCells) heq
    have hdiff : CellsDifferOnCube indexBits (OpenedClaimFold.lift cells)
        (openedCells cols row) := by
      obtain ⟨j, hj, hne⟩ := hdiffPad
      refine ⟨j, hj, ?_⟩
      simpa only [padCells, getD_append_replicate_zero] using hne
    refine Or.inr ⟨hdiff, ?_, cellAgreement_card_bound indexBits _ _ hdiff⟩
    rw [mem_cellAgreementSet_packedFold indexBits _ _ _ hlift hlenCells hlenCols]
    rw [OpenedClaimFold.raw_lift, raw_openedCells cols row hc]
    exact hfold

/-! ## 7. BOTH LANES, AT THE FIVE BOUND CELLS OF A RUN -/

/-- DEFINITIONAL, recorded so the lane assignment is visible: cells `0, 1, 2` are
folded at the LOG index lane and cells `3, 4` at the GATE index lane, by
`OpenedClaimFold.boundCell`'s own definition (Solidity
`_foldV2UsedCellsUnchecked`, Rust `POINT_LOG_V2` / `POINT_GATE_V2`).  Every
statement of §7 therefore covers both lanes at once. -/
theorem bound_cell_index_lane (u : Verifier.UsedClaims) (idx : Verifier.IndexPoints) :
    (OpenedClaimFold.boundCell u idx 0).2 = idx.log ∧
    (OpenedClaimFold.boundCell u idx 1).2 = idx.log ∧
    (OpenedClaimFold.boundCell u idx 2).2 = idx.log ∧
    (OpenedClaimFold.boundCell u idx 3).2 = idx.gate ∧
    (OpenedClaimFold.boundCell u idx 4).2 = idx.gate :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Both lanes have `indexBits` coordinates, so every bound cell's index point
does.  For an accepted run the two lane lengths are conjuncts 8-9 of
`Verifier.verify_success_checks` (`Verifier.lean` 459, the two conjuncts at
lines 465-466); with `sampleIndices` installed they are the adopted
`InstalledIndexSampler.index_lanes_have_index_bits_length`. -/
theorem bound_cell_index_length (u : Verifier.UsedClaims) (idx : Verifier.IndexPoints)
    (bits : Nat) (hlog : idx.log.length = bits) (hgate : idx.gate.length = bits) (i : Fin 5) :
    (OpenedClaimFold.boundCell u idx i).2.length = bits := by
  fin_cases i <;> assumption

/-- **THE SUPPLIED CELL FAMILY FITS THE INDEX CUBE, FROM `shape` AND `envelope`,
NOT ASSUMED.**  Each of the five supplied lists has one of the three shape
lengths, all of which are at most `Verifier.width c`, and the envelope's own
capacity clause is `width c ≤ 2 ^ c.indexBits`. -/
theorem bound_cell_supplied_width_le (pin : Verifier.Pinned) (c : Verifier.Config)
    (p : Verifier.Proof) (idx : Verifier.IndexPoints) (i : Fin 5)
    (hsh : Verifier.shape pin c p = true) (henv : Verifier.envelope c = true) :
    (OpenedClaimFold.boundCell p.used idx i).1.length ≤ 2 ^ c.indexBits := by
  simp only [Verifier.shape, decide_eq_true_eq] at hsh
  -- The capacity clause is extracted by NAME-FREE search, not by counting
  -- conjuncts: `Verifier.envelope` is a 21-fold `And` and a positional
  -- projection into it would silently break if a clause were inserted.
  have hw : Verifier.width c ≤ 2 ^ c.indexBits := by
    simp only [Verifier.envelope, decide_eq_true_eq] at henv
    tauto
  have hwd : Verifier.width c
      = max (c.numConstants + c.numRouted) (max c.numWires (2 * c.numRouted)) := rfl
  have hb : ∀ n : Nat, n ≤ Verifier.width c → n ≤ 2 ^ c.indexBits := fun n h => le_trans h hw
  fin_cases i
  · show p.used.logPreprocessed.length ≤ _
    rw [hsh.2.2.2.2.2.2.2.1]
    exact hb _ (by rw [hwd]; omega)
  · show p.used.logWitness.length ≤ _
    rw [hsh.2.2.2.2.2.2.2.2.1]
    exact hb _ (by rw [hwd]; omega)
  · show p.used.logNormInverse.length ≤ _
    rw [hsh.2.2.2.2.2.2.2.2.2.1]
    exact hb _ (by rw [hwd]; omega)
  · show p.used.gatePreprocessed.length ≤ _
    rw [hsh.2.2.2.2.2.2.2.2.2.2.1]
    exact hb _ (by rw [hwd]; omega)
  · show p.used.gateWitness.length ≤ _
    rw [hsh.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hb _ (by rw [hwd]; omega)

/-- **THE ADOPTED FOLD-LEVEL PREDICATE GIVES THE FOLD-LEVEL EQUATION.**
`OpenedClaimFold.CellOpensFullTable` — the conclusion of
`InstalledWhirTail.TailExtractsFoldLevel`, i.e. residue R1b at the level the
WHIR claim actually binds — says the expected claim of cell `i` is the dense
evaluation of the padded committed table at `row ++ index`.  The adopted
`OpenedClaimFold.full_table_evaluation_is_fold_of_row_openings` turns that
evaluation into the packed fold of the committed per-column openings, and the
adopted `OpenedClaimFold.expected_claim_cell_exact` says the expected claim is
the packed fold of the SUPPLIED cells.  Equating the two is `hfold` of §6. -/
theorem fold_level_claim_of_cell_opens (c : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (i : Fin 5)
    (cols : List (List Element))
    (hc : ∀ col ∈ cols, col.length = 2 ^ (OpenedClaimFold.cellRow s i).length)
    (hw : cols.length ≤ 2 ^ (OpenedClaimFold.boundCell p.used idx i).2.length)
    (hopen : OpenedClaimFold.CellOpensFullTable
      (Verifier.whirContext Connections.packedFold c p s idx) i.val (OpenedClaimFold.cellPoint i)
      cols (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2)) :
    Packed.fold ((OpenedClaimFold.boundCell p.used idx i).1.map Subtype.val)
        (DenseMleIndexed.raw
          (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2))
      = Packed.fold
          (OpenedClaimFold.rowOpenings cols
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i)))
          (DenseMleIndexed.raw
            (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2)) := by
  obtain ⟨result, _, heval, hclaim⟩ := hopen
  have hrow : (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i)).length
      = (OpenedClaimFold.cellRow s i).length := List.length_map _ _
  have hindex : (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2).length
      = (OpenedClaimFold.boundCell p.used idx i).2.length := List.length_map _ _
  obtain ⟨result', heval', hval'⟩ :=
    OpenedClaimFold.full_table_evaluation_is_fold_of_row_openings cols
      (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2)
      (by rw [hrow]; exact hc) (by rw [hindex]; exact hw)
  have hres : result = result' := Option.some.inj (heval.symm.trans heval')
  subst hres
  have hexp := OpenedClaimFold.expected_claim_cell_exact Connections.packedFold c p idx i
  have hclaim' : (Verifier.expectedClaims Connections.packedFold c p idx)[i.val]?
      = some (some result.toVerifier) := hclaim
  rw [hexp, Option.some.injEq, Option.some.injEq] at hclaim'
  have hsupplied : result.toVerifier.val
      = Packed.fold ((OpenedClaimFold.boundCell p.used idx i).1.map Subtype.val)
        ((OpenedClaimFold.boundCell p.used idx i).2.map Subtype.val) := by
    rw [← hclaim']
    exact Connections.packedFold_exact _ _ _
  rw [OpenedClaimFold.raw_lift, ← hsupplied, hval', OpenedClaimFold.raw_lift]

/-- **THE R3 THEOREM AT A BOUND CELL OF A RUN, BOTH LANES.**  The same
dichotomy as `fold_level_gives_per_column_off_bad_set`, with the fold-level
hypothesis supplied by the adopted `CellOpensFullTable` and the index point
taken from the cell's own lane (`OpenedClaimFold.boundCell`: log for cells
`0, 1, 2`, gate for `3, 4`). -/
theorem run_fold_level_gives_per_column_off_bad_set (c : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (i : Fin 5)
    (cols : List (List Element)) (width : Nat)
    (hidx : (OpenedClaimFold.boundCell p.used idx i).2.length = c.indexBits)
    (hc : ∀ col ∈ cols, col.length = 2 ^ (OpenedClaimFold.cellRow s i).length)
    (hcellsW : (OpenedClaimFold.boundCell p.used idx i).1.length = width)
    (hcolsW : cols.length = width) (hcap : width ≤ 2 ^ c.indexBits)
    (hopen : OpenedClaimFold.CellOpensFullTable
      (Verifier.whirContext Connections.packedFold c p s idx) i.val (OpenedClaimFold.cellPoint i)
      cols (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2)) :
    OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).1
        = openedCells cols (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i))
      ∨ (CellsDifferOnCube c.indexBits
            (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).1)
            (openedCells cols (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i)))
          ∧ tupleAt c.indexBits
              (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).2)
              ∈ cellAgreementSet c.indexBits
                  (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).1)
                  (openedCells cols (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i)))
          ∧ (cellAgreementSet c.indexBits
                (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used idx i).1)
                (openedCells cols
                  (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i)))).card
              * Fintype.card Element
              ≤ c.indexBits * Fintype.card Element ^ c.indexBits) := by
  have hw : cols.length ≤ 2 ^ (OpenedClaimFold.boundCell p.used idx i).2.length := by
    rw [hidx, hcolsW]; exact hcap
  exact fold_level_gives_per_column_off_bad_set c.indexBits width
    (OpenedClaimFold.boundCell p.used idx i).1 (OpenedClaimFold.boundCell p.used idx i).2 cols
    (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i)) hidx
    (by simpa only [OpenedClaimFold.lift, List.length_map] using hc) hcellsW hcolsW hcap
    (fold_level_claim_of_cell_opens c p s idx i cols hc hw hopen)

/-! ## 8. THE UNIFORM LAW, ON THE ADOPTED INDEX SPACE -/

/-- The `bits` LOG index coordinates of a point of the adopted `IndexSpace`,
reduced coordinatewise by the adopted `OuterChallenge.reduceTriple`.  Cells
`0, 1, 2` are folded at this lane. -/
def logReduction (bits : Nat) (w : InstalledIndexSampler.IndexSpace bits) : ZeroCheckSemantics.Tuple bits :=
  fun i => OuterChallenge.reduceTriple (w (InstalledIndexSampler.IndexDraw.log i))

/-- The `bits` GATE index coordinates, reduced.  Cells `3, 4` are folded here. -/
def gateReduction (bits : Nat) (w : InstalledIndexSampler.IndexSpace bits) : ZeroCheckSemantics.Tuple bits :=
  fun i => OuterChallenge.reduceTriple (w (InstalledIndexSampler.IndexDraw.gate i))

def logIndexEvent (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits)) :
    Finset (InstalledIndexSampler.IndexSpace bits) :=
  Finset.univ.filter (fun w => logReduction bits w ∈ S)

def gateIndexEvent (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits)) :
    Finset (InstalledIndexSampler.IndexSpace bits) :=
  Finset.univ.filter (fun w => gateReduction bits w ∈ S)

theorem mem_logIndexEvent (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits))
    (w : InstalledIndexSampler.IndexSpace bits) : w ∈ logIndexEvent bits S ↔ logReduction bits w ∈ S := by
  simp only [logIndexEvent, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_gateIndexEvent (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits))
    (w : InstalledIndexSampler.IndexSpace bits) : w ∈ gateIndexEvent bits S ↔ gateReduction bits w ∈ S := by
  simp only [gateIndexEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The index space splits as (LOG lane) x (GATE lane): two blocks of `bits`
digest triples each, by `InstalledIndexSampler.IndexDraw`'s own two
constructors. -/
def logSplit (bits : Nat) :
    InstalledIndexSampler.IndexSpace bits ≃ ChallengeUnionBound.TripleTuple bits × ChallengeUnionBound.TripleTuple bits where
  toFun w := (fun i => w (InstalledIndexSampler.IndexDraw.log i), fun i => w (InstalledIndexSampler.IndexDraw.gate i))
  invFun q := fun k => match k with
    | InstalledIndexSampler.IndexDraw.log i => q.1 i
    | InstalledIndexSampler.IndexDraw.gate i => q.2 i
  left_inv w := by funext k; cases k <;> rfl
  right_inv q := by
    obtain ⟨a, b⟩ := q
    exact Prod.ext (by funext i; rfl) (by funext i; rfl)

/-- The same split with the GATE lane first. -/
def gateSplit (bits : Nat) :
    InstalledIndexSampler.IndexSpace bits ≃ ChallengeUnionBound.TripleTuple bits × ChallengeUnionBound.TripleTuple bits where
  toFun w := (fun i => w (InstalledIndexSampler.IndexDraw.gate i), fun i => w (InstalledIndexSampler.IndexDraw.log i))
  invFun q := fun k => match k with
    | InstalledIndexSampler.IndexDraw.log i => q.2 i
    | InstalledIndexSampler.IndexDraw.gate i => q.1 i
  left_inv w := by funext k; cases k <;> rfl
  right_inv q := by
    obtain ⟨a, b⟩ := q
    exact Prod.ext (by funext i; rfl) (by funext i; rfl)

theorem logIndexEvent_card (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits)) :
    (logIndexEvent bits S).card
      = (ChallengeUnionBound.productEvent bits S).card * (OuterChallenge.wordSize ^ 3) ^ bits := by
  classical
  have hmap : logIndexEvent bits S
      = ((ChallengeUnionBound.productEvent bits S) ×ˢ
          (Finset.univ : Finset (ChallengeUnionBound.TripleTuple bits))).map
            (logSplit bits).symm.toEmbedding := by
    ext w
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_logIndexEvent,
      ChallengeUnionBound.mem_productEvent]
    exact Iff.rfl
  rw [hmap, Finset.card_map, Finset.card_product, Finset.card_univ,
    ChallengeUnionBound.product_space_card]

theorem gateIndexEvent_card (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits)) :
    (gateIndexEvent bits S).card
      = (ChallengeUnionBound.productEvent bits S).card * (OuterChallenge.wordSize ^ 3) ^ bits := by
  classical
  have hmap : gateIndexEvent bits S
      = ((ChallengeUnionBound.productEvent bits S) ×ˢ
          (Finset.univ : Finset (ChallengeUnionBound.TripleTuple bits))).map
            (gateSplit bits).symm.toEmbedding := by
    ext w
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_gateIndexEvent,
      ChallengeUnionBound.mem_productEvent]
    exact Iff.rfl
  rw [hmap, Finset.card_map, Finset.card_product, Finset.card_univ,
    ChallengeUnionBound.product_space_card]

/-- THE EXPLICIT IDEAL LAW ON THE ADOPTED INDEX SPACE.  Same convention as the
adopted `OuterChallenge.uniformTupleProbability` and
`InstalledIndexSampler.uniformIndexMass`: count on the explicit finite space,
then divide by its size.  Nothing says the actual draw
`InstalledIndexSampler.actualIndexDraw` is distributed by it — that is the
unformalized half (B). -/
noncomputable def indexProbability (bits : Nat) (E : Finset (InstalledIndexSampler.IndexSpace bits)) : ℚ :=
  (E.card : ℚ) / (Fintype.card (InstalledIndexSampler.IndexSpace bits) : ℚ)

/-- The law is the adopted per-point mass, counted. -/
theorem indexProbability_is_counted_uniform_mass (bits : Nat) (E : Finset (InstalledIndexSampler.IndexSpace bits)) :
    indexProbability bits E = (E.card : ℚ) * InstalledIndexSampler.uniformIndexMass bits := by
  unfold indexProbability InstalledIndexSampler.uniformIndexMass
  rw [mul_one_div]

/-- **THE PROJECTION FACT, LOG LANE.**  The mass of the pullback to the adopted
`IndexSpace` EQUALS the adopted product mass on `TripleTuple bits` — the same
cylinder split the adopted `JointChallengeSpace.tau_event_mass` and
`GatePointZeroCheck.gate_point_event_mass` perform on their blocks. -/
theorem log_index_event_mass (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits)) :
    indexProbability bits (logIndexEvent bits S)
      = ChallengeUnionBound.uniformProductProbability bits S := by
  unfold indexProbability ChallengeUnionBound.uniformProductProbability
  rw [logIndexEvent_card, InstalledIndexSampler.index_space_card,
    ChallengeUnionBound.product_space_card]
  push_cast
  rw [show 2 * bits = bits + bits by omega,
    pow_add ((OuterChallenge.wordSize : ℚ) ^ 3) bits bits]
  exact JointChallengeSpace.cylinder_quotient
    ((ChallengeUnionBound.productEvent bits S).card : ℚ)
    ((OuterChallenge.wordSize : ℚ) ^ 3) bits bits
    JointChallengeSpace.word_size_cube_cast_ne_zero

/-- **THE PROJECTION FACT, GATE LANE.** -/
theorem gate_index_event_mass (bits : Nat) (S : Finset (ZeroCheckSemantics.Tuple bits)) :
    indexProbability bits (gateIndexEvent bits S)
      = ChallengeUnionBound.uniformProductProbability bits S := by
  unfold indexProbability ChallengeUnionBound.uniformProductProbability
  rw [gateIndexEvent_card, InstalledIndexSampler.index_space_card,
    ChallengeUnionBound.product_space_card]
  push_cast
  rw [show 2 * bits = bits + bits by omega,
    pow_add ((OuterChallenge.wordSize : ℚ) ^ 3) bits bits]
  exact JointChallengeSpace.cylinder_quotient
    ((ChallengeUnionBound.productEvent bits S).card : ℚ)
    ((OuterChallenge.wordSize : ℚ) ^ 3) bits bits
    JointChallengeSpace.word_size_cube_cast_ne_zero

/-- THE PULLBACKS: the cell agreement set of a forged family, on the LOG and
GATE coordinates of the adopted index space. -/
def logAgreementEvent (bits : Nat) (cells cells' : List Element) : Finset (InstalledIndexSampler.IndexSpace bits) :=
  logIndexEvent bits (cellAgreementSet bits cells cells')

def gateAgreementEvent (bits : Nat) (cells cells' : List Element) : Finset (InstalledIndexSampler.IndexSpace bits) :=
  gateIndexEvent bits (cellAgreementSet bits cells cells')

/-- **(Deliverable 4) THE INDEX-POINT AGREEMENT MASS, LOG LANE.**  Bounded by
the adopted `ChallengeUnionBound.tauTerm indexBits` — the same closed form the
adopted `JointChallengeSpace.tau_bad_event_mass_le` and
`GatePointZeroCheck.gate_point_agreement_joint_mass_bound` get for their
blocks. -/
theorem log_index_agreement_mass_bound (bits : Nat) (cells cells' : List Element)
    (h : CellsDifferOnCube bits cells cells') :
    indexProbability bits (logAgreementEvent bits cells cells')
      ≤ ChallengeUnionBound.tauTerm bits := by
  rw [logAgreementEvent, log_index_event_mass]
  exact cell_agreement_mass_bound bits cells cells' h

/-- **(Deliverable 4) THE INDEX-POINT AGREEMENT MASS, GATE LANE.** -/
theorem gate_index_agreement_mass_bound (bits : Nat) (cells cells' : List Element)
    (h : CellsDifferOnCube bits cells cells') :
    indexProbability bits (gateAgreementEvent bits cells cells')
      ≤ ChallengeUnionBound.tauTerm bits := by
  rw [gateAgreementEvent, gate_index_event_mass]
  exact cell_agreement_mass_bound bits cells cells' h

/-! ### 8a. Transport: a good index draw puts the run's index point off the set -/

theorem lift_getD_of_get (xs : List Verifier.Ext3) : ∀ (i : Nat) (v : Verifier.Ext3),
    xs.get? i = some v → (OpenedClaimFold.lift xs).getD i 0 = ⟨v⟩ := by
  induction xs with
  | nil => intro i v h; cases i <;> simp at h
  | cons x xs ih =>
      intro i v h
      cases i with
      | zero =>
          have hv : x = v := by simpa using h
          subst hv
          rfl
      | succ i =>
          have hrec := ih i v (by simpa using h)
          simpa only [OpenedClaimFold.lift, List.map_cons, List.getD_cons_succ] using hrec

/-- A point of the index space whose LOG coordinates ARE the run's index lane
entries reduces to that lane's tuple. -/
theorem tupleAt_lift_eq_logReduction (bits : Nat) (idx : List Verifier.Ext3)
    (w : InstalledIndexSampler.IndexSpace bits)
    (hget : ∀ i : Fin bits,
      idx.get? i.val = some (OuterChallenge.reduceTriple (w (InstalledIndexSampler.IndexDraw.log i))).toVerifier) :
    tupleAt bits (OpenedClaimFold.lift idx) = logReduction bits w := by
  funext i
  exact lift_getD_of_get idx i.val _ (hget i)

theorem tupleAt_lift_eq_gateReduction (bits : Nat) (idx : List Verifier.Ext3)
    (w : InstalledIndexSampler.IndexSpace bits)
    (hget : ∀ i : Fin bits,
      idx.get? i.val = some (OuterChallenge.reduceTriple (w (InstalledIndexSampler.IndexDraw.gate i))).toVerifier) :
    tupleAt bits (OpenedClaimFold.lift idx) = gateReduction bits w := by
  funext i
  exact lift_getD_of_get idx i.val _ (hget i)

/-- **THE COMPOSED TRANSPORT, LOG LANE.**  A draw outside the pullback, whose
log coordinates carry the run's own index lane, gives exactly the `hgood` that
`per_column_identification_off_bad_set` consumes. -/
theorem log_index_point_off_agreement_of_draw (bits : Nat) (cells cells' : List Element)
    (idx : List Verifier.Ext3) (w : InstalledIndexSampler.IndexSpace bits)
    (hget : ∀ i : Fin bits,
      idx.get? i.val = some (OuterChallenge.reduceTriple (w (InstalledIndexSampler.IndexDraw.log i))).toVerifier)
    (hgood : w ∉ logAgreementEvent bits cells cells') :
    tupleAt bits (OpenedClaimFold.lift idx) ∉ cellAgreementSet bits cells cells' := by
  rw [tupleAt_lift_eq_logReduction bits idx w hget]
  intro hmem
  exact hgood ((mem_logIndexEvent bits _ w).mpr hmem)

/-- **THE COMPOSED TRANSPORT, GATE LANE.** -/
theorem gate_index_point_off_agreement_of_draw (bits : Nat) (cells cells' : List Element)
    (idx : List Verifier.Ext3) (w : InstalledIndexSampler.IndexSpace bits)
    (hget : ∀ i : Fin bits,
      idx.get? i.val = some (OuterChallenge.reduceTriple (w (InstalledIndexSampler.IndexDraw.gate i))).toVerifier)
    (hgood : w ∉ gateAgreementEvent bits cells cells') :
    tupleAt bits (OpenedClaimFold.lift idx) ∉ cellAgreementSet bits cells cells' := by
  rw [tupleAt_lift_eq_gateReduction bits idx w hget]
  intro hmem
  exact hgood ((mem_gateIndexEvent bits _ w).mpr hmem)

/-- The adopted sampler's own lanes ARE such coordinates
(`InstalledIndexSampler.index_points_are_space_coordinates`), so the transport
applies to the run's actual index points with `w` the run's actual draw. -/
theorem sampled_lanes_are_draw_coordinates (thash : Transcript.Hash) (s : Transcript.State)
    (u : Verifier.UsedClaims) (bits : Nat) :
    (∀ i : Fin bits, (OuterAdapter.sampleResult thash s u bits).points.log.get? i.val
      = some (OuterChallenge.reduceTriple
          (InstalledIndexSampler.actualIndexDraw thash
            (InstalledIndexSampler.indexDigest thash s u) bits (InstalledIndexSampler.IndexDraw.log i))).toVerifier) ∧
    (∀ i : Fin bits, (OuterAdapter.sampleResult thash s u bits).points.gate.get? i.val
      = some (OuterChallenge.reduceTriple
          (InstalledIndexSampler.actualIndexDraw thash
            (InstalledIndexSampler.indexDigest thash s u) bits (InstalledIndexSampler.IndexDraw.gate i))).toVerifier) :=
  ⟨fun i => (InstalledIndexSampler.index_points_are_space_coordinates thash s u bits i.val i.isLt).1,
   fun i => (InstalledIndexSampler.index_points_are_space_coordinates thash s u bits i.val i.isLt).2⟩

/-! ## 9. THE HONEST ADAPTIVITY REMARK -/

/-- Cell `i`'s SUPPLIED family is literally one of the eight frames the
index-sampling digest absorbs: frame `i + 1` of
`InstalledIndexSampler.claimFrames`, tagged `TAG_EXT3_VEC_V2`.  Definitional; it
records WHICH frame, it proves nothing about the sampler. -/
theorem bound_cell_is_an_absorbed_claim_frame (u : Verifier.UsedClaims)
    (idx : Verifier.IndexPoints) (i : Fin 5) :
    (InstalledIndexSampler.claimFrames u).get? (i.val + 1)
      = some ⟨6, OuterAdapter.encodedVec (OpenedClaimFold.boundCell u idx i).1⟩ := by
  fin_cases i <;> rfl

/-- **THE ADAPTIVITY REMARK, HALF (A) ONLY.**

The Schwartz--Zippel reading of §3/§8 is meaningful only if the SUPPLIED cell
family is fixed BEFORE the index point is squeezed.  For the TRANSCRIPT ORDER
that is exactly what the adopted `InstalledIndexSampler` proves, and the
statement below collects the two halves at the shape this module consumes:

1. the digest the two index lanes are squeezed from is the fold of the eight
   claim frames over the post-rounds state — so ALL five supplied cell lists,
   including cell `i`'s (`bound_cell_is_an_absorbed_claim_frame`), are absorbed
   before the first index squeeze;
2. no other incoming state and used-claims vector reaches that same digest
   unless the outer hash chain collides — the adopted
   `InstalledIndexSampler.used_claims_fixed_before_index_squeeze`, whose
   `TranscriptCollision` is EXHIBITED, never assumed.

**HALF (B) IS NOT FORMALIZED, HERE OR ANYWHERE IN THIS AUDIT.**  Nothing turns
"the cells were absorbed first" into "the cells were CHOSEN first" against a
Fiat--Shamir adversary: there is no random oracle, no distribution on `thash`,
and no extraction argument.  The masses of §8 are masses of explicit events on
an EXPLICIT ideal law over `InstalledIndexSampler.IndexSpace`; the adopted
`InstalledIndexSampler.uniformIndexMass` header says in as many words that
nothing asserts the actual draw is distributed by it.  So §6's dichotomy is a
statement about a FIXED pair of families and a point of that law, not a
soundness bound against an adaptive prover. -/
theorem supplied_cells_fixed_before_index_squeeze (thash : Transcript.Hash)
    (s : Transcript.State) (u : Verifier.UsedClaims) :
    OuterAdapter.claimsCommitted thash s u
        = OuterInitial.absorbMessages thash s (InstalledIndexSampler.claimFrames u) ∧
    (∀ (t : Transcript.State) (v : Verifier.UsedClaims),
      InstalledIndexSampler.indexDigest thash t v = InstalledIndexSampler.indexDigest thash s u →
        (t.digest = s.digest ∧ v = u) ∨ CommitmentOrder.TranscriptCollision thash) :=
  ⟨InstalledIndexSampler.claims_committed_is_the_frame_fold thash s u,
   fun t v h => InstalledIndexSampler.used_claims_fixed_before_index_squeeze thash t s v u h⟩

/-! ## 10. A CONCRETE INSTANCE AT `indexBits = 1`

The adopted `OpenedClaimFold` example: two constituent columns of two rows each
(`width = 2`, one row bit, one index bit), honest openings `[6, 8]` at row point
`[5]`, index point `[7]`.  The adopted
`OpenedClaimFold.example_dishonest_openings_differ` replaces the second opened
cell by `9` and observes the claim move from `20` to `27`.  In the language of
this module that is precisely "the index point `7` is OUTSIDE the agreement set
of the two cell families"; the agreement set here is `{0}`.

Nothing is ever `decide`d about a `Finset` over a tuple space: membership is
reduced to arithmetic FIRST, and only then evaluated on small `Element`
literals.  `Fintype.card Element` never appears in a tactic. -/

namespace Example

def indexPoint : List Verifier.Ext3 := [(7 : Element).toVerifier]
def honestCells : List Verifier.Ext3 := [(6 : Element).toVerifier, (8 : Element).toVerifier]
def forgedCells : List Verifier.Ext3 := [(6 : Element).toVerifier, (9 : Element).toVerifier]

def honest : List Element := OpenedClaimFold.lift honestCells
def forged : List Element := OpenedClaimFold.lift forgedCells
def point : List Element := OpenedClaimFold.lift indexPoint

theorem honest_is_literal : honest = [6, 8] := rfl
theorem forged_is_literal : forged = [6, 9] := rfl
theorem point_is_literal : point = [7] := rfl

/-- The adopted claim values, through the bridge of §1: `6 + 7*(8-6) = 20` for
the honest family, `6 + 7*(9-6) = 27` for the forged one — the very numbers of
`OpenedClaimFold.example_expected_cell` and
`OpenedClaimFold.example_dishonest_openings_differ`. -/
theorem claim_values :
    ZeroCheckSemantics.extension honest point = 20 ∧
    ZeroCheckSemantics.extension forged point = 27 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The bridge instantiated: the verifier's executable fold of the FORGED cells
at the index point is the extension of the forged family there. -/
theorem bridge_instance :
    Connections.packedFold forgedCells 2 indexPoint
      = (ZeroCheckSemantics.extension forged point).toVerifier :=
  connections_packedFold_eq_extension forgedCells indexPoint 2 (by decide)

theorem cells_differ : forged ≠ honest := by decide

theorem cells_differ_on_cube : CellsDifferOnCube 1 forged honest :=
  cellsDifferOnCube_of_ne 1 forged honest rfl (by decide) cells_differ

/-- The run's index point `7` is OUTSIDE the agreement set: the forged family is
caught. -/
theorem seven_not_mem_agreement :
    tupleAt 1 point ∉ cellAgreementSet 1 forged honest := by
  rw [mem_cellAgreementSet_tupleAt 1 forged honest point rfl]
  show ¬ (ZeroCheckSemantics.extension forged point = ZeroCheckSemantics.extension honest point)
  decide

/-- The index point `0` IS in the agreement set: at `0` both families fold to
their first cell `6`.  The bad set is genuinely nonempty, so the `hgood`
condition of §6 is necessary, not decoration. -/
theorem zero_mem_agreement :
    (fun _ : Fin 1 => (0 : Element)) ∈ cellAgreementSet 1 forged honest := by
  rw [mem_cellAgreementSet]
  show ZeroCheckSemantics.extension forged (List.ofFn (fun _ : Fin 1 => (0 : Element)))
    = ZeroCheckSemantics.extension honest (List.ofFn (fun _ : Fin 1 => (0 : Element)))
  have hofn : List.ofFn (fun _ : Fin 1 => (0 : Element)) = [0] := by simp
  rw [hofn]
  decide

/-- The forged family really does move the claim, and the two claims differ:
the fold-level mismatch of §6, at this witness. -/
theorem forged_claim_differs :
    Packed.fold (forgedCells.map Subtype.val) (DenseMleIndexed.raw point)
      ≠ Packed.fold (honestCells.map Subtype.val) (DenseMleIndexed.raw point) := by
  decide

/-- The product mass bound at this witness: the adopted `tauTerm 1`. -/
theorem mass_bound :
    ChallengeUnionBound.uniformProductProbability 1 (cellAgreementSet 1 forged honest)
      ≤ ChallengeUnionBound.tauTerm 1 :=
  cell_agreement_mass_bound 1 forged honest cells_differ_on_cube

/-- The same on the adopted index space, LOG lane (cells `0, 1, 2`). -/
theorem log_mass_bound :
    indexProbability 1 (logAgreementEvent 1 forged honest) ≤ ChallengeUnionBound.tauTerm 1 :=
  log_index_agreement_mass_bound 1 forged honest cells_differ_on_cube

/-- The same on the GATE lane (cells `3, 4`). -/
theorem gate_mass_bound :
    indexProbability 1 (gateAgreementEvent 1 forged honest) ≤ ChallengeUnionBound.tauTerm 1 :=
  gate_index_agreement_mass_bound 1 forged honest cells_differ_on_cube

/-- Deliverable 5 at this witness: the two families have the same width, so the
agreement set is NOT everything — the residue class of "different lists, equal
packed-fold polynomial" is empty here. -/
theorem agreement_set_not_univ : cellAgreementSet 1 forged honest ≠ Finset.univ := by
  intro h
  exact cells_differ ((agreement_set_of_equal_extensions 1 forged honest rfl (by decide)).mp h)

end Example

end Audit.Wire3.IndexPointZeroCheck
