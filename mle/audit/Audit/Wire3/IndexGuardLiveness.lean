import Audit.Wire3.ZeroCheckSemantics
import Audit.Wire3.EqTableProvenance
import Audit.Wire3.GatePointZeroCheck
import Audit.Wire3.OpenedClaimFold
import Audit.Wire3.IndexPointZeroCheck
import Audit.Wire3.IndexLanesOracle
import Audit.Wire3.IndexStageFinerSplit

/-!
# `Audit.Wire3.IndexGuardLiveness` -- when the adopted index guard fires

**WHAT THIS MODULE ADDS.**  `Audit.Wire3.IndexStageFinerSplit` (ISFS) closes its
HONESTY (9) with a named open item: nothing in the tree shows that the adopted
guard `IndexPointZeroCheck.CellsDifferOnCube` is live at a NON-CONSTANT committed
column.  ISFS's `live_index_guard_is_live_at_every_outer_draw` and TSCC's
`guard_live_at_constant_column` are both proved at ONE CONSTANT column, where the
committed cell is the same field element at every row point.  This module
characterizes the guard and exhibits its liveness at a column that is genuinely
not constant.

* **Section 1 -- the characterization.**  `cells_differ_iff` prints the adopted
  guard, `guard_dead_iff_cube_agreement` and `guard_dead_iff_equal` say the guard
  is DEAD exactly when the supplied and committed cell lists coincide (at a common
  width that fits the index cube), `cells_differ_singleton_iff` specializes to the
  one-cell shape of TwoStageConditionalCount's `liveProof` (section 5; general
  consumers carry a supplied width pinned by `Verifier.shape` against
  `cols.length` committed entries with NO length tie, where the dead condition is
  the padded agreement `guard_dead_iff_cube_agreement`, not list equality), and
  `dead_guard_means_claim_true` / `dead_guard_kills_index_event` state the audit
  meaning.
* **Section 2 -- a non-constant column.**  `spikeColumn m v w` is the width-`2 ^ m`
  column that is `v` everywhere on the cube except `w` at vertex zero;
  `spike_column_not_constant` shows it equals NO constant column once `w ≠ v` and
  `0 < m`.  `extension_spikeColumn` computes its adopted multilinear extension at
  every row point of the matching length as `v + (w - v) * eqAtZero row`, where
  `eqAtZero row` is the adopted eq weight `EqTableProvenance.rowProdFrom 0 row 0`
  at vertex zero (`rowProdFrom_at_zero`).  This generalizes TSCC's
  `extension_const`, which is the `w = v` case (`spikeColumn_self`).
* **Section 3 -- liveness and death at that column.**
  `guard_live_at_nonconstant_column_iff` and `guard_dead_at_nonconstant_column_iff`
  are the exact dichotomy; `guard_dead_at_nonconstant_column_iff_ratio` and
  `guard_live_at_nonconstant_column_of_ne` write it as the single Element equation
  `eqAtZero row = (x - v) / (w - v)`.
  `guard_dead_at_a_supplied_cell_outside_the_column_values` is the honest warning:
  a supplied cell lying outside `{v, w}` does NOT by itself make the guard live,
  because `eqAtZero row` ranges over the whole field.
* **Section 4 -- the mass reading.**  The row point is a function of the run's own
  outer draw (ISFS's `rowPointOf`), so at a fixed non-constant column and a fixed
  supplied cell the outer draws at which the guard is dead form the LEVEL SET of a
  single field-valued function of the row point
  (`dead_outer_draws_eq_level_set`, `guard_dead_at_the_outer_draw_iff`).
* **Section 5 -- the concrete instance.**  At TSCC's `liveProof x`, with the
  column `spikeColumn m 0 1`, the guard is live at the all-zero row point exactly
  when the supplied cell is not `1` (`live_guard_at_the_all_zero_row_iff`,
  `live_guard_is_live_at_the_all_zero_row`), and dead at any row point carrying a
  coordinate `1` when the supplied cell is `0`
  (`live_guard_is_dead_at_a_row_with_a_one`).  At a live guard the adopted
  `IndexLanesOracle.guardedIndexBadEvent` is the union of the two lane
  agreement pullbacks -- the guard does not set it to `∅`
  (`index_event_not_killed_at_the_spike_column`); whether that union is
  inhabited is NOT shown here.

## HONESTY -- read before quoting anything below

1. **THIS MODULE CHANGES NO BOUND.**  Every mass bound in ISFS, TSCC, RLUB and
   `SoundnessAssembly` is exactly what it was.  Nothing here is a new soundness
   statement, a tighter constant, or a smaller failure mass.  What is added is an
   EXPLANATION of one hypothesis-shaped side condition that the adopted bounds
   carry, and one worked instance of it at a column that is not constant.
2. **A DEAD GUARD IS THE HONEST PROVER, NOT A GAP.**  `guard_dead_iff_equal` is
   the whole point: at a common width fitting the index cube the guard is dead
   exactly when the supplied cell list IS the committed cell list -- the prover's
   claimed opening equals the committed column's extension at the row point.
   There is then nothing for the index draw to catch, `guardedIndexBadEvent` is
   `∅`, and `2 * ChallengeUnionBound.tauTerm` is pure slack.  A dead guard never
   makes the adopted bound FALSE; it makes it uninformative at that point.  This
   module does not claim otherwise, and it does not claim the guard is live at
   every non-constant column -- `guard_dead_at_nonconstant_column_iff` says
   precisely where it is not.
3. **RANDOM ORACLE MODEL AND FIXED (NON-ADAPTIVE) PROVER, INHERITED.**  Section 4
   and section 5 name ISFS's `rowPointOf` and TSCC's `liveProof`; the law, the
   prover model and the transcript model are ISFS's and TSCC's, quoted unchanged.
   Nothing here widens the prover model, and nothing here is a statement about the
   deployed permutation.
4. **THESE STATEMENTS ARE NOT THE SYSTEM'S SOUNDNESS ERROR.**  The deployed
   profile's design point is about a hundred bits and its dominant terms are the
   WHIR and Merkle ones that `ChallengeUnionBound.combinedBound` excludes.  No
   sentence in this module says soundness is proved, and no number here should be
   quoted as a soundness error.
5. **NO SCHWARTZ--ZIPPEL OVER OUTER DRAWS IS PROVED.**  Section 4 says the dead
   set is the level set of one field-valued function of the row point, and stops
   there.  No adopted lemma in this tree bounds the number of outer draws whose
   row point solves `eqAtZero row = (x - v) / (w - v)`: the adopted root-count
   lemmas (`ZeroCheckSemantics.vanishing_card_bound` and the
   `GateAggregatePolynomial` / `ConditionalSoundness` degree bounds) count TUPLES
   of free field coordinates, and the realized row point is the reduction of an
   oracle draw, not a free tuple.  Turning the level set into a mass over oracle
   tables is a FOLLOW-UP, explicitly not done here.
6. **THE EXHIBITED ROW POINTS ARE NOT SHOWN TO BE REALIZED.**  Section 5's
   all-zero row point, and section 3's `[1 - x]`, are row points OF THE RIGHT
   LENGTH.  No theorem here constructs an outer draw `u` with
   `OpenedClaimFold.lift (IndexStageFinerSplit.rowPointOf m cellIndex u)` equal to
   either of them, and none is claimed: `rowPointOf` reduces oracle squeezes, and
   which lists it can produce is not determined anywhere in this tree.  What
   section 5 exhibits is that the guard's liveness at a non-constant column is a
   NON-VACUOUS condition on the row point -- true on one explicit row point, false
   on another -- which is precisely what ISFS's HONESTY (9) records as unknown.
7. **THE RESIDUES ARE UNTOUCHED.**  `SoundnessAssembly`'s residue R1b, and the
   fact that acceptance is never exhibited anywhere in this tree, are inherited
   exactly as ISFS states them.  Explaining the guard discharges neither.

## Tactic note

`sorry`, `admit`, `axiom`, `decide`, `native_decide` and `set_option` do not
occur.  `Fintype.card Element` and `Fintype.card Block` are never evaluated, and
no `Finset` over the index space, the challenge space or the joint space is ever
enumerated.  `Finset.univ` does not occur in this module at all: the one place a
statement would naturally reach for it -- "the agreement set is everything" --
is written instead as a membership quantifier
(`guard_dead_iff_every_index_point_agrees`).  Only `Audit.Wire3.*` modules are
imported; Mathlib is reached only through them.
-/

namespace Audit.Wire3.IndexGuardLiveness

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. THE ADOPTED GUARD, CHARACTERIZED -/

/-- (1) **THE GUARD, PRINTED.**  `IndexPointZeroCheck.CellsDifferOnCube bits
supplied committed` is literally: the two zero-padded cell families differ at some
index of the index cube.  Everything in section 1 is a repackaging of this one
existential. -/
theorem cells_differ_iff (bits : Nat) (supplied committed : List Element) :
    IndexPointZeroCheck.CellsDifferOnCube bits supplied committed
      ↔ ∃ j, j < 2 ^ bits ∧ supplied.getD j 0 ≠ committed.getD j 0 :=
  Iff.rfl

/-- (1) **THE GUARD IS DEAD EXACTLY ON CUBE AGREEMENT.**  De Morgan on
`cells_differ_iff`. -/
theorem guard_dead_iff_cube_agreement (bits : Nat) (supplied committed : List Element) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube bits supplied committed
      ↔ ∀ j, j < 2 ^ bits → supplied.getD j 0 = committed.getD j 0 := by
  constructor
  · intro h j hj
    by_contra hne
    exact h ⟨j, hj, hne⟩
  · rintro h ⟨j, hj, hne⟩
    exact hne (h j hj)

/-- (1) **THE GUARD IS DEAD EXACTLY AT THE HONEST CLAIM.**  At a COMMON width that
fits the index cube -- NOTE: general consumers (IndexStageFinerSplit's `indexBadAt`)
carry a supplied width pinned by `Verifier.shape` against `cols.length` committed
entries with no length tie, so for them the dead condition is the zero-padded
agreement `guard_dead_iff_cube_agreement`; the common-width form below is the
shape of the closed witnesses -- the guard is dead if and only if the supplied
cell list IS the committed cell list.  Read in audit terms: the guarded index event is the event
that the ADVERSARY's claimed cells disagree with the commitment AND the index draw
fails to catch the disagreement; a dead guard says the claim is TRUE, so there is
nothing to catch. -/
theorem guard_dead_iff_equal (bits : Nat) (supplied committed : List Element)
    (hlen : supplied.length = committed.length) (hcap : supplied.length ≤ 2 ^ bits) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube bits supplied committed ↔ supplied = committed := by
  constructor
  · intro h
    exact IndexPointZeroCheck.cells_eq_of_cube_agreement bits supplied committed hlen hcap
      ((guard_dead_iff_cube_agreement bits supplied committed).mp h)
  · rintro h ⟨j, _, hne⟩
    exact hne (by rw [h])

/-- (1) The positive form of `guard_dead_iff_equal`: at a common width fitting the
cube the guard is live exactly at a genuine forgery. -/
theorem guard_live_iff_ne (bits : Nat) (supplied committed : List Element)
    (hlen : supplied.length = committed.length) (hcap : supplied.length ≤ 2 ^ bits) :
    IndexPointZeroCheck.CellsDifferOnCube bits supplied committed ↔ supplied ≠ committed := by
  constructor
  · rintro ⟨j, _, hne⟩ heq
    exact hne (by rw [heq])
  · intro hne
    exact IndexPointZeroCheck.cellsDifferOnCube_of_ne bits supplied committed hlen hcap hne

/-- (1) **THE ONE-CELL SHAPE.**  The closed witnesses (`liveProof`, one used cell
against one committed column) have this shape, and there the guard collapses to a
single field inequality; general consumers do not (see the remark above).  The zero padding above index zero is the same on both sides and
cannot contribute. -/
theorem cells_differ_singleton_iff (bits : Nat) (x y : Element) :
    IndexPointZeroCheck.CellsDifferOnCube bits [x] [y] ↔ x ≠ y := by
  refine Iff.trans (guard_live_iff_ne bits [x] [y] rfl ?_) ?_
  · have h : 0 < 2 ^ bits := pow_pos (by norm_num) bits
    show 1 ≤ 2 ^ bits
    exact h
  · constructor
    · intro hne hxy
      exact hne (by rw [hxy])
    · intro hne hlist
      exact hne (List.head_eq_of_cons_eq hlist)

/-- (1) **THE AGREEMENT SET IS EVERYTHING EXACTLY WHEN THE GUARD IS DEAD**, written
without naming the ambient `Finset` so nothing is ever enumerated. -/
theorem guard_dead_iff_every_index_point_agrees (bits : Nat) (supplied committed : List Element) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube bits supplied committed
      ↔ ∀ t : ZeroCheckSemantics.Tuple bits,
        t ∈ IndexPointZeroCheck.cellAgreementSet bits supplied committed := by
  constructor
  · intro h t
    rw [IndexPointZeroCheck.mem_cellAgreementSet]
    refine IndexPointZeroCheck.extension_congr_on_cube supplied committed (List.ofFn t) ?_
    intro i hi
    refine (guard_dead_iff_cube_agreement bits supplied committed).mp h i ?_
    simpa only [List.length_ofFn] using hi
  · rintro h ⟨j, hj, hne⟩
    have hmem := h (IndexPointZeroCheck.tupleAt bits (ZeroCheckSemantics.boolPoint bits j))
    rw [IndexPointZeroCheck.mem_cellAgreementSet_tupleAt bits supplied committed _
      (ZeroCheckSemantics.boolPoint_length bits j)] at hmem
    have hc : ZeroCheckSemantics.extension supplied (ZeroCheckSemantics.boolPoint bits j)
        = ZeroCheckSemantics.extension committed (ZeroCheckSemantics.boolPoint bits j) := hmem
    rw [ZeroCheckSemantics.extension_at_boolean_point supplied bits j hj,
      ZeroCheckSemantics.extension_at_boolean_point committed bits j hj] at hc
    exact hne hc

/-- (1) **WHAT A DEAD GUARD MEANS FOR THE CLAIM.**  If the guard is dead then the
supplied and committed cell families have the SAME packed fold at EVERY index
point of the cube's width -- the claimed opening is the true one at every index the
verifier could draw.  There is no forgery for the index draw to miss. -/
theorem dead_guard_means_claim_true (bits : Nat) (supplied committed tau : List Element)
    (hlen : tau.length ≤ bits)
    (h : ¬ IndexPointZeroCheck.CellsDifferOnCube bits supplied committed) :
    ZeroCheckSemantics.extension supplied tau = ZeroCheckSemantics.extension committed tau := by
  refine IndexPointZeroCheck.extension_congr_on_cube supplied committed tau ?_
  intro i hi
  refine (guard_dead_iff_cube_agreement bits supplied committed).mp h i ?_
  exact lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hlen)

/-- (1) **AND WHAT IT MEANS FOR THE EVENT.**  A dead guard makes the adopted
`IndexLanesOracle.guardedIndexBadEvent` the EMPTY event, so the
`2 * ChallengeUnionBound.tauTerm` charged against it is pure slack there.  This is
exactly the degeneracy ISFS's HONESTY (9) names, restated so that its cause --
an honest claim -- is visible. -/
theorem dead_guard_kills_index_event (bits : Nat) (supplied committed : List Element)
    (h : ¬ IndexPointZeroCheck.CellsDifferOnCube bits supplied committed) :
    IndexLanesOracle.guardedIndexBadEvent bits supplied committed = ∅ :=
  IndexLanesOracle.guarded_index_bad_event_of_cube_agreement bits supplied committed h

/-! ## 2. A COMMITTED COLUMN THAT IS NOT CONSTANT -/

/-- (2) The width-`2 ^ m` committed column that carries `w` at cube vertex zero and
`v` at every other vertex.  At `w = v` it IS the constant column TSCC's
`extension_const` handles (`spikeColumn_self`); at `w ≠ v` and `0 < m` it is not
constant (`spike_column_not_constant`). -/
def spikeColumn (m : Nat) (v w : Element) : List Element :=
  w :: List.replicate (2 ^ m - 1) v

/-- (2) The adopted eq weight at cube vertex zero, as a product over the row point.
`rowProdFrom_at_zero` identifies it with `EqTableProvenance.rowProdFrom 0 row 0`. -/
def eqAtZero (tau : List Element) : Element :=
  (tau.map (fun t => 1 - t)).prod

theorem eqAtZero_nil : eqAtZero ([] : List Element) = 1 := rfl

theorem eqAtZero_cons (t : Element) (rest : List Element) :
    eqAtZero (t :: rest) = (1 - t) * eqAtZero rest := by
  simp only [eqAtZero, List.map_cons, List.prod_cons]

/-- (2) **THE ADOPTED EQ WEIGHT AT VERTEX ZERO IS THE PRODUCT OF `1 - t`.**  Vertex
zero has every bit clear, so `EqTableProvenance.bitFactor` takes its `1 - t`
branch at every coordinate, whatever the bit offset `j`. -/
theorem rowProdFrom_at_zero : ∀ (tau : List Element) (j : Nat),
    EqTableProvenance.rowProdFrom j tau 0 = eqAtZero tau
  | [], _ => rfl
  | t :: rest, j => by
      show EqTableProvenance.bitFactor t j 0 * EqTableProvenance.rowProdFrom (j + 1) rest 0
        = eqAtZero (t :: rest)
      rw [rowProdFrom_at_zero rest (j + 1), eqAtZero_cons]
      congr 1
      unfold EqTableProvenance.bitFactor
      have hz : 0 / 2 ^ j % 2 = 0 := by
        rw [Nat.zero_div, Nat.zero_mod]
      rw [hz, if_pos rfl]

theorem spikeColumn_length (m : Nat) (v w : Element) : (spikeColumn m v w).length = 2 ^ m := by
  have h : 0 < 2 ^ m := pow_pos (by norm_num) m
  simp only [spikeColumn, List.length_cons, List.length_replicate]
  omega

theorem spikeColumn_getD_zero (m : Nat) (v w : Element) : (spikeColumn m v w).getD 0 0 = w := rfl

theorem spikeColumn_getD_of_pos (m : Nat) (v w : Element) (j : Nat) (hj0 : 0 < j)
    (hj : j < 2 ^ m) : (spikeColumn m v w).getD j 0 = v := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  show (List.replicate (2 ^ m - 1) v).getD k 0 = v
  rw [List.getD_eq_getElem?, List.getElem?_replicate_of_lt (by omega)]
  rfl

/-- (2) At `w = v` the spike column IS the constant column, so
`extension_spikeColumn` below genuinely generalizes TSCC's `extension_const`. -/
theorem spikeColumn_self (m : Nat) (v : Element) :
    spikeColumn m v v = List.replicate (2 ^ m) v := by
  have h : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hm : 2 ^ m = (2 ^ m - 1) + 1 := by omega
  rw [spikeColumn]
  conv_rhs => rw [hm]
  rw [List.replicate_succ]

/-- (2) **AND AT `w ≠ v` IT IS NOT ANY CONSTANT COLUMN.**  Two cube vertices below
`2 ^ m` carry different values as soon as `0 < m`, so the column cannot equal
`List.replicate (2 ^ m) u` for ANY `u` -- not merely "not equal to the constant `v`
column".  This is what makes section 3 a statement about a NON-CONSTANT committed
column in the sense ISFS's HONESTY (9) asks for. -/
theorem spike_column_not_constant (m : Nat) (v w u : Element) (hm : 0 < m) (hne : w ≠ v) :
    spikeColumn m v w ≠ List.replicate (2 ^ m) u := by
  intro h
  have h2 : (2 : Nat) ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hlt : 1 < 2 ^ m := by
    have : (2 : Nat) ^ 1 = 2 := by norm_num
    omega
  have e0 : (spikeColumn m v w).getD 0 0 = (List.replicate (2 ^ m) u).getD 0 0 := by rw [h]
  have e1 : (spikeColumn m v w).getD 1 0 = (List.replicate (2 ^ m) u).getD 1 0 := by rw [h]
  rw [spikeColumn_getD_zero] at e0
  rw [spikeColumn_getD_of_pos m v w 1 (by norm_num) hlt] at e1
  rw [List.getD_eq_getElem?, List.getElem?_replicate_of_lt (by omega)] at e0
  rw [List.getD_eq_getElem?, List.getElem?_replicate_of_lt (by omega)] at e1
  simp only [Option.getD_some] at e0 e1
  exact hne (e0.trans e1.symm)

/-- (2) The adopted extension of a constant VALUE FAMILY is that constant, at every
row point.  TSCC's `extension_const` is the list-indexed form of this. -/
theorem extensionOf_const (v : Element) (tau : List Element) :
    ZeroCheckSemantics.extensionOf (fun _ => v) tau = v := by
  unfold ZeroCheckSemantics.extensionOf
  have hcong : ∀ i ∈ List.range (2 ^ tau.length),
      EqTableProvenance.rowProdFrom 0 tau i * v = v * EqTableProvenance.rowProdFrom 0 tau i :=
    fun i _ => mul_comm _ _
  rw [List.map_congr_left hcong, ZeroCheckSemantics.sum_map_mul_left,
    TwoStageConditionalCount.sum_rowProd, mul_one]

/-- (2) The adopted extension of the INDICATOR of cube vertex zero is the eq weight
at that vertex. -/
theorem extensionOf_indicator_at_zero (tau : List Element) :
    ZeroCheckSemantics.extensionOf (fun i => if i = 0 then (1 : Element) else 0) tau
      = eqAtZero tau := by
  unfold ZeroCheckSemantics.extensionOf
  have hcong : ∀ i ∈ List.range (2 ^ tau.length),
      EqTableProvenance.rowProdFrom 0 tau i * (if i = 0 then (1 : Element) else 0)
        = if i = 0 then EqTableProvenance.rowProdFrom 0 tau i else 0 := by
    intro i _
    by_cases h0 : i = 0
    · rw [if_pos h0, if_pos h0, mul_one]
    · rw [if_neg h0, if_neg h0, mul_zero]
  rw [List.map_congr_left hcong,
    ZeroCheckSemantics.sum_range_indicator (fun i => EqTableProvenance.rowProdFrom 0 tau i)
      (2 ^ tau.length) 0 (pow_pos (by norm_num) _)]
  exact rowProdFrom_at_zero tau 0

/-- (2) **THE EXTENSION OF THE NON-CONSTANT COLUMN.**  A constant plus a single
indicator: at every row point of the column's own width the committed cell is
`v + (w - v) * eqAtZero row`.  The proof is the adopted linearity
(`GatePointZeroCheck.extensionOf_affine`) over the adopted eq weights; nothing new
about the extension is assumed. -/
theorem extension_spikeColumn (m : Nat) (v w : Element) (tau : List Element)
    (hlen : tau.length = m) :
    ZeroCheckSemantics.extension (spikeColumn m v w) tau = v + (w - v) * eqAtZero tau := by
  have hstep := GatePointZeroCheck.extensionOf_affine 1 (w - v) (fun _ => v)
    (fun i => if i = 0 then (1 : Element) else 0) tau
  have hcong : ZeroCheckSemantics.extensionOf (fun i => (spikeColumn m v w).getD i 0) tau
      = ZeroCheckSemantics.extensionOf
        (fun i => (1 : Element) * (fun _ : Nat => v) i
          + (w - v) * (fun i : Nat => if i = 0 then (1 : Element) else 0) i) tau := by
    refine GatePointZeroCheck.extensionOf_congr _ _ tau ?_
    intro i hi
    rw [hlen] at hi
    by_cases h0 : i = 0
    · subst h0
      show (spikeColumn m v w).getD 0 0
        = (1 : Element) * v + (w - v) * (if (0 : Nat) = 0 then (1 : Element) else 0)
      rw [spikeColumn_getD_zero, if_pos rfl]
      ring
    · show (spikeColumn m v w).getD i 0
        = (1 : Element) * v + (w - v) * (if i = 0 then (1 : Element) else 0)
      rw [spikeColumn_getD_of_pos m v w i (Nat.pos_of_ne_zero h0) hi, if_neg h0]
      ring
  show ZeroCheckSemantics.extensionOf (fun i => (spikeColumn m v w).getD i 0) tau = _
  rw [hcong, hstep, extensionOf_const, extensionOf_indicator_at_zero, one_mul]

/-! ## 3. LIVENESS AND DEATH AT THE NON-CONSTANT COLUMN -/

/-- (3) The committed cell family of the single non-constant column, at every row
point of its own width.  This is the analogue of ISFS's
`opened_cells_at_constant_column`, now with the row point genuinely entering the
value. -/
theorem openedCells_at_spike_column (m : Nat) (v w : Element) (row : List Element)
    (hrow : row.length = m) :
    IndexPointZeroCheck.openedCells [spikeColumn m v w] row
      = [v + (w - v) * eqAtZero row] := by
  simp only [IndexPointZeroCheck.openedCells, List.map_cons, List.map_nil]
  rw [extension_spikeColumn m v w row hrow]

/-- (3) **THE DICHOTOMY, POSITIVE FORM.**  For supplied cell `x` the adopted guard
fires at row point `row` exactly when `x` is not the committed value there. -/
theorem guard_live_at_nonconstant_column_iff (bits m : Nat) (v w x : Element)
    (row : List Element) (hrow : row.length = m) :
    IndexPointZeroCheck.CellsDifferOnCube bits [x]
        (IndexPointZeroCheck.openedCells [spikeColumn m v w] row)
      ↔ x ≠ v + (w - v) * eqAtZero row := by
  rw [openedCells_at_spike_column m v w row hrow, cells_differ_singleton_iff]

/-- (3) **THE DICHOTOMY, NEGATIVE FORM.**  The guard is dead at exactly the row
points solving one Element equation -- a proper condition on the row point, not a
property of the column alone. -/
theorem guard_dead_at_nonconstant_column_iff (bits m : Nat) (v w x : Element)
    (row : List Element) (hrow : row.length = m) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube bits [x]
        (IndexPointZeroCheck.openedCells [spikeColumn m v w] row)
      ↔ x = v + (w - v) * eqAtZero row := by
  rw [guard_live_at_nonconstant_column_iff bits m v w x row hrow, not_ne_iff]

/-- (3) **THE DEAD SET AS A SINGLE RATIO CONDITION.**  Once `w ≠ v` the equation
solves for the eq weight: the guard is dead at `row` exactly when
`eqAtZero row = (x - v) / (w - v)`.  Both sides are field elements; nothing is
enumerated. -/
theorem guard_dead_at_nonconstant_column_iff_ratio (bits m : Nat) (v w x : Element)
    (row : List Element) (hrow : row.length = m) (hwv : w ≠ v) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube bits [x]
        (IndexPointZeroCheck.openedCells [spikeColumn m v w] row)
      ↔ eqAtZero row = (x - v) / (w - v) := by
  have hne : w - v ≠ 0 := sub_ne_zero.mpr hwv
  rw [guard_dead_at_nonconstant_column_iff bits m v w x row hrow]
  constructor
  · intro h
    rw [eq_div_iff hne, h]
    ring
  · intro h
    rw [h, mul_comm, div_mul_cancel₀ _ hne]
    ring

/-- (3) **LIVENESS AT A NON-CONSTANT COMMITTED COLUMN.**  This is the statement
ISFS's HONESTY (9) asks for: at the column `spikeColumn m v w` with `w ≠ v`, which
`spike_column_not_constant` shows is no constant column, the adopted guard is LIVE
at every row point whose eq weight at vertex zero avoids the single value
`(x - v) / (w - v)`. -/
theorem guard_live_at_nonconstant_column_of_ne (bits m : Nat) (v w x : Element)
    (row : List Element) (hrow : row.length = m) (hwv : w ≠ v)
    (h : eqAtZero row ≠ (x - v) / (w - v)) :
    IndexPointZeroCheck.CellsDifferOnCube bits [x]
      (IndexPointZeroCheck.openedCells [spikeColumn m v w] row) := by
  by_contra hc
  exact h ((guard_dead_at_nonconstant_column_iff_ratio bits m v w x row hrow hwv).mp hc)

/-- (3) **THE HONEST WARNING: `x ∉ {v, w}` DOES NOT IMPLY LIVENESS.**  The naive
reading -- "the supplied cell is neither of the column's two values, so it cannot
equal the committed cell" -- is FALSE.  The eq weight at vertex zero ranges over
the whole field as the row point moves, so `v + (w - v) * eqAtZero row` does too.
Here is the counterexample, at the one-round spike column with `v = 0`, `w = 1`:
for ANY supplied `x` the row point `[1 - x]` makes the committed cell exactly `x`
and kills the guard, including every `x` outside `{0, 1}`.  Liveness is a
condition on the ROW POINT, which is why the theorems above are stated that way. -/
theorem guard_dead_at_a_supplied_cell_outside_the_column_values (bits : Nat) (x : Element) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube bits [x]
      (IndexPointZeroCheck.openedCells [spikeColumn 1 0 1] [1 - x]) := by
  rw [guard_dead_at_nonconstant_column_iff bits 1 0 1 x [1 - x] rfl, eqAtZero_cons, eqAtZero_nil]
  ring

/-! ## 4. THE MASS READING, AND WHERE IT STOPS -/

/-- (4) The outer draws at which the guard is dead, for a fixed non-constant
committed column and a fixed supplied cell, read through ISFS's `rowPointOf` --
the row point the run's OWN outer draw determines. -/
def deadOuterDraws (m : Nat) (cellIndex : Fin 5) (bits : Nat) (v w x : Element) :
    Set (JointChallengeSpace.JointSpace m) :=
  { u | ¬ IndexPointZeroCheck.CellsDifferOnCube bits [x]
      (IndexPointZeroCheck.openedCells [spikeColumn m v w]
        (OpenedClaimFold.lift (IndexStageFinerSplit.rowPointOf m cellIndex u))) }

theorem row_point_lift_length (m : Nat) (cellIndex : Fin 5)
    (u : JointChallengeSpace.JointSpace m) :
    (OpenedClaimFold.lift (IndexStageFinerSplit.rowPointOf m cellIndex u)).length = m := by
  rw [OpenedClaimFold.lift, List.length_map, IndexStageFinerSplit.row_point_of_length]

/-- (4) **AT THE RUN'S OWN OUTER DRAW THE DEAD CONDITION IS ONE ELEMENT
EQUATION.** -/
theorem guard_dead_at_the_outer_draw_iff (m : Nat) (cellIndex : Fin 5) (bits : Nat)
    (v w x : Element) (hwv : w ≠ v) (u : JointChallengeSpace.JointSpace m) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube bits [x]
        (IndexPointZeroCheck.openedCells [spikeColumn m v w]
          (OpenedClaimFold.lift (IndexStageFinerSplit.rowPointOf m cellIndex u)))
      ↔ eqAtZero (OpenedClaimFold.lift (IndexStageFinerSplit.rowPointOf m cellIndex u))
        = (x - v) / (w - v) :=
  guard_dead_at_nonconstant_column_iff_ratio bits m v w x _ (row_point_lift_length m cellIndex u)
    hwv

/-- (4) **SO THE DEAD SET IS A LEVEL SET**, and that is exactly as far as this
module goes.  Turning "the row point solves one field equation" into a bound on
the MASS of such outer draws would need a root count for the realized row point as
a function of the oracle draw; the adopted root-count lemmas count free field
tuples, not reductions of oracle squeezes, so no such bound is claimed here.  See
HONESTY (5). -/
theorem dead_outer_draws_eq_level_set (m : Nat) (cellIndex : Fin 5) (bits : Nat)
    (v w x : Element) (hwv : w ≠ v) :
    deadOuterDraws m cellIndex bits v w x
      = { u | eqAtZero (OpenedClaimFold.lift (IndexStageFinerSplit.rowPointOf m cellIndex u))
          = (x - v) / (w - v) } := by
  apply Set.ext
  intro u
  exact guard_dead_at_the_outer_draw_iff m cellIndex bits v w x hwv u

/-! ## 5. THE CONCRETE INSTANCE AT TSCC'S LIVE WITNESS -/

theorem eqAtZero_replicate_zero : ∀ m : Nat, eqAtZero (List.replicate m (0 : Element)) = 1
  | 0 => rfl
  | m + 1 => by
      rw [List.replicate_succ, eqAtZero_cons, eqAtZero_replicate_zero m]
      ring

theorem eqAtZero_eq_zero_of_one_mem : ∀ (tau : List Element), (1 : Element) ∈ tau →
    eqAtZero tau = 0
  | [], h => absurd h (by simp)
  | t :: rest, h => by
      rcases List.mem_cons.mp h with h1 | h2
      · rw [eqAtZero_cons, ← h1]
        ring
      · rw [eqAtZero_cons, eqAtZero_eq_zero_of_one_mem rest h2]
        ring

/-- (5) The supplied cell family at TSCC's `liveProof x` is the singleton `[⟨x⟩]`
at every one of the five bound cells and at every index point. -/
theorem live_supplied_cell (x : Verifier.Ext3) (idx0 : Verifier.IndexPoints) (cellIndex : Fin 5) :
    OpenedClaimFold.lift (OpenedClaimFold.boundCell (TwoStageConditionalCount.liveProof x).used
      idx0 cellIndex).1 = [(⟨x⟩ : Element)] := by
  fin_cases cellIndex <;> rfl

/-- (5) **THE GUARD AT TSCC'S LIVE WITNESS AGAINST A NON-CONSTANT COLUMN.**  With
`v = 0` and `w = 1` the committed cell at the ALL-ZERO row point is `w = 1`, so the
guard is live exactly when the supplied cell is not `1`. -/
theorem live_guard_at_the_all_zero_row_iff (m : Nat) (x : Verifier.Ext3)
    (idx0 : Verifier.IndexPoints) (cellIndex : Fin 5) :
    IndexPointZeroCheck.CellsDifferOnCube 8
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell (TwoStageConditionalCount.liveProof x).used
          idx0 cellIndex).1)
        (IndexPointZeroCheck.openedCells [spikeColumn m 0 1] (List.replicate m 0))
      ↔ (⟨x⟩ : Element) ≠ 1 := by
  rw [live_supplied_cell,
    guard_live_at_nonconstant_column_iff 8 m 0 1 _ (List.replicate m 0) (by simp),
    eqAtZero_replicate_zero]
  constructor
  · intro h hx
    exact h (by rw [hx]; ring)
  · intro h hx
    exact h (by rw [hx]; ring)

/-- (5) **A ROW POINT AT WHICH THE GUARD IS LIVE, AT A NON-CONSTANT COMMITTED
COLUMN.**  This is the witness ISFS's HONESTY (9) does not have: the committed
column `spikeColumn m 0 1` is not constant for `0 < m`
(`spike_column_not_constant`), and the adopted guard nevertheless fires at the
all-zero row point for every supplied cell other than `1`.  The all-zero row point
is a row point of the right LENGTH; it is NOT shown to be realized by any outer
draw, and nothing below claims it is.  See HONESTY (6). -/
theorem live_guard_is_live_at_the_all_zero_row (m : Nat) (x : Verifier.Ext3)
    (idx0 : Verifier.IndexPoints) (cellIndex : Fin 5) (hx : (⟨x⟩ : Element) ≠ 1) :
    IndexPointZeroCheck.CellsDifferOnCube 8
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell (TwoStageConditionalCount.liveProof x).used
        idx0 cellIndex).1)
      (IndexPointZeroCheck.openedCells [spikeColumn m 0 1] (List.replicate m 0)) :=
  (live_guard_at_the_all_zero_row_iff m x idx0 cellIndex).mpr hx

/-- (5) **AND A ROW POINT AT WHICH IT IS DEAD.**  Any row point carrying a
coordinate `1` kills the eq weight at vertex zero, so the committed cell is `v = 0`
there and a supplied `0` agrees with it.  This is the honest case: the claim is
true, and `guardedIndexBadEvent` is `∅` by `dead_guard_kills_index_event`. -/
theorem live_guard_is_dead_at_a_row_with_a_one (m : Nat) (x : Verifier.Ext3)
    (idx0 : Verifier.IndexPoints) (cellIndex : Fin 5) (row : List Element)
    (hrow : row.length = m) (hone : (1 : Element) ∈ row) (hx : (⟨x⟩ : Element) = 0) :
    ¬ IndexPointZeroCheck.CellsDifferOnCube 8
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell (TwoStageConditionalCount.liveProof x).used
        idx0 cellIndex).1)
      (IndexPointZeroCheck.openedCells [spikeColumn m 0 1] row) := by
  rw [live_supplied_cell, guard_dead_at_nonconstant_column_iff 8 m 0 1 _ row hrow,
    eqAtZero_eq_zero_of_one_mem row hone, hx]
  ring

/-- (5) **THE PAYOFF FOR THE INDEX HALF.**  Where the guard is live the adopted
`IndexLanesOracle.guardedIndexBadEvent` is the FULL union of the two lane
agreement pullbacks, not the `∅` of `dead_guard_kills_index_event`.  So at a
non-constant committed column the index half of ISFS's split is not killed by its
guard.  What this does NOT say: that the union is non-empty, that the index draw
lands in it, or that any bound changes.  See HONESTY (1) and (2). -/
theorem index_event_not_killed_at_the_spike_column (m : Nat) (x : Verifier.Ext3)
    (idx0 : Verifier.IndexPoints) (cellIndex : Fin 5) (hx : (⟨x⟩ : Element) ≠ 1) :
    IndexLanesOracle.guardedIndexBadEvent 8
        (OpenedClaimFold.lift (OpenedClaimFold.boundCell (TwoStageConditionalCount.liveProof x).used
          idx0 cellIndex).1)
        (IndexPointZeroCheck.openedCells [spikeColumn m 0 1] (List.replicate m 0))
      = IndexPointZeroCheck.logAgreementEvent 8
          (OpenedClaimFold.lift (OpenedClaimFold.boundCell
            (TwoStageConditionalCount.liveProof x).used idx0 cellIndex).1)
          (IndexPointZeroCheck.openedCells [spikeColumn m 0 1] (List.replicate m 0))
        ∪ IndexPointZeroCheck.gateAgreementEvent 8
          (OpenedClaimFold.lift (OpenedClaimFold.boundCell
            (TwoStageConditionalCount.liveProof x).used idx0 cellIndex).1)
          (IndexPointZeroCheck.openedCells [spikeColumn m 0 1] (List.replicate m 0)) :=
  IndexLanesOracle.guarded_index_bad_event_of_differ 8 _ _
    (live_guard_is_live_at_the_all_zero_row m x idx0 cellIndex hx)

end Audit.Wire3.IndexGuardLiveness
