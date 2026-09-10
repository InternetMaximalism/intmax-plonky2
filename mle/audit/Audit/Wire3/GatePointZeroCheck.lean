import Audit.Wire3.ConstantsProvenance
import Audit.Wire3.JointChallengeSpace

/-!
# The gate-point zero check: closing the fold-vs-column residue of `ConstantsProvenance`

## The gap this module closes

The adopted `Audit.Wire3.ConstantsProvenance` proves
`partial_zeroing_forces_one_of_three`: if the SUPPLIED constants column and the
column the DEPLOYMENT-PINNED preprocessed root commits to have DIFFERENT fully
bound cells at the verifier's derived gate point, then one of three things
breaks (root pin / extraction join / opening relation).  Its recorded residue is
`bound_cell_agreement_is_not_column_equality`:

> THE RESIDUE IS FOLD-LEVEL, NOT COLUMN-LEVEL. … a forger whose selector edit is
> invisible at the derived gate point falsifies the hypothesis of the attack
> theorem.  Excluding that needs a zero check over the gate point, which is a
> SUMCHECK challenge; no such argument is attempted here.

That zero check is what this module supplies, and nothing else.

## WHAT IS PROVED

1. **THE BRIDGE.**  `cell_bindColumn_eq_extension`: for a point of length `n` and
   a column of length AT LEAST `2 ^ n`, the adopted fold
   `NormTerminalBinding.cell (NormTerminalBinding.bindColumn col point)` IS the
   adopted multilinear extension `ZeroCheckSemantics.extension col point`, whose
   weights are the actual `ext3_eq_evals` entries
   (`ZeroCheckSemantics.extensionOf_uses_eq_table`).  No new evaluation
   function is introduced; the two adopted notions are identified.

   The hypothesis is `2 ^ point.length ≤ col.length`, an INEQUALITY.  Only
   SHORTER columns break the identity: `padding_breaks_the_bridge` exhibits one
   (`bindColumn` truncates — `bind_buffer_length` halves the length — while
   `extension` zero-pads through `getD`, and the two disagree already at `[5]`
   in one variable), and `longer_column_agrees` exhibits a LONGER column at which
   the identity still HOLDS (`[1,2,3,4]` in one variable), which is why the
   equality version would be too strong.  `cell_bindColumn_eq_extension_of_width`
   is the `col.length = 2 ^ point.length` corollary, kept because the width the
   downstream theorems actually have on hand is an equality.

   Where the EQUALITY of widths is genuinely needed is NOT the bridge but
   `columnsDifferOnCube_of_ne`: turning a LIST inequality `col ≠ committedCol`
   into a differing index BELOW `2 ^ n` — a differing CUBE index, the shape the
   Schwartz--Zippel count consumes — needs both columns to have exactly the cube
   width, since two lists may differ only above the cube.

2. **THE AGREEMENT SET IS A VANISHING SET.**  `columnAgreementSet n col
   committedCol` is the set of gate points at which the two columns' bound cells
   AGREE.  `columnAgreementSet_eq_vanishingSet` proves it is exactly the adopted
   `ZeroCheckSemantics.vanishingSet` of the DIFFERENCE column, using the
   linearity of the adopted extension in the value family
   (`extensionOf_affine`, proved here from the adopted `sum_map_mul_left`).
   Hence the adopted `vanishing_card_bound` / `vanishing_density_bound` apply
   verbatim: if the columns differ at some cube index, the agreement set has at
   most `n * |F|^(n-1)` points, density at most `n / |F|`, with `|F| = p^3`.

3. **THE MASS, ON THE ADOPTED PRODUCT LAW.**  `gate_point_agreement_mass_bound`:
   on the SAME explicit uniform law the adopted `ChallengeUnionBound` uses for
   the tau column (`uniformProductProbability` on `TripleTuple n`), the mass of
   the agreement set is at most the adopted `ChallengeUnionBound.tauTerm n` —
   the SAME bound the tau zero check gets, because it is the SAME
   Schwartz--Zippel statement about a different value family.

4. **THE COMPOSED ATTACK THEOREM.**
   `column_forgery_forces_one_of_three_off_bad_set` and its acceptance form
   `accepted_column_forgery_forces_join_or_opening_off_bad_set` replace the
   adopted `hdiff` (bound cells differ — a hypothesis about ONE linear
   functional) by `hpoint`: the derived gate point is OUTSIDE the agreement set.
   They conclude the same three-way (resp. two-way) disjunction.  The point
   length is DERIVED from acceptance, through the adopted
   `Verifier.acceptance_coupled_point_lengths` and
   `Integrated.concrete_engine_keeps_transcript`
   (`accepted_gate_point_width`), not assumed.

   Neither `col ≠ committedCol` nor the COMMITTED column's width is a
   hypothesis.  The first follows from `hpoint`
   (`columns_differ_of_point_off_agreement`).  The second is DERIVED inside
   branch (B): if the opening relation stands, `OpensCommittedTable.full` at
   bound cell `3` (whose row point `OpenedClaimFold.cellRow s 3` IS the gate
   point) forces `committedCol.length = 2 ^ (gate point length)` once
   `committedCol ∈ cols 3`, which `hcols`/`hcc` supply — see
   `committed_width_of_opens`.  The SUPPLIED column's width is likewise pinned
   by the adopted `GateDenseRound.Consistent` (adopted field 2 of
   `GateDerivedRejection.DerivedGateAssumptions`) together with the adopted
   `EqCellBinding` — `supplied_width_of_consistent` — so the `…_of_consistent`
   variants of all three composed theorems take `Consistent` in place of a raw
   width hypothesis.

5. **THE GATE POINT IS THE `outerGate` BLOCK OF THE ADOPTED JOINT SPACE.**
   `gate_point_column_is_the_gate_lane_challenges` proves — it is not assumed —
   that `TranscriptProvenance.gatePointColumn e c p` is exactly the list of
   per-coupled-round GATE challenges, i.e. the `challenge` fields of the adopted
   `ConditionalSoundness.gateLaneOf`.  Those are precisely the draws the adopted
   `JointChallengeSpace.Draw.outerGate` indexes.  So the agreement set is added
   as a FOURTH family pulled back to the `outerGate` coordinates of the ONE
   adopted `JointSpace`, with `gate_point_event_mass` (mass EQUALS the product
   mass, by the same cylinder split the adopted `tau_event_mass` performs) and
   `gate_point_agreement_joint_mass_bound`.
   `gate_point_off_agreement_of_joint` transports a good joint draw to
   `¬ PointAgrees`, so the composed theorem is consumable from the joint law.

## WHAT IS **NOT** PROVED

* **NO PROBABILITY OVER RUNS.**  The gate point is DERIVED from the run's own
  transcript by `Verifier.derivedRounds`; it is not sampled.  Every bound here
  is the mass of an explicit event on an EXPLICIT finite uniform law
  (`ChallengeUnionBound.uniformProductProbability`,
  `JointChallengeSpace.jointProbability`), exactly as the adopted
  `OuterChallenge.uniformTupleProbability` is.  Nothing connects either law to
  the deployed Keccak sponge, and the adopted
  `JointChallengeSpace` header's caveat carries over unchanged: the
  `(round + 1, 0)` / `(round + 1, 3)` counters that label `outerLog` /
  `outerGate` are DOCUMENTED against
  `OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`,
  not derived for the abstract `Verifier.Engine` these theorems quantify over.
  What IS derived here is the other half: that the gate point column IS the
  gate-lane round-challenge list (§5), so the `outerGate` block is the right
  block to have pulled back.
* **ADAPTIVITY — HALF FORMALIZED, HALF NOT.**  Read as a probability statement,
  the argument needs the forged column `col` to be fixed BEFORE the gate point
  is squeezed.
  * Half **(A)**, PARTLY covered, and only for the COMMITTED column.  The
    committed column sits under the PREPROCESSED ROOT, and the adopted
    `CommitmentOrder` pins that root at PREFIX FRAME 13
    (`frames_get_preprocessed_root`); that root is compared against the
    deployment pin (adopted `ConstantsProvenance.accepted_root_is_pinned`).
    What the adopted `CommitmentOrder` half (A)
    (`deterministic_adaptivity`-style factorization) actually states is about
    the GATE ALPHA and GATE TAU squeezes from the PREFIX digest, and it is
    stated MODULO the visible `CommittedTables` extraction join.  It says
    NOTHING about the coupled-ROUND challenges, which is what the gate POINT is
    made of; and "the round digests are chained after the prefix" is DOCUMENTED
    for the CONCRETE engine only — for the abstract `Verifier.Engine` these
    theorems quantify over it is not derived (this is the RES-4 caveat, repeated
    here so that half (A) is not read as more than it is).
  * The SUPPLIED column `s0.tables.constants` is tied to that root by NOTHING
    except the two branches of the conclusion (R2/R3): `ConstantsColumnsOfRoot`
    is a supplied map and `OpensCommittedTable` is a visible hypothesis.  So in
    THIS model an adversary who chooses `col` AFTER seeing the gate point is not
    excluded by anything other than those branches.  The density reading of §2/§3
    is meaningful only with `col` FIXED BEFORE the point.
  * Half **(B)**, NOT covered: nothing in the adopted model turns "the root was
    absorbed first" into "the COLUMN was chosen first" — that is exactly
    residues R1/R2/R3 below.  No Fiat--Shamir extraction argument is formalized
    anywhere in this audit, and none is attempted here.
* **R1/R2/R3 ARE UNCHANGED.**  The three-way disjunction still has the adopted
  `OpeningBinding` residues in two of its branches: R1 (no link from the
  engine's WHIR observation to a concrete `WhirRows`/`Merkle` execution), R2
  (`OpensCommittedTable` is a visible hypothesis), R3 (`ConstantsColumnsOfRoot`
  is a supplied root-to-columns map).  This module does not touch them.
* **WHIR AND MERKLE ARE EXCLUDED.**  Nothing here is about the PCS.
* **THIS IS NOT THE SYSTEM'S SOUNDNESS ERROR.**  `tauTerm n` is the mass of ONE
  event on ONE explicit law.  It is not composed with the adopted union bound
  into a soundness statement, and no soundness theorem exists in this audit.
* **THE DISJUNCTION IS STILL A DISJUNCTION.**  The composed theorem does not say
  partial selector zeroing is impossible; it says a column forgery that is
  visible at the gate point must break the extraction join or the opening
  relation.

## RESIDUES OF THIS MODULE

* **RES-1 (adaptivity half (B))**, above: `col` is quantified over, not
  extracted; the bound is on the explicit law, not on a Fiat--Shamir adversary.
* **RES-2 (width), NARROWED**: both widths ARE forced by the adopted model, so
  neither is a standing assumption of the composed theorems any more.
  * The SUPPLIED column's width is pinned by the adopted
    `GateDenseRound.Consistent (Integrated.gateConfig vc) s0` — adopted field 2
    of `GateDerivedRejection.DerivedGateAssumptions` — together with the adopted
    `EqCellBinding`, which equates the bound challenge list with the derived
    gate point: `supplied_width_of_consistent`.
  * The COMMITTED column's width is forced by the OPENING RELATION itself,
    inside branch (B): `OpensCommittedTable.full` at bound cell `3`, whose row
    point is the gate point: `committed_width_of_opens`.  So the composed
    theorems carry no `hccWidth` at all.
  * WHAT REMAINS: the Schwartz--Zippel COUNT needs `ColumnsDifferOnCube`, and
    deriving that from the list inequality `col ≠ committedCol`
    (`columnsDifferOnCube_of_ne`) needs BOTH widths as EQUALITIES, since two
    lists can differ only above the cube.  A consumer who wants the DENSITY
    statement (not merely the disjunction) therefore still has to hold both
    width equalities at once; the bridge itself does not (it holds under `≤`).
* **RES-3 (one column at a time)**: the theorem is indexed by ONE constants
  index `j < numConstants`.  No union over the `numConstants` columns is taken,
  so the honest multi-column bound would be `numConstants` times this one.
* **RES-4 (counter labels)**: inherited from the adopted `JointChallengeSpace` —
  the `outerGate` counter label is documented against the concrete engine, not
  derived for the abstract `Verifier.Engine` quantified over here.  Half (A)
  above repeats it, because half (A) is otherwise easy to over-read.

## DEGENERACY NOTES

* `col = committedCol` makes the composed theorems VACUOUS, not false: the
  agreement set is then ALL of `Finset.univ` (`agreement_set_of_equal_columns`),
  so `hpoint` cannot hold (`no_point_off_agreement_at_equal_columns`).
* `degreeBits = 0` makes the bound TRIVIAL and the event EMPTY-ish in the same
  degenerate way: `tauTerm_zero` gives `ChallengeUnionBound.tauTerm 0 = 0`, and a
  zero-length point means the columns are single cells, where "differ on the
  cube" is just "differ at index `0`" and the fold IS that cell.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Audit.Wire3.GatePointZeroCheck

open Audit.Wire3 GoldilocksExt3Field

/-! ## 0. Linearity of the adopted multilinear extension in its value family

`ZeroCheckSemantics.extensionOf g tau` is a fixed eq-weighted sum of the values
`g i`, so it is linear in `g`.  The adopted module proves the affine split in
the POINT coordinate (`extensionOf_cons`); this section proves the affine
combination in the VALUES, which is what turns "two columns agree at a point"
into "the difference column's extension vanishes there". -/

theorem sum_map_add (l : List Nat) (f g : Nat → Element) :
    (l.map (fun i => f i + g i)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- Only the cube values matter: two families agreeing below `2 ^ |tau|` have
the same extension. -/
theorem extensionOf_congr (a b : Nat → Element) (tau : List Element)
    (h : ∀ i, i < 2 ^ tau.length → a i = b i) :
    ZeroCheckSemantics.extensionOf a tau = ZeroCheckSemantics.extensionOf b tau := by
  simp only [ZeroCheckSemantics.extensionOf]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i hi
  rw [h i (List.mem_range.mp hi)]

/-- LINEARITY IN THE VALUES.  The adopted extension of an affine combination of
two value families is that affine combination of their extensions. -/
theorem extensionOf_affine (c d : Element) (a b : Nat → Element) (tau : List Element) :
    ZeroCheckSemantics.extensionOf (fun i => c * a i + d * b i) tau
      = c * ZeroCheckSemantics.extensionOf a tau + d * ZeroCheckSemantics.extensionOf b tau := by
  simp only [ZeroCheckSemantics.extensionOf]
  have hmap : ((List.range (2 ^ tau.length)).map
        (fun i => EqTableProvenance.rowProdFrom 0 tau i * (c * a i + d * b i)))
      = (List.range (2 ^ tau.length)).map
        (fun i => c * (EqTableProvenance.rowProdFrom 0 tau i * a i)
          + d * (EqTableProvenance.rowProdFrom 0 tau i * b i)) := by
    refine List.map_congr_left ?_
    intro i _
    ring
  rw [hmap, sum_map_add, ZeroCheckSemantics.sum_map_mul_left,
    ZeroCheckSemantics.sum_map_mul_left]

/-- Difference form of `extensionOf_affine`. -/
theorem extensionOf_sub (a b : Nat → Element) (tau : List Element) :
    ZeroCheckSemantics.extensionOf (fun i => a i - b i) tau
      = ZeroCheckSemantics.extensionOf a tau - ZeroCheckSemantics.extensionOf b tau := by
  have hfun : (fun i => a i - b i) = (fun i => (1 : Element) * a i + (-1 : Element) * b i) := by
    funext i
    ring
  rw [hfun, extensionOf_affine]
  ring

/-! ## 1. THE BRIDGE: the adopted fold IS the adopted multilinear extension -/

/-- **THE BRIDGE.**  For a point of length `n` and a column of length AT LEAST
`2 ^ n`, the fully bound cell of the adopted `NormTerminalBinding.bindColumn`
fold is the adopted `ZeroCheckSemantics.extension` of the column at that point.

Both sides are adopted objects: the left is the gate prover's actual
`bind_challenge` loop on one column (`ConstantsProvenance.bindAlong_constants`),
the right is the eq-weighted Boolean-cube sum whose weights are the entries of
the real `ext3_eq_evals` table (`ZeroCheckSemantics.extensionOf_uses_eq_table`).

EXACT HYPOTHESIS: `2 ^ point.length ≤ col.length`.  Only SHORTER columns break
the identity (`padding_breaks_the_bridge`); LONGER ones do not
(`longer_column_agrees`), because `bindBuffer` reads exactly the `2 ^ n` lines
the cube uses and drops the rest.  The equality version is
`cell_bindColumn_eq_extension_of_width`.  The EQUALITY of widths is needed
elsewhere — by `columnsDifferOnCube_of_ne`, to turn a LIST inequality into a
differing CUBE index — not here. -/
theorem cell_bindColumn_eq_extension : ∀ (point col : List Element),
    2 ^ point.length ≤ col.length →
    NormTerminalBinding.cell (NormTerminalBinding.bindColumn col point)
      = ZeroCheckSemantics.extension col point := by
  intro point
  induction point with
  | nil =>
      intro col _hlen
      rw [NormTerminalBinding.bind_column_nil, ZeroCheckSemantics.extension_eq_extensionOf,
        ZeroCheckSemantics.extensionOf_nil]
      rfl
  | cons r rs ih =>
      intro col hlen
      have hpow : 2 ^ (r :: rs).length = 2 * 2 ^ rs.length := by
        rw [List.length_cons, Nat.pow_succ]; omega
      have hhalf : 2 ^ rs.length ≤ (DenseMleIndexed.bindBuffer col r).length := by
        rw [DenseMleIndexed.bind_buffer_length]; omega
      have hstep : ZeroCheckSemantics.extensionOf
            (fun i => (DenseMleIndexed.bindBuffer col r).getD i 0) rs
          = ZeroCheckSemantics.extensionOf
            (fun i => (1 - r) * col.getD (2 * i) 0 + r * col.getD (2 * i + 1) 0) rs := by
        refine extensionOf_congr _ _ rs ?_
        intro i hi
        have hib : i < col.length / 2 := by omega
        rw [DenseMleIndexed.bind_buffer_reads_exact_line col r i hib]
        rfl
      calc NormTerminalBinding.cell (NormTerminalBinding.bindColumn col (r :: rs))
          = ZeroCheckSemantics.extensionOf
              (fun i => (DenseMleIndexed.bindBuffer col r).getD i 0) rs :=
            ih (DenseMleIndexed.bindBuffer col r) hhalf
        _ = ZeroCheckSemantics.extensionOf
              (fun i => (1 - r) * col.getD (2 * i) 0 + r * col.getD (2 * i + 1) 0) rs := hstep
        _ = (1 - r) * ZeroCheckSemantics.extensionOf (fun i => col.getD (2 * i) 0) rs
              + r * ZeroCheckSemantics.extensionOf (fun i => col.getD (2 * i + 1) 0) rs :=
            extensionOf_affine _ _ _ _ rs
        _ = ZeroCheckSemantics.extension col (r :: rs) :=
            (ZeroCheckSemantics.extensionOf_cons (fun i => col.getD i 0) r rs).symm

/-- THE EQUALITY COROLLARY of the bridge, in the form the downstream theorems
have on hand (they get widths as equations, from `Consistent` or from the
opening relation). -/
theorem cell_bindColumn_eq_extension_of_width (point col : List Element)
    (hlen : col.length = 2 ^ point.length) :
    NormTerminalBinding.cell (NormTerminalBinding.bindColumn col point)
      = ZeroCheckSemantics.extension col point :=
  cell_bindColumn_eq_extension point col (le_of_eq hlen.symm)

/-- A column SHORTER than the cube: one entry, one variable. -/
def shortColumn : List Element := [5]

/-- **THE NEGATIVE SIDE: SHORTER COLUMNS BREAK THE BRIDGE.**  `bindColumn`
TRUNCATES (the adopted `bind_buffer_length` halves the length, so a one-entry
column binds to the empty list, whose `cell` is the zero-totalized `0`), while
`extension` ZERO-PADS through `getD` and returns `5`.  So the bridge is false
for columns NARROWER than the cube — this is the only direction in which the
hypothesis bites. -/
theorem padding_breaks_the_bridge :
    NormTerminalBinding.cell (NormTerminalBinding.bindColumn shortColumn [0])
      ≠ ZeroCheckSemantics.extension shortColumn [0] := by
  decide

/-- **THE POSITIVE SIDE: LONGER COLUMNS DO NOT.**  A four-entry column at a
ONE-variable point — twice the cube width — still satisfies the identity, at a
nonzero challenge.  Together with `padding_breaks_the_bridge` this is why the
bridge's hypothesis is the INEQUALITY `2 ^ point.length ≤ col.length` and not
the equation: the equation would exclude this case for no reason. -/
theorem longer_column_agrees :
    NormTerminalBinding.cell (NormTerminalBinding.bindColumn [1, 2, 3, 4] [7])
      = ZeroCheckSemantics.extension [1, 2, 3, 4] [7] := by
  decide

/-! ## 2. THE AGREEMENT SET AND ITS SCHWARTZ--ZIPPEL BOUND -/

/-- The two columns' folds agree at this point. -/
def PointAgrees (col committedCol point : List Element) : Prop :=
  ZeroCheckSemantics.extension col point = ZeroCheckSemantics.extension committedCol point

/-- The DIFFERENCE column, as a value family on the Boolean cube. -/
def diffColumn (col committedCol : List Element) : Nat → Element :=
  fun i => col.getD i 0 - committedCol.getD i 0

/-- **THE AGREEMENT SET**: the gate points, as `n`-coordinate tuples, at which
the supplied column and the committed column have the SAME fully bound cell.
This is the set the forger must hit; §3 bounds its mass. -/
def columnAgreementSet (n : Nat) (col committedCol : List Element) :
    Finset (ZeroCheckSemantics.Tuple n) :=
  Finset.univ.filter (fun r => ZeroCheckSemantics.extension col (List.ofFn r)
    = ZeroCheckSemantics.extension committedCol (List.ofFn r))

theorem mem_columnAgreementSet (n : Nat) (col committedCol : List Element)
    (r : ZeroCheckSemantics.Tuple n) :
    r ∈ columnAgreementSet n col committedCol ↔ PointAgrees col committedCol (List.ofFn r) := by
  simp only [columnAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and, PointAgrees]

/-- List form, with no coordinate transport: the tuple of a point list is in the
agreement set of that list's own width exactly when the folds agree. -/
theorem mem_columnAgreementSet_tupleOf (col committedCol point : List Element) :
    ZeroCheckSemantics.tupleOf point ∈ columnAgreementSet point.length col committedCol
      ↔ PointAgrees col committedCol point := by
  rw [mem_columnAgreementSet, ZeroCheckSemantics.ofFn_tupleOf]

/-- Transport across a proved width, in the shape the adopted
`JointChallengeSpace.good_derived_tau_of_joint` uses: a tuple whose coordinates
ARE the point's entries is in the agreement set exactly when the folds agree. -/
theorem not_agrees_of_not_mem (n : Nat) (col committedCol point : List Element)
    (hn : point.length = n) (t : ZeroCheckSemantics.Tuple n)
    (hget : ∀ i : Fin n, ∀ h : i.val < point.length, point.get ⟨i.val, h⟩ = t i)
    (h : t ∉ columnAgreementSet n col committedCol) :
    ¬ PointAgrees col committedCol point := by
  subst hn
  have ht : ZeroCheckSemantics.tupleOf point = t := by
    funext i
    exact hget i i.isLt
  intro hagree
  exact h (ht ▸ (mem_columnAgreementSet_tupleOf col committedCol point).mpr hagree)

/-- **THE AGREEMENT SET IS THE VANISHING SET OF THE DIFFERENCE COLUMN.**  This
is the whole content of the reduction: the adopted `vanishingSet` machinery
applies to it verbatim. -/
theorem columnAgreementSet_eq_vanishingSet (n : Nat) (col committedCol : List Element) :
    columnAgreementSet n col committedCol
      = ZeroCheckSemantics.vanishingSet n (diffColumn col committedCol) := by
  apply Finset.ext
  intro r
  rw [mem_columnAgreementSet, ZeroCheckSemantics.mem_vanishingSet]
  have hsub : ZeroCheckSemantics.extensionOf (diffColumn col committedCol) (List.ofFn r)
      = ZeroCheckSemantics.extension col (List.ofFn r)
        - ZeroCheckSemantics.extension committedCol (List.ofFn r) :=
    extensionOf_sub (fun i => col.getD i 0) (fun i => committedCol.getD i 0) (List.ofFn r)
  rw [hsub, sub_eq_zero]
  exact Iff.rfl

/-- The exact shape of "the columns differ" that the count needs: they differ at
some index of the Boolean cube. -/
def ColumnsDifferOnCube (n : Nat) (col committedCol : List Element) : Prop :=
  ∃ j, j < 2 ^ n ∧ col.getD j 0 ≠ committedCol.getD j 0

theorem exists_differing_index : ∀ (a b : List Element), a.length = b.length → a ≠ b →
    ∃ j, j < a.length ∧ a.getD j 0 ≠ b.getD j 0
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, hne => by
      by_cases hxy : x = y
      · subst hxy
        have hxs : xs ≠ ys := fun h => hne (by rw [h])
        obtain ⟨j, hj, hne'⟩ := exists_differing_index xs ys (by simpa using hlen) hxs
        exact ⟨j + 1, by simp only [List.length_cons]; omega, hne'⟩
      · exact ⟨0, by simp only [List.length_cons]; omega, hxy⟩

/-- Column inequality, at the cube width, IS `ColumnsDifferOnCube`.

**THIS — NOT THE BRIDGE — IS WHERE THE WIDTH EQUALITIES ARE NEEDED.**  A LIST
inequality only says the columns differ SOMEWHERE; the Schwartz--Zippel count
needs them to differ at an index BELOW `2 ^ n`.  Two lists of unequal or excess
length can differ only ABOVE the cube, where the extension does not look.  Both
`hcol` and `hcc` are therefore equations here, and only here. -/
theorem columnsDifferOnCube_of_ne (n : Nat) (col committedCol : List Element)
    (hcol : col.length = 2 ^ n) (hcc : committedCol.length = 2 ^ n)
    (hne : col ≠ committedCol) : ColumnsDifferOnCube n col committedCol := by
  obtain ⟨j, hj, hne'⟩ := exists_differing_index col committedCol (by rw [hcol, hcc]) hne
  exact ⟨j, by rw [← hcol]; exact hj, hne'⟩

/-- The difference column is a nonzero cube value family. -/
theorem diffColumn_ne_zero (n : Nat) (col committedCol : List Element)
    (h : ColumnsDifferOnCube n col committedCol) :
    ∃ j, j < 2 ^ n ∧ diffColumn col committedCol j ≠ 0 := by
  obtain ⟨j, hj, hne⟩ := h
  exact ⟨j, hj, sub_ne_zero.mpr hne⟩

/-- **(1) THE COUNT.**  Two columns that differ somewhere on the cube agree at
at most `n * |F|^(n-1)` of the `|F|^n` gate points.  This is the adopted
`ZeroCheckSemantics.vanishing_card_bound` applied to the difference column;
nothing sharper is claimed, and `|F| = p^3` is never evaluated. -/
theorem columnAgreement_card_bound (n : Nat) (col committedCol : List Element)
    (h : ColumnsDifferOnCube n col committedCol) :
    (columnAgreementSet n col committedCol).card * Fintype.card Element
      ≤ n * Fintype.card Element ^ n := by
  rw [columnAgreementSet_eq_vanishingSet]
  exact ZeroCheckSemantics.vanishing_card_bound n (diffColumn col committedCol)
    (diffColumn_ne_zero n col committedCol h)

/-- **(1) THE DENSITY.**  The same count as a density: at most `n / |F|`. -/
theorem columnAgreement_density_bound (n : Nat) (col committedCol : List Element)
    (h : ColumnsDifferOnCube n col committedCol) :
    ((columnAgreementSet n col committedCol).card : ℚ) / ((Fintype.card Element : ℚ) ^ n)
      ≤ (n : ℚ) / (Fintype.card Element : ℚ) := by
  rw [columnAgreementSet_eq_vanishingSet]
  exact ZeroCheckSemantics.vanishing_density_bound n (diffColumn col committedCol)
    (diffColumn_ne_zero n col committedCol h)

/-- Under the difference hypothesis the agreement set IS the adopted
`zeroCheckBadSet` of the difference column, so every adopted consumer of that
bad set applies. -/
theorem columnAgreementSet_eq_zeroCheckBadSet (n : Nat) (col committedCol : List Element)
    (h : ColumnsDifferOnCube n col committedCol) :
    columnAgreementSet n col committedCol
      = ZeroCheckSemantics.zeroCheckBadSet n (diffColumn col committedCol) := by
  have hnot : ¬ ZeroCheckSemantics.CubeZero n (diffColumn col committedCol) := by
    obtain ⟨j, hj, hne⟩ := diffColumn_ne_zero n col committedCol h
    intro hz
    exact hne (hz j hj)
  rw [ZeroCheckSemantics.zeroCheckBadSet_of_not_cube_zero n _ hnot,
    columnAgreementSet_eq_vanishingSet]

/-! ## 3. THE MASS, ON THE ADOPTED PRODUCT LAW -/

/-- **(2) THE GATE-POINT AGREEMENT MASS.**  On the SAME explicit uniform law the
adopted `ChallengeUnionBound` puts on an `n`-coordinate challenge column —
`n` independent digest triples, coordinatewise `OuterChallenge.reduceTriple` —
the mass of the gate points at which a forged constants column is invisible is
at most the adopted `ChallengeUnionBound.tauTerm n`.

It is LITERALLY the tau term: the tau zero check and this one are the same
Schwartz--Zippel statement about two different value families, so the bound is
the same expression, not merely one of the same shape.

NOT a probability over runs: the gate point is derived from the transcript.  See
the header. -/
theorem gate_point_agreement_mass_bound (n : Nat) (col committedCol : List Element)
    (h : ColumnsDifferOnCube n col committedCol) :
    ChallengeUnionBound.uniformProductProbability n (columnAgreementSet n col committedCol)
      ≤ ChallengeUnionBound.tauTerm n := by
  rw [columnAgreementSet_eq_zeroCheckBadSet n col committedCol h]
  exact ChallengeUnionBound.tau_product_mass_bound n (diffColumn col committedCol)

/-! ## 4. THE COMPOSED ATTACK THEOREM -/

/-- THE WIDTH OF THE DERIVED GATE POINT, FROM ACCEPTANCE, NOT ASSUMED.  The
adopted `Verifier.acceptance_coupled_point_lengths` gives
`(derivedRounds ...).gatePoint.length = degreeBits` for the model engine, and
the adopted `Integrated.concrete_engine_keeps_transcript` says the model engine
runs the SAME rounds as `e`; `TranscriptProvenance.liftList_length` carries it
to the lifted column. -/
theorem accepted_gate_point_width (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (vc : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ()) :
    (TranscriptProvenance.gatePointColumn e vc p).length = vc.degreeBits := by
  obtain ⟨_, _, _, _, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier e decode pin chain vc p hacc
  have h := (Verifier.acceptance_coupled_point_lengths (Integrated.modelEngine e decode) pin chain
    vc p hv).2
  rw [(Integrated.concrete_engine_keeps_transcript e decode vc p).2] at h
  show (TranscriptProvenance.liftList (Verifier.derivedRounds e vc p).gatePoint).length = _
  rw [TranscriptProvenance.liftList_length]
  exact h

/-- A gate point outside the agreement set forces the two bound cells apart:
this is the bridge of §1 read contrapositively, and it is the step that replaces
the adopted `hdiff`. -/
theorem bound_cells_differ_of_point_off_agreement (col committedCol point : List Element)
    (hcolWidth : col.length = 2 ^ point.length)
    (hccWidth : committedCol.length = 2 ^ point.length)
    (hpoint : ZeroCheckSemantics.tupleOf point ∉ columnAgreementSet point.length col committedCol) :
    NormTerminalBinding.cell (NormTerminalBinding.bindColumn col point)
      ≠ NormTerminalBinding.cell (NormTerminalBinding.bindColumn committedCol point) := by
  rw [cell_bindColumn_eq_extension_of_width point col hcolWidth,
    cell_bindColumn_eq_extension_of_width point committedCol hccWidth]
  intro hagree
  exact hpoint ((mem_columnAgreementSet_tupleOf col committedCol point).mpr hagree)

/-- `col ≠ committedCol` is not an extra assumption on top of `hpoint`: a point
outside the agreement set already witnesses that the columns differ.  This is why
the composed theorems below carry NO `col ≠ committedCol` binder.
It remains the hypothesis under which the agreement set is SMALL
(`columnAgreement_card_bound`), which is what makes the density reading
meaningful. -/
theorem columns_differ_of_point_off_agreement (col committedCol point : List Element)
    (hpoint : ZeroCheckSemantics.tupleOf point ∉ columnAgreementSet point.length col committedCol) :
    col ≠ committedCol := by
  intro heq
  subst heq
  exact hpoint ((mem_columnAgreementSet_tupleOf col col point).mpr rfl)

/-! ### 4a. Both widths are FORCED by the adopted model (RES-2, narrowed) -/

/-- **THE COMMITTED COLUMN'S WIDTH IS FORCED BY THE OPENING RELATION.**  The
adopted `OpeningBinding.OpensCommittedTable` unfolds to
`IntegratedTerminalChain.HonestOpenings`, whose field `full` says every column of
group `i` has length `2 ^ (OpenedClaimFold.cellRow s i).length`; and
`OpenedClaimFold.cellRow s 3` IS `s.gatePoint`.  So inside branch (B) — the
branch that is standing whenever the disjunction has NOT been discharged — the
committed column's width is not an assumption but a consequence.

This is why the composed theorems carry no `hccWidth`. -/
theorem committed_width_of_opens (e : Verifier.Engine) (vc : Verifier.Config) (p : Verifier.Proof)
    (cols : Fin 5 → List (List Element)) (committedCol : List Element)
    (hyp : OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
      (Verifier.derivedIndices e vc p) cols)
    (hmem : committedCol ∈ cols 3) :
    committedCol.length = 2 ^ (TranscriptProvenance.gatePointColumn e vc p).length := by
  have h3 := hyp.full 3 committedCol hmem
  show committedCol.length
    = 2 ^ (TranscriptProvenance.liftList (Verifier.derivedRounds e vc p).gatePoint).length
  rw [TranscriptProvenance.liftList_length]
  exact h3

/-- **THE SUPPLIED COLUMN'S WIDTH IS FORCED BY THE ADOPTED `Consistent`.**
`GateDenseRound.Consistent (Integrated.gateConfig vc) s0` is ADOPTED FIELD 2 of
`GateDerivedRejection.DerivedGateAssumptions` (`extractedStateConsistent`); its
shape clause says every constants MLE state of `s0` is valid with
`numVars = s0.eq.numVars`.  The adopted `EqCellBinding` equates the bound
challenge list with the derived gate point, so `s0.eq.numVars` IS the gate
point's length.

Hence the supplied constants column at any index has EXACTLY the cube width, and
`hcolWidth` need not be assumed either: the `…_of_consistent` variants below take
`Consistent` instead. -/
theorem supplied_width_of_consistent (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (j : Nat) (col : List Element)
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcol : s0.tables.constants.get? j = some col) :
    col.length = 2 ^ (TranscriptProvenance.gatePointColumn e vc p).length := by
  obtain ⟨t, steps, hsteps, _, _, hmap⟩ := hbind
  have hpt : (TranscriptProvenance.gatePointColumn e vc p).length = s0.eq.numVars := by
    rw [← hmap, List.length_map, hsteps]
  rw [hpt]
  have hshape := hcons.1.2.2.2.2
  have hcolm : (s0.constants.map DenseMleIndexed.State.evaluations).get? j = some col := hcol
  rw [ConstantsProvenance.get_map] at hcolm
  cases hst : s0.constants.get? j with
  | none => rw [hst] at hcolm; exact absurd hcolm (by simp)
  | some st =>
      rw [hst] at hcolm
      simp only [Option.map_some', Option.some.injEq] at hcolm
      have hmem : st ∈ s0.constants := List.get?_mem hst
      obtain ⟨hvalid, hnv⟩ := hshape st hmem
      rw [← hcolm, hvalid, hnv]

/-! ### 4b. The composed theorems -/

/-- **THE COMPOSED ATTACK THEOREM.  A COLUMN forgery outside the gate-point bad
set must break one of exactly three things.**

This is the adopted `ConstantsProvenance.partial_zeroing_forces_one_of_three`
with its FOLD-level hypothesis `hdiff` — "the two bound cells at the derived
gate point differ" — REPLACED by the bad-set condition

* `hpoint`, the verifier's own derived gate point is NOT in
  `columnAgreementSet`, the set §2 proves is the vanishing set of the difference
  column and §3 bounds by the adopted `ChallengeUnionBound.tauTerm degreeBits`,

together with ONE width hypothesis, `hcolWidth`, on the SUPPLIED column (and see
`column_forgery_forces_one_of_three_off_bad_set_of_consistent`, which derives even
that from the adopted `Consistent`).

NOT hypotheses, and deliberately absent from the statement:

* `col ≠ committedCol` — it FOLLOWS from `hpoint`, by
  `columns_differ_of_point_off_agreement`;
* the committed column's width — it is DERIVED inside branch (B) by
  `committed_width_of_opens`, from the opening relation that branch asserts.
  The proof is therefore by contradiction: assuming all three branches fail
  hands us `OpensCommittedTable`, from which the missing width follows.

Conclusion, unchanged from the adopted theorem: at least one of

* (C) `p.preprocessedRoot ≠ pin.preprocessedRoot` — killed by the deployment pin
  (`ConstantsProvenance.wrong_root_never_accepted`);
* (A) `¬ GateTerminalBinding.CellsMatchClaims` — the extraction join rejects;
* (B) `¬ OpeningBinding.OpensCommittedTable` — the preprocessed root is opened to
  different cells at bound cell `3`.

NOTHING MORE IS CLAIMED: this is not a probability statement about any run, and
residues R1/R2/R3 of the adopted `OpeningBinding` still sit inside branches (A)
and (B). -/
theorem column_forgery_forces_one_of_three_off_bad_set (e : Verifier.Engine)
    (pin : Verifier.Pinned) (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (hcolWidth : col.length = 2 ^ (TranscriptProvenance.gatePointColumn e vc p).length)
    (hpoint : ZeroCheckSemantics.tupleOf (TranscriptProvenance.gatePointColumn e vc p)
      ∉ columnAgreementSet (TranscriptProvenance.gatePointColumn e vc p).length col committedCol) :
    p.preprocessedRoot ≠ pin.preprocessedRoot ∨
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hroot, hk, hyp⟩ := hcon
  have hmem : committedCol ∈ cols 3 := by
    rw [hcols, hroot]
    exact List.get?_mem hcc
  have hccWidth := committed_width_of_opens e vc p cols committedCol hyp hmem
  rcases ConstantsProvenance.partial_zeroing_forces_one_of_three e pin vc p s0 k cols committedBy j
    col committedCol hj hbind hcols hcol hcc
    (bound_cells_differ_of_point_off_agreement col committedCol
      (TranscriptProvenance.gatePointColumn e vc p) hcolWidth hccWidth hpoint) with h | h | h
  · exact h hroot
  · exact h hk
  · exact h hyp

/-- `column_forgery_forces_one_of_three_off_bad_set` with the SUPPLIED column's
width replaced by the adopted `GateDenseRound.Consistent` — adopted field 2 of
`GateDerivedRejection.DerivedGateAssumptions` — so that NEITHER width is a
hypothesis of this statement.  See `supplied_width_of_consistent`. -/
theorem column_forgery_forces_one_of_three_off_bad_set_of_consistent (e : Verifier.Engine)
    (pin : Verifier.Pinned) (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (hpoint : ZeroCheckSemantics.tupleOf (TranscriptProvenance.gatePointColumn e vc p)
      ∉ columnAgreementSet (TranscriptProvenance.gatePointColumn e vc p).length col committedCol) :
    p.preprocessedRoot ≠ pin.preprocessedRoot ∨
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols :=
  column_forgery_forces_one_of_three_off_bad_set e pin vc p s0 k cols committedBy j col committedCol
    hj hbind hcols hcol hcc
    (supplied_width_of_consistent e vc p s0 k j col hcons hbind hcol) hpoint

/-- **THE COMPOSED ATTACK THEOREM UNDER ACCEPTANCE.**  Branch (C) is closed by
the deployment pin, so an ACCEPTED proof whose constants column is invisible-free
at a derived gate point outside the density-`≤ degreeBits / |F|` agreement set
must break the extraction join or the opening relation.

The supplied width is stated at `2 ^ vc.degreeBits` and the bad set at
`vc.degreeBits`: the gate point's width is DERIVED from acceptance by
`accepted_gate_point_width`, not assumed.  As above, the COMMITTED column's width
is not a hypothesis (branch (B) forces it) and neither is `col ≠ committedCol`
(`hpoint` forces it). -/
theorem accepted_column_forgery_forces_join_or_opening_off_bad_set (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (hcolWidth : col.length = 2 ^ vc.degreeBits)
    (hpoint : ¬ PointAgrees col committedCol (TranscriptProvenance.gatePointColumn e vc p)) :
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  have hwidth := accepted_gate_point_width e decode pin chain vc p hacc
  have hmem : ZeroCheckSemantics.tupleOf (TranscriptProvenance.gatePointColumn e vc p)
      ∉ columnAgreementSet (TranscriptProvenance.gatePointColumn e vc p).length col committedCol := by
    intro hin
    exact hpoint ((mem_columnAgreementSet_tupleOf col committedCol _).mp hin)
  rcases column_forgery_forces_one_of_three_off_bad_set e pin vc p s0 k cols committedBy j col
    committedCol hj hbind hcols hcol hcc (by rw [hwidth]; exact hcolWidth) hmem with h | h | h
  · exact absurd (ConstantsProvenance.accepted_root_is_pinned e decode pin chain vc p hacc) h
  · exact Or.inl h
  · exact Or.inr h

/-- The acceptance form with the supplied width replaced by the adopted
`GateDenseRound.Consistent`: no width hypothesis at all. -/
theorem accepted_column_forgery_forces_join_or_opening_off_bad_set_of_consistent
    (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (hpoint : ¬ PointAgrees col committedCol (TranscriptProvenance.gatePointColumn e vc p)) :
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  refine accepted_column_forgery_forces_join_or_opening_off_bad_set e decode pin chain vc p s0 k
    cols committedBy j col committedCol hj hacc hbind hcols hcol hcc ?_ hpoint
  have hw := supplied_width_of_consistent e vc p s0 k j col hcons hbind hcol
  rw [accepted_gate_point_width e decode pin chain vc p hacc] at hw
  exact hw

/-- The acceptance theorem's `hpoint`, in the bad-set form of deliverable 3: a
tuple of the derived width whose coordinates are the gate point's entries and
which lies outside the agreement set. -/
theorem accepted_column_forgery_forces_join_or_opening_off_bad_set_tuple (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (hcolWidth : col.length = 2 ^ vc.degreeBits)
    (t : ZeroCheckSemantics.Tuple vc.degreeBits)
    (hget : ∀ i : Fin vc.degreeBits,
      ∀ h : i.val < (TranscriptProvenance.gatePointColumn e vc p).length,
        (TranscriptProvenance.gatePointColumn e vc p).get ⟨i.val, h⟩ = t i)
    (hpoint : t ∉ columnAgreementSet vc.degreeBits col committedCol) :
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  refine accepted_column_forgery_forces_join_or_opening_off_bad_set e decode pin chain vc p s0 k
    cols committedBy j col committedCol hj hacc hbind hcols hcol hcc hcolWidth ?_
  exact not_agrees_of_not_mem vc.degreeBits col committedCol _
    (accepted_gate_point_width e decode pin chain vc p hacc) t hget hpoint

/-- The tuple form with the supplied width replaced by the adopted
`GateDenseRound.Consistent`. -/
theorem accepted_column_forgery_forces_join_or_opening_off_bad_set_tuple_of_consistent
    (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (vc : Verifier.Config) (p : Verifier.Proof)
    (s0 : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsProvenance.ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (t : ZeroCheckSemantics.Tuple vc.degreeBits)
    (hget : ∀ i : Fin vc.degreeBits,
      ∀ h : i.val < (TranscriptProvenance.gatePointColumn e vc p).length,
        (TranscriptProvenance.gatePointColumn e vc p).get ⟨i.val, h⟩ = t i)
    (hpoint : t ∉ columnAgreementSet vc.degreeBits col committedCol) :
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  refine accepted_column_forgery_forces_join_or_opening_off_bad_set_tuple e decode pin chain vc p
    s0 k cols committedBy j col committedCol hj hacc hbind hcols hcol hcc ?_ t hget hpoint
  have hw := supplied_width_of_consistent e vc p s0 k j col hcons hbind hcol
  rw [accepted_gate_point_width e decode pin chain vc p hacc] at hw
  exact hw

/-! ## 5. THE GATE POINT IS THE `outerGate` BLOCK OF THE ADOPTED JOINT SPACE

Deliverable 4 of this module's brief asks whether the gate point coordinates
really are the adopted `JointChallengeSpace.Draw.outerGate` draws.  They are, and
§5a proves it rather than assuming it. -/

/-! ### 5a. The gate point column IS the gate lane's round-challenge list -/

/-- Every coupled round appends its GATE challenge to `gatePoint`
(`Verifier.roundStep`), and the adopted `ConditionalSoundness.lane` records the
same challenge in its `LaneRound.challenge` field.  So the lifted gate point of
a run of rounds is the starting gate point followed by the lane's challenges. -/
theorem liftList_runRounds_gatePoint (commit : Verifier.CommitRound)
    (sel : Verifier.CoupledMessage → List Verifier.Ext3) :
    ∀ (ms : List Verifier.CoupledMessage) (truths : List (List Element))
      (s : Verifier.RoundState),
      TranscriptProvenance.liftList (Verifier.runRounds commit s ms).gatePoint
        = TranscriptProvenance.liftList s.gatePoint
          ++ (ConditionalSoundness.lane commit sel Verifier.RoundChallenges.gate truths s ms).map
              ConditionalSoundness.LaneRound.challenge
  | [], _truths, s => by
      simp only [Verifier.runRounds, ConditionalSoundness.lane, List.map_nil, List.append_nil]
  | m :: ms, truths, s => by
      show TranscriptProvenance.liftList
          (Verifier.runRounds commit (Verifier.roundStep commit s m) ms).gatePoint = _
      rw [liftList_runRounds_gatePoint commit sel ms truths.tail (Verifier.roundStep commit s m)]
      show (TranscriptProvenance.liftList
          (s.gatePoint ++ [(commit s.transcript s.roundIndex m.1 m.2).gate])) ++ _ = _
      simp only [TranscriptProvenance.liftList, ConditionalSoundness.lane, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- **(4) THE GATE POINT COLUMN IS THE GATE LANE'S CHALLENGE LIST.**  Proved,
not assumed: `TranscriptProvenance.gatePointColumn e c p` is exactly the list of
per-coupled-round GATE challenges recorded by the adopted
`ConditionalSoundness.gateLaneOf`.  Those are the draws the adopted
`JointChallengeSpace.Draw.outerGate` indexes, so §5b's pullback is over the
right block.

CAVEAT, INHERITED VERBATIM from the adopted `JointChallengeSpace` header: that
each such challenge is squeezed at counter `3` of its round's commit digest is
DOCUMENTED against `OuterChallenge.coupled_success_uses_same_committed_digest_and_six_counters`,
not derived for the abstract `Verifier.Engine` quantified over here. -/
theorem gate_point_column_is_the_gate_lane_challenges (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element)) :
    TranscriptProvenance.gatePointColumn e c p
      = (ConditionalSoundness.gateLaneOf e c p truths).map
          ConditionalSoundness.LaneRound.challenge := by
  have h := liftList_runRounds_gatePoint e.commitRound Prod.snd (p.logRounds.zip p.gateRounds)
    truths (Verifier.start (e.initialTranscript c p))
  show TranscriptProvenance.liftList (Verifier.derivedRounds e c p).gatePoint = _
  show TranscriptProvenance.liftList
      (Verifier.runRounds e.commitRound (Verifier.start (e.initialTranscript c p))
        (p.logRounds.zip p.gateRounds)).gatePoint = _
  rw [h]
  rfl

/-- The gate LANE's length is not independent information: §5a identifies the
gate point column with the lane's challenge list, so the point's width already
pins the lane's.  This is why `gate_point_off_agreement_of_joint` below carries
no separate `hlane` hypothesis. -/
theorem gate_lane_length_of_gate_point_width (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element))
    (hwidth : (TranscriptProvenance.gatePointColumn e c p).length = c.degreeBits) :
    (ConditionalSoundness.gateLaneOf e c p truths).length = c.degreeBits := by
  rw [gate_point_column_is_the_gate_lane_challenges e c p truths, List.length_map] at hwidth
  exact hwidth

/-! ### 5b. The agreement set as a FOURTH family on the adopted `JointSpace` -/

/-- The `degreeBits` coupled-round GATE coordinates of a joint point, reduced.
The exact analogue of the adopted `JointChallengeSpace.tauReduction` on the
`outerGate` block. -/
def gateReduction (d : Nat) (w : JointChallengeSpace.JointSpace d) :
    ZeroCheckSemantics.Tuple d :=
  fun i => OuterChallenge.reduceTriple (w (JointChallengeSpace.Draw.outerGate i))

/-- MULTI-COORDINATE PULLBACK to the `outerGate` block: the joint points whose
gate point lands in a set of tuples. -/
def gatePointEvent (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d)) :
    Finset (JointChallengeSpace.JointSpace d) :=
  Finset.univ.filter (fun w => gateReduction d w ∈ S)

theorem mem_gatePointEvent (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d))
    (w : JointChallengeSpace.JointSpace d) :
    w ∈ gatePointEvent d S ↔ gateReduction d w ∈ S := by
  simp only [gatePointEvent, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The joint space splits as (`outerGate` block) x (everything else).  The
complement block — gate alpha, the gate tau column, the log-lane round
challenges — has the same SHAPE as the adopted `JointChallengeSpace.TauRest`,
so that module's cardinality lemmas are reused verbatim. -/
def gateSplit (d : Nat) :
    JointChallengeSpace.JointSpace d ≃
      ChallengeUnionBound.TripleTuple d ×
        (JointChallengeSpace.TauRest d → OuterChallenge.DigestTriple) where
  toFun w :=
    (fun i => w (JointChallengeSpace.Draw.outerGate i),
     fun jj => match jj with
       | Sum.inl _ => w JointChallengeSpace.Draw.gateAlpha
       | Sum.inr (Sum.inl i) => w (JointChallengeSpace.Draw.gateTau i)
       | Sum.inr (Sum.inr r) => w (JointChallengeSpace.Draw.outerLog r))
  invFun q := fun k => match k with
    | JointChallengeSpace.Draw.gateAlpha => q.2 (Sum.inl ())
    | JointChallengeSpace.Draw.gateTau i => q.2 (Sum.inr (Sum.inl i))
    | JointChallengeSpace.Draw.outerLog r => q.2 (Sum.inr (Sum.inr r))
    | JointChallengeSpace.Draw.outerGate r => q.1 r
  left_inv w := by funext k; cases k <;> rfl
  right_inv q := by
    obtain ⟨t, r⟩ := q
    refine Prod.ext ?_ ?_
    · funext i; rfl
    · funext jj; rcases jj with _ | i | i <;> rfl

theorem gatePointEvent_card (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d)) :
    (gatePointEvent d S).card
      = (ChallengeUnionBound.productEvent d S).card
        * (OuterChallenge.wordSize ^ 3) ^ (2 * d + 1) := by
  classical
  have hmap : gatePointEvent d S
      = ((ChallengeUnionBound.productEvent d S) ×ˢ
          (Finset.univ : Finset (JointChallengeSpace.TauRest d → OuterChallenge.DigestTriple))).map
            (gateSplit d).symm.toEmbedding := by
    ext w
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_gatePointEvent,
      ChallengeUnionBound.mem_productEvent]
    exact Iff.rfl
  rw [hmap, Finset.card_map, Finset.card_product, Finset.card_univ,
    JointChallengeSpace.tau_rest_fun_card]

/-- **(4) THE PROJECTION FACT, the gate-point block.**  The mass of the pullback
under the adopted JOINT uniform law EQUALS the adopted product mass on
`TripleTuple degreeBits` — the same cylinder split the adopted
`JointChallengeSpace.tau_event_mass` performs, on the other block. -/
theorem gate_point_event_mass (d : Nat) (S : Finset (ZeroCheckSemantics.Tuple d)) :
    JointChallengeSpace.jointProbability d (gatePointEvent d S)
      = ChallengeUnionBound.uniformProductProbability d S := by
  unfold JointChallengeSpace.jointProbability ChallengeUnionBound.uniformProductProbability
  rw [gatePointEvent_card, JointChallengeSpace.joint_space_card,
    ChallengeUnionBound.product_space_card]
  push_cast
  rw [show 3 * d + 1 = (2 * d + 1) + d by omega,
    pow_add ((OuterChallenge.wordSize : ℚ) ^ 3) (2 * d + 1) d]
  exact JointChallengeSpace.cylinder_quotient
    ((ChallengeUnionBound.productEvent d S).card : ℚ)
    ((OuterChallenge.wordSize : ℚ) ^ 3) (2 * d + 1) d
    JointChallengeSpace.word_size_cube_cast_ne_zero

/-- THE FOURTH PULLBACK: the gate-point agreement set of a forged constants
column, on the `outerGate` coordinates of the ONE adopted joint space. -/
def agreementBadEvent (d : Nat) (col committedCol : List Element) :
    Finset (JointChallengeSpace.JointSpace d) :=
  gatePointEvent d (columnAgreementSet d col committedCol)

/-- **(4) THE FOURTH FAMILY'S JOINT MASS.**  Equal to the product mass, hence
bounded by the adopted `ChallengeUnionBound.tauTerm degreeBits` — the same
closed form the adopted `JointChallengeSpace.tau_bad_event_mass_le` gets for the
tau block. -/
theorem gate_point_agreement_joint_mass_bound (d : Nat) (col committedCol : List Element)
    (h : ColumnsDifferOnCube d col committedCol) :
    JointChallengeSpace.jointProbability d (agreementBadEvent d col committedCol)
      ≤ ChallengeUnionBound.tauTerm d := by
  rw [agreementBadEvent, gate_point_event_mass]
  exact gate_point_agreement_mass_bound d col committedCol h

/-! ### 5c. Transport: a good joint draw puts the run's gate point off the set -/

/-- The adopted `JointChallengeSpace.DrawnAt`, read coordinatewise — the
converse of the adopted `drawnAt_of_pointwise`. -/
theorem challenge_of_drawnAt (d : Nat) (w : JointChallengeSpace.JointSpace d)
    (proj : Nat → JointChallengeSpace.Draw d) :
    ∀ (rs : List ConditionalSoundness.LaneRound) (k j : Nat) (hj : j < rs.length),
      JointChallengeSpace.DrawnAt d w proj rs k →
      (rs.get ⟨j, hj⟩).challenge = OuterChallenge.reduceTriple (w (proj (k + j)))
  | [], _, _, hj, _ => absurd hj (by simp)
  | _ :: _, k, 0, _, h => by simpa using h.1
  | _ :: rs, k, j + 1, hj, h => by
      have hrec := challenge_of_drawnAt d w proj rs (k + 1) j
        (by simpa using Nat.lt_of_succ_lt_succ hj) h.2
      rw [show k + (j + 1) = k + 1 + j by omega]
      simpa using hrec

/-- **(4) THE GATE POINT'S COORDINATES ARE THE `outerGate` DRAWS.**  Combining
§5a with the adopted `DrawnAt` on the gate lane: entry `i` of the run's gate
point column is the reduction of joint coordinate `Draw.outerGate i`.  This is
the hypothesis shape the adopted `JointChallengeSpace.good_derived_tau_of_joint`
uses for the tau block. -/
theorem gate_point_coordinates_are_outerGate_draws (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element))
    (w : JointChallengeSpace.JointSpace c.degreeBits)
    (hlane : (ConditionalSoundness.gateLaneOf e c p truths).length = c.degreeBits)
    (hdrawn : JointChallengeSpace.DrawnAt c.degreeBits w
      (JointChallengeSpace.gateProj c.degreeBits)
      (ConditionalSoundness.gateLaneOf e c p truths) 0) :
    ∀ i : Fin c.degreeBits, ∀ h : i.val < (TranscriptProvenance.gatePointColumn e c p).length,
      (TranscriptProvenance.gatePointColumn e c p).get ⟨i.val, h⟩
        = OuterChallenge.reduceTriple (w (JointChallengeSpace.Draw.outerGate i)) := by
  intro i h
  have hcol := gate_point_column_is_the_gate_lane_challenges e c p truths
  have hi : i.val < (ConditionalSoundness.gateLaneOf e c p truths).length := by
    rw [hlane]; exact i.isLt
  have hlane' := challenge_of_drawnAt c.degreeBits w (JointChallengeSpace.gateProj c.degreeBits)
    (ConditionalSoundness.gateLaneOf e c p truths) 0 i.val hi hdrawn
  rw [Nat.zero_add, JointChallengeSpace.gateProj_apply c.degreeBits i.val i.isLt] at hlane'
  have hget : (TranscriptProvenance.gatePointColumn e c p).get? i.val
      = some ((ConditionalSoundness.gateLaneOf e c p truths).get ⟨i.val, hi⟩).challenge := by
    rw [hcol, ConstantsProvenance.get_map, List.get?_eq_get hi]
    rfl
  rw [List.get?_eq_get h] at hget
  rw [Option.some.inj hget, hlane']

/-- **(4) THE COMPOSED TRANSPORT.**  A joint draw outside the fourth family's
pullback, whose `outerGate` coordinates carry the run's own gate challenges,
gives exactly the `hpoint` the composed attack theorem of §4 consumes.

No `hlane` hypothesis: the lane's length follows from the point's width, by
`gate_lane_length_of_gate_point_width`. -/
theorem gate_point_off_agreement_of_joint (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (truths : List (List Element)) (col committedCol : List Element)
    (w : JointChallengeSpace.JointSpace c.degreeBits)
    (hwidth : (TranscriptProvenance.gatePointColumn e c p).length = c.degreeBits)
    (hdrawn : JointChallengeSpace.DrawnAt c.degreeBits w
      (JointChallengeSpace.gateProj c.degreeBits)
      (ConditionalSoundness.gateLaneOf e c p truths) 0)
    (hgood : w ∉ agreementBadEvent c.degreeBits col committedCol) :
    ¬ PointAgrees col committedCol (TranscriptProvenance.gatePointColumn e c p) := by
  have hnot : gateReduction c.degreeBits w
      ∉ columnAgreementSet c.degreeBits col committedCol := by
    intro hmem
    refine hgood ?_
    rw [agreementBadEvent, mem_gatePointEvent]
    exact hmem
  exact not_agrees_of_not_mem c.degreeBits col committedCol
    (TranscriptProvenance.gatePointColumn e c p) hwidth (gateReduction c.degreeBits w)
    (gate_point_coordinates_are_outerGate_draws e c p truths w
      (gate_lane_length_of_gate_point_width e c p truths hwidth) hdrawn) hnot

/-! ## 6. DEGENERACY NOTES

Two ways the composed theorems say nothing.  Both are recorded because the
statement's strength should not be over-read. -/

/-- **VACUITY AT `col = committedCol`.**  If the supplied column IS the committed
column, the agreement set is ALL of `Finset.univ`.  Nothing is ever `decide`d
here: the membership predicate reduces to `x = x`. -/
theorem agreement_set_of_equal_columns (n : Nat) (col : List Element) :
    columnAgreementSet n col col = Finset.univ := by
  apply Finset.ext
  intro r
  simp only [mem_columnAgreementSet, Finset.mem_univ, iff_true, PointAgrees]

/-- Consequently `hpoint` is UNSATISFIABLE at equal columns: the composed
theorems of §4 are vacuously true there, not evidence about equal columns. -/
theorem no_point_off_agreement_at_equal_columns (n : Nat) (col : List Element)
    (t : ZeroCheckSemantics.Tuple n) : t ∈ columnAgreementSet n col col := by
  rw [agreement_set_of_equal_columns]
  exact Finset.mem_univ t

/-- **DEGENERACY AT `degreeBits = 0`.**  The adopted `ChallengeUnionBound.tauTerm`
carries the variable count as a leading factor, so at zero variables the bound is
`0` and §3's mass statement forces the agreement set to have mass zero.  That is
consistent, not contradictory: with an empty point a column of width `2 ^ 0 = 1`
is a single cell, `ColumnsDifferOnCube 0` says the two cells differ, and the fold
IS that cell — so the agreement set really is empty and there is no
Schwartz--Zippel content at all.  `Fintype.card Element` is not evaluated. -/
theorem tauTerm_zero : ChallengeUnionBound.tauTerm 0 = 0 := by
  rw [ChallengeUnionBound.tauTerm]
  simp only [Nat.cast_zero, zero_mul]

/-! ## 7. THE ADOPTED RESIDUE WITNESS, AT ONE VARIABLE

The adopted `ConstantsProvenance.bound_cell_agreement_is_not_column_equality`
exhibits `[5, 3]` and `[9, 3]`, which agree at the point `[1]`.  In the language
of this module: the agreement set of those two columns in ONE variable is
`{r : 5(1-r) + 3r = 9(1-r) + 3r} = {1}`.  Nothing is ever `decide`d about a
`Finset` over a tuple space: membership is reduced to the arithmetic FIRST, and
only then evaluated on the adopted small `Element` literals. -/

namespace Example

/-- The adopted residue columns. -/
def columnA : List Element := ConstantsProvenance.residueColumnA
def columnB : List Element := ConstantsProvenance.residueColumnB

theorem widthA : columnA.length = 2 ^ ([1] : List Element).length := rfl
theorem widthB : columnB.length = 2 ^ ([1] : List Element).length := rfl
theorem widthA_zero : columnA.length = 2 ^ ([0] : List Element).length := rfl
theorem widthB_zero : columnB.length = 2 ^ ([0] : List Element).length := rfl

theorem columns_differ : columnA ≠ columnB := ConstantsProvenance.residue_columns_differ

/-- The columns differ on the one-variable cube: at index `0`, `5 ≠ 9`. -/
theorem columns_differ_on_cube : ColumnsDifferOnCube 1 columnA columnB :=
  columnsDifferOnCube_of_ne 1 columnA columnB rfl rfl columns_differ

/-- `r = 1` IS in the agreement set: this is the adopted
`residue_columns_share_bound_cell` read through the bridge of §1. -/
theorem one_mem_agreement :
    (fun _ : Fin 1 => (1 : Element)) ∈ columnAgreementSet 1 columnA columnB := by
  rw [mem_columnAgreementSet]
  show ZeroCheckSemantics.extension columnA (List.ofFn (fun _ : Fin 1 => (1 : Element)))
    = ZeroCheckSemantics.extension columnB (List.ofFn (fun _ : Fin 1 => (1 : Element)))
  have hofn : List.ofFn (fun _ : Fin 1 => (1 : Element)) = [1] := by simp
  rw [hofn, ← cell_bindColumn_eq_extension_of_width [1] columnA widthA,
    ← cell_bindColumn_eq_extension_of_width [1] columnB widthB]
  exact congrArg NormTerminalBinding.cell ConstantsProvenance.residue_columns_share_bound_cell

/-- `r = 0` is NOT: there the folds are `5` and `9`. -/
theorem zero_not_mem_agreement :
    (fun _ : Fin 1 => (0 : Element)) ∉ columnAgreementSet 1 columnA columnB := by
  rw [mem_columnAgreementSet]
  show ¬ (ZeroCheckSemantics.extension columnA (List.ofFn (fun _ : Fin 1 => (0 : Element)))
    = ZeroCheckSemantics.extension columnB (List.ofFn (fun _ : Fin 1 => (0 : Element))))
  have hofn : List.ofFn (fun _ : Fin 1 => (0 : Element)) = [0] := by simp
  rw [hofn, ← cell_bindColumn_eq_extension_of_width [0] columnA widthA_zero,
    ← cell_bindColumn_eq_extension_of_width [0] columnB widthB_zero]
  decide

/-- The mass bound at this witness: the adopted `tauTerm 1`. -/
theorem example_mass_bound :
    ChallengeUnionBound.uniformProductProbability 1 (columnAgreementSet 1 columnA columnB)
      ≤ ChallengeUnionBound.tauTerm 1 :=
  gate_point_agreement_mass_bound 1 columnA columnB columns_differ_on_cube

/-- The same on the adopted joint space, at `degreeBits = 1`. -/
theorem example_joint_mass_bound :
    JointChallengeSpace.jointProbability 1 (agreementBadEvent 1 columnA columnB)
      ≤ ChallengeUnionBound.tauTerm 1 :=
  gate_point_agreement_joint_mass_bound 1 columnA columnB columns_differ_on_cube

end Example

end Audit.Wire3.GatePointZeroCheck
