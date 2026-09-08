import Audit.Wire3.GateClaimChain
import Audit.Wire3.ZeroCheckSemantics

/-!
# Giving the GATE lane's cube-sum conclusion rejection power

The adopted `Audit.Wire3.GateClaimChain.accepted_gate_cube_sum_vanishes` proves,
for an accepting `Integrated.verify` run under eight named assumptions and a
`BadEventFree` hypothesis, that

  `GateDenseRound.cubeSum … s0.tables (2 ^ s0.eq.numVars) = 0`,

i.e. the SUPPLIED eq column, used as a row weight, kills the SUPPLIED gate
aggregate over the whole Boolean cube.  That module's own header records that
this statement HAS NO REJECTION POWER: assumption 8 (`eqCell`) pins exactly one
linear functional of the eq column (the fully bound cell) while the conclusion
sums a DIFFERENT linear functional of the same column, so a supplier free to
choose `s0` can zero the conclusion without touching the witness.

This module does three things and claims nothing beyond them.

1. IT ENUMERATES THE DEGENERACIES AS THEOREMS, not as prose.  Section 1 gives
   four named scenarios and, for each, a proof that it is REAL — that the
   adopted conclusion holds while the supplied tables carry a nonzero gate
   aggregate, or holds for any tables whatsoever.

2. IT PROVES THE PARTITION OF UNITY for the adopted eq table (section 2):
   `Σ_{i < 2^|tau|} EqTableProvenance.rowProdFrom 0 tau i = 1` for EVERY `tau`.
   Consequently an eq column with the adopted full-table provenance
   (`EqTableProvenance.GateEqProvenance`) has row sum `1`, never `0`, and the
   zero-eq-column and zero-row-sum forgeries of section 1 become IMPOSSIBLE.

3. IT STRENGTHENS THE ASSUMPTION SET (section 3) by ADDING the adopted
   `GateEqProvenance` field, composes the adopted conclusion with the adopted
   `ZeroCheckSemantics.gate_rows_vanish`, and obtains `∀ i < 2^|tau|,
   gateValue … i = 0` — every row's gate aggregate, not merely a weighted sum.
   Section 4 states the rejection-power theorem in contrapositive form and
   exhibits a concrete supplied state that the strengthened assumptions REJECT
   and the adopted ones ACCEPT.

## Exactly what is added to the adopted assumption set

`StrongAssumptions` CONTAINS the adopted `GateClaimChain.Assumptions` as its
field `base` and ADDS two visible fields.  It is therefore STRICTLY STRONGER
than the adopted set, which is all the rejection-power argument needs.  It is
NOT a "replacement" of assumption 8: making `eqCell` derivable from
`GateEqProvenance` needs, in addition, the identification of this module's
`tau` with `(e.initialTranscript vc p).gateTau` and of the binding steps with
`(Verifier.derivedRounds e vc p).gatePoint`, through the adopted
`EqTableProvenance.bound_gate_eq_cell`.  That bridge is NOT built here and no
theorem below pretends it is; see `## What is NOT proved`.

## What is NOT proved

* THE SELECTOR DEGENERACY SURVIVES THE STRENGTHENING, and this is proved, not
  conceded in prose: `selector_forgery_survives_eq_provenance` exhibits a
  validated, constraint-POSITIVE configuration and a state whose eq column IS a
  genuine `eqTable`, whose every row's gate aggregate is `0`, and whose cube sum
  is `0` — because every selector filter is `0`.  The strengthened conclusion is
  TRUE there and detects nothing.  SCOPE: the state exhibited by that theorem has
  EVERY filter zero, so `activeFilter` does exclude that particular witness.  The
  residual attack is PARTIAL selector zeroing — zeroing the filters on the rows
  that matter while leaving some gate active elsewhere — which satisfies
  `activeFilter` and is NOT exhibited here.  Excluding it is a
  CONSTANTS-PROVENANCE obligation (the constants columns must be the committed
  preprocessed columns), part of the open extraction join rather than of the
  eq-table story.  Like the adopted field 4 (`gateConstraintsPositive`),
  `activeFilter` is a guard and NOT sufficient.
* `tau` IS NOT TIED TO THE TRANSCRIPT.  Throughout this module `tau` is a free
  universally quantified variable, never identified with
  `(e.initialTranscript vc p).gateTau`.  So an adversary choosing `tau` AFTER
  fixing the tables is excluded only by the `hgood` hypothesis, not by anything
  proved here.  Do not read `tau` as "the drawn challenge".
* THE eqCell REPLACEMENT BRIDGE, as above.
* FROM ROW AGGREGATES TO INDIVIDUAL GATE CONSTRAINTS.  `gateValue = 0` at every
  row says the alpha-Horner COMBINATION of the row's gate constraints is zero.
  Concluding that each individual constraint is zero needs a SECOND zero check,
  over the aggregation randomness `alpha` (a separate module); nothing here
  performs it.
* THE EXTRACTION JOIN remains open exactly as in the adopted module: nothing
  connects the WHIR/Merkle-bound values to the cells of the extracted tables
  (adopted assumption 6).
* NO PROBABILITY.  `hgood` (the SUPPLIED `tau` avoids
  `ZeroCheckSemantics.zeroCheckBadSet`) is a hypothesis about the run, not an
  event with a computed mass.  The adopted `zeroCheckBadSet_density_bound` is an
  ideal-law counting statement over `(Element)^n` and is NEVER composed with
  `hgood` here.  The adaptivity obligation of `ZeroCheckSemantics` (the tables
  must be fixed before the gate-tau block) is likewise untouched.
* `StrongAssumptions` IS NOT SHOWN TO BE INHABITED, since the adopted
  `Assumptions` is not.  The rejection-power theorems are therefore conditional
  in the same way the adopted theorem is; what changes is that the CONCLUSION
  now has content, not that the hypotheses are discharged.
* No Rust/Solidity refinement, gas, WHIR profile or transcript claim.

Tactic note: `simp`/`ring`/`norm_num` must never see `Fintype.card Element`.
Nothing below mentions it.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Audit.Wire3.GateRejectionPower

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.EqTableProvenance Audit.Wire3.ZeroCheckSemantics
open Audit.Wire3.GateSuffixPolynomial Audit.Wire3.GateDenseRound
open Audit.Wire3.GateTerminalBinding (ProverState Cells publicHashFunction)

/-! ## 0. The eq column as a free parameter

Everything in section 1 rests on one structural fact: the eq column enters the
adopted `cubeSum` LINEARLY, and it enters the gate aggregate NOT AT ALL.  A
supplier who swaps the eq column changes the conclusion and leaves the witness
untouched. -/

/-- The tables with the eq column replaced.  The wire and constant columns —
i.e. the whole witness — are untouched. -/
def withEq (t : Tables) (column : List Element) : Tables :=
  ⟨t.wires, t.constants, column⟩

/-- SWAPPING THE EQ COLUMN DOES NOT TOUCH THE GATE AGGREGATE.  This is the
precise sense in which the eq column is free: it is not an input of
`GatesComplete.evalCombined`. -/
theorem gate_value_ignores_eq (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (column : List Element)
    (index : Nat) :
    gateValue c gates publicHash alpha (withEq t column) index
      = gateValue c gates publicHash alpha t index := rfl

/-- The row sum of the eq column over the cube, the functional the adopted
provenance does NOT pin and the partition of unity DOES. -/
def eqRowSum (t : Tables) (count : Nat) : Element :=
  ((List.range count).map (fun i => t.eq.getD i 0)).sum

/-- THE ADOPTED CUBE SUM IS A LINEAR FUNCTIONAL OF THE EQ COLUMN, with the gate
aggregate supplying the coefficients.  Immediate from the adopted
`ZeroCheckSemantics.rowElement_is_eq_times_gate`; stated because every scenario
below is an instance of it. -/
theorem cube_sum_is_eq_functional (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (count : Nat) :
    cubeSum c gates publicHash alpha t count
      = ((List.range count).map
          (fun i => t.eq.getD i 0 * gateValue c gates publicHash alpha t i)).sum := by
  unfold cubeSum
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i _
  exact rowElement_is_eq_times_gate c gates publicHash alpha t i

theorem replicate_zero_getD : ∀ (n i : Nat), (List.replicate n (0 : Element)).getD i 0 = 0
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, i + 1 => replicate_zero_getD n i

/-! ## 1. The scenario inventory

Four named degeneracies of the adopted conclusion, each with a theorem proving
it is REAL.  "Real" means: the adopted conclusion `cubeSum = 0` holds while the
supplied tables carry a gate aggregate that is not identically zero, or holds
for any tables at all. -/

/-! ### Scenario 1: the zero eq column (and, more generally, a zero row sum) -/

/-- SCENARIO 1a.  The supplied eq column is zero on the whole cube. -/
def ZeroEqColumn (t : Tables) (count : Nat) : Prop := ∀ i, i < count → t.eq.getD i 0 = 0

/-- SCENARIO 1b.  The supplied eq column sums to zero over the cube.  This is
the class the module header of `GateClaimChain` names; 1a is its extreme point,
and section 2 shows the whole class is excluded by the eq table's provenance. -/
def ZeroEqRowSum (t : Tables) (count : Nat) : Prop := eqRowSum t count = 0

theorem zero_eq_column_row_sum (t : Tables) (count : Nat) (h : ZeroEqColumn t count) :
    ZeroEqRowSum t count := by
  refine List.sum_eq_zero ?_
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  exact h i (List.mem_range.mp hi)

/-- SCENARIO 1 IS REAL, general form.  A zero eq column makes the adopted
conclusion true FOR ANY configuration, ANY decoded gates, ANY aggregation
challenge and ANY witness columns.  The conclusion therefore carries no
information about the witness. -/
theorem zero_eq_column_cube_sum_vanishes (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (count : Nat)
    (h : ZeroEqColumn t count) :
    cubeSum c gates publicHash alpha t count = 0 := by
  rw [cube_sum_is_eq_functional]
  refine List.sum_eq_zero ?_
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  rw [h i (List.mem_range.mp hi), zero_mul]

/-- SCENARIO 1 IS REAL, forgery form.  THE SHARP STATEMENT OF "NO REJECTION
POWER": from ANY tables at all, the supplier obtains tables with the SAME gate
aggregate at every row and a VANISHING cube sum, simply by presenting a zero eq
column.  Nothing about the witness is constrained by the adopted conclusion. -/
theorem zero_eq_forgery (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (count : Nat) :
    cubeSum c gates publicHash alpha (withEq t (List.replicate count 0)) count = 0 ∧
      ∀ index, gateValue c gates publicHash alpha (withEq t (List.replicate count 0)) index
        = gateValue c gates publicHash alpha t index := by
  refine ⟨zero_eq_column_cube_sum_vanishes c gates publicHash alpha _ count ?_, fun index => rfl⟩
  intro i _
  exact replicate_zero_getD count i

/-! ### Scenario 2: the constraint-free configuration (adopted, cited) -/

/-- SCENARIO 2 IS REAL — CITED, NOT RE-PROVED.  On a validated configuration
declaring `numGateConstraints = 0` the adopted
`GateClaimChain.constraint_free_cube_sum_vanishes` gives `cubeSum = 0` for ANY
tables.  The adopted `Assumptions` field 4 (`gateConstraintsPositive`) excludes
exactly this regime, and `StrongAssumptions` inherits that field through
`base`. -/
theorem constraint_free_scenario_is_real (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (count : Nat)
    (hv : Gates.validateConfiguration c gates = some ())
    (h0 : c.numGateConstraints = 0) :
    cubeSum c gates publicHash alpha t count = 0 :=
  GateClaimChain.constraint_free_cube_sum_vanishes c gates publicHash alpha t count hv h0

/-! ### Scenario 3: every selector filter zero -/

/-- The filter the adopted `GatesComplete.contribution` computes for gate `g` at
Boolean row `index`, read from the SUPPLIED constants columns.  This is a
verbatim unfolding of `contribution`'s own `let filter := …`. -/
def rowFilter (c : Gates.Config) (g : Gates.GateInfo) (t : Tables) (index : Nat) : Verifier.Ext3 :=
  Gates.computeFilter g
    (Gates.readValue (t.constants.map (fun column => (column.getD index 0).toVerifier))
      g.selectorIndex)
    (decide (1 < c.numSelectors))

/-- SCENARIO 3.  Every decoded gate's filter is zero at every Boolean row. -/
def AllFiltersZero (c : Gates.Config) (gates : List Gates.GateInfo) (t : Tables)
    (count : Nat) : Prop :=
  ∀ i, i < count → ∀ g ∈ gates, rowFilter c g t i = Verifier.zero

/-- The adopted `contribution` short-circuits on a zero filter. -/
theorem zero_filter_contribution (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (alpha : Verifier.Ext3)
    (h0 : Gates.computeFilter g (Gates.readValue constants g.selectorIndex)
      (decide (1 < c.numSelectors)) = Verifier.zero) :
    GatesComplete.contribution c g wires constants publicHash alpha = some Verifier.zero := by
  unfold GatesComplete.contribution
  dsimp only
  rw [if_pos h0]

theorem zero_filter_combine_rows (c : Gates.Config) (wires constants : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (alpha : Verifier.Ext3) :
    ∀ (gs : List Gates.GateInfo) (acc : Verifier.Ext3),
      (∀ g ∈ gs, Gates.computeFilter g (Gates.readValue constants g.selectorIndex)
        (decide (1 < c.numSelectors)) = Verifier.zero) →
      GatesComplete.combineRows c wires constants publicHash alpha gs acc = some acc
  | [], _, _ => rfl
  | g :: gs, acc, h0 => by
      unfold GatesComplete.combineRows
      rw [zero_filter_contribution c g wires constants publicHash alpha
        (h0 g (List.mem_cons_self _ _))]
      simp only [Option.bind_eq_bind, Option.some_bind]
      rw [Gates.add_zero]
      exact zero_filter_combine_rows c wires constants publicHash alpha gs acc
        (fun q hq => h0 q (List.mem_cons_of_mem _ hq))

theorem zero_filter_eval_combined (c : Gates.Config) (gates : List Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (alpha : Verifier.Ext3)
    (hw : wires.length = c.numWires) (hc : constants.length = c.numConstants)
    (hv : Gates.validateConfiguration c gates = some ())
    (h0 : ∀ g ∈ gates, Gates.computeFilter g (Gates.readValue constants g.selectorIndex)
      (decide (1 < c.numSelectors)) = Verifier.zero) :
    GatesComplete.evalCombined c gates wires constants publicHash alpha = some Verifier.zero := by
  unfold GatesComplete.evalCombined
  rw [if_neg (by simp only [hw, hc, ne_eq, not_true_eq_false, or_self, not_false_eq_true])]
  simp only [hv, Option.bind_eq_bind, Option.some_bind]
  exact zero_filter_combine_rows c wires constants publicHash alpha gates Verifier.zero h0

/-- SCENARIO 3 IS REAL, row form.  On a validated configuration with the right
column counts, zeroing every selector filter zeroes the gate aggregate at that
row REGARDLESS OF THE WIRE VALUES.  The selectors are read from the SUPPLIED
constants columns. -/
theorem all_filters_zero_gate_value (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (index : Nat)
    (hw : t.wires.length = c.numWires) (hc : t.constants.length = c.numConstants)
    (hv : Gates.validateConfiguration c gates = some ())
    (h0 : ∀ g ∈ gates, rowFilter c g t index = Verifier.zero) :
    gateValue c gates publicHash alpha t index = 0 := by
  unfold gateValue
  rw [zero_filter_eval_combined c gates _ _ publicHash alpha.toVerifier
    (by rw [List.length_map]; exact hw) (by rw [List.length_map]; exact hc) hv h0]
  exact rfl

/-- SCENARIO 3 IS REAL, cube form.  Zeroing every selector filter makes the
adopted conclusion true with a genuine, positive-constraint configuration and an
ARBITRARY eq column — in particular with a HONESTLY DERIVED one.  This scenario
is therefore NOT excluded by section 2. -/
theorem all_filters_zero_cube_sum (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (count : Nat)
    (hw : t.wires.length = c.numWires) (hc : t.constants.length = c.numConstants)
    (hv : Gates.validateConfiguration c gates = some ())
    (h0 : AllFiltersZero c gates t count) :
    cubeSum c gates publicHash alpha t count = 0 := by
  rw [cube_sum_is_eq_functional]
  refine List.sum_eq_zero ?_
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  rw [all_filters_zero_gate_value c gates publicHash alpha t i hw hc hv
    (h0 i (List.mem_range.mp hi)), mul_zero]

/-! ### Scenario 4: the evaluation-failure (shape mismatch) degeneracy -/

/-- SCENARIO 4 IS REAL.  If the supplied column COUNTS do not match the
configuration, the adopted `GatesComplete.evalCombined` returns `none` at every
row, the adopted `rowElement` totalises to `0`, and `cubeSum = 0` FOR ANY
TABLES.  This is the "vacuity on failing rows" obligation of
`ZeroCheckSemantics` in its strongest form.

IT IS ALREADY EXCLUDED by the adopted `Assumptions` field 2
(`extractedStateConsistent`), through `GateDenseRound.consistent_table_shape`;
it is enumerated here because the exclusion is a consequence of a field whose
docstring is about the constructor's shape ensures, not about this degeneracy. -/
theorem shape_mismatch_cube_sum_vanishes (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (count : Nat)
    (h : t.wires.length ≠ c.numWires ∨ t.constants.length ≠ c.numConstants) :
    cubeSum c gates publicHash alpha t count = 0 := by
  have hrow : ∀ index : Nat, gateValue c gates publicHash alpha t index = 0 := by
    intro index
    unfold gateValue
    rw [show GatesComplete.evalCombined c gates
        (t.wires.map (fun column => (column.getD index 0).toVerifier))
        (t.constants.map (fun column => (column.getD index 0).toVerifier))
        publicHash alpha.toVerifier = none by
      unfold GatesComplete.evalCombined
      rw [if_pos (by simpa only [List.length_map] using h)]]
  rw [cube_sum_is_eq_functional]
  refine List.sum_eq_zero ?_
  intro y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  rw [hrow i, mul_zero]

/-- SCENARIO 4 IS EXCLUDED by the adopted assumption 2: a `Consistent`
incomplete state has exactly `numWires` wire columns and `numConstants`
constant columns. -/
theorem consistent_state_has_matching_shape (c : Gates.Config) (s : ProverState)
    (hc : Consistent c s) (hn : ¬ isComplete s) :
    s.tables.wires.length = c.numWires ∧ s.tables.constants.length = c.numConstants :=
  let h := consistent_table_shape c s hc hn
  ⟨h.1, h.2.1⟩

/-! ## 2. The partition of unity for the adopted eq table

The adopted `EqTableProvenance.GateEqProvenance` pins the WHOLE eq column, not
one cell.  Its row sum is then not a free parameter at all: it is `1`. -/

/-- THE PARTITION OF UNITY, in the adopted multilinear-extension form: the
extension of the CONSTANT family `1` is `1` at every point.  The induction is
the adopted head split `ZeroCheckSemantics.extensionOf_cons`; each step
contributes the factor `(1 - t) + t = 1`. -/
theorem extensionOf_one : ∀ tau : List Element, extensionOf (fun _ => (1 : Element)) tau = 1
  | [] => by rw [extensionOf_nil]
  | t :: tau => by
      rw [extensionOf_cons, extensionOf_one tau]
      ring

/-- (2) THE PARTITION OF UNITY.  The adopted per-row eq products sum to `1` over
the whole Boolean cube, for EVERY `tau`. -/
theorem partition_of_unity (tau : List Element) :
    ((List.range (2 ^ tau.length)).map (fun i => rowProdFrom 0 tau i)).sum = 1 := by
  have h := extensionOf_one tau
  unfold extensionOf at h
  simpa only [mul_one] using h

/-- (2) THE EQ TABLE'S ROW SUM IS `1`.  The entries of `eqTable tau` are the
per-row products (adopted `eq_table_getD`), so their sum over the cube is the
partition of unity. -/
theorem eq_table_row_sum (tau : List Element) :
    ((List.range (2 ^ tau.length)).map (fun i => (eqTable tau).getD i 0)).sum = 1 := by
  rw [← partition_of_unity tau]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro i hi
  exact eq_table_getD tau i (List.mem_range.mp hi)

/-- (2) THE ROW SUM OF A PROVENANCED EQ COLUMN IS `1`.  `s.tables.eq` is
`s.eq.evaluations` by the adopted `ProverState.tables`, and
`GateEqProvenance` equates it with `eqTable tau` at the matching width. -/
theorem eq_provenance_row_sum (s : ProverState) (tau : List Element)
    (h : GateEqProvenance s tau) :
    eqRowSum s.tables (2 ^ s.eq.numVars) = 1 := by
  unfold eqRowSum
  rw [← h.2]
  have hcol : ∀ i : Nat, s.tables.eq.getD i 0 = (eqTable tau).getD i 0 := by
    intro i
    rw [show s.tables.eq = s.eq.evaluations from rfl, h.1]
  rw [List.map_congr_left (fun i _ => hcol i)]
  exact eq_table_row_sum tau

/-- (2) THE REJECTION ENGINE.  A supplied state whose eq column does NOT sum to
`1` over its cube has NO eq-table provenance, for ANY `tau`.  This is the lemma
that turns section 1's forgeries into impossibilities. -/
theorem no_eq_provenance_of_row_sum_ne_one (s : ProverState)
    (h : eqRowSum s.tables (2 ^ s.eq.numVars) ≠ 1) :
    ∀ tau : List Element, ¬ GateEqProvenance s tau :=
  fun tau hp => h (eq_provenance_row_sum s tau hp)

/-- (2) SCENARIO 1b IS IMPOSSIBLE UNDER PROVENANCE.  An eq column with the
adopted full-table provenance never has zero row sum. -/
theorem provenance_excludes_zero_row_sum (s : ProverState) (tau : List Element)
    (h : GateEqProvenance s tau) : ¬ ZeroEqRowSum s.tables (2 ^ s.eq.numVars) := by
  unfold ZeroEqRowSum
  rw [eq_provenance_row_sum s tau h]
  exact one_ne_zero

/-- (2) SCENARIO 1a IS IMPOSSIBLE UNDER PROVENANCE, a fortiori. -/
theorem provenance_excludes_zero_eq_column (s : ProverState) (tau : List Element)
    (h : GateEqProvenance s tau) : ¬ ZeroEqColumn s.tables (2 ^ s.eq.numVars) :=
  fun hz => provenance_excludes_zero_row_sum s tau h
    (zero_eq_column_row_sum s.tables (2 ^ s.eq.numVars) hz)

/-! ## 3. The strengthened assumption set and the strengthened conclusion -/

section Strong
open ConditionalSoundness
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {gates : List Gates.GateInfo} {s0 sLast : ProverState} {x : Element}
  {k : Cells} {alpha : Element} {gateTruths : List (List Element)} {tau : List Element}

/-- THE STRENGTHENED GATE-LANE ASSUMPTIONS.  Field `base` is the adopted
`GateClaimChain.Assumptions`, UNCHANGED and not restated, so everything the
adopted module proves about those eight fields applies verbatim.  Two fields are
ADDED; both are visible and both say what they assume. -/
structure StrongAssumptions (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (vc : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (s0 sLast : ProverState) (x : Element) (k : Cells) (alpha : Element)
    (gateTruths : List (List Element)) (tau : List Element) : Prop where
  /-- The adopted eight-field `GateClaimChain.Assumptions`, unchanged.  Keeping
  it makes `StrongAssumptions` STRICTLY STRONGER than the adopted set and lets
  the adopted `accepted_gate_cube_sum_vanishes` be applied as a black box. -/
  base : GateClaimChain.Assumptions e decode vc p gates s0 sLast x k alpha gateTruths
  /-- STRONG ASSUMPTION S1 (`eqProvenance`).  THE WHOLE EQ COLUMN of the
  extracted fresh state IS `ext3_eq_evals(tau)`, at the matching width: the
  adopted `EqTableProvenance.GateEqProvenance`.

  THIS IS THE FIELD THAT CREATES REJECTION POWER.  The adopted field 8
  (`eqCell`) pins ONE linear functional of this column; this field pins the
  column.  Section 2 then forces the row sum to be `1`, so the forgeries of
  scenarios 1a/1b become impossible, and section 4 turns a vanishing cube sum
  into a statement about every row.

  NOT PROVED: the eq table's construction is an extraction-boundary observation,
  exactly as adopted fields 2/3/6 are.  What would discharge it: threading the
  gate prover's constructor (`gate_ext3_v2.rs:95`,
  `Ext3DenseMle::new(ext3_eq_evals(gate_tau))`) through the same extractor that
  supplies `s0`.

  NOT CLAIMED: that this field makes the adopted field 8 redundant.  Deriving
  field 8 from it needs `tau = (e.initialTranscript vc p).gateTau` and the
  identification of the binding steps with the derived `gatePoint`, through the
  adopted `EqTableProvenance.bound_gate_eq_cell`.  That bridge is not built
  here, so field 8 is KEPT rather than replaced. -/
  eqProvenance : GateEqProvenance s0 tau
  /-- STRONG ASSUMPTION S2 (`activeFilter`).  AT LEAST ONE GATE IS ACTIVE AT AT
  LEAST ONE BOOLEAN ROW: some row's SUPPLIED constants give a nonzero selector
  filter for some decoded gate.

  WITHOUT THIS FIELD THE STRENGTHENED CONCLUSION IS STILL CONTENTLESS ON A REAL,
  REACHABLE SHAPE.  The adopted `GatesComplete.contribution` short-circuits to
  `some zero` whenever the filter is zero, and the selectors are read from the
  SUPPLIED constants columns, so a supplier who zeroes every selector obtains
  `gateValue = 0` at every row with a validated, constraint-POSITIVE
  configuration AND a genuine eq table; that is PROVED here, in
  `all_filters_zero_cube_sum` and `selector_forgery_survives_eq_provenance`.

  IT IS A NECESSARY, NOT A SUFFICIENT, NON-DEGENERACY CONDITION, exactly like
  the adopted field 4, and IT IS NOT USED in the proof of the conclusion below —
  it only excludes a regime in which the conclusion says nothing.  What would
  really close the hole is CONSTANTS PROVENANCE (the constants columns are the
  committed preprocessed columns), which is part of the open extraction join.

  NOT PROVED, and NOT derivable from acceptance. -/
  activeFilter : ∃ i, i < 2 ^ tau.length ∧
    ∃ g ∈ gates, rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero

/-- (3) The adopted conclusion, re-indexed by `tau`'s width.  Nothing is
strengthened yet; `GateEqProvenance`'s second component supplies
`tau.length = s0.eq.numVars`. -/
theorem strong_gate_cube_sum_vanishes (pin : Verifier.Pinned) (chain : Nat)
    (A : StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths tau)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths)) :
    cubeSum (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables
      (2 ^ tau.length) = 0 := by
  rw [A.eqProvenance.2]
  exact GateClaimChain.accepted_gate_cube_sum_vanishes pin chain A.base hacc hfree

/-- (3) THE STRENGTHENED CONCLUSION.  Under the strengthened assumptions, an
accepting run whose gate lane avoided every round agreement set AND whose drawn
`tau` avoids the adopted `ZeroCheckSemantics.zeroCheckBadSet` forces EVERY
Boolean row's gate aggregate to be zero — not merely a weighted sum.

This is the composition of the adopted `accepted_gate_cube_sum_vanishes` with
the adopted `ZeroCheckSemantics.gate_rows_vanish`; no new semantics is
introduced.  `hgood` is a HYPOTHESIS about the SUPPLIED tau, with no probability
attached: see the module header. -/
theorem strong_gate_rows_vanish (pin : Verifier.Pinned) (chain : Nat)
    (A : StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths tau)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths))
    (hgood : tupleOf tau ∉ zeroCheckBadSet tau.length
      (gateValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables)) :
    ∀ i, i < 2 ^ tau.length →
      gateValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i = 0 ∧
      rowElement (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i = 0 ∧
      ∀ v, rowTerm (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i = some v →
        v = Verifier.zero :=
  gate_rows_vanish (Integrated.gateConfig vc) gates
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables tau
    A.eqProvenance.1 (strong_gate_cube_sum_vanishes pin chain A hacc hfree) hgood

/-! ## 4. Rejection power -/

/-- (4) REJECTION POWER, DIRECT FORM.  If ANY Boolean row of the supplied tables
carries a nonzero gate aggregate, then under the strengthened assumptions an
accepting, bad-event-free run FORCES the SUPPLIED `tau` into the zero-check bad
set.  There is no other escape: the conclusion is now contingent on the
challenge, which is exactly what "having teeth" means. -/
theorem nonzero_row_forces_bad_tau (pin : Verifier.Pinned) (chain : Nat)
    (A : StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths tau)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
      (gateLaneOf e vc p gateTruths))
    (i : Nat) (hi : i < 2 ^ tau.length)
    (hnz : gateValue (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i ≠ 0) :
    tupleOf tau ∈ zeroCheckBadSet tau.length
      (gateValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables) := by
  by_contra hgood
  exact hnz ((strong_gate_rows_vanish pin chain A hacc hfree hgood i hi).1)

/-- (4) THE REJECTION-POWER THEOREM, CONTRAPOSITIVE FORM.  A supplied state with
a nonzero gate aggregate at some Boolean row, together with a drawn `tau`
OUTSIDE the zero-check bad set, is INCOMPATIBLE with the conjunction of
acceptance, the strengthened assumptions and bad-event freedom.

Something is now excluded.  The adopted statement excluded nothing: by
`zero_eq_forgery`, its conclusion is satisfiable from ANY tables whatsoever. -/
theorem strong_assumptions_reject (pin : Verifier.Pinned) (chain : Nat)
    (i : Nat) (hi : i < 2 ^ tau.length)
    (hnz : gateValue (Integrated.gateConfig vc) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables i ≠ 0)
    (hgood : tupleOf tau ∉ zeroCheckBadSet tau.length
      (gateValue (Integrated.gateConfig vc) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0.tables)) :
    ¬ (Integrated.verify e decode pin chain vc p = .ok () ∧
        StrongAssumptions e decode vc p gates s0 sLast x k alpha gateTruths tau ∧
        BadEventFree 0
          (GateClaimChain.endpointSum (Integrated.gateConfig vc) gates
            (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s0)
          (gateLaneOf e vc p gateTruths)) := by
  rintro ⟨hacc, A, hfree⟩
  exact hgood (nonzero_row_forces_bad_tau pin chain A hacc hfree i hi hnz)

/-- (4) THE DIFFERENCE, STATED AS ONE THEOREM.  For a state whose eq column does
not sum to `1`, the ADOPTED conclusion can hold (left conjunct, whenever the
column is zero on the cube) while the STRENGTHENED assumption set is
UNSATISFIABLE for every `tau` (right conjunct).  This is "rejected now, accepted
before" in the abstract; `forged_state_rejected_but_previously_accepted` gives
it on a concrete state. -/
theorem row_sum_forgery_rejected (s : ProverState)
    (h : eqRowSum s.tables (2 ^ s.eq.numVars) ≠ 1) :
    ∀ (e : Verifier.Engine) (decode : Integrated.DecodeGates) (vc : Verifier.Config)
      (p : Verifier.Proof) (gates : List Gates.GateInfo) (sLast : ProverState) (x : Element)
      (k : Cells) (alpha : Element) (gateTruths : List (List Element)) (tau : List Element),
      ¬ StrongAssumptions e decode vc p gates s sLast x k alpha gateTruths tau :=
  fun _ _ _ _ _ _ _ _ _ _ tau A => no_eq_provenance_of_row_sum_ne_one s h tau A.eqProvenance

end Strong

/-! ## 5. Concrete states: what is rejected now that was accepted before

All three states below are built on the adopted `GateDenseRound.exampleState`'s
witness columns, on the adopted validated `exampleConfig` (which declares
`numGateConstraints = 1`, so the adopted field 4 is satisfied) and on the
adopted `exampleGates`.  Only the eq column differs. -/

/-- A two-coordinate `tau`. -/
def exampleTau : List Element := [3, 5]

/-- The HONEST eq column: literally `ext3_eq_evals([3,5])`. -/
def honestEqColumn : List Element := [8, -12, -10, 15]

theorem honest_eq_column_is_eq_table : honestEqColumn = eqTable exampleTau := by decide

/-- The honest state: the adopted example's witness with a PROVENANCED eq
column. -/
def honestState : ProverState :=
  ⟨exampleState.wires, exampleState.constants, ⟨2, honestEqColumn⟩, 4, [], []⟩

/-- FORGERY 1a: the same witness with a ZERO eq column. -/
def forgedZeroState : ProverState :=
  ⟨exampleState.wires, exampleState.constants, ⟨2, [0, 0, 0, 0]⟩, 4, [], []⟩

/-- FORGERY 1b: the same witness with a NONZERO eq column of ZERO row sum,
chosen orthogonal to the example's gate aggregate `[0, -4, -7, -10]`:
`0·0 + (-1)·(-4) + 2·(-7) + (-1)·(-10) = 0` and `0 - 1 + 2 - 1 = 0`. -/
def forgedZeroSumState : ProverState :=
  ⟨exampleState.wires, exampleState.constants, ⟨2, [0, -1, 2, -1]⟩, 4, [], []⟩

/-- All three states are `GateDenseRound.Consistent` for the adopted
`exampleConfig`, so none of them is excluded by the adopted assumption 2. -/
theorem forged_states_consistent :
    Consistent exampleConfig honestState ∧ Consistent exampleConfig forgedZeroState ∧
      Consistent exampleConfig forgedZeroSumState :=
  ⟨⟨by decide, rfl, rfl⟩, ⟨by decide, rfl, rfl⟩, ⟨by decide, rfl, rfl⟩⟩

/-- THE WITNESS IS A LYING ONE: the adopted example's gate aggregate is NOT
identically zero on the cube — row 1 already fails.  The eq column does not
enter this value at all (`gate_value_ignores_eq`). -/
theorem forged_state_row_nonzero :
    gateValue exampleConfig exampleGates examplePublicHash exampleAlpha
      forgedZeroState.tables 1 ≠ 0 ∧
    gateValue exampleConfig exampleGates examplePublicHash exampleAlpha
      forgedZeroSumState.tables 1 ≠ 0 ∧
    ¬ CubeZero 2 (gateValue exampleConfig exampleGates examplePublicHash exampleAlpha
      honestState.tables) := by decide

/-- (1) WHAT THE ADOPTED CONCLUSION ACCEPTS.  Both forgeries satisfy the ADOPTED
conclusion `cubeSum = 0` on the full cube, with the lying witness above. -/
theorem forged_states_satisfy_adopted_conclusion :
    cubeSum exampleConfig exampleGates examplePublicHash exampleAlpha
      forgedZeroState.tables (2 ^ forgedZeroState.eq.numVars) = 0 ∧
    cubeSum exampleConfig exampleGates examplePublicHash exampleAlpha
      forgedZeroSumState.tables (2 ^ forgedZeroSumState.eq.numVars) = 0 := by decide

/-- (4) WHAT THE STRENGTHENED ASSUMPTIONS REJECT.  Neither forgery has an
eq-table provenance for ANY `tau`: their eq columns sum to `0`, and section 2
forces `1`. -/
theorem forged_states_have_no_eq_provenance :
    (∀ tau : List Element, ¬ GateEqProvenance forgedZeroState tau) ∧
      ∀ tau : List Element, ¬ GateEqProvenance forgedZeroSumState tau :=
  ⟨no_eq_provenance_of_row_sum_ne_one forgedZeroState (by decide),
   no_eq_provenance_of_row_sum_ne_one forgedZeroSumState (by decide)⟩

/-- (4) THE CONCRETE "REJECTED NOW, ACCEPTED BEFORE" STATEMENT.  For each
forgery: the adopted conclusion HOLDS, the witness is nonzero at a Boolean row,
and the strengthened assumption set is UNSATISFIABLE — for every engine, config,
proof, decoder, companion state, cells, challenge, alpha, truths and `tau`. -/
theorem forged_state_rejected_but_previously_accepted :
    (cubeSum exampleConfig exampleGates examplePublicHash exampleAlpha
        forgedZeroState.tables (2 ^ forgedZeroState.eq.numVars) = 0 ∧
      gateValue exampleConfig exampleGates examplePublicHash exampleAlpha
        forgedZeroState.tables 1 ≠ 0) ∧
    ∀ (e : Verifier.Engine) (decode : Integrated.DecodeGates) (vc : Verifier.Config)
      (p : Verifier.Proof) (gates : List Gates.GateInfo) (sLast : ProverState) (x : Element)
      (k : Cells) (alpha : Element) (gateTruths : List (List Element)) (tau : List Element),
      ¬ StrongAssumptions e decode vc p gates forgedZeroState sLast x k alpha gateTruths tau :=
  ⟨⟨forged_states_satisfy_adopted_conclusion.1, forged_state_row_nonzero.1⟩,
   row_sum_forgery_rejected forgedZeroState (by decide)⟩

/-- (4) THE HONEST STATE IS NOT REJECTED BY THE NEW FIELD, and the new field is
not vacuous: `honestState` DOES have eq-table provenance at `exampleTau`. -/
theorem honest_state_has_eq_provenance : GateEqProvenance honestState exampleTau :=
  ⟨honest_eq_column_is_eq_table, rfl⟩

/-- (4) …AND ON THE HONEST EQ COLUMN THE ZERO CHECK ACTUALLY FIRES: with the
provenanced column, the same lying witness has a NONZERO cube sum, so it cannot
satisfy the strengthened conclusion at this `tau` at all.  `-32 ≠ 0`. -/
theorem honest_state_cube_sum_nonzero :
    cubeSum exampleConfig exampleGates examplePublicHash exampleAlpha
      honestState.tables (2 ^ exampleTau.length) ≠ 0 := by decide

/-- (4) A GENERIC BRIDGE a consumer needs: a nonzero multilinear extension at a
challenge tuple puts that tuple OUTSIDE the adopted zero-check bad set.  Stated
generically in the variable count, so no `Finset.univ` over `Tuple n` is ever
elaborated. -/
theorem not_mem_zeroCheckBadSet_of_extension_ne_zero (n : Nat) (g : Nat → Element)
    (r : Tuple n) (h : extensionOf g (List.ofFn r) ≠ 0) : r ∉ zeroCheckBadSet n g := by
  intro hmem
  by_cases hz : CubeZero n g
  · rw [zeroCheckBadSet_empty n g hz] at hmem
    exact absurd hmem (Finset.not_mem_empty _)
  · rw [zeroCheckBadSet_of_not_cube_zero n g hz, mem_vanishingSet] at hmem
    exact h hmem

/-- (4) …AND THE GOOD-TAU CONDITION IS SATISFIABLE ON THIS WITNESS: at
`exampleTau` the multilinear extension of the example's gate aggregate is
NONZERO (it is `-32`), which by
`not_mem_zeroCheckBadSet_of_extension_ne_zero` is exactly "the drawn tuple is
outside the zero-check bad set".

The `Finset` form is NOT instantiated at these literals on purpose: elaborating
`zeroCheckBadSet 2 g` forces `Finset.univ : Finset (Fin 2 → Element)`, the
`p^6`-element function universe, and blows the elaborator — the same hazard as
the adopted `Fintype.card Element` note.  Nothing is lost: the generic lemma
above converts this statement into the membership form for any consumer that
needs it, and `hgood` in section 3/4 is always the generic form. -/
theorem honest_state_extension_nonzero :
    extensionOf (gateValue exampleConfig exampleGates examplePublicHash exampleAlpha
      honestState.tables) exampleTau ≠ 0 := by
  rw [← cubeSum_is_extension exampleConfig exampleGates examplePublicHash exampleAlpha
    honestState.tables exampleTau honest_state_has_eq_provenance.1]
  exact honest_state_cube_sum_nonzero

/-! ### The selector forgery, which the eq strengthening does NOT exclude -/

/-- A validated two-row configuration with TWO selectors, so the adopted
`Gates.computeFilter` carries the unused-selector factor and can be zeroed:
`⟨numSelectors 2, numConstants 4, numGateConstraints 1, numWires 4,
quotientDegree 4⟩`. -/
def selectorConfig : Gates.Config := ⟨2, 4, 1, 4, 4⟩

/-- Two arithmetic gates sharing the selector group `[0,2)`. -/
def selectorGates : List Gates.GateInfo := [⟨3, 0, 0, 2, 0, 1, 1, 0, 0⟩, ⟨3, 0, 0, 2, 1, 1, 1, 0, 0⟩]

/-- The same witness columns as the adopted example, a selector column pinned to
the UNUSED selector value `4294967295` at every row, and a HONEST, provenanced
eq column. -/
def selectorForgedState : ProverState :=
  ⟨[⟨2, [5, 1, 2, 3]⟩, ⟨2, [7, 1, 1, 2]⟩, ⟨2, [11, 1, 4, 5]⟩, ⟨2, [103, 1, 9, 17]⟩],
   [⟨2, [4294967295, 4294967295, 4294967295, 4294967295]⟩, ⟨2, [2, 2, 2, 2]⟩,
    ⟨2, [3, 3, 3, 3]⟩, ⟨2, [1, 1, 1, 1]⟩],
   ⟨2, honestEqColumn⟩, 6, [], []⟩

theorem selector_configuration_valid :
    Gates.validateConfiguration selectorConfig selectorGates = some () ∧
      0 < selectorConfig.numGateConstraints ∧
      Consistent selectorConfig selectorForgedState :=
  ⟨by decide, by decide, ⟨by decide, rfl, rfl⟩⟩

/-- (1, scenario 3) THE SELECTOR FORGERY IS REAL AND SURVIVES SECTION 2.  The
configuration is validated and declares a POSITIVE constraint count (adopted
field 4 satisfied); the eq column HAS provenance (strong field S1 satisfied);
every Boolean row's gate aggregate is `0` and so is the cube sum — because every
selector filter is `0`, not because the witness satisfies anything.

CONSEQUENCE, STATED PLAINLY: the strengthened conclusion of section 3 is TRUE
here and detects nothing.  The eq strengthening does not close this hole; only
provenance for the CONSTANTS columns would. -/
theorem selector_forgery_survives_eq_provenance :
    GateEqProvenance selectorForgedState exampleTau ∧
      (∀ i, i < 4 → gateValue selectorConfig selectorGates examplePublicHash exampleAlpha
        selectorForgedState.tables i = 0) ∧
      cubeSum selectorConfig selectorGates examplePublicHash exampleAlpha
        selectorForgedState.tables 4 = 0 :=
  ⟨⟨honest_eq_column_is_eq_table, rfl⟩, by decide, by decide⟩

/-- (1, scenario 3) …and the same configuration with an ORDINARY selector column
does NOT vanish, so the forgery above is a property of the zeroed selectors, not
of the configuration. -/
theorem selector_column_matters :
    cubeSum selectorConfig selectorGates examplePublicHash exampleAlpha
      ⟨selectorForgedState.tables.wires,
        [[0, 1, 0, 1], [2, 2, 2, 2], [3, 3, 3, 3], [1, 1, 1, 1]],
        honestEqColumn⟩ 4 ≠ 0 := by decide

end Audit.Wire3.GateRejectionPower
