import Audit.Wire3.DenseMleIndexed
import Audit.Wire3.OuterInterpolationTotal

/-!
# Norm/logUp prover round on the indexed DenseMle tables

Source: mle/src/permutation/norm_logup.rs
* `NORM_LOGUP_MAX_DEGREE = 5` (24);
* `PreparedChallenges` (270-316): lambda powers by a running product, k_is
  taken to `num_routed_wires`;
* `evaluate_target_from_values` (319-359): four width `assert_eq!`s, one loop
  over routed wires with both accumulators, then
  `eq*helper + kappa*logup + xi*public_input_binding`;
* `line_value` (386-390): `low + point*(high-low)` at `2*suffix`, `2*suffix+1`;
* `NormLogupMleState` / `PublicInputBindingState` (392-410) and `from_base`
  (414-491): every DenseMle has `num_rows = 1 << tau.len()` entries, PI rows
  and columns are asserted in range, `prefix_eq` starts at one and the eta
  powers are a running product;
* `round_sum_at` (493-540): four scratch vectors, the suffix loop, the PI loop
  with `row >> (bound+1)` / `(row >> bound) & 1`, then `sum + xi*binding`;
* `bind` (542-563): PI prefix update BEFORE `bound_variables += 1`, then
  `bind_variable_in_place` on every table;
* `NormLogupProverStateError` (568-580), `NormLogupProverState` (607-614),
  `current_round` (682-703): `is_complete`
  error, cached `pending_round`, samples at `Field64_3::from(0..=5)`,
  `ext3_evaluations_to_coefficients`, and `coefficients[1..]`;
* `bind_challenge` (707-723), `is_complete` (726-728),
  `into_proof_and_point` (744-758).
Interpolation is mle/src/sumcheck/coefficients.rs:180-195,219-238 through the
adopted `OuterInterpolation.interpolate`.

The variable is the NEXT outer coordinate. Current arrays and prepared
challenges are fixed before it is quantified. `Shape` is the caller invariant
established by the constructor asserts; it is NOT an additional runtime guard.
`getD` is a totalized read; the Tables-level round theorems take
`0 < remaining` so that every index they reach is covered by the separately
proved read-bound theorems, and the state-level theorems derive that from
`Consistent` and `¬isComplete`. The verifier-evaluation theorems use the honest
endpoint-sum claim; no dishonest-prover or cross-round chaining statement is
made. A failed `num_vars > 0` assert in `bind` is modelled as `none` (abort),
not as the partially mutated Rust state; the width asserts of `evaluate_target_from_values`, the `num_vars > 0` assert
of every table bind, and the interpolation pivot inversions are modelled as
`none`/`panic`. Each scratch vector is written by its own index loop, which is
the same as the source's interleaved writes to four distinct vectors.

Not modelled here: the constructor's base-to-Ext3 transposition and eq table,
the origin of the prepared weights beyond their lengths, transcript
distribution, circuit truth, individual PI equality, Rust compiler/word/memory
refinement, and PCS/Fiat-Shamir soundness.
-/
namespace Audit.Wire3.NormDenseRound
open Audit.Wire3 GoldilocksExt3Field

/-- PublicInputBindingState (norm_logup.rs:404-410). `publicValue` is the
base value whose embedding `Norm.embed` is the stored `value`. -/
structure Binding where
  row : Nat
  column : Nat
  publicValue : Verifier.Base
  etaPower : Element
  prefixEq : Element

/-- NormLogupMleState (norm_logup.rs:392-402). `remaining` is the shared
`num_vars` of every constituent Ext3DenseMle: `tau.len()` at construction,
decremented by every bind. -/
structure Tables where
  eq : List Element
  subgroup : List Element
  wires : List (List Element)
  sigmas : List (List Element)
  identityHelpers : List (List Element)
  sigmaHelpers : List (List Element)
  bindings : List Binding
  boundVariables : Nat
  remaining : Nat

/-- PreparedChallenges (norm_logup.rs:270-279); beta/gamma limbs are read
from `challenges` by the adopted NormPolynomial denominators. -/
structure Prepared where
  challenges : Norm.Challenges
  kIs : List Verifier.Base
  lambdaPowers : List Element

def ColumnShape (columns : List (List Element)) (width length : Nat) : Prop :=
  columns.length=width ∧ ∀ column ∈ columns, column.length=length

/-- The constructor invariants (from_base 425-444, PreparedChallenges::new
288-297) as they stand after `boundVariables` binds. -/
def Shape (t : Tables) (p : Prepared) : Prop :=
  t.eq.length=2^t.remaining ∧ t.subgroup.length=2^t.remaining ∧
  ColumnShape t.wires t.wires.length (2^t.remaining) ∧
  ColumnShape t.sigmas t.wires.length (2^t.remaining) ∧
  ColumnShape t.identityHelpers t.wires.length (2^t.remaining) ∧
  ColumnShape t.sigmaHelpers t.wires.length (2^t.remaining) ∧
  p.kIs.length=t.wires.length ∧ p.lambdaPowers.length=t.wires.length ∧
  ∀ b ∈ t.bindings, b.row<2^(t.boundVariables+t.remaining) ∧ b.column<t.wires.length

/-! ## line_value and its three adopted readings -/

/-- line_value (norm_logup.rs:386-390). -/
def line (column : List Element) (suffix : Nat) (x : Element) : Element :=
  column.getD (2*suffix) 0+x*(column.getD (2*suffix+1) 0-column.getD (2*suffix) 0)

theorem line_same_dense (column : List Element) (suffix : Nat) (x : Element) :
    line column suffix x = DenseMleIndexed.line column x suffix :=
  (DenseMleIndexed.blend_equals_line _ _ _).symm

theorem line_same_polynomial (column : List Element) (suffix : Nat) (x : Element) :
    line column suffix x = (NormPolynomial.affine (DenseMleIndexed.endpoints column suffix)).eval x := by
  exact (NormPolynomial.affine_evaluation (DenseMleIndexed.endpoints column suffix) x).symm

theorem line_same_actual_binding (column : List Element) (suffix : Nat) (x : Element)
    (h : suffix<column.length/2) :
    line column suffix x = (DenseMleIndexed.bindBuffer column x).getD suffix 0 := by
  rw [DenseMleIndexed.bind_buffer_reads_exact_line column x suffix h,line_same_dense]

def columnAt (columns : List (List Element)) (j : Nat) : List Element := columns.getD j []
def baseZero : Verifier.Base := ⟨0,by decide⟩

/-! ## One suffix row as the adopted degree-five row polynomial -/

def wireValues (t : Tables) (p : Prepared) (suffix j : Nat) (x : Element) : NormPolynomial.WireValues :=
  ⟨(line (columnAt t.wires j) suffix x).toVerifier,
    Verifier.scalar (line t.subgroup suffix x).toVerifier (p.kIs.getD j baseZero).val,
    (line (columnAt t.sigmas j) suffix x).toVerifier,
    (line (columnAt t.identityHelpers j) suffix x).toVerifier,
    (line (columnAt t.sigmaHelpers j) suffix x).toVerifier⟩

def wireLine (t : Tables) (p : Prepared) (suffix j : Nat) : NormPolynomial.WireLine :=
  ⟨DenseMleIndexed.endpoints (columnAt t.wires j) suffix,
    DenseMleIndexed.endpoints (columnAt t.sigmas j) suffix,
    DenseMleIndexed.endpoints (columnAt t.identityHelpers j) suffix,
    DenseMleIndexed.endpoints (columnAt t.sigmaHelpers j) suffix,
    (p.kIs.getD j baseZero).val,p.lambdaPowers.getD j 0⟩

def capturedRow (t : Tables) (p : Prepared) (suffix : Nat) : NormPolynomial.Row :=
  ⟨DenseMleIndexed.endpoints t.eq suffix,
    DenseMleIndexed.endpoints t.subgroup suffix,
    (List.range t.wires.length).map (wireLine t p suffix)⟩

/-- The two accumulator increments of one routed wire (norm_logup.rs:337-355). -/
def contribution (t : Tables) (p : Prepared) (suffix : Nat) (x : Element) (j : Nat) :
    Verifier.Ext3 × Verifier.Ext3 :=
  NormPolynomial.actualContribution p.challenges (p.lambdaPowers.getD j 0).toVerifier
    (wireValues t p suffix j x)

def rowValue (t : Tables) (p : Prepared) (suffix : Nat) (x : Element) : Verifier.Ext3 :=
  Verifier.add
    (Verifier.mul (line t.eq suffix x).toVerifier
      ((List.range t.wires.length).foldl (fun acc j => Verifier.add acc (contribution t p suffix x j).1) Verifier.zero))
    (Verifier.mul p.challenges.kappa
      ((List.range t.wires.length).foldl (fun acc j => Verifier.add acc (contribution t p suffix x j).2) Verifier.zero))

theorem captured_wire_values (t : Tables) (p : Prepared) (suffix j : Nat) (x : Element) :
    NormPolynomial.evaluatedWireValues (DenseMleIndexed.endpoints t.subgroup suffix)
      (wireLine t p suffix j) x = wireValues t p suffix j x := by
  simp only [NormPolynomial.evaluatedWireValues,wireLine,wireValues,← line_same_polynomial]

theorem captured_row_value (t : Tables) (p : Prepared) (suffix : Nat) (x : Element) :
    NormPolynomial.actualRowEvaluation p.challenges (capturedRow t p suffix) x = rowValue t p suffix x := by
  simp only [NormPolynomial.actualRowEvaluation,capturedRow,List.foldl_map,Function.comp_def,
    captured_wire_values,← line_same_polynomial,rowValue,contribution]
  rfl

/-! ## The public-input line -/

def piSuffix (t : Tables) (b : Binding) : Nat := b.row / 2^(t.boundVariables+1)
def piFactor (t : Tables) (b : Binding) (x : Element) : Element :=
  b.prefixEq * if b.row / 2^t.boundVariables % 2 = 0 then 1-x else x

def piValue (t : Tables) (b : Binding) (x : Element) : Verifier.Ext3 :=
  Verifier.mul (Verifier.mul b.etaPower.toVerifier (piFactor t b x).toVerifier)
    (Verifier.sub (line (columnAt t.wires b.column) (piSuffix t b) x).toVerifier (Norm.embed b.publicValue.val))

def capturedPi (t : Tables) (b : Binding) : NormPolynomial.PiLine :=
  ⟨b.row,t.boundVariables,b.prefixEq,b.etaPower,b.publicValue,
    DenseMleIndexed.endpoints (columnAt t.wires b.column) (piSuffix t b)⟩

theorem captured_pi_value (t : Tables) (b : Binding) (x : Element) :
    NormPolynomial.actualPiLineEvaluation (capturedPi t b) x = piValue t b x := by
  simp only [NormPolynomial.actualPiLineEvaluation,capturedPi,piValue,piFactor,Norm.booleanFactor,
    ← line_same_polynomial]
  split <;> rfl

/-- The PI loop body exactly as written (norm_logup.rs:527-538): shifts and
the `& 1` mask. -/
def piSource (t : Tables) (b : Binding) (x : Element) : Verifier.Ext3 :=
  let suffix := b.row >>> (t.boundVariables+1)
  let bit := (b.row >>> t.boundVariables) &&& 1
  let eqLine := b.prefixEq * if bit = 0 then 1-x else x
  Verifier.mul (Verifier.mul b.etaPower.toVerifier eqLine.toVerifier)
    (Verifier.sub (line (columnAt t.wires b.column) suffix x).toVerifier (Norm.embed b.publicValue.val))

theorem pi_bit_shift_is_same (t : Tables) (b : Binding) :
    (b.row >>> t.boundVariables) % 2 = b.row / 2^t.boundVariables % 2 := by
  rw [Nat.shiftRight_eq_div_pow]

theorem pi_suffix_shift_is_same (t : Tables) (b : Binding) :
    b.row >>> (t.boundVariables+1) = piSuffix t b := by
  rw [Nat.shiftRight_eq_div_pow]
  rfl

theorem pi_source_is_pi_value (t : Tables) (b : Binding) (x : Element) :
    piSource t b x = piValue t b x := by
  simp only [piSource,piValue,piFactor,piSuffix,Nat.shiftRight_eq_div_pow,Nat.and_one_is_mod]

/-! ## The whole round as one polynomial -/

def roundValue (t : Tables) (p : Prepared) (x : Element) : Verifier.Ext3 :=
  Verifier.add
    ((List.range (t.eq.length/2)).foldl (fun acc s => Verifier.add acc (rowValue t p s x)) Verifier.zero)
    (Verifier.mul p.challenges.xi
      (t.bindings.foldl (fun acc b => Verifier.add acc (piValue t b x)) Verifier.zero))

noncomputable def roundPolynomial (t : Tables) (p : Prepared) : NormPolynomial.Poly :=
  NormPolynomial.roundPolynomial p.challenges
    ((List.range (t.eq.length/2)).map (capturedRow t p)) (t.bindings.map (capturedPi t))

theorem round_polynomial_same_ordered_evaluation (t : Tables) (p : Prepared) (x : Element) :
    ((roundPolynomial t p).eval x).toVerifier = roundValue t p x := by
  simp only [roundPolynomial,NormPolynomial.round_evaluation_actual,List.foldl_map,
    Function.comp_def,captured_row_value,captured_pi_value,roundValue]

theorem round_polynomial_degree_five (t : Tables) (p : Prepared) :
    (roundPolynomial t p).natDegree ≤ 5 :=
  NormPolynomial.round_degree_five _ _ _

/-- One fixed polynomial for all x; this does not claim the totalized
unshaped helper is an actual safe source execution. Bounds are below. -/
theorem one_fixed_round_polynomial (t : Tables) (p : Prepared) :
    ∃ f : NormPolynomial.Poly, f.natDegree ≤ 5 ∧ ∀ x, (f.eval x).toVerifier = roundValue t p x :=
  ⟨roundPolynomial t p,round_polynomial_degree_five t p,round_polynomial_same_ordered_evaluation t p⟩

/-! ## evaluate_target_from_values on the scratch slices -/

def values (xs : List Element) : List Verifier.Ext3 := xs.map Element.toVerifier

theorem values_getD (xs : List Element) (i : Nat) :
    (values xs).getD i Verifier.zero = (xs.getD i 0).toVerifier := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [values,List.map_cons,List.getD_cons_succ] using ih i

theorem values_length (xs : List Element) : (values xs).length = xs.length :=
  List.length_map xs Element.toVerifier

/-- The five reads of one routed wire (norm_logup.rs:337-345). -/
def sliceWireValues (p : Prepared) (wires sigmas identityHelpers sigmaHelpers : List Verifier.Ext3)
    (subgroup : Verifier.Ext3) (j : Nat) : NormPolynomial.WireValues :=
  ⟨wires.getD j Verifier.zero,
    Verifier.scalar subgroup (p.kIs.getD j baseZero).val,
    sigmas.getD j Verifier.zero,
    identityHelpers.getD j Verifier.zero,
    sigmaHelpers.getD j Verifier.zero⟩

def sliceContribution (p : Prepared) (wires sigmas identityHelpers sigmaHelpers : List Verifier.Ext3)
    (subgroup : Verifier.Ext3) (j : Nat) : Verifier.Ext3 × Verifier.Ext3 :=
  NormPolynomial.actualContribution p.challenges (p.lambdaPowers.getD j 0).toVerifier
    (sliceWireValues p wires sigmas identityHelpers sigmaHelpers subgroup j)

/-- The single source loop carrying both accumulators (norm_logup.rs:334-355). -/
def targetLoop (p : Prepared) (wires sigmas identityHelpers sigmaHelpers : List Verifier.Ext3)
    (subgroup : Verifier.Ext3) : Verifier.Ext3 × Verifier.Ext3 :=
  (List.range p.lambdaPowers.length).foldl (fun acc j =>
    (Verifier.add acc.1 (sliceContribution p wires sigmas identityHelpers sigmaHelpers subgroup j).1,
     Verifier.add acc.2 (sliceContribution p wires sigmas identityHelpers sigmaHelpers subgroup j).2))
    (Verifier.zero,Verifier.zero)

/-- evaluate_target_from_values (norm_logup.rs:319-359). The four width
`assert_eq!`s are `none`; the `xi * public_input_binding` term is kept even
though every suffix call passes zero. -/
def targetValue (p : Prepared) (eqValue : Verifier.Ext3)
    (wires sigmas identityHelpers sigmaHelpers : List Verifier.Ext3)
    (subgroup publicInputBinding : Verifier.Ext3) : Option Verifier.Ext3 :=
  if wires.length=p.lambdaPowers.length ∧ sigmas.length=p.lambdaPowers.length ∧
      identityHelpers.length=p.lambdaPowers.length ∧ sigmaHelpers.length=p.lambdaPowers.length then
    some (Verifier.add
      (Verifier.add
        (Verifier.mul eqValue (targetLoop p wires sigmas identityHelpers sigmaHelpers subgroup).1)
        (Verifier.mul p.challenges.kappa (targetLoop p wires sigmas identityHelpers sigmaHelpers subgroup).2))
      (Verifier.mul p.challenges.xi publicInputBinding))
  else none

theorem target_value_width_mismatch (p : Prepared) (eqValue : Verifier.Ext3)
    (wires sigmas identityHelpers sigmaHelpers : List Verifier.Ext3) (subgroup publicInputBinding : Verifier.Ext3)
    (h : ¬(wires.length=p.lambdaPowers.length ∧ sigmas.length=p.lambdaPowers.length ∧
      identityHelpers.length=p.lambdaPowers.length ∧ sigmaHelpers.length=p.lambdaPowers.length)) :
    targetValue p eqValue wires sigmas identityHelpers sigmaHelpers subgroup publicInputBinding = none := by
  simp only [targetValue,if_neg h]

theorem pair_fold_splits {α : Type} (f g : α → Verifier.Ext3) (xs : List α) (a b : Verifier.Ext3) :
    xs.foldl (fun acc x => (Verifier.add acc.1 (f x),Verifier.add acc.2 (g x))) (a,b) =
      (xs.foldl (fun acc x => Verifier.add acc (f x)) a,xs.foldl (fun acc x => Verifier.add acc (g x)) b) := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x _ ih => exact ih _ _

theorem target_loop_splits (p : Prepared) (wires sigmas identityHelpers sigmaHelpers : List Verifier.Ext3)
    (subgroup : Verifier.Ext3) :
    targetLoop p wires sigmas identityHelpers sigmaHelpers subgroup =
      ((List.range p.lambdaPowers.length).foldl
        (fun acc j => Verifier.add acc (sliceContribution p wires sigmas identityHelpers sigmaHelpers subgroup j).1) Verifier.zero,
       (List.range p.lambdaPowers.length).foldl
        (fun acc j => Verifier.add acc (sliceContribution p wires sigmas identityHelpers sigmaHelpers subgroup j).2) Verifier.zero) :=
  pair_fold_splits (fun j => (sliceContribution p wires sigmas identityHelpers sigmaHelpers subgroup j).1)
    (fun j => (sliceContribution p wires sigmas identityHelpers sigmaHelpers subgroup j).2) _ _ _

theorem add_scaled_zero (a b : Verifier.Ext3) : Verifier.add a (Verifier.mul b Verifier.zero) = a := by
  have h : NormPolynomial.lift a + NormPolynomial.lift b * 0 = NormPolynomial.lift a := by ring
  exact congrArg Element.toVerifier h

/-! ## The scratch vectors of round_sum_at -/

theorem set_loop_exact (f : Nat → Element) (count : Nat) : ∀ (start : Nat) (v : List Element),
    start+count ≤ v.length → (∀ j, j < start → v.getD j 0 = f j) →
    ((List.range' start count).foldl (fun v j => v.set j (f j)) v).length = v.length ∧
    ∀ j, j < start+count → ((List.range' start count).foldl (fun v j => v.set j (f j)) v).getD j 0 = f j := by
  induction count with
  | zero =>
      intro start v _ hv
      exact ⟨rfl,fun j hj => hv j (by omega)⟩
  | succ count ih =>
      intro start v hlen hv
      have hstep := ih (start+1) (v.set start (f start)) (by rw [List.length_set]; omega) (by
        intro j hj
        by_cases he : start = j
        · subst he
          exact DenseMleIndexed.set_same v start (f start) (by omega)
        · rw [DenseMleIndexed.set_other v start j (f start) he]
          exact hv j (by omega))
      rw [List.range'_succ,List.foldl_cons]
      refine ⟨hstep.1.trans (List.length_set _ _ _),fun j hj => hstep.2 j (by omega)⟩

/-- `scratch[j] = f j` for every `j < width` on any vector of length `width`
(the source's `vec![ZERO; width]` and, in later suffixes, the previous
iteration's fully overwritten vector). -/
theorem range_set_loop_exact (f : Nat → Element) (width : Nat) (v : List Element) (hv : v.length = width) :
    (List.range width).foldl (fun v j => v.set j (f j)) v = (List.range width).map f := by
  have h := set_loop_exact f width 0 v (by omega) (by intro j hj; omega)
  rw [← List.range_eq_range'] at h
  apply List.ext_get (by rw [h.1,hv,List.length_map,List.length_range])
  intro j hj hk
  rw [← List.getD_eq_get _ _ hj,h.2 j (by rw [h.1,hv] at hj; omega)]
  simp only [List.get_eq_getElem,List.getElem_map,List.getElem_range]

theorem map_range_getD {α : Type} (f : Nat → α) (d : α) (n j : Nat) (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  rw [List.getD_eq_get _ _ (by rw [List.length_map,List.length_range]; exact hj)]
  simp only [List.get_eq_getElem,List.getElem_map,List.getElem_range]

/-- One scratch write loop of round_sum_at (norm_logup.rs:503-510) for one of
the four vectors: `for j in 0..width { scratch[j] = line_value(columns[j], suffix, point) }`. -/
def fill (width : Nat) (scratch : List Element) (columns : List (List Element)) (suffix : Nat) (x : Element) :
    List Element :=
  (List.range width).foldl (fun scratch j => scratch.set j (line (columnAt columns j) suffix x)) scratch

theorem fill_exact (width : Nat) (scratch : List Element) (columns : List (List Element)) (suffix : Nat)
    (x : Element) (h : scratch.length = width) :
    fill width scratch columns suffix x = (List.range width).map (fun j => line (columnAt columns j) suffix x) :=
  range_set_loop_exact _ width scratch h

/-- The four scratch vectors `wires, sigmas, inverse_identity, inverse_sigma`
(norm_logup.rs:496-499). -/
structure Scratch where
  wires : List Element
  sigmas : List Element
  identityHelpers : List Element
  sigmaHelpers : List Element

def ScratchShape (width : Nat) (s : Scratch) : Prop :=
  s.wires.length = width ∧ s.sigmas.length = width ∧
  s.identityHelpers.length = width ∧ s.sigmaHelpers.length = width

def initialScratch (width : Nat) : Scratch :=
  ⟨List.replicate width 0,List.replicate width 0,List.replicate width 0,List.replicate width 0⟩

theorem initial_scratch_shape (width : Nat) : ScratchShape width (initialScratch width) := by
  simp [ScratchShape,initialScratch]

def fillScratch (t : Tables) (s : Scratch) (suffix : Nat) (x : Element) : Scratch :=
  ⟨fill t.wires.length s.wires t.wires suffix x,
   fill t.wires.length s.sigmas t.sigmas suffix x,
   fill t.wires.length s.identityHelpers t.identityHelpers suffix x,
   fill t.wires.length s.sigmaHelpers t.sigmaHelpers suffix x⟩

def scratchAt (t : Tables) (suffix : Nat) (x : Element) : Scratch :=
  ⟨(List.range t.wires.length).map (fun j => line (columnAt t.wires j) suffix x),
   (List.range t.wires.length).map (fun j => line (columnAt t.sigmas j) suffix x),
   (List.range t.wires.length).map (fun j => line (columnAt t.identityHelpers j) suffix x),
   (List.range t.wires.length).map (fun j => line (columnAt t.sigmaHelpers j) suffix x)⟩

theorem scratch_at_shape (t : Tables) (suffix : Nat) (x : Element) :
    ScratchShape t.wires.length (scratchAt t suffix x) := by
  simp [ScratchShape,scratchAt]

theorem fill_scratch_exact (t : Tables) (s : Scratch) (suffix : Nat) (x : Element)
    (hs : ScratchShape t.wires.length s) : fillScratch t s suffix x = scratchAt t suffix x := by
  simp only [fillScratch,scratchAt,fill_exact _ _ _ _ _ hs.1,fill_exact _ _ _ _ _ hs.2.1,
    fill_exact _ _ _ _ _ hs.2.2.1,fill_exact _ _ _ _ _ hs.2.2.2]

theorem scratch_wire_values (t : Tables) (p : Prepared) (suffix : Nat) (x : Element) (j : Nat)
    (hj : j < t.wires.length) :
    sliceWireValues p (values (scratchAt t suffix x).wires) (values (scratchAt t suffix x).sigmas)
      (values (scratchAt t suffix x).identityHelpers) (values (scratchAt t suffix x).sigmaHelpers)
      (line t.subgroup suffix x).toVerifier j = wireValues t p suffix j x := by
  simp only [sliceWireValues,wireValues,scratchAt,values_getD,map_range_getD _ _ _ _ hj]

theorem foldl_pair_congr {α : Type} (f g : α → Verifier.Ext3 × Verifier.Ext3) (xs : List α)
    (h : ∀ a ∈ xs, f a = g a) (a b : Verifier.Ext3) :
    xs.foldl (fun acc x => Verifier.add acc (f x).1) a = xs.foldl (fun acc x => Verifier.add acc (g x).1) a ∧
    xs.foldl (fun acc x => Verifier.add acc (f x).2) b = xs.foldl (fun acc x => Verifier.add acc (g x).2) b := by
  induction xs generalizing a b with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
      simp only [List.foldl_cons,h x (by simp)]
      exact ih (fun y hy => h y (by simp [hy])) _ _

/-- The suffix call of evaluate_target_from_values (norm_logup.rs:511-521)
with `public_input_binding = ZERO`. -/
def suffixTarget (t : Tables) (p : Prepared) (s : Scratch) (suffix : Nat) (x : Element) : Option Verifier.Ext3 :=
  targetValue p (line t.eq suffix x).toVerifier (values s.wires) (values s.sigmas)
    (values s.identityHelpers) (values s.sigmaHelpers) (line t.subgroup suffix x).toVerifier Verifier.zero

theorem scratch_target_is_row_value (t : Tables) (p : Prepared) (suffix : Nat) (x : Element)
    (hl : p.lambdaPowers.length = t.wires.length) :
    suffixTarget t p (scratchAt t suffix x) suffix x = some (rowValue t p suffix x) := by
  have hw : ScratchShape t.wires.length (scratchAt t suffix x) := scratch_at_shape t suffix x
  have hc : ∀ j ∈ List.range t.wires.length,
      sliceContribution p (values (scratchAt t suffix x).wires) (values (scratchAt t suffix x).sigmas)
        (values (scratchAt t suffix x).identityHelpers) (values (scratchAt t suffix x).sigmaHelpers)
        (line t.subgroup suffix x).toVerifier j = contribution t p suffix x j := by
    intro j hj
    simp only [sliceContribution,contribution,scratch_wire_values t p suffix x j (List.mem_range.mp hj)]
  have hf := foldl_pair_congr _ _ (List.range t.wires.length) hc Verifier.zero Verifier.zero
  simp only [suffixTarget,targetValue,values_length,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2,hl,and_self,if_true,
    target_loop_splits,add_scaled_zero,rowValue,hf.1,hf.2]

/-- One iteration of the suffix loop (norm_logup.rs:502-522): overwrite the
four scratch vectors, then add the target value. -/
def suffixStep (t : Tables) (p : Prepared) (x : Element) (state : Verifier.Ext3 × Scratch) (suffix : Nat) :
    Option (Verifier.Ext3 × Scratch) := do
  let s := fillScratch t state.2 suffix x
  let v ← suffixTarget t p s suffix x
  pure (Verifier.add state.1 v,s)

theorem suffix_step_shaped (t : Tables) (p : Prepared) (x : Element) (acc : Verifier.Ext3) (s : Scratch)
    (suffix : Nat) (hl : p.lambdaPowers.length = t.wires.length) (hs : ScratchShape t.wires.length s) :
    suffixStep t p x (acc,s) suffix = some (Verifier.add acc (rowValue t p suffix x),scratchAt t suffix x) := by
  simp only [suffixStep,fill_scratch_exact t s suffix x hs,scratch_target_is_row_value t p suffix x hl,
    bind,Option.bind,pure]

theorem suffix_loop_shaped (t : Tables) (p : Prepared) (x : Element) (hl : p.lambdaPowers.length = t.wires.length)
    (suffixes : List Nat) : ∀ (acc : Verifier.Ext3) (s : Scratch), ScratchShape t.wires.length s →
    ∃ s', suffixes.foldlM (suffixStep t p x) (acc,s) =
      some (suffixes.foldl (fun acc suffix => Verifier.add acc (rowValue t p suffix x)) acc,s') ∧
      ScratchShape t.wires.length s' := by
  induction suffixes with
  | nil => intro acc s hs; exact ⟨s,rfl,hs⟩
  | cons suffix rest ih =>
      intro acc s hs
      obtain ⟨s',hrest,hshape⟩ := ih (Verifier.add acc (rowValue t p suffix x)) (scratchAt t suffix x)
        (scratch_at_shape t suffix x)
      refine ⟨s',?_,hshape⟩
      simp only [List.foldlM_cons,suffix_step_shaped t p x acc s suffix hl hs,bind,Option.bind,hrest,List.foldl_cons]

/-- round_sum_at (norm_logup.rs:493-540): `half = eq.len()/2`, the scratch
vectors sized by `wires.len()`, the suffix loop, then the ordered PI loop and
`sum + xi * public_input_binding`. -/
def roundSumAt (t : Tables) (p : Prepared) (x : Element) : Option Verifier.Ext3 := do
  let result ← (List.range (t.eq.length/2)).foldlM (suffixStep t p x) (Verifier.zero,initialScratch t.wires.length)
  let publicInputBinding := t.bindings.foldl (fun acc b => Verifier.add acc (piSource t b x)) Verifier.zero
  pure (Verifier.add result.1 (Verifier.mul p.challenges.xi publicInputBinding))

theorem round_sum_at_shaped (t : Tables) (p : Prepared) (x : Element) (h : Shape t p)
    (hr : 0 < t.remaining) :
    roundSumAt t p x = some (roundValue t p x) := by
  have _ := hr
  obtain ⟨s',hloop,_⟩ := suffix_loop_shaped t p x h.2.2.2.2.2.2.2.1 (List.range (t.eq.length/2))
    Verifier.zero (initialScratch t.wires.length) (initial_scratch_shape _)
  simp only [roundSumAt,hloop,bind,Option.bind,pure,roundValue,pi_source_is_pi_value]

/-! ## current_round: samples at 0..=5, interpolation, omitted constant -/

/-- NORM_LOGUP_MAX_DEGREE (norm_logup.rs:24). -/
def maxDegree : Nat := 5

/-- Left-to-right `.map(..).collect()` with any panic propagated. -/
def collect : List (Option Element) → Option (List Element)
  | [] => some []
  | none :: _ => none
  | some a :: rest => (collect rest).map (a :: ·)

theorem collect_all_some {α : Type} (f : α → Element) (xs : List α) :
    collect (xs.map (fun a => some (f a))) = some (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,collect,ih,Option.map_some']

/-- The six samples (norm_logup.rs:687-692): `Field64_3::from(i as u64)` for
`i` in `0..=5` is the embedded small integer, i.e. the Nat cast. -/
def samples (t : Tables) (p : Prepared) : Option (List Element) :=
  collect ((List.range (maxDegree+1)).map (fun i : Nat => (roundSumAt t p (i : Element)).map NormPolynomial.lift))

theorem samples_shaped (t : Tables) (p : Prepared) (h : Shape t p) (hr : 0 < t.remaining) :
    samples t p = some (OuterInterpolation.samplePolynomial (roundPolynomial t p) 5) := by
  have hs : ∀ i : Nat, (roundSumAt t p (i : Element)).map NormPolynomial.lift =
      some ((roundPolynomial t p).eval (i : Element)) := by
    intro i
    rw [round_sum_at_shaped t p _ h hr,Option.map_some',← round_polynomial_same_ordered_evaluation]
    rfl
  simp only [samples,hs,maxDegree,OuterInterpolation.samplePolynomial]
  exact collect_all_some _ _

/-- ext3_evaluations_to_coefficients then `coefficients[1..].to_vec()`
(norm_logup.rs:693-696). Interpolation is the adopted source-ordered Gaussian
model; a sample panic, the empty-input assert or a zero pivot is `none`. -/
def computeRound (t : Tables) (p : Prepared) : Option (List Element) := do
  let evaluations ← samples t p
  let coefficients ← OuterInterpolation.interpolate evaluations
  pure coefficients.tail

theorem compute_round_exact (t : Tables) (p : Prepared) (evaluations coefficients : List Element)
    (hs : samples t p = some evaluations) (hi : OuterInterpolation.interpolate evaluations = some coefficients) :
    computeRound t p = some coefficients.tail := by
  simp only [computeRound,hs,hi,bind,Option.bind,pure]

theorem sample_count_is_degree_plus_one (t : Tables) (p : Prepared) (h : Shape t p)
    (hr : 0 < t.remaining) :
    ∃ evaluations, samples t p = some evaluations ∧ evaluations.length = maxDegree+1 :=
  ⟨_,samples_shaped t p h hr,OuterInterpolation.sample_count _ _⟩

/-- The full interpolated coefficient list IS the round polynomial; the sent
message is its tail, with exactly five entries. -/
theorem current_round_coefficients_shaped (t : Tables) (p : Prepared) (h : Shape t p)
    (hr : 0 < t.remaining) :
    ∃ coefficients, OuterInterpolation.interpolate (OuterInterpolation.samplePolynomial (roundPolynomial t p) 5) =
        some coefficients ∧
      WhirPolynomial.ofCoefficients coefficients = roundPolynomial t p ∧
      computeRound t p = some coefficients.tail ∧ coefficients.tail.length = 5 := by
  obtain ⟨coefficients,hi,hpoly,hlen⟩ :=
    OuterInterpolationTotal.norm_degree_five_total (roundPolynomial t p) (round_polynomial_degree_five t p)
  exact ⟨coefficients,hi,hpoly,compute_round_exact t p _ coefficients (samples_shaped t p h hr) hi,hlen⟩

/-- The omitted entry is the constant coefficient of the round polynomial and
is exactly what the verifier's half-sum reconstruction recovers from the
sent tail and the honest endpoint sum. -/
theorem omitted_constant_coefficient (t : Tables) (p : Prepared) (h : Shape t p)
    (hr : 0 < t.remaining) :
    ∃ coefficients : List Element, computeRound t p = some coefficients.tail ∧
      coefficients.getD 0 0 = (roundPolynomial t p).coeff 0 ∧
      OuterRound.constantCoefficient ((roundPolynomial t p).eval 0+(roundPolynomial t p).eval 1) coefficients.tail =
        coefficients.getD 0 0 := by
  obtain ⟨coefficients,_,hpoly,hround,hlen⟩ := current_round_coefficients_shaped t p h hr
  refine ⟨coefficients,hround,?_,?_⟩
  · rw [← hpoly,WhirPolynomial.coefficient_exact]
  · cases coefficients with
    | nil => simp at hlen
    | cons a rest =>
        rw [← hpoly]
        exact OuterInterpolation.reconstruct_constant_from_full_coefficients a rest

/-- Honest message generation composes with the ACTUAL verifier round
evaluation: with the endpoint sum as claim, the verifier's reconstruction of
the sent five coefficients evaluates to round_sum_at at every challenge. -/
theorem sent_round_evaluates_as_verifier (t : Tables) (p : Prepared) (h : Shape t p)
    (hr : 0 < t.remaining) :
    ∃ message, computeRound t p = some message ∧ message.length = 5 ∧
      ∀ r : Element, Verifier.evaluateRound (Verifier.add (roundValue t p 0) (roundValue t p 1))
        (message.map Element.toVerifier) r.toVerifier = roundValue t p r := by
  obtain ⟨coefficients,hi,hlen,hev⟩ := OuterInterpolationTotal.total_sample_actual_outer_round
    (roundPolynomial t p) 5 (by decide) (round_polynomial_degree_five t p)
  refine ⟨coefficients.tail,compute_round_exact t p _ coefficients (samples_shaped t p h hr) hi,hlen,?_⟩
  intro r
  have := hev r
  rw [add_exact,round_polynomial_same_ordered_evaluation,round_polynomial_same_ordered_evaluation,
    round_polynomial_same_ordered_evaluation] at this
  exact this

/-! ## bind: PI prefix update and every table's adjacent-pair binding -/

/-- `prefix_eq *= if bit == 0 { ONE - challenge } else { challenge }` with
`bit = (row >> bound_variables) & 1` (norm_logup.rs:543-550). -/
def prefixUpdate (t : Tables) (b : Binding) (challenge : Element) : Element :=
  b.prefixEq * if (b.row >>> t.boundVariables) &&& 1 = 0 then 1-challenge else challenge

theorem prefix_update_is_pi_factor (t : Tables) (b : Binding) (challenge : Element) :
    prefixUpdate t b challenge = piFactor t b challenge := by
  simp only [prefixUpdate,piFactor,Nat.shiftRight_eq_div_pow,Nat.and_one_is_mod]

theorem prefix_update_is_boolean_factor (t : Tables) (b : Binding) (challenge : Element) :
    (prefixUpdate t b challenge).toVerifier =
      Verifier.mul b.prefixEq.toVerifier (Norm.booleanFactor b.row t.boundVariables challenge.toVerifier) := by
  rw [prefix_update_is_pi_factor,piFactor,mul_exact,Norm.booleanFactor]
  by_cases hc : b.row / 2^t.boundVariables % 2 = 0
  · rw [if_pos hc,if_pos hc]
    rfl
  · rw [if_neg hc,if_neg hc]

/-- bind (norm_logup.rs:542-563): PI prefixes first (with the OLD
`bound_variables`), then `bound_variables += 1`, then every table is bound
by the indexed adjacent-pair loop. Every table's `num_vars > 0` assert is the
single shared `remaining ≠ 0` check. -/
def bindTables (t : Tables) (challenge : Element) : Option Tables :=
  if t.remaining = 0 then none else some
    { eq := DenseMleIndexed.bindBuffer t.eq challenge,
      subgroup := DenseMleIndexed.bindBuffer t.subgroup challenge,
      wires := t.wires.map (fun column => DenseMleIndexed.bindBuffer column challenge),
      sigmas := t.sigmas.map (fun column => DenseMleIndexed.bindBuffer column challenge),
      identityHelpers := t.identityHelpers.map (fun column => DenseMleIndexed.bindBuffer column challenge),
      sigmaHelpers := t.sigmaHelpers.map (fun column => DenseMleIndexed.bindBuffer column challenge),
      bindings := t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b challenge }),
      boundVariables := t.boundVariables+1,
      remaining := t.remaining-1 }

theorem bind_tables_exhausted (t : Tables) (challenge : Element) (h : t.remaining = 0) :
    bindTables t challenge = none := by simp [bindTables,h]

/-- Each per-table bind is exactly the adopted `bindVariable` on the
`⟨remaining, column⟩` state (ext3.rs:47-68). -/
theorem bind_column_is_adopted_binding (t : Tables) (column : List Element) (challenge : Element)
    (hr : 0 < t.remaining) :
    DenseMleIndexed.bindVariable ⟨t.remaining,column⟩ challenge =
      some ⟨t.remaining-1,DenseMleIndexed.bindBuffer column challenge⟩ :=
  DenseMleIndexed.positive_binding_exact _ _ hr

/-- The bound cell at `suffix` is the next round's line at the challenge. -/
theorem bound_cell_is_round_line (column : List Element) (suffix : Nat) (challenge : Element)
    (h : suffix < column.length/2) :
    (DenseMleIndexed.bindBuffer column challenge).getD suffix 0 = line column suffix challenge :=
  (line_same_actual_binding column suffix challenge h).symm

theorem half_pow (n : Nat) : 2^(n+1)/2 = 2^n := by
  rw [Nat.pow_succ]
  exact Nat.mul_div_cancel _ (by decide)

theorem bound_columns_shape (columns : List (List Element)) (width n : Nat) (challenge : Element)
    (h : ColumnShape columns width (2^(n+1))) :
    ColumnShape (columns.map (fun column => DenseMleIndexed.bindBuffer column challenge)) width (2^n) := by
  refine ⟨by rw [List.length_map,h.1],?_⟩
  intro column hc
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hc
  rw [DenseMleIndexed.bind_buffer_length,h.2 original ho,half_pow]

theorem bind_tables_shaped (t : Tables) (p : Prepared) (challenge : Element)
    (h : Shape t p) (hr : 0 < t.remaining) :
    ∃ t', bindTables t challenge = some t' ∧ Shape t' p ∧
      t'.remaining+1 = t.remaining ∧ t'.boundVariables = t.boundVariables+1 ∧
      t'.wires.length = t.wires.length ∧
      t'.bindings = t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b challenge }) := by
  obtain ⟨n,hn⟩ : ∃ n, t.remaining = n+1 := ⟨t.remaining-1,by omega⟩
  rcases h with ⟨he,hg,hw,hsig,hi,hh,hk,hl,hb⟩
  simp only [bindTables,if_neg (show t.remaining ≠ 0 by omega)]
  refine ⟨_,rfl,?_,by dsimp; omega,rfl,List.length_map _ _,rfl⟩
  rw [hn] at he hg hw hsig hi hh hb
  have hwl : (t.wires.map (fun column => DenseMleIndexed.bindBuffer column challenge)).length = t.wires.length :=
    List.length_map _ _
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp; rw [DenseMleIndexed.bind_buffer_length,he,hn,Nat.add_sub_cancel,half_pow]
  · dsimp; rw [DenseMleIndexed.bind_buffer_length,hg,hn,Nat.add_sub_cancel,half_pow]
  · dsimp; rw [hwl,hn,Nat.add_sub_cancel]; exact bound_columns_shape _ _ n challenge hw
  · dsimp; rw [hwl,hn,Nat.add_sub_cancel]; exact bound_columns_shape _ _ n challenge hsig
  · dsimp; rw [hwl,hn,Nat.add_sub_cancel]; exact bound_columns_shape _ _ n challenge hi
  · dsimp; rw [hwl,hn,Nat.add_sub_cancel]; exact bound_columns_shape _ _ n challenge hh
  · dsimp; rw [hwl]; exact hk
  · dsimp; rw [hwl]; exact hl
  · dsimp
    intro b' hb'
    obtain ⟨b,hbm,rfl⟩ := List.mem_map.mp hb'
    have := hb b hbm
    dsimp at this ⊢
    rw [hwl,hn,Nat.add_sub_cancel]
    refine ⟨?_,this.2⟩
    have hexp : t.boundVariables+1+n = t.boundVariables+(n+1) := by omega
    rw [hexp]
    exact this.1

/-- The prefix after one bind is the verifier's booleanRowEq factor product
extended by the new coordinate (Norm.booleanRowEq over the bound point). -/
theorem boolean_row_eq_append (row : Nat) (point : List Verifier.Ext3) (c : Verifier.Ext3) :
    Norm.booleanRowEq row (point ++ [c]) =
      Verifier.mul (Norm.booleanRowEq row point) (Norm.booleanFactor row point.length c) := by
  simp only [Norm.booleanRowEq,List.enum_append,Norm.productLoop,List.foldl_append,List.enumFrom_cons,
    List.enumFrom_nil,List.foldl_cons,List.foldl_nil]

theorem bound_prefix_is_boolean_row_eq (t : Tables) (b : Binding) (challenge : Element)
    (point : List Element) (hl : point.length = t.boundVariables)
    (hb : b.prefixEq.toVerifier = Norm.booleanRowEq b.row (point.map Element.toVerifier)) :
    (prefixUpdate t b challenge).toVerifier =
      Norm.booleanRowEq b.row ((point ++ [challenge]).map Element.toVerifier) := by
  rw [List.map_append,List.map_singleton,boolean_row_eq_append,List.length_map,hl,
    prefix_update_is_boolean_factor,hb]

/-! ## The constructor's public-input bindings -/

/-- from_base's binding construction (norm_logup.rs:446-460): running eta
power from ONE, `prefix_eq: ONE`. -/
def buildBindings (eta : Element) : Element → List (Nat × Nat × Verifier.Base) → List Binding
  | _,[] => []
  | power,(row,column,value)::rest =>
      ⟨row,column,value,power,1⟩ :: buildBindings eta (power*eta) rest

theorem build_bindings_length (eta power : Element) (pairs : List (Nat × Nat × Verifier.Base)) :
    (buildBindings eta power pairs).length = pairs.length := by
  induction pairs generalizing power with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨_,_,_⟩ := pair
      simp only [buildBindings,List.length_cons,ih]

theorem initial_prefix_is_one (eta power : Element) (pairs : List (Nat × Nat × Verifier.Base)) :
    ∀ b ∈ buildBindings eta power pairs, b.prefixEq = 1 := by
  induction pairs generalizing power with
  | nil => intro b hb; simp [buildBindings] at hb
  | cons pair rest ih =>
      obtain ⟨row,column,value⟩ := pair
      intro b hb
      simp only [buildBindings,List.mem_cons] at hb
      rcases hb with rfl|hb
      · rfl
      · exact ih _ b hb

theorem build_bindings_row_column (eta power : Element) (pairs : List (Nat × Nat × Verifier.Base)) :
    ∀ b ∈ buildBindings eta power pairs, (b.row,b.column,b.publicValue) ∈ pairs := by
  induction pairs generalizing power with
  | nil => intro b hb; simp [buildBindings] at hb
  | cons pair rest ih =>
      obtain ⟨row,column,value⟩ := pair
      intro b hb
      simp only [buildBindings,List.mem_cons] at hb
      rcases hb with rfl|hb
      · simp
      · exact List.mem_cons_of_mem _ (ih _ b hb)

/-- The i-th binding carries `power * eta^i`; from ONE this is the fixed
`eta^i` weight of the adopted PiLine model. -/
theorem build_bindings_eta_power (eta : Element) (pairs : List (Nat × Nat × Verifier.Base)) :
    ∀ (power : Element) (i : Nat), i < pairs.length →
      ((buildBindings eta power pairs).getD i ⟨0,0,baseZero,0,0⟩).etaPower = power*eta^i := by
  induction pairs with
  | nil => intro power i hi; simp at hi
  | cons pair rest ih =>
      obtain ⟨row,column,value⟩ := pair
      intro power i hi
      cases i with
      | zero => simp [buildBindings]
      | succ i =>
          simp only [buildBindings,List.getD_cons_succ]
          rw [ih (power*eta) i (by simpa using hi),pow_succ]
          ring

theorem initial_prefix_provenance (eta : Element) (pairs : List (Nat × Nat × Verifier.Base)) :
    ∀ b ∈ buildBindings eta 1 pairs,
      b.prefixEq.toVerifier = Norm.booleanRowEq b.row (([] : List Element).map Element.toVerifier) := by
  intro b hb
  rw [initial_prefix_is_one eta 1 pairs b hb]
  rfl

/-! ## Read bounds -/

theorem column_at_shape (columns : List (List Element)) (width length j : Nat)
    (h : ColumnShape columns width length) (hj : j<width) :
    j<columns.length ∧ (columnAt columns j).length=length := by
  refine ⟨by rw [h.1]; exact hj,?_⟩
  unfold columnAt
  rw [List.getD_eq_get _ _ (by rw [h.1]; exact hj)]
  exact h.2 _ (List.get_mem _ _ _)

theorem even_power_two (remaining : Nat) (h : 0<remaining) :
    2^remaining=2*(2^remaining/2) := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (show remaining≠0 by omega)
  simp [hn,Nat.pow_succ,Nat.mul_comm]

theorem adjacent_reads_bounded (column : List Element) (remaining suffix : Nat)
    (hlen : column.length=2^remaining) (hr : 0<remaining) (hs : suffix<2^remaining/2) :
    2*suffix<column.length ∧ 2*suffix+1<column.length := by
  have h := even_power_two remaining hr
  rw [hlen]
  omega

/-- Every index of the scratch loops (`self.wires[j]`, `self.sigmas[j]`,
`self.inverse_identity[j]`, `self.inverse_sigma[j]`, `prepared.k_is[j]`,
`prepared.lambda_powers[j]`) and every adjacent line_value read of the suffix
loop is in bounds. -/
theorem routed_reads_bounded (t : Tables) (p : Prepared) (suffix j : Nat)
    (h : Shape t p) (hr : 0<t.remaining)
    (hs : suffix<t.eq.length/2) (hj : j<t.wires.length) :
    j<t.sigmas.length ∧ j<t.identityHelpers.length ∧ j<t.sigmaHelpers.length ∧
    j<p.kIs.length ∧ j<p.lambdaPowers.length ∧
    (∀ column ∈ [columnAt t.wires j,columnAt t.sigmas j,
      columnAt t.identityHelpers j,columnAt t.sigmaHelpers j,t.eq,t.subgroup],
      2*suffix<column.length ∧ 2*suffix+1<column.length) := by
  rcases h with ⟨he,hg,hw,hsig,hi,ht,hk,hl,_⟩
  have a := column_at_shape _ _ _ j hw hj
  have b := column_at_shape _ _ _ j hsig hj
  have c := column_at_shape _ _ _ j hi hj
  have d := column_at_shape _ _ _ j ht hj
  refine ⟨b.1,c.1,d.1,by omega,by omega,?_⟩
  intro column hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
    apply adjacent_reads_bounded _ t.remaining suffix (by first | assumption | exact a.2 | exact b.2 | exact c.2 | exact d.2) hr (by simpa only [he] using hs)

/-- The scratch writes `scratch[j]` hit an existing cell of each
`vec![ZERO; wires.len()]`. -/
theorem scratch_writes_bounded (t : Tables) (s : Scratch) (j : Nat)
    (hs : ScratchShape t.wires.length s) (hj : j<t.wires.length) :
    j<s.wires.length ∧ j<s.sigmas.length ∧ j<s.identityHelpers.length ∧ j<s.sigmaHelpers.length := by
  rcases hs with ⟨h1,h2,h3,h4⟩
  omega

theorem pi_suffix_in_range (t : Tables) (b : Binding) (remaining : Nat)
    (hr : 0<remaining) (hb : b.row<2^(t.boundVariables+remaining)) :
    piSuffix t b < 2^remaining/2 := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (show remaining≠0 by omega)
  subst remaining
  have hp : 0<2^(t.boundVariables+1) := by positivity
  have hexp : 2^(t.boundVariables+(n+1)) = 2^n * 2^(t.boundVariables+1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hexp] at hb
  have hdiv : b.row / 2^(t.boundVariables+1)<2^n := (Nat.div_lt_iff_lt_mul hp).mpr hb
  simpa [piSuffix,Nat.pow_succ] using hdiv

/-- `self.wires[binding.column]` and both adjacent reads of the PI line are in
bounds, and the PI suffix is one of the Boolean suffixes of the round. -/
theorem pi_reads_bounded (t : Tables) (p : Prepared) (b : Binding)
    (h : Shape t p) (hr : 0<t.remaining) (hb : b ∈ t.bindings) :
    b.column<t.wires.length ∧ piSuffix t b<t.eq.length/2 ∧
    2*piSuffix t b<(columnAt t.wires b.column).length ∧
      2*piSuffix t b+1<(columnAt t.wires b.column).length := by
  have hbinding := h.2.2.2.2.2.2.2.2 b hb
  have hs := pi_suffix_in_range t b t.remaining hr hbinding.1
  have hc := column_at_shape _ _ _ b.column h.2.2.1 hbinding.2
  exact ⟨hbinding.2,by simpa only [h.1] using hs,
    adjacent_reads_bounded _ t.remaining _ hc.2 hr hs⟩

/-- The source PI loop's shifted suffix is the same bounded suffix. -/
theorem pi_source_reads_bounded (t : Tables) (p : Prepared) (b : Binding)
    (h : Shape t p) (hr : 0<t.remaining) (hb : b ∈ t.bindings) :
    2*(b.row >>> (t.boundVariables+1))<(columnAt t.wires b.column).length ∧
      2*(b.row >>> (t.boundVariables+1))+1<(columnAt t.wires b.column).length := by
  rw [pi_suffix_shift_is_same]
  exact (pi_reads_bounded t p b h hr hb).2.2

/-! ## NormLogupProverState: current_round and bind_challenge -/

/-- NormLogupProverStateError (norm_logup.rs:568-580). -/
inductive StateError where
  | roundNotComputed (round : Nat)
  | noRoundsRemaining
  | incomplete (completedRounds totalRounds : Nat)

/-- `panic` is an assert/expect failure inside the call; `error` is the
returned `Err`. -/
inductive Outcome (α : Type) where
  | panic
  | error (e : StateError)
  | ok (value : α)

/-- NormLogupProverState (norm_logup.rs:607-614). -/
structure ProverState where
  tables : Tables
  prepared : Prepared
  totalRounds : Nat
  completedRounds : List (List Element)
  pendingRound : Option (List Element)
  point : List Element

/-- is_complete (norm_logup.rs:726-728). -/
def isComplete (s : ProverState) : Prop := s.completedRounds.length = s.totalRounds

instance (s : ProverState) : Decidable (isComplete s) := by unfold isComplete; infer_instance

/-- current_round (norm_logup.rs:682-703). -/
def currentRound (s : ProverState) : Outcome (List Element × ProverState) :=
  if isComplete s then .error .noRoundsRemaining else
  match s.pendingRound with
  | some round => .ok (round,s)
  | none =>
    match computeRound s.tables s.prepared with
    | none => .panic
    | some round => .ok (round,{ s with pendingRound := some round })

/-- bind_challenge (norm_logup.rs:707-723). -/
def bindChallenge (s : ProverState) (challenge : Element) : Outcome ProverState :=
  if isComplete s then .error .noRoundsRemaining else
  match s.pendingRound with
  | none => .error (.roundNotComputed s.completedRounds.length)
  | some round =>
    match bindTables s.tables challenge with
    | none => .panic
    | some tables =>
      .ok { s with
            tables := tables
            completedRounds := s.completedRounds ++ [round]
            pendingRound := none
            point := s.point ++ [challenge] }

/-- into_proof_and_point (norm_logup.rs:744-758). -/
def intoProofAndPoint (s : ProverState) : Outcome (List (List Element) × List Element) :=
  if isComplete s then .ok (s.completedRounds,s.point)
  else .error (.incomplete s.completedRounds.length s.totalRounds)

/-- The constructor's counters (new_with_public_inputs 643-680: `total_rounds
= tau.len()`, empty completed rounds and point, `bound_variables = 0`) as
they stand after any number of binds, together with the table shape. -/
def Consistent (s : ProverState) : Prop :=
  s.completedRounds.length = s.tables.boundVariables ∧
  s.totalRounds = s.tables.boundVariables + s.tables.remaining ∧
  s.point.length = s.tables.boundVariables ∧
  Shape s.tables s.prepared

/-- new_with_public_inputs (norm_logup.rs:644-680): `total_rounds = tau.len()`,
no completed rounds, no pending round, empty point. -/
def initialState (t : Tables) (p : Prepared) : ProverState :=
  ⟨t,p,t.remaining,[],none,[]⟩

theorem initial_consistent (t : Tables) (p : Prepared) (h : Shape t p) (h0 : t.boundVariables = 0) :
    Consistent (initialState t p) :=
  ⟨by simp [initialState,h0],by simp [initialState,h0],by simp [initialState,h0],h⟩

theorem incomplete_means_variables_remain (s : ProverState) (hc : Consistent s) (hn : ¬isComplete s) :
    0 < s.tables.remaining := by
  unfold isComplete at hn
  rcases hc with ⟨h1,h2,_,_⟩
  omega

theorem complete_means_no_variables_remain (s : ProverState) (hc : Consistent s) (h : isComplete s) :
    s.tables.remaining = 0 := by
  unfold isComplete at h
  rcases hc with ⟨h1,h2,_,_⟩
  omega

theorem current_round_after_completion (s : ProverState) (h : isComplete s) :
    currentRound s = .error .noRoundsRemaining := by
  simp [currentRound,h]

theorem current_round_cached (s round : _) (h : s.pendingRound = some round) (hn : ¬isComplete s) :
    currentRound s = .ok (round,s) := by
  simp [currentRound,h,hn]

/-- Repeated calls before binding return the same round and do not advance
the algebraic state. -/
theorem current_round_idempotent (s s' : ProverState) (message : List Element)
    (h : currentRound s = .ok (message,s')) : currentRound s' = .ok (message,s') := by
  unfold currentRound at h
  split at h
  · cases h
  · rename_i hn
    split at h
    · rename_i hr
      cases h
      simp [currentRound,hr,hn]
    · split at h
      · cases h
      · rename_i hr
        cases h
        simp only [isComplete] at hn
        simp [currentRound,isComplete,hn]

/-- A fresh incomplete consistent state computes exactly the five-coefficient
tail, caches it, and the sent message reconstructs round_sum_at through the
actual verifier evaluation. -/
theorem current_round_shaped (s : ProverState) (hc : Consistent s) (hn : ¬isComplete s)
    (hp : s.pendingRound = none) :
    ∃ message, currentRound s = .ok (message,{ s with pendingRound := some message }) ∧
      message.length = 5 ∧
      ∀ r : Element, Verifier.evaluateRound
        (Verifier.add (roundValue s.tables s.prepared 0) (roundValue s.tables s.prepared 1))
        (message.map Element.toVerifier) r.toVerifier = roundValue s.tables s.prepared r := by
  obtain ⟨message,hm,hlen,hev⟩ := sent_round_evaluates_as_verifier s.tables s.prepared hc.2.2.2
    (incomplete_means_variables_remain s hc hn)
  refine ⟨message,?_,hlen,hev⟩
  simp [currentRound,hn,hp,hm]

/-- Every table read of a computed round is in bounds when the state is
consistent and incomplete (the only situation in which round_sum_at runs). -/
theorem current_round_reads_bounded (s : ProverState) (hc : Consistent s) (hn : ¬isComplete s) :
    (∀ suffix j, suffix<s.tables.eq.length/2 → j<s.tables.wires.length →
      j<s.tables.sigmas.length ∧ j<s.tables.identityHelpers.length ∧ j<s.tables.sigmaHelpers.length ∧
      j<s.prepared.kIs.length ∧ j<s.prepared.lambdaPowers.length ∧
      (∀ column ∈ [columnAt s.tables.wires j,columnAt s.tables.sigmas j,
        columnAt s.tables.identityHelpers j,columnAt s.tables.sigmaHelpers j,s.tables.eq,s.tables.subgroup],
        2*suffix<column.length ∧ 2*suffix+1<column.length)) ∧
    (∀ b ∈ s.tables.bindings, b.column<s.tables.wires.length ∧ piSuffix s.tables b<s.tables.eq.length/2 ∧
      2*piSuffix s.tables b<(columnAt s.tables.wires b.column).length ∧
        2*piSuffix s.tables b+1<(columnAt s.tables.wires b.column).length) := by
  have hr := incomplete_means_variables_remain s hc hn
  exact ⟨fun suffix j hs hj => routed_reads_bounded s.tables s.prepared suffix j hc.2.2.2 hr hs hj,
    fun b hb => pi_reads_bounded s.tables s.prepared b hc.2.2.2 hr hb⟩

theorem bind_after_completion (s : ProverState) (challenge : Element) (h : isComplete s) :
    bindChallenge s challenge = .error .noRoundsRemaining := by
  simp [bindChallenge,h]

theorem bind_without_round (s : ProverState) (challenge : Element) (hn : ¬isComplete s)
    (hp : s.pendingRound = none) :
    bindChallenge s challenge = .error (.roundNotComputed s.completedRounds.length) := by
  simp [bindChallenge,hn,hp]

/-- Binding a computed round on a consistent state succeeds, appends exactly
that round and challenge, clears the cache, and keeps the state consistent
with one fewer variable. -/
theorem bind_challenge_consistent (s : ProverState) (challenge : Element) (round : List Element)
    (hc : Consistent s) (hn : ¬isComplete s) (hp : s.pendingRound = some round) :
    ∃ s', bindChallenge s challenge = .ok s' ∧ Consistent s' ∧
      s'.completedRounds = s.completedRounds ++ [round] ∧ s'.point = s.point ++ [challenge] ∧
      s'.pendingRound = none ∧ s'.prepared = s.prepared ∧ s'.totalRounds = s.totalRounds ∧
      s'.tables.remaining+1 = s.tables.remaining ∧
      s'.tables.bindings = s.tables.bindings.map (fun b => { b with prefixEq := prefixUpdate s.tables b challenge }) := by
  have hr := incomplete_means_variables_remain s hc hn
  obtain ⟨t',ht,hshape,hrem,hbound,_,hbind⟩ := bind_tables_shaped s.tables s.prepared challenge hc.2.2.2 hr
  simp only [bindChallenge,if_neg hn,hp,ht]
  refine ⟨_,rfl,?_,rfl,rfl,rfl,rfl,rfl,hrem,hbind⟩
  rcases hc with ⟨h1,h2,h3,_⟩
  refine ⟨?_,?_,?_,hshape⟩
  · dsimp; rw [List.length_append,List.length_singleton,hbound,h1]
  · dsimp; omega
  · dsimp; rw [List.length_append,List.length_singleton,hbound,h3]

/-- Every PI prefix equals the verifier's booleanRowEq of its row over the
bound point so far; preserved by bind_challenge. -/
def PrefixProvenance (s : ProverState) : Prop :=
  ∀ b ∈ s.tables.bindings, b.prefixEq.toVerifier = Norm.booleanRowEq b.row (s.point.map Element.toVerifier)

theorem initial_state_prefix_provenance (t : Tables) (p : Prepared) (eta : Element)
    (pairs : List (Nat × Nat × Verifier.Base)) (hb : t.bindings = buildBindings eta 1 pairs) :
    PrefixProvenance (initialState t p) := by
  intro b hbm
  simp only [initialState] at hbm ⊢
  rw [hb] at hbm
  exact initial_prefix_provenance eta pairs b hbm

theorem bind_preserves_prefix_provenance (s s' : ProverState) (challenge : Element)
    (hc : Consistent s) (hpp : PrefixProvenance s) (h : bindChallenge s challenge = .ok s') :
    PrefixProvenance s' := by
  unfold bindChallenge at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i tables ht
        cases h
        intro b' hb'
        unfold bindTables at ht
        split at ht
        · cases ht
        · simp only [Option.some.injEq] at ht
          subst ht
          dsimp at hb' ⊢
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hb'
          exact bound_prefix_is_boolean_row_eq s.tables b challenge s.point hc.2.2.1 (hpp b hb)

theorem proof_extraction_requires_completion (s : ProverState) (h : ¬isComplete s) :
    intoProofAndPoint s = .error (.incomplete s.completedRounds.length s.totalRounds) := by
  simp [intoProofAndPoint,h]

theorem proof_extraction_exact (s : ProverState) (h : isComplete s) :
    intoProofAndPoint s = .ok (s.completedRounds,s.point) := by
  simp [intoProofAndPoint,h]

end Audit.Wire3.NormDenseRound
