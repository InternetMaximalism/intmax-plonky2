import Audit.Wire3.GatesComplete
import Audit.Wire3.WhirPolynomial
import Mathlib.Data.List.Count

/-!
# Concrete gate control-flow, affine columns and selector polynomials

Manual source correspondence: Plonky2GateEvaluatorExt3.sol:115–145,346–360;
mle/src/gate_ext3.rs:599–647; gate_ext3_v2.rs:106–137. Every checked family
uses GatesComplete's ACTUAL evaluateUnfiltered; no evaluator observation is
introduced. The zero-filter branch is erased POINTWISE, not assumed zero
or claimed identically zero because it vanished at one challenge.

Column endpoints are concrete canonical Ext3 values. BOTH wire and local-
constant/selector columns interpolate affinely in X. Metadata, public hash,
literal table entries and aggregation alpha are FIXED in X. The reducing
gate's wire-alpha is not the fixed aggregation alpha.

Symbolic Polynomial is noncomputable; the related audit arithmetic and gate
functions remain executable. This is a bridge to those functions, not a
compiler/Yul/source equivalence proof or a circuit-witness/PCS/FS theorem.
Canonical typed input and validated lengths are caller boundaries; no guards
are added to a prevalidated source path. Actual MLE endpoint provenance and
outer transcript distributions remain separate. Outer gate rounds are NOT
inner WHIR quadratic rounds or the inner 120-byte challenge.
-/
namespace Audit.Wire3.GatePolynomial
open Audit.Wire3 GoldilocksExt3Field
open Polynomial

abbrev P := Polynomial Element

def value (p : P) (x : Element) : Verifier.Ext3 := (p.eval x).toVerifier

@[simp] theorem value_zero (x : Element) : value 0 x = Verifier.zero := by simp [value]; rfl
@[simp] theorem value_one (x : Element) : value 1 x = Gates.one := by simp [value]; rfl
@[simp] theorem value_constant (a x : Element) : value (C a) x = a.toVerifier := by simp [value]
@[simp] theorem value_nat_constant (n : Nat) (x : Element) : value (C (n : Element)) x = Gates.embed n := by
  simp only [value_constant]
  rfl
@[simp] theorem value_add (p q : P) (x : Element) :
    value (p+q) x = Verifier.add (value p x) (value q x) := by simp [value]; rfl
@[simp] theorem value_sub (p q : P) (x : Element) :
    value (p-q) x = Verifier.sub (value p x) (value q x) := by simp [value]; rfl
@[simp] theorem value_mul (p q : P) (x : Element) :
    value (p*q) x = Verifier.mul (value p x) (value q x) := by simp [value]; rfl
@[simp] theorem value_scalar (p : P) (n : Nat) (x : Element) :
    value (p*C (n : Element)) x = Verifier.scalar (value p x) n := by
  rw [value_mul, value_nat_constant, Algebra.scalar_as_embedded_mul]
  rfl

/-- Erase the source optimization using its actual decoder-free evaluator
result. This lemma's execution equation is not a soundness assumption. -/
theorem actual_contribution_branch_erased (c : Gates.Config) (g : Gates.GateInfo)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (alpha : Verifier.Ext3) (terms : List Verifier.Ext3)
    (he : GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors = some terms)
    (hl : terms.length = g.numConstraints) :
    GatesComplete.contribution c g wires constants publicHash alpha =
      some (Verifier.mul
        (Gates.computeFilter g (Gates.readValue constants g.selectorIndex) (decide (1 < c.numSelectors)))
        (Gates.horner terms alpha)) := by
  unfold GatesComplete.contribution
  dsimp only
  split
  · rename_i hz
    rw [hz, Gates.zero_mul]
  · simp only [he, bind, Option.bind, hl, ↓reduceIte]

/-- ALL fourteen valid families: terms and their exact output length are
DERIVED from the existing total checked dispatcher, not supplied as an oracle. -/
theorem every_validated_family_branch_erased (c : Gates.Config) (row total : Nat)
    (g : Gates.GateInfo) (requirements : Gates.Requirements)
    (wires constants : List Verifier.Ext3) (publicHash : Nat → Verifier.Base)
    (alpha : Verifier.Ext3)
    (hv : Gates.validateGate c row total g = some requirements)
    (hw : wires.length = c.numWires) :
    ∃ terms,
      GatesComplete.evaluateUnfiltered g wires constants publicHash c.numSelectors = some terms ∧
      terms.length = g.numConstraints ∧
      GatesComplete.contribution c g wires constants publicHash alpha =
        some (Verifier.mul
          (Gates.computeFilter g (Gates.readValue constants g.selectorIndex) (decide (1 < c.numSelectors)))
          (Gates.horner terms alpha)) := by
  obtain ⟨terms, he, hl⟩ := GatesComplete.every_validated_family_evaluates
    c row total g requirements wires constants publicHash hv hw
  exact ⟨terms,he,hl,actual_contribution_branch_erased c g wires constants publicHash alpha terms he hl⟩

noncomputable def affine (left right : Element) : P := C left + X*C (right-left)

theorem affine_eval_exact (left right x : Element) :
    (affine left right).eval x = (1-x)*left+x*right := by
  simp only [affine, eval_add, eval_mul, eval_C, eval_X]
  ring

theorem affine_actual_arithmetic (left right x : Element) :
    value (affine left right) x =
      Verifier.add (Verifier.mul (Verifier.sub Norm.one x.toVerifier) left.toVerifier)
        (Verifier.mul x.toVerifier right.toVerifier) := by
  exact congrArg Element.toVerifier (affine_eval_exact left right x)

theorem affine_degree (left right : Element) : (affine left right).natDegree ≤ 1 := by
  unfold affine
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact (natDegree_mul_le (p := X) (q := C (right-left))).trans (by simp)

@[simp] theorem affine_at_zero (left right : Element) : value (affine left right) 0 = left.toVerifier := by
  simp [value, affine_eval_exact]
@[simp] theorem affine_at_one (left right : Element) : value (affine left right) 1 = right.toVerifier := by
  simp [value, affine_eval_exact]

noncomputable def affineColumns (endpoints : List (Element × Element)) : List P :=
  endpoints.map (fun pair => affine pair.1 pair.2)
def columnValues (polys : List P) (x : Element) : List Verifier.Ext3 := polys.map (fun p => value p x)
noncomputable def readPoly (polys : List P) (i : Nat) : P := polys.getD i 0

theorem column_values_preserve_length (polys : List P) (x : Element) :
    (columnValues polys x).length = polys.length := List.length_map _ _

theorem affine_columns_preserve_length (endpoints : List (Element × Element)) :
    (affineColumns endpoints).length = endpoints.length := List.length_map _ _

theorem affine_columns_have_degree_one (endpoints : List (Element × Element)) :
    ∀ p ∈ affineColumns endpoints, p.natDegree ≤ 1 := by
  intro p hp
  obtain ⟨pair,_,rfl⟩ := List.mem_map.mp hp
  exact affine_degree _ _

theorem affine_columns_at_zero (endpoints : List (Element × Element)) :
    columnValues (affineColumns endpoints) 0 = endpoints.map (fun pair => pair.1.toVerifier) := by
  simp only [columnValues, affineColumns, List.map_map, Function.comp_def, affine_at_zero]

theorem affine_columns_at_one (endpoints : List (Element × Element)) :
    columnValues (affineColumns endpoints) 1 = endpoints.map (fun pair => pair.2.toVerifier) := by
  simp only [columnValues, affineColumns, List.map_map, Function.comp_def, affine_at_one]

theorem read_poly_is_actual_read (polys : List P) (i : Nat) (x : Element) :
    value (readPoly polys i) x = Gates.readValue (columnValues polys x) i := by
  induction polys generalizing i with
  | nil => simp [readPoly, Gates.readValue, columnValues]
  | cons p ps ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

theorem read_poly_degree (polys : List P) (bound i : Nat)
    (h : ∀ p ∈ polys, p.natDegree ≤ bound) : (readPoly polys i).natDegree ≤ bound := by
  induction polys generalizing i with
  | nil => simp [readPoly]
  | cons p ps ih =>
      cases i with
      | zero => exact h p (List.mem_cons_self _ _)
      | succ i => exact ih i (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem add_degree_bound (p q : P) (a b : Nat) (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p+q).natDegree ≤ max a b := (natDegree_add_le _ _).trans (max_le_max hp hq)
theorem sub_degree_bound (p q : P) (a b : Nat) (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p-q).natDegree ≤ max a b := (natDegree_sub_le _ _).trans (max_le_max hp hq)
theorem mul_degree_bound (p q : P) (a b : Nat) (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p*q).natDegree ≤ a+b := (natDegree_mul_le).trans (Nat.add_le_add hp hq)

noncomputable def productPoly (factors : List P) (initial : P) : P := factors.foldl (· * ·) initial

theorem actual_product_eval (factors : List P) (initial : P) (x : Element) :
    value (productPoly factors initial) x =
      Gates.productFactors (columnValues factors x) (value initial x) := by
  induction factors generalizing initial with
  | nil => rfl
  | cons f fs ih =>
      simpa only [productPoly, Gates.productFactors, List.foldl_cons,
        columnValues, List.map_cons, value_mul] using ih (initial*f)

theorem product_poly_degree (factors : List P) (initial : P) (bound : Nat)
    (hi : initial.natDegree ≤ bound) (hf : ∀ f ∈ factors, f.natDegree ≤ 1) :
    (productPoly factors initial).natDegree ≤ bound+factors.length := by
  induction factors generalizing initial bound with
  | nil => simpa only [productPoly, List.foldl_nil, List.length_nil, Nat.add_zero] using hi
  | cons f fs ih =>
      have hmul := mul_degree_bound initial f bound 1 hi (hf f (List.mem_cons_self _ _))
      have ht := ih (initial*f) (bound+1) hmul (fun p hp => hf p (List.mem_cons_of_mem _ hp))
      simpa only [productPoly, List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ht

def selectorLabels (g : Gates.GateInfo) : List Nat :=
  ((List.range (g.groupEnd-g.groupStart)).map (fun i => g.groupStart+i)).filter
    (fun other => decide (other ≠ g.gateRowIndex))

noncomputable def selectorFactorsPoly (g : Gates.GateInfo) (selector : P) (many : Bool) : List P :=
  (selectorLabels g).map (fun other : Nat => C (other : Element)-selector) ++
    if many then [C (4294967295 : Element)-selector] else []

noncomputable def selectorPoly (g : Gates.GateInfo) (selector : P) (many : Bool) : P :=
  productPoly (selectorFactorsPoly g selector many) 1

theorem selector_factor_values_exact (g : Gates.GateInfo) (selector : P) (many : Bool) (x : Element) :
    columnValues (selectorFactorsPoly g selector many) x =
      Gates.selectorFactors g (value selector x) many := by
  cases many <;> simp only [columnValues, selectorFactorsPoly, Gates.selectorFactors,
    selectorLabels, List.map_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.append_nil, value_sub, value_nat_constant, Bool.false_eq_true, ↓reduceIte]
  simp only [value_constant]
  rfl

theorem selector_actual_evaluation (g : Gates.GateInfo) (selector : P) (many : Bool) (x : Element) :
    value (selectorPoly g selector many) x = Gates.computeFilter g (value selector x) many := by
  rw [selectorPoly, actual_product_eval, selector_factor_values_exact, value_one]
  rfl

theorem selector_factors_degree_one (g : Gates.GateInfo) (selector : P) (many : Bool)
    (hs : selector.natDegree ≤ 1) : ∀ f ∈ selectorFactorsPoly g selector many, f.natDegree ≤ 1 := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨n,_,rfl⟩ := List.mem_map.mp hf
    exact (natDegree_sub_le _ _).trans (by simpa only [natDegree_C, zero_le, max_eq_right] using hs)
  · cases many with
    | false => simp [selectorFactorsPoly] at hf
    | true =>
        simp only [↓reduceIte, List.mem_singleton] at hf
        subst f
        exact (natDegree_sub_le _ _).trans (by simpa only [natDegree_C, zero_le, max_eq_right] using hs)

/-- Removing the selected row removes at least one factor. An upper bound
suffices and does not assume group labels' field encodings are distinct. -/
theorem selector_label_count_bound (g : Gates.GateInfo)
    (hstart : g.groupStart ≤ g.gateRowIndex) (hend : g.gateRowIndex < g.groupEnd) :
    (selectorLabels g).length ≤ g.groupEnd-g.groupStart-1 := by
  have hm : g.gateRowIndex ∈ (List.range (g.groupEnd-g.groupStart)).map (fun i => g.groupStart+i) := by
    apply List.mem_map.mpr
    exact ⟨g.gateRowIndex-g.groupStart, List.mem_range.mpr (by omega), by omega⟩
  have hlt := (List.length_filter_lt_length_iff_exists
    (p := fun other => decide (other ≠ g.gateRowIndex))
    ((List.range (g.groupEnd-g.groupStart)).map (fun i => g.groupStart+i))).mpr
    ⟨g.gateRowIndex,hm,by simp⟩
  simp only [List.length_map, List.length_range] at hlt
  exact Nat.le_pred_of_lt hlt

theorem selector_factor_count_bound (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (hv : Gates.locationValid c row total g) :
    (selectorFactorsPoly g 0 (decide (1 < c.numSelectors))).length ≤ Gates.filterDegree c g := by
  have hl := selector_label_count_bound g (by have := hv.2.2.2.2.1; rw [hv.1]; exact this)
    (by have := hv.2.2.2.2.2; rw [hv.1]; exact this)
  simp only [selectorFactorsPoly, List.length_append, List.length_map, Gates.filterDegree]
  split <;> simp_all
  simpa only [if_neg (by omega : ¬1 < c.numSelectors), Nat.add_zero] using hl

theorem selector_poly_degree_bound (c : Gates.Config) (row total : Nat) (g : Gates.GateInfo)
    (selector : P) (hv : Gates.locationValid c row total g) (hs : selector.natDegree ≤ 1) :
    (selectorPoly g selector (decide (1 < c.numSelectors))).natDegree ≤ Gates.filterDegree c g := by
  have hp := product_poly_degree (selectorFactorsPoly g selector (decide (1 < c.numSelectors))) 1 0
    (by simp) (selector_factors_degree_one g selector _ hs)
  have hc := selector_factor_count_bound c row total g hv
  have he : (selectorFactorsPoly g selector (decide (1 < c.numSelectors))).length =
      (selectorFactorsPoly g 0 (decide (1 < c.numSelectors))).length := by
    simp only [selectorFactorsPoly, List.length_append, List.length_map]
    split <;> rfl
  simpa only [Nat.zero_add, he, selectorPoly] using hp.trans (by simpa only [Nat.zero_add, he] using hc)

noncomputable def hornerPoly (terms : List P) (alpha : Element) : P :=
  match terms with
  | [] => 0
  | term::rest => hornerPoly rest alpha * C alpha + term

theorem actual_horner_eval (terms : List P) (alpha x : Element) :
    value (hornerPoly terms alpha) x = Gates.horner (columnValues terms x) alpha.toVerifier := by
  induction terms with
  | nil => simp only [hornerPoly, value_zero, columnValues, List.map_nil,
      Gates.horner, List.reverse_nil, List.foldl_nil]
  | cons term rest ih =>
      rw [hornerPoly, value_add, value_mul, value_constant, ih]
      exact (Gates.horner_cons _ _ _).symm

theorem fixed_alpha_horner_degree (terms : List P) (alpha : Element) (bound : Nat)
    (ht : ∀ term ∈ terms, term.natDegree ≤ bound) : (hornerPoly terms alpha).natDegree ≤ bound := by
  induction terms with
  | nil => simp [hornerPoly]
  | cons term rest ih =>
      have hr := ih (fun p hp => ht p (List.mem_cons_of_mem _ hp))
      have hm := mul_degree_bound (hornerPoly rest alpha) (C alpha) bound 0 hr (by simp)
      exact (natDegree_add_le _ _).trans (max_le (by simpa using hm) (ht term (List.mem_cons_self _ _)))

end Audit.Wire3.GatePolynomial
