import Audit.Wire3.GateAggregatePolynomial

/-!
Ordered Boolean-suffix accumulation using the SAME all-fourteen executable
gate aggregate, constants/publicHash/alpha and challenge x for every suffix.
The captured inputs are real adjacent table reads at 2*s and 2*s+1; every
interpolation and field sum below is executable, not an evaluator observation.

This corresponds to the per-integer inner accumulator of
gate_ext3_v2.rs::current_round:106-137, with Boolean suffix indices represented
by 0..2^remaining-1. The exact Lean boundary is GatesComplete, not the Rust
slot-first/forward-power evaluator. Its algebraic/source refinement and the
full mutable grid loop transpose, DenseMle/prover-state table extraction,
authenticated endpoint/equality-table provenance, coefficient interpolation,
bind_challenge, circuit truth and PCS/Fiat-Shamir remain explicitly separate.
-/
namespace Audit.Wire3.GateSuffixPolynomial
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateAggregatePolynomial Polynomial

structure Slice where
  wires : List (Element × Element)
  constants : List (Element × Element)
  eqLeft : Element
  eqRight : Element

def Widths (c : Gates.Config) (s : Slice) : Prop :=
  s.wires.length=c.numWires ∧ s.constants.length=c.numConstants

def evalSlice (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha x : Element) (s : Slice) : Option Verifier.Ext3 :=
  evaluateWeighted c gates s.wires s.constants publicHash alpha s.eqLeft s.eqRight x

noncomputable def slicePolynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : Slice) : Option P := do
  let gate ← evaluatePolynomial c gates (affineColumns s.wires) (affineColumns s.constants) publicHash alpha
  pure (affine s.eqLeft s.eqRight*gate)

theorem slice_polynomial_complete (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : Slice)
    (hv : Gates.validateConfiguration c gates=some ()) (hs : Widths c s) :
    ∃ p : P, slicePolynomial c gates publicHash alpha s=some p ∧ p.natDegree ≤ c.quotientDegree+2 ∧
      ∀ x, evalSlice c gates publicHash alpha x s=some (value p x) := by
  obtain ⟨gate,hp,hd,he⟩ := configured_affine_aggregate c gates s.wires s.constants publicHash alpha hv hs.1 hs.2
  simp only [affine_columns_actual_values] at he
  refine ⟨affine s.eqLeft s.eqRight*gate,?_,?_,?_⟩
  · simp only [slicePolynomial,hp,bind,Option.bind,pure,Option.pure_def]
  · exact (mul_degree_bound _ _ 1 (c.quotientDegree+1) (affine_degree _ _) hd).trans (by omega)
  · intro x
    simp only [evalSlice,evaluateWeighted,he,bind,Option.bind,pure,Option.pure_def,
      value_mul,affine_actual_arithmetic,affineWeight]

def sumSuffixes (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha x : Element) : List Slice → Verifier.Ext3 → Option Verifier.Ext3
  | [],accumulated => some accumulated
  | s::rest,accumulated => do
      let term ← evalSlice c gates publicHash alpha x s
      sumSuffixes c gates publicHash alpha x rest (Verifier.add accumulated term)

noncomputable def sumSuffixPolys (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) : List Slice → P → Option P
  | [],accumulated => some accumulated
  | s::rest,accumulated => do
      let term ← slicePolynomial c gates publicHash alpha s
      sumSuffixPolys c gates publicHash alpha rest (accumulated+term)

theorem suffix_sum_polynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (slices : List Slice) (accumulated : P)
    (hv : Gates.validateConfiguration c gates=some ()) (hs : ∀ s ∈ slices, Widths c s)
    (ha : accumulated.natDegree ≤ c.quotientDegree+2) :
    ∃ p : P, sumSuffixPolys c gates publicHash alpha slices accumulated=some p ∧
      p.natDegree ≤ c.quotientDegree+2 ∧
      ∀ x, sumSuffixes c gates publicHash alpha x slices (value accumulated x)=some (value p x) := by
  induction slices generalizing accumulated with
  | nil => exact ⟨accumulated,rfl,ha,fun _ => rfl⟩
  | cons s rest ih =>
      obtain ⟨term,ht,hd,he⟩ := slice_polynomial_complete c gates publicHash alpha s hv (hs s (by simp))
      have hnext := add_degree_bound accumulated term (c.quotientDegree+2) (c.quotientDegree+2) ha hd
      obtain ⟨p,hp,hdeg,heval⟩ := ih (accumulated+term) (fun s hs' => hs s (by simp [hs']))
        (by simpa only [max_self] using hnext)
      refine ⟨p,?_,hdeg,?_⟩
      · simpa only [sumSuffixPolys,ht,bind,Option.bind] using hp
      · intro x
        simpa only [sumSuffixes,he,bind,Option.bind,value_add] using heval x

structure Tables where
  wires : List (List Element)
  constants : List (List Element)
  eq : List Element

/-- Shape conditions describe the supplied tables; they do not authenticate
them or assert the equality-table contents have been derived from tau. -/
def TableShape (c : Gates.Config) (half : Nat) (t : Tables) : Prop :=
  t.wires.length=c.numWires ∧ t.constants.length=c.numConstants ∧ t.eq.length=2*half ∧
    (∀ column ∈ t.wires, column.length=2*half) ∧ (∀ column ∈ t.constants, column.length=2*half)

def captureAdjacent (columns : List (List Element)) (suffix : Nat) : List (Element × Element) :=
  columns.map (fun column => (column.getD (2*suffix) 0,column.getD (2*suffix+1) 0))

def captureSlice (t : Tables) (suffix : Nat) : Slice :=
  ⟨captureAdjacent t.wires suffix,captureAdjacent t.constants suffix,
    t.eq.getD (2*suffix) 0,t.eq.getD (2*suffix+1) 0⟩

def captureSuffixes (t : Tables) (half : Nat) : List Slice := (List.range half).map (captureSlice t)

theorem capture_adjacent_length (columns : List (List Element)) (suffix : Nat) :
    (captureAdjacent columns suffix).length=columns.length := List.length_map _ _

theorem capture_suffixes_length (t : Tables) (half : Nat) : (captureSuffixes t half).length=half := by
  simp only [captureSuffixes,List.length_map,List.length_range]

/-- Literal shared-x affine arithmetic of both actual endpoint reads. -/
theorem captured_values_exact (columns : List (List Element)) (suffix : Nat) (x : Element) :
    affineValues (captureAdjacent columns suffix) x = columns.map (fun column =>
      Verifier.add
        (Verifier.mul (Verifier.sub Norm.one x.toVerifier) (column.getD (2*suffix) 0).toVerifier)
        (Verifier.mul x.toVerifier (column.getD (2*suffix+1) 0).toVerifier)) := by
  simp only [affineValues,captureAdjacent,List.map_map,Function.comp_def,affineWeight]

theorem captured_slice_widths (c : Gates.Config) (t : Tables) (half suffix : Nat)
    (ht : TableShape c half t) : Widths c (captureSlice t suffix) := by
  simpa only [Widths,captureSlice,capture_adjacent_length] using And.intro ht.1 ht.2.1

theorem captured_all_reads_bounded (c : Gates.Config) (t : Tables) (half suffix : Nat)
    (ht : TableShape c half t) (hs : suffix < half) :
    2*suffix < t.eq.length ∧ 2*suffix+1 < t.eq.length ∧
    (∀ column ∈ t.wires, 2*suffix < column.length ∧ 2*suffix+1 < column.length) ∧
    (∀ column ∈ t.constants, 2*suffix < column.length ∧ 2*suffix+1 < column.length) := by
  refine ⟨by have := ht.2.2.1; omega,by have := ht.2.2.1; omega,?_,?_⟩
  · intro column hc
    have h := ht.2.2.2.1 column hc
    omega
  · intro column hc
    have h := ht.2.2.2.2 column hc
    omega

theorem read_at_valid_index (column : List Element) (index : Nat) (h : index < column.length) :
    column.getD index 0 = column.get ⟨index,h⟩ := List.getD_eq_get column 0 h

theorem captured_integer_half (c : Gates.Config) (t : Tables) (half : Nat) (ht : TableShape c half t) :
    t.eq.length/2=half := by rw [ht.2.2.1]; omega

def currentRoundValue (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (t : Tables) (half : Nat) : Option Verifier.Ext3 :=
  sumSuffixes c gates publicHash alpha x (captureSuffixes t half) Verifier.zero

noncomputable def currentRoundPolynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (half : Nat) : Option P :=
  sumSuffixPolys c gates publicHash alpha (captureSuffixes t half) 0

theorem captured_round_polynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (half : Nat)
    (hv : Gates.validateConfiguration c gates=some ()) (ht : TableShape c half t) :
    ∃ p : P, currentRoundPolynomial c gates publicHash alpha t half=some p ∧
      p.natDegree ≤ c.quotientDegree+2 ∧
      ∀ x, currentRoundValue c gates publicHash alpha x t half=some (value p x) := by
  obtain ⟨p,hp,hd,he⟩ := suffix_sum_polynomial c gates publicHash alpha (captureSuffixes t half) 0 hv (by
    intro s hs
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp hs
    exact captured_slice_widths c t half index ht) (by simp)
  exact ⟨p,hp,hd,fun x => by simpa only [currentRoundValue,value_zero] using he x⟩

/-- All natural-index encodings of the remaining Boolean suffixes, including
remaining=0 (one suffix). The same polynomial works at every field x. -/
theorem boolean_suffix_round_polynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (remaining : Nat)
    (hv : Gates.validateConfiguration c gates=some ()) (ht : TableShape c (2^remaining) t) :
    ∃ p : P, p.natDegree ≤ 10 ∧
      (captureSuffixes t (2^remaining)).length=2^remaining ∧ t.eq.length/2=2^remaining ∧
      ∀ x, currentRoundValue c gates publicHash alpha x t (2^remaining)=some (value p x) := by
  obtain ⟨p,_,hd,he⟩ := captured_round_polynomial c gates publicHash alpha t (2^remaining) hv ht
  have henv := (Gates.validate_configuration_success c gates hv).1
  simp only [Gates.envelope] at henv
  exact ⟨p,hd.trans (by omega),capture_suffixes_length t (2^remaining),captured_integer_half c t _ ht,he⟩

end Audit.Wire3.GateSuffixPolynomial
