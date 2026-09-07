import Audit.Wire3.GateSlotCommutation
import Audit.Wire3.GateSuffixPolynomial
import Audit.Wire3.DenseMleIndexed

/-!
Rust mle/src/sumcheck/gate_ext3_v2.rs:105-134, `GateExt3ProverState::current_round`
up to, but not including, the coefficient interpolation at 136-139:
the `num_vars > 0` ensure (106), `half = eq.evaluations.len()/2` (107), the
zero-initialised `evaluations` accumulator of length `degree+1` (108), and the
transposed grid loop (112-134): outer loop over `suffix in 0..half`, inner loop
over `evaluations.iter_mut().enumerate()`, adjacent reads at `2*suffix` and
`2*suffix+1` of the eq/wire/constant tables interpolated at the integer grid
point `x = from(integer)` (114-125), the validated slot-first gate evaluator
(126-131) and the forward-power aggregate, accumulated as
`*sum += eq_value * aggregate` (132).

`gridTerm` is that iteration body with the SAME slot-first evaluator model
(GateSlotCommutation.evalPreparedSlots, gate_ext3.rs:543-608). It is proved
equal to the GatesComplete slice value of Audit.Wire3.GateSuffixPolynomial,
whose captured adjacent reads and suffix sums are reused rather than redone.
The mutable accumulator loop is modelled with the fuel/index pattern of
DenseMleIndexed.run and proved equal to a lockstep form; the suffix-outer,
integer-inner order is proved to produce, at each integer, exactly the
per-integer suffix-first sum `GateSuffixPolynomial.currentRoundValue`.
The eq table is a DenseMleIndexed.State so that the source's `num_vars`
ensure and its `half` are literal.

Not modelled here: `ext3_evaluations_to_coefficients` (136), the `degree`
constructor check (gate_ext3_v2.rs:80-83), DenseMle construction and
`bind_challenge`, transcript binding, eq-table provenance from tau, and any
Rust compiler/memory refinement. TableShape/Valid are supplied caller
invariants of the prover state, not new source runtime checks.
-/
namespace Audit.Wire3.GateSlotRound
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GatePolynomial Audit.Wire3.GateAggregatePolynomial
open Audit.Wire3.GateSlotAlgebra Audit.Wire3.GateSlotCommutation Audit.Wire3.GateSuffixPolynomial

/-- The source grid point `Field64_3::from(integer as u64)` (114). -/
def gridPoint (integer : Nat) : Element := (integer : Element)

theorem grid_point_exact (integer : Nat) : (gridPoint integer).toVerifier = Norm.embed integer :=
  nat_cast_exact integer

/-- One literal adjacent-pair read (116-125): `(ONE - x)*table[2*suffix] + x*table[2*suffix+1]`,
with the existing zero-defaulting `getD`; bounds are `captured_all_reads_bounded`. -/
def interpolateRead (column : List Element) (suffix : Nat) (x : Element) : Verifier.Ext3 :=
  Verifier.add (Verifier.mul (Verifier.sub Norm.one x.toVerifier) (column.getD (2*suffix) 0).toVerifier)
    (Verifier.mul x.toVerifier (column.getD (2*suffix+1) 0).toVerifier)

/-- The (suffix, integer) iteration body 114-132: eq/wire/constant reads, the
validated slot-first evaluator with the forward-power aggregate
(`evalPreparedSlots`), and the product `eq_value * aggregate`. `none` is the
`?` propagation of the evaluator's failure (131). -/
def gridTerm (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (t : Tables) (suffix integer : Nat) : Option Verifier.Ext3 :=
  let x := gridPoint integer
  let eqValue := interpolateRead t.eq suffix x
  let wireValues := t.wires.map (fun column => interpolateRead column suffix x)
  let constantValues := t.constants.map (fun column => interpolateRead column suffix x)
  do
    let aggregate ← evalPreparedSlots c gates wireValues constantValues publicHash alpha
    pure (Verifier.mul eqValue aggregate)

/-- The iteration body is the weighted slot-first evaluation of the captured
adjacent endpoints of GateSuffixPolynomial at the grid point. -/
theorem grid_term_weighted_slots (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (suffix integer : Nat) :
    gridTerm c gates publicHash alpha t suffix integer =
      weightedSlots c gates (captureAdjacent t.wires suffix) (captureAdjacent t.constants suffix)
        publicHash alpha (t.eq.getD (2*suffix) 0) (t.eq.getD (2*suffix+1) 0) (gridPoint integer) := by
  simp only [gridTerm,weightedSlots,captured_values_exact,interpolateRead,affineWeight]

/-- (a) at slice level: the slot-first evaluator's weighted value of any slice
equals the GateSuffixPolynomial slice value computed through GatesComplete. -/
def slotSlice (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha x : Element) (s : Slice) : Option Verifier.Ext3 :=
  weightedSlots c gates s.wires s.constants publicHash alpha s.eqLeft s.eqRight x

theorem slot_slice_equals_complete (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (s : Slice)
    (hv : Gates.validateConfiguration c gates=some ()) :
    slotSlice c gates publicHash alpha x s = evalSlice c gates publicHash alpha x s :=
  weighted_slots_equal_rows c gates s.wires s.constants publicHash alpha s.eqLeft s.eqRight x hv

/-- (a) at table level: the literal iteration body equals the GateSuffixPolynomial
slice value of the captured suffix at the grid point. -/
theorem grid_term_equals_suffix_slice (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (suffix integer : Nat)
    (hv : Gates.validateConfiguration c gates=some ()) :
    gridTerm c gates publicHash alpha t suffix integer =
      evalSlice c gates publicHash alpha (gridPoint integer) (captureSlice t suffix) := by
  rw [grid_term_weighted_slots]
  exact slot_slice_equals_complete c gates publicHash alpha (gridPoint integer) (captureSlice t suffix) hv

/-! ### The inner mutable accumulator loop (113-133) -/

/-- `for (integer, sum) in evaluations.iter_mut().enumerate() { *sum += term(integer) }`
as an indexed loop with the iteration count fixed at entry (the fuel), each
write reading the CURRENT cell; the same pattern as DenseMleIndexed.run.
`none` is the `?` propagation of a failed body. -/
def integerSweep (term : Nat → Option Verifier.Ext3) :
    Nat → Nat → List Verifier.Ext3 → Option (List Verifier.Ext3)
  | 0,_,evaluations => some evaluations
  | remaining+1,integer,evaluations => do
      let v ← term integer
      integerSweep term remaining (integer+1)
        (evaluations.set integer (Verifier.add (evaluations.getD integer Verifier.zero) v))

/-- The source loop: exactly `evaluations.len()` iterations from index 0. -/
def innerLoop (term : Nat → Option Verifier.Ext3) (evaluations : List Verifier.Ext3) :
    Option (List Verifier.Ext3) :=
  integerSweep term evaluations.length 0 evaluations

/-- Lockstep form: each cell receives its own term. -/
def integerLoop (term : Nat → Option Verifier.Ext3) : Nat → List Verifier.Ext3 → Option (List Verifier.Ext3)
  | _,[] => some []
  | integer,sum::rest => do
      let v ← term integer
      let rest' ← integerLoop term (integer+1) rest
      pure (Verifier.add sum v::rest')

theorem integer_loop_shift (term : Nat → Option Verifier.Ext3) (integer : Nat)
    (evaluations : List Verifier.Ext3) :
    integerLoop term (integer+1) evaluations = integerLoop (fun j => term (j+1)) integer evaluations := by
  induction evaluations generalizing term integer with
  | nil => rfl
  | cons sum rest ih =>
      simp only [integerLoop]
      rw [ih term (integer+1)]

theorem integer_loop_length (term : Nat → Option Verifier.Ext3) (integer : Nat)
    (evaluations result : List Verifier.Ext3)
    (h : integerLoop term integer evaluations = some result) : result.length = evaluations.length := by
  induction evaluations generalizing integer result with
  | nil => simp only [integerLoop,Option.some.injEq] at h; subst h; rfl
  | cons sum rest ih =>
      simp only [integerLoop,Option.bind_eq_bind,Option.pure_def] at h
      cases ht : term integer with
      | none => rw [ht,Option.none_bind] at h; exact Option.noConfusion h
      | some v =>
          rw [ht,Option.some_bind] at h
          cases hr : integerLoop term (integer+1) rest with
          | none => rw [hr,Option.none_bind] at h; exact Option.noConfusion h
          | some rest' =>
              rw [hr,Option.some_bind,Option.some.injEq] at h
              subst h
              simp only [List.length_cons,ih (integer+1) rest' hr]

/-- Sweeping from index `integer+1` over `head::rest` leaves `head` untouched
and is the sweep of `rest` from `integer` with the terms shifted by one. -/
theorem integer_sweep_shift (term : Nat → Option Verifier.Ext3) (remaining integer : Nat)
    (head : Verifier.Ext3) (rest : List Verifier.Ext3) :
    integerSweep term remaining (integer+1) (head::rest) =
      (integerSweep (fun j => term (j+1)) remaining integer rest).bind (fun swept => some (head::swept)) := by
  induction remaining generalizing integer rest with
  | zero => rfl
  | succ remaining ih =>
      simp only [integerSweep,List.set_cons_succ,List.getD_cons_succ,Option.bind_eq_bind]
      cases term (integer+1) with
      | none => rfl
      | some v =>
          simp only [Option.some_bind]
          exact ih (integer+1) _

/-- The executed mutable loop equals the lockstep form. -/
theorem inner_loop_lockstep (term : Nat → Option Verifier.Ext3) (evaluations : List Verifier.Ext3) :
    innerLoop term evaluations = integerLoop term 0 evaluations := by
  unfold innerLoop
  induction evaluations generalizing term with
  | nil => rfl
  | cons sum rest ih =>
      simp only [List.length_cons,integerSweep,List.set_cons_zero,List.getD_cons_zero,integerLoop,
        integer_loop_shift,Option.bind_eq_bind,Option.pure_def]
      cases term 0 with
      | none => rfl
      | some v =>
          simp only [Option.some_bind]
          rw [integer_sweep_shift,ih (fun j => term (j+1))]

/-! ### The outer suffix loop (112-134) and its transposition -/

/-- `for suffix in suffixes { inner loop }` on a shared accumulator. -/
def suffixLoop (term : Nat → Nat → Option Verifier.Ext3) :
    List Nat → List Verifier.Ext3 → Option (List Verifier.Ext3)
  | [],evaluations => some evaluations
  | suffix::rest,evaluations => do
      let next ← innerLoop (term suffix) evaluations
      suffixLoop term rest next

/-- The suffix-first sum at one integer, in suffix order, from an accumulator. -/
def suffixSum (term : Nat → Nat → Option Verifier.Ext3) (integer : Nat) :
    List Nat → Verifier.Ext3 → Option Verifier.Ext3
  | [],accumulated => some accumulated
  | suffix::rest,accumulated => do
      let v ← term suffix integer
      suffixSum term integer rest (Verifier.add accumulated v)

/-- Every integer's suffix-first sum, cell by cell. -/
def columnSums (term : Nat → Nat → Option Verifier.Ext3) (suffixes : List Nat) :
    Nat → List Verifier.Ext3 → Option (List Verifier.Ext3)
  | _,[] => some []
  | integer,accumulated::rest => do
      let v ← suffixSum term integer suffixes accumulated
      let rest' ← columnSums term suffixes (integer+1) rest
      pure (v::rest')

theorem column_sums_nil (term : Nat → Nat → Option Verifier.Ext3) (integer : Nat)
    (evaluations : List Verifier.Ext3) : columnSums term [] integer evaluations = some evaluations := by
  induction evaluations generalizing integer with
  | nil => rfl
  | cons accumulated rest ih =>
      simp only [columnSums,suffixSum,Option.bind_eq_bind,Option.pure_def,Option.some_bind,ih]

/-- One outer iteration followed by the column sums of the remaining suffixes
is the column sums including that suffix: the loop-order commutation. -/
theorem column_sums_step (term : Nat → Nat → Option Verifier.Ext3) (suffix : Nat) (rest : List Nat)
    (integer : Nat) (evaluations : List Verifier.Ext3) :
    (integerLoop (term suffix) integer evaluations).bind (columnSums term rest integer) =
      columnSums term (suffix::rest) integer evaluations := by
  induction evaluations generalizing integer with
  | nil => rfl
  | cons accumulated evaluations ih =>
      simp only [integerLoop,columnSums,suffixSum,Option.bind_eq_bind,Option.pure_def]
      cases term suffix integer with
      | none => rfl
      | some v =>
          simp only [Option.some_bind]
          rw [← ih (integer+1)]
          cases integerLoop (term suffix) (integer+1) evaluations with
          | none => cases suffixSum term integer rest (Verifier.add accumulated v) <;> rfl
          | some next => simp only [Option.some_bind,columnSums,Option.bind_eq_bind,Option.pure_def]

/-- The suffix-outer, integer-inner mutable loop computes exactly the
per-integer suffix-first sums, for any term function and any start buffer. -/
theorem suffix_loop_transposes (term : Nat → Nat → Option Verifier.Ext3) (suffixes : List Nat)
    (evaluations : List Verifier.Ext3) :
    suffixLoop term suffixes evaluations = columnSums term suffixes 0 evaluations := by
  induction suffixes generalizing evaluations with
  | nil => exact (column_sums_nil term 0 evaluations).symm
  | cons suffix rest ih =>
      rw [← column_sums_step]
      simp only [suffixLoop,inner_loop_lockstep,Option.bind_eq_bind]
      cases integerLoop (term suffix) 0 evaluations with
      | none => rfl
      | some next => simp only [Option.some_bind]; exact ih next

theorem column_sums_lookup (term : Nat → Nat → Option Verifier.Ext3) (suffixes : List Nat)
    (integer : Nat) (evaluations result : List Verifier.Ext3)
    (h : columnSums term suffixes integer evaluations = some result) :
    result.length = evaluations.length ∧
      ∀ k, k < evaluations.length →
        suffixSum term (integer+k) suffixes (evaluations.getD k Verifier.zero) =
          some (result.getD k Verifier.zero) := by
  induction evaluations generalizing integer result with
  | nil =>
      simp only [columnSums,Option.some.injEq] at h
      subst h
      exact ⟨rfl,fun k hk => by simp at hk⟩
  | cons accumulated rest ih =>
      simp only [columnSums,Option.bind_eq_bind,Option.pure_def] at h
      cases hs : suffixSum term integer suffixes accumulated with
      | none => rw [hs,Option.none_bind] at h; exact Option.noConfusion h
      | some v =>
          rw [hs,Option.some_bind] at h
          cases hr : columnSums term suffixes (integer+1) rest with
          | none => rw [hr,Option.none_bind] at h; exact Option.noConfusion h
          | some rest' =>
              rw [hr,Option.some_bind,Option.some.injEq] at h
              subst h
              obtain ⟨hlen,hall⟩ := ih (integer+1) rest' hr
              refine ⟨by simp only [List.length_cons,hlen],fun k hk => ?_⟩
              cases k with
              | zero => simpa only [Nat.add_zero,List.getD_cons_zero] using hs
              | succ k =>
                  simp only [List.getD_cons_succ]
                  rw [show integer+(k+1)=integer+1+k by omega]
                  exact hall k (by simpa using hk)

theorem column_sums_total (term : Nat → Nat → Option Verifier.Ext3) (suffixes : List Nat)
    (integer : Nat) (evaluations : List Verifier.Ext3)
    (h : ∀ k, k < evaluations.length →
      ∃ v, suffixSum term (integer+k) suffixes (evaluations.getD k Verifier.zero) = some v) :
    ∃ result, columnSums term suffixes integer evaluations = some result := by
  induction evaluations generalizing integer with
  | nil => exact ⟨[],rfl⟩
  | cons accumulated rest ih =>
      obtain ⟨v,hv⟩ := h 0 (by simp)
      simp only [Nat.add_zero,List.getD_cons_zero] at hv
      obtain ⟨rest',hr⟩ := ih (integer+1) (fun k hk => by
        obtain ⟨w,hw⟩ := h (k+1) (by simpa using hk)
        simp only [List.getD_cons_succ] at hw
        rw [show integer+(k+1)=integer+1+k by omega] at hw
        exact ⟨w,hw⟩)
      exact ⟨v::rest',by simp only [columnSums,hv,hr,Option.bind_eq_bind,Option.pure_def,Option.some_bind]⟩

theorem replicate_getD (n k : Nat) (a : Verifier.Ext3) : (List.replicate n a).getD k a = a := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => cases k with
    | zero => rfl
    | succ k => simpa only [List.replicate_succ,List.getD_cons_succ] using ih k

/-! ### The gate round grid -/

/-- The grid of gate_ext3_v2.rs:108-134 with the slot-first iteration body:
`evaluations = vec![ZERO; degree+1]`, then the suffix-outer loop over
`0..half`. -/
def currentRoundGrid (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (t : Tables) (degree half : Nat) : Option (List Verifier.Ext3) :=
  suffixLoop (gridTerm c gates publicHash alpha t) (List.range half)
    (List.replicate (degree+1) Verifier.zero)

/-- The suffix-first sum of the slot-first bodies over a suffix list is the
GateSuffixPolynomial suffix sum of the captured slices, at the grid point. -/
theorem suffix_sum_captured (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (integer : Nat)
    (suffixes : List Nat) (accumulated : Verifier.Ext3)
    (hv : Gates.validateConfiguration c gates=some ()) :
    suffixSum (gridTerm c gates publicHash alpha t) integer suffixes accumulated =
      sumSuffixes c gates publicHash alpha (gridPoint integer) (suffixes.map (captureSlice t)) accumulated := by
  induction suffixes generalizing accumulated with
  | nil => rfl
  | cons suffix rest ih =>
      simp only [suffixSum,List.map_cons,sumSuffixes,Option.bind_eq_bind,
        grid_term_equals_suffix_slice c gates publicHash alpha t suffix integer hv]
      cases evalSlice c gates publicHash alpha (gridPoint integer) (captureSlice t suffix) with
      | none => rfl
      | some v => simp only [Option.some_bind]; exact ih _

/-- (b): the transposed grid is the list of per-integer suffix-first sums. -/
theorem grid_transposes (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (t : Tables) (degree half : Nat) :
    currentRoundGrid c gates publicHash alpha t degree half =
      columnSums (gridTerm c gates publicHash alpha t) (List.range half) 0
        (List.replicate (degree+1) Verifier.zero) :=
  suffix_loop_transposes _ _ _

/-- (b) against GateSuffixPolynomial: whenever the executed grid loop returns,
its accumulator has `degree+1` cells and the cell at each integer is exactly
`currentRoundValue` at that grid point, the per-integer suffix-first sum. -/
theorem grid_entries_are_suffix_sums (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (degree half : Nat)
    (evaluations : List Verifier.Ext3) (hv : Gates.validateConfiguration c gates=some ())
    (h : currentRoundGrid c gates publicHash alpha t degree half = some evaluations) :
    evaluations.length = degree+1 ∧
      ∀ integer, integer ≤ degree →
        currentRoundValue c gates publicHash alpha (gridPoint integer) t half =
          some (evaluations.getD integer Verifier.zero) := by
  rw [grid_transposes] at h
  obtain ⟨hlen,hall⟩ := column_sums_lookup _ _ _ _ _ h
  refine ⟨by simpa using hlen,fun integer hi => ?_⟩
  have hk := hall integer (by simp only [List.length_replicate]; omega)
  rw [Nat.zero_add,replicate_getD,suffix_sum_captured c gates publicHash alpha t integer _ _ hv] at hk
  exact hk

/-- Under configuration validity and the table shape, the executed grid loop
returns: no iteration body fails. -/
theorem configured_grid_executes (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (degree half : Nat)
    (hv : Gates.validateConfiguration c gates=some ()) (ht : TableShape c half t) :
    ∃ evaluations, currentRoundGrid c gates publicHash alpha t degree half = some evaluations := by
  obtain ⟨p,_,_,he⟩ := captured_round_polynomial c gates publicHash alpha t half hv ht
  rw [grid_transposes]
  apply column_sums_total
  intro k _
  rw [Nat.zero_add,replicate_getD,suffix_sum_captured c gates publicHash alpha t k _ _ hv]
  exact ⟨_,he (gridPoint k)⟩

/-- The executed grid is the point-value list of ONE fixed polynomial of degree
at most quotientDegree+2 at the integer grid points 0..degree. -/
theorem configured_grid_polynomial (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (degree half : Nat)
    (hv : Gates.validateConfiguration c gates=some ()) (ht : TableShape c half t) :
    ∃ evaluations, currentRoundGrid c gates publicHash alpha t degree half = some evaluations ∧
      evaluations.length = degree+1 ∧
      ∃ p : P, p.natDegree ≤ c.quotientDegree+2 ∧
        ∀ integer, integer ≤ degree →
          evaluations.getD integer Verifier.zero = value p (gridPoint integer) := by
  obtain ⟨evaluations,he⟩ := configured_grid_executes c gates publicHash alpha t degree half hv ht
  obtain ⟨hlen,hcells⟩ := grid_entries_are_suffix_sums c gates publicHash alpha t degree half evaluations hv he
  obtain ⟨p,_,hd,hp⟩ := captured_round_polynomial c gates publicHash alpha t half hv ht
  refine ⟨evaluations,he,hlen,p,hd,fun integer hi => ?_⟩
  have h1 := hcells integer hi
  rw [hp (gridPoint integer)] at h1
  exact (Option.some_inj.mp h1).symm

/-! ### (c) The source half and the num_vars guard (106-107) -/

/-- The eq table as the prover-state DenseMle; wires/constants as tables. -/
def tablesOf (wires constants : List (List Element)) (eq : DenseMleIndexed.State) : Tables :=
  ⟨wires,constants,eq.evaluations⟩

/-- `let half = self.eq.evaluations.len() / 2` (107). -/
def sourceHalf (eq : DenseMleIndexed.State) : Nat := eq.evaluations.length/2

/-- `current_round` 105-134: the `num_vars > 0` ensure, the source half, and
the grid; the coefficient interpolation at 136 is outside this module. -/
def currentRoundEvaluations (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (wires constants : List (List Element))
    (eq : DenseMleIndexed.State) (degree : Nat) : Option (List Verifier.Ext3) :=
  if eq.numVars = 0 then none else
    currentRoundGrid c gates publicHash alpha (tablesOf wires constants eq) degree (sourceHalf eq)

theorem constant_round_rejected (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (wires constants : List (List Element))
    (eq : DenseMleIndexed.State) (degree : Nat) (h : eq.numVars = 0) :
    currentRoundEvaluations c gates publicHash alpha wires constants eq degree = none := by
  simp [currentRoundEvaluations,h]

theorem positive_round_exact (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (wires constants : List (List Element))
    (eq : DenseMleIndexed.State) (degree : Nat) (h : 0 < eq.numVars) :
    currentRoundEvaluations c gates publicHash alpha wires constants eq degree =
      currentRoundGrid c gates publicHash alpha (tablesOf wires constants eq) degree (sourceHalf eq) := by
  simp [currentRoundEvaluations,show eq.numVars ≠ 0 by omega]

/-- The source half is the shape half, exactly as `captured_integer_half`. -/
theorem source_half_is_shape_half (c : Gates.Config) (wires constants : List (List Element))
    (eq : DenseMleIndexed.State) (half : Nat) (ht : TableShape c half (tablesOf wires constants eq)) :
    sourceHalf eq = half :=
  captured_integer_half c (tablesOf wires constants eq) half ht

/-- For a valid power-of-two eq table with a round left, the source half is
`2^(num_vars-1)` and the eq length is exactly twice it: every adjacent pair
read `2*suffix, 2*suffix+1` for `suffix < half` is in range. -/
theorem valid_source_half (eq : DenseMleIndexed.State) (hv : DenseMleIndexed.Valid eq)
    (hn : 0 < eq.numVars) :
    sourceHalf eq = 2^(eq.numVars-1) ∧ eq.evaluations.length = 2*sourceHalf eq := by
  obtain ⟨n,hnum⟩ := Nat.exists_eq_succ_of_ne_zero (show eq.numVars ≠ 0 by omega)
  have hlen : eq.evaluations.length = 2^(n+1) := by
    have h : eq.evaluations.length = 2^eq.numVars := hv
    rw [h,hnum]
  simp only [sourceHalf,hlen,hnum,Nat.succ_sub_one,Nat.add_sub_cancel,Nat.pow_succ]
  omega

/-- The full source round body under the prover-state invariants: a valid eq
table with a round left and shaped wire/constant tables. The returned
accumulator is the point-value list of one polynomial of degree at most
quotientDegree+2 at the integer grid points 0..degree. -/
theorem valid_round_executes (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (wires constants : List (List Element))
    (eq : DenseMleIndexed.State) (degree : Nat)
    (hv : Gates.validateConfiguration c gates=some ()) (hvalid : DenseMleIndexed.Valid eq)
    (hn : 0 < eq.numVars) (ht : TableShape c (2^(eq.numVars-1)) (tablesOf wires constants eq)) :
    ∃ evaluations, currentRoundEvaluations c gates publicHash alpha wires constants eq degree =
        some evaluations ∧ evaluations.length = degree+1 ∧
      ∃ p : P, p.natDegree ≤ c.quotientDegree+2 ∧
        ∀ integer, integer ≤ degree →
          evaluations.getD integer Verifier.zero = value p (gridPoint integer) := by
  rw [positive_round_exact c gates publicHash alpha wires constants eq degree hn,
    (valid_source_half eq hvalid hn).1]
  exact configured_grid_polynomial c gates publicHash alpha _ degree _ hv ht

/-- At the constructor's reviewed degree `degree = quotient_degree_factor + 2`
(gate_ext3_v2.rs:80-83, a prior condition, not re-checked here), the grid has
`degree+1` points for a polynomial of degree at most `degree`: the point count
that the (separately modelled) coefficient interpolation consumes. -/
theorem reviewed_degree_grid (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (wires constants : List (List Element))
    (eq : DenseMleIndexed.State)
    (hv : Gates.validateConfiguration c gates=some ()) (hvalid : DenseMleIndexed.Valid eq)
    (hn : 0 < eq.numVars) (ht : TableShape c (2^(eq.numVars-1)) (tablesOf wires constants eq)) :
    ∃ evaluations, currentRoundEvaluations c gates publicHash alpha wires constants eq
        (c.quotientDegree+2) = some evaluations ∧ evaluations.length = c.quotientDegree+3 ∧
      ∃ p : P, p.natDegree ≤ c.quotientDegree+2 ∧ p.natDegree ≤ 10 ∧
        ∀ integer, integer ≤ c.quotientDegree+2 →
          evaluations.getD integer Verifier.zero = value p (gridPoint integer) := by
  obtain ⟨evaluations,he,hlen,p,hd,hp⟩ :=
    valid_round_executes c gates publicHash alpha wires constants eq (c.quotientDegree+2) hv hvalid hn ht
  have henv := (Gates.validate_configuration_success c gates hv).1
  simp only [Gates.envelope] at henv
  exact ⟨evaluations,he,hlen,p,hd,by omega,hp⟩

end Audit.Wire3.GateSlotRound
