import Audit.Wire3.OuterRound
import Audit.Wire3.Gates

/-!+# Actual outer Ext3 interpolation: fixed nodes and indexed elimination

Source: mle/src/sumcheck/coefficients.rs:180-238. The variable is the outer
sumcheck coordinate. Matrix rows are nodes 0..degree, columns are increasing
monomial powers followed by the supplied RHS. The algorithm uses NO row
pivoting: invert [pivot,pivot], normalize columns pivot..n inclusive, clone
that normalized row, visit every other row, capture its OLD pivot factor,
and overwrite columns pivot..n. Final coefficients are RHS column n in row
order (constant coefficient FIRST).

The scalar operations are the concrete GoldilocksExt3Field.Element operations;
its inverse executes WhirFinal.inverse, with a separate zero-pivot failure.
An indexed functional matrix abstracts array storage, not Solidity/Rust memory.
Below-range/out-of-range entries are totalized; source applicability is confined
to the proved n by (n+1) access bounds. No compiler, machine-word, ABI, allocation,
gas, circuit truth, transcript distribution, or full PCS theorem is asserted.

The raw interpolation helper has no degree<=10 guard. That bound applies only
to the checked wire-v3 caller profile: prover_v2.rs:358-359 and
verifier_v2.rs:98-99 require q>0 and q+2<=MAX_GATE_ROUND_DEGREE_V2=10;
gate_ext3_v2.rs:81 sets degree=q+2. Norm/logUp uses the literal degree 5 at
norm_logup.rs:24,687-693. These caller facts remain separate from the helper.
The Rust row-as-u64 cast agrees with natural embedding only below 2^64;
the proved distinct-node regime degree<p implies this range. The helper
model is not asserted equivalent for arbitrary machine-overflowing sizes.

All successful executions are proved correct below, including coefficient
omission and actual verifier reconstruction. Universal success/nonzero pivots
for every reviewed size is NOT yet proved; numerical examples do not replace
that obligation. Option.none represents the helper's empty-input assertion or
zero-inverse failure, not an exact Rust exception-semantics theorem.
-/
namespace Audit.Wire3.OuterInterpolation
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open Audit.Wire3 GoldilocksExt3Field Polynomial
abbrev Poly := Polynomial Element
abbrev Matrix := Nat → Nat → Element

theorem natural_nodes_injective_below_modulus (a b : Nat)
    (ha : a < Arithmetic.modulus) (hb : b < Arithmetic.modulus)
    (h : (a : Element) = (b : Element)) : a = b := by
  have hc := congrArg (fun x : Element => x.toVerifier.val.c0) h
  change a % Arithmetic.modulus = b % Arithmetic.modulus at hc
  simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hc

theorem distinct_node_regime_fits_source_u64 (degree i : Nat)
    (hd : degree < Arithmetic.modulus) (hi : i ≤ degree) : i < 2^64 := by
  unfold Arithmetic.modulus at hd
  omega

def nodeSet (degree : Nat) : Finset Element :=
  (Finset.range (degree+1)).image (fun n : Nat => (n : Element))

theorem node_membership (degree : Nat) (x : Element) :
    x ∈ nodeSet degree ↔ ∃ i ≤ degree, (i : Element) = x := by
  simp only [nodeSet,Finset.mem_image,Finset.mem_range,Nat.lt_succ_iff]

theorem node_count_exact (degree : Nat) (hd : degree < Arithmetic.modulus) :
    (nodeSet degree).card = degree+1 := by
  rw [nodeSet,Finset.card_image_iff.mpr]
  · exact Finset.card_range _
  · intro a ha b hb hab
    exact natural_nodes_injective_below_modulus a b
      (by have := Finset.mem_range.mp ha; omega) (by have := Finset.mem_range.mp hb; omega) hab

theorem interpolation_unique (f g : Poly) (degree : Nat) (hd : degree < Arithmetic.modulus)
    (hf : f.natDegree ≤ degree) (hg : g.natDegree ≤ degree)
    (he : ∀ i ≤ degree, f.eval (i : Element) = g.eval (i : Element)) : f = g := by
  by_contra hne
  have hbound := WhirPolynomial.fixed_polynomial_agreements_le_degree f g hne degree hf hg (nodeSet degree)
  have hall : WhirPolynomial.agreementPoints f g (nodeSet degree) = nodeSet degree := by
    apply Finset.ext
    intro x
    simp only [WhirPolynomial.agreementPoints,Finset.mem_filter]
    constructor
    · exact And.left
    · intro hx
      obtain ⟨i,hi,rfl⟩ := (node_membership degree x).mp hx
      exact ⟨hx,he i hi⟩
  rw [hall,node_count_exact degree hd] at hbound
  omega

/-- Source checked entry guard, not a newly imposed interpolation precondition. -/
def ReviewedGateProfile (quotientDegree : Nat) : Prop :=
  0 < quotientDegree ∧ quotientDegree+2 ≤ 10

theorem checked_gate_degree_range (q : Nat) (h : ReviewedGateProfile q) :
    3 ≤ q+2 ∧ q+2 ≤ 10 := by rcases h with ⟨hp,hb⟩; omega

theorem actual_gate_configuration_implies_profile (c : Gates.Config) (gates : List Gates.GateInfo)
    (h : Gates.validateConfiguration c gates = some ()) : ReviewedGateProfile c.quotientDegree := by
  have he := (Gates.validate_configuration_success c gates h).1
  rcases he with ⟨_,_,_,_,_,_,_,_,hq,hu⟩
  exact ⟨hq,by omega⟩

theorem checked_gate_nodes_distinct (q : Nat) (h : ReviewedGateProfile q) :
    (nodeSet (q+2)).card = q+3 := by
  exact node_count_exact (q+2) (by have := h.2; unfold Arithmetic.modulus; omega)

theorem logup_six_nodes_distinct : (nodeSet 5).card = 6 :=
  node_count_exact 5 (by decide)

def readWrite (matrix : Matrix) (row column : Nat) (value : Element) : Matrix :=
  fun i j => if i=row ∧ j=column then value else matrix i j

theorem write_same_cell (m : Matrix) (r c : Nat) (v : Element) :
    readWrite m r c v r c = v := by simp [readWrite]

theorem write_other_cell (m : Matrix) (r c i j : Nat) (v : Element)
    (h : i ≠ r ∨ j ≠ c) : readWrite m r c v i j = m i j := by
  simp only [readWrite]
  split <;> simp_all

/-- Increasing-column overwrite loop. The callback receives the CURRENT
cell; the lemma below proves each cell is visited exactly once. -/
def modifyColumns (f : Nat → Element → Element) (row : Nat) :
    Nat → Nat → Matrix → Matrix
  | _,0,m => m
  | start,count+1,m => modifyColumns f row (start+1) count
      (readWrite m row start (f start (m row start)))

theorem modify_columns_exact (f : Nat → Element → Element) (row start count : Nat)
    (m : Matrix) (i j : Nat) :
    modifyColumns f row start count m i j =
      if i=row ∧ start ≤ j ∧ j < start+count then f j (m i j) else m i j := by
  induction count generalizing start m with
  | zero => simp only [modifyColumns,Nat.add_zero]; rw [if_neg (by omega)]
  | succ count ih =>
    rw [modifyColumns,ih]
    by_cases hir : i=row
    · subst i
      by_cases hjs : j=start
      · subst j
        simp [readWrite]
      · have hwrite : readWrite m row start (f start (m row start)) row j = m row j :=
          write_other_cell m row start row j _ (Or.inr hjs)
        rw [hwrite]
        by_cases hs : start ≤ j
        · have hs' : start+1 ≤ j := by omega
          simp [hs,hs',Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        · simp [hs,show ¬start+1 ≤ j by omega]
    · have hwrite : readWrite m row start (f start (m row start)) i j = m i j :=
        write_other_cell m row start i j _ (Or.inl hir)
      simp only [hir,false_and,↓reduceIte,hwrite]

theorem modify_columns_frame (f : Nat → Element → Element) (row start count : Nat)
    (m : Matrix) (i j : Nat) (h : i ≠ row ∨ j < start ∨ start+count ≤ j) :
    modifyColumns f row start count m i j = m i j := by
  rw [modify_columns_exact]
  exact if_neg (by omega)

/-- Exactly the source pivot row normalization columns [pivot,n], inclusive. -/
def normalizePivot (m : Matrix) (n pivot : Nat) (inverse : Element) : Matrix :=
  modifyColumns (fun _ cell => cell*inverse) pivot pivot (n+1-pivot) m

/-- `factor` is captured BEFORE any target-row write; `pivotRow` is the
clone taken AFTER normalization and stays constant throughout elimination. -/
def eliminateRow (m : Matrix) (n pivot row : Nat) (pivotRow : Nat → Element) : Matrix :=
  let factor := m row pivot
  modifyColumns (fun column cell => cell-factor*pivotRow column) row pivot (n+1-pivot) m

def eliminateRows (n pivot : Nat) (pivotRow : Nat → Element) :
    Nat → Nat → Matrix → Matrix
  | _,0,m => m
  | row,count+1,m =>
      let next := if row=pivot then m else eliminateRow m n pivot row pivotRow
      eliminateRows n pivot pivotRow (row+1) count next

def gaussianStep (m : Matrix) (n pivot : Nat) : Option Matrix :=
  if m pivot pivot = 0 then none else
    let normalized := normalizePivot m n pivot (m pivot pivot)⁻¹
    let pivotRow := normalized pivot
    some (eliminateRows n pivot pivotRow 0 n normalized)

def gaussianLoop (n : Nat) : Nat → Nat → Matrix → Option Matrix
  | _,0,m => some m
  | pivot,count+1,m => do
      let next ← gaussianStep m n pivot
      gaussianLoop n (pivot+1) count next

/-- Increasing power construction: store old power then multiply by node. -/
def powerRow (node : Element) (row : Nat) : Nat → Nat → Element → Matrix → Matrix
  | _,0,_,m => m
  | column,count+1,power,m => powerRow node row (column+1) count (power*node)
      (readWrite m row column power)

def buildRows (evaluations : List Element) (n : Nat) : Nat → Nat → Matrix → Matrix
  | _,0,m => m
  | row,count+1,m =>
      let powers := powerRow (row : Element) row 0 n 1 m
      let withRhs := readWrite powers row n (evaluations.getD row 0)
      buildRows evaluations n (row+1) count withRhs

def initialMatrix (evaluations : List Element) : Matrix :=
  buildRows evaluations evaluations.length 0 evaluations.length (fun _ _ => 0)

def takeCoefficients (m : Matrix) (n : Nat) : List Element :=
  (List.range n).map (fun row => m row n)

def interpolate (evaluations : List Element) : Option (List Element) :=
  if evaluations = [] then none else do
    let result ← gaussianLoop evaluations.length 0 evaluations.length (initialMatrix evaluations)
    pure (takeCoefficients result evaluations.length)

theorem empty_input_rejected : interpolate [] = none := rfl

theorem coefficient_read_order (m : Matrix) (n j : Nat) (hj : j < n) :
    (takeCoefficients m n).getD j 0 = m j n := by
  rw [List.getD_eq_get _ _ (by simpa [takeCoefficients] using hj)]
  simp [takeCoefficients]

theorem coefficient_count (m : Matrix) (n : Nat) : (takeCoefficients m n).length = n := by
  simp [takeCoefficients]

theorem successful_coefficient_count (evaluations coefficients : List Element)
    (h : interpolate evaluations = some coefficients) : coefficients.length = evaluations.length := by
  unfold interpolate at h
  split at h
  · simp at h
  · cases hg : gaussianLoop evaluations.length 0 evaluations.length (initialMatrix evaluations) with
    | none => simp [hg] at h
    | some result => simp only [hg,bind,Option.bind,pure,Option.some.injEq] at h
                     subst coefficients
                     exact coefficient_count _ _

theorem normalize_pivot_diagonal (m : Matrix) (n pivot : Nat)
    (hp : pivot < n) (hz : m pivot pivot ≠ 0) :
    normalizePivot m n pivot (m pivot pivot)⁻¹ pivot pivot = 1 := by
  rw [normalizePivot,modify_columns_exact,if_pos (by omega)]
  exact actual_mul_inverse _ hz

theorem normalization_access_bounds (n pivot column : Nat) (hp : pivot < n)
    (hc : pivot ≤ column ∧ column < pivot+(n+1-pivot)) :
    pivot < n ∧ column < n+1 := by omega

theorem elimination_access_bounds (n pivot row column : Nat) (hp : pivot < n) (hr : row < n)
    (hc : pivot ≤ column ∧ column < pivot+(n+1-pivot)) :
    row < n ∧ pivot < n ∧ column < n+1 := by omega

theorem pivot_inverse_executes (m : Matrix) (pivot : Nat) (hz : m pivot pivot ≠ 0) :
    WhirFinal.inverse (m pivot pivot).toVerifier.val = some ((m pivot pivot)⁻¹).toVerifier.val :=
  field_inverse_executes_when_nonzero _ hz

theorem power_row_exact (node : Element) (row start count : Nat) (power : Element)
    (m : Matrix) (i j : Nat) :
    powerRow node row start count power m i j =
      if i=row ∧ start ≤ j ∧ j < start+count then power*node^(j-start) else m i j := by
  induction count generalizing start power m with
  | zero => simp only [powerRow,Nat.add_zero]; rw [if_neg (by omega)]
  | succ count ih =>
    rw [powerRow,ih]
    by_cases hir : i=row
    · subst i
      by_cases hjs : j=start
      · subst j
        simp [readWrite]
      · have hwrite : readWrite m row start power row j = m row j :=
          write_other_cell m row start row j _ (Or.inr hjs)
        rw [hwrite]
        by_cases hinside : start ≤ j ∧ j < start+(count+1)
        · have hrange : row=row ∧ start+1 ≤ j ∧ j < start+1+count := by omega
          rw [if_pos hrange,if_pos (by omega)]
          have he : j-start = (j-(start+1))+1 := by omega
          rw [he,pow_succ]
          ring
        · rw [if_neg (by omega),if_neg (by omega)]
    · simp only [hir,false_and,↓reduceIte]
      exact write_other_cell m row start i j power (Or.inl hir)

theorem built_single_row_exact (evaluations : List Element) (m : Matrix) (n row i j : Nat) :
    readWrite (powerRow (row : Element) row 0 n 1 m) row n (evaluations.getD row 0) i j =
      if i=row ∧ j<n then (row : Element)^j else
      if i=row ∧ j=n then evaluations.getD row 0 else m i j := by
  unfold readWrite
  rw [power_row_exact]
  by_cases hi : i=row
  · subst i
    by_cases hj : j=n
    · subst j; simp
    · simp [hj]
  · simp [hi]

theorem build_rows_exact (evaluations : List Element) (n start count : Nat) (m : Matrix) (i j : Nat) :
    buildRows evaluations n start count m i j =
      if start ≤ i ∧ i < start+count then
        (if j<n then (i : Element)^j else if j=n then evaluations.getD i 0 else m i j)
      else m i j := by
  induction count generalizing start m with
  | zero => simp only [buildRows,Nat.add_zero]; rw [if_neg (by omega)]
  | succ count ih =>
    rw [buildRows,ih]
    by_cases his : i=start
    · subst i
      rw [if_neg (by omega),if_pos (by omega),built_single_row_exact]
      simp
    · have hold : readWrite (powerRow (start : Element) start 0 n 1 m)
          start n (evaluations.getD start 0) i j = m i j := by
        rw [built_single_row_exact]
        simp [his]
      rw [hold]
      have hiff : (start+1 ≤ i ∧ i < start+1+count) ↔ (start ≤ i ∧ i < start+(count+1)) := by omega
      exact if_congr hiff rfl rfl

theorem initial_matrix_entry (evaluations : List Element) (i j : Nat) (hi : i < evaluations.length) :
    initialMatrix evaluations i j =
      if j < evaluations.length then (i : Element)^j else
      if j=evaluations.length then evaluations.getD i 0 else 0 := by
  rw [initialMatrix,build_rows_exact,if_pos (by omega)]

theorem initial_matrix_rhs (evaluations : List Element) (i : Nat) (hi : i < evaluations.length) :
    initialMatrix evaluations i evaluations.length = evaluations.getD i 0 := by
  rw [initial_matrix_entry evaluations i evaluations.length hi]
  simp

theorem initial_matrix_monomial (evaluations : List Element) (i j : Nat)
    (hi : i < evaluations.length) (hj : j < evaluations.length) :
    initialMatrix evaluations i j = (i : Element)^j := by
  rw [initial_matrix_entry evaluations i j hi,if_pos hj]

theorem normalize_pivot_entry (m : Matrix) (n pivot i j : Nat) (hp : pivot ≤ n) :
    normalizePivot m n pivot (m pivot pivot)⁻¹ i j =
      if i=pivot ∧ pivot ≤ j ∧ j≤n then m i j*(m pivot pivot)⁻¹ else m i j := by
  rw [normalizePivot,modify_columns_exact]
  exact if_congr (by omega) rfl rfl

theorem eliminate_row_entry (m : Matrix) (n pivot row i j : Nat) (pivotRow : Nat → Element)
    (hp : pivot ≤ n) :
    eliminateRow m n pivot row pivotRow i j =
      if i=row ∧ pivot ≤ j ∧ j≤n then m i j-m row pivot*pivotRow j else m i j := by
  rw [eliminateRow,modify_columns_exact]
  exact if_congr (by omega) rfl rfl

theorem eliminate_row_frame (m : Matrix) (n pivot row i j : Nat) (pivotRow : Nat → Element)
    (hi : i ≠ row) : eliminateRow m n pivot row pivotRow i j = m i j := by
  apply modify_columns_frame
  exact Or.inl hi

theorem eliminate_rows_exact (n pivot start count : Nat) (pivotRow : Nat → Element)
    (m : Matrix) (i j : Nat) (hp : pivot ≤ n) :
    eliminateRows n pivot pivotRow start count m i j =
      if start ≤ i ∧ i < start+count ∧ i≠pivot ∧ pivot ≤ j ∧ j≤n
      then m i j-m i pivot*pivotRow j else m i j := by
  induction count generalizing start m with
  | zero => simp only [eliminateRows,Nat.add_zero]; rw [if_neg (by omega)]
  | succ count ih =>
    rw [eliminateRows]
    by_cases hsp : start=pivot
    · rw [if_pos hsp,ih]
      exact if_congr (by omega) rfl rfl
    · rw [if_neg hsp,ih]
      by_cases his : i=start
      · subst i
        rw [if_neg (by omega),eliminate_row_entry _ _ _ _ _ _ _ hp]
        exact if_congr (by omega) rfl rfl
      · rw [eliminate_row_frame _ _ _ _ _ _ _ his,eliminate_row_frame _ _ _ _ _ _ _ his]
        exact if_congr (by omega) rfl rfl

/-- Identity in every already eliminated pivot column, including rows
not yet processed. This is established by the algorithm, not assumed at end. -/
def ReducedPrefix (m : Matrix) (n pivot : Nat) : Prop :=
  ∀ i < n, ∀ j < pivot, m i j = if i=j then 1 else 0

theorem initial_reduced_prefix (m : Matrix) (n : Nat) : ReducedPrefix m n 0 := by
  intro i _hi j hj
  omega

theorem gaussian_step_prefix (m result : Matrix) (n pivot : Nat)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot)
    (h : gaussianStep m n pivot = some result) : ReducedPrefix result n (pivot+1) := by
  unfold gaussianStep at h
  split at h
  · simp at h
  · rename_i hz
    simp only [Option.some.injEq] at h
    subst result
    intro i hi j hj
    rw [eliminate_rows_exact _ _ _ _ _ _ _ _ (by omega)]
    by_cases hjp : j < pivot
    · rw [if_neg (by omega),normalize_pivot_entry _ _ _ _ _ (by omega),if_neg (by omega)]
      exact hprev i hi j hjp
    · have he : j=pivot := by omega
      subst j
      by_cases hip : i=pivot
      · subst i
        rw [if_neg (by omega),normalize_pivot_diagonal _ _ _ hp hz]
        simp
      · rw [if_pos (by omega),normalize_pivot_diagonal _ _ _ hp hz]
        simp [hip]

theorem gaussian_loop_prefix (m result : Matrix) (n pivot count : Nat)
    (hb : pivot+count ≤ n) (hprev : ReducedPrefix m n pivot)
    (h : gaussianLoop n pivot count m = some result) : ReducedPrefix result n (pivot+count) := by
  induction count generalizing pivot m with
  | zero => cases h; simpa using hprev
  | succ count ih =>
    cases hs : gaussianStep m n pivot with
    | none => simp [gaussianLoop,hs] at h
    | some next =>
      simp only [gaussianLoop,hs,bind,Option.bind] at h
      have hn := gaussian_step_prefix m next n pivot (by omega) hprev hs
      have hr := ih (m := next) (pivot := pivot+1) (by omega) hn h
      simpa only [Nat.add_assoc,Nat.add_comm 1] using hr

theorem successful_gaussian_has_identity_left (m result : Matrix) (n : Nat)
    (h : gaussianLoop n 0 n m = some result) :
    ∀ i < n, ∀ j < n, result i j = if i=j then 1 else 0 := by
  simpa only [Nat.zero_add] using
    gaussian_loop_prefix m result n 0 n (by omega) (initial_reduced_prefix m n) h

theorem normalized_prefix_unchanged (m : Matrix) (n pivot : Nat)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) :
    ReducedPrefix (normalizePivot m n pivot (m pivot pivot)⁻¹) n pivot := by
  intro i hi j hj
  rw [normalize_pivot_entry _ _ _ _ _ (by omega),if_neg (by omega)]
  exact hprev i hi j hj

theorem normalize_full_entry (m : Matrix) (n pivot i j : Nat)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) (hj : j ≤ n) :
    normalizePivot m n pivot (m pivot pivot)⁻¹ i j =
      if i=pivot then m i j*(m pivot pivot)⁻¹ else m i j := by
  rw [normalize_pivot_entry _ _ _ _ _ (by omega)]
  by_cases hi : i=pivot
  · subst i
    by_cases hbefore : j<pivot
    · have hz := hprev pivot hp j hbefore
      rw [if_neg (by omega),if_pos rfl,hz,if_neg (by omega)]
      simp
    · rw [if_pos (by omega),if_pos rfl]
  · rw [if_neg (by omega),if_neg hi]

theorem elimination_full_entry (m : Matrix) (n pivot i j : Nat)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) (hi : i < n) (hj : j ≤ n) :
    eliminateRows n pivot (m pivot) 0 n m i j =
      if i=pivot then m i j else m i j-m i pivot*m pivot j := by
  rw [eliminate_rows_exact _ _ _ _ _ _ _ _ (by omega)]
  by_cases hip : i=pivot
  · rw [if_neg (by omega),if_pos hip]
  · rw [if_neg hip]
    by_cases hbefore : j<pivot
    · rw [if_neg (by omega),hprev pivot hp j hbefore,if_neg (by omega)]
      simp
    · rw [if_pos (by omega)]

def rowDot (m : Matrix) (n : Nat) (coefficients : Nat → Element) (row : Nat) : Element :=
  ∑ j ∈ Finset.range n, m row j*coefficients j

def Solves (m : Matrix) (n : Nat) (coefficients : Nat → Element) : Prop :=
  ∀ row < n, rowDot m n coefficients row = m row n

theorem normalize_row_dot (m : Matrix) (n pivot i : Nat) (coefficients : Nat → Element)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) :
    rowDot (normalizePivot m n pivot (m pivot pivot)⁻¹) n coefficients i =
      if i=pivot then rowDot m n coefficients i*(m pivot pivot)⁻¹ else rowDot m n coefficients i := by
  by_cases hi : i=pivot
  · rw [if_pos hi]
    simp only [rowDot,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalize_full_entry _ _ _ _ _ hp hprev (by have := Finset.mem_range.mp hj; omega),if_pos hi]
    ring
  · rw [if_neg hi]
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalize_full_entry _ _ _ _ _ hp hprev (by have := Finset.mem_range.mp hj; omega),if_neg hi]

theorem normalization_preserves_solution (m : Matrix) (n pivot : Nat) (coefficients : Nat → Element)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) (hs : Solves m n coefficients) :
    Solves (normalizePivot m n pivot (m pivot pivot)⁻¹) n coefficients := by
  intro i hi
  rw [normalize_row_dot _ _ _ _ _ hp hprev,normalize_full_entry _ _ _ _ _ hp hprev (by omega),hs i hi]

theorem eliminate_row_dot (m : Matrix) (n pivot i : Nat) (coefficients : Nat → Element)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) (hi : i < n) :
    rowDot (eliminateRows n pivot (m pivot) 0 n m) n coefficients i =
      if i=pivot then rowDot m n coefficients i else
        rowDot m n coefficients i-m i pivot*rowDot m n coefficients pivot := by
  by_cases hip : i=pivot
  · rw [if_pos hip]
    apply Finset.sum_congr rfl
    intro j hj
    rw [elimination_full_entry _ _ _ _ _ hp hprev hi (by have := Finset.mem_range.mp hj; omega),if_pos hip]
  · rw [if_neg hip]
    simp only [rowDot,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [elimination_full_entry _ _ _ _ _ hp hprev hi (by have := Finset.mem_range.mp hj; omega),if_neg hip]
    ring

theorem elimination_preserves_solution (m : Matrix) (n pivot : Nat) (coefficients : Nat → Element)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) (hs : Solves m n coefficients) :
    Solves (eliminateRows n pivot (m pivot) 0 n m) n coefficients := by
  intro i hi
  rw [eliminate_row_dot _ _ _ _ _ hp hprev hi,elimination_full_entry _ _ _ _ _ hp hprev hi (by omega),
    hs i hi,hs pivot hp]

theorem gaussian_step_preserves_solution (m result : Matrix) (n pivot : Nat) (coefficients : Nat → Element)
    (hp : pivot < n) (hprev : ReducedPrefix m n pivot) (hs : Solves m n coefficients)
    (h : gaussianStep m n pivot = some result) : Solves result n coefficients := by
  unfold gaussianStep at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst result
    exact elimination_preserves_solution _ n pivot coefficients hp
      (normalized_prefix_unchanged m n pivot hp hprev)
      (normalization_preserves_solution m n pivot coefficients hp hprev hs)

theorem gaussian_loop_preserves_solution (m result : Matrix) (n pivot count : Nat)
    (coefficients : Nat → Element) (hb : pivot+count ≤ n)
    (hprev : ReducedPrefix m n pivot) (hs : Solves m n coefficients)
    (h : gaussianLoop n pivot count m = some result) : Solves result n coefficients := by
  induction count generalizing pivot m with
  | zero => cases h; exact hs
  | succ count ih =>
    cases hstep : gaussianStep m n pivot with
    | none => simp [gaussianLoop,hstep] at h
    | some next =>
      simp only [gaussianLoop,hstep,bind,Option.bind] at h
      exact ih (m := next) (pivot := pivot+1) (by omega)
        (gaussian_step_prefix m next n pivot (by omega) hprev hstep)
        (gaussian_step_preserves_solution m next n pivot coefficients (by omega) hprev hs hstep) h

theorem identity_row_dot (m : Matrix) (n row : Nat) (coefficients : Nat → Element)
    (hi : ∀ i < n, ∀ j < n, m i j = if i=j then 1 else 0) (hr : row < n) :
    rowDot m n coefficients row = coefficients row := by
  unfold rowDot
  calc
    _ = ∑ j ∈ Finset.range n, if j=row then coefficients j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hi row hr j (Finset.mem_range.mp hj)]
      by_cases he : j=row
      · subst j; simp
      · simp [he,Ne.symm he]
    _ = coefficients row := by simp [hr]

/-- Successful real elimination produces the coefficients of EVERY
solution of its original equations; neither the identity left block nor
the solved equations are assumptions about the OUTPUT matrix. -/
theorem successful_elimination_extracts_original_solution (m result : Matrix) (n : Nat)
    (coefficients : Nat → Element) (hs : Solves m n coefficients)
    (h : gaussianLoop n 0 n m = some result) (j : Nat) (hj : j < n) :
    (takeCoefficients result n).getD j 0 = coefficients j := by
  rw [coefficient_read_order result n j hj]
  have hsolution := gaussian_loop_preserves_solution m result n 0 n coefficients (by omega)
    (initial_reduced_prefix m n) hs h
  exact (hsolution j hj).symm.trans
    (identity_row_dot result n j coefficients (successful_gaussian_has_identity_left m result n h) hj)

/-- The supplied evaluations are the actual matrix RHS, not a replacement
matrix or an abstract interpolator. -/
theorem original_polynomial_solves_built_matrix (evaluations : List Element) (f : Poly)
    (hd : f.natDegree < evaluations.length)
    (he : ∀ i < evaluations.length, evaluations.getD i 0 = f.eval (i : Element)) :
    Solves (initialMatrix evaluations) evaluations.length f.coeff := by
  intro i hi
  rw [initial_matrix_rhs evaluations i hi,he i hi,Polynomial.eval_eq_sum_range' hd]
  apply Finset.sum_congr rfl
  intro j hj
  rw [initial_matrix_monomial evaluations i j hi (Finset.mem_range.mp hj)]
  exact mul_comm _ _

theorem successful_interpolation_coefficients (evaluations coefficients : List Element) (f : Poly)
    (hd : f.natDegree < evaluations.length)
    (he : ∀ i < evaluations.length, evaluations.getD i 0 = f.eval (i : Element))
    (h : interpolate evaluations = some coefficients) :
    ∀ j < evaluations.length, coefficients.getD j 0 = f.coeff j := by
  have hs := original_polynomial_solves_built_matrix evaluations f hd he
  unfold interpolate at h
  split at h
  · simp at h
  · cases hg : gaussianLoop evaluations.length 0 evaluations.length (initialMatrix evaluations) with
    | none => simp [hg] at h
    | some result =>
      simp only [hg,bind,Option.bind,pure,Option.some.injEq] at h
      subst coefficients
      intro j hj
      exact successful_elimination_extracts_original_solution (initialMatrix evaluations) result
        evaluations.length f.coeff hs hg j hj

/-- Actual successful loop -> exact original polynomial. Success is an
execution hypothesis, NOT a premise that its coefficients interpolate.
This statement does not yet prove all required pivots are nonzero. -/
theorem successful_interpolation_polynomial_exact (evaluations coefficients : List Element) (f : Poly)
    (hd : f.natDegree < evaluations.length)
    (he : ∀ i < evaluations.length, evaluations.getD i 0 = f.eval (i : Element))
    (h : interpolate evaluations = some coefficients) :
    WhirPolynomial.ofCoefficients coefficients = f := by
  have hl := successful_coefficient_count evaluations coefficients h
  have hc := successful_interpolation_coefficients evaluations coefficients f hd he h
  apply Polynomial.ext
  intro j
  rw [WhirPolynomial.coefficient_exact]
  by_cases hj : j < evaluations.length
  · exact hc j hj
  · rw [List.getD_eq_default _ _ (by omega),Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

noncomputable def samplePolynomial (f : Poly) (degree : Nat) : List Element :=
  (List.range (degree+1)).map (fun i : Nat => f.eval (i : Element))

theorem sample_count (f : Poly) (degree : Nat) : (samplePolynomial f degree).length = degree+1 := by
  simp only [samplePolynomial,List.length_map,List.length_range]

theorem sample_value (f : Poly) (degree i : Nat) (hi : i ≤ degree) :
    (samplePolynomial f degree).getD i 0 = f.eval (i : Element) := by
  rw [List.getD_eq_get _ _ (by rw [sample_count]; omega)]
  simp only [samplePolynomial,List.get_eq_getElem,List.getElem_map,List.getElem_range]

theorem successful_sample_interpolation_exact (f : Poly) (degree : Nat) (coefficients : List Element)
    (hd : f.natDegree ≤ degree)
    (h : interpolate (samplePolynomial f degree) = some coefficients) :
    WhirPolynomial.ofCoefficients coefficients = f := by
  apply successful_interpolation_polynomial_exact (samplePolynomial f degree) coefficients f
    (by rw [sample_count]; omega)
  · intro i hi
    rw [sample_count] at hi
    exact sample_value f degree i (by omega)
  · exact h

theorem polynomial_coefficient_eval_one (coefficients : List Element) :
    (WhirPolynomial.ofCoefficients coefficients).eval 1 = coefficients.sum := by
  induction coefficients with
  | nil => simp [WhirPolynomial.ofCoefficients]
  | cons a rest ih =>
    simp only [WhirPolynomial.ofCoefficients,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,mul_one,ih,List.sum_cons]
    exact add_comm _ _

theorem reconstruct_constant_from_full_coefficients (a : Element) (rest : List Element) :
    OuterRound.constantCoefficient
      ((WhirPolynomial.ofCoefficients (a::rest)).eval 0+
       (WhirPolynomial.ofCoefficients (a::rest)).eval 1) rest = a := by
  rw [polynomial_coefficient_eval_one]
  simp only [WhirPolynomial.ofCoefficients,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,mul_zero,zero_add,List.sum_cons,
    OuterRound.constantCoefficient,OuterRound.coefficient_sum_eq_list_sum]
  calc
    (a+(a+rest.sum)-rest.sum)*OuterRound.half = a*(2*OuterRound.half) := by ring
    _ = a := by rw [OuterRound.two_times_concrete_half,mul_one]

/-- Exact omission/recovery of the constant-first coefficient, matching
the prover's coefficients[1..] and verifier's half-sum reconstruction. -/
theorem reconstruction_from_nonconstant_tail (coefficients : List Element) (hn : coefficients ≠ []) :
    OuterRound.polynomial
      ((WhirPolynomial.ofCoefficients coefficients).eval 0+
       (WhirPolynomial.ofCoefficients coefficients).eval 1) coefficients.tail =
      WhirPolynomial.ofCoefficients coefficients := by
  cases coefficients with
  | nil => contradiction
  | cons a rest =>
    simp only [OuterRound.polynomial,OuterRound.coefficients,List.tail_cons,
      reconstruct_constant_from_full_coefficients]

theorem successful_sample_message_length (f : Poly) (degree : Nat) (coefficients : List Element)
    (h : interpolate (samplePolynomial f degree) = some coefficients) : coefficients.tail.length = degree := by
  have hl := successful_coefficient_count (samplePolynomial f degree) coefficients h
  rw [sample_count] at hl
  simp [List.length_tail,hl]

/-- Honest coefficient generation, omission, and ACTUAL verifier evaluation
compose without an assumed polynomial evaluator. The current sum must be the
displayed endpoint sum; a full sumcheck-chain/circuit theorem is separate. -/
theorem successful_interpolation_actual_outer_round (f : Poly) (degree : Nat)
    (coefficients : List Element) (r : Element) (hd : f.natDegree ≤ degree)
    (h : interpolate (samplePolynomial f degree) = some coefficients) :
    Verifier.evaluateRound (f.eval 0+f.eval 1).toVerifier
      (coefficients.tail.map Element.toVerifier) r.toVerifier = (f.eval r).toVerifier := by
  have hpoly := successful_sample_interpolation_exact f degree coefficients hd h
  have hl := successful_coefficient_count (samplePolynomial f degree) coefficients h
  have hn : coefficients ≠ [] := by
    intro hz
    rw [hz,List.length_nil,sample_count] at hl
    omega
  rw [OuterRound.actual_round_is_polynomial_eval,← hpoly,reconstruction_from_nonconstant_tail coefficients hn]

theorem first_pivot_nonzero (evaluations : List Element) (hn : evaluations ≠ []) :
    initialMatrix evaluations 0 0 = 1 := by
  have hl : 0 < evaluations.length := List.length_pos.mpr hn
  rw [initial_matrix_monomial evaluations 0 0 hl hl,pow_zero]

/-- A raw-helper constant example (not an assertion that a gate round's
validated degree is zero). -/
theorem one_node_example : interpolate [7] = some [7] := by decide

/-- Nonconstant quadratic and constant-first extraction; all three pivots,
row copies, and elimination updates execute in this ordinary example. -/
theorem quadratic_three_node_example : interpolate [2,5,10] = some [2,2,1] := by decide

end Audit.Wire3.OuterInterpolation
