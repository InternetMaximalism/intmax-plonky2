import Audit.Wire3.OuterInterpolation

/-!
# Actual indexed interpolation: unconditional nonzero pivots and totality

This module extends the frozen source-ordered Gaussian model for
`mle/src/sumcheck/coefficients.rs:180-238`. It does not replace its algorithm.
The proof uses a ghost right-hand side only to identify a pivot: changing
that column does not change any actual coefficient-block entry or pivot.
The concrete scalar field is GoldilocksExt3Field.Element, not an assumed
generic field. Source machine arithmetic, memory, allocation, panic semantics,
compiler refinement, circuit truth, and transcript distribution remain outside
the model. The helper has no degree-10 guard; that bound belongs to its checked
gate caller, while the norm caller uses degree 5.
-/
namespace Audit.Wire3.OuterInterpolationTotal
open Audit.Wire3 GoldilocksExt3Field Polynomial Audit.Wire3.OuterInterpolation
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Equality of the actual left coefficient block, excluding RHS column n. -/
def LeftEq (n : Nat) (m k : Matrix) : Prop :=
  ∀ i < n, ∀ j < n, m i j = k i j

theorem normalize_left_congruence (m k : Matrix) (n pivot : Nat)
    (hp : pivot < n) (he : LeftEq n m k) :
    LeftEq n (normalizePivot m n pivot (m pivot pivot)⁻¹)
      (normalizePivot k n pivot (k pivot pivot)⁻¹) := by
  intro i hi j hj
  rw [normalize_pivot_entry _ _ _ _ _ (by omega),
    normalize_pivot_entry _ _ _ _ _ (by omega),he i hi j hj,he pivot hp pivot hp]

theorem eliminate_left_congruence (m k : Matrix) (n pivot : Nat)
    (hp : pivot < n) (he : LeftEq n m k) :
    LeftEq n (eliminateRows n pivot (m pivot) 0 n m)
      (eliminateRows n pivot (k pivot) 0 n k) := by
  intro i hi j hj
  rw [eliminate_rows_exact _ _ _ _ _ _ _ _ (by omega),
    eliminate_rows_exact _ _ _ _ _ _ _ _ (by omega),
    he i hi j hj,he i hi pivot hp,he pivot hp j hj]

theorem gaussian_step_left_congruence (m k result : Matrix) (n pivot : Nat)
    (hp : pivot < n) (he : LeftEq n m k)
    (h : gaussianStep m n pivot = some result) :
    ∃ other, gaussianStep k n pivot = some other ∧ LeftEq n result other := by
  unfold gaussianStep at h ⊢
  have hdiag := he pivot hp pivot hp
  split at h
  · simp at h
  · rename_i hn
    rw [if_neg (by simpa only [← hdiag] using hn)]
    simp only [Option.some.injEq] at h
    subst result
    exact ⟨_,rfl,eliminate_left_congruence _ _ n pivot hp
      (normalize_left_congruence m k n pivot hp he)⟩

theorem gaussian_loop_left_congruence (m k result : Matrix) (n start count : Nat)
    (hb : start+count ≤ n) (he : LeftEq n m k)
    (h : gaussianLoop n start count m = some result) :
    ∃ other, gaussianLoop n start count k = some other ∧ LeftEq n result other := by
  induction count generalizing start m k with
  | zero => cases h; exact ⟨k,rfl,he⟩
  | succ count ih =>
    cases hs : gaussianStep m n start with
    | none => simp [gaussianLoop,hs] at h
    | some next =>
      obtain ⟨other,ho,hl⟩ := gaussian_step_left_congruence m k next n start (by omega) he hs
      simp only [gaussianLoop,hs,bind,Option.bind] at h
      obtain ⟨last,hloop,hleft⟩ := ih (m:=next) (k:=other) (start:=start+1) (by omega) hl h
      exact ⟨last,by simp only [gaussianLoop,ho,bind,Option.bind,hloop],hleft⟩

theorem gaussian_step_zero_rhs_frame (m result : Matrix) (n pivot : Nat)
    (hp : pivot < n) (hz : m pivot n = 0)
    (h : gaussianStep m n pivot = some result) :
    ∀ i < n, result i n = m i n := by
  unfold gaussianStep at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst result
    intro i _hi
    have hn : normalizePivot m n pivot (m pivot pivot)⁻¹ pivot n = 0 := by
      rw [normalize_pivot_entry _ _ _ _ _ (by omega),if_pos (by omega),hz,zero_mul]
    rw [eliminate_rows_exact _ _ _ _ _ _ _ _ (by omega),hn]
    simp only [mul_zero,sub_zero,ite_self]
    rw [normalize_pivot_entry _ _ _ _ _ (by omega)]
    split
    · rename_i hc
      rw [hc.1,hz,zero_mul]
    · rfl

theorem gaussian_loop_zero_rhs_frame (m result : Matrix) (n start count : Nat)
    (hb : start+count ≤ n)
    (hz : ∀ j, start ≤ j → j < start+count → m j n = 0)
    (h : gaussianLoop n start count m = some result) :
    ∀ i < n, result i n = m i n := by
  induction count generalizing start m with
  | zero => cases h; intro i _; rfl
  | succ count ih =>
    cases hs : gaussianStep m n start with
    | none => simp [gaussianLoop,hs] at h
    | some next =>
      have hframe := gaussian_step_zero_rhs_frame m next n start (by omega)
        (hz start (by omega) (by omega)) hs
      simp only [gaussianLoop,hs,bind,Option.bind] at h
      have hrest := ih (m:=next) (start:=start+1) (by omega)
        (by intro j hlow hhigh; rw [hframe j (by omega)]; exact hz j (by omega) (by omega)) h
      intro i hi
      exact (hrest i hi).trans (hframe i hi)

/-- Monic polynomial vanishing at exactly the first `count` natural nodes
inside the distinct-node range. Used only in the mathematical proof. -/
noncomputable def falling : Nat → Poly
  | 0 => 1
  | count+1 => falling count * (X-C (count : Element))

theorem falling_monic (count : Nat) : (falling count).Monic := by
  induction count with
  | zero => exact Polynomial.monic_one
  | succ count ih => exact ih.mul (Polynomial.monic_X_sub_C _)

theorem falling_degree (count : Nat) : (falling count).natDegree = count := by
  induction count with
  | zero => simp [falling]
  | succ count ih =>
    rw [falling,Polynomial.natDegree_mul (falling_monic count).ne_zero
      (Polynomial.monic_X_sub_C _).ne_zero,ih,Polynomial.natDegree_X_sub_C]

theorem falling_top_coefficient (count : Nat) : (falling count).coeff count = 1 := by
  have hm := (falling_monic count).leadingCoeff
  rw [← Polynomial.coeff_natDegree,falling_degree] at hm
  exact hm

theorem falling_upper_coefficient_zero (count j : Nat) (hj : count < j) :
    (falling count).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [falling_degree]; exact hj)

theorem falling_eval_earlier (count node : Nat) (hn : node < count) :
    (falling count).eval (node : Element) = 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [falling,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    by_cases he : node=count
    · subst node; simp
    · rw [ih (by omega),zero_mul]

theorem falling_eval_later_nonzero (count node : Nat)
    (hcn : count ≤ node) (hn : node < Arithmetic.modulus) :
    (falling count).eval (node : Element) ≠ 0 := by
  induction count with
  | zero => simp [falling]
  | succ count ih =>
    rw [falling,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    apply mul_ne_zero (ih (by omega))
    intro hz
    have he := natural_nodes_injective_below_modulus node count hn (by omega) (sub_eq_zero.mp hz)
    omega

theorem falling_eval_product (count : Nat) (x : Element) :
    (falling count).eval x = ∏ j ∈ Finset.range count, (x-(j : Element)) := by
  induction count with
  | zero => simp [falling]
  | succ count ih =>
    rw [falling,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,Finset.prod_range_succ,ih]

theorem reduced_prefix_falling_dot (m : Matrix) (n pivot : Nat)
    (hp : pivot < n) (hr : ReducedPrefix m n pivot) :
    rowDot m n (falling pivot).coeff pivot = m pivot pivot := by
  unfold rowDot
  calc
    _ = ∑ j ∈ Finset.range n, if j=pivot then m pivot pivot else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases he : j=pivot
      · subst j; simp [falling_top_coefficient]
      · rw [if_neg he]
        by_cases hlt : j<pivot
        · rw [hr pivot hp j hlt,if_neg (by omega),zero_mul]
        · rw [falling_upper_coefficient_zero pivot j (by omega),mul_zero]
    _ = m pivot pivot := by simp [hp]

/-- Proof-only RHS substitution; no invocation of the actual helper is
replaced by this matrix. Its left block is proved equal below. -/
noncomputable def ghostMatrix (n : Nat) (f : Poly) : Matrix :=
  fun i j => if j<n then (i : Element)^j else if j=n then f.eval (i : Element) else 0

theorem ghost_left_equal (evaluations : List Element) (f : Poly) :
    LeftEq evaluations.length (initialMatrix evaluations) (ghostMatrix evaluations.length f) := by
  intro i hi j hj
  rw [initial_matrix_monomial evaluations i j hi hj,ghostMatrix,if_pos hj]

theorem ghost_rhs (n i : Nat) (f : Poly) :
    ghostMatrix n f i n = f.eval (i : Element) := by
  simp [ghostMatrix]

theorem ghost_solves (n : Nat) (f : Poly) (hd : f.natDegree < n) :
    Solves (ghostMatrix n f) n f.coeff := by
  intro i _hi
  rw [ghost_rhs,Polynomial.eval_eq_sum_range' hd]
  apply Finset.sum_congr rfl
  intro j hj
  change (if j<n then (i : Element)^j else _) * f.coeff j = _
  rw [if_pos (Finset.mem_range.mp hj)]
  exact mul_comm _ _

/-- Every next pivot of an actually successful prefix equals the product
of differences from its preceding natural nodes. Nonzeroness is derived
separately below in the distinct-node range. No output reducedness or
pivot-nonzero property is assumed. -/
theorem successful_prefix_pivot_exact (evaluations : List Element) (result : Matrix)
    (pivot : Nat) (hp : pivot < evaluations.length)
    (h : gaussianLoop evaluations.length 0 pivot (initialMatrix evaluations) = some result) :
    result pivot pivot = (falling pivot).eval (pivot : Element) := by
  let n := evaluations.length
  let ghost := ghostMatrix n (falling pivot)
  obtain ⟨other,hother,hleft⟩ := gaussian_loop_left_congruence
    (initialMatrix evaluations) ghost result n 0 pivot (by dsimp [n]; omega)
    (ghost_left_equal evaluations (falling pivot)) h
  have hprefix := gaussian_loop_prefix ghost other n 0 pivot (by dsimp [n]; omega)
    (initial_reduced_prefix ghost n) hother
  have hsolves := gaussian_loop_preserves_solution ghost other n 0 pivot (falling pivot).coeff
    (by dsimp [n]; omega) (initial_reduced_prefix ghost n)
    (ghost_solves n (falling pivot) (by rw [falling_degree]; exact hp)) hother
  have hframe := gaussian_loop_zero_rhs_frame ghost other n 0 pivot (by dsimp [n]; omega)
    (by
      intro j _hlo hhi
      change ghostMatrix n (falling pivot) j n = 0
      rw [ghost_rhs]
      exact falling_eval_earlier pivot j (by omega)) hother
  calc
    result pivot pivot = other pivot pivot := hleft pivot hp pivot hp
    _ = rowDot other n (falling pivot).coeff pivot :=
      (reduced_prefix_falling_dot other n pivot hp (by simpa only [Nat.zero_add] using hprefix)).symm
    _ = other pivot n := hsolves pivot hp
    _ = ghost pivot n := hframe pivot hp
    _ = (falling pivot).eval (pivot : Element) := ghost_rhs n pivot (falling pivot)

theorem successful_prefix_next_pivot_nonzero (evaluations : List Element) (result : Matrix)
    (pivot : Nat) (hp : pivot < evaluations.length) (hn : evaluations.length ≤ Arithmetic.modulus)
    (h : gaussianLoop evaluations.length 0 pivot (initialMatrix evaluations) = some result) :
    result pivot pivot ≠ 0 := by
  rw [successful_prefix_pivot_exact evaluations result pivot hp h]
  exact falling_eval_later_nonzero pivot pivot (by omega) (by omega)

theorem successful_prefix_pivot_product (evaluations : List Element) (result : Matrix)
    (pivot : Nat) (hp : pivot < evaluations.length)
    (h : gaussianLoop evaluations.length 0 pivot (initialMatrix evaluations) = some result) :
    result pivot pivot = ∏ j ∈ Finset.range pivot, ((pivot : Element)-(j : Element)) := by
  rw [successful_prefix_pivot_exact evaluations result pivot hp h,falling_eval_product]

/-- The inverse used at each reached pivot is the successful concrete
`WhirFinal.inverse` computation, not merely a field-level existence claim. -/
theorem reached_pivot_actual_inverse_executes (evaluations : List Element) (result : Matrix)
    (pivot : Nat) (hp : pivot < evaluations.length) (hn : evaluations.length ≤ Arithmetic.modulus)
    (h : gaussianLoop evaluations.length 0 pivot (initialMatrix evaluations) = some result) :
    WhirFinal.inverse (result pivot pivot).toVerifier.val =
      some ((result pivot pivot)⁻¹).toVerifier.val :=
  field_inverse_executes_when_nonzero (result pivot pivot)
    (successful_prefix_next_pivot_nonzero evaluations result pivot hp hn h)

theorem gaussian_step_succeeds (m : Matrix) (n pivot : Nat) (hn : m pivot pivot ≠ 0) :
    ∃ result, gaussianStep m n pivot = some result := by
  unfold gaussianStep
  rw [if_neg hn]
  exact ⟨_,rfl⟩

theorem gaussian_loop_append (n start first second : Nat) (m : Matrix) :
    gaussianLoop n start (first+second) m = (do
      let next ← gaussianLoop n start first m
      gaussianLoop n (start+first) second next) := by
  induction first generalizing start m with
  | zero => simp only [Nat.zero_add,Nat.add_zero,gaussianLoop,bind,Option.bind]
  | succ first ih =>
    rw [show first+1+second=(first+second)+1 by omega,gaussianLoop]
    cases hs : gaussianStep m n start with
    | none => simp [hs,gaussianLoop]
    | some next =>
      simp only [hs,bind,Option.bind]
      rw [ih,gaussianLoop,hs]
      simp only [bind,Option.bind,Nat.add_assoc,Nat.add_comm 1]

/-- Universal prefix totality for any non-repeating natural-node regime.
No numerical example or caller-specific degree enumeration is used. -/
theorem every_gaussian_prefix_succeeds (evaluations : List Element) (count : Nat)
    (hc : count ≤ evaluations.length) (hn : evaluations.length ≤ Arithmetic.modulus) :
    ∃ result, gaussianLoop evaluations.length 0 count (initialMatrix evaluations) = some result := by
  induction count with
  | zero => exact ⟨_,rfl⟩
  | succ count ih =>
    obtain ⟨previous,hprevious⟩ := ih (by omega)
    have hz := successful_prefix_next_pivot_nonzero evaluations previous count (by omega) hn hprevious
    obtain ⟨result,hresult⟩ := gaussian_step_succeeds previous evaluations.length count hz
    refine ⟨result,?_⟩
    rw [gaussian_loop_append evaluations.length 0 count 1,hprevious]
    simp only [bind,Option.bind,Nat.zero_add,gaussianLoop,hresult]

theorem full_gaussian_succeeds (evaluations : List Element)
    (hn : evaluations.length ≤ Arithmetic.modulus) :
    ∃ result, gaussianLoop evaluations.length 0 evaluations.length (initialMatrix evaluations) = some result :=
  every_gaussian_prefix_succeeds evaluations evaluations.length (by omega) hn

theorem nonempty_interpolation_succeeds (evaluations : List Element)
    (hne : evaluations ≠ []) (hn : evaluations.length ≤ Arithmetic.modulus) :
    ∃ coefficients, interpolate evaluations = some coefficients := by
  obtain ⟨result,hr⟩ := full_gaussian_succeeds evaluations hn
  refine ⟨takeCoefficients result evaluations.length,?_⟩
  simp only [interpolate,if_neg hne,hr,bind,Option.bind,pure]

theorem empty_interpolation_fails : interpolate [] = none := rfl

theorem distinct_node_sample_interpolation_total (f : Poly) (degree : Nat)
    (hd : degree < Arithmetic.modulus) :
    ∃ coefficients, interpolate (samplePolynomial f degree) = some coefficients := by
  apply nonempty_interpolation_succeeds
  · intro he
    have hl := sample_count f degree
    rw [he] at hl
    simp only [List.length_nil] at hl
  · rw [sample_count]
    omega

theorem total_sample_interpolation_exact (f : Poly) (degree : Nat)
    (hd : degree < Arithmetic.modulus) (hf : f.natDegree ≤ degree) :
    ∃ coefficients, interpolate (samplePolynomial f degree) = some coefficients ∧
      WhirPolynomial.ofCoefficients coefficients = f ∧ coefficients.tail.length = degree := by
  obtain ⟨coefficients,hc⟩ := distinct_node_sample_interpolation_total f degree hd
  exact ⟨coefficients,hc,successful_sample_interpolation_exact f degree coefficients hf hc,
    successful_sample_message_length f degree coefficients hc⟩

theorem total_sample_actual_outer_round (f : Poly) (degree : Nat)
    (hd : degree < Arithmetic.modulus) (hf : f.natDegree ≤ degree) :
    ∃ coefficients, interpolate (samplePolynomial f degree) = some coefficients ∧
      coefficients.tail.length = degree ∧
      ∀ r : Element, Verifier.evaluateRound (f.eval 0+f.eval 1).toVerifier
        (coefficients.tail.map Element.toVerifier) r.toVerifier = (f.eval r).toVerifier := by
  obtain ⟨coefficients,hc⟩ := distinct_node_sample_interpolation_total f degree hd
  exact ⟨coefficients,hc,successful_sample_message_length f degree coefficients hc,
    fun r => successful_interpolation_actual_outer_round f degree coefficients r hf hc⟩

theorem norm_degree_five_total (f : Poly) (hf : f.natDegree ≤ 5) :
    ∃ coefficients, interpolate (samplePolynomial f 5) = some coefficients ∧
      WhirPolynomial.ofCoefficients coefficients = f ∧ coefficients.tail.length = 5 :=
  total_sample_interpolation_exact f 5 (by decide) hf

theorem checked_gate_degree_total (f : Poly) (q : Nat)
    (hq : ReviewedGateProfile q) (hf : f.natDegree ≤ q+2) :
    ∃ coefficients, interpolate (samplePolynomial f (q+2)) = some coefficients ∧
      WhirPolynomial.ofCoefficients coefficients = f ∧ coefficients.tail.length = q+2 :=
  total_sample_interpolation_exact f (q+2)
    (by have := hq.2; unfold Arithmetic.modulus; omega) hf

theorem validated_gate_configuration_total (f : Poly) (c : Gates.Config) (gates : List Gates.GateInfo)
    (hc : Gates.validateConfiguration c gates = some ()) (hf : f.natDegree ≤ c.quotientDegree+2) :
    ∃ coefficients, interpolate (samplePolynomial f (c.quotientDegree+2)) = some coefficients ∧
      WhirPolynomial.ofCoefficients coefficients = f ∧ coefficients.tail.length = c.quotientDegree+2 :=
  checked_gate_degree_total f c.quotientDegree (actual_gate_configuration_implies_profile c gates hc) hf

end Audit.Wire3.OuterInterpolationTotal
