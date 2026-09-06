import Audit.Wire3.WhirInitial
import Audit.Wire3.WhirChallenge

/-!
# Actual inner-WHIR geometric RLC and fixed-vector agreement

The coefficient list is Spongefish.geometricPowers, and the inner product is
WhirInitial.dotRow, not an unconstrained evaluator. The source's count 0 / 1
branches consume nothing; count >= 2 consumes one 120-byte Ext3 squeeze (four
hash blocks). Both initial RLC calls keep their actual order and distinct sizes.

Polynomials are over the concrete canonical Ext3 Field. Fixed same-length
different vectors imply different polynomials. The byte probability is ONLY
the explicitly uniform law over 120 bytes, with the actual 3x40 LE reduction
bias. Hash uniformity, conditional/adaptive fixedness, commitment binding and
constituent extraction, source/Yul/ABI/memory refinement, and full PCS security
are not established. Raw out-of-range row reads are the existing typed model's
zero totalization; source applicability requires its validated shape bounds.
-/
namespace Audit.Wire3.WhirRlc
open Audit.Wire3 GoldilocksExt3Field WhirPolynomial
open Polynomial

theorem geometric_power_at (x previous : Element) (count j : Nat) (hj : j < count) :
    (Spongefish.geometricPowers x.toVerifier count previous.toVerifier).getD j Verifier.zero =
      (previous * x^j).toVerifier := by
  induction count generalizing previous j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero => simp only [Spongefish.geometricPowers, List.getD_cons_zero, pow_zero, mul_one]
      | succ j =>
          rw [Spongefish.geometricPowers, List.getD_cons_succ]
          have h := ih (previous*x) j (by omega)
          change (Spongefish.geometricPowers x.toVerifier n (previous*x).toVerifier).getD j Verifier.zero =
            (previous * x^(j+1)).toVerifier
          rw [h]
          congr 1
          ring

theorem geometric_one_power_at (x : Element) (count j : Nat) (hj : j < count) :
    (Spongefish.geometricPowers x.toVerifier count Spongefish.one).getD j Verifier.zero =
      (x^j).toVerifier := by
  simpa only [one_mul] using geometric_power_at x 1 count j hj

theorem range_fold_exact (f : Nat → Element) (n : Nat) (initial : Element) :
    (List.range n).foldl (fun acc j => Verifier.add acc (f j).toVerifier) initial.toVerifier =
      (initial + ∑ j ∈ Finset.range n, f j).toVerifier := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih, Finset.sum_range_succ]
      exact congrArg Element.toVerifier (add_assoc initial _ _)

theorem list_fold_agrees_on_members {A B : Type} (xs : List A) (f g : B → A → B)
    (h : ∀ a ∈ xs, ∀ b, f b a = g b a) (initial : B) :
    xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.foldl_cons]
      rw [h a (by simp) initial]
      exact ih (fun a ha b => h a (by simp [ha]) b) _

/-- Same actual row-major reads, in increasing constituent index order. -/
def rowCoefficients (matrix : List Verifier.Ext3) (row width : Nat) : List Element :=
  (List.range width).map fun j => ⟨matrix.getD (row*width+j) Verifier.zero⟩

theorem row_coefficients_length (matrix : List Verifier.Ext3) (row width : Nat) :
    (rowCoefficients matrix row width).length = width := by
  simp [rowCoefficients]

theorem row_coefficient_at (matrix : List Verifier.Ext3) (row width j : Nat) (hj : j < width) :
    (rowCoefficients matrix row width).getD j 0 =
      (⟨matrix.getD (row*width+j) Verifier.zero⟩ : Element) := by
  rw [List.getD_eq_get _ _ (by simpa [rowCoefficients] using hj)]
  simp [rowCoefficients]

theorem polynomial_eval_as_power_sum (cs : List Element) (x : Element) :
    (ofCoefficients cs).eval x = ∑ j ∈ Finset.range cs.length, cs.getD j 0 * x^j := by
  by_cases he : cs = []
  · subst cs
    simp [ofCoefficients]
  · have hl : 0 < cs.length := List.length_pos.mpr he
    rw [Polynomial.eval_eq_sum_range' (by
      have := degree_bound_including_empty cs
      omega : (ofCoefficients cs).natDegree < cs.length)]
    simp only [coefficient_exact]

/-- The actual forward dot accumulation equals constant-first polynomial
evaluation at the SAME x used by the actual geometric generator. -/
theorem actual_dot_row_is_polynomial (matrix : List Verifier.Ext3) (row width : Nat) (x : Element) :
    WhirInitial.dotRow matrix (Spongefish.geometricPowers x.toVerifier width Spongefish.one) row width =
      ((ofCoefficients (rowCoefficients matrix row width)).eval x).toVerifier := by
  unfold WhirInitial.dotRow
  rw [list_fold_agrees_on_members (List.range width) _
      (fun acc j => Verifier.add acc
        ((⟨matrix.getD (row*width+j) Verifier.zero⟩ : Element)*x^j).toVerifier) (by
        intro j hj acc
        rw [geometric_one_power_at x width j (List.mem_range.mp hj)]
        rfl)]
  change (List.range width).foldl (fun acc j => Verifier.add acc
      ((⟨matrix.getD (row*width+j) Verifier.zero⟩ : Element)*x^j).toVerifier) (0 : Element).toVerifier = _
  rw [range_fold_exact _ _ 0]
  rw [polynomial_eval_as_power_sum, row_coefficients_length, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [row_coefficient_at matrix row width j (Finset.mem_range.mp hj)]

def vectorCoefficients (cs : List Verifier.Ext3) : List Element := cs.map Element.mk

theorem whole_row_coefficients (cs : List Verifier.Ext3) :
    rowCoefficients cs 0 cs.length = vectorCoefficients cs := by
  apply List.ext_get (by simp [rowCoefficients,vectorCoefficients])
  intro j hj hk
  have h := row_coefficient_at cs 0 cs.length j (by simpa [rowCoefficients] using hj)
  rw [List.getD_eq_get _ _ hj] at h
  simp only [Nat.zero_mul,Nat.zero_add] at h
  rw [List.getD_eq_get cs Verifier.zero (by simpa [vectorCoefficients] using hk)] at h
  simpa [vectorCoefficients] using h

/-- Actual initial-row loop with the actual geometric coefficient list. -/
def rlc (cs : List Verifier.Ext3) (x : Element) : Verifier.Ext3 :=
  WhirInitial.dotRow cs (Spongefish.geometricPowers x.toVerifier cs.length Spongefish.one) 0 cs.length

theorem actual_rlc_polynomial (cs : List Verifier.Ext3) (x : Element) :
    rlc cs x = ((ofCoefficients (vectorCoefficients cs)).eval x).toVerifier := by
  simpa only [rlc,whole_row_coefficients] using actual_dot_row_is_polynomial cs 0 cs.length x

theorem vector_coefficients_length (cs : List Verifier.Ext3) :
    (vectorCoefficients cs).length = cs.length := List.length_map _ _

theorem vector_coefficients_injective : Function.Injective vectorCoefficients := by
  intro cs ds he
  have := congrArg (List.map Element.toVerifier) he
  simpa [vectorCoefficients, List.map_map, Function.comp_def] using this

theorem different_vectors_have_different_polynomials (cs ds : List Verifier.Ext3)
    (hlen : cs.length = ds.length) (hne : cs ≠ ds) :
    ofCoefficients (vectorCoefficients cs) ≠ ofCoefficients (vectorCoefficients ds) := by
  intro he
  exact hne (vector_coefficients_injective
    (equal_length_coefficient_lists_injective _ _
      (by simpa only [vector_coefficients_length] using hlen) he))

def agreementPoints (cs ds : List Verifier.Ext3) (domain : Finset Element) : Finset Element :=
  domain.filter (fun x => rlc cs x = rlc ds x)

theorem actual_rlc_agreement_is_polynomial_agreement (cs ds : List Verifier.Ext3)
    (domain : Finset Element) : agreementPoints cs ds domain =
      WhirPolynomial.agreementPoints (ofCoefficients (vectorCoefficients cs))
        (ofCoefficients (vectorCoefficients ds)) domain := by
  apply Finset.ext
  intro x
  simp only [agreementPoints, WhirPolynomial.agreementPoints, Finset.mem_filter, actual_rlc_polynomial]
  constructor
  · intro h
    exact ⟨h.1, element_eq _ _ h.2⟩
  · intro h
    exact ⟨h.1, congrArg Element.toVerifier h.2⟩

/-- Fixed canonical constituent vectors, equal length, DIFFERENT values.
The domain is a set of distinct field challenges, not a repeated sample list. -/
theorem fixed_different_vectors_agree_at_most_length_sub_one (cs ds : List Verifier.Ext3)
    (hlen : cs.length = ds.length) (hne : cs ≠ ds) (domain : Finset Element) :
    (agreementPoints cs ds domain).card ≤ cs.length-1 := by
  rw [actual_rlc_agreement_is_polynomial_agreement]
  apply fixed_polynomial_agreements_le_degree _ _
    (different_vectors_have_different_polynomials cs ds hlen hne)
  · simpa only [vector_coefficients_length] using degree_bound_including_empty (vectorCoefficients cs)
  · simpa only [vector_coefficients_length,hlen] using degree_bound_including_empty (vectorCoefficients ds)

theorem empty_rlc (x : Element) : rlc [] x = Verifier.zero := rfl

theorem singleton_rlc (c : Verifier.Ext3) (x : Element) : rlc [c] x = c := by
  rw [actual_rlc_polynomial]
  simp only [vectorCoefficients,List.map_cons,List.map_nil,ofCoefficients,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_zero,zero_mul,zero_add]

theorem distinct_singletons_never_agree (c d : Verifier.Ext3) (hne : c ≠ d) (x : Element) :
    rlc [c] x ≠ rlc [d] x := by simpa only [singleton_rlc] using hne

theorem actual_rlc_byte_event_exact (cs ds : List Verifier.Ext3) :
    WhirChallenge.byteEvent (agreementPoints cs ds Finset.univ) =
      Finset.univ.filter (fun bytes : WhirChallenge.ByteBlock 120 =>
        WhirInitial.dotRow cs (Spongefish.geometricPowers (Spongefish.reduceChallenge bytes.val)
          cs.length Spongefish.one) 0 cs.length =
        WhirInitial.dotRow ds (Spongefish.geometricPowers (Spongefish.reduceChallenge bytes.val)
          ds.length Spongefish.one) 0 ds.length) := by
  apply Finset.ext
  intro bytes
  simp only [WhirChallenge.byteEvent,agreementPoints,Finset.mem_filter,
    Finset.mem_univ,true_and,WhirChallenge.reduceBytes,rlc]

/-- A conditional one-round law: uniform actual length-120 input, with the
actual modulo bias. It is applicable to a squeezing RLC call only for n>=2;
the n=0/1 source branches are separately proved not to squeeze. This theorem
does not infer uniformity or independence from the transcript Hash parameter. -/
theorem fixed_vectors_uniform_120byte_probability_bound (cs ds : List Verifier.Ext3)
    (hlen : cs.length = ds.length) (hne : cs ≠ ds) :
    WhirChallenge.uniformByteProbability (agreementPoints cs ds Finset.univ) ≤
      ((cs.length-1 : Nat) : ℚ) *
        ((WhirChallenge.fiberCeiling : ℚ) / (WhirChallenge.wordSize : ℚ))^3 := by
  exact WhirChallenge.uniform_byte_probability_product_form _ _
    (fixed_different_vectors_agree_at_most_length_sub_one cs ds hlen hne Finset.univ)

theorem fixed_vectors_uniform_bound_explicit (cs ds : List Verifier.Ext3)
    (hlen : cs.length = ds.length) (hne : cs ≠ ds) :
    WhirChallenge.uniformByteProbability (agreementPoints cs ds Finset.univ) ≤
      ((cs.length-1 : Nat) : ℚ) *
        (((((2^320+Arithmetic.modulus-1)/Arithmetic.modulus : Nat) : ℚ))/(2 : ℚ)^320)^3 := by
  simpa only [WhirChallenge.fiberCeiling,WhirChallenge.ceilingQuotient,
    WhirChallenge.word_size_is_320_bits,Nat.cast_pow,Nat.cast_ofNat] using
    fixed_vectors_uniform_120byte_probability_bound cs ds hlen hne

/-- Exact bytes used if a call squeezes. For counts 0/1 this expression is
only a hypothetical evaluation point; no verifierMessage call is made. -/
def challengeBytes (hash : Spongefish.Hash) (s : Spongefish.State) : WhirChallenge.ByteBlock 120 :=
  ⟨(Spongefish.blockStream hash s.sponge.digest s.sponge.counter 4).take 120, by
    simp only [List.length_take,Spongefish.block_stream_length]
    decide⟩

def challengePoint (hash : Spongefish.Hash) (s : Spongefish.State) : Element :=
  WhirChallenge.reduceBytes (challengeBytes hash s)

theorem count_zero_consumes_nothing (hash : Spongefish.Hash) (s : Spongefish.State) :
    Spongefish.geometricChallenge hash s 0 = some ([],s) := rfl

theorem count_one_consumes_nothing (hash : Spongefish.Hash) (s : Spongefish.State) :
    Spongefish.geometricChallenge hash s 1 = some ([Spongefish.one],s) := rfl

/-- For n>=2 there is exactly the one actual Ext3 verifier call, whose
successful output and output state are retained, not supplied by an oracle. -/
theorem squeezing_geometric_trace (hash : Spongefish.Hash) (s t : Spongefish.State)
    (count : Nat) (coefficients : List Verifier.Ext3) (hn : 2 ≤ count)
    (h : Spongefish.geometricChallenge hash s count = some (coefficients,t)) :
    ∃ x, Spongefish.verifierExt3 hash s = some (x,t) ∧
      coefficients = Spongefish.geometricPowers x count Spongefish.one := by
  cases count with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ n =>
          cases hv : Spongefish.verifierExt3 hash s with
          | none => simp [Spongefish.geometricChallenge,hv] at h
          | some pair =>
              rcases pair with ⟨x,u⟩
              simp only [Spongefish.geometricChallenge,hv,bind,Option.bind,pure,
                Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              exact ⟨x,rfl,rfl⟩

theorem squeezing_geometric_same_bytes_and_state (hash : Spongefish.Hash)
    (s t : Spongefish.State) (count : Nat) (coefficients : List Verifier.Ext3)
    (hn : 2 ≤ count) (h : Spongefish.geometricChallenge hash s count = some (coefficients,t)) :
    coefficients = Spongefish.geometricPowers (challengePoint hash s).toVerifier count Spongefish.one ∧
    t.transcriptPos = s.transcriptPos ∧ t.hintPos = s.hintPos ∧
    t.sponge.digest = s.sponge.digest ∧ t.sponge.counter = s.sponge.counter+4 := by
  obtain ⟨x,hx,hc⟩ := squeezing_geometric_trace hash s t count coefficients hn h
  have ht := Spongefish.verifier_ext3_exact_cursor_and_bytes hash s t x hx
  refine ⟨?_,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1⟩
  rw [hc,ht.2.2.2.2]
  rfl

def blocksForRlc (count : Nat) : Nat := if 2 ≤ count then 4 else 0

/-- All branch outcomes preserve both input cursors and the digest. Small
counts do not consume entropy even if the counter has no four-block capacity. -/
theorem geometric_all_counts_state (hash : Spongefish.Hash) (s t : Spongefish.State)
    (count : Nat) (coefficients : List Verifier.Ext3)
    (h : Spongefish.geometricChallenge hash s count = some (coefficients,t)) :
    coefficients.length = count ∧ t.transcriptPos = s.transcriptPos ∧
    t.hintPos = s.hintPos ∧ t.sponge.digest = s.sponge.digest ∧
    t.sponge.counter = s.sponge.counter+blocksForRlc count := by
  cases count with
  | zero => cases h; simp [blocksForRlc]
  | succ n =>
      cases n with
      | zero => cases h; simp [blocksForRlc]
      | succ n =>
          obtain ⟨hc,hp,hh,hd,hn⟩ := squeezing_geometric_same_bytes_and_state hash s t (n+2) coefficients (by omega) h
          exact ⟨by rw [hc,Spongefish.geometric_powers_length],hp,hh,hd,
            by simpa [blocksForRlc] using hn⟩

theorem generated_rlc_row_exact (hash : Spongefish.Hash) (s t : Spongefish.State)
    (width row : Nat) (coefficients matrix : List Verifier.Ext3) (hn : 2 ≤ width)
    (h : Spongefish.geometricChallenge hash s width = some (coefficients,t)) :
    WhirInitial.dotRow matrix coefficients row width =
      ((ofCoefficients (rowCoefficients matrix row width)).eval (challengePoint hash s)).toVerifier := by
  rw [(squeezing_geometric_same_bytes_and_state hash s t width coefficients hn h).1]
  exact actual_dot_row_is_polynomial matrix row width (challengePoint hash s)

/-- Actual sampled coefficient list, same width and same constituent vector.
The polynomial is fixed by the vector, not selected after evaluating x. -/
theorem generated_constituent_rlc_exact (hash : Spongefish.Hash) (s t : Spongefish.State)
    (coefficients cs : List Verifier.Ext3) (hn : 2 ≤ cs.length)
    (h : Spongefish.geometricChallenge hash s cs.length = some (coefficients,t)) :
    WhirInitial.dotRow cs coefficients 0 cs.length =
      ((ofCoefficients (vectorCoefficients cs)).eval (challengePoint hash s)).toVerifier := by
  simpa only [whole_row_coefficients] using generated_rlc_row_exact hash s t cs.length 0 coefficients cs hn h

theorem generated_comparison_is_same_point_event (hash : Spongefish.Hash)
    (s t : Spongefish.State) (coefficients cs ds : List Verifier.Ext3)
    (hn : 2 ≤ cs.length) (hlen : cs.length = ds.length)
    (h : Spongefish.geometricChallenge hash s cs.length = some (coefficients,t)) :
    (WhirInitial.dotRow cs coefficients 0 cs.length = WhirInitial.dotRow ds coefficients 0 ds.length) ↔
      challengePoint hash s ∈ agreementPoints cs ds Finset.univ := by
  have hc := (squeezing_geometric_same_bytes_and_state hash s t cs.length coefficients hn h).1
  simp only [agreementPoints,Finset.mem_filter,Finset.mem_univ,true_and,rlc]
  rw [hc,hlen]

/-- The same transcript path: complete roots/own OOD, ALL statement claims,
then cross OOD, then vector RLC, then constraint RLC. The output vectors and
states are the ones stored by phaseInitial. No claim/root extraction theorem
or probabilistic independence is inferred from this sequential trace. -/
theorem initial_same_ordered_rlc_trace (hash : Spongefish.Hash) (source : Spongefish.Bytes)
    (p : WhirInitial.Params) (roots : List Spongefish.Digest) (expected : List Verifier.Ext3)
    (mask : Spongefish.Bytes) (s t : Spongefish.State) (r : WhirInitial.Result)
    (h : WhirInitial.phaseInitial hash source p roots expected mask s = some (r,t)) :
    ∃ afterCommitments afterClaims afterCross afterVector,
      WhirInitial.receiveCommitments hash source p roots s = some (r.commitments,afterCommitments) ∧
      WhirInitial.readClaims hash source mask 0 expected afterCommitments = some (r.evaluations,afterClaims) ∧
      WhirInitial.completeSlots hash source (WhirInitial.matrixSlots p r.commitments) afterClaims =
        some (r.oodMatrix,afterCross) ∧
      Spongefish.geometricChallenge hash afterCross (WhirInitial.totalVectors p) = some (r.vectorRlc,afterVector) ∧
      Spongefish.geometricChallenge hash afterVector (WhirInitial.totalOodPoints p+p.forms.length) =
        some (r.initialConstraintRlc,t) ∧
      t.sponge.counter = afterCross.sponge.counter+blocksForRlc (WhirInitial.totalVectors p)+
        blocksForRlc (WhirInitial.totalOodPoints p+p.forms.length) ∧
      t.sponge.digest = afterCross.sponge.digest ∧
      t.transcriptPos = afterCross.transcriptPos ∧ t.hintPos = afterCross.hintPos := by
  obtain ⟨entries,evals,matrix,vr,cr,a,b,c,d,hr,he,hm,hv,hc,rfl⟩ :=
    WhirInitial.phase_initial_trace hash source p roots expected mask s t r h
  have hvstate := geometric_all_counts_state hash c d _ vr hv
  have hcstate := geometric_all_counts_state hash d t _ cr hc
  refine ⟨a,b,c,d,hr,he,hm,hv,hc,?_,?_,?_,?_⟩
  · rw [hcstate.2.2.2.2,hvstate.2.2.2.2]
  · exact hcstate.2.2.2.1.trans hvstate.2.2.2.1
  · exact hcstate.2.1.trans hvstate.2.1
  · exact hcstate.2.2.1.trans hvstate.2.2.1

/-- Source shape is an explicit existing precondition, NOT a new runtime
guard. It supplies the source numLinearForms division and in-bounds row reads.
All row-polynomial evaluation uses the actual post-cross vector challenge.
Constraint coefficients come from the NEXT state, not that same challenge. -/
theorem initial_vector_polynomials_and_next_constraint (hash : Spongefish.Hash)
    (source : Spongefish.Bytes) (p : WhirInitial.Params) (roots : List Spongefish.Digest)
    (expected : List Verifier.Ext3) (mask : Spongefish.Bytes) (s t : Spongefish.State)
    (r : WhirInitial.Result) (hp : WhirInitial.validatedParams p roots expected mask)
    (hn : 2 ≤ WhirInitial.totalVectors p)
    (h : WhirInitial.phaseInitial hash source p roots expected mask s = some (r,t)) :
    ∃ afterClaims afterCross afterVector,
      WhirInitial.completeSlots hash source (WhirInitial.matrixSlots p r.commitments) afterClaims =
        some (r.oodMatrix,afterCross) ∧
      Spongefish.geometricChallenge hash afterCross (WhirInitial.totalVectors p) = some (r.vectorRlc,afterVector) ∧
      Spongefish.geometricChallenge hash afterVector (WhirInitial.totalOodPoints p+p.forms.length) =
        some (r.initialConstraintRlc,t) ∧
      r.evaluations.length / WhirInitial.totalVectors p = p.forms.length ∧
      afterVector.sponge.counter = afterCross.sponge.counter+4 ∧
      (∀ row, WhirInitial.dotRow r.evaluations r.vectorRlc row (WhirInitial.totalVectors p) =
        ((ofCoefficients (rowCoefficients r.evaluations row (WhirInitial.totalVectors p))).eval
          (challengePoint hash afterCross)).toVerifier) ∧
      (∀ row, WhirInitial.dotRow r.oodMatrix r.vectorRlc row (WhirInitial.totalVectors p) =
        ((ofCoefficients (rowCoefficients r.oodMatrix row (WhirInitial.totalVectors p))).eval
          (challengePoint hash afterCross)).toVerifier) ∧
      (2 ≤ WhirInitial.totalOodPoints p+p.forms.length →
        r.initialConstraintRlc = Spongefish.geometricPowers (challengePoint hash afterVector).toVerifier
          (WhirInitial.totalOodPoints p+p.forms.length) Spongefish.one) := by
  obtain ⟨a,b,c,d,_hr,_he,hm,hv,hc,_⟩ := initial_same_ordered_rlc_trace hash source p roots expected mask s t r h
  have hlen := (WhirInitial.initial_all_roots_and_checked_claims hash source p roots expected mask s t r h).2.2.1
  exact ⟨b,c,d,hm,hv,hc,by rw [hlen]; exact WhirInitial.validated_form_count p roots expected mask hp,
    (squeezing_geometric_same_bytes_and_state hash c d _ r.vectorRlc hn hv).2.2.2.2,
    fun row => generated_rlc_row_exact hash c d _ row r.vectorRlc r.evaluations hn hv,
    fun row => generated_rlc_row_exact hash c d _ row r.vectorRlc r.oodMatrix hn hv,
    fun hcsize => (squeezing_geometric_same_bytes_and_state hash d t _ r.initialConstraintRlc hcsize hc).1⟩

theorem statement_row_source_bounds (hash : Spongefish.Hash) (source : Spongefish.Bytes)
    (p : WhirInitial.Params) (roots : List Spongefish.Digest) (expected : List Verifier.Ext3)
    (mask : Spongefish.Bytes) (s t : Spongefish.State) (r : WhirInitial.Result)
    (hp : WhirInitial.validatedParams p roots expected mask)
    (h : WhirInitial.phaseInitial hash source p roots expected mask s = some (r,t))
    (row j : Nat) (hr : row < p.forms.length) (hj : j < WhirInitial.totalVectors p) :
    row*WhirInitial.totalVectors p+j < r.evaluations.length ∧ j < r.vectorRlc.length := by
  have shape := WhirInitial.initial_output_shapes hash source p roots expected mask s t r hp h
  rw [shape.2.2.1,shape.2.2.2.2.1]
  exact ⟨WhirInitial.ordered_matrix_row_index_bounded row p.forms.length j _ hr hj,hj⟩

/-- Ordinary non-base point: theta^3=2; powers retain source list order. -/
def theta : Element := ⟨⟨⟨0,1,0⟩,by decide,by decide,by decide⟩⟩

theorem nonbase_geometric_example :
    (Spongefish.geometricPowers theta.toVerifier 4 Spongefish.one).map Subtype.val =
      [Arithmetic.one,⟨0,1,0⟩,⟨0,0,1⟩,⟨2,0,0⟩] := by decide

theorem nonbase_rlc_example :
    (rlc [Spongefish.one,theta.toVerifier] theta).val = ⟨1,0,1⟩ := by decide

/-- A normal deterministic transcript example, not a uniformity fixture.
Vector count 3 and constraint count 2 consume four blocks EACH and no reads. -/
theorem two_geometric_calls_example :
    (do
      let (vr,s) ← Spongefish.geometricChallenge (fun _ => Spongefish.zeroDigest)
        ⟨⟨Spongefish.zeroDigest,0⟩,17,9⟩ 3
      let (cr,t) ← Spongefish.geometricChallenge (fun _ => Spongefish.zeroDigest) s 2
      pure (vr,cr,t)) =
    some ([Spongefish.one,Verifier.zero,Verifier.zero], [Spongefish.one,Verifier.zero],
      (⟨⟨Spongefish.zeroDigest,8⟩,17,9⟩ : Spongefish.State)) := by decide

end Audit.Wire3.WhirRlc
