import Audit.Wire3.WhirQuadratic
import Audit.Wire3.Spongefish
import Mathlib.Data.Fintype.Card

/-!
# Counting the actual 120-byte WHIR challenge reduction

This is a deterministic finite counting theorem for an EXPLICIT uniform
120-byte input, not a derivation of uniformity from Keccak or a random oracle.
The uniform law is represented by exact rational count/total on all fixed-
length byte lists. Each 40-byte little-endian word has 2^320 possibilities.
The actual Spongefish.reduceChallenge takes the same input's three slices
at 0,40,80 and reduces each modulo the concrete Goldilocks modulus.

Generic quotient/remainder injections bound fiber sizes without enumerating
the enormous sample space. Byte/int bijections and actual slice correspondence
are explicit. Conditional one-round bounds concern fixed claim/message pairs;
they do not establish Fiat–Shamir independence, adaptive transcript fixedness,
ROM/Keccak security, source/Yul refinement or full WHIR/PCS soundness.
INNER WHIR only: outer TranscriptV2.squeezeExt3 uses three separate 32-byte
digest reductions, so this 120-byte bound is not the outer MLE challenge bound.
-/
namespace Audit.Wire3.WhirChallenge
open Audit.Wire3 GoldilocksExt3Field WhirPolynomial
set_option maxRecDepth 4096

def ceilingQuotient (size modulus : Nat) : Nat := (size + modulus - 1) / modulus

theorem ceiling_quotient_pred_form (size modulus : Nat) (hs : 0 < size) (hm : 0 < modulus) :
    ceilingQuotient size modulus = (size - 1) / modulus + 1 := by
  unfold ceilingQuotient
  have he : size + modulus - 1 = (size - 1) + modulus := by omega
  rw [he, Nat.add_div_right _ hm]

theorem quotient_lt_ceiling (size modulus : Nat) (hs : 0 < size) (hm : 0 < modulus)
    (x : Fin size) : x.val / modulus < ceilingQuotient size modulus := by
  rw [ceiling_quotient_pred_form size modulus hs hm]
  have hx : x.val ≤ size - 1 := by have := x.isLt; omega
  exact Nat.lt_succ_of_le (Nat.div_le_div_right hx)

theorem ceiling_quotient_is_least_upper_multiple (size modulus : Nat)
    (hs : 0 < size) (hm : 0 < modulus) (k : Nat) :
    ceilingQuotient size modulus ≤ k ↔ size ≤ modulus * k := by
  rw [ceiling_quotient_pred_form size modulus hs hm]
  constructor
  · intro hk
    have hd : (size - 1) / modulus < k := by omega
    have hlt := (Nat.div_lt_iff_lt_mul hm).mp hd
    rw [Nat.mul_comm] at hlt
    omega
  · intro hk
    have hlt : size - 1 < k * modulus := by rw [Nat.mul_comm]; omega
    have hd : (size - 1) / modulus < k := (Nat.div_lt_iff_lt_mul hm).mpr hlt
    omega

def quotientCode (size modulus : Nat) (hs : 0 < size) (hm : 0 < modulus)
    (x : Fin size) : Fin (ceilingQuotient size modulus) :=
  ⟨x.val / modulus, quotient_lt_ceiling size modulus hs hm x⟩

theorem same_remainder_and_quotient_are_same_word
    (size modulus : Nat) (a b : Fin size)
    (hr : a.val % modulus = b.val % modulus)
    (hq : a.val / modulus = b.val / modulus) : a = b := by
  apply Fin.ext
  have ha := Nat.mod_add_div a.val modulus
  have hb := Nat.mod_add_div b.val modulus
  rw [hr, hq] at ha
  exact ha.symm.trans hb

/-- A fixed residue's preimages inject into the possible integer quotients.
No enumeration or distribution assumption is used in this cardinal theorem. -/
theorem fixed_residue_fiber_bound (size modulus residue : Nat)
    (hs : 0 < size) (hm : 0 < modulus) :
    (Finset.univ.filter (fun x : Fin size => x.val % modulus = residue)).card ≤
      ceilingQuotient size modulus := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun x : Fin size => x.val % modulus = residue))
    (t := Finset.univ) (quotientCode size modulus hs hm)
    (fun _ _ => Finset.mem_univ _) (by
      intro a ha b hb he
      exact same_remainder_and_quotient_are_same_word size modulus a b
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
        (congrArg Fin.val he))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

abbrev ByteBlock (n : Nat) := { bytes : Transcript.Bytes // bytes.length = n }

theorem from_le_is_bounded (bytes : Transcript.Bytes) :
    Transcript.fromLe bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [Transcript.fromLe]
  | cons b bs ih =>
      simp only [Transcript.fromLe, List.length_cons, Nat.pow_succ]
      have hb := b.isLt
      omega

theorem le_from_le_roundtrip (bytes : Transcript.Bytes) :
    Transcript.le bytes.length (Transcript.fromLe bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.length_cons, Transcript.fromLe, Transcript.le,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt,
        Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt b.isLt,
        Nat.zero_add, ih]

def wordEquiv (n : Nat) : ByteBlock n ≃ Fin (256 ^ n) where
  toFun bytes := ⟨Transcript.fromLe bytes.val, by
    have hb := from_le_is_bounded bytes.val
    simpa only [bytes.property] using hb⟩
  invFun word := ⟨Transcript.le n word.val, Transcript.le_length n word.val⟩
  left_inv bytes := by
    apply Subtype.eq
    change Transcript.le n (Transcript.fromLe bytes.val) = bytes.val
    simpa only [bytes.property] using le_from_le_roundtrip bytes.val
  right_inv word := by
    apply Fin.ext
    exact Transcript.fromLe_le_roundtrip n word.val word.isLt

instance byteBlockFintype (n : Nat) : Fintype (ByteBlock n) :=
  Fintype.ofEquiv (Fin (256 ^ n)) (wordEquiv n).symm

theorem byte_block_cardinality (n : Nat) : Fintype.card (ByteBlock n) = 256 ^ n := by
  exact (Fintype.card_congr (wordEquiv n)).trans (Fintype.card_fin _)

def splitEquiv (m n : Nat) : ByteBlock (m+n) ≃ ByteBlock m × ByteBlock n where
  toFun bytes :=
    (⟨bytes.val.take m, by simp only [List.length_take, bytes.property]; omega⟩,
     ⟨bytes.val.drop m, by simp only [List.length_drop, bytes.property]; omega⟩)
  invFun pair := ⟨pair.1.val ++ pair.2.val, by simp only [List.length_append, pair.1.property, pair.2.property]⟩
  left_inv bytes := by
    apply Subtype.eq
    exact List.take_append_drop m bytes.val
  right_inv pair := by
    apply Prod.ext <;> apply Subtype.eq
    · change (pair.1.val ++ pair.2.val).take m = pair.1.val
      simpa only [pair.1.property] using List.take_left pair.1.val pair.2.val
    · change (pair.1.val ++ pair.2.val).drop m = pair.2.val
      simpa only [pair.1.property] using List.drop_left pair.1.val pair.2.val

def wordSize : Nat := 256 ^ 40
def fiberCeiling : Nat := ceilingQuotient wordSize Arithmetic.modulus
abbrev Word := Fin wordSize
abbrev Sample := Word × Word × Word

theorem word_size_is_320_bits : wordSize = 2 ^ 320 := by norm_num [wordSize]
theorem word_size_positive : 0 < wordSize := by exact pow_pos (by decide) _
theorem modulus_positive : 0 < Arithmetic.modulus := Arithmetic.modulus_positive

def inputEquiv : ByteBlock 120 ≃ Sample :=
  (splitEquiv 40 80).trans (Equiv.prodCongr (wordEquiv 40)
    ((splitEquiv 40 40).trans (Equiv.prodCongr (wordEquiv 40) (wordEquiv 40))))

theorem input_forward_slices (bytes : ByteBlock 120) :
    (inputEquiv bytes).1.val = Transcript.fromLe (bytes.val.take 40) ∧
    (inputEquiv bytes).2.1.val = Transcript.fromLe ((bytes.val.drop 40).take 40) ∧
    (inputEquiv bytes).2.2.val = Transcript.fromLe ((bytes.val.drop 80).take 40) := by
  refine ⟨rfl, rfl, ?_⟩
  change Transcript.fromLe ((bytes.val.drop 40).drop 40) = _
  rw [List.drop_drop]
  have hl : (bytes.val.drop 80).length = 40 := by simp [bytes.property]
  rw [List.take_length_le (by omega : (bytes.val.drop 80).length ≤ 40)]

theorem input_inverse_is_three_encodings (s : Sample) :
    (inputEquiv.symm s).val = Transcript.le 40 s.1.val ++
      (Transcript.le 40 s.2.1.val ++ Transcript.le 40 s.2.2.val) := rfl

def reduceSample (s : Sample) : Element :=
  ⟨⟨⟨s.1.val % Arithmetic.modulus, s.2.1.val % Arithmetic.modulus,
    s.2.2.val % Arithmetic.modulus⟩,
    Nat.mod_lt _ modulus_positive, Nat.mod_lt _ modulus_positive, Nat.mod_lt _ modulus_positive⟩⟩

/-- Same actual 120-byte input and exactly the source slices, not three
separate calls to the sponge or unrelated uniform-limb observations. -/
theorem actual_reduction_exact (bytes : ByteBlock 120) :
    (reduceSample (inputEquiv bytes)).toVerifier = Spongefish.reduceChallenge bytes.val := by
  apply Subtype.eq
  simp only [reduceSample, Spongefish.reduceChallenge, Arithmetic.reduce]
  congr 1
  exact congrArg (fun n => n % Arithmetic.modulus) (input_forward_slices bytes).2.2

theorem encoded_sample_reduction_exact (s : Sample) :
    (reduceSample s).toVerifier = Spongefish.reduceChallenge (inputEquiv.symm s).val := by
  simpa only [Equiv.apply_symm_apply] using actual_reduction_exact (inputEquiv.symm s)

/-- Transport event counts along an actual bijection, without enumerating
either finite type. -/
theorem equiv_event_card {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun a : A => p (e a))).card =
      (Finset.univ.filter p).card := by
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ he
    exact e.injective he
  · intro b hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hb).2⟩

theorem fixed_40byte_residue_preimage_bound (residue : Nat) :
    (Finset.univ.filter (fun bytes : ByteBlock 40 =>
      Transcript.fromLe bytes.val % Arithmetic.modulus = residue)).card ≤ fiberCeiling := by
  have he := equiv_event_card (wordEquiv 40)
    (fun x : Word => x.val % Arithmetic.modulus = residue)
  rw [show (Finset.univ.filter (fun bytes : ByteBlock 40 =>
      Transcript.fromLe bytes.val % Arithmetic.modulus = residue)).card =
      (Finset.univ.filter (fun x : Word => x.val % Arithmetic.modulus = residue)).card from he]
  exact fixed_residue_fiber_bound wordSize Arithmetic.modulus residue word_size_positive modulus_positive

/-- Exact uniform-law ratio for one full 40-byte input, including reduction
bias. The sample space is all ByteBlock 40, whose cardinality is wordSize. -/
theorem fixed_40byte_uniform_probability_bound (residue : Nat) :
    ((Finset.univ.filter (fun bytes : ByteBlock 40 =>
      Transcript.fromLe bytes.val % Arithmetic.modulus = residue)).card : ℚ) / (wordSize : ℚ) ≤
      (fiberCeiling : ℚ) / (wordSize : ℚ) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast fixed_40byte_residue_preimage_bound residue

abbrev QuotientSample := Fin fiberCeiling × Fin fiberCeiling × Fin fiberCeiling

def quotientSample (s : Sample) : QuotientSample :=
  (quotientCode wordSize Arithmetic.modulus word_size_positive modulus_positive s.1,
   quotientCode wordSize Arithmetic.modulus word_size_positive modulus_positive s.2.1,
   quotientCode wordSize Arithmetic.modulus word_size_positive modulus_positive s.2.2)

theorem reduction_and_quotients_determine_sample (a b : Sample)
    (hr : reduceSample a = reduceSample b) (hq : quotientSample a = quotientSample b) : a = b := by
  have hr0 := congrArg (fun x : Element => (raw x).c0) hr
  have hr1 := congrArg (fun x : Element => (raw x).c1) hr
  have hr2 := congrArg (fun x : Element => (raw x).c2) hr
  have hq0 := congrArg (fun x : QuotientSample => x.1.val) hq
  have hq1 := congrArg (fun x : QuotientSample => x.2.1.val) hq
  have hq2 := congrArg (fun x : QuotientSample => x.2.2.val) hq
  exact Prod.ext (same_remainder_and_quotient_are_same_word _ _ a.1 b.1 hr0 hq0)
    (Prod.ext (same_remainder_and_quotient_are_same_word _ _ a.2.1 b.2.1 hr1 hq1)
      (same_remainder_and_quotient_are_same_word _ _ a.2.2 b.2.2 hr2 hq2))

theorem quotient_sample_cardinality : Fintype.card QuotientSample = fiberCeiling ^ 3 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

theorem sample_cardinality : Fintype.card Sample = wordSize ^ 3 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

theorem actual_120byte_cardinality : Fintype.card (ByteBlock 120) = wordSize ^ 3 := by
  exact (Fintype.card_congr inputEquiv).trans sample_cardinality

def sampleEvent (points : Finset Element) : Finset Sample :=
  Finset.univ.filter (fun s => reduceSample s ∈ points)

/-- Generic finite counting avoids normalization of concrete gigantic univ
enumerations: only injectivity and cardinal algebra enter the proof. -/
theorem event_bound_by_residue_and_code {A B C : Type}
    [Fintype A] [Fintype C] [DecidableEq B]
    (f : A → B) (g : A → C) (hi : Function.Injective (fun a => (f a, g a)))
    (points : Finset B) :
    (Finset.univ.filter (fun a : A => f a ∈ points)).card ≤ points.card * Fintype.card C := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun a : A => f a ∈ points))
    (t := points.product (Finset.univ : Finset C)) (fun a : A => (f a,g a))
    (by
      intro a ha
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp ha).2, Finset.mem_univ _⟩)
    (by intro a _ b _ he; exact hi he)
  calc
    (Finset.univ.filter (fun a : A => f a ∈ points)).card ≤
        (points.product (Finset.univ : Finset C)).card := h
    _ = points.card * (Finset.univ : Finset C).card := Finset.card_product _ _
    _ = points.card * Fintype.card C := by rw [Finset.card_univ]

/-- The whole event injects into (accepted field value, three quotients).
This combines the limbs by a PRODUCT sample space, not an independence claim
about the hash outputs. The actual byte bijection supplies this space. -/
theorem fixed_point_set_preimage_bound (points : Finset Element) :
    (sampleEvent points).card ≤ points.card * fiberCeiling ^ 3 := by
  have h := event_bound_by_residue_and_code reduceSample quotientSample (by
    intro a b he
    exact reduction_and_quotients_determine_sample a b (congrArg Prod.fst he) (congrArg Prod.snd he)) points
  simpa only [sampleEvent, quotient_sample_cardinality] using h

theorem at_most_d_points_preimage_bound (points : Finset Element) (d : Nat)
    (hd : points.card ≤ d) : (sampleEvent points).card ≤ d * fiberCeiling ^ 3 :=
  (fixed_point_set_preimage_bound points).trans (Nat.mul_le_mul_right _ hd)

theorem fixed_ext3_value_preimage_bound (value : Element) :
    (Finset.univ.filter (fun s : Sample => reduceSample s = value)).card ≤ fiberCeiling ^ 3 := by
  simpa only [sampleEvent, Finset.mem_singleton, Finset.card_singleton, Nat.one_mul] using
    fixed_point_set_preimage_bound {value}

def reduceBytes (bytes : ByteBlock 120) : Element := ⟨Spongefish.reduceChallenge bytes.val⟩

theorem actual_reduction_element_exact (bytes : ByteBlock 120) :
    reduceSample (inputEquiv bytes) = reduceBytes bytes :=
  element_eq _ _ (actual_reduction_exact bytes)

def byteEvent (points : Finset Element) : Finset (ByteBlock 120) :=
  Finset.univ.filter (fun bytes => reduceBytes bytes ∈ points)

theorem actual_byte_and_sample_event_counts_agree (points : Finset Element) :
    (byteEvent points).card = (sampleEvent points).card := by
  have he := equiv_event_card inputEquiv (fun s : Sample => reduceSample s ∈ points)
  simpa only [actual_reduction_element_exact, byteEvent, sampleEvent] using he

theorem actual_120byte_point_set_preimage_bound (points : Finset Element) (d : Nat)
    (hd : points.card ≤ d) : (byteEvent points).card ≤ d * fiberCeiling ^ 3 := by
  rw [actual_byte_and_sample_event_counts_agree]
  exact at_most_d_points_preimage_bound points d hd

theorem actual_120byte_fixed_value_preimage_bound (value : Element) :
    (Finset.univ.filter (fun bytes : ByteBlock 120 =>
      Spongefish.reduceChallenge bytes.val = value.toVerifier)).card ≤ fiberCeiling ^ 3 := by
  have he (bytes : ByteBlock 120) : reduceBytes bytes = value ↔
      Spongefish.reduceChallenge bytes.val = value.toVerifier := by
    exact ⟨congrArg Element.toVerifier, fun h => element_eq _ _ h⟩
  simpa only [byteEvent, Finset.mem_singleton, he, Nat.one_mul] using
    actual_120byte_point_set_preimage_bound {value} 1 (by simp)

/-- DEFINITION of the explicit uniform input law: each length-120 byte string
has equal mass 1/card. This is not a claim about the real sponge distribution. -/
def uniformByteProbability (points : Finset Element) : ℚ :=
  ((byteEvent points).card : ℚ) / (Fintype.card (ByteBlock 120) : ℚ)

theorem uniform_byte_probability_is_between_zero_and_one (points : Finset Element) :
    0 ≤ uniformByteProbability points ∧ uniformByteProbability points ≤ 1 := by
  have hp : 0 < (Fintype.card (ByteBlock 120) : ℚ) := by
    rw [actual_120byte_cardinality, Nat.cast_pow]
    exact pow_pos (Nat.cast_pos.mpr word_size_positive) _
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hp.le
  · apply (div_le_one hp).mpr
    exact_mod_cast (byteEvent points).card_le_univ

theorem uniform_empty_event_probability : uniformByteProbability ∅ = 0 := by
  have he : byteEvent ∅ = ∅ := by
    apply Finset.ext
    intro bytes
    simp only [byteEvent, Finset.mem_filter, Finset.not_mem_empty, and_false]
  simp only [uniformByteProbability, he, Finset.card_empty, Nat.cast_zero, zero_div]

theorem uniform_entire_field_probability : uniformByteProbability Finset.univ = 1 := by
  have hn : (Fintype.card (ByteBlock 120) : ℚ) ≠ 0 := by
    rw [actual_120byte_cardinality, Nat.cast_pow]
    exact pow_ne_zero _ (ne_of_gt (Nat.cast_pos.mpr word_size_positive))
  have he : byteEvent Finset.univ = (Finset.univ : Finset (ByteBlock 120)) := by
    apply Finset.ext
    intro bytes
    simp only [byteEvent, Finset.mem_filter, Finset.mem_univ, and_self]
  unfold uniformByteProbability
  rw [he, Finset.card_univ]
  exact div_self hn

theorem uniform_byte_probability_bound (points : Finset Element) (d : Nat)
    (hd : points.card ≤ d) :
    uniformByteProbability points ≤ (d : ℚ) * (fiberCeiling : ℚ)^3 / (wordSize : ℚ)^3 := by
  have h := actual_120byte_point_set_preimage_bound points d hd
  have hc : ((byteEvent points).card : ℚ) ≤ (d : ℚ) * (fiberCeiling : ℚ)^3 := by
    exact_mod_cast h
  unfold uniformByteProbability
  rw [actual_120byte_cardinality, Nat.cast_pow]
  exact div_le_div_of_nonneg_right hc (by positivity)

theorem uniform_byte_probability_product_form (points : Finset Element) (d : Nat)
    (hd : points.card ≤ d) :
    uniformByteProbability points ≤ (d : ℚ) * ((fiberCeiling : ℚ) / (wordSize : ℚ))^3 := by
  have h := uniform_byte_probability_bound points d hd
  rw [div_pow]
  simpa only [mul_div_assoc] using h

def quadraticPoints (claimA claimB : Element) (a b : WhirQuadratic.Message) : Finset Element :=
  WhirQuadratic.actualAgreementPoints claimA claimB a b Finset.univ

theorem actual_quadratic_byte_event_exact (claimA claimB : Element)
    (a b : WhirQuadratic.Message) :
    byteEvent (quadraticPoints claimA claimB a b) =
      Finset.univ.filter (fun bytes : ByteBlock 120 =>
        WhirFinal.quadratic (raw claimA) a.toRaw (Spongefish.reduceChallenge bytes.val).val =
        WhirFinal.quadratic (raw claimB) b.toRaw (Spongefish.reduceChallenge bytes.val).val) := by
  apply Finset.ext
  intro bytes
  simp only [byteEvent, quadraticPoints, WhirQuadratic.actualAgreementPoints,
    Finset.mem_filter, Finset.mem_univ, true_and, reduceBytes, raw]

/-- One fixed quadratic comparison under the EXPLICIT uniform 120-byte law.
The ceiling factor includes the actual modulo-reduction bias. No independence
from preceding messages and no uniformity of Keccak is concluded. -/
theorem fixed_quadratics_uniform_byte_probability_bound (claimA claimB : Element)
    (a b : WhirQuadratic.Message) (hne : claimA ≠ claimB) :
    uniformByteProbability (quadraticPoints claimA claimB a b) ≤
      2 * ((fiberCeiling : ℚ) / (wordSize : ℚ))^3 := by
  exact uniform_byte_probability_product_form (quadraticPoints claimA claimB a b) 2
    (WhirQuadratic.fixed_different_claims_agree_at_most_two claimA claimB a b hne Finset.univ)

/-- The same bound with 2^320 and the integer ceiling written explicitly.
The quotient inside the numerator is NATURAL division; the outer division
and cube are rational. No rounding correction is omitted. -/
theorem fixed_quadratics_uniform_bound_explicit (claimA claimB : Element)
    (a b : WhirQuadratic.Message) (hne : claimA ≠ claimB) :
    uniformByteProbability (quadraticPoints claimA claimB a b) ≤
      2 * (((((2^320 + Arithmetic.modulus - 1) / Arithmetic.modulus : Nat) : ℚ)) /
        (2 : ℚ)^320)^3 := by
  simpa only [fiberCeiling, ceilingQuotient, word_size_is_320_bits, Nat.cast_pow, Nat.cast_ofNat] using
    fixed_quadratics_uniform_byte_probability_bound claimA claimB a b hne

end Audit.Wire3.WhirChallenge
