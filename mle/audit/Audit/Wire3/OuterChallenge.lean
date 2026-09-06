import Audit.Wire3.OuterRound
import Audit.Wire3.WhirChallenge

/-!
# OUTER MLE: three actual 32-byte digest reductions and an explicit uniform law

Source: TranscriptV2.sol squeezeChallenge/squeezeExt3/commitCoupledOuterRound
(219–260), transcript_v2.rs (98–146). Each OUTER Ext3 consists of three
separate 32-byte digest reductions with consecutive little-endian counters.
This is NOT Spongefish's single 120-byte squeeze split into three 40-byte words.
Only generic byte/int bijections and quotient/cardinality lemmas are reused
from WhirChallenge; no inner challenge reducer or inner quadratic is used.

squeezeExt3 executes the existing Transcript.squeeze three times, retaining
the same digest and its actual counters. Its result is proved equal to the
reduction of those SAME three actual hash outputs, not unrelated observations.
The uniform law below is DEFINED on all triples of 32-byte strings. No theorem
derives this law, independence, adaptive fixedness or conditional ROM security
from the deterministic Hash input. The degree-bound event uses the actual outer
Verifier.evaluateRound via OuterRound, for two FIXED different claims/messages.
Log/gate degree specializations are separate one-lane bounds, not a product
bound or security amplification attributed to their coupled transcript order.

The Rust/EVM modulo-reduction word loops and hash implementation are still
manual-refinement/cryptographic boundaries. Counter statements describe the
existing checked nonoverflowing Transcript model, not Rust overflow build modes.
No full MLE/PCS or genuine circuit-polynomial theorem is claimed.
-/
namespace Audit.Wire3.OuterChallenge
open Audit.Wire3 GoldilocksExt3Field
set_option maxRecDepth 4096

abbrev DigestBlock := WhirChallenge.ByteBlock 32
abbrev DigestTriple := DigestBlock × DigestBlock × DigestBlock

def digestBlock (d : Transcript.Digest) : DigestBlock := ⟨d.bytes,d.length_eq⟩

def actualDigests (hash : Transcript.Hash) (s : Transcript.State) : DigestTriple :=
  (digestBlock (hash (Transcript.challengeInput s.digest s.counter)),
   digestBlock (hash (Transcript.challengeInput s.digest (s.counter+1))),
   digestBlock (hash (Transcript.challengeInput s.digest (s.counter+2))))

def reduceTriple (ds : DigestTriple) : Element :=
  ⟨⟨⟨Transcript.fromLe ds.1.val % Arithmetic.modulus,
    Transcript.fromLe ds.2.1.val % Arithmetic.modulus,
    Transcript.fromLe ds.2.2.val % Arithmetic.modulus⟩,
    Nat.mod_lt _ Arithmetic.modulus_positive,Nat.mod_lt _ Arithmetic.modulus_positive,
    Nat.mod_lt _ Arithmetic.modulus_positive⟩⟩

def packFields (a b c : Transcript.Field) : Verifier.Ext3 :=
  ⟨⟨a.val,b.val,c.val⟩,a.isLt,b.isLt,c.isLt⟩

def squeezeExt3 (hash : Transcript.Hash) (s : Transcript.State) :
    Option (Verifier.Ext3 × Transcript.State) := do
  let (a,s1) ← Transcript.squeeze hash s
  let (b,s2) ← Transcript.squeeze hash s1
  let (c,s3) ← Transcript.squeeze hash s2
  pure (packFields a b c,s3)

theorem actual_digest_reduction_uses_consecutive_counters (hash : Transcript.Hash) (s : Transcript.State) :
    (reduceTriple (actualDigests hash s)).toVerifier =
      packFields (Transcript.challengeAt hash s.digest s.counter)
        (Transcript.challengeAt hash s.digest (s.counter+1))
        (Transcript.challengeAt hash s.digest (s.counter+2)) := rfl

theorem squeeze_ext3_at_bounded_counter (hash : Transcript.Hash) (s : Transcript.State)
    (h : s.counter+3 < Transcript.u64Limit) :
    squeezeExt3 hash s =
      some ((reduceTriple (actualDigests hash s)).toVerifier,⟨s.digest,s.counter+3⟩) := by
  have h1 : s.counter+1 < Transcript.u64Limit := by omega
  have h2 : s.counter+1+1 < Transcript.u64Limit := by omega
  have h3 : s.counter+1+1+1 < Transcript.u64Limit := by omega
  simp only [squeezeExt3,Transcript.squeeze,if_pos h1,if_pos h2,if_pos h3,
    bind,Option.bind,pure]
  rfl

theorem squeeze_ext3_success (hash : Transcript.Hash) (s t : Transcript.State) (x : Verifier.Ext3)
    (h : squeezeExt3 hash s = some (x,t)) :
    x = (reduceTriple (actualDigests hash s)).toVerifier ∧
      t.digest=s.digest ∧ t.counter=s.counter+3 ∧ t.counter<Transcript.u64Limit := by
  unfold squeezeExt3 at h
  cases h1 : Transcript.squeeze hash s with
  | none => simp [h1] at h
  | some pair =>
    obtain ⟨a,s1⟩ := pair
    cases h2 : Transcript.squeeze hash s1 with
    | none => simp [h1,h2] at h
    | some pair =>
      obtain ⟨b,s2⟩ := pair
      cases h3 : Transcript.squeeze hash s2 with
      | none => simp [h1,h2,h3] at h
      | some pair =>
        obtain ⟨c,s3⟩ := pair
        simp only [h1,h2,h3,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨hx,ht⟩ := h
        have hs1 := Transcript.squeeze_success hash s s1 a h1
        have hs2 := Transcript.squeeze_success hash s1 s2 b h2
        have hs3 := Transcript.squeeze_success hash s2 s3 c h3
        have hb : s.counter+3 < Transcript.u64Limit := by omega
        have he := squeeze_ext3_at_bounded_counter hash s hb
        have hh : squeezeExt3 hash s = some (x,t) := by
          simp only [squeezeExt3,h1,h2,h3,bind,Option.bind,pure,hx,ht]
        rw [he] at hh
        cases hh
        exact ⟨rfl,rfl,rfl,hb⟩

theorem squeeze_ext3_rejects_nonrepresentable_counter (hash : Transcript.Hash) (s : Transcript.State)
    (h : ¬ s.counter+3 < Transcript.u64Limit) : squeezeExt3 hash s = none := by
  cases he : squeezeExt3 hash s with
  | none => rfl
  | some pair =>
    obtain ⟨x,t⟩ := pair
    have hs := squeeze_ext3_success hash s t x he
    exact (h (by omega)).elim

theorem actual_three_digest_inputs_are_distinct (s : Transcript.State)
    (h : s.counter+3 < Transcript.u64Limit) :
    Transcript.challengeInput s.digest s.counter ≠ Transcript.challengeInput s.digest (s.counter+1) ∧
    Transcript.challengeInput s.digest s.counter ≠ Transcript.challengeInput s.digest (s.counter+2) ∧
    Transcript.challengeInput s.digest (s.counter+1) ≠ Transcript.challengeInput s.digest (s.counter+2) := by
  have hi : s.counter<Transcript.u64Limit := by omega
  have h1 : s.counter+1<Transcript.u64Limit := by omega
  have h2 : s.counter+2<Transcript.u64Limit := by omega
  constructor
  · intro he
    have := Transcript.challenge_inputs_distinguish_bounded_counters s.digest _ _ hi h1 he
    omega
  constructor
  · intro he
    have := Transcript.challenge_inputs_distinguish_bounded_counters s.digest _ _ hi h2 he
    omega
  · intro he
    have := Transcript.challenge_inputs_distinguish_bounded_counters s.digest _ _ h1 h2 he
    omega

def wordSize : Nat := 256^32
def fiberCeiling : Nat := WhirChallenge.ceilingQuotient wordSize Arithmetic.modulus
abbrev Word := Fin wordSize
abbrev Sample := Word × Word × Word
abbrev QuotientSample := Fin fiberCeiling × Fin fiberCeiling × Fin fiberCeiling

theorem word_size_is_256_bits : wordSize=2^256 := by norm_num [wordSize]
theorem word_size_positive : 0<wordSize := pow_pos (by decide) _

def tripleEquiv : DigestTriple ≃ Sample :=
  Equiv.prodCongr (WhirChallenge.wordEquiv 32)
    (Equiv.prodCongr (WhirChallenge.wordEquiv 32) (WhirChallenge.wordEquiv 32))

theorem actual_tuple_word_values_exact (ds : DigestTriple) :
    (tripleEquiv ds).1.val=Transcript.fromLe ds.1.val ∧
    (tripleEquiv ds).2.1.val=Transcript.fromLe ds.2.1.val ∧
    (tripleEquiv ds).2.2.val=Transcript.fromLe ds.2.2.val := ⟨rfl,rfl,rfl⟩

theorem digest_tuple_cardinality : Fintype.card DigestTriple=wordSize^3 := by
  rw [Fintype.card_congr tripleEquiv]
  simp only [Fintype.card_prod,Fintype.card_fin]
  ring

def reduceSample (s : Sample) : Element :=
  ⟨⟨⟨s.1.val%Arithmetic.modulus,s.2.1.val%Arithmetic.modulus,s.2.2.val%Arithmetic.modulus⟩,
    Nat.mod_lt _ Arithmetic.modulus_positive,Nat.mod_lt _ Arithmetic.modulus_positive,
    Nat.mod_lt _ Arithmetic.modulus_positive⟩⟩

theorem tuple_reduction_is_same_words (ds : DigestTriple) :
    reduceSample (tripleEquiv ds)=reduceTriple ds := rfl

def quotientSample (s : Sample) : QuotientSample :=
  (WhirChallenge.quotientCode wordSize Arithmetic.modulus word_size_positive Arithmetic.modulus_positive s.1,
   WhirChallenge.quotientCode wordSize Arithmetic.modulus word_size_positive Arithmetic.modulus_positive s.2.1,
   WhirChallenge.quotientCode wordSize Arithmetic.modulus word_size_positive Arithmetic.modulus_positive s.2.2)

theorem reduction_and_quotients_determine_sample (a b : Sample)
    (hr : reduceSample a=reduceSample b) (hq : quotientSample a=quotientSample b) : a=b := by
  have hr0 := congrArg (fun x : Element => (WhirPolynomial.raw x).c0) hr
  have hr1 := congrArg (fun x : Element => (WhirPolynomial.raw x).c1) hr
  have hr2 := congrArg (fun x : Element => (WhirPolynomial.raw x).c2) hr
  have hq0 := congrArg (fun x : QuotientSample => x.1.val) hq
  have hq1 := congrArg (fun x : QuotientSample => x.2.1.val) hq
  have hq2 := congrArg (fun x : QuotientSample => x.2.2.val) hq
  exact Prod.ext (WhirChallenge.same_remainder_and_quotient_are_same_word _ _ a.1 b.1 hr0 hq0)
    (Prod.ext (WhirChallenge.same_remainder_and_quotient_are_same_word _ _ a.2.1 b.2.1 hr1 hq1)
      (WhirChallenge.same_remainder_and_quotient_are_same_word _ _ a.2.2 b.2.2 hr2 hq2))

theorem quotient_sample_cardinality : Fintype.card QuotientSample=fiberCeiling^3 := by
  simp only [Fintype.card_prod,Fintype.card_fin]
  ring

def tupleEvent (points : Finset Element) : Finset DigestTriple :=
  Finset.univ.filter (fun ds => reduceTriple ds ∈ points)

theorem fixed_point_set_preimage_bound (points : Finset Element) :
    (tupleEvent points).card ≤ points.card*fiberCeiling^3 := by
  have he := WhirChallenge.equiv_event_card tripleEquiv (fun s : Sample => reduceSample s ∈ points)
  have hi : Function.Injective (fun s : Sample => (reduceSample s,quotientSample s)) := by
    intro a b hh
    exact reduction_and_quotients_determine_sample a b (congrArg Prod.fst hh) (congrArg Prod.snd hh)
  have hb := WhirChallenge.event_bound_by_residue_and_code reduceSample quotientSample hi points
  simpa only [tuple_reduction_is_same_words,← he,quotient_sample_cardinality] using hb

theorem fixed_value_preimage_bound (value : Element) :
    (Finset.univ.filter (fun ds : DigestTriple => reduceTriple ds=value)).card ≤ fiberCeiling^3 := by
  simpa only [tupleEvent,Finset.mem_singleton,Finset.card_singleton,Nat.one_mul] using
    fixed_point_set_preimage_bound {value}

/-- Explicit ideal law: each triple of 32-byte outputs has the same mass.
This is not asserted for actualDigests(hash,state) for any deterministic hash. -/
def uniformTupleProbability (points : Finset Element) : ℚ :=
  ((tupleEvent points).card : ℚ)/(Fintype.card DigestTriple : ℚ)

theorem uniform_probability_between_zero_and_one (points : Finset Element) :
    0≤uniformTupleProbability points ∧ uniformTupleProbability points≤1 := by
  have hp : 0<(Fintype.card DigestTriple : ℚ) := by
    rw [digest_tuple_cardinality,Nat.cast_pow]
    exact pow_pos (Nat.cast_pos.mpr word_size_positive) _
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hp.le
  · apply (div_le_one hp).mpr
    exact_mod_cast (tupleEvent points).card_le_univ

theorem uniform_tuple_probability_bound (points : Finset Element) (d : Nat) (hd : points.card≤d) :
    uniformTupleProbability points ≤ (d : ℚ)*((fiberCeiling : ℚ)/(wordSize : ℚ))^3 := by
  have hb := (fixed_point_set_preimage_bound points).trans (Nat.mul_le_mul_right (fiberCeiling^3) hd)
  have hr : ((tupleEvent points).card : ℚ) ≤ (d : ℚ)*(fiberCeiling : ℚ)^3 := by exact_mod_cast hb
  unfold uniformTupleProbability
  rw [digest_tuple_cardinality,Nat.cast_pow,div_pow,← mul_div_assoc]
  exact div_le_div_of_nonneg_right hr (by positivity)

def outerAgreementPoints (claimA claimB : Element) (a b : List Element) : Finset Element :=
  OuterRound.actualAgreementPoints claimA claimB a b Finset.univ

theorem outer_round_tuple_event_exact (claimA claimB : Element) (a b : List Element) :
    tupleEvent (outerAgreementPoints claimA claimB a b) =
      Finset.univ.filter (fun ds : DigestTriple =>
        Verifier.evaluateRound claimA.toVerifier (a.map Element.toVerifier) (reduceTriple ds).toVerifier =
        Verifier.evaluateRound claimB.toVerifier (b.map Element.toVerifier) (reduceTriple ds).toVerifier) := by
  apply Finset.ext
  intro ds
  simp only [tupleEvent,outerAgreementPoints,OuterRound.actualAgreementPoints,Finset.mem_filter,
    Finset.mem_univ,true_and]

theorem fixed_different_outer_claims_uniform_bound (claimA claimB : Element) (a b : List Element)
    (hne : claimA≠claimB) (d : Nat) (ha : a.length≤d) (hb : b.length≤d) :
    uniformTupleProbability (outerAgreementPoints claimA claimB a b) ≤
      (d : ℚ)*((fiberCeiling : ℚ)/(wordSize : ℚ))^3 :=
  uniform_tuple_probability_bound _ d
    (OuterRound.fixed_different_claims_agree_at_most_degree claimA claimB a b hne d ha hb Finset.univ)

theorem fixed_different_outer_claims_uniform_bound_explicit (claimA claimB : Element) (a b : List Element)
    (hne : claimA≠claimB) (d : Nat) (ha : a.length≤d) (hb : b.length≤d) :
    uniformTupleProbability (outerAgreementPoints claimA claimB a b) ≤
      (d : ℚ)*(((((2^256+Arithmetic.modulus-1)/Arithmetic.modulus : Nat) : ℚ))/(2 : ℚ)^256)^3 := by
  simpa only [fiberCeiling,WhirChallenge.ceilingQuotient,word_size_is_256_bits,Nat.cast_pow,Nat.cast_ofNat] using
    fixed_different_outer_claims_uniform_bound claimA claimB a b hne d ha hb

/-- Same real accepted challenge, now related to the derived outer polynomial.
No probability assertion about this particular deterministic hash is made. -/
theorem actual_squeeze_round_update_is_derived_polynomial (hash : Transcript.Hash)
    (s t : Transcript.State) (r : Verifier.Ext3) (h : squeezeExt3 hash s=some (r,t))
    (claim : Verifier.Ext3) (cs : List Verifier.Ext3) :
    Verifier.evaluateRound claim cs r =
      ((OuterRound.polynomial (OuterRound.lift claim) (cs.map OuterRound.lift)).eval
        (reduceTriple (actualDigests hash s))).toVerifier := by
  have hr := (squeeze_ext3_success hash s t r h).1
  rw [hr]
  exact OuterRound.actual_typed_round_is_polynomial_eval claim _ cs

def serializedExt3 (a : Verifier.Ext3) : Transcript.Ext3 :=
  ⟨⟨a.val.c0,a.property.1⟩,⟨a.val.c1,a.property.2.1⟩,⟨a.val.c2,a.property.2.2⟩⟩

theorem serialized_coefficients_keep_all_limbs (a : Verifier.Ext3) :
    packFields (serializedExt3 a).c0 (serializedExt3 a).c1 (serializedExt3 a).c2 = a :=
  Subtype.eq (by cases a; rfl)

/-- Execute the existing full commit-before-six-squeezes function; the pattern
only packages its already-proved six base fields as the two source Ext3 values. -/
def coupledChallenges (hash : Transcript.Hash) (s : Transcript.State) (round : Nat)
    (log gate : List Verifier.Ext3) : Option ((Verifier.Ext3 × Verifier.Ext3) × Transcript.State) := do
  let (fields,t) ← Transcript.coupledRound hash s round
    (log.map serializedExt3) (gate.map serializedExt3)
  match fields with
  | [a,b,c,d,e,f] => some ((packFields a b c,packFields d e f),t)
  | _ => none

theorem actual_coupled_six_fields (hash : Transcript.Hash) (s t : Transcript.State)
    (round : Nat) (log gate : List Transcript.Ext3) (fields : List Transcript.Field)
    (h : Transcript.coupledRound hash s round log gate=some (fields,t)) :
    let d := (Transcript.commitRound hash s round log gate).digest
    fields=[Transcript.challengeAt hash d 0,Transcript.challengeAt hash d 1,
      Transcript.challengeAt hash d 2,Transcript.challengeAt hash d 3,
      Transcript.challengeAt hash d 4,Transcript.challengeAt hash d 5] ∧
      t.digest=d ∧ t.counter=6 := by
  unfold Transcript.coupledRound at h
  split at h
  · change Transcript.squeezeMany hash 6
      ⟨(Transcript.commitRound hash s round log gate).digest,0⟩=some (fields,t) at h
    rw [Transcript.six_squeezes_use_consecutive_inputs] at h
    cases h
    exact ⟨rfl,rfl,rfl⟩
  · simp at h

theorem coupled_success_uses_same_committed_digest_and_six_counters
    (hash : Transcript.Hash) (s t : Transcript.State) (round : Nat)
    (log gate : List Verifier.Ext3) (rl rg : Verifier.Ext3)
    (h : coupledChallenges hash s round log gate=some ((rl,rg),t)) :
    let d := (Transcript.commitRound hash s round
      (log.map serializedExt3) (gate.map serializedExt3)).digest
    rl=(reduceTriple (actualDigests hash ⟨d,0⟩)).toVerifier ∧
      rg=(reduceTriple (actualDigests hash ⟨d,3⟩)).toVerifier ∧ t.digest=d ∧ t.counter=6 := by
  unfold coupledChallenges at h
  cases hc : Transcript.coupledRound hash s round (log.map serializedExt3) (gate.map serializedExt3) with
  | none => simp [hc] at h
  | some pair =>
    obtain ⟨fields,after⟩ := pair
    obtain ⟨hf,hd,hn⟩ := actual_coupled_six_fields hash s after round
      (log.map serializedExt3) (gate.map serializedExt3) fields hc
    simp only [hc,bind,Option.bind,hf,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨⟨hlog,hgate⟩,ht⟩ := h
    subst rl
    subst rg
    subst t
    exact ⟨rfl,rfl,hd,hn⟩

theorem coupled_success_updates_both_same_actual_polynomials
    (hash : Transcript.Hash) (s t : Transcript.State) (round : Nat)
    (log gate : List Verifier.Ext3) (rl rg claimLog claimGate : Verifier.Ext3)
    (h : coupledChallenges hash s round log gate=some ((rl,rg),t)) :
    let d := (Transcript.commitRound hash s round
      (log.map serializedExt3) (gate.map serializedExt3)).digest
    Verifier.evaluateRound claimLog log rl=
      ((OuterRound.polynomial (OuterRound.lift claimLog) (log.map OuterRound.lift)).eval
        (reduceTriple (actualDigests hash ⟨d,0⟩))).toVerifier ∧
    Verifier.evaluateRound claimGate gate rg=
      ((OuterRound.polynomial (OuterRound.lift claimGate) (gate.map OuterRound.lift)).eval
        (reduceTriple (actualDigests hash ⟨d,3⟩))).toVerifier := by
  obtain ⟨hl,hg,_,_⟩ := coupled_success_uses_same_committed_digest_and_six_counters
    hash s t round log gate rl rg h
  rw [hl,hg]
  exact ⟨OuterRound.actual_typed_round_is_polynomial_eval claimLog _ log,
    OuterRound.actual_typed_round_is_polynomial_eval claimGate _ gate⟩

theorem outer_log_degree_five_uniform_bound (claimA claimB : Element) (a b : List Element)
    (hne : claimA≠claimB) (ha : a.length=5) (hb : b.length=5) :
    uniformTupleProbability (outerAgreementPoints claimA claimB a b) ≤
      5*((fiberCeiling : ℚ)/(wordSize : ℚ))^3 :=
  fixed_different_outer_claims_uniform_bound claimA claimB a b hne 5 (by omega) (by omega)

theorem outer_gate_configured_degree_uniform_bound (quotientDegree : Nat)
    (claimA claimB : Element) (a b : List Element) (hne : claimA≠claimB)
    (ha : a.length=quotientDegree+2) (hb : b.length=quotientDegree+2) :
    uniformTupleProbability (outerAgreementPoints claimA claimB a b) ≤
      ((quotientDegree+2 : Nat) : ℚ)*((fiberCeiling : ℚ)/(wordSize : ℚ))^3 :=
  fixed_different_outer_claims_uniform_bound claimA claimB a b hne (quotientDegree+2)
    (by omega) (by omega)

def ordinaryDigest : Transcript.Digest :=
  ⟨Transcript.le 32 5,Transcript.le_length 32 5⟩

theorem ordinary_outer_three_digest_example :
    (squeezeExt3 (fun _ => ordinaryDigest) ⟨ordinaryDigest,7⟩).map
      (fun pair => (pair.1.val,pair.2.counter)) = some (⟨5,5,5⟩,10) := by decide

theorem ordinary_coupled_nonempty_messages_example :
    (coupledChallenges (fun _ => ordinaryDigest) ⟨ordinaryDigest,99⟩ 4
      [Norm.embed 2,Norm.embed 3] [Norm.embed 7]).map
      (fun pair => (pair.1.1.val,pair.1.2.val,pair.2.counter)) =
      some (⟨5,5,5⟩,⟨5,5,5⟩,6) := by decide

end Audit.Wire3.OuterChallenge
