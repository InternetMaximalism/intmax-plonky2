import Audit.Wire3.InstalledWhirTail
import Audit.Wire3.CommitmentOrder
import Audit.Wire3.JointChallengeSpace
import Audit.Wire3.TranscriptProvenance

/-!
# Installing the concrete constituent-index sampler into the outer engine

## What this module does

`Verifier.Engine.sampleIndices : Bytes -> UsedClaims -> Nat -> IndexPoints`
(Verifier.lean 350) is an OBSERVATION, and `Verifier.derivedIndices e c p =
e.sampleIndices (derivedRounds e c p).transcript p.used c.indexBits`
(Verifier.lean 389-390) is the only place the outer index points come from.
`InstalledWhirTail.installedEngine` installs the WHIR tail but leaves
`sampleIndices` abstract (`installed_engine_keeps_every_other_field`), and two
adopted facts lean on it being the REAL sampler:

* R1b's remark that per-column identification (residue R3) comes from "idx
  sampled AFTER the used claims are absorbed" -- an OBSERVATION in
  `InstalledWhirTail`'s header, because an abstract `sampleIndices` need not
  read `p.used` at all;
* the outer index points feed `OpenedClaimFold.boundCell`, hence every bound
  cell of `Verifier.expectedClaims`.

`installedSamplerEngine e decode hash wp thash` is
`InstalledWhirTail.installedEngine e decode hash wp` with `sampleIndices`
replaced by `concreteSampleIndices thash`, which is the ADOPTED checked sampler
`OuterAdapter.sampleResult` (OuterAdapter.lean 190-193) totalised over the
snapshot decode. Nothing about the concrete sampler is re-proved here: it is the
adopted `Transcript.commitClaims` / `OuterInitial.drawMany` pair, reached across
the newly closed interface.

## The absorb/squeeze order this installs, with source citations

Rust, `prover_v2.rs::absorb_v2_claims_and_sample_indices` (prover_v2.rs 144-164),
called by the VERIFIER at `verifier_v2.rs` 303-311:

1. `transcript.domain_separate(DOMAIN_CONSTITUENT_CLAIMS_V2)` -- prover_v2.rs
   153; the label is `"pcs-constituent-claims-v3"` (generated/mle_whir_v2.rs 99).
2. `absorb_ext3_vec` of `log_preprocessed`, `log_witness`, `log_norm_inverse`,
   `gate_preprocessed`, `gate_witness` and then of the EMPTY slice -- prover_v2.rs
   154-159. Six frames, tag `TAG_EXT3_VEC_V2 = 6` (generated/mle_whir_v2.rs 49),
   payload `len_u64_le || (c0 || c1 || c2)*` (transcript_v2.rs 87-96).
3. `transcript.domain_separate(DOMAIN_CONSTITUENT_INDEX_V2)` -- prover_v2.rs 160;
   label `"pcs-constituent-index-v3"` (generated/mle_whir_v2.rs 100).
4. `(0..NUM_PCS_TERMINAL_POINTS_V2).map(|_| squeeze_ext3_challenges(index_bits))`
   -- prover_v2.rs 161-163, with `NUM_PCS_TERMINAL_POINTS_V2 = 2`
   (generated/mle_whir_v2.rs 102), `POINT_LOG_V2 = 0`, `POINT_GATE_V2 = 1`
   (108-109). So the LOG lane is squeezed first, then the GATE lane.

Each `squeeze_ext3` is three consecutive `squeeze_challenge` calls
(transcript_v2.rs 113-121), each hashing
`CHALLENGE_PREFIX || state || counter_u64_le` and bumping the counter
(transcript_v2.rs 98-107); `absorb_frame` resets the counter to zero
(transcript_v2.rs 43-53). Hence, with `d` the digest after step 3 and
`b = index_bits`, the log point's coordinate `i` uses counters `3i, 3i+1, 3i+2`
and the gate point's coordinate `i` uses `3b+3i, 3b+3i+1, 3b+3i+2` -- exactly
what `sampled_log_index_counter` / `sampled_gate_index_counter` say.

Solidity, `MleVerifierV2.sol::_absorbClaimsAndSampleIndices` (458-476), called
at MleVerifierV2.sol 349: the same six `absorbExt3Vec*` frames between the same
two `domainSeparate` calls (463-470), then two `_squeezeExt3Vector(transcript,
indexBits)` calls in the loop at 472-475 (`_squeezeExt3Vector` at 675-684,
`TranscriptV2.squeezeExt3` at 236-240, `squeezeChallenge` at 219-234). The
`absorbExt3VecPrevalidated` variant differs from `absorbExt3Vec` only in
skipping the canonicality precheck, not in the bytes it frames
(TranscriptV2.sol 116-133).

The adopted model already carries all of this: `Transcript.commitClaims`
(Transcript.lean 247-256) is steps 1-3, `OuterAdapter.claimsCommitted`
(OuterAdapter.lean 173-177) applies it to a `Verifier.UsedClaims`, and
`OuterAdapter.sampleResult` (OuterAdapter.lean 190-193) is step 4 through
`OuterInitial.drawMany`. **This module reuses them; it defines no new
serialization.**

## What is installed and what is still an OBSERVATION

INSTALLED (concrete, executable): `foldClaim`, `normEvaluation`, `eqEvaluation`,
`gateEvaluation` (from `Integrated.modelEngine`), `whirTail` (from
`InstalledWhirTail`) and, new here, `sampleIndices`.

STILL OBSERVATIONS, unchanged and opaque: `parseWhir`, `configurationHash`,
`deploymentValid`, `initialObservation` (hence `initialTranscript`),
`commitRound` and `publicInputsHash`. In particular the transcript snapshot the
sampler decodes is produced by the ABSTRACT `commitRound`; every theorem below
that needs a decoded state takes `OuterAdapter.decode (derivedRounds e c p).transcript
= some st` as an explicit hypothesis, and `installed_sampler_matches_the_checked_execution`
is the one statement that connects it to the adopted checked execution, under
the adopted `OuterAdapter.CommitAgrees` hypothesis.

That hypothesis is not vacuous. `decoded_snapshot_exists_under_checked_execution`
(section 4) DISCHARGES it under exactly those adopted hypotheses: a successful
adopted checked `OuterAdapter.execute` produces the derived rounds, and
`OuterAdapter.sample_decode_failure` then rules out a non-decoding snapshot.
`fixture_snapshot_decodes_for_every_hash` instantiates that on the adopted
`OuterAdapter.fixtureConfig` / `fixtureProof` for EVERY `thash`, via the adopted
`OuterAdapter.ordinary_prefix_for_every_hash`, so the decode instances of this
module are not confined to the hand-made `toySnapshot` of section 8.

## What is NOT proved

`hash` and `thash` are arbitrary deterministic functions. No hash security, no
collision resistance (`CommitmentOrder.TranscriptCollision` is always a
CONCLUSION here, never a hypothesis), no random-oracle property, no
Fiat--Shamir soundness, no WHIR/PCS soundness, no Rust/Yul/Solidity refinement.
The model is a manual reading of the sources cited above.

Half (B) of the Fiat--Shamir reading -- that the actual index draw is
DISTRIBUTED by the uniform law on `IndexSpace` -- is NOT formalized, here or
anywhere in the adopted tree; section 6 builds the finite space and proves the
run's points are its coordinates, and stops there. Consequently the R3
(per-column identification) hook of section 8 is an ORDERING theorem plus a
non-malleability theorem; the PROBABILISTIC step -- that a forged cell family
cannot survive a freshly sampled index point -- remains unproved.

Nothing here is the deployed system's soundness error. The wire-v3 WHIR profile
this models is the ~100-bit design point. No figure in this module is a security
level, and in particular nothing here says "125".
-/

namespace Audit.Wire3.InstalledIndexSampler

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The claim frames: the exact absorbed material before the index squeeze -/

/-- The eight frames the source absorbs between the last coupled round and the
first index squeeze, in source order: the claims domain separator, the six
`TAG_EXT3_VEC_V2` cell frames (the sixth is the explicitly EMPTY gate/norm
cell), and the index domain separator. This is `Transcript.commitClaims` written
as an `OuterInitial.Message` list so that the adopted
`CommitmentOrder.absorb_messages_bind_or_collide` applies to it verbatim. -/
def claimFrames (u : Verifier.UsedClaims) : List OuterInitial.Message :=
  (OuterInitial.domainMessage "pcs-constituent-claims-v3" ::
    (OuterAdapter.claimCells u).map (fun xs => ⟨6, OuterAdapter.encodedVec xs⟩)) ++
    [OuterInitial.domainMessage "pcs-constituent-index-v3"]

theorem claim_frame_count (u : Verifier.UsedClaims) : (claimFrames u).length = 8 := rfl

/-- (1) The adopted `OuterAdapter.claimsCommitted` IS the fold of those eight
frames. Nothing is re-serialized: this is `rfl`. -/
theorem claims_committed_is_the_frame_fold (thash : Transcript.Hash) (s : Transcript.State)
    (u : Verifier.UsedClaims) :
    OuterAdapter.claimsCommitted thash s u = OuterInitial.absorbMessages thash s (claimFrames u) :=
  rfl

theorem claim_frames_get_log_preprocessed (u : Verifier.UsedClaims) :
    (claimFrames u).get? 1 = some ⟨6, OuterAdapter.encodedVec u.logPreprocessed⟩ := rfl
theorem claim_frames_get_log_witness (u : Verifier.UsedClaims) :
    (claimFrames u).get? 2 = some ⟨6, OuterAdapter.encodedVec u.logWitness⟩ := rfl
theorem claim_frames_get_log_norm_inverse (u : Verifier.UsedClaims) :
    (claimFrames u).get? 3 = some ⟨6, OuterAdapter.encodedVec u.logNormInverse⟩ := rfl
theorem claim_frames_get_gate_preprocessed (u : Verifier.UsedClaims) :
    (claimFrames u).get? 4 = some ⟨6, OuterAdapter.encodedVec u.gatePreprocessed⟩ := rfl
theorem claim_frames_get_gate_witness (u : Verifier.UsedClaims) :
    (claimFrames u).get? 5 = some ⟨6, OuterAdapter.encodedVec u.gateWitness⟩ := rfl

/-- (1) The sixth cell is the source's explicitly empty gate/norm-inverse cell,
and the two domain separators bracket the block. -/
theorem claim_frames_brackets (u : Verifier.UsedClaims) :
    (claimFrames u).get? 0 = some (OuterInitial.domainMessage "pcs-constituent-claims-v3") ∧
    (claimFrames u).get? 6 = some ⟨6, OuterAdapter.encodedVec []⟩ ∧
    (claimFrames u).get? 7 = some (OuterInitial.domainMessage "pcs-constituent-index-v3") :=
  ⟨rfl, rfl, rfl⟩

/-! ## 2. The cell encoding is injective -/

theorem ext3_bytes_injective (a b : Transcript.Ext3)
    (h : Transcript.ext3Bytes a = Transcript.ext3Bytes b) : a = b := by
  simp only [Transcript.ext3Bytes, List.append_assoc] at h
  obtain ⟨h0, h1⟩ := List.append_inj h (by
    simp only [Transcript.field_bytes_length])
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by
    simp only [Transcript.field_bytes_length])
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  simp only [Transcript.Ext3.mk.injEq]
  exact ⟨Transcript.field_encoding_injective _ _ h0, Transcript.field_encoding_injective _ _ h2,
    Transcript.field_encoding_injective _ _ h3⟩

theorem ext3_payload_injective : ∀ xs ys : List Transcript.Ext3,
    xs.bind Transcript.ext3Bytes = ys.bind Transcript.ext3Bytes → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          exfalso
          have hl := congrArg List.length h
          simp only [List.bind, List.join, List.map, List.length_nil, List.length_append,
            Transcript.ext3_bytes_length] at hl
          omega
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          exfalso
          have hl := congrArg List.length h
          simp only [List.bind, List.join, List.map, List.length_nil, List.length_append,
            Transcript.ext3_bytes_length] at hl
          omega
      | cons y ys =>
          have h' : Transcript.ext3Bytes x ++ xs.bind Transcript.ext3Bytes =
              Transcript.ext3Bytes y ++ ys.bind Transcript.ext3Bytes := by
            simpa only [List.bind_cons] using h
          obtain ⟨h0, h1⟩ := List.append_inj h' (by
            simp only [Transcript.ext3_bytes_length])
          exact congrArg₂ List.cons (ext3_bytes_injective x y h0) (ih ys h1)

/-- (2) The `TAG_EXT3_VEC_V2` payload determines the claim cell it frames. -/
theorem encoded_vec_injective (xs ys : List Verifier.Ext3)
    (h : OuterAdapter.encodedVec xs = OuterAdapter.encodedVec ys) : xs = ys := by
  simp only [OuterAdapter.encodedVec, Transcript.ext3VecBytes] at h
  obtain ⟨_, h1⟩ := List.append_inj h (by simp only [Transcript.le_length])
  have hmap := ext3_payload_injective _ _ h1
  have : ∀ as bs : List Verifier.Ext3,
      as.map Connections.toTranscript = bs.map Connections.toTranscript → as = bs := by
    intro as
    induction as with
    | nil => intro bs hb; cases bs with
      | nil => rfl
      | cons _ _ => simp at hb
    | cons a as iha =>
        intro bs hb
        cases bs with
        | nil => simp at hb
        | cons b bs =>
            simp only [List.map_cons, List.cons.injEq] at hb
            exact congrArg₂ List.cons (Connections.toTranscript_injective hb.1) (iha bs hb.2)
  exact this xs ys hmap

/-- (2) The eight-frame block determines the used claims. -/
theorem claim_frames_injective (u v : Verifier.UsedClaims) (h : claimFrames u = claimFrames v) :
    u = v := by
  have h1 := (claim_frames_get_log_preprocessed u).symm.trans ((congrArg (fun l => l.get? 1) h).trans
    (claim_frames_get_log_preprocessed v))
  have h2 := (claim_frames_get_log_witness u).symm.trans ((congrArg (fun l => l.get? 2) h).trans
    (claim_frames_get_log_witness v))
  have h3 := (claim_frames_get_log_norm_inverse u).symm.trans
    ((congrArg (fun l => l.get? 3) h).trans (claim_frames_get_log_norm_inverse v))
  have h4 := (claim_frames_get_gate_preprocessed u).symm.trans
    ((congrArg (fun l => l.get? 4) h).trans (claim_frames_get_gate_preprocessed v))
  have h5 := (claim_frames_get_gate_witness u).symm.trans
    ((congrArg (fun l => l.get? 5) h).trans (claim_frames_get_gate_witness v))
  obtain ⟨a1, a2, a3, a4, a5⟩ := u
  obtain ⟨b1, b2, b3, b4, b5⟩ := v
  simp only [Verifier.UsedClaims.mk.injEq]
  refine ⟨encoded_vec_injective _ _ ?_, encoded_vec_injective _ _ ?_,
    encoded_vec_injective _ _ ?_, encoded_vec_injective _ _ ?_, encoded_vec_injective _ _ ?_⟩
  · exact congrArg OuterInitial.Message.payload (Option.some.inj h1)
  · exact congrArg OuterInitial.Message.payload (Option.some.inj h2)
  · exact congrArg OuterInitial.Message.payload (Option.some.inj h3)
  · exact congrArg OuterInitial.Message.payload (Option.some.inj h4)
  · exact congrArg OuterInitial.Message.payload (Option.some.inj h5)


/-! ## 3. The concrete sampler, and its agreement with the adopted checked one -/

/-- Success of one checked Ext3 squeeze pins the counter bound AND the value:
it is the adopted total `OuterInitial.draw`. -/
theorem squeeze_ext3_success (thash : Transcript.Hash) (s t : Transcript.State)
    (x : Verifier.Ext3) (h : OuterInitial.squeezeExt3 thash s = some (x, t)) :
    s.counter + 3 < Transcript.u64Limit ∧ t.counter = s.counter + 3 ∧
      (x, t) = OuterInitial.draw thash s := by
  have hb : s.counter + 3 < Transcript.u64Limit := by
    unfold OuterInitial.squeezeExt3 at h
    cases h1 : Transcript.squeeze thash s with
    | none => simp [h1] at h
    | some pair =>
        obtain ⟨a, s1⟩ := pair
        cases h2 : Transcript.squeeze thash s1 with
        | none => simp [h1, h2] at h
        | some pair2 =>
            obtain ⟨b, s2⟩ := pair2
            cases h3 : Transcript.squeeze thash s2 with
            | none => simp [h1, h2, h3] at h
            | some pair3 =>
                obtain ⟨c, s3⟩ := pair3
                have hs1 := Transcript.squeeze_success thash s s1 a h1
                have hs2 := Transcript.squeeze_success thash s1 s2 b h2
                have hs3 := Transcript.squeeze_success thash s2 s3 c h3
                omega
  rw [OuterInitial.draw_matches_three_checked_squeezes thash s hb] at h
  have hpair : (x, t) = OuterInitial.draw thash s := (Option.some.inj h).symm
  refine ⟨hb, ?_, hpair⟩
  have := congrArg (fun q : Verifier.Ext3 × Transcript.State => q.2.counter) hpair
  simpa only [OuterInitial.draw_counter] using this

theorem squeeze_ext3_many_bound (thash : Transcript.Hash) :
    ∀ (n : Nat) (s t : Transcript.State) (xs : List Verifier.Ext3),
      s.counter < Transcript.u64Limit →
      OuterInitial.squeezeExt3Many thash n s = some (xs, t) →
      s.counter + 3 * n < Transcript.u64Limit := by
  intro n
  induction n with
  | zero => intro s t xs hs _hn; simpa using hs
  | succ n ih =>
      intro s t xs _hs h
      cases h1 : OuterInitial.squeezeExt3 thash s with
      | none => simp [OuterInitial.squeezeExt3Many, h1] at h
      | some pair =>
          obtain ⟨x, mid⟩ := pair
          cases h2 : OuterInitial.squeezeExt3Many thash n mid with
          | none => simp [OuterInitial.squeezeExt3Many, h1, h2] at h
          | some pair2 =>
              obtain ⟨ys, u⟩ := pair2
              have ha := squeeze_ext3_success thash s mid x h1
              have hb := ih mid u ys (by omega) h2
              omega

theorem squeeze_ext3_many_success (thash : Transcript.Hash) (n : Nat) (s t : Transcript.State)
    (xs : List Verifier.Ext3) (hs : s.counter < Transcript.u64Limit)
    (h : OuterInitial.squeezeExt3Many thash n s = some (xs, t)) :
    s.counter + 3 * n < Transcript.u64Limit ∧ (xs, t) = OuterInitial.drawMany thash n s := by
  have hb := squeeze_ext3_many_bound thash n s t xs hs h
  refine ⟨hb, ?_⟩
  rw [OuterInitial.draw_many_matches_checked_squeezes thash n s hb] at h
  exact (Option.some.inj h).symm

/-- Success of the adopted checked sampler exposes its two admission conditions:
the claim cells fit a u64 length field and the six-per-coordinate squeeze
counter does not overflow. -/
theorem sample_checked_success_conditions (thash : Transcript.Hash) (raw : Verifier.Bytes)
    (s : Transcript.State) (u : Verifier.UsedClaims) (bits : Nat) (r : OuterAdapter.SampleResult)
    (hd : OuterAdapter.decode raw = some s)
    (h : OuterAdapter.sampleChecked thash raw u bits = some r) :
    OuterAdapter.ClaimsFit u ∧ 6 * bits < Transcript.u64Limit := by
  by_cases hf : OuterAdapter.ClaimsFit u
  · refine ⟨hf, ?_⟩
    simp only [OuterAdapter.sampleChecked, hd, bind, Option.bind] at h
    rw [if_neg (not_not_intro hf)] at h
    cases h1 : OuterInitial.squeezeExt3Many thash bits (OuterAdapter.claimsCommitted thash s u) with
    | none => simp [h1] at h
    | some pair =>
        obtain ⟨lg, t⟩ := pair
        cases h2 : OuterInitial.squeezeExt3Many thash bits t with
        | none => simp [h1, h2] at h
        | some pair2 =>
            obtain ⟨gt, last⟩ := pair2
            have b1 := squeeze_ext3_many_success thash bits _ t lg
              (by rw [OuterAdapter.claims_commit_counter_zero]; unfold Transcript.u64Limit; omega) h1
            have ht : t = (OuterInitial.drawMany thash bits
                (OuterAdapter.claimsCommitted thash s u)).2 :=
              congrArg Prod.snd b1.2
            have htc : t.counter = 3 * bits := by
              rw [ht, (OuterInitial.draw_many_shape thash bits
                (OuterAdapter.claimsCommitted thash s u)).2.2,
                OuterAdapter.claims_commit_counter_zero]
              omega
            have b2 := squeeze_ext3_many_bound thash bits t last gt (by omega) h2
            omega
  · exfalso
    simp only [OuterAdapter.sampleChecked, hd, bind, Option.bind] at h
    rw [if_pos hf] at h
    exact Option.noConfusion h

/-- **THE CONCRETE SAMPLER.** The adopted checked sampler
`OuterAdapter.sampleResult` -- `Transcript.commitClaims` on the six claim cells,
then `2 * indexBits` `OuterInitial.draw`s -- totalised over the snapshot decode.
A malformed 40-byte snapshot yields the empty point pair, which fails the
verifier's own index-length guard whenever `indexBits` is positive
(`malformed_snapshot_fails_the_index_length_guard`); no fallback state and no
zero digest is invented. -/
def concreteSampleIndices (thash : Transcript.Hash) :
    Verifier.Bytes → Verifier.UsedClaims → Nat → Verifier.IndexPoints :=
  fun raw u bits =>
    match OuterAdapter.decode raw with
    | some s => (OuterAdapter.sampleResult thash s u bits).points
    | none => ⟨[], []⟩

theorem concrete_sampler_on_decoded_snapshot (thash : Transcript.Hash) (raw : Verifier.Bytes)
    (s : Transcript.State) (u : Verifier.UsedClaims) (bits : Nat)
    (hd : OuterAdapter.decode raw = some s) :
    concreteSampleIndices thash raw u bits = (OuterAdapter.sampleResult thash s u bits).points := by
  simp only [concreteSampleIndices, hd]

theorem concrete_sampler_rejects_malformed_snapshot (thash : Transcript.Hash)
    (raw : Verifier.Bytes) (u : Verifier.UsedClaims) (bits : Nat)
    (hd : OuterAdapter.decode raw = none) :
    concreteSampleIndices thash raw u bits = ⟨[], []⟩ := by
  simp only [concreteSampleIndices, hd]

/-- (3) The installed sampler IS the adopted checked sampler wherever the latter
succeeds, so the adopted `OuterAdapter.execute_matches_existing_derived_context`
applies to any engine carrying it. -/
theorem concrete_sampler_agrees_with_checked (thash : Transcript.Hash) :
    OuterAdapter.SamplesAgree thash (concreteSampleIndices thash) := by
  intro raw u bits r h
  cases hd : OuterAdapter.decode raw with
  | none =>
      rw [OuterAdapter.sample_decode_failure thash raw u bits hd] at h
      exact Option.noConfusion h
  | some s =>
      obtain ⟨hf, hb⟩ := sample_checked_success_conditions thash raw s u bits r hd h
      have he := OuterAdapter.sample_checked_exact thash raw s u bits hd hf hb
      rw [he] at h
      rw [concrete_sampler_on_decoded_snapshot thash raw s u bits hd, ← Option.some.inj h]

/-! ## 4. The engine with the sampler installed -/

abbrev VkParams := InstalledWhirTail.VkParams

/-- The outer engine with only `sampleIndices` replaced. Used to show that
installing the sampler is the same as installing the WHIR tail on top of an
engine that already carries it. -/
def resampled (e : Verifier.Engine) (thash : Transcript.Hash) : Verifier.Engine :=
  { e with sampleIndices := concreteSampleIndices thash }

/-- **THE ENGINE OF THIS MODULE.** `InstalledWhirTail.installedEngine` with the
concrete constituent-index sampler installed. `hash` is the WHIR/Merkle hash and
`thash` the outer transcript hash; in the source both are Keccak, but nothing in
the Lean model ties them, and both are arbitrary deterministic functions. -/
def installedSamplerEngine (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) : Verifier.Engine :=
  { InstalledWhirTail.installedEngine e gdec hash wp with
    sampleIndices := concreteSampleIndices thash }

/-- (4) Installing the sampler commutes with installing the tail, so EVERY
adopted `InstalledWhirTail` theorem -- including the R1b family -- applies to
this engine verbatim, with `e` replaced by `resampled e thash`. -/
theorem installed_sampler_is_installed_tail_of_resampled (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    installedSamplerEngine e gdec hash wp thash =
      InstalledWhirTail.installedEngine (resampled e thash) gdec hash wp := rfl

/-- (4) **THE TRANSCRIPT AND THE ROUNDS ARE UNCHANGED**, so every adopted result
that is quantified over an arbitrary engine still applies, and the derived
rounds fed to the sampler are exactly the ones the abstract engine produced. -/
theorem installed_sampler_keeps_transcript_and_rounds (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    (installedSamplerEngine e gdec hash wp thash).initialTranscript c p =
      e.initialTranscript c p ∧
    Verifier.derivedRounds (installedSamplerEngine e gdec hash wp thash) c p =
      Verifier.derivedRounds e c p ∧
    (installedSamplerEngine e gdec hash wp thash).commitRound = e.commitRound ∧
    (installedSamplerEngine e gdec hash wp thash).initialObservation = e.initialObservation :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem installed_sampler_installed_and_observed_fields (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) :
    (installedSamplerEngine e gdec hash wp thash).sampleIndices = concreteSampleIndices thash ∧
    (installedSamplerEngine e gdec hash wp thash).whirTail = InstalledWhirTail.installedTail hash wp ∧
    (installedSamplerEngine e gdec hash wp thash).foldClaim = Connections.packedFold ∧
    (installedSamplerEngine e gdec hash wp thash).parseWhir = e.parseWhir ∧
    (installedSamplerEngine e gdec hash wp thash).configurationHash = e.configurationHash ∧
    (installedSamplerEngine e gdec hash wp thash).deploymentValid = e.deploymentValid ∧
    (installedSamplerEngine e gdec hash wp thash).publicInputsHash = e.publicInputsHash :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (4) The derived index points of the installed engine, unfolded: the concrete
sampler applied to the derived rounds' snapshot, the proof's own used claims and
the configured `indexBits`. -/
theorem installed_sampler_derived_indices (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p =
      concreteSampleIndices thash (Verifier.derivedRounds e c p).transcript p.used c.indexBits :=
  rfl

/-- (4) The one bridge to the adopted CHECKED execution: under the adopted
`CommitAgrees` / initial-transcript hypotheses, the checked run's index points
and WHIR context ARE this engine's derived ones. The hypotheses are exactly the
adopted ones; nothing new is assumed about `commitRound`. -/
theorem installed_sampler_matches_the_checked_execution (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (result : OuterAdapter.Execution)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hc : OuterAdapter.CommitAgrees thash e.commitRound) (hd : c.degreeBits ≤ 13)
    (h : OuterAdapter.execute thash c p = some result) :
    result.indices.points = Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p ∧
    result.context = Verifier.derivedContext (installedSamplerEngine e gdec hash wp thash) c p := by
  have hall := OuterAdapter.execute_matches_existing_derived_context thash
    (installedSamplerEngine e gdec hash wp thash) c p result hi hc
    (concrete_sampler_agrees_with_checked thash) rfl hd h
  exact ⟨hall.2.2.1, hall.2.2.2⟩

/-- (4) **THE DECODE HYPOTHESIS IS SATISFIABLE ON A REAL RUN.** Each key
statement of sections 5 and 7 carries
`OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st` as an
explicit hypothesis, because the snapshot is produced by the ABSTRACT
`commitRound`. Under exactly the hypotheses of
`installed_sampler_matches_the_checked_execution` -- the adopted initial-transcript
and `CommitAgrees` hypotheses, plus `c.degreeBits ≤ 13` -- a successful adopted
CHECKED execution DISCHARGES it: the checked run's own rounds are the derived
ones, and `OuterAdapter.sample_decode_failure` rules out a snapshot that does not
decode. So the hypothesis is not vacuous, and the only decode instance is no
longer the hand-made `toySnapshot` of section 8. -/
theorem decoded_snapshot_exists_under_checked_execution (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (result : OuterAdapter.Execution)
    (hi : e.initialTranscript c p =
      OuterInitial.toInitial (OuterInitial.derive thash c (Verifier.statement p)))
    (hc : OuterAdapter.CommitAgrees thash e.commitRound) (hd : c.degreeBits ≤ 13)
    (h : OuterAdapter.execute thash c p = some result) :
    ∃ st, OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st := by
  have hall := OuterAdapter.execute_matches_existing_derived_context thash
    (installedSamplerEngine e gdec hash wp thash) c p result hi hc
    (concrete_sampler_agrees_with_checked thash) rfl hd h
  have hr : result.rounds = Verifier.derivedRounds e c p := hall.2.1
  simp only [OuterAdapter.execute, bind, Option.bind] at h
  cases h0 : OuterInitial.checkedBaseState thash c (Verifier.statement p) with
  | none => simp [h0] at h
  | some _ =>
    cases h1 : OuterInitial.checkedDerive thash c (Verifier.statement p) with
    | none => simp [h0, h1] at h
    | some initial =>
      cases h2 : OuterAdapter.runChecked thash (Verifier.start (OuterInitial.toInitial initial))
          (p.logRounds.zip p.gateRounds) with
      | none => simp [h0, h1, h2] at h
      | some rounds =>
        cases h3 : OuterAdapter.sampleChecked thash rounds.transcript p.used c.indexBits with
        | none => simp [h0, h1, h2, h3] at h
        | some idx =>
          simp only [h0, h1, h2, h3, pure, Option.some.injEq] at h
          have hrr : rounds = Verifier.derivedRounds e c p := by rw [← hr, ← h]
          cases hdec : OuterAdapter.decode rounds.transcript with
          | none =>
            rw [OuterAdapter.sample_decode_failure thash _ _ _ hdec] at h3
            exact Option.noConfusion h3
          | some st => exact ⟨st, by rw [← hrr]; exact hdec⟩

/-- (4) The same discharge, instantiated on the ADOPTED fixture and with no
execution hypothesis left: `OuterAdapter.ordinary_prefix_for_every_hash` supplies
the successful checked execution of `fixtureConfig` / `fixtureProof` for EVERY
`thash`, so on that pair a decodable real snapshot exists unconditionally (given
only the adopted initial-transcript and `CommitAgrees` hypotheses on the abstract
engine). -/
theorem fixture_snapshot_decodes_for_every_hash (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash)
    (hi : e.initialTranscript OuterAdapter.fixtureConfig OuterAdapter.fixtureProof =
      OuterInitial.toInitial (OuterInitial.derive thash OuterAdapter.fixtureConfig
        (Verifier.statement OuterAdapter.fixtureProof)))
    (hc : OuterAdapter.CommitAgrees thash e.commitRound) :
    ∃ st, OuterAdapter.decode
      (Verifier.derivedRounds e OuterAdapter.fixtureConfig
        OuterAdapter.fixtureProof).transcript = some st := by
  obtain ⟨result, hex, -⟩ := OuterAdapter.ordinary_prefix_for_every_hash thash
  exact decoded_snapshot_exists_under_checked_execution e gdec hash wp thash _ _ result hi hc
    (by decide) hex

/-! ## 5. THE KEY THEOREMS -/

/-- The digest the two index lanes are squeezed from: the state after the eight
`claimFrames`, i.e. after the source's `DOMAIN_CONSTITUENT_INDEX_V2` separator. -/
def indexDigest (thash : Transcript.Hash) (s : Transcript.State) (u : Verifier.UsedClaims) :
    Transcript.Digest :=
  (OuterAdapter.claimsCommitted thash s u).digest

/-- Each index coordinate is the adopted three-digest reduction of
`OuterChallenge`, at consecutive counters of the SAME post-claims digest. -/
theorem ext3_at_is_reduced_digest_triple (thash : Transcript.Hash) (d : Transcript.Digest)
    (k : Nat) :
    OuterInitial.ext3At thash d k =
      (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash ⟨d, k⟩)).toVerifier := rfl

/-- (5a) **THE INDEX POINTS ARE SQUEEZED FROM A STATE THAT ABSORBED `p.used`.**
For the engine with the sampler installed, and any decoded rounds snapshot `st`:

* the state the two lanes are squeezed from is exactly
  `st` folded through the eight `claimFrames p.used` -- the claims domain
  separator, the five used-claim cells, the empty sixth cell, the index domain
  separator -- so every cell of `p.used` is absorbed BEFORE the first squeeze,
  and the squeeze counter is reset to zero by that last absorb;
* both lanes have length `c.indexBits`;
* log coordinate `i` is the reduction of the digest triple at counters
  `3i, 3i+1, 3i+2`, and gate coordinate `i` at
  `3*indexBits+3i, +1, +2`, of that one digest.

This is the ORDERING fact only. It says nothing about the distribution of those
reductions, and `thash` is an arbitrary deterministic function. -/
theorem sampled_indices_absorb_used_claims (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (st : Transcript.State)
    (hd : OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st) :
    OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (claimFrames p.used) ∧
    (claimFrames p.used).length = 8 ∧
    (OuterAdapter.claimsCommitted thash st p.used).counter = 0 ∧
    (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log.length =
      c.indexBits ∧
    (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).gate.length =
      c.indexBits ∧
    (∀ i, i < c.indexBits →
      (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log.get? i =
        some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
          ⟨indexDigest thash st p.used, 3 * i⟩)).toVerifier) ∧
    (∀ i, i < c.indexBits →
      (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).gate.get? i =
        some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
          ⟨indexDigest thash st p.used, 3 * c.indexBits + 3 * i⟩)).toVerifier) := by
  have hpoints : Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p =
      (OuterAdapter.sampleResult thash st p.used c.indexBits).points := by
    rw [installed_sampler_derived_indices,
      concrete_sampler_on_decoded_snapshot thash _ st p.used c.indexBits hd]
  refine ⟨rfl, rfl, OuterAdapter.claims_commit_counter_zero thash st p.used, ?_, ?_, ?_, ?_⟩
  · rw [hpoints]; exact (OuterAdapter.sample_result_shape thash st p.used c.indexBits).1
  · rw [hpoints]; exact (OuterAdapter.sample_result_shape thash st p.used c.indexBits).2.1
  · intro i hi
    rw [hpoints, OuterAdapter.sampled_log_index_counter thash st p.used c.indexBits i hi,
      ext3_at_is_reduced_digest_triple]
    rfl
  · intro i hi
    rw [hpoints, OuterAdapter.sampled_gate_index_counter thash st p.used c.indexBits i hi,
      ext3_at_is_reduced_digest_triple]
    rfl

/-- (5b) **NON-MALLEABILITY OF THE ABSORBED CLAIM BLOCK.** Two runs whose index
squeeze starts from the same digest had the same incoming state digest AND the
same used claims -- or a concrete pair of distinct byte strings with equal hash
is EXHIBITED. Collision resistance is a CONCLUSION, never a hypothesis; the
adopted `CommitmentOrder.absorb_messages_bind_or_collide` (itself built on the
adopted frame injectivity `CommitmentOrder.frame_injective`) does the work.

WHAT THIS IS NOT. It is stated at the DIGEST the lanes are squeezed from, not at
the index POINTS: `OuterChallenge.reduceTriple` maps `2^768` digest triples per
coordinate onto one field element, so equal points are strictly weaker than an
equal digest and cannot bind anything on their own. Same convention as
`CommitmentOrder`'s prefix-digest lemmas. -/
theorem used_claims_fixed_before_index_squeeze (thash : Transcript.Hash)
    (s t : Transcript.State) (u v : Verifier.UsedClaims)
    (h : indexDigest thash s u = indexDigest thash t v) :
    (s.digest = t.digest ∧ u = v) ∨ CommitmentOrder.TranscriptCollision thash := by
  rcases CommitmentOrder.absorb_messages_bind_or_collide thash (claimFrames u) (claimFrames v)
      s t (by rw [claim_frame_count, claim_frame_count]) h with ⟨hdig, hframes⟩ | hcol
  · exact Or.inl ⟨hdig, claim_frames_injective u v hframes⟩
  · exact Or.inr hcol

/-- (5b) CONTRAPOSITIVE: a prover who changes any used-claim cell CANNOT keep
the digest the index points are squeezed from, unless the hash chain collides. -/
theorem changing_used_claims_changes_the_index_digest_or_collides (thash : Transcript.Hash)
    (s t : Transcript.State) (u v : Verifier.UsedClaims) (hne : u ≠ v)
    (h : indexDigest thash s u = indexDigest thash t v) :
    CommitmentOrder.TranscriptCollision thash := by
  rcases used_claims_fixed_before_index_squeeze thash s t u v h with ⟨_, heq⟩ | hcol
  · exact absurd heq hne
  · exact hcol

/-- (5b) The same statement at the engine level: two runs of the installed
engine whose rounds snapshots decode and whose index-sampling digests agree used
the same claim cells, or the outer hash collides. -/
theorem installed_sampler_index_digest_binds_the_used_claims (e e' : Verifier.Engine)
    (thash : Transcript.Hash) (c c' : Verifier.Config) (p p' : Verifier.Proof)
    (st st' : Transcript.State)
    (_hd : OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st)
    (_hd' : OuterAdapter.decode (Verifier.derivedRounds e' c' p').transcript = some st')
    (h : indexDigest thash st p.used = indexDigest thash st' p'.used) :
    (st.digest = st'.digest ∧ p.used = p'.used) ∨ CommitmentOrder.TranscriptCollision thash :=
  used_claims_fixed_before_index_squeeze thash st st' p.used p'.used h

/-- (5c) **THE LANE LENGTHS THE VERIFIER ALREADY DEMANDS ARE NOW THEOREMS.**
`Verifier.verify` rejects with `.configuration` unless both index lanes have
length `c.indexBits` (Verifier.lean 419-421), and `Verifier.verify_success_checks`
therefore RETURNS those two equalities. With the sampler installed they hold by
construction on every decoded snapshot, so the guard is consistent rather than
an extra assumption: the second conjunct is the adopted extraction, the first is
the new unconditional fact. -/
theorem index_lanes_have_index_bits_length (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (wp : VkParams) (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (st : Transcript.State)
    (hd : OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st) :
    ((Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log.length =
        c.indexBits ∧
      (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).gate.length =
        c.indexBits) ∧
    (∀ (pin : Verifier.Pinned) (chain : Nat),
      Verifier.verify (installedSamplerEngine e gdec hash wp thash) pin chain c p = .ok () →
        (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log.length =
          c.indexBits ∧
        (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).gate.length =
          c.indexBits) := by
  have hall := sampled_indices_absorb_used_claims e gdec hash wp thash c p st hd
  refine ⟨⟨hall.2.2.2.1, hall.2.2.2.2.1⟩, ?_⟩
  intro pin chain hv
  have hs := Verifier.verify_success_checks (installedSamplerEngine e gdec hash wp thash)
    pin chain c p hv
  exact ⟨hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1⟩

/-- (5c) The verifier's index-length guard is SATISFIED by the installed
sampler on every decoded snapshot. -/
theorem installed_sampler_meets_the_verify_index_length_guard (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) (st : Transcript.State)
    (hd : OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st) :
    ¬((Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log.length ≠
        c.indexBits ∨
      (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).gate.length ≠
        c.indexBits) := by
  have h := (index_lanes_have_index_bits_length e gdec hash wp thash c p st hd).1
  rintro (hn | hn)
  · exact hn h.1
  · exact hn h.2

/-- (5c) Conversely, a malformed 40-byte rounds snapshot makes the installed
sampler return empty lanes, which the verifier's own guard REJECTS whenever
`indexBits` is positive. No fallback point is invented. -/
theorem malformed_snapshot_fails_the_index_length_guard (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (hd : OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = none)
    (hb : c.indexBits ≠ 0) :
    (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log.length ≠
      c.indexBits ∧
    (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).gate.length ≠
      c.indexBits := by
  have hpoints : Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p =
      ⟨[], []⟩ := by
    rw [installed_sampler_derived_indices,
      concrete_sampler_rejects_malformed_snapshot thash _ p.used c.indexBits hd]
  rw [hpoints]
  exact ⟨fun h => hb h.symm, fun h => hb h.symm⟩

/-- (5c) The two index-length conjuncts of the adopted
`TranscriptProvenance.ObservationOnlyDerived` are no longer assumptions for this
engine: the structure is built from its other seven fields plus the
decoded-snapshot hypothesis `hd` -- which is itself dischargeable under the
adopted `OuterAdapter.CommitAgrees` route, see
`decoded_snapshot_exists_under_checked_execution`. The two index fields are the
ones that stop being inputs; `hd` replaces them. -/
theorem installed_sampler_observation_needs_no_index_hypotheses (e : Verifier.Engine)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (st : Transcript.State)
    (hd : OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st)
    (hchain : chain = pin.chainId)
    (hcfg : (installedSamplerEngine e gdec hash wp thash).configurationHash c = pin.configDigest)
    (henv : Verifier.envelope c = true)
    (hdep : (installedSamplerEngine e gdec hash wp thash).deploymentValid c = true)
    (hshape : Verifier.shape pin c p = true)
    (hwhir : Verifier.verifyWhir
      (Integrated.modelEngine (installedSamplerEngine e gdec hash wp thash) gdec)
      (Verifier.derivedContext
        (Integrated.modelEngine (installedSamplerEngine e gdec hash wp thash) gdec) c p) p = true)
    (hnorm : Norm.shapeValid c
      (Norm.challengesFromInitial
        ((installedSamplerEngine e gdec hash wp thash).initialTranscript c p))
      (Verifier.normTerminalInput p)
      (Verifier.derivedRounds (installedSamplerEngine e gdec hash wp thash) c p).logPoint = true) :
    TranscriptProvenance.ObservationOnlyDerived (installedSamplerEngine e gdec hash wp thash)
      gdec pin chain c p :=
  { chain := hchain, configurationHash := hcfg, envelope := henv, deployment := hdep,
    shape := hshape,
    logIndex := (index_lanes_have_index_bits_length e gdec hash wp thash c p st hd).1.1,
    gateIndex := (index_lanes_have_index_bits_length e gdec hash wp thash c p st hd).1.2,
    whir := hwhir, normShape := hnorm }

/-! ## 6. (5d) The finite index-draw space, in the `JointChallengeSpace` style

`JointChallengeSpace.Draw` indexes the post-prefix GATE-lane schedule and stops
before the constituent-index block, so the index points are not coordinates of
it. Extending that space would drag in its whole union-bound apparatus for no
gain here, so this section builds the small separate space instead: `2 * bits`
digest-triple coordinates, positioned strictly AFTER the outer schedule's
blocks. The seam theorem below is a COORDINATE statement, proved for every hash;
it is NOT the distributional half. -/

inductive IndexDraw (bits : Nat) where
  /-- Log-lane index coordinate `i`, squeezed at counters `3i, 3i+1, 3i+2`. -/
  | log : Fin bits → IndexDraw bits
  /-- Gate-lane index coordinate `i`, at `3*bits+3i, +1, +2`. -/
  | gate : Fin bits → IndexDraw bits
  deriving DecidableEq

def indexDrawEquiv (bits : Nat) : IndexDraw bits ≃ Fin bits ⊕ Fin bits where
  toFun k := match k with
    | IndexDraw.log i => Sum.inl i
    | IndexDraw.gate i => Sum.inr i
  invFun j := match j with
    | Sum.inl i => IndexDraw.log i
    | Sum.inr i => IndexDraw.gate i
  left_inv k := by cases k <;> rfl
  right_inv j := by rcases j with i | i <;> rfl

instance instFintypeIndexDraw (bits : Nat) : Fintype (IndexDraw bits) :=
  Fintype.ofEquiv _ (indexDrawEquiv bits).symm

/-- (5d) Two lanes of `bits` coordinates each. -/
theorem index_draw_card (bits : Nat) : Fintype.card (IndexDraw bits) = 2 * bits := by
  rw [Fintype.card_congr (indexDrawEquiv bits)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- The little-endian squeeze counter of the draw inside the post-claims block,
exactly as `OuterAdapter.sampled_log_index_counter` /
`OuterAdapter.sampled_gate_index_counter` pin them. -/
def indexCounter (bits : Nat) : IndexDraw bits → Nat
  | IndexDraw.log i => 3 * i.val
  | IndexDraw.gate i => 3 * bits + 3 * i.val

/-- The draw's place in the source squeeze schedule: block `degreeBits + 1` --
after the prefix block `0` and the `degreeBits` coupled-round blocks
`1 .. degreeBits` of `JointChallengeSpace.sourceBlock` -- at the counter above.

THE BLOCK NUMBER IS DOCUMENTED, NOT DERIVED, exactly in the sense in which
`JointChallengeSpace.Draw`'s `outerLog` / `outerGate` counters are documented
(JointChallengeSpace.lean 178-181): `degreeBits + 1` is a LABEL this module
ASSIGNS, read off the source order of §2 -- the constituent-claims block is
absorbed after the last coupled round -- and `index_positions_follow_the_outer_schedule`
below is true BY that assignment, not by any computation over the engine.
Nothing forces an abstract `Verifier.Engine` to number its blocks this way.

What IS derived, and does not depend on the label, is the counter side: the two
lanes are squeezed from `indexDigest thash st p.used`, i.e. from
`OuterAdapter.claimsCommitted thash st p.used` with `st` the POST-ROUNDS
snapshot, at the counters `indexCounter` records --
`sampled_indices_absorb_used_claims` and `index_points_are_space_coordinates`. -/
def indexSchedulePosition (degreeBits bits : Nat) (k : IndexDraw bits) : Nat × Nat :=
  (degreeBits + 1, indexCounter bits k)

theorem index_log_position (degreeBits bits : Nat) (i : Fin bits) :
    indexSchedulePosition degreeBits bits (IndexDraw.log i) = (degreeBits + 1, 3 * i.val) := rfl

theorem index_gate_position (degreeBits bits : Nat) (i : Fin bits) :
    indexSchedulePosition degreeBits bits (IndexDraw.gate i) =
      (degreeBits + 1, 3 * bits + 3 * i.val) := rfl

/-- (5d) No two index draws share a schedule position. -/
theorem index_schedule_position_injective (degreeBits bits : Nat) :
    Function.Injective (indexSchedulePosition degreeBits bits) := by
  intro a b h
  have hc := congrArg Prod.snd h
  simp only [indexSchedulePosition] at hc
  cases a with
  | log i =>
      cases b with
      | log j =>
          exact congrArg IndexDraw.log (Fin.ext (by simp only [indexCounter] at hc; omega))
      | gate j =>
          exfalso
          simp only [indexCounter] at hc
          omega
  | gate i =>
      cases b with
      | log j =>
          exfalso
          simp only [indexCounter] at hc
          omega
      | gate j =>
          exact congrArg IndexDraw.gate (Fin.ext (by simp only [indexCounter] at hc; omega))

/-- (5d) **THE INDEX BLOCK COMES AFTER THE WHOLE OUTER SCHEDULE.** Every
`JointChallengeSpace.Draw` sits in a strictly earlier block than every index
draw, so the two coordinate families do not overlap. DOCUMENTED, NOT DERIVED:
this holds by the block LABEL `degreeBits + 1` that `indexSchedulePosition`
assigns, against `JointChallengeSpace.sourceBlock`'s own documented labels; it is
arithmetic over two label functions, not a fact recovered from an engine run. -/
theorem index_positions_follow_the_outer_schedule (d bits : Nat) (k : IndexDraw bits)
    (j : JointChallengeSpace.Draw d) :
    (JointChallengeSpace.schedulePosition d j).1 < (indexSchedulePosition d bits k).1 := by
  cases j with
  | gateAlpha =>
      simp only [JointChallengeSpace.schedulePosition, JointChallengeSpace.sourceBlock,
        indexSchedulePosition]
      omega
  | gateTau i =>
      simp only [JointChallengeSpace.schedulePosition, JointChallengeSpace.sourceBlock,
        indexSchedulePosition]
      omega
  | outerLog r =>
      have hr := r.isLt
      simp only [JointChallengeSpace.schedulePosition, JointChallengeSpace.sourceBlock,
        indexSchedulePosition]
      omega
  | outerGate r =>
      have hr := r.isLt
      simp only [JointChallengeSpace.schedulePosition, JointChallengeSpace.sourceBlock,
        indexSchedulePosition]
      omega

/-- THE INDEX SAMPLE SPACE: one `OuterChallenge.DigestTriple` per scheduled
index draw. -/
abbrev IndexSpace (bits : Nat) := IndexDraw bits → OuterChallenge.DigestTriple

/-- (5d) CARDINALITY: `(2^768)^(2 * indexBits)`. -/
theorem index_space_card (bits : Nat) :
    Fintype.card (IndexSpace bits) = (OuterChallenge.wordSize ^ 3) ^ (2 * bits) := by
  rw [Fintype.card_fun, index_draw_card, OuterChallenge.digest_tuple_cardinality]

/-- The point of `IndexSpace` the run actually produces: the three actual
32-byte hash outputs at each scheduled counter of the post-claims digest. -/
def actualIndexDraw (thash : Transcript.Hash) (d : Transcript.Digest) (bits : Nat) :
    IndexSpace bits :=
  fun k => OuterChallenge.actualDigests thash ⟨d, indexCounter bits k⟩

/-- (5d) **THE SEAM, AS A COORDINATE STATEMENT.** The index points the installed
sampler produces ARE the coordinatewise `OuterChallenge.reduceTriple` reductions
of the single point `actualIndexDraw thash (indexDigest thash st p.used) bits` of
`IndexSpace bits`. Proved for EVERY deterministic hash; no law is attached and
none is claimed. -/
theorem index_points_are_space_coordinates (thash : Transcript.Hash) (s : Transcript.State)
    (u : Verifier.UsedClaims) (bits i : Nat) (hi : i < bits) :
    (OuterAdapter.sampleResult thash s u bits).points.log.get? i =
      some (OuterChallenge.reduceTriple
        (actualIndexDraw thash (indexDigest thash s u) bits (IndexDraw.log ⟨i, hi⟩))).toVerifier ∧
    (OuterAdapter.sampleResult thash s u bits).points.gate.get? i =
      some (OuterChallenge.reduceTriple
        (actualIndexDraw thash (indexDigest thash s u) bits (IndexDraw.gate ⟨i, hi⟩))).toVerifier := by
  constructor
  · rw [OuterAdapter.sampled_log_index_counter thash s u bits i hi,
      ext3_at_is_reduced_digest_triple]
    rfl
  · rw [OuterAdapter.sampled_gate_index_counter thash s u bits i hi,
      ext3_at_is_reduced_digest_triple]
    rfl

/-- The IDEAL uniform mass of one point of `IndexSpace`. It is a DEFINITION.
**No theorem anywhere says that the actual draw
`actualIndexDraw thash (indexDigest thash st p.used) bits` is distributed by it**
for any deterministic `thash`; that is the unformalized half (B) of the
Fiat--Shamir reading, exactly as in `JointChallengeSpace`'s header. -/
def uniformIndexMass (bits : Nat) : ℚ := 1 / (Fintype.card (IndexSpace bits) : ℚ)

theorem uniform_index_mass_positive (bits : Nat) : 0 < uniformIndexMass bits := by
  have h : 0 < (OuterChallenge.wordSize ^ 3) ^ (2 * bits) :=
    pow_pos (pow_pos OuterChallenge.word_size_positive 3) _
  unfold uniformIndexMass
  rw [index_space_card]
  exact div_pos one_pos (by exact_mod_cast h)

/-! ## 7. (Deliverable 4) What this buys for residue R3 -/

/-- **THE R3 ORDERING FACT, NOW A THEOREM ABOUT THE INSTALLED SAMPLER.**

`InstalledWhirTail`'s header records, as an OBSERVATION, that in the deployed
protocol "the index point is sampled after the cells are in the outer
transcript", and therefore that the per-column identification assumed by
`TailExtractsCommittedTables` (residue R3, riding on R1b) is not arbitrary. With
`sampleIndices` installed the ORDERING half of that sentence becomes provable.
This theorem is not a proof of R3; it is a PACKAGING CONJUNCTION that collects
the ordering and non-malleability facts of sections 5 and 6 next to R1b's
extraction, in one statement, so that what R3 would still need is visible in one
place. Under R1b and acceptance of the installed-sampler engine on the deployed
route (`wp.rounds ≠ []`), with the rounds snapshot decoding to `st` (a hypothesis
dischargeable under `decoded_snapshot_exists_under_checked_execution`):

1. there is a per-cell column family `cols` with
   `OpeningBinding.OpensCommittedTable` at the DERIVED index points -- this is
   R1b's own content, transported to this engine;
2. every bound cell is opened at a point whose index half is one of those two
   derived lanes. DEFINITIONAL: `OpenedClaimFold.boundCell` pairs cells `0,1,2`
   with the log lane and `3,4` with the gate lane by its own definition, so each
   of the five disjuncts is `rfl`. It records the lane assignment; it proves
   nothing about the sampler;
3. those lanes are squeezed from the state that absorbed ALL of `p.used`
   through the eight `claimFrames` -- the ordering fact, from
   `sampled_indices_absorb_used_claims`;
4. each log coordinate is the reduction of the actual digest triple at counters
   `3i, 3i+1, 3i+2` of that one digest;
5. any other incoming state and used-claims vector reaching the SAME sampling
   digest agrees with this run's, or the outer hash collides.

**WHAT IS STILL NOT PROVED.** The PROBABILISTIC step -- that a FORGED cell
family cannot survive a freshly sampled index point, i.e. that agreement of the
folds at a random index point forces agreement of the cells -- is NOT proved,
here or in the adopted tree. Conjuncts 3-5 are ordering and non-malleability
only; there is no distribution on `thash`, no random oracle, and no bound. R1b
itself remains an assumption (`hyp`), and so does everything it subsumes. -/
theorem per_column_identification_hook (hash : Spongefish.Hash) (wp : VkParams)
    (thash : Transcript.Hash) (hyp : InstalledWhirTail.TailExtractsCommittedTables hash wp)
    (hrounds : wp.rounds ≠ []) (e : Verifier.Engine) (gdec : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (st : Transcript.State)
    (hv : Integrated.verify (installedSamplerEngine e gdec hash wp thash) gdec pin chain c p =
      .ok ())
    (hd : OuterAdapter.decode (Verifier.derivedRounds e c p).transcript = some st) :
    ∃ cols : Fin 5 → List (List Element),
      OpeningBinding.OpensCommittedTable c p (Verifier.derivedRounds e c p)
        (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p) cols ∧
      (∀ i : Fin 5,
        (OpenedClaimFold.boundCell p.used
            (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p) i).2 =
          (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log ∨
        (OpenedClaimFold.boundCell p.used
            (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p) i).2 =
          (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).gate) ∧
      OuterAdapter.claimsCommitted thash st p.used =
        OuterInitial.absorbMessages thash st (claimFrames p.used) ∧
      (∀ i, i < c.indexBits →
        (Verifier.derivedIndices (installedSamplerEngine e gdec hash wp thash) c p).log.get? i =
          some (OuterChallenge.reduceTriple (OuterChallenge.actualDigests thash
            ⟨indexDigest thash st p.used, 3 * i⟩)).toVerifier) ∧
      (∀ (st' : Transcript.State) (v : Verifier.UsedClaims),
        indexDigest thash st' v = indexDigest thash st p.used →
          (st'.digest = st.digest ∧ v = p.used) ∨ CommitmentOrder.TranscriptCollision thash) := by
  obtain ⟨extract, hex⟩ := hyp
  have hv' : Integrated.verify (InstalledWhirTail.installedEngine (resampled e thash) gdec hash wp)
      gdec pin chain c p = .ok () := hv
  obtain ⟨r, hrun, _, _, _, _, _⟩ :=
    InstalledWhirTail.installed_acceptance_runs_the_concrete_tail (resampled e thash) gdec hash wp
      pin chain c p hv'
  obtain ⟨opening, hopen⟩ :=
    InstalledWhirTail.tail_success_has_round_one_opening hash wp _ _ _ hrounds r hrun
  have hall := sampled_indices_absorb_used_claims e gdec hash wp thash c p st hd
  refine ⟨extract (r.retained.origin.initial.commitments.map (fun x => x.root)) opening,
    ?_, ?_, hall.1, ?_, ?_⟩
  · exact hex (resampled e thash) gdec pin chain c p r opening hv' hrun hopen
  · intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  · exact hall.2.2.2.2.2.1
  · intro st' v h
    exact used_claims_fixed_before_index_squeeze thash st' st v p.used h

/-! ## 8. Examples on small data

A CONSTANT toy hash, not Keccak, and the adopted `OuterAdapter.fixtureProof`
claim cells. Nothing below is a fixture of the deployed profile and nothing
computes over the digest space; the two evaluations are `decide` on 40 snapshot
bytes and one index coordinate per lane. -/

def toyHash : Transcript.Hash := fun _ => OuterChallenge.ordinaryDigest

def toySnapshot : Verifier.Bytes := OuterInitial.snapshot ⟨OuterChallenge.ordinaryDigest, 0⟩

theorem toy_snapshot_decodes :
    OuterAdapter.decode toySnapshot = some ⟨OuterChallenge.ordinaryDigest, 0⟩ :=
  OuterAdapter.decode_snapshot _ (by decide)

/-- (8) The installed sampler produces ONE coordinate per lane at
`indexBits = 1`, on the adopted fixture's used claims. -/
theorem example_concrete_sampler_shape :
    (concreteSampleIndices toyHash toySnapshot OuterAdapter.fixtureProof.used 1).log.length = 1 ∧
    (concreteSampleIndices toyHash toySnapshot OuterAdapter.fixtureProof.used 1).gate.length = 1 := by
  rw [concrete_sampler_on_decoded_snapshot toyHash toySnapshot _ OuterAdapter.fixtureProof.used 1
    toy_snapshot_decodes]
  exact ⟨(OuterAdapter.sample_result_shape toyHash _ OuterAdapter.fixtureProof.used 1).1,
    (OuterAdapter.sample_result_shape toyHash _ OuterAdapter.fixtureProof.used 1).2.1⟩

/-- (8) Both coordinates evaluate, on this constant hash, to the reduction of
the constant digest: `fromLe (le 32 5) % p = 5` in each of the three limbs. -/
theorem example_concrete_sampler_values :
    ((concreteSampleIndices toyHash toySnapshot OuterAdapter.fixtureProof.used 1).log.get? 0).map
        (fun x => (x.val.c0, x.val.c1, x.val.c2)) = some (5, 5, 5) ∧
    ((concreteSampleIndices toyHash toySnapshot OuterAdapter.fixtureProof.used 1).gate.get? 0).map
        (fun x => (x.val.c0, x.val.c1, x.val.c2)) = some (5, 5, 5) := by
  constructor <;> decide

/-- (8) **THE ABSTRACT OBSERVATION IS NOT THIS FUNCTION.**
`Verifier.testEngine.sampleIndices` returns the EMPTY point pair for every
input, and `Integrated.exampleEngine.sampleIndices` returns the constant
`[zero]` pair; neither reads its `UsedClaims` argument at all. The installed
sampler differs from both -- in SHAPE from the first, in VALUE from the
second. -/
theorem example_concrete_sampler_is_not_the_abstract_observation :
    Verifier.testEngine.sampleIndices toySnapshot OuterAdapter.fixtureProof.used 1 =
      (⟨[], []⟩ : Verifier.IndexPoints) ∧
    Integrated.exampleEngine.sampleIndices toySnapshot OuterAdapter.fixtureProof.used 1 =
      (⟨[Verifier.zero], [Verifier.zero]⟩ : Verifier.IndexPoints) ∧
    concreteSampleIndices toyHash toySnapshot OuterAdapter.fixtureProof.used 1 ≠
      (⟨[], []⟩ : Verifier.IndexPoints) ∧
    concreteSampleIndices toyHash toySnapshot OuterAdapter.fixtureProof.used 1 ≠
      (⟨[Verifier.zero], [Verifier.zero]⟩ : Verifier.IndexPoints) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h
    have hl := example_concrete_sampler_shape.1
    rw [h] at hl
    exact absurd hl (by decide)
  · intro h
    have hv := example_concrete_sampler_values.1
    rw [h] at hv
    exact absurd hv (by decide)

/-- (8) The claim block really is eight frames, and the sixth cell really is
empty, on the adopted fixture. -/
theorem example_fixture_claim_frames :
    (claimFrames OuterAdapter.fixtureProof.used).length = 8 ∧
    (claimFrames OuterAdapter.fixtureProof.used).get? 6 =
      some ⟨6, OuterAdapter.encodedVec []⟩ :=
  ⟨rfl, rfl⟩

end Audit.Wire3.InstalledIndexSampler
