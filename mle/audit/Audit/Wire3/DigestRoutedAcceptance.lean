import Audit.Wire3.RoutedAcceptance

/-!
# Digest-reading routed acceptance: `numRouted = 80` at a hash that reads the digest

**WHAT IS REPAIRED, STATED FIRST.**  The adopted `Audit.Wire3.RoutedAcceptance`
exhibits `Verifier.verify` accepting at `numRouted = 80` on the adopted
`DerivedAcceptance.derivedEngine`, but its `routedHash` answers on the COUNTER
SUFFIX of its input alone and never looks at the digest
(`RoutedAcceptance.routed_hash_is_a_transcript_collision`).  `Transcript.absorb`
hands the hash a FRAME, and `routedHash` sends essentially every frame to the
single constant `twoDigest` (`routed_hash_on_a_long_frame`), so the entire
Fiat--Shamir chain of that module is a constant and no challenge anywhere depends
on the statement (`RoutedAcceptance.rho_ignores_the_statement`).  Two proofs
differing only in `normInverseRoot` share their whole derived transcript there --
proved here, not asserted: `routed_initial_transcripts_do_not_separate_the_two_proofs`.

This module keeps the acceptance and repairs the hash.  `fixedHash` separates the
two domains by the single byte in which the two adopted prefixes differ --
`Transcript.framePrefix` is `plonky2-mle-v3-frame` and
`Transcript.challengePrefix` is `plonky2-mle-v3-challenge`, so byte fifteen is
`f` in one and `c` in the other (`frame_mark`, `challenge_mark`) -- and then

* on a FRAME it carries the incoming digest's THIRTY-ONE trailing bytes forward
  verbatim and adds its first byte to the byte fold of the tag, the length field
  and the WHOLE payload (`frame_mix_value`): all thirty-two digest bytes and all
  payload bytes are read;
* on a CHALLENGE INPUT whose eight-byte counter encoding is not one of those of
  three, four and five it does the same with the counter encoding in place of the
  payload (`fixed_hash_on_a_challenge_input`), and is therefore INJECTIVE IN THE
  DIGEST (`fixed_hash_is_injective_in_the_digest`);
* on a CHALLENGE INPUT at counters three, four and five -- and at their `2 ^ 64`
  aliases, see below -- it returns the adopted
  `RoutedAcceptance.minusOneDigest`, `zeroDigest`, `zeroDigest`, exactly as
  `routedHash` does -- which pins the derived `rho` at `-1`
  (`fixed_rho_is_minus_one`) and is what the acceptance argument needs.

**THE CHAIN STATE IS ONE BYTE WIDE -- READ EVERYTHING BELOW THROUGH THIS.**
`fixedHash` READS all thirty-two digest bytes but WRITES one: the thirty-one
trailing bytes of every answer are the thirty-one trailing bytes of the INCOMING
digest, carried forward verbatim (`frame_answer_freezes_the_tail`,
`challenge_answer_freezes_the_tail`).  `OuterInitial.startState` is the all-zero
digest, so at EVERY configuration and EVERY statement the derived chain digest is
a single varying byte followed by thirty-one zeros
(`derive_digest_tail_is_thirty_one_zero_bytes`): the whole derivation moves
through AT MOST 256 DISTINCT CHAIN DIGESTS.  When this header says that 180 of
228 squeezes read the digest chain, it means they read THAT ONE-BYTE STATE.  What
is restored is the STRUCTURE of the Fiat--Shamir dependence -- which challenges
are functions of which absorptions -- and NOT any quantitative collision
resistance; `fixed_hash_is_still_a_transcript_collision` disclaims the latter
explicitly.

**THE HEADLINE.**

    `Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash P)
       (RoutedAcceptance.routedPin khash) 1 RoutedAcceptance.routedConfig
       RoutedAcceptance.routedProof = .ok ()`

(`fixed_acceptance`) at `numRouted = 80`, under the single hypothesis
`PinnedWhirProfile.profileOk P RoutedAcceptance.routedConfig = true`, discharged
at the adopted stand-in profile (`fixed_acceptance_at_the_profile_witness`) and at
the adopted SHARP profile (`fixed_acceptance_at_the_sharp_profile`); again through
the adopted `Integrated.verify` (`fixed_integrated_acceptance`), whose checked
norm adapter enforces the FULL `Norm.shapeValid` predicate including
`c.kIs.length = c.numRouted` at eighty (`fixed_norm_shape_valid`); and again at
the adopted second configuration carrying `numPublicInputs = 3`
(`fixed_public_acceptance`, `fixed_public_integrated_acceptance`).  The ENGINE is
LITERALLY the adopted `DerivedAcceptance.derivedEngine`, the CONFIGURATION and
the PROOF are LITERALLY the adopted `RoutedAcceptance.routedConfig` and
`RoutedAcceptance.routedProof`, and `khash` and `P` remain UNIVERSALLY QUANTIFIED.

**THE DIGEST SENSITIVITY, AS THEOREMS.**

* `fixed_hash_is_injective_in_the_digest`: at every counter whose eight-byte
  little-endian encoding differs from those of three, four and five, two challenge
  inputs with the same counter tag and different digests get different answers.  `fixed_hash_separates_two_digests_at_one_counter` applies it
  to the exact pair that `RoutedAcceptance.routed_hash_is_a_transcript_collision`
  exhibits, so the mechanism behind that proof is closed.
* `fixed_initial_transcript_separates_the_two_proofs`: the derived initial
  transcript -- the forty snapshot bytes of `Verifier.Initial` -- DIFFERS between
  `RoutedAcceptance.routedProof` and `RoutedAcceptance.altProof`, which differ
  only in `normInverseRoot`.  **THE SEPARATION IS FOLD-SPECIFIC, NOT GENERIC, AND
  ITS COUNTERWEIGHT IS PROVED IMMEDIATELY NEXT TO IT (Section 5c).**  It holds
  because that pair's two roots have DIFFERENT one-byte frame folds
  (`alt_root_folds_differ`: thirty-four against thirty-five).  For a pair whose
  folds AGREE -- `normInverseRoot = 1` against `normInverseRoot = 256` -- the two
  proofs share their ENTIRE derived initial transcript at `fixedHash`
  (`fixed_hash_does_not_separate_the_other_root_pair`), exactly as every pair does
  at `RoutedAcceptance.routedHash`.  Which pairs separate is a property of the
  one-byte fold, not of statement distinctness.  The chain is split at the
  norm-root absorption
  (`norm_root_digests_split`) and the split survives every later absorption
  (`frames_preserve_a_split`), so it reaches the relation state
  (`relation_digests_split`) from which the taus, `lambda`, `kappa`, `alpha` and
  the gate taus are all drawn, and reaches the round and index stages through it.
  `fixed_lambda_inputs_differ` records that the two runs' `lambda` draws are
  answered on different digests.  The contrast with the adopted module is one pair
  of theorems: `routed_initial_transcripts_do_not_separate_the_two_proofs` versus
  `fixed_initial_transcript_separates_the_two_proofs`.

**WHAT REMAINS COUNTER-KEYED -- A DISCLOSED RESIDUE, NOT A HIDDEN ONE.**  At
counters three, four and five the answer is a constant
(`fixed_hash_is_digest_blind_at_the_three_tuned_counters`), and at every counter
whose eight-byte little-endian encoding differs from those of three, four and five
the hash is injective in the digest (`fixed_hash_is_injective_in_the_digest`).
That phrasing is exact and the stronger one would be false: `counterTag` is
`Transcript.le 8`, which encodes `k mod 2 ^ 64`, so counters congruent to three,
four or five modulo `2 ^ 64` enter the tuned branch too
(`counter_tag_aliases_at_two_to_the_sixty_four`,
`fixed_hash_is_blind_at_a_fourth_counter`).  No chain of this model reaches such a
counter: `Transcript.squeeze` refuses to advance past `Transcript.u64Limit`
(`the_aliased_counter_is_out_of_squeeze_range`).  Consequently the derived
`rho` (`fixed_rho_is_minus_one`) and the derived `gamma`
(`fixed_gamma_is_minus_one`), each of which begins at counter three of its own
state, are still statement-independent, and so are the squeezes at counters three,
four and five of each round-commit state and of the index-sampling state.
Bookkeeping of the adopted schedule at this configuration -- `OuterInitial.derive`
with `degreeBits = 13`, `Transcript.coupledRound`'s six squeezes per round for
thirteen rounds, and `OuterAdapter.sampleResult`'s two `drawMany` calls at
`indexBits = 8` -- gives `102 + 78 + 48 = 228` squeezes in all, of which
`6 + 39 + 3 = 48` are digest-blind and `180` read the chain -- and, by the
paragraph above, what those `180` read is the ONE-BYTE chain state.  Of that
ledger the first summand is now a THEOREM (`derive_squeeze_counts`: the four
derivation states are squeezed `3 + 6 + 3 + 90 = 102` times) and so is the
per-round count behind the second (`a_round_squeezes_six_from_counter_zero`: each
round's commit resets the counter, so its six squeezes sit at counters zero to
five and three of them are tuned, giving `3 * 13 = 39`).  The index-sampling
summand `48`, its blind part `3`, and the three totals remain arithmetic on the
cited definitions and are NOT proved as theorems here.  **The
last degenerate pin is NOT claimed removed.**  `rho` is digest-blind BY
CONSTRUCTION, because that is exactly what makes the wire pair cancel
(`RoutedAcceptance.minus_one_pair_vanishes`).  Programming the concrete digests of
this run so that even the counter-three draw would read the chain was NOT
attempted here; I did not find such a construction and no adopted lemma gives one.
It is NOT claimed impossible.

**THE SEPARATION QUESTION -- AN HONEST NEGATIVE.**  The alt proof is STILL
ACCEPTED (`alt_proof_is_still_accepted`) even though its derived transcript now
genuinely differs.  The reason is located exactly, and it is not the hash:

* gate 7 evaluates `Norm.normEvaluation`, which reads the norm-inverse COLUMN of
  `Verifier.normTerminalInput` -- all zero in both proofs -- and the challenges
  only through `rho`, which is `-1` in both;
* gate 8's `Verifier.rootsAndClaimsMatch` DOES compare `parsed.actualRoots`
  against the context's three roots, `normInverseRoot` among them, but the
  engine's `parseWhir` is still the adopted fixture's, which ECHOES those very
  roots (`fixture_parse_echoes_the_context_roots`), so the comparison is an
  identity;
* `Verifier.shape` binds only `preprocessedRoot` to the pin
  (`alt_proof_differs_only_in_the_unbound_root`).

So a separating instance must come from route (a) -- a non-zero norm-inverse
column whose packed fold still vanishes at the derived index point -- or from an
INSTALLED WHIR parse.  That is what this negative pins down; it is not a claim
that no separating instance exists.

**WHAT THIS MODULE DOES NOT ESTABLISH.**

* `fixedHash` is NOT collision-resistant, NOT Keccak, NOT a permutation and NOT a
  claim about the deployed hash.  It is an arbitrary element of the model type
  `Transcript.Hash = Bytes -> Digest`, and it IS a `CommitmentOrder.TranscriptCollision`
  (`fixed_hash_is_still_a_transcript_collision`): it folds a payload to ONE byte,
  so any two payloads with the same fold collide, and the counter-four and
  counter-five answers coincide.  Its chain state is ONE BYTE WIDE, as above.
  What is claimed, and proved, is only that it READS the digest and that the two
  EXHIBITED proofs' transcripts are separated DIRECTLY; separation is NOT claimed
  for statement pairs in general, and the counterweight pair is proved not to
  separate (`fixed_hash_does_not_separate_the_other_root_pair`).
* **Against the adopted `RoutedAcceptance` this module is strictly better on the
  hash and equal everywhere else** -- same engine, same configuration, same proof,
  same `numRouted = 80`, same universal `khash` and `P`, the public-input
  configuration of that module's Section 13 carried over too.  Its algebra is
  reused verbatim, never re-derived.
* **Against the adopted `DerivedAcceptance` it remains INCOMPARABLE, and the
  quantifier is still the price, stated at headline weight: `thash` is
  INSTANTIATED here and UNIVERSAL there.**  What is bought back is that the
  instantiated hash is no longer a collapsing one.
* **Against `NonDegenerateAcceptance.maximalConfig` the adopted ledger carries
  over unchanged**, because the configuration is literally that module's: six
  numeric fields tie including `numRouted`
  (`config_ties_the_adopted_maximal_on_six_fields`) and four sit strictly below
  (`config_is_below_the_adopted_maximal_on_four_fields`); at the public-input
  configuration seven tie and three sit below.  `maximalConfig`'s acceptance is at
  the FIXTURE engine, so the two remain incomparable and no conclusion may be
  drawn by combining any two of the three instances.
* The WHIR parse and the WHIR tail are still the adopted fixture's; every caveat
  in `DerivedAcceptance`'s header about them applies here verbatim.
* Gate 2 is still non-binding: `RoutedAcceptance.routedPin` is DEFINED from
  `khash`.
* Whether the digest-reading challenges take DIFFERENT FIELD VALUES for the two
  proofs is NOT proved: `Transcript.challengeAt` reduces a 256-bit digest modulo
  the Goldilocks modulus, and no adopted lemma rules out a coincidence there.
  What is proved is that the hash ANSWERS differ (`fixed_lambda_inputs_differ`).
* Nothing is claimed about the adopted `AdaptiveAssemblyFailure` event, and no
  vacuity record of `IndexHalfTransport` is lifted.

**PROOF HYGIENE.**  Acceptance is assembled gate by gate through the adopted
`NonDegenerateAcceptance.verify_of_checks`, never by one kernel reduction.  No
`set_option` of any kind is used.  The only import is
`Audit.Wire3.RoutedAcceptance`.
-/
namespace Audit.Wire3.DigestRoutedAcceptance

open Verifier

/-! ## 1. Byte and list helpers -/

def zeroByte : Transcript.Byte := ⟨0, by decide⟩

/-- Addition of bytes modulo `256`: the only combining operation the hash uses. -/
def mixByte (x y : Transcript.Byte) : Transcript.Byte :=
  ⟨(x.val + y.val) % 256, Nat.mod_lt _ (by decide)⟩

theorem mix_byte_left_cancel (x y s : Transcript.Byte) (h : mixByte x s = mixByte y s) :
    x = y := by
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  have h2 : (x.val + s.val) % 256 = (y.val + s.val) % 256 := congrArg Fin.val h
  omega

theorem mix_byte_right_cancel (s x y : Transcript.Byte) (h : mixByte s x = mixByte s y) :
    x = y := by
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  have h2 : (s.val + x.val) % 256 = (s.val + y.val) % 256 := congrArg Fin.val h
  omega

/-- The byte fold of a block: the hash reads EVERY byte of the block through
this. -/
def foldBytes (b : Transcript.Bytes) : Transcript.Byte := b.foldl mixByte zeroByte

/-- Truncate-or-pad to exactly `n` bytes. -/
def clip (n : Nat) (b : Transcript.Bytes) : Transcript.Bytes :=
  b.take n ++ List.replicate (n - b.length) zeroByte

theorem clip_length (n : Nat) (b : Transcript.Bytes) : (clip n b).length = n := by
  simp only [clip, List.length_append, List.length_take, List.length_replicate]
  omega

theorem clip_append (n : Nat) (b c : Transcript.Bytes) (h : b.length = n) :
    clip n (b ++ c) = b := by
  have htake : (b ++ c).take n = b := by
    rw [← h]
    exact List.take_left b c
  have hlen : n - (b ++ c).length = 0 := by
    rw [List.length_append, h]
    omega
  rw [clip, htake, hlen]
  exact List.append_nil b

theorem drop_append_of_length {α : Type} (xs ys : List α) (n : Nat) (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by
  rw [← h]
  exact List.drop_left xs ys

theorem digest_ext (d e : Transcript.Digest) (h : d.bytes = e.bytes) : d = e := by
  cases d with
  | mk bs hb =>
      cases e with
      | mk cs hc =>
          simp only [Transcript.Digest.mk.injEq]
          exact h

theorem digest_splits (d : Transcript.Digest) :
    ∃ x r, d.bytes = x :: r ∧ r.length = 31 := by
  cases hb : d.bytes with
  | nil =>
      have h := d.length_eq
      rw [hb] at h
      exact absurd h (by simp)
  | cons x r =>
      have h := d.length_eq
      rw [hb] at h
      exact ⟨x, r, rfl, by simpa using h⟩

/-- A digest is its own head byte followed by its own tail. -/
theorem digest_head_tail (d : Transcript.Digest) :
    d.bytes = d.bytes.headD zeroByte :: d.bytes.drop 1 := by
  obtain ⟨x, r, hb, _⟩ := digest_splits d
  rw [hb]
  rfl

/-- Two digests with the same head byte and the same tail are equal. -/
theorem digest_of_head_and_tail (d e : Transcript.Digest)
    (hh : d.bytes.headD zeroByte = e.bytes.headD zeroByte)
    (ht : d.bytes.drop 1 = e.bytes.drop 1) : d = e := by
  refine digest_ext d e ?_
  rw [digest_head_tail d, digest_head_tail e, hh, ht]

/-! ## 2. The repaired transcript hash

`Transcript.absorb` hands the hash a FRAME
`framePrefix ++ digest ++ [tag] ++ le 8 len ++ payload` with `framePrefix` of
length twenty, and `Transcript.challengeAt` hands it a CHALLENGE INPUT
`challengePrefix ++ digest ++ le 8 counter` with `challengePrefix` of length
twenty-four.  A single mixing rule serves both, read at the offset where that
kind of input keeps its digest.
-/

/-- The mixing rule: the thirty-one trailing bytes of the incoming digest are
carried forward verbatim, and its first byte is added to the byte fold of
EVERYTHING that follows the digest. -/
def mixFrom (off : Nat) (b : Transcript.Bytes) : Transcript.Digest :=
  ⟨mixByte ((b.drop off).headD zeroByte) (foldBytes ((b.drop off).drop 32)) ::
      clip 31 ((b.drop off).drop 1),
    by rw [List.length_cons, clip_length]⟩

/-- Byte fifteen of `Transcript.challengePrefix`: the ASCII `c` of `challenge`. -/
def challengeMark : Transcript.Byte := ⟨99, by decide⟩

/-- Byte fifteen of `Transcript.framePrefix`: the ASCII `f` of `frame`. -/
def frameMark : Transcript.Byte := ⟨102, by decide⟩

theorem challenge_mark (d : Transcript.Digest) (k : Nat) :
    (Transcript.challengeInput d k).getD 15 zeroByte = challengeMark := rfl

theorem frame_mark (d : Transcript.Digest) (t : Transcript.Byte) (p : Transcript.Bytes) :
    (Transcript.frame d t p).getD 15 zeroByte = frameMark := rfl

theorem frame_mark_is_not_the_challenge_mark : frameMark ≠ challengeMark := by decide

/-- **THE REPAIRED HASH.**  Domain-separated by the one byte in which the two
adopted prefixes differ; digest-reading on both sides; counter-keyed exactly on
the three counter ENCODINGS `counterTag 3`, `counterTag 4` and `counterTag 5`,
which is where the acceptance argument needs a fixed answer.  It writes ONE byte
of state (see Section 4b and Section 5a). -/
def fixedHash : Transcript.Hash := fun b =>
  if b.getD 15 zeroByte = challengeMark then
    (if b.reverse.take 8 = RoutedAcceptance.counterTag 3 then RoutedAcceptance.minusOneDigest
     else if b.reverse.take 8 = RoutedAcceptance.counterTag 4 then RoutedAcceptance.zeroDigest
     else if b.reverse.take 8 = RoutedAcceptance.counterTag 5 then RoutedAcceptance.zeroDigest
     else mixFrom 24 b)
  else mixFrom 20 b

/-! ## 3. The hash on challenge inputs -/

theorem fixed_hash_at_three (d : Transcript.Digest) :
    fixedHash (Transcript.challengeInput d 3) = RoutedAcceptance.minusOneDigest := by
  show (if _ then _ else _) = _
  rw [if_pos (challenge_mark d 3), RoutedAcceptance.challenge_input_tail, if_pos rfl]

theorem fixed_hash_at_four (d : Transcript.Digest) :
    fixedHash (Transcript.challengeInput d 4) = RoutedAcceptance.zeroDigest := by
  show (if _ then _ else _) = _
  rw [if_pos (challenge_mark d 4), RoutedAcceptance.challenge_input_tail, if_neg (by decide),
    if_pos rfl]

theorem fixed_hash_at_five (d : Transcript.Digest) :
    fixedHash (Transcript.challengeInput d 5) = RoutedAcceptance.zeroDigest := by
  show (if _ then _ else _) = _
  rw [if_pos (challenge_mark d 5), RoutedAcceptance.challenge_input_tail, if_neg (by decide),
    if_neg (by decide), if_pos rfl]

theorem fixed_hash_off_the_tuned_counters (d : Transcript.Digest) (k : Nat)
    (h3 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 3)
    (h4 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 4)
    (h5 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 5) :
    fixedHash (Transcript.challengeInput d k) = mixFrom 24 (Transcript.challengeInput d k) := by
  show (if _ then _ else _) = _
  rw [if_pos (challenge_mark d k), RoutedAcceptance.challenge_input_tail, if_neg h3, if_neg h4,
    if_neg h5]

/-- **THE ANSWER ON A CHALLENGE INPUT.**  Every one of the incoming digest's
thirty-two bytes is read: thirty-one are carried forward verbatim and the first
is added to the byte fold of the counter encoding. -/
theorem fixed_hash_on_a_challenge_input (d : Transcript.Digest) (k : Nat)
    (h3 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 3)
    (h4 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 4)
    (h5 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 5) :
    (fixedHash (Transcript.challengeInput d k)).bytes =
      mixByte (d.bytes.headD zeroByte) (foldBytes (Transcript.le 8 k)) :: d.bytes.drop 1 := by
  obtain ⟨x, r, hb, hr⟩ := digest_splits d
  have hdrop : (Transcript.challengeInput d k).drop 24 =
      Transcript.digestBytes d ++ Transcript.le 8 k := by
    show ((Transcript.challengePrefix ++ Transcript.digestBytes d) ++ Transcript.le 8 k).drop 24 = _
    rw [List.append_assoc]
    rfl
  have hbytes : Transcript.digestBytes d = x :: r := hb
  rw [fixed_hash_off_the_tuned_counters d k h3 h4 h5]
  show mixByte (((Transcript.challengeInput d k).drop 24).headD zeroByte)
      (foldBytes (((Transcript.challengeInput d k).drop 24).drop 32)) ::
        clip 31 (((Transcript.challengeInput d k).drop 24).drop 1) = _
  rw [hdrop, hbytes]
  have h32 : ((x :: r) ++ Transcript.le 8 k).drop 32 = Transcript.le 8 k :=
    drop_append_of_length _ _ 32 (by rw [List.length_cons, hr])
  have hhead : (((x :: r) ++ Transcript.le 8 k).headD zeroByte) = x := rfl
  have hrest : (((x :: r) ++ Transcript.le 8 k).drop 1) = r ++ Transcript.le 8 k := rfl
  rw [h32, hhead, hrest, clip_append 31 _ _ hr, hb]
  rfl

/-- **THE HASH IS INJECTIVE IN THE DIGEST AT EVERY UNTUNED COUNTER.**  The exact
negation of the mechanism behind `RoutedAcceptance.routed_hash_is_a_transcript_collision`,
whose proof exhibits two challenge inputs at counter zero carrying different
digests and observes that `routedHash` identifies them. -/
theorem fixed_hash_is_injective_in_the_digest (d e : Transcript.Digest) (k : Nat)
    (h3 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 3)
    (h4 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 4)
    (h5 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 5)
    (h : fixedHash (Transcript.challengeInput d k) =
      fixedHash (Transcript.challengeInput e k)) : d = e := by
  have hb := congrArg Transcript.Digest.bytes h
  rw [fixed_hash_on_a_challenge_input d k h3 h4 h5,
    fixed_hash_on_a_challenge_input e k h3 h4 h5] at hb
  have hh : mixByte (d.bytes.headD zeroByte) (foldBytes (Transcript.le 8 k)) =
      mixByte (e.bytes.headD zeroByte) (foldBytes (Transcript.le 8 k)) :=
    congrArg (fun l => l.headD zeroByte) hb
  have ht : d.bytes.drop 1 = e.bytes.drop 1 := congrArg (fun l => l.drop 1) hb
  exact digest_of_head_and_tail d e (mix_byte_left_cancel _ _ _ hh) ht

/-- **(2c) THE RESIDUE, EXACTLY.**  The hash is digest-blind at counters three,
four and five -- and, by `fixed_hash_is_injective_in_the_digest`, at every
counter whose eight-byte little-endian encoding differs from those of three, four
and five.  That is NOT the same as "at no other natural number": `counterTag` is
`Transcript.le 8`, which encodes `k mod 2 ^ 64`, so every counter congruent to
three, four or five modulo `2 ^ 64` enters the tuned branch as well
(`counter_tag_aliases_at_two_to_the_sixty_four`,
`fixed_hash_is_blind_at_a_fourth_counter`).  No chain of this model ever reaches
such a counter, because `Transcript.squeeze` refuses to advance past `u64Limit`
(`the_aliased_counter_is_out_of_squeeze_range`).  These three answers are what
pins `rho` and `gamma` at `-1`; they are the price of the wire-pair cancellation
and they are disclosed, not hidden. -/
theorem fixed_hash_is_digest_blind_at_the_three_tuned_counters (d e : Transcript.Digest) :
    fixedHash (Transcript.challengeInput d 3) = fixedHash (Transcript.challengeInput e 3) ∧
      fixedHash (Transcript.challengeInput d 4) = fixedHash (Transcript.challengeInput e 4) ∧
      fixedHash (Transcript.challengeInput d 5) = fixedHash (Transcript.challengeInput e 5) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fixed_hash_at_three, fixed_hash_at_three]
  · rw [fixed_hash_at_four, fixed_hash_at_four]
  · rw [fixed_hash_at_five, fixed_hash_at_five]

/-! ### 3b. The tuned branch has aliases, and they are out of range

`RoutedAcceptance.counterTag k` is `Transcript.le 8 k`, an eight-byte
little-endian encoding, so it is NOT injective on `Nat`: it identifies every pair
of counters congruent modulo `2 ^ 64`.  The gate of every theorem above is stated
on `counterTag k`, never on `k`, so every theorem is exactly as strong as it
looks; what follows is the precise scope of the residue, written down rather than
rounded off. -/

/-- `counterTag` identifies `2 ^ 64 + 3` with `3`. -/
theorem counter_tag_aliases_at_two_to_the_sixty_four :
    RoutedAcceptance.counterTag (18446744073709551616 + 3) = RoutedAcceptance.counterTag 3 := by
  decide

/-- **THE FOURTH BLIND COUNTER.**  The tuned branch fires at `2 ^ 64 + 3` for
every digest, exactly as it does at three.  So the residue is "at every counter
whose eight-byte little-endian encoding is one of those of three, four and five",
not "at exactly three natural numbers". -/
theorem fixed_hash_is_blind_at_a_fourth_counter (d : Transcript.Digest) :
    fixedHash (Transcript.challengeInput d (18446744073709551616 + 3)) =
      RoutedAcceptance.minusOneDigest := by
  show (if _ then _ else _) = _
  rw [if_pos (challenge_mark d _), RoutedAcceptance.challenge_input_tail,
    counter_tag_aliases_at_two_to_the_sixty_four, if_pos rfl]

/-- **AND NO CHAIN REACHES IT.**  `Transcript.squeeze` refuses to advance past
`Transcript.u64Limit`, so the aliased counter is unreachable in the model's own
squeeze schedule for every hash and every digest.  The alias is a scope fact
about the hash, not a hole in the derivation. -/
theorem the_aliased_counter_is_out_of_squeeze_range (hash : Transcript.Hash)
    (d : Transcript.Digest) :
    Transcript.squeeze hash ⟨d, 18446744073709551616 + 3⟩ = none := by
  show (if _ then _ else _) = _
  rw [if_neg (by change ¬ (18446744073709551616 + 3 + 1 < Transcript.u64Limit); decide)]

/-- **(2a) THE ADOPTED COLLISION PAIR IS SEPARATED.**  The two challenge inputs
`RoutedAcceptance.routed_hash_is_a_transcript_collision` exhibits -- same counter
tag, different digests -- receive different answers here. -/
theorem fixed_hash_separates_two_digests_at_one_counter :
    fixedHash (Transcript.challengeInput RoutedAcceptance.zeroDigest 0) ≠
      fixedHash (Transcript.challengeInput RoutedAcceptance.twoDigest 0) := by
  intro h
  exact RoutedAcceptance.zero_digest_ne_two_digest
    (fixed_hash_is_injective_in_the_digest _ _ 0 (by decide) (by decide) (by decide) h)

/-! ## 4. The hash on frames: the chain really moves -/

/-- The byte fold of everything a frame carries after its digest: the tag, the
length encoding and the WHOLE payload. -/
def frameTailFold (t : Transcript.Byte) (p : Transcript.Bytes) : Transcript.Byte :=
  foldBytes ([t] ++ (Transcript.le 8 p.length ++ p))

theorem fixed_hash_on_a_frame (d : Transcript.Digest) (t : Transcript.Byte)
    (p : Transcript.Bytes) :
    fixedHash (Transcript.frame d t p) = mixFrom 20 (Transcript.frame d t p) := by
  show (if _ then _ else _) = _
  rw [frame_mark d t p, if_neg frame_mark_is_not_the_challenge_mark]

/-- **THE ANSWER ON A FRAME.**  Every one of the incoming digest's thirty-two
bytes is read, and so is every byte of the absorbed payload. -/
theorem frame_mix_value (d : Transcript.Digest) (t : Transcript.Byte) (p : Transcript.Bytes) :
    (fixedHash (Transcript.frame d t p)).bytes =
      mixByte (d.bytes.headD zeroByte) (frameTailFold t p) :: d.bytes.drop 1 := by
  obtain ⟨x, r, hb, hr⟩ := digest_splits d
  have hdrop : (Transcript.frame d t p).drop 20 =
      Transcript.digestBytes d ++ ([t] ++ (Transcript.le 8 p.length ++ p)) := by
    show ((((Transcript.framePrefix ++ Transcript.digestBytes d) ++ [t]) ++
      Transcript.le 8 p.length) ++ p).drop 20 = _
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
    rfl
  have hbytes : Transcript.digestBytes d = x :: r := hb
  rw [fixed_hash_on_a_frame]
  show mixByte (((Transcript.frame d t p).drop 20).headD zeroByte)
      (foldBytes (((Transcript.frame d t p).drop 20).drop 32)) ::
        clip 31 (((Transcript.frame d t p).drop 20).drop 1) = _
  rw [hdrop, hbytes]
  have h32 : ((x :: r) ++ ([t] ++ (Transcript.le 8 p.length ++ p))).drop 32 =
      [t] ++ (Transcript.le 8 p.length ++ p) :=
    drop_append_of_length _ _ 32 (by rw [List.length_cons, hr])
  have hhead : (((x :: r) ++ ([t] ++ (Transcript.le 8 p.length ++ p))).headD zeroByte) = x := rfl
  have hrest : (((x :: r) ++ ([t] ++ (Transcript.le 8 p.length ++ p))).drop 1) =
      r ++ ([t] ++ (Transcript.le 8 p.length ++ p)) := rfl
  rw [h32, hhead, hrest, clip_append 31 _ _ hr, hb]
  rfl

/-- **THE FRAME BRANCH IS INJECTIVE IN THE DIGEST TOO.**  Used implicitly wherever
a split is propagated through an absorption; stated here in its own right, so that
the frame side is on the same footing as `fixed_hash_is_injective_in_the_digest`
on the challenge side. -/
theorem frame_hash_is_injective_in_the_digest (d e : Transcript.Digest)
    (t : Transcript.Byte) (p : Transcript.Bytes)
    (h : fixedHash (Transcript.frame d t p) = fixedHash (Transcript.frame e t p)) : d = e := by
  have hb := congrArg Transcript.Digest.bytes h
  rw [frame_mix_value, frame_mix_value] at hb
  refine digest_of_head_and_tail d e
    (mix_byte_left_cancel (d.bytes.headD zeroByte) (e.bytes.headD zeroByte)
      (frameTailFold t p) ?_) ?_
  · exact congrArg (fun l => l.headD zeroByte) hb
  · exact congrArg (fun l => l.drop 1) hb

/-! ### 4b. THE WIDTH OF THE CHAIN STATE

`mixFrom` READS thirty-two digest bytes and WRITES one: the thirty-one trailing
bytes of the answer are the thirty-one trailing bytes of the INCOMING digest,
verbatim, on both branches.  The two theorems below are that observation, and
§5a turns them into the quantitative consequence for a whole derivation. -/

/-- On a frame, the trailing thirty-one bytes of the answer are those of the
incoming digest. -/
theorem frame_answer_freezes_the_tail (d : Transcript.Digest) (t : Transcript.Byte)
    (p : Transcript.Bytes) :
    (fixedHash (Transcript.frame d t p)).bytes.drop 1 = d.bytes.drop 1 := by
  rw [frame_mix_value]
  rfl

/-- On an untuned challenge input, likewise. -/
theorem challenge_answer_freezes_the_tail (d : Transcript.Digest) (k : Nat)
    (h3 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 3)
    (h4 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 4)
    (h5 : RoutedAcceptance.counterTag k ≠ RoutedAcceptance.counterTag 5) :
    (fixedHash (Transcript.challengeInput d k)).bytes.drop 1 = d.bytes.drop 1 := by
  rw [fixed_hash_on_a_challenge_input d k h3 h4 h5]
  rfl

/-- The converse face of `frames_with_distinct_folds_split`: two absorptions with
the SAME one-byte fold are identified, whatever the payloads.  This is the
counterweight the separation result of §5 has to be read against. -/
theorem frames_with_equal_folds_collide (d : Transcript.Digest) (t : Transcript.Byte)
    (p q : Transcript.Bytes) (h : frameTailFold t p = frameTailFold t q) :
    fixedHash (Transcript.frame d t p) = fixedHash (Transcript.frame d t q) := by
  refine digest_ext _ _ ?_
  rw [frame_mix_value, frame_mix_value, h]

/-- Two digests that differ in their first byte and agree everywhere after it. -/
def SplitAt (d e : Transcript.Digest) : Prop :=
  d.bytes.headD zeroByte ≠ e.bytes.headD zeroByte ∧ d.bytes.drop 1 = e.bytes.drop 1

theorem split_at_gives_distinct_digests (d e : Transcript.Digest) (h : SplitAt d e) : d ≠ e := by
  intro hde
  exact h.1 (by rw [hde])

/-- **THE DIFFERENCE IS BORN.**  Two absorptions of different payloads into the
same digest split the chain, as soon as the absorbed blocks fold differently. -/
theorem frames_with_distinct_folds_split (d : Transcript.Digest) (t : Transcript.Byte)
    (p q : Transcript.Bytes) (h : frameTailFold t p ≠ frameTailFold t q) :
    SplitAt (fixedHash (Transcript.frame d t p)) (fixedHash (Transcript.frame d t q)) := by
  refine ⟨?_, ?_⟩
  · rw [frame_mix_value, frame_mix_value]
    intro hh
    exact h (mix_byte_right_cancel _ _ _ hh)
  · rw [frame_mix_value, frame_mix_value]
    rfl

/-- **THE DIFFERENCE SURVIVES EVERY LATER ABSORPTION.**  A split pair of digests,
absorbed under the same tag and the same payload, stays a split pair. -/
theorem frames_preserve_a_split (d e : Transcript.Digest) (t : Transcript.Byte)
    (p : Transcript.Bytes) (h : SplitAt d e) :
    SplitAt (fixedHash (Transcript.frame d t p)) (fixedHash (Transcript.frame e t p)) := by
  refine ⟨?_, ?_⟩
  · rw [frame_mix_value, frame_mix_value]
    intro hh
    exact h.1 (mix_byte_left_cancel _ _ _ hh)
  · rw [frame_mix_value, frame_mix_value]
    show d.bytes.drop 1 = e.bytes.drop 1
    exact h.2

/-! ## 5. The derived chain separates two proofs that differ only in a root -/

theorem norm_root_digest_value (hash : Transcript.Hash) (c : Verifier.Config)
    (s : Verifier.Statement) :
    (OuterInitial.normRootState hash c s).digest =
      hash (Transcript.frame
        (Transcript.domain hash (OuterInitial.preRoot hash c s).afterGamma
          "pcs-group-norm-inverse-v3").digest 2
        (OuterInitial.rootBytes s.normInverseRoot)) := rfl

theorem mix_state_digest_value (hash : Transcript.Hash) (c : Verifier.Config)
    (s : Verifier.Statement) :
    (OuterInitial.mixState hash c s).digest =
      hash (Transcript.frame (OuterInitial.normRootState hash c s).digest 1
        (Transcript.ascii "public-input-mix-challenge-v3")) := rfl

theorem relation_state_digest_value (hash : Transcript.Hash) (c : Verifier.Config)
    (s : Verifier.Statement) :
    (OuterInitial.relationState hash c s).digest =
      hash (Transcript.frame (OuterInitial.mixState hash c s).digest 1
        (Transcript.ascii "outer-relation-challenges-v3")) := rfl

/-! ### 5a. THE CHAIN STATE IS ONE BYTE WIDE

`OuterInitial.startState` carries the all-zero digest, and every absorption
preserves the thirty-one trailing bytes (`frame_answer_freezes_the_tail`), so for
EVERY configuration and EVERY statement the derived chain digest is one varying
byte followed by thirty-one zeros.  The whole derivation therefore moves through
at most `256` distinct chain digests.  This is the honest reading of "the
challenges are functions of the chain": the STRUCTURE of the Fiat--Shamir
dependence is restored, the quantity of it is not.  `fixed_hash_is_still_a_transcript_collision`
disclaims the quantitative side. -/

theorem absorb_messages_freeze_the_tail (s : Transcript.State)
    (ms : List OuterInitial.Message) :
    (OuterInitial.absorbMessages fixedHash s ms).digest.bytes.drop 1 =
      s.digest.bytes.drop 1 := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
      show (OuterInitial.absorbMessages fixedHash
        (OuterInitial.absorbMessage fixedHash s m) ms).digest.bytes.drop 1 = _
      rw [ih (OuterInitial.absorbMessage fixedHash s m)]
      exact frame_answer_freezes_the_tail s.digest m.tag m.payload

/-- **THE ONE-BYTE STATE, AS A THEOREM.**  At every configuration and every
statement the derived chain digest is a single varying byte followed by
thirty-one zero bytes. -/
theorem derive_digest_tail_is_thirty_one_zero_bytes (c : Verifier.Config)
    (s : Verifier.Statement) :
    (OuterInitial.derive fixedHash c s).state.digest.bytes.drop 1 =
      List.replicate 31 zeroByte := by
  rw [OuterInitial.derived_final_digest, relation_state_digest_value,
    frame_answer_freezes_the_tail, mix_state_digest_value, frame_answer_freezes_the_tail,
    norm_root_digest_value, frame_answer_freezes_the_tail]
  show (fixedHash (Transcript.frame (OuterInitial.preRoot fixedHash c s).afterGamma.digest 1
    (Transcript.ascii "pcs-group-norm-inverse-v3"))).bytes.drop 1 = _
  rw [frame_answer_freezes_the_tail]
  show (fixedHash (Transcript.frame (OuterInitial.etaState fixedHash c s).digest 1
    (Transcript.ascii "norm-denominator-challenges-v3"))).bytes.drop 1 = _
  rw [frame_answer_freezes_the_tail]
  show (fixedHash (Transcript.frame (OuterInitial.baseState fixedHash c s).digest 1
    (Transcript.ascii "public-input-aggregation-challenge-v3"))).bytes.drop 1 = _
  rw [frame_answer_freezes_the_tail]
  show (OuterInitial.absorbMessages fixedHash OuterInitial.startState
    (OuterInitial.baseMessages c s)).digest.bytes.drop 1 = _
  rw [absorb_messages_freeze_the_tail]
  rfl

/-- The norm-inverse root is absorbed into a digest that does not depend on it
(`OuterInitial.pre_root_challenges_ignore_norm_root`), so a change of that root
splits the chain the moment it is absorbed. -/
theorem norm_root_digests_split (c : Verifier.Config) (s : Verifier.Statement)
    (r : Verifier.Root)
    (h : frameTailFold 2 (OuterInitial.rootBytes s.normInverseRoot) ≠
      frameTailFold 2 (OuterInitial.rootBytes r)) :
    SplitAt (OuterInitial.normRootState fixedHash c s).digest
      (OuterInitial.normRootState fixedHash c { s with normInverseRoot := r }).digest := by
  rw [norm_root_digest_value, norm_root_digest_value,
    OuterInitial.pre_root_challenges_ignore_norm_root]
  exact frames_with_distinct_folds_split _ 2 _ _ h

theorem relation_digests_split (c : Verifier.Config) (s : Verifier.Statement)
    (r : Verifier.Root)
    (h : frameTailFold 2 (OuterInitial.rootBytes s.normInverseRoot) ≠
      frameTailFold 2 (OuterInitial.rootBytes r)) :
    SplitAt (OuterInitial.relationState fixedHash c s).digest
      (OuterInitial.relationState fixedHash c { s with normInverseRoot := r }).digest := by
  rw [relation_state_digest_value, relation_state_digest_value]
  refine frames_preserve_a_split _ _ 1 _ ?_
  rw [mix_state_digest_value, mix_state_digest_value]
  refine frames_preserve_a_split _ _ 1 _ ?_
  exact norm_root_digests_split c s r h

theorem derived_state_digests_split (c : Verifier.Config) (s : Verifier.Statement)
    (r : Verifier.Root)
    (h : frameTailFold 2 (OuterInitial.rootBytes s.normInverseRoot) ≠
      frameTailFold 2 (OuterInitial.rootBytes r)) :
    SplitAt (OuterInitial.derive fixedHash c s).state.digest
      (OuterInitial.derive fixedHash c { s with normInverseRoot := r }).state.digest := by
  rw [OuterInitial.derived_final_digest, OuterInitial.derived_final_digest]
  exact relation_digests_split c s r h

theorem snapshots_differ (s t : Transcript.State) (h : s.digest ≠ t.digest) :
    OuterInitial.snapshot s ≠ OuterInitial.snapshot t := by
  intro heq
  refine h (digest_ext _ _ ?_)
  rw [← OuterInitial.snapshot_retains_digest s, ← OuterInitial.snapshot_retains_digest t, heq]

theorem initial_transcripts_differ (c : Verifier.Config) (s : Verifier.Statement)
    (r : Verifier.Root)
    (h : frameTailFold 2 (OuterInitial.rootBytes s.normInverseRoot) ≠
      frameTailFold 2 (OuterInitial.rootBytes r)) :
    (OuterInitial.toInitial (OuterInitial.derive fixedHash c s)).transcript ≠
      (OuterInitial.toInitial
        (OuterInitial.derive fixedHash c { s with normInverseRoot := r })).transcript := by
  show OuterInitial.snapshot _ ≠ OuterInitial.snapshot _
  exact snapshots_differ _ _
    (split_at_gives_distinct_digests _ _ (derived_state_digests_split c s r h))

theorem alt_statement_is_the_root_variant :
    Verifier.statement RoutedAcceptance.altProof =
      { Verifier.statement RoutedAcceptance.routedProof with
          normInverseRoot := RoutedAcceptance.altProof.normInverseRoot } := rfl

theorem alt_root_folds_differ :
    frameTailFold 2
        (OuterInitial.rootBytes
          (Verifier.statement RoutedAcceptance.routedProof).normInverseRoot) ≠
      frameTailFold 2 (OuterInitial.rootBytes RoutedAcceptance.altProof.normInverseRoot) := by
  decide

/-- **(2b) THE DERIVED INITIAL TRANSCRIPT SEPARATES THE TWO PROOFS.**  The forty
snapshot bytes of `Verifier.Initial` differ between `RoutedAcceptance.routedProof`
and `RoutedAcceptance.altProof`, which differ only in `normInverseRoot`.  In
`RoutedAcceptance` those two transcripts are equal, which is why that module can
only record the adopted dependence implication as vacuously satisfied through its
collision disjunct. -/
theorem fixed_initial_transcript_separates_the_two_proofs
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) :
    ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript c
        RoutedAcceptance.routedProof).transcript ≠
      ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript c
        RoutedAcceptance.altProof).transcript := by
  show (OuterInitial.toInitial (OuterInitial.derive fixedHash c
    (Verifier.statement RoutedAcceptance.routedProof))).transcript ≠
      (OuterInitial.toInitial (OuterInitial.derive fixedHash c
        (Verifier.statement RoutedAcceptance.altProof))).transcript
  rw [alt_statement_is_the_root_variant]
  exact initial_transcripts_differ c _ _ alt_root_folds_differ

/-! ### 5c. THE COUNTERWEIGHT: the separation is fold-specific, not generic

`fixed_initial_transcript_separates_the_two_proofs` holds because the two
norm-inverse roots of the EXHIBITED pair have DIFFERENT one-byte frame folds
(`alt_root_folds_differ`: thirty-four against thirty-five).  It is therefore a
fact about that pair, not about distinct statements in general.  The chain below
exhibits a second pair of proofs -- `normInverseRoot = 1` against
`normInverseRoot = 256` -- whose folds AGREE, and proves that `fixedHash` gives
those two their whole derived initial transcript in common, exactly as
`RoutedAcceptance.routedHash` does for every pair.  Which pairs separate is a
property of the one-byte fold, not of statement distinctness. -/

theorem norm_root_digests_agree (c : Verifier.Config) (s : Verifier.Statement)
    (r : Verifier.Root)
    (h : frameTailFold 2 (OuterInitial.rootBytes s.normInverseRoot) =
      frameTailFold 2 (OuterInitial.rootBytes r)) :
    (OuterInitial.normRootState fixedHash c s).digest =
      (OuterInitial.normRootState fixedHash c { s with normInverseRoot := r }).digest := by
  rw [norm_root_digest_value, norm_root_digest_value,
    OuterInitial.pre_root_challenges_ignore_norm_root]
  exact frames_with_equal_folds_collide _ 2 _ _ h

theorem relation_digests_agree (c : Verifier.Config) (s : Verifier.Statement)
    (r : Verifier.Root)
    (h : frameTailFold 2 (OuterInitial.rootBytes s.normInverseRoot) =
      frameTailFold 2 (OuterInitial.rootBytes r)) :
    (OuterInitial.relationState fixedHash c s).digest =
      (OuterInitial.relationState fixedHash c { s with normInverseRoot := r }).digest := by
  rw [relation_state_digest_value, relation_state_digest_value, mix_state_digest_value,
    mix_state_digest_value, norm_root_digests_agree c s r h]

theorem initial_transcripts_agree (c : Verifier.Config) (s : Verifier.Statement)
    (r : Verifier.Root)
    (h : frameTailFold 2 (OuterInitial.rootBytes s.normInverseRoot) =
      frameTailFold 2 (OuterInitial.rootBytes r)) :
    (OuterInitial.toInitial (OuterInitial.derive fixedHash c s)).transcript =
      (OuterInitial.toInitial
        (OuterInitial.derive fixedHash c { s with normInverseRoot := r })).transcript := by
  have hd : (OuterInitial.derive fixedHash c s).state.digest =
      (OuterInitial.derive fixedHash c { s with normInverseRoot := r }).state.digest := by
    rw [OuterInitial.derived_final_digest, OuterInitial.derived_final_digest]
    exact relation_digests_agree c s r h
  have hc : (OuterInitial.derive fixedHash c s).state.counter =
      (OuterInitial.derive fixedHash c { s with normInverseRoot := r }).state.counter := by
    rw [OuterInitial.derived_final_counter, OuterInitial.derived_final_counter]
  show OuterInitial.bytesBack ((OuterInitial.derive fixedHash c s).state.digest.bytes ++
    Transcript.le 8 (OuterInitial.derive fixedHash c s).state.counter) = _
  rw [hd, hc]
  rfl

/-- The second alt root: `256` in place of the adopted alt proof's `1`. -/
def shiftRoot : Verifier.Root := ⟨256, by decide⟩

/-- The adopted routed proof carrying `shiftRoot` as its norm-inverse root. -/
def shiftProof : Verifier.Proof :=
  { RoutedAcceptance.routedProof with normInverseRoot := shiftRoot }

theorem shift_proof_differs_from_the_alt_proof :
    RoutedAcceptance.altProof.normInverseRoot ≠ shiftProof.normInverseRoot := by decide

theorem alt_and_shift_root_folds_agree :
    frameTailFold 2
        (OuterInitial.rootBytes
          (Verifier.statement RoutedAcceptance.altProof).normInverseRoot) =
      frameTailFold 2 (OuterInitial.rootBytes shiftRoot) := by decide

theorem shift_statement_is_the_alt_root_variant :
    Verifier.statement shiftProof =
      { Verifier.statement RoutedAcceptance.altProof with normInverseRoot := shiftRoot } := rfl

/-- **THE COUNTERWEIGHT, PROVED.**  Two proofs differing only in
`normInverseRoot` -- `1` against `256` -- share their WHOLE derived initial
transcript at `fixedHash`, exactly as every pair does at
`RoutedAcceptance.routedHash`.  Read this next to
`fixed_initial_transcript_separates_the_two_proofs`: separation holds for the
exhibited pair, whose folds differ, and fails for this pair, whose folds agree. -/
theorem fixed_hash_does_not_separate_the_other_root_pair
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) :
    ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript c
        RoutedAcceptance.altProof).transcript =
      ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript c
        shiftProof).transcript := by
  show (OuterInitial.toInitial (OuterInitial.derive fixedHash c
    (Verifier.statement RoutedAcceptance.altProof))).transcript =
      (OuterInitial.toInitial (OuterInitial.derive fixedHash c
        (Verifier.statement shiftProof))).transcript
  rw [shift_statement_is_the_alt_root_variant]
  exact initial_transcripts_agree c _ _ alt_and_shift_root_folds_agree

/-- The hash answers that feed the two proofs' `lambda` draws differ as well: the
relation states the two runs sample from are distinct digests, and the hash is
injective in the digest at counter zero. -/
theorem fixed_lambda_inputs_differ (c : Verifier.Config) :
    fixedHash (Transcript.challengeInput
        (OuterInitial.relationState fixedHash c
          (Verifier.statement RoutedAcceptance.routedProof)).digest 0) ≠
      fixedHash (Transcript.challengeInput
        (OuterInitial.relationState fixedHash c
          (Verifier.statement RoutedAcceptance.altProof)).digest 0) := by
  intro h
  refine split_at_gives_distinct_digests _ _ ?_
    (fixed_hash_is_injective_in_the_digest _ _ 0 (by decide) (by decide) (by decide) h)
  rw [alt_statement_is_the_root_variant]
  exact relation_digests_split c _ _ alt_root_folds_differ

/-! ## 5b. What the adopted `routedHash` does to the very same pair

The contrast is proved, not asserted: at the adopted digest-ignoring hash the two
proofs share their whole derived transcript.
-/

theorem take_append_le {α : Type} :
    ∀ (n : Nat) (xs ys : List α), n ≤ xs.length → (xs ++ ys).take n = xs.take n
  | 0, _, _, _ => rfl
  | _ + 1, [], _, h => absurd h (by simp)
  | n + 1, x :: xs, ys, h => by
      have hx : n ≤ xs.length := by simpa using h
      simpa only [List.cons_append, List.take_succ_cons, List.cons.injEq, true_and] using
        take_append_le n xs ys hx

theorem frame_reverse_tail (d : Transcript.Digest) (t : Transcript.Byte)
    (p : Transcript.Bytes) (h : 8 ≤ p.length) :
    (Transcript.frame d t p).reverse.take 8 = p.reverse.take 8 := by
  show ((((Transcript.framePrefix ++ Transcript.digestBytes d) ++ [t]) ++
    Transcript.le 8 p.length) ++ p).reverse.take 8 = _
  rw [List.reverse_append]
  exact take_append_le 8 _ _ (by rw [List.length_reverse]; exact h)

/-- The adopted `routedHash` answers `twoDigest` on EVERY frame whose payload is
at least eight bytes long and does not end in one of the three tuned counter
patterns -- so the adopted chain forgets the digest it was handed. -/
theorem routed_hash_on_a_long_frame (d : Transcript.Digest) (t : Transcript.Byte)
    (p : Transcript.Bytes) (h8 : 8 ≤ p.length)
    (h3 : p.reverse.take 8 ≠ RoutedAcceptance.counterTag 3)
    (h4 : p.reverse.take 8 ≠ RoutedAcceptance.counterTag 4)
    (h5 : p.reverse.take 8 ≠ RoutedAcceptance.counterTag 5) :
    RoutedAcceptance.routedHash (Transcript.frame d t p) = RoutedAcceptance.twoDigest := by
  show (if _ then _ else _) = _
  rw [frame_reverse_tail d t p h8, if_neg h3, if_neg h4, if_neg h5]

/-- **WHY THE BYTE-FIFTEEN GATE IS NOT DECORATION.**  The round-three commit frame
`Transcript.absorb hash s 2 (Transcript.le 8 3)` of `Transcript.commitRound` ends
in exactly the counter-three pattern, and the adopted `routedHash`, which looks
only at the last eight bytes of whatever it is handed, collapses on it. -/
theorem routed_hash_collapses_on_the_round_three_commit_frame (d : Transcript.Digest) :
    RoutedAcceptance.routedHash (Transcript.frame d 2 (Transcript.le 8 3)) =
      RoutedAcceptance.minusOneDigest := by
  show (if _ then _ else _) = _
  rw [frame_reverse_tail d 2 (Transcript.le 8 3) (by simp [Transcript.le_length]),
    if_pos (by decide : (Transcript.le 8 3).reverse.take 8 = RoutedAcceptance.counterTag 3)]

/-- `fixedHash` does not: the byte-fifteen gate routes that same frame to the
FRAME branch, where it stays injective in the incoming digest. -/
theorem fixed_hash_keeps_the_round_three_commit_frame_injective (d e : Transcript.Digest)
    (h : fixedHash (Transcript.frame d 2 (Transcript.le 8 3)) =
      fixedHash (Transcript.frame e 2 (Transcript.le 8 3))) : d = e :=
  frame_hash_is_injective_in_the_digest d e 2 _ h

theorem routed_chain_agrees_at_the_norm_root (c : Verifier.Config) :
    (OuterInitial.normRootState RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.routedProof)).digest =
      (OuterInitial.normRootState RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.altProof)).digest := by
  rw [norm_root_digest_value, norm_root_digest_value,
    routed_hash_on_a_long_frame _ 2 _ (by decide) (by decide) (by decide) (by decide),
    routed_hash_on_a_long_frame _ 2 _ (by decide) (by decide) (by decide) (by decide)]

theorem routed_chain_agrees_at_the_relation_state (c : Verifier.Config) :
    (OuterInitial.relationState RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.routedProof)).digest =
      (OuterInitial.relationState RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.altProof)).digest := by
  rw [relation_state_digest_value, relation_state_digest_value, mix_state_digest_value,
    mix_state_digest_value, routed_chain_agrees_at_the_norm_root]

/-- **THE CONTRAST, PROVED.**  At the adopted `RoutedAcceptance.routedHash` the
two proofs have the SAME derived initial transcript; at `fixedHash` they do not
(`fixed_initial_transcript_separates_the_two_proofs`).  That is the whole of the
improvement, stated as one pair of theorems. -/
theorem routed_initial_transcripts_do_not_separate_the_two_proofs
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c : Verifier.Config) :
    ((DerivedAcceptance.derivedEngine RoutedAcceptance.routedHash khash P).initialTranscript c
        RoutedAcceptance.routedProof).transcript =
      ((DerivedAcceptance.derivedEngine RoutedAcceptance.routedHash khash P).initialTranscript c
        RoutedAcceptance.altProof).transcript := by
  have hd : (OuterInitial.derive RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.routedProof)).state.digest =
      (OuterInitial.derive RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.altProof)).state.digest := by
    rw [OuterInitial.derived_final_digest, OuterInitial.derived_final_digest]
    exact routed_chain_agrees_at_the_relation_state c
  have hc : (OuterInitial.derive RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.routedProof)).state.counter =
      (OuterInitial.derive RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.altProof)).state.counter := by
    rw [OuterInitial.derived_final_counter, OuterInitial.derived_final_counter]
  show OuterInitial.bytesBack ((OuterInitial.derive RoutedAcceptance.routedHash c
      (Verifier.statement RoutedAcceptance.routedProof)).state.digest.bytes ++
      Transcript.le 8 (OuterInitial.derive RoutedAcceptance.routedHash c
        (Verifier.statement RoutedAcceptance.routedProof)).state.counter) = _
  rw [hd, hc]
  rfl

/-- **AND WHAT IS STILL NOT CLAIMED.**  `fixedHash` is NOT collision-free: it
maps the counter-four and counter-five challenge inputs of one digest to the same
answer, so it satisfies the adopted `CommitmentOrder.TranscriptCollision`
predicate exactly as `routedHash` does.  The repair is that the derived
transcripts of the two proofs are proved DIFFERENT DIRECTLY
(`fixed_initial_transcript_separates_the_two_proofs`), not that the adopted
dependence implication has become non-vacuous. -/
theorem fixed_hash_is_still_a_transcript_collision :
    CommitmentOrder.TranscriptCollision fixedHash := by
  refine ⟨Transcript.challengeInput RoutedAcceptance.zeroDigest 4,
    Transcript.challengeInput RoutedAcceptance.zeroDigest 5, ?_, ?_⟩
  · intro h
    exact absurd (Transcript.challenge_inputs_distinguish_bounded_counters
      RoutedAcceptance.zeroDigest 4 5 (by decide) (by decide) h) (by decide)
  · rw [fixed_hash_at_four, fixed_hash_at_five]

/-! ## 6. The derived relation challenges at the repaired hash -/

theorem fixed_challenge_at_three (d : Transcript.Digest) :
    Transcript.challengeAt fixedHash d 3 = ⟨18446744069414584320, by decide⟩ := by
  apply Fin.ext
  show Transcript.fromLe (Transcript.digestBytes (fixedHash
    (Transcript.challengeInput d 3))) % Transcript.modulus = _
  rw [fixed_hash_at_three]
  decide

theorem fixed_challenge_at_four (d : Transcript.Digest) :
    Transcript.challengeAt fixedHash d 4 = ⟨0, by decide⟩ := by
  apply Fin.ext
  show Transcript.fromLe (Transcript.digestBytes (fixedHash
    (Transcript.challengeInput d 4))) % Transcript.modulus = _
  rw [fixed_hash_at_four]
  decide

theorem fixed_challenge_at_five (d : Transcript.Digest) :
    Transcript.challengeAt fixedHash d 5 = ⟨0, by decide⟩ := by
  apply Fin.ext
  show Transcript.fromLe (Transcript.digestBytes (fixedHash
    (Transcript.challengeInput d 5))) % Transcript.modulus = _
  rw [fixed_hash_at_five]
  decide

/-- The draw that starts at counter three is exactly `-1`, at EVERY digest. -/
theorem fixed_draw_at_three (d : Transcript.Digest) :
    (OuterInitial.draw fixedHash ⟨d, 3⟩).1 = Verifier.sub Verifier.zero Norm.one := by
  show Connections.fromTranscript ⟨Transcript.challengeAt fixedHash d 3,
    Transcript.challengeAt fixedHash d (3 + 1),
    Transcript.challengeAt fixedHash d (3 + 2)⟩ = _
  rw [show (3 + 1 : Nat) = 4 from rfl, show (3 + 2 : Nat) = 5 from rfl,
    fixed_challenge_at_three, fixed_challenge_at_four, fixed_challenge_at_five]
  apply Subtype.eq
  decide

/-- **THE OBSTRUCTION FACTOR IS STILL KILLED.**  The derived `rho` is `-1` at
every configuration and every statement -- the ONE place the repaired hash is
still answered by counter alone, and the place the wire-pair cancellation
needs. -/
theorem fixed_rho_is_minus_one (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive fixedHash c s).log.rho = Verifier.sub Verifier.zero Norm.one := by
  show (OuterInitial.draw fixedHash
    (OuterInitial.draw fixedHash (OuterInitial.relationState fixedHash c s)).2).1 = _
  exact fixed_draw_at_three _

/-- **THE OTHER COUNTER-KEYED RESIDUE, DISCLOSED.**  The derived `gamma` also
starts at counter three, of the denominator state, so it too is `-1` at every
digest.  These two draws are the ONLY challenges of the initial derivation that
remain digest-blind. -/
theorem fixed_gamma_is_minus_one (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive fixedHash c s).log.gamma = Verifier.sub Verifier.zero Norm.one := by
  show (OuterInitial.draw fixedHash
    (OuterInitial.draw fixedHash (OuterInitial.denominatorState fixedHash c s)).2).1 = _
  exact fixed_draw_at_three _

/-- `eta`, `beta`, `xi`, `lambda`, `kappa`, the taus, `alpha` and the gate taus
are all drawn at counters outside the tuned three, so each of them is the hash's
answer on a challenge input whose digest is the running chain digest.  Recorded
here as the exact draw the adopted schedule performs. -/
theorem fixed_lambda_is_drawn_from_the_relation_digest (c : Verifier.Config)
    (s : Verifier.Statement) :
    (OuterInitial.derive fixedHash c s).log.lambda =
      Connections.fromTranscript
        ⟨Transcript.challengeAt fixedHash (OuterInitial.relationState fixedHash c s).digest 0,
          Transcript.challengeAt fixedHash (OuterInitial.relationState fixedHash c s).digest 1,
          Transcript.challengeAt fixedHash (OuterInitial.relationState fixedHash c s).digest 2⟩ :=
  rfl

/-! ### 6b. The residue ledger's first two summands, as theorems

The header's squeeze ledger is `102 + 78 + 48 = 228`, of which `6 + 39 + 3 = 48`
are digest-blind.  The first summand and the per-round count are proved here; the
index-sampling summand, and the three total lines, remain arithmetic on the cited
definitions. -/

/-- **THE LEDGER'S FIRST SUMMAND, AS A THEOREM.**  The counter resets at every
absorption, so `OuterInitial.derive` squeezes its four states `3`, `6`, `3` and
`90` times: `3 + 6 + 3 + 90 = 102`.  Universal in the hash and the statement. -/
theorem derive_squeeze_counts (hash : Transcript.Hash) (s : Verifier.Statement) :
    (OuterInitial.draw hash
        (OuterInitial.etaState hash RoutedAcceptance.routedConfig s)).2.counter = 3 ∧
      (OuterInitial.preRoot hash RoutedAcceptance.routedConfig s).afterGamma.counter = 6 ∧
      (OuterInitial.draw hash
        (OuterInitial.mixState hash RoutedAcceptance.routedConfig s)).2.counter = 3 ∧
      (OuterInitial.derive hash RoutedAcceptance.routedConfig s).state.counter = 90 := by
  refine ⟨?_, OuterInitial.pre_root_counter hash RoutedAcceptance.routedConfig s, ?_, ?_⟩
  · rw [OuterInitial.draw_counter]; rfl
  · rw [OuterInitial.draw_counter]; rfl
  · show (OuterInitial.drawMany hash 13
        (OuterInitial.draw hash (OuterInitial.drawMany hash 13
          (OuterInitial.relations hash RoutedAcceptance.routedConfig s).afterKappa).2).2).2.counter
      = 90
    rw [(OuterInitial.draw_many_shape hash 13 _).2.2, OuterInitial.draw_counter,
      (OuterInitial.draw_many_shape hash 13 _).2.2,
      OuterInitial.relation_counter hash RoutedAcceptance.routedConfig s]

/-- **THE PER-ROUND COUNT, AS A THEOREM.**  Each round commits by absorbing, which
resets the counter to zero, and then squeezes six: so its six squeezes sit at
counters `0`-`5`, three of which are the tuned ones.  That is the ledger's
`3 * 13 = 39`. -/
theorem a_round_squeezes_six_from_counter_zero (hash : Transcript.Hash) (s : Transcript.State)
    (round : Nat) (log gate : List Transcript.Ext3) :
    (Transcript.commitRound hash s round log gate).counter = 0 := rfl

/-! ## 7. Acceptance at eighty routed wires -/

theorem fixed_claims_vanish (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).logClaim = Verifier.zero ∧
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).gateClaim = Verifier.zero := by
  refine DerivedAcceptance.run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

/-- **GATE 7.**  The installed `Norm.normEvaluation` at `numRouted = 80`, the wire
loop running eighty times, matches the zero log claim -- because the derived
`rho` is `-1`. -/
theorem fixed_log_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).logTerminal
        RoutedAcceptance.routedConfig
        ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
          RoutedAcceptance.routedConfig RoutedAcceptance.routedProof)
        RoutedAcceptance.routedProof
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
          RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).logPoint =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).logClaim := by
  rw [(fixed_claims_vanish khash P).1]
  refine RoutedAcceptance.norm_terminal_vanishes_at_minus_one_rho
    RoutedAcceptance.routedConfig _ (Verifier.normTerminalInput RoutedAcceptance.routedProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j) rfl ?_
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive fixedHash RoutedAcceptance.routedConfig
      (Verifier.statement RoutedAcceptance.routedProof)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact fixed_rho_is_minus_one _ _

theorem fixed_expected_claims_are_zero (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold RoutedAcceptance.routedConfig
    RoutedAcceptance.routedProof
    (Verifier.derivedIndices (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  exact ⟨DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _⟩

/-- **GATE 8.** -/
theorem fixed_whir_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (DerivedAcceptance.derivedEngine fixedHash khash P)
      (Verifier.derivedContext (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.routedProof)
      RoutedAcceptance.routedProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [fixed_expected_claims_are_zero khash P]
  rfl

theorem fixed_gate_evaluation_at_the_proof (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).gateEvaluation
        RoutedAcceptance.routedConfig RoutedAcceptance.routedProof.used.gateWitness
        (RoutedAcceptance.routedProof.used.gatePreprocessed.take
          RoutedAcceptance.routedConfig.numConstants) publicHash alpha = Verifier.zero := by
  rw [DerivedAcceptance.derived_gate_evaluation_field]
  simp only []
  rw [RoutedAcceptance.routed_gate_claim_columns_are_zero.1,
    RoutedAcceptance.routed_gate_claim_columns_are_zero.2,
    RoutedAcceptance.routed_gate_evaluation_vanishes publicHash hp]
  rfl

/-- **GATE 9.** -/
theorem fixed_gate_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.routedProof =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).gateClaim := by
  rw [(fixed_claims_vanish khash P).2, DerivedAcceptance.gate_terminal_unfolds,
    DerivedAcceptance.derived_public_input_hash_field,
    fixed_gate_evaluation_at_the_proof khash P _
      (PublicInputHashBinding.hash_no_pad_length RoutedAcceptance.routedProof.publicInputs)]
  exact Algebra.vmul_zero _

/-- **THE HEADLINE: ACCEPTANCE AT EIGHTY ROUTED WIRES, AT A DIGEST-READING
TRANSCRIPT HASH.**  The adopted `Verifier.verify`, at the adopted
`DerivedAcceptance.derivedEngine`, at the adopted `RoutedAcceptance.routedConfig`
and `RoutedAcceptance.routedProof`, for EVERY configuration hash `khash` and
EVERY WHIR profile passing the canonical check. -/
theorem fixed_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P RoutedAcceptance.routedConfig = true) :
    Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash P)
      (RoutedAcceptance.routedPin khash) 1 RoutedAcceptance.routedConfig
      RoutedAcceptance.routedProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl
    RoutedAcceptance.routed_config_envelope ?_ (RoutedAcceptance.routed_shape_holds khash)
    (DerivedAcceptance.derived_tau_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.routedProof).1
    (DerivedAcceptance.derived_tau_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.routedProof).2
    (DerivedAcceptance.derived_index_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.routedProof (by decide)).1
    (DerivedAcceptance.derived_index_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.routedProof (by decide)).2
    (fixed_log_terminal_gate khash P) (fixed_whir_gate khash P)
    (fixed_gate_terminal_gate khash P)
  show ExplicitEngine.explicitDeployment P DerivedAcceptance.derivedConfig
    RoutedAcceptance.routedConfig = true
  have hw : RoutedAcceptance.routedConfig.whirEncoding =
    DerivedAcceptance.derivedConfig.whirEncoding := rfl
  simp [ExplicitEngine.explicitDeployment, hw, hprofile]

/-- **THE CLOSED ACCEPTANCE.**  No hypothesis at all, for EVERY configuration
hash. -/
theorem fixed_acceptance_at_the_profile_witness (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash
        DerivedAcceptance.derivedProfile) (RoutedAcceptance.routedPin khash) 1
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof = .ok () :=
  fixed_acceptance khash DerivedAcceptance.derivedProfile
    RoutedAcceptance.routed_profile_passes_the_canonical_check

/-- The same instance at the adopted SHARP profile, whose parameter decoder
rejects every nonempty WHIR encoding and whose digests are non-constant. -/
theorem fixed_acceptance_at_the_sharp_profile (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash
        DerivedAcceptance.probeSharpProfile) (RoutedAcceptance.routedPin khash) 1
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof = .ok () :=
  fixed_acceptance khash DerivedAcceptance.probeSharpProfile
    RoutedAcceptance.routed_sharp_profile_passes

/-! ## 8. The same instance through the adopted `Integrated.verify` -/

theorem fixed_engine_is_its_own_model_engine (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.modelEngine (DerivedAcceptance.derivedEngine fixedHash khash P)
        DerivedAcceptance.derivedDecoder =
      DerivedAcceptance.derivedEngine fixedHash khash P := rfl

theorem fixed_log_point_length (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).logPoint.length = 13 := by
  have h := (Verifier.runRounds_lengths (InstalledRoundCommit.concreteCommitRound fixedHash)
    (Verifier.start ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof))
    (RoutedAcceptance.routedProof.logRounds.zip RoutedAcceptance.routedProof.gateRounds)).2.1
  have hz : (RoutedAcceptance.routedProof.logRounds.zip
    RoutedAcceptance.routedProof.gateRounds).length = 13 := rfl
  rw [hz] at h
  exact h

/-- The FULL norm shape predicate of the checked adapter holds, including the
`c.kIs.length = c.numRouted` conjunct at eighty. -/
theorem fixed_norm_shape_valid (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Norm.shapeValid RoutedAcceptance.routedConfig
        (Norm.challengesFromInitial
          ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
            RoutedAcceptance.routedConfig RoutedAcceptance.routedProof))
        (Verifier.normTerminalInput RoutedAcceptance.routedProof)
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
          RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).logPoint = true := by
  have hpt := fixed_log_point_length khash P
  have htau := (DerivedAcceptance.derived_tau_lengths fixedHash khash P
    RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).1
  simp only [Norm.shapeValid, decide_eq_true_eq]
  refine ⟨hpt, ?_, ?_, List.length_replicate _ _, by decide, List.length_replicate _ _,
    List.length_replicate _ _, List.length_replicate _ _, rfl, rfl, ?_⟩
  · show ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).logTau.length = _
    rw [htau, hpt]
    rfl
  · show (List.replicate 13 (Verifier.base 1)).length = _
    rw [List.length_replicate, hpt]
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

theorem fixed_integrated_norm_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.normResult (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof = some Verifier.zero := by
  have hchal : ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof).logChallenges.length = 7 :=
    (OuterInitial.derived_initial_shape fixedHash RoutedAcceptance.routedConfig
      (Verifier.statement RoutedAcceptance.routedProof)).1
  simp only [Integrated.normResult, Norm.checkedNormEvaluation, Norm.checkedEvaluate,
    hchal, if_pos, fixed_norm_shape_valid, ite_true]
  show some (Norm.normEvaluation RoutedAcceptance.routedConfig _ _ _) = _
  refine congrArg some ?_
  refine RoutedAcceptance.norm_terminal_vanishes_at_minus_one_rho
    RoutedAcceptance.routedConfig _ (Verifier.normTerminalInput RoutedAcceptance.routedProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j) rfl ?_
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive fixedHash RoutedAcceptance.routedConfig
      (Verifier.statement RoutedAcceptance.routedProof)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact fixed_rho_is_minus_one _ _

theorem fixed_integrated_gate_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.gateResult (DerivedAcceptance.derivedEngine fixedHash khash P)
      DerivedAcceptance.derivedDecoder RoutedAcceptance.routedConfig
      RoutedAcceptance.routedProof = some Verifier.zero := by
  show Integrated.evaluateGate DerivedAcceptance.derivedDecoder RoutedAcceptance.routedConfig
    RoutedAcceptance.routedProof.used.gateWitness
    (RoutedAcceptance.routedProof.used.gatePreprocessed.take
      RoutedAcceptance.routedConfig.numConstants)
    ((DerivedAcceptance.derivedEngine fixedHash khash P).publicInputsHash
      RoutedAcceptance.routedProof.publicInputs) _ = _
  rw [DerivedAcceptance.derived_public_input_hash_field,
    RoutedAcceptance.routed_gate_claim_columns_are_zero.1,
    RoutedAcceptance.routed_gate_claim_columns_are_zero.2,
    RoutedAcceptance.routed_gate_evaluation_vanishes _
      (PublicInputHashBinding.hash_no_pad_length RoutedAcceptance.routedProof.publicInputs)]

/-- **THE INTEGRATED ACCEPTANCE AT EIGHTY ROUTED WIRES.** -/
theorem fixed_integrated_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P RoutedAcceptance.routedConfig = true) :
    Integrated.verify (DerivedAcceptance.derivedEngine fixedHash khash P)
      DerivedAcceptance.derivedDecoder (RoutedAcceptance.routedPin khash) 1
      RoutedAcceptance.routedConfig RoutedAcceptance.routedProof = .ok () := by
  simp only [Integrated.verify, fixed_engine_is_its_own_model_engine,
    fixed_integrated_norm_result, fixed_integrated_gate_result]
  exact fixed_acceptance khash P hprofile

theorem fixed_integrated_acceptance_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Integrated.verify (DerivedAcceptance.derivedEngine fixedHash khash
        DerivedAcceptance.derivedProfile) DerivedAcceptance.derivedDecoder
      (RoutedAcceptance.routedPin khash) 1 RoutedAcceptance.routedConfig
      RoutedAcceptance.routedProof = .ok () :=
  fixed_integrated_acceptance khash DerivedAcceptance.derivedProfile
    RoutedAcceptance.routed_profile_passes_the_canonical_check

/-! ## 8b. The same instance at three public inputs

The adopted `RoutedAcceptance` carries its instance to `numPublicInputs = 3`, the
adopted maximal value, at a second configuration.  That whole section is carried
here too, so nothing of the adopted result is lost by repairing the hash.
-/

theorem fixed_public_claims_vanish (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedPublicConfig
        RoutedAcceptance.routedPublicProof).logClaim = Verifier.zero ∧
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedPublicConfig
        RoutedAcceptance.routedPublicProof).gateClaim = Verifier.zero := by
  refine DerivedAcceptance.run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

theorem fixed_public_rho_is_minus_one (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (c : Verifier.Config) (p : Verifier.Proof) :
    (Norm.challengesFromInitial
      ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript c p)).rho =
      Verifier.sub Verifier.zero Norm.one := by
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive fixedHash c (Verifier.statement p)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact fixed_rho_is_minus_one _ _

theorem fixed_public_log_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).logTerminal
        RoutedAcceptance.routedPublicConfig
        ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
          RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof)
        RoutedAcceptance.routedPublicProof
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
          RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).logPoint =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).logClaim := by
  rw [(fixed_public_claims_vanish khash P).1]
  exact RoutedAcceptance.norm_terminal_vanishes_at_minus_one_rho_and_zero_binding
    RoutedAcceptance.routedPublicConfig _
    (Verifier.normTerminalInput RoutedAcceptance.routedPublicProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j)
    (RoutedAcceptance.routed_public_binding_vanishes _ _)
    (fixed_public_rho_is_minus_one khash P RoutedAcceptance.routedPublicConfig
      RoutedAcceptance.routedPublicProof)

theorem fixed_public_expected_claims_are_zero (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold RoutedAcceptance.routedPublicConfig
    RoutedAcceptance.routedPublicProof
    (Verifier.derivedIndices (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  exact ⟨DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _⟩

theorem fixed_public_whir_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (DerivedAcceptance.derivedEngine fixedHash khash P)
      (Verifier.derivedContext (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof)
      RoutedAcceptance.routedPublicProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [fixed_public_expected_claims_are_zero khash P]
  rfl

theorem fixed_public_gate_evaluation_at_the_proof (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).gateEvaluation
        RoutedAcceptance.routedPublicConfig
        RoutedAcceptance.routedPublicProof.used.gateWitness
        (RoutedAcceptance.routedPublicProof.used.gatePreprocessed.take
          RoutedAcceptance.routedPublicConfig.numConstants) publicHash alpha = Verifier.zero := by
  rw [DerivedAcceptance.derived_gate_evaluation_field]
  simp only []
  rw [RoutedAcceptance.routed_public_gate_claim_columns_are_zero.1,
    RoutedAcceptance.routed_public_gate_claim_columns_are_zero.2,
    RoutedAcceptance.routed_public_gate_evaluation_vanishes publicHash hp]
  rfl

theorem fixed_public_gate_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).gateClaim := by
  rw [(fixed_public_claims_vanish khash P).2, DerivedAcceptance.gate_terminal_unfolds,
    DerivedAcceptance.derived_public_input_hash_field,
    fixed_public_gate_evaluation_at_the_proof khash P _
      (PublicInputHashBinding.hash_no_pad_length
        RoutedAcceptance.routedPublicProof.publicInputs)]
  exact Algebra.vmul_zero _

/-- **ACCEPTANCE AT EIGHTY ROUTED WIRES AND THREE PUBLIC INPUTS.** -/
theorem fixed_public_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P RoutedAcceptance.routedPublicConfig = true) :
    Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash P)
      (RoutedAcceptance.routedPublicPin khash) 1 RoutedAcceptance.routedPublicConfig
      RoutedAcceptance.routedPublicProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl
    RoutedAcceptance.routed_public_config_envelope ?_
    (RoutedAcceptance.routed_public_shape_holds khash)
    (DerivedAcceptance.derived_tau_lengths fixedHash khash P
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).1
    (DerivedAcceptance.derived_tau_lengths fixedHash khash P
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).2
    (DerivedAcceptance.derived_index_lengths fixedHash khash P
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof (by decide)).1
    (DerivedAcceptance.derived_index_lengths fixedHash khash P
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof (by decide)).2
    (fixed_public_log_terminal_gate khash P) (fixed_public_whir_gate khash P)
    (fixed_public_gate_terminal_gate khash P)
  show ExplicitEngine.explicitDeployment P DerivedAcceptance.derivedConfig
    RoutedAcceptance.routedPublicConfig = true
  have hw : RoutedAcceptance.routedPublicConfig.whirEncoding =
    DerivedAcceptance.derivedConfig.whirEncoding := rfl
  simp [ExplicitEngine.explicitDeployment, hw, hprofile]

theorem fixed_public_acceptance_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash
        DerivedAcceptance.derivedProfile) (RoutedAcceptance.routedPublicPin khash) 1
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof = .ok () :=
  fixed_public_acceptance khash DerivedAcceptance.derivedProfile
    RoutedAcceptance.routed_public_profile_passes_the_canonical_check

theorem fixed_public_log_point_length (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedPublicConfig
      RoutedAcceptance.routedPublicProof).logPoint.length = 13 := by
  have h := (Verifier.runRounds_lengths (InstalledRoundCommit.concreteCommitRound fixedHash)
    (Verifier.start ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof))
    (RoutedAcceptance.routedPublicProof.logRounds.zip
      RoutedAcceptance.routedPublicProof.gateRounds)).2.1
  have hz : (RoutedAcceptance.routedPublicProof.logRounds.zip
    RoutedAcceptance.routedPublicProof.gateRounds).length = 13 := rfl
  rw [hz] at h
  exact h

theorem fixed_public_targets_are_in_range (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (i : Nat) :
    (Norm.targetAt RoutedAcceptance.routedPublicConfig.publicInputWireMap i).column <
        RoutedAcceptance.routedPublicConfig.numRouted ∧
      (Norm.targetAt RoutedAcceptance.routedPublicConfig.publicInputWireMap i).row <
        2 ^ (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
          RoutedAcceptance.routedPublicConfig
          RoutedAcceptance.routedPublicProof).logPoint.length := by
  rw [RoutedAcceptance.routed_public_wire_map, RoutedAcceptance.target_at_zero_map,
    fixed_public_log_point_length khash P]
  exact ⟨by decide, by decide⟩

theorem fixed_public_norm_shape_valid (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Norm.shapeValid RoutedAcceptance.routedPublicConfig
        (Norm.challengesFromInitial
          ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
            RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof))
        (Verifier.normTerminalInput RoutedAcceptance.routedPublicProof)
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
          RoutedAcceptance.routedPublicConfig
          RoutedAcceptance.routedPublicProof).logPoint = true := by
  have hpt := fixed_public_log_point_length khash P
  have htau := (DerivedAcceptance.derived_tau_lengths fixedHash khash P
    RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).1
  simp only [Norm.shapeValid, decide_eq_true_eq]
  refine ⟨hpt, ?_, ?_, List.length_replicate _ _, by decide, List.length_replicate _ _,
    List.length_replicate _ _, List.length_replicate _ _, List.length_replicate _ _, ?_, ?_⟩
  · show ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof).logTau.length = _
    rw [htau, hpt]
    rfl
  · show (List.replicate 13 (Verifier.base 1)).length = _
    rw [List.length_replicate, hpt]
  · show (List.replicate 9 (0 : UInt8)).length =
      3 * (List.replicate 3 (Verifier.base 0)).length
    rw [List.length_replicate, List.length_replicate]
  · intro i _
    exact fixed_public_targets_are_in_range khash P i

theorem fixed_public_integrated_norm_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.normResult (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof =
      some Verifier.zero := by
  have hchal : ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
      RoutedAcceptance.routedPublicConfig
      RoutedAcceptance.routedPublicProof).logChallenges.length = 7 :=
    (OuterInitial.derived_initial_shape fixedHash RoutedAcceptance.routedPublicConfig
      (Verifier.statement RoutedAcceptance.routedPublicProof)).1
  simp only [Integrated.normResult, Norm.checkedNormEvaluation, Norm.checkedEvaluate,
    hchal, if_pos, fixed_public_norm_shape_valid, ite_true]
  show some (Norm.normEvaluation RoutedAcceptance.routedPublicConfig _ _ _) = _
  refine congrArg some ?_
  exact RoutedAcceptance.norm_terminal_vanishes_at_minus_one_rho_and_zero_binding
    RoutedAcceptance.routedPublicConfig _
    (Verifier.normTerminalInput RoutedAcceptance.routedPublicProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j)
    (RoutedAcceptance.routed_public_binding_vanishes _ _)
    (fixed_public_rho_is_minus_one khash P RoutedAcceptance.routedPublicConfig
      RoutedAcceptance.routedPublicProof)

theorem fixed_public_integrated_gate_result (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Integrated.gateResult (DerivedAcceptance.derivedEngine fixedHash khash P)
      DerivedAcceptance.derivedDecoder RoutedAcceptance.routedPublicConfig
      RoutedAcceptance.routedPublicProof = some Verifier.zero := by
  show Integrated.evaluateGate DerivedAcceptance.derivedDecoder
    RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof.used.gateWitness
    (RoutedAcceptance.routedPublicProof.used.gatePreprocessed.take
      RoutedAcceptance.routedPublicConfig.numConstants)
    ((DerivedAcceptance.derivedEngine fixedHash khash P).publicInputsHash
      RoutedAcceptance.routedPublicProof.publicInputs) _ = _
  rw [DerivedAcceptance.derived_public_input_hash_field,
    RoutedAcceptance.routed_public_gate_claim_columns_are_zero.1,
    RoutedAcceptance.routed_public_gate_claim_columns_are_zero.2,
    RoutedAcceptance.routed_public_gate_evaluation_vanishes _
      (PublicInputHashBinding.hash_no_pad_length
        RoutedAcceptance.routedPublicProof.publicInputs)]

/-- **THE INTEGRATED ACCEPTANCE AT EIGHTY ROUTED WIRES AND THREE PUBLIC
INPUTS.**  Every conjunct of `Norm.shapeValid` is live, the public-input clause
included. -/
theorem fixed_public_integrated_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P RoutedAcceptance.routedPublicConfig = true) :
    Integrated.verify (DerivedAcceptance.derivedEngine fixedHash khash P)
      DerivedAcceptance.derivedDecoder (RoutedAcceptance.routedPublicPin khash) 1
      RoutedAcceptance.routedPublicConfig RoutedAcceptance.routedPublicProof = .ok () := by
  simp only [Integrated.verify, fixed_engine_is_its_own_model_engine,
    fixed_public_integrated_norm_result, fixed_public_integrated_gate_result]
  exact fixed_public_acceptance khash P hprofile

theorem fixed_public_integrated_acceptance_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Integrated.verify (DerivedAcceptance.derivedEngine fixedHash khash
        DerivedAcceptance.derivedProfile) DerivedAcceptance.derivedDecoder
      (RoutedAcceptance.routedPublicPin khash) 1 RoutedAcceptance.routedPublicConfig
      RoutedAcceptance.routedPublicProof = .ok () :=
  fixed_public_integrated_acceptance khash DerivedAcceptance.derivedProfile
    RoutedAcceptance.routed_public_profile_passes_the_canonical_check

/-! ## 9. The separation question: an honest negative -/

theorem fixed_claims_vanish_at_the_alt_proof (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.altProof).logClaim = Verifier.zero ∧
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.altProof).gateClaim = Verifier.zero := by
  refine DerivedAcceptance.run_rounds_keeps_zero_claims _ _ _ ?_ rfl rfl
  intro m hm
  obtain ⟨hl, hg⟩ := List.of_mem_zip hm
  exact ⟨⟨5, List.eq_of_mem_replicate hl⟩, ⟨10, List.eq_of_mem_replicate hg⟩⟩

theorem fixed_alt_log_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).logTerminal
        RoutedAcceptance.routedConfig
        ((DerivedAcceptance.derivedEngine fixedHash khash P).initialTranscript
          RoutedAcceptance.routedConfig RoutedAcceptance.altProof) RoutedAcceptance.altProof
        (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
          RoutedAcceptance.routedConfig RoutedAcceptance.altProof).logPoint =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.altProof).logClaim := by
  rw [(fixed_claims_vanish_at_the_alt_proof khash P).1]
  refine RoutedAcceptance.norm_terminal_vanishes_at_minus_one_rho
    RoutedAcceptance.routedConfig _ (Verifier.normTerminalInput RoutedAcceptance.altProof) _
    (fun j => DerivedAcceptance.getD_replicate_zero 160 j) rfl ?_
  show (Norm.challengesFromInitial (OuterInitial.toInitial
    (OuterInitial.derive fixedHash RoutedAcceptance.routedConfig
      (Verifier.statement RoutedAcceptance.altProof)))).rho = _
  rw [OuterInitial.initial_norm_adapter_is_lossless]
  exact fixed_rho_is_minus_one _ _

theorem fixed_alt_expected_claims_are_zero (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (Verifier.derivedContext (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedConfig RoutedAcceptance.altProof).expectedClaims =
      [some Verifier.zero, some Verifier.zero, some Verifier.zero, some Verifier.zero,
        some Verifier.zero, none] := by
  show Verifier.expectedClaims Connections.packedFold RoutedAcceptance.routedConfig
    RoutedAcceptance.altProof
    (Verifier.derivedIndices (DerivedAcceptance.derivedEngine fixedHash khash P)
      RoutedAcceptance.routedConfig RoutedAcceptance.altProof) = _
  simp only [Verifier.expectedClaims, List.cons.injEq, Option.some.injEq, and_true]
  exact ⟨DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _,
    DerivedAcceptance.packed_fold_of_zero_claims 160 _ _⟩

/-- **THE GATE THAT FAILS TO BIND, NAMED.**  Gate 8 does compare the parsed
roots with the context's three roots, `normInverseRoot` among them -- but the
engine's `parseWhir` is still the adopted fixture's, which ECHOES those very
roots back, so the comparison is an identity and binds nothing. -/
theorem fixture_parse_echoes_the_context_roots (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (ctx : Verifier.WhirContext) (a b : Verifier.Bytes) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).parseWhir ctx a b =
      some ⟨ctx.roots, ctx.roots, List.replicate 6 Verifier.zero⟩ := rfl

theorem fixed_alt_whir_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.verifyWhir (DerivedAcceptance.derivedEngine fixedHash khash P)
      (Verifier.derivedContext (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.altProof)
      RoutedAcceptance.altProof = true := by
  simp only [Verifier.verifyWhir, Verifier.rootsAndClaimsMatch]
  rw [fixed_alt_expected_claims_are_zero khash P]
  rfl

theorem fixed_alt_gate_evaluation_at_the_proof (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (publicHash : List Verifier.Base)
    (hp : publicHash.length = 4) (alpha : Verifier.Ext3) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).gateEvaluation
        RoutedAcceptance.routedConfig RoutedAcceptance.altProof.used.gateWitness
        (RoutedAcceptance.altProof.used.gatePreprocessed.take
          RoutedAcceptance.routedConfig.numConstants) publicHash alpha = Verifier.zero := by
  rw [DerivedAcceptance.derived_gate_evaluation_field]
  simp only []
  rw [RoutedAcceptance.alt_gate_claim_columns_are_zero.1,
    RoutedAcceptance.alt_gate_claim_columns_are_zero.2,
    RoutedAcceptance.routed_gate_evaluation_vanishes publicHash hp]
  rfl

theorem fixed_alt_gate_terminal_gate (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    Verifier.gateTerminal (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.altProof =
      (Verifier.derivedRounds (DerivedAcceptance.derivedEngine fixedHash khash P)
        RoutedAcceptance.routedConfig RoutedAcceptance.altProof).gateClaim := by
  rw [(fixed_claims_vanish_at_the_alt_proof khash P).2, DerivedAcceptance.gate_terminal_unfolds,
    DerivedAcceptance.derived_public_input_hash_field,
    fixed_alt_gate_evaluation_at_the_proof khash P _
      (PublicInputHashBinding.hash_no_pad_length RoutedAcceptance.altProof.publicInputs)]
  exact Algebra.vmul_zero _

/-- **THE HONEST NEGATIVE.**  The alt proof, whose derived transcript is now
GENUINELY DIFFERENT (`fixed_initial_transcript_separates_the_two_proofs`), is
STILL ACCEPTED.  Digest-reading challenges are not by themselves a separating
verifier: gate 7 reads the norm-inverse COLUMN, which is all zero in both proofs,
and the challenges only through `rho`; gate 8's root comparison is answered by
the fixture parse (`fixture_parse_echoes_the_context_roots`); and `Verifier.shape`
binds only `preprocessedRoot`.  Separation must come from route (a) -- a non-zero
norm-inverse column -- or from an installed WHIR parse. -/
theorem alt_proof_is_still_accepted (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile)
    (hprofile : PinnedWhirProfile.profileOk P RoutedAcceptance.routedConfig = true) :
    Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash P)
      (RoutedAcceptance.routedPin khash) 1 RoutedAcceptance.routedConfig
      RoutedAcceptance.altProof = .ok () := by
  refine NonDegenerateAcceptance.verify_of_checks _ _ _ _ _ rfl rfl
    RoutedAcceptance.routed_config_envelope ?_ (RoutedAcceptance.alt_shape_holds khash)
    (DerivedAcceptance.derived_tau_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.altProof).1
    (DerivedAcceptance.derived_tau_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.altProof).2
    (DerivedAcceptance.derived_index_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.altProof (by decide)).1
    (DerivedAcceptance.derived_index_lengths fixedHash khash P RoutedAcceptance.routedConfig
      RoutedAcceptance.altProof (by decide)).2
    (fixed_alt_log_terminal_gate khash P) (fixed_alt_whir_gate khash P)
    (fixed_alt_gate_terminal_gate khash P)
  show ExplicitEngine.explicitDeployment P DerivedAcceptance.derivedConfig
    RoutedAcceptance.routedConfig = true
  have hw : RoutedAcceptance.routedConfig.whirEncoding =
    DerivedAcceptance.derivedConfig.whirEncoding := rfl
  simp [ExplicitEngine.explicitDeployment, hw, hprofile]

theorem alt_proof_is_still_accepted_at_the_profile_witness
    (khash : Verifier.Bytes → Verifier.Root) :
    Verifier.verify (DerivedAcceptance.derivedEngine fixedHash khash
        DerivedAcceptance.derivedProfile) (RoutedAcceptance.routedPin khash) 1
      RoutedAcceptance.routedConfig RoutedAcceptance.altProof = .ok () :=
  alt_proof_is_still_accepted khash DerivedAcceptance.derivedProfile
    RoutedAcceptance.routed_profile_passes_the_canonical_check

/-- The two proofs really are distinct, and the pin really does bind only the
preprocessed root. -/
theorem alt_proof_differs_only_in_the_unbound_root :
    RoutedAcceptance.routedProof.preprocessedRoot =
        RoutedAcceptance.altProof.preprocessedRoot ∧
      RoutedAcceptance.routedProof.witnessRoot = RoutedAcceptance.altProof.witnessRoot ∧
      RoutedAcceptance.routedProof.normInverseRoot ≠
        RoutedAcceptance.altProof.normInverseRoot := by decide

/-! ## 10. The trade ledger -/

/-- Against the adopted `RoutedAcceptance`: the SAME engine, the SAME
configuration, the SAME proof, the SAME routed-wire count. -/
theorem same_instance_as_the_adopted_routed_acceptance (khash : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) :
    (DerivedAcceptance.derivedEngine fixedHash khash P).normEvaluation = Norm.normEvaluation ∧
      (DerivedAcceptance.derivedEngine fixedHash khash P).foldClaim = Connections.packedFold ∧
      (DerivedAcceptance.derivedEngine fixedHash khash P).eqEvaluation = Norm.eqEvaluation ∧
      (DerivedAcceptance.derivedEngine fixedHash khash P).initialObservation =
        InstalledInitialTranscript.concreteInitialObservation fixedHash ∧
      (DerivedAcceptance.derivedEngine fixedHash khash P).commitRound =
        InstalledRoundCommit.concreteCommitRound fixedHash ∧
      (DerivedAcceptance.derivedEngine fixedHash khash P).sampleIndices =
        InstalledIndexSampler.concreteSampleIndices fixedHash :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem routed_config_sits_at_the_routed_ceiling :
    RoutedAcceptance.routedConfig.numRouted = 80 := rfl

/-- The adopted `RoutedAcceptance` ledger against
`NonDegenerateAcceptance.maximalConfig` carries over verbatim, because the
configuration is literally theirs. -/
theorem config_ties_the_adopted_maximal_on_six_fields :
    RoutedAcceptance.routedConfig.numRouted =
        NonDegenerateAcceptance.maximalConfig.numRouted ∧
      RoutedAcceptance.routedConfig.numWires = NonDegenerateAcceptance.maximalConfig.numWires ∧
      RoutedAcceptance.routedConfig.numConstants =
        NonDegenerateAcceptance.maximalConfig.numConstants ∧
      RoutedAcceptance.routedConfig.degreeBits =
        NonDegenerateAcceptance.maximalConfig.degreeBits ∧
      RoutedAcceptance.routedConfig.indexBits =
        NonDegenerateAcceptance.maximalConfig.indexBits ∧
      RoutedAcceptance.routedConfig.quotientDegree =
        NonDegenerateAcceptance.maximalConfig.quotientDegree :=
  RoutedAcceptance.routed_config_ties_the_adopted_maximal_on_six_fields

/-- At the public-input configuration only the three stand-in-decoder fields sit
below the adopted maximal instance. -/
theorem public_config_ties_the_adopted_maximal_on_seven_fields :
    RoutedAcceptance.routedPublicConfig.numRouted =
        NonDegenerateAcceptance.maximalConfig.numRouted ∧
      RoutedAcceptance.routedPublicConfig.numWires =
        NonDegenerateAcceptance.maximalConfig.numWires ∧
      RoutedAcceptance.routedPublicConfig.numConstants =
        NonDegenerateAcceptance.maximalConfig.numConstants ∧
      RoutedAcceptance.routedPublicConfig.degreeBits =
        NonDegenerateAcceptance.maximalConfig.degreeBits ∧
      RoutedAcceptance.routedPublicConfig.indexBits =
        NonDegenerateAcceptance.maximalConfig.indexBits ∧
      RoutedAcceptance.routedPublicConfig.quotientDegree =
        NonDegenerateAcceptance.maximalConfig.quotientDegree ∧
      RoutedAcceptance.routedPublicConfig.numPublicInputs =
        NonDegenerateAcceptance.maximalConfig.numPublicInputs :=
  RoutedAcceptance.routed_public_config_ties_the_adopted_maximal_on_seven_fields

theorem public_config_is_below_the_adopted_maximal_on_three_fields :
    RoutedAcceptance.routedPublicConfig.numSelectors <
        NonDegenerateAcceptance.maximalConfig.numSelectors ∧
      RoutedAcceptance.routedPublicConfig.numGateConstraints <
        NonDegenerateAcceptance.maximalConfig.numGateConstraints ∧
      RoutedAcceptance.routedPublicConfig.gateRows <
        NonDegenerateAcceptance.maximalConfig.gateRows :=
  RoutedAcceptance.routed_public_config_is_below_the_adopted_maximal_on_three_fields

theorem config_is_below_the_adopted_maximal_on_four_fields :
    RoutedAcceptance.routedConfig.numPublicInputs <
        NonDegenerateAcceptance.maximalConfig.numPublicInputs ∧
      RoutedAcceptance.routedConfig.numSelectors <
        NonDegenerateAcceptance.maximalConfig.numSelectors ∧
      RoutedAcceptance.routedConfig.numGateConstraints <
        NonDegenerateAcceptance.maximalConfig.numGateConstraints ∧
      RoutedAcceptance.routedConfig.gateRows <
        NonDegenerateAcceptance.maximalConfig.gateRows :=
  RoutedAcceptance.routed_config_is_below_the_adopted_maximal_on_four_fields

end Audit.Wire3.DigestRoutedAcceptance
