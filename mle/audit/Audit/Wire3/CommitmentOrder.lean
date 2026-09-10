import Audit.Wire3.AlphaZeroCheck
import Audit.Wire3.GateRejectionPower

/-!
# Commitment order: the DETERMINISTIC half of the Fiat--Shamir adaptivity
argument for the gate challenges (wire v3)

## The gap this module addresses, and the half it does NOT close

The adopted zero-check modules `Audit.Wire3.ZeroCheckSemantics`,
`Audit.Wire3.AlphaZeroCheck` and `Audit.Wire3.GateRejectionPower` all carry a
"good challenge" hypothesis (`hgood`) whose bad set is INDEXED BY THE PROVER'S
OWN TABLES:

    tupleOf tau ∉ ZeroCheckSemantics.zeroCheckBadSet n (gateValue c gates publicHash alpha t)
    alpha       ∉ AlphaZeroCheck.alphaBadSet coeffs

`ZeroCheckSemantics`' own header states the obligation: "Before `hgood` may be
read as a probability event, a Fiat--Shamir argument must establish that those
tables are fixed by transcript material PRECEDING the gate-tau block."

That argument has two halves.

* **(A) DETERMINISTIC.** The tables are fixed by transcript material that
  PRECEDES the challenge squeezes, so an adaptive prover cannot choose tables
  after seeing the challenge. THIS MODULE PROVES (A) for the gate lane, MODULO
  the visible `CommittedTables` extraction join, and with the gate list, gate
  configuration and public-input hash HELD FIXED as parameters (their own
  provenance from the config/VK digest frames is not proved here).
* **(B) PROBABILISTIC.** The squeezes are uniform and independent of that
  preceding material. THIS MODULE DOES NOT PROVE (B), AND CANNOT.

**HALF (B) IS A HASH ASSUMPTION THIS AUDIT DOES NOT AND CANNOT PROVE.**
`Transcript.Hash` is an ARBITRARY deterministic function `Bytes → Digest`.
For a fixed such function the gate challenge is a FUNCTION of the transcript
prefix, so "uniform and independent given the prefix" is not even expressible
here: it is a statement about a DISTRIBUTION over hash functions, or about a
random-oracle idealisation, and this model has neither. Section 5 makes the
point constructively rather than in prose: `SeparatesPrefixes` is the strictly
WEAKER, purely deterministic shadow of (B) ("distinct prefixes give distinct
challenges"), and `separation_fails_for_a_deterministic_hash` PROVES that even
that shadow is false for a general deterministic `hash` — the constant hash
gives one and the same gate alpha to two statements whose absorbed prefixes
differ in the norm-inverse root frame. ONLY WITH (B) does `hgood` become a
probability event; without it, `hgood` remains a hypothesis about the particular
run, exactly as `GateRejectionPower`'s header says.

Nothing below assumes injectivity, collision resistance, uniformity,
unpredictability or a random-oracle property of `hash`. Every theorem holds for
EVERY deterministic `hash`. Section 4's non-malleability results are stated as
"…or a concrete `TranscriptCollision hash`", i.e. they EXHIBIT a colliding pair
of actual byte strings rather than assuming none exists.

## The exact frame order, as verified against the sources

Sources (worktree `intmax-plonky2-lean-wire3`):
`mle/contracts/src/MleVerifierV2.sol` 394-455 (`_deriveInitialTranscript`),
`mle/contracts/src/TranscriptV2.sol` (`create`, `domainSeparate`, `absorbBytes`,
`bindWhirIdentifiers`, `squeezeExt3`), `mle/src/verifier_v2.rs` 232-275,
`mle/src/prover_v2.rs` 90-142 (`absorb_v2_statement_and_base_roots`).

`gateChallengeFrames c s` is the EXACT list of frames absorbed before the gate
challenges, in source order — twenty-two of them, the adopted
`OuterInitial.baseMessages` (sixteen) followed by six more:

    0  domain  "plonky2-mle-outer-v3"          (TranscriptV2.create)
    1  domain  "circuit-statement-v3"
    2  fields  circuitDigest
    3  fields  publicInputs                    (RAW public inputs, not their hash)
    4  domain  "mle-whir-packed-schema-v3"
    5  bytes   metadata (fifteen u64 words, 120 bytes)
    6  domain  "circuit-config-digest-v3"
    7  bytes   circuitConfigDigest             (fixed configuration)
    8  domain  "whir-protocol-id-v3"
    9  bytes   whirProtocolId                  (fixed configuration)
    10 domain  "whir-session-id-v3"
    11 bytes   whirSessionId                   (fixed configuration)
    12 domain  "pcs-group-preprocessed-v3"
    13 bytes   PREPROCESSED ROOT
    14 domain  "pcs-group-witness-v3"
    15 bytes   WITNESS ROOT
    16 domain  "public-input-aggregation-challenge-v3"   [then eta,   3 squeezes]
    17 domain  "norm-denominator-challenges-v3"          [then beta, gamma, 6]
    18 domain  "pcs-group-norm-inverse-v3"
    19 bytes   NORM-INVERSE ROOT
    20 domain  "public-input-mix-challenge-v3"           [then xi,    3 squeezes]
    21 domain  "outer-relation-challenges-v3"

After frame 21 NO further frame is absorbed before the gate challenges. The
absorb at each frame RESETS the counter to `0` (`Transcript.absorb`), and a
squeeze changes only the counter, never the digest, so every challenge from
`lambda` onwards is squeezed from the digest of frame 21 at these counters:

    lambda 0,   rho 3,   kappa 6,
    log tau  i  at  9 + 3i          (i < degreeBits)
    GATE ALPHA  at  9 + 3·degreeBits
    GATE TAU i  at  12 + 3·degreeBits + 3i   (i < degreeBits)

These are the counters the adopted `OuterInitial.gate_alpha_follows_log_tau`,
`OuterInitial.gate_tau_follows_gate_alpha` and
`TranscriptProvenance.derived_columns_at_source_counters` already pin. This
module does NOT re-model the transcript: `gateChallengeFrames` is proved EQUAL
to the adopted `OuterInitial.relationState` (`prefix_state_is_relation_state`),
and every challenge fact is routed through the adopted theorems.

## What is proved

1. **PREFIX STRUCTURE** (section 1). `prefix_state_is_relation_state`: the state
   at which the gate challenges are squeezed is the twenty-two-frame fold
   `absorbMessages startState (gateChallengeFrames c s)`, i.e. a deterministic
   function of a PREFIX of absorbed frames. `three_roots_inside_the_prefix` puts
   the preprocessed, witness and norm-inverse roots at prefix positions 13, 15
   and 19. `only_two_domain_separators_after_the_last_root` shows the ONLY
   frames absorbed after the last root frame are the two fixed domain
   separators `"public-input-mix-challenge-v3"` and
   `"outer-relation-challenges-v3"`, and
   `frames_after_the_last_root_are_statement_independent` shows those two carry
   no configuration- or statement-dependent bytes at all.
   `gate_challenges_factor_through_prefix` is the factorisation: the pair
   (gate alpha, gate tau) is `gateChallengesAt hash (prefixDigest …) degreeBits`,
   a function of the prefix DIGEST and the configured width alone.
2. **DEPENDENCY** (section 2). `gateBadSet` is, verbatim, the set the adopted
   `hgood` names. `gate_bad_set_ignores_the_eq_column` (the eq column is not an
   input of the bad set at all — via the adopted
   `GateRejectionPower.gate_value_ignores_eq`),
   `gate_bad_set_depends_only_on_wires_and_constants`, and
   `gate_eq_table_is_a_function_of_tau_alone` (the eq table is `eqTable tau`,
   the adopted `EqTableProvenance.GateEqProvenance`). On the alpha side,
   `alpha_bad_set_depends_only_on_row_values` and
   `gate_alpha_precedes_every_gate_tau_coordinate`.
   `gate_bad_set_determined_by_the_roots` then says: everything the gate bad set
   depends on OTHER THAN tau is determined by the two table roots plus the fixed
   configuration — hence by material absorbed BEFORE the squeeze.
3. **THE EXTRACTION JOIN STAYS A VISIBLE NAMED HYPOTHESIS.** The step from
   "root" to "table" is `CommittedTables`, an explicit hypothesis of every
   theorem that needs it. `Audit.Wire3.OpeningBinding` proves BINDING, not
   EXTRACTION ("BINDING IS NOT EXTRACTION", its header;
   `opening_relation_ignores_the_commitment` shows the model never connects a
   `Verifier.Root` to a column list). Nothing here discharges it, and nothing
   here weakens it. What IS proved unconditionally is the ROOT-level statement:
   the three roots are absorbed strictly before the squeeze, and the prefix
   digest binds them up to a concrete hash collision.
4. **NON-MALLEABILITY OF ORDER** (section 4). `prefix_digest_binds_the_frames`:
   two runs with the same prefix digest have the SAME twenty-two frames, or a
   concrete `TranscriptCollision hash` is exhibited. Hence
   `prefix_digest_binds_the_three_roots` and, under `CommittedTables`,
   `changing_the_committed_tables_changes_the_prefix_or_collides`: a prover
   cannot hold the prefix digest fixed while changing the committed wire or
   constant tables unless the hash chain collides. Collision resistance is NOT
   assumed: the conclusion PRODUCES the colliding pair.
5. **COMPOSED DETERMINISTIC ADAPTIVITY** (section 6),
   `deterministic_adaptivity`, and **the fixture** (section 7).

## Boundaries (explicitly NOT proved)

* **HALF (B).** As above. `SeparatesPrefixes` is refuted for a concrete
  deterministic hash. No probability, unpredictability, uniformity,
  independence, random-oracle or Fiat--Shamir-soundness statement is made.
  In particular NOTHING here says that a prover who changes the tables gets a
  DIFFERENT CHALLENGE; only that it changes the absorbed PREFIX, and that
  holding the prefix DIGEST fixed costs a collision. Two different prefix
  digests may still squeeze to the same challenge, and excluding that is (B).
* **THE EXTRACTION JOIN.** `CommittedTables` is assumed wherever used; see 3.
* **NO COLLISION RESISTANCE.** `TranscriptCollision` is a conclusion, never a
  hypothesis. `separation_fails_for_a_deterministic_hash` uses a hash that does
  collide, and that is the point.
* **THE ROUND PHASE.** Only the INITIAL derivation (`OuterInitial.derive`) is
  analysed. The coupled rounds (`OuterAdapter.runChecked`,
  `OuterClaimChain`) and the claim/index sampling are not.
* No Rust/Solidity refinement, gas, WHIR profile, PCS or Merkle claim; no
  config/VK digest provenance; no public-input hash computation.
-/

namespace Audit.Wire3.CommitmentOrder

open Audit.Wire3 GoldilocksExt3Field

abbrev Hash := Transcript.Hash

/-! ## 0. The collision shape

The adopted collision shape is `WhirRowBinding.HashCollision`
(`∃ a b : Bytes, a ≠ b ∧ hash a = hash b`). It is stated for
`Spongefish.Hash = Merkle.Hash`, whose digest is the SUBTYPE
`{bytes // bytes.length = 32}`, while the outer transcript's `Transcript.Hash`
lands in the STRUCTURE `Transcript.Digest`. The two are different types, so the
adopted predicate cannot be applied verbatim; `TranscriptCollision` is the same
shape transported to the outer hash. It is only ever a CONCLUSION below: no
theorem assumes its negation. -/
def TranscriptCollision (hash : Hash) : Prop :=
  ∃ a b : Transcript.Bytes, a ≠ b ∧ hash a = hash b

theorem transcript_collision_exhibits_actual_hash_inputs (hash : Hash)
    (h : TranscriptCollision hash) : ∃ a b : Transcript.Bytes, a ≠ b ∧ hash a = hash b := h

/-- The adopted `Transcript.frame_tag_and_payload_are_unambiguous` for a FIXED
state, strengthened to different states: the framing is unambiguous in the state
digest too, because `digestBytes` occupies a fixed 32-byte slot. -/
theorem frame_injective (d e : Transcript.Digest) (t u : Transcript.Byte)
    (p q : Transcript.Bytes) (h : Transcript.frame d t p = Transcript.frame e u q) :
    d = e ∧ t = u ∧ p = q := by
  simp only [Transcript.frame, List.append_assoc] at h
  have h1 := List.append_cancel_left h
  have hlen : (Transcript.digestBytes d).length = (Transcript.digestBytes e).length := by
    simp only [Transcript.digestBytes, d.length_eq, e.length_eq]
  obtain ⟨hd, h2⟩ := List.append_inj h1 hlen
  have hde : d = e := by
    cases d
    cases e
    simpa only [Transcript.Digest.mk.injEq] using hd
  simp only [List.singleton_append, List.cons.injEq] at h2
  obtain ⟨htu, h3⟩ := h2
  obtain ⟨_, hpq⟩ := List.append_inj h3 (by simp only [Transcript.le_length])
  exact ⟨hde, htu, hpq⟩

/-! ## 1. Prefix structure -/

/-- THE ABSORBED PREFIX. The exact twenty-two frames the source absorbs before
the gate challenges, in source order: the adopted sixteen
`OuterInitial.baseMessages` (which end with the preprocessed and witness root
frames) then the aggregation and denominator domain separators, the
norm-inverse root frame, and the mix and relation domain separators. See the
header for the full table with positions. -/
def gateChallengeFrames (c : Verifier.Config) (s : Verifier.Statement) :
    List OuterInitial.Message :=
  OuterInitial.baseMessages c s ++
    [OuterInitial.domainMessage "public-input-aggregation-challenge-v3",
     OuterInitial.domainMessage "norm-denominator-challenges-v3",
     OuterInitial.domainMessage "pcs-group-norm-inverse-v3",
     OuterInitial.byteMessage (OuterInitial.rootBytes s.normInverseRoot),
     OuterInitial.domainMessage "public-input-mix-challenge-v3",
     OuterInitial.domainMessage "outer-relation-challenges-v3"]

/-- The state the gate challenges are squeezed from, as a fold of the prefix. -/
def prefixState (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Transcript.State :=
  OuterInitial.absorbMessages hash OuterInitial.startState (gateChallengeFrames c s)

def prefixDigest (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) : Transcript.Digest :=
  (prefixState hash c s).digest

theorem prefix_frame_count (c : Verifier.Config) (s : Verifier.Statement) :
    (gateChallengeFrames c s).length = 22 := rfl

/-- (1) THE PREFIX IS THE ADOPTED STATE. No re-modelling: the fold of the
twenty-two frames IS `OuterInitial.relationState`, the state whose digest the
adopted counter theorems already use. -/
theorem prefix_state_is_relation_state (hash : Hash) (c : Verifier.Config)
    (s : Verifier.Statement) : prefixState hash c s = OuterInitial.relationState hash c s := by
  rw [prefixState, gateChallengeFrames, OuterInitial.absorbMessages, List.foldl_append]
  rfl

/-- Every absorb resets the counter, so the prefix state's counter is `0` and
the challenge counters below are counted from the prefix, not from the run. -/
theorem prefix_state_counter_zero (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (prefixState hash c s).counter = 0 := by
  rw [prefix_state_is_relation_state]
  rfl

theorem frames_get_preprocessed_root (c : Verifier.Config) (s : Verifier.Statement) :
    (gateChallengeFrames c s).get? 13 =
      some (OuterInitial.byteMessage (OuterInitial.rootBytes s.preprocessedRoot)) := rfl

theorem frames_get_witness_root (c : Verifier.Config) (s : Verifier.Statement) :
    (gateChallengeFrames c s).get? 15 =
      some (OuterInitial.byteMessage (OuterInitial.rootBytes s.witnessRoot)) := rfl

theorem frames_get_norm_inverse_root (c : Verifier.Config) (s : Verifier.Statement) :
    (gateChallengeFrames c s).get? 19 =
      some (OuterInitial.byteMessage (OuterInitial.rootBytes s.normInverseRoot)) := rfl

/-- (1) ALL THREE ROOTS ARE INSIDE THE PREFIX, at positions 13, 15 and 19 of
twenty-two. -/
theorem three_roots_inside_the_prefix (c : Verifier.Config) (s : Verifier.Statement) :
    (gateChallengeFrames c s).get? 13 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes s.preprocessedRoot)) ∧
    (gateChallengeFrames c s).get? 15 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes s.witnessRoot)) ∧
    (gateChallengeFrames c s).get? 19 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes s.normInverseRoot)) ∧
    (gateChallengeFrames c s).length = 22 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- (1) NOTHING IS ABSORBED BETWEEN THE LAST ROOT FRAME AND THE SQUEEZES EXCEPT
THE TWO DOMAIN SEPARATORS THE ADOPTED DERIVATION LISTS: after the norm-inverse
root frame at position 19 come exactly `"public-input-mix-challenge-v3"` and
`"outer-relation-challenges-v3"`, and then the twenty-two-frame prefix ends. -/
theorem only_two_domain_separators_after_the_last_root (c : Verifier.Config)
    (s : Verifier.Statement) :
    (gateChallengeFrames c s).drop 20 =
      [OuterInitial.domainMessage "public-input-mix-challenge-v3",
       OuterInitial.domainMessage "outer-relation-challenges-v3"] := rfl

/-- (1) …and those two frames carry NO configuration- or statement-dependent
bytes: they are literally the same two frames for every config and statement,
so no prover-supplied material intervenes between the last root and the gate
challenges. -/
theorem frames_after_the_last_root_are_statement_independent
    (c c2 : Verifier.Config) (s s2 : Verifier.Statement) :
    (gateChallengeFrames c s).drop 20 = (gateChallengeFrames c2 s2).drop 20 := by
  rw [only_two_domain_separators_after_the_last_root,
    only_two_domain_separators_after_the_last_root]

/-- Both remaining frames are domain separators (tag `1`), not payload absorbs. -/
theorem frames_after_the_last_root_are_domain_tags (c : Verifier.Config)
    (s : Verifier.Statement) :
    ((gateChallengeFrames c s).drop 20).map OuterInitial.Message.tag = [1, 1] := by
  rw [only_two_domain_separators_after_the_last_root]
  rfl

/-- `OuterInitial.drawMany` reads only the state's digest and counter. -/
theorem draw_many_congr (hash : Hash) (n : Nat) (s t : Transcript.State)
    (hd : s.digest = t.digest) (hc : s.counter = t.counter) :
    OuterInitial.drawMany hash n s = OuterInitial.drawMany hash n t := by
  obtain ⟨sd, sc⟩ := s
  obtain ⟨td, tc⟩ := t
  simp only at hd hc
  subst hd
  subst hc
  rfl

/-- THE GATE CHALLENGES AS A FUNCTION OF THE PREFIX DIGEST ALONE. Gate alpha is
the three reduced digests at counters `9+3d, 9+3d+1, 9+3d+2`; gate tau
coordinate `i` is the block at `12+3d+3i`. -/
def gateChallengesAt (hash : Hash) (d : Transcript.Digest) (degreeBits : Nat) :
    Verifier.Ext3 × List Verifier.Ext3 :=
  (OuterInitial.ext3At hash d (9 + 3 * degreeBits),
   (OuterInitial.drawMany hash degreeBits ⟨d, 12 + 3 * degreeBits⟩).1)

theorem gate_alpha_from_prefix (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive hash c s).gateAlpha
      = OuterInitial.ext3At hash (prefixDigest hash c s) (9 + 3 * c.degreeBits) := by
  rw [prefixDigest, prefix_state_is_relation_state]
  exact OuterInitial.gate_alpha_follows_log_tau hash c s

theorem gate_tau_from_prefix (hash : Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive hash c s).gateTau
      = (OuterInitial.drawMany hash c.degreeBits
          ⟨prefixDigest hash c s, 12 + 3 * c.degreeBits⟩).1 := by
  have hd : (OuterInitial.draw hash (OuterInitial.drawMany hash c.degreeBits
        (OuterInitial.relations hash c s).afterKappa).2).2.digest = prefixDigest hash c s := by
    rw [prefixDigest, prefix_state_is_relation_state, OuterInitial.draw_digest,
      (OuterInitial.draw_many_shape hash c.degreeBits _).2.1]
    rfl
  have hc : (OuterInitial.draw hash (OuterInitial.drawMany hash c.degreeBits
        (OuterInitial.relations hash c s).afterKappa).2).2.counter = 12 + 3 * c.degreeBits := by
    rw [OuterInitial.draw_counter, (OuterInitial.draw_many_shape hash c.degreeBits _).2.2,
      OuterInitial.relation_counter]
    omega
  change (OuterInitial.drawMany hash c.degreeBits (OuterInitial.draw hash
    (OuterInitial.drawMany hash c.degreeBits (OuterInitial.relations hash c s).afterKappa).2).2).1 = _
  rw [draw_many_congr hash c.degreeBits _ ⟨prefixDigest hash c s, 12 + 3 * c.degreeBits⟩ hd hc]

/-- (1) THE FACTORISATION. The pair (gate alpha, gate tau) the source derives is
`gateChallengesAt` applied to the DIGEST OF THE TWENTY-TWO-FRAME PREFIX and the
configured width. Nothing absorbed after the prefix, and no proof field other
than the statement absorbed inside it, can influence them. -/
theorem gate_challenges_factor_through_prefix (hash : Hash) (c : Verifier.Config)
    (s : Verifier.Statement) :
    ((OuterInitial.derive hash c s).gateAlpha, (OuterInitial.derive hash c s).gateTau)
      = gateChallengesAt hash (prefixDigest hash c s) c.degreeBits := by
  rw [gateChallengesAt, gate_alpha_from_prefix, gate_tau_from_prefix]

/-- (1) Equal prefix digests and equal configured widths give equal gate
challenges — the "deterministic function of the prefix" statement. -/
theorem equal_prefix_gives_equal_gate_challenges (hash : Hash) (c c2 : Verifier.Config)
    (s s2 : Verifier.Statement) (hw : c.degreeBits = c2.degreeBits)
    (h : prefixDigest hash c s = prefixDigest hash c2 s2) :
    (OuterInitial.derive hash c s).gateAlpha = (OuterInitial.derive hash c2 s2).gateAlpha ∧
    (OuterInitial.derive hash c s).gateTau = (OuterInitial.derive hash c2 s2).gateTau := by
  have hp : ((OuterInitial.derive hash c s).gateAlpha, (OuterInitial.derive hash c s).gateTau)
      = ((OuterInitial.derive hash c2 s2).gateAlpha, (OuterInitial.derive hash c2 s2).gateTau) := by
    rw [gate_challenges_factor_through_prefix, gate_challenges_factor_through_prefix, h, hw]
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- The counter facts, restated from the adopted
`TranscriptProvenance.derived_columns_at_source_counters`: gate alpha at
`9+3·degreeBits`, gate tau coordinate `i` at `12+3·degreeBits+3i`, both from the
prefix digest. -/
theorem gate_challenge_counters (hash : Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (i : Nat) (hi : i < c.degreeBits) :
    (TranscriptProvenance.derived hash c p).gateAlpha =
        OuterInitial.ext3At hash (prefixDigest hash c (Verifier.statement p))
          (9 + 3 * c.degreeBits) ∧
    (TranscriptProvenance.derived hash c p).gateTau.get? i =
        some (OuterInitial.ext3At hash (prefixDigest hash c (Verifier.statement p))
          (12 + 3 * c.degreeBits + 3 * i)) := by
  have h := TranscriptProvenance.derived_columns_at_source_counters hash c p i hi
  rw [prefixDigest, prefix_state_is_relation_state]
  exact ⟨h.2.1, h.2.2⟩

/-! ## 2. What the gate bad sets depend on -/

open ZeroCheckSemantics in
/-- THE GATE BAD SET, verbatim the set the adopted `hgood` names. With
`n := (TranscriptProvenance.gateTauColumn hash cfg p).length` this is exactly
the `zeroCheckBadSet` of `ZeroCheckSemantics.gate_rows_vanish_of_derived_tau`
and of `GateRejectionPower.strong_gate_rows_vanish`. -/
def gateBadSet (gc : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (t : GateSuffixPolynomial.Tables) (n : Nat) : Finset (Tuple n) :=
  zeroCheckBadSet n (gateValue gc gates publicHash alpha t)

/-- The index width of the bad set in `hgood` is the configured `degreeBits`
(the adopted `TranscriptProvenance.derived_column_lengths`). -/
theorem gate_bad_set_index_width (hash : Hash) (cfg : Verifier.Config) (p : Verifier.Proof) :
    (TranscriptProvenance.gateTauColumn hash cfg p).length = cfg.degreeBits :=
  (TranscriptProvenance.derived_column_lengths hash cfg p).2

/-- (2) THE EQ COLUMN IS NOT AN INPUT OF THE BAD SET AT ALL. Immediate from the
adopted `GateRejectionPower.gate_value_ignores_eq`: `gateValue` reads only the
wire and constant columns. So the "eq table is a function of tau" half of the
dependency is not merely unproblematic, it is vacuous — tau enters the bad set
only through the index type. -/
theorem gate_bad_set_ignores_the_eq_column (gc : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element)
    (t : GateSuffixPolynomial.Tables) (column : List Element) (n : Nat) :
    gateBadSet gc gates publicHash alpha (GateRejectionPower.withEq t column) n
      = gateBadSet gc gates publicHash alpha t n := rfl

/-- (2) THE BAD SET DEPENDS ON THE TABLES ONLY THROUGH THE WIRE AND CONSTANT
COLUMNS — i.e. through the committed witness and preprocessed tables. -/
theorem gate_bad_set_depends_only_on_wires_and_constants (gc : Gates.Config)
    (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base) (alpha : Element)
    (t u : GateSuffixPolynomial.Tables) (n : Nat)
    (hw : t.wires = u.wires) (hc : t.constants = u.constants) :
    gateBadSet gc gates publicHash alpha t n = gateBadSet gc gates publicHash alpha u n := by
  have h : ZeroCheckSemantics.gateValue gc gates publicHash alpha t
      = ZeroCheckSemantics.gateValue gc gates publicHash alpha u := by
    funext index
    unfold ZeroCheckSemantics.gateValue
    rw [hw, hc]
  rw [gateBadSet, gateBadSet, h]

/-- (2) THE EQ TABLE IS A FUNCTION OF TAU ALONE. The adopted
`EqTableProvenance.GateEqProvenance s tau` says `s.eq.evaluations = eqTable tau`;
`eqTable` takes nothing but `tau`, so two prover states with the same tau have
the same eq table, whatever their wires and constants are. -/
theorem gate_eq_table_is_a_function_of_tau_alone (s u : GateTerminalBinding.ProverState)
    (tau : List Element) (hs : EqTableProvenance.GateEqProvenance s tau)
    (hu : EqTableProvenance.GateEqProvenance u tau) :
    s.eq.evaluations = u.eq.evaluations ∧ s.eq.evaluations = EqTableProvenance.eqTable tau :=
  ⟨hs.1.trans hu.1.symm, hs.1⟩

/-- (2) The ALPHA bad set of `Audit.Wire3.AlphaZeroCheck` is indexed by
`slotCoefficients`, which takes the row's wire and constant values, the gates
and the public-input hash — and NEITHER alpha NOR tau. So it too is fixed by
material that precedes the alpha squeeze. -/
theorem alpha_bad_set_depends_only_on_row_values (gc : Gates.Config)
    (gates : List Gates.GateInfo) (wires constants wires2 constants2 : List Verifier.Ext3)
    (publicHash : Nat → Verifier.Base) (coeffs coeffs2 : List Element)
    (hw : wires = wires2) (hc : constants = constants2)
    (h : AlphaZeroCheck.slotCoefficients gc gates wires constants publicHash = some coeffs)
    (h2 : AlphaZeroCheck.slotCoefficients gc gates wires2 constants2 publicHash = some coeffs2) :
    AlphaZeroCheck.alphaBadSet coeffs = AlphaZeroCheck.alphaBadSet coeffs2 := by
  subst hw
  subst hc
  rw [Option.some.inj (h.symm.trans h2)]

/-- (2) THE ORDER OF THE TWO GATE CHALLENGES. Gate alpha is squeezed at counter
`9+3·degreeBits`, strictly before every gate tau coordinate
(`12+3·degreeBits+3i`), from the same prefix digest. So the alpha that indexes
the tau bad set is itself already fixed when the tau block is squeezed. -/
theorem gate_alpha_precedes_every_gate_tau_coordinate (degreeBits i : Nat) :
    9 + 3 * degreeBits < 12 + 3 * degreeBits + 3 * i := by omega

/-! ## 3. The extraction join, kept as a visible named hypothesis -/

/-- **THE OPEN EXTRACTION JOIN.** `tablesOf` is any map from the two table roots
a statement carries to a table pair; `CommittedTables tablesOf s t` says the
run's gate wire and constant columns ARE the ones this statement's preprocessed
and witness roots name.

THIS IS NOT PROVED ANYWHERE IN THE AUDIT AND IS NOT PROVED HERE.
`Audit.Wire3.OpeningBinding` proves BINDING (two accepted openings of the same
root at the same index agree, or a concrete collision is exhibited), and its own
header says "BINDING IS NOT EXTRACTION"; its
`opening_relation_ignores_the_commitment` shows the model never connects a
`Verifier.Root` to a column list, and its
`CommittedColumnsAreExtractedTables` is the residue left standing. Every
theorem below that needs the root-to-table step carries this hypothesis
explicitly. The theorems that do NOT carry it — sections 1, 2 and 4 — are the
ones stated at ROOT level, and they are unconditional. -/
structure CommittedTables (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (s : Verifier.Statement) (t : GateSuffixPolynomial.Tables) : Prop where
  wires : t.wires = (tablesOf s.preprocessedRoot s.witnessRoot).wires
  constants : t.constants = (tablesOf s.preprocessedRoot s.witnessRoot).constants

/-- (2)+(3) EVERYTHING THE GATE BAD SET DEPENDS ON OTHER THAN TAU IS DETERMINED
BY THE TWO TABLE ROOTS PLUS THE FIXED CONFIGURATION. Under the extraction join,
two runs with the same preprocessed and witness roots, the same configuration
(`gc`, `gates`), the same public-input hash and the same alpha have literally
the same bad set.  The roots are absorbed at prefix positions 13/15 and alpha
is squeezed at counter `9+3·degreeBits`, both BEFORE the gate-tau block.  The
configuration (`gc`, `gates`) and the public-input hash are HELD FIXED as
parameters of this theorem; nothing here proves they are functions of the
config-digest / public-input frames (positions 3, 5/7/9/11) — that provenance
sits behind the config/VK digest, which this module excludes. -/
theorem gate_bad_set_determined_by_the_roots
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gc : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (n : Nat) (s s2 : Verifier.Statement)
    (t u : GateSuffixPolynomial.Tables)
    (ht : CommittedTables tablesOf s t) (hu : CommittedTables tablesOf s2 u)
    (hpre : s.preprocessedRoot = s2.preprocessedRoot)
    (hwit : s.witnessRoot = s2.witnessRoot) :
    gateBadSet gc gates publicHash alpha t n = gateBadSet gc gates publicHash alpha u n := by
  refine gate_bad_set_depends_only_on_wires_and_constants gc gates publicHash alpha t u n ?_ ?_
  · rw [ht.wires, hu.wires, hpre, hwit]
  · rw [ht.constants, hu.constants, hpre, hwit]

/-! ## 4. Non-malleability of the absorbed order -/

/-- The hash chain is unambiguous frame by frame, or it collides: equal fold
digests over equally long frame lists force equal starting digests and equal
frame lists, unless a concrete pair of distinct byte strings with equal hash is
produced. NO collision resistance is assumed; the collision is a CONCLUSION. -/
theorem absorb_messages_bind_or_collide (hash : Hash) :
    ∀ (ms ns : List OuterInitial.Message) (s t : Transcript.State),
      ms.length = ns.length →
      (OuterInitial.absorbMessages hash s ms).digest
          = (OuterInitial.absorbMessages hash t ns).digest →
      (s.digest = t.digest ∧ ms = ns) ∨ TranscriptCollision hash := by
  intro ms
  induction ms with
  | nil =>
      intro ns s t hlen h
      cases ns with
      | nil => exact Or.inl ⟨h, rfl⟩
      | cons _ _ => simp only [List.length_nil, List.length_cons] at hlen
  | cons m ms ih =>
      intro ns s t hlen h
      cases ns with
      | nil => simp only [List.length_nil, List.length_cons] at hlen
      | cons n ns =>
          have hlen2 : ms.length = ns.length := by
            simp only [List.length_cons, Nat.succ.injEq] at hlen
            exact hlen
          have hstep : (OuterInitial.absorbMessages hash
                (OuterInitial.absorbMessage hash s m) ms).digest
              = (OuterInitial.absorbMessages hash
                (OuterInitial.absorbMessage hash t n) ns).digest := h
          rcases ih ns (OuterInitial.absorbMessage hash s m)
            (OuterInitial.absorbMessage hash t n) hlen2 hstep with ⟨hd, hms⟩ | hcol
          · have hh : hash (Transcript.frame s.digest m.tag m.payload)
                = hash (Transcript.frame t.digest n.tag n.payload) := hd
            by_cases hfr : Transcript.frame s.digest m.tag m.payload
                = Transcript.frame t.digest n.tag n.payload
            · obtain ⟨hdig, htag, hpay⟩ := frame_injective _ _ _ _ _ _ hfr
              have hmn : m = n := by
                obtain ⟨mt, mp⟩ := m
                obtain ⟨nt, np⟩ := n
                simp only [OuterInitial.Message.mk.injEq]
                exact ⟨htag, hpay⟩
              exact Or.inl ⟨hdig, by rw [hmn, hms]⟩
            · exact Or.inr ⟨_, _, hfr, hh⟩
          · exact Or.inr hcol

/-- (4) THE PREFIX DIGEST BINDS THE WHOLE TWENTY-TWO-FRAME PREFIX, or the hash
chain collides. -/
theorem prefix_digest_binds_the_frames (hash : Hash) (c c2 : Verifier.Config)
    (s s2 : Verifier.Statement) (h : prefixDigest hash c s = prefixDigest hash c2 s2) :
    gateChallengeFrames c s = gateChallengeFrames c2 s2 ∨ TranscriptCollision hash := by
  rcases absorb_messages_bind_or_collide hash (gateChallengeFrames c s)
    (gateChallengeFrames c2 s2) OuterInitial.startState OuterInitial.startState
    (by rw [prefix_frame_count, prefix_frame_count]) h with
    ⟨_, hf⟩ | hcol
  · exact Or.inl hf
  · exact Or.inr hcol

theorem root_of_equal_byte_messages (r q : Verifier.Root)
    (h : (some (OuterInitial.byteMessage (OuterInitial.rootBytes r)) : Option OuterInitial.Message)
        = some (OuterInitial.byteMessage (OuterInitial.rootBytes q))) : r = q :=
  OuterInitial.root_bytes_injective r q
    (congrArg OuterInitial.Message.payload (Option.some.inj h))

/-- (4) THE PREFIX DIGEST BINDS ALL THREE ROOTS, or the hash chain collides. -/
theorem prefix_digest_binds_the_three_roots (hash : Hash) (c c2 : Verifier.Config)
    (s s2 : Verifier.Statement) (h : prefixDigest hash c s = prefixDigest hash c2 s2) :
    (s.preprocessedRoot = s2.preprocessedRoot ∧ s.witnessRoot = s2.witnessRoot ∧
      s.normInverseRoot = s2.normInverseRoot) ∨ TranscriptCollision hash := by
  rcases prefix_digest_binds_the_frames hash c c2 s s2 h with hf | hcol
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · refine root_of_equal_byte_messages _ _ ?_
      rw [← frames_get_preprocessed_root c s, ← frames_get_preprocessed_root c2 s2, hf]
    · refine root_of_equal_byte_messages _ _ ?_
      rw [← frames_get_witness_root c s, ← frames_get_witness_root c2 s2, hf]
    · refine root_of_equal_byte_messages _ _ ?_
      rw [← frames_get_norm_inverse_root c s, ← frames_get_norm_inverse_root c2 s2, hf]
  · exact Or.inr hcol

/-- (4) CONTRAPOSITIVE: a prover who changes any of the three roots CANNOT keep
the absorbed prefix digest, unless the hash chain collides. -/
theorem distinct_roots_force_a_distinct_prefix_or_a_collision (hash : Hash)
    (c c2 : Verifier.Config) (s s2 : Verifier.Statement)
    (hne : s.preprocessedRoot ≠ s2.preprocessedRoot ∨ s.witnessRoot ≠ s2.witnessRoot ∨
      s.normInverseRoot ≠ s2.normInverseRoot)
    (h : prefixDigest hash c s = prefixDigest hash c2 s2) : TranscriptCollision hash := by
  rcases prefix_digest_binds_the_three_roots hash c c2 s s2 h with ⟨h1, h2, h3⟩ | hcol
  · rcases hne with hn | hn | hn
    · exact absurd h1 hn
    · exact absurd h2 hn
    · exact absurd h3 hn
  · exact hcol

/-- (4) THE NON-MALLEABILITY STATEMENT, under the extraction join: a prover
cannot hold the absorbed prefix digest — hence, by
`equal_prefix_gives_equal_gate_challenges`, the gate challenges it determines —
while changing the committed wire or constant tables, unless the hash chain
collides. The collision is EXHIBITED, not assumed away.

WHAT THIS DOES NOT SAY: it does not say that changing the tables changes the
CHALLENGE. Distinct prefix digests may still squeeze to the same challenge; ruling
that out is half (B), and section 5 shows it is false for a general
deterministic hash. -/
theorem changing_the_committed_tables_changes_the_prefix_or_collides (hash : Hash)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (c c2 : Verifier.Config) (s s2 : Verifier.Statement)
    (t u : GateSuffixPolynomial.Tables)
    (ht : CommittedTables tablesOf s t) (hu : CommittedTables tablesOf s2 u)
    (hne : t.wires ≠ u.wires ∨ t.constants ≠ u.constants)
    (h : prefixDigest hash c s = prefixDigest hash c2 s2) : TranscriptCollision hash := by
  rcases prefix_digest_binds_the_three_roots hash c c2 s s2 h with ⟨h1, h2, _⟩ | hcol
  · exfalso
    rcases hne with hn | hn
    · exact hn (by rw [ht.wires, hu.wires, h1, h2])
    · exact hn (by rw [ht.constants, hu.constants, h1, h2])
  · exact hcol

/-! ## 5. HALF (B): what is NOT proved, proved to be missing

`SeparatesPrefixes` is the strictly WEAKER, purely deterministic shadow of half
(B): merely that distinct absorbed prefixes give distinct gate alphas. It says
nothing about uniformity or independence. `separation_fails_for_a_deterministic_hash`
shows that even this shadow is FALSE for a general deterministic `hash`, so no
strengthening of section 4 can supply (B): (B) is a hash assumption, and this
audit does not and cannot prove it. -/

def SeparatesPrefixes (hash : Hash) : Prop :=
  ∀ (c c2 : Verifier.Config) (s s2 : Verifier.Statement),
    gateChallengeFrames c s ≠ gateChallengeFrames c2 s2 →
    (OuterInitial.derive hash c s).gateAlpha ≠ (OuterInitial.derive hash c2 s2).gateAlpha

/-- A deterministic hash, as admissible as any other in this model. -/
def constantHash : Hash := fun _ => OuterInitial.zeroDigest

theorem constant_hash_prefix_digest (c : Verifier.Config) (s : Verifier.Statement) :
    prefixDigest constantHash c s = OuterInitial.zeroDigest := rfl

/-- Under the constant hash the whole prefix is forgotten: every statement gets
the same gate alpha and the same gate tau. -/
theorem constant_hash_collapses_the_gate_challenges (c : Verifier.Config)
    (s s2 : Verifier.Statement) :
    (OuterInitial.derive constantHash c s).gateAlpha
        = (OuterInitial.derive constantHash c s2).gateAlpha ∧
    (OuterInitial.derive constantHash c s).gateTau
        = (OuterInitial.derive constantHash c s2).gateTau :=
  equal_prefix_gives_equal_gate_challenges constantHash c c s s2 rfl
    (by rw [constant_hash_prefix_digest, constant_hash_prefix_digest])

def altRoot : Verifier.Root := ⟨1, by decide⟩
def statementA : Verifier.Statement := Verifier.statement OuterAdapter.fixtureProof
def statementB : Verifier.Statement := { statementA with normInverseRoot := altRoot }

theorem statement_prefixes_differ :
    gateChallengeFrames OuterAdapter.fixtureConfig statementA
      ≠ gateChallengeFrames OuterAdapter.fixtureConfig statementB := by
  intro h
  have h19 : (some (OuterInitial.byteMessage (OuterInitial.rootBytes statementA.normInverseRoot))
      : Option OuterInitial.Message)
      = some (OuterInitial.byteMessage (OuterInitial.rootBytes statementB.normInverseRoot)) := by
    rw [← frames_get_norm_inverse_root OuterAdapter.fixtureConfig statementA,
      ← frames_get_norm_inverse_root OuterAdapter.fixtureConfig statementB, h]
  have hr := root_of_equal_byte_messages _ _ h19
  exact absurd (congrArg Fin.val hr) (by decide)

/-- **HALF (B) IS NOT AVAILABLE FROM ORDER ALONE.** Two statements whose
absorbed prefixes genuinely differ — in the norm-inverse root frame at position
19 — receive one and the same gate alpha under a deterministic hash. Section 4
therefore cannot be pushed any further: the step from "the prefix differs" to
"the challenge differs", let alone to "the challenge is uniform and independent
of the prefix", is a HASH ASSUMPTION. -/
theorem separation_fails_for_a_deterministic_hash : ¬ SeparatesPrefixes constantHash := by
  intro hsep
  exact hsep OuterAdapter.fixtureConfig OuterAdapter.fixtureConfig statementA statementB
    statement_prefixes_differ
    (constant_hash_collapses_the_gate_challenges OuterAdapter.fixtureConfig
      statementA statementB).1

/-! ## 6. The composed deterministic adaptivity result -/

/-- **THE DETERMINISTIC ADAPTIVITY THEOREM (half (A)).**

Under the adopted `TranscriptProvenance.DerivedInitial` (the engine's initial
observation IS the source's own derivation) and the visible extraction-join
hypothesis `CommittedTables`, the map (tables → gate challenge) FACTORS THROUGH
(roots → transcript prefix state → squeeze), with the tables' roots committed
strictly before the squeeze:

1. the engine's gate alpha and gate tau are `gateChallengesAt` of the prefix
   DIGEST and the configured width — a function of the prefix alone;
2. the preprocessed, witness and norm-inverse roots sit at positions 13, 15 and
   19 of that twenty-two-frame prefix;
3. the only frames after the last root are the two fixed domain separators, and
   they depend on neither configuration nor statement;
4. the bad set that `hgood` names depends on the tables only through the wire
   and constant columns those roots commit to (and not at all on the eq column,
   hence not on tau except through the index width);
5. holding the prefix digest while changing those committed columns EXHIBITS a
   concrete hash collision.

**HALF (B) IS NOT INCLUDED AND IS NOT PROVED.** That the squeeze at the counters
of (1) is uniform and independent of the prefix of (2)-(3) is a hash assumption;
`separation_fails_for_a_deterministic_hash` shows even its deterministic shadow
fails for a general `hash`. Only with (B) does `hgood` become a probability
event. -/
theorem deterministic_adaptivity (hash : Hash)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (gc : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (n : Nat) (t : GateSuffixPolynomial.Tables)
    (hderiv : TranscriptProvenance.DerivedInitial hash e c p)
    (hcom : CommittedTables tablesOf (Verifier.statement p) t) :
    ((e.initialTranscript c p).gateAlpha, (e.initialTranscript c p).gateTau)
        = gateChallengesAt hash (prefixDigest hash c (Verifier.statement p)) c.degreeBits ∧
    ((gateChallengeFrames c (Verifier.statement p)).get? 13 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.preprocessedRoot)) ∧
      (gateChallengeFrames c (Verifier.statement p)).get? 15 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.witnessRoot)) ∧
      (gateChallengeFrames c (Verifier.statement p)).get? 19 =
        some (OuterInitial.byteMessage (OuterInitial.rootBytes p.normInverseRoot)) ∧
      (gateChallengeFrames c (Verifier.statement p)).length = 22) ∧
    (gateChallengeFrames c (Verifier.statement p)).drop 20 =
        [OuterInitial.domainMessage "public-input-mix-challenge-v3",
         OuterInitial.domainMessage "outer-relation-challenges-v3"] ∧
    (∀ (u : GateSuffixPolynomial.Tables),
        CommittedTables tablesOf (Verifier.statement p) u →
        gateBadSet gc gates publicHash alpha u n = gateBadSet gc gates publicHash alpha t n) ∧
    (∀ (c2 : Verifier.Config) (s2 : Verifier.Statement) (u : GateSuffixPolynomial.Tables),
        CommittedTables tablesOf s2 u → (u.wires ≠ t.wires ∨ u.constants ≠ t.constants) →
        prefixDigest hash c2 s2 = prefixDigest hash c (Verifier.statement p) →
        TranscriptCollision hash) := by
  refine ⟨?_, three_roots_inside_the_prefix c (Verifier.statement p),
    only_two_domain_separators_after_the_last_root c (Verifier.statement p), ?_, ?_⟩
  · rw [hderiv]
    exact gate_challenges_factor_through_prefix hash c (Verifier.statement p)
  · intro u hu
    exact gate_bad_set_determined_by_the_roots tablesOf gc gates publicHash alpha n
      (Verifier.statement p) (Verifier.statement p) u t hu hcom rfl rfl
  · intro c2 s2 u hu hne hdig
    exact changing_the_committed_tables_changes_the_prefix_or_collides hash tablesOf c2 c s2
      (Verifier.statement p) u t hu hcom hne hdig

/-! ## 7. (5) The adopted `OuterAdapter` fixture

`OuterAdapter.fixtureConfig` / `fixtureProof` (one coupled round, one index
coordinate, `degreeBits = 1`) satisfies `TranscriptProvenance.DerivedInitial`
BY `rfl` for the engine `OuterInitial.withInitial hash e`, exactly as the
adopted `TranscriptProvenance.Example` records. Every statement below is
universally quantified over `hash` and over the engine whose remaining hooks
are unconstrained. The fixture is NOT a valid gate/WHIR deployment and NOT an
accepting proof; nothing here says otherwise. -/
namespace Example

open OuterAdapter

def engineOf (hash : Hash) (e : Verifier.Engine) : Verifier.Engine :=
  OuterInitial.withInitial hash e

theorem fixture_derived (hash : Hash) (e : Verifier.Engine) :
    TranscriptProvenance.DerivedInitial hash (engineOf hash e) fixtureConfig fixtureProof := rfl

/-- The fixture's prefix: twenty-two frames, the three roots at 13, 15 and 19,
and only the two fixed domain separators after the last root. -/
theorem fixture_prefix_shape :
    (gateChallengeFrames fixtureConfig (Verifier.statement fixtureProof)).length = 22 ∧
    (gateChallengeFrames fixtureConfig (Verifier.statement fixtureProof)).get? 13 =
      some (OuterInitial.byteMessage (OuterInitial.rootBytes fixtureProof.preprocessedRoot)) ∧
    (gateChallengeFrames fixtureConfig (Verifier.statement fixtureProof)).get? 15 =
      some (OuterInitial.byteMessage (OuterInitial.rootBytes fixtureProof.witnessRoot)) ∧
    (gateChallengeFrames fixtureConfig (Verifier.statement fixtureProof)).get? 19 =
      some (OuterInitial.byteMessage (OuterInitial.rootBytes fixtureProof.normInverseRoot)) ∧
    (gateChallengeFrames fixtureConfig (Verifier.statement fixtureProof)).drop 20 =
      [OuterInitial.domainMessage "public-input-mix-challenge-v3",
       OuterInitial.domainMessage "outer-relation-challenges-v3"] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `fixtureConfig.degreeBits = 1`, so gate alpha is squeezed at counter `12` and
the single gate tau coordinate at counter `15`, both from the prefix digest. -/
theorem fixture_gate_challenge_counters (hash : Hash) :
    fixtureConfig.degreeBits = 1 ∧
    (TranscriptProvenance.derived hash fixtureConfig fixtureProof).gateAlpha =
      OuterInitial.ext3At hash
        (prefixDigest hash fixtureConfig (Verifier.statement fixtureProof)) 12 ∧
    (TranscriptProvenance.derived hash fixtureConfig fixtureProof).gateTau.get? 0 =
      some (OuterInitial.ext3At hash
        (prefixDigest hash fixtureConfig (Verifier.statement fixtureProof)) 15) := by
  have h := gate_challenge_counters hash fixtureConfig fixtureProof 0 (by decide)
  exact ⟨rfl, h.1, h.2⟩

/-- The factorisation on the fixture, for the engine that satisfies
`DerivedInitial`. -/
theorem fixture_factorisation (hash : Hash) (e : Verifier.Engine) :
    (((engineOf hash e).initialTranscript fixtureConfig fixtureProof).gateAlpha,
      ((engineOf hash e).initialTranscript fixtureConfig fixtureProof).gateTau)
      = gateChallengesAt hash
          (prefixDigest hash fixtureConfig (Verifier.statement fixtureProof)) 1 := by
  rw [fixture_derived hash e]
  exact gate_challenges_factor_through_prefix hash fixtureConfig (Verifier.statement fixtureProof)

/-- The adopted checked `OuterAdapter.execute` succeeds on the fixture for every
hash, and its initial component is the very transcript this engine observes —
so the prefix analysed above is the one a whole checked run absorbs. -/
theorem fixture_execution_matches_engine (hash : Hash) (e : Verifier.Engine) :
    ∃ result, execute hash fixtureConfig fixtureProof = some result ∧
      result.initial = (engineOf hash e).initialTranscript fixtureConfig fixtureProof := by
  obtain ⟨result, hres, hini, _, _, _, _⟩ := ordinary_prefix_for_every_hash hash
  exact ⟨result, hres, hini⟩

/-- The composed theorem, instantiated on the fixture. The extraction join
`CommittedTables` is still supplied by the caller — it is not discharged here
and is not discharged anywhere in the audit. -/
theorem fixture_deterministic_adaptivity (hash : Hash) (e : Verifier.Engine)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gc : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (n : Nat) (t : GateSuffixPolynomial.Tables)
    (hcom : CommittedTables tablesOf (Verifier.statement fixtureProof) t) :
    (((engineOf hash e).initialTranscript fixtureConfig fixtureProof).gateAlpha,
        ((engineOf hash e).initialTranscript fixtureConfig fixtureProof).gateTau)
        = gateChallengesAt hash
            (prefixDigest hash fixtureConfig (Verifier.statement fixtureProof)) 1 ∧
    (∀ (u : GateSuffixPolynomial.Tables),
        CommittedTables tablesOf (Verifier.statement fixtureProof) u →
        gateBadSet gc gates publicHash alpha u n = gateBadSet gc gates publicHash alpha t n) ∧
    (∀ (c2 : Verifier.Config) (s2 : Verifier.Statement) (u : GateSuffixPolynomial.Tables),
        CommittedTables tablesOf s2 u → (u.wires ≠ t.wires ∨ u.constants ≠ t.constants) →
        prefixDigest hash c2 s2
            = prefixDigest hash fixtureConfig (Verifier.statement fixtureProof) →
        TranscriptCollision hash) := by
  obtain ⟨h1, _, _, h4, h5⟩ := deterministic_adaptivity hash tablesOf (engineOf hash e)
    fixtureConfig fixtureProof gc gates publicHash alpha n t (fixture_derived hash e) hcom
  exact ⟨h1, h4, h5⟩

end Example

end Audit.Wire3.CommitmentOrder
