import Audit.Wire3.RustCallBoundary
import Audit.Wire3.ExtractorConstruction
import Audit.Wire3.IndexPointZeroCheck
import Audit.Wire3.InstalledInitialTranscript
import Audit.Wire3.OpeningBinding
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Localized collision predicates: the adopted `∨ …Collision` disjunctions are
statement-level tautologies, and what to say instead (wire v3)

## The finding, in one paragraph

`CommitmentOrder.TranscriptCollision hash := ∃ a b : Transcript.Bytes, a ≠ b ∧
hash a = hash b` and `ExplicitEngine.KhashCollision khash := ∃ a b, a ≠ b ∧
khash a = khash b` are PIGEONHOLE TAUTOLOGIES. Their domain is a byte LIST type
(`List (Fin 256)`, resp. `List UInt8`), which is infinite; their codomain is
`Transcript.Digest` (thirty-two bytes), resp. `Verifier.Root = Fin (2 ^ 256)`,
which is finite. So they hold for EVERY function, with no hypothesis whatsoever:
`transcript_collision_is_a_tautology` and `khash_collision_is_a_tautology` below
prove exactly that, via `Finite.exists_ne_map_eq_of_infinite`. Consequently every
adopted statement of the form `P ∨ TranscriptCollision hash` or
`P ∨ KhashCollision khash` is TRUE AS A STATEMENT regardless of `P`, and every
adopted statement whose conclusion is a BARE `TranscriptCollision hash` is true
regardless of its hypotheses. Section 6 proves that for each affected
adopted result, by deriving its conclusion with all hypotheses dropped.

## Why this is NOT a soundness defect

The adopted PROOFS are constructive and do the real work: they exhibit two
SPECIFIC colliding byte strings, built from the actual absorbed material of the
two runs under comparison (`absorb_messages_bind_or_collide` produces the two
`Transcript.frame` strings at a position where the two folds disagree — its
recursion descends into the TAIL before it ever inspects the head, so the pair it
returns sits at the LAST index at which the two frames differ, not the first;
`config_digest_binds_the_configuration` produces the two `encodeConfig`
strings). Nothing in the adopted tree ASSUMES collision freedom, and nothing is
proved by invoking the tautology. What is wrong is only the STATEMENT FORM: as
written, the disjunctions carry no information, because their right disjunct is
provable outright. The audit content lives in the proof terms and cannot be read
off the theorem statements. That is an overclaim in statement form, and the
repair is to name the two inputs in the statement.

## What this module adds

Localized predicates that NAME the colliding inputs, and restatements of the
headline results with the localized disjunct in place of the tautological one.

* `FrameCollision hash d e m n` — the two absorbed frames
  `Transcript.frame d m.tag m.payload` and `Transcript.frame e n.tag n.payload`
  are distinct and have equal hash.
* `FrameFoldCollision hash s t ms ns` — there is a position `k` at which the two
  absorbed message lists have entries `m`, `n` whose frames, taken at the two
  running digests `absorbMessages hash s (ms.take k)` and
  `absorbMessages hash t (ns.take k)`, are a `FrameCollision`. This is exactly
  the witness `absorb_messages_bind_or_collide`'s proof constructs, lifted into
  the statement. The predicate quantifies `k` existentially and does not claim
  minimality: the induction recurses on the tail first and shifts the recovered
  position by one, so the `k` the proof below supplies is the LAST index at which
  the two frames differ, not the first.
* `IndexDigestClash thash s t u v` — `FrameFoldCollision` on the two eight-frame
  claim blocks `InstalledIndexSampler.claimFrames u` / `claimFrames v`.
* `RoundDigestClash thash s t i j m n` — `FrameFoldCollision` on the two
  five-frame round blocks `InstalledRoundCommit.roundFrames i m` /
  `roundFrames j n`.
* `ConfigEncodingCollision khash c c2` — the two configuration encodings
  `ExplicitEngine.encodeConfig c` and `encodeConfig c2` are distinct and have
  equal `khash`. The localized deployment statements then read: THE ACCEPTED
  CONFIGURATION IS THE DEPLOYED ONE UNLESS `khash` COLLIDES ON PRECISELY THESE
  TWO ENCODINGS.

Each localized predicate is FALSIFIABLE, which is the whole point:
`frame_fold_collision_fails_on_equal_runs` shows `FrameFoldCollision hash s s ms
ms` is false for EVERY `hash`, and `config_encoding_collision_fails_for_a_
separating_khash` gives an explicit `khash` (a two-valued lookup, `separatingKhash`)
under which `ConfigEncodingCollision khash c c2` is false even though
`KhashCollision khash` still holds. `localized_is_not_a_tautology` puts the two
halves side by side. `localized_implies_global` shows nothing is lost: each
localized predicate implies the adopted tautological one, so every restatement
below is strictly STRONGER than the adopted theorem it mirrors
(`localized_recovers_the_adopted_frame_disjunction` and
`localized_recovers_the_adopted_deployment_disjunction` derive the adopted
conclusions from the localized ones).

## The affected adopted theorems

Every adopted conclusion containing `TranscriptCollision`, `KhashCollision` or
`Khash2Collision`, and the section-6 theorem that shows its statement trivial.

| adopted module | adopted theorem | shape | triviality theorem here |
|---|---|---|---|
| `CommitmentOrder` | `absorb_messages_bind_or_collide` | `P ∨ TC` | `absorb_messages_bind_or_collide_statement_is_trivial` |
| `CommitmentOrder` | `prefix_digest_binds_the_frames` | `P ∨ TC` | `prefix_digest_binds_the_frames_statement_is_trivial` |
| `CommitmentOrder` | `prefix_digest_binds_the_three_roots` | `P ∨ TC` | `prefix_digest_binds_the_three_roots_statement_is_trivial` |
| `CommitmentOrder` | `distinct_roots_force_a_distinct_prefix_or_a_collision` | bare `TC` | `distinct_roots_force_a_distinct_prefix_statement_is_trivial` |
| `CommitmentOrder` | `changing_the_committed_tables_changes_the_prefix_or_collides` | bare `TC` | `changing_the_committed_tables_statement_is_trivial` |
| `CommitmentOrder` | `deterministic_adaptivity` | 5th conjunct bare `TC` | `deterministic_adaptivity_last_conjunct_is_trivial` |
| `CommitmentOrder` | `Example.fixture_deterministic_adaptivity` | 3rd conjunct bare `TC` | `fixture_deterministic_adaptivity_last_conjunct_is_trivial` |
| `InstalledInitialTranscript` | `installed_deterministic_adaptivity` | 5th conjunct bare `TC` | `installed_deterministic_adaptivity_last_conjunct_is_trivial` |
| `InstalledIndexSampler` | `used_claims_fixed_before_index_squeeze` | `P ∨ TC` | `used_claims_fixed_before_index_squeeze_statement_is_trivial` |
| `InstalledIndexSampler` | `changing_used_claims_changes_the_index_digest_or_collides` | bare `TC` | `changing_used_claims_statement_is_trivial` |
| `InstalledIndexSampler` | `installed_sampler_index_digest_binds_the_used_claims` | `P ∨ TC` | `installed_sampler_index_digest_binds_statement_is_trivial` |
| `InstalledIndexSampler` | `per_column_identification_hook` | last conjunct `P ∨ TC` | `per_column_identification_hook_last_conjunct_is_trivial` |
| `InstalledRoundCommit` | `round_message_fixed_before_round_challenges` | `P ∨ TC` | `round_message_fixed_before_round_challenges_statement_is_trivial` |
| `InstalledRoundCommit` | `changing_a_round_message_changes_the_round_digest_or_collides` | bare `TC` | `changing_a_round_message_statement_is_trivial` |
| `InstalledRoundCommit` | `run_round_digest_binds_the_round_message` | `P ∨ TC` | `run_round_digest_binds_the_round_message_statement_is_trivial` |
| `InstalledRoundCommit` | `run_round_digest_binds_the_round_message_of_a_shaped_proof` | `P ∨ TC` | `run_round_digest_binds_a_shaped_proof_statement_is_trivial` |
| `IndexPointZeroCheck` | `supplied_cells_fixed_before_index_squeeze` | 2nd conjunct `P ∨ TC` | `supplied_cells_fixed_before_index_squeeze_second_conjunct_is_trivial` |
| `ExplicitEngine` | `config_digest_binds_the_configuration` | `P ∨ KC` (inlined) | `config_digest_binds_the_configuration_statement_is_trivial` |
| `ExplicitEngine` | `config_digest_binds_the_core` | `P ∨ KC` | `config_digest_binds_the_core_statement_is_trivial` |
| `ExplicitEngine` | `accepted_configuration_is_the_deployed_one` | `P ∨ KC` | `accepted_configuration_is_the_deployed_one_statement_is_trivial` |
| `ExplicitEngine` | `accepted_configuration_is_the_deployed_one_from_lengths` | `P ∨ KC` | `accepted_configuration_is_the_deployed_one_from_lengths_statement_is_trivial` |
| `ExplicitEngine` | `accepted_gate_rows_match_deployed_gates` | `P ∨ KC` | `accepted_gate_rows_match_deployed_gates_statement_is_trivial` |
| `ExplicitEngine` | `accepted_gate_rows_match_deployed_gates_from_lengths` | `P ∨ KC` | `accepted_gate_rows_match_deployed_gates_from_lengths_statement_is_trivial` |
| `ExplicitEngine` | `accepted_whir_bytes_are_the_deployed_ones` | `P ∨ KC` | `accepted_whir_bytes_are_the_deployed_ones_statement_is_trivial` |
| `ExplicitEngine` | `accepted_whir_bytes_are_the_deployed_ones_from_lengths` | `P ∨ KC` | `accepted_whir_bytes_are_the_deployed_ones_from_lengths_statement_is_trivial` |
| `ExplicitEngine` | `weak_acceptance_recovers_the_deployment_predicate` | `P ∨ KC` | `weak_acceptance_recovers_the_deployment_predicate_statement_is_trivial` |
| `ExplicitEngine` | `weak_acceptance_recovers_the_deployment_predicate_from_lengths` | `P ∨ KC` | `weak_acceptance_recovers_the_deployment_predicate_from_lengths_statement_is_trivial` |
| `ExplicitEngine` | `accepted_configuration_matches_the_deployment_up_to_the_residue` | `P ∨ KC` | `accepted_configuration_matches_the_residue_statement_is_trivial` |
| `ExplicitEngine` | `accepted_configuration_matches_the_deployment_up_to_the_residue_from_lengths` | `P ∨ KC` | `accepted_configuration_matches_the_residue_from_lengths_statement_is_trivial` |
| `ExplicitEngine` | `accepted_call_pins_everything_but_the_two_digests` | `P ∨ KC` | `accepted_call_pins_everything_but_the_two_digests_statement_is_trivial` |
| `CanonicalProofCheck` | `no_free_config_field_remains` | `P ∨ KC` | `no_free_config_field_remains_statement_is_trivial` |
| `CanonicalProofCheck` | `accepted_configuration_is_the_deployment` | `P ∨ KC` | `accepted_configuration_is_the_deployment_statement_is_trivial` |
| `CanonicalProofCheck` | `accepted_call_is_a_deployed_call` | `P ∨ KC` | `accepted_call_is_a_deployed_call_statement_is_trivial` |
| `SoundnessAssembly` | `explicit_good_draw_assembly` | last conjunct `P ∨ KC` | `explicit_good_draw_assembly_last_conjunct_is_trivial` |
| `ExtractorConstruction` | `explicit_good_draw_of_extraction` | last conjunct `P ∨ KC` | `explicit_good_draw_of_extraction_last_conjunct_is_trivial` |
| `RustCallBoundary` | `rust_checks_are_consequences_of_solidity_acceptance_up_to` | `P ∨ KC` | `rust_checks_are_consequences_of_solidity_acceptance_statement_is_trivial` |
| `RustCallBoundary` | `recomputed_digest_binds_the_recomputed_core` | `P ∨ K2C` | `recomputed_digest_binds_the_recomputed_core_statement_is_trivial` |

`TC` = `CommitmentOrder.TranscriptCollision`, `KC` =
`ExplicitEngine.KhashCollision`, `K2C` = `RustCallBoundary.Khash2Collision`.
Thirty-seven adopted theorems across ten modules.

## The second affected family: `RowCollision` and `HashCollision`

`WhirRowBinding.HashCollision hash := ∃ a b : Spongefish.Bytes, a ≠ b ∧
hash a = hash b` is the same INFINITE-domain pigeonhole as `TC` and `KC`, and
`hash_collision_is_a_tautology` proves it.

`WhirRowBinding.RowCollision hash row other` is HALF localized. Its FIRST
disjunct, `row ≠ other ∧ hash row = hash other`, names the two rows and is the
localized shape (`LeafCollision` here, `leaf_collision_implies_row_collision`).
Its SECOND disjunct, `∃ a b, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧
hash a = hash b`, mentions neither `row` nor `other`, and
`row_collision_second_disjunct_gives_every_row_pair` shows a single witness for
it yields `RowCollision hash row other` for EVERY pair of rows.

That second disjunct is a FINITE pigeonhole, and section 8 FORMALIZES it:
`compression_collision_is_a_tautology` compares the two symbolic cardinals
`Fintype.card (Fin 32 → Fin 256)` and `Fintype.card (Fin 64 → Fin 256)` through
`Fintype.card_fun` and `Nat.pow_lt_pow_right`, then applies
`Fintype.exists_ne_map_eq_of_card_lt` to the map sending a length-sixty-four
string to the entries of its digest. Neither cardinal is ever evaluated, no
cardinal of a DIGEST type is taken, and no `Finset` over a digest space occurs in
any statement — so the earlier claim that this audit's conventions forbid the
argument was OVERSTATED, and it is withdrawn. Consequently
`row_collision_is_a_tautology hash row other` holds for EVERY `hash` and EVERY
pair of byte strings, and the sixteen adopted statements in the table below are
trivial as statements in exactly the sense of the thirty-seven above.

ONE ADOPTED THEOREM IS VACUOUS, WHICH IS WORSE.
`ConditionalSoundness.no_row_collision_binds_opened_dot` (line 728) takes
`hfree : ¬ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes` as a
HYPOTHESIS, and that hypothesis is UNSATISFIABLE
(`no_row_collision_hypothesis_is_unsatisfiable`). No instance of that theorem can
ever be discharged, so it constrains no execution whatsoever. This is a strictly
stronger defect than statement-triviality, which at least leaves the proof term
informative. RECOMMENDED AMENDMENT: replace the hypothesis by the
`OpeningBinding.NoCollision`-style LOCALIZED injectivity that the same file
already uses correctly — `ConditionalSoundness.NoCollisionAmong hash inputs`,
injectivity on the FINITE list of byte strings the execution actually hashes,
instantiated at the two opened rows — or, equivalently for the pair at hand, by
the negation of `LeafCollision hash row.bytes otherRow.bytes`. Either is
satisfiable, so either restores content.

PRIOR ART, ACKNOWLEDGED. `ConditionalSoundness` already states the
infinite-domain pigeonhole for `HashCollision`, twice: at lines 685-692, beside
`MerkleCollision` ("the GLOBAL statement `¬ WhirRowBinding.HashCollision hash` is
FALSE for every `hash` … Assuming it would make every theorem below vacuous"),
and again at lines 1349-1357, beside `no_collision_among_nil`. Both remarks are
correct and this module does not claim them. What is NEW here is (i) the same
pigeonhole for `TranscriptCollision`, `KhashCollision` and `Khash2Collision`,
which no adopted module records; (ii) the FINITE pigeonhole for `RowCollision`'s
second disjunct; (iii) the STATEMENT-FORM consequence, tabulated adopted theorem
by adopted theorem; and (iv) the observation that the very file carrying that
honesty remark then ASSUMES `¬ RowCollision` at line 728.

| adopted module | adopted theorem | shape | theorem here |
|---|---|---|---|
| `WhirRowBinding` 45 | `row_collision_exposes_actual_hash_inputs` | bare `HC` | `row_collision_exposes_actual_hash_inputs_statement_is_trivial` |
| `WhirRowBinding` 113 | `accepted_raw_rows_bind_or_collision` | `P ∨ RC` | `accepted_raw_rows_bind_or_collision_statement_is_trivial` |
| `WhirRowBinding` 131 | `accepted_positions_bind_or_collision` | `P ∨ RC` | `accepted_positions_bind_or_collision_statement_is_trivial` |
| `WhirRowBinding` 156 | `accepted_decoded_rows_bind_or_collision` | `P ∨ RC` | `accepted_decoded_rows_bind_or_collision_statement_is_trivial` |
| `WhirRowBinding` 171 | `distinct_accepted_decoded_rows_expose_hash_collision` | bare `HC` | `distinct_accepted_decoded_rows_statement_is_trivial` |
| `WhirRowBinding` 213 | `accepted_decoded_dots_bind_or_collision` | `P ∨ RC` | `accepted_decoded_dots_bind_or_collision_statement_is_trivial` |
| `WhirRowBinding` 238 | `accepted_full_column_dot_binding` | 3rd conjunct `P ∨ RC` | `accepted_full_column_dot_binding_last_conjunct_is_trivial` |
| `WhirRowBinding` 255 | `distinct_accepted_dot_values_expose_hash_collision` | bare `HC` | `distinct_accepted_dot_values_statement_is_trivial` |
| `OpeningBinding` 596 | `accepted_groups_position_rows_bind_or_collision` | `P ∨ RC` | `accepted_groups_position_rows_bind_or_collision_statement_is_trivial` |
| `ConstantsProvenance` 616 | `preprocessed_rows_bind_or_collision` | `P ∨ RC` | `preprocessed_rows_bind_or_collision_statement_is_trivial` |
| `InstalledWhirTail` 675 | `installed_accepted_rows_bind_or_collision_finalsplit` | `P ∨ RC` | `installed_accepted_rows_bind_finalsplit_statement_is_trivial` |
| `InstalledWhirTail` 726 | `installed_accepted_rows_bind_or_collision_round_one` | `P ∨ RC` | `installed_accepted_rows_bind_round_one_statement_is_trivial` |
| `ConditionalSoundness` 716 | `opened_dot_binds_or_row_collision` | `P ∨ RC` | `opened_dot_binds_or_row_collision_statement_is_trivial` |
| `Merkle` 325 | `path_collision_exposes_hash_collision` | bare `CC` | `path_collision_exposes_hash_collision_statement_is_trivial` |
| `MerkleExtraction` 151 | `two_accepted_openings_bind_or_compression_collision` | `P ∨ CC` | `two_accepted_openings_bind_or_compression_collision_statement_is_trivial` |
| `MerkleExtraction` 175 | `accepted_raw_rows_bind_or_hash_collision` | 3rd disjunct `CC` | `accepted_raw_rows_bind_or_hash_collision_statement_is_trivial` |
| `ConditionalSoundness` 728 | `no_row_collision_binds_opened_dot` | VACUOUS: `¬ RC` hypothesis | `no_row_collision_hypothesis_is_unsatisfiable` |

`HC` = `WhirRowBinding.HashCollision`, `RC` = `WhirRowBinding.RowCollision`,
`CC` = the unlocalized length-sixty-four compression existential. Seventeen rows:
sixteen trivial statements plus one vacuous theorem, across seven modules.

## Predicates this finding does NOT touch

* `OpeningBinding.NoCollision hash inputs := ∀ a ∈ inputs, ∀ b ∈ inputs,
  hash a = hash b → a = b` is the GOOD PATTERN: injectivity on a FINITE,
  EXECUTION-COMPUTED list of byte strings, used as a HYPOTHESIS rather than a
  conclusion, and both satisfiable and falsifiable
  (`no_collision_holds_on_the_empty_list`, `no_collision_fails_on_a_colliding_pair`).
* `ConditionalSoundness.NoCollisionAmong` is the same shape, and the adopted file
  itself says so; it is the repair the vacuous theorem above wants.
* `Merkle.PathCollision hash i a s b t` names the two parent inputs of the two
  extracted paths at each level, so it is localized to those paths.
* `OpeningBinding.path_collision_recorded` records the concrete colliding pair
  that a `PathCollision` supplies, so its content is in the statement already.

## Recommendation for the adopted documents

The affected sentences are the ones that read the disjunction as if the right
disjunct were hard to satisfy. Amend, by module:

* `CommitmentOrder` header, section "What is proved" bullet 4 and the "NO
  COLLISION RESISTANCE" bullet: "…or a concrete `TranscriptCollision hash`, i.e.
  they EXHIBIT a colliding pair of actual byte strings" is accurate about the
  PROOFS and inaccurate about the STATEMENTS. Add: the predicate is satisfied by
  every deterministic `hash`, so the disjunction is informative only through its
  proof term; cite the localized form.
* `InstalledIndexSampler` and `InstalledRoundCommit` headers, "What is NOT
  proved": "`CommitmentOrder.TranscriptCollision` is always a CONCLUSION here,
  never a hypothesis" is true and should stay, but must be followed by "and as a
  CONCLUSION it is a tautology; the content is the exhibited pair".
* `IndexPointZeroCheck` section 9 prose: "whose `TranscriptCollision` is
  EXHIBITED, never assumed" — same amendment.
* `ExplicitEngine` header ("…with `KhashCollision khash`, and a reader who wants
  the left disjunct must supply…"): state that the right disjunct is provable
  outright, so a reader can never "supply" anything by refuting it; the localized
  `ConfigEncodingCollision` is what a reader can refute for a given pair.
* `CanonicalProofCheck` header ("still carries `ExplicitEngine.KhashCollision
  khash` as an explicit disjunct") and `RustCallBoundary` header (two places,
  `KhashCollision` and `Khash2Collision`): same amendment.
* `SoundnessAssembly` and `ExtractorConstruction`: the deployment disjunct they
  carry through is the same one; one sentence each.
* `ConditionalSoundness`: the honesty remark at lines 685-692 and the note at
  lines 1349-1357 are CORRECT and should stay. What must change is line 728:
  `no_row_collision_binds_opened_dot` assumes the negation of a tautology and is
  therefore vacuous; give it `NoCollisionAmong` on the two opened rows instead.
* `SCOPE.md`: the hash-assumption claims are in Japanese, at lines 170-175 (the
  Merkle / `WhirRowBinding` reduction, "hashの単射性は仮定しない"), line 362
  ("hashは任意の決定的関数のままで…") and line 399 ("全てのhashに無条件の数学的
  安全性があると仮定しない"). All three are CORRECT and become stronger, not
  weaker, once the disjunctions are localized. The sentence to add is that the
  collision disjuncts were, in their adopted form, trivial AS STATEMENTS, and
  that the localized forms are what the claims should be read as. The audit's
  `REPORT.md` carries no corresponding hash-assumption sentence, so there is
  nothing there to amend.

## What is NOT proved here

No hash security, no collision resistance, no random-oracle property, no
Fiat--Shamir soundness, no WHIR/PCS soundness, no Rust/Yul/Solidity refinement.
`hash`, `thash`, `khash` and `khash2` remain arbitrary deterministic functions
and no theorem below assumes anything of them. Nothing here is a probability
statement or a bound, and nothing here is the deployed system's soundness error;
the wire-v3 WHIR profile this tree models is the ~100-bit design point, and no
figure in this module is a security parameter. The localized predicates do not
become false for a real hash — they are simply the statements one can refute for
a given pair of inputs, which the adopted forms are not.
-/

namespace Audit.Wire3.LocalizedCollisions

open Audit.Wire3

/-! ## 1. The pigeonhole: byte lists are infinite, digest spaces are finite

`Transcript.Digest` is a thirty-two byte list packaged with its length proof, so
`digestEntry` injects it into `Fin 32 → Transcript.Byte` and it is finite.
`Verifier.Root = Fin (2 ^ 256)` is finite outright. Both byte-list domains are
infinite because their byte types are nonempty. No `Finset` over a digest space
appears in any statement here, and no cardinal is ever evaluated. -/

def digestEntry (d : Transcript.Digest) (i : Fin 32) : Transcript.Byte :=
  d.bytes.get ⟨i.val, by rw [d.length_eq]; exact i.isLt⟩

theorem digest_entry_injective : Function.Injective digestEntry := by
  intro d e h
  have hlen : d.bytes.length = e.bytes.length := by rw [d.length_eq, e.length_eq]
  have hb : d.bytes = e.bytes := by
    refine List.ext_get hlen ?_
    intro n h1 h2
    have hn : n < 32 := by rw [d.length_eq] at h1; exact h1
    exact congrFun h ⟨n, hn⟩
  obtain ⟨db, dl⟩ := d
  obtain ⟨eb, el⟩ := e
  simp only [Transcript.Digest.mk.injEq]
  exact hb

instance instFiniteTranscriptDigest : Finite Transcript.Digest :=
  Finite.of_injective digestEntry digest_entry_injective

/-! ## 2. The two adopted collision predicates hold for EVERY function -/

theorem transcript_collision_is_a_tautology (hash : CommitmentOrder.Hash) :
    CommitmentOrder.TranscriptCollision hash :=
  Finite.exists_ne_map_eq_of_infinite hash

theorem khash_collision_is_a_tautology (khash : Verifier.Bytes → Verifier.Root) :
    ExplicitEngine.KhashCollision khash :=
  Finite.exists_ne_map_eq_of_infinite khash

/-! ## 3. The localized transcript-side predicates

`FrameCollision` names the two byte strings; `FrameFoldCollision` says WHERE in
the two absorbed message lists they come from. `absorb_messages_bind_or_frame_collision`
is the adopted `CommitmentOrder.absorb_messages_bind_or_collide` with the witness
promoted into the statement: same induction, same frame-injectivity step, and the
head case now records position `0` while the recursive case shifts by one. -/

def FrameCollision (hash : CommitmentOrder.Hash) (d e : Transcript.Digest)
    (m n : OuterInitial.Message) : Prop :=
  Transcript.frame d m.tag m.payload ≠ Transcript.frame e n.tag n.payload ∧
    hash (Transcript.frame d m.tag m.payload) = hash (Transcript.frame e n.tag n.payload)

def FrameFoldCollision (hash : CommitmentOrder.Hash) (s t : Transcript.State)
    (ms ns : List OuterInitial.Message) : Prop :=
  ∃ (k : Nat) (m n : OuterInitial.Message),
    ms.get? k = some m ∧ ns.get? k = some n ∧
      FrameCollision hash (OuterInitial.absorbMessages hash s (ms.take k)).digest
        (OuterInitial.absorbMessages hash t (ns.take k)).digest m n

theorem absorb_messages_bind_or_frame_collision (hash : CommitmentOrder.Hash) :
    ∀ (ms ns : List OuterInitial.Message) (s t : Transcript.State),
      ms.length = ns.length →
      (OuterInitial.absorbMessages hash s ms).digest
          = (OuterInitial.absorbMessages hash t ns).digest →
      (s.digest = t.digest ∧ ms = ns) ∨ FrameFoldCollision hash s t ms ns := by
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
            · obtain ⟨hdig, htag, hpay⟩ := CommitmentOrder.frame_injective _ _ _ _ _ _ hfr
              have hmn : m = n := by
                obtain ⟨mt, mp⟩ := m
                obtain ⟨nt, np⟩ := n
                simp only [OuterInitial.Message.mk.injEq]
                exact ⟨htag, hpay⟩
              exact Or.inl ⟨hdig, by rw [hmn, hms]⟩
            · exact Or.inr ⟨0, m, n, rfl, rfl, hfr, hh⟩
          · obtain ⟨k, a, b, hka, hkb, hfc⟩ := hcol
            exact Or.inr ⟨k + 1, a, b, hka, hkb, hfc⟩

/-! ## 4. Falsifiability of the transcript-side localized predicate, and the
localized restatements of the index-sampling and round-commit
non-malleability results -/

theorem frame_fold_collision_implies_transcript_collision (hash : CommitmentOrder.Hash)
    (s t : Transcript.State) (ms ns : List OuterInitial.Message)
    (h : FrameFoldCollision hash s t ms ns) : CommitmentOrder.TranscriptCollision hash := by
  obtain ⟨_, _, _, _, _, hne, heq⟩ := h
  exact ⟨_, _, hne, heq⟩

theorem frame_fold_collision_fails_on_equal_runs (hash : CommitmentOrder.Hash)
    (s : Transcript.State) (ms : List OuterInitial.Message) :
    ¬ FrameFoldCollision hash s s ms ms := by
  rintro ⟨k, m, n, hkm, hkn, hne, -⟩
  exact hne (by rw [Option.some.inj (hkm.symm.trans hkn)])

theorem frame_fold_collision_holds_for_the_constant_hash (s : Transcript.State) :
    FrameFoldCollision CommitmentOrder.constantHash s s
      [OuterInitial.byteMessage []] [OuterInitial.byteMessage [0]] := by
  refine ⟨0, OuterInitial.byteMessage [], OuterInitial.byteMessage [0], rfl, rfl, ?_, rfl⟩
  intro hfr
  obtain ⟨-, hp⟩ := Transcript.frame_tag_and_payload_are_unambiguous s.digest 2 2 [] [0] hfr
  exact absurd hp (by decide)

def IndexDigestClash (thash : Transcript.Hash) (s t : Transcript.State)
    (u v : Verifier.UsedClaims) : Prop :=
  FrameFoldCollision thash s t (InstalledIndexSampler.claimFrames u)
    (InstalledIndexSampler.claimFrames v)

theorem used_claims_fixed_before_index_squeeze_localized (thash : Transcript.Hash)
    (s t : Transcript.State) (u v : Verifier.UsedClaims)
    (h : InstalledIndexSampler.indexDigest thash s u
        = InstalledIndexSampler.indexDigest thash t v) :
    (s.digest = t.digest ∧ u = v) ∨ IndexDigestClash thash s t u v := by
  rcases absorb_messages_bind_or_frame_collision thash (InstalledIndexSampler.claimFrames u)
      (InstalledIndexSampler.claimFrames v) s t
      (by rw [InstalledIndexSampler.claim_frame_count,
        InstalledIndexSampler.claim_frame_count]) h with ⟨hdig, hframes⟩ | hcol
  · exact Or.inl ⟨hdig, InstalledIndexSampler.claim_frames_injective u v hframes⟩
  · exact Or.inr hcol

theorem changing_used_claims_changes_the_index_digest_or_clashes (thash : Transcript.Hash)
    (s t : Transcript.State) (u v : Verifier.UsedClaims) (hne : u ≠ v)
    (h : InstalledIndexSampler.indexDigest thash s u
        = InstalledIndexSampler.indexDigest thash t v) :
    IndexDigestClash thash s t u v := by
  rcases used_claims_fixed_before_index_squeeze_localized thash s t u v h with ⟨_, heq⟩ | hcol
  · exact absurd heq hne
  · exact hcol

def RoundDigestClash (thash : Transcript.Hash) (s t : Transcript.State) (i j : Nat)
    (m n : Verifier.CoupledMessage) : Prop :=
  FrameFoldCollision thash s t (InstalledRoundCommit.roundFrames i m)
    (InstalledRoundCommit.roundFrames j n)

theorem round_message_fixed_before_round_challenges_localized (thash : Transcript.Hash)
    (s t : Transcript.State) (i j : Nat) (m n : Verifier.CoupledMessage)
    (hbi : i < Transcript.u64Limit) (hbj : j < Transcript.u64Limit)
    (h : (OuterAdapter.roundCommitted thash s i m.1 m.2).digest =
      (OuterAdapter.roundCommitted thash t j n.1 n.2).digest) :
    (s.digest = t.digest ∧ i = j ∧ m = n) ∨ RoundDigestClash thash s t i j m n := by
  have hbytes : (256 : Nat) ^ 8 = Transcript.u64Limit := by
    unfold Transcript.u64Limit
    norm_num
  rw [InstalledRoundCommit.round_committed_is_the_frame_fold,
    InstalledRoundCommit.round_committed_is_the_frame_fold] at h
  rcases absorb_messages_bind_or_frame_collision thash (InstalledRoundCommit.roundFrames i m)
      (InstalledRoundCommit.roundFrames j n) s t
      (by rw [InstalledRoundCommit.round_frame_count,
        InstalledRoundCommit.round_frame_count]) h with ⟨hdig, hframes⟩ | hcol
  · refine Or.inl ⟨hdig, ?_, ?_⟩
    · have h1 := (InstalledRoundCommit.round_frames_get_index i m).symm.trans
        ((congrArg (fun l => l.get? 1) hframes).trans
          (InstalledRoundCommit.round_frames_get_index j n))
      have hle : Transcript.le 8 i = Transcript.le 8 j :=
        congrArg OuterInitial.Message.payload (Option.some.inj h1)
      exact Transcript.le_injective_bounded 8 i j (by rw [hbytes]; exact hbi)
        (by rw [hbytes]; exact hbj) hle
    · have h2 := (InstalledRoundCommit.round_frames_get_log_message i m).symm.trans
        ((congrArg (fun l => l.get? 2) hframes).trans
          (InstalledRoundCommit.round_frames_get_log_message j n))
      have h3 := (InstalledRoundCommit.round_frames_get_gate_message i m).symm.trans
        ((congrArg (fun l => l.get? 3) hframes).trans
          (InstalledRoundCommit.round_frames_get_gate_message j n))
      have hlog : m.1 = n.1 := InstalledIndexSampler.encoded_vec_injective _ _
        (congrArg OuterInitial.Message.payload (Option.some.inj h2))
      have hgate : m.2 = n.2 := InstalledIndexSampler.encoded_vec_injective _ _
        (congrArg OuterInitial.Message.payload (Option.some.inj h3))
      exact Prod.ext hlog hgate
  · exact Or.inr hcol

theorem changing_a_round_message_changes_the_round_digest_or_clashes (thash : Transcript.Hash)
    (s t : Transcript.State) (i j : Nat) (m n : Verifier.CoupledMessage)
    (hbi : i < Transcript.u64Limit) (hbj : j < Transcript.u64Limit) (hne : m ≠ n)
    (h : (OuterAdapter.roundCommitted thash s i m.1 m.2).digest =
      (OuterAdapter.roundCommitted thash t j n.1 n.2).digest) :
    RoundDigestClash thash s t i j m n := by
  rcases round_message_fixed_before_round_challenges_localized thash s t i j m n hbi hbj h with
    ⟨_, _, heq⟩ | hcol
  · exact absurd heq hne
  · exact hcol

theorem run_round_digest_binds_the_round_message_localized (thash : Transcript.Hash)
    (s0 t0 : Transcript.State) (ms ns : List Verifier.CoupledMessage) (r : Nat)
    (m n : Verifier.CoupledMessage) (hbr : r < Transcript.u64Limit)
    (h : (OuterAdapter.roundCommitted thash
        (InstalledRoundCommit.concreteFinal thash s0 0 (ms.take r)) r m.1 m.2).digest =
      (OuterAdapter.roundCommitted thash
        (InstalledRoundCommit.concreteFinal thash t0 0 (ns.take r)) r n.1 n.2).digest) :
    ((InstalledRoundCommit.concreteFinal thash s0 0 (ms.take r)).digest =
        (InstalledRoundCommit.concreteFinal thash t0 0 (ns.take r)).digest ∧ m = n) ∨
      RoundDigestClash thash (InstalledRoundCommit.concreteFinal thash s0 0 (ms.take r))
        (InstalledRoundCommit.concreteFinal thash t0 0 (ns.take r)) r r m n := by
  rcases round_message_fixed_before_round_challenges_localized thash _ _ r r m n hbr hbr h with
    ⟨hdig, _, heq⟩ | hcol
  · exact Or.inl ⟨hdig, heq⟩
  · exact Or.inr hcol

/-! ## 5. The localized configuration-side predicate and the deployment chain

`ConfigEncodingCollision khash c c2` names the two `encodeConfig` strings. The
chain below re-runs the adopted proofs of `ExplicitEngine` and
`CanonicalProofCheck` with this disjunct in place of `KhashCollision`; no step is
weakened, and every collision-free ingredient (the gate preflight, the envelope,
the canonical profile table, the two pinned digests) is reused verbatim from the
adopted modules. -/

def ConfigEncodingCollision (khash : Verifier.Bytes → Verifier.Root)
    (c c2 : Verifier.Config) : Prop :=
  ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c2 ∧
    khash (ExplicitEngine.encodeConfig c) = khash (ExplicitEngine.encodeConfig c2)

theorem config_encoding_collision_implies_khash_collision
    (khash : Verifier.Bytes → Verifier.Root) (c c2 : Verifier.Config)
    (h : ConfigEncodingCollision khash c c2) : ExplicitEngine.KhashCollision khash :=
  ⟨_, _, h.1, h.2⟩

theorem config_encoding_collision_fails_on_equal_configurations
    (khash : Verifier.Bytes → Verifier.Root) (c : Verifier.Config) :
    ¬ ConfigEncodingCollision khash c c := fun h => h.1 rfl

def separatingKhash (a : Verifier.Bytes) : Verifier.Bytes → Verifier.Root :=
  fun b => if b = a then ⟨0, by decide⟩ else ⟨1, by decide⟩

theorem config_encoding_collision_fails_for_a_separating_khash (c c2 : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c2) :
    ¬ ConfigEncodingCollision (separatingKhash (ExplicitEngine.encodeConfig c)) c c2 := by
  rintro ⟨-, heq⟩
  have h1 : separatingKhash (ExplicitEngine.encodeConfig c) (ExplicitEngine.encodeConfig c)
      = ⟨0, by decide⟩ := if_pos rfl
  have h2 : separatingKhash (ExplicitEngine.encodeConfig c) (ExplicitEngine.encodeConfig c2)
      = ⟨1, by decide⟩ := if_neg (fun h => hne h.symm)
  rw [h1, h2] at heq
  exact absurd heq (by decide)

theorem config_digest_binds_the_core_localized (khash : Verifier.Bytes → Verifier.Root)
    (c c2 : Verifier.Config) (hc : ExplicitEngine.Bounded c) (hc2 : ExplicitEngine.Bounded c2)
    (h : ExplicitEngine.concreteConfigurationHash khash c
        = ExplicitEngine.concreteConfigurationHash khash c2) :
    ExplicitEngine.core c = ExplicitEngine.core c2 ∨ ConfigEncodingCollision khash c c2 := by
  by_cases he : ExplicitEngine.encodeConfig c = ExplicitEngine.encodeConfig c2
  · exact Or.inl (ExplicitEngine.encode_config_injective hc hc2 he)
  · exact Or.inr ⟨he, h⟩

theorem accepted_configuration_is_the_deployed_one_localized (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hdep : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀))
    (hc : ExplicitEngine.Bounded c) (hc₀ : ExplicitEngine.Bounded c₀)
    (hacc : Integrated.verify (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec
      pin chain c p = .ok ()) :
    ExplicitEngine.core c = ExplicitEngine.core c₀ ∨ ConfigEncodingCollision khash c c₀ := by
  have h := ExplicitEngine.accepted_configuration_is_the_pinned_one gdec hash thash khash P c₀
    pin chain c p hacc
  rw [hdep] at h
  exact config_digest_binds_the_core_localized khash c c₀ hc hc₀ h

theorem accepted_gate_rows_match_deployed_gates_localized (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hdep : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀))
    (hc : ExplicitEngine.Bounded c) (hc₀ : ExplicitEngine.Bounded c₀)
    (hacc : Integrated.verify (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec
      pin chain c p = .ok ()) :
    (∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      ConfigEncodingCollision khash c c₀ := by
  rcases accepted_configuration_is_the_deployed_one_localized gdec hash thash khash P c₀ pin
    chain c p hdep hc hc₀ hacc with hcore | hcol
  · obtain ⟨gates, hdg, hr, -⟩ := ExplicitEngine.accepted_gate_rows_are_the_decoded_length gdec
      hash thash khash P c₀ pin chain c p hacc
    have he : c.gatesEncoding = c₀.gatesEncoding :=
      congrArg ExplicitEngine.Core.gatesEncoding hcore
    exact Or.inl ⟨gates, he ▸ hdg, hr⟩
  · exact Or.inr hcol

theorem accepted_configuration_matches_the_deployment_up_to_the_residue_localized
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (henv₀ : Verifier.envelope c₀ = true)
    (hdep : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀))
    (hc : ExplicitEngine.Bounded c) (hc₀ : ExplicitEngine.Bounded c₀)
    (hacc : Integrated.verify (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec
      pin chain c p = .ok ()) :
    (ExplicitEngine.core c = ExplicitEngine.core c₀ ∧ c.indexBits = c₀.indexBits) ∨
      ConfigEncodingCollision khash c c₀ := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier
    (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
  have henv : Verifier.envelope c = true :=
    (Verifier.verify_success_checks _ pin chain c p hv).2.2.1
  rcases accepted_configuration_is_the_deployed_one_localized gdec hash thash khash P c₀ pin
    chain c p hdep hc hc₀ hacc with hcore | hcol
  · exact Or.inl ⟨hcore,
      ExplicitEngine.envelope_and_core_determine_index_bits henv henv₀ hcore⟩
  · exact Or.inr hcol

theorem accepted_call_pins_everything_but_the_two_digests_localized
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (henv₀ : Verifier.envelope c₀ = true)
    (hdep : pin.configDigest = khash (ExplicitEngine.encodeConfig c₀))
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hc₀ : ExplicitEngine.Bounded c₀)
    (hacc : Integrated.verify (ExplicitEngine.explicitEngine gdec hash thash khash P c₀) gdec
      pin chain c p = .ok ()) :
    (ExplicitEngine.core c = ExplicitEngine.core c₀ ∧ c.indexBits = c₀.indexBits ∧
      ∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      ConfigEncodingCollision khash c c₀ := by
  have hc : ExplicitEngine.Bounded c :=
    ExplicitEngine.bounded_of_acceptance gdec hash thash khash P c₀ pin chain c p hg hw hacc
  rcases accepted_configuration_matches_the_deployment_up_to_the_residue_localized gdec hash
    thash khash P c₀ pin chain c p henv₀ hdep hc hc₀ hacc with ⟨hcore, hib⟩ | hcol
  · rcases accepted_gate_rows_match_deployed_gates_localized gdec hash thash khash P c₀ pin
      chain c p hdep hc hc₀ hacc with hgates | hcol
    · exact Or.inl ⟨hcore, hib, hgates⟩
    · exact Or.inr hcol
  · exact Or.inr hcol

theorem no_free_config_field_remains_localized (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    (c.degreeBits = c₀.degreeBits ∧ c.numConstants = c₀.numConstants ∧
      c.numRouted = c₀.numRouted ∧ c.numWires = c₀.numWires ∧
      c.numPublicInputs = c₀.numPublicInputs ∧ c.numSelectors = c₀.numSelectors ∧
      c.numGateConstraints = c₀.numGateConstraints ∧ c.quotientDegree = c₀.quotientDegree ∧
      c.gateRows = c₀.gateRows ∧ c.indexBits = c₀.indexBits ∧ c.kIs = c₀.kIs ∧
      c.subgroupPowers = c₀.subgroupPowers ∧ c.publicInputWireMap = c₀.publicInputWireMap ∧
      c.gatesEncoding = c₀.gatesEncoding ∧ c.whirEncoding = c₀.whirEncoding ∧
      c.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest ∧
      c.whirProtocolId = c₀.whirProtocolId ∧ c.whirSessionId = c₀.whirSessionId) ∨
    ConfigEncodingCollision khash c c₀ := by
  have hexpacc := CanonicalProofCheck.pinned_acceptance_is_explicit_acceptance gdec hash thash
    khash P c₀ pin chain c p hacc
  rcases accepted_call_pins_everything_but_the_two_digests_localized gdec hash thash khash P c₀
    pin chain c p hd.envelope hd.pinnedDigest hg hw hd.bounded hexpacc with
    ⟨hcore, hib, gates, hgd, hgl⟩ | hcol
  · obtain ⟨hcd, hccd⟩ := CanonicalProofCheck.accepted_digests_are_the_deployed_ones gdec hash
      thash khash P c₀ pin chain c p hacc
    obtain ⟨wp, -, hcheck, hpc₀, -, -, -, -⟩ :=
      CanonicalProofCheck.pinned_accepted_profile_is_canonical gdec hash thash khash P c₀ pin
        chain c p hacc
    obtain ⟨wp₀, hpc₀2, hcheck₀⟩ :=
      (PinnedWhirProfile.profile_ok_exact P c₀).mp hd.canonicalProfile
    have hwp : wp₀ = wp := Option.some.inj (hpc₀2.symm.trans hpc₀)
    subst hwp
    obtain ⟨-, -, hsid, -, hpid⟩ := (PinnedWhirProfile.canonical_check_exact P c wp₀).mp hcheck
    obtain ⟨-, -, hsid₀, -, hpid₀⟩ :=
      (PinnedWhirProfile.canonical_check_exact P c₀ wp₀).mp hcheck₀
    exact Or.inl
      ⟨congrArg ExplicitEngine.Core.degreeBits hcore,
       congrArg ExplicitEngine.Core.numConstants hcore,
       congrArg ExplicitEngine.Core.numRouted hcore,
       congrArg ExplicitEngine.Core.numWires hcore,
       congrArg ExplicitEngine.Core.numPublicInputs hcore,
       congrArg ExplicitEngine.Core.numSelectors hcore,
       congrArg ExplicitEngine.Core.numGateConstraints hcore,
       congrArg ExplicitEngine.Core.quotientDegree hcore,
       hgl.symm.trans (hd.decodedGateRows gates hgd), hib,
       congrArg ExplicitEngine.Core.kIs hcore,
       congrArg ExplicitEngine.Core.subgroupPowers hcore,
       congrArg ExplicitEngine.Core.publicInputWireMap hcore,
       congrArg ExplicitEngine.Core.gatesEncoding hcore,
       congrArg ExplicitEngine.Core.whirEncoding hcore,
       hcd, hccd, hpid.trans hpid₀.symm, hsid.trans hsid₀.symm⟩
  · exact Or.inr hcol

theorem accepted_configuration_is_the_deployment_localized (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    c = c₀ ∨ ConfigEncodingCollision khash c c₀ := by
  rcases no_free_config_field_remains_localized gdec hash thash khash P c₀ pin chain c p hd hg
    hw hacc with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ | hcol
  · exact Or.inl (CanonicalProofCheck.config_eq_of_fields h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      h13 h14 h15 h16 h17 h18 h19)
  · exact Or.inr hcol

theorem accepted_call_is_a_deployed_call_localized (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    (c = c₀ ∧ p.protocolVersion = 3 ∧ p.circuitDigest = c₀.circuitDigest ∧
      p.preprocessedRoot = pin.preprocessedRoot ∧ p.constituentWidth = Verifier.width c₀) ∨
    ConfigEncodingCollision khash c c₀ := by
  rcases accepted_configuration_is_the_deployment_localized gdec hash thash khash P c₀ pin chain
    c p hd hg hw hacc with heq | hcol
  · obtain ⟨-, -, -, -, hv⟩ := Integrated.accepted_preflights_and_original_verifier
      (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀) gdec pin chain c p hacc
    have hs := Verifier.verify_success_checks _ pin chain c p hv
    have hshape : Verifier.shape pin c p = true := hs.2.2.2.2.1
    obtain ⟨hpd, -, -⟩ := CanonicalProofCheck.accepted_proof_circuit_digest_is_deployed gdec hash
      thash khash P c₀ pin chain c p hacc
    simp only [Verifier.shape, decide_eq_true_eq] at hshape
    exact Or.inl ⟨heq, hshape.1, hpd, hshape.2.2.2.2.1, heq ▸ hshape.2.1⟩
  · exact Or.inr hcol

theorem rust_checks_are_consequences_of_solidity_acceptance_up_to_localized
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash khash2 : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hr : RustCallBoundary.RustDeployedFacts gdec khash2 P c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    RustCallBoundary.rustDeployment gdec khash2 P c = true ∨ ConfigEncodingCollision khash c c₀ := by
  rcases accepted_configuration_is_the_deployment_localized gdec hash thash khash P c₀ pin chain
    c p hd hg hw hacc with heq | hcol
  · exact Or.inl (heq ▸ RustCallBoundary.rust_deployment_of_deployed_facts gdec khash2 P c₀ hr)
  · exact Or.inr hcol

/-! ## 6. Each affected adopted conclusion, with ALL hypotheses dropped

Every statement in this section is the conclusion of an adopted theorem (or the
affected conjunct of one) with its hypotheses removed, proved from the tautology
alone. Nothing here contradicts the adopted theorems: it shows that their
statements carry no information beyond what these one-line proofs already give,
so the audit content of each is entirely in its proof term. -/

theorem khash2_collision_is_a_tautology (khash2 : Verifier.Bytes → Verifier.Root) :
    RustCallBoundary.Khash2Collision khash2 :=
  Finite.exists_ne_map_eq_of_infinite khash2

theorem absorb_messages_bind_or_collide_statement_is_trivial (hash : CommitmentOrder.Hash)
    (ms ns : List OuterInitial.Message) (s t : Transcript.State) :
    (s.digest = t.digest ∧ ms = ns) ∨ CommitmentOrder.TranscriptCollision hash :=
  Or.inr (transcript_collision_is_a_tautology hash)

theorem prefix_digest_binds_the_frames_statement_is_trivial (hash : CommitmentOrder.Hash)
    (c c2 : Verifier.Config) (s s2 : Verifier.Statement) :
    CommitmentOrder.gateChallengeFrames c s = CommitmentOrder.gateChallengeFrames c2 s2 ∨
      CommitmentOrder.TranscriptCollision hash :=
  Or.inr (transcript_collision_is_a_tautology hash)

theorem prefix_digest_binds_the_three_roots_statement_is_trivial (hash : CommitmentOrder.Hash)
    (s s2 : Verifier.Statement) :
    (s.preprocessedRoot = s2.preprocessedRoot ∧ s.witnessRoot = s2.witnessRoot ∧
      s.normInverseRoot = s2.normInverseRoot) ∨ CommitmentOrder.TranscriptCollision hash :=
  Or.inr (transcript_collision_is_a_tautology hash)

theorem distinct_roots_force_a_distinct_prefix_statement_is_trivial
    (hash : CommitmentOrder.Hash) : CommitmentOrder.TranscriptCollision hash :=
  transcript_collision_is_a_tautology hash

theorem changing_the_committed_tables_statement_is_trivial (hash : CommitmentOrder.Hash) :
    CommitmentOrder.TranscriptCollision hash :=
  transcript_collision_is_a_tautology hash

theorem deterministic_adaptivity_last_conjunct_is_trivial (hash : CommitmentOrder.Hash)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (c : Verifier.Config) (p : Verifier.Proof) (t : GateSuffixPolynomial.Tables) :
    ∀ (c2 : Verifier.Config) (s2 : Verifier.Statement) (u : GateSuffixPolynomial.Tables),
      CommitmentOrder.CommittedTables tablesOf s2 u →
      (u.wires ≠ t.wires ∨ u.constants ≠ t.constants) →
      CommitmentOrder.prefixDigest hash c2 s2
          = CommitmentOrder.prefixDigest hash c (Verifier.statement p) →
      CommitmentOrder.TranscriptCollision hash :=
  fun _ _ _ _ _ _ => transcript_collision_is_a_tautology hash

theorem fixture_deterministic_adaptivity_last_conjunct_is_trivial (hash : CommitmentOrder.Hash)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (t : GateSuffixPolynomial.Tables) :
    ∀ (c2 : Verifier.Config) (s2 : Verifier.Statement) (u : GateSuffixPolynomial.Tables),
      CommitmentOrder.CommittedTables tablesOf s2 u →
      (u.wires ≠ t.wires ∨ u.constants ≠ t.constants) →
      CommitmentOrder.prefixDigest hash c2 s2
          = CommitmentOrder.prefixDigest hash OuterAdapter.fixtureConfig
            (Verifier.statement OuterAdapter.fixtureProof) →
      CommitmentOrder.TranscriptCollision hash :=
  fun _ _ _ _ _ _ => transcript_collision_is_a_tautology hash

theorem installed_deterministic_adaptivity_last_conjunct_is_trivial (thash : Transcript.Hash)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (c : Verifier.Config) (p : Verifier.Proof) (t : GateSuffixPolynomial.Tables) :
    ∀ (c2 : Verifier.Config) (s2 : Verifier.Statement) (u : GateSuffixPolynomial.Tables),
      CommitmentOrder.CommittedTables tablesOf s2 u →
      (u.wires ≠ t.wires ∨ u.constants ≠ t.constants) →
      CommitmentOrder.prefixDigest thash c2 s2
          = CommitmentOrder.prefixDigest thash c (Verifier.statement p) →
      CommitmentOrder.TranscriptCollision thash :=
  fun _ _ _ _ _ _ => transcript_collision_is_a_tautology thash

theorem used_claims_fixed_before_index_squeeze_statement_is_trivial (thash : Transcript.Hash)
    (s t : Transcript.State) (u v : Verifier.UsedClaims) :
    (s.digest = t.digest ∧ u = v) ∨ CommitmentOrder.TranscriptCollision thash :=
  Or.inr (transcript_collision_is_a_tautology thash)

theorem changing_used_claims_statement_is_trivial (thash : Transcript.Hash) :
    CommitmentOrder.TranscriptCollision thash :=
  transcript_collision_is_a_tautology thash

theorem installed_sampler_index_digest_binds_statement_is_trivial (thash : Transcript.Hash)
    (st st2 : Transcript.State) (p p2 : Verifier.Proof) :
    (st.digest = st2.digest ∧ p.used = p2.used) ∨ CommitmentOrder.TranscriptCollision thash :=
  Or.inr (transcript_collision_is_a_tautology thash)

theorem per_column_identification_hook_last_conjunct_is_trivial (thash : Transcript.Hash)
    (st : Transcript.State) (p : Verifier.Proof) :
    ∀ (st2 : Transcript.State) (v : Verifier.UsedClaims),
      InstalledIndexSampler.indexDigest thash st2 v
          = InstalledIndexSampler.indexDigest thash st p.used →
        (st2.digest = st.digest ∧ v = p.used) ∨ CommitmentOrder.TranscriptCollision thash :=
  fun _ _ _ => Or.inr (transcript_collision_is_a_tautology thash)

theorem supplied_cells_fixed_before_index_squeeze_second_conjunct_is_trivial
    (thash : Transcript.Hash) (s : Transcript.State) (u : Verifier.UsedClaims) :
    ∀ (t : Transcript.State) (v : Verifier.UsedClaims),
      InstalledIndexSampler.indexDigest thash t v
          = InstalledIndexSampler.indexDigest thash s u →
        (t.digest = s.digest ∧ v = u) ∨ CommitmentOrder.TranscriptCollision thash :=
  fun _ _ _ => Or.inr (transcript_collision_is_a_tautology thash)

theorem round_message_fixed_before_round_challenges_statement_is_trivial
    (thash : Transcript.Hash) (s t : Transcript.State) (i j : Nat)
    (m n : Verifier.CoupledMessage) :
    (s.digest = t.digest ∧ i = j ∧ m = n) ∨ CommitmentOrder.TranscriptCollision thash :=
  Or.inr (transcript_collision_is_a_tautology thash)

theorem changing_a_round_message_statement_is_trivial (thash : Transcript.Hash) :
    CommitmentOrder.TranscriptCollision thash :=
  transcript_collision_is_a_tautology thash

theorem run_round_digest_binds_the_round_message_statement_is_trivial
    (thash : Transcript.Hash) (s0 t0 : Transcript.State)
    (ms ns : List Verifier.CoupledMessage) (r : Nat) (m n : Verifier.CoupledMessage) :
    ((InstalledRoundCommit.concreteFinal thash s0 0 (ms.take r)).digest =
        (InstalledRoundCommit.concreteFinal thash t0 0 (ns.take r)).digest ∧ m = n) ∨
      CommitmentOrder.TranscriptCollision thash :=
  Or.inr (transcript_collision_is_a_tautology thash)

theorem run_round_digest_binds_a_shaped_proof_statement_is_trivial
    (thash : Transcript.Hash) (s0 t0 : Transcript.State)
    (ms ns : List Verifier.CoupledMessage) (r : Nat) (m n : Verifier.CoupledMessage) :
    ((InstalledRoundCommit.concreteFinal thash s0 0 (ms.take r)).digest =
        (InstalledRoundCommit.concreteFinal thash t0 0 (ns.take r)).digest ∧ m = n) ∨
      CommitmentOrder.TranscriptCollision thash :=
  Or.inr (transcript_collision_is_a_tautology thash)

theorem config_digest_binds_the_configuration_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c2 : Verifier.Config) :
    ExplicitEngine.encodeConfig c = ExplicitEngine.encodeConfig c2 ∨
      ∃ a b, a ≠ b ∧ khash a = khash b :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem config_digest_binds_the_core_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c2 : Verifier.Config) :
    ExplicitEngine.core c = ExplicitEngine.core c2 ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_configuration_is_the_deployed_one_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    ExplicitEngine.core c = ExplicitEngine.core c₀ ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_configuration_is_the_deployed_one_from_lengths_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    ExplicitEngine.core c = ExplicitEngine.core c₀ ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_gate_rows_match_deployed_gates_statement_is_trivial
    (gdec : Integrated.DecodeGates) (khash : Verifier.Bytes → Verifier.Root)
    (c c₀ : Verifier.Config) :
    (∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_gate_rows_match_deployed_gates_from_lengths_statement_is_trivial
    (gdec : Integrated.DecodeGates) (khash : Verifier.Bytes → Verifier.Root)
    (c c₀ : Verifier.Config) :
    (∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_whir_bytes_are_the_deployed_ones_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    c.whirEncoding = c₀.whirEncoding ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_whir_bytes_are_the_deployed_ones_from_lengths_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    c.whirEncoding = c₀.whirEncoding ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem weak_acceptance_recovers_the_deployment_predicate_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c c₀ : Verifier.Config) :
    ExplicitEngine.explicitDeployment P c₀ c = true ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem weak_acceptance_recovers_the_deployment_predicate_from_lengths_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c c₀ : Verifier.Config) :
    ExplicitEngine.explicitDeployment P c₀ c = true ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_configuration_matches_the_residue_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    (ExplicitEngine.core c = ExplicitEngine.core c₀ ∧ c.indexBits = c₀.indexBits) ∨
      ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_configuration_matches_the_residue_from_lengths_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    (ExplicitEngine.core c = ExplicitEngine.core c₀ ∧ c.indexBits = c₀.indexBits) ∨
      ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_call_pins_everything_but_the_two_digests_statement_is_trivial
    (gdec : Integrated.DecodeGates) (khash : Verifier.Bytes → Verifier.Root)
    (c c₀ : Verifier.Config) :
    (ExplicitEngine.core c = ExplicitEngine.core c₀ ∧ c.indexBits = c₀.indexBits ∧
      ∃ gates, gdec c₀.gatesEncoding = some gates ∧ gates.length = c.gateRows) ∨
      ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem no_free_config_field_remains_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    (c.degreeBits = c₀.degreeBits ∧ c.numConstants = c₀.numConstants ∧
      c.numRouted = c₀.numRouted ∧ c.numWires = c₀.numWires ∧
      c.numPublicInputs = c₀.numPublicInputs ∧ c.numSelectors = c₀.numSelectors ∧
      c.numGateConstraints = c₀.numGateConstraints ∧ c.quotientDegree = c₀.quotientDegree ∧
      c.gateRows = c₀.gateRows ∧ c.indexBits = c₀.indexBits ∧ c.kIs = c₀.kIs ∧
      c.subgroupPowers = c₀.subgroupPowers ∧ c.publicInputWireMap = c₀.publicInputWireMap ∧
      c.gatesEncoding = c₀.gatesEncoding ∧ c.whirEncoding = c₀.whirEncoding ∧
      c.circuitDigest = c₀.circuitDigest ∧ c.circuitConfigDigest = c₀.circuitConfigDigest ∧
      c.whirProtocolId = c₀.whirProtocolId ∧ c.whirSessionId = c₀.whirSessionId) ∨
    ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_configuration_is_the_deployment_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    c = c₀ ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem accepted_call_is_a_deployed_call_statement_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (p : Verifier.Proof) :
    (c = c₀ ∧ p.protocolVersion = 3 ∧ p.circuitDigest = c₀.circuitDigest ∧
      p.preprocessedRoot = pin.preprocessedRoot ∧ p.constituentWidth = Verifier.width c₀) ∨
    ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem explicit_good_draw_assembly_last_conjunct_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    ExplicitEngine.core c = ExplicitEngine.core c₀ ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem explicit_good_draw_of_extraction_last_conjunct_is_trivial
    (khash : Verifier.Bytes → Verifier.Root) (c c₀ : Verifier.Config) :
    ExplicitEngine.core c = ExplicitEngine.core c₀ ∨ ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem rust_checks_are_consequences_of_solidity_acceptance_statement_is_trivial
    (gdec : Integrated.DecodeGates) (khash khash2 : Verifier.Bytes → Verifier.Root)
    (P : PinnedWhirProfile.Profile) (c : Verifier.Config) :
    RustCallBoundary.rustDeployment gdec khash2 P c = true ∨
      ExplicitEngine.KhashCollision khash :=
  Or.inr (khash_collision_is_a_tautology khash)

theorem recomputed_digest_binds_the_recomputed_core_statement_is_trivial
    (khash2 : Verifier.Bytes → Verifier.Root) (c c2 : Verifier.Config) :
    RustCallBoundary.core2 c = RustCallBoundary.core2 c2 ∨
      RustCallBoundary.Khash2Collision khash2 :=
  Or.inr (khash2_collision_is_a_tautology khash2)

/-! ## 7. Localized implies global, localized is not a tautology, and the
relation to the two predicates the adopted tree already localizes -/

theorem index_digest_clash_implies_transcript_collision (thash : Transcript.Hash)
    (s t : Transcript.State) (u v : Verifier.UsedClaims) (h : IndexDigestClash thash s t u v) :
    CommitmentOrder.TranscriptCollision thash :=
  frame_fold_collision_implies_transcript_collision thash s t _ _ h

theorem round_digest_clash_implies_transcript_collision (thash : Transcript.Hash)
    (s t : Transcript.State) (i j : Nat) (m n : Verifier.CoupledMessage)
    (h : RoundDigestClash thash s t i j m n) : CommitmentOrder.TranscriptCollision thash :=
  frame_fold_collision_implies_transcript_collision thash s t _ _ h

theorem index_digest_clash_fails_on_equal_runs (thash : Transcript.Hash) (s : Transcript.State)
    (u : Verifier.UsedClaims) : ¬ IndexDigestClash thash s s u u :=
  frame_fold_collision_fails_on_equal_runs thash s _

theorem round_digest_clash_fails_on_equal_runs (thash : Transcript.Hash) (s : Transcript.State)
    (i : Nat) (m : Verifier.CoupledMessage) : ¬ RoundDigestClash thash s s i i m m :=
  frame_fold_collision_fails_on_equal_runs thash s _

theorem localized_implies_global (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (s t : Transcript.State)
    (ms ns : List OuterInitial.Message) (u v : Verifier.UsedClaims) (i j : Nat)
    (m n : Verifier.CoupledMessage) (c c2 : Verifier.Config) :
    (FrameFoldCollision thash s t ms ns → CommitmentOrder.TranscriptCollision thash) ∧
    (IndexDigestClash thash s t u v → CommitmentOrder.TranscriptCollision thash) ∧
    (RoundDigestClash thash s t i j m n → CommitmentOrder.TranscriptCollision thash) ∧
    (ConfigEncodingCollision khash c c2 → ExplicitEngine.KhashCollision khash) :=
  ⟨frame_fold_collision_implies_transcript_collision thash s t ms ns,
   index_digest_clash_implies_transcript_collision thash s t u v,
   round_digest_clash_implies_transcript_collision thash s t i j m n,
   config_encoding_collision_implies_khash_collision khash c c2⟩

theorem localized_is_not_a_tautology (hash : CommitmentOrder.Hash) (s : Transcript.State)
    (ms : List OuterInitial.Message) (c c2 : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c2) :
    (CommitmentOrder.TranscriptCollision hash ∧ ¬ FrameFoldCollision hash s s ms ms) ∧
    (ExplicitEngine.KhashCollision (separatingKhash (ExplicitEngine.encodeConfig c)) ∧
      ¬ ConfigEncodingCollision (separatingKhash (ExplicitEngine.encodeConfig c)) c c2) :=
  ⟨⟨transcript_collision_is_a_tautology hash,
    frame_fold_collision_fails_on_equal_runs hash s ms⟩,
   ⟨khash_collision_is_a_tautology _,
    config_encoding_collision_fails_for_a_separating_khash c c2 hne⟩⟩

theorem localized_recovers_the_adopted_frame_disjunction (hash : CommitmentOrder.Hash)
    (ms ns : List OuterInitial.Message) (s t : Transcript.State)
    (hlen : ms.length = ns.length)
    (h : (OuterInitial.absorbMessages hash s ms).digest
        = (OuterInitial.absorbMessages hash t ns).digest) :
    (s.digest = t.digest ∧ ms = ns) ∨ CommitmentOrder.TranscriptCollision hash := by
  rcases absorb_messages_bind_or_frame_collision hash ms ns s t hlen h with hl | hcol
  · exact Or.inl hl
  · exact Or.inr (frame_fold_collision_implies_transcript_collision hash s t ms ns hcol)

theorem localized_recovers_the_adopted_deployment_disjunction (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (khash : Verifier.Bytes → Verifier.Root) (P : PinnedWhirProfile.Profile)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hd : CanonicalProofCheck.DeployedFacts gdec khash P pin c₀)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hacc : Integrated.verify (CanonicalProofCheck.pinnedProofEngine gdec hash thash khash P c₀)
      gdec pin chain c p = .ok ()) :
    c = c₀ ∨ ExplicitEngine.KhashCollision khash := by
  rcases accepted_configuration_is_the_deployment_localized gdec hash thash khash P c₀ pin chain
    c p hd hg hw hacc with heq | hcol
  · exact Or.inl heq
  · exact Or.inr (config_encoding_collision_implies_khash_collision khash c c₀ hcol)

def LeafCollision (hash : Spongefish.Hash) (row other : Spongefish.Bytes) : Prop :=
  row ≠ other ∧ hash row = hash other

theorem leaf_collision_implies_row_collision (hash : Spongefish.Hash)
    (row other : Spongefish.Bytes) (h : LeafCollision hash row other) :
    WhirRowBinding.RowCollision hash row other := Or.inl h

theorem row_collision_second_disjunct_gives_every_row_pair (hash : Spongefish.Hash)
    (a b : Spongefish.Bytes) (ha : a.length = 64) (hb : b.length = 64) (hne : a ≠ b)
    (heq : hash a = hash b) :
    ∀ row other : Spongefish.Bytes, WhirRowBinding.RowCollision hash row other :=
  fun _ _ => Or.inr ⟨a, b, ha, hb, hne, heq⟩

theorem no_collision_holds_on_the_empty_list (hash : Spongefish.Hash) :
    OpeningBinding.NoCollision hash [] := by
  intro a ha
  exact absurd ha (by simp)

theorem no_collision_fails_on_a_colliding_pair (hash : Spongefish.Hash)
    (a b : Spongefish.Bytes) (hne : a ≠ b) (heq : hash a = hash b) :
    ¬ OpeningBinding.NoCollision hash [a, b] := by
  intro h
  exact hne (h a (by simp) b (by simp) heq)

/-! ## 8. The row-collision family: `HashCollision` is the same infinite
pigeonhole, `RowCollision`'s second disjunct is a FINITE one, and one adopted
result assumes the negation of a tautology

The Merkle/Spongefish digest is thirty-two bytes packaged with its length proof,
so `merkleDigestEntry` injects it into `Fin 32 → Transcript.Byte` and it is
finite; `Spongefish.Bytes` is infinite, which gives `HashCollision` outright.

For the length-sixty-four disjunct the domain is finite too, so the pigeonhole is
a CARDINALITY comparison rather than an infinite-domain one. It is carried out on
the two function types `Fin 32 → Fin 256` and `Fin 64 → Fin 256` via
`Fintype.card_fun`: neither cardinal is evaluated, no cardinal of a digest TYPE
is taken, and no `Finset` over a digest space appears in any statement here. -/

def merkleDigestEntry (d : Merkle.Digest) (i : Fin 32) : Transcript.Byte :=
  d.1.get ⟨i.val, by rw [d.2]; exact i.isLt⟩

theorem merkle_digest_entry_injective : Function.Injective merkleDigestEntry := by
  intro d e h
  apply Subtype.ext
  refine List.ext_get (by rw [d.2, e.2]) ?_
  intro n h1 h2
  have hn : n < 32 := by rw [d.2] at h1; exact h1
  exact congrFun h ⟨n, hn⟩

instance instFiniteMerkleDigest : Finite Merkle.Digest :=
  Finite.of_injective merkleDigestEntry merkle_digest_entry_injective

theorem hash_collision_is_a_tautology (hash : Spongefish.Hash) :
    WhirRowBinding.HashCollision hash :=
  Finite.exists_ne_map_eq_of_infinite hash

theorem compression_collision_is_a_tautology (hash : Spongefish.Hash) :
    ∃ a b : Spongefish.Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b := by
  have hcard : Fintype.card (Fin 32 → Fin 256) < Fintype.card (Fin 64 → Fin 256) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  obtain ⟨v, w, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun v : Fin 64 → Fin 256 => merkleDigestEntry (hash (List.ofFn v))) hcard
  exact ⟨List.ofFn v, List.ofFn w, List.length_ofFn _, List.length_ofFn _,
    fun h => hne (List.ofFn_injective h), merkle_digest_entry_injective heq⟩

theorem row_collision_is_a_tautology (hash : Spongefish.Hash) (row other : Spongefish.Bytes) :
    WhirRowBinding.RowCollision hash row other :=
  Or.inr (compression_collision_is_a_tautology hash)

theorem no_row_collision_hypothesis_is_unsatisfiable (hash : Spongefish.Hash)
    (row other : WhirRows.RawRow) :
    ¬ ¬ WhirRowBinding.RowCollision hash row.bytes other.bytes :=
  fun h => h (row_collision_is_a_tautology hash row.bytes other.bytes)

theorem row_collision_exposes_actual_hash_inputs_statement_is_trivial (hash : Spongefish.Hash) :
    WhirRowBinding.HashCollision hash :=
  hash_collision_is_a_tautology hash

theorem distinct_accepted_decoded_rows_statement_is_trivial (hash : Spongefish.Hash) :
    WhirRowBinding.HashCollision hash :=
  hash_collision_is_a_tautology hash

theorem distinct_accepted_dot_values_statement_is_trivial (hash : Spongefish.Hash) :
    WhirRowBinding.HashCollision hash :=
  hash_collision_is_a_tautology hash

theorem accepted_raw_rows_bind_or_collision_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem accepted_positions_bind_or_collision_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem accepted_decoded_rows_bind_or_collision_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) (values otherValues : List Spongefish.Ext3) :
    values = otherValues ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem accepted_decoded_dots_bind_or_collision_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) (value otherValue : Arithmetic.Ext3) :
    value = otherValue ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem accepted_full_column_dot_binding_last_conjunct_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) (weights : List Arithmetic.Ext3)
    (values otherValues : List Spongefish.Ext3) :
    WhirTerminal.dot weights (values.map Subtype.val)
        = WhirTerminal.dot weights (otherValues.map Subtype.val) ∨
      WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem accepted_groups_position_rows_bind_or_collision_statement_is_trivial
    (hash : Spongefish.Hash) (row otherRow : WhirRows.RawRow) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem preprocessed_rows_bind_or_collision_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem installed_accepted_rows_bind_finalsplit_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem installed_accepted_rows_bind_round_one_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem opened_dot_binds_or_row_collision_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : WhirRows.RawRow) (value otherValue : Arithmetic.Ext3) :
    value = otherValue ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes :=
  Or.inr (row_collision_is_a_tautology hash row.bytes otherRow.bytes)

theorem path_collision_exposes_hash_collision_statement_is_trivial (hash : Spongefish.Hash) :
    ∃ a b : Spongefish.Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b :=
  compression_collision_is_a_tautology hash

theorem two_accepted_openings_bind_or_compression_collision_statement_is_trivial
    (hash : Spongefish.Hash) (leaf otherLeaf : Merkle.Digest) :
    leaf = otherLeaf ∨
      ∃ a b : Spongefish.Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b :=
  Or.inr (compression_collision_is_a_tautology hash)

theorem accepted_raw_rows_bind_or_hash_collision_statement_is_trivial (hash : Spongefish.Hash)
    (row otherRow : Spongefish.Bytes) :
    row = otherRow ∨ (row ≠ otherRow ∧ hash row = hash otherRow) ∨
      ∃ a b : Spongefish.Bytes, a.length = 64 ∧ b.length = 64 ∧ a ≠ b ∧ hash a = hash b :=
  Or.inr (Or.inr (compression_collision_is_a_tautology hash))

end Audit.Wire3.LocalizedCollisions
