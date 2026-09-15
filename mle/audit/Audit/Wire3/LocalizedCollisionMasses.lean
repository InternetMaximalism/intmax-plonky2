import Audit.Wire3.CommittedTablesClauses
import Audit.Wire3.BirthdayClashBound

/-!
# Explicit random-oracle masses for the two LOCALIZED collision events of the
committed-tables clauses (wire v3)

## HONESTY HEADER — read this before any number below

**ROM, NOT KECCAK.**  Every mass in this module is a COUNTING FACT about the
uniform law on the finite table space `RandomOracleSqueezes.OracleTable Q`,
exactly as the adopted `RandomOracleSqueezes.oracleProbability` writes that law
down.  Nothing here is a statement about keccak256, about Poseidon, or about any
deployed hash.  The deployed verifier does not sample a table; the theorems below
say what the mass of the localized collision events WOULD be if it did.  Reading
`1 / Fintype.card Block` as "the deployed collision probability" is exactly the
substitution this module does NOT license.

**WHICH HASH IS BEING MODELLED.**  The adopted collision predicates live on two
DIFFERENT function types: `LocalizedCollisions.ConfigEncodingCollision` on
`Verifier.Bytes → Verifier.Root`, and `LocalizedCollisions.LeafCollision` on
`Spongefish.Hash = Transcript.Bytes → Merkle.Digest`.  A table `T` presents both
through adopted, PROVED-INJECTIVE re-encodings and nothing else:
`khashOf` is `WhirTail.rootWord ∘ OuterChallenge.digestBlock ∘ hashOf Q T ∘
WhirFinalSpongefish.toTranscriptBytes`, and `leafHashOf` is
`OuterChallenge.digestBlock ∘ hashOf Q T`.  The three re-encodings are injective
(`root_word_injective`, `digest_block_injective`, `to_transcript_bytes_injective`),
so a collision of the presented hash is EXACTLY a collision of the table, and no
mass is gained or lost in the translation.  This is a MODELLING CHOICE: the
deployed `khash` is not `khashOf Q T` for any `Q, T`, and no theorem here claims
it is.

**PER-PAIR VERSUS UNION, AND THE ADVERSARY'S CHOICE ORDER.**  This is the part a
reader must not skim.

* `fixed_pair_collision_mass` and the three degenerate variants are PER-PAIR
  statements at a pair of byte strings FIXED BEFORE THE TABLE IS SAMPLED.  They
  are equalities, and they survive an adaptive adversary only in the sense that
  the pair must be named first.  `config_encoding_collision_mass` and
  `leaf_collision_mass` are the same statement transported along the two
  injections: they too need the pair fixed first.
* An adversary who picks the second configuration AFTER seeing the deployed
  digest is NOT covered by those.  Two statements cover him, and they are not
  equally good.  The CRUDE PER-FAMILY READING is the union over a named finite
  family: `config_family_collision_mass_le` bounds the mass of "SOME member of
  the finite family `F` collides with the deployed `c₀`" by `F.card / |Block|`,
  and `fixed_tables_costs_a_birthday_term_over_a_family` transports it to the
  ROM line.  Those statements are kept below, but `F` is the WRONG SURROGATE and
  the reader should not stop there; see the next bullet for the statement that
  replaces them.
* **WHAT BOUNDS THE ADVERSARY'S CHOICE — AND WHY `F` IS THE WRONG SURROGATE.**
  `Verifier.Config` carries `Nat` and `List` fields, so the submittable
  configurations are NOT a finite type, and no adopted statement cuts them down
  to a `Finset`: acceptance does not, and neither does deployment.
  `CanonicalProofCheck`'s deployment pins the nineteen ENCODED fields and
  `ExplicitEngine.residue_fields_are_not_encoded` leaves six fields outside the
  encoding — but `ExplicitEngine.example_residue_variant_has_the_same_encoding`
  shows the residue variants have the SAME encoding, so they never populate the
  collision event at all (`config_collision_event_is_empty_on_equal_encodings`).
  So reading the union term as `F.card` buys nothing: `F` is a parameter this
  module introduces and the adopted tree never produces.
  The RIGHT surrogate is the QUERY SET.  `any_config_collision_mass_le` bounds
  the fully adaptive event — "SOME configuration AT ALL, quantified over the
  whole of `Verifier.Config`, with no family named anywhere, collides with the
  deployed `c₀`" — by `(Q.card + 1) / |Block|`, assuming only
  `configQuery c₀ ∈ Q`.  The decomposition (`any_config_collision_subset`) is
  this.  A colliding configuration whose encoding query lands IN `Q` is
  re-indexed by `Q.erase (configQuery c₀)`, and each such term costs at most
  `1 / |Block|` by `pair_collision_mass_le`.  A colliding configuration whose
  encoding query lands OUTSIDE `Q` is answered by the adopted off-`Q` default
  `OuterInitial.zeroDigest`, so ALL such configurations — infinitely many of
  them — collapse into the SINGLE fixed event
  `hashOf Q T (configQuery c₀) = OuterInitial.zeroDigest`, whose mass is exactly
  `1 / |Block|` (`zero_sink_event_mass`).  The erased in-`Q` terms plus that one
  sink term are the `Q.card + 1`.
  And `Q` IS bounded in the adopted tree.  `config_query_mem_bounded_queries`
  puts the deployed encoding query inside `BirthdayClashBound.boundedQueries L`
  whenever `L` is at least the encoding length, and
  `any_config_collision_mass_le_at_the_bounded_queries` states the headline right
  there, so the union term is `(BirthdayClashBound.boundedQueries L).card + 1` —
  a quantity the adopted query-length model owns, not a parameter invented here.
* **THE ROW CAVEAT IS MILDER THAN IT LOOKS.**  `opened_rows_collision_mass_le`
  already assumes `hR : R ⊆ Q`, hence `R.card ≤ Q.card`, so `R` was never really
  unbounded either: `opened_rows_collision_mass_le_by_query_size` restates the
  row bound as `Q.card * Q.card / |Block|`, with no row-set parameter left in
  the numerator.  What the adopted tree still does not do is pin the opened-row
  count itself; the WHIR shape and layout pins consumed by
  `CommittedTablesClauses.opened_cells_root_determined_or_collision`
  (`WhirRows.Layout`, `WhirIntermediate.Opening`, and the width/index pins of
  `OpenedDotBinding.executedMerkleInputs`) are not turned into a `Finset`
  cardinality anywhere.  The query-set reading is the one that carries.

**THE DEGENERATE BRANCHES ARE REPORTED, NOT HIDDEN.**  The adopted
`RandomOracleSqueezes.hashOf` answers `OuterInitial.zeroDigest` OFF the query set
`Q`.  So a pair with BOTH strings outside `Q` collides for EVERY table:
`pair_collision_mass_outside` proves the mass is `1`, not `1 / |Block|`.  A pair
with exactly one string outside `Q` still has mass exactly `1 / |Block|`
(`pair_collision_mass_left`, `pair_collision_mass_right`), because the inside
answer must hit one fixed block.  Every union statement below therefore carries a
membership hypothesis, and that hypothesis is proved satisfiable
(`config_query_mem_bounded_queries`, `config_query_mem_set_right`,
`rows_subset_bounded_queries`).

**THE ADDED HYPOTHESES OF THIS CANDIDATE, NAMED.**  The adopted
`CommittedTablesClauses.committed_tables_join_up_to_collisions` takes `khash` as
a BARE function `Verifier.Bytes → Verifier.Root` with NO query-set side
condition of any kind.  So `hc₀ : configQuery c₀ ∈ Q` — which every mass
statement in sections 3 and 5 carries — is an ADDED hypothesis of THIS
candidate, with no adopted counterpart: the adopted lemma neither supplies it
nor needs it, and it only becomes meaningful once the ROM table model of this
module is imposed on top.  It is load-bearing rather than cosmetic:
`pair_collision_mass_outside` proves that the configuration event has mass `1`,
not `1 / |Block|`, when the membership fails on both sides.  This module
discharges it SATISFIABLY (`config_query_mem_bounded_queries` at any
`L` at least the encoding length, `config_query_mem_set_right` at the two-element
`configQuerySet`), but it never discharges it JOINTLY with
`CanonicalProofCheck.DeployedFacts`: no theorem here exhibits one instance
carrying both, so the reader must treat `hc₀` as an assumption of the ROM model
rather than as a fact inherited from the adopted tree.  The same reading applies
to `hR : R ⊆ Q` in section 4 and to `hne` in the per-pair equalities.

**R1b IS UNTOUCHED.**  `CommitmentOrder.CommittedTables` — the extraction join,
clause 1b — is carried as a HYPOTHESIS of `fixed_tables_costs_a_birthday_term`
and its family form, exactly as in `CommittedTablesClauses`.  Nothing here proves
it, weakens it, or supplies it.  The committed-tables join is NOT proved by this
module.

**NOT THE SYSTEM'S SOUNDNESS ERROR.**  `1 / |Block|` and `F.card / |Block|` are
the masses of TWO named events.  They are not the soundness error of the
settlement, not the WHIR soundness error, not a grinding bound, and they do not
compose with anything here.  `fixed_tables_costs_a_birthday_term` bounds the mass
of ONE failure event conditioned on R1b; it is an upper bound on that event and
nothing more.  Note too that `CommittedTablesClauses` itself records that the
collision disjunct is INERT for the two-run tau-table statement
(`tau_table_is_fixed_data_from_r1b_at_the_two_runs_alone` proves the left
disjunct from R1b alone); the birthday term here is genuinely load-bearing only
for the clause-1 join `committed_tables_join_up_to_collisions`, which is what
`fixed_tables_costs_a_birthday_term` is stated against.

**EMPTINESS IS NOT A CLAIM.**  `joinFailureEvent` may well be empty for a given
`(c, p)`; the theorem bounds its mass and does not assert it is inhabited.  The
content is the CONTAINMENT (`join_failure_event_subset`), which is what turns an
unquantified disjunct into a named event.

**THE SECTION-5 NUMBER IS NOT EARNED BY THE COLLISION ANALYSIS.**  This bound is
not earned by the collision analysis: `joinFailureEvent` carries
`CanonicalProofCheck.DeployedFacts` as a CONJUNCT, whose `pinnedDigest` field
pins the table coordinate at `configQuery c₀`, so ANY event containing that
conjunct already has mass at most `1 / |Block|`.  That is proved here rather than
asserted: `deployed_facts_alone_costs_the_whole_birthday_term` takes an ARBITRARY
predicate `X` on tables and bounds the mass of
`{T | DeployedFacts gdec (khashOf Q T) P pin c₀ ∧ X T}` by `1 / |Block|` — take
`X := fun _ => True` and the bound still holds, with no R1b, no word bounds, no
containment, and no collision anywhere.  So the number in
`fixed_tables_costs_a_birthday_term` comes from the CONDITIONING, not from any
collision analysis.  The content of this section is the containment
`join_failure_event_subset`, not the number.

## Disclosure of the local conventions

* `Finset.univ` appears in exactly two definitions, `allTables` and
  `rootWordFiber`, and in no theorem statement; every event below is a `filter`
  or a `biUnion` of `Finset`s built from `allTables`.
* `Fintype.card Block` is used SYMBOLICALLY throughout and is never evaluated,
  never fed to `ring`/`omega`, and never compared to a numeral.
* No unfinished proof, no new postulate, no kernel-bypassing evaluation, and no
  compiler option override anywhere in the module.
* Imports are two adopted `Audit.Wire3` modules; Mathlib enters only through
  them.

## The theorem inventory

Section 1 — the three injections and the two presented hashes.
Section 2 — the per-pair mass: `fixed_pair_collision_mass` (an EQUALITY,
`1 / |Block|`), the two one-sided variants, the degenerate both-outside variant
(mass `1`), and the uniform `pair_collision_mass_le`.
Section 3 — the configuration-encoding event: per-pair equality and bound, the
empty case on equal encodings, the crude per-family union
`config_family_collision_mass_le`, and then the FAMILY-FREE headline
`any_config_collision_mass_le` (`(Q.card + 1) / |Block|` over ALL of
`Verifier.Config`) with its off-`Q` sink `zero_sink_event_mass`.
Section 4 — the leaf event on two named opened rows: per-pair equality and bound,
the union `opened_rows_collision_mass_le` over a row set, and its query-set form
`opened_rows_collision_mass_le_by_query_size`.
Section 5 — the ROM line: `join_failure_event_subset` and
`fixed_tables_costs_a_birthday_term`, plus the family form; then the negative
result `deployed_facts_alone_costs_the_whole_birthday_term`, which shows the
number is bought by the `DeployedFacts` conjunct alone.
Section 6 — non-vacuity: the constant table inhabits every non-degenerate event,
the degenerate branch is exhibited, every membership hypothesis is discharged at
a concrete instance built from `BirthdayClashBound.boundedQueries`, and the
family-free headline is instantiated there
(`any_config_collision_mass_le_at_the_bounded_queries`).
-/

namespace Audit.Wire3.LocalizedCollisionMasses

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The presented hashes, and the three injections that carry masses -/

/-- One oracle answer: the adopted 32-byte block. -/
abbrev Block := RandomOracleSqueezes.Block

/-- The adopted table space over a finite query set. -/
abbrev OracleTable (Q : Finset Transcript.Bytes) := RandomOracleSqueezes.OracleTable Q

/-- **ONE OF THE TWO `Finset.univ`S IN THIS MODULE** (the other is
`rootWordFiber`, in section 5).  The whole table space, as a `Finset`; every
event below is carved out of it. -/
def allTables (Q : Finset Transcript.Bytes) : Finset (OracleTable Q) := Finset.univ

theorem mem_all_tables (Q : Finset Transcript.Bytes) (T : OracleTable Q) :
    T ∈ allTables Q := Finset.mem_univ T

theorem all_tables_card (Q : Finset Transcript.Bytes) :
    (allTables Q).card = Fintype.card (OracleTable Q) := Finset.card_univ

theorem oracle_probability_all_tables (Q : Finset Transcript.Bytes) :
    RandomOracleSqueezes.oracleProbability Q (allTables Q) = 1 := by
  rw [RandomOracleSqueezes.oracleProbability, all_tables_card]
  exact div_self (RandomOracleSqueezes.oracle_card_cast_pos Q).ne'

theorem block_digest_injective : Function.Injective RandomOracleSqueezes.blockDigest := by
  intro x y h
  have hx : OuterChallenge.digestBlock (RandomOracleSqueezes.blockDigest x) = x := rfl
  have hy : OuterChallenge.digestBlock (RandomOracleSqueezes.blockDigest y) = y := rfl
  rw [← hx, ← hy, h]

theorem digest_block_injective : Function.Injective OuterChallenge.digestBlock := by
  intro d e h
  have hd : RandomOracleSqueezes.blockDigest (OuterChallenge.digestBlock d) = d := rfl
  have he : RandomOracleSqueezes.blockDigest (OuterChallenge.digestBlock e) = e := rfl
  rw [← hd, ← he, h]

theorem root_word_injective : Function.Injective WhirTail.rootWord := by
  intro d e h
  apply Subtype.ext
  have hd := WhirTail.root_projection_is_lossless d
  have he := WhirTail.root_projection_is_lossless e
  rw [← hd, ← he, h]

theorem to_transcript_bytes_injective :
    Function.Injective WhirFinalSpongefish.toTranscriptBytes := by
  intro u v h
  have hu := WhirFinalSpongefish.bytes_roundtrip u
  have hv := WhirFinalSpongefish.bytes_roundtrip v
  rw [← hu, ← hv, h]

/-- The Merkle/Spongefish leaf hash a table presents. -/
def leafHashOf (Q : Finset Transcript.Bytes) (T : OracleTable Q) : Spongefish.Hash :=
  fun s => OuterChallenge.digestBlock (RandomOracleSqueezes.hashOf Q T s)

/-- The Solidity-side configuration hash a table presents. -/
def khashOf (Q : Finset Transcript.Bytes) (T : OracleTable Q) :
    Verifier.Bytes → Verifier.Root :=
  fun v => WhirTail.rootWord (OuterChallenge.digestBlock
    (RandomOracleSqueezes.hashOf Q T (WhirFinalSpongefish.toTranscriptBytes v)))

/-- The byte string the presented `khash` actually queries for a configuration. -/
def configQuery (c : Verifier.Config) : Transcript.Bytes :=
  WhirFinalSpongefish.toTranscriptBytes (ExplicitEngine.encodeConfig c)

theorem leaf_hash_of_eq_iff (Q : Finset Transcript.Bytes) (T : OracleTable Q)
    (a b : Spongefish.Bytes) :
    leafHashOf Q T a = leafHashOf Q T b ↔
      RandomOracleSqueezes.hashOf Q T a = RandomOracleSqueezes.hashOf Q T b := by
  constructor
  · intro h
    exact digest_block_injective h
  · intro h
    simp only [leafHashOf, h]

theorem khash_of_eq_iff (Q : Finset Transcript.Bytes) (T : OracleTable Q)
    (u v : Verifier.Bytes) :
    khashOf Q T u = khashOf Q T v ↔
      RandomOracleSqueezes.hashOf Q T (WhirFinalSpongefish.toTranscriptBytes u)
        = RandomOracleSqueezes.hashOf Q T (WhirFinalSpongefish.toTranscriptBytes v) := by
  constructor
  · intro h
    exact digest_block_injective (root_word_injective h)
  · intro h
    simp only [khashOf, h]


/-! ## 2. The per-pair mass at two byte strings FIXED BEFORE THE TABLE -/

theorem block_digest_eq_iff (x : Block) (d : Transcript.Digest) :
    RandomOracleSqueezes.blockDigest x = d ↔ x = OuterChallenge.digestBlock d := by
  constructor
  · intro h
    rw [← h]
    rfl
  · intro h
    rw [h]
    rfl

open Classical in
/-- Every event in this module is carved out of `allTables` by an arbitrary
proposition; this is the single place the classical decidability of that
proposition is used. -/
noncomputable def filterTables (Q : Finset Transcript.Bytes)
    (p : OracleTable Q → Prop) : Finset (OracleTable Q) :=
  (allTables Q).filter p

open Classical in
theorem mem_filter_tables (Q : Finset Transcript.Bytes) (p : OracleTable Q → Prop)
    (T : OracleTable Q) : T ∈ filterTables Q p ↔ p T := by
  rw [filterTables, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_all_tables Q T, h⟩⟩

open Classical in
/-- A union of events over a finite index, with the same convention. -/
noncomputable def unionTables {ι : Type} (Q : Finset Transcript.Bytes) (F : Finset ι)
    (f : ι → Finset (OracleTable Q)) : Finset (OracleTable Q) :=
  F.biUnion f

open Classical in
/-- The union bound, in the adopted counting style. -/
theorem oracle_probability_union_tables_le {ι : Type} (Q : Finset Transcript.Bytes)
    (F : Finset ι) (f : ι → Finset (OracleTable Q)) :
    RandomOracleSqueezes.oracleProbability Q (unionTables Q F f)
      ≤ ∑ i in F, RandomOracleSqueezes.oracleProbability Q (f i) := by
  have hc : ((unionTables Q F f).card : ℚ) ≤ ∑ i in F, ((f i).card : ℚ) := by
    rw [unionTables]
    exact_mod_cast Finset.card_biUnion_le
  simp only [RandomOracleSqueezes.oracleProbability]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hc (RandomOracleSqueezes.oracle_card_cast_pos Q).le

/-- The two-event union bound, in the same counting style.  Used to add the
off-`Q` sink term to the in-`Q` union in section 3. -/
theorem oracle_probability_union_le (Q : Finset Transcript.Bytes)
    (A B : Finset (OracleTable Q)) :
    RandomOracleSqueezes.oracleProbability Q (A ∪ B)
      ≤ RandomOracleSqueezes.oracleProbability Q A
        + RandomOracleSqueezes.oracleProbability Q B := by
  have hc : ((A ∪ B).card : ℚ) ≤ (A.card : ℚ) + (B.card : ℚ) := by
    exact_mod_cast Finset.card_union_le A B
  simp only [RandomOracleSqueezes.oracleProbability]
  rw [← add_div]
  exact div_le_div_of_nonneg_right hc (RandomOracleSqueezes.oracle_card_cast_pos Q).le

/-- **THE EVENT AT A FIXED PAIR.**  The two named strings receive equal answers.
`a` and `b` are parameters: they are fixed before the table is sampled. -/
noncomputable def pairCollisionEvent (Q : Finset Transcript.Bytes)
    (a b : Transcript.Bytes) : Finset (OracleTable Q) :=
  filterTables Q
    (fun T => RandomOracleSqueezes.hashOf Q T a = RandomOracleSqueezes.hashOf Q T b)

theorem mem_pair_collision_event (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (T : OracleTable Q) :
    T ∈ pairCollisionEvent Q a b ↔
      RandomOracleSqueezes.hashOf Q T a = RandomOracleSqueezes.hashOf Q T b := by
  rw [pairCollisionEvent]
  exact mem_filter_tables Q _ T

theorem pair_collision_event_symm (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes) :
    pairCollisionEvent Q a b = pairCollisionEvent Q b a := by
  apply Finset.ext
  intro T
  rw [mem_pair_collision_event, mem_pair_collision_event]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem invariant_at_all_tables (Q : Finset Transcript.Bytes)
    (q : { x : Transcript.Bytes // x ∈ Q }) :
    BirthdayClashBound.InvariantAt Q q (allTables Q) :=
  fun T T2 _ => ⟨fun _ => mem_all_tables Q T2, fun _ => mem_all_tables Q T⟩

/-- Inside `Q` the event is literally "the two coordinates agree". -/
theorem mem_pair_collision_event_inside (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (ha : a ∈ Q) (hb : b ∈ Q) (T : OracleTable Q) :
    T ∈ pairCollisionEvent Q a b ↔ T ⟨a, ha⟩ = T ⟨b, hb⟩ := by
  rw [mem_pair_collision_event, RandomOracleSqueezes.hash_of_at Q T ⟨a, ha⟩,
    RandomOracleSqueezes.hash_of_at Q T ⟨b, hb⟩]
  exact ⟨fun h => block_digest_injective h, fun h => by rw [h]⟩

/-- Outside `Q` the adopted `hashOf` answers `OuterInitial.zeroDigest`. -/
theorem hash_of_outside (Q : Finset Transcript.Bytes) (T : OracleTable Q)
    (a : Transcript.Bytes) (ha : a ∉ Q) :
    RandomOracleSqueezes.hashOf Q T a = OuterInitial.zeroDigest := by
  simp only [RandomOracleSqueezes.hashOf, ha, dif_neg, not_false_iff]

/-- **(1) THE EXACT PER-PAIR COUNT.**  For two DISTINCT strings both in `Q`, the
tables on which they collide are exactly one `|Block|`-th of all tables.  Proved
by the adopted `BirthdayClashBound.adaptive_fresh_step_card` at the singleton
target: the second coordinate is read, the first is fresh. -/
theorem pair_collision_card_inside (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (ha : a ∈ Q) (hb : b ∈ Q) (hne : a ≠ b) :
    (pairCollisionEvent Q a b).card * Fintype.card Block
      = Fintype.card (OracleTable Q) := by
  have hq : (⟨b, hb⟩ : { x : Transcript.Bytes // x ∈ Q }) ≠ ⟨a, ha⟩ := by
    intro h
    exact hne (congrArg Subtype.val h).symm
  have hfresh : BirthdayClashBound.FreshStep Q (allTables Q)
      (fun _ : OracleTable Q => (⟨a, ha⟩ : { x : Transcript.Bytes // x ∈ Q }))
      (fun T : OracleTable Q => ({T ⟨b, hb⟩} : Finset Block)) := by
    refine ⟨fun T _ β => mem_all_tables Q _, fun T _ β => rfl, fun T _ β => ?_⟩
    show ({BirthdayClashBound.reassign T ⟨a, ha⟩ β ⟨b, hb⟩} : Finset Block) = {T ⟨b, hb⟩}
    rw [BirthdayClashBound.reassign_off T ⟨a, ha⟩ ⟨b, hb⟩ β hq]
  have hcard := BirthdayClashBound.adaptive_fresh_step_card hfresh
  have hset : (allTables Q).filter
      (fun T : OracleTable Q => T ⟨a, ha⟩ ∈ ({T ⟨b, hb⟩} : Finset Block))
      = pairCollisionEvent Q a b := by
    apply Finset.ext
    intro T
    rw [Finset.mem_filter, mem_pair_collision_event_inside Q a b ha hb T,
      Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨mem_all_tables Q T, h⟩⟩
  have hsum : (∑ U in allTables Q, ({U ⟨b, hb⟩} : Finset Block).card)
      = Fintype.card (OracleTable Q) := by
    simp only [Finset.card_singleton, Finset.sum_const, smul_eq_mul, Nat.mul_one,
      all_tables_card]
  rw [hset, hsum] at hcard
  exact hcard

/-- **(1) THE PER-PAIR MASS, AS AN EQUALITY.**  Both strings queried, distinct:
mass EXACTLY `1 / |Block|`.  The pair is fixed before the table is sampled. -/
theorem fixed_pair_collision_mass (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (ha : a ∈ Q) (hb : b ∈ Q) (hne : a ≠ b) :
    RandomOracleSqueezes.oracleProbability Q (pairCollisionEvent Q a b)
      = 1 / (Fintype.card Block : ℚ) := by
  have hc : ((pairCollisionEvent Q a b).card : ℚ) * (Fintype.card Block : ℚ)
      = (Fintype.card (OracleTable Q) : ℚ) := by
    exact_mod_cast pair_collision_card_inside Q a b ha hb hne
  rw [RandomOracleSqueezes.oracleProbability,
    div_eq_div_iff (RandomOracleSqueezes.oracle_card_cast_pos Q).ne'
      BirthdayClashBound.block_card_cast_ne, one_mul]
  exact hc

/-- **(1) DEGENERATE BRANCH, ONE SIDE OUT.**  The string outside `Q` is answered
by the fixed default, so the inside coordinate must hit ONE fixed block: the mass
is again exactly `1 / |Block|`. -/
theorem pair_collision_mass_left (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (ha : a ∈ Q) (hb : b ∉ Q) :
    RandomOracleSqueezes.oracleProbability Q (pairCollisionEvent Q a b)
      = 1 / (Fintype.card Block : ℚ) := by
  have hset : pairCollisionEvent Q a b
      = (allTables Q).filter (fun T : OracleTable Q =>
          T ⟨a, ha⟩ = OuterChallenge.digestBlock OuterInitial.zeroDigest) := by
    apply Finset.ext
    intro T
    rw [mem_pair_collision_event, Finset.mem_filter,
      RandomOracleSqueezes.hash_of_at Q T ⟨a, ha⟩, hash_of_outside Q T b hb,
      block_digest_eq_iff]
    exact ⟨fun h => ⟨mem_all_tables Q T, h⟩, fun h => h.2⟩
  rw [hset, BirthdayClashBound.fresh_coordinate_probability (invariant_at_all_tables Q ⟨a, ha⟩),
    oracle_probability_all_tables]

theorem pair_collision_mass_right (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (ha : a ∉ Q) (hb : b ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q (pairCollisionEvent Q a b)
      = 1 / (Fintype.card Block : ℚ) := by
  rw [pair_collision_event_symm]
  exact pair_collision_mass_left Q b a hb ha

/-- **(1) THE HONEST DEGENERATE BRANCH.**  Both strings outside `Q`: the adopted
`hashOf` gives them the SAME default answer for every table, so the event is
everything and the mass is `1`.  This is why every union statement below carries
a membership hypothesis. -/
theorem pair_collision_mass_outside (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (ha : a ∉ Q) (hb : b ∉ Q) :
    RandomOracleSqueezes.oracleProbability Q (pairCollisionEvent Q a b) = 1 := by
  have hset : pairCollisionEvent Q a b = allTables Q := by
    apply Finset.ext
    intro T
    rw [mem_pair_collision_event, hash_of_outside Q T a ha, hash_of_outside Q T b hb]
    exact ⟨fun _ => mem_all_tables Q T, fun _ => rfl⟩
  rw [hset, oracle_probability_all_tables]

/-- **(1) THE UNIFORM PER-PAIR BOUND.**  One membership suffices for
`≤ 1 / |Block|`; it is an equality in each of the three non-degenerate cases. -/
theorem pair_collision_mass_le (Q : Finset Transcript.Bytes) (a b : Transcript.Bytes)
    (hmem : a ∈ Q ∨ b ∈ Q) (hne : a ≠ b) :
    RandomOracleSqueezes.oracleProbability Q (pairCollisionEvent Q a b)
      ≤ 1 / (Fintype.card Block : ℚ) := by
  rcases hmem with ha | hb
  · by_cases hb : b ∈ Q
    · exact le_of_eq (fixed_pair_collision_mass Q a b ha hb hne)
    · exact le_of_eq (pair_collision_mass_left Q a b ha hb)
  · by_cases ha : a ∈ Q
    · exact le_of_eq (fixed_pair_collision_mass Q a b ha hb hne)
    · exact le_of_eq (pair_collision_mass_right Q a b ha hb)

theorem one_div_block_card_nonneg :
    (0 : ℚ) ≤ 1 / (Fintype.card Block : ℚ) :=
  le_of_lt (div_pos one_pos BirthdayClashBound.block_card_cast_pos)

theorem empty_event_mass (Q : Finset Transcript.Bytes) :
    RandomOracleSqueezes.oracleProbability Q (∅ : Finset (OracleTable Q)) = 0 := by
  rw [RandomOracleSqueezes.oracleProbability, Finset.card_empty, Nat.cast_zero, zero_div]

/-! ## 3. The configuration-encoding collision -/

/-- **THE ADOPTED EVENT (i), AS A `Finset` OF TABLES.**  `c` and `c₀` are fixed
parameters: this is the PER-PAIR form. -/
noncomputable def configCollisionEvent (Q : Finset Transcript.Bytes)
    (c c₀ : Verifier.Config) : Finset (OracleTable Q) :=
  filterTables Q (fun T => LocalizedCollisions.ConfigEncodingCollision (khashOf Q T) c c₀)

theorem mem_config_collision_event (Q : Finset Transcript.Bytes) (c c₀ : Verifier.Config)
    (T : OracleTable Q) :
    T ∈ configCollisionEvent Q c c₀ ↔
      LocalizedCollisions.ConfigEncodingCollision (khashOf Q T) c c₀ := by
  rw [configCollisionEvent]
  exact mem_filter_tables Q _ T

/-- On equal encodings the event is EMPTY: the adopted predicate's first conjunct
already fails.  This is exactly the residue family
(`ExplicitEngine.example_residue_variant_has_the_same_encoding`). -/
theorem config_collision_event_is_empty_on_equal_encodings (Q : Finset Transcript.Bytes)
    (c c₀ : Verifier.Config)
    (heq : ExplicitEngine.encodeConfig c = ExplicitEngine.encodeConfig c₀) :
    configCollisionEvent Q c c₀ = (∅ : Finset (OracleTable Q)) := by
  apply Finset.ext
  intro T
  rw [mem_config_collision_event]
  constructor
  · intro h
    exact absurd heq h.1
  · intro h
    exact absurd h (Finset.not_mem_empty T)

theorem config_query_ne (c c₀ : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c₀) :
    configQuery c ≠ configQuery c₀ := by
  intro h
  exact hne (to_transcript_bytes_injective h)

/-- The event (i) IS the fixed-pair event at the two encoding queries. -/
theorem config_collision_event_eq (Q : Finset Transcript.Bytes) (c c₀ : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c₀) :
    configCollisionEvent Q c c₀ = pairCollisionEvent Q (configQuery c) (configQuery c₀) := by
  apply Finset.ext
  intro T
  rw [mem_config_collision_event, mem_pair_collision_event]
  constructor
  · intro h
    exact (khash_of_eq_iff Q T (ExplicitEngine.encodeConfig c)
      (ExplicitEngine.encodeConfig c₀)).mp h.2
  · intro h
    exact ⟨hne, (khash_of_eq_iff Q T (ExplicitEngine.encodeConfig c)
      (ExplicitEngine.encodeConfig c₀)).mpr h⟩

/-- **(2) THE PER-PAIR CONFIGURATION MASS, AS AN EQUALITY.**  A FIXED deployed
`c₀` and a FIXED accepted `c` with different encodings, both encoding queries in
`Q`: the mass is exactly `1 / |Block|`. -/
theorem config_encoding_collision_mass (Q : Finset Transcript.Bytes)
    (c c₀ : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c₀)
    (hc : configQuery c ∈ Q) (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q (configCollisionEvent Q c c₀)
      = 1 / (Fintype.card Block : ℚ) := by
  rw [config_collision_event_eq Q c c₀ hne]
  exact fixed_pair_collision_mass Q (configQuery c) (configQuery c₀) hc hc₀
    (config_query_ne c c₀ hne)

/-- **(2) THE PER-PAIR CONFIGURATION BOUND.**  Only the DEPLOYED configuration's
encoding query has to be in `Q` -- which is what deployment does -- and the
hypothesis on the encodings is discharged internally, so this form applies to
every submitted `c`. -/
theorem config_encoding_collision_mass_le (Q : Finset Transcript.Bytes)
    (c c₀ : Verifier.Config) (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q (configCollisionEvent Q c c₀)
      ≤ 1 / (Fintype.card Block : ℚ) := by
  by_cases heq : ExplicitEngine.encodeConfig c = ExplicitEngine.encodeConfig c₀
  · rw [config_collision_event_is_empty_on_equal_encodings Q c c₀ heq, empty_event_mass]
    exact one_div_block_card_nonneg
  · rw [config_collision_event_eq Q c c₀ heq]
    exact pair_collision_mass_le Q (configQuery c) (configQuery c₀) (Or.inr hc₀)
      (config_query_ne c c₀ heq)

/-- **THE UNION EVENT.**  "SOME configuration in the finite family `F` collides
with the deployed `c₀`."  `F` is a PARAMETER: see the honesty header on why the
adopted model does not produce one. -/
noncomputable def configFamilyCollisionEvent (Q : Finset Transcript.Bytes)
    (F : Finset Verifier.Config) (c₀ : Verifier.Config) : Finset (OracleTable Q) :=
  unionTables Q F (fun c => configCollisionEvent Q c c₀)

/-- **(2) THE UNION READING -- the adversary picks `c` AFTER seeing the digest.**
The mass of "some member of `F` collides with `c₀`" is at most `F.card / |Block|`.
This is the statement that survives adaptive choice WITHIN `F`; the per-pair
equality above does not. -/
theorem config_family_collision_mass_le (Q : Finset Transcript.Bytes)
    (F : Finset Verifier.Config) (c₀ : Verifier.Config) (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q (configFamilyCollisionEvent Q F c₀)
      ≤ (F.card : ℚ) / (Fintype.card Block : ℚ) := by
  rw [configFamilyCollisionEvent]
  refine le_trans (oracle_probability_union_tables_le Q F
    (fun c => configCollisionEvent Q c c₀)) ?_
  refine le_trans (Finset.sum_le_sum
    (fun c _ => config_encoding_collision_mass_le Q c c₀ hc₀)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-! ### 3b. The family-free reading: the QUERY SET, not a family, is the surrogate

The statements above take a `Finset Verifier.Config` as a parameter, and nothing
in the adopted tree produces one.  The statements below need no family at all.
-/

open Classical in
/-- **THE OFF-`Q` SINK.**  The adopted `RandomOracleSqueezes.hashOf` answers
`OuterInitial.zeroDigest` off `Q`, so EVERY configuration whose encoding query
misses `Q` collides with the deployed `c₀` exactly on this one event.  It is a
single event, not a union: that is why infinitely many off-`Q` configurations
cost one term and not one term each. -/
noncomputable def zeroSinkEvent (Q : Finset Transcript.Bytes) (c₀ : Verifier.Config) :
    Finset (OracleTable Q) :=
  filterTables Q (fun T =>
    RandomOracleSqueezes.hashOf Q T (configQuery c₀) = OuterInitial.zeroDigest)

/-- The off-`Q` sink has mass exactly `1 / |Block|` once the deployed encoding
query is in `Q`: the read coordinate must hit the one fixed default block. -/
theorem zero_sink_event_mass (Q : Finset Transcript.Bytes) (c₀ : Verifier.Config)
    (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q (zeroSinkEvent Q c₀)
      = 1 / (Fintype.card Block : ℚ) := by
  have hset : zeroSinkEvent Q c₀
      = (allTables Q).filter (fun T : OracleTable Q =>
          T ⟨configQuery c₀, hc₀⟩ = OuterChallenge.digestBlock OuterInitial.zeroDigest) := by
    apply Finset.ext
    intro T
    rw [zeroSinkEvent, mem_filter_tables, Finset.mem_filter,
      RandomOracleSqueezes.hash_of_at Q T ⟨configQuery c₀, hc₀⟩, block_digest_eq_iff]
    exact ⟨fun h => ⟨mem_all_tables Q T, h⟩, fun h => h.2⟩
  rw [hset,
    BirthdayClashBound.fresh_coordinate_probability
      (invariant_at_all_tables Q ⟨configQuery c₀, hc₀⟩),
    oracle_probability_all_tables]

open Classical in
/-- **THE FULLY ADAPTIVE EVENT, WITH NO FAMILY NAMED.**  "SOME configuration at
all — quantified over the whole of `Verifier.Config` — collides with the deployed
`c₀`."  No `Finset Verifier.Config` appears anywhere in this definition. -/
noncomputable def anyConfigCollisionEvent (Q : Finset Transcript.Bytes)
    (c₀ : Verifier.Config) : Finset (OracleTable Q) :=
  filterTables Q (fun T => ∃ c : Verifier.Config,
    LocalizedCollisions.ConfigEncodingCollision (khashOf Q T) c c₀)

theorem mem_any_config_collision_event (Q : Finset Transcript.Bytes)
    (c₀ : Verifier.Config) (T : OracleTable Q) :
    T ∈ anyConfigCollisionEvent Q c₀ ↔
      ∃ c : Verifier.Config, LocalizedCollisions.ConfigEncodingCollision (khashOf Q T) c c₀ := by
  rw [anyConfigCollisionEvent]
  exact mem_filter_tables Q _ T

/-- **THE DECOMPOSITION.**  A colliding configuration whose encoding query lands
IN `Q` is re-indexed by `Q.erase (configQuery c₀)` — the erase is legitimate
because distinct encodings give distinct queries (`config_query_ne`).  A
colliding configuration whose encoding query lands OUTSIDE `Q` gets the adopted
default answer, so it forces the deployed coordinate to that same default: all of
them collapse into the single `zeroSinkEvent`. -/
theorem any_config_collision_subset (Q : Finset Transcript.Bytes) (c₀ : Verifier.Config) :
    anyConfigCollisionEvent Q c₀
      ⊆ unionTables Q (Q.erase (configQuery c₀))
          (fun a => pairCollisionEvent Q a (configQuery c₀)) ∪ zeroSinkEvent Q c₀ := by
  intro T hT
  obtain ⟨c, hne, hcol⟩ := (mem_any_config_collision_event Q c₀ T).mp hT
  have hpair : RandomOracleSqueezes.hashOf Q T (configQuery c)
      = RandomOracleSqueezes.hashOf Q T (configQuery c₀) :=
    (khash_of_eq_iff Q T (ExplicitEngine.encodeConfig c)
      (ExplicitEngine.encodeConfig c₀)).mp hcol
  have hq : configQuery c ≠ configQuery c₀ := config_query_ne c c₀ hne
  by_cases hmem : configQuery c ∈ Q
  · refine Finset.mem_union_left _ ?_
    rw [unionTables]
    exact Finset.mem_biUnion.mpr ⟨configQuery c, Finset.mem_erase.mpr ⟨hq, hmem⟩,
      (mem_pair_collision_event Q _ _ T).mpr hpair⟩
  · refine Finset.mem_union_right _ ?_
    rw [zeroSinkEvent, mem_filter_tables]
    rw [← hpair]
    exact hash_of_outside Q T (configQuery c) hmem

/-- **(2) THE ADAPTIVE BOUND THAT NAMES NO FAMILY — THE HEADLINE OF SECTION 3.**
The mass of "the adversary finds ANY configuration whatsoever colliding with the
deployed `c₀`" is at most `(Q.card + 1) / |Block|`, given only that the deployed
encoding query is in `Q`.  The surrogate for the adversary's freedom is the QUERY
SET, not a `Finset Verifier.Config`; `config_family_collision_mass_le` above is
the crude per-family reading of the same phenomenon, and it is strictly weaker
because nothing in the adopted tree bounds its `F`.  For the instantiation at the
adopted bounded query set see
`any_config_collision_mass_le_at_the_bounded_queries` in section 6. -/
theorem any_config_collision_mass_le (Q : Finset Transcript.Bytes) (c₀ : Verifier.Config)
    (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q (anyConfigCollisionEvent Q c₀)
      ≤ ((Q.card : ℚ) + 1) / (Fintype.card Block : ℚ) := by
  refine le_trans (RandomOracleSqueezes.oracle_probability_mono Q _ _
    (any_config_collision_subset Q c₀)) ?_
  refine le_trans (oracle_probability_union_le Q _ _) ?_
  have hU : RandomOracleSqueezes.oracleProbability Q
      (unionTables Q (Q.erase (configQuery c₀))
        (fun a => pairCollisionEvent Q a (configQuery c₀)))
      ≤ ((Q.erase (configQuery c₀)).card : ℚ) / (Fintype.card Block : ℚ) := by
    refine le_trans (oracle_probability_union_tables_le Q _ _) ?_
    have hterm : ∀ a ∈ Q.erase (configQuery c₀),
        RandomOracleSqueezes.oracleProbability Q (pairCollisionEvent Q a (configQuery c₀))
          ≤ 1 / (Fintype.card Block : ℚ) := by
      intro a ha
      exact pair_collision_mass_le Q a (configQuery c₀) (Or.inr hc₀)
        (Finset.mem_erase.mp ha).1
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [zero_sink_event_mass Q c₀ hc₀]
  have hcard : ((Q.erase (configQuery c₀)).card : ℚ) ≤ (Q.card : ℚ) := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  have hstep : ((Q.erase (configQuery c₀)).card : ℚ) / (Fintype.card Block : ℚ)
      ≤ (Q.card : ℚ) / (Fintype.card Block : ℚ) :=
    div_le_div_of_nonneg_right hcard BirthdayClashBound.block_card_cast_pos.le
  have hsplit : ((Q.card : ℚ) + 1) / (Fintype.card Block : ℚ)
      = (Q.card : ℚ) / (Fintype.card Block : ℚ) + 1 / (Fintype.card Block : ℚ) := by
    rw [add_div]
  rw [hsplit]
  exact add_le_add (le_trans hU hstep) le_rfl

/-- The family-free bound DOMINATES the per-family one whenever the family's
encoding queries are inside `Q`: the family event sits inside the family-free
event, so the crude reading can be discarded without loss. -/
theorem config_family_collision_event_subset_any (Q : Finset Transcript.Bytes)
    (F : Finset Verifier.Config) (c₀ : Verifier.Config) :
    configFamilyCollisionEvent Q F c₀ ⊆ anyConfigCollisionEvent Q c₀ := by
  intro T hT
  rw [configFamilyCollisionEvent, unionTables] at hT
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hT
  exact (mem_any_config_collision_event Q c₀ T).mpr
    ⟨c, (mem_config_collision_event Q c c₀ T).mp hc⟩

/-! ## 4. The leaf collision on two NAMED opened rows -/

/-- **THE ADOPTED EVENT (ii), AS A `Finset` OF TABLES.**  `row` and `other` are
the two rows the adopted binding lemma
`CommittedTablesClauses.opened_cells_root_determined_or_collision` NAMES; they are
a fixed pair per run. -/
noncomputable def leafCollisionEvent (Q : Finset Transcript.Bytes)
    (row other : Spongefish.Bytes) : Finset (OracleTable Q) :=
  filterTables Q (fun T => LocalizedCollisions.LeafCollision (leafHashOf Q T) row other)

theorem mem_leaf_collision_event (Q : Finset Transcript.Bytes)
    (row other : Spongefish.Bytes) (T : OracleTable Q) :
    T ∈ leafCollisionEvent Q row other ↔
      LocalizedCollisions.LeafCollision (leafHashOf Q T) row other := by
  rw [leafCollisionEvent]
  exact mem_filter_tables Q _ T

theorem leaf_collision_event_is_empty_on_equal_rows (Q : Finset Transcript.Bytes)
    (row : Spongefish.Bytes) :
    leafCollisionEvent Q row row = (∅ : Finset (OracleTable Q)) := by
  apply Finset.ext
  intro T
  rw [mem_leaf_collision_event]
  constructor
  · intro h
    exact absurd rfl h.1
  · intro h
    exact absurd h (Finset.not_mem_empty T)

theorem leaf_collision_event_eq (Q : Finset Transcript.Bytes)
    (row other : Spongefish.Bytes) (hne : row ≠ other) :
    leafCollisionEvent Q row other = pairCollisionEvent Q row other := by
  apply Finset.ext
  intro T
  rw [mem_leaf_collision_event, mem_pair_collision_event]
  constructor
  · intro h
    exact (leaf_hash_of_eq_iff Q T row other).mp h.2
  · intro h
    exact ⟨hne, (leaf_hash_of_eq_iff Q T row other).mpr h⟩

/-- **(2b) THE PER-PAIR LEAF MASS, AS AN EQUALITY.**  The two named rows, both
queried, distinct: mass exactly `1 / |Block|`. -/
theorem leaf_collision_mass (Q : Finset Transcript.Bytes) (row other : Spongefish.Bytes)
    (hrow : row ∈ Q) (hother : other ∈ Q) (hne : row ≠ other) :
    RandomOracleSqueezes.oracleProbability Q (leafCollisionEvent Q row other)
      = 1 / (Fintype.card Block : ℚ) := by
  rw [leaf_collision_event_eq Q row other hne]
  exact fixed_pair_collision_mass Q row other hrow hother hne

/-- **(2b) THE PER-PAIR LEAF BOUND**, with the equal-rows case discharged
internally. -/
theorem leaf_collision_mass_le (Q : Finset Transcript.Bytes) (row other : Spongefish.Bytes)
    (hmem : row ∈ Q ∨ other ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q (leafCollisionEvent Q row other)
      ≤ 1 / (Fintype.card Block : ℚ) := by
  by_cases hne : row = other
  · subst hne
    rw [leaf_collision_event_is_empty_on_equal_rows, empty_event_mass]
    exact one_div_block_card_nonneg
  · rw [leaf_collision_event_eq Q row other hne]
    exact pair_collision_mass_le Q row other hmem hne

/-- The ordered pairs of distinct rows drawn from a row set. -/
def distinctRowPairs (R : Finset Spongefish.Bytes) :
    Finset (Spongefish.Bytes × Spongefish.Bytes) :=
  (R ×ˢ R).filter (fun z => z.1 ≠ z.2)

theorem distinct_row_pairs_card_le (R : Finset Spongefish.Bytes) :
    (distinctRowPairs R).card ≤ R.card * R.card := by
  rw [distinctRowPairs, ← Finset.card_product R R]
  exact Finset.card_filter_le _ _

theorem mem_distinct_row_pairs (R : Finset Spongefish.Bytes)
    (z : Spongefish.Bytes × Spongefish.Bytes) (hz : z ∈ distinctRowPairs R) :
    z.1 ∈ R ∧ z.2 ∈ R ∧ z.1 ≠ z.2 := by
  rw [distinctRowPairs, Finset.mem_filter] at hz
  exact ⟨(Finset.mem_product.mp hz.1).1, (Finset.mem_product.mp hz.1).2, hz.2⟩

/-- **THE UNION EVENT OVER THE ROWS A RUN OPENS.**  "SOME ordered pair of
distinct rows drawn from `R` collides."  `R` is a PARAMETER: see the honesty
header on what does and does not bound it in the adopted tree. -/
noncomputable def openedRowsCollisionEvent (Q : Finset Transcript.Bytes)
    (R : Finset Spongefish.Bytes) : Finset (OracleTable Q) :=
  unionTables Q (distinctRowPairs R) (fun z => leafCollisionEvent Q z.1 z.2)

/-- **(2b) THE UNION READING FOR THE OPENED ROWS.**  With every opened row among
the queried strings, the mass of "some two distinct opened rows collide" is at
most `R.card * R.card / |Block|`.  The bound is the crude ordered-pair count; the
unordered count would halve it, and is not needed for an upper bound. -/
theorem opened_rows_collision_mass_le (Q : Finset Transcript.Bytes)
    (R : Finset Spongefish.Bytes) (hR : R ⊆ Q) :
    RandomOracleSqueezes.oracleProbability Q (openedRowsCollisionEvent Q R)
      ≤ ((R.card : ℚ) * (R.card : ℚ)) / (Fintype.card Block : ℚ) := by
  rw [openedRowsCollisionEvent]
  refine le_trans (oracle_probability_union_tables_le Q (distinctRowPairs R)
    (fun z => leafCollisionEvent Q z.1 z.2)) ?_
  have hterm : ∀ z ∈ distinctRowPairs R,
      RandomOracleSqueezes.oracleProbability Q (leafCollisionEvent Q z.1 z.2)
        ≤ 1 / (Fintype.card Block : ℚ) := by
    intro z hz
    exact leaf_collision_mass_le Q z.1 z.2 (Or.inl (hR (mem_distinct_row_pairs R z hz).1))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hle : ((distinctRowPairs R).card : ℚ) ≤ (R.card : ℚ) * (R.card : ℚ) := by
    exact_mod_cast distinct_row_pairs_card_le R
  exact div_le_div_of_nonneg_right hle BirthdayClashBound.block_card_cast_pos.le

/-- **(2b) THE ROW BOUND WITH NO ROW-SET PARAMETER IN THE NUMERATOR.**  The
hypothesis `R ⊆ Q` that `opened_rows_collision_mass_le` already carries gives
`R.card ≤ Q.card` for free, so the row set was never really an unbounded
parameter: the QUERY SET bounds it, exactly as in section 3b.  This is the row
analogue of `any_config_collision_mass_le`. -/
theorem opened_rows_collision_mass_le_by_query_size (Q : Finset Transcript.Bytes)
    (R : Finset Spongefish.Bytes) (hR : R ⊆ Q) :
    RandomOracleSqueezes.oracleProbability Q (openedRowsCollisionEvent Q R)
      ≤ ((Q.card : ℚ) * (Q.card : ℚ)) / (Fintype.card Block : ℚ) := by
  refine le_trans (opened_rows_collision_mass_le Q R hR) ?_
  have hcard : (R.card : ℚ) ≤ (Q.card : ℚ) := by
    exact_mod_cast Finset.card_le_card hR
  refine div_le_div_of_nonneg_right ?_ BirthdayClashBound.block_card_cast_pos.le
  exact mul_le_mul hcard hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ## 5. The consequence for the ROM line -/

/-- **THE FAILURE EVENT OF THE CLAUSE-1 JOIN, AT A TABLE-PRESENTED `khash`.**  The
tables at which the deployment facts and the acceptance both hold and the adopted
`CommittedTablesJoin` nevertheless FAILS.  R1b is NOT part of this event: it is a
hypothesis of the theorems below, exactly as in `CommittedTablesClauses`. -/
noncomputable def joinFailureEvent (Q : Finset Transcript.Bytes)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : PinnedWhirProfile.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening) :
    Finset (OracleTable Q) :=
  filterTables Q (fun T =>
    CanonicalProofCheck.DeployedFacts gdec (khashOf Q T) P pin c₀ ∧
    Integrated.verify
        (CanonicalProofCheck.pinnedProofEngine gdec hash thash (khashOf Q T) P c₀)
        gdec pin chain c p = .ok () ∧
    ¬ CommitmentOrderSurvey.CommittedTablesJoin tablesOf thash c c₀ pin extract p roots opening)

theorem mem_join_failure_event (Q : Finset Transcript.Bytes)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : PinnedWhirProfile.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (T : OracleTable Q) :
    T ∈ joinFailureEvent Q tablesOf gdec hash thash P c₀ pin chain c p extract roots opening ↔
      (CanonicalProofCheck.DeployedFacts gdec (khashOf Q T) P pin c₀ ∧
        Integrated.verify
            (CanonicalProofCheck.pinnedProofEngine gdec hash thash (khashOf Q T) P c₀)
            gdec pin chain c p = .ok () ∧
        ¬ CommitmentOrderSurvey.CommittedTablesJoin tablesOf thash c c₀ pin extract p roots
          opening) := by
  rw [joinFailureEvent]
  exact mem_filter_tables Q _ T

/-- **(3) THE CONTAINMENT -- this is the content.**  Under R1b and the two word
bounds, every table at which the clause-1 join FAILS is a table at which the
localized configuration-encoding collision HOLDS.  The unquantified disjunct of
`CommittedTablesClauses.committed_tables_join_up_to_collisions` is thereby
replaced by a NAMED event. -/
theorem join_failure_event_subset (Q : Finset Transcript.Bytes)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : PinnedWhirProfile.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hr1b : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract roots opening).tables) :
    joinFailureEvent Q tablesOf gdec hash thash P c₀ pin chain c p extract roots opening
      ⊆ configCollisionEvent Q c c₀ := by
  intro T hT
  obtain ⟨hd, hacc, hfail⟩ := (mem_join_failure_event Q tablesOf gdec hash thash P c₀ pin chain
    c p extract roots opening T).mp hT
  rcases CommittedTablesClauses.committed_tables_join_up_to_collisions tablesOf gdec hash thash
    (khashOf Q T) P c₀ pin chain c p extract roots opening hd hg hw hacc hr1b with hjoin | hcol
  · exact absurd hjoin hfail
  · exact (mem_config_collision_event Q c c₀ T).mpr hcol

/-- **(3) THE ROM LINE WITH A NAMED BIRTHDAY TERM.**  R1b IS A HYPOTHESIS AND IS
NOT CLAIMED.  Given R1b at the run, the tables at which the adopted clause-1 join
fails form an event of mass at most `1 / |Block|`.  This is the per-pair reading:
the submitted `c` is fixed before the table.  For the adaptive reading see
`fixed_tables_costs_a_birthday_term_over_a_family` (the crude per-family form) and
`any_config_collision_mass_le` (the family-free form).

**THIS BOUND IS NOT EARNED BY THE COLLISION ANALYSIS.**  `joinFailureEvent`
carries `CanonicalProofCheck.DeployedFacts` as a CONJUNCT, whose `pinnedDigest`
field pins the table coordinate at `configQuery c₀`, so ANY event containing that
conjunct already has mass at most `1 / |Block|` —
`deployed_facts_alone_costs_the_whole_birthday_term` below proves it for an
arbitrary second conjunct, with no R1b, no word bounds and no collision anywhere.
The content of this section is the containment `join_failure_event_subset`, not
the number. -/
theorem fixed_tables_costs_a_birthday_term (Q : Finset Transcript.Bytes)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : PinnedWhirProfile.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (hg : c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : c.whirEncoding.length < ExplicitEngine.wordBound)
    (hr1b : CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract roots opening).tables)
    (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q
        (joinFailureEvent Q tablesOf gdec hash thash P c₀ pin chain c p extract roots opening)
      ≤ 1 / (Fintype.card Block : ℚ) :=
  le_trans
    (RandomOracleSqueezes.oracle_probability_mono Q _ _
      (join_failure_event_subset Q tablesOf gdec hash thash P c₀ pin chain c p extract roots
        opening hg hw hr1b))
    (config_encoding_collision_mass_le Q c c₀ hc₀)

/-- **(3) THE SAME, OVER A FAMILY OF SUBMITTABLE CONFIGURATIONS.**  With R1b
assumed at every member of `F` (never proved), the mass of "the join fails for
SOME configuration the adversary may submit out of `F`" is at most
`F.card / |Block|`.  `F` is a parameter; nothing here bounds it. -/
theorem fixed_tables_costs_a_birthday_term_over_a_family (Q : Finset Transcript.Bytes)
    (tablesOf : Verifier.Root → Verifier.Root → GateSuffixPolynomial.Tables)
    (gdec : Integrated.DecodeGates) (hash : Spongefish.Hash) (thash : Transcript.Hash)
    (P : PinnedWhirProfile.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (F : Finset Verifier.Config) (p : Verifier.Proof)
    (extract : List Spongefish.Digest → WhirIntermediate.Opening → Fin 5 →
      List (List Element))
    (roots : List Spongefish.Digest) (opening : WhirIntermediate.Opening)
    (hg : ∀ c ∈ F, c.gatesEncoding.length < ExplicitEngine.wordBound)
    (hw : ∀ c ∈ F, c.whirEncoding.length < ExplicitEngine.wordBound)
    (hr1b : ∀ c ∈ F, CommitmentOrder.CommittedTables tablesOf (Verifier.statement p)
      (ExtractorConstruction.extractedState thash c p extract roots opening).tables)
    (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q
        (unionTables Q F (fun c => joinFailureEvent Q tablesOf gdec hash thash P c₀ pin chain c p
          extract roots opening))
      ≤ (F.card : ℚ) / (Fintype.card Block : ℚ) := by
  refine le_trans (oracle_probability_union_tables_le Q F
    (fun c => joinFailureEvent Q tablesOf gdec hash thash P c₀ pin chain c p extract roots
      opening)) ?_
  refine le_trans (Finset.sum_le_sum (fun c hc =>
    fixed_tables_costs_a_birthday_term Q tablesOf gdec hash thash P c₀ pin chain c p extract
      roots opening (hg c hc) (hw c hc) (hr1b c hc) hc₀)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-! ### 5b. Where the section-5 number actually comes from — an honest negative
result

`joinFailureEvent` conditions on `CanonicalProofCheck.DeployedFacts`, and that
structure's `pinnedDigest` field equates `pin.configDigest` with the presented
`khash` at the deployed encoding.  Since the presented `khash` at that encoding IS
the root word of one table coordinate, the conjunct pins that coordinate into a
fibre of `WhirTail.rootWord`, and the fibre has at most one element.  So the
`1 / |Block|` of `fixed_tables_costs_a_birthday_term` is bought by the
conditioning alone.
-/

open Classical in
/-- The fibre of the adopted root projection over one root word.  This is the
SECOND and last `Finset.univ` in this module, and it is a definition rather than
a theorem statement. -/
noncomputable def rootWordFiber (r : Verifier.Root) : Finset Block :=
  (Finset.univ : Finset Block).filter (fun β => WhirTail.rootWord β = r)

theorem mem_root_word_fiber (r : Verifier.Root) (β : Block) :
    β ∈ rootWordFiber r ↔ WhirTail.rootWord β = r := by
  rw [rootWordFiber, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The fibre carries at most one block, by `root_word_injective`. -/
theorem root_word_fiber_card_le_one (r : Verifier.Root) :
    (rootWordFiber r).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  exact root_word_injective
    (((mem_root_word_fiber r x).mp hx).trans ((mem_root_word_fiber r y).mp hy).symm)

/-- The presented `khash` at the deployed encoding is literally the root word of
ONE table coordinate — the coordinate at `configQuery c₀`. -/
theorem khash_at_deployed_is_root_word (Q : Finset Transcript.Bytes)
    (T : OracleTable Q) (c₀ : Verifier.Config) (hc₀ : configQuery c₀ ∈ Q) :
    khashOf Q T (ExplicitEngine.encodeConfig c₀)
      = WhirTail.rootWord (T ⟨configQuery c₀, hc₀⟩) := by
  rw [khashOf]
  congr 1
  rw [show WhirFinalSpongefish.toTranscriptBytes (ExplicitEngine.encodeConfig c₀)
        = configQuery c₀ from rfl,
    RandomOracleSqueezes.hash_of_at Q T ⟨configQuery c₀, hc₀⟩]
  rfl

open Classical in
/-- **(3) THE NEGATIVE RESULT: THE NUMBER COMES FROM THE CONDITIONING.**  ANY
event whose defining predicate includes `CanonicalProofCheck.DeployedFacts` at the
presented `khash` already has mass at most `1 / |Block|`.  The second conjunct `X`
is an ARBITRARY predicate on tables — take `X := fun _ => True` and the bound
still holds.  No R1b, no word bounds, no containment and no collision analysis
enters this proof.  Consequently `fixed_tables_costs_a_birthday_term` does not
EARN its `1 / |Block|` from the birthday term; what that theorem contributes is
the containment `join_failure_event_subset`, which names the disjunct. -/
theorem deployed_facts_alone_costs_the_whole_birthday_term
    (Q : Finset Transcript.Bytes) (gdec : Integrated.DecodeGates)
    (P : PinnedWhirProfile.Profile) (pin : Verifier.Pinned) (c₀ : Verifier.Config)
    (X : OracleTable Q → Prop) (hc₀ : configQuery c₀ ∈ Q) :
    RandomOracleSqueezes.oracleProbability Q
        (filterTables Q (fun T => CanonicalProofCheck.DeployedFacts gdec (khashOf Q T) P pin c₀
          ∧ X T))
      ≤ 1 / (Fintype.card Block : ℚ) := by
  have hsub : filterTables Q (fun T =>
      CanonicalProofCheck.DeployedFacts gdec (khashOf Q T) P pin c₀ ∧ X T)
      ⊆ (allTables Q).filter (fun T : OracleTable Q =>
          T ⟨configQuery c₀, hc₀⟩ ∈ rootWordFiber pin.configDigest) := by
    intro T hT
    obtain ⟨hd, -⟩ := (mem_filter_tables Q _ T).mp hT
    refine Finset.mem_filter.mpr ⟨mem_all_tables Q T, ?_⟩
    refine (mem_root_word_fiber _ _).mpr ?_
    rw [← khash_at_deployed_is_root_word Q T c₀ hc₀]
    exact hd.pinnedDigest.symm
  refine le_trans (RandomOracleSqueezes.oracle_probability_mono Q _ _ hsub) ?_
  rw [BirthdayClashBound.fresh_coordinate_target_probability
    (invariant_at_all_tables Q ⟨configQuery c₀, hc₀⟩) (rootWordFiber pin.configDigest),
    oracle_probability_all_tables, mul_one]
  have hcard : ((rootWordFiber pin.configDigest).card : ℚ) ≤ 1 := by
    exact_mod_cast root_word_fiber_card_le_one pin.configDigest
  exact div_le_div_of_nonneg_right hcard BirthdayClashBound.block_card_cast_pos.le

/-! ## 6. Non-vacuity: every event is inhabited at a concrete instance, and every
membership hypothesis is discharged -/

/-- The constant table: one fixed answer for every query. -/
def constTable (Q : Finset Transcript.Bytes) (β : Block) : OracleTable Q := fun _ => β

theorem const_table_hash_of (Q : Finset Transcript.Bytes) (β : Block)
    (a : Transcript.Bytes) (ha : a ∈ Q) :
    RandomOracleSqueezes.hashOf Q (constTable Q β) a = RandomOracleSqueezes.blockDigest β :=
  RandomOracleSqueezes.hash_of_at Q (constTable Q β) ⟨a, ha⟩

/-- **(4) THE EVENT IS NON-EMPTY.**  The constant table collides on every pair of
queried strings, so `fixed_pair_collision_mass` is a mass of a NON-EMPTY event. -/
theorem const_table_mem_pair_collision_event (Q : Finset Transcript.Bytes)
    (β : Block) (a b : Transcript.Bytes) (ha : a ∈ Q) (hb : b ∈ Q) :
    constTable Q β ∈ pairCollisionEvent Q a b := by
  rw [mem_pair_collision_event, const_table_hash_of Q β a ha, const_table_hash_of Q β b hb]

theorem const_table_mem_leaf_collision_event (Q : Finset Transcript.Bytes)
    (β : Block) (row other : Spongefish.Bytes) (hrow : row ∈ Q) (hother : other ∈ Q)
    (hne : row ≠ other) :
    constTable Q β ∈ leafCollisionEvent Q row other := by
  rw [leaf_collision_event_eq Q row other hne]
  exact const_table_mem_pair_collision_event Q β row other hrow hother

theorem const_table_mem_config_collision_event (Q : Finset Transcript.Bytes)
    (β : Block) (c c₀ : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c₀)
    (hc : configQuery c ∈ Q) (hc₀ : configQuery c₀ ∈ Q) :
    constTable Q β ∈ configCollisionEvent Q c c₀ := by
  rw [config_collision_event_eq Q c c₀ hne]
  exact const_table_mem_pair_collision_event Q β (configQuery c) (configQuery c₀) hc hc₀

/-- **(4) THE DEGENERATE BRANCH, EXHIBITED.**  Outside `Q` the event is ALL
tables, so the constant table is in it there too -- for the opposite reason. -/
theorem const_table_mem_pair_collision_event_outside (Q : Finset Transcript.Bytes)
    (β : Block) (a b : Transcript.Bytes) (ha : a ∉ Q) (hb : b ∉ Q) :
    constTable Q β ∈ pairCollisionEvent Q a b := by
  rw [mem_pair_collision_event, hash_of_outside Q (constTable Q β) a ha,
    hash_of_outside Q (constTable Q β) b hb]

/-- Two distinct short strings, used as the concrete non-degenerate instance. -/
abbrev shortOne : Transcript.Bytes := []

abbrev shortTwo : Transcript.Bytes := [(0 : Transcript.Byte)]

theorem short_strings_distinct : shortOne ≠ shortTwo := by decide

theorem short_one_mem (L : Nat) : shortOne ∈ BirthdayClashBound.boundedQueries L :=
  (BirthdayClashBound.mem_bounded_queries L shortOne).mpr (Nat.zero_le L)

theorem short_two_mem (L : Nat) (hL : 1 ≤ L) :
    shortTwo ∈ BirthdayClashBound.boundedQueries L :=
  (BirthdayClashBound.mem_bounded_queries L shortTwo).mpr hL

theorem not_mem_bounded_queries_of_long (x : Transcript.Bytes) (L : Nat)
    (h : L < x.length) : x ∉ BirthdayClashBound.boundedQueries L := by
  intro hx
  exact absurd ((BirthdayClashBound.mem_bounded_queries L x).mp hx) (Nat.not_le.mpr h)

/-- **(4) THE HYPOTHESES OF `fixed_pair_collision_mass` ARE SATISFIED**, at a
non-degenerate instance: the adopted bounded query set, two distinct strings in
it, and a witness table in the event. -/
theorem fixed_pair_hypotheses_are_satisfiable (β : Block) (L : Nat) (hL : 1 ≤ L) :
    shortOne ∈ BirthdayClashBound.boundedQueries L ∧
    shortTwo ∈ BirthdayClashBound.boundedQueries L ∧
    shortOne ≠ shortTwo ∧
    constTable (BirthdayClashBound.boundedQueries L) β
      ∈ pairCollisionEvent (BirthdayClashBound.boundedQueries L) shortOne shortTwo :=
  ⟨short_one_mem L, short_two_mem L hL, short_strings_distinct,
    const_table_mem_pair_collision_event (BirthdayClashBound.boundedQueries L) β shortOne
      shortTwo (short_one_mem L) (short_two_mem L hL)⟩

/-- The mass statement itself, at that instance: an EQUALITY on a non-empty
event. -/
theorem fixed_pair_collision_mass_at_the_bounded_queries (L : Nat) (hL : 1 ≤ L) :
    RandomOracleSqueezes.oracleProbability (BirthdayClashBound.boundedQueries L)
        (pairCollisionEvent (BirthdayClashBound.boundedQueries L) shortOne shortTwo)
      = 1 / (Fintype.card Block : ℚ) :=
  fixed_pair_collision_mass (BirthdayClashBound.boundedQueries L) shortOne shortTwo
    (short_one_mem L) (short_two_mem L hL) short_strings_distinct

/-- **(4) THE MEMBERSHIP HYPOTHESIS OF THE CONFIGURATION STATEMENTS IS
SATISFIABLE**: an encoding query has the length of its encoding, so the adopted
bounded query set at any length that large contains it. -/
theorem config_query_mem_bounded_queries (c : Verifier.Config) (L : Nat)
    (hL : (ExplicitEngine.encodeConfig c).length ≤ L) :
    configQuery c ∈ BirthdayClashBound.boundedQueries L := by
  refine (BirthdayClashBound.mem_bounded_queries L (configQuery c)).mpr ?_
  rw [configQuery, WhirFinalSpongefish.byte_conversion_length]
  exact hL

/-- **(4) THE FAMILY-FREE HEADLINE, INSTANTIATED WHERE THE ADOPTED TREE BOUNDS
THE QUERY SET.**  At the adopted `BirthdayClashBound.boundedQueries L`, with `L`
at least the deployed encoding's length, the mass of "SOME configuration at all
collides with the deployed `c₀`" is at most
`((boundedQueries L).card + 1) / |Block|`.  This is the step that turns the union
term into a quantity the adopted query-length model owns: the hypothesis is
discharged by `config_query_mem_bounded_queries`, and no
`Finset Verifier.Config` appears in the statement or in the proof. -/
theorem any_config_collision_mass_le_at_the_bounded_queries (c₀ : Verifier.Config)
    (L : Nat) (hL : (ExplicitEngine.encodeConfig c₀).length ≤ L) :
    RandomOracleSqueezes.oracleProbability (BirthdayClashBound.boundedQueries L)
        (anyConfigCollisionEvent (BirthdayClashBound.boundedQueries L) c₀)
      ≤ (((BirthdayClashBound.boundedQueries L).card : ℚ) + 1)
          / (Fintype.card Block : ℚ) :=
  any_config_collision_mass_le (BirthdayClashBound.boundedQueries L) c₀
    (config_query_mem_bounded_queries c₀ L hL)

/-- A two-element query set: exactly the two encoding queries of a submitted and
a deployed configuration.  This is the concrete non-degenerate instance at which
the membership hypotheses of section 3 are discharged; `boundedQueries` above is
the adopted alternative whenever a length bound is available. -/
def configQuerySet (c c₀ : Verifier.Config) : Finset Transcript.Bytes :=
  insert (configQuery c) {configQuery c₀}

theorem config_query_mem_set_left (c c₀ : Verifier.Config) :
    configQuery c ∈ configQuerySet c c₀ := Finset.mem_insert_self _ _

theorem config_query_mem_set_right (c c₀ : Verifier.Config) :
    configQuery c₀ ∈ configQuerySet c c₀ :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **(4) THE `hne` HYPOTHESIS IS SATISFIABLE AT AN ADOPTED PAIR.**  The adopted
`ExplicitEngine.exampleWhirVariant` and `Verifier.testConfig` have different
encodings, so the configuration event is a genuine event and not the empty one. -/
theorem config_encoding_hypothesis_is_satisfiable :
    ExplicitEngine.encodeConfig ExplicitEngine.exampleWhirVariant
      ≠ ExplicitEngine.encodeConfig Verifier.testConfig :=
  ExplicitEngine.example_whir_variant_has_a_different_encoding

/-- A two-element query set over two ABSTRACT byte strings. -/
def pairQuerySet (a b : Transcript.Bytes) : Finset Transcript.Bytes := insert a {b}

theorem mem_pair_query_set_left (a b : Transcript.Bytes) : a ∈ pairQuerySet a b :=
  Finset.mem_insert_self _ _

theorem mem_pair_query_set_right (a b : Transcript.Bytes) : b ∈ pairQuerySet a b :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **(4) A FULLY CLOSED NON-DEGENERATE INSTANCE.**  Query set: the two strings
themselves.  The constant table is in the event, so the event is inhabited. -/
theorem pair_collision_event_nonempty_at_a_two_element_query_set (β : Block)
    (a b : Transcript.Bytes) :
    constTable (pairQuerySet a b) β ∈ pairCollisionEvent (pairQuerySet a b) a b :=
  const_table_mem_pair_collision_event (pairQuerySet a b) β a b
    (mem_pair_query_set_left a b) (mem_pair_query_set_right a b)

/-- **(4) AND ITS MASS**, an equality on that non-empty event. -/
theorem fixed_pair_collision_mass_at_a_two_element_query_set (a b : Transcript.Bytes)
    (hne : a ≠ b) :
    RandomOracleSqueezes.oracleProbability (pairQuerySet a b)
        (pairCollisionEvent (pairQuerySet a b) a b)
      = 1 / (Fintype.card Block : ℚ) :=
  fixed_pair_collision_mass (pairQuerySet a b) a b (mem_pair_query_set_left a b)
    (mem_pair_query_set_right a b) hne

/-- **(4) THE CONFIGURATION EVENT IS NON-EMPTY AND ITS MASS IS THE EQUALITY**, at
any query set carrying the two encoding queries.  The two memberships are jointly
satisfiable -- by `configQuerySet` (`config_query_mem_set_left`,
`config_query_mem_set_right`) and by the adopted bounded query set
(`config_query_mem_bounded_queries`) -- and `hne` is discharged at the adopted
pair by `config_encoding_hypothesis_is_satisfiable`.  So no hypothesis here is
vacuous. -/
theorem config_collision_event_is_inhabited_with_the_stated_mass
    (Q : Finset Transcript.Bytes) (β : Block) (c c₀ : Verifier.Config)
    (hne : ExplicitEngine.encodeConfig c ≠ ExplicitEngine.encodeConfig c₀)
    (hc : configQuery c ∈ Q) (hc₀ : configQuery c₀ ∈ Q) :
    constTable Q β ∈ configCollisionEvent Q c c₀ ∧
      RandomOracleSqueezes.oracleProbability Q (configCollisionEvent Q c c₀)
        = 1 / (Fintype.card Block : ℚ) :=
  ⟨const_table_mem_config_collision_event Q β c c₀ hne hc hc₀,
    config_encoding_collision_mass Q c c₀ hne hc hc₀⟩

/-- **(4) THE SAME FOR THE LEAF EVENT ON TWO NAMED OPENED ROWS.** -/
theorem leaf_collision_event_is_inhabited_with_the_stated_mass
    (Q : Finset Transcript.Bytes) (β : Block) (row other : Spongefish.Bytes)
    (hrow : row ∈ Q) (hother : other ∈ Q) (hne : row ≠ other) :
    constTable Q β ∈ leafCollisionEvent Q row other ∧
      RandomOracleSqueezes.oracleProbability Q (leafCollisionEvent Q row other)
        = 1 / (Fintype.card Block : ℚ) :=
  ⟨const_table_mem_leaf_collision_event Q β row other hrow hother hne,
    leaf_collision_mass Q row other hrow hother hne⟩

/-- **(4) THE ROW-SET HYPOTHESIS IS SATISFIABLE.**  Any finite set of rows no
longer than `L` sits inside the adopted bounded query set at `L`. -/
theorem rows_subset_bounded_queries (R : Finset Spongefish.Bytes) (L : Nat)
    (hL : ∀ x ∈ R, x.length ≤ L) : R ⊆ BirthdayClashBound.boundedQueries L := by
  intro x hx
  exact (BirthdayClashBound.mem_bounded_queries L x).mpr (hL x hx)

/-- **(4) THE ROW BOUND AT THE ADOPTED QUERY SET.**  Any row set whose rows are
no longer than `L` sits inside `boundedQueries L`, so the row union is bounded
there with no row-set parameter left in the numerator — the row analogue of
`any_config_collision_mass_le_at_the_bounded_queries`. -/
theorem opened_rows_collision_mass_le_at_the_bounded_queries
    (R : Finset Spongefish.Bytes) (L : Nat) (hL : ∀ x ∈ R, x.length ≤ L) :
    RandomOracleSqueezes.oracleProbability (BirthdayClashBound.boundedQueries L)
        (openedRowsCollisionEvent (BirthdayClashBound.boundedQueries L) R)
      ≤ (((BirthdayClashBound.boundedQueries L).card : ℚ)
          * ((BirthdayClashBound.boundedQueries L).card : ℚ))
          / (Fintype.card Block : ℚ) :=
  opened_rows_collision_mass_le_by_query_size (BirthdayClashBound.boundedQueries L) R
    (rows_subset_bounded_queries R L hL)

/-- **(4) THE DEGENERATE MASS IS REAL.**  At a query set that does not contain
the two strings the mass is `1`, not `1 / |Block|` -- the branch the honesty
header warns about, proved rather than asserted. -/
theorem degenerate_branch_has_mass_one :
    RandomOracleSqueezes.oracleProbability (BirthdayClashBound.boundedQueries 0)
        (pairCollisionEvent (BirthdayClashBound.boundedQueries 0) shortTwo
          [(1 : Transcript.Byte)])
      = 1 :=
  pair_collision_mass_outside (BirthdayClashBound.boundedQueries 0) shortTwo
    [(1 : Transcript.Byte)]
    (not_mem_bounded_queries_of_long shortTwo 0 (by decide))
    (not_mem_bounded_queries_of_long [(1 : Transcript.Byte)] 0 (by decide))

end Audit.Wire3.LocalizedCollisionMasses
