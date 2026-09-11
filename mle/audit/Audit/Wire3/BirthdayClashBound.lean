import Audit.Wire3.RandomOracleSqueezes

/-!
# THE FRESH-QUERY COUNT, AND A BIRTHDAY BOUND FOR A TRANSCRIPT CHAIN

## The gap this module addresses

`RandomOracleSqueezes` proves a run-level bound,
`run_bad_draw_probability_le_fibrewise`:

  `oracleProbability Q (runDrawEvent Q c p (jointBadEvent ...))`
    `<= ChallengeUnionBound.combinedBound ... + oracleProbability Q (scheduleNonInjectiveEvent Q c p)`

and says, in its own section 8.1, that the additive term is NOT BOUNDED anywhere:
it is exactly `1` on every frame-free query set, the `closureWitness` its own
satisfiability lemma produces included (`clash_term_one`,
`closure_witness_clash_term_one`), and the only query set it exhibits where the
term is `< 1` is `goodSet`, on the separating hash `sepHash`
(`informative_query_set_exists`).  Its header names the missing argument:

  "THERE IS NO SEQUENTIAL FRESH-QUERY INDUCTION HERE ... a sequential,
   round-by-round argument -- round `r`'s frame query is fresh, or it repeats an
   earlier one -- is the birthday count over the frame fibres that would BOUND
   the clash term."

THIS MODULE CARRIES OUT THAT SEQUENTIAL FRESH-QUERY INDUCTION, and applies it to
a chain whose five stages per round are the adopted
`InstalledRoundCommit.roundFrames`, PRECEDED BY the adopted twenty-two-frame
relation prefix `CommitmentOrder.gateChallengeFrames`, from the genuinely fixed
`OuterInitial.zeroDigest`.  What it does NOT do is stated in full under HONESTY
(iii); the short form is that nothing here identifies the chain's stages with the
POSITIONS of `InstalledRoundCommit.concreteChain`, so the result is a bound on a
chain MODEL of the adopted fold, not yet on
`RandomOracleSqueezes.RoundDigestClash` itself.

## What is proved

1. THE FRESH-QUERY LEMMA (section 1).  `fresh_coordinate_probability`: for every
   event `A` that does not look at the answer at one query `q` -- `InvariantAt`,
   stated exactly as "for all `T`, `T2` agreeing at every `q2 != q`, `T ∈ A` iff
   `T2 ∈ A`" -- and every block `b`,

     `oracleProbability Q (A.filter (fun T => T q = b)) = oracleProbability Q A / |Block|`.

   `fresh_coordinate_target_probability` is the union over a target set `S`:

     `oracleProbability Q (A.filter (fun T => T q ∈ S)) = |S| / |Block| * oracleProbability Q A`.

   The proof is pure counting: overwriting the `q`-th answer is a bijection
   between the fibres of `T q` inside `A` (`fibre_card_const`), so all `|Block|`
   fibres have the same size.  No equivalence of table spaces is used; the
   adopted `frameSplit` / `restrict_ratio` are not needed here.
2. THE ADAPTIVE FRESH STEP (section 2).  `adaptive_fresh_step`: the query AND the
   target may both depend on the table -- which they must, because a transcript
   query is built out of earlier answers -- provided neither they nor the
   conditioning event depend on the answer AT that query (`FreshStep`).  Then

     `oracleProbability Q (A.filter (fun T => T (sel T) ∈ targ T)) <= m / |Block| * oracleProbability Q A`

   whenever `|targ T| <= m` on `A`.  `adaptive_fresh_step_card` is the exact
   identity behind it: the pairing `(T, b) |-> (reassign T (sel T) b, T (sel T))`
   is an involutive bijection from `{T ∈ A | T (sel T) ∈ targ T} x Block` onto
   `{(U, a) | U ∈ A, a ∈ targ U}`.
3. THE SEQUENTIAL BIRTHDAY BOUND (section 3).  `chain_clash_probability_le`: for
   a chain of table-dependent queries that is CAUSAL and FRESH on its own good
   event (`Causal`: overwriting the stage-`k` answer changes no query up to stage
   `k`, and the stage-`k` query differs from every earlier one, both required only
   on `noClash sel avoid k`),

     `oracleProbability Q (noClash sel avoid n)ᶜ <= (n * |avoid| + n (n-1) / 2) / |Block|`.

   `avoid` is the set of blocks the chain must also not reach -- for a transcript
   chain, the block of the digest it started from, which is not one of its own
   answers.  `no_clash_nonempty` turns the bound around: below `|Block|` the good
   event is NOT empty.
4. A FINITE, TABLE-INDEPENDENT QUERY SET (section 4).  `boundedQueries L` is every
   byte string of length at most `L`, as a `Finset`, built as a union of images of
   `Fin k -> Transcript.Byte` and NEVER enumerated.  `bounded_queries_closed`: it
   satisfies the adopted `RandomOracleSqueezes.QueryClosure` at every `degreeBits`
   as soon as `64 <= L`, because a squeeze input is always `24 + 32 + 8` bytes
   (`challenge_input_length`).  `bounded_queries_frame`: it also answers every
   frame whose payload fits, which the adopted `closureWitness` never does --
   `bounded_queries_not_frame_free` records that the adopted `clash_term_one` does
   NOT apply to it.
5. THE TRANSCRIPT FRAME CHAIN (section 5).  A transcript is a chain of
   `Transcript.frame` queries in which only the STATE digest varies with the
   table: the tag and the payload of each absorb are fixed by the config, the
   statement and the proof.  `frameState` / `frameSel` are that chain, from a base
   digest `e0` and a table-independent `shape : Nat -> Byte x Bytes`.
   `frame_chain_causal` proves `Causal` for it with NO hypothesis on the shape:
   two stages carry different incoming digests as soon as nothing has clashed, and
   the adopted `CommitmentOrder.frame_injective` turns that into distinct queries.
   `frame_chain_clash_probability_le`:

     `oracleProbability (boundedQueries L) (noClash (frameSel ...) (avoidBase e0) n)ᶜ`
       `<= n (n + 1) / 2 / |Block|`.

   `index_frame_ne` records the sharper, UNCONDITIONAL separation the round index
   gives: `Transcript.frame e 2 (Transcript.le 8 i)` and
   `Transcript.frame e2 2 (Transcript.le 8 j)` differ for `i != j` at every pair of
   state digests, by the adopted `Transcript.le_injective_bounded`.
6. THE RUN'S FIVE-FRAME ROUND FOLD (section 6).  `stageOne` .. `stageFive` are the
   five absorbs of the adopted `InstalledRoundCommit.roundFrames`, and
   `round_commit_is_stage_five` is `rfl`: nothing is re-serialized.
   `stageQueries` is the five FRAME INPUTS of a round's fold, as a list, and
   `stage_five_clash_collision` walks the five stages BACKWARDS to conclude, for
   two rounds with the same commit digest,

     `∃ k, k < 5 ∧ ∃ x y, (stageQueries thash e i m).get? k = some x ∧`
       `(stageQueries thash e2 j m2).get? k = some y ∧ x != y ∧ thash x = thash y`,

   i.e. a collision at the SAME POSITION of the two rounds' own five-frame folds
   -- at the first stage where the incoming digests differ, or, if the walk
   reaches the round-index frame (position `1`), at that frame, where the two
   queries differ outright because the round indices do.
   `round_digest_clash_gives_round_frame_collision` routes the adopted
   `RandomOracleSqueezes.RoundDigestClash` through it and produces the two round
   indices, the position, and the two strings, built from the run's own
   `roundIncoming` digests and `roundMessage` pairs.  THE CONCLUSION IS NOT
   `CommitmentOrder.TranscriptCollision`: that weakening is recorded separately,
   as `round_digest_clash_gives_transcript_collision`, and is marked for what it
   is -- a TAUTOLOGY about any non-injective function, which is exactly the defect
   of the adopted `chain_digest_binds_round`'s alternative.
7. THE ROUND FOLD AS A CHAIN, AND THE BIRTHDAY BOUND ON ITS CLASH (section 7).
   `roundShape` is the five-stages-per-round shape function of the adopted fold,
   and `round_chain_step` proves that five stages of the chain ARE one adopted
   `OuterAdapter.roundCommitted`:

     `frameState L e0 (roundShape ms) hlen (5 * i + 5) T`
       `= stageFive (hashOf (boundedQueries L) T) (frameState L e0 (roundShape ms) hlen (5 * i) T) i m_i`.

   `round_shape_payload_bound` discharges the length hypothesis from an explicit
   budget (`98 <= L` plus the two encoded message cells), and
   `round_shape_payload_bound_at_envelope` discharges it from the DEGREE bounds
   the composition of section 9 already carries -- `5` on the log lane and
   `quotientDegree + 2` on the gate lane -- through the adopted
   `OuterAdapter.encoded_vector_length` (`8 + 24 * length`), leaving only
   `189 + 24 * quotientDegree <= L`.  `round_digests_distinct` refutes the clash
   table by table on the good event, and `round_digest_clash_mass_le`:

     `oracleProbability (boundedQueries L) (roundDigestClashEvent L ms hlen e0 d)`
       `<= 5 d (5 d + 1) / 2 / |Block|`,

   instantiated at the envelope's `degreeBits = 13` by
   `round_digest_clash_mass_at_thirteen` as `<= 2145 / |Block|`, with
   `|Block| = 256 ^ 32` by the adopted `block_card`.  `256 ^ 32` is never
   evaluated: only `2145 < 65536 = 256 ^ 2 <= 256 ^ 32` is used
   (`block_card_gt_small`), and `round_digest_clash_bound_lt_one` records that the
   bound is a real number below `1`.
8. THE RELATION PREFIX, PREPENDED (section 8).  `prefixRoundShape c s ms` is the
   shape of the WHOLE run: the twenty-two frames of the adopted
   `CommitmentOrder.gateChallengeFrames`, then `roundShape`.  `foldDigest` is the
   chain of section 5 with the membership proofs dropped (`frame_state_is_fold`),
   `fold_digest_add` splits it at any stage, and `fold_digest_absorb` identifies a
   frame chain over a message list with the adopted `OuterInitial.absorbMessages`.
   The consequence is `prefix_state_is_derive_digest`:

     `frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen 22 T`
       `= (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state.digest`,

   THE BASE DIGEST IS NO LONGER A PARAMETER: the chain starts at the fixed
   `OuterInitial.zeroDigest` and reaches the adopted `derive` digest after the
   prefix, by the adopted `CommitmentOrder.prefix_state_is_relation_state` and
   `OuterInitial.derived_final_digest`.  `prefix_round_chain_step` is
   `round_chain_step` shifted by the prefix, and
   `prefix_round_digest_clash_mass_at_thirteen`:

     `oracleProbability (boundedQueries L) (prefixRoundDigestClashEvent L c s ms hlen 13)`
       `<= 3828 / |Block|`,

   the `22 + 65 = 87` stages of the whole chain, up from section 7's `2145` for
   the round stages alone, and still below `1`
   (`prefix_round_digest_clash_bound_lt_one`).
9. WHAT A CLASH BOUND BUYS (section 9).  `run_bad_draw_probability_le_of_clash_bound`
   composes any bound `eps` on the adopted localized clash mass with the adopted
   `run_bad_draw_probability_le_fibrewise` to give

     `<= ChallengeUnionBound.combinedBound ... + eps`.

   THIS MODULE DOES NOT SUPPLY THAT `eps` FOR THE ADOPTED
   `InstalledRoundCommit.actualChain`.  See (iii).

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  Everything below is a statement
about the uniform counting law on `RandomOracleSqueezes.OracleTable Q`, a table of
independent uniform answers on a finite set of byte strings.  Nothing here is a
property of Keccak, of the Solidity or Rust transcript, or of any deterministic
function.  The place where the difference bites is EXACTLY the fresh-query lemma
of section 1: it says a fresh query's answer is uniform given everything else,
which is the defining property of a random table and is false, as a theorem, for
any fixed hash.  The adopted
`CommitmentOrder.separation_fails_for_a_deterministic_hash` shows the
deterministic shadow of the property already fails.  Replacing the deployed hash
by a table drawn from this law is an ASSUMPTION with no proof anywhere in this
tree.

(ii) THE PROVER IS FIXED; AN ADAPTIVE PROVER IS STILL EXCLUDED.  The message list
`ms` -- and, in section 9, the proof `p` -- is an argument of every statement
below, quantified OUTSIDE the law.  A prover that reads oracle answers and then
chooses its messages is not modelled here or anywhere in this tree, and that,
not the counting, is the Fiat--Shamir-specific step.  The `shape` function of
section 5 is table-independent BY CONSTRUCTION, and that is precisely the
non-adaptivity assumption in the form the proof uses it.

(iii) WHAT SEPARATES SECTIONS 7 AND 8 FROM THE ADOPTED `actualChain`, PRECISELY.
ONE thing, and it is not hidden in a hypothesis.

  (a) THE BASE DIGEST -- DONE IN SECTION 8, AND NO LONGER A GAP.  Section 7's
      `frameState L e0 (roundShape ms) hlen` starts from a FIXED parameter digest
      `e0`, whereas the adopted `InstalledRoundCommit.actualChain` starts from
      `(OuterInitial.derive thash c (Verifier.statement p)).state`, whose digest is
      ITSELF an oracle answer -- the last frame of the relation prefix -- and
      therefore varies with the table.  Section 8 closes this: `prefixRoundShape`
      prepends the adopted twenty-two-frame `CommitmentOrder.gateChallengeFrames`,
      the chain starts at the genuinely fixed `OuterInitial.zeroDigest`, and
      `prefix_state_is_derive_digest` proves that the chain's digest after those
      twenty-two absorbs IS the adopted `derive` digest, at the table-backed hash.
      The count is charged for it: `22 + 5 d` stages, `3828 / |Block|` at
      `degreeBits = 13` instead of section 7's `2145 / |Block|`.
  (b) THE LIST BOOKKEEPING -- STILL MISSING.  `round_chain_step` and
      `prefix_round_chain_step` identify five chain stages with one adopted
      `OuterAdapter.roundCommitted` fold, which is the mathematical content.
      Threading that through `InstalledRoundCommit.concreteChain` and
      `concreteFinal` to conclude
      `(actualChain thash c p).get? r = some (frameState ... (22 + (5 * r + 5)) T)`
      is index bookkeeping over the message list -- a nested induction with an
      index shift, no probability in it -- and is NOT written here.  Until it is,
      `prefixRoundDigestClashEvent` is an event about the chain, and not,
      syntactically, the mass of `RandomOracleSqueezes.RoundDigestClash`.

  CONSEQUENCE: `run_bad_draw_probability_le_of_clash_bound` is stated with `eps` as
  a hypothesis, and this module does not discharge it.  Quoting section 8's `3828`
  as a bound on the adopted run's clash term would be wrong until (b) is done.

(iv) THE NUMBER IS NOT A SECURITY LEVEL, AND THE MASSES ARE NOT THE SYSTEM'S
SOUNDNESS ERROR.  Only the `JointChallengeSpace` coordinates are in scope at all,
inherited from `RandomOracleSqueezes`: the two coupled-round challenges of each
round, the gate alpha and the gate tau column.  The `InstalledIndexSampler` index
lanes are NOT covered.  The WHIR and Merkle events, which DOMINATE, are excluded
entirely.  `ChallengeUnionBound.combinedBound` is not the deployed system's
soundness error.  The wire-v3 WHIR profile modelled by this tree is the
approximately hundred-bit design point; no figure here is a security level, and no
stray envelope figure from elsewhere in the repository is asserted or implied by
anything below.

(v) WHAT THE `avoid` SET IS FOR, AND WHY IT IS NOT COSMETIC.  A transcript chain
can come back to the digest it STARTED from; that digest is not one of the chain's
own answers, so the pairwise clause alone cannot exclude it, and the freshness of
stage `k` genuinely needs it excluded.  It is charged honestly: one extra bad block
per stage, which is where `n (n - 1) / 2` becomes `n (n + 1) / 2`.

(vi) NON-DEGENERACY, TESTED.  Every hypothesis below is checked against the
constant table.  `frame_chain_causal` holds for EVERY table, the constant table
included -- it has no table hypothesis at all.  `constant_table_clashes`,
`constant_table_in_round_clash_event` and
`constant_table_in_prefix_round_clash_event` show the CLASH events of sections 5,
7 and 8 are non-empty (the constant table is in all three), so no bound here is
proved by an empty event; `frame_chain_no_clash_nonempty` shows the CONDITIONING
events of sections 2 and 3 are non-empty, at every chain length with
`n (n + 1) < 2 * 65536`, that is at every `n <= 361` -- far above the `87` stages
this module actually uses.  `clash_bound_hypothesis_satisfiable` records that the
`eps` hypothesis of section 9 is satisfiable, at `eps = 1`, for every query set
and every run.
-/

namespace Audit.Wire3.BirthdayClashBound

open Audit.Wire3
open Audit.Wire3.RandomOracleSqueezes

/-! ## 1. ONE COORDINATE OF A TABLE -/

/-- Overwrite the answer of `T` at the single query `q`, leaving every other
answer alone.  This is the only operation on tables used below. -/
def reassign {Q : Finset Transcript.Bytes} (T : OracleTable Q)
    (q : { x : Transcript.Bytes // x ∈ Q }) (b : Block) : OracleTable Q :=
  Function.update T q b

theorem reassign_at {Q : Finset Transcript.Bytes} (T : OracleTable Q)
    (q : { x : Transcript.Bytes // x ∈ Q }) (b : Block) : reassign T q b q = b :=
  Function.update_same _ _ _

theorem reassign_off {Q : Finset Transcript.Bytes} (T : OracleTable Q)
    (q q2 : { x : Transcript.Bytes // x ∈ Q }) (b : Block) (h : q2 ≠ q) :
    reassign T q b q2 = T q2 :=
  Function.update_noteq h _ _

theorem reassign_same {Q : Finset Transcript.Bytes} (T : OracleTable Q)
    (q : { x : Transcript.Bytes // x ∈ Q }) : reassign T q (T q) = T :=
  Function.update_eq_self _ _

theorem reassign_reassign {Q : Finset Transcript.Bytes} (T : OracleTable Q)
    (q : { x : Transcript.Bytes // x ∈ Q }) (b b2 : Block) :
    reassign (reassign T q b) q b2 = reassign T q b2 :=
  Function.update_idem _ _ _

/-- **THE EVENT DOES NOT LOOK AT `q`.**  Exactly the shape requested: `A` is
unchanged when the table is altered at `q` alone. -/
def InvariantAt (Q : Finset Transcript.Bytes) (q : { x : Transcript.Bytes // x ∈ Q })
    (A : Finset (OracleTable Q)) : Prop :=
  ∀ T T2 : OracleTable Q,
    (∀ q2 : { x : Transcript.Bytes // x ∈ Q }, q2 ≠ q → T q2 = T2 q2) → (T ∈ A ↔ T2 ∈ A)

theorem invariant_at_reassign {Q : Finset Transcript.Bytes}
    {q : { x : Transcript.Bytes // x ∈ Q }} {A : Finset (OracleTable Q)}
    (hA : InvariantAt Q q A) (T : OracleTable Q) (b : Block) (hT : T ∈ A) :
    reassign T q b ∈ A :=
  (hA T (reassign T q b) (fun q2 h2 => (reassign_off T q q2 b h2).symm)).mp hT

/-- (1) The fibres of the answer at `q` inside an event that does not look at `q`
all have the SAME size: overwriting the `q`-th answer is a bijection between
them. -/
theorem fibre_card_const {Q : Finset Transcript.Bytes}
    {q : { x : Transcript.Bytes // x ∈ Q }} {A : Finset (OracleTable Q)}
    (hA : InvariantAt Q q A) (b b2 : Block) :
    (A.filter (fun T => T q = b)).card = (A.filter (fun T => T q = b2)).card := by
  refine Finset.card_nbij' (fun T => reassign T q b2) (fun T => reassign T q b) ?_ ?_ ?_ ?_
  · intro T hT
    obtain ⟨hTA, _⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨invariant_at_reassign hA T b2 hTA, reassign_at T q b2⟩
  · intro T hT
    obtain ⟨hTA, _⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨invariant_at_reassign hA T b hTA, reassign_at T q b⟩
  · intro T hT
    obtain ⟨_, hTq⟩ := Finset.mem_filter.mp hT
    show reassign (reassign T q b2) q b = T
    rw [reassign_reassign, ← hTq, reassign_same]
  · intro T hT
    obtain ⟨_, hTq⟩ := Finset.mem_filter.mp hT
    show reassign (reassign T q b) q b2 = T
    rw [reassign_reassign, ← hTq, reassign_same]

/-- (1) **THE FRESH-QUERY COUNT.**  Inside an event that does not look at `q`,
exactly one `|Block|`-th of the tables answer `b` at `q`. -/
theorem fresh_coordinate_card {Q : Finset Transcript.Bytes}
    {q : { x : Transcript.Bytes // x ∈ Q }} {A : Finset (OracleTable Q)}
    (hA : InvariantAt Q q A) (b : Block) :
    (A.filter (fun T => T q = b)).card * Fintype.card Block = A.card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := fun T : OracleTable Q => T q)
    (s := A) (t := (Finset.univ : Finset Block)) (fun _ _ => Finset.mem_univ _)
  rw [h, Finset.sum_congr rfl (fun b2 _ => fibre_card_const hA b2 b), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.mul_comm]

theorem block_card_cast_pos : (0 : ℚ) < (Fintype.card Block : ℚ) := by
  exact_mod_cast block_card_pos

theorem block_card_cast_ne : (Fintype.card Block : ℚ) ≠ 0 := block_card_cast_pos.ne'

/-- (1) **THE FRESH-QUERY LEMMA, AS A MASS.**  `P(A ∩ {T | T q = b}) = P(A) / |Block|`
for every event `A` that is invariant under changing the table at `q` alone. -/
theorem fresh_coordinate_probability {Q : Finset Transcript.Bytes}
    {q : { x : Transcript.Bytes // x ∈ Q }} {A : Finset (OracleTable Q)}
    (hA : InvariantAt Q q A) (b : Block) :
    oracleProbability Q (A.filter (fun T => T q = b))
      = oracleProbability Q A / (Fintype.card Block : ℚ) := by
  have hc : ((A.filter (fun T => T q = b)).card : ℚ) * (Fintype.card Block : ℚ)
      = (A.card : ℚ) := by exact_mod_cast fresh_coordinate_card hA b
  rw [oracleProbability, oracleProbability, div_div,
    div_eq_div_iff (oracle_card_cast_pos Q).ne'
      (mul_ne_zero (oracle_card_cast_pos Q).ne' block_card_cast_ne)]
  linear_combination (Fintype.card (OracleTable Q) : ℚ) * hc

/-- (1) **THE UNION OVER A TARGET SET.**  The same count, for the event that the
answer at `q` lands anywhere in a finite set `S` of blocks. -/
theorem fresh_coordinate_target_card {Q : Finset Transcript.Bytes}
    {q : { x : Transcript.Bytes // x ∈ Q }} {A : Finset (OracleTable Q)}
    (hA : InvariantAt Q q A) (S : Finset Block) :
    (A.filter (fun T => T q ∈ S)).card * Fintype.card Block = S.card * A.card := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun T : OracleTable Q => T q)
    (s := A.filter (fun T => T q ∈ S)) (t := S)
    (fun _ hx => (Finset.mem_filter.mp hx).2)
  have hinner : ∀ b ∈ S,
      ((A.filter (fun T => T q ∈ S)).filter (fun T => T q = b)).card
        = (A.filter (fun T => T q = b)).card := by
    intro b hb
    congr 1
    apply Finset.ext
    intro T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hTA, _⟩, hTb⟩
      exact ⟨hTA, hTb⟩
    · rintro ⟨hTA, hTb⟩
      exact ⟨⟨hTA, hTb ▸ hb⟩, hTb⟩
  rw [hfib, Finset.sum_congr rfl hinner, Finset.sum_mul,
    Finset.sum_congr rfl (fun b _ => fresh_coordinate_card hA b), Finset.sum_const,
    smul_eq_mul]

/-- (1) **THE FRESH-QUERY LEMMA IN THE UNION FORM.**
`P(A ∩ {T | T q ∈ S}) = |S| / |Block| * P(A)`, hence `≤ |S| / |Block|`. -/
theorem fresh_coordinate_target_probability {Q : Finset Transcript.Bytes}
    {q : { x : Transcript.Bytes // x ∈ Q }} {A : Finset (OracleTable Q)}
    (hA : InvariantAt Q q A) (S : Finset Block) :
    oracleProbability Q (A.filter (fun T => T q ∈ S))
      = (S.card : ℚ) / (Fintype.card Block : ℚ) * oracleProbability Q A := by
  have hc : ((A.filter (fun T => T q ∈ S)).card : ℚ) * (Fintype.card Block : ℚ)
      = (S.card : ℚ) * (A.card : ℚ) := by exact_mod_cast fresh_coordinate_target_card hA S
  rw [oracleProbability, oracleProbability, div_mul_div_comm,
    div_eq_div_iff (oracle_card_cast_pos Q).ne'
      (mul_ne_zero block_card_cast_ne (oracle_card_cast_pos Q).ne')]
  linear_combination (Fintype.card (OracleTable Q) : ℚ) * hc

/-! ## 2. THE ADAPTIVE FRESH STEP -/

/-- **THE HYPOTHESES OF ONE ADAPTIVE FRESH ORACLE STEP.**  The query `sel T` and
the target set `targ T` may both depend on the table -- that is the whole point,
because the run's queries are built out of earlier oracle answers -- but neither
they nor the conditioning event `A` may depend on the answer AT `sel T`.  That is
exactly "the query is fresh, given the history". -/
def FreshStep (Q : Finset Transcript.Bytes) (A : Finset (OracleTable Q))
    (sel : OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (targ : OracleTable Q → Finset Block) : Prop :=
  (∀ T ∈ A, ∀ b : Block, reassign T (sel T) b ∈ A) ∧
  (∀ T ∈ A, ∀ b : Block, sel (reassign T (sel T) b) = sel T) ∧
  (∀ T ∈ A, ∀ b : Block, targ (reassign T (sel T) b) = targ T)

/-- (2) **THE EXACT COUNT AT AN ADAPTIVE FRESH STEP.**  The pairing
`(T, b) ↦ (reassign T (sel T) b, T (sel T))` is an involutive bijection from
`{T ∈ A | T (sel T) ∈ targ T} × Block` onto `{(U, a) | U ∈ A, a ∈ targ U}`.  No
fibration and no equivalence of table spaces is needed. -/
theorem adaptive_fresh_step_card {Q : Finset Transcript.Bytes} {A : Finset (OracleTable Q)}
    {sel : OracleTable Q → { x : Transcript.Bytes // x ∈ Q }}
    {targ : OracleTable Q → Finset Block} (h : FreshStep Q A sel targ) :
    (A.filter (fun T => T (sel T) ∈ targ T)).card * Fintype.card Block
      = ∑ U in A, (targ U).card := by
  obtain ⟨hstab, hsel, htarg⟩ := h
  have key : ∀ U ∈ A, ∀ b : Block,
      ((reassign (reassign U (sel U) b) (sel (reassign U (sel U) b)) (U (sel U)),
        (reassign U (sel U) b) (sel (reassign U (sel U) b))) : OracleTable Q × Block)
        = (U, b) := by
    intro U hU b
    rw [hsel U hU b, reassign_at, reassign_reassign, reassign_same]
  have hbij : ((A.filter (fun T => T (sel T) ∈ targ T)) ×ˢ
        (Finset.univ : Finset Block)).card
      = ((A ×ˢ (Finset.univ : Finset Block)).filter (fun z => z.2 ∈ targ z.1)).card := by
    refine Finset.card_nbij'
      (fun z => (reassign z.1 (sel z.1) z.2, z.1 (sel z.1)))
      (fun z => (reassign z.1 (sel z.1) z.2, z.1 (sel z.1))) ?_ ?_ ?_ ?_
    · intro z hz
      obtain ⟨hz1, -⟩ := Finset.mem_product.mp hz
      obtain ⟨hzA, hzt⟩ := Finset.mem_filter.mp hz1
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hstab z.1 hzA z.2, Finset.mem_univ _⟩, ?_⟩
      show z.1 (sel z.1) ∈ targ (reassign z.1 (sel z.1) z.2)
      rw [htarg z.1 hzA z.2]
      exact hzt
    · intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzA, -⟩ := Finset.mem_product.mp hz1
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hstab z.1 hzA z.2, ?_⟩,
        Finset.mem_univ _⟩
      show (reassign z.1 (sel z.1) z.2) (sel (reassign z.1 (sel z.1) z.2))
        ∈ targ (reassign z.1 (sel z.1) z.2)
      rw [hsel z.1 hzA z.2, htarg z.1 hzA z.2, reassign_at]
      exact hz2
    · intro z hz
      obtain ⟨hz1, -⟩ := Finset.mem_product.mp hz
      exact key z.1 (Finset.mem_filter.mp hz1).1 z.2
    · intro z hz
      obtain ⟨hz1, -⟩ := Finset.mem_filter.mp hz
      exact key z.1 (Finset.mem_product.mp hz1).1 z.2
  rw [Finset.card_product, Finset.card_univ] at hbij
  rw [hbij, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  simp only [Finset.sum_boole, Nat.cast_id, Finset.filter_univ_mem]

/-- (2) **THE ADAPTIVE FRESH STEP, AS A MASS.**  If every target set has at most
`m` elements, a fresh adaptive query lands in its target with mass at most
`m / |Block|` of the conditioning event. -/
theorem adaptive_fresh_step {Q : Finset Transcript.Bytes} {A : Finset (OracleTable Q)}
    {sel : OracleTable Q → { x : Transcript.Bytes // x ∈ Q }}
    {targ : OracleTable Q → Finset Block} (h : FreshStep Q A sel targ) (m : Nat)
    (hm : ∀ T ∈ A, (targ T).card ≤ m) :
    oracleProbability Q (A.filter (fun T => T (sel T) ∈ targ T))
      ≤ (m : ℚ) / (Fintype.card Block : ℚ) * oracleProbability Q A := by
  have hsum : ∑ U in A, (targ U).card ≤ A.card * m := by
    have hs := Finset.sum_le_sum hm
    rw [Finset.sum_const, smul_eq_mul] at hs
    exact hs
  have hcard := adaptive_fresh_step_card h
  have hle : ((A.filter (fun T => T (sel T) ∈ targ T)).card : ℚ) * (Fintype.card Block : ℚ)
      ≤ (m : ℚ) * (A.card : ℚ) := by
    have : (A.filter (fun T => T (sel T) ∈ targ T)).card * Fintype.card Block ≤ m * A.card := by
      rw [hcard, Nat.mul_comm]
      exact hsum
    exact_mod_cast this
  have hN := oracle_card_cast_pos Q
  rw [oracleProbability, oracleProbability, div_mul_div_comm,
    div_le_div_iff hN (mul_pos block_card_cast_pos hN)]
  calc ((A.filter (fun T => T (sel T) ∈ targ T)).card : ℚ)
        * ((Fintype.card Block : ℚ) * (Fintype.card (OracleTable Q) : ℚ))
      = (((A.filter (fun T => T (sel T) ∈ targ T)).card : ℚ) * (Fintype.card Block : ℚ))
          * (Fintype.card (OracleTable Q) : ℚ) := by ring
    _ ≤ ((m : ℚ) * (A.card : ℚ)) * (Fintype.card (OracleTable Q) : ℚ) :=
        mul_le_mul_of_nonneg_right hle hN.le
    _ = (m : ℚ) * (A.card : ℚ) * (Fintype.card (OracleTable Q) : ℚ) := by ring

/-- (2) The same step with the conditioning event dropped. -/
theorem adaptive_fresh_step_abs {Q : Finset Transcript.Bytes} {A : Finset (OracleTable Q)}
    {sel : OracleTable Q → { x : Transcript.Bytes // x ∈ Q }}
    {targ : OracleTable Q → Finset Block} (h : FreshStep Q A sel targ) (m : Nat)
    (hm : ∀ T ∈ A, (targ T).card ≤ m) :
    oracleProbability Q (A.filter (fun T => T (sel T) ∈ targ T))
      ≤ (m : ℚ) / (Fintype.card Block : ℚ) := by
  refine le_trans (adaptive_fresh_step h m hm) ?_
  have h1 := oracle_probability_le_one Q A
  have h2 : (0 : ℚ) ≤ (m : ℚ) / (Fintype.card Block : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) block_card_cast_pos.le
  calc (m : ℚ) / (Fintype.card Block : ℚ) * oracleProbability Q A
      ≤ (m : ℚ) / (Fintype.card Block : ℚ) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = (m : ℚ) / (Fintype.card Block : ℚ) := mul_one _

/-! ## 3. A SEQUENTIAL ORACLE CHAIN AND ITS BIRTHDAY BOUND -/

/-- The block the chain reads at stage `k`: the table's answer at the stage-`k`
query, which may itself be built out of the earlier answers. -/
def chainVal {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (k : Nat)
    (T : OracleTable Q) : Block := T (sel k T)

/-- The good event: no two of the chain's first `n` blocks coincide, AND none of
them lands in the forbidden set `avoid`.  `avoid` carries the blocks the chain
must not reach -- for a transcript chain, the block of the digest it STARTED
from, which is not itself one of the chain's answers and therefore cannot be
separated from them by the pairwise clause alone. -/
def noClash {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T =>
    (∀ r ∈ Finset.range n, ∀ s ∈ Finset.range n, r < s →
      chainVal sel r T ≠ chainVal sel s T) ∧
    (∀ s ∈ Finset.range n, chainVal sel s T ∉ avoid))

theorem mem_no_clash {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) (T : OracleTable Q) :
    T ∈ noClash sel avoid n ↔
      (∀ r s : Nat, r < s → s < n → chainVal sel r T ≠ chainVal sel s T) ∧
      (∀ s : Nat, s < n → chainVal sel s T ∉ avoid) := by
  simp only [noClash, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun r s hrs hsn => h1 r (lt_trans hrs hsn) s hsn hrs, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun r _ s hsn hrs => h1 r s hrs hsn, h2⟩

theorem mem_clash_event {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) (T : OracleTable Q) :
    T ∈ (noClash sel avoid n)ᶜ ↔
      (∃ r s : Nat, r < s ∧ s < n ∧ chainVal sel r T = chainVal sel s T) ∨
      (∃ s : Nat, s < n ∧ chainVal sel s T ∈ avoid) := by
  rw [Finset.mem_compl, mem_no_clash, not_and_or]
  constructor
  · rintro (h | h)
    · push_neg at h
      obtain ⟨r, s, hrs, hsn, heq⟩ := h
      exact Or.inl ⟨r, s, hrs, hsn, heq⟩
    · push_neg at h
      obtain ⟨s, hsn, hin⟩ := h
      exact Or.inr ⟨s, hsn, hin⟩
  · rintro (⟨r, s, hrs, hsn, heq⟩ | ⟨s, hsn, hin⟩)
    · refine Or.inl ?_
      push_neg
      exact ⟨r, s, hrs, hsn, heq⟩
    · refine Or.inr ?_
      push_neg
      exact ⟨s, hsn, hin⟩

/-- What the stage-`k` answer must avoid: the forbidden set, together with the
blocks the chain has already produced. -/
def chainTarget {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (k : Nat) (T : OracleTable Q) : Finset Block :=
  avoid ∪ (Finset.range k).image (fun j => chainVal sel j T)

theorem chain_target_card_le {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (k : Nat) (T : OracleTable Q) :
    (chainTarget sel avoid k T).card ≤ avoid.card + k := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  exact le_trans Finset.card_image_le (le_of_eq (Finset.card_range k))

/-- **THE CHAIN IS CAUSAL AND ITS STAGES ARE FRESH.**  Overwriting the answer at
stage `k`'s query changes no query up to stage `k` -- that is CAUSALITY, the
stage-`j` query is a function of the answers before it -- and stage `k`'s query
differs from every earlier query -- that is FRESHNESS.  Both are required only on
the good event `noClash sel avoid k`, which is what a transcript chain needs:
stage `k`'s query is fresh PROVIDED no two earlier stages have already clashed. -/
def Causal {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q })
    (avoid : Finset Block) (n : Nat) : Prop :=
  (∀ k, k < n → ∀ j, j ≤ k → ∀ T ∈ noClash sel avoid k, ∀ b : Block,
      sel j (reassign T (sel k T) b) = sel j T) ∧
  (∀ k, k < n → ∀ j, j < k → ∀ T ∈ noClash sel avoid k, sel j T ≠ sel k T)

theorem causal_mono {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} {avoid : Finset Block}
    {n : Nat} (hc : Causal sel avoid n) (m : Nat) (hm : m ≤ n) : Causal sel avoid m :=
  ⟨fun k hk => hc.1 k (lt_of_lt_of_le hk hm), fun k hk => hc.2 k (lt_of_lt_of_le hk hm)⟩

theorem chain_val_stable {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} {avoid : Finset Block}
    {n : Nat} (hc : Causal sel avoid n) (k : Nat) (hk : k < n) (j : Nat) (hj : j < k)
    (T : OracleTable Q) (hT : T ∈ noClash sel avoid k) (b : Block) :
    chainVal sel j (reassign T (sel k T) b) = chainVal sel j T := by
  show (reassign T (sel k T) b) (sel j (reassign T (sel k T) b)) = T (sel j T)
  rw [hc.1 k hk j (le_of_lt hj) T hT b]
  exact reassign_off T (sel k T) (sel j T) b (hc.2 k hk j hj T hT)

theorem no_clash_reassign {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} {avoid : Finset Block}
    {n : Nat} (hc : Causal sel avoid n) (k : Nat) (hk : k < n) (T : OracleTable Q)
    (hT : T ∈ noClash sel avoid k) (b : Block) :
    reassign T (sel k T) b ∈ noClash sel avoid k := by
  obtain ⟨hT1, hT2⟩ := (mem_no_clash sel avoid k T).mp hT
  rw [mem_no_clash]
  refine ⟨fun r s hrs hsk => ?_, fun s hsk => ?_⟩
  · rw [chain_val_stable hc k hk r (lt_trans hrs hsk) T hT b,
      chain_val_stable hc k hk s hsk T hT b]
    exact hT1 r s hrs hsk
  · rw [chain_val_stable hc k hk s hsk T hT b]
    exact hT2 s hsk

/-- (3) A causal chain's stage `k` is an ADAPTIVE FRESH STEP of section 2, with
the conditioning event "no clash yet" and the target "forbidden, or an earlier
block". -/
theorem fresh_step_of_causal {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} {avoid : Finset Block}
    {n : Nat} (hc : Causal sel avoid n) (k : Nat) (hk : k < n) :
    FreshStep Q (noClash sel avoid k) (sel k) (chainTarget sel avoid k) := by
  refine ⟨fun T hT b => no_clash_reassign hc k hk T hT b,
    fun T hT b => hc.1 k hk k (le_refl k) T hT b, fun T hT b => ?_⟩
  refine congrArg (fun z => avoid ∪ z) (Finset.image_congr ?_)
  intro j hj
  exact chain_val_stable hc k hk j (Finset.mem_range.mp hj) T hT b

theorem clash_step_bound {Q : Finset Transcript.Bytes}
    {sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }} {avoid : Finset Block}
    {n : Nat} (hc : Causal sel avoid n) (k : Nat) (hk : k < n) :
    oracleProbability Q
        ((noClash sel avoid k).filter
          (fun T => chainVal sel k T ∈ chainTarget sel avoid k T))
      ≤ ((avoid.card : ℚ) + (k : ℚ)) / (Fintype.card Block : ℚ) := by
  have h := adaptive_fresh_step_abs (fresh_step_of_causal hc k hk) (avoid.card + k)
    (fun T _ => chain_target_card_le sel avoid k T)
  rw [Nat.cast_add] at h
  exact h

theorem no_clash_succ_compl {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (avoid : Finset Block)
    (k : Nat) :
    (noClash sel avoid (k + 1))ᶜ ⊆ (noClash sel avoid k)ᶜ ∪
      (noClash sel avoid k).filter
        (fun T => chainVal sel k T ∈ chainTarget sel avoid k T) := by
  intro T hT
  by_cases hk : T ∈ noClash sel avoid k
  · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, ?_⟩)
    obtain ⟨hk1, hk2⟩ := (mem_no_clash sel avoid k T).mp hk
    rcases (mem_clash_event sel avoid (k + 1) T).mp hT with ⟨r, s, hrs, hsk, heq⟩ | ⟨s, hsk, hin⟩
    · have hsk2 : s = k := by
        by_contra hne
        exact hk1 r s hrs (by omega) heq
      subst hsk2
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hrs, heq⟩)
    · have hsk2 : s = k := by
        by_contra hne
        exact hk2 s (by omega) hin
      subst hsk2
      exact Finset.mem_union_left _ hin
  · exact Finset.mem_union_left _ (Finset.mem_compl.mpr hk)

theorem oracle_probability_union_le (Q : Finset Transcript.Bytes)
    (A B : Finset (OracleTable Q)) :
    oracleProbability Q (A ∪ B) ≤ oracleProbability Q A + oracleProbability Q B := by
  have hc : ((A ∪ B).card : ℚ) ≤ (A.card : ℚ) + (B.card : ℚ) := by
    exact_mod_cast Finset.card_union_le A B
  rw [oracleProbability, oracleProbability, oracleProbability, div_add_div_same]
  exact div_le_div_of_nonneg_right hc (oracle_card_cast_pos Q).le

theorem clash_probability_le_sum {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (avoid : Finset Block)
    (n : Nat) (hc : Causal sel avoid n) :
    oracleProbability Q (noClash sel avoid n)ᶜ
      ≤ ∑ k in Finset.range n,
          ((avoid.card : ℚ) + (k : ℚ)) / (Fintype.card Block : ℚ) := by
  induction n with
  | zero =>
      have h0 : noClash sel avoid 0 = (Finset.univ : Finset (OracleTable Q)) := by
        apply Finset.ext
        intro T
        simp only [noClash, Finset.mem_filter, Finset.mem_univ, true_and, Finset.range_zero,
          Finset.not_mem_empty, false_implies, implies_true, and_self, iff_self]
      rw [h0, Finset.compl_univ, Finset.range_zero, Finset.sum_empty, oracleProbability,
        Finset.card_empty, Nat.cast_zero, zero_div]
  | succ k ih =>
      have hck : Causal sel avoid k := causal_mono hc k (Nat.le_succ k)
      calc oracleProbability Q (noClash sel avoid (k + 1))ᶜ
          ≤ oracleProbability Q ((noClash sel avoid k)ᶜ ∪
              (noClash sel avoid k).filter
                (fun T => chainVal sel k T ∈ chainTarget sel avoid k T)) :=
            oracle_probability_mono Q _ _ (no_clash_succ_compl sel avoid k)
        _ ≤ oracleProbability Q (noClash sel avoid k)ᶜ
              + oracleProbability Q ((noClash sel avoid k).filter
                  (fun T => chainVal sel k T ∈ chainTarget sel avoid k T)) :=
            oracle_probability_union_le Q _ _
        _ ≤ (∑ j in Finset.range k,
              ((avoid.card : ℚ) + (j : ℚ)) / (Fintype.card Block : ℚ))
              + ((avoid.card : ℚ) + (k : ℚ)) / (Fintype.card Block : ℚ) :=
            add_le_add (ih hck) (clash_step_bound hc k (Nat.lt_succ_self k))
        _ = ∑ j in Finset.range (k + 1),
              ((avoid.card : ℚ) + (j : ℚ)) / (Fintype.card Block : ℚ) :=
            (Finset.sum_range_succ _ _).symm

theorem sum_range_div_closed (a : ℚ) (n : Nat) :
    ∑ k in Finset.range n, (a + (k : ℚ)) / (Fintype.card Block : ℚ)
      = ((n : ℚ) * a + (n : ℚ) * ((n : ℚ) - 1) / 2) / (Fintype.card Block : ℚ) := by
  rw [← Finset.sum_div]
  congr 1
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- (3) **THE BIRTHDAY BOUND FOR A CAUSAL, FRESH ORACLE CHAIN.**  Under the
random-oracle counting law of `RandomOracleSqueezes`, the mass of the event that
two of the chain's first `n` blocks coincide, or that one of them lands in the
forbidden set, is at most `n |avoid| + n (n - 1) / 2` over the block space.  The
proof is the sequential fresh-query induction: stage `k`'s query is fresh on the
event that nothing has gone wrong before it, so conditioned on that event its
answer hits one of the `|avoid| + k` bad blocks with mass at most
`(|avoid| + k) / |Block|`; the `n` steps are summed. -/
theorem chain_clash_probability_le {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (avoid : Finset Block)
    (n : Nat) (hc : Causal sel avoid n) :
    oracleProbability Q (noClash sel avoid n)ᶜ
      ≤ ((n : ℚ) * (avoid.card : ℚ) + (n : ℚ) * ((n : ℚ) - 1) / 2)
        / (Fintype.card Block : ℚ) := by
  rw [← sum_range_div_closed (avoid.card : ℚ) n]
  exact clash_probability_le_sum sel avoid n hc

/-- (3) Since the bound is strictly below `1`, the good event is NOT empty: a
table whose chain is pairwise distinct and avoids the forbidden set exists. -/
theorem no_clash_nonempty {Q : Finset Transcript.Bytes}
    (sel : Nat → OracleTable Q → { x : Transcript.Bytes // x ∈ Q }) (avoid : Finset Block)
    (n : Nat) (hc : Causal sel avoid n)
    (hsmall : ((n : ℚ) * (avoid.card : ℚ) + (n : ℚ) * ((n : ℚ) - 1) / 2)
      / (Fintype.card Block : ℚ) < 1) : (noClash sel avoid n).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have h1 : oracleProbability Q (noClash sel avoid n)ᶜ = 1 := by
    rw [hempty, Finset.compl_empty, oracleProbability, Finset.card_univ]
    exact div_self (oracle_card_cast_pos Q).ne'
  have h2 := chain_clash_probability_le sel avoid n hc
  rw [h1] at h2
  exact absurd (lt_of_le_of_lt h2 hsmall) (lt_irrefl 1)

/-! ## 4. A FINITE, TABLE-INDEPENDENT QUERY SET: THE SHORT STRINGS -/

/-- **EVERY BYTE STRING OF LENGTH AT MOST `L`.**  Finite, fixed before any table
is sampled, and never enumerated: it is written as a union of images of the
function spaces `Fin k → Transcript.Byte`, one per length. -/
def boundedQueries (L : Nat) : Finset Transcript.Bytes :=
  (Finset.range (L + 1)).biUnion
    (fun k => Finset.image (fun v : Fin k → Transcript.Byte => List.ofFn v) Finset.univ)

theorem mem_bounded_queries (L : Nat) (x : Transcript.Bytes) :
    x ∈ boundedQueries L ↔ x.length ≤ L := by
  constructor
  · intro h
    obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hx
    rw [← hv, List.length_ofFn]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  · intro h
    exact Finset.mem_biUnion.mpr ⟨x.length, Finset.mem_range.mpr (Nat.lt_succ_of_le h),
      Finset.mem_image.mpr ⟨x.get, Finset.mem_univ _, List.ofFn_get x⟩⟩

theorem challenge_prefix_length : Transcript.challengePrefix.length = 24 := by decide

theorem frame_prefix_length : Transcript.framePrefix.length = 20 := by decide

/-- Every squeeze input is `24 + 32 + 8` bytes, whatever the counter is. -/
theorem challenge_input_length (e : Transcript.Digest) (n : Nat) :
    (Transcript.challengeInput e n).length = 64 := by
  simp only [Transcript.challengeInput, List.length_append, Transcript.digestBytes,
    e.length_eq, Transcript.le_length, challenge_prefix_length]

/-- Every frame is `20 + 32 + 1 + 8` bytes plus its payload. -/
theorem frame_total_length (e : Transcript.Digest) (t : Transcript.Byte)
    (pl : Transcript.Bytes) : (Transcript.frame e t pl).length = 61 + pl.length := by
  rw [Transcript.frame_length, frame_prefix_length]

theorem bounded_queries_challenge (L : Nat) (hL : 64 ≤ L) (e : Transcript.Digest) (n : Nat) :
    Transcript.challengeInput e n ∈ boundedQueries L := by
  rw [mem_bounded_queries, challenge_input_length]
  exact hL

/-- (4) **`boundedQueries` SATISFIES THE ADOPTED `QueryClosure`.**  `L ≥ 64` is
enough at EVERY `degreeBits`, because a squeeze input has a fixed length. -/
theorem bounded_queries_closed (L d : Nat) (hL : 64 ≤ L) :
    RandomOracleSqueezes.QueryClosure (boundedQueries L) d :=
  fun e n _ => bounded_queries_challenge L hL e n

/-- (4) **`boundedQueries` ALSO ANSWERS FRAMES.**  This is what the adopted
`closureWitness` never does, and what section 8.1 of `RandomOracleSqueezes`
identifies as the reason its clash term is `1`. -/
theorem bounded_queries_frame (L : Nat) (e : Transcript.Digest) (t : Transcript.Byte)
    (pl : Transcript.Bytes) (h : 61 + pl.length ≤ L) :
    Transcript.frame e t pl ∈ boundedQueries L := by
  rw [mem_bounded_queries, frame_total_length]
  exact h

/-- (4) `boundedQueries` is NOT frame-free, so the adopted `clash_term_one` does
not apply to it. -/
theorem bounded_queries_not_frame_free (L : Nat) (hL : 61 ≤ L) :
    ¬ RandomOracleSqueezes.FrameFree (boundedQueries L) := by
  intro h
  exact h OuterInitial.zeroDigest 0 []
    (bounded_queries_frame L OuterInitial.zeroDigest 0 [] (by simpa using hL))

/-- (4) On `boundedQueries L` the table-backed hash never falls back on its
off-set default at a string of length at most `L`. -/
theorem hash_of_bounded (L : Nat) (T : OracleTable (boundedQueries L)) (q : Transcript.Bytes)
    (hq : q.length ≤ L) :
    hashOf (boundedQueries L) T q = blockDigest (T ⟨q, (mem_bounded_queries L q).mpr hq⟩) :=
  hash_of_at (boundedQueries L) T ⟨q, (mem_bounded_queries L q).mpr hq⟩

/-! ## 5. THE TRANSCRIPT FRAME CHAIN, AND ITS BIRTHDAY BOUND -/

/-- The adopted round-index frame of `InstalledRoundCommit.roundFrames`: tag `2`,
payload the eight little-endian bytes of the round index. -/
def indexFrame (e : Transcript.Digest) (k : Nat) : Transcript.Bytes :=
  Transcript.frame e 2 (Transcript.le 8 k)

theorem index_frame_length (e : Transcript.Digest) (k : Nat) : (indexFrame e k).length = 69 := by
  rw [indexFrame, frame_total_length, Transcript.le_length]

theorem index_frame_mem (L : Nat) (hL : 69 ≤ L) (e : Transcript.Digest) (k : Nat) :
    indexFrame e k ∈ boundedQueries L := by
  rw [mem_bounded_queries, index_frame_length]
  exact hL

/-- (5) **THE ROUND INDEX SEPARATES THE FRAMES OF DIFFERENT ROUNDS, WHATEVER THE
INCOMING STATE IS.**  Round `s`'s index frame is not round `r`'s index frame for
any `r ≠ s` and any pair of state digests, so this particular freshness needs no
assumption on the oracle at all. -/
theorem index_frame_ne (e e2 : Transcript.Digest) (i j : Nat)
    (hi : i < Transcript.u64Limit) (hj : j < Transcript.u64Limit) (hne : i ≠ j) :
    indexFrame e i ≠ indexFrame e2 j := by
  intro h
  obtain ⟨-, -, hpl⟩ := CommitmentOrder.frame_injective e e2 2 2 _ _ h
  exact hne (Transcript.le_injective_bounded 8 i j
    (by rw [RandomOracleSqueezes.byte_limit]; exact hi)
    (by rw [RandomOracleSqueezes.byte_limit]; exact hj) hpl)

/-- **THE STATE DIGEST AFTER `k` ABSORBS.**  A transcript chain is completely
described by its starting digest `e0` and the SHAPE of each absorb -- the tag and
the payload, both of which are fixed by the config, the statement and the proof
and do NOT depend on the table.  Only the state digest of each frame varies, and
it is the previous answer. -/
def frameState (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) :
    Nat → OracleTable (boundedQueries L) → Transcript.Digest
  | 0, _ => e0
  | k + 1, T =>
      let e := frameState L e0 shape hlen k T
      blockDigest (T ⟨Transcript.frame e (shape k).1 (shape k).2,
        bounded_queries_frame L e (shape k).1 (shape k).2 (hlen k)⟩)

/-- The stage-`k` query of a transcript chain. -/
def frameSel (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k : Nat)
    (T : OracleTable (boundedQueries L)) : { x : Transcript.Bytes // x ∈ boundedQueries L } :=
  ⟨Transcript.frame (frameState L e0 shape hlen k T) (shape k).1 (shape k).2,
    bounded_queries_frame L _ (shape k).1 (shape k).2 (hlen k)⟩

theorem frame_state_succ (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    frameState L e0 shape hlen (k + 1) T
      = blockDigest (chainVal (frameSel L e0 shape hlen) k T) := rfl

/-- (5) The chain's state digests ARE the table-backed hash of the frames: no
second serialization is introduced. -/
theorem frame_state_is_hash (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    frameState L e0 shape hlen (k + 1) T
      = hashOf (boundedQueries L) T
          (Transcript.frame (frameState L e0 shape hlen k T) (shape k).1 (shape k).2) :=
  (hash_of_at (boundedQueries L) T (frameSel L e0 shape hlen k T)).symm

/-- The one block a transcript chain must not come back to: the block of the
digest it started from.  That digest is not one of the chain's own answers, so
the pairwise clause of `noClash` cannot separate the chain from it. -/
def avoidBase (e0 : Transcript.Digest) : Finset Block :=
  {OuterChallenge.digestBlock e0}

theorem avoid_base_card (e0 : Transcript.Digest) : (avoidBase e0).card = 1 :=
  Finset.card_singleton _

/-- (5) **EVERY STAGE OF A TRANSCRIPT CHAIN IS FRESH ON THE GOOD EVENT.**  No
hypothesis on the shape function is needed: two stages `j < k` of the chain carry
DIFFERENT incoming state digests as soon as the chain has not clashed and has not
returned to its base, and `CommitmentOrder.frame_injective` turns that into
distinct queries.  This is the exact point at which a real hash differs from a
random table. -/
theorem frame_sel_ne (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k j : Nat) (hj : j < k)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (frameSel L e0 shape hlen) (avoidBase e0) k) :
    frameSel L e0 shape hlen j T ≠ frameSel L e0 shape hlen k T := by
  intro hEq
  obtain ⟨h1, h2⟩ := (mem_no_clash (frameSel L e0 shape hlen) (avoidBase e0) k T).mp hT
  obtain ⟨hst, -, -⟩ :=
    CommitmentOrder.frame_injective _ _ _ _ _ _ (congrArg Subtype.val hEq)
  obtain ⟨k2, rfl⟩ : ∃ k2, k = k2 + 1 := ⟨k - 1, by omega⟩
  cases j with
  | zero =>
      refine h2 k2 (by omega) ?_
      rw [avoidBase, Finset.mem_singleton]
      rw [frame_state_succ] at hst
      exact (congrArg OuterChallenge.digestBlock hst).symm
  | succ j2 =>
      rw [frame_state_succ, frame_state_succ] at hst
      exact h1 j2 k2 (by omega) (by omega) (congrArg OuterChallenge.digestBlock hst)

theorem frame_state_stable (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (frameSel L e0 shape hlen) (avoidBase e0) k) (b : Block) :
    ∀ j : Nat, j ≤ k →
      frameState L e0 shape hlen j (reassign T (frameSel L e0 shape hlen k T) b)
        = frameState L e0 shape hlen j T := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hmk : m < k := by omega
      have hst := ih (le_of_lt hmk)
      have hsel : frameSel L e0 shape hlen m (reassign T (frameSel L e0 shape hlen k T) b)
          = frameSel L e0 shape hlen m T := by
        apply Subtype.ext
        show Transcript.frame
            (frameState L e0 shape hlen m (reassign T (frameSel L e0 shape hlen k T) b))
            (shape m).1 (shape m).2
          = Transcript.frame (frameState L e0 shape hlen m T) (shape m).1 (shape m).2
        rw [hst]
      rw [frame_state_succ, frame_state_succ]
      show blockDigest ((reassign T (frameSel L e0 shape hlen k T) b)
          (frameSel L e0 shape hlen m (reassign T (frameSel L e0 shape hlen k T) b)))
        = blockDigest (T (frameSel L e0 shape hlen m T))
      rw [hsel, reassign_off T _ _ b (frame_sel_ne L e0 shape hlen k m hmk T hT)]

/-- (5) **A TRANSCRIPT FRAME CHAIN IS CAUSAL AND FRESH.** -/
theorem frame_chain_causal (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (n : Nat) :
    Causal (frameSel L e0 shape hlen) (avoidBase e0) n := by
  constructor
  · intro k _ j hj T hT b
    apply Subtype.ext
    show Transcript.frame
        (frameState L e0 shape hlen j (reassign T (frameSel L e0 shape hlen k T) b))
        (shape j).1 (shape j).2
      = Transcript.frame (frameState L e0 shape hlen j T) (shape j).1 (shape j).2
    rw [frame_state_stable L e0 shape hlen k T hT b j hj]
  · intro k _ j hj T hT
    exact frame_sel_ne L e0 shape hlen k j hj T hT

/-- (5) **TWO STATE DIGESTS OF A TRANSCRIPT CHAIN DIFFER ON THE GOOD EVENT.**
The generic form of `round_digests_distinct`: any two stages `a + 1 < b + 1`
inside the chain's good prefix carry different digests, whatever the shape is and
wherever the chain starts. -/
theorem frame_state_distinct_on_no_clash (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (n : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (frameSel L e0 shape hlen) (avoidBase e0) n)
    (a b : Nat) (hab : a < b) (hb : b < n) :
    frameState L e0 shape hlen (a + 1) T ≠ frameState L e0 shape hlen (b + 1) T := by
  intro heq
  obtain ⟨h1, -⟩ := (mem_no_clash (frameSel L e0 shape hlen) (avoidBase e0) n T).mp hT
  rw [frame_state_succ, frame_state_succ] at heq
  exact h1 a b hab hb (congrArg OuterChallenge.digestBlock heq)

/-- (5) **THE BIRTHDAY BOUND FOR A TRANSCRIPT FRAME CHAIN.**  Under the
random-oracle counting law on `boundedQueries L`, the mass of the event that two
of the chain's first `n` state digests coincide -- or that one of them is the
digest the chain started from -- is at most `n (n + 1) / 2` over the block space.

THIS IS THE SEQUENTIAL FRESH-QUERY ARGUMENT, CARRIED OUT.  Stage `k`'s frame
input is a fixed string once the earlier answers are fixed, and it differs from
every earlier stage's input as long as no two earlier digests already coincided;
conditioned on those answers the stage-`k` answer is uniform on `Block`, so it
hits one of the `k + 1` forbidden blocks with mass at most `(k + 1) / |Block|`. -/
theorem frame_chain_clash_probability_le (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (n : Nat) :
    oracleProbability (boundedQueries L)
        (noClash (frameSel L e0 shape hlen) (avoidBase e0) n)ᶜ
      ≤ (n : ℚ) * ((n : ℚ) + 1) / 2 / (Fintype.card Block : ℚ) := by
  have h := chain_clash_probability_le (frameSel L e0 shape hlen) (avoidBase e0) n
    (frame_chain_causal L e0 shape hlen n)
  rw [avoid_base_card] at h
  have hrw : ((n : ℚ) * ((1 : Nat) : ℚ) + (n : ℚ) * ((n : ℚ) - 1) / 2)
      = (n : ℚ) * ((n : ℚ) + 1) / 2 := by
    push_cast
    ring
  rw [hrw] at h
  exact h

theorem block_card_gt_small (m : Nat) (h : m < 65536) : m < Fintype.card Block := by
  rw [block_card]
  calc m < 65536 := h
    _ = 256 ^ 2 := by norm_num
    _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- (5) **THE GOOD EVENT IS NOT EMPTY** at every chain length `n ≤ 361`, which is
exactly the hypothesis `n (n + 1) < 2 * 65536`: the bound is strictly below `1`
there, so tables whose whole chain is pairwise distinct exist.  The conditioning
events of section 2 are therefore instantiated at non-empty events.  The chain
lengths this module uses are far smaller: `5 d ≤ 65` in section 7, and `22 + 5 d
≤ 87` once the relation prefix is prepended in section 8. -/
theorem frame_chain_no_clash_nonempty (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (n : Nat) (hn : n * (n + 1) < 2 * 65536) :
    (noClash (frameSel L e0 shape hlen) (avoidBase e0) n).Nonempty := by
  refine no_clash_nonempty (frameSel L e0 shape hlen) (avoidBase e0) n
    (frame_chain_causal L e0 shape hlen n) ?_
  rw [avoid_base_card, div_lt_one block_card_cast_pos]
  have hb : ((n * (n + 1) : Nat) : ℚ) < 2 * 65536 := by exact_mod_cast hn
  have hcn : 65536 ≤ Fintype.card Block := block_card_gt_small 65535 (by norm_num)
  have hc : (65536 : ℚ) ≤ (Fintype.card Block : ℚ) := by exact_mod_cast hcn
  have hrw : (n : ℚ) * ((1 : Nat) : ℚ) + (n : ℚ) * ((n : ℚ) - 1) / 2
      = ((n * (n + 1) : Nat) : ℚ) / 2 := by
    push_cast
    ring
  rw [hrw]
  linarith

/-- The table that answers one fixed block everywhere: the worst case for a
chain, and the table every hypothesis is tested at. -/
def constantTable (L : Nat) : OracleTable (boundedQueries L) :=
  fun _ => OuterChallenge.digestBlock OuterInitial.zeroDigest

theorem constant_table_state (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (k : Nat) :
    frameState L e0 shape hlen (k + 1) (constantTable L) = OuterInitial.zeroDigest := rfl

/-- (5) **THE CLASH EVENT IS NOT EMPTY EITHER.**  The constant table clashes at
once, so `frame_chain_clash_probability_le` is not proved by an empty event, and
the hypotheses of sections 2 and 3 are satisfied by a chain whose clash event has
members. -/
theorem constant_table_clashes (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (n : Nat) (hn : 2 ≤ n) :
    constantTable L ∈ (noClash (frameSel L e0 shape hlen) (avoidBase e0) n)ᶜ := by
  rw [mem_clash_event]
  refine Or.inl ⟨0, 1, by omega, by omega, ?_⟩
  have h0 : blockDigest (chainVal (frameSel L e0 shape hlen) 0 (constantTable L))
      = blockDigest (chainVal (frameSel L e0 shape hlen) 1 (constantTable L)) := by
    rw [← frame_state_succ, ← frame_state_succ, constant_table_state L e0 shape hlen 0,
      constant_table_state L e0 shape hlen 1]
  exact congrArg OuterChallenge.digestBlock h0

/-! ## 6. THE RUN'S OWN FIVE-FRAME ROUND FOLD -/

/-- The digest after the round domain separator, the first of the adopted
`InstalledRoundCommit.roundFrames`. -/
def stageOne (thash : Transcript.Hash) (e : Transcript.Digest) : Transcript.Digest :=
  thash (Transcript.frame e 1 (Transcript.ascii "outer-sumcheck-lockstep-round-v3"))

/-- The digest after the round-index frame, the second of the five. -/
def stageTwo (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat) : Transcript.Digest :=
  thash (indexFrame (stageOne thash e) i)

/-- The digest after the log message cell, the third of the five. -/
def stageThree (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) : Transcript.Digest :=
  thash (Transcript.frame (stageTwo thash e i) 6 (OuterAdapter.encodedVec m.1))

/-- The digest after the gate message cell, the fourth of the five. -/
def stageFour (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) : Transcript.Digest :=
  thash (Transcript.frame (stageThree thash e i m) 6 (OuterAdapter.encodedVec m.2))

/-- The round's commit digest: the answer at the challenge domain separator, the
fifth and last of the five. -/
def stageFive (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) : Transcript.Digest :=
  thash (Transcript.frame (stageFour thash e i m) 1
    (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3"))

/-- (6) The adopted `OuterAdapter.roundCommitted` IS this five-stage fold.
Nothing is re-serialized: `rfl`. -/
theorem round_commit_is_stage_five (thash : Transcript.Hash) (s : Transcript.State) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (OuterAdapter.roundCommitted thash s i m.1 m.2).digest = stageFive thash s.digest i m := rfl

/-- (6) The chain's index frame IS the adopted round-index frame. -/
theorem index_frame_is_round_index_frame (e : Transcript.Digest) (i : Nat) :
    indexFrame e i
      = Transcript.frame e (OuterInitial.Message.tag ⟨2, Transcript.le 8 i⟩)
          (OuterInitial.Message.payload ⟨2, Transcript.le 8 i⟩) := rfl

/-- **THE FIVE STRINGS THE ORACLE IS ASKED ABOUT IN ROUND `i`**, in the source
order of the adopted `InstalledRoundCommit.roundFrames`, from the incoming digest
`e`: the round domain separator, the round-index frame, the log message cell, the
gate message cell and the challenge domain separator.  These are the FRAME INPUTS
of the fold, not its digests, and they are what a collision claim below is about. -/
def stageQueries (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) : List Transcript.Bytes :=
  [Transcript.frame e 1 (Transcript.ascii "outer-sumcheck-lockstep-round-v3"),
   indexFrame (stageOne thash e) i,
   Transcript.frame (stageTwo thash e i) 6 (OuterAdapter.encodedVec m.1),
   Transcript.frame (stageThree thash e i m) 6 (OuterAdapter.encodedVec m.2),
   Transcript.frame (stageFour thash e i m) 1
     (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3")]

theorem stage_queries_length (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) : (stageQueries thash e i m).length = 5 := rfl

theorem stage_queries_get_zero (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (stageQueries thash e i m).get? 0
      = some (Transcript.frame e 1 (Transcript.ascii "outer-sumcheck-lockstep-round-v3")) := rfl

theorem stage_queries_get_one (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (stageQueries thash e i m).get? 1 = some (indexFrame (stageOne thash e) i) := rfl

theorem stage_queries_get_two (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (stageQueries thash e i m).get? 2
      = some (Transcript.frame (stageTwo thash e i) 6 (OuterAdapter.encodedVec m.1)) := rfl

theorem stage_queries_get_three (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (stageQueries thash e i m).get? 3
      = some (Transcript.frame (stageThree thash e i m) 6 (OuterAdapter.encodedVec m.2)) := rfl

theorem stage_queries_get_four (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (stageQueries thash e i m).get? 4
      = some (Transcript.frame (stageFour thash e i m) 1
          (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3")) := rfl

/-- (6) The oracle answer at stage `k` of a round's own five queries is that
round's stage-`k + 1` digest: the list above is the fold, read as strings. -/
theorem stage_queries_answer (thash : Transcript.Hash) (e : Transcript.Digest) (i : Nat)
    (m : Verifier.CoupledMessage) :
    ((stageQueries thash e i m).map thash)
      = [stageOne thash e, stageTwo thash e i, stageThree thash e i m,
         stageFour thash e i m, stageFive thash e i m] := rfl

/-- (6) **TWO ROUNDS WITH THE SAME COMMIT DIGEST COLLIDE AT THE SAME POSITION OF
THEIR OWN FIVE-FRAME FOLDS.**  Walk the five stages backwards: at the first stage
where the incoming digests differ, the two frames AT THAT POSITION are distinct
queries with equal answers; and if the walk reaches the round-index frame --
position `1` -- those two frames are distinct OUTRIGHT because the round indices
differ.  So a round-digest clash is never a "collision somewhere in an infinite
string space": the conclusion NAMES a position `k < 5` and produces the two
strings at that position of `stageQueries`, which are frames of the two clashing
rounds and of nothing else. -/
theorem stage_five_clash_collision (thash : Transcript.Hash) (e e2 : Transcript.Digest)
    (i j : Nat) (m m2 : Verifier.CoupledMessage)
    (hi : i < Transcript.u64Limit) (hj : j < Transcript.u64Limit) (hij : i ≠ j)
    (h : stageFive thash e i m = stageFive thash e2 j m2) :
    ∃ k, k < 5 ∧ ∃ x y : Transcript.Bytes,
      (stageQueries thash e i m).get? k = some x ∧
      (stageQueries thash e2 j m2).get? k = some y ∧
      x ≠ y ∧ thash x = thash y := by
  by_cases h4 : stageFour thash e i m = stageFour thash e2 j m2
  · by_cases h3 : stageThree thash e i m = stageThree thash e2 j m2
    · by_cases h2 : stageTwo thash e i = stageTwo thash e2 j
      · exact ⟨1, by omega, indexFrame (stageOne thash e) i, indexFrame (stageOne thash e2) j,
          stage_queries_get_one thash e i m, stage_queries_get_one thash e2 j m2,
          index_frame_ne _ _ i j hi hj hij, h2⟩
      · refine ⟨2, by omega,
          Transcript.frame (stageTwo thash e i) 6 (OuterAdapter.encodedVec m.1),
          Transcript.frame (stageTwo thash e2 j) 6 (OuterAdapter.encodedVec m2.1),
          stage_queries_get_two thash e i m, stage_queries_get_two thash e2 j m2, ?_, h3⟩
        intro hq
        exact h2 (CommitmentOrder.frame_injective _ _ _ _ _ _ hq).1
    · refine ⟨3, by omega,
        Transcript.frame (stageThree thash e i m) 6 (OuterAdapter.encodedVec m.2),
        Transcript.frame (stageThree thash e2 j m2) 6 (OuterAdapter.encodedVec m2.2),
        stage_queries_get_three thash e i m, stage_queries_get_three thash e2 j m2, ?_, h4⟩
      intro hq
      exact h3 (CommitmentOrder.frame_injective _ _ _ _ _ _ hq).1
  · refine ⟨4, by omega,
      Transcript.frame (stageFour thash e i m) 1
        (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3"),
      Transcript.frame (stageFour thash e2 j m2) 1
        (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3"),
      stage_queries_get_four thash e i m, stage_queries_get_four thash e2 j m2, ?_, h⟩
    intro hq
    exact h4 (CommitmentOrder.frame_injective _ _ _ _ _ _ hq).1

/-- (6) The weak form of the walk, with the positions and the strings FORGOTTEN.
This is literally `CommitmentOrder.TranscriptCollision thash`, and on its own it
is a TAUTOLOGY about any non-injective function: it is recorded only so that the
strengthening above can be compared with it. -/
theorem stage_five_clash_transcript_collision (thash : Transcript.Hash)
    (e e2 : Transcript.Digest) (i j : Nat) (m m2 : Verifier.CoupledMessage)
    (hi : i < Transcript.u64Limit) (hj : j < Transcript.u64Limit) (hij : i ≠ j)
    (h : stageFive thash e i m = stageFive thash e2 j m2) :
    CommitmentOrder.TranscriptCollision thash := by
  obtain ⟨-, -, x, y, -, -, hxy, hh⟩ := stage_five_clash_collision thash e e2 i j m m2 hi hj hij h
  exact ⟨x, y, hxy, hh⟩

/-- The coupled messages of a run, as the adopted `InstalledRoundCommit` reads
them off the proof. -/
def roundMessages (p : Verifier.Proof) : List Verifier.CoupledMessage :=
  p.logRounds.zip p.gateRounds

/-- Round `r`'s coupled message pair. -/
def roundMessage (p : Verifier.Proof) (r : Nat) : Verifier.CoupledMessage :=
  ((roundMessages p).get? r).getD ([], [])

/-- The digest round `r` commits ONTO: the state left by rounds `< r`, starting
from the adopted `OuterInitial.derive` state. -/
def roundIncoming (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof)
    (r : Nat) : Transcript.Digest :=
  (InstalledRoundCommit.concreteFinal thash
    (OuterInitial.derive thash c (Verifier.statement p)).state 0
    ((roundMessages p).take r)).digest

theorem round_message_get (p : Verifier.Proof) (r : Nat) (hr : r < (roundMessages p).length) :
    roundMessage p r = (roundMessages p).get ⟨r, hr⟩ := by
  rw [roundMessage, List.get?_eq_get hr, Option.getD_some]

/-- (6) **THE ADOPTED `RoundDigestClash` LOCALIZES TO A COLLISION AT THE SAME
POSITION OF TWO NAMED ROUND FOLDS.**  The conclusion is NOT
`CommitmentOrder.TranscriptCollision`: it produces two round indices `r != s` of
this run, a position `k < 5`, and the two strings at position `k` of
`stageQueries` for round `r` and for round `s` -- built from the run's own
incoming digests `roundIncoming` and its own message pairs `roundMessage` --
which are distinct and have the same oracle answer.  That is strictly sharper
than the adopted `chain_digest_binds_round`, whose alternative is the GLOBAL
collision predicate and therefore says nothing about where to look. -/
theorem round_digest_clash_gives_round_frame_collision (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : (roundMessages p).length = c.degreeBits) (hdb : c.degreeBits ≤ 13)
    (h : RandomOracleSqueezes.RoundDigestClash thash c p) :
    ∃ r s : Nat, r ≠ s ∧ r < c.degreeBits ∧ s < c.degreeBits ∧
      ∃ k, k < 5 ∧ ∃ x y : Transcript.Bytes,
        (stageQueries thash (roundIncoming thash c p r) r (roundMessage p r)).get? k = some x ∧
        (stageQueries thash (roundIncoming thash c p s) s (roundMessage p s)).get? k = some y ∧
        x ≠ y ∧ thash x = thash y := by
  obtain ⟨r, s, hrs, heq⟩ := h
  have hr : r.val < (roundMessages p).length := by rw [hlen]; exact r.isLt
  have hs : s.val < (roundMessages p).length := by rw [hlen]; exact s.isLt
  have hrv := r.isLt
  have hsv := s.isLt
  have hne : r.val ≠ s.val := fun hij => hrs (Fin.ext hij)
  simp only [RandomOracleSqueezes.sourceDigest, InstalledRoundCommit.actualChain] at heq
  rw [show p.logRounds.zip p.gateRounds = roundMessages p from rfl,
    InstalledRoundCommit.concrete_chain_get thash _ _ 0 r.val hr,
    InstalledRoundCommit.concrete_chain_get thash _ _ 0 s.val hs,
    Option.getD_some, Option.getD_some, round_commit_is_stage_five,
    round_commit_is_stage_five, Nat.zero_add, Nat.zero_add,
    ← round_message_get p r.val hr, ← round_message_get p s.val hs] at heq
  refine ⟨r.val, s.val, hne, hrv, hsv,
    stage_five_clash_collision thash _ _ r.val s.val _ _ ?_ ?_ hne heq⟩
  · unfold Transcript.u64Limit; omega
  · unfold Transcript.u64Limit; omega

/-- (6) The weak, TAUTOLOGICAL form of the localization, kept for comparison: the
adopted `CommitmentOrder.TranscriptCollision` with the round indices, the
position and the two strings all forgotten.  Everything of value in the theorem
above is the data this corollary throws away. -/
theorem round_digest_clash_gives_transcript_collision (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : (roundMessages p).length = c.degreeBits) (hdb : c.degreeBits ≤ 13)
    (h : RandomOracleSqueezes.RoundDigestClash thash c p) :
    CommitmentOrder.TranscriptCollision thash := by
  obtain ⟨-, -, -, -, -, -, -, x, y, -, -, hxy, hh⟩ :=
    round_digest_clash_gives_round_frame_collision thash c p hlen hdb h
  exact ⟨x, y, hxy, hh⟩

/-! ## 7. THE ADOPTED COUPLED-ROUND FOLD AS A TRANSCRIPT FRAME CHAIN -/

/-- The shape of the `j`-th of the five frames of coupled round `i`, in the
source order of the adopted `InstalledRoundCommit.roundFrames`. -/
def roundShapeAt (ms : List Verifier.CoupledMessage) (i : Nat) :
    Nat → Transcript.Byte × Transcript.Bytes
  | 0 => (1, Transcript.ascii "outer-sumcheck-lockstep-round-v3")
  | 1 => (2, Transcript.le 8 i)
  | 2 => (6, OuterAdapter.encodedVec ((ms.get? i).getD ([], [])).1)
  | 3 => (6, OuterAdapter.encodedVec ((ms.get? i).getD ([], [])).2)
  | _ => (1, Transcript.ascii "outer-sumcheck-lockstep-challenges-v3")

/-- Five stages per round: stage `k` is frame `k % 5` of round `k / 5`. -/
def roundShape (ms : List Verifier.CoupledMessage) (k : Nat) :
    Transcript.Byte × Transcript.Bytes :=
  roundShapeAt ms (k / 5) (k % 5)

theorem round_shape_at (ms : List Verifier.CoupledMessage) (i j : Nat) (hj : j < 5) :
    roundShape ms (5 * i + j) = roundShapeAt ms i j := by
  rw [roundShape, show (5 * i + j) / 5 = i from by omega,
    show (5 * i + j) % 5 = j from by omega]

theorem round_shape_zero (ms : List Verifier.CoupledMessage) (i : Nat) :
    roundShape ms (5 * i) = roundShapeAt ms i 0 := by
  have h := round_shape_at ms i 0 (by omega)
  rw [show 5 * i + 0 = 5 * i from by omega] at h
  exact h

theorem round_shape_tag_zero (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i)).1 = 1 := by
  rw [round_shape_zero ms i]
  rfl

theorem round_shape_payload_zero (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i)).2 = Transcript.ascii "outer-sumcheck-lockstep-round-v3" := by
  rw [round_shape_zero ms i]
  rfl

theorem round_shape_tag_one (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 1)).1 = 2 := by
  rw [round_shape_at ms i 1 (by omega)]
  rfl

theorem round_shape_payload_one (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 1)).2 = Transcript.le 8 i := by
  rw [round_shape_at ms i 1 (by omega)]
  rfl

theorem round_shape_tag_two (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 2)).1 = 6 := by
  rw [round_shape_at ms i 2 (by omega)]
  rfl

theorem round_shape_payload_two (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 2)).2
      = OuterAdapter.encodedVec ((ms.get? i).getD ([], [])).1 := by
  rw [round_shape_at ms i 2 (by omega)]
  rfl

theorem round_shape_tag_three (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 3)).1 = 6 := by
  rw [round_shape_at ms i 3 (by omega)]
  rfl

theorem round_shape_payload_three (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 3)).2
      = OuterAdapter.encodedVec ((ms.get? i).getD ([], [])).2 := by
  rw [round_shape_at ms i 3 (by omega)]
  rfl

theorem round_shape_tag_four (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 4)).1 = 1 := by
  rw [round_shape_at ms i 4 (by omega)]
  rfl

theorem round_shape_payload_four (ms : List Verifier.CoupledMessage) (i : Nat) :
    (roundShape ms (5 * i + 4)).2
      = Transcript.ascii "outer-sumcheck-lockstep-challenges-v3" := by
  rw [round_shape_at ms i 4 (by omega)]
  rfl

theorem round_separator_length :
    (Transcript.ascii "outer-sumcheck-lockstep-round-v3").length = 32 := by decide

theorem challenge_separator_length :
    (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3").length = 37 := by decide

/-- (7) **`boundedQueries L` CONTAINS EVERY FRAME OF THE RUN'S ROUND FOLD.**  The
length budget is explicit: `61` bytes of framing, a `37`-byte domain separator at
worst, the eight index bytes, and the two encoded message cells, whose lengths
are fixed by the proof.  This is the hypothesis `hlen` of the chain, discharged. -/
theorem round_shape_payload_bound (L : Nat) (ms : List Verifier.CoupledMessage) (hL : 98 ≤ L)
    (hlog : ∀ i, 61 + (OuterAdapter.encodedVec ((ms.get? i).getD ([], [])).1).length ≤ L)
    (hgate : ∀ i, 61 + (OuterAdapter.encodedVec ((ms.get? i).getD ([], [])).2).length ≤ L) :
    ∀ k, 61 + (roundShape ms k).2.length ≤ L := by
  intro k
  have hk : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rw [roundShape]
  rcases hk with h | h | h | h | h <;> rw [h]
  · show 61 + (Transcript.ascii "outer-sumcheck-lockstep-round-v3").length ≤ L
    rw [round_separator_length]
    omega
  · show 61 + (Transcript.le 8 (k / 5)).length ≤ L
    rw [Transcript.le_length]
    omega
  · exact hlog (k / 5)
  · exact hgate (k / 5)
  · show 61 + (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3").length ≤ L
    rw [challenge_separator_length]
    omega

/-- (7) **THE CHAIN'S LENGTH HYPOTHESIS, FROM DEGREE BOUNDS ALONE.**  The adopted
`OuterAdapter.encoded_vector_length` makes a message cell exactly
`8 + 24 * length` bytes, so a bound on the NUMBER OF COEFFICIENTS in each lane
fixes the budget outright and no hypothesis about byte payloads survives. -/
theorem round_shape_payload_bound_of_degree (L : Nat) (ms : List Verifier.CoupledMessage)
    (dlog dgate : Nat) (hL : 98 ≤ L)
    (hlog : ∀ i, ((ms.get? i).getD ([], [])).1.length ≤ dlog)
    (hgate : ∀ i, ((ms.get? i).getD ([], [])).2.length ≤ dgate)
    (hLlog : 69 + 24 * dlog ≤ L) (hLgate : 69 + 24 * dgate ≤ L) :
    ∀ k, 61 + (roundShape ms k).2.length ≤ L := by
  refine round_shape_payload_bound L ms hL ?_ ?_
  · intro i
    rw [OuterAdapter.encoded_vector_length]
    have h := hlog i
    have : 24 * ((ms.get? i).getD ([], [])).1.length ≤ 24 * dlog := Nat.mul_le_mul_left 24 h
    omega
  · intro i
    rw [OuterAdapter.encoded_vector_length]
    have h := hgate i
    have : 24 * ((ms.get? i).getD ([], [])).2.length ≤ 24 * dgate := Nat.mul_le_mul_left 24 h
    omega

/-- (7) **THE LENGTH HYPOTHESIS AT THE ADOPTED DEGREE BOUNDS.**  The two degree
bounds `run_bad_draw_probability_le_of_clash_bound` already carries -- `5` on the
log lane and `quotientDegree + 2` on the gate lane, exactly its `hlogDeg` and
`hgateDeg` -- discharge the chain's `hlen` as soon as `L` clears
`189 + 24 * quotientDegree`.  So the query set `boundedQueries L` of section 4 is
large enough for the run's own frames at a size read off the envelope. -/
theorem round_shape_payload_bound_at_envelope (L : Nat) (ms : List Verifier.CoupledMessage)
    (quotientDegree : Nat)
    (hlog : ∀ i, ((ms.get? i).getD ([], [])).1.length ≤ 5)
    (hgate : ∀ i, ((ms.get? i).getD ([], [])).2.length ≤ quotientDegree + 2)
    (hL : 189 + 24 * quotientDegree ≤ L) :
    ∀ k, 61 + (roundShape ms k).2.length ≤ L :=
  round_shape_payload_bound_of_degree L ms 5 (quotientDegree + 2) (by omega) hlog hgate
    (by omega) (by omega)

/-- (7) **FIVE STAGES OF THE CHAIN ARE ONE ADOPTED COUPLED ROUND.**  The chain's
state digest after `5 i + 5` absorbs is the adopted `roundCommitted` fold of
round `i` -- written through `stageFive` of section 6 -- applied to its state
digest after `5 i` absorbs.  Nothing is re-serialized: the five frames are the
adopted `InstalledRoundCommit.roundFrames`. -/
theorem round_chain_step (L : Nat) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (roundShape ms k).2.length ≤ L) (e0 : Transcript.Digest)
    (T : OracleTable (boundedQueries L)) (i : Nat) :
    frameState L e0 (roundShape ms) hlen (5 * i + 5) T
      = stageFive (hashOf (boundedQueries L) T)
          (frameState L e0 (roundShape ms) hlen (5 * i) T) i
          ((ms.get? i).getD ([], [])) := by
  simp only [stageFive, stageFour, stageThree, stageTwo, stageOne, indexFrame]
  rw [show 5 * i + 5 = 5 * i + 4 + 1 from by omega, frame_state_is_hash,
    round_shape_tag_four, round_shape_payload_four,
    show 5 * i + 4 = 5 * i + 3 + 1 from by omega, frame_state_is_hash,
    round_shape_tag_three, round_shape_payload_three,
    show 5 * i + 3 = 5 * i + 2 + 1 from by omega, frame_state_is_hash,
    round_shape_tag_two, round_shape_payload_two,
    show 5 * i + 2 = 5 * i + 1 + 1 from by omega, frame_state_is_hash,
    round_shape_tag_one, round_shape_payload_one,
    frame_state_is_hash, round_shape_tag_zero, round_shape_payload_zero]

/-- (7) **THE RUN'S ROUND COMMIT DIGESTS ARE PAIRWISE DISTINCT ON THE GOOD
EVENT.**  This is the localized `RoundDigestClash` refuted, table by table, for
the chain model of the adopted fold. -/
theorem round_digests_distinct (L : Nat) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (roundShape ms k).2.length ≤ L) (e0 : Transcript.Digest) (n : Nat)
    (T : OracleTable (boundedQueries L))
    (hT : T ∈ noClash (frameSel L e0 (roundShape ms) hlen) (avoidBase e0) n)
    (r s : Nat) (hrs : r < s) (hs : 5 * s + 4 < n) :
    frameState L e0 (roundShape ms) hlen (5 * r + 5) T
      ≠ frameState L e0 (roundShape ms) hlen (5 * s + 5) T := by
  intro heq
  obtain ⟨h1, -⟩ := (mem_no_clash (frameSel L e0 (roundShape ms) hlen) (avoidBase e0) n T).mp hT
  rw [show 5 * r + 5 = 5 * r + 4 + 1 from by omega,
    show 5 * s + 5 = 5 * s + 4 + 1 from by omega, frame_state_succ, frame_state_succ] at heq
  exact h1 (5 * r + 4) (5 * s + 4) (by omega) hs (congrArg OuterChallenge.digestBlock heq)

open Classical in
/-- The event that two DIFFERENT coupled rounds of the chain commit to the same
digest: the chain-model form of the adopted
`RandomOracleSqueezes.RoundDigestClash`. -/
noncomputable def roundDigestClashEvent (L : Nat) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (roundShape ms k).2.length ≤ L) (e0 : Transcript.Digest) (d : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ∃ r s : Nat, r < s ∧ s < d ∧
    frameState L e0 (roundShape ms) hlen (5 * r + 5) T
      = frameState L e0 (roundShape ms) hlen (5 * s + 5) T)

theorem round_digest_clash_event_subset (L : Nat) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (roundShape ms k).2.length ≤ L) (e0 : Transcript.Digest) (d : Nat) :
    roundDigestClashEvent L ms hlen e0 d
      ⊆ (noClash (frameSel L e0 (roundShape ms) hlen) (avoidBase e0) (5 * d))ᶜ := by
  intro T hT
  simp only [roundDigestClashEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨r, s, hrs, hsd, heq⟩ := hT
  by_contra hgood
  rw [Finset.not_mem_compl] at hgood
  exact round_digests_distinct L ms hlen e0 (5 * d) T hgood r s hrs (by omega) heq

/-- (7) **THE ROUND-DIGEST CLASH EVENT IS NOT EMPTY EITHER.**  The constant table
is IN it already at `d = 2`: rounds `0` and `1` of the chain model commit to the
same digest, because every answer of that table is `OuterInitial.zeroDigest`.  So
`round_digest_clash_mass_le` is NOT a bound proved on an empty event, and
`round_digest_clash_event_subset` is not a vacuous inclusion. -/
theorem constant_table_in_round_clash_event (L : Nat) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (roundShape ms k).2.length ≤ L) (e0 : Transcript.Digest) :
    constantTable L ∈ roundDigestClashEvent L ms hlen e0 2 := by
  simp only [roundDigestClashEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨0, 1, by omega, by omega, ?_⟩
  rw [show 5 * 0 + 5 = 4 + 1 from rfl, show 5 * 1 + 5 = 9 + 1 from rfl,
    constant_table_state, constant_table_state]

/-- (7) **THE BIRTHDAY BOUND ON THE RUN'S ROUND-DIGEST CLASH.**  Under the
random-oracle counting law on `boundedQueries L`, the mass of the event that two
of the `d` coupled rounds of the adopted five-frame fold commit to the same
digest is at most `5 d (5 d + 1) / 2` over the block space.

This is the birthday count the third review of `RandomOracleSqueezes` asked for,
for the CHAIN MODEL of the adopted round fold.  See the header for exactly which
bookkeeping step still separates this chain from
`InstalledRoundCommit.actualChain`. -/
theorem round_digest_clash_mass_le (L : Nat) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (roundShape ms k).2.length ≤ L) (e0 : Transcript.Digest) (d : Nat) :
    oracleProbability (boundedQueries L) (roundDigestClashEvent L ms hlen e0 d)
      ≤ ((5 * d : Nat) : ℚ) * (((5 * d : Nat) : ℚ) + 1) / 2 / (Fintype.card Block : ℚ) :=
  le_trans
    (oracle_probability_mono _ _ _ (round_digest_clash_event_subset L ms hlen e0 d))
    (frame_chain_clash_probability_le L e0 (roundShape ms) hlen (5 * d))

/-- (7) **THE BOUND AT THE ENVELOPE'S `degreeBits = 13`**: `2145 / |Block|`, with
`|Block| = 256 ^ 32` by the adopted `block_card`.  The denominator is
never evaluated; only `2145 < 65536 = 256 ^ 2 ≤ 256 ^ 32` is used. -/
theorem round_digest_clash_mass_at_thirteen (L : Nat) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (roundShape ms k).2.length ≤ L) (e0 : Transcript.Digest) :
    oracleProbability (boundedQueries L) (roundDigestClashEvent L ms hlen e0 13)
      ≤ 2145 / (Fintype.card Block : ℚ) := by
  have h := round_digest_clash_mass_le L ms hlen e0 13
  have hnum : ((5 * 13 : Nat) : ℚ) * (((5 * 13 : Nat) : ℚ) + 1) / 2 = 2145 := by norm_num
  rw [hnum] at h
  exact h

theorem round_digest_clash_bound_lt_one : (2145 : ℚ) / (Fintype.card Block : ℚ) < 1 := by
  rw [div_lt_one block_card_cast_pos]
  exact_mod_cast block_card_gt_small 2145 (by norm_num)

/-! ## 8. THE RELATION PREFIX, PREPENDED: THE CHAIN FROM `zeroDigest` -/

/-- **THE CHAIN'S STATE DIGEST, WITH THE TABLE REPLACED BY A PLAIN HASH.**  The
same recursion as `frameState`, with no membership proof carried: `frameState` IS
this, at the table-backed hash (`frame_state_is_fold`).  Everything in this
section is bookkeeping about the shape function, and this is the form in which it
is cheapest to do. -/
def foldDigest (thash : Transcript.Hash) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes) : Nat → Transcript.Digest
  | 0 => e0
  | k + 1 =>
      thash (Transcript.frame (foldDigest thash e0 shape k) (shape k).1 (shape k).2)

/-- (8) The chain of section 5 IS this fold, at the table-backed hash. -/
theorem frame_state_is_fold (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L) (T : OracleTable (boundedQueries L)) :
    ∀ k, frameState L e0 shape hlen k T
      = foldDigest (hashOf (boundedQueries L) T) e0 shape k
  | 0 => rfl
  | k + 1 => by
      rw [frame_state_is_hash, frame_state_is_fold L e0 shape hlen T k]
      rfl

/-- (8) **THE FOLD SPLITS AT ANY STAGE.**  Running `a + b` absorbs is running `a`
of them and then running `b` more from the digest they left, with the shape
shifted by `a`.  This is what lets a prefix be prepended to the round chain
without touching section 3's counting. -/
theorem fold_digest_add (thash : Transcript.Hash) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes) (a : Nat) :
    ∀ b : Nat, foldDigest thash e0 shape (a + b)
      = foldDigest thash (foldDigest thash e0 shape a) (fun j => shape (a + j)) b
  | 0 => rfl
  | b + 1 => by
      show thash (Transcript.frame (foldDigest thash e0 shape (a + b)) (shape (a + b)).1
        (shape (a + b)).2) = _
      rw [fold_digest_add thash e0 shape a b]
      rfl

/-- (8) The one-step form of the split: peel the FIRST absorb instead of the
last. -/
theorem fold_digest_shift (thash : Transcript.Hash) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes) :
    ∀ k : Nat, foldDigest thash e0 shape (k + 1)
      = foldDigest thash (thash (Transcript.frame e0 (shape 0).1 (shape 0).2))
          (fun j => shape (j + 1)) k
  | 0 => rfl
  | k + 1 => by
      show thash (Transcript.frame (foldDigest thash e0 shape (k + 1)) (shape (k + 1)).1
        (shape (k + 1)).2) = _
      rw [fold_digest_shift thash e0 shape k]
      rfl

/-- The shape of the `k`-th frame of a LIST of adopted `OuterInitial.Message`s.
Past the end of the list this is an arbitrary empty domain frame; only the first
`msgs.length` entries are ever read. -/
def messageShape (msgs : List OuterInitial.Message) (k : Nat) :
    Transcript.Byte × Transcript.Bytes :=
  match msgs.get? k with
  | some m => (m.tag, m.payload)
  | none => (1, [])

/-- (8) **A FRAME CHAIN OVER A MESSAGE LIST IS THE ADOPTED `absorbMessages`.**
No re-serialization: the chain's digest after `msgs.length` absorbs IS the digest
of the adopted fold of those very messages. -/
theorem fold_digest_absorb (thash : Transcript.Hash) :
    ∀ (msgs : List OuterInitial.Message) (e0 : Transcript.Digest)
      (shape : Nat → Transcript.Byte × Transcript.Bytes),
      (∀ j, j < msgs.length → shape j = messageShape msgs j) →
      foldDigest thash e0 shape msgs.length
        = (OuterInitial.absorbMessages thash ⟨e0, 0⟩ msgs).digest
  | [], _, _, _ => rfl
  | m :: rest, e0, shape, hs => by
      have h0 : shape 0 = (m.tag, m.payload) := hs 0 (Nat.succ_pos _)
      have hrest : ∀ j, j < rest.length → (fun j2 => shape (j2 + 1)) j = messageShape rest j :=
        fun j hj => hs (j + 1) (Nat.succ_lt_succ hj)
      calc foldDigest thash e0 shape (rest.length + 1)
          = foldDigest thash (thash (Transcript.frame e0 (shape 0).1 (shape 0).2))
              (fun j => shape (j + 1)) rest.length :=
            fold_digest_shift thash e0 shape rest.length
        _ = foldDigest thash (thash (Transcript.frame e0 m.tag m.payload))
              (fun j => shape (j + 1)) rest.length := by rw [h0]
        _ = (OuterInitial.absorbMessages thash
              ⟨thash (Transcript.frame e0 m.tag m.payload), 0⟩ rest).digest :=
            fold_digest_absorb thash rest _ _ hrest
        _ = (OuterInitial.absorbMessages thash ⟨e0, 0⟩ (m :: rest)).digest := rfl

/-- **THE WHOLE RUN'S SHAPE, FROM `OuterInitial.zeroDigest`.**  The twenty-two
frames of the adopted `CommitmentOrder.gateChallengeFrames` -- the relation
prefix -- and then the five-frames-per-round `roundShape`.  This is the shape
HONESTY (iii)(a) named as missing; it is written here. -/
def prefixRoundShape (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (k : Nat) : Transcript.Byte × Transcript.Bytes :=
  if k < 22 then messageShape (CommitmentOrder.gateChallengeFrames c s) k
  else roundShape ms (k - 22)

theorem prefix_round_shape_prefix (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (k : Nat) (hk : k < 22) :
    prefixRoundShape c s ms k = messageShape (CommitmentOrder.gateChallengeFrames c s) k :=
  if_pos hk

theorem prefix_round_shape_round (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (k : Nat) :
    prefixRoundShape c s ms (22 + k) = roundShape ms k := by
  rw [prefixRoundShape, if_neg (by omega), show 22 + k - 22 = k from by omega]

theorem prefix_round_shape_len (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L) :
    ∀ k, 61 + (roundShape ms k).2.length ≤ L := by
  intro k
  rw [← prefix_round_shape_round c s ms k]
  exact hlen (22 + k)

/-- (8) **THE LENGTH BUDGET FOR THE WHOLE CHAIN.**  Twenty-two prefix payloads
plus the round payloads; the prefix ones are the proof's and the config's own
data (public inputs, roots, metadata) and are therefore a hypothesis, exactly as
the message cells are in section 7. -/
theorem prefix_round_shape_payload_bound (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hround : ∀ k, 61 + (roundShape ms k).2.length ≤ L) :
    ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L := by
  intro k
  by_cases hk : k < 22
  · rw [prefix_round_shape_prefix c s ms k hk]
    exact hpre k hk
  · rw [prefixRoundShape, if_neg hk]
    exact hround (k - 22)

/-- (8) **THE CHAIN'S DIGEST AFTER TWENTY-TWO ABSORBS IS THE ADOPTED
`OuterInitial.derive` DIGEST.**  This is HONESTY (iii)(a) DISCHARGED: the base of
the round chain is no longer a parameter.  The chain starts at the genuinely
fixed `OuterInitial.zeroDigest`, and the digest it reaches after the adopted
twenty-two-frame relation prefix IS the digest the adopted
`InstalledRoundCommit.actualChain` starts from, by the adopted
`CommitmentOrder.prefix_state_is_relation_state` and
`OuterInitial.derived_final_digest`.  No new serialization is introduced. -/
theorem prefix_fold_is_derive_digest (thash : Transcript.Hash) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) :
    foldDigest thash OuterInitial.zeroDigest (prefixRoundShape c s ms) 22
      = (OuterInitial.derive thash c s).state.digest := by
  have hmsgs : ∀ j, j < (CommitmentOrder.gateChallengeFrames c s).length →
      prefixRoundShape c s ms j
        = messageShape (CommitmentOrder.gateChallengeFrames c s) j := by
    intro j hj
    exact prefix_round_shape_prefix c s ms j (by
      rw [CommitmentOrder.prefix_frame_count] at hj
      exact hj)
  have h := fold_digest_absorb thash (CommitmentOrder.gateChallengeFrames c s)
    OuterInitial.zeroDigest (prefixRoundShape c s ms) hmsgs
  rw [CommitmentOrder.prefix_frame_count] at h
  rw [h, OuterInitial.derived_final_digest]
  exact congrArg Transcript.State.digest
    (CommitmentOrder.prefix_state_is_relation_state thash c s)

/-- (8) **THE CHAIN'S DIGEST AFTER TWENTY-TWO ABSORBS, AS A TABLE EVENT.** -/
theorem prefix_state_is_derive_digest (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) :
    frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen 22 T
      = (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state.digest := by
  rw [frame_state_is_fold, prefix_fold_is_derive_digest]

/-- (8) **FIVE STAGES AFTER THE PREFIX ARE ONE ADOPTED COUPLED ROUND, FROM THE
ADOPTED BASE.**  `round_chain_step` with the parameter base digest replaced by
the run's own: stages `22 + 5 i` to `22 + 5 i + 5` of the chain from
`OuterInitial.zeroDigest` are the adopted `OuterAdapter.roundCommitted` fold of
round `i`. -/
theorem prefix_round_chain_step (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) (i : Nat) :
    frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen (22 + (5 * i + 5)) T
      = stageFive (hashOf (boundedQueries L) T)
          (frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen (22 + 5 * i) T) i
          ((ms.get? i).getD ([], [])) := by
  have hround := prefix_round_shape_len L c s ms hlen
  have hshape : (fun j => prefixRoundShape c s ms (22 + j)) = roundShape ms :=
    funext (fun j => prefix_round_shape_round c s ms j)
  have hsplit : ∀ b : Nat,
      frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen (22 + b) T
        = frameState L
            (foldDigest (hashOf (boundedQueries L) T) OuterInitial.zeroDigest
              (prefixRoundShape c s ms) 22) (roundShape ms) hround b T := by
    intro b
    rw [frame_state_is_fold, frame_state_is_fold,
      fold_digest_add (hashOf (boundedQueries L) T) OuterInitial.zeroDigest
        (prefixRoundShape c s ms) 22 b, hshape]
  rw [hsplit (5 * i + 5), hsplit (5 * i)]
  exact round_chain_step L ms hround _ T i

open Classical in
/-- The event that two DIFFERENT coupled rounds of the WHOLE chain -- prefix and
rounds, from `OuterInitial.zeroDigest` -- commit to the same digest. -/
noncomputable def prefixRoundDigestClashEvent (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L) (d : Nat) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ∃ r t : Nat, r < t ∧ t < d ∧
    frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen (22 + (5 * r + 5)) T
      = frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen
          (22 + (5 * t + 5)) T)

theorem prefix_round_digest_clash_event_subset (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L) (d : Nat) :
    prefixRoundDigestClashEvent L c s ms hlen d
      ⊆ (noClash (frameSel L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen)
          (avoidBase OuterInitial.zeroDigest) (22 + 5 * d))ᶜ := by
  intro T hT
  simp only [prefixRoundDigestClashEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨r, t, hrt, htd, heq⟩ := hT
  by_contra hgood
  rw [Finset.not_mem_compl] at hgood
  rw [show 22 + (5 * r + 5) = (22 + 5 * r + 4) + 1 from by omega,
    show 22 + (5 * t + 5) = (22 + 5 * t + 4) + 1 from by omega] at heq
  exact frame_state_distinct_on_no_clash L OuterInitial.zeroDigest (prefixRoundShape c s ms)
    hlen (22 + 5 * d) T hgood (22 + 5 * r + 4) (22 + 5 * t + 4) (by omega) (by omega) heq

/-- (8) **THE BIRTHDAY BOUND ON THE WHOLE RUN'S ROUND-DIGEST CLASH.**  The chain
now runs from `OuterInitial.zeroDigest` through the adopted twenty-two-frame
relation prefix and then `d` coupled rounds, so it has `22 + 5 d` stages and the
count is `(22 + 5 d)(22 + 5 d + 1) / 2`. -/
theorem prefix_round_digest_clash_mass_le (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L) (d : Nat) :
    oracleProbability (boundedQueries L) (prefixRoundDigestClashEvent L c s ms hlen d)
      ≤ ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) :=
  le_trans
    (oracle_probability_mono _ _ _ (prefix_round_digest_clash_event_subset L c s ms hlen d))
    (frame_chain_clash_probability_le L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlen
      (22 + 5 * d))

/-- (8) **THE BOUND AT THE ENVELOPE'S `degreeBits = 13`, WITH THE PREFIX
THREADED**: `3828 / |Block|`, the `22 + 65 = 87` stages of the whole chain, up
from section 7's `2145` for the round stages alone.  `|Block| = 256 ^ 32` by the
adopted `block_card`, and is never evaluated. -/
theorem prefix_round_digest_clash_mass_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L) :
    oracleProbability (boundedQueries L) (prefixRoundDigestClashEvent L c s ms hlen 13)
      ≤ 3828 / (Fintype.card Block : ℚ) := by
  have h := prefix_round_digest_clash_mass_le L c s ms hlen 13
  have hnum : ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 := by
    norm_num
  rw [hnum] at h
  exact h

theorem prefix_round_digest_clash_bound_lt_one : (3828 : ℚ) / (Fintype.card Block : ℚ) < 1 := by
  rw [div_lt_one block_card_cast_pos]
  exact_mod_cast block_card_gt_small 3828 (by norm_num)

/-- (8) **THE CLASH EVENT OF THE WHOLE CHAIN IS NOT EMPTY EITHER.**  The constant
table is in it at `d = 2`, exactly as in section 7: the bound above is not proved
on an empty event. -/
theorem constant_table_in_prefix_round_clash_event (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L) :
    constantTable L ∈ prefixRoundDigestClashEvent L c s ms hlen 2 := by
  simp only [prefixRoundDigestClashEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨0, 1, by omega, by omega, ?_⟩
  rw [show 22 + (5 * 0 + 5) = 26 + 1 from rfl, show 22 + (5 * 1 + 5) = 31 + 1 from rfl,
    constant_table_state, constant_table_state]

/-! ## 9. WHAT A CLASH BOUND BUYS, AND WHAT IS STILL MISSING -/

open Classical in
/-- The run's localized clash, as an event on tables. -/
noncomputable def clashEvent (Q : Finset Transcript.Bytes) (c : Verifier.Config)
    (p : Verifier.Proof) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => RandomOracleSqueezes.RoundDigestClash (hashOf Q T) c p)

/-- (9) The adopted `scheduleNonInjectiveEvent` is contained in the clash event,
by the adopted `schedule_non_injective_is_clash`. -/
theorem schedule_non_injective_subset_clash (Q : Finset Transcript.Bytes)
    (c : Verifier.Config) (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) :
    RandomOracleSqueezes.scheduleNonInjectiveEvent Q c p ⊆ clashEvent Q c p := by
  intro T hT
  simp only [clashEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact RandomOracleSqueezes.schedule_non_injective_is_clash Q c p hdb T hT

/-- (9) **THE COMPOSITION.**  Any bound on the run's localized clash mass turns
the adopted `run_bad_draw_probability_le_fibrewise` into a run-level number.
THIS MODULE DOES NOT SUPPLY THAT BOUND FOR THE ADOPTED
`InstalledRoundCommit.actualChain`, and what is missing is stated in full under
HONESTY (iii).  It is NOT the frames: section 7 covers ALL FIVE frames of every
round, and section 8 prepends the adopted twenty-two-frame relation prefix and
identifies the chain's digest there with the adopted `OuterInitial.derive` digest
(`prefix_state_is_derive_digest`), so the base digest is no longer a parameter.
What is still missing is the LIST BOOKKEEPING of HONESTY (iii)(b): nothing here
identifies the chain's stage `22 + 5 r + 5` with position `r` of
`InstalledRoundCommit.concreteChain`, so `prefixRoundDigestClashEvent` is still an
event about the chain and not, syntactically, about
`RandomOracleSqueezes.RoundDigestClash`.  The hypothesis `hclash` is satisfiable
-- at `eps = 1` by `oracle_probability_le_one` for every `Q`, and the content of
the statement is what happens for smaller `eps`. -/
theorem run_bad_draw_probability_le_of_clash_bound (Q : Finset Transcript.Bytes)
    (c : Verifier.Config) (p : Verifier.Proof)
    (hQ : RandomOracleSqueezes.QueryClosure Q c.degreeBits) (hdb : c.degreeBits ≤ 13)
    (eps : ℚ) (hclash : oracleProbability Q (clashEvent Q c p) ≤ eps)
    (quotientDegree constraints : Nat)
    (logCompare gateCompare : GoldilocksExt3Field.Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound)
    (g : Nat → GoldilocksExt3Field.Element)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element)
    (hlogLen : logLane.length = c.degreeBits) (hgateLen : gateLane.length = c.degreeBits)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability Q (RandomOracleSqueezes.runDrawEvent Q c p
        (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane g
          (2 ^ c.degreeBits) coeffsOf))
      ≤ ChallengeUnionBound.combinedBound c.degreeBits quotientDegree c.degreeBits constraints
        + eps := by
  refine le_trans (RandomOracleSqueezes.run_bad_draw_probability_le_fibrewise Q c p hQ
    quotientDegree constraints logCompare gateCompare logLane gateLane g coeffsOf
    hlogLen hgateLen hlogDeg hgateDeg hclen) ?_
  refine add_le_add_left ?_ _
  exact le_trans
    (oracle_probability_mono Q _ _ (schedule_non_injective_subset_clash Q c p hdb)) hclash

/-- (9) The hypothesis of the composition is satisfiable, non-degenerately: at
`eps = 1` it holds for every query set and every run. -/
theorem clash_bound_hypothesis_satisfiable (Q : Finset Transcript.Bytes)
    (c : Verifier.Config) (p : Verifier.Proof) :
    oracleProbability Q (clashEvent Q c p) ≤ 1 :=
  oracle_probability_le_one Q _

end Audit.Wire3.BirthdayClashBound
