import Audit.Wire3.InstalledRoundCommit

/-!
# THE RANDOM-ORACLE LAW FOR THE FIAT--SHAMIR SQUEEZES

## The gap this module addresses

Every probabilistic statement in the adopted tree is a MASS under an explicit
ideal uniform law on a coordinate space: `OuterChallenge.uniformTupleProbability`
on one `DigestTriple`, `JointChallengeSpace.jointProbability` on
`JointChallengeSpace.JointSpace d`, `InstalledIndexSampler`'s law on its index
space.  The seam that connects those laws to a run --
`JointChallengeSpace.DrawEncodesRun`, inhabited at the run's OWN digest triples
by `InstalledRoundCommit.actual_digest_draw_encodes_run` -- is a COORDINATE
statement: it says only WHICH point of `JointSpace d` one is looking at.

Half (B) of the Fiat--Shamir reading -- "the actual draw is
`jointProbability`-distributed" -- is nowhere formalized.  This module is a
FIRST formal piece of it.  It writes down the random-oracle model as an explicit
finite counting law on oracle tables, proves that squeezes at DISTINCT oracle
inputs are jointly uniform, and concludes that CONDITIONED ON THE BLOCK DIGESTS
the draw assembled from the schedule's `3 * (3 * degreeBits + 1)` challenge
inputs is EXACTLY `jointProbability`-distributed -- so a bad-event mass becomes a
probability over the HASH TABLE rather than over an abstract coordinate point.

## What is proved

1. THE LAW.  `OracleTable Q := (q : Q) -> Block` for a finite query set
   `Q : Finset Transcript.Bytes`, with the uniform counting law
   `oracleProbability`.  `oracle_card` gives `|Digest| ^ |Q|`, and `Block` is the
   adopted `OuterChallenge.DigestBlock`, whose cardinality is the adopted
   `256 ^ 32` (`WhirChallenge.byte_block_cardinality`).  No digest space is ever
   enumerated: `Fintype.card Block` is only ever handled symbolically.
2. DISTINCT-INPUT UNIFORMITY.  `pushforward_uniform` (and its index-type form
   `pushforward_uniform_index`): for an INJECTIVE family of queries, the
   pushforward of the uniform law on `OracleTable Q` is the uniform law on
   `Fin m -> Block`.  Pure counting: the split `OracleTable Q ~= (Fin m -> Block)
   x (rest -> Block)` makes every fibre have `|Digest| ^ (|Q| - m)` elements and
   the free coordinates cancel.
3. THE JOINT SHAPE.  `joint_pushforward_uniform`: bundling three consecutive
   squeezes per coordinate into an `OuterChallenge.DigestTriple` carries the
   uniform law on `OracleTable Q` to the adopted
   `JointChallengeSpace.jointProbability d`, when the `3 * (3 * d + 1)` inputs
   of the schedule are pairwise distinct members of `Q`.
4. THE RUN'S SQUEEZE INPUTS.  `squeezeInputAt` is the EXACT oracle input of each
   scheduled squeeze, built from the adopted `Transcript.challengeInput` at the
   adopted `JointChallengeSpace.sourceCounter`, on the adopted block digest
   (`InstalledRoundCommit.actualBase` for the relation prefix,
   `InstalledRoundCommit.actualChain` for the coupled rounds).
   `actual_digest_draw_at_squeeze_inputs` is `rfl`: the adopted
   `InstalledRoundCommit.actualDigestDraw` IS the hash at those inputs.
   `squeeze_inputs_distinct_or_round_digest_clash` proves the inputs are pairwise
   DISTINCT, or two DIFFERENT rounds of the run share a commit digest --
   the LOCALIZED `RoundDigestClash`, which is refutable.  The adopted
   `∨ CommitmentOrder.TranscriptCollision` form is kept as a corollary
   (`squeeze_inputs_distinct_or_collision`) and EXHIBITS a colliding pair, but is
   a tautology as a STATEMENT: see (iii).
5. THE PAYOFF, AND ITS EXACT SCOPE.  `draw_at_fixed_digests_is_uniform` and its
   bad-event corollary `bad_draw_at_fixed_digests_le` are statements CONDITIONED
   ON THE BLOCK DIGESTS: the digest assignment `dig` is quantified OUTSIDE the
   law, and under that conditioning the mass of the adopted
   `JointChallengeSpace.jointBadEvent` is at most the adopted
   `ChallengeUnionBound.combinedBound`.  The left-hand side is a mass over the
   HASH TABLE, not over an abstract coordinate point of `JointSpace`.  The
   hypotheses are SHOWN SATISFIABLE, at every `degreeBits <= 13` and explicitly
   at `13`, by `fixed_digest_hypotheses_are_satisfiable` /
   `fixed_digest_hypotheses_are_satisfiable_at_thirteen` and the fully
   instantiated `bad_draw_bound_at_thirteen`: `blockDigests` is a concrete
   block-separating digest assignment and `scheduleSet` / `scheduleSel` a
   concrete query set and injective query family for it.
6. THE FRAME/CHALLENGE SEPARATION.  `source_digest_depends_only_on_frame_queries`
   is the congruence lemma the missing run-level statement needs: the run's block
   digests read the oracle ONLY at `Transcript.frame`-shaped inputs, so two
   tables that agree at every non-challenge query give the SAME block digests.
   Its two ingredients are `frame_ne_challenge_input` (frames carry
   `Transcript.framePrefix`, squeezes carry `Transcript.challengePrefix`, and the
   two prefixes differ at byte `15`) and the hash-congruence chain
   `absorb_congr ... actual_chain_congr` over the whole adopted prefix
   (`OuterInitial.baseState` through `OuterInitial.relationState` and
   `OuterInitial.derive`) and the adopted round chain
   (`InstalledRoundCommit.concreteChain`).
7. THE RUN-LEVEL BOUND.  `run_draw_probability_le_fibrewise` and its bad-event
   corollary `run_bad_draw_probability_le_fibrewise` weigh the RUN'S OWN draw,
   with NO conditioning on the block digests: the mass of the adopted
   `JointChallengeSpace.jointBadEvent` at the run's own digests is at most the
   adopted `ChallengeUnionBound.combinedBound` PLUS the mass of the event that
   the run's schedule of oracle inputs is not injective, which by
   `schedule_non_injective_is_clash` is the localized `RoundDigestClash`.  The
   one hypothesis beyond the model is `QueryClosure`, shown satisfiable by
   `query_closure_is_satisfiable`.  THE CLASH TERM IS NOT BOUNDED HERE, and
   section 8.1 discloses what it actually is: at the frame-free `closureWitness`
   of `query_closure_is_satisfiable` it is identically `1`
   (`closure_witness_clash_term_one`), so there the bound reads
   `≤ combinedBound + 1` and follows from `oracle_probability_le_one` alone
   (`run_bound_trivial_at_frame_free`).  It is `< 1` only for a `Q` that also
   answers the run's OWN frame inputs; such a `Q` is EXHIBITED, at every
   `degreeBits <= 13`, by `informative_query_set_exists`.
8. THE SEPARATING HASH.  `sepHash` answers the adopted round-index frame with the
   digest spelling the round index, so every round of the run commits to a
   DISTINCT digest and `RoundDigestClash sepHash c p` is refuted at every
   `degreeBits <= 13` with a chain of matching length (`sep_hash_no_clash`).
   That is the sharper non-triviality witness `round_digest_clash_needs_two_rounds`
   does not give, and it is the hash that `informative_query_set_exists` installs.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK.  `OracleTable Q` with the
counting law is a DEFINITION written down here.  Nothing below is a property of
Keccak, of the Solidity or Rust transcript, or of any deterministic function.
The adopted `CommitmentOrder.separation_fails_for_a_deterministic_hash` shows
that even the deterministic shadow of the property fails for a general `hash`.
Replacing the deployed hash by a table drawn from this law is an ASSUMPTION with
no proof anywhere in this tree.

(ii) THE RUN-LEVEL BOUND IS CONDITIONAL ON AN UNBOUNDED CLASH TERM, AND THAT IS
THE MAIN LIMITATION.  `run_bad_draw_probability_le_fibrewise` weighs the run's own
draw and produces `combinedBound + P[schedule not injective]`.  The second term is
not bounded anywhere in this tree, so the statement is a REDUCTION, not a number.

WHAT THE REDUCTION ACTUALLY USES, precisely, since an earlier revision of this
header described it wrongly.  The split of `Q` into a FRAME half and a CHALLENGE
half is by STRING SHAPE -- byte `15` of the query, `ChallengeShaped` -- and is
therefore INDEPENDENT of the table: `frameSplit` is an equivalence
`OracleTable Q ≃ (ChallengeHalf Q → Block) × (FrameHalf Q → Block)` fixed before
anything is sampled.  Inside one frame fibre `f` the run's block digests are
CONSTANT, by the congruence lemma `source_digest_congr` together with
`frame_not_shaped`; so the run's schedule is, in that fibre, a FIXED family of
challenge-half queries, and whenever that family is injective the challenge draw
is EXACTLY `JointChallengeSpace.jointProbability`-distributed by `restrict_ratio`
(the arbitrary-domain form of `pushforward_uniform_index`).  Summing the fibres --
plain Fubini, `Fintype.sum_prod_type_right` -- and bounding the non-injective
fibres by `1` gives the bound.  The only extra input is `QueryClosure`: `Q` must
answer every challenge input at every counter below `6 * degreeBits + 12`, at
every digest; that is a finite requirement because `Transcript.Digest` is finite,
and `query_closure_is_satisfiable` produces a witness NONCOMPUTABLY (the set has
about `2 ^ 256` members and is never enumerated).

WHAT THE ADDITIVE TERM IS AT THE QUERY SETS THIS MODULE EXHIBITS -- READ THIS
BEFORE QUOTING THE BOUND.  `QueryClosure` constrains CHALLENGE-shaped strings
only, so it never forces a single `Transcript.frame` into `Q`: every closed `Q`
has a closed FRAME-FREE subset (`closure_has_frame_free_sub`).  On a frame-free
`Q` every table answers `OuterInitial.zeroDigest` at every frame, so by
`source_digest_congr` all of the run's block digests collapse to
`OuterInitial.zeroDigest`, the schedule repeats an input as soon as
`degreeBits >= 2`, and the additive term is EXACTLY `1` (`clash_term_one`).  The
witness of `query_closure_is_satisfiable` -- `closureWitness` -- is such a `Q`
(`closure_witness_clash_term_one`); AT IT THE RUN-LEVEL BOUND READS
`≤ combinedBound + 1` AND FOLLOWS FROM `oracle_probability_le_one` ALONE
(`run_bound_trivial_at_frame_free`).  The term is `< 1` only for a `Q` that also
answers the run's OWN frame inputs, and such a `Q` is exhibited -- at every
`degreeBits <= 13`, for a proof whose coupled-round chain has the matching length
-- by `informative_query_set_exists`, on the separating hash `sepHash`.  NO SMALL
BOUND ON THE CLASH TERM IS PROVED ANYWHERE IN THIS MODULE; `< 1` is not a
security statement.

Note also the `getD` base of `sourceDigest`: a round index beyond the proof's
coupled-round chain falls back to `InstalledRoundCommit.actualBase`, so if the
chain is at least two rounds SHORTER than `degreeBits` two round indices share
the base digest, `RoundDigestClash` holds for EVERY hash and the additive term is
`1` whatever the oracle does.  That is why `sep_hash_no_clash` and
`informative_query_set_exists` carry the chain-length hypothesis.

THERE IS NO SEQUENTIAL FRESH-QUERY INDUCTION HERE, AND NONE IS NEEDED FOR THE
FIBRE DECOMPOSITION.  A sequential, round-by-round argument -- round `r`'s frame
query is fresh, or it repeats an earlier one -- is the birthday count over the
frame fibres that would BOUND the clash term, and it is needed only for the
LOCALIZED predicate; it is NOT carried out here.  It is one of TWO things missing
between this module and an unconditional run-level number, the other being the
adaptive prover of the next paragraph.

WHAT IS STILL OUT OF SCOPE, AND IT IS THE FIAT--SHAMIR-SPECIFIC STEP.  The proof
`p` is a FIXED argument of every statement below, quantified OUTSIDE the law.  An
ADAPTIVE prover -- one that reads oracle answers and then chooses `p` -- is not
modelled anywhere in this tree.  The counting above says nothing about such a
prover.

A PREVIOUS REVISION of this module shipped two run-level theorems
(`nonadaptive_actual_draw_is_uniform`, `nonadaptive_bad_draw_probability_le`)
under the hypothesis `hfix : forall T, sourceDigest (hashOf Q T) c p = dig`.
Review showed that hypothesis to be INCONSISTENT, not merely undischarged: the
constant table forces `dig` to be constantly `OuterInitial.zeroDigest`, which
contradicts the injectivity of the schedule as soon as `degreeBits >= 2`.  Both
were VACUOUS and both have been REMOVED; the bound of section 8 replaces them and
assumes no such thing.

(iii) THE COLLISION ALTERNATIVE IS A CONCLUSION -- BUT THE GLOBAL COLLISION
PREDICATE IS A TAUTOLOGY.  No theorem below assumes
`Not (CommitmentOrder.TranscriptCollision thash)`.  That is the adopted
convention, shared with `CommitmentOrder.absorb_messages_bind_or_collide` and
`InstalledRoundCommit.round_message_fixed_before_round_challenges`.  IT MUST BE
READ WITH THIS DISCLOSURE: `CommitmentOrder.TranscriptCollision hash` is
`∃ a b, a ≠ b ∧ hash a = hash b` over ALL byte strings, `Transcript.Bytes` is
infinite and `Transcript.Digest` finite, so pigeonhole proves it for EVERY hash
(`transcript_collision_is_a_tautology`).  Hence every
`Good ∨ CommitmentOrder.TranscriptCollision hash` statement in the adopted tree --
in `CommitmentOrder`, `InstalledIndexSampler` and `InstalledRoundCommit`, and the
analogous `∨ ExplicitEngine.KhashCollision` statements -- is TRUE AS A STATEMENT
whatever `Good` says.  Their content is in their PROOFS, which exhibit concrete
colliding pairs; it is not in their conclusions.  The informative form is
LOCALIZED: `RoundDigestClash thash c p` names two DIFFERENT rounds of THIS run
whose commit digests coincide, is refuted by
`round_digest_clash_needs_two_rounds` and, at every `degreeBits <= 13`, by
`sep_hash_no_clash`, and is what
`squeeze_inputs_distinct_or_round_digest_clash` concludes.  Localizing is
NECESSARY for a run-level bound of the shape `≤ combinedBound + P{T | clash}` to
be capable of saying anything -- with the global predicate the additive term is
identically `1` (`hash_of_always_collides`) and the bound reads
`≤ combinedBound + 1` for every `Q`.  It is NOT SUFFICIENT: the LOCALIZED term is
`1` as well on any frame-free `Q`, the `closureWitness` included.  See (ii) and
section 8.1.

(iv) SCOPE AND NUMBERS.  Only the `JointChallengeSpace` coordinates are covered:
the two coupled-round challenges of each round, the gate alpha and the gate tau
column.  The `InstalledIndexSampler` index lanes are NOT covered, and the
WHIR/Merkle events -- which DOMINATE -- are excluded entirely.
`ChallengeUnionBound.combinedBound` is not the deployed system's soundness error.
The wire-v3 WHIR profile modelled by this tree is the ~100-bit design point; no
figure here is a security level, and no stray envelope figure from elsewhere in
the repository is asserted or implied by anything below.

(v) RELATION TO `OuterSequentialConditioning`.  That module handles adaptivity at
the LAW level: adaptive bad SETS on a fixed product space, with the coordinates
already assumed uniform, proved by a Fubini peel over DISTINCT coordinates.  This
module handles the ORACLE level for FIXED inputs: it derives the product law
itself from the counting law on tables.  The two are complementary halves of one
argument and NEITHER subsumes the other; combining them -- adaptive queries under
the random-oracle law -- is the remaining step of half (B), and it is not taken
here.
-/

namespace Audit.Wire3.RandomOracleSqueezes

open Audit.Wire3 GoldilocksExt3Field

/-! ## 1. The random-oracle law as a finite counting law -/

/-- One oracle output: the adopted 32-byte block of `OuterChallenge`. -/
abbrev Block := OuterChallenge.DigestBlock

/-- A digest out of a block; inverse to the adopted `OuterChallenge.digestBlock`. -/
def blockDigest (b : Block) : Transcript.Digest := ⟨b.val, b.property⟩

theorem digest_block_block_digest (b : Block) : OuterChallenge.digestBlock (blockDigest b) = b :=
  rfl

theorem block_digest_digest_block (d : Transcript.Digest) :
    blockDigest (OuterChallenge.digestBlock d) = d := rfl

/-- **THE ORACLE TABLE.** One 32-byte output per query of the finite query set
`Q`.  The random-oracle model is the UNIFORM law on this finite type; it is
written down here, exactly as the adopted `OuterChallenge.uniformTupleProbability`
and `JointChallengeSpace.jointProbability` write down their laws. -/
abbrev OracleTable (Q : Finset Transcript.Bytes) := { q : Transcript.Bytes // q ∈ Q } → Block

theorem block_card : Fintype.card Block = 256 ^ 32 :=
  WhirChallenge.byte_block_cardinality 32

/-- The adopted `OuterChallenge.wordSize`, as the cardinality of one squeeze. -/
theorem block_card_eq_word_size : Fintype.card Block = OuterChallenge.wordSize :=
  WhirChallenge.byte_block_cardinality 32

theorem block_card_pos : 0 < Fintype.card Block := by
  rw [block_card]
  exact pow_pos (by norm_num) 32

/-- (1) **THE SIZE OF THE TABLE SPACE.**  `|Digest| ^ |Q|`.  No digest space is
enumerated: `Fintype.card Block` stays symbolic. -/
theorem oracle_card (Q : Finset Transcript.Bytes) :
    Fintype.card (OracleTable Q) = Fintype.card Block ^ Q.card := by
  rw [Fintype.card_fun, Fintype.card_coe]

theorem oracle_card_pos (Q : Finset Transcript.Bytes) : 0 < Fintype.card (OracleTable Q) := by
  rw [oracle_card]
  exact pow_pos block_card_pos _

theorem oracle_card_cast_pos (Q : Finset Transcript.Bytes) :
    (0 : ℚ) < (Fintype.card (OracleTable Q) : ℚ) := by
  exact_mod_cast oracle_card_pos Q

/-- **THE LAW.**  Same convention as the adopted
`JointChallengeSpace.jointProbability`: count on an explicit finite space, then
divide by its size. -/
noncomputable def oracleProbability (Q : Finset Transcript.Bytes)
    (E : Finset (OracleTable Q)) : ℚ :=
  (E.card : ℚ) / (Fintype.card (OracleTable Q) : ℚ)

theorem oracle_probability_nonneg (Q : Finset Transcript.Bytes) (E : Finset (OracleTable Q)) :
    0 ≤ oracleProbability Q E :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem oracle_probability_le_one (Q : Finset Transcript.Bytes) (E : Finset (OracleTable Q)) :
    oracleProbability Q E ≤ 1 := by
  refine (div_le_one (oracle_card_cast_pos Q)).mpr ?_
  exact_mod_cast E.card_le_univ

theorem oracle_probability_mono (Q : Finset Transcript.Bytes) (A B : Finset (OracleTable Q))
    (h : A ⊆ B) : oracleProbability Q A ≤ oracleProbability Q B := by
  have hc : (A.card : ℚ) ≤ (B.card : ℚ) := by exact_mod_cast Finset.card_le_card h
  exact div_le_div_of_nonneg_right hc (oracle_card_cast_pos Q).le

/-- The deterministic hash a table induces: the table on `Q`, and a fixed
arbitrary digest off `Q`.  Every theorem below reads the table only on `Q`. -/
def hashOf (Q : Finset Transcript.Bytes) (T : OracleTable Q) : Transcript.Hash :=
  fun q => if h : q ∈ Q then blockDigest (T ⟨q, h⟩) else OuterInitial.zeroDigest

theorem hash_of_at (Q : Finset Transcript.Bytes) (T : OracleTable Q)
    (x : { q : Transcript.Bytes // q ∈ Q }) : hashOf Q T x.val = blockDigest (T x) := by
  simp only [hashOf, x.property, dif_pos]

/-! ## 2. Distinct-input uniformity: pure counting -/

open Classical in
/-- The split of a table along an injective query family: the `I` queries of the
family, and everything else.  This is the ONE place the non-adaptivity of the
family is used -- the split is a single equivalence of TYPES, so the family must
not depend on the table. -/
noncomputable def splitTable {I : Type} [Fintype I] [DecidableEq I]
    (Q : Finset Transcript.Bytes) (sel : I → { q : Transcript.Bytes // q ∈ Q })
    (hsel : Function.Injective sel) :
    OracleTable Q ≃
      (I → Block) × ({ a : { q : Transcript.Bytes // q ∈ Q } // a ∉ Set.range sel } → Block) :=
  (Equiv.arrowCongr
      ((Equiv.sumCongr (Equiv.ofInjective sel hsel) (Equiv.refl _)).trans
        (Equiv.sumCompl (fun a : { q : Transcript.Bytes // q ∈ Q } => a ∈ Set.range sel))).symm
      (Equiv.refl Block)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

open Classical in
theorem split_table_fst {I : Type} [Fintype I] [DecidableEq I]
    (Q : Finset Transcript.Bytes) (sel : I → { q : Transcript.Bytes // q ∈ Q })
    (hsel : Function.Injective sel) (T : OracleTable Q) :
    (splitTable Q sel hsel T).1 = fun i => T (sel i) := rfl

/-- The event "the table restricted to the query family lands in `E`". -/
noncomputable def restrictEvent {I : Type} [Fintype I] [DecidableEq I]
    (Q : Finset Transcript.Bytes) (sel : I → { q : Transcript.Bytes // q ∈ Q })
    (E : Finset (I → Block)) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => (fun i => T (sel i)) ∈ E)

/-- (2) **DISTINCT INPUTS ARE JOINTLY UNIFORM**, for an arbitrary finite index
type.  Each fibre of the restriction map has `|Digest| ^ (|Q| - |I|)` elements and
those free coordinates cancel. -/
theorem pushforward_uniform_index {I : Type} [Fintype I] [DecidableEq I]
    (Q : Finset Transcript.Bytes) (sel : I → { q : Transcript.Bytes // q ∈ Q })
    (hsel : Function.Injective sel) (E : Finset (I → Block)) :
    oracleProbability Q (restrictEvent Q sel E)
      = (E.card : ℚ) / (Fintype.card Block : ℚ) ^ Fintype.card I := by
  classical
  set C := { a : { q : Transcript.Bytes // q ∈ Q } // a ∉ Set.range sel }
  set Phi := splitTable Q sel hsel
  have hev := WhirChallenge.equiv_event_card Phi (fun z : (I → Block) × (C → Block) => z.1 ∈ E)
  have hfil : (Finset.univ.filter
      (fun z : (I → Block) × (C → Block) => z.1 ∈ E)) = E ×ˢ Finset.univ := by
    apply Finset.ext
    intro z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
  have hcard : (restrictEvent Q sel E).card = E.card * Fintype.card (C → Block) := by
    have h1 : restrictEvent Q sel E
        = Finset.univ.filter (fun T : OracleTable Q => (Phi T).1 ∈ E) := by
      apply Finset.ext
      intro T
      simp only [restrictEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        split_table_fst Q sel hsel T]
    rw [h1, hev, hfil, Finset.card_product, Finset.card_univ]
  have htot : Fintype.card (OracleTable Q)
      = Fintype.card Block ^ Fintype.card I * Fintype.card (C → Block) := by
    rw [Fintype.card_congr Phi, Fintype.card_prod, Fintype.card_fun]
  have hKpos : 0 < Fintype.card (C → Block) := Fintype.card_pos_iff.mpr
    ⟨fun _ => Classical.choice (Fintype.card_pos_iff.mp block_card_pos)⟩
  have hK : ((Fintype.card (C → Block) : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hKpos.ne'
  rw [oracleProbability, hcard, htot]
  push_cast
  rw [mul_comm (E.card : ℚ) _, mul_comm ((Fintype.card Block : ℚ) ^ Fintype.card I) _]
  exact mul_div_mul_left _ _ hK

/-- (2) **THE STATEMENT IN THE REQUESTED SHAPE.**  For an injective family
`sel : Fin m -> Q`, the pushforward of the uniform law on `OracleTable Q` along
`T |-> fun i => T (sel i)` is the uniform law on `Fin m -> Block`. -/
theorem pushforward_uniform (Q : Finset Transcript.Bytes) (m : Nat)
    (sel : Fin m → { q : Transcript.Bytes // q ∈ Q }) (hsel : Function.Injective sel)
    (E : Finset (Fin m → Block)) :
    oracleProbability Q (restrictEvent Q sel E)
      = (E.card : ℚ) / (Fintype.card Block : ℚ) ^ m := by
  simpa only [Fintype.card_fin] using pushforward_uniform_index Q sel hsel E

/-! ### 2.1 The same count on an ARBITRARY finite query domain -/

open Classical in
/-- The split of section 2, on an arbitrary finite domain `A` rather than on a
whole query set.  Needed because the run-level statement of section 8 counts
INSIDE one frame fibre, whose free coordinates are only the CHALLENGE half of
`Q`, not all of `Q`. -/
noncomputable def splitAt {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (sel : I → A) (hsel : Function.Injective sel) :
    (A → Block) ≃ (I → Block) × ({ a : A // a ∉ Set.range sel } → Block) :=
  (Equiv.arrowCongr
      ((Equiv.sumCongr (Equiv.ofInjective sel hsel) (Equiv.refl _)).trans
        (Equiv.sumCompl (fun a : A => a ∈ Set.range sel))).symm
      (Equiv.refl Block)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

open Classical in
theorem split_at_fst {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (sel : I → A) (hsel : Function.Injective sel) (T : A → Block) :
    (splitAt sel hsel T).1 = fun i => T (sel i) := rfl

/-- The event "the map restricted to the query family lands in `E`", on an
arbitrary finite domain.  The `restrictEvent` of section 2 with `OracleTable Q`
replaced by `A → Block`. -/
noncomputable def restrictAt {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (sel : I → A) (E : Finset (I → Block)) : Finset (A → Block) :=
  Finset.univ.filter (fun h => (fun i => h (sel i)) ∈ E)

/-- (2) **DISTINCT INPUTS ARE JOINTLY UNIFORM, ON ANY FINITE DOMAIN.**  Stated as
a cross-multiplied identity so that the complement type never appears: the number
of maps `A → Block` whose restriction along an INJECTIVE `sel` lands in `E`, times
`|Block| ^ |I|`, is `|E|` times the size of the whole space.  Dividing, the
restriction is uniform on `I → Block`.  This is `pushforward_uniform_index` with
`OracleTable Q` replaced by an arbitrary finite domain. -/
theorem restrict_ratio {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (sel : I → A) (hsel : Function.Injective sel) (E : Finset (I → Block)) :
    ((restrictAt sel E).card : ℚ) * (Fintype.card Block : ℚ) ^ Fintype.card I
      = (E.card : ℚ) * (Fintype.card (A → Block) : ℚ) := by
  classical
  rw [restrictAt]
  set C := { a : A // a ∉ Set.range sel }
  set Phi := splitAt sel hsel
  have hev := WhirChallenge.equiv_event_card Phi (fun z : (I → Block) × (C → Block) => z.1 ∈ E)
  have hfil : (Finset.univ.filter
      (fun z : (I → Block) × (C → Block) => z.1 ∈ E)) = E ×ˢ Finset.univ := by
    apply Finset.ext
    intro z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
  have hcard : (Finset.univ.filter (fun h : A → Block => (fun i => h (sel i)) ∈ E)).card
      = E.card * Fintype.card (C → Block) := by
    have h1 : (Finset.univ.filter (fun h : A → Block => (fun i => h (sel i)) ∈ E))
        = Finset.univ.filter (fun T : A → Block => (Phi T).1 ∈ E) := by
      apply Finset.ext
      intro T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, split_at_fst sel hsel T]
    rw [h1, hev, hfil, Finset.card_product, Finset.card_univ]
  have htot : Fintype.card (A → Block)
      = Fintype.card Block ^ Fintype.card I * Fintype.card (C → Block) := by
    rw [Fintype.card_congr Phi, Fintype.card_prod, Fintype.card_fun]
  rw [hcard, htot]
  push_cast
  ring

/-! ## 3. Three consecutive squeezes per coordinate: the joint shape -/

/-- Three squeezes bundled into the adopted `OuterChallenge.DigestTriple`, one
triple per scheduled draw. -/
def bundleEquiv (d : Nat) :
    (JointChallengeSpace.Draw d × Fin 3 → Block) ≃ JointChallengeSpace.JointSpace d where
  toFun f := fun k => (f (k, 0), f (k, 1), f (k, 2))
  invFun w := fun kj =>
    if kj.2.val = 0 then (w kj.1).1 else if kj.2.val = 1 then (w kj.1).2.1 else (w kj.1).2.2
  left_inv f := by
    funext kj
    obtain ⟨k, j⟩ := kj
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨n + 3, hn⟩ => exact absurd hn (by omega)
  right_inv w := by
    funext k
    rfl

/-- The joint point a table produces along a schedule of queries. -/
def encodedDraw (Q : Finset Transcript.Bytes) (d : Nat)
    (sel : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (T : OracleTable Q) : JointChallengeSpace.JointSpace d :=
  bundleEquiv d (fun kj => T (sel kj))

theorem encoded_draw_apply (Q : Finset Transcript.Bytes) (d : Nat)
    (sel : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (T : OracleTable Q) (k : JointChallengeSpace.Draw d) :
    encodedDraw Q d sel T k = (T (sel (k, 0)), T (sel (k, 1)), T (sel (k, 2))) := rfl

open Classical in
/-- The event, on oracle tables, that the assembled joint point lands in `E`. -/
noncomputable def encodedEvent (Q : Finset Transcript.Bytes) (d : Nat)
    (sel : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (E : Finset (JointChallengeSpace.JointSpace d)) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => encodedDraw Q d sel T ∈ E)

theorem schedule_index_card (d : Nat) :
    Fintype.card (JointChallengeSpace.Draw d × Fin 3) = (3 * d + 1) * 3 := by
  rw [Fintype.card_prod, JointChallengeSpace.draw_card, Fintype.card_fin]

theorem joint_space_card_as_blocks (d : Nat) :
    (Fintype.card (JointChallengeSpace.JointSpace d) : ℚ)
      = (Fintype.card Block : ℚ) ^ ((3 * d + 1) * 3) := by
  rw [JointChallengeSpace.joint_space_card, block_card_eq_word_size]
  push_cast
  ring

/-- (2) **THE JOINT SHAPE.**  When the `3 * (3 * d + 1)` scheduled queries are
pairwise distinct members of `Q`, the pushforward of the uniform law on
`OracleTable Q` along the assembled draw IS the adopted
`JointChallengeSpace.jointProbability d`. -/
theorem joint_pushforward_uniform (Q : Finset Transcript.Bytes) (d : Nat)
    (sel : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : Function.Injective sel) (E : Finset (JointChallengeSpace.JointSpace d)) :
    oracleProbability Q (encodedEvent Q d sel E) = JointChallengeSpace.jointProbability d E := by
  classical
  have hFcard : (Finset.univ.filter
      (fun f : JointChallengeSpace.Draw d × Fin 3 → Block => bundleEquiv d f ∈ E)).card
      = E.card := by
    have h := WhirChallenge.equiv_event_card (bundleEquiv d) (fun w => w ∈ E)
    have h2 : (Finset.univ.filter (fun w : JointChallengeSpace.JointSpace d => w ∈ E)) = E := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h2] at h
    exact h
  have hset : encodedEvent Q d sel E
      = restrictEvent Q sel (Finset.univ.filter (fun f => bundleEquiv d f ∈ E)) := by
    apply Finset.ext
    intro T
    simp only [encodedEvent, restrictEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      encodedDraw]
  rw [hset, pushforward_uniform_index Q sel hsel _, hFcard, schedule_index_card,
    JointChallengeSpace.jointProbability, joint_space_card_as_blocks]

/-! ## 4. The run's own squeeze inputs -/

/-- The transcript state each scheduled draw is squeezed from: the adopted
relation-prefix digest for the gate alpha and the gate tau column, and the
adopted commit digest of coupled round `r` for that round's two challenges.
This is the block half of the adopted `JointChallengeSpace.schedulePosition`,
read off the adopted `InstalledRoundCommit.actualDigestDraw`. -/
def sourceDigest (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    JointChallengeSpace.Draw c.degreeBits → Transcript.Digest
  | JointChallengeSpace.Draw.gateAlpha => InstalledRoundCommit.actualBase thash c p
  | JointChallengeSpace.Draw.gateTau _ => InstalledRoundCommit.actualBase thash c p
  | JointChallengeSpace.Draw.outerLog r =>
      ((InstalledRoundCommit.actualChain thash c p).get? r.val).getD
        (InstalledRoundCommit.actualBase thash c p)
  | JointChallengeSpace.Draw.outerGate r =>
      ((InstalledRoundCommit.actualChain thash c p).get? r.val).getD
        (InstalledRoundCommit.actualBase thash c p)

/-- The exact oracle input of the `j`-th of the three squeezes of draw `k`, from
a block-digest assignment: the adopted `Transcript.challengeInput` at the adopted
`JointChallengeSpace.sourceCounter`, offset by `j`. -/
def squeezeInputAt (d : Nat) (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (k : JointChallengeSpace.Draw d) (j : Fin 3) : Transcript.Bytes :=
  Transcript.challengeInput (dig k) (JointChallengeSpace.sourceCounter d k + j.val)

/-- The whole schedule of oracle inputs, as one function on the index set. -/
def scheduleIndex (d : Nat) (dig : JointChallengeSpace.Draw d → Transcript.Digest) :
    JointChallengeSpace.Draw d × Fin 3 → Transcript.Bytes :=
  fun kj => squeezeInputAt d dig kj.1 kj.2

/-- The run's own schedule of oracle inputs. -/
def squeezeIndex (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    JointChallengeSpace.Draw c.degreeBits × Fin 3 → Transcript.Bytes :=
  scheduleIndex c.degreeBits (sourceDigest thash c p)

/-- The run's squeeze inputs as a list, one entry per scheduled squeeze. -/
noncomputable def squeezeInputs (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    List Transcript.Bytes :=
  (Finset.univ : Finset (JointChallengeSpace.Draw c.degreeBits × Fin 3)).toList.map
    (squeezeIndex thash c p)

theorem squeeze_inputs_length (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    (squeezeInputs thash c p).length = (3 * c.degreeBits + 1) * 3 := by
  rw [squeezeInputs, List.length_map, Finset.length_toList, Finset.card_univ,
    schedule_index_card]

/-- The query set of a schedule: the image of its `3 * (3 * d + 1)` inputs.  Used
as the concrete `Q` of the satisfiability lemmas of section 6. -/
def scheduleSet (d : Nat) (dig : JointChallengeSpace.Draw d → Transcript.Digest) :
    Finset Transcript.Bytes :=
  Finset.image (scheduleIndex d dig) Finset.univ

/-- The joint point a hash produces at a FIXED block-digest assignment: the
adopted `OuterChallenge.actualDigests` at the adopted counters. -/
def drawAtDigests (thash : Transcript.Hash) (d : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) : JointChallengeSpace.JointSpace d :=
  fun k => OuterChallenge.actualDigests thash ⟨dig k, JointChallengeSpace.sourceCounter d k⟩

/-- (4) The adopted `InstalledRoundCommit.actualDigestDraw` IS the draw at the
run's own block digests.  Nothing is re-modelled: this is `rfl` per constructor. -/
theorem actual_digest_draw_is_draw_at_digests (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) :
    InstalledRoundCommit.actualDigestDraw thash c p
      = drawAtDigests thash c.degreeBits (sourceDigest thash c p) := by
  funext k
  cases k <;> rfl

/-- (4) The adopted draw, coordinate by coordinate, as the hash at the three
EXACT oracle inputs of that coordinate's squeezes. -/
theorem actual_digest_draw_at_squeeze_inputs (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (k : JointChallengeSpace.Draw c.degreeBits) :
    InstalledRoundCommit.actualDigestDraw thash c p k =
      (OuterChallenge.digestBlock (thash (squeezeIndex thash c p (k, 0))),
       OuterChallenge.digestBlock (thash (squeezeIndex thash c p (k, 1))),
       OuterChallenge.digestBlock (thash (squeezeIndex thash c p (k, 2)))) := by
  cases k <;> rfl

/-! ## 5. The inputs are pairwise distinct, or the hash collides -/

/-! ### 5.0 The global collision predicate is a TAUTOLOGY -/

/-- Byte strings of every length exist, so `Transcript.Bytes` is infinite. -/
instance bytesInfinite : Infinite Transcript.Bytes :=
  Infinite.of_injective (fun n : Nat => List.replicate n (⟨0, by decide⟩ : Transcript.Byte))
    (fun a b h => by simpa using congrArg List.length h)

/-- `Transcript.Digest` injects into the adopted `OuterChallenge.DigestBlock`,
which is a `Fintype`, so the digest space is finite. -/
instance digestFinite : Finite Transcript.Digest :=
  Finite.of_injective OuterChallenge.digestBlock
    (fun a b h => by rw [← block_digest_digest_block a, h, block_digest_digest_block])

/-- (5) **AUDIT DISCLOSURE: `CommitmentOrder.TranscriptCollision` HOLDS FOR EVERY
HASH.**  That predicate is `∃ a b : Transcript.Bytes, a ≠ b ∧ hash a = hash b`
over ALL byte strings.  `Transcript.Bytes` is infinite and `Transcript.Digest` is
finite, so pigeonhole (`Finite.exists_ne_map_eq_of_infinite`) proves it outright,
with NO hypothesis on `hash` -- for the deployed Keccak, for a random table, for
the constant function alike.

CONSEQUENCE FOR THE WHOLE ADOPTED CONVENTION.  Every statement of the shape
`Good ∨ CommitmentOrder.TranscriptCollision hash` -- in the adopted
`CommitmentOrder`, `InstalledIndexSampler` and `InstalledRoundCommit`, and in
this module -- is TRUE AS A STATEMENT whatever `Good` says, and the analogous
`∨ ExplicitEngine.KhashCollision` disjunctions are in exactly the same position.
A disjunction of that shape carries no information in its STATEMENT; all of its
content sits in its PROOF, which exhibits a concrete colliding pair built out of
the run's own frames.  Anything QUANTITATIVE must therefore be phrased with a
LOCALIZED predicate instead: see `RoundDigestClash` and
`squeeze_inputs_distinct_or_round_digest_clash` below.  In particular, a
run-level bound of the shape `≤ combinedBound + P{T | clash}` can say something
only for the localized predicate; with the GLOBAL one the additive term is
identically `1` (`hash_of_always_collides`), so such a bound degenerates to
`≤ combinedBound + 1` and says nothing.  Localizing is NECESSARY and NOT
SUFFICIENT: section 8.1 shows the localized term is `1` too on any frame-free
query set, and exhibits a query set where it is `< 1`. -/
theorem transcript_collision_is_a_tautology (hash : Transcript.Hash) :
    CommitmentOrder.TranscriptCollision hash :=
  Finite.exists_ne_map_eq_of_infinite hash

/-- (5) The module's own table-backed hash is no exception: it collides for every
query set and every table, so `oracleProbability Q {T | TranscriptCollision
(hashOf Q T)}` is `1`. -/
theorem hash_of_always_collides (Q : Finset Transcript.Bytes) (T : OracleTable Q) :
    CommitmentOrder.TranscriptCollision (hashOf Q T) :=
  transcript_collision_is_a_tautology _

theorem byte_limit : (256 : Nat) ^ 8 = Transcript.u64Limit := by
  unfold Transcript.u64Limit
  norm_num

/-- The adopted `Transcript.challenge_inputs_distinguish_bounded_counters`,
strengthened to different digests: the challenge framing is unambiguous in the
state digest too, because `Transcript.digestBytes` occupies a fixed 32-byte slot.
Same technique as the adopted `CommitmentOrder.frame_injective`. -/
theorem challenge_input_injective (d e : Transcript.Digest) (i j : Nat)
    (hi : i < Transcript.u64Limit) (hj : j < Transcript.u64Limit)
    (h : Transcript.challengeInput d i = Transcript.challengeInput e j) : d = e ∧ i = j := by
  simp only [Transcript.challengeInput, List.append_assoc] at h
  have h1 := List.append_cancel_left h
  have hlen : (Transcript.digestBytes d).length = (Transcript.digestBytes e).length := by
    simp only [Transcript.digestBytes, d.length_eq, e.length_eq]
  obtain ⟨hd, hc⟩ := List.append_inj h1 hlen
  refine ⟨?_, ?_⟩
  · cases d
    cases e
    simpa only [Transcript.Digest.mk.injEq] using hd
  · exact Transcript.le_injective_bounded 8 i j (by rw [byte_limit]; exact hi)
      (by rw [byte_limit]; exact hj) hc

/-- Every scheduled counter of an enveloped run is far below the source's own
u64 guard, so that guard is never the binding constraint.  `degreeBits <= 13` is
the adopted `Verifier.envelope` bound. -/
theorem source_counter_bound (d : Nat) (hdb : d ≤ 13) (k : JointChallengeSpace.Draw d)
    (j : Fin 3) :
    JointChallengeSpace.sourceCounter d k + j.val < Transcript.u64Limit := by
  have hj := j.isLt
  unfold Transcript.u64Limit
  cases k with
  | gateAlpha => simp only [JointChallengeSpace.sourceCounter]; omega
  | gateTau i =>
      have hi := i.isLt
      simp only [JointChallengeSpace.sourceCounter]
      omega
  | outerLog r => simp only [JointChallengeSpace.sourceCounter]; omega
  | outerGate r => simp only [JointChallengeSpace.sourceCounter]; omega

/-- **THE LOCALIZED ROUND-DIGEST CLASH.**  Two DIFFERENT coupled rounds of THIS
run whose commit digests coincide.  This is the informative replacement for the
global `CommitmentOrder.TranscriptCollision`: it speaks only about the
`c.degreeBits` digests the run actually squeezes from, it is refutable
(`round_digest_clash_needs_two_rounds`), and it is exactly the alternative the
proof of `squeeze_inputs_distinct_or_round_digest_clash` derives before any
collision is exhibited.

The two coupled challenges of a round are squeezed from the same digest, so the
`Draw.outerGate` clash is the same proposition as the `Draw.outerLog` one
(`round_digest_clash_of_outer_gate`); the predicate is stated on `Draw.outerLog`
only. -/
def RoundDigestClash (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    Prop :=
  ∃ r s : Fin c.degreeBits, r ≠ s ∧
    sourceDigest thash c p (JointChallengeSpace.Draw.outerLog r)
      = sourceDigest thash c p (JointChallengeSpace.Draw.outerLog s)

/-- The gate-lane form of the clash is the log-lane form. -/
theorem round_digest_clash_of_outer_gate (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (r s : Fin c.degreeBits) (hrs : r ≠ s)
    (h : sourceDigest thash c p (JointChallengeSpace.Draw.outerGate r)
      = sourceDigest thash c p (JointChallengeSpace.Draw.outerGate s)) :
    RoundDigestClash thash c p :=
  ⟨r, s, hrs, h⟩

/-- (5) **THE LOCALIZED PREDICATE IS NOT A TAUTOLOGY.**  A run with fewer than two
coupled rounds has no clash at all, for every hash and every proof -- in contrast
with `CommitmentOrder.TranscriptCollision`, which no hypothesis can refute.  The
sharper witness is `sep_hash_no_clash` of section 8.2: the separating hash
`sepHash` has pairwise distinct round digests, so the clash is refuted at EVERY
`degreeBits ≤ 13` for which the proof's coupled-round chain has the matching
length -- not only at `degreeBits ≤ 1`. -/
theorem round_digest_clash_needs_two_rounds (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (hdb : c.degreeBits ≤ 1) : ¬ RoundDigestClash thash c p := by
  rintro ⟨r, s, hrs, -⟩
  have hr := r.isLt
  have hs := s.isLt
  exact hrs (Fin.ext (by omega))

/-- (5) **THE ROUND DIGEST BINDS THE ROUND INDEX.**  Two coupled rounds of one
run whose commit digests agree are the SAME round, or a concrete pair of distinct
byte strings with equal hash is EXHIBITED.  The work is done by the adopted
`InstalledRoundCommit.round_message_fixed_before_round_challenges`, which reads
the eight little-endian round-index bytes out of the adopted
`InstalledRoundCommit.roundFrames`. -/
theorem chain_digest_binds_round (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (hlen : (p.logRounds.zip p.gateRounds).length = c.degreeBits)
    (hdb : c.degreeBits ≤ 13) (r s : Fin c.degreeBits)
    (h : ((InstalledRoundCommit.actualChain thash c p).get? r.val).getD
          (InstalledRoundCommit.actualBase thash c p)
        = ((InstalledRoundCommit.actualChain thash c p).get? s.val).getD
          (InstalledRoundCommit.actualBase thash c p)) :
    r = s ∨ CommitmentOrder.TranscriptCollision thash := by
  have hr : r.val < (p.logRounds.zip p.gateRounds).length := by rw [hlen]; exact r.isLt
  have hs : s.val < (p.logRounds.zip p.gateRounds).length := by rw [hlen]; exact s.isLt
  have gr := InstalledRoundCommit.concrete_chain_get thash (p.logRounds.zip p.gateRounds)
    (OuterInitial.derive thash c (Verifier.statement p)).state 0 r.val hr
  have gs := InstalledRoundCommit.concrete_chain_get thash (p.logRounds.zip p.gateRounds)
    (OuterInitial.derive thash c (Verifier.statement p)).state 0 s.val hs
  rw [InstalledRoundCommit.actualChain, gr, gs, Option.getD_some, Option.getD_some] at h
  have hbr : 0 + r.val < Transcript.u64Limit := by
    unfold Transcript.u64Limit
    omega
  have hbs : 0 + s.val < Transcript.u64Limit := by
    unfold Transcript.u64Limit
    omega
  rcases InstalledRoundCommit.round_message_fixed_before_round_challenges thash _ _
      (0 + r.val) (0 + s.val) _ _ hbr hbs h with ⟨_, hidx, _⟩ | hcol
  · exact Or.inl (Fin.ext (by omega))
  · exact Or.inr hcol

/-- (5) **LOCALIZED: THE SCHEDULE'S ORACLE INPUTS ARE PAIRWISE DISTINCT, OR TWO
DIFFERENT ROUNDS OF THIS RUN SHARE A COMMIT DIGEST.**  This is the INFORMATIVE
form of the distinctness statement.  Its alternative is the localized
`RoundDigestClash`, a property of this run's own `c.degreeBits` round digests
which concrete situations refute (`round_digest_clash_needs_two_rounds`); it is
NOT the global `CommitmentOrder.TranscriptCollision`, which holds for every hash
whatsoever (`transcript_collision_is_a_tautology`).

Two squeezes of one block differ by their little-endian counter bytes, which the
adopted `Transcript.le_injective_bounded` separates; the relation-prefix block
and every round block differ by their counters outright (block-`0` counters start
at `9 + 3 * degreeBits`, round counters stop at `5`); and two DIFFERENT rounds
whose commit digests agree are exactly the clash.  Note that no `hlen` hypothesis
is needed: the chain lemma is used only to turn the clash into an exhibited
collision, in the corollary below.

Note also what distinctness does NOT give on its own: it is what
`pushforward_uniform` needs, but `pushforward_uniform` also needs the inputs to
be FIXED before the table is sampled, and these inputs are functions of the hash
-- see (ii) in the header and `run_bad_draw_probability_le_fibrewise`. -/
theorem squeeze_inputs_distinct_or_round_digest_clash (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) :
    Function.Injective (squeezeIndex thash c p) ∨ RoundDigestClash thash c p := by
  by_cases hclash : RoundDigestClash thash c p
  · exact Or.inr hclash
  refine Or.inl ?_
  rintro ⟨k, j⟩ ⟨k2, j2⟩ h
  simp only [squeezeIndex, scheduleIndex, squeezeInputAt] at h
  have hj := j.isLt
  have hj2 := j2.isLt
  obtain ⟨hdig, hcnt⟩ := challenge_input_injective _ _ _ _
    (source_counter_bound c.degreeBits hdb k j) (source_counter_bound c.degreeBits hdb k2 j2) h
  cases k with
  | gateAlpha =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          have hjj : j = j2 := Fin.ext (by omega)
          rw [hjj]
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
  | gateTau i =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          have hii : i = i2 := Fin.ext (by omega)
          have hjj : j = j2 := Fin.ext (by omega)
          rw [hii, hjj]
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
  | outerLog r =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          have hjj : j = j2 := Fin.ext (by omega)
          by_cases hrr : r = r2
          · rw [hrr, hjj]
          · exact absurd (⟨r, r2, hrr, hdig⟩ : RoundDigestClash thash c p) hclash
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
  | outerGate r =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          have hjj : j = j2 := Fin.ext (by omega)
          by_cases hrr : r = r2
          · rw [hrr, hjj]
          · exact absurd (round_digest_clash_of_outer_gate thash c p r r2 hrr hdig) hclash

/-- (5) **THE SAME FACT IN THE ADOPTED DISJUNCTIVE CONVENTION.**  The clash is
routed through `chain_digest_binds_round`, which EXHIBITS a concrete pair of
distinct byte strings with equal hash, built from the two rounds' own frames.
Collision resistance is a CONCLUSION here, never a hypothesis.

TAUTOLOGICAL AS A STATEMENT.  `CommitmentOrder.TranscriptCollision thash` holds
for every `thash` (`transcript_collision_is_a_tautology`), so this disjunction is
`True` no matter what the schedule does, and the `hlen`, `hdb` hypotheses are not
needed to prove the STATEMENT.  All of its content is in the proof.  The
informative statement is `squeeze_inputs_distinct_or_round_digest_clash` above;
this form is kept only because the adopted
`CommitmentOrder.absorb_messages_bind_or_collide` and
`InstalledRoundCommit.round_message_fixed_before_round_challenges` are stated in
this convention. -/
theorem squeeze_inputs_distinct_or_collision (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (hlen : (p.logRounds.zip p.gateRounds).length = c.degreeBits)
    (hdb : c.degreeBits ≤ 13) :
    Function.Injective (squeezeIndex thash c p) ∨ CommitmentOrder.TranscriptCollision thash := by
  rcases squeeze_inputs_distinct_or_round_digest_clash thash c p hdb with hinj | ⟨r, s, hrs, heq⟩
  · exact Or.inl hinj
  · rcases chain_digest_binds_round thash c p hlen hdb r s heq with hrs2 | hcol
    · exact absurd hrs2 hrs
    · exact Or.inr hcol

/-! ## 6. The draw at fixed digests, and the bad-event mass over the hash -/

/-- (2) The joint point a table produces at a FIXED block-digest assignment is
exactly the assembled draw of the schedule. -/
theorem draw_at_digests_is_encoded (Q : Finset Transcript.Bytes) (d : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (sel : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : ∀ (k : JointChallengeSpace.Draw d) (j : Fin 3),
      (sel (k, j)).val = squeezeInputAt d dig k j)
    (T : OracleTable Q) : drawAtDigests (hashOf Q T) d dig = encodedDraw Q d sel T := by
  funext k
  show (OuterChallenge.digestBlock (hashOf Q T (squeezeInputAt d dig k 0)),
        OuterChallenge.digestBlock (hashOf Q T (squeezeInputAt d dig k 1)),
        OuterChallenge.digestBlock (hashOf Q T (squeezeInputAt d dig k 2)))
      = (T (sel (k, 0)), T (sel (k, 1)), T (sel (k, 2)))
  rw [← hsel k 0, ← hsel k 1, ← hsel k 2, hash_of_at, hash_of_at, hash_of_at,
    digest_block_block_digest, digest_block_block_digest, digest_block_block_digest]

open Classical in
/-- The event, on oracle tables, that the draw at a fixed block-digest
assignment lands in `E`. -/
noncomputable def digestDrawEvent (Q : Finset Transcript.Bytes) (d : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (E : Finset (JointChallengeSpace.JointSpace d)) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => drawAtDigests (hashOf Q T) d dig ∈ E)

/-- (2) **THE PAYOFF, CONDITIONED ON THE BLOCK DIGESTS.**  Fix the block digests
OUTSIDE the law.  If the `3 * (3 * d + 1)` scheduled challenge inputs are
pairwise distinct members of `Q`, then under the random-oracle counting law on
`OracleTable Q` the draw assembled from those squeezes is EXACTLY
`jointProbability d`-distributed.

This is the honest content of the module: conditioned on the block digests, the
challenge squeezes at distinct counters are jointly uniform.  It says NOTHING
about a run whose block digests are themselves oracle outputs -- see (ii) in the
header.  The hypotheses are not vacuous: `fixed_digest_hypotheses_are_satisfiable`
exhibits `dig`, `Q` and `sel` satisfying them for every `d <= 13`. -/
theorem draw_at_fixed_digests_is_uniform (Q : Finset Transcript.Bytes) (d : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (sel : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : ∀ (k : JointChallengeSpace.Draw d) (j : Fin 3),
      (sel (k, j)).val = squeezeInputAt d dig k j)
    (hinj : Function.Injective sel) (E : Finset (JointChallengeSpace.JointSpace d)) :
    oracleProbability Q (digestDrawEvent Q d dig E)
      = JointChallengeSpace.jointProbability d E := by
  have hset : digestDrawEvent Q d dig E = encodedEvent Q d sel E := by
    apply Finset.ext
    intro T
    simp only [digestDrawEvent, encodedEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      draw_at_digests_is_encoded Q d dig sel hsel T]
  rw [hset, joint_pushforward_uniform Q d sel hinj E]

/-- (6) **A BAD-EVENT PROBABILITY OVER THE HASH.**  Composing
`draw_at_fixed_digests_is_uniform` with the adopted
`JointChallengeSpace.joint_union_bound`: conditioned on the block digests, the
probability -- under the random-oracle counting law on `OracleTable Q` -- that
the draw assembled from the schedule's squeezes falls in the adopted
`JointChallengeSpace.jointBadEvent` is at most the adopted
`ChallengeUnionBound.combinedBound`.

The left-hand side is a mass over the HASH TABLE, not over an abstract coordinate
point of `JointSpace`.  It inherits the adopted bound's own scope: it EXCLUDES
the dominant WHIR/Merkle events and is NOT the deployed system's soundness error.
It also inherits the conditioning: `dig` is quantified outside the law, so this
is not a statement about the run's own block digests -- see (ii) in the header. -/
theorem bad_draw_at_fixed_digests_le (Q : Finset Transcript.Bytes) (d : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (sel : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : ∀ (k : JointChallengeSpace.Draw d) (j : Fin 3),
      (sel (k, j)).val = squeezeInputAt d dig k j)
    (hinj : Function.Injective sel)
    (quotientDegree constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlogLen : logLane.length = d) (hgateLen : gateLane.length = d)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability Q (digestDrawEvent Q d dig
        (JointChallengeSpace.jointBadEvent d logCompare gateCompare logLane gateLane g
          (2 ^ d) coeffsOf))
      ≤ ChallengeUnionBound.combinedBound d quotientDegree d constraints := by
  rw [draw_at_fixed_digests_is_uniform Q d dig sel hsel hinj]
  exact JointChallengeSpace.joint_union_bound d quotientDegree constraints logCompare gateCompare
    logLane gateLane g coeffsOf hlogLen hgateLen hlogDeg hgateDeg hclen

/-! ### 6.1 The hypotheses of section 6 are satisfiable, at every `d <= 13` -/

theorem small_lt_byte_power (x : Nat) (hx : x < 256) : x < 256 ^ 32 :=
  lt_of_lt_of_le hx (by
    calc (256 : Nat) = 256 ^ 1 := (pow_one 256).symm
    _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-- The digest that spells a small number in the adopted little-endian encoding.
Concrete data only: thirty-two bytes, no digest space is enumerated. -/
def indexDigest (n : Nat) : Transcript.Digest := ⟨Transcript.le 32 n, Transcript.le_length 32 n⟩

theorem index_digest_injective (m n : Nat) (hm : m < 256) (hn : n < 256)
    (h : indexDigest m = indexDigest n) : m = n :=
  Transcript.le_injective_bounded 32 m n (small_lt_byte_power m hm) (small_lt_byte_power n hn)
    (congrArg Transcript.Digest.bytes h)

/-- A concrete block-digest assignment that SEPARATES THE BLOCKS: draw `k` is
given the digest spelling its adopted `JointChallengeSpace.sourceBlock`.  It is a
plain function of the index, not a hash output -- this is the witness that the
hypotheses of section 6 are satisfiable, not a model of a run. -/
def blockDigests (d : Nat) (k : JointChallengeSpace.Draw d) : Transcript.Digest :=
  indexDigest (JointChallengeSpace.sourceBlock d k)

theorem source_block_small (d : Nat) (hdb : d ≤ 13) (k : JointChallengeSpace.Draw d) :
    JointChallengeSpace.sourceBlock d k < 256 := by
  cases k with
  | gateAlpha => simp only [JointChallengeSpace.sourceBlock]; omega
  | gateTau _ => simp only [JointChallengeSpace.sourceBlock]; omega
  | outerLog r => have := r.isLt; simp only [JointChallengeSpace.sourceBlock]; omega
  | outerGate r => have := r.isLt; simp only [JointChallengeSpace.sourceBlock]; omega

theorem block_digests_separate (d : Nat) (hdb : d ≤ 13) (k k2 : JointChallengeSpace.Draw d)
    (h : blockDigests d k = blockDigests d k2) :
    JointChallengeSpace.sourceBlock d k = JointChallengeSpace.sourceBlock d k2 :=
  index_digest_injective _ _ (source_block_small d hdb k) (source_block_small d hdb k2) h

/-- (5) **DISTINCTNESS FROM THE BLOCKS ALONE.**  When the digest assignment
separates the adopted `JointChallengeSpace.sourceBlock`, the whole schedule of
oracle inputs is injective: same block forces the same counter range, and the
adopted counters then separate the squeezes.  This is the hypothesis-free
counterpart of `squeeze_inputs_distinct_or_collision`, which has to go through a
collision alternative because a HASH need not separate the blocks. -/
theorem schedule_distinct_of_separating_digests (d : Nat) (hdb : d ≤ 13)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (hsep : ∀ k k2 : JointChallengeSpace.Draw d, dig k = dig k2 →
      JointChallengeSpace.sourceBlock d k = JointChallengeSpace.sourceBlock d k2) :
    Function.Injective (scheduleIndex d dig) := by
  rintro ⟨k, j⟩ ⟨k2, j2⟩ h
  simp only [scheduleIndex, squeezeInputAt] at h
  have hj := j.isLt
  have hj2 := j2.isLt
  obtain ⟨hdig, hcnt⟩ := challenge_input_injective _ _ _ _
    (source_counter_bound d hdb k j) (source_counter_bound d hdb k2 j2) h
  have hblk := hsep k k2 hdig
  cases k with
  | gateAlpha =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact congrArg _ (Fin.ext (by omega))
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
  | gateTau i =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          have hii : i = i2 := Fin.ext (by omega)
          have hjj : j = j2 := Fin.ext (by omega)
          rw [hii, hjj]
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
  | outerLog r =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          have hrr : r = r2 := Fin.ext (by omega)
          have hjj : j = j2 := Fin.ext (by omega)
          rw [hrr, hjj]
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
  | outerGate r =>
      cases k2 with
      | gateAlpha =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
      | gateTau i2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
      | outerLog r2 =>
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          exact absurd hcnt (by omega)
      | outerGate r2 =>
          simp only [JointChallengeSpace.sourceBlock] at hblk
          simp only [JointChallengeSpace.sourceCounter] at hcnt
          have hrr : r = r2 := Fin.ext (by omega)
          have hjj : j = j2 := Fin.ext (by omega)
          rw [hrr, hjj]

theorem schedule_index_mem (d : Nat) (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (kj : JointChallengeSpace.Draw d × Fin 3) : scheduleIndex d dig kj ∈ scheduleSet d dig :=
  Finset.mem_image_of_mem _ (Finset.mem_univ kj)

/-- The schedule as a membership-carrying query family into its own query set. -/
def scheduleSel (d : Nat) (dig : JointChallengeSpace.Draw d → Transcript.Digest) :
    JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ scheduleSet d dig } :=
  fun kj => ⟨scheduleIndex d dig kj, schedule_index_mem d dig kj⟩

/-- (6) **THE HYPOTHESES OF SECTION 6 ARE SATISFIABLE**, at every degree bound
the adopted `Verifier.envelope` allows.  `blockDigests d` is a concrete digest
assignment, `scheduleSet d (blockDigests d)` a concrete query set, and
`scheduleSel d (blockDigests d)` a concrete INJECTIVE query family for it.  So
`draw_at_fixed_digests_is_uniform` and `bad_draw_at_fixed_digests_le` are not
vacuously true on an empty hypothesis set. -/
theorem fixed_digest_hypotheses_are_satisfiable (d : Nat) (hdb : d ≤ 13) :
    (∀ (k : JointChallengeSpace.Draw d) (j : Fin 3),
        (scheduleSel d (blockDigests d) (k, j)).val
          = squeezeInputAt d (blockDigests d) k j) ∧
      Function.Injective (scheduleSel d (blockDigests d)) := by
  refine ⟨fun k j => rfl, ?_⟩
  intro a b h
  exact schedule_distinct_of_separating_digests d hdb (blockDigests d)
    (block_digests_separate d hdb) (congrArg Subtype.val h)

/-- (6) The same at the DEPLOYED degree bound `degreeBits = 13`: `40` draws,
`120` pairwise distinct oracle inputs. -/
theorem fixed_digest_hypotheses_are_satisfiable_at_thirteen :
    (∀ (k : JointChallengeSpace.Draw 13) (j : Fin 3),
        (scheduleSel 13 (blockDigests 13) (k, j)).val
          = squeezeInputAt 13 (blockDigests 13) k j) ∧
      Function.Injective (scheduleSel 13 (blockDigests 13)) :=
  fixed_digest_hypotheses_are_satisfiable 13 (by omega)

/-- (6) **THE BOUND, FULLY INSTANTIATED AT `degreeBits = 13`.**  Every hypothesis
about the schedule has been discharged by
`fixed_digest_hypotheses_are_satisfiable_at_thirteen`; what remains are the
adopted lane-shape hypotheses of `JointChallengeSpace.joint_union_bound`.  This
is the non-vacuous witness that `bad_draw_at_fixed_digests_le` has content. -/
theorem bad_draw_bound_at_thirteen (quotientDegree constraints : Nat)
    (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlogLen : logLane.length = 13) (hgateLen : gateLane.length = 13)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ constraints) :
    oracleProbability (scheduleSet 13 (blockDigests 13))
        (digestDrawEvent (scheduleSet 13 (blockDigests 13)) 13 (blockDigests 13)
          (JointChallengeSpace.jointBadEvent 13 logCompare gateCompare logLane gateLane g
            (2 ^ 13) coeffsOf))
      ≤ ChallengeUnionBound.combinedBound 13 quotientDegree 13 constraints :=
  bad_draw_at_fixed_digests_le _ 13 (blockDigests 13) (scheduleSel 13 (blockDigests 13))
    fixed_digest_hypotheses_are_satisfiable_at_thirteen.1
    fixed_digest_hypotheses_are_satisfiable_at_thirteen.2
    quotientDegree constraints logCompare gateCompare logLane gateLane g coeffsOf
    hlogLen hgateLen hlogDeg hgateDeg hclen

/-! ### 6.2 A CLOSED instance of the bound, and the non-degeneracy of the payoff -/

/-- A lane of `13` rounds carrying empty messages: the cheapest witness that the
adopted lane-shape hypotheses of `bad_draw_bound_at_thirteen` are satisfiable. -/
def trivialLane (x : Element) : List ConditionalSoundness.LaneRound :=
  List.replicate 13 ⟨[], [], x⟩

theorem trivial_lane_length (x : Element) : (trivialLane x).length = 13 :=
  List.length_replicate _ _

theorem trivial_lane_deg (x : Element) (n : Nat) :
    ∀ r ∈ trivialLane x, r.message.length ≤ n ∧ r.truth.length ≤ n := by
  intro r hr
  rw [trivialLane, List.mem_replicate] at hr
  rw [hr.2]
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- (6) **THE BOUND WITH EVERY HYPOTHESIS DISCHARGED.**  No side condition is
left: the query set, the digest assignment, the query family AND the lane shapes
are all concrete, so this is a closed inequality between a mass on oracle tables
and a number.  It is the strongest non-vacuity evidence for section 6 -- the
conclusion of `bad_draw_at_fixed_digests_le` is reached from no assumptions at
all beyond the choice of the field element `x`. -/
theorem bad_draw_bound_at_thirteen_closed (x : Element) :
    oracleProbability (scheduleSet 13 (blockDigests 13))
        (digestDrawEvent (scheduleSet 13 (blockDigests 13)) 13 (blockDigests 13)
          (JointChallengeSpace.jointBadEvent 13 x x (trivialLane x) (trivialLane x) (fun _ => x)
            (2 ^ 13) (fun _ => [])))
      ≤ ChallengeUnionBound.combinedBound 13 0 13 0 :=
  bad_draw_bound_at_thirteen 0 0 x x (trivialLane x) (trivialLane x) (fun _ => x) (fun _ => [])
    (trivial_lane_length x) (trivial_lane_length x) (trivial_lane_deg x 5)
    (trivial_lane_deg x (0 + 2)) (fun _ _ => by simp)

/-- (6) **THE PAYOFF IS NOT `0 = 0`.**  At the concrete `d = 13` witness the law
gives the whole space mass `1`.  Together with `witness_mass_empty` this shows
`draw_at_fixed_digests_is_uniform` transports a genuinely normalized law, not a
degenerate one. -/
theorem witness_mass_univ :
    oracleProbability (scheduleSet 13 (blockDigests 13))
      (digestDrawEvent (scheduleSet 13 (blockDigests 13)) 13 (blockDigests 13) Finset.univ)
      = 1 := by
  rw [draw_at_fixed_digests_is_uniform _ 13 (blockDigests 13) (scheduleSel 13 (blockDigests 13))
    fixed_digest_hypotheses_are_satisfiable_at_thirteen.1
    fixed_digest_hypotheses_are_satisfiable_at_thirteen.2]
  unfold JointChallengeSpace.jointProbability
  rw [Finset.card_univ]
  exact div_self (JointChallengeSpace.joint_space_card_cast_pos 13).ne'

/-- (6) The empty event has mass `0` at the same witness. -/
theorem witness_mass_empty :
    oracleProbability (scheduleSet 13 (blockDigests 13))
      (digestDrawEvent (scheduleSet 13 (blockDigests 13)) 13 (blockDigests 13) ∅) = 0 := by
  rw [draw_at_fixed_digests_is_uniform _ 13 (blockDigests 13) (scheduleSel 13 (blockDigests 13))
    fixed_digest_hypotheses_are_satisfiable_at_thirteen.1
    fixed_digest_hypotheses_are_satisfiable_at_thirteen.2]
  exact JointChallengeSpace.joint_probability_empty 13

/-! ## 7. The frame/challenge separation: what a run-level statement needs

No probability is claimed in this section.  It supplies the two structural facts
the run-level theorem of section 8 rests on -- the disjointness of the frame and
challenge query families, and the congruence lemma saying that the run's block
digests read the oracle ONLY on the frame family -- and states, in
`run_draw_event_mem`, the exact form of the run's own event.
-/

/-- (6) **FRAMES AND SQUEEZES ARE NEVER THE SAME QUERY.**  The adopted
`Transcript.frame` begins with `Transcript.framePrefix` and the adopted
`Transcript.challengeInput` with `Transcript.challengePrefix`; both prefixes are
longer than sixteen bytes and they differ at byte `15`, so the two families of
oracle inputs are disjoint for every digest, tag, payload and counter. -/
theorem frame_ne_challenge_input (dg e : Transcript.Digest) (t : Transcript.Byte)
    (pl : Transcript.Bytes) (n : Nat) :
    Transcript.frame dg t pl ≠ Transcript.challengeInput e n := by
  intro h
  have hf : (Transcript.frame dg t pl)[15]? = Transcript.framePrefix[15]? := by
    simp only [Transcript.frame, List.append_assoc]
    exact List.getElem?_append (by decide)
  have hc : (Transcript.challengeInput e n)[15]? = Transcript.challengePrefix[15]? := by
    simp only [Transcript.challengeInput, List.append_assoc]
    exact List.getElem?_append (by decide)
  rw [h, hc] at hf
  exact absurd hf.symm (by decide)

/-- Two hashes agree on every `Transcript.frame`-shaped input.  This is the
relation the whole absorb chain is congruent under. -/
def FrameAgreement (h1 h2 : Transcript.Hash) : Prop :=
  ∀ (dg : Transcript.Digest) (t : Transcript.Byte) (pl : Transcript.Bytes),
    h1 (Transcript.frame dg t pl) = h2 (Transcript.frame dg t pl)

theorem absorb_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (s : Transcript.State) (t : Transcript.Byte) (pl : Transcript.Bytes) :
    Transcript.absorb h1 s t pl = Transcript.absorb h2 s t pl := by
  simp only [Transcript.absorb, ha s.digest t pl]

theorem absorb_messages_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (ms : List OuterInitial.Message) (s : Transcript.State) :
    OuterInitial.absorbMessages h1 s ms = OuterInitial.absorbMessages h2 s ms := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
      simp only [OuterInitial.absorbMessages, List.foldl_cons]
      show OuterInitial.absorbMessages h1 (OuterInitial.absorbMessage h1 s m) ms
        = OuterInitial.absorbMessages h2 (OuterInitial.absorbMessage h2 s m) ms
      rw [show OuterInitial.absorbMessage h1 s m = OuterInitial.absorbMessage h2 s m from
        absorb_congr ha s m.tag m.payload, ih]

theorem domain_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (s : Transcript.State) (l : String) :
    Transcript.domain h1 s l = Transcript.domain h2 s l :=
  absorb_congr ha s 1 (Transcript.ascii l)

/-- A squeeze moves the counter and nothing else: the adopted `OuterInitial.draw`
never changes the state digest, so it never depends on a hash value. -/
theorem draw_state (h : Transcript.Hash) (s : Transcript.State) :
    (OuterInitial.draw h s).2 = ⟨s.digest, s.counter + 3⟩ := rfl

theorem draw_many_state (h : Transcript.Hash) (n : Nat) (s : Transcript.State) :
    (OuterInitial.drawMany h n s).2 = ⟨s.digest, s.counter + 3 * n⟩ := by
  obtain ⟨_, hd, hc⟩ := OuterInitial.draw_many_shape h n s
  show (⟨(OuterInitial.drawMany h n s).2.digest, (OuterInitial.drawMany h n s).2.counter⟩ :
    Transcript.State) = _
  rw [hd, hc]

theorem base_state_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (s : Verifier.Statement) :
    OuterInitial.baseState h1 c s = OuterInitial.baseState h2 c s :=
  absorb_messages_congr ha _ _

theorem eta_state_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (s : Verifier.Statement) :
    OuterInitial.etaState h1 c s = OuterInitial.etaState h2 c s := by
  simp only [OuterInitial.etaState, base_state_congr ha c s, domain_congr ha]

theorem denominator_state_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (s : Verifier.Statement) :
    OuterInitial.denominatorState h1 c s = OuterInitial.denominatorState h2 c s := by
  simp only [OuterInitial.denominatorState, draw_state, eta_state_congr ha c s, domain_congr ha]

theorem after_gamma_state (h : Transcript.Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.preRoot h c s).afterGamma
      = ⟨(OuterInitial.denominatorState h c s).digest, 6⟩ := rfl

theorem relation_state_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (s : Verifier.Statement) :
    OuterInitial.relationState h1 c s = OuterInitial.relationState h2 c s := by
  simp only [OuterInitial.relationState, OuterInitial.mixState, OuterInitial.normRootState,
    after_gamma_state, draw_state, denominator_state_congr ha c s, domain_congr ha,
    absorb_congr ha]

theorem after_kappa_state (h : Transcript.Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.relations h c s).afterKappa
      = ⟨(OuterInitial.relationState h c s).digest, 9⟩ := rfl

theorem derive_state_unfold (h : Transcript.Hash) (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive h c s).state
      = (OuterInitial.drawMany h c.degreeBits (OuterInitial.draw h
          (OuterInitial.drawMany h c.degreeBits
            (OuterInitial.relations h c s).afterKappa).2).2).2 := rfl

theorem derive_state_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (s : Verifier.Statement) :
    (OuterInitial.derive h1 c s).state = (OuterInitial.derive h2 c s).state := by
  simp only [derive_state_unfold, draw_many_state, draw_state, after_kappa_state,
    relation_state_congr ha c s]

theorem round_committed_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (st : Transcript.State) (i : Nat) (m : Verifier.CoupledMessage) :
    OuterAdapter.roundCommitted h1 st i m.1 m.2 = OuterAdapter.roundCommitted h2 st i m.1 m.2 := by
  rw [InstalledRoundCommit.round_committed_is_the_frame_fold,
    InstalledRoundCommit.round_committed_is_the_frame_fold, absorb_messages_congr ha]

theorem concrete_chain_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2) :
    ∀ (ms : List Verifier.CoupledMessage) (st : Transcript.State) (i : Nat),
      InstalledRoundCommit.concreteChain h1 st i ms
        = InstalledRoundCommit.concreteChain h2 st i ms
  | [], _, _ => rfl
  | m :: ms, st, i => by
      rw [InstalledRoundCommit.concrete_chain_step, InstalledRoundCommit.concrete_chain_step,
        round_committed_congr ha st i m, concrete_chain_congr ha ms _ (i + 1)]

theorem actual_base_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (p : Verifier.Proof) :
    InstalledRoundCommit.actualBase h1 c p = InstalledRoundCommit.actualBase h2 c p := by
  simp only [InstalledRoundCommit.actualBase, relation_state_congr ha]

theorem actual_chain_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (p : Verifier.Proof) :
    InstalledRoundCommit.actualChain h1 c p = InstalledRoundCommit.actualChain h2 c p := by
  simp only [InstalledRoundCommit.actualChain, derive_state_congr ha, concrete_chain_congr ha]

/-- (6) **THE BLOCK DIGESTS READ THE ORACLE ONLY AT FRAMES.**  Two hashes that
agree on every `Transcript.frame`-shaped input give the run the SAME block
digests: the relation-prefix digest and every round commit digest are folds of
`Transcript.absorb`, and the intervening squeezes move only the counter
(`draw_state`, `draw_many_state`). -/
theorem source_digest_congr {h1 h2 : Transcript.Hash} (ha : FrameAgreement h1 h2)
    (c : Verifier.Config) (p : Verifier.Proof) :
    sourceDigest h1 c p = sourceDigest h2 c p := by
  funext k
  cases k <;>
    simp only [sourceDigest, actual_base_congr ha c p, actual_chain_congr ha c p]

open Classical in
/-- A hash with EVERY challenge-shaped answer overwritten by `f`. -/
noncomputable def rewriteChallenges (thash : Transcript.Hash)
    (f : Transcript.Bytes → Transcript.Digest) : Transcript.Hash :=
  fun q =>
    if ∃ (e : Transcript.Digest) (n : Nat), q = Transcript.challengeInput e n then f q else thash q

/-- (6) **THE BLOCK DIGESTS IGNORE EVERY CHALLENGE ANSWER.**  Rewriting ALL
challenge-shaped answers of a hash, arbitrarily and all at once, leaves the run's
block digests unchanged.  This is the sharp form of `source_digest_congr`: it
shows the congruence is not vacuous quantification but a real independence, and
it is the fact the frame/challenge fibration of
`run_bad_draw_probability_le_fibrewise` rests on. -/
theorem source_digest_ignores_challenge_answers (thash : Transcript.Hash)
    (f : Transcript.Bytes → Transcript.Digest) (c : Verifier.Config) (p : Verifier.Proof) :
    sourceDigest (rewriteChallenges thash f) c p = sourceDigest thash c p := by
  refine source_digest_congr (fun dg t pl => ?_) c p
  simp only [rewriteChallenges]
  rw [if_neg]
  rintro ⟨e, n, hq⟩
  exact frame_ne_challenge_input dg e t pl n hq

/-- (6) **THE CONGRUENCE LEMMA, ON TABLES.**  If two oracle tables agree at every
query that is NOT one of the schedule's challenge inputs, the run's block digests
are the same under both.  Equivalently: the block digests are a function of the
FRAME restriction of the table alone.  This is the fact a fibrewise run-level
statement rests on -- the frame half of the query set determines `dig`, and the
challenge half is then free.  Section 8 carries that fibration out, in the
sharper form `source_digest_congr` (agreement on `Transcript.frame`-shaped
queries alone); `source_digest_ignores_challenge_answers` is the same fact stated
as an independence. -/
theorem source_digest_depends_only_on_frame_queries (Q : Finset Transcript.Bytes)
    (T T2 : OracleTable Q) (c : Verifier.Config) (p : Verifier.Proof)
    (hagree : ∀ q : { q : Transcript.Bytes // q ∈ Q },
      (∀ (e : Transcript.Digest) (n : Nat), q.val ≠ Transcript.challengeInput e n) → T q = T2 q) :
    sourceDigest (hashOf Q T) c p = sourceDigest (hashOf Q T2) c p := by
  refine source_digest_congr (fun dg t pl => ?_) c p
  by_cases hm : Transcript.frame dg t pl ∈ Q
  · have hq := hagree ⟨Transcript.frame dg t pl, hm⟩
      (fun e n => frame_ne_challenge_input dg e t pl n)
    simp only [hashOf, hm, dif_pos, hq]
  · simp only [hashOf, hm, dif_neg, not_false_iff]

open Classical in
/-- The event, on oracle tables, that the RUN's adopted draw lands in `E`. -/
noncomputable def runDrawEvent (Q : Finset Transcript.Bytes) (c : Verifier.Config)
    (p : Verifier.Proof) (E : Finset (JointChallengeSpace.JointSpace c.degreeBits)) :
    Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => InstalledRoundCommit.actualDigestDraw (hashOf Q T) c p ∈ E)

/-- (6) **WHERE THE MISSING ARGUMENT GOES.**  The run's event is the
fixed-digest event of section 6 -- with the digest assignment
`sourceDigest (hashOf Q T) c p`, which is a function OF THE TABLE.  That is the
precise reason `draw_at_fixed_digests_is_uniform` does not apply to it directly.  Section 8
closes that gap by summing over the frame fibres of `frameSplit`, at the cost of
one additive term for the fibres whose schedule is not injective
(`run_draw_probability_le_fibrewise`). -/
theorem run_draw_event_mem (Q : Finset Transcript.Bytes) (c : Verifier.Config)
    (p : Verifier.Proof) (E : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (T : OracleTable Q) :
    T ∈ runDrawEvent Q c p E ↔
      drawAtDigests (hashOf Q T) c.degreeBits (sourceDigest (hashOf Q T) c p) ∈ E := by
  simp only [runDrawEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    actual_digest_draw_is_draw_at_digests (hashOf Q T) c p]

/-! ## 8. THE RUN-LEVEL BOUND, FIBREWISE OVER THE FRAME QUERIES

This section carries out the decomposition sketched in (ii) of the header and
states the module's ONLY run-level mass.  Nothing here is conditioned on the
block digests: the digest assignment is the run's own
`sourceDigest (hashOf Q T) c p`, a function of the table.

The argument is NOT a sequential fresh-query induction.  It is a Fubini over the
fibres of a `T`-INDEPENDENT split of the query set, by STRING SHAPE: a query is
challenge-shaped or it is not, and that is decided by its byte `15`
(`ChallengeShaped`), before any table is sampled.  Inside one frame fibre the
block digests are constant (`source_digest_congr`), so the schedule is a FIXED
family of challenge-half queries, and `restrict_ratio` makes the challenge draw
exactly `jointProbability`-distributed whenever that family is injective.  The
fibres where it is NOT injective are collected into one additive term.

THAT ADDITIVE TERM IS NOT BOUNDED HERE, AND SECTION 8.1 SAYS WHAT IT IS: `1` at
every frame-free query set, the `closureWitness` of this section included, and
`< 1` at a query set that answers the run's own frame inputs, which section 8.2
exhibits.  Read section 8.1 before quoting the bound.
-/

/-- **THE DECIDABLE FRAME/CHALLENGE SEPARATOR.**  A query is challenge-shaped when
its byte `15` is the byte `15` of the adopted `Transcript.challengePrefix`.  This
is a purely syntactic test on the STRING -- decidable, and independent of any
table -- and it is what makes the split of section 8 a `T`-independent split of
`Q`.  It is coarser than "is a `Transcript.challengeInput`", which is all that is
needed: every squeeze input passes it (`challenge_input_shaped`) and no
`Transcript.frame` does (`frame_not_shaped`). -/
def ChallengeShaped (q : Transcript.Bytes) : Prop :=
  q[15]? = Transcript.challengePrefix[15]?

instance challengeShapedDecidable (q : Transcript.Bytes) : Decidable (ChallengeShaped q) := by
  unfold ChallengeShaped
  infer_instance

theorem challenge_input_shaped (e : Transcript.Digest) (n : Nat) :
    ChallengeShaped (Transcript.challengeInput e n) := by
  simp only [ChallengeShaped, Transcript.challengeInput, List.append_assoc]
  exact List.getElem?_append (by decide)

theorem frame_not_shaped (dg : Transcript.Digest) (t : Transcript.Byte) (pl : Transcript.Bytes) :
    ¬ ChallengeShaped (Transcript.frame dg t pl) := by
  intro h
  have hf : (Transcript.frame dg t pl)[15]? = Transcript.framePrefix[15]? := by
    simp only [Transcript.frame, List.append_assoc]
    exact List.getElem?_append (by decide)
  rw [ChallengeShaped, hf] at h
  exact absurd h (by decide)

/-- The byte-`15` test refines the hypothesis shape of
`source_digest_depends_only_on_frame_queries`. -/
theorem not_shaped_ne_challenge_input (q : Transcript.Bytes) (h : ¬ ChallengeShaped q)
    (e : Transcript.Digest) (n : Nat) : q ≠ Transcript.challengeInput e n := by
  intro hq
  exact h (hq ▸ challenge_input_shaped e n)

/-- The challenge half of a query set. -/
abbrev ChallengeHalf (Q : Finset Transcript.Bytes) :=
  { a : { q : Transcript.Bytes // q ∈ Q } // ChallengeShaped a.val }

/-- The frame half of a query set: everything the squeezes never touch. -/
abbrev FrameHalf (Q : Finset Transcript.Bytes) :=
  { a : { q : Transcript.Bytes // q ∈ Q } // ¬ ChallengeShaped a.val }

/-- (8) **THE `T`-INDEPENDENT SPLIT OF THE TABLE SPACE.**  An oracle table is
exactly a pair: its answers on the challenge half and its answers on the frame
half.  The split is by string shape, so unlike `splitTable` along a run-dependent
schedule it is available BEFORE the table is sampled. -/
noncomputable def frameSplit (Q : Finset Transcript.Bytes) :
    OracleTable Q ≃ (ChallengeHalf Q → Block) × (FrameHalf Q → Block) :=
  (Equiv.arrowCongr
      (Equiv.sumCompl (fun a : { q : Transcript.Bytes // q ∈ Q } => ChallengeShaped a.val)).symm
      (Equiv.refl Block)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem frame_split_fst (Q : Finset Transcript.Bytes) (T : OracleTable Q) :
    (frameSplit Q T).1 = fun i => T i.val := rfl

theorem frame_split_snd (Q : Finset Transcript.Bytes) (T : OracleTable Q) :
    (frameSplit Q T).2 = fun a => T a.val := rfl

/-- Every counter the schedule ever squeezes at is below `6 * degreeBits + 12`:
the largest is the last gate tau column, `12 + 3 * d + 3 * (d - 1) + 2`. -/
theorem source_counter_small (d : Nat) (k : JointChallengeSpace.Draw d) (j : Fin 3) :
    JointChallengeSpace.sourceCounter d k + j.val < 6 * d + 12 := by
  have hj := j.isLt
  cases k with
  | gateAlpha => simp only [JointChallengeSpace.sourceCounter]; omega
  | gateTau i =>
      have hi := i.isLt
      simp only [JointChallengeSpace.sourceCounter]
      omega
  | outerLog r => simp only [JointChallengeSpace.sourceCounter]; omega
  | outerGate r => simp only [JointChallengeSpace.sourceCounter]; omega

/-- **THE QUERY SET IS BIG ENOUGH.**  `Q` answers every challenge input at every
counter the schedule can reach, AT EVERY DIGEST.  This is what lets the schedule
of a fibre be a family INTO `Q` without knowing the run's digests in advance; it
is the one hypothesis of `run_draw_probability_le_fibrewise` beyond the model
itself, and `query_closure_is_satisfiable` shows it has models.

WHAT IT DOES NOT SAY.  It constrains CHALLENGE-shaped strings only.  It forces no
`Transcript.frame` into `Q` at all -- every closed `Q` has a closed frame-free
subset (`closure_has_frame_free_sub`) -- and on a frame-free `Q` the additive
term of section 8 is exactly `1` (`clash_term_one`).  Section 8.1 is the
disclosure; `informative_query_set_exists` is the query set at which the term is
`< 1`. -/
def QueryClosure (Q : Finset Transcript.Bytes) (d : Nat) : Prop :=
  ∀ (e : Transcript.Digest) (n : Nat), n < 6 * d + 12 → Transcript.challengeInput e n ∈ Q

/-- **THE MINIMAL CLOSURE WITNESS**: the challenge inputs at the `6 * d + 12`
reachable counters, at every digest.  Finite because `Transcript.Digest` is
finite (`digestFinite`), and never enumerated -- the set has about `2 ^ 256`
members.  It contains NO frame, which is what section 8.1 is about. -/
noncomputable def closureWitness (d : Nat) : Finset Transcript.Bytes :=
  (Set.finite_range (fun z : Transcript.Digest × Fin (6 * d + 12) =>
    Transcript.challengeInput z.1 z.2.val)).toFinset

theorem closure_witness_closed (d : Nat) : QueryClosure (closureWitness d) d := by
  intro e n hn
  rw [closureWitness, Set.Finite.mem_toFinset]
  exact ⟨(e, ⟨n, hn⟩), rfl⟩

/-- (8) **THE CLOSURE HYPOTHESIS IS SATISFIABLE.**  `closureWitness` is a model.
The witness is a NONCOMPUTABLE existence statement, which is all the theorem
needs: `Q` is only ever a parameter of the counting law.  It is also the WORST
query set for the additive term of section 8 -- being frame-free, it makes that
term `1` (`closure_witness_clash_term_one`). -/
theorem query_closure_is_satisfiable (d : Nat) :
    ∃ Q : Finset Transcript.Bytes, QueryClosure Q d :=
  ⟨closureWitness d, closure_witness_closed d⟩

open Classical in
/-- The event, on oracle tables, that the run's OWN schedule of oracle inputs
fails to be injective.  By `squeeze_inputs_distinct_or_round_digest_clash` this
event is contained in `{T | RoundDigestClash (hashOf Q T) c p}` whenever
`c.degreeBits ≤ 13`, so it is the LOCALIZED clash term, not the global collision
tautology. -/
noncomputable def scheduleNonInjectiveEvent (Q : Finset Transcript.Bytes) (c : Verifier.Config)
    (p : Verifier.Proof) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => ¬ Function.Injective (squeezeIndex (hashOf Q T) c p))

/-- (8) The non-injective event is the localized clash event, at every enveloped
`degreeBits`.  This replaces the global collision tautology -- which would make
the additive term of `run_draw_probability_le_fibrewise` identically `1` for
every `Q` -- by a property of THIS run's own round digests.  It does NOT make the
term small, and it does not even make it `< 1`: on a frame-free `Q`, including
the `closureWitness` of `query_closure_is_satisfiable`, the LOCALIZED term is `1`
as well (`clash_term_one`, `closure_witness_clash_term_one`).  Localizing is
necessary, not sufficient. -/
theorem schedule_non_injective_is_clash (Q : Finset Transcript.Bytes) (c : Verifier.Config)
    (p : Verifier.Proof) (hdb : c.degreeBits ≤ 13) (T : OracleTable Q)
    (hT : T ∈ scheduleNonInjectiveEvent Q c p) : RoundDigestClash (hashOf Q T) c p := by
  have hmem : ¬ Function.Injective (squeezeIndex (hashOf Q T) c p) := by
    simpa only [scheduleNonInjectiveEvent, Finset.mem_filter, Finset.mem_univ, true_and] using hT
  rcases squeeze_inputs_distinct_or_round_digest_clash (hashOf Q T) c p hdb with hinj | hclash
  · exact absurd hinj hmem
  · exact hclash

/-- (8) **THE RUN-LEVEL BOUND.**  The mass -- under the random-oracle counting law
on `OracleTable Q` -- of the event that the RUN'S OWN adopted draw
(`InstalledRoundCommit.actualDigestDraw` at the run's own block digests, which are
themselves oracle outputs) lands in `E`, is at most the ideal
`JointChallengeSpace.jointProbability` of `E` plus the mass of the event that the
run's schedule of oracle inputs is not injective.

NOTHING IS CONDITIONED.  Unlike `draw_at_fixed_digests_is_uniform`, the digest
assignment is not quantified outside the law: it is `sourceDigest (hashOf Q T) c p`,
a function of the table being weighed.  This is the first statement in this module
about the run's own draw.

HOW IT IS PROVED, and what it is NOT.  It is a Fubini over the fibres of
`frameSplit`, a split of `Q` by STRING SHAPE that does not depend on the table.
Inside one fibre the block digests are constant (`source_digest_congr` through
`frame_not_shaped`), so the schedule is a FIXED injective family into the
challenge half and `restrict_ratio` gives the challenge draw EXACTLY
`jointProbability`; the fibres where the family is not injective are bounded by
`1` and collected into the additive term.  No sequential fresh-query induction
and no birthday argument is used, and none is needed for THIS statement; they are
needed only to bound the additive term, which is left unbounded here.

WHAT THE HYPOTHESIS SAYS.  `QueryClosure` asks `Q` to answer every challenge
input at every reachable counter, at EVERY digest.  It is satisfiable
(`query_closure_is_satisfiable`), noncomputably.

HOW TO READ IT, AND AT WHICH `Q`.  The statement is TRUE and, as a statement, not
vacuous; but `QueryClosure` alone says nothing about frames, and on a frame-free
`Q` -- the `closureWitness` of `query_closure_is_satisfiable` included -- the
additive term is exactly `1`, so the bound degenerates to
`≤ jointProbability E + 1` and is then a consequence of
`oracle_probability_le_one` alone (`clash_term_one`,
`closure_witness_clash_term_one`, `run_bound_trivial_at_frame_free`).  A `Q` at
which the term is `< 1` -- one that also answers the run's own frame inputs -- is
exhibited by `informative_query_set_exists`.  NO SMALL BOUND ON THE ADDITIVE TERM
IS PROVED; that is the birthday/sequential count over the frame fibres, and it is
not carried out in this tree.  Section 8.1 is the disclosure in full.

WHAT IS STILL OUT OF SCOPE.  The proof `p` is a FIXED argument, quantified outside
the law: an ADAPTIVE prover, whose proof is chosen as a function of the table it
has already queried, is not modelled anywhere in this tree, and that -- not the
counting -- is the Fiat--Shamir-specific step. -/
theorem run_draw_probability_le_fibrewise (Q : Finset Transcript.Bytes) (c : Verifier.Config)
    (p : Verifier.Proof) (hQ : QueryClosure Q c.degreeBits)
    (E : Finset (JointChallengeSpace.JointSpace c.degreeBits)) :
    oracleProbability Q (runDrawEvent Q c p E)
      ≤ JointChallengeSpace.jointProbability c.degreeBits E
        + oracleProbability Q (scheduleNonInjectiveEvent Q c p) := by
  classical
  obtain ⟨b0⟩ := Fintype.card_pos_iff.mp block_card_pos
  have hg : ∀ (g : ChallengeHalf Q → Block) (f : FrameHalf Q → Block) (i : ChallengeHalf Q),
      (frameSplit Q).symm (g, f) i.val = g i := by
    intro g f i
    have h0 : ((frameSplit Q) ((frameSplit Q).symm (g, f))).1 = g :=
      congrArg Prod.fst ((frameSplit Q).apply_symm_apply (g, f))
    rw [frame_split_fst] at h0
    exact congrFun h0 i
  have hf : ∀ (g : ChallengeHalf Q → Block) (f : FrameHalf Q → Block) (a : FrameHalf Q),
      (frameSplit Q).symm (g, f) a.val = f a := by
    intro g f a
    have h0 : ((frameSplit Q) ((frameSplit Q).symm (g, f))).2 = f :=
      congrArg Prod.snd ((frameSplit Q).apply_symm_apply (g, f))
    rw [frame_split_snd] at h0
    exact congrFun h0 a
  have hdigind : ∀ (f : FrameHalf Q → Block) (g1 g2 : ChallengeHalf Q → Block),
      sourceDigest (hashOf Q ((frameSplit Q).symm (g1, f))) c p
        = sourceDigest (hashOf Q ((frameSplit Q).symm (g2, f))) c p := by
    intro f g1 g2
    refine source_digest_congr (fun dg t pl => ?_) c p
    by_cases hm : Transcript.frame dg t pl ∈ Q
    · have h1 := hf g1 f ⟨⟨Transcript.frame dg t pl, hm⟩, frame_not_shaped dg t pl⟩
      have h2 := hf g2 f ⟨⟨Transcript.frame dg t pl, hm⟩, frame_not_shaped dg t pl⟩
      simp only [hashOf, hm, dif_pos, h1, h2]
    · simp only [hashOf, hm, dif_neg, not_false_iff]
  -- ONE FRAME FIBRE
  have hfibre : ∀ f : FrameHalf Q → Block,
      ((Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
          InstalledRoundCommit.actualDigestDraw
            (hashOf Q ((frameSplit Q).symm (g, f))) c p ∈ E)).card : ℚ)
        ≤ JointChallengeSpace.jointProbability c.degreeBits E
            * (Fintype.card (ChallengeHalf Q → Block) : ℚ)
          + ((Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
              ¬ Function.Injective
                (squeezeIndex (hashOf Q ((frameSplit Q).symm (g, f))) c p))).card : ℚ) := by
    intro f
    by_cases hinj : ∀ g : ChallengeHalf Q → Block,
        Function.Injective (squeezeIndex (hashOf Q ((frameSplit Q).symm (g, f))) c p)
    · -- the schedule is injective in this fibre: the challenge draw is exactly uniform
      have hmem : ∀ (k : JointChallengeSpace.Draw c.degreeBits) (j : Fin 3),
          squeezeInputAt c.degreeBits
            (sourceDigest (hashOf Q ((frameSplit Q).symm ((fun _ => b0), f))) c p) k j ∈ Q :=
        fun k j => hQ _ _ (source_counter_small c.degreeBits k j)
      set dig := sourceDigest (hashOf Q ((frameSplit Q).symm ((fun _ => b0), f))) c p with hdigdef
      set sel : JointChallengeSpace.Draw c.degreeBits × Fin 3 → ChallengeHalf Q :=
        fun kj => ⟨⟨squeezeInputAt c.degreeBits dig kj.1 kj.2, hmem kj.1 kj.2⟩,
          challenge_input_shaped _ _⟩
      have hselinj : Function.Injective sel := by
        intro a b hab
        exact hinj (fun _ => b0) (congrArg (fun z => z.val.val) hab)
      have hdraw : ∀ g : ChallengeHalf Q → Block,
          InstalledRoundCommit.actualDigestDraw (hashOf Q ((frameSplit Q).symm (g, f))) c p
            = bundleEquiv c.degreeBits (fun kj => g (sel kj)) := by
        intro g
        rw [actual_digest_draw_is_draw_at_digests, hdigind f g (fun _ => b0), ← hdigdef,
          draw_at_digests_is_encoded Q c.degreeBits dig (fun kj => (sel kj).val)
            (fun k j => rfl)]
        unfold encodedDraw
        exact congrArg (bundleEquiv c.degreeBits) (funext fun kj => hg g f (sel kj))
      have hset : (Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
            InstalledRoundCommit.actualDigestDraw
              (hashOf Q ((frameSplit Q).symm (g, f))) c p ∈ E))
          = Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
              (fun kj => g (sel kj)) ∈ Finset.univ.filter
                (fun w : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block =>
                  bundleEquiv c.degreeBits w ∈ E)) := by
        apply Finset.ext
        intro g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdraw g]
      have hEcard : (Finset.univ.filter
          (fun w : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block =>
            bundleEquiv c.degreeBits w ∈ E)).card = E.card := by
        have h := WhirChallenge.equiv_event_card (bundleEquiv c.degreeBits) (fun w => w ∈ E)
        have h2 : (Finset.univ.filter
            (fun w : JointChallengeSpace.JointSpace c.degreeBits => w ∈ E)) = E := by
          apply Finset.ext
          intro w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [h2] at h
        exact h
      have hratio := restrict_ratio sel hselinj (Finset.univ.filter
        (fun w : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block =>
          bundleEquiv c.degreeBits w ∈ E))
      rw [restrictAt, hEcard, schedule_index_card] at hratio
      rw [hset]
      have hbpos : (0 : ℚ) < (Fintype.card Block : ℚ) := by exact_mod_cast block_card_pos
      have hpow : (0 : ℚ) < (Fintype.card Block : ℚ) ^ ((3 * c.degreeBits + 1) * 3) :=
        pow_pos hbpos _
      have heq : ((Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
            (fun kj => g (sel kj)) ∈ Finset.univ.filter
              (fun w : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block =>
                bundleEquiv c.degreeBits w ∈ E))).card : ℚ)
          = JointChallengeSpace.jointProbability c.degreeBits E
            * (Fintype.card (ChallengeHalf Q → Block) : ℚ) := by
        rw [JointChallengeSpace.jointProbability, joint_space_card_as_blocks,
          div_mul_eq_mul_div, eq_div_iff hpow.ne']
        exact hratio
      rw [heq]
      linarith
    · -- the schedule is not injective in this fibre: the whole fibre is in the bad event
      push_neg at hinj
      obtain ⟨g0, hg0⟩ := hinj
      have hall : ∀ g : ChallengeHalf Q → Block,
          ¬ Function.Injective (squeezeIndex (hashOf Q ((frameSplit Q).symm (g, f))) c p) := by
        intro g
        have hrw : squeezeIndex (hashOf Q ((frameSplit Q).symm (g, f))) c p
            = squeezeIndex (hashOf Q ((frameSplit Q).symm (g0, f))) c p := by
          simp only [squeezeIndex, hdigind f g g0]
        rw [hrw]
        exact hg0
      have hb : (Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
          ¬ Function.Injective
            (squeezeIndex (hashOf Q ((frameSplit Q).symm (g, f))) c p))) = Finset.univ := by
        apply Finset.ext
        intro g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact hall g
      rw [hb, Finset.card_univ]
      have hle : (Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
          InstalledRoundCommit.actualDigestDraw
            (hashOf Q ((frameSplit Q).symm (g, f))) c p ∈ E)).card
          ≤ Fintype.card (ChallengeHalf Q → Block) := by
        rw [← Finset.card_univ]
        exact Finset.card_filter_le _ _
      have hlec : ((Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
          InstalledRoundCommit.actualDigestDraw
            (hashOf Q ((frameSplit Q).symm (g, f))) c p ∈ E)).card : ℚ)
          ≤ (Fintype.card (ChallengeHalf Q → Block) : ℚ) := by exact_mod_cast hle
      have hjp := JointChallengeSpace.joint_probability_nonneg c.degreeBits E
      have hNnn : (0 : ℚ) ≤ (Fintype.card (ChallengeHalf Q → Block) : ℚ) := by positivity
      nlinarith [mul_nonneg hjp hNnn]
  -- FUBINI OVER THE FRAME FIBRES
  haveI : Nonempty (ChallengeHalf Q → Block) := ⟨fun _ => b0⟩
  haveI : Nonempty (FrameHalf Q → Block) := ⟨fun _ => b0⟩
  have hA : (runDrawEvent Q c p E).card
      = ∑ f : FrameHalf Q → Block, (Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
          InstalledRoundCommit.actualDigestDraw
            (hashOf Q ((frameSplit Q).symm (g, f))) c p ∈ E)).card := by
    have h1 : runDrawEvent Q c p E
        = Finset.univ.filter (fun T : OracleTable Q =>
            (fun z : (ChallengeHalf Q → Block) × (FrameHalf Q → Block) =>
              InstalledRoundCommit.actualDigestDraw
                (hashOf Q ((frameSplit Q).symm z)) c p ∈ E) (frameSplit Q T)) := by
      apply Finset.ext
      intro T
      simp only [runDrawEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_apply_apply]
    rw [h1, WhirChallenge.equiv_event_card (frameSplit Q)
        (fun z : (ChallengeHalf Q → Block) × (FrameHalf Q → Block) =>
          InstalledRoundCommit.actualDigestDraw (hashOf Q ((frameSplit Q).symm z)) c p ∈ E),
      Finset.card_filter, Fintype.sum_prod_type_right]
    simp only [Finset.card_filter]
  have hB : (scheduleNonInjectiveEvent Q c p).card
      = ∑ f : FrameHalf Q → Block, (Finset.univ.filter (fun g : ChallengeHalf Q → Block =>
          ¬ Function.Injective
            (squeezeIndex (hashOf Q ((frameSplit Q).symm (g, f))) c p))).card := by
    have h1 : scheduleNonInjectiveEvent Q c p
        = Finset.univ.filter (fun T : OracleTable Q =>
            (fun z : (ChallengeHalf Q → Block) × (FrameHalf Q → Block) =>
              ¬ Function.Injective
                (squeezeIndex (hashOf Q ((frameSplit Q).symm z)) c p)) (frameSplit Q T)) := by
      apply Finset.ext
      intro T
      simp only [scheduleNonInjectiveEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_apply_apply]
    rw [h1, WhirChallenge.equiv_event_card (frameSplit Q)
        (fun z : (ChallengeHalf Q → Block) × (FrameHalf Q → Block) =>
          ¬ Function.Injective (squeezeIndex (hashOf Q ((frameSplit Q).symm z)) c p)),
      Finset.card_filter, Fintype.sum_prod_type_right]
    simp only [Finset.card_filter]
  have htot : Fintype.card (OracleTable Q)
      = Fintype.card (ChallengeHalf Q → Block) * Fintype.card (FrameHalf Q → Block) := by
    rw [Fintype.card_congr (frameSplit Q), Fintype.card_prod]
  have hNpos : (0 : ℚ) < (Fintype.card (ChallengeHalf Q → Block) : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := ChallengeHalf Q → Block)
  have hMpos : (0 : ℚ) < (Fintype.card (FrameHalf Q → Block) : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := FrameHalf Q → Block)
  have hNM : (0 : ℚ) < (Fintype.card (ChallengeHalf Q → Block) : ℚ)
      * (Fintype.card (FrameHalf Q → Block) : ℚ) := mul_pos hNpos hMpos
  rw [oracleProbability, oracleProbability, hA, hB, htot]
  push_cast
  rw [div_le_iff hNM, add_mul, div_mul_cancel₀ _ hNM.ne']
  refine le_trans (Finset.sum_le_sum (fun f _ => hfibre f)) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- (8) **THE RUN-LEVEL BAD-EVENT BOUND.**  `run_draw_probability_le_fibrewise`
composed with the adopted `JointChallengeSpace.joint_union_bound`: the mass of the
run's own draw falling in the adopted `JointChallengeSpace.jointBadEvent` is at
most the adopted `ChallengeUnionBound.combinedBound` plus the mass of the
schedule-collision event.

The additive term is the LOCALIZED clash (`schedule_non_injective_is_clash`), not
the global `CommitmentOrder.TranscriptCollision`, which would make the bound
`≤ combinedBound + 1` and therefore empty for every `Q` -- see
`transcript_collision_is_a_tautology`.  NO BOUND ON THE CLASH TERM IS PROVED
HERE, and localizing does not by itself make it smaller than `1`: at the
frame-free `closureWitness` it IS `1` (`closure_witness_clash_term_one`), while
`informative_query_set_exists` exhibits a `Q` at which it is `< 1`.  Two steps
are missing before this is a number: the birthday/sequential count over the frame
fibres, and the adaptive prover, neither of which appears in this tree.  The
bound also inherits the adopted scope: it EXCLUDES the dominant WHIR/Merkle
events and is not the deployed system's soundness error. -/
theorem run_bad_draw_probability_le_fibrewise (Q : Finset Transcript.Bytes)
    (c : Verifier.Config) (p : Verifier.Proof) (hQ : QueryClosure Q c.degreeBits)
    (quotientDegree constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element)
    (hlogLen : logLane.length = c.degreeBits) (hgateLen : gateLane.length = c.degreeBits)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability Q (runDrawEvent Q c p
        (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane g
          (2 ^ c.degreeBits) coeffsOf))
      ≤ ChallengeUnionBound.combinedBound c.degreeBits quotientDegree c.degreeBits constraints
        + oracleProbability Q (scheduleNonInjectiveEvent Q c p) :=
  le_trans (run_draw_probability_le_fibrewise Q c p hQ _)
    (add_le_add_right (JointChallengeSpace.joint_union_bound c.degreeBits quotientDegree constraints
      logCompare gateCompare logLane gateLane g coeffsOf hlogLen hgateLen hlogDeg hgateDeg hclen) _)

/-! ## 8.1 WHAT THE ADDITIVE TERM ACTUALLY IS

Section 8 leaves `oracleProbability Q (scheduleNonInjectiveEvent Q c p)` unbounded.
This section says, honestly, what that term is at the query sets this module can
exhibit -- because without it the run-level bound is easy to misread.

(a) AT A FRAME-FREE `Q` THE TERM IS EXACTLY `1`.  `QueryClosure` constrains only
    CHALLENGE-shaped strings, so it forces no `Transcript.frame` into `Q` at all
    (`closure_has_frame_free_sub`: every closed `Q` has a closed frame-free
    subset).  On a `Q` containing no frame, EVERY table answers
    `OuterInitial.zeroDigest` at every frame, the congruence lemma
    `source_digest_congr` collapses all of the run's block digests to
    `OuterInitial.zeroDigest`, the schedule repeats an input as soon as
    `degreeBits >= 2`, and `scheduleNonInjectiveEvent Q c p` is the WHOLE table
    space (`non_injective_event_univ`, `clash_term_one`).  The witness produced by
    `query_closure_is_satisfiable` is exactly such a `Q`
    (`closure_witness_clash_term_one`), so AT THE MODULE'S OWN CLOSURE WITNESS the
    run-level bound reads `<= combinedBound + 1` and is derivable from
    `oracle_probability_le_one` alone (`run_bound_trivial_at_frame_free`).

(b) A QUERY SET AT WHICH THE TERM IS `< 1` EXISTS.  `sepHash` carries the state
    digest through every frame, except that a tag-`2` frame with an eight-byte
    payload -- the adopted round-index frame of
    `InstalledRoundCommit.roundFrames` -- is answered by the digest SPELLING that
    payload.  Every round of the run then commits to `idxDigest r`, and those are
    pairwise distinct, so `RoundDigestClash sepHash c p` is FALSE at every
    `degreeBits <= 13` with a chain of matching length (`sep_hash_no_clash` --
    this is also the sharper non-triviality witness that `RoundDigestClash` is
    refutable beyond `degreeBits <= 1`).  Answering `sepHash` on
    `goodSet c p` -- the closure witness TOGETHER WITH the run's own index and
    carry frames -- gives a `QueryClosure`-satisfying `Q` at which the additive
    term is `< 1` (`informative_query_set_exists`).

(c) NO SMALL BOUND ON THE TERM IS PROVED ANYWHERE HERE, and `< 1` is not a
    security statement.  Bounding it needs the birthday/sequential count over the
    frame fibres -- how many tables answer two of the run's pairwise distinct
    round frames alike -- which is not written down in this tree, and even that
    would leave the adaptive prover of header (ii) untouched.

(d) A `getD` REMARK.  `sourceDigest` reads the round chain through
    `((InstalledRoundCommit.actualChain thash c p).get? r).getD
    (InstalledRoundCommit.actualBase thash c p)`.  If the proof's coupled-round
    chain is at least two rounds SHORTER than `degreeBits`, two round indices fall
    back to the SAME base digest, so `RoundDigestClash` holds and the additive
    term is `1` for EVERY hash and every query set -- no property of the oracle
    can help.  `sep_hash_no_clash` and `informative_query_set_exists` therefore
    carry the length hypothesis `hlen`.
-/

/-- The hash that answers `OuterInitial.zeroDigest` everywhere: what a frame-free
query set looks like to the run's block digests, whatever the table says. -/
def zeroHash : Transcript.Hash := fun _ => OuterInitial.zeroDigest

theorem actual_base_zero_hash (c : Verifier.Config) (p : Verifier.Proof) :
    InstalledRoundCommit.actualBase zeroHash c p = OuterInitial.zeroDigest := rfl

theorem round_committed_zero_hash (s : Transcript.State) (i : Nat)
    (m : Verifier.CoupledMessage) :
    (OuterAdapter.roundCommitted zeroHash s i m.1 m.2).digest = OuterInitial.zeroDigest := rfl

theorem concrete_chain_zero_hash :
    ∀ (ms : List Verifier.CoupledMessage) (st : Transcript.State) (i : Nat)
      (x : Transcript.Digest),
      x ∈ InstalledRoundCommit.concreteChain zeroHash st i ms → x = OuterInitial.zeroDigest
  | [], _, _, _, h => absurd h (by simp [InstalledRoundCommit.concreteChain])
  | m :: ms, st, i, x, h => by
      simp only [InstalledRoundCommit.concreteChain, List.mem_cons] at h
      rcases h with rfl | h
      · exact round_committed_zero_hash st i m
      · exact concrete_chain_zero_hash ms _ (i + 1) x h

/-- (8.1) Under `zeroHash` every block digest of the run -- relation prefix and
every coupled round alike -- is `OuterInitial.zeroDigest`. -/
theorem source_digest_zero_hash (c : Verifier.Config) (p : Verifier.Proof)
    (k : JointChallengeSpace.Draw c.degreeBits) :
    sourceDigest zeroHash c p k = OuterInitial.zeroDigest := by
  cases k with
  | gateAlpha => exact actual_base_zero_hash c p
  | gateTau _ => exact actual_base_zero_hash c p
  | outerLog r =>
      simp only [sourceDigest]
      cases hget : (InstalledRoundCommit.actualChain zeroHash c p).get? r.val with
      | none => exact actual_base_zero_hash c p
      | some x =>
          simp only [Option.getD_some]
          rw [InstalledRoundCommit.actualChain] at hget
          exact concrete_chain_zero_hash _ _ _ x (List.get?_mem hget)
  | outerGate r =>
      simp only [sourceDigest]
      cases hget : (InstalledRoundCommit.actualChain zeroHash c p).get? r.val with
      | none => exact actual_base_zero_hash c p
      | some x =>
          simp only [Option.getD_some]
          rw [InstalledRoundCommit.actualChain] at hget
          exact concrete_chain_zero_hash _ _ _ x (List.get?_mem hget)

/-- **A QUERY SET CONTAINING NO `Transcript.frame` AT ALL.**  `QueryClosure` never
rules this out: it speaks only about `Transcript.challengeInput`. -/
def FrameFree (Q : Finset Transcript.Bytes) : Prop :=
  ∀ (dg : Transcript.Digest) (t : Transcript.Byte) (pl : Transcript.Bytes),
    Transcript.frame dg t pl ∉ Q

theorem frame_agreement_of_frame_free (Q : Finset Transcript.Bytes) (hQ : FrameFree Q)
    (T : OracleTable Q) : FrameAgreement (hashOf Q T) zeroHash := by
  intro dg t pl
  simp only [hashOf, hQ dg t pl, dif_neg, not_false_iff]
  rfl

/-- (8.1) On a frame-free `Q`, EVERY table gives the run the constant
`OuterInitial.zeroDigest` block digests. -/
theorem source_digest_of_frame_free (Q : Finset Transcript.Bytes) (hQ : FrameFree Q)
    (T : OracleTable Q) (c : Verifier.Config) (p : Verifier.Proof) :
    sourceDigest (hashOf Q T) c p = fun _ => OuterInitial.zeroDigest := by
  rw [source_digest_congr (frame_agreement_of_frame_free Q hQ T)]
  funext k
  exact source_digest_zero_hash c p k

/-- (8.1) Every table over a frame-free `Q` clashes, at `degreeBits >= 2`. -/
theorem clash_of_frame_free (Q : Finset Transcript.Bytes) (hQ : FrameFree Q)
    (T : OracleTable Q) (c : Verifier.Config) (p : Verifier.Proof) (h2 : 2 ≤ c.degreeBits) :
    RoundDigestClash (hashOf Q T) c p := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    simp at this
  · rw [source_digest_of_frame_free Q hQ T]

theorem not_injective_of_frame_free (Q : Finset Transcript.Bytes) (hQ : FrameFree Q)
    (T : OracleTable Q) (c : Verifier.Config) (p : Verifier.Proof) (h2 : 2 ≤ c.degreeBits) :
    ¬ Function.Injective (squeezeIndex (hashOf Q T) c p) := by
  intro hinj
  have heq : squeezeIndex (hashOf Q T) c p (JointChallengeSpace.Draw.outerLog ⟨0, by omega⟩, 0)
      = squeezeIndex (hashOf Q T) c p (JointChallengeSpace.Draw.outerLog ⟨1, by omega⟩, 0) := by
    simp only [squeezeIndex, scheduleIndex, squeezeInputAt, source_digest_of_frame_free Q hQ T,
      JointChallengeSpace.sourceCounter]
  have h := hinj heq
  have hlog := JointChallengeSpace.Draw.outerLog.inj (congrArg Prod.fst h)
  have hval := congrArg Fin.val hlog
  simp at hval

/-- (8.1) **THE NON-INJECTIVE EVENT IS THE WHOLE TABLE SPACE** on a frame-free
`Q`, at every `degreeBits >= 2`. -/
theorem non_injective_event_univ (Q : Finset Transcript.Bytes) (hQ : FrameFree Q)
    (c : Verifier.Config) (p : Verifier.Proof) (h2 : 2 ≤ c.degreeBits) :
    scheduleNonInjectiveEvent Q c p = Finset.univ := by
  apply Finset.ext
  intro T
  simp only [scheduleNonInjectiveEvent, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact not_injective_of_frame_free Q hQ T c p h2

/-- (8.1) **THE ADDITIVE TERM OF SECTION 8 IS `1`** on a frame-free `Q`, at every
`degreeBits >= 2`.  Localizing the clash predicate was NECESSARY -- with the
global `CommitmentOrder.TranscriptCollision` the term is `1` for every `Q`
whatsoever -- but it is not SUFFICIENT. -/
theorem clash_term_one (Q : Finset Transcript.Bytes) (hQ : FrameFree Q)
    (c : Verifier.Config) (p : Verifier.Proof) (h2 : 2 ≤ c.degreeBits) :
    oracleProbability Q (scheduleNonInjectiveEvent Q c p) = 1 := by
  rw [non_injective_event_univ Q hQ c p h2, oracleProbability, Finset.card_univ]
  exact div_self (oracle_card_cast_pos Q).ne'

theorem closure_witness_frame_free (d : Nat) : FrameFree (closureWitness d) := by
  intro dg t pl h
  rw [closureWitness, Set.Finite.mem_toFinset] at h
  obtain ⟨⟨e, n⟩, hz⟩ := h
  exact frame_ne_challenge_input dg e t pl n.val hz.symm

/-- (8.1) **AT THE MODULE'S OWN CLOSURE WITNESS THE ADDITIVE TERM IS `1`.**  The
`Q` produced by `query_closure_is_satisfiable` is frame-free, so
`run_draw_probability_le_fibrewise` instantiated at it says exactly
`<= jointProbability E + 1`. -/
theorem closure_witness_clash_term_one (c : Verifier.Config) (p : Verifier.Proof)
    (h2 : 2 ≤ c.degreeBits) :
    oracleProbability (closureWitness c.degreeBits)
      (scheduleNonInjectiveEvent (closureWitness c.degreeBits) c p) = 1 :=
  clash_term_one _ (closure_witness_frame_free _) c p h2

/-- (8.1) **`QueryClosure` CARRIES NO FRAME CONTENT.**  Every closed `Q` has a
closed FRAME-FREE subset, so the hypothesis of section 8 can never by itself force
the additive term below `1`. -/
theorem closure_has_frame_free_sub (Q : Finset Transcript.Bytes) (d : Nat)
    (hQ : QueryClosure Q d) :
    ∃ Q2 ⊆ Q, QueryClosure Q2 d ∧ FrameFree Q2 :=
  ⟨Q.filter ChallengeShaped, Finset.filter_subset _ _,
    fun e n hn => Finset.mem_filter.mpr ⟨hQ e n hn, challenge_input_shaped e n⟩,
    fun dg t pl h => frame_not_shaped dg t pl (Finset.mem_filter.mp h).2⟩

/-- (8.1) **AT A FRAME-FREE `Q` THE RUN-LEVEL BOUND IS `oracle_probability_le_one`.**
Same conclusion as `run_draw_probability_le_fibrewise`, with no fibration, no
`restrict_ratio` and no `QueryClosure`: the additive term has already swallowed
everything.  This is the disclosure that the run-level bound, TRUE and NOT vacuous
as a statement, is vacuous at the only query set sections 8 exhibited. -/
theorem run_bound_trivial_at_frame_free (Q : Finset Transcript.Bytes) (hQ : FrameFree Q)
    (c : Verifier.Config) (p : Verifier.Proof) (h2 : 2 ≤ c.degreeBits)
    (E : Finset (JointChallengeSpace.JointSpace c.degreeBits)) :
    oracleProbability Q (runDrawEvent Q c p E)
      ≤ JointChallengeSpace.jointProbability c.degreeBits E
        + oracleProbability Q (scheduleNonInjectiveEvent Q c p) := by
  rw [clash_term_one Q hQ c p h2]
  have hle := oracle_probability_le_one Q (runDrawEvent Q c p E)
  have hnn := JointChallengeSpace.joint_probability_nonneg c.degreeBits E
  linarith

/-! ### 8.2 A SEPARATING HASH, AND A QUERY SET AT WHICH THE TERM IS `< 1` -/

/-- The digest spelling `n` in eight little-endian bytes, zero-padded to `32`. -/
def idxDigest (n : Nat) : Transcript.Digest :=
  ⟨Transcript.le 8 n ++ List.replicate 24 0, by simp [Transcript.le_length]⟩

theorem idx_digest_injective (m n : Nat) (hm : m < 256 ^ 8) (hn : n < 256 ^ 8)
    (h : idxDigest m = idxDigest n) : m = n := by
  have hb := congrArg Transcript.Digest.bytes h
  simp only [idxDigest] at hb
  have hl : (Transcript.le 8 m).length = (Transcript.le 8 n).length := by
    simp [Transcript.le_length]
  exact Transcript.le_injective_bounded 8 m n hm hn (List.append_inj_left hb hl)

/-- The state digest of a frame-shaped string. -/
def frameState (q : Transcript.Bytes) : Option Transcript.Digest :=
  if h : ((q.drop Transcript.framePrefix.length).take 32).length = 32
    then some ⟨(q.drop Transcript.framePrefix.length).take 32, h⟩ else none

/-- The domain tag of a frame-shaped string. -/
def frameTag (q : Transcript.Bytes) : Option Transcript.Byte :=
  ((q.drop Transcript.framePrefix.length).drop 32).head?

/-- The payload of a frame-shaped string. -/
def framePayload (q : Transcript.Bytes) : Transcript.Bytes :=
  (((q.drop Transcript.framePrefix.length).drop 32).drop 1).drop 8

/-- **THE SEPARATING HASH.**  Carry the state digest through every frame; on a
tag-`2` frame with an eight-byte payload -- the adopted round-index frame of
`InstalledRoundCommit.roundFrames` -- answer the digest SPELLING that payload.
Everything that is not frame-shaped gets `OuterInitial.zeroDigest`.  This is a
DEFINITION used to refute `RoundDigestClash`; it is not a model of Keccak and no
claim is made that any deployed hash behaves like it. -/
def sepHash : Transcript.Hash := fun q =>
  match frameState q, frameTag q with
  | some dg, some t =>
      if t = 2 then
        (if h : (framePayload q).length = 8
          then ⟨framePayload q ++ List.replicate 24 0, by simp [h]⟩ else dg)
      else dg
  | _, _ => OuterInitial.zeroDigest

theorem frame_unfold (dg : Transcript.Digest) (t : Transcript.Byte) (pl : Transcript.Bytes) :
    Transcript.frame dg t pl
      = Transcript.framePrefix ++ (Transcript.digestBytes dg ++
          (t :: (Transcript.le 8 pl.length ++ pl))) := by
  simp only [Transcript.frame, List.append_assoc, List.cons_append, List.nil_append]

theorem frame_state_frame (dg : Transcript.Digest) (t : Transcript.Byte)
    (pl : Transcript.Bytes) : frameState (Transcript.frame dg t pl) = some dg := by
  have h32 : (Transcript.digestBytes dg).length = 32 := dg.length_eq
  simp only [frameState, frame_unfold, List.drop_left, List.take_left' h32]
  rw [dif_pos h32]
  rfl

theorem frame_tag_frame (dg : Transcript.Digest) (t : Transcript.Byte)
    (pl : Transcript.Bytes) : frameTag (Transcript.frame dg t pl) = some t := by
  have h32 : (Transcript.digestBytes dg).length = 32 := dg.length_eq
  simp only [frameTag, frame_unfold, List.drop_left, List.drop_left' h32, List.head?_cons]

theorem frame_payload_frame (dg : Transcript.Digest) (t : Transcript.Byte)
    (pl : Transcript.Bytes) : framePayload (Transcript.frame dg t pl) = pl := by
  have h32 : (Transcript.digestBytes dg).length = 32 := dg.length_eq
  have h8 : (Transcript.le 8 pl.length).length = 8 := Transcript.le_length 8 _
  simp only [framePayload, frame_unfold, List.drop_left, List.drop_left' h32,
    List.drop_succ_cons, List.drop_zero, List.drop_left' h8]

/-- (8.2) The round-index frame of round `i` is answered by `idxDigest i`, from
every incoming state. -/
theorem sep_hash_index (dg : Transcript.Digest) (i : Nat) :
    sepHash (Transcript.frame dg 2 (Transcript.le 8 i)) = idxDigest i := by
  have h8 : (Transcript.le 8 i).length = 8 := Transcript.le_length 8 i
  simp only [sepHash, frame_state_frame, frame_tag_frame, frame_payload_frame, if_true, h8,
    dif_pos]
  rfl

/-- (8.2) Every other frame carries its incoming state digest through unchanged. -/
theorem sep_hash_carry (dg : Transcript.Digest) (t : Transcript.Byte) (pl : Transcript.Bytes)
    (ht : t ≠ 2) : sepHash (Transcript.frame dg t pl) = dg := by
  simp only [sepHash, frame_state_frame, frame_tag_frame, if_neg ht]

/-- The four answers a hash must control for round `i` of the adopted
`InstalledRoundCommit.roundFrames` fold to come out as `idxDigest i`, whatever
the incoming state. -/
def RoundControlled (h : Transcript.Hash) (i : Nat) (m : Verifier.CoupledMessage) : Prop :=
  (∀ e : Transcript.Digest, h (Transcript.frame e 2 (Transcript.le 8 i)) = idxDigest i) ∧
  h (Transcript.frame (idxDigest i) 6 (OuterAdapter.encodedVec m.1)) = idxDigest i ∧
  h (Transcript.frame (idxDigest i) 6 (OuterAdapter.encodedVec m.2)) = idxDigest i ∧
  h (Transcript.frame (idxDigest i) 1
      (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3")) = idxDigest i

theorem sep_hash_controls (i : Nat) (m : Verifier.CoupledMessage) : RoundControlled sepHash i m :=
  ⟨fun e => sep_hash_index e i,
   sep_hash_carry _ _ _ (by decide),
   sep_hash_carry _ _ _ (by decide),
   sep_hash_carry _ _ _ (by decide)⟩

/-- (8.2) **A CONTROLLED ROUND COMMITS TO `idxDigest i`, FROM ANY STATE.** -/
theorem round_committed_controlled (h : Transcript.Hash) (i : Nat) (m : Verifier.CoupledMessage)
    (hc : RoundControlled h i m) (s : Transcript.State) :
    (OuterAdapter.roundCommitted h s i m.1 m.2).digest = idxDigest i := by
  obtain ⟨hidx, hlog, hgate, hchal⟩ := hc
  rw [InstalledRoundCommit.round_committed_is_the_frame_fold]
  simp only [InstalledRoundCommit.roundFrames, OuterInitial.absorbMessages, List.foldl_cons,
    List.foldl_nil, OuterInitial.absorbMessage, OuterInitial.domainMessage, Transcript.absorb]
  rw [hidx, hlog, hgate, hchal]

/-- (8.2) Round `r` of a chain whose rounds are all controlled has commit digest
`idxDigest (i + r)`. -/
theorem concrete_chain_controlled (h : Transcript.Hash) (ms : List Verifier.CoupledMessage)
    (st : Transcript.State) (i r : Nat) (hr : r < ms.length)
    (hc : RoundControlled h (i + r) (ms.get ⟨r, hr⟩)) :
    (InstalledRoundCommit.concreteChain h st i ms).get? r = some (idxDigest (i + r)) := by
  rw [InstalledRoundCommit.concrete_chain_get h ms st i r hr, round_committed_controlled h _ _ hc]

/-- (8.2) **`RoundDigestClash sepHash c p` IS FALSE AT EVERY ENVELOPED
`degreeBits`.**  The sharper non-triviality witness that
`round_digest_clash_needs_two_rounds` does not give: the localized predicate is
refutable at every `degreeBits <= 13`, not only at `degreeBits <= 1`, as soon as
the proof's coupled-round chain has the matching length.  `hlen` cannot be
dropped -- see (d) of section 8.1. -/
theorem sep_hash_no_clash (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : (p.logRounds.zip p.gateRounds).length = c.degreeBits) (hdb : c.degreeBits ≤ 13) :
    ¬ RoundDigestClash sepHash c p := by
  rintro ⟨r, s, hrs, heq⟩
  have hr : r.val < (p.logRounds.zip p.gateRounds).length := by rw [hlen]; exact r.isLt
  have hs : s.val < (p.logRounds.zip p.gateRounds).length := by rw [hlen]; exact s.isLt
  simp only [sourceDigest, InstalledRoundCommit.actualChain] at heq
  rw [concrete_chain_controlled sepHash _ _ 0 r.val hr (sep_hash_controls _ _),
    concrete_chain_controlled sepHash _ _ 0 s.val hs (sep_hash_controls _ _),
    Option.getD_some, Option.getD_some, Nat.zero_add, Nat.zero_add] at heq
  have hb : (256 : Nat) ^ 8 = Transcript.u64Limit := byte_limit
  have hval := idx_digest_injective r.val s.val
    (by rw [hb]; unfold Transcript.u64Limit; omega)
    (by rw [hb]; unfold Transcript.u64Limit; omega) heq
  exact hrs (Fin.ext hval)

/-- The table that answers `sepHash` on `Q`. -/
def sepTable (Q : Finset Transcript.Bytes) : OracleTable Q :=
  fun q => OuterChallenge.digestBlock (sepHash q.val)

theorem hash_of_sep_table (Q : Finset Transcript.Bytes) (q : Transcript.Bytes) (hq : q ∈ Q) :
    hashOf Q (sepTable Q) q = sepHash q := by
  simp only [hashOf, hq, dif_pos, sepTable, block_digest_digest_block]

/-- The round-index frames of round `i` at EVERY incoming digest: a finite set,
by the finiteness of `Transcript.Digest`, never enumerated. -/
noncomputable def indexQueries (i : Nat) : Finset Transcript.Bytes :=
  (Set.finite_range (fun e : Transcript.Digest =>
    Transcript.frame e 2 (Transcript.le 8 i))).toFinset

/-- The three carry frames of round `i`: its two coupled messages and its
challenge domain separator. -/
def carryQueries (i : Nat) (m : Verifier.CoupledMessage) : Finset Transcript.Bytes :=
  {Transcript.frame (idxDigest i) 6 (OuterAdapter.encodedVec m.1),
   Transcript.frame (idxDigest i) 6 (OuterAdapter.encodedVec m.2),
   Transcript.frame (idxDigest i) 1 (Transcript.ascii "outer-sumcheck-lockstep-challenges-v3")}

/-- **THE INFORMATIVE QUERY SET**: the closure witness of section 8 TOGETHER WITH
the run's own round-index and carry frames.  Finite, and never enumerated. -/
noncomputable def goodSet (c : Verifier.Config) (p : Verifier.Proof) :
    Finset Transcript.Bytes :=
  closureWitness c.degreeBits ∪
    (Finset.range (p.logRounds.zip p.gateRounds).length).biUnion
      (fun i => indexQueries i ∪
        carryQueries i (((p.logRounds.zip p.gateRounds).get? i).getD ([], [])))

theorem good_set_closed (c : Verifier.Config) (p : Verifier.Proof) :
    QueryClosure (goodSet c p) c.degreeBits :=
  fun e n hn => Finset.mem_union_left _ (closure_witness_closed c.degreeBits e n hn)

theorem good_set_controls (c : Verifier.Config) (p : Verifier.Proof) (r : Nat)
    (hr : r < (p.logRounds.zip p.gateRounds).length) :
    RoundControlled (hashOf (goodSet c p) (sepTable (goodSet c p))) r
      ((p.logRounds.zip p.gateRounds).get ⟨r, hr⟩) := by
  set ms := p.logRounds.zip p.gateRounds
  have hm : (ms.get? r).getD ([], []) = ms.get ⟨r, hr⟩ := by
    rw [List.get?_eq_get hr, Option.getD_some]
  have hmemU : ∀ q, q ∈ indexQueries r ∪ carryQueries r (ms.get ⟨r, hr⟩) →
      q ∈ goodSet c p := by
    intro q hq
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hr, ?_⟩)
    rw [hm]
    exact hq
  have hidx : ∀ e : Transcript.Digest,
      Transcript.frame e 2 (Transcript.le 8 r) ∈ goodSet c p := by
    intro e
    apply hmemU
    apply Finset.mem_union_left
    rw [indexQueries, Set.Finite.mem_toFinset]
    exact ⟨e, rfl⟩
  have hcar : ∀ q ∈ carryQueries r (ms.get ⟨r, hr⟩), q ∈ goodSet c p :=
    fun q hq => hmemU q (Finset.mem_union_right _ hq)
  obtain ⟨sidx, slog, sgate, schal⟩ := sep_hash_controls r (ms.get ⟨r, hr⟩)
  refine ⟨fun e => ?_, ?_, ?_, ?_⟩
  · rw [hash_of_sep_table _ _ (hidx e)]
    exact sidx e
  · rw [hash_of_sep_table _ _ (hcar _ (Finset.mem_insert_self _ _))]
    exact slog
  · rw [hash_of_sep_table _ _ (hcar _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))]
    exact sgate
  · rw [hash_of_sep_table _ _ (hcar _ (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))]
    exact schal

theorem good_table_no_clash (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : (p.logRounds.zip p.gateRounds).length = c.degreeBits) (hdb : c.degreeBits ≤ 13) :
    ¬ RoundDigestClash (hashOf (goodSet c p) (sepTable (goodSet c p))) c p := by
  rintro ⟨r, s, hrs, heq⟩
  have hr : r.val < (p.logRounds.zip p.gateRounds).length := by rw [hlen]; exact r.isLt
  have hs : s.val < (p.logRounds.zip p.gateRounds).length := by rw [hlen]; exact s.isLt
  simp only [sourceDigest, InstalledRoundCommit.actualChain] at heq
  rw [concrete_chain_controlled _ _ _ 0 r.val hr
      (by rw [Nat.zero_add]; exact good_set_controls c p r.val hr),
    concrete_chain_controlled _ _ _ 0 s.val hs
      (by rw [Nat.zero_add]; exact good_set_controls c p s.val hs),
    Option.getD_some, Option.getD_some, Nat.zero_add, Nat.zero_add] at heq
  have hb : (256 : Nat) ^ 8 = Transcript.u64Limit := byte_limit
  have hval := idx_digest_injective r.val s.val
    (by rw [hb]; unfold Transcript.u64Limit; omega)
    (by rw [hb]; unfold Transcript.u64Limit; omega) heq
  exact hrs (Fin.ext hval)

/-- (8.2) The `sepHash` table over `goodSet` has an injective schedule: one
concrete table OUTSIDE `scheduleNonInjectiveEvent`. -/
theorem good_table_injective (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : (p.logRounds.zip p.gateRounds).length = c.degreeBits) (hdb : c.degreeBits ≤ 13) :
    Function.Injective (squeezeIndex (hashOf (goodSet c p) (sepTable (goodSet c p))) c p) := by
  rcases squeeze_inputs_distinct_or_round_digest_clash _ c p hdb with hinj | hclash
  · exact hinj
  · exact absurd hclash (good_table_no_clash c p hlen hdb)

/-- (8.2) **THE ADDITIVE TERM IS `< 1` AT `goodSet`.**  So
`run_draw_probability_le_fibrewise` CAN say something -- at a query set that
answers the run's OWN frames, which `QueryClosure` alone never supplies.  NOTHING
HERE MAKES THE TERM SMALL: the gap between `< 1` and a birthday bound is the
count that is not carried out in this tree. -/
theorem good_set_clash_term_lt_one (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : (p.logRounds.zip p.gateRounds).length = c.degreeBits) (hdb : c.degreeBits ≤ 13) :
    oracleProbability (goodSet c p) (scheduleNonInjectiveEvent (goodSet c p) c p) < 1 := by
  classical
  have hnot : sepTable (goodSet c p) ∉ scheduleNonInjectiveEvent (goodSet c p) c p := by
    simp only [scheduleNonInjectiveEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact good_table_injective c p hlen hdb
  have hss : scheduleNonInjectiveEvent (goodSet c p) c p ⊂ Finset.univ :=
    Finset.ssubset_univ_iff.mpr (fun h => hnot (h ▸ Finset.mem_univ _))
  have hlt := Finset.card_lt_card hss
  rw [Finset.card_univ] at hlt
  rw [oracleProbability, div_lt_one (oracle_card_cast_pos _)]
  exact_mod_cast hlt

/-- (8.2) **A QUERY SET AT WHICH THE RUN-LEVEL BOUND IS NOT VACUOUS EXISTS.**  At
every `degreeBits <= 13`, for every proof whose coupled-round chain has the
matching length, there is a `Q` satisfying the `QueryClosure` hypothesis of
section 8 whose additive clash term is `< 1`.  Read it together with
`closure_witness_clash_term_one`: the term is `< 1` only for a `Q` that contains
the run's own frame inputs, and NO SMALL BOUND on it is proved here. -/
theorem informative_query_set_exists (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : (p.logRounds.zip p.gateRounds).length = c.degreeBits) (hdb : c.degreeBits ≤ 13) :
    ∃ Q : Finset Transcript.Bytes, QueryClosure Q c.degreeBits ∧
      oracleProbability Q (scheduleNonInjectiveEvent Q c p) < 1 :=
  ⟨goodSet c p, good_set_closed c p, good_set_clash_term_lt_one c p hlen hdb⟩

/-! ## 9. Example: the twelve oracle inputs of a one-round schedule

Small data only.  No digest space is enumerated and no `Fintype.card` is
evaluated; the only computation is on the twelve little-endian counters. -/

/-- The twelve scheduled squeezes of a `degreeBits = 1` run, in source order:
coupled round `0`'s log challenge (counters `0, 1, 2`), its gate challenge
(counters `3, 4, 5`), the gate alpha (counters `12, 13, 14`) and the single gate
tau coordinate (counters `15, 16, 17`). -/
def exampleSchedule (dig : JointChallengeSpace.Draw 1 → Transcript.Digest) :
    List Transcript.Bytes :=
  [scheduleIndex 1 dig (JointChallengeSpace.Draw.outerLog 0, 0),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.outerLog 0, 1),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.outerLog 0, 2),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.outerGate 0, 0),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.outerGate 0, 1),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.outerGate 0, 2),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.gateAlpha, 0),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.gateAlpha, 1),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.gateAlpha, 2),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.gateTau 0, 0),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.gateTau 0, 1),
   scheduleIndex 1 dig (JointChallengeSpace.Draw.gateTau 0, 2)]

/-- (6) **THE TWELVE INPUTS, WRITTEN OUT.**  Each is the adopted
`Transcript.challengeInput` of that draw's block digest at an explicit counter. -/
theorem example_twelve_inputs (dig : JointChallengeSpace.Draw 1 → Transcript.Digest) :
    exampleSchedule dig =
      [Transcript.challengeInput (dig (JointChallengeSpace.Draw.outerLog 0)) 0,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.outerLog 0)) 1,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.outerLog 0)) 2,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.outerGate 0)) 3,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.outerGate 0)) 4,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.outerGate 0)) 5,
       Transcript.challengeInput (dig JointChallengeSpace.Draw.gateAlpha) 12,
       Transcript.challengeInput (dig JointChallengeSpace.Draw.gateAlpha) 13,
       Transcript.challengeInput (dig JointChallengeSpace.Draw.gateAlpha) 14,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.gateTau 0)) 15,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.gateTau 0)) 16,
       Transcript.challengeInput (dig (JointChallengeSpace.Draw.gateTau 0)) 17] := rfl

/-- Distinctness of a whole schedule from the COUNTERS alone: when no two
scheduled squeezes share a counter, no block comparison is needed at all and the
adopted `Transcript.le_injective_bounded` separates the inputs by their eight
little-endian counter bytes. -/
theorem schedule_distinct_of_counters (d : Nat) (hdb : d ≤ 13)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest)
    (hc : ∀ (k k2 : JointChallengeSpace.Draw d) (j j2 : Fin 3),
      JointChallengeSpace.sourceCounter d k + j.val
        = JointChallengeSpace.sourceCounter d k2 + j2.val → k = k2 ∧ j = j2) :
    Function.Injective (scheduleIndex d dig) := by
  rintro ⟨k, j⟩ ⟨k2, j2⟩ h
  simp only [scheduleIndex, squeezeInputAt] at h
  obtain ⟨_, hcnt⟩ := challenge_input_injective _ _ _ _
    (source_counter_bound d hdb k j) (source_counter_bound d hdb k2 j2) h
  obtain ⟨hk, hj⟩ := hc k k2 j j2 hcnt
  rw [hk, hj]

/-- (6) **THE TWELVE COUNTERS OF A ONE-ROUND SCHEDULE ARE PAIRWISE DISTINCT.**
Decided on the twelve small numerals `0..5` and `12..17`; nothing is evaluated
over a digest space. -/
theorem example_one_round_counters_distinct :
    ∀ (k k2 : JointChallengeSpace.Draw 1) (j j2 : Fin 3),
      JointChallengeSpace.sourceCounter 1 k + j.val
        = JointChallengeSpace.sourceCounter 1 k2 + j2.val → k = k2 ∧ j = j2 := by decide

/-- (6) **THE ONE-ROUND SCHEDULE IS DISTINCT FOR AN ARBITRARY HASH.**  At
`degreeBits = 1` the twelve counters `0..5` and `12..17` are already pairwise
distinct, so the twelve oracle inputs differ by their little-endian counter bytes
alone: no block comparison, no collision alternative and no hypothesis on the
hash is needed.  For `degreeBits >= 2` this stops being true -- rounds `0` and
`1` share the counters `0..5` -- and the general
`squeeze_inputs_distinct_or_collision` has to separate them by their commit
digests, which is where the collision alternative appears. -/
theorem example_one_round_schedule_distinct
    (dig : JointChallengeSpace.Draw 1 → Transcript.Digest) :
    Function.Injective (scheduleIndex 1 dig) :=
  schedule_distinct_of_counters 1 (by omega) dig example_one_round_counters_distinct

end Audit.Wire3.RandomOracleSqueezes
