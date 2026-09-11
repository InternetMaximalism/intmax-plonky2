import Audit.Wire3.BirthdayClashBound
import Audit.Wire3.IndexPointZeroCheck
import Audit.Wire3.InstalledIndexSampler
import Audit.Wire3.RandomOracleSqueezes

/-!
# THE RANDOM-ORACLE LAW FOR THE INDEX LANES

## The gap this module addresses

`RandomOracleSqueezes` (adopted) and `BirthdayClashBound` (adopted) put the
JointSpace coordinates -- the block-`0` gate alpha / gate tau squeezes and the
`2 * degreeBits` outer round squeezes -- under an explicit random-oracle counting
law on `OracleTable Q`.  Both EXCLUDE the index lanes.  The index lanes are
`InstalledIndexSampler`'s `IndexSpace indexBits`: `2 * indexBits` digest-triple
coordinates squeezed from `InstalledIndexSampler.indexDigest thash st p.used` --
the digest after the eight claim frames are absorbed onto the post-rounds
snapshot `st` -- at the counters `3 i` (log lane) and `3 * indexBits + 3 i` (gate
lane).  `IndexPointZeroCheck`'s agreement events
(`log_index_agreement_mass_bound` / `gate_index_agreement_mass_bound`, each at
most `ChallengeUnionBound.tauTerm indexBits`) live on that space, and
`SoundnessAssembly`'s `hidx` consumes a point of it.

Before this module the two spaces were DIFFERENT ABSTRACT SPACES with two
different ideal laws (`JointChallengeSpace.jointProbability` and
`IndexPointZeroCheck.indexProbability`), which is why `SoundnessAssembly` could
add their bad-event masses only as an ARITHMETIC sum of masses on unrelated
spaces, never as a mass of a union under one law.  Under the random-oracle model
they are both functions of the SAME table `T`, and that is what is written down
here.

## What is proved

1. THE INDEX SHAPE.  `prefixRoundIndexShape c s ms u d` is the adopted
   twenty-two-frame relation prefix, then the `5 d` round frames, then the EIGHT
   adopted `InstalledIndexSampler.claimFrames u`.  `index_state_is_index_digest`:
   the chain's digest after `22 + 5 d + 8` stages IS
   `InstalledIndexSampler.indexDigest (hashOf ... T) st p.used`, for any snapshot
   `st` whose digest is the chain's digest after `22 + 5 d` stages.  Proved from
   the adopted `BirthdayClashBound.fold_digest_absorb` and
   `InstalledIndexSampler.claims_committed_is_the_frame_fold`; no new
   serialization.
2. INDEX SQUEEZE UNIFORMITY, CONDITIONED ON THE INDEX DIGEST.
   `index_counters_distinct` (the `2 * indexBits * 3` counters are pairwise
   distinct), `index_pushforward_uniform` and
   `index_draw_at_fixed_digest_is_uniform`: at a FIXED index digest `e`, the
   pushforward of the uniform law on `OracleTable Q` along the adopted
   `InstalledIndexSampler.actualIndexDraw (hashOf Q T) e indexBits` is EXACTLY
   the adopted `IndexPointZeroCheck.indexProbability indexBits`.  The bad-event
   corollary `index_bad_draw_at_fixed_digest_le` is `2 * tauTerm indexBits`,
   under the same `CellsDifferOnCube` GUARD `SoundnessAssembly.indexBadEvent`
   uses.
3. ONE LAW FOR BOTH FAMILIES.  `combined_schedule_injective`: the joint schedule
   and the index schedule are pairwise distinct oracle inputs exactly when the
   index digest `e` differs from every block digest `dig k` -- the counters alone
   do NOT separate them, because the index counters run `0 .. 6 * indexBits - 1`
   and a coupled round's counters are `0 .. 5`
   (`index_counters_meet_round_counters` exhibits the numeric overlap).
   `joint_and_index_bad_at_fixed_digests_le` is then the union's mass under the
   ONE oracle law: at most `combinedBound + 2 * tauTerm indexBits`.  This is the
   FIXED-DIGESTS version; see (iv) for what the run-level version still needs.
   The CROSS-distinctness carried by `hne` (and hence by `hcomb`) is NOT
   load-bearing in any probability statement of this module -- the union bound
   consumes only the two families' separate injectivities, as the docstring of
   `joint_and_index_bad_at_fixed_digests_le` says -- it is used only on the
   satisfiability route, where `combined_schedule_injective` builds `hcomb` from
   it.
4. THE BIRTHDAY BOUND FOR THE EXTENDED CHAIN.  `extendedDigestClashEvent` is
   "two coupled rounds clash, OR the index digest equals a round digest, OR the
   index digest equals the relation-prefix digest", and
   `extended_digest_clash_mass_le` bounds it by
   `(22 + 5 d + 8)(22 + 5 d + 9) / 2 / |Block|` -- `4560 / |Block|` at the
   envelope's `degreeBits = 13`.  The eight claim frames are causal and fresh for
   exactly the reason the round frames are: they carry the fixed separators, the
   tag-`6` cell frames and the used-claims payload, and the adopted
   `BirthdayClashBound.frame_chain_causal` needs no hypothesis on the shape.
   `extended_clash_index_disjuncts_are_run_digests` then reads the second and
   third disjuncts back as statements about the adopted
   `InstalledIndexSampler.indexDigest`, the adopted `OuterAdapter.roundCommitted`
   digests and the adopted `OuterInitial.derive` digest, so the disjuncts are not
   merely stage indices of an abstract chain.

## HONESTY

(i) WHICH IDENTIFICATIONS ARE CHAIN-MODEL AND WHICH ARE RUN-LEVEL.

  * RUN-LEVEL (no model step): `index_state_is_index_digest`'s right-hand side is
    the adopted `InstalledIndexSampler.indexDigest`, and the adopted
    `InstalledIndexSampler.sampled_indices_absorb_used_claims` /
    `index_points_are_space_coordinates` say the installed sampler's two lanes
    ARE the `reduceTriple` reductions of `actualIndexDraw` at that digest.  The
    counters are the adopted `InstalledIndexSampler.indexCounter`.
  * BRIDGED HERE (section 1.3): the adopted
    `BirthdayClashBound.prefix_state_is_derive_digest` and
    `prefix_round_chain_step` are stated on the adopted `prefixRoundShape` chain,
    NOT on the extended `prefixRoundIndexShape` chain this module's events and
    hypotheses mention.  `frame_state_agree_below` (two shapes agreeing below `n`
    have the same stage-`n` digest) and `extended_prefix_agrees` (the two chains
    agree on every stage `k ≤ 22 + 5 d`) transport them:
    `extended_stage22_is_derive` identifies stage `22` of the EXTENDED chain with
    the adopted `OuterInitial.derive` digest, and `extended_round_stage_five`
    identifies stage `22 + 5 i + 5`, `i < d`, with the adopted
    `OuterAdapter.roundCommitted` fold of round `i`.  So the identifications the
    header claims are theorems of this module, not a reader's inference.
  * CHAIN-MODEL: the hypothesis `hst` of `index_state_is_index_digest` --
    "the post-rounds snapshot's digest is the chain's digest after `22 + 5 d`
    stages" -- is ASSUMED, not derived here.  What nobody has written down is the
    LIST BOOKKEEPING that stage `22 + 5 d` is position `d` of
    `InstalledRoundCommit.concreteChain`, i.e. the `concreteFinal` snapshot
    `SoundnessAssembly.actualIndexDraw` uses.  That threading is deliberately
    left to a separate module; this one takes it as the explicit hypothesis
    `hst`, which is satisfiable (`index_state_hypothesis_is_satisfiable` takes
    the chain's own state).
  * CHAIN-MODEL: `extendedDigestClashEvent` is an event about the chain's stage
    digests, not syntactically about `RandomOracleSqueezes.RoundDigestClash`.
    This is the same residue `BirthdayClashBound`'s own section 9 discloses.

(ii) THE MODEL IS THE RANDOM ORACLE, NOT KECCAK.  `OracleTable Q` is a uniform
table on a finite query set.  Nothing here is a statement about the deployed
hash; a real permutation is not a random function and no reduction is claimed.

(iii) THE PROVER IS FIXED.  The shapes `prefixRoundShape` / the claim frames are
functions of the config, the statement, the coupled messages and `p.used`, all
fixed BEFORE the table is sampled.  An adaptive prover choosing its messages
after seeing oracle answers is NOT modelled; this is the same non-adaptivity the
adopted `splitTable` needs.

(iv) SECTION 3 IS THE FIXED-DIGESTS VERSION.  `dig` and `e` are quantified
OUTSIDE the law.  The run-level version would replace them by
`sourceDigest (hashOf Q T) c p` and `indexDigest (hashOf Q T) st p.used`, which
are functions OF THE TABLE, and would need the frame-fibre Fubini of the adopted
`RandomOracleSqueezes.run_bad_draw_probability_le_fibrewise` run once for the
PAIR of families -- both draws are functions of the challenge half of the table
inside one frame fibre, and `source_digest_congr` plus
`index_state_is_index_digest` make both digests constant on a fibre.  What is
NOT delivered here is that Fubini for the union; what IS delivered is the
statement it would land on, plus the additive clash term it would need
(section 4).

(v) WHAT THE INDEX LANES ARE FOR.  Residue R3 -- the ORDER in which the used
claims are absorbed relative to the index squeeze -- and the
`IndexPointZeroCheck` agreement events.  Those two now sit under the SAME
counting law as the gate and outer lanes, which is the entire content of this
module.

(vi) SCOPE.  WHIR and Merkle events are EXCLUDED, exactly as in the adopted
`ChallengeUnionBound.combinedBound`.  `combinedBound + 2 * tauTerm indexBits` is
NOT the deployed system's soundness error; the dominant terms are elsewhere.  The
design point the envelope targets is about one hundred bits.  No digit string
one-two-five is claimed for it.

(vii) SATISFIABILITY.  Every hypothesis INTRODUCED BY THIS MODULE has an
exhibited witness at a closed instance `indexBits ≤ 8`, `degreeBits ≤ 13`:
`index_schedule_hypotheses_are_satisfiable`,
`separated_digest_hypotheses_are_satisfiable`,
`length_budget_is_satisfiable_at_the_envelope`,
`index_state_hypothesis_is_satisfiable`, and
`constant_table_in_extended_clash_event` (the clash event is not empty either).
Two families of hypotheses are INHERITED, not introduced, and are discharged
where they were introduced, not here: `hpre` -- the twenty-two relation-prefix
payload budget -- is the adopted `BirthdayClashBound` hypothesis, carried through
`prefix_round_index_shape_payload_bound` and
`length_budget_is_satisfiable_at_the_envelope` unchanged (its round twin `hround`
IS discharged, by `envelope_round_budget_is_the_adopted_one`); and the five lane
hypotheses of `joint_and_index_bad_at_fixed_digests_le` -- `hlogLen`, `hgateLen`,
`hlogDeg`, `hgateDeg`, `hclen` -- are the adopted `RandomOracleSqueezes` /
`ChallengeUnionBound` ones, satisfied by the adopted `trivialLane` witnesses.
`joint_and_index_bad_at_the_envelope_closed` is the resulting FULLY CLOSED
envelope instance: `degreeBits = 13`, `indexBits = 8`, the adopted
`blockDigests 13` and this module's `separatedIndexDigest`, the adopted
`trivialLane x` lanes, empty coefficient lists and empty cell lists, with no
remaining hypothesis at all -- only the free field element `x` naming the lanes.
-/

namespace Audit.Wire3.IndexLanesOracle

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound

/-! ## 1. The index shape: the eight claim frames after the round frames -/

/-- The shape of the `k`-th of the adopted `InstalledIndexSampler.claimFrames`:
the claims domain separator, the five used-claim cells, the explicitly empty
sixth cell, the index domain separator.  Past the eighth frame this is the
adopted `BirthdayClashBound.messageShape` default, which is never read. -/
def claimShapeAt (u : Verifier.UsedClaims) (k : Nat) : Transcript.Byte × Transcript.Bytes :=
  messageShape (InstalledIndexSampler.claimFrames u) k

/-- **THE WHOLE RUN'S SHAPE, THROUGH THE INDEX SQUEEZE.**  The adopted
`BirthdayClashBound.prefixRoundShape` -- twenty-two relation-prefix frames and
then five frames per coupled round -- extended by the EIGHT claim frames.  The
chain therefore has `22 + 5 d + 8` stages, and its last state digest is the
digest the two index lanes are squeezed from. -/
def prefixRoundIndexShape (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d : Nat) (k : Nat) :
    Transcript.Byte × Transcript.Bytes :=
  if k < 22 + 5 * d then prefixRoundShape c s ms k
  else claimShapeAt u (k - (22 + 5 * d))

theorem prefix_round_index_shape_early (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d k : Nat)
    (hk : k < 22 + 5 * d) :
    prefixRoundIndexShape c s ms u d k = prefixRoundShape c s ms k :=
  if_pos hk

theorem prefix_round_index_shape_claim (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d k : Nat) :
    prefixRoundIndexShape c s ms u d (22 + 5 * d + k) = claimShapeAt u k := by
  rw [prefixRoundIndexShape, if_neg (by omega),
    show 22 + 5 * d + k - (22 + 5 * d) = k from by omega]

/-! ### 1.1 The length budget of the eight claim frames -/

theorem claim_shape_zero (u : Verifier.UsedClaims) :
    (claimShapeAt u 0).2 = Transcript.ascii "pcs-constituent-claims-v3" := rfl

theorem claim_shape_one (u : Verifier.UsedClaims) :
    (claimShapeAt u 1).2 = OuterAdapter.encodedVec u.logPreprocessed := rfl

theorem claim_shape_two (u : Verifier.UsedClaims) :
    (claimShapeAt u 2).2 = OuterAdapter.encodedVec u.logWitness := rfl

theorem claim_shape_three (u : Verifier.UsedClaims) :
    (claimShapeAt u 3).2 = OuterAdapter.encodedVec u.logNormInverse := rfl

theorem claim_shape_four (u : Verifier.UsedClaims) :
    (claimShapeAt u 4).2 = OuterAdapter.encodedVec u.gatePreprocessed := rfl

theorem claim_shape_five (u : Verifier.UsedClaims) :
    (claimShapeAt u 5).2 = OuterAdapter.encodedVec u.gateWitness := rfl

theorem claim_shape_six (u : Verifier.UsedClaims) :
    (claimShapeAt u 6).2 = OuterAdapter.encodedVec [] := rfl

theorem claim_shape_seven (u : Verifier.UsedClaims) :
    (claimShapeAt u 7).2 = Transcript.ascii "pcs-constituent-index-v3" := rfl

theorem claim_shape_past_end (u : Verifier.UsedClaims) (n : Nat) :
    (claimShapeAt u (n + 8)).2 = [] := rfl

/-- (1) **THE EIGHT FRAME TAGS**, which the payload lemmas above do not record:
a domain separator is tag `1`, a used-claim cell vector is tag `6`, so the eight
claim frames run `1, 6, 6, 6, 6, 6, 6, 1`.  The adopted
`InstalledIndexSampler.claimFrames` spelling, read off definitionally. -/
theorem claim_shape_tags (u : Verifier.UsedClaims) :
    ((claimShapeAt u 0).1, (claimShapeAt u 1).1, (claimShapeAt u 2).1, (claimShapeAt u 3).1,
        (claimShapeAt u 4).1, (claimShapeAt u 5).1, (claimShapeAt u 6).1, (claimShapeAt u 7).1)
      = ((1 : Transcript.Byte), (6 : Transcript.Byte), (6 : Transcript.Byte),
        (6 : Transcript.Byte), (6 : Transcript.Byte), (6 : Transcript.Byte),
        (6 : Transcript.Byte), (1 : Transcript.Byte)) := rfl

theorem claims_separator_length :
    (Transcript.ascii "pcs-constituent-claims-v3").length = 25 := by decide

theorem index_separator_length :
    (Transcript.ascii "pcs-constituent-index-v3").length = 24 := by decide

/-- (1) **THE CLAIM FRAMES FIT IN THE BUDGET.**  A cell frame is
`61 + 8 + 24 * (cell length)` bytes by the adopted
`OuterAdapter.encoded_vector_length`; the two domain separators are `86` and `85`
bytes.  So a width bound `W` on the five used-claim vectors gives the budget
`69 + 24 W`. -/
theorem claim_shape_payload_bound (L W : Nat) (u : Verifier.UsedClaims)
    (h1 : u.logPreprocessed.length ≤ W) (h2 : u.logWitness.length ≤ W)
    (h3 : u.logNormInverse.length ≤ W) (h4 : u.gatePreprocessed.length ≤ W)
    (h5 : u.gateWitness.length ≤ W) (hW : 69 + 24 * W ≤ L) (hdom : 86 ≤ L) :
    ∀ k, 61 + (claimShapeAt u k).2.length ≤ L := by
  intro k
  match k with
  | 0 => rw [claim_shape_zero, claims_separator_length]; omega
  | 1 =>
      rw [claim_shape_one, OuterAdapter.encoded_vector_length]
      have : 24 * u.logPreprocessed.length ≤ 24 * W := Nat.mul_le_mul_left 24 h1
      omega
  | 2 =>
      rw [claim_shape_two, OuterAdapter.encoded_vector_length]
      have : 24 * u.logWitness.length ≤ 24 * W := Nat.mul_le_mul_left 24 h2
      omega
  | 3 =>
      rw [claim_shape_three, OuterAdapter.encoded_vector_length]
      have : 24 * u.logNormInverse.length ≤ 24 * W := Nat.mul_le_mul_left 24 h3
      omega
  | 4 =>
      rw [claim_shape_four, OuterAdapter.encoded_vector_length]
      have : 24 * u.gatePreprocessed.length ≤ 24 * W := Nat.mul_le_mul_left 24 h4
      omega
  | 5 =>
      rw [claim_shape_five, OuterAdapter.encoded_vector_length]
      have : 24 * u.gateWitness.length ≤ 24 * W := Nat.mul_le_mul_left 24 h5
      omega
  | 6 => rw [claim_shape_six, OuterAdapter.encoded_vector_length]; simp only [List.length_nil]; omega
  | 7 => rw [claim_shape_seven, index_separator_length]; omega
  | n + 8 => rw [claim_shape_past_end]; simp only [List.length_nil]; omega

/-- (1) **THE LENGTH BUDGET FOR THE WHOLE EXTENDED CHAIN.**  The adopted
`BirthdayClashBound.prefix_round_shape_payload_bound` for the first `22 + 5 d`
stages, and `claim_shape_payload_bound` for the last eight. -/
theorem prefix_round_index_shape_payload_bound (L W : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims)
    (d : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L)
    (hround : ∀ k, 61 + (roundShape ms k).2.length ≤ L)
    (h1 : u.logPreprocessed.length ≤ W) (h2 : u.logWitness.length ≤ W)
    (h3 : u.logNormInverse.length ≤ W) (h4 : u.gatePreprocessed.length ≤ W)
    (h5 : u.gateWitness.length ≤ W) (hW : 69 + 24 * W ≤ L) (hdom : 86 ≤ L) :
    ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L := by
  intro k
  by_cases hk : k < 22 + 5 * d
  · rw [prefix_round_index_shape_early c s ms u d k hk]
    exact prefix_round_shape_payload_bound L c s ms hpre hround k
  · rw [prefixRoundIndexShape, if_neg hk]
    exact claim_shape_payload_bound L W u h1 h2 h3 h4 h5 hW hdom (k - (22 + 5 * d))

/-! ### 1.2 The chain's last state digest IS the adopted index digest -/

theorem absorb_messages_cons (thash : Transcript.Hash) (st : Transcript.State)
    (m : OuterInitial.Message) (rest : List OuterInitial.Message) :
    OuterInitial.absorbMessages thash st (m :: rest)
      = OuterInitial.absorbMessages thash (OuterInitial.absorbMessage thash st m) rest := rfl

/-- The adopted `Transcript.absorb` reads only the state's DIGEST, so a fold over
a NON-EMPTY message list does not see the incoming counter. -/
theorem absorb_messages_digest_congr (thash : Transcript.Hash) (st tt : Transcript.State)
    (m : OuterInitial.Message) (rest : List OuterInitial.Message)
    (hd : st.digest = tt.digest) :
    OuterInitial.absorbMessages thash st (m :: rest)
      = OuterInitial.absorbMessages thash tt (m :: rest) := by
  rw [absorb_messages_cons, absorb_messages_cons]
  have hstep : OuterInitial.absorbMessage thash st m = OuterInitial.absorbMessage thash tt m := by
    simp only [OuterInitial.absorbMessage, Transcript.absorb, hd]
  rw [hstep]

/-- (1) The adopted `InstalledIndexSampler.indexDigest` depends on the snapshot
only through its digest. -/
theorem index_digest_congr (thash : Transcript.Hash) (st tt : Transcript.State)
    (u : Verifier.UsedClaims) (hd : st.digest = tt.digest) :
    InstalledIndexSampler.indexDigest thash st u
      = InstalledIndexSampler.indexDigest thash tt u := by
  show (OuterAdapter.claimsCommitted thash st u).digest
    = (OuterAdapter.claimsCommitted thash tt u).digest
  rw [InstalledIndexSampler.claims_committed_is_the_frame_fold,
    InstalledIndexSampler.claims_committed_is_the_frame_fold]
  exact congrArg Transcript.State.digest
    (absorb_messages_digest_congr thash st tt _ _ hd)

/-- (1) **THE EXTENDED CHAIN'S LAST DIGEST IS THE ADOPTED INDEX DIGEST.**  After
`22 + 5 d + 8` stages the chain from `OuterInitial.zeroDigest` stands exactly at
`InstalledIndexSampler.indexDigest`, on the post-rounds snapshot `st`.

The hypothesis `hst` is the CHAIN-MODEL identification of HONESTY (i): the
snapshot's digest is the chain's digest after `22 + 5 d` stages.  Everything else
is the adopted `BirthdayClashBound.fold_digest_absorb` applied to the adopted
eight-element `InstalledIndexSampler.claimFrames`, so nothing is re-serialized. -/
theorem index_state_is_index_digest (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d : Nat)
    (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) (st : Transcript.State)
    (hst : st.digest =
      frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
        (22 + 5 * d) T) :
    frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
        (22 + 5 * d + 8) T
      = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st u := by
  have hshift : ∀ j, j < (InstalledIndexSampler.claimFrames u).length →
      (fun j2 => prefixRoundIndexShape c s ms u d (22 + 5 * d + j2)) j
        = messageShape (InstalledIndexSampler.claimFrames u) j := by
    intro j _
    exact prefix_round_index_shape_claim c s ms u d j
  have hcf : (InstalledIndexSampler.claimFrames u).length = 8 := rfl
  have habs := fold_digest_absorb (hashOf (boundedQueries L) T)
    (InstalledIndexSampler.claimFrames u)
    (foldDigest (hashOf (boundedQueries L) T) OuterInitial.zeroDigest
      (prefixRoundIndexShape c s ms u d) (22 + 5 * d))
    (fun j2 => prefixRoundIndexShape c s ms u d (22 + 5 * d + j2)) hshift
  rw [hcf] at habs
  have hbase : (⟨foldDigest (hashOf (boundedQueries L) T) OuterInitial.zeroDigest
      (prefixRoundIndexShape c s ms u d) (22 + 5 * d), 0⟩ : Transcript.State).digest
      = st.digest := by
    rw [hst, frame_state_is_fold]
  rw [frame_state_is_fold,
    fold_digest_add (hashOf (boundedQueries L) T) OuterInitial.zeroDigest
      (prefixRoundIndexShape c s ms u d) (22 + 5 * d) 8, habs]
  refine Eq.trans (congrArg Transcript.State.digest
    (absorb_messages_digest_congr (hashOf (boundedQueries L) T) _ st _ _ hbase)) ?_
  exact (congrArg Transcript.State.digest
    (InstalledIndexSampler.claims_committed_is_the_frame_fold
      (hashOf (boundedQueries L) T) st u)).symm

/-- (1) The chain-model hypothesis `hst` is satisfiable: the chain's own state at
stage `22 + 5 d` is a snapshot with that digest. -/
theorem index_state_hypothesis_is_satisfiable (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims)
    (d : Nat) (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) :
    ∃ st : Transcript.State,
      st.digest = frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
        (22 + 5 * d) T ∧
      frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
          (22 + 5 * d + 8) T
        = InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st u :=
  ⟨⟨frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
      (22 + 5 * d) T, 0⟩, rfl,
    index_state_is_index_digest L c s ms u d hlen T _ rfl⟩

/-! ### 1.3 The bridge to the adopted stage identifications

The adopted `BirthdayClashBound.prefix_state_is_derive_digest` and
`prefix_round_chain_step` are stated on the adopted `prefixRoundShape` chain.
Every event and hypothesis of this module lives on the EXTENDED
`prefixRoundIndexShape` chain, so those two lemmas do not apply to them as they
stand.  The three lemmas below transport them: the two chains agree on every
stage `k ≤ 22 + 5 d`, which is exactly the range the identifications need. -/

/-- (1) **TWO SHAPES AGREEING BELOW `n` HAVE THE SAME STAGE-`n` DIGEST.**  The
adopted `frameState` reads the shape only at the stages it has already passed, so
agreement of the two shapes on `k < n` forces agreement of the two chains at
every `k ≤ n`.  Stated for arbitrary shapes; each side carries its own length
budget, and the budgets need not agree. -/
theorem frame_state_agree_below (L : Nat) (e0 : Transcript.Digest)
    (sh1 sh2 : Nat → Transcript.Byte × Transcript.Bytes)
    (h1 : ∀ k, 61 + (sh1 k).2.length ≤ L) (h2 : ∀ k, 61 + (sh2 k).2.length ≤ L)
    (n : Nat) (hagree : ∀ k, k < n → sh1 k = sh2 k) (T : OracleTable (boundedQueries L)) :
    ∀ k, k ≤ n → frameState L e0 sh1 h1 k T = frameState L e0 sh2 h2 k T := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hs := hagree m (by omega)
      have hst := ih (by omega)
      show blockDigest (T ⟨Transcript.frame (frameState L e0 sh1 h1 m T) (sh1 m).1 (sh1 m).2, _⟩)
        = blockDigest (T ⟨Transcript.frame (frameState L e0 sh2 h2 m T) (sh2 m).1 (sh2 m).2, _⟩)
      congr 1
      apply congrArg
      apply Subtype.ext
      show Transcript.frame (frameState L e0 sh1 h1 m T) (sh1 m).1 (sh1 m).2
        = Transcript.frame (frameState L e0 sh2 h2 m T) (sh2 m).1 (sh2 m).2
      rw [hst, hs]

/-- (1) **THE EXTENDED CHAIN IS THE ADOPTED CHAIN BELOW STAGE `22 + 5 d`.**  The
eight claim frames are appended AFTER stage `22 + 5 d`, so
`prefix_round_index_shape_early` and `frame_state_agree_below` give equality of
the two chains at every stage up to and including `22 + 5 d`. -/
theorem extended_prefix_agrees (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d : Nat)
    (hlenI : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) (k : Nat) (hk : k ≤ 22 + 5 * d) :
    frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI k T
      = frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlenP k T :=
  frame_state_agree_below L OuterInitial.zeroDigest _ _ hlenI hlenP (22 + 5 * d)
    (fun j hj => prefix_round_index_shape_early c s ms u d j hj) T k hk

/-- (1) **STAGE `22` OF THE EXTENDED CHAIN IS THE ADOPTED DERIVE DIGEST.**  This
is the identification the THIRD disjunct of `extendedDigestClashEvent` is about;
before this lemma the adopted `BirthdayClashBound.prefix_state_is_derive_digest`
could not be applied to it. -/
theorem extended_stage22_is_derive (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d : Nat)
    (hlenI : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) :
    frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI 22 T
      = (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state.digest := by
  rw [extended_prefix_agrees L c s ms u d hlenI hlenP T 22 (by omega),
    prefix_state_is_derive_digest]

/-- (1) **STAGE `22 + 5 i + 5` OF THE EXTENDED CHAIN IS THE ADOPTED
`OuterAdapter.roundCommitted` DIGEST OF ROUND `i`**, for every `i < d`.  This is
the identification the SECOND disjunct of `extendedDigestClashEvent` is about.
The adopted `prefix_round_chain_step` supplies the five-frame fold and the
adopted `BirthdayClashBound.round_commit_is_stage_five` names it as the adopted
round commit. -/
theorem extended_round_stage_five (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d : Nat)
    (hlenI : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) (i : Nat) (hi : i < d) :
    frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI
        (22 + (5 * i + 5)) T
      = (OuterAdapter.roundCommitted (hashOf (boundedQueries L) T)
          ⟨frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI
            (22 + 5 * i) T, 0⟩ i ((ms.get? i).getD ([], [])).1
          ((ms.get? i).getD ([], [])).2).digest := by
  rw [extended_prefix_agrees L c s ms u d hlenI hlenP T (22 + (5 * i + 5)) (by omega),
    extended_prefix_agrees L c s ms u d hlenI hlenP T (22 + 5 * i) (by omega),
    prefix_round_chain_step]
  exact (round_commit_is_stage_five (hashOf (boundedQueries L) T)
    ⟨frameState L OuterInitial.zeroDigest (prefixRoundShape c s ms) hlenP (22 + 5 * i) T, 0⟩
    i ((ms.get? i).getD ([], []))).symm

/-- (1) **THE SECOND AND THIRD DISJUNCTS OF `extendedDigestClashEvent` ARE ABOUT
THE RUN'S OWN DIGESTS.**  Under the same chain-model hypothesis `hst` that
`index_state_is_index_digest` takes, the two index disjuncts say exactly: the
adopted `InstalledIndexSampler.indexDigest` equals the adopted
`OuterAdapter.roundCommitted` digest of some round `r < d`, or it equals the
adopted `OuterInitial.derive` digest.  Those are precisely the failures of the
hypothesis `e ≠ dig k` of `combined_schedule_injective`, read at the run's own
digests rather than at stage indices. -/
theorem extended_clash_index_disjuncts_are_run_digests (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims)
    (d : Nat)
    (hlenI : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) (st : Transcript.State)
    (hst : st.digest =
      frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI
        (22 + 5 * d) T) :
    ((∃ r : Nat, r < d ∧
        frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI
            (22 + 5 * d + 8) T
          = frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI
              (22 + (5 * r + 5)) T)
      ∨ frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI
            (22 + 5 * d + 8) T
          = frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI 22 T)
    ↔ ((∃ r : Nat, r < d ∧
        InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st u
          = (OuterAdapter.roundCommitted (hashOf (boundedQueries L) T)
              ⟨frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlenI
                (22 + 5 * r) T, 0⟩ r ((ms.get? r).getD ([], [])).1
              ((ms.get? r).getD ([], [])).2).digest)
      ∨ InstalledIndexSampler.indexDigest (hashOf (boundedQueries L) T) st u
          = (OuterInitial.derive (hashOf (boundedQueries L) T) c s).state.digest) := by
  rw [← index_state_is_index_digest L c s ms u d hlenI T st hst,
    ← extended_stage22_is_derive L c s ms u d hlenI hlenP T]
  refine or_congr (exists_congr (fun r => and_congr_right (fun hr => ?_))) Iff.rfl
  rw [extended_round_stage_five L c s ms u d hlenI hlenP T r hr]

/-! ## 2. The index squeezes at a fixed index digest are jointly uniform -/

/-- The exact oracle input of the `j`-th of the three squeezes of index draw `k`,
from an index digest: the adopted `Transcript.challengeInput` at the adopted
`InstalledIndexSampler.indexCounter`, offset by `j`. -/
def indexSqueezeInputAt (bits : Nat) (e : Transcript.Digest)
    (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3) : Transcript.Bytes :=
  Transcript.challengeInput e (InstalledIndexSampler.indexCounter bits k + j.val)

/-- The whole index schedule of oracle inputs, as one function on the index
set. -/
def indexScheduleIndex (bits : Nat) (e : Transcript.Digest) :
    InstalledIndexSampler.IndexDraw bits × Fin 3 → Transcript.Bytes :=
  fun kj => indexSqueezeInputAt bits e kj.1 kj.2

/-- (2) **THE `2 * indexBits * 3` INDEX COUNTERS ARE PAIRWISE DISTINCT.**  The
log lane occupies `0 .. 3 * indexBits - 1` and the gate lane
`3 * indexBits .. 6 * indexBits - 1`, so the two lanes never meet and inside a
lane the stride is three. -/
theorem index_counters_distinct (bits : Nat) :
    Function.Injective (fun kj : InstalledIndexSampler.IndexDraw bits × Fin 3 =>
      InstalledIndexSampler.indexCounter bits kj.1 + kj.2.val) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  simp only at h
  have hi := i.isLt
  have hj := j.isLt
  cases a with
  | log x =>
      cases b with
      | log y =>
          simp only [InstalledIndexSampler.indexCounter] at h
          rw [Prod.mk.injEq]
          exact ⟨congrArg InstalledIndexSampler.IndexDraw.log (Fin.ext (by omega)),
            Fin.ext (by omega)⟩
      | gate y =>
          exfalso
          simp only [InstalledIndexSampler.indexCounter] at h
          omega
  | gate x =>
      cases b with
      | log y =>
          exfalso
          simp only [InstalledIndexSampler.indexCounter] at h
          omega
      | gate y =>
          simp only [InstalledIndexSampler.indexCounter] at h
          rw [Prod.mk.injEq]
          exact ⟨congrArg InstalledIndexSampler.IndexDraw.gate (Fin.ext (by omega)),
            Fin.ext (by omega)⟩

/-- (2) Every index counter is below `6 * indexBits`. -/
theorem index_counter_range (bits : Nat) (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3) :
    InstalledIndexSampler.indexCounter bits k + j.val < 6 * bits := by
  have hj := j.isLt
  cases k with
  | log x => have hx := x.isLt; simp only [InstalledIndexSampler.indexCounter]; omega
  | gate x => have hx := x.isLt; simp only [InstalledIndexSampler.indexCounter]; omega

/-- (2) At the envelope's `indexBits ≤ 8` every index counter is far below the
source's own u64 guard, so that guard never binds. -/
theorem index_counter_bound (bits : Nat) (hbb : bits ≤ 8)
    (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3) :
    InstalledIndexSampler.indexCounter bits k + j.val < Transcript.u64Limit := by
  have h := index_counter_range bits k j
  unfold Transcript.u64Limit
  omega

/-- (2) The index schedule is a family of PAIRWISE DISTINCT oracle inputs at a
fixed index digest. -/
theorem index_schedule_index_injective (bits : Nat) (hbb : bits ≤ 8) (e : Transcript.Digest) :
    Function.Injective (indexScheduleIndex bits e) := by
  rintro ⟨k, j⟩ ⟨k2, j2⟩ h
  simp only [indexScheduleIndex, indexSqueezeInputAt] at h
  obtain ⟨-, hcnt⟩ := challenge_input_injective _ _ _ _
    (index_counter_bound bits hbb k j) (index_counter_bound bits hbb k2 j2) h
  exact index_counters_distinct bits hcnt

/-! ### 2.1 The pushforward -/

/-- Three squeezes bundled into the adopted `OuterChallenge.DigestTriple`, one
triple per index draw.  The index twin of the adopted
`RandomOracleSqueezes.bundleEquiv`. -/
def indexBundleEquiv (bits : Nat) :
    (InstalledIndexSampler.IndexDraw bits × Fin 3 → Block)
      ≃ InstalledIndexSampler.IndexSpace bits where
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

/-- The index point a table produces along a schedule of queries. -/
def indexEncodedDraw (Q : Finset Transcript.Bytes) (bits : Nat)
    (sel : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (T : OracleTable Q) : InstalledIndexSampler.IndexSpace bits :=
  indexBundleEquiv bits (fun kj => T (sel kj))

open Classical in
/-- The preimage of an index event under the bundling, as an event on block
tuples. -/
noncomputable def indexBundlePreimage (bits : Nat)
    (E : Finset (InstalledIndexSampler.IndexSpace bits)) :
    Finset (InstalledIndexSampler.IndexDraw bits × Fin 3 → Block) :=
  Finset.univ.filter (fun f => indexBundleEquiv bits f ∈ E)

theorem index_bundle_preimage_card (bits : Nat)
    (E : Finset (InstalledIndexSampler.IndexSpace bits)) :
    (indexBundlePreimage bits E).card = E.card := by
  classical
  have h := WhirChallenge.equiv_event_card (indexBundleEquiv bits) (fun w => w ∈ E)
  refine Eq.trans h ?_
  congr 1
  apply Finset.ext
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- The event, on oracle tables, that the assembled index point lands in `E`. -/
noncomputable def indexEncodedEvent (Q : Finset Transcript.Bytes) (bits : Nat)
    (sel : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (E : Finset (InstalledIndexSampler.IndexSpace bits)) : Finset (OracleTable Q) :=
  Finset.univ.filter (fun T => indexEncodedDraw Q bits sel T ∈ E)

theorem index_schedule_card (bits : Nat) :
    Fintype.card (InstalledIndexSampler.IndexDraw bits × Fin 3) = 2 * bits * 3 := by
  rw [Fintype.card_prod, InstalledIndexSampler.index_draw_card, Fintype.card_fin]

theorem index_space_card_as_blocks (bits : Nat) :
    (Fintype.card (InstalledIndexSampler.IndexSpace bits) : ℚ)
      = (Fintype.card Block : ℚ) ^ (2 * bits * 3) := by
  rw [InstalledIndexSampler.index_space_card, block_card_eq_word_size]
  push_cast
  ring

/-- (2) **THE INDEX SHAPE.**  When the `2 * indexBits * 3` index queries are
pairwise distinct members of `Q`, the pushforward of the uniform law on
`OracleTable Q` along the assembled index point IS the adopted
`IndexPointZeroCheck.indexProbability indexBits`. -/
theorem index_pushforward_uniform (Q : Finset Transcript.Bytes) (bits : Nat)
    (sel : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : Function.Injective sel) (E : Finset (InstalledIndexSampler.IndexSpace bits)) :
    oracleProbability Q (indexEncodedEvent Q bits sel E)
      = IndexPointZeroCheck.indexProbability bits E := by
  classical
  have hset : indexEncodedEvent Q bits sel E
      = restrictEvent Q sel (indexBundlePreimage bits E) := by
    apply Finset.ext
    intro T
    simp only [indexEncodedEvent, restrictEvent, indexBundlePreimage, Finset.mem_filter,
      Finset.mem_univ, true_and, indexEncodedDraw]
  rw [hset, pushforward_uniform_index Q sel hsel _, index_bundle_preimage_card,
    index_schedule_card, IndexPointZeroCheck.indexProbability, index_space_card_as_blocks]

/-- (2) The adopted `InstalledIndexSampler.actualIndexDraw` at a FIXED index
digest is exactly the assembled index point of the schedule. -/
theorem index_draw_at_digest_is_encoded (Q : Finset Transcript.Bytes) (bits : Nat)
    (e : Transcript.Digest)
    (sel : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : ∀ (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3),
      (sel (k, j)).val = indexSqueezeInputAt bits e k j)
    (T : OracleTable Q) :
    InstalledIndexSampler.actualIndexDraw (hashOf Q T) e bits = indexEncodedDraw Q bits sel T := by
  funext k
  show (OuterChallenge.digestBlock (hashOf Q T (indexSqueezeInputAt bits e k 0)),
        OuterChallenge.digestBlock (hashOf Q T (indexSqueezeInputAt bits e k 1)),
        OuterChallenge.digestBlock (hashOf Q T (indexSqueezeInputAt bits e k 2)))
      = (T (sel (k, 0)), T (sel (k, 1)), T (sel (k, 2)))
  rw [← hsel k 0, ← hsel k 1, ← hsel k 2, hash_of_at, hash_of_at, hash_of_at,
    digest_block_block_digest, digest_block_block_digest, digest_block_block_digest]

open Classical in
/-- The event, on oracle tables, that the index draw at a FIXED index digest
lands in `E`. -/
noncomputable def indexDigestDrawEvent (Q : Finset Transcript.Bytes) (bits : Nat)
    (e : Transcript.Digest) (E : Finset (InstalledIndexSampler.IndexSpace bits)) :
    Finset (OracleTable Q) :=
  Finset.univ.filter (fun T =>
    InstalledIndexSampler.actualIndexDraw (hashOf Q T) e bits ∈ E)

/-- (2) **THE INDEX PAYOFF, CONDITIONED ON THE INDEX DIGEST.**  Fix the index
digest OUTSIDE the law.  If the `2 * indexBits * 3` index inputs are pairwise
distinct members of `Q`, then under the random-oracle counting law on
`OracleTable Q` the adopted `InstalledIndexSampler.actualIndexDraw` at that
digest is EXACTLY `IndexPointZeroCheck.indexProbability indexBits`-distributed.

This is the index twin of the adopted
`RandomOracleSqueezes.draw_at_fixed_digests_is_uniform`, and it is what fills
`InstalledIndexSampler.uniformIndexMass`'s own disclosure "no theorem anywhere
says that the actual draw is distributed by it" -- at a FIXED index digest and in
the random-oracle model.  It says nothing about a run whose index digest is
itself an oracle output; see HONESTY (i) and (iv). -/
theorem index_draw_at_fixed_digest_is_uniform (Q : Finset Transcript.Bytes) (bits : Nat)
    (e : Transcript.Digest)
    (sel : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : ∀ (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3),
      (sel (k, j)).val = indexSqueezeInputAt bits e k j)
    (hinj : Function.Injective sel) (E : Finset (InstalledIndexSampler.IndexSpace bits)) :
    oracleProbability Q (indexDigestDrawEvent Q bits e E)
      = IndexPointZeroCheck.indexProbability bits E := by
  have hset : indexDigestDrawEvent Q bits e E = indexEncodedEvent Q bits sel E := by
    apply Finset.ext
    intro T
    simp only [indexDigestDrawEvent, indexEncodedEvent, Finset.mem_filter, Finset.mem_univ,
      true_and, index_draw_at_digest_is_encoded Q bits e sel hsel T]
  rw [hset, index_pushforward_uniform Q bits sel hinj E]

/-! ### 2.2 The guarded index bad event, and its mass over the hash -/

open Classical in
/-- The union of the adopted `IndexPointZeroCheck` per-lane agreement pullbacks,
GUARDED by `IndexPointZeroCheck.CellsDifferOnCube` exactly as
`SoundnessAssembly.indexBadEvent` is.  The guard is not cosmetic: without it the
event is all of the index space whenever the two cell families agree on the cube,
and a hypothesis "the draw misses it" is then refutable. -/
noncomputable def guardedIndexBadEvent (bits : Nat) (suppliedCells committedCells : List Element) :
    Finset (InstalledIndexSampler.IndexSpace bits) :=
  if IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells then
    IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
      IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells
  else ∅

theorem guarded_index_bad_event_of_differ (bits : Nat) (suppliedCells committedCells : List Element)
    (h : IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells) :
    guardedIndexBadEvent bits suppliedCells committedCells =
      IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
        IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells := by
  rw [guardedIndexBadEvent, if_pos h]

theorem guarded_index_bad_event_of_cube_agreement (bits : Nat)
    (suppliedCells committedCells : List Element)
    (h : ¬ IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells) :
    guardedIndexBadEvent bits suppliedCells committedCells = ∅ := by
  rw [guardedIndexBadEvent, if_neg h]

theorem guarded_index_bad_event_of_equal_cells (bits : Nat) (cells : List Element) :
    guardedIndexBadEvent bits cells cells = ∅ :=
  guarded_index_bad_event_of_cube_agreement bits cells cells (fun ⟨_, _, hne⟩ => hne rfl)

theorem tau_term_nonneg (n : Nat) : (0 : ℚ) ≤ ChallengeUnionBound.tauTerm n := by
  rw [ChallengeUnionBound.tauTerm]
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) ?_
  · exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

theorem index_space_card_cast_pos (bits : Nat) :
    (0 : ℚ) < (Fintype.card (InstalledIndexSampler.IndexSpace bits) : ℚ) := by
  have h : 0 < (OuterChallenge.wordSize ^ 3) ^ (2 * bits) :=
    pow_pos (pow_pos OuterChallenge.word_size_positive 3) _
  rw [InstalledIndexSampler.index_space_card]
  exact_mod_cast h

/-- (2) **THE GUARDED INDEX BAD EVENT HAS MASS AT MOST `2 * tauTerm indexBits`**
under the adopted index law: one `tauTerm` per lane, by the adopted
`IndexPointZeroCheck.log_index_agreement_mass_bound` and its gate twin.  No
`CellsDifferOnCube` side condition: on the agreement branch the event is empty. -/
theorem guarded_index_bad_event_mass_le (bits : Nat) (suppliedCells committedCells : List Element) :
    IndexPointZeroCheck.indexProbability bits
        (guardedIndexBadEvent bits suppliedCells committedCells)
      ≤ 2 * ChallengeUnionBound.tauTerm bits := by
  have hpos := index_space_card_cast_pos bits
  have htau : (0 : ℚ) ≤ ChallengeUnionBound.tauTerm bits := tau_term_nonneg bits
  by_cases hdiff : IndexPointZeroCheck.CellsDifferOnCube bits suppliedCells committedCells
  · rw [guarded_index_bad_event_of_differ bits suppliedCells committedCells hdiff]
    have hcard : (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
        IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells).card ≤
        (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells).card +
          (IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells).card :=
      Finset.card_union_le _ _
    have hsplit : IndexPointZeroCheck.indexProbability bits
        (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells ∪
          IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells) ≤
        IndexPointZeroCheck.indexProbability bits
          (IndexPointZeroCheck.logAgreementEvent bits suppliedCells committedCells) +
        IndexPointZeroCheck.indexProbability bits
          (IndexPointZeroCheck.gateAgreementEvent bits suppliedCells committedCells) := by
      unfold IndexPointZeroCheck.indexProbability
      rw [div_add_div_same]
      exact JointChallengeSpace.div_le_div_num _ _ _ (by exact_mod_cast hcard) hpos
    have h1 := IndexPointZeroCheck.log_index_agreement_mass_bound bits suppliedCells
      committedCells hdiff
    have h2 := IndexPointZeroCheck.gate_index_agreement_mass_bound bits suppliedCells
      committedCells hdiff
    linarith
  · rw [guarded_index_bad_event_of_cube_agreement bits suppliedCells committedCells hdiff]
    unfold IndexPointZeroCheck.indexProbability
    rw [Finset.card_empty, Nat.cast_zero, zero_div]
    linarith

/-- (2) **A BAD-INDEX-DRAW PROBABILITY OVER THE HASH.**  Conditioned on the index
digest, the probability -- under the random-oracle counting law on
`OracleTable Q` -- that the adopted `InstalledIndexSampler.actualIndexDraw` falls
in the guarded agreement union is at most `2 * ChallengeUnionBound.tauTerm
indexBits`.  The left-hand side is a mass over the HASH TABLE, not over an
abstract coordinate point of `IndexSpace`. -/
theorem index_bad_draw_at_fixed_digest_le (Q : Finset Transcript.Bytes) (bits : Nat)
    (e : Transcript.Digest)
    (sel : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hsel : ∀ (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3),
      (sel (k, j)).val = indexSqueezeInputAt bits e k j)
    (hinj : Function.Injective sel) (suppliedCells committedCells : List Element) :
    oracleProbability Q (indexDigestDrawEvent Q bits e
        (guardedIndexBadEvent bits suppliedCells committedCells))
      ≤ 2 * ChallengeUnionBound.tauTerm bits := by
  rw [index_draw_at_fixed_digest_is_uniform Q bits e sel hsel hinj]
  exact guarded_index_bad_event_mass_le bits suppliedCells committedCells

/-! ## 3. Both families under ONE oracle law -/

/-- The two schedules, as one query family on the disjoint union of the two index
sets.  This is the family a genuine PRODUCT law would be taken along. -/
def combinedSel (Q : Finset Transcript.Bytes) (d bits : Nat)
    (selJ : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (selI : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q }) :
    (JointChallengeSpace.Draw d × Fin 3) ⊕ (InstalledIndexSampler.IndexDraw bits × Fin 3)
      → { q : Transcript.Bytes // q ∈ Q }
  | Sum.inl x => selJ x
  | Sum.inr y => selI y

theorem combined_sel_inl (Q : Finset Transcript.Bytes) (d bits : Nat)
    (selJ : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (selI : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (x : JointChallengeSpace.Draw d × Fin 3) :
    combinedSel Q d bits selJ selI (Sum.inl x) = selJ x := rfl

theorem combined_sel_inr (Q : Finset Transcript.Bytes) (d bits : Nat)
    (selJ : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (selI : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (y : InstalledIndexSampler.IndexDraw bits × Fin 3) :
    combinedSel Q d bits selJ selI (Sum.inr y) = selI y := rfl

/-- (3) **THE COUNTERS ALONE DO NOT SEPARATE THE TWO FAMILIES.**  The log lane's
first index counter is `0`, and so is the adopted
`JointChallengeSpace.sourceCounter` of a coupled round's log challenge; likewise
the gate lane meets `3` at `indexBits = 1`.  So distinctness across the index
block and a round block MUST come from the digests, not from the counters. -/
theorem index_counters_meet_round_counters (bits d : Nat) (hb : 0 < bits) (r : Fin d) :
    InstalledIndexSampler.indexCounter bits (InstalledIndexSampler.IndexDraw.log ⟨0, hb⟩)
      = JointChallengeSpace.sourceCounter d (JointChallengeSpace.Draw.outerLog r) := rfl

/-- (3) **CROSS-DISTINCTNESS IS EXACTLY THE DIGEST CONDITION.**  Once the index
digest differs from every block digest, every index squeeze input differs from
every joint squeeze input, because the adopted
`RandomOracleSqueezes.challenge_input_injective` reads the digest slot of the
challenge framing. -/
theorem index_input_ne_joint_input (d bits : Nat) (hdb : d ≤ 13) (hbb : bits ≤ 8)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) (e : Transcript.Digest)
    (hne : ∀ k : JointChallengeSpace.Draw d, e ≠ dig k)
    (k : JointChallengeSpace.Draw d) (j : Fin 3)
    (k2 : InstalledIndexSampler.IndexDraw bits) (j2 : Fin 3) :
    indexSqueezeInputAt bits e k2 j2 ≠ squeezeInputAt d dig k j := by
  intro h
  obtain ⟨hdig, -⟩ := challenge_input_injective _ _ _ _
    (index_counter_bound bits hbb k2 j2) (source_counter_bound d hdb k j) h
  exact hne k hdig

/-- (3) **THE COMBINED FAMILY IS INJECTIVE.**  The joint schedule's own
injectivity, the index schedule's own injectivity, and the digest separation of
`index_input_ne_joint_input`. -/
theorem combined_schedule_injective (Q : Finset Transcript.Bytes) (d bits : Nat)
    (hdb : d ≤ 13) (hbb : bits ≤ 8)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) (e : Transcript.Digest)
    (hne : ∀ k : JointChallengeSpace.Draw d, e ≠ dig k)
    (selJ : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (selI : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hselJ : ∀ (k : JointChallengeSpace.Draw d) (j : Fin 3),
      (selJ (k, j)).val = squeezeInputAt d dig k j)
    (hselI : ∀ (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3),
      (selI (k, j)).val = indexSqueezeInputAt bits e k j)
    (hJ : Function.Injective selJ) (hI : Function.Injective selI) :
    Function.Injective (combinedSel Q d bits selJ selI) := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (hJ h)
  · exfalso
    obtain ⟨k, j⟩ := x
    obtain ⟨k2, j2⟩ := y
    refine index_input_ne_joint_input d bits hdb hbb dig e hne k j k2 j2 ?_
    rw [← hselI k2 j2, ← hselJ k j]
    exact (congrArg Subtype.val h).symm
  · exfalso
    obtain ⟨k2, j2⟩ := x
    obtain ⟨k, j⟩ := y
    refine index_input_ne_joint_input d bits hdb hbb dig e hne k j k2 j2 ?_
    rw [← hselI k2 j2, ← hselJ k j]
    exact congrArg Subtype.val h
  · exact congrArg Sum.inr (hI h)

theorem joint_sel_injective_of_combined (Q : Finset Transcript.Bytes) (d bits : Nat)
    (selJ : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (selI : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hcomb : Function.Injective (combinedSel Q d bits selJ selI)) :
    Function.Injective selJ := by
  intro a b h
  exact Sum.inl.inj (hcomb (show combinedSel Q d bits selJ selI (Sum.inl a)
    = combinedSel Q d bits selJ selI (Sum.inl b) from h))

theorem index_sel_injective_of_combined (Q : Finset Transcript.Bytes) (d bits : Nat)
    (selJ : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (selI : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hcomb : Function.Injective (combinedSel Q d bits selJ selI)) :
    Function.Injective selI := by
  intro a b h
  exact Sum.inr.inj (hcomb (show combinedSel Q d bits selJ selI (Sum.inr a)
    = combinedSel Q d bits selJ selI (Sum.inr b) from h))

/-- The union of the two bad events, ON THE SAME TABLE SPACE.  This is the object
`SoundnessAssembly` could not name: its two masses lived on two unrelated
coordinate spaces, so their sum was arithmetic, not a union. -/
noncomputable def jointOrIndexBadEvent (Q : Finset Transcript.Bytes) (d bits : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) (e : Transcript.Digest)
    (EJ : Finset (JointChallengeSpace.JointSpace d))
    (EI : Finset (InstalledIndexSampler.IndexSpace bits)) : Finset (OracleTable Q) :=
  digestDrawEvent Q d dig EJ ∪ indexDigestDrawEvent Q bits e EI

/-- (3) **ONE LAW FOR BOTH FAMILIES, AT FIXED DIGESTS.**  All the digests are
fixed outside the law and pairwise distinct -- the separation is packaged as the
injectivity of `combinedSel`, which `combined_schedule_injective` derives from
`e ≠ dig k` -- and then the mass, under the SINGLE random-oracle counting law on
`OracleTable Q`, of the UNION of the adopted `JointChallengeSpace.jointBadEvent`
and the guarded index agreement union is at most
`ChallengeUnionBound.combinedBound + 2 * ChallengeUnionBound.tauTerm indexBits`.

WHAT CONSUMES WHAT.  The union bound itself consumes only the two families'
separate injectivities, which `hcomb` supplies through
`joint_sel_injective_of_combined` and `index_sel_injective_of_combined`.  The
CROSS distinctness inside `hcomb` is what a genuine PRODUCT law -- "the joint
draw and the index draw are independent" -- would need, and
`index_counters_meet_round_counters` shows it cannot be had from the counters.
Scope as in HONESTY (iv) and (vi): fixed digests, no WHIR/Merkle, not the
system's soundness error. -/
theorem joint_and_index_bad_at_fixed_digests_le (Q : Finset Transcript.Bytes) (d bits : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) (e : Transcript.Digest)
    (selJ : JointChallengeSpace.Draw d × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (selI : InstalledIndexSampler.IndexDraw bits × Fin 3 → { q : Transcript.Bytes // q ∈ Q })
    (hselJ : ∀ (k : JointChallengeSpace.Draw d) (j : Fin 3),
      (selJ (k, j)).val = squeezeInputAt d dig k j)
    (hselI : ∀ (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3),
      (selI (k, j)).val = indexSqueezeInputAt bits e k j)
    (hcomb : Function.Injective (combinedSel Q d bits selJ selI))
    (quotientDegree constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (g : Nat → Element)
    (coeffsOf : Nat → List Element) (suppliedCells committedCells : List Element)
    (hlogLen : logLane.length = d) (hgateLen : gateLane.length = d)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability Q (jointOrIndexBadEvent Q d bits dig e
        (JointChallengeSpace.jointBadEvent d logCompare gateCompare logLane gateLane g
          (2 ^ d) coeffsOf)
        (guardedIndexBadEvent bits suppliedCells committedCells))
      ≤ ChallengeUnionBound.combinedBound d quotientDegree d constraints
        + 2 * ChallengeUnionBound.tauTerm bits := by
  have hJ := joint_sel_injective_of_combined Q d bits selJ selI hcomb
  have hI := index_sel_injective_of_combined Q d bits selJ selI hcomb
  refine le_trans (oracle_probability_union_le Q _ _) ?_
  refine add_le_add ?_ ?_
  · exact bad_draw_at_fixed_digests_le Q d dig selJ hselJ hJ quotientDegree constraints
      logCompare gateCompare logLane gateLane g coeffsOf hlogLen hgateLen hlogDeg hgateDeg hclen
  · exact index_bad_draw_at_fixed_digest_le Q bits e selI hselI hI suppliedCells committedCells

/-! ## 4. The birthday bound for the extended chain -/

open Classical in
/-- **THE EXTENDED CLASH.**  Two different coupled rounds of the whole chain
commit to the same digest, OR the index digest -- the chain's stage
`22 + 5 d + 8` -- equals a coupled round's commit digest, OR it equals the
relation-prefix digest the adopted `sourceDigest` uses for the gate alpha and
gate tau columns.  The second and third disjuncts are exactly the failure of the
hypothesis `e ≠ dig k` of `combined_schedule_injective`, read on the chain. -/
noncomputable def extendedDigestClashEvent (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d : Nat)
    (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    (∃ r t : Nat, r < t ∧ t < d ∧
      frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
        (22 + (5 * r + 5)) T
        = frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
            (22 + (5 * t + 5)) T)
    ∨ (∃ r : Nat, r < d ∧
      frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
        (22 + 5 * d + 8) T
        = frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
            (22 + (5 * r + 5)) T)
    ∨ frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen
        (22 + 5 * d + 8) T
        = frameState L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen 22 T)

/-- (4) The extended clash sits inside the complement of the adopted
`BirthdayClashBound.noClash` good event of the `22 + 5 d + 8`-stage chain.  The
eight claim frames need no special treatment: the adopted
`frame_chain_causal` holds for EVERY shape function. -/
theorem extended_digest_clash_event_subset (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims)
    (d : Nat) (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L) :
    extendedDigestClashEvent L c s ms u d hlen
      ⊆ (noClash (frameSel L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen)
          (avoidBase OuterInitial.zeroDigest) (22 + 5 * d + 8))ᶜ := by
  intro T hT
  simp only [extendedDigestClashEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  by_contra hgood
  rw [Finset.not_mem_compl] at hgood
  rcases hT with ⟨r, t, hrt, htd, heq⟩ | ⟨r, hrd, heq⟩ | heq
  · rw [show 22 + (5 * r + 5) = (22 + 5 * r + 4) + 1 from by omega,
      show 22 + (5 * t + 5) = (22 + 5 * t + 4) + 1 from by omega] at heq
    exact frame_state_distinct_on_no_clash L OuterInitial.zeroDigest
      (prefixRoundIndexShape c s ms u d) hlen (22 + 5 * d + 8) T hgood
      (22 + 5 * r + 4) (22 + 5 * t + 4) (by omega) (by omega) heq
  · rw [show 22 + (5 * r + 5) = (22 + 5 * r + 4) + 1 from by omega,
      show 22 + 5 * d + 8 = (22 + 5 * d + 7) + 1 from by omega] at heq
    exact frame_state_distinct_on_no_clash L OuterInitial.zeroDigest
      (prefixRoundIndexShape c s ms u d) hlen (22 + 5 * d + 8) T hgood
      (22 + 5 * r + 4) (22 + 5 * d + 7) (by omega) (by omega) heq.symm
  · rw [show (22 : Nat) = 21 + 1 from by omega,
      show 22 + 5 * d + 8 = (21 + 5 * d + 8) + 1 from by omega] at heq
    exact frame_state_distinct_on_no_clash L OuterInitial.zeroDigest
      (prefixRoundIndexShape c s ms u d) hlen (22 + 5 * d + 8) T hgood
      21 (21 + 5 * d + 8) (by omega) (by omega) heq.symm

/-- (4) **THE BIRTHDAY BOUND FOR THE EXTENDED CHAIN.**  `22 + 5 d + 8` stages, so
`(22 + 5 d + 8)(22 + 5 d + 9) / 2` over the block space.  Cheap given the adopted
`BirthdayClashBound.frame_chain_clash_probability_le`: only the shape changed. -/
theorem extended_digest_clash_mass_le (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims) (d : Nat)
    (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L) :
    oracleProbability (boundedQueries L) (extendedDigestClashEvent L c s ms u d hlen)
      ≤ ((22 + 5 * d + 8 : Nat) : ℚ) * (((22 + 5 * d + 8 : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) :=
  le_trans
    (oracle_probability_mono _ _ _ (extended_digest_clash_event_subset L c s ms u d hlen))
    (frame_chain_clash_probability_le L OuterInitial.zeroDigest
      (prefixRoundIndexShape c s ms u d) hlen (22 + 5 * d + 8))

/-- (4) **THE BOUND AT THE ENVELOPE'S `degreeBits = 13`**: `95` stages, so
`4560 / |Block|`, up from the adopted `3828` for the chain that stops at the last
round.  `|Block| = 256 ^ 32` by the adopted `block_card`, never evaluated. -/
theorem extended_digest_clash_mass_at_thirteen (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims)
    (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u 13 k).2.length ≤ L) :
    oracleProbability (boundedQueries L) (extendedDigestClashEvent L c s ms u 13 hlen)
      ≤ 4560 / (Fintype.card Block : ℚ) := by
  have h := extended_digest_clash_mass_le L c s ms u 13 hlen
  have hnum : ((22 + 5 * 13 + 8 : Nat) : ℚ) * (((22 + 5 * 13 + 8 : Nat) : ℚ) + 1) / 2 = 4560 := by
    norm_num
  rw [hnum] at h
  exact h

theorem extended_digest_clash_bound_lt_one : (4560 : ℚ) / (Fintype.card Block : ℚ) < 1 := by
  rw [div_lt_one block_card_cast_pos]
  exact_mod_cast block_card_gt_small 4560 (by norm_num)

/-- (4) **THE EXTENDED CLASH EVENT IS NOT EMPTY.**  The adopted
`BirthdayClashBound.constantTable` is in it at every `d`, through the third
disjunct: a table that answers one fixed block everywhere makes the index digest
equal to the relation-prefix digest.  The bound above is not proved on an empty
event. -/
theorem constant_table_in_extended_clash_event (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims)
    (d : Nat) (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L) :
    constantTable L ∈ extendedDigestClashEvent L c s ms u d hlen := by
  simp only [extendedDigestClashEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine Or.inr (Or.inr ?_)
  rw [show 22 + 5 * d + 8 = (21 + 5 * d + 8) + 1 from by omega,
    show (22 : Nat) = 21 + 1 from by omega, constant_table_state, constant_table_state]

/-- (4) **THE GOOD EVENT IS NOT EMPTY EITHER**, at every `d ≤ 13`: `95 * 96`
is below `2 * 65536`, so the adopted
`BirthdayClashBound.frame_chain_no_clash_nonempty` applies and the conditioning
of section 3 is instantiated at a non-empty event. -/
theorem extended_chain_good_event_nonempty (L : Nat) (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (u : Verifier.UsedClaims)
    (d : Nat) (hdb : d ≤ 13)
    (hlen : ∀ k, 61 + (prefixRoundIndexShape c s ms u d k).2.length ≤ L) :
    (noClash (frameSel L OuterInitial.zeroDigest (prefixRoundIndexShape c s ms u d) hlen)
      (avoidBase OuterInitial.zeroDigest) (22 + 5 * d + 8)).Nonempty := by
  refine frame_chain_no_clash_nonempty L OuterInitial.zeroDigest
    (prefixRoundIndexShape c s ms u d) hlen (22 + 5 * d + 8) ?_
  have h : 22 + 5 * d + 8 ≤ 95 := by omega
  calc (22 + 5 * d + 8) * (22 + 5 * d + 8 + 1) ≤ 95 * 96 := Nat.mul_le_mul h (by omega)
    _ < 2 * 65536 := by norm_num

/-! ## 5. Satisfiability of every hypothesis, at a closed instance -/

/-- The index schedule's own query set: the image of its `2 * indexBits * 3`
inputs. -/
noncomputable def indexScheduleSet (bits : Nat) (e : Transcript.Digest) :
    Finset Transcript.Bytes :=
  Finset.image (indexScheduleIndex bits e) Finset.univ

theorem index_schedule_index_mem (bits : Nat) (e : Transcript.Digest)
    (kj : InstalledIndexSampler.IndexDraw bits × Fin 3) :
    indexScheduleIndex bits e kj ∈ indexScheduleSet bits e :=
  Finset.mem_image_of_mem _ (Finset.mem_univ kj)

/-- The index schedule as a membership-carrying query family into its own query
set. -/
noncomputable def indexScheduleSel (bits : Nat) (e : Transcript.Digest) :
    InstalledIndexSampler.IndexDraw bits × Fin 3 →
      { q : Transcript.Bytes // q ∈ indexScheduleSet bits e } :=
  fun kj => ⟨indexScheduleIndex bits e kj, index_schedule_index_mem bits e kj⟩

/-- (5) **THE HYPOTHESES OF SECTION 2 ARE SATISFIABLE**, at every `indexBits ≤ 8`
the envelope allows: a concrete index digest, a concrete query set and a concrete
INJECTIVE query family for it. -/
theorem index_schedule_hypotheses_are_satisfiable (bits : Nat) (hbb : bits ≤ 8)
    (e : Transcript.Digest) :
    (∀ (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3),
        (indexScheduleSel bits e (k, j)).val = indexSqueezeInputAt bits e k j) ∧
      Function.Injective (indexScheduleSel bits e) := by
  refine ⟨fun k j => rfl, ?_⟩
  intro a b h
  exact index_schedule_index_injective bits hbb e (congrArg Subtype.val h)

theorem index_schedule_hypotheses_are_satisfiable_at_eight :
    (∀ (k : InstalledIndexSampler.IndexDraw 8) (j : Fin 3),
        (indexScheduleSel 8 OuterInitial.zeroDigest (k, j)).val
          = indexSqueezeInputAt 8 OuterInitial.zeroDigest k j) ∧
      Function.Injective (indexScheduleSel 8 OuterInitial.zeroDigest) :=
  index_schedule_hypotheses_are_satisfiable 8 (by omega) OuterInitial.zeroDigest

/-! ### 5.1 A separated pair of digests, and a query set for both families -/

/-- The index digest of the satisfiability witness: the adopted
`RandomOracleSqueezes.indexDigest` spelling `200`, which no
`RandomOracleSqueezes.blockDigests d` can equal for `d ≤ 13` because the adopted
`JointChallengeSpace.sourceBlock` never exceeds `d + 1`. -/
def separatedIndexDigest : Transcript.Digest := RandomOracleSqueezes.indexDigest 200

theorem source_block_le_degree (d : Nat) (k : JointChallengeSpace.Draw d) :
    JointChallengeSpace.sourceBlock d k ≤ d := by
  cases k with
  | gateAlpha => exact Nat.zero_le d
  | gateTau i => exact Nat.zero_le d
  | outerLog r => exact r.isLt
  | outerGate r => exact r.isLt

theorem separated_index_digest_ne (d : Nat) (hdb : d ≤ 13)
    (k : JointChallengeSpace.Draw d) : separatedIndexDigest ≠ blockDigests d k := by
  intro h
  have hsmall := source_block_small d hdb k
  have hle := source_block_le_degree d k
  have h200 : (200 : Nat) = JointChallengeSpace.sourceBlock d k :=
    index_digest_injective 200 _ (by omega) hsmall h
  omega

/-- The query set of BOTH schedules. -/
noncomputable def combinedSet (d bits : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) (e : Transcript.Digest) :
    Finset Transcript.Bytes :=
  scheduleSet d dig ∪ indexScheduleSet bits e

noncomputable def combinedJointSel (d bits : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) (e : Transcript.Digest) :
    JointChallengeSpace.Draw d × Fin 3 →
      { q : Transcript.Bytes // q ∈ combinedSet d bits dig e } :=
  fun kj => ⟨scheduleIndex d dig kj,
    Finset.mem_union_left _ (schedule_index_mem d dig kj)⟩

noncomputable def combinedIndexSel (d bits : Nat)
    (dig : JointChallengeSpace.Draw d → Transcript.Digest) (e : Transcript.Digest) :
    InstalledIndexSampler.IndexDraw bits × Fin 3 →
      { q : Transcript.Bytes // q ∈ combinedSet d bits dig e } :=
  fun kj => ⟨indexScheduleIndex bits e kj,
    Finset.mem_union_right _ (index_schedule_index_mem bits e kj)⟩

/-- (5) **THE HYPOTHESES OF SECTION 3 ARE SATISFIABLE**, at every
`degreeBits ≤ 13` and `indexBits ≤ 8`.  `blockDigests d` and
`separatedIndexDigest` are concrete and pairwise separated, `combinedSet` is a
concrete query set answering both schedules, and the combined family is
injective.  So `joint_and_index_bad_at_fixed_digests_le` is not vacuous. -/
theorem separated_digest_hypotheses_are_satisfiable (d bits : Nat) (hdb : d ≤ 13)
    (hbb : bits ≤ 8) :
    (∀ (k : JointChallengeSpace.Draw d) (j : Fin 3),
        (combinedJointSel d bits (blockDigests d) separatedIndexDigest (k, j)).val
          = squeezeInputAt d (blockDigests d) k j) ∧
      (∀ (k : InstalledIndexSampler.IndexDraw bits) (j : Fin 3),
        (combinedIndexSel d bits (blockDigests d) separatedIndexDigest (k, j)).val
          = indexSqueezeInputAt bits separatedIndexDigest k j) ∧
      Function.Injective (combinedSel (combinedSet d bits (blockDigests d) separatedIndexDigest)
        d bits (combinedJointSel d bits (blockDigests d) separatedIndexDigest)
        (combinedIndexSel d bits (blockDigests d) separatedIndexDigest)) := by
  refine ⟨fun k j => rfl, fun k j => rfl, ?_⟩
  refine combined_schedule_injective _ d bits hdb hbb (blockDigests d) separatedIndexDigest
    (separated_index_digest_ne d hdb) _ _ (fun k j => rfl) (fun k j => rfl) ?_ ?_
  · intro a b h
    exact schedule_distinct_of_separating_digests d hdb (blockDigests d)
      (block_digests_separate d hdb) (congrArg Subtype.val h)
  · intro a b h
    exact index_schedule_index_injective bits hbb separatedIndexDigest (congrArg Subtype.val h)

theorem separated_digest_hypotheses_are_satisfiable_at_the_envelope :
    (∀ (k : JointChallengeSpace.Draw 13) (j : Fin 3),
        (combinedJointSel 13 8 (blockDigests 13) separatedIndexDigest (k, j)).val
          = squeezeInputAt 13 (blockDigests 13) k j) ∧
      (∀ (k : InstalledIndexSampler.IndexDraw 8) (j : Fin 3),
        (combinedIndexSel 13 8 (blockDigests 13) separatedIndexDigest (k, j)).val
          = indexSqueezeInputAt 8 separatedIndexDigest k j) ∧
      Function.Injective (combinedSel (combinedSet 13 8 (blockDigests 13) separatedIndexDigest)
        13 8 (combinedJointSel 13 8 (blockDigests 13) separatedIndexDigest)
        (combinedIndexSel 13 8 (blockDigests 13) separatedIndexDigest)) :=
  separated_digest_hypotheses_are_satisfiable 13 8 (by omega) (by omega)

/-- (5) **THE FULLY CLOSED ENVELOPE INSTANCE OF SECTION 3.**  Every hypothesis of
`joint_and_index_bad_at_fixed_digests_le` is discharged at once, at the
envelope's `degreeBits = 13` and `indexBits = 8`: the query set is this module's
`combinedSet`, the digests are the adopted `blockDigests 13` and
`separatedIndexDigest`, the two query families are `combinedJointSel` and
`combinedIndexSel` with their `hsel`s and their combined injectivity from
`separated_digest_hypotheses_are_satisfiable_at_the_envelope`, and the five
INHERITED lane hypotheses are met by the adopted `RandomOracleSqueezes.trivialLane`
witnesses at `quotientDegree = 0` and `constraints = 0`, with empty supplied and
committed cell lists.  Nothing is left assumed except the free field element `x`
that names the two lanes; see HONESTY (vii). -/
theorem joint_and_index_bad_at_the_envelope_closed (x : Element) :
    oracleProbability (combinedSet 13 8 (blockDigests 13) separatedIndexDigest)
        (jointOrIndexBadEvent _ 13 8 (blockDigests 13) separatedIndexDigest
          (JointChallengeSpace.jointBadEvent 13 x x (trivialLane x) (trivialLane x) (fun _ => x)
            (2 ^ 13) (fun _ => []))
          (guardedIndexBadEvent 8 [] []))
      ≤ ChallengeUnionBound.combinedBound 13 0 13 0 + 2 * ChallengeUnionBound.tauTerm 8 :=
  joint_and_index_bad_at_fixed_digests_le _ 13 8 (blockDigests 13) separatedIndexDigest _ _
    separated_digest_hypotheses_are_satisfiable_at_the_envelope.1
    separated_digest_hypotheses_are_satisfiable_at_the_envelope.2.1
    separated_digest_hypotheses_are_satisfiable_at_the_envelope.2.2
    0 0 x x (trivialLane x) (trivialLane x) (fun _ => x) (fun _ => []) [] []
    (trivial_lane_length x) (trivial_lane_length x) (trivial_lane_deg x 5)
    (trivial_lane_deg x (0 + 2)) (fun _ _ => by simp)

/-! ### 5.2 The length budget has a witness -/

/-- The used claims of the satisfiability witness: five EMPTY cell vectors. -/
def emptyClaims : Verifier.UsedClaims := ⟨[], [], [], [], []⟩

/-- (5) **THE LENGTH BUDGET IS SATISFIABLE AT THE ENVELOPE.**  At `L = 8192` and
a per-cell width bound `W = 338` the eight claim frames fit, whatever the
relation prefix and the round payloads need -- those two are the adopted
`BirthdayClashBound` hypotheses and are carried through unchanged. -/
theorem length_budget_is_satisfiable_at_the_envelope (c : Verifier.Config)
    (s : Verifier.Statement) (ms : List Verifier.CoupledMessage) (d : Nat)
    (hpre : ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ 8192)
    (hround : ∀ k, 61 + (roundShape ms k).2.length ≤ 8192) :
    ∀ k, 61 + (prefixRoundIndexShape c s ms emptyClaims d k).2.length ≤ 8192 :=
  prefix_round_index_shape_payload_bound 8192 338 c s ms emptyClaims d hpre hround
    (by simp only [emptyClaims, List.length_nil]; omega)
    (by simp only [emptyClaims, List.length_nil]; omega)
    (by simp only [emptyClaims, List.length_nil]; omega)
    (by simp only [emptyClaims, List.length_nil]; omega)
    (by simp only [emptyClaims, List.length_nil]; omega)
    (by omega) (by omega)

/-- (5) **THE ROUND-SHAPE BUDGET AT THE ENVELOPE IS THE ADOPTED ONE.**  The
adopted `BirthdayClashBound.round_shape_payload_bound_at_envelope` supplies
`hround` at the deployed shape, so the witness above is not conditional on an
unexamined hypothesis. -/
theorem envelope_round_budget_is_the_adopted_one (ms : List Verifier.CoupledMessage)
    (quotientDegree : Nat)
    (hlog : ∀ i, ((ms.get? i).getD ([], [])).1.length ≤ 5)
    (hgate : ∀ i, ((ms.get? i).getD ([], [])).2.length ≤ quotientDegree + 2)
    (hL : 189 + 24 * quotientDegree ≤ 8192) :
    ∀ k, 61 + (roundShape ms k).2.length ≤ 8192 :=
  round_shape_payload_bound_at_envelope 8192 ms quotientDegree hlog hgate hL

end Audit.Wire3.IndexLanesOracle
