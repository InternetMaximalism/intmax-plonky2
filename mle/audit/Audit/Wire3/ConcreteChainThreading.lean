import Audit.Wire3.BirthdayClashBound

/-!
# THE CHAIN MODEL IS THE RUN'S OWN COMMIT CHAIN

## The gap this module closes

`BirthdayClashBound` proves a birthday bound for a CHAIN MODEL: the frame chain
`prefixRoundShape c s ms`, twenty-two relation-prefix frames from
`OuterInitial.zeroDigest` followed by five frames per coupled round.  It proves

* `prefix_state_is_derive_digest` -- the chain's digest after the prefix IS the
  adopted `OuterInitial.derive` digest,
* `prefix_round_chain_step` -- five stages of the chain ARE one adopted
  `OuterAdapter.roundCommitted` fold,
* `prefix_round_digest_clash_mass_le` -- the mass of the chain's own clash event
  is at most `(22 + 5 d) (22 + 5 d + 1) / 2` over the block space,

and a run-level corollary `run_bad_draw_probability_le_of_clash_bound` whose
additive term is a HYPOTHESIS `eps` on
`oracleProbability Q (clashEvent Q c p)`.  Its own section 9 names what is
missing: nothing there identifies the chain's stage `22 + 5 r + 5` with position
`r` of `InstalledRoundCommit.concreteChain`, so the chain's clash event is not,
syntactically, the run's `RandomOracleSqueezes.RoundDigestClash`.

THIS MODULE CARRIES OUT THAT IDENTIFICATION.  `chain_model_is_the_run_chain` is
an induction on the round index: the chain's state digest after `22 + 5 r`
absorbs IS `InstalledRoundCommit.concreteFinal` of the run's first `r` coupled
messages, from the adopted derived state.  `run_round_digest_is_chain_digest`
reads the adopted `RandomOracleSqueezes.sourceDigest` off it, and
`run_round_digest_clash_event_is_prefix_round_clash` turns the two into an
EQUALITY of events.  The hypothesis `eps` is then discharged:
`run_bad_draw_probability_le_birthday` is a run-level bound with NO clash
hypothesis left, for a fixed (non-adaptive) prover under the random oracle
model.

## What is proved

1. **THE THREADING THEOREM** (section 2).  `chain_model_is_the_run_chain`:
   for every `r` at most the number of coupled rounds,

     `frameState L zeroDigest (prefixRoundShape c (statement p) (roundMessages p)) hlen (22 + 5 r) T`
       `= (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)`
           `(OuterInitial.derive (hashOf (boundedQueries L) T) c (statement p)).state 0`
           `((roundMessages p).take r)).digest`

   by induction on `r`, with `prefix_state_is_derive_digest` at `r = 0` and
   `prefix_round_chain_step` together with `round_commit_is_stage_five` and
   `round_committed_is_the_frame_fold` at the step.  `concrete_final_take_succ`
   is the list bookkeeping the adopted module left open.
   `run_round_digest_is_chain_digest` is the same fact read at the adopted
   `sourceDigest`: the digest round `r`'s two challenges are squeezed from is
   the chain's state after `22 + (5 r + 5)` absorbs.

2. **THE DISCHARGE** (section 4).  `run_round_digest_clash_event_is_prefix_round_clash`:
   the adopted `clashEvent (boundedQueries L) c p` and the chain model's
   `prefixRoundDigestClashEvent` are THE SAME FINSET.  Hence
   `run_clash_probability_le`, and then
   `run_bad_draw_probability_le_birthday` (section 5): the first run-level
   random-oracle bound in this development with no clash hypothesis, for a fixed
   (non-adaptive) prover under the random oracle model --

     `oracleProbability (boundedQueries L) (runDrawEvent ... (jointBadEvent ...))`
       `<= combinedBound degreeBits quotientDegree degreeBits constraints`
         `+ (22 + 5 d)(22 + 5 d + 1) / 2 / |Block|`

   and at `d = 13` the numeral `3828 / |Block|`, which
   `birthday_term_le_two_pow_neg` bounds by `2 ^ (-244)` symbolically.

3. **THE LENGTH BUDGET** (sections 3 and 6).  `LengthBudget L c p quotientDegree`
   collects every side condition the chain needs into one predicate, and
   `length_budget_at_envelope` is a closed witness at `d = 13`: the adopted
   `Verifier.testConfig` at `degreeBits := 13`, thirteen coupled rounds of the
   adopted shape, and `L = 381 = 189 + 24 * 8`.
   `run_bad_draw_probability_le_birthday_closed` is the run-level bound at that
   witness, with no hypothesis left but the choice of a field element, and
   `closed_bound_lt_one` records that the right-hand side of that closed bound is
   strictly below `1` -- the adopted
   `ChallengeUnionBound.combined_bound_at_extremes_numeric` gives `2 ^ (-172)`
   for the `combinedBound` term and `birthday_term_le_two_pow_neg` gives
   `2 ^ (-244)` for the birthday term.

4. **NON-VACUITY** (section 7).  The constant table is in the clash event
   (`constant_table_in_run_clash_event`), so the bound is on a non-empty event;
   and `boundedQueries L` is not frame-free, so the adopted
   `run_bound_trivial_at_frame_free` does not apply to it -- the bound here is
   not the trivial `+ 1`.

## HONESTY

(i) **THIS IS THE RANDOM ORACLE MODEL.**  The counting law is the uniform
measure on `OracleTable (boundedQueries L)` -- an independent uniform block per
byte string of length at most `L`.  Nothing here is a statement about keccak, or
about any concrete hash function.  The numeral `3828 / |Block|` is the birthday
term OF THIS CHAIN MODEL UNDER THAT LAW; it is not a property of the deployed
permutation and it is not measured against any keccak cryptanalysis.

(ii) **THE PROVER IS FIXED.**  `p` is a `Verifier.Proof` quantified OUTSIDE the
law: `roundMessages p` are fixed before the table `T` is sampled.  In the real
protocol the prover chooses round `r + 1`'s messages AFTER seeing round `r`'s
challenges, so an adaptive prover is NOT covered.  Extending the argument to an
adaptive prover means re-running the fresh-query induction against a strategy,
not against a list, and none of that is here.

(iii) **THE LANES ARE THE OUTER SUMCHECK LANES.**  The index lanes, the WHIR
folding transcript and the Merkle openings are NOT covered: the chain modelled
here is the twenty-two relation-prefix frames plus the five frames per coupled
round, and nothing else of the run is threaded.

(iv) **THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.**  The bound is on the
mass of a draw event under the oracle law, with the conditional-soundness
apparatus of `ConditionalSoundness` and `JointChallengeSpace` supplying the
`combinedBound` term.  The design point of the deployed profile is about a
hundred bits; the numbers here bound one named term of one named event and do
not aggregate into a soundness statement for the protocol.

(v) **THE PREFIX LENGTHS ARE HYPOTHESES ABOUT THE STATEMENT.**  Of the
twenty-two prefix frames, TWO carry statement field vectors -- positions `2` and
`3` of the adopted `CommitmentOrder.gateChallengeFrames`, the circuit digest and
the public inputs -- and THREE more carry statement roots at positions `13`, `15`
and `19`, which are fixed at thirty-two bytes and so need no hypothesis.  Two
further frames carry configuration byte strings.  Only the two field vectors and
the two configuration strings have lengths that are not fixed outright, and those
four lengths are exactly the four arithmetic side conditions of `LengthBudget`,
discharged at the closed witness and assumed in general.
-/

namespace Audit.Wire3.ConcreteChainThreading

open Audit.Wire3
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound

/-! ## 1. THE RUN'S INCOMING STATE, ONE COUPLED ROUND AT A TIME -/

/-- (1) **THE LIST BOOKKEEPING THE ADOPTED MODULE LEFT OPEN.**  The state left by
the first `r + 1` coupled rounds is round `r`'s own five-frame fold onto the
state left by the first `r`, with the counter at `6` because that round draws six
scalars.  This is the successor equation for `InstalledRoundCommit.concreteFinal`
that `concrete_chain_get` presupposes but never states. -/
theorem concrete_final_take_succ (thash : Transcript.Hash) :
    ∀ (ms : List Verifier.CoupledMessage) (st : Transcript.State) (i r : Nat),
      r < ms.length →
      InstalledRoundCommit.concreteFinal thash st i (ms.take (r + 1))
        = ⟨(OuterAdapter.roundCommitted thash
              (InstalledRoundCommit.concreteFinal thash st i (ms.take r)) (i + r)
              ((ms.get? r).getD ([], [])).1 ((ms.get? r).getD ([], [])).2).digest, 6⟩
  | [], _, _, _, hr => absurd hr (by simp)
  | _ :: _, _, _, 0, _ => rfl
  | m :: ms, st, i, r + 1, hr => by
      have hr2 : r < ms.length := by simpa using hr
      have ih := concrete_final_take_succ thash ms
        ⟨(OuterAdapter.roundCommitted thash st i m.1 m.2).digest, 6⟩ (i + 1) r hr2
      show InstalledRoundCommit.concreteFinal thash
          ⟨(OuterAdapter.roundCommitted thash st i m.1 m.2).digest, 6⟩ (i + 1)
          (ms.take (r + 1)) = _
      rw [ih, show i + 1 + r = i + (r + 1) from by omega]
      rfl

/-- (1) **ONE ADOPTED COUPLED ROUND, AS A STEP OF `roundIncoming`.**  The digest
round `r + 1` commits onto is round `r`'s `stageFive` fold of the digest round
`r` committed onto.  No re-serialization: `round_commit_is_stage_five` is `rfl`
and `round_committed_is_the_frame_fold` says those five frames are the adopted
`InstalledRoundCommit.roundFrames`. -/
theorem round_incoming_succ (thash : Transcript.Hash) (c : Verifier.Config)
    (p : Verifier.Proof) (r : Nat) (hr : r < (roundMessages p).length) :
    roundIncoming thash c p (r + 1)
      = stageFive thash (roundIncoming thash c p r) r
          (((roundMessages p).get? r).getD ([], [])) := by
  show (InstalledRoundCommit.concreteFinal thash
      (OuterInitial.derive thash c (Verifier.statement p)).state 0
      ((roundMessages p).take (r + 1))).digest = _
  rw [concrete_final_take_succ thash (roundMessages p) _ 0 r hr, Nat.zero_add]
  exact round_commit_is_stage_five thash _ r _

/-- (1) The five frames of that step ARE the adopted
`InstalledRoundCommit.roundFrames`, spelled out: this is the adopted
`round_committed_is_the_frame_fold` at the state `roundIncoming` names. -/
theorem round_incoming_step_is_the_frame_fold (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) (r : Nat) :
    OuterAdapter.roundCommitted thash
        ⟨roundIncoming thash c p r, 6⟩ r (((roundMessages p).get? r).getD ([], [])).1
        (((roundMessages p).get? r).getD ([], [])).2
      = OuterInitial.absorbMessages thash ⟨roundIncoming thash c p r, 6⟩
          (InstalledRoundCommit.roundFrames r (((roundMessages p).get? r).getD ([], []))) :=
  InstalledRoundCommit.round_committed_is_the_frame_fold thash _ r _

/-! ## 2. THE THREADING THEOREM -/

/-- (2) **THE CHAIN MODEL IS THE RUN'S OWN COMMIT CHAIN.**  The state digest of
the chain of `BirthdayClashBound` -- from the genuinely fixed
`OuterInitial.zeroDigest`, through the adopted twenty-two-frame relation prefix
and then five frames per coupled round -- after `22 + 5 r` absorbs IS the digest
of `InstalledRoundCommit.concreteFinal` on the run's first `r` coupled messages,
started from the adopted `OuterInitial.derive` state.

This is the step the adopted module's HONESTY (iii)(b) named as missing.  The
induction is on `r`: the base is `prefix_state_is_derive_digest`, and the step is
`prefix_round_chain_step` -- five chain stages are one `stageFive` -- composed
with `round_incoming_succ`, which is `round_commit_is_stage_five` over the list
equation `concrete_final_take_succ`.  Nothing is re-serialized anywhere: every
frame in sight is an adopted `InstalledRoundCommit.roundFrames` entry or an
adopted `CommitmentOrder.gateChallengeFrames` entry. -/
theorem chain_model_is_the_run_chain (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) :
    ∀ r : Nat, r ≤ (roundMessages p).length →
      frameState L OuterInitial.zeroDigest
          (prefixRoundShape c (Verifier.statement p) (roundMessages p)) hlen (22 + 5 * r) T
        = (InstalledRoundCommit.concreteFinal (hashOf (boundedQueries L) T)
            (OuterInitial.derive (hashOf (boundedQueries L) T) c (Verifier.statement p)).state 0
            ((roundMessages p).take r)).digest := by
  intro r
  induction r with
  | zero =>
      intro _
      rw [show 22 + 5 * 0 = 22 from by omega]
      exact prefix_state_is_derive_digest L c (Verifier.statement p) (roundMessages p) hlen T
  | succ r ih =>
      intro hr
      rw [show 22 + 5 * (r + 1) = 22 + (5 * r + 5) from by omega,
        prefix_round_chain_step L c (Verifier.statement p) (roundMessages p) hlen T r,
        ih (by omega)]
      exact (round_incoming_succ (hashOf (boundedQueries L) T) c p r (by omega)).symm

/-- (2) The threading theorem, written at `BirthdayClashBound.roundIncoming` --
the same statement, since `roundIncoming` IS that `concreteFinal` digest. -/
theorem chain_model_is_the_round_incoming (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (T : OracleTable (boundedQueries L)) (r : Nat) (hr : r ≤ (roundMessages p).length) :
    frameState L OuterInitial.zeroDigest
        (prefixRoundShape c (Verifier.statement p) (roundMessages p)) hlen (22 + 5 * r) T
      = roundIncoming (hashOf (boundedQueries L) T) c p r :=
  chain_model_is_the_run_chain L c p hlen T r hr

/-- (2) **THE RUN'S SQUEEZE SOURCE IS A CHAIN STAGE.**  The digest coupled round
`r`'s two challenges are squeezed from -- the adopted
`RandomOracleSqueezes.sourceDigest` at `Draw.outerLog r`, which is entry `r` of
`InstalledRoundCommit.actualChain` -- is the chain's state digest after
`22 + (5 r + 5)` absorbs.  The indexing is the one the clash event of
`BirthdayClashBound` uses: block `r` of the run is the chain AFTER round `r`'s
five frames.  The `getD` fallback of `sourceDigest` is never taken: `r` is a
`Fin c.degreeBits` and the coupled-message list has exactly that length. -/
theorem run_round_digest_is_chain_digest (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (T : OracleTable (boundedQueries L)) (r : Fin c.degreeBits) :
    RandomOracleSqueezes.sourceDigest (hashOf (boundedQueries L) T) c p
        (JointChallengeSpace.Draw.outerLog r)
      = frameState L OuterInitial.zeroDigest
          (prefixRoundShape c (Verifier.statement p) (roundMessages p)) hlen
          (22 + (5 * r.val + 5)) T := by
  have hr : r.val < (roundMessages p).length := by rw [hmlen]; exact r.isLt
  rw [prefix_round_chain_step L c (Verifier.statement p) (roundMessages p) hlen T r.val,
    chain_model_is_the_round_incoming L c p hlen T r.val (Nat.le_of_lt hr)]
  simp only [RandomOracleSqueezes.sourceDigest, InstalledRoundCommit.actualChain]
  rw [show p.logRounds.zip p.gateRounds = roundMessages p from rfl,
    InstalledRoundCommit.concrete_chain_get (hashOf (boundedQueries L) T) _ _ 0 r.val hr,
    Option.getD_some, round_commit_is_stage_five, Nat.zero_add,
    ← round_message_get p r.val hr]
  rfl

/-- (2) The gate lane of coupled round `r` is squeezed from the SAME chain stage:
the adopted `sourceDigest` sends `Draw.outerGate r` to the same digest as
`Draw.outerLog r`. -/
theorem run_gate_round_digest_is_chain_digest (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (T : OracleTable (boundedQueries L)) (r : Fin c.degreeBits) :
    RandomOracleSqueezes.sourceDigest (hashOf (boundedQueries L) T) c p
        (JointChallengeSpace.Draw.outerGate r)
      = frameState L OuterInitial.zeroDigest
          (prefixRoundShape c (Verifier.statement p) (roundMessages p)) hlen
          (22 + (5 * r.val + 5)) T :=
  run_round_digest_is_chain_digest L c p hlen hmlen T r

/-! ## 3. THE LENGTH BUDGET -/

/-- (3) **THE TWENTY-TWO PREFIX PAYLOADS, BOUNDED.**  Thirteen of the adopted
`CommitmentOrder.gateChallengeFrames` are domain separators -- closed byte
strings, the longest `37` bytes -- four are thirty-two-byte roots, one is the
`120`-byte configuration metadata, two are the configuration's WHIR identifier
strings and two are the statement's field vectors.  Only the last four carry
lengths that are not fixed outright, and they are exactly the four arithmetic
hypotheses. -/
theorem prefix_message_payload_bound (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (hL : 181 ≤ L)
    (hcd : 69 + 8 * s.circuitDigest.length ≤ L)
    (hpi : 69 + 8 * s.publicInputs.length ≤ L)
    (hprot : 61 + c.whirProtocolId.length ≤ L)
    (hsess : 61 + c.whirSessionId.length ≤ L) :
    ∀ k, k < 22 →
      61 + (messageShape (CommitmentOrder.gateChallengeFrames c s) k).2.length ≤ L := by
  intro k hk
  have hroot : ∀ r : Verifier.Root, 61 + (OuterInitial.rootBytes r).length ≤ L := by
    intro r
    rw [OuterInitial.root_bytes_length]
    omega
  have hmeta : 61 + (OuterInitial.metadata c).length ≤ L := by
    rw [OuterInitial.metadata_has_exact_120_bytes]
    omega
  have hfcd : 61 + (Transcript.fieldVecBytes s.circuitDigest).length ≤ L := by
    rw [Transcript.field_vector_length]
    omega
  have hfpi : 61 + (Transcript.fieldVecBytes s.publicInputs).length ≤ L := by
    rw [Transcript.field_vector_length]
    omega
  have hbp : 61 + (OuterInitial.bytes c.whirProtocolId).length ≤ L := by
    rw [OuterInitial.bytes_length]
    omega
  have hbs : 61 + (OuterInitial.bytes c.whirSessionId).length ≤ L := by
    rw [OuterInitial.bytes_length]
    omega
  have hasc : ∀ str : String, (Transcript.ascii str).length ≤ 120 →
      61 + (Transcript.ascii str).length ≤ L := by
    intro str h
    omega
  interval_cases k
  · exact hasc "plonky2-mle-outer-v3" (by decide)
  · exact hasc "circuit-statement-v3" (by decide)
  · exact hfcd
  · exact hfpi
  · exact hasc "mle-whir-packed-schema-v3" (by decide)
  · exact hmeta
  · exact hasc "circuit-config-digest-v3" (by decide)
  · exact hroot c.circuitConfigDigest
  · exact hasc "whir-protocol-id-v3" (by decide)
  · exact hbp
  · exact hasc "whir-session-id-v3" (by decide)
  · exact hbs
  · exact hasc "pcs-group-preprocessed-v3" (by decide)
  · exact hroot s.preprocessedRoot
  · exact hasc "pcs-group-witness-v3" (by decide)
  · exact hroot s.witnessRoot
  · exact hasc "public-input-aggregation-challenge-v3" (by decide)
  · exact hasc "norm-denominator-challenges-v3" (by decide)
  · exact hasc "pcs-group-norm-inverse-v3" (by decide)
  · exact hroot s.normInverseRoot
  · exact hasc "public-input-mix-challenge-v3" (by decide)
  · exact hasc "outer-relation-challenges-v3" (by decide)

/-- **EVERY SIDE CONDITION THE CHAIN NEEDS, IN ONE PREDICATE.**  The query set
`boundedQueries L` has to answer every frame of the run's chain: the five frames
of each coupled round -- whose message cells are `8 + 24 * length` bytes, so a
degree bound fixes them -- and the twenty-two relation-prefix frames, four of
which carry statement and configuration data.  `189 + 24 * quotientDegree <= L`
is the adopted envelope budget of
`BirthdayClashBound.round_shape_payload_bound_at_envelope`; it also covers the
`64` bytes of a squeeze input and the `181` bytes of the widest fixed prefix
frame. -/
def LengthBudget (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree : Nat) : Prop :=
  189 + 24 * quotientDegree ≤ L ∧
  69 + 8 * (Verifier.statement p).circuitDigest.length ≤ L ∧
  69 + 8 * (Verifier.statement p).publicInputs.length ≤ L ∧
  61 + c.whirProtocolId.length ≤ L ∧
  61 + c.whirSessionId.length ≤ L ∧
  (∀ i, (((roundMessages p).get? i).getD ([], [])).1.length ≤ 5) ∧
  (∀ i, (((roundMessages p).get? i).getD ([], [])).2.length ≤ quotientDegree + 2)

/-- (3) The budget clears the adopted `QueryClosure` threshold of `64` bytes. -/
theorem length_budget_queries (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree : Nat) (h : LengthBudget L c p quotientDegree) : 64 ≤ L := by
  obtain ⟨h1, -⟩ := h
  omega

/-- (3) The budget clears the `61` bytes of framing, so `boundedQueries L` is not
frame-free. -/
theorem length_budget_frames (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree : Nat) (h : LengthBudget L c p quotientDegree) : 61 ≤ L := by
  obtain ⟨h1, -⟩ := h
  omega

/-- (3) **THE BUDGET DISCHARGES THE CHAIN'S LENGTH HYPOTHESIS.**  This is the
`hlen` argument of every chain theorem of `BirthdayClashBound`, produced from the
predicate above. -/
theorem length_budget_chain (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree : Nat) (h : LengthBudget L c p quotientDegree) :
    ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine prefix_round_shape_payload_bound L c (Verifier.statement p) (roundMessages p) ?_ ?_
  · exact prefix_message_payload_bound L c (Verifier.statement p) (by omega) h2 h3 h4 h5
  · exact round_shape_payload_bound_at_envelope L (roundMessages p) quotientDegree h6 h7 h1

/-! ## 4. THE DISCHARGE -/

/-- (4) **THE RUN'S CLASH EVENT IS THE CHAIN MODEL'S CLASH EVENT.**  Not an
inclusion: the two finsets are EQUAL.  Left to right, a clash of the adopted
`RandomOracleSqueezes.RoundDigestClash` names two rounds of this run whose
`sourceDigest`s agree, and `run_round_digest_is_chain_digest` turns each into a
chain stage; right to left, two chain stages `22 + (5 r + 5)` and
`22 + (5 t + 5)` with `r < t < degreeBits` name two `Fin c.degreeBits` rounds
whose `sourceDigest`s agree.  This is the identification the adopted module's
section 9 said was missing. -/
theorem run_round_digest_clash_event_is_prefix_round_clash (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) :
    clashEvent (boundedQueries L) c p
      = prefixRoundDigestClashEvent L c (Verifier.statement p) (roundMessages p) hlen
          c.degreeBits := by
  ext T
  simp only [clashEvent, prefixRoundDigestClashEvent, RandomOracleSqueezes.RoundDigestClash,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, s, hrs, heq⟩
    rw [run_round_digest_is_chain_digest L c p hlen hmlen T r,
      run_round_digest_is_chain_digest L c p hlen hmlen T s] at heq
    rcases Nat.lt_trichotomy r.val s.val with h | h | h
    · exact ⟨r.val, s.val, h, s.isLt, heq⟩
    · exact absurd (Fin.ext h) hrs
    · exact ⟨s.val, r.val, h, r.isLt, heq.symm⟩
  · rintro ⟨r, t, hrt, htd, heq⟩
    refine ⟨⟨r, Nat.lt_trans hrt htd⟩, ⟨t, htd⟩, ?_, ?_⟩
    · intro hcon
      exact absurd (congrArg Fin.val hcon) (Nat.ne_of_lt hrt)
    · rw [run_round_digest_is_chain_digest L c p hlen hmlen T ⟨r, Nat.lt_trans hrt htd⟩,
        run_round_digest_is_chain_digest L c p hlen hmlen T ⟨t, htd⟩]
      exact heq

/-- (4) **THE BIRTHDAY BOUND, ON THE RUN'S OWN CLASH EVENT.**  The hypothesis
`hclash` of the adopted `run_bad_draw_probability_le_of_clash_bound` is now a
theorem, with `eps` the chain's own birthday count over the block space. -/
theorem run_clash_probability_le (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) :
    oracleProbability (boundedQueries L) (clashEvent (boundedQueries L) c p)
      ≤ ((22 + 5 * c.degreeBits : Nat) : ℚ) * (((22 + 5 * c.degreeBits : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) := by
  rw [run_round_digest_clash_event_is_prefix_round_clash L c p hlen hmlen]
  exact prefix_round_digest_clash_mass_le L c (Verifier.statement p) (roundMessages p) hlen
    c.degreeBits

/-- (4) The same bound from the length budget alone. -/
theorem run_clash_probability_le_of_budget (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree : Nat) (hb : LengthBudget L c p quotientDegree)
    (hmlen : (roundMessages p).length = c.degreeBits) :
    oracleProbability (boundedQueries L) (clashEvent (boundedQueries L) c p)
      ≤ ((22 + 5 * c.degreeBits : Nat) : ℚ) * (((22 + 5 * c.degreeBits : Nat) : ℚ) + 1) / 2
        / (Fintype.card Block : ℚ) :=
  run_clash_probability_le L c p (length_budget_chain L c p quotientDegree hb) hmlen

/-- (4) **AT THE ENVELOPE'S `degreeBits = 13`**: the eighty-seven stages of the
whole chain give `3828 / |Block|`. -/
theorem run_clash_probability_at_thirteen (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) (hd : c.degreeBits = 13) :
    oracleProbability (boundedQueries L) (clashEvent (boundedQueries L) c p)
      ≤ 3828 / (Fintype.card Block : ℚ) := by
  rw [run_round_digest_clash_event_is_prefix_round_clash L c p hlen hmlen, hd]
  exact prefix_round_digest_clash_mass_at_thirteen L c (Verifier.statement p) (roundMessages p)
    hlen

/-! ## 5. THE RUN-LEVEL BOUND, WITH NO CLASH HYPOTHESIS, FOR A FIXED
(NON-ADAPTIVE) PROVER UNDER THE RANDOM ORACLE MODEL -/

/-- (5) **THE FIRST FULLY DISCHARGED RUN-LEVEL RANDOM-ORACLE BOUND, FOR A FIXED
(NON-ADAPTIVE) PROVER UNDER THE RANDOM ORACLE MODEL.**  The
adopted `run_bad_draw_probability_le_of_clash_bound` carries a hypothesis `eps`
bounding the clash mass, and the adopted module can only satisfy it at
`eps = 1`.  Here `eps` is the chain's own birthday count, so the conclusion is a
bound with NO probabilistic side condition, for a fixed (non-adaptive) prover
under the random oracle model: the query set is
`boundedQueries L`, the closure hypothesis is `bounded_queries_closed`, and the
clash term is `run_clash_probability_le_of_budget`.

Read HONESTY (i) and (ii) in the header before quoting the number: this is the
random oracle model, and the prover is fixed. -/
theorem run_bad_draw_probability_le_birthday (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree constraints : Nat)
    (hb : LengthBudget L c p quotientDegree)
    (hmlen : (roundMessages p).length = c.degreeBits) (hdb : c.degreeBits ≤ 13)
    (logCompare gateCompare : GoldilocksExt3Field.Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound)
    (g : Nat → GoldilocksExt3Field.Element)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element)
    (hlogLen : logLane.length = c.degreeBits) (hgateLen : gateLane.length = c.degreeBits)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L) (RandomOracleSqueezes.runDrawEvent (boundedQueries L) c p
        (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane g
          (2 ^ c.degreeBits) coeffsOf))
      ≤ ChallengeUnionBound.combinedBound c.degreeBits quotientDegree c.degreeBits constraints
        + ((22 + 5 * c.degreeBits : Nat) : ℚ) * (((22 + 5 * c.degreeBits : Nat) : ℚ) + 1) / 2
          / (Fintype.card Block : ℚ) :=
  run_bad_draw_probability_le_of_clash_bound (boundedQueries L) c p
    (bounded_queries_closed L c.degreeBits (length_budget_queries L c p quotientDegree hb)) hdb
    _ (run_clash_probability_le_of_budget L c p quotientDegree hb hmlen)
    quotientDegree constraints logCompare gateCompare logLane gateLane g coeffsOf
    hlogLen hgateLen hlogDeg hgateDeg hclen

/-- (5) **THE NUMERIC COROLLARY AT THE ENVELOPE.**  `degreeBits = 13`,
`quotientDegree = 8` -- the deployed close envelope -- and the adopted
`numGateConstraints` ceiling `123`: the additive term is `3828 / |Block|`, the
birthday count of the eighty-seven-stage chain. -/
theorem run_bad_draw_probability_le_birthday_at_thirteen (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hb : LengthBudget L c p 8)
    (hmlen : (roundMessages p).length = c.degreeBits) (hd : c.degreeBits = 13)
    (logCompare gateCompare : GoldilocksExt3Field.Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound)
    (g : Nat → GoldilocksExt3Field.Element)
    (coeffsOf : Nat → List GoldilocksExt3Field.Element)
    (hlogLen : logLane.length = c.degreeBits) (hgateLen : gateLane.length = c.degreeBits)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ 10 ∧ r.truth.length ≤ 10)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ 123) :
    oracleProbability (boundedQueries L) (RandomOracleSqueezes.runDrawEvent (boundedQueries L) c p
        (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane g
          (2 ^ c.degreeBits) coeffsOf))
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) := by
  refine le_trans (run_bad_draw_probability_le_birthday L c p 8 123 hb hmlen (by omega)
    logCompare gateCompare logLane gateLane g coeffsOf hlogLen hgateLen hlogDeg hgateDeg
    hclen) ?_
  rw [hd, show ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2 = 3828 from by
    norm_num]

/-- (5) `3828 * 2 ^ 244` fits inside the block space: `3828 < 2 ^ 12` and
`|Block| = 256 ^ 32 = 2 ^ 256` by the adopted `block_card`.  The cardinal is
never evaluated -- only `Nat` power laws are used. -/
theorem block_card_ge_birthday_scale : 3828 * 2 ^ 244 ≤ Fintype.card Block := by
  have hb : (256 : Nat) = 2 ^ 8 := by norm_num
  have hp : (256 : Nat) ^ 32 = 2 ^ 256 := by
    conv_lhs => rw [hb]
    rw [← pow_mul]
  rw [block_card, hp]
  calc (3828 : Nat) * 2 ^ 244 ≤ 2 ^ 12 * 2 ^ 244 := Nat.mul_le_mul (by norm_num) (Nat.le_refl _)
    _ = 2 ^ 256 := by rw [← pow_add]

/-- (5) **THE BIRTHDAY TERM, SYMBOLICALLY.**  `3828 / |Block| <= 2 ^ (-244)`,
written as `1 / 2 ^ 244`.  This is a statement about the chain model under the
random-oracle counting law -- see HONESTY (i): it is NOT a claim about keccak,
and it is NOT the system's soundness error. -/
theorem birthday_term_le_two_pow_neg :
    (3828 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 244 := by
  rw [div_le_div_iff block_card_cast_pos (by positivity), one_mul]
  exact_mod_cast block_card_ge_birthday_scale

/-! ## 6. SATISFIABILITY AT `degreeBits = 13` -/

/-- The adopted `Verifier.testConfig` with the envelope's `degreeBits`. -/
def budgetConfig : Verifier.Config := { Verifier.testConfig with degreeBits := 13 }

/-- One coupled round of the adopted `Verifier.testProof` shape: a five-coefficient
log message and a three-coefficient gate message. -/
def budgetRound : Verifier.CoupledMessage :=
  (List.replicate 5 Verifier.zero, List.replicate 3 Verifier.zero)

/-- The adopted `Verifier.testProof` with thirteen coupled rounds of that shape. -/
def budgetProof : Verifier.Proof :=
  { Verifier.testProof with
      logRounds := List.replicate 13 (List.replicate 5 Verifier.zero),
      gateRounds := List.replicate 13 (List.replicate 3 Verifier.zero) }

theorem zip_replicate (a b : List Verifier.Ext3) :
    ∀ n : Nat, (List.replicate n a).zip (List.replicate n b) = List.replicate n (a, b)
  | 0 => rfl
  | n + 1 => by
      show (a, b) :: (List.replicate n a).zip (List.replicate n b) = _
      rw [zip_replicate a b n]
      rfl

theorem budget_round_messages :
    roundMessages budgetProof = List.replicate 13 budgetRound :=
  zip_replicate _ _ 13

theorem replicate_get_d (x : Verifier.CoupledMessage) :
    ∀ n i : Nat, ((List.replicate n x).get? i).getD ([], []) = x
      ∨ ((List.replicate n x).get? i).getD ([], []) = ([], [])
  | 0, _ => Or.inr rfl
  | _ + 1, 0 => Or.inl rfl
  | n + 1, i + 1 => replicate_get_d x n i

theorem budget_round_count : (roundMessages budgetProof).length = budgetConfig.degreeBits := by
  rw [budget_round_messages]
  rfl

/-- (6) **THE LENGTH BUDGET IS SATISFIABLE, AT A CLOSED WITNESS.**  `L = 381` is
`189 + 24 * 8`, the envelope budget at `quotientDegree = 8`; the config is the
adopted `Verifier.testConfig` at `degreeBits = 13` and the proof the adopted
`Verifier.testProof` with thirteen coupled rounds.  No hypothesis is left: every
conjunct is a closed arithmetic fact about lists whose lengths are fixed. -/
theorem length_budget_at_envelope : LengthBudget 381 budgetConfig budgetProof 8 := by
  refine ⟨by norm_num, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro i
    rw [budget_round_messages]
    rcases replicate_get_d budgetRound 13 i with h | h <;> rw [h]
    · decide
    · decide
  · intro i
    rw [budget_round_messages]
    rcases replicate_get_d budgetRound 13 i with h | h <;> rw [h]
    · decide
    · decide

/-- (6) The witness, with the two side conditions the run-level bound also needs:
the coupled-message list has exactly `degreeBits` entries, and `degreeBits` is
the envelope's `13`. -/
theorem length_budget_is_satisfiable_at_thirteen :
    LengthBudget 381 budgetConfig budgetProof 8
      ∧ (roundMessages budgetProof).length = budgetConfig.degreeBits
      ∧ budgetConfig.degreeBits = 13 :=
  ⟨length_budget_at_envelope, budget_round_count, rfl⟩

/-- (6) **THE RUN-LEVEL BOUND WITH EVERY HYPOTHESIS DISCHARGED.**  The query set,
the config, the proof, the length budget and the lane shapes are all concrete --
the lanes are the adopted `RandomOracleSqueezes.trivialLane`, the same closed
witness that module uses.  Only the field element `x` is a parameter, exactly as
in the adopted `bad_draw_bound_at_thirteen_closed`.  This is an inequality
between a mass on oracle tables and a number, with no side condition at all. -/
theorem run_bad_draw_probability_le_birthday_closed (x : GoldilocksExt3Field.Element) :
    oracleProbability (boundedQueries 381)
        (RandomOracleSqueezes.runDrawEvent (boundedQueries 381) budgetConfig budgetProof
          (JointChallengeSpace.jointBadEvent budgetConfig.degreeBits x x
            (trivialLane x) (trivialLane x) (fun _ => x) (2 ^ budgetConfig.degreeBits)
            (fun _ => [])))
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) :=
  run_bad_draw_probability_le_birthday_at_thirteen 381 budgetConfig budgetProof
    length_budget_at_envelope budget_round_count rfl x x (trivialLane x) (trivialLane x)
    (fun _ => x) (fun _ => []) (trivial_lane_length x) (trivial_lane_length x)
    (trivial_lane_deg x 5) (trivial_lane_deg x 10) (fun _ _ => Nat.zero_le _)

/-- (6) **THE CLOSED BOUND IS A NON-TRIVIAL NUMBER.**  The right-hand side of
`run_bad_draw_probability_le_birthday_closed` is strictly below `1`: the adopted
`ChallengeUnionBound.combined_bound_at_extremes_numeric` puts the `combinedBound`
term at most `2 ^ (-172)` and `birthday_term_le_two_pow_neg` puts the birthday
term at most `2 ^ (-244)`, and those two powers sum to less than `1` by rational
arithmetic.  `Fintype.card Block` is never evaluated -- it enters only through
the existing lemma.

Read HONESTY (i) and (iv) before quoting this: it says the bound is not the
vacuous `<= 1`, NOT that the protocol has this soundness error. -/
theorem closed_bound_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 3828 / (Fintype.card Block : ℚ) < 1 := by
  have hcomb : ChallengeUnionBound.combinedBound 13 8 13 123 ≤ (1 : ℚ) / 2 ^ 172 :=
    ChallengeUnionBound.combined_bound_at_extremes_numeric
  have hbirth : (3828 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 244 :=
    birthday_term_le_two_pow_neg
  have hsum : (1 : ℚ) / 2 ^ 172 + 1 / 2 ^ 244 < 1 := by norm_num
  linarith

/-! ## 7. NON-VACUITY -/

theorem prefix_round_clash_event_mono (L : Nat) (c : Verifier.Config) (s : Verifier.Statement)
    (ms : List Verifier.CoupledMessage)
    (hlen : ∀ k, 61 + (prefixRoundShape c s ms k).2.length ≤ L) (d e : Nat) (hde : d ≤ e) :
    prefixRoundDigestClashEvent L c s ms hlen d ⊆ prefixRoundDigestClashEvent L c s ms hlen e := by
  intro T hT
  simp only [prefixRoundDigestClashEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
  obtain ⟨r, t, hrt, htd, heq⟩ := hT
  exact ⟨r, t, hrt, Nat.lt_of_lt_of_le htd hde, heq⟩

/-- (7) **THE BOUND IS NOT PROVED ON AN EMPTY EVENT.**  The constant table -- the
one whose every answer is `OuterInitial.zeroDigest` -- IS in the run's clash
event, at every `degreeBits` of at least two.  The adopted
`constant_table_in_prefix_round_clash_event` says this for the chain model, and
section 4 says the two events are the same finset. -/
theorem constant_table_in_run_clash_event (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) (hd : 2 ≤ c.degreeBits) :
    constantTable L ∈ clashEvent (boundedQueries L) c p := by
  rw [run_round_digest_clash_event_is_prefix_round_clash L c p hlen hmlen]
  exact prefix_round_clash_event_mono L c (Verifier.statement p) (roundMessages p) hlen 2
    c.degreeBits hd
    (constant_table_in_prefix_round_clash_event L c (Verifier.statement p) (roundMessages p) hlen)

theorem run_clash_event_nonempty (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlen : ∀ k,
      61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) (hd : 2 ≤ c.degreeBits) :
    (clashEvent (boundedQueries L) c p).Nonempty :=
  ⟨constantTable L, constant_table_in_run_clash_event L c p hlen hmlen hd⟩

/-- (7) **THE ADOPTED TRIVIALITY DOES NOT APPLY HERE.**  The adopted
`RandomOracleSqueezes.run_bound_trivial_at_frame_free` reaches the same SHAPE of
conclusion with the additive term equal to `1`, on any frame-free query set.
`boundedQueries L` is not frame-free once `L` clears the `61` bytes of framing,
which the length budget forces -- so the bound of section 5 is not that
triviality. -/
theorem budget_query_set_is_not_frame_free (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree : Nat) (hb : LengthBudget L c p quotientDegree) :
    ¬ RandomOracleSqueezes.FrameFree (boundedQueries L) :=
  bounded_queries_not_frame_free L (length_budget_frames L c p quotientDegree hb)

/-- (7) And the additive term is not `1` either: the chain's birthday mass at the
envelope is strictly below `1`, by the adopted
`prefix_round_digest_clash_bound_lt_one`. -/
theorem birthday_term_lt_one : (3828 : ℚ) / (Fintype.card Block : ℚ) < 1 :=
  prefix_round_digest_clash_bound_lt_one

end Audit.Wire3.ConcreteChainThreading
