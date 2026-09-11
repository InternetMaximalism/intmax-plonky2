import Audit.Wire3.ConcreteChainThreading
import Audit.Wire3.IndexLanesOracle
import Audit.Wire3.SoundnessAssembly

/-!
# `Audit.Wire3.RunLevelUnionBound` — the run-level union bound under ONE oracle law

**WHAT THIS MODULE ADDS.**  `ConcreteChainThreading` (CCT) identifies the
`BirthdayClashBound` chain model with the run's own commit chain, and
`IndexLanesOracle` (ILO) puts the index lanes and the outer/gate lanes on ONE
random-oracle table — but only at FIXED digests, and only after assuming a
chain-model hypothesis `hst` about the post-rounds snapshot.  Here

* `hst` is DISCHARGED (section 1): the extended chain's stage `22 + 5 d + 8`
  digest IS the run's own index digest, the one
  `SoundnessAssembly.actualIndexDraw` squeezes from;
* the frame-fibre Fubini of `RandomOracleSqueezes.run_draw_probability_le_fibrewise`
  is re-run ONCE for the PAIR of families (section 2), so the outer/gate lanes
  and the index lanes are weighed as ONE union under ONE law, with ONE additive
  chain term;
* the explicit engine's assembly (section 4) is placed against that union: the
  tables on which the adopted `SoundnessAssembly.explicit_good_draw_assembly`
  conclusion can fail are contained in it.

## HONESTY — read before quoting anything below

1. **RANDOM ORACLE MODEL, NOT KECCAK.**  The law is the uniform counting measure
   on `RandomOracleSqueezes.OracleTable (BirthdayClashBound.boundedQueries L)`:
   one independent uniform block per byte string of length at most `L`.  Nothing
   here is a statement about the deployed permutation, no reduction to any
   keccak assumption is claimed, and no keccak cryptanalysis is cited.
2. **FIXED (NON-ADAPTIVE) PROVER.**  `p : Verifier.Proof` and `p.used` are
   quantified OUTSIDE the law: the prover's round messages and used claims are
   fixed before the table `T` is sampled.  In the deployed protocol the prover
   chooses round `r + 1` after seeing round `r`'s challenges, so an **adaptive
   prover is NOT covered**, here or anywhere in this tree.  Every "discharged"
   headline below is discharged *for a fixed (non-adaptive) prover under the
   random oracle model* — that qualification is part of the claim, not a caveat
   bolted on afterwards.
3. **SCOPE: OUTER SUMCHECK + INDEX LANES ONLY.**  The twenty-two relation-prefix
   frames, five frames per coupled round, and the eight used-claim frames.  WHIR
   folding and Merkle openings are EXCLUDED, exactly as the adopted
   `ChallengeUnionBound.combinedBound` excludes them.
4. **THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.**  They bound two named
   additive families of one named draw event.  The deployed profile's design
   point is about a hundred bits and the dominant terms are the excluded
   WHIR/Merkle ones; quoting `combinedBound + 2 * tauTerm + chain term` as the
   wire-v3 soundness error would be wrong by a wide margin.  **No sentence in
   this module says soundness is proved.**
5. **WHAT THE ASSEMBLY CONCLUSION IS.**  Section 4 does not say the circuit is
   true.  It says: off the union bad event, the adopted
   `SoundnessAssembly.explicit_good_draw_assembly` conclusion holds — good-draw
   conditional constraint vanishing at every row, the cell identification, the
   pinned WHIR parameters, and the `core c = core c₀` / `KhashCollision`
   disjunction.  **Residue R1b is still assumed inside `AssemblyResidue`** and is
   not discharged here.
6. **ITEM 3 DELIVERS THE INCLUSION; ITS MASS BOUND IS NOT DELIVERED.**  Section
   4.2's `assembly_failure_subset_run_union` is unconditional: the tables on
   which the adopted `SoundnessAssembly.explicit_good_draw_assembly` conclusion
   can fail lie inside the HASH-INDEXED `runUnionBadEventAt`.  **No mass bound
   for that set is proved here**, and no theorem in this module assumes one.
   The reason is stated in full in section 4.3 and is worth stating here too:
   the naive bridge would need a COVER — ONE fixed `jointBadEvent` dominating
   the engine's gate-lane bad set at EVERY hash, and ONE fixed
   `guardedIndexBadEvent` dominating the engine's committed cell family at
   EVERY hash — and that cover is not known to be satisfiable at any
   non-degenerate run (it holds only degenerately, e.g. at empty bad sets or at
   the adopted `trivialLane`).  Per this tree's vacuity policy a theorem whose
   hypothesis is not known to be satisfiable does not ship, so the cover
   statement and the mass corollary that used it have been REMOVED.

   **THE GAP IS NOT ADAPTIVITY.**  At a FIXED prover the hash enters
   `SoundnessAssembly.outerBadEvent` only through the single gate alpha
   coordinate `TranscriptProvenance.gateAlphaElement thash c p` (one coordinate
   of the very draw being weighed), and it enters
   `SoundnessAssembly.indexBadEvent` only through the outer row point
   `OpenedClaimFold.cellRow (Verifier.derivedRounds … c p)` — the SUPPLIED
   cells are independent of the index draw altogether.  What is missing is a
   TWO-STAGE CONDITIONAL COUNT for that fixed prover, not an adaptive-prover
   treatment; section 4.3 states it as the follow-up module's contract.
7. **CHAIN-MODEL RESIDUE, INHERITED.**  `IndexLanesOracle.extendedDigestClashEvent`
   is an event about the chain's stage digests.  The identification of those
   stages with the run's own digests is CCT's and ILO's, and is used here; the
   residue that `BirthdayClashBound`'s own section 9 discloses is unchanged.
8. **ITEM 1'S `hlenI` COSTS MORE THAN CCT'S `LengthBudget`.**
   `length_budget_extended_chain` (section 3) needs, BEYOND
   `ConcreteChainThreading.LengthBudget`, five per-claim width bounds
   (`p.used.logPreprocessed`, `logWitness`, `logNormInverse`,
   `gatePreprocessed`, `gateWitness`, each of length at most `W`) and the frame
   budget `69 + 24 * W ≤ L`.  At the closed witness's `L = 381` that budget
   allows only `W ≤ 13`, i.e. claims of width at most thirteen.  The DEPLOYED
   profile's `indexBits = 8` claims can be two hundred fifty-six wide, and such
   a run needs ILO's own `L = 8192` envelope, not this module's `L = 381`.
   The closed instance of section 3 is therefore a witness that the hypotheses
   are simultaneously satisfiable, NOT the deployed configuration.
9. **THE CLOSED WITNESS'S INDEX HALF IS EMPTY.**  At the closed instance the
   index event is `IndexLanesOracle.guardedIndexBadEvent 8 [] []`, and the
   guard `IndexPointZeroCheck.CellsDifferOnCube 8 [] []` is false, so that
   event is `∅`.  So `run_union_good_table_exists_at_the_envelope` (section 5)
   certifies that the closed bound is DISCHARGEABLE — a table outside the union
   bad event exists — and does NOT certify any non-trivial index mass.
-/

namespace Audit.Wire3.RunLevelUnionBound

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound

/-! ## 0. The frame half determines every chain stage -/

/-- Two tables that agree on the FRAME half of `boundedQueries L` answer every
`Transcript.frame` query alike.  `RandomOracleSqueezes.frame_not_shaped` is the
whole content: a frame is never `ChallengeShaped`. -/
theorem hash_of_frame_congr (L : Nat) (T1 T2 : OracleTable (boundedQueries L))
    (h : ∀ a : FrameHalf (boundedQueries L), T1 a.val = T2 a.val)
    (e : Transcript.Digest) (t : Transcript.Byte) (pl : Transcript.Bytes) :
    hashOf (boundedQueries L) T1 (Transcript.frame e t pl)
      = hashOf (boundedQueries L) T2 (Transcript.frame e t pl) := by
  by_cases hm : Transcript.frame e t pl ∈ boundedQueries L
  · have h1 := h ⟨⟨Transcript.frame e t pl, hm⟩, frame_not_shaped e t pl⟩
    simp only [hashOf, hm, dif_pos, h1]
  · simp only [hashOf, hm, dif_neg, not_false_iff]

/-- (0) **EVERY CHAIN STAGE IS A FUNCTION OF THE FRAME HALF ALONE.**  The chain
absorbs only `Transcript.frame` strings, so its stage digests do not move when
the challenge half of the table is changed.  This is the index twin of the
adopted `RandomOracleSqueezes.source_digest_congr`, and it is what makes the
index digest constant inside one fibre of `frameSplit`. -/
theorem frame_state_frame_congr (L : Nat) (e0 : Transcript.Digest)
    (shape : Nat → Transcript.Byte × Transcript.Bytes)
    (hlen : ∀ k, 61 + (shape k).2.length ≤ L)
    (T1 T2 : OracleTable (boundedQueries L))
    (h : ∀ a : FrameHalf (boundedQueries L), T1 a.val = T2 a.val) :
    ∀ k, frameState L e0 shape hlen k T1 = frameState L e0 shape hlen k T2 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [frame_state_is_hash, frame_state_is_hash, ih]
      exact hash_of_frame_congr L T1 T2 h _ _ _

/-! ## 1. The extended chain's last stage IS the run's own index digest -/

/-- The transcript state the run ends the coupled rounds in: the adopted
`InstalledRoundCommit.concreteFinal` over ALL of the run's coupled messages.
This is exactly the snapshot the adopted `SoundnessAssembly.actualIndexDraw`
and `InstalledIndexSampler.indexDigest` are applied to. -/
def runIndexState (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    Transcript.State :=
  InstalledRoundCommit.concreteFinal thash
    (OuterInitial.derive thash c (Verifier.statement p)).state 0 (roundMessages p)

/-- The run's own index digest: the adopted `InstalledIndexSampler.indexDigest`
at that snapshot and at the run's own used claims. -/
def runIndexDigest (thash : Transcript.Hash) (c : Verifier.Config) (p : Verifier.Proof) :
    Transcript.Digest :=
  InstalledIndexSampler.indexDigest thash (runIndexState thash c p) p.used

/-- (1) The adopted `SoundnessAssembly.actualIndexDraw` IS the adopted
`InstalledIndexSampler.actualIndexDraw` at `runIndexDigest`.  Definitional: this
module re-serializes nothing. -/
theorem assembly_index_draw_is_at_run_index_digest (thash : Transcript.Hash)
    (c : Verifier.Config) (p : Verifier.Proof) :
    SoundnessAssembly.actualIndexDraw thash c p
      = InstalledIndexSampler.actualIndexDraw thash (runIndexDigest thash c p) c.indexBits :=
  rfl

/-- (1) **`hst` IS DISCHARGED, for a fixed (non-adaptive) prover under the random
oracle model.**  Stage `22 + 5 d + 8` of ILO's extended chain is the RUN'S OWN
index digest — the digest `SoundnessAssembly.actualIndexDraw` squeezes the index
lanes from — with no chain-model hypothesis left.

Route, all three steps adopted or staged: CCT's `chain_model_is_the_run_chain` at
`r = d` (with `hmlen`, so `List.take` is the identity) identifies stage
`22 + 5 d` of the `prefixRoundShape` chain with the `concreteFinal` snapshot's
digest; ILO's `extended_prefix_agrees` at `k = 22 + 5 d` carries that onto the
EXTENDED chain; ILO's `index_state_is_index_digest` then folds the eight adopted
claim frames onto it.

The two length side conditions are explicit and are exactly the two shapes'
payload budgets: `hlenP` is CCT's `length_budget_chain`, `hlenI` is ILO's
`prefix_round_index_shape_payload_bound`.  Section 3 discharges both at a closed
witness. -/
theorem extended_chain_index_digest_is_the_run_index_digest (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (T : OracleTable (boundedQueries L)) :
    frameState L OuterInitial.zeroDigest
        (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p) (roundMessages p)
          p.used c.degreeBits) hlenI (22 + 5 * c.degreeBits + 8) T
      = runIndexDigest (hashOf (boundedQueries L) T) c p := by
  refine IndexLanesOracle.index_state_is_index_digest L c (Verifier.statement p)
    (roundMessages p) p.used c.degreeBits hlenI T
    (runIndexState (hashOf (boundedQueries L) T) c p) ?_
  rw [IndexLanesOracle.extended_prefix_agrees L c (Verifier.statement p) (roundMessages p)
      p.used c.degreeBits hlenI hlenP T (22 + 5 * c.degreeBits) (Nat.le_refl _),
    ConcreteChainThreading.chain_model_is_the_run_chain L c p hlenP T c.degreeBits
      (Nat.le_of_eq hmlen.symm)]
  rw [runIndexState, ← hmlen, List.take_length]


/-! ## 2. The run-level union: ONE event, ONE law

The two families are weighed together.  `runUnionBadEvent` is a single
`Finset (OracleTable (boundedQueries L))`; the fibre-fibre Fubini of the adopted
`RandomOracleSqueezes.run_draw_probability_le_fibrewise` is re-run for the PAIR,
so there is ONE additive chain term rather than two. -/

/-- The run's COMBINED schedule of oracle inputs: the `3 * (3 d + 1)` outer/gate
squeeze inputs at the run's own block digests, and the `6 * indexBits` index
squeeze inputs at the run's own index digest, as ONE family on a sum type. -/
def runCombinedSchedule (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (T : OracleTable (boundedQueries L)) :
    (JointChallengeSpace.Draw c.degreeBits × Fin 3)
      ⊕ (InstalledIndexSampler.IndexDraw c.indexBits × Fin 3) → Transcript.Bytes
  | Sum.inl kj =>
      squeezeInputAt c.degreeBits (sourceDigest (hashOf (boundedQueries L) T) c p) kj.1 kj.2
  | Sum.inr kj =>
      IndexLanesOracle.indexSqueezeInputAt c.indexBits
        (runIndexDigest (hashOf (boundedQueries L) T) c p) kj.1 kj.2

theorem run_combined_schedule_inl (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (T : OracleTable (boundedQueries L)) (x : JointChallengeSpace.Draw c.degreeBits × Fin 3) :
    runCombinedSchedule L c p T (Sum.inl x)
      = squeezeInputAt c.degreeBits (sourceDigest (hashOf (boundedQueries L) T) c p) x.1 x.2 :=
  rfl

theorem run_combined_schedule_inr (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (T : OracleTable (boundedQueries L))
    (y : InstalledIndexSampler.IndexDraw c.indexBits × Fin 3) :
    runCombinedSchedule L c p T (Sum.inr y)
      = IndexLanesOracle.indexSqueezeInputAt c.indexBits
          (runIndexDigest (hashOf (boundedQueries L) T) c p) y.1 y.2 :=
  rfl

open Classical in
/-- The exceptional event of the Fubini: the run's combined schedule of oracle
inputs is not injective.  The index twin of the adopted
`RandomOracleSqueezes.scheduleNonInjectiveEvent`, enlarged to both families. -/
noncomputable def runCombinedNonInjectiveEvent (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ¬ Function.Injective (runCombinedSchedule L c p T))

/-- (2) **THE WHOLE COMBINED FAMILY IS PAIRWISE DISTINCT OFF THE EXTENDED
CLASH.**  All three ingredients of ILO's `combined_schedule_injective` are
supplied from the chain: the joint family's own injectivity from the adopted
`squeeze_inputs_distinct_or_round_digest_clash` against disjunct (1) (through
CCT's `run_round_digest_clash_event_is_prefix_round_clash`), the index family's
own injectivity from ILO's `index_schedule_index_injective`, and the CROSS
distinctness `e ≠ dig k` from disjuncts (2) and (3), read at the run's own
digests through section 1.

`hne` is where section 1 is indispensable: without
`extended_chain_index_digest_is_the_run_index_digest` the index digest is not
known to be a chain stage at all. -/
theorem run_combined_schedule_injective_off_clash (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hL : 64 ≤ L) (hdb : c.degreeBits ≤ 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (T : OracleTable (boundedQueries L))
    (hT : T ∉ IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits hlenI) :
    Function.Injective (runCombinedSchedule L c p T) := by
  classical
  have hstage := extended_chain_index_digest_is_the_run_index_digest L c p hlenI hlenP hmlen T
  simp only [IndexLanesOracle.extendedDigestClashEvent, Finset.mem_filter, Finset.mem_univ,
    true_and] at hT
  -- (a) the joint family's own injectivity, from disjunct (1)
  have hJ : Function.Injective (squeezeIndex (hashOf (boundedQueries L) T) c p) := by
    by_contra hcon
    have hmem : T ∈ scheduleNonInjectiveEvent (boundedQueries L) c p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩
    have hcl := schedule_non_injective_subset_clash (boundedQueries L) c p hdb hmem
    rw [ConcreteChainThreading.run_round_digest_clash_event_is_prefix_round_clash L c p
      hlenP hmlen] at hcl
    obtain ⟨r, t, hrt, htd, heq⟩ :=
      (Finset.mem_filter.mp (by simpa only [prefixRoundDigestClashEvent] using hcl)).2
    refine hT (Or.inl ⟨r, t, hrt, htd, ?_⟩)
    rw [IndexLanesOracle.extended_prefix_agrees L c (Verifier.statement p) (roundMessages p)
        p.used c.degreeBits hlenI hlenP T (22 + (5 * r + 5)) (by omega),
      IndexLanesOracle.extended_prefix_agrees L c (Verifier.statement p) (roundMessages p)
        p.used c.degreeBits hlenI hlenP T (22 + (5 * t + 5)) (by omega)]
    exact heq
  -- (b) the index family's own injectivity
  have hI : Function.Injective (IndexLanesOracle.indexScheduleIndex c.indexBits
      (runIndexDigest (hashOf (boundedQueries L) T) c p)) :=
    IndexLanesOracle.index_schedule_index_injective c.indexBits hbb _
  -- (c) the cross distinctness, from disjuncts (2) and (3)
  have hne : ∀ k : JointChallengeSpace.Draw c.degreeBits,
      runIndexDigest (hashOf (boundedQueries L) T) c p
        ≠ sourceDigest (hashOf (boundedQueries L) T) c p k := by
    intro k hk
    have hbase : ∀ i : JointChallengeSpace.Draw c.degreeBits,
        (i = JointChallengeSpace.Draw.gateAlpha ∨ ∃ n, i = JointChallengeSpace.Draw.gateTau n) →
        sourceDigest (hashOf (boundedQueries L) T) c p i
          = (OuterInitial.derive (hashOf (boundedQueries L) T) c
              (Verifier.statement p)).state.digest := by
      rintro i (rfl | ⟨n, rfl⟩) <;>
        exact (OuterInitial.derived_final_digest (hashOf (boundedQueries L) T) c
          (Verifier.statement p)).symm
    cases k with
    | gateAlpha =>
        refine hT (Or.inr (Or.inr ?_))
        rw [hstage, IndexLanesOracle.extended_stage22_is_derive L c (Verifier.statement p)
          (roundMessages p) p.used c.degreeBits hlenI hlenP T]
        rw [hk]
        exact hbase _ (Or.inl rfl)
    | gateTau n =>
        refine hT (Or.inr (Or.inr ?_))
        rw [hstage, IndexLanesOracle.extended_stage22_is_derive L c (Verifier.statement p)
          (roundMessages p) p.used c.degreeBits hlenI hlenP T]
        rw [hk]
        exact hbase _ (Or.inr ⟨n, rfl⟩)
    | outerLog r =>
        refine hT (Or.inr (Or.inl ⟨r.val, r.isLt, ?_⟩))
        rw [hstage, IndexLanesOracle.extended_prefix_agrees L c (Verifier.statement p)
          (roundMessages p) p.used c.degreeBits hlenI hlenP T (22 + (5 * r.val + 5)) (by omega),
          ← ConcreteChainThreading.run_round_digest_is_chain_digest L c p hlenP hmlen T r]
        exact hk
    | outerGate r =>
        refine hT (Or.inr (Or.inl ⟨r.val, r.isLt, ?_⟩))
        rw [hstage, IndexLanesOracle.extended_prefix_agrees L c (Verifier.statement p)
          (roundMessages p) p.used c.degreeBits hlenI hlenP T (22 + (5 * r.val + 5)) (by omega),
          ← ConcreteChainThreading.run_gate_round_digest_is_chain_digest L c p hlenP hmlen T r]
        exact hk
  -- (d) ILO's combined injectivity, transported to the raw byte family
  have hmemJ : ∀ (k : JointChallengeSpace.Draw c.degreeBits) (j : Fin 3),
      squeezeInputAt c.degreeBits (sourceDigest (hashOf (boundedQueries L) T) c p) k j
        ∈ boundedQueries L := fun _ _ => bounded_queries_challenge L hL _ _
  have hmemI : ∀ (k : InstalledIndexSampler.IndexDraw c.indexBits) (j : Fin 3),
      IndexLanesOracle.indexSqueezeInputAt c.indexBits
          (runIndexDigest (hashOf (boundedQueries L) T) c p) k j ∈ boundedQueries L :=
    fun _ _ => bounded_queries_challenge L hL _ _
  have hcomb := IndexLanesOracle.combined_schedule_injective (boundedQueries L) c.degreeBits
    c.indexBits hdb hbb (sourceDigest (hashOf (boundedQueries L) T) c p)
    (runIndexDigest (hashOf (boundedQueries L) T) c p) hne
    (fun kj => ⟨squeezeInputAt c.degreeBits (sourceDigest (hashOf (boundedQueries L) T) c p)
      kj.1 kj.2, hmemJ kj.1 kj.2⟩)
    (fun kj => ⟨IndexLanesOracle.indexSqueezeInputAt c.indexBits
      (runIndexDigest (hashOf (boundedQueries L) T) c p) kj.1 kj.2, hmemI kj.1 kj.2⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun a b hab => hJ (congrArg Subtype.val hab))
    (fun a b hab => hI (congrArg Subtype.val hab))
  intro a b hab
  refine hcomb ?_
  cases a <;> cases b <;> exact Subtype.ext hab

/-- (2) **THE EXCEPTIONAL EVENT IS INSIDE THE EXTENDED CHAIN CLASH.**  So ILO's
`extended_digest_clash_mass_le` bounds it, and the Fubini's additive term becomes
a number. -/
theorem run_combined_non_injective_subset_clash (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hL : 64 ≤ L) (hdb : c.degreeBits ≤ 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits) :
    runCombinedNonInjectiveEvent L c p
      ⊆ IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
          (roundMessages p) p.used c.degreeBits hlenI := by
  intro T hT
  by_contra hcon
  exact (Finset.mem_filter.mp hT).2
    (run_combined_schedule_injective_off_clash L c p hL hdb hbb hlenI hlenP hmlen T hcon)


/-! ### 2.1 The union event, and the Fubini for the PAIR of families -/

open Classical in
/-- The event, on oracle tables, that the RUN'S OWN outer/gate draw lands in `EJ`
OR the RUN'S OWN index draw lands in `EI`.  One `Finset (OracleTable Q)`, one
law.  The two draws are the adopted `InstalledRoundCommit.actualDigestDraw` and
the adopted `SoundnessAssembly.actualIndexDraw`, both at the table's own hash. -/
noncomputable def runUnionBadEvent (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EI : Finset (InstalledIndexSampler.IndexSpace c.indexBits)) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L) T) c p ∈ EJ
      ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c p ∈ EI)

open Classical in
/-- The index half of the union, on its own. -/
noncomputable def runIndexDrawEvent (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (EI : Finset (InstalledIndexSampler.IndexSpace c.indexBits)) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c p ∈ EI)

/-- (2) The union event IS the union of the adopted `runDrawEvent` and the index
half: nothing new is being weighed. -/
theorem run_union_bad_event_is_union (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EI : Finset (InstalledIndexSampler.IndexSpace c.indexBits)) :
    runUnionBadEvent L c p EJ EI
      = runDrawEvent (boundedQueries L) c p EJ ∪ runIndexDrawEvent L c p EI := by
  classical
  apply Finset.ext
  intro T
  simp only [runUnionBadEvent, runDrawEvent, runIndexDrawEvent, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem index_probability_nonneg (bits : Nat)
    (E : Finset (InstalledIndexSampler.IndexSpace bits)) :
    (0 : ℚ) ≤ IndexPointZeroCheck.indexProbability bits E :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! #### 2.1.1 One frame fibre: both digests are constant on it -/

/-- A table rebuilt from a fibre answers the challenge half by `g`. -/
theorem frame_split_challenge (L : Nat) (g : ChallengeHalf (boundedQueries L) → Block)
    (f : FrameHalf (boundedQueries L) → Block) (i : ChallengeHalf (boundedQueries L)) :
    (frameSplit (boundedQueries L)).symm (g, f) i.val = g i := by
  have h0 : ((frameSplit (boundedQueries L))
      ((frameSplit (boundedQueries L)).symm (g, f))).1 = g :=
    congrArg Prod.fst ((frameSplit (boundedQueries L)).apply_symm_apply (g, f))
  rw [frame_split_fst] at h0
  exact congrFun h0 i

/-- A table rebuilt from a fibre answers the frame half by `f`. -/
theorem frame_split_frame (L : Nat) (g : ChallengeHalf (boundedQueries L) → Block)
    (f : FrameHalf (boundedQueries L) → Block) (a : FrameHalf (boundedQueries L)) :
    (frameSplit (boundedQueries L)).symm (g, f) a.val = f a := by
  have h0 : ((frameSplit (boundedQueries L))
      ((frameSplit (boundedQueries L)).symm (g, f))).2 = f :=
    congrArg Prod.snd ((frameSplit (boundedQueries L)).apply_symm_apply (g, f))
  rw [frame_split_snd] at h0
  exact congrFun h0 a

/-- (2) The run's block digests are CONSTANT on a frame fibre.  The adopted
`source_digest_congr` through the adopted `frame_not_shaped`. -/
theorem run_source_digest_fibre_const (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (f : FrameHalf (boundedQueries L) → Block)
    (g1 g2 : ChallengeHalf (boundedQueries L) → Block) :
    sourceDigest (hashOf (boundedQueries L) ((frameSplit (boundedQueries L)).symm (g1, f))) c p
      = sourceDigest (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g2, f))) c p := by
  refine source_digest_congr (fun dg t pl => ?_) c p
  by_cases hm : Transcript.frame dg t pl ∈ boundedQueries L
  · have h1 := frame_split_frame L g1 f ⟨⟨Transcript.frame dg t pl, hm⟩, frame_not_shaped dg t pl⟩
    have h2 := frame_split_frame L g2 f ⟨⟨Transcript.frame dg t pl, hm⟩, frame_not_shaped dg t pl⟩
    simp only [hashOf, hm, dif_pos, h1, h2]
  · simp only [hashOf, hm, dif_neg, not_false_iff]

/-- (2) **THE RUN'S INDEX DIGEST IS CONSTANT ON A FRAME FIBRE TOO.**  This is
what section 1 buys: the index digest is a CHAIN STAGE, and a chain stage reads
only frame-shaped queries (`frame_state_frame_congr`).  Without section 1 the
index digest would be an opaque function of the whole table and the Fubini could
not be run for the pair. -/
theorem run_index_digest_fibre_const (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (f : FrameHalf (boundedQueries L) → Block)
    (g1 g2 : ChallengeHalf (boundedQueries L) → Block) :
    runIndexDigest (hashOf (boundedQueries L)
        ((frameSplit (boundedQueries L)).symm (g1, f))) c p
      = runIndexDigest (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g2, f))) c p := by
  rw [← extended_chain_index_digest_is_the_run_index_digest L c p hlenI hlenP hmlen
      ((frameSplit (boundedQueries L)).symm (g1, f)),
    ← extended_chain_index_digest_is_the_run_index_digest L c p hlenI hlenP hmlen
      ((frameSplit (boundedQueries L)).symm (g2, f))]
  exact frame_state_frame_congr L OuterInitial.zeroDigest _ hlenI _ _
    (fun a => (frame_split_frame L g1 f a).trans (frame_split_frame L g2 f a).symm) _

/-- (2) Hence the whole combined schedule is constant on a frame fibre. -/
theorem run_combined_schedule_fibre_const (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (f : FrameHalf (boundedQueries L) → Block)
    (g1 g2 : ChallengeHalf (boundedQueries L) → Block) :
    runCombinedSchedule L c p ((frameSplit (boundedQueries L)).symm (g1, f))
      = runCombinedSchedule L c p ((frameSplit (boundedQueries L)).symm (g2, f)) := by
  funext x
  cases x with
  | inl kj => simp only [runCombinedSchedule, run_source_digest_fibre_const L c p f g1 g2]
  | inr kj =>
      simp only [runCombinedSchedule, run_index_digest_fibre_const L c p hlenI hlenP hmlen f g1 g2]

/-! #### 2.1.2 The count inside ONE fibre -/

open Classical in
/-- (2) **THE JOINT HALF OF A GOOD FIBRE IS EXACTLY `jointProbability`.**  The
adopted `restrict_ratio` at the fibre's own FIXED schedule. -/
theorem run_joint_fibre_count (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hL : 64 ≤ L) (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (f : FrameHalf (boundedQueries L) → Block)
    (b0 : Block)
    (hinj : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      Function.Injective (runCombinedSchedule L c p
        ((frameSplit (boundedQueries L)).symm (g, f)))) :
    ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ)).card : ℚ)
      = JointChallengeSpace.jointProbability c.degreeBits EJ
        * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) := by
  classical
  set dig := sourceDigest (hashOf (boundedQueries L)
    ((frameSplit (boundedQueries L)).symm ((fun _ => b0), f))) c p with hdigdef
  have hmemJ : ∀ (k : JointChallengeSpace.Draw c.degreeBits) (j : Fin 3),
      squeezeInputAt c.degreeBits dig k j ∈ boundedQueries L :=
    fun _ _ => bounded_queries_challenge L hL _ _
  set selJ : JointChallengeSpace.Draw c.degreeBits × Fin 3 → ChallengeHalf (boundedQueries L) :=
    fun kj => ⟨⟨squeezeInputAt c.degreeBits dig kj.1 kj.2, hmemJ kj.1 kj.2⟩,
      challenge_input_shaped _ _⟩
  have hselJinj : Function.Injective selJ := by
    intro a b hab
    exact Sum.inl.inj (hinj (fun _ => b0) (congrArg (fun z => z.val.val) hab))
  have hdrawJ : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p
        = bundleEquiv c.degreeBits (fun kj => g (selJ kj)) := by
    intro g
    rw [actual_digest_draw_is_draw_at_digests,
      run_source_digest_fibre_const L c p f g (fun _ => b0), ← hdigdef,
      draw_at_digests_is_encoded (boundedQueries L) c.degreeBits dig
        (fun kj => (selJ kj).val) (fun k j => rfl)]
    unfold encodedDraw
    exact congrArg (bundleEquiv c.degreeBits) (funext fun kj => frame_split_challenge L g f (selJ kj))
  have hset : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ))
      = Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          (fun kj => g (selJ kj)) ∈ Finset.univ.filter
            (fun w : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block =>
              bundleEquiv c.degreeBits w ∈ EJ)) := by
    apply Finset.ext
    intro g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdrawJ g]
  have hEJcard : (Finset.univ.filter
      (fun w : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block =>
        bundleEquiv c.degreeBits w ∈ EJ)).card = EJ.card := by
    have h := WhirChallenge.equiv_event_card (bundleEquiv c.degreeBits) (fun w => w ∈ EJ)
    have h2 : (Finset.univ.filter
        (fun w : JointChallengeSpace.JointSpace c.degreeBits => w ∈ EJ)) = EJ := by
      apply Finset.ext
      intro w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h2] at h
    exact h
  have hratio := restrict_ratio selJ hselJinj (Finset.univ.filter
    (fun w : JointChallengeSpace.Draw c.degreeBits × Fin 3 → Block =>
      bundleEquiv c.degreeBits w ∈ EJ))
  rw [restrictAt, hEJcard, schedule_index_card] at hratio
  have hbpos : (0 : ℚ) < (Fintype.card Block : ℚ) := by exact_mod_cast block_card_pos
  rw [hset, JointChallengeSpace.jointProbability, joint_space_card_as_blocks,
    div_mul_eq_mul_div, eq_div_iff (pow_pos hbpos ((3 * c.degreeBits + 1) * 3)).ne']
  exact hratio

open Classical in
/-- (2) **THE INDEX HALF OF A GOOD FIBRE IS EXACTLY `indexProbability`.**  The
index twin of `run_joint_fibre_count`, at the fibre's own index digest -- which
is constant on the fibre by `run_index_digest_fibre_const`, i.e. by section 1. -/
theorem run_index_fibre_count (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hL : 64 ≤ L)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (EI : Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (f : FrameHalf (boundedQueries L) → Block)
    (b0 : Block)
    (hinj : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      Function.Injective (runCombinedSchedule L c p
        ((frameSplit (boundedQueries L)).symm (g, f)))) :
    ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card : ℚ)
      = IndexPointZeroCheck.indexProbability c.indexBits EI
        * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) := by
  classical
  set e := runIndexDigest (hashOf (boundedQueries L)
    ((frameSplit (boundedQueries L)).symm ((fun _ => b0), f))) c p with hedef
  have hmemI : ∀ (k : InstalledIndexSampler.IndexDraw c.indexBits) (j : Fin 3),
      IndexLanesOracle.indexSqueezeInputAt c.indexBits e k j ∈ boundedQueries L :=
    fun _ _ => bounded_queries_challenge L hL _ _
  set selI : InstalledIndexSampler.IndexDraw c.indexBits × Fin 3
      → ChallengeHalf (boundedQueries L) :=
    fun kj => ⟨⟨IndexLanesOracle.indexSqueezeInputAt c.indexBits e kj.1 kj.2, hmemI kj.1 kj.2⟩,
      challenge_input_shaped _ _⟩
  have hselIinj : Function.Injective selI := by
    intro a b hab
    exact Sum.inr.inj (hinj (fun _ => b0) (congrArg (fun z => z.val.val) hab))
  have hdrawI : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p
        = IndexLanesOracle.indexBundleEquiv c.indexBits (fun kj => g (selI kj)) := by
    intro g
    rw [assembly_index_draw_is_at_run_index_digest,
      run_index_digest_fibre_const L c p hlenI hlenP hmlen f g (fun _ => b0), ← hedef,
      IndexLanesOracle.index_draw_at_digest_is_encoded (boundedQueries L) c.indexBits e
        (fun kj => (selI kj).val) (fun k j => rfl)]
    unfold IndexLanesOracle.indexEncodedDraw
    exact congrArg (IndexLanesOracle.indexBundleEquiv c.indexBits)
      (funext fun kj => frame_split_challenge L g f (selI kj))
  have hset : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
          ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI))
      = Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          (fun kj => g (selI kj)) ∈ IndexLanesOracle.indexBundlePreimage c.indexBits EI) := by
    apply Finset.ext
    intro g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdrawI g,
      IndexLanesOracle.indexBundlePreimage]
  have hratio := restrict_ratio selI hselIinj
    (IndexLanesOracle.indexBundlePreimage c.indexBits EI)
  rw [restrictAt, IndexLanesOracle.index_bundle_preimage_card,
    IndexLanesOracle.index_schedule_card] at hratio
  have hbpos : (0 : ℚ) < (Fintype.card Block : ℚ) := by exact_mod_cast block_card_pos
  rw [hset, IndexPointZeroCheck.indexProbability, IndexLanesOracle.index_space_card_as_blocks,
    div_mul_eq_mul_div, eq_div_iff (pow_pos hbpos (2 * c.indexBits * 3)).ne']
  exact hratio

open Classical in
/-- (2) **THE FIBRE BOUND.**  On a fibre whose combined schedule is injective the
two halves are exactly their ideal masses and the union is at most their sum; on
any other fibre the whole fibre is in the exceptional count and the bound is
`1`. -/
theorem run_union_fibre_count_le (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hL : 64 ≤ L)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EI : Finset (InstalledIndexSampler.IndexSpace c.indexBits))
    (b0 : Block) (f : FrameHalf (boundedQueries L) → Block) :
    ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card : ℚ)
      ≤ (JointChallengeSpace.jointProbability c.degreeBits EJ
          + IndexPointZeroCheck.indexProbability c.indexBits EI)
          * (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ)
        + ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
            ¬ Function.Injective (runCombinedSchedule L c p
              ((frameSplit (boundedQueries L)).symm (g, f))))).card : ℚ) := by
  classical
  have hcardle : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card
      ≤ (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ)).card
        + (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    exact hx
  have hcardleq : ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card : ℚ)
      ≤ ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ)).card : ℚ)
        + ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
          SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card : ℚ) := by
    exact_mod_cast hcardle
  by_cases hinj : ∀ g : ChallengeHalf (boundedQueries L) → Block,
      Function.Injective (runCombinedSchedule L c p
        ((frameSplit (boundedQueries L)).symm (g, f)))
  · rw [run_joint_fibre_count L c p hL EJ f b0 hinj,
      run_index_fibre_count L c p hL hlenI hlenP hmlen EI f b0 hinj] at hcardleq
    rw [add_mul]
    linarith [Nat.cast_nonneg (α := ℚ) (Finset.univ.filter
      (fun g : ChallengeHalf (boundedQueries L) → Block =>
        ¬ Function.Injective (runCombinedSchedule L c p
          ((frameSplit (boundedQueries L)).symm (g, f))))).card]
  · push_neg at hinj
    obtain ⟨g0, hg0⟩ := hinj
    have hb : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        ¬ Function.Injective (runCombinedSchedule L c p
          ((frameSplit (boundedQueries L)).symm (g, f))))) = Finset.univ := by
      apply Finset.ext
      intro g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [run_combined_schedule_fibre_const L c p hlenI hlenP hmlen f g g0]
      exact hg0
    rw [hb, Finset.card_univ]
    have hle : (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card
        ≤ Fintype.card (ChallengeHalf (boundedQueries L) → Block) := by
      rw [← Finset.card_univ]
      exact Finset.card_filter_le _ _
    have hlec : ((Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
        InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
          ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
            ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card : ℚ)
        ≤ (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) := by
      exact_mod_cast hle
    have hjp := JointChallengeSpace.joint_probability_nonneg c.degreeBits EJ
    have hip := index_probability_nonneg c.indexBits EI
    have hNnn : (0 : ℚ) ≤ (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) :=
      Nat.cast_nonneg _
    have hpos := mul_nonneg (add_nonneg hjp hip) hNnn
    linarith

/-! #### 2.1.3 The Fubini -/

/-- (2) **THE RUN-LEVEL FUBINI FOR THE UNION, for a fixed (non-adaptive) prover
under the random oracle model.**  The mass of the union of the run's OWN two bad
draws is at most the two ideal masses -- the adopted
`JointChallengeSpace.jointProbability` and the adopted
`IndexPointZeroCheck.indexProbability` -- plus ONE additive term, the mass of the
fibres on which the run's combined schedule of oracle inputs is not injective.

NOTHING IS CONDITIONED.  Neither the block digests nor the index digest is
quantified outside the law: they are `sourceDigest (hashOf Q T) c p` and
`runIndexDigest (hashOf Q T) c p`, both functions of the table being weighed.
This is the statement ILO's "What remains" names, and it is the PAIR version of
the adopted `RandomOracleSqueezes.run_draw_probability_le_fibrewise`.

HOW IT IS PROVED.  A Fubini over the fibres of the adopted `frameSplit`, the
split of `Q` by STRING SHAPE that does not depend on the table.  Inside one frame
fibre BOTH digests are constant -- the block digests by the adopted
`source_digest_congr` through `frame_not_shaped`, and the index digest by section
1 together with `frame_state_frame_congr`, since the eight claim frames are
frame-shaped inputs and so live in the frame half of the split.  The two
schedules are then FIXED injective families into the challenge half, and the
adopted `restrict_ratio` gives each draw exactly its ideal mass; the fibres where
the combined family is not injective are bounded by `1` and collected.  No
sequential fresh-query induction and no birthday argument appears here: those
bound the additive term, in section 2.2. -/
theorem run_union_draw_probability_le_fibrewise (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (hL : 64 ≤ L)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (EJ : Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EI : Finset (InstalledIndexSampler.IndexSpace c.indexBits)) :
    oracleProbability (boundedQueries L) (runUnionBadEvent L c p EJ EI)
      ≤ JointChallengeSpace.jointProbability c.degreeBits EJ
        + IndexPointZeroCheck.indexProbability c.indexBits EI
        + oracleProbability (boundedQueries L) (runCombinedNonInjectiveEvent L c p) := by
  classical
  obtain ⟨b0⟩ := Fintype.card_pos_iff.mp block_card_pos
  haveI : Nonempty (ChallengeHalf (boundedQueries L) → Block) := ⟨fun _ => b0⟩
  haveI : Nonempty (FrameHalf (boundedQueries L) → Block) := ⟨fun _ => b0⟩
  have hA : (runUnionBadEvent L c p EJ EI).card
      = ∑ f : FrameHalf (boundedQueries L) → Block,
          (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
            InstalledRoundCommit.actualDigestDraw (hashOf (boundedQueries L)
                ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EJ
              ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L)
                ((frameSplit (boundedQueries L)).symm (g, f))) c p ∈ EI)).card := by
    have h1 : runUnionBadEvent L c p EJ EI
        = Finset.univ.filter (fun T : OracleTable (boundedQueries L) =>
            (fun z : (ChallengeHalf (boundedQueries L) → Block)
                × (FrameHalf (boundedQueries L) → Block) =>
              InstalledRoundCommit.actualDigestDraw
                  (hashOf (boundedQueries L) ((frameSplit (boundedQueries L)).symm z)) c p ∈ EJ
                ∨ SoundnessAssembly.actualIndexDraw
                  (hashOf (boundedQueries L) ((frameSplit (boundedQueries L)).symm z)) c p ∈ EI)
              (frameSplit (boundedQueries L) T)) := by
      apply Finset.ext
      intro T
      simp only [runUnionBadEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_apply_apply]
    rw [h1, WhirChallenge.equiv_event_card (frameSplit (boundedQueries L))
        (fun z : (ChallengeHalf (boundedQueries L) → Block)
            × (FrameHalf (boundedQueries L) → Block) =>
          InstalledRoundCommit.actualDigestDraw
              (hashOf (boundedQueries L) ((frameSplit (boundedQueries L)).symm z)) c p ∈ EJ
            ∨ SoundnessAssembly.actualIndexDraw
              (hashOf (boundedQueries L) ((frameSplit (boundedQueries L)).symm z)) c p ∈ EI),
      Finset.card_filter, Fintype.sum_prod_type_right]
    simp only [Finset.card_filter]
  have hB : (runCombinedNonInjectiveEvent L c p).card
      = ∑ f : FrameHalf (boundedQueries L) → Block,
          (Finset.univ.filter (fun g : ChallengeHalf (boundedQueries L) → Block =>
            ¬ Function.Injective (runCombinedSchedule L c p
              ((frameSplit (boundedQueries L)).symm (g, f))))).card := by
    have h1 : runCombinedNonInjectiveEvent L c p
        = Finset.univ.filter (fun T : OracleTable (boundedQueries L) =>
            (fun z : (ChallengeHalf (boundedQueries L) → Block)
                × (FrameHalf (boundedQueries L) → Block) =>
              ¬ Function.Injective (runCombinedSchedule L c p
                ((frameSplit (boundedQueries L)).symm z))) (frameSplit (boundedQueries L) T)) := by
      apply Finset.ext
      intro T
      simp only [runCombinedNonInjectiveEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_apply_apply]
    rw [h1, WhirChallenge.equiv_event_card (frameSplit (boundedQueries L))
        (fun z : (ChallengeHalf (boundedQueries L) → Block)
            × (FrameHalf (boundedQueries L) → Block) =>
          ¬ Function.Injective (runCombinedSchedule L c p
            ((frameSplit (boundedQueries L)).symm z))),
      Finset.card_filter, Fintype.sum_prod_type_right]
    simp only [Finset.card_filter]
  have htot : Fintype.card (OracleTable (boundedQueries L))
      = Fintype.card (ChallengeHalf (boundedQueries L) → Block)
        * Fintype.card (FrameHalf (boundedQueries L) → Block) := by
    rw [Fintype.card_congr (frameSplit (boundedQueries L)), Fintype.card_prod]
  have hNpos : (0 : ℚ) < (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := ChallengeHalf (boundedQueries L) → Block)
  have hMpos : (0 : ℚ) < (Fintype.card (FrameHalf (boundedQueries L) → Block) : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := FrameHalf (boundedQueries L) → Block)
  have hNM : (0 : ℚ) < (Fintype.card (ChallengeHalf (boundedQueries L) → Block) : ℚ)
      * (Fintype.card (FrameHalf (boundedQueries L) → Block) : ℚ) := mul_pos hNpos hMpos
  rw [oracleProbability, oracleProbability, hA, hB, htot]
  push_cast
  rw [div_le_iff hNM, add_mul, div_mul_cancel₀ _ hNM.ne']
  refine le_trans (Finset.sum_le_sum
    (fun f _ => run_union_fibre_count_le L c p hL hlenI hlenP hmlen EJ EI b0 f)) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring


/-! ## 2.2 The named bounds

The two ideal masses are replaced by the adopted numbers and the additive term by
ILO's extended birthday count. -/

/-- (2) **THE RUN-LEVEL UNION BOUND, for a fixed (non-adaptive) prover under the
random oracle model.**  Under ONE random-oracle counting law on
`OracleTable (boundedQueries L)`, the mass of the event that the run's outer/gate
draw falls in the adopted `JointChallengeSpace.jointBadEvent` OR the run's index
draw falls in ILO's guarded index agreement union is at most

  `combinedBound + 2 * tauTerm indexBits + (the extended chain's clash mass)`.

ONE clash term, not two: the Fubini is run once for the pair.  Neither digest is
conditioned; both are functions of the table.  Scope and disclaimers: HONESTY
(i)-(iv) in the header -- in particular this is NOT the system's soundness
error. -/
theorem run_union_bad_draw_probability_le (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hL : 64 ≤ L) (hdb : c.degreeBits ≤ 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (quotientDegree constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (lane : Nat → Element)
    (coeffsOf : Nat → List Element) (suppliedCells committedCells : List Element)
    (hlogLen : logLane.length = c.degreeBits) (hgateLen : gateLane.length = c.degreeBits)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L) (runUnionBadEvent L c p
        (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane
          lane (2 ^ c.degreeBits) coeffsOf)
        (IndexLanesOracle.guardedIndexBadEvent c.indexBits suppliedCells committedCells))
      ≤ ChallengeUnionBound.combinedBound c.degreeBits quotientDegree c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + oracleProbability (boundedQueries L)
            (IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
              (roundMessages p) p.used c.degreeBits hlenI) := by
  have h0 := run_union_draw_probability_le_fibrewise L c p hL hlenI hlenP hmlen
    (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane
      lane (2 ^ c.degreeBits) coeffsOf)
    (IndexLanesOracle.guardedIndexBadEvent c.indexBits suppliedCells committedCells)
  have h1 := JointChallengeSpace.joint_union_bound c.degreeBits quotientDegree constraints
    logCompare gateCompare logLane gateLane lane coeffsOf hlogLen hgateLen hlogDeg hgateDeg hclen
  have h2 := IndexLanesOracle.guarded_index_bad_event_mass_le c.indexBits suppliedCells
    committedCells
  have h3 := oracle_probability_mono (boundedQueries L) _ _
    (run_combined_non_injective_subset_clash L c p hL hdb hbb hlenI hlenP hmlen)
  linarith

/-- (2) **THE SAME BOUND WITH THE CLASH TERM REPLACED BY ILO'S BIRTHDAY COUNT.**
`22 + 5 d + 8` chain stages, so `(22 + 5 d + 8)(22 + 5 d + 9) / 2 / |Block|`.
NO probabilistic side condition remains, for a fixed (non-adaptive) prover under
the random oracle model. -/
theorem run_union_bad_draw_probability_le_birthday (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hL : 64 ≤ L) (hdb : c.degreeBits ≤ 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (quotientDegree constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (lane : Nat → Element)
    (coeffsOf : Nat → List Element) (suppliedCells committedCells : List Element)
    (hlogLen : logLane.length = c.degreeBits) (hgateLen : gateLane.length = c.degreeBits)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ quotientDegree + 2 ∧
      r.truth.length ≤ quotientDegree + 2)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L) (runUnionBadEvent L c p
        (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane
          lane (2 ^ c.degreeBits) coeffsOf)
        (IndexLanesOracle.guardedIndexBadEvent c.indexBits suppliedCells committedCells))
      ≤ ChallengeUnionBound.combinedBound c.degreeBits quotientDegree c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits
        + ((22 + 5 * c.degreeBits + 8 : Nat) : ℚ)
            * (((22 + 5 * c.degreeBits + 8 : Nat) : ℚ) + 1) / 2 / (Fintype.card Block : ℚ) := by
  have h := run_union_bad_draw_probability_le L c p hL hdb hbb hlenI hlenP hmlen quotientDegree
    constraints logCompare gateCompare logLane gateLane lane coeffsOf suppliedCells committedCells
    hlogLen hgateLen hlogDeg hgateDeg hclen
  have hc := IndexLanesOracle.extended_digest_clash_mass_le L c (Verifier.statement p)
    (roundMessages p) p.used c.degreeBits hlenI
  linarith

/-- (2) **AT THE ENVELOPE'S `degreeBits = 13`, for a fixed (non-adaptive) prover
under the random oracle model**: ninety-five chain stages, so `4560 / |Block|`,
up from CCT's `3828` for the chain that stops at the last coupled round.
`Fintype.card Block` is never evaluated. -/
theorem run_union_bad_draw_probability_le_at_thirteen (L : Nat) (c : Verifier.Config)
    (p : Verifier.Proof)
    (hL : 64 ≤ L) (hd : c.degreeBits = 13) (hbb : c.indexBits ≤ 8)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L)
    (hlenP : ∀ k, 61 + (prefixRoundShape c (Verifier.statement p) (roundMessages p) k).2.length ≤ L)
    (hmlen : (roundMessages p).length = c.degreeBits)
    (constraints : Nat) (logCompare gateCompare : Element)
    (logLane gateLane : List ConditionalSoundness.LaneRound) (lane : Nat → Element)
    (coeffsOf : Nat → List Element) (suppliedCells committedCells : List Element)
    (hlogLen : logLane.length = c.degreeBits) (hgateLen : gateLane.length = c.degreeBits)
    (hlogDeg : ∀ r ∈ logLane, r.message.length ≤ 5 ∧ r.truth.length ≤ 5)
    (hgateDeg : ∀ r ∈ gateLane, r.message.length ≤ 10 ∧ r.truth.length ≤ 10)
    (hclen : ∀ i, i < 2 ^ c.degreeBits → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L) (runUnionBadEvent L c p
        (JointChallengeSpace.jointBadEvent c.degreeBits logCompare gateCompare logLane gateLane
          lane (2 ^ c.degreeBits) coeffsOf)
        (IndexLanesOracle.guardedIndexBadEvent c.indexBits suppliedCells committedCells))
      ≤ ChallengeUnionBound.combinedBound c.degreeBits 8 c.degreeBits constraints
        + 2 * ChallengeUnionBound.tauTerm c.indexBits + 4560 / (Fintype.card Block : ℚ) := by
  have h := run_union_bad_draw_probability_le_birthday L c p hL (by omega) hbb hlenI hlenP hmlen
    8 constraints logCompare gateCompare logLane gateLane lane coeffsOf suppliedCells
    committedCells hlogLen hgateLen hlogDeg hgateDeg hclen
  have hnum : ((22 + 5 * c.degreeBits + 8 : Nat) : ℚ)
      * (((22 + 5 * c.degreeBits + 8 : Nat) : ℚ) + 1) / 2 = 4560 := by
    rw [hd]
    norm_num
  rw [hnum] at h
  exact h

/-! ## 3. A CLOSED INSTANCE AT THE ENVELOPE -/

/-- (3) **THE EXTENDED CHAIN'S LENGTH BUDGET, FROM CCT'S `LengthBudget` AND A
CELL WIDTH BOUND.**  The twenty-two prefix frames and the round frames are CCT's
budget verbatim; the eight claim frames need only a per-cell width bound `W`,
because a cell frame is `69 + 24 W` bytes by the adopted
`OuterAdapter.encoded_vector_length` (ILO's `claim_shape_payload_bound`).

WHAT THIS COSTS BEYOND CCT.  Five per-claim width bounds and `69 + 24 W ≤ L`
are EXTRA hypotheses, not consequences of `LengthBudget`; see HONESTY (8).  At
`L = 381` they allow only `W ≤ 13`, so this route covers claims of width at most
thirteen — not the deployed `indexBits = 8` profile, which needs ILO's own
`L = 8192` envelope. -/
theorem length_budget_extended_chain (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (quotientDegree W : Nat) (hb : ConcreteChainThreading.LengthBudget L c p quotientDegree)
    (h1 : p.used.logPreprocessed.length ≤ W) (h2 : p.used.logWitness.length ≤ W)
    (h3 : p.used.logNormInverse.length ≤ W) (h4 : p.used.gatePreprocessed.length ≤ W)
    (h5 : p.used.gateWitness.length ≤ W) (hW : 69 + 24 * W ≤ L) :
    ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hb
  refine IndexLanesOracle.prefix_round_index_shape_payload_bound L W c (Verifier.statement p)
    (roundMessages p) p.used c.degreeBits ?_ ?_ h1 h2 h3 h4 h5 hW (by omega)
  · exact ConcreteChainThreading.prefix_message_payload_bound L c (Verifier.statement p)
      (by omega) g2 g3 g4 g5
  · exact round_shape_payload_bound_at_envelope L (roundMessages p) quotientDegree g6 g7 g1

/-- The closed witness's config: the adopted `Verifier.testConfig` at the
envelope's `degreeBits = 13` and the envelope's index cap `indexBits = 8`.  CCT's
`budgetConfig` is the same config at `indexBits = 0`, at which
`ChallengeUnionBound.tauTerm` is trivially zero; the index cap is used here so
that the index half of the bound is the envelope's own figure. -/
def unionConfig : Verifier.Config :=
  { Verifier.testConfig with degreeBits := 13, indexBits := 8 }

/-- The closed witness's proof: CCT's `budgetProof`, the adopted
`Verifier.testProof` with thirteen coupled rounds.  Its `used` claims are the
adopted test claims, whose five cell vectors have length at most one. -/
def unionProof : Verifier.Proof := ConcreteChainThreading.budgetProof

theorem union_config_degree : unionConfig.degreeBits = 13 := rfl

theorem union_config_index : unionConfig.indexBits = 8 := rfl

theorem union_round_count : (roundMessages unionProof).length = unionConfig.degreeBits :=
  ConcreteChainThreading.budget_round_count

/-- (3) CCT's closed length budget, at this module's config.  The two config
conjuncts of `LengthBudget` read only `whirProtocolId` and `whirSessionId`, which
`unionConfig` inherits unchanged from the adopted `Verifier.testConfig`. -/
theorem union_length_budget : ConcreteChainThreading.LengthBudget 381 unionConfig unionProof 8 :=
  ConcreteChainThreading.length_budget_at_envelope

theorem union_length_budget_chain :
    ∀ k, 61 + (prefixRoundShape unionConfig (Verifier.statement unionProof)
      (roundMessages unionProof) k).2.length ≤ 381 :=
  ConcreteChainThreading.length_budget_chain 381 unionConfig unionProof 8 union_length_budget

/-- (3) The extended chain fits in the SAME `L = 381` envelope CCT uses: the five
used-claim vectors of the adopted test proof have length at most one, so the
eight claim frames need only `69 + 24 = 93` bytes. -/
theorem union_length_budget_extended :
    ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape unionConfig (Verifier.statement unionProof)
      (roundMessages unionProof) unionProof.used unionConfig.degreeBits k).2.length ≤ 381 :=
  length_budget_extended_chain 381 unionConfig unionProof 8 1 union_length_budget
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)

/-- (3) **THE RUN-LEVEL UNION BOUND WITH EVERY HYPOTHESIS DISCHARGED.**  Query
set, config, proof, length budgets and lane shapes are all concrete -- the lanes
are the adopted `RandomOracleSqueezes.trivialLane`, the same closed witness CCT
and ILO use.  Only the field element `x` is a parameter.  An inequality between a
mass on oracle tables and a number, with no side condition at all, for a fixed
(non-adaptive) prover under the random oracle model. -/
theorem run_union_bad_draw_at_the_envelope_closed (x : Element) :
    oracleProbability (boundedQueries 381) (runUnionBadEvent 381 unionConfig unionProof
        (JointChallengeSpace.jointBadEvent unionConfig.degreeBits x x (trivialLane x)
          (trivialLane x) (fun _ => x) (2 ^ unionConfig.degreeBits) (fun _ => []))
        (IndexLanesOracle.guardedIndexBadEvent unionConfig.indexBits [] []))
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
        + 4560 / (Fintype.card Block : ℚ) :=
  run_union_bad_draw_probability_le_at_thirteen 381 unionConfig unionProof (by norm_num)
    union_config_degree (le_of_eq union_config_index) union_length_budget_extended
    union_length_budget_chain
    union_round_count 123 x x (trivialLane x) (trivialLane x) (fun _ => x) (fun _ => []) [] []
    (trivial_lane_length x) (trivial_lane_length x) (trivial_lane_deg x 5)
    (trivial_lane_deg x 10) (fun _ _ => Nat.zero_le _)

/-- (3) `4560 * 2 ^ 243` fits inside the block space: `4560 < 2 ^ 13` and
`|Block| = 256 ^ 32 = 2 ^ 256` by the adopted `block_card`.  Only `Nat` power
laws are used; the cardinal is never evaluated. -/
theorem block_card_ge_extended_birthday_scale : 4560 * 2 ^ 243 ≤ Fintype.card Block := by
  have hb : (256 : Nat) = 2 ^ 8 := by norm_num
  have hp : (256 : Nat) ^ 32 = 2 ^ 256 := by
    conv_lhs => rw [hb]
    rw [← pow_mul]
  rw [block_card, hp]
  calc (4560 : Nat) * 2 ^ 243 ≤ 2 ^ 13 * 2 ^ 243 := Nat.mul_le_mul (by norm_num) (Nat.le_refl _)
    _ = 2 ^ 256 := by rw [← pow_add]

/-- (3) **THE EXTENDED BIRTHDAY TERM, SYMBOLICALLY**: `4560 / |Block| ≤ 2 ^ (-243)`.
A statement about the chain model under the random-oracle counting law -- see
HONESTY (i) and (iv). -/
theorem extended_birthday_term_le_two_pow_neg :
    (4560 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 243 := by
  rw [div_le_div_iff block_card_cast_pos (by positivity), one_mul]
  exact_mod_cast block_card_ge_extended_birthday_scale

/-- (3) **THE CLOSED BOUND IS A NON-TRIVIAL NUMBER.**  The right-hand side of
`run_union_bad_draw_at_the_envelope_closed` is strictly below `1`: the adopted
`ChallengeUnionBound.combined_bound_at_extremes_numeric` puts the outer term at
most `2 ^ (-172)`, the adopted `SoundnessAssembly.index_mass_at_the_envelope`
puts the index term at most `2 ^ (-187)`, and
`extended_birthday_term_le_two_pow_neg` puts the chain term at most `2 ^ (-243)`.

Read HONESTY (i) and (iv) before quoting this: it says the closed statement is
not the vacuous `≤ 1`.  It does NOT say the protocol has this soundness error. -/
theorem run_union_closed_bound_lt_one :
    ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
      + 4560 / (Fintype.card Block : ℚ) < 1 := by
  have hcomb : ChallengeUnionBound.combinedBound 13 8 13 123 ≤ (1 : ℚ) / 2 ^ 172 :=
    ChallengeUnionBound.combined_bound_at_extremes_numeric
  have hidx : 2 * ChallengeUnionBound.tauTerm 8 ≤ (1 : ℚ) / 2 ^ 187 :=
    SoundnessAssembly.index_mass_at_the_envelope 8 (Nat.le_refl 8)
  have hbirth : (4560 : ℚ) / (Fintype.card Block : ℚ) ≤ 1 / 2 ^ 243 :=
    extended_birthday_term_le_two_pow_neg
  have hsum : (1 : ℚ) / 2 ^ 172 + 1 / 2 ^ 187 + 1 / 2 ^ 243 < 1 := by norm_num
  linarith


/-! ## 4. THE PAYOFF: the explicit engine's assembly against the union

### 4.1 The table-indexed union event

The explicit engine's own bad events are FUNCTIONS OF THE HASH -- the adopted
`SoundnessAssembly.outerBadEvent` takes `thash`, and the adopted
`SoundnessAssembly.indexBadEvent`'s two cell families are read off
`Verifier.derivedIndices` / `Verifier.derivedRounds` of the engine at `thash`.  A
union bound needs ONE fixed event, so the two are separated: section 4.2 is the
INCLUSION, which is unconditional and IS delivered, and section 4.3 is the MASS,
which is NOT delivered -- it is prose, not a theorem.  See HONESTY (6). -/

open Classical in
/-- The union bad event with the two events supplied as FUNCTIONS OF THE HASH. -/
noncomputable def runUnionBadEventAt (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (EJ : Transcript.Hash → Finset (JointChallengeSpace.JointSpace c.degreeBits))
    (EI : Transcript.Hash → Finset (InstalledIndexSampler.IndexSpace c.indexBits)) :
    Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T =>
    SoundnessAssembly.actualDigestDraw (hashOf (boundedQueries L) T) c p
        ∈ EJ (hashOf (boundedQueries L) T)
      ∨ SoundnessAssembly.actualIndexDraw (hashOf (boundedQueries L) T) c p
        ∈ EI (hashOf (boundedQueries L) T))

/-! ### 4.2 The failure event of the explicit engine's assembly -/

open Classical in
/-- The tables on which the adopted `SoundnessAssembly.explicit_good_draw_assembly`
conclusion FAILS: the engine accepts and the residue holds at that table's hash,
yet the conclusion does not.  The conclusion is the adopted one verbatim --
good-draw conditional constraint vanishing at every row, the cell identification,
the pinned WHIR parameters, and the `core c = core c₀` / `KhashCollision`
disjunction.  It is NOT circuit truth; see HONESTY (v). -/
noncomputable def assemblyFailureEvent (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (gateTruths : List (List Element))
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) : Finset (OracleTable (boundedQueries L)) :=
  Finset.univ.filter (fun T => ¬ (
    Integrated.verify (SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P c₀)
        gdec pin chain c p = Except.ok () →
    SoundnessAssembly.AssemblyResidue gdec hash (hashOf (boundedQueries L) T) khash P c₀ pin c p
        wq (pre ++ gate :: post) s0 sLast xg cells gateTruths coeffsOf cellIndex cols →
    ((∀ row < 2 ^ c.degreeBits,
        (∀ g' ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
            = Verifier.zero) →
        (∀ g' ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig c) g' s0.tables row
            = Verifier.zero) →
        GateRejectionPower.rowFilter (Integrated.gateConfig c) gate s0.tables row
            ≠ Verifier.zero →
        ∃ terms, GatesComplete.evaluateUnfiltered gate
              (AlphaZeroCheck.rowWires s0.tables row)
              (AlphaZeroCheck.rowConstants s0.tables row)
              (GateTerminalBinding.publicHashFunction
                ((SoundnessAssembly.engine gdec hash (hashOf (boundedQueries L) T) khash P
                  c₀).publicInputsHash p.publicInputs))
              (Integrated.gateConfig c).numSelectors = some terms
            ∧ ∀ y ∈ terms, y = Verifier.zero)
      ∧ OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
            (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash
              (hashOf (boundedQueries L) T) khash P c₀) c p) cellIndex).1
          = IndexPointZeroCheck.openedCells (cols cellIndex)
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow
              (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash
                (hashOf (boundedQueries L) T) khash P c₀) c p) cellIndex))
      ∧ (PinnedWhirProfile.pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧ wq.rounds ≠ [])
      ∧ (ExplicitEngine.core c = ExplicitEngine.core c₀
          ∨ ExplicitEngine.KhashCollision khash))))

/-- (4) **THE ASSEMBLY CAN ONLY FAIL ON THE RUN UNION BAD EVENT, for a fixed
(non-adaptive) prover under the random oracle model.**  A Finset inclusion, with
no hypothesis: on every table outside the hash-indexed union of the adopted
`SoundnessAssembly.outerBadEvent` and `SoundnessAssembly.indexBadEvent`, the
adopted `explicit_good_draw_assembly` supplies its conclusion, because its two
draw hypotheses `hdraw` and `hidx` are exactly non-membership in those two
events.

WHAT THIS IS NOT.  It is not a soundness statement.  The conclusion is
good-draw-conditional constraint vanishing and identification, residue R1b is
still assumed inside `AssemblyResidue`, and WHIR/Merkle are out of scope; see
HONESTY (iii)-(v).

**AND IT IS NOT A MASS BOUND.**  The container is `runUnionBadEventAt`, the
HASH-INDEXED event; nothing in this module weighs it.  Sections 2 and 3 weigh
`runUnionBadEvent`, the FIXED-event version, and the two are joined only by a
cover that is not known to be satisfiable at any non-degenerate run -- so this
module states no such cover and proves no mass bound for
`assemblyFailureEvent`.  Section 4.3 spells out what the missing step actually
is: a two-stage conditional count for THIS fixed prover, not an adaptive-prover
treatment. -/
theorem assembly_failure_subset_run_union (L : Nat) (gdec : Integrated.DecodeGates)
    (hash : Spongefish.Hash) (khash : Verifier.Bytes → Verifier.Root)
    (P : SoundnessAssembly.Profile) (c₀ : Verifier.Config) (pin : Verifier.Pinned)
    (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) (wq : SoundnessAssembly.VkParams)
    (pre post : List Gates.GateInfo) (gate : Gates.GateInfo)
    (s0 sLast : GateTerminalBinding.ProverState) (xg : Element)
    (cells : GateTerminalBinding.Cells) (logTruths gateTruths : List (List Element))
    (t : NormDenseRound.Tables) (pr : NormDenseRound.Prepared)
    (coeffsOf : Nat → List Element) (cellIndex : Fin 5)
    (cols : Fin 5 → List (List Element)) :
    assemblyFailureEvent L gdec hash khash P c₀ pin chain c p wq pre post gate s0 sLast xg cells
        gateTruths coeffsOf cellIndex cols
      ⊆ runUnionBadEventAt L c p
          (fun th => SoundnessAssembly.outerBadEvent th
            (SoundnessAssembly.engine gdec hash th khash P c₀) c p (pre ++ gate :: post) s0
            logTruths gateTruths t pr coeffsOf)
          (fun th => SoundnessAssembly.indexBadEvent c.indexBits
            (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used
              (Verifier.derivedIndices (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
              cellIndex).1)
            (IndexPointZeroCheck.openedCells (cols cellIndex)
              (OpenedClaimFold.lift (OpenedClaimFold.cellRow
                (Verifier.derivedRounds (SoundnessAssembly.engine gdec hash th khash P c₀) c p)
                cellIndex)))) := by
  classical
  intro T hT
  simp only [assemblyFailureEvent, runUnionBadEventAt, Finset.mem_filter, Finset.mem_univ,
    true_and] at hT ⊢
  by_contra hcon
  push_neg at hcon
  exact hT (fun hacc hres => SoundnessAssembly.explicit_good_draw_assembly gdec hash
    (hashOf (boundedQueries L) T) khash P c₀ pin chain c p wq pre post gate s0 sLast xg cells
    logTruths gateTruths t pr coeffsOf cellIndex cols hacc hres hcon.1 hcon.2)

/-! ### 4.3 THE MASS -- NOT DELIVERED HERE; the follow-up module's contract

**THERE IS NO THEOREM IN THIS SECTION, AND THAT IS THE POINT.**  Section 4.2
puts the assembly's failure set inside the HASH-INDEXED `runUnionBadEventAt`;
sections 2 and 3 weigh the FIXED-event `runUnionBadEvent`.  The naive bridge
between them is a COVER: ONE fixed `JointChallengeSpace.jointBadEvent` containing
the engine's gate-lane bad set at EVERY hash, and ONE fixed
`IndexLanesOracle.guardedIndexBadEvent` containing the engine's committed cell
family at EVERY hash.  That cover is NOT KNOWN TO BE SATISFIABLE at any
non-degenerate run -- it holds only degenerately, at empty bad sets or at the
adopted `trivialLane` -- and this tree does not ship a theorem whose hypothesis
is not known to be satisfiable.  An earlier draft of this module carried a
`run_union_event_mono_of_cover` bridge and an `assembly_failure_mass_le`
corollary of it; both have been REMOVED for exactly that reason.

**WHAT THE MISSING STEP ACTUALLY IS.**  It is NOT an adaptive-prover treatment.
At the FIXED prover `p` of this module the hash enters the two events through a
single coordinate each:

* `SoundnessAssembly.outerBadEvent th E c p …` depends on `th` only through
  `TranscriptProvenance.gateAlphaElement th c p`, which is one coordinate of the
  joint draw already being weighed (the gate alpha is squeezed from block `0`,
  the derive digest -- `OuterInitial.derived_final_digest`, and the `gateTau`
  coordinates share that source digest);
* `SoundnessAssembly.indexBadEvent`'s COMMITTED cells depend on `th` only
  through the outer row point
  `OpenedClaimFold.cellRow (Verifier.derivedRounds (engine … th …) c p)`, while
  its SUPPLIED cells -- `OpenedClaimFold.boundCell p.used idx cellIndex` -- do
  not depend on the index draw at all.

So the bridge that is genuinely owed is a TWO-STAGE CONDITIONAL COUNT for this
fixed prover:

1. **Outer stage.**  The alpha coordinate is ONE uniform block-`0` squeeze.
   CONDITIONED on alpha, the gate-lane bad set is a FIXED finite set, and the
   outer diagonal event on `JointChallengeSpace.JointSpace` has mass at most
   `ChallengeUnionBound.combinedBound`.  This is the sequential-conditioning
   structure of the adopted `Audit.Wire3.OuterSequentialConditioning`: its
   `walk_union_mass_bound` / `adaptive_union_mass_bound` weigh exactly a family
   of per-coordinate bad sets that may depend on the realized prefix, and its
   `joint_union_bound_recovered` shows that structure recovers
   `JointChallengeSpace.joint_union_bound` at a frozen family.
2. **Index stage.**  CONDITIONED on the WHOLE outer draw, the index draw is
   uniform on `InstalledIndexSampler.IndexSpace`: the index squeezes live on
   oracle cells DISJOINT from the outer ones, which is exactly where ILO's cross
   distinctness (`IndexLanesOracle.combined_schedule_injective`, supplied here
   by `run_combined_schedule_injective_off_clash`) becomes load-bearing rather
   than decorative.  The index bad set, now FIXED by the conditioning, has mass
   at most `2 * ChallengeUnionBound.tauTerm c.indexBits` by
   `IndexLanesOracle.guarded_index_bad_event_mass_le`.

That is a CONTRACT for a follow-up module, stated here so that no reader mistakes
section 4.2's inclusion for a mass bound.  **It is not a theorem of this
module.** -/


/-! ## 5. NON-VACUITY -/

/-- (5) **THE ADDITIVE TERM IS NOT PROVED ON AN EMPTY EVENT.**  The adopted
`BirthdayClashBound.constantTable` -- the table that answers one fixed block
everywhere -- is in the extended clash event at every `d`, through its third
disjunct.  Inherited from ILO. -/
theorem constant_table_in_union_clash_event (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L) :
    constantTable L ∈ IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits hlenI :=
  IndexLanesOracle.constant_table_in_extended_clash_event L c (Verifier.statement p)
    (roundMessages p) p.used c.degreeBits hlenI

theorem union_clash_event_nonempty (L : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (hlenI : ∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits k).2.length ≤ L) :
    (IndexLanesOracle.extendedDigestClashEvent L c (Verifier.statement p)
      (roundMessages p) p.used c.degreeBits hlenI).Nonempty :=
  ⟨constantTable L, constant_table_in_union_clash_event L c p hlenI⟩

/-- (5) **THE GOOD EVENT IS NOT EMPTY EITHER, AT THE CLOSED WITNESS.**  Ninety-five
stages and `95 * 96 < 2 * 65536`, so ILO's `extended_chain_good_event_nonempty`
applies: the fibres the Fubini's good branch is about do exist. -/
theorem union_good_event_nonempty_at_the_envelope :
    (noClash (frameSel 381 OuterInitial.zeroDigest
        (IndexLanesOracle.prefixRoundIndexShape unionConfig (Verifier.statement unionProof)
          (roundMessages unionProof) unionProof.used unionConfig.degreeBits)
        union_length_budget_extended) (avoidBase OuterInitial.zeroDigest)
      (22 + 5 * unionConfig.degreeBits + 8)).Nonempty :=
  IndexLanesOracle.extended_chain_good_event_nonempty 381 unionConfig
    (Verifier.statement unionProof) (roundMessages unionProof) unionProof.used
    unionConfig.degreeBits (le_of_eq union_config_degree) union_length_budget_extended

/-- (5) **THE QUERY SET IS NOT FRAME-FREE**, so the adopted
`RandomOracleSqueezes.run_bound_trivial_at_frame_free` -- which reaches the same
shape of conclusion with additive term exactly `1` -- does not apply at
`L = 381`. -/
theorem union_query_set_is_not_frame_free : ¬ FrameFree (boundedQueries 381) :=
  bounded_queries_not_frame_free 381 (by norm_num)

/-- (5) The extended chain term is strictly below `1`, so the additive term of
the closed bound is not the trivial `1`.  Inherited from ILO. -/
theorem union_birthday_term_lt_one : (4560 : ℚ) / (Fintype.card Block : ℚ) < 1 :=
  IndexLanesOracle.extended_digest_clash_bound_lt_one

/-- (5) **EVERY HYPOTHESIS OF SECTIONS 1-3 HOLDS SIMULTANEOUSLY AT THE CLOSED
WITNESS.**  One conjunction, so that no reader has to check them one at a time
and so that nothing false is derivable from the package: the query budget, both
chain length budgets, the round count, the two envelope parameters, and the fact
that the query set answers frames.  Collected exactly as CCT collects its
own. -/
theorem union_hypotheses_are_satisfiable_at_the_envelope :
    64 ≤ 381
      ∧ unionConfig.degreeBits = 13
      ∧ unionConfig.indexBits = 8
      ∧ (roundMessages unionProof).length = unionConfig.degreeBits
      ∧ ConcreteChainThreading.LengthBudget 381 unionConfig unionProof 8
      ∧ (∀ k, 61 + (prefixRoundShape unionConfig (Verifier.statement unionProof)
          (roundMessages unionProof) k).2.length ≤ 381)
      ∧ (∀ k, 61 + (IndexLanesOracle.prefixRoundIndexShape unionConfig
          (Verifier.statement unionProof) (roundMessages unionProof) unionProof.used
          unionConfig.degreeBits k).2.length ≤ 381)
      ∧ ¬ FrameFree (boundedQueries 381) :=
  ⟨by norm_num, union_config_degree, union_config_index, union_round_count, union_length_budget,
    union_length_budget_chain, union_length_budget_extended, union_query_set_is_not_frame_free⟩

/-- (5) **THE CLOSED STATEMENT IS NOT THE VACUOUS `≤ 1`.**  The mass bound and
the strict inequality of its right-hand side, side by side.  Per HONESTY (iv)
this says the bound has content; it does NOT say the protocol has this soundness
error. -/
theorem run_union_at_the_envelope_is_not_vacuous (x : Element) :
    oracleProbability (boundedQueries 381) (runUnionBadEvent 381 unionConfig unionProof
        (JointChallengeSpace.jointBadEvent unionConfig.degreeBits x x (trivialLane x)
          (trivialLane x) (fun _ => x) (2 ^ unionConfig.degreeBits) (fun _ => []))
        (IndexLanesOracle.guardedIndexBadEvent unionConfig.indexBits [] []))
        ≤ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
          + 4560 / (Fintype.card Block : ℚ)
      ∧ ChallengeUnionBound.combinedBound 13 8 13 123 + 2 * ChallengeUnionBound.tauTerm 8
          + 4560 / (Fintype.card Block : ℚ) < 1 :=
  ⟨run_union_bad_draw_at_the_envelope_closed x, run_union_closed_bound_lt_one⟩

/-- (5) An event of mass strictly below `1` under the uniform counting law on
`OracleTable Q` is not all of `OracleTable Q`, so some table avoids it.  Pure
counting: were it everything, its mass would be `1`. -/
theorem exists_good_table_of_mass_lt_one (Q : Finset Transcript.Bytes)
    (E : Finset (OracleTable Q)) (h : oracleProbability Q E < 1) : ∃ T, T ∉ E := by
  by_contra hcon
  push_neg at hcon
  have heq : E = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon
  rw [heq, oracleProbability, Finset.card_univ, div_self (oracle_card_cast_pos Q).ne'] at h
  exact lt_irrefl _ h

/-- (5) **THE CLOSED BOUND IS DISCHARGEABLE: A GOOD TABLE EXISTS.**  At the closed
witness the union bad event is not all of `OracleTable (boundedQueries 381)` --
its mass is below `1` by `run_union_at_the_envelope_is_not_vacuous` -- so SOME
table leaves both the run's outer/gate draw and the run's index draw good.

READ HONESTY (9) BEFORE QUOTING THIS.  The closed witness's index half is
`IndexLanesOracle.guardedIndexBadEvent 8 [] []`, whose guard
`IndexPointZeroCheck.CellsDifferOnCube 8 [] []` is FALSE, so that half is `∅`.
This theorem therefore certifies DISCHARGEABILITY of the closed bound -- the good
event it names is inhabited -- and certifies NOTHING about a non-trivial index
mass.  The outer half is the adopted `trivialLane` instance, likewise closed. -/
theorem run_union_good_table_exists_at_the_envelope (x : Element) :
    ∃ T, T ∉ runUnionBadEvent 381 unionConfig unionProof
        (JointChallengeSpace.jointBadEvent unionConfig.degreeBits x x (trivialLane x)
          (trivialLane x) (fun _ => x) (2 ^ unionConfig.degreeBits) (fun _ => []))
        (IndexLanesOracle.guardedIndexBadEvent unionConfig.indexBits [] []) :=
  exists_good_table_of_mass_lt_one _ _
    (lt_of_le_of_lt (run_union_at_the_envelope_is_not_vacuous x).1
      (run_union_at_the_envelope_is_not_vacuous x).2)

end Audit.Wire3.RunLevelUnionBound
