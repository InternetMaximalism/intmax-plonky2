import Audit.Wire3.GrindingUnionBound

/-!
# THE GRINDER'S OWN LANE, AND THE ZERO-PROBE IDENTITY

## The two gaps this module addresses

The adopted `Audit.Wire3.GrindingUnionBound` (GUB) names exactly two things it
does not deliver.  HONESTY (v): "WHAT IS STILL MISSING is the PAIRING: a
`grindLaneOfGrinder g` whose round-`r` message is literally `g`'s stage-`22 + 5 r`
absorb payload as a `List Element`.  Two things it would need are absent here -- a
bytes-to-elements decoder for the payload, and a truncation of the unrestricted
stage-digest argument the adopted `GrindingStrategy.absorb` is handed".
HONESTY (ii) and section 3: "Subsumption would additionally need
`grindingFullBadEvent` at `q = 0` and `grindingOfStrategy strat` to be the adopted
`RawBlockLanes.rawFullBadEvent` at `strat`, as sets; that identity is NOT proved
anywhere in this tree".

Both are delivered here.

## What is proved

1. THE DECODER (section 1).  `elementOfBytes` reads three little-endian eight-byte
   limbs and reduces them, in the limb layout of the adopted
   `Spongefish.decodeCanonicalExt3` and by the reduction of the adopted
   `Spongefish.reduceChallenge`; `element_of_bytes_agrees_with_canonical_decode`
   shows it AGREES with the adopted partial decoder wherever that succeeds, so it
   is the adopted prover-message parser totalized, not a new encoding.  THE
   AGREEMENT IS ONE-DIRECTIONAL AND ITS DOMAIN IS NARROW: the adopted decoder
   succeeds only on twenty-four bytes whose three limbs are already below the
   modulus, and OFF that domain the totalization INVENTS -- `canonical_decode_short`
   and `decoder_invents_on_rejected_payloads` exhibit two DIFFERENT payloads that
   the deployed parser rejects and that `decodeElements` gives the SAME non-empty
   round message, so `decodeElements` is not injective and off the adopted domain
   the lane's message is a MODELLING CHOICE, not the verifier's reading.
   `decodeElements` chunks a payload into elements; `decode_elements_length_le`
   bounds the message length by the payload length, `element_of_bytes_of_element`
   and `decode_elements_of_element` show the decoder is ONTO, and
   `decode_unit_repeat_length` shows the length bound is ATTAINED.
2. THE RECONSTRUCTION (section 2).  `grinderHist` and `grinderProbes` rebuild, out
   of the run's own answer list alone, the two history arguments the run hands the
   stage absorb -- including the TRUNCATION HONESTY (v) names, which
   `grinder_hist_is_run_history` shows is not a modelling choice but what the
   adopted `GrindingQueryBound.run_ans_eq` already does.  `digestLookup` rebuilds
   the challenge ORACLE (a function of a digest) out of the lane's stage-indexed
   challenge VIEW, and `digest_lookup_at_of_determined` shows it returns the right
   column at EVERY table, with no conditioning event, because the run's raw view
   is a function of the stage digest.  TWO SEPARATE FACTS ARE AT WORK HERE: the
   TOTALITY of `digestLookup` closes the type mismatch (digest-indexed against
   stage-indexed) by definition alone, with no content; its CORRECTNESS under a
   shared digest is exactly `grinder_table_view_determined` and nothing else, and
   `digest_lookup_wrong_without_determinacy` shows that determinacy lemma is
   load-bearing rather than implied by the totality -- at a history with
   `h 0 = h 1` and a view with `ch 0 ≠ ch 1` the lookup returns the WRONG column.
3. THE PAIRED LANE AND THE PAIRING (sections 3 and 4).  `grinderLane e0 q g tr cl tcl`
   is a GUB `GrindLane` whose round-`r` message is `grinderMessage`, and
   `grinder_lane_message_is_absorbed_payload` is the pairing: at EVERY table, that
   message IS `decodeElements` of the payload `g`'s stage-`22 + 5 r` ABSORB emits,
   at the very history, the very probe answers and the very challenge answers the
   run hands it.  `grinder_run_frame_carries_the_lane_message` puts the same
   payload inside the byte string the run actually asked the oracle.
4. THE RESTATED UNION BOUND (section 5).
   `grinder_paired_union_bad_draw_probability_le_combined` is GUB's headline with
   the free lane family replaced by the paired lanes:

     `oracleProbability (boundedQueries L) (grindingFullBadEvent … (grinderLane …) (grinderLane …) …)`
       `<= ChallengeUnionBound.combinedBound d quo d constraints`
          `+ N (N + 1) / 2 / |Block|`,  `N = (22 + 5 d) (q + 1)`.

   Nothing is added and nothing is dropped: the constant is GUB's, term for term.
   TWO RESTRICTIONS CUT THE CLASS IT COVERS, and both are stated as theorems, not
   as prose.  FIRST, THE BYTE BUDGET.  This bound covers exactly those
   `ChallengeRestricted` grinders whose absorb payload is at most
   `min 120 (24 * (quo + 2))` bytes at EVERY coupled stage -- at the adopted
   `quo = 8`, at most 120 bytes, i.e. five encoded field elements per absorb
   (`fitlog_iff`, `fitgate_iff`, `budget_is_five_elements`, `five_elements_fit`,
   `six_elements_do_not_fit`).  A grinder that absorbs six (`longMessageGrinder`)
   is outside it, and no adopted lemma bounds the bad-draw mass of its paired
   lanes.  SECOND, AND LARGER: BOTH OUTER LANES CARRY THE SAME ROUND MESSAGE.
   `both_paired_lanes_carry_the_same_message` is a `rfl`: the grinder emits ONE
   payload at stage `22 + 5 r` and `grinderMessage` is the only message
   `grinderLane` installs, so the LOG lane and the GATE lane of the headline are
   definitionally equal as message families, while in the protocol they are two
   distinct coupled prover messages.
5. THE WITNESS (section 6).  `selectorGrinder` probes at its own digest and emits
   the twenty-four bytes of `1` WHEN AND ONLY WHEN its first probe came back the
   constant table's block, and of `0` otherwise.  It is `GrindingBounded`,
   `ChallengeRestricted`, provably reads its probe answers
   (`selector_grinder_reads_probes`), and provably is NOT the lift of any adopted
   `StrategyChainBound.Strategy` (`selector_grinder_is_not_transcript_restricted`).
   `selector_grinder_paired_target_zero_nonempty` exhibits an inhabited round-`0`
   target for ITS OWN paired lane, and
   `selector_grinder_paired_bound_at_thirteen` closes the instance at thirteen
   rounds with every hypothesis discharged.
6. THE ZERO-PROBE IDENTITY (section 7).  At `q = 0` and the adopted
   `grindingOfStrategy strat`, the grinding chain's stage digests, its raw
   challenge view, its digest triples, its NO-CLASH EVENT, its per-round claims,
   bad sets, targets and round events, its outer bad event, its gate tau column
   and its gate tau and gate alpha events all coincide with the adopted
   `RawBlockLanes` ones, and `zero_probe_full_bad_event_eq` concludes
   `grindingFullBadEvent = RawBlockLanes.rawFullBadEvent` as `Finset`s.
   `grinding_bound_at_zero_probes_is_the_adopted_raw_bound` then DERIVES the
   adopted `RawBlockLanes.raw_full_bad_draw_probability_le_combined` from GUB's
   headline, with the clash term collapsed to the adopted chain's
   `N (N + 1) / 2` at `N = 22 + 5 d` (`zero_probe_clash_count`).
7. THE SCOPE (section 8).  `paired_lane_is_not_a_lifted_raw_lane` shows the paired
   lane is outside the adopted `RawLane` image, and
   `paired_message_is_not_run_independent` strengthens that to an
   EMBEDDING-INDEPENDENT form: the paired lane's message is not
   `fun r _ ch => f r ch` for ANY `f` at all, so the scope claim does not depend
   on a choice of lift.  `long_message_grinder_paired_lane_is_not_log_bounded` is
   a NEGATIVE RESULT: a legal `GrindingBounded` prover whose paired lane violates
   the adopted log-lane degree bound.  GUB's own headline still applies to that
   prover with FREE lanes; what no adopted lemma and nothing here bounds is the
   bad-draw mass of its PAIRED lanes.

## HONESTY

(i) THIS IS THE RANDOM-ORACLE MODEL, NOT KECCAK, and it inherits every assumption
of GUB's own honesty header.  Everything below is about the uniform counting law
on `RandomOracleSqueezes.OracleTable (boundedQueries L)`.  Replacing the deployed
Keccak by a table drawn from that law is an assumption with no proof anywhere in
this tree.

(ii) WHAT SECTION 5 DOES AND DOES NOT CHANGE ABOUT GUB.  It changes WHOSE bad sets
are bounded: GUB's lanes are quantified freely and, in its own words, "nothing
below says the lanes carry the grinder's own round messages"; the lanes of
section 5 do carry them.  IT DOES NOT CHANGE THE CONSTANT, IT DOES NOT WEAKEN ANY
GUB HYPOTHESIS, AND IT DOES NOT ENLARGE THE CLASS OF PROVERS -- it NARROWS it,
by (iv) and (v) below.  `ChallengeRestricted` is still assumed and still not
discharged -- GUB HONESTY (ii) and (iii), and its `preReadGrinder`, stand
unchanged.  The pre-read attack is still uncharged, and the constant such a
prover should pay is still proved nowhere.  In particular, NOTHING BELOW SHOWS
THAT GRINDING BUYS A PROVER ANYTHING: no searching prover is exhibited in this
module, and the one prover that would search, GUB's `preReadGrinder`, is excluded
by `ChallengeRestricted` and not by anything proved here.

(iii) THE PAIRING IS FOR THE MESSAGE ONLY.  A `GrindLane` has four fields; only
`message` is paired.  `truth`, `claim` and `truthClaim` remain free parameters,
exactly as the adopted `RawBlockLanes.rawLogLaneOfStrategy` leaves them free: they
are the HONEST column and the initial running claims, which are not the prover's
data at all.  Pairing them with `g` is not attempted here and no adopted lemma
does it.

(iv) THE DEGREE BOUND IS NOW A BYTE BUDGET, IT IS A THEOREM, AND IT EXCLUDES
PROVERS.  Section 5 converts the prover's absorb-payload length into the adopted
degree bounds `5` and `quo + 2` through the decoder.  `fitlog_iff` and
`fitgate_iff` pin the class exactly -- `hfitlog : (p + 23) / 24 ≤ 5` is EXACTLY
`p ≤ 120`, and `hfitgate : (p + 23) / 24 ≤ quo + 2` is EXACTLY
`p ≤ 24 * (quo + 2)` -- and `budget_is_five_elements` collapses the conjunction,
for `quo ≥ 3`, to the single condition `p ≤ 120`.  SO: the bound covers exactly
those `ChallengeRestricted` grinders whose absorb payload is at most
`min 120 (24 * (quo + 2))` bytes at EVERY coupled stage; at the adopted `quo = 8`,
at most 120 bytes, i.e. five encoded field elements per absorb.  The boundary is
not one or two elements and it is not slack: `five_elements_fit` puts
`unitRepeat 5` INSIDE the budget and `six_elements_do_not_fit` puts
`unitRepeat 6` exactly one element OUT.
`long_message_grinder_paired_lane_is_not_log_bounded` exhibits a legal
`GrindingBounded` prover that absorbs six, so `hfitlog` cannot be discharged for
it; GUB's headline still applies to it with FREE lanes, and what NO adopted lemma
and nothing here bounds is the bad-draw mass of its PAIRED lanes.  This is the
honest scope, not a hidden assumption.

(v) A LARGER RESTRICTION: BOTH OUTER LANES CARRY THE SAME ROUND MESSAGE.
`both_paired_lanes_carry_the_same_message` is a `rfl`:
`(grinderLane e0 q g tr1 cl1 tcl1).message = (grinderLane e0 q g tr2 cl2 tcl2).message`
for ANY two honest columns and initial claims.  The grinder emits ONE payload at
stage `22 + 5 r`, and `grinderMessage` is the only message `grinderLane` ever
installs, so in the headline of section 5 the LOG lane and the GATE lane carry
IDENTICAL round messages -- while in the protocol these are two distinct coupled
prover messages.  This is a STRICTLY LARGER restriction on the covered class than
the byte budget of (iv): a prover whose log-lane and gate-lane coupled messages
differ at any round is outside section 5's headline entirely, whatever its
payload lengths are, and no adopted lemma bounds the bad-draw mass of ITS paired
lanes either.  Nothing in this module widens `GrindingStrategy` to emit two
payloads per coupled stage; doing so is not attempted here.

(vi) THE ROUND SCHEDULE IS GUB's AND IS NOT DERIVED.  `grinderMessage` identifies
coupled round `r` with chain stage `22 + 5 r`, which is the stage index GUB's
`GrindCausal` and `roundStage` already use.  That the deployed protocol absorbs
round `r`'s coupled message at exactly that stage is the adopted
`OuterLaneTransport` / `ReducedFullTransport` reading; it is not re-derived here,
and no run-level schedule is threaded onto the grinding chain, as the adopted
`RunLevelTransportAudit` does for a transcript-restricted prover.

(vii) WHAT THE ZERO-PROBE IDENTITY IS AND IS NOT.  It says GUB's class CONTAINS the
adopted `RawBlockLanes` line -- same event, same bound, same constant.  It does
NOT say GUB's bound is stronger in any other respect, and it says nothing about
provers with `q > 0` beyond what GUB already proved.  FOUR of its steps are
DEFINITIONAL and the rest are not; `zero_probe_lane_message_is_raw`,
`zero_probe_lane_truth_is_raw`, `zero_probe_state_zero` and
`zero_probe_claims_zero` are the definitional ones and
are stated as such, while `zero_probe_state_eq` (the adopted
`GrindingQueryBound.grinding_chain_of_strategy_chain`, an induction) and
`zero_probe_no_clash_eq` (an index shift plus injectivity of
`OuterChallenge.digestBlock`, because the two conditioning events have DIFFERENT
SHAPES) are genuine proofs.

(viii) THESE MASSES ARE NOT THE SYSTEM'S SOUNDNESS ERROR.  No extractor, no
knowledge soundness and no adaptive Fiat--Shamir soundness statement is proved
here.  The index lanes, the WHIR folding transcript and the Merkle openings are
not covered here any more than they are in GUB.

(ix) NO CARDINALITY IS EVALUATED.  `Fintype.card Block` appears only inside
statements transported verbatim from GUB and the adopted `RawBlockLanes`; no
cardinality of `Element`, `Block` or `OuterChallenge.DigestTriple` is ever
evaluated numerically or handed to a `ring` or `omega` goal.  `Finset.univ` does
not appear in any STATEMENT of this module.  The one occurrence of the name in
the file is this sentence; `Finset.mem_univ` is used inside three proofs.

(x) THE REDUCTION OF SECTION 7 IS NON-CIRCULAR, AND THAT WAS CHECKED RATHER THAN
ASSERTED.  A transitive constant-dependency walk over the stored proof terms
establishes it: neither `grinding_bound_at_zero_probes_is_the_adopted_raw_bound`
nor its closed instance `zero_probe_reduction_at_thirteen` touches the adopted
`RawBlockLanes.raw_full_bad_draw_probability_le_combined` anywhere in its
transitive dependencies, while the reduction DOES use
`GrindingUnionBound.grinding_union_bad_draw_probability_le_combined`.  The only
`RawBlockLanes` constant the reduction reaches is `rawFullBadEvent`, which is in
its statement.  So the adopted raw bound is genuinely DERIVED from the grinding
headline and is not being quoted back to itself.
-/

namespace Audit.Wire3.GrindLanePairing

open Audit.Wire3
open Audit.Wire3.GoldilocksExt3Field
open Audit.Wire3.RandomOracleSqueezes
open Audit.Wire3.BirthdayClashBound
open Audit.Wire3.StrategyChainBound
open Audit.Wire3.OuterLaneTransport
open Audit.Wire3.ReducedFullTransport
open Audit.Wire3.RawBlockLanes
open Audit.Wire3.GrindingQueryBound
open Audit.Wire3.GrindingUnionBound

/-! ## 1. THE BYTE DECODER -/

/-- **ONE FIELD ELEMENT OUT OF A BYTE STRING.**  Three little-endian eight-byte
limbs, reduced into the canonical range, in the limb layout of the adopted
`Spongefish.decodeCanonicalExt3` and by the reduction of the adopted
`Spongefish.reduceChallenge`.  It is TOTAL where the adopted decoder is partial:
`element_of_bytes_agrees_with_canonical_decode` says the two agree wherever the
adopted one succeeds. -/
def elementOfBytes (bs : Transcript.Bytes) : Element :=
  ⟨⟨⟨Arithmetic.reduce (Transcript.fromLe (bs.take 8)),
      Arithmetic.reduce (Transcript.fromLe ((bs.drop 8).take 8)),
      Arithmetic.reduce (Transcript.fromLe ((bs.drop 16).take 8))⟩,
    Arithmetic.reduce_canonical _, Arithmetic.reduce_canonical _,
    Arithmetic.reduce_canonical _⟩⟩

/-- **AND THE TWENTY-FOUR BYTES OF ONE FIELD ELEMENT**, the adopted
`Transcript.fieldBytes` layout limb by limb. -/
def bytesOfElement (x : Element) : Transcript.Bytes :=
  Transcript.le 8 x.toVerifier.val.c0 ++
    (Transcript.le 8 x.toVerifier.val.c1 ++ Transcript.le 8 x.toVerifier.val.c2)

theorem bytes_of_element_length (x : Element) : (bytesOfElement x).length = 24 := by
  simp only [bytesOfElement, List.length_append, Transcript.le_length]

theorem take_of_append (A B : Transcript.Bytes) (n : Nat) (h : A.length = n) :
    (A ++ B).take n = A := by
  subst h; exact List.take_left A B

theorem drop_of_append (A B : Transcript.Bytes) (n : Nat) (h : A.length = n) :
    (A ++ B).drop n = B := by
  subst h; exact List.drop_left A B

theorem modulus_lt_byte_power : Arithmetic.modulus < 256 ^ 8 := by
  norm_num [Arithmetic.modulus]

theorem reduce_of_canonical (n : Nat) (h : n < Arithmetic.modulus) :
    Arithmetic.reduce n = n := Nat.mod_eq_of_lt h

/-- (1) **THE DECODER IS ONTO.**  Every field element is the decoding of its own
twenty-four bytes, so the lane class of section 3 is not a class of lanes whose
messages are constrained to a proper subset of the field. -/
theorem element_of_bytes_of_element (x : Element) :
    elementOfBytes (bytesOfElement x) = x := by
  have hc := x.toVerifier.property
  have h0 : (bytesOfElement x).take 8 = Transcript.le 8 x.toVerifier.val.c0 :=
    take_of_append _ _ 8 (Transcript.le_length 8 _)
  have hd0 : (bytesOfElement x).drop 8
      = Transcript.le 8 x.toVerifier.val.c1 ++ Transcript.le 8 x.toVerifier.val.c2 :=
    drop_of_append _ _ 8 (Transcript.le_length 8 _)
  have h1 : ((bytesOfElement x).drop 8).take 8 = Transcript.le 8 x.toVerifier.val.c1 := by
    rw [hd0]; exact take_of_append _ _ 8 (Transcript.le_length 8 _)
  have hd16 : (bytesOfElement x).drop 16 = Transcript.le 8 x.toVerifier.val.c2 := by
    have : (bytesOfElement x).drop 16 = ((bytesOfElement x).drop 8).drop 8 := by
      rw [List.drop_drop]
    rw [this, hd0]
    exact drop_of_append _ _ 8 (Transcript.le_length 8 _)
  have h2 : ((bytesOfElement x).drop 16).take 8 = Transcript.le 8 x.toVerifier.val.c2 := by
    rw [hd16, List.take_all_of_le (le_of_eq (Transcript.le_length 8 _))]
  refine element_eq _ _ (Subtype.ext ?_)
  show (⟨Arithmetic.reduce (Transcript.fromLe ((bytesOfElement x).take 8)),
        Arithmetic.reduce (Transcript.fromLe (((bytesOfElement x).drop 8).take 8)),
        Arithmetic.reduce (Transcript.fromLe (((bytesOfElement x).drop 16).take 8))⟩ :
      Arithmetic.Ext3) = x.toVerifier.val
  rw [h0, h1, h2,
    Transcript.fromLe_le_roundtrip 8 _ (lt_trans hc.1 modulus_lt_byte_power),
    Transcript.fromLe_le_roundtrip 8 _ (lt_trans hc.2.1 modulus_lt_byte_power),
    Transcript.fromLe_le_roundtrip 8 _ (lt_trans hc.2.2 modulus_lt_byte_power),
    reduce_of_canonical _ hc.1, reduce_of_canonical _ hc.2.1, reduce_of_canonical _ hc.2.2]

/-- (1) **THE DECODER EXTENDS THE ADOPTED PARSER.**  Wherever the adopted
`Spongefish.decodeCanonicalExt3` returns a value -- that is, on twenty-four bytes
whose three limbs are already canonical -- `elementOfBytes` returns the same
value.  So this is the adopted prover-message decoder, totalized, not a new one. -/
theorem element_of_bytes_agrees_with_canonical_decode (bs : Transcript.Bytes)
    (x : Verifier.Ext3) (h : Spongefish.decodeCanonicalExt3 bs = some x) :
    elementOfBytes bs = ⟨x⟩ := by
  obtain ⟨-, h0, h1, h2⟩ := Spongefish.canonical_decode_preserves_raw_limbs bs x h
  refine element_eq _ _ (Subtype.ext ?_)
  show (⟨Arithmetic.reduce (Transcript.fromLe (bs.take 8)),
        Arithmetic.reduce (Transcript.fromLe ((bs.drop 8).take 8)),
        Arithmetic.reduce (Transcript.fromLe ((bs.drop 16).take 8))⟩ :
      Arithmetic.Ext3) = x.val
  have hc := x.property
  rw [← h0, ← h1, ← h2, reduce_of_canonical _ hc.1, reduce_of_canonical _ hc.2.1,
    reduce_of_canonical _ hc.2.2]

/-- **A BYTE STRING, CHUNKED INTO FIELD ELEMENTS.**  `n` is a fuel bound; the
public `decodeElements` supplies enough of it for the string's own length. -/
def decodeElementsAux : Nat → Transcript.Bytes → List Element
  | 0, _ => []
  | n + 1, bs =>
      match bs with
      | [] => []
      | b :: rest =>
          elementOfBytes ((b :: rest).take 24) :: decodeElementsAux n ((b :: rest).drop 24)

/-- **THE DECODER FROM ABSORBED BYTES TO A ROUND MESSAGE.**  This is the map
HONESTY (v) of the adopted `GrindingUnionBound` names as missing: the payload a
grinding prover hands its stage absorb, read as the list of field elements the
lane's round message has to be. -/
def decodeElements (bs : Transcript.Bytes) : List Element :=
  decodeElementsAux ((bs.length + 23) / 24) bs

theorem decode_elements_aux_length_le (n : Nat) (bs : Transcript.Bytes) :
    (decodeElementsAux n bs).length ≤ n := by
  induction n generalizing bs with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
      cases bs with
      | nil => exact Nat.zero_le _
      | cons b rest =>
          show (elementOfBytes _ :: decodeElementsAux k ((b :: rest).drop 24)).length ≤ k + 1
          rw [List.length_cons]
          exact Nat.succ_le_succ (ih _)

/-- (1) **THE LENGTH THE DECODER CAN PRODUCE IS FIXED BY THE PAYLOAD LENGTH.**
This is what turns the adopted `GrindLaneBounded` degree bound into a bound on
the prover's absorb length. -/
theorem decode_elements_length_le (bs : Transcript.Bytes) :
    (decodeElements bs).length ≤ (bs.length + 23) / 24 :=
  decode_elements_aux_length_le _ bs

/-- (1) A payload of at most `p` bytes decodes to at most `(p + 23) / 24`
elements. -/
theorem decode_elements_length_le_of_payload (bs : Transcript.Bytes) (p : Nat)
    (h : bs.length ≤ p) : (decodeElements bs).length ≤ (p + 23) / 24 :=
  le_trans (decode_elements_length_le bs) (Nat.div_le_div_right (by omega))

/-- (1) **AND EVERY SINGLETON MESSAGE IS REACHED.**  Together with
`element_of_bytes_of_element` this says the decoder is onto the one-element
messages, so a lane built through it is not a lane whose messages are
degenerate. -/
theorem decode_elements_aux_nil (n : Nat) : decodeElementsAux n [] = [] := by
  cases n with
  | zero => rfl
  | succ k => rfl

theorem decode_elements_aux_singleton (n : Nat) (bs : Transcript.Bytes) (hne : bs ≠ [])
    (hshort : bs.length ≤ 24) : decodeElementsAux (n + 1) bs = [elementOfBytes bs] := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons b rest =>
      have htake : (b :: rest).take 24 = b :: rest := List.take_all_of_le hshort
      have hdrop : (b :: rest).drop 24 = [] := by
        rw [← List.length_eq_zero, List.length_drop]
        omega
      show elementOfBytes ((b :: rest).take 24)
          :: decodeElementsAux n ((b :: rest).drop 24)
        = [elementOfBytes (b :: rest)]
      rw [htake, hdrop, decode_elements_aux_nil]

theorem decode_elements_of_element (x : Element) :
    decodeElements (bytesOfElement x) = [x] := by
  have hlen := bytes_of_element_length x
  have hne : bytesOfElement x ≠ [] := by
    intro h
    rw [h] at hlen
    exact absurd hlen (by decide)
  have hfuel : ((bytesOfElement x).length + 23) / 24 = 0 + 1 := by omega
  rw [decodeElements, hfuel,
    decode_elements_aux_singleton 0 _ hne (le_of_eq hlen), element_of_bytes_of_element]

/-- A payload of `n` field elements, in the adopted twenty-four-byte limb
layout. -/
def unitRepeat : Nat → Transcript.Bytes
  | 0 => []
  | n + 1 => bytesOfElement 1 ++ unitRepeat n

theorem unit_repeat_length (n : Nat) : (unitRepeat n).length = 24 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show (bytesOfElement 1 ++ unitRepeat k).length = 24 * (k + 1)
      rw [List.length_append, bytes_of_element_length, ih]
      omega

theorem decode_elements_aux_chunk (n : Nat) (A B : Transcript.Bytes) (hA : A.length = 24) :
    decodeElementsAux (n + 1) (A ++ B) = elementOfBytes A :: decodeElementsAux n B := by
  cases A with
  | nil => exact absurd hA (by decide)
  | cons a rest =>
      show elementOfBytes (((a :: rest) ++ B).take 24)
          :: decodeElementsAux n (((a :: rest) ++ B).drop 24)
        = elementOfBytes (a :: rest) :: decodeElementsAux n B
      rw [take_of_append _ _ 24 hA, drop_of_append _ _ 24 hA]

theorem decode_elements_aux_unit_repeat (n : Nat) :
    (decodeElementsAux n (unitRepeat n)).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show (decodeElementsAux (k + 1) (bytesOfElement 1 ++ unitRepeat k)).length = k + 1
      rw [decode_elements_aux_chunk k _ _ (bytes_of_element_length 1), List.length_cons, ih]

/-- (1) **THE DECODER'S LENGTH BOUND IS ATTAINED.**  A payload of `n` encoded
elements decodes to exactly `n` of them, so the byte budget of section 5 is a
real constraint rather than a slack one. -/
theorem decode_unit_repeat_length (n : Nat) : (decodeElements (unitRepeat n)).length = n := by
  have hlen := unit_repeat_length n
  have hfuel : ((unitRepeat n).length + 23) / 24 = n := by omega
  rw [decodeElements, hfuel]
  exact decode_elements_aux_unit_repeat n

/-! ### 1b. WHAT THE AGREEMENT WITH THE ADOPTED PARSER DOES NOT SAY

`element_of_bytes_agrees_with_canonical_decode` is ONE-DIRECTIONAL, and its domain
is narrow: the adopted `Spongefish.decodeCanonicalExt3` succeeds only on payloads
of exactly twenty-four bytes whose three limbs are all already below the modulus.
The three theorems below say what happens OFF that domain, so that the scope of
the pairing is not overstated. -/

/-- (1b) Two byte strings with equal limbs decode to the same element. -/
theorem elem_eq_of_limbs (A B : Transcript.Bytes)
    (h0 : Transcript.fromLe (A.take 8) = Transcript.fromLe (B.take 8))
    (h1 : Transcript.fromLe ((A.drop 8).take 8) = Transcript.fromLe ((B.drop 8).take 8))
    (h2 : Transcript.fromLe ((A.drop 16).take 8) = Transcript.fromLe ((B.drop 16).take 8)) :
    elementOfBytes A = elementOfBytes B := by
  refine element_eq _ _ (Subtype.ext ?_)
  show (⟨Arithmetic.reduce (Transcript.fromLe (A.take 8)),
        Arithmetic.reduce (Transcript.fromLe ((A.drop 8).take 8)),
        Arithmetic.reduce (Transcript.fromLe ((A.drop 16).take 8))⟩ : Arithmetic.Ext3)
      = ⟨Arithmetic.reduce (Transcript.fromLe (B.take 8)),
        Arithmetic.reduce (Transcript.fromLe ((B.drop 8).take 8)),
        Arithmetic.reduce (Transcript.fromLe ((B.drop 16).take 8))⟩
  rw [h0, h1, h2]

/-- (1b) **THE ADOPTED PARSER REJECTS ANYTHING THAT IS NOT EXACTLY TWENTY-FOUR
BYTES.** -/
theorem canonical_decode_short (bs : Transcript.Bytes) (h : bs.length ≠ 24) :
    Spongefish.decodeCanonicalExt3 bs = none := by
  unfold Spongefish.decodeCanonicalExt3
  dsimp only
  rw [dif_neg]
  intro hc
  exact h hc.1

/-- (1b) **OFF THE ADOPTED PARSER'S DOMAIN THE TOTALIZATION INVENTS.**  Two
DIFFERENT payloads, both REJECTED by the adopted `Spongefish.decodeCanonicalExt3`,
are given the SAME non-empty round message by `decodeElements`.  So
`decodeElements` is NOT injective, and off the adopted domain the lane's round
message is a MODELLING CHOICE rather than the deployed verifier's reading of the
payload.

This is CONSERVATIVE rather than unsound for the pairing of section 4 -- that
pairing is an equation true by construction, and `element_of_bytes_of_element`
rules out a degenerate image -- but it IS a place where the paired lane's message
is this module's convention and not an adopted one. -/
theorem decoder_invents_on_rejected_payloads :
    Spongefish.decodeCanonicalExt3 [(0 : Transcript.Byte)] = none ∧
    Spongefish.decodeCanonicalExt3 [(0 : Transcript.Byte), 0] = none ∧
    decodeElements [(0 : Transcript.Byte)] = decodeElements [(0 : Transcript.Byte), 0] ∧
    (decodeElements [(0 : Transcript.Byte)]).length = 1 := by
  refine ⟨canonical_decode_short _ (by decide), canonical_decode_short _ (by decide), ?_, ?_⟩
  · have hlim : elementOfBytes ([(0 : Transcript.Byte)].take 24)
        = elementOfBytes ([(0 : Transcript.Byte), 0].take 24) :=
      elem_eq_of_limbs _ _ (by decide) (by decide) (by decide)
    show elementOfBytes ([(0 : Transcript.Byte)].take 24)
        :: decodeElementsAux 0 ([(0 : Transcript.Byte)].drop 24)
      = elementOfBytes ([(0 : Transcript.Byte), 0].take 24)
        :: decodeElementsAux 0 ([(0 : Transcript.Byte), 0].drop 24)
    rw [hlim]
    rfl
  · show (elementOfBytes ([(0 : Transcript.Byte)].take 24)
      :: decodeElementsAux 0 ([(0 : Transcript.Byte)].drop 24)).length = 1
    rfl

/-! ## 2. THE LANE-SIDE RECONSTRUCTION OF WHAT THE GRINDER IS HANDED -/

/-- THE BLOCK THE ADOPTED `BirthdayClashBound.constantTable` RETURNS AT EVERY
QUERY, and the block of the adopted `OuterInitial.zeroDigest`. -/
def unitTarget : Block := OuterChallenge.digestBlock OuterInitial.zeroDigest

theorem unit_target_from_le : Transcript.fromLe unitTarget.val = 0 := by decide

theorem one_block_ne_unit_target : oneDigestBlock.val ≠ unitTarget.val := by
  intro h
  have h1 : Transcript.fromLe (Transcript.le 32 1) = 1 :=
    Transcript.fromLe_le_roundtrip 32 1 (small_lt_byte_power 1 (by norm_num))
  have h2 : (oneDigestBlock.val : Transcript.Bytes) = Transcript.le 32 1 := rfl
  rw [← h2, h, unit_target_from_le] at h1
  exact absurd h1 (by decide)

/-- **THE STAGE DIGESTS, OFF THE RUN'S OWN ANSWER LIST, TRUNCATED AT STAGE `k`.**
The adopted `GrindingQueryBound.stateOf` below stage `k` and the base digest
beyond it -- which is exactly what the run's own truncated answer list reports at
the stage-`k` absorb position (`grinder_hist_is_run_history`).  The truncation is
the second of the two obstructions the adopted `GrindingUnionBound` HONESTY (v)
names; it is discharged here by reading it off the run rather than by assuming
the absorb ignores the future. -/
def grinderHist (e0 : Transcript.Digest) (q k : Nat) (a : Nat → Block) :
    Nat → Transcript.Digest :=
  fun j => if j ≤ k then stateOf e0 q a j else e0

/-- **THE PROBE ANSWERS, OFF THE RUN'S OWN ANSWER LIST, TRUNCATED AT STAGE `k`'s
ABSORB POSITION.** -/
def grinderProbes (e0 : Transcript.Digest) (q k : Nat) (a : Nat → Block) :
    Nat → Nat → Block :=
  fun k2 i =>
    if slotPos q k2 i < slotPos q k q then a (slotPos q k2 i)
    else OuterChallenge.digestBlock e0

theorem digest_of_bytes_eq (d e : Transcript.Digest) (h : d.bytes = e.bytes) : d = e := by
  cases d; cases e; cases h; rfl

/-- **THE CHALLENGE ORACLE, REBUILT FROM THE STAGE-INDEXED VIEW.**  A
`GrindingQueryBound.GrindingStrategy`'s absorb is handed the challenge oracle as a
function of a DIGEST; a `GrindingUnionBound.GrindLane`'s message is handed it as a
function of a STAGE INDEX.  `digestLookup h ch k` turns the second into the first
by looking the digest up among `h 0, …, h k`.  On the chain's no-clash event those
`k + 1` digests are distinct, so the lookup returns the stage's own column
(`digest_lookup_at`); off it, `digest_lookup_at` no longer applies.
`grinder_lookup_is_challenges` nevertheless shows the lookup AGREES WITH THE RUN
at every table, via `grinder_table_view_determined`.

TWO DIFFERENT FACTS ARE IN PLAY, and only one of them is free.  That this
definition is TOTAL -- that it produces some column for every digest -- closes the
digest-indexed/stage-indexed type mismatch by definition alone and carries no
content.  That it produces the RIGHT column when two stages share a digest is
exactly `grinder_table_view_determined` and nothing else:
`digest_lookup_wrong_without_determinacy` exhibits `h 0 = h 1` with
`ch 0 ≠ ch 1` at which `digestLookup h ch 1 (h 0) ≠ ch 0`, so the determinacy
lemma is load-bearing and is NOT implied by the totality. -/
def digestLookup (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    Nat → Transcript.Digest → Nat → Block
  | 0, _ => ch 0
  | k + 1, e => if e.bytes = (h (k + 1)).bytes then ch (k + 1) else digestLookup h ch k e

/-- (2) **THE LOOKUP RETURNS THE RIGHT COLUMN** at every stage at or below `k`,
provided the `k + 1` digests are distinct. -/
theorem digest_lookup_at (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    ∀ (k : Nat), (∀ i j, i ≤ k → j ≤ k → h i = h j → i = j) →
      ∀ j, j ≤ k → digestLookup h ch k (h j) = ch j := by
  intro k
  induction k with
  | zero =>
      intro _ j hj
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      rfl
  | succ k2 ih =>
      intro hinj j hj
      by_cases hb : (h j).bytes = (h (k2 + 1)).bytes
      · have hjk : j = k2 + 1 :=
          hinj j (k2 + 1) hj (le_refl _) (digest_of_bytes_eq _ _ hb)
        show (if (h j).bytes = (h (k2 + 1)).bytes then ch (k2 + 1)
          else digestLookup h ch k2 (h j)) = ch j
        rw [if_pos hb, hjk]
      · have hjne : j ≠ k2 + 1 := by
          intro hEq
          exact hb (by rw [hEq])
        show (if (h j).bytes = (h (k2 + 1)).bytes then ch (k2 + 1)
          else digestLookup h ch k2 (h j)) = ch j
        rw [if_neg hb]
        exact ih (fun i j2 hi hj2 hEq => hinj i j2 (by omega) (by omega) hEq) j (by omega)

/-- (2) **AND IT RETURNS THE RIGHT COLUMN WITHOUT ANY DISTINCTNESS AT ALL**, as
long as the stage-indexed view is itself a function of the digest -- which is what
`grinder_table_view_determined` says of the run's own raw view.  This is what lets
the pairing of section 4 be stated at EVERY table rather than only on the chain's
no-clash event. -/
theorem digest_lookup_at_of_determined (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block) :
    ∀ (k : Nat), (∀ i j, i ≤ k → j ≤ k → h i = h j → ch i = ch j) →
      ∀ j, j ≤ k → digestLookup h ch k (h j) = ch j := by
  intro k
  induction k with
  | zero =>
      intro _ j hj
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      rfl
  | succ k2 ih =>
      intro hdet j hj
      show (if (h j).bytes = (h (k2 + 1)).bytes then ch (k2 + 1)
        else digestLookup h ch k2 (h j)) = ch j
      by_cases hbb : (h j).bytes = (h (k2 + 1)).bytes
      · rw [if_pos hbb]
        exact hdet (k2 + 1) j (le_refl _) hj (digest_of_bytes_eq _ _ hbb).symm
      · have hjne : j ≠ k2 + 1 := fun hEq => hbb (by rw [hEq])
        rw [if_neg hbb]
        exact ih (fun i j2 hi hj2 hEq => hdet i j2 (by omega) (by omega) hEq) j (by omega)

/-- (2) **THE DETERMINACY HYPOTHESIS IS LOAD-BEARING, AND IS NOT IMPLIED BY THE
TOTALITY OF THE LOOKUP.**  With two stages sharing a digest and carrying DIFFERENT
columns, `digestLookup` returns the WRONG column.  So the correctness of the
reconstruction of section 2 rests on `grinder_table_view_determined` (section 4)
and on nothing else; the definition being total gives it for free only the type
match, not the agreement. -/
theorem digest_lookup_wrong_without_determinacy :
    ∃ (h : Nat → Transcript.Digest) (ch : Nat → Nat → Block),
      digestLookup h ch 1 (h 0) ≠ ch 0 := by
  refine ⟨fun _ => OuterInitial.zeroDigest,
    fun i => if i = 0 then (fun _ => unitTarget) else (fun _ => oneDigestBlock), ?_⟩
  intro hEq
  have h1 : digestLookup (fun _ => OuterInitial.zeroDigest)
      (fun i => if i = 0 then (fun _ => unitTarget) else (fun _ => oneDigestBlock)) 1
      OuterInitial.zeroDigest = (fun _ => oneDigestBlock) := by
    show (if (OuterInitial.zeroDigest).bytes = (OuterInitial.zeroDigest).bytes
        then (if (1 : Nat) = 0 then (fun _ => unitTarget) else (fun _ => oneDigestBlock))
        else _) = _
    rw [if_pos rfl, if_neg (by decide : ¬ (1 : Nat) = 0)]
  rw [h1] at hEq
  have hx := congrFun hEq 0
  rw [show ((fun i => if i = 0 then (fun _ : Nat => unitTarget)
      else (fun _ => oneDigestBlock)) : Nat → Nat → Block) 0 0 = unitTarget from rfl] at hx
  exact one_block_ne_unit_target (congrArg (fun b : Block => b.val) hx)

/-- (2) The lookup reads the stage-indexed view only at the stages up to `k`. -/
theorem digest_lookup_congr (h : Nat → Transcript.Digest) (ch1 ch2 : Nat → Nat → Block) :
    ∀ (k : Nat), (∀ j, j ≤ k → ch1 j = ch2 j) →
      digestLookup h ch1 k = digestLookup h ch2 k := by
  intro k
  induction k with
  | zero => intro hch; funext _; exact hch 0 (le_refl 0)
  | succ k2 ih =>
      intro hch
      funext e
      show (if e.bytes = (h (k2 + 1)).bytes then ch1 (k2 + 1) else digestLookup h ch1 k2 e)
        = (if e.bytes = (h (k2 + 1)).bytes then ch2 (k2 + 1) else digestLookup h ch2 k2 e)
      by_cases hb : e.bytes = (h (k2 + 1)).bytes
      · rw [if_pos hb, if_pos hb, hch (k2 + 1) (le_refl _)]
      · rw [if_neg hb, if_neg hb, ih (fun j hj => hch j (by omega))]

/-! ## 3. THE LANE WHOSE ROUND MESSAGE IS THE GRINDER'S OWN ABSORBED PAYLOAD -/

/-- **THE PAIRED ROUND MESSAGE.**  Round `r` of the coupled schedule is the
grinding chain's stage `22 + 5 r`; this is the payload that stage's ABSORB emits,
decoded into field elements -- built from the run's own answer list and the raw
challenge view alone, which is all a `GrindingUnionBound.GrindLane` is handed. -/
def grinderMessage (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  fun r a ch =>
    decodeElements
      (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a)
        (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
        (grinderProbes e0 q (22 + 5 * r) a)).2

theorem grinder_hist_congr (e0 : Transcript.Digest) (q k : Nat) (a1 a2 : Nat → Block)
    (ha : ∀ m, m < (k + 1) * (q + 1) → a1 m = a2 m) :
    grinderHist e0 q k a1 = grinderHist e0 q k a2 := by
  funext j
  show (if j ≤ k then stateOf e0 q a1 j else e0) = (if j ≤ k then stateOf e0 q a2 j else e0)
  by_cases hj : j ≤ k
  · rw [if_pos hj, if_pos hj]
    cases j with
    | zero => rfl
    | succ j2 =>
        show blockDigest (a1 (slotPos q j2 q)) = blockDigest (a2 (slotPos q j2 q))
        rw [ha (slotPos q j2 q) (slot_pos_lt_of_le q (k + 1) j2 (by omega))]
  · rw [if_neg hj, if_neg hj]

theorem grinder_probes_congr (e0 : Transcript.Digest) (q k : Nat) (a1 a2 : Nat → Block)
    (ha : ∀ m, m < (k + 1) * (q + 1) → a1 m = a2 m) :
    grinderProbes e0 q k a1 = grinderProbes e0 q k a2 := by
  funext k2 i
  show (if slotPos q k2 i < slotPos q k q then a1 (slotPos q k2 i)
      else OuterChallenge.digestBlock e0)
    = (if slotPos q k2 i < slotPos q k q then a2 (slotPos q k2 i)
      else OuterChallenge.digestBlock e0)
  by_cases hs : slotPos q k2 i < slotPos q k q
  · have hk : slotPos q k q < (k + 1) * (q + 1) := slot_pos_lt_of_le q (k + 1) k (by omega)
    rw [if_pos hs, if_pos hs, ha (slotPos q k2 i) (by omega)]
  · rw [if_neg hs, if_neg hs]

/-- (3) **THE PAIRED MESSAGE OBEYS THE PROTOCOL'S CAUSALITY.**  It reads the run's
answers only at positions of stages at or below `22 + 5 r` and the challenge view
only at those stages, which is the adopted `GrindingUnionBound.GrindCausal` clause
verbatim.  So round `r`'s message is fixed before round `r`'s challenges are
squeezed, and the diagonal step of the adopted module applies to it. -/
theorem grinder_message_causal (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) :
    GrindCausal q (grinderMessage e0 q g) := by
  intro r a1 a2 ch1 ch2 ha hch
  have hh : grinderHist e0 q (22 + 5 * r) a1 = grinderHist e0 q (22 + 5 * r) a2 :=
    grinder_hist_congr e0 q (22 + 5 * r) a1 a2 ha
  have hp : grinderProbes e0 q (22 + 5 * r) a1 = grinderProbes e0 q (22 + 5 * r) a2 :=
    grinder_probes_congr e0 q (22 + 5 * r) a1 a2 ha
  have hl : digestLookup (grinderHist e0 q (22 + 5 * r) a1) ch1 (22 + 5 * r)
      = digestLookup (grinderHist e0 q (22 + 5 * r) a1) ch2 (22 + 5 * r) :=
    digest_lookup_congr _ ch1 ch2 (22 + 5 * r) hch
  show decodeElements (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a1)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a1) ch1 (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a1)).2
    = decodeElements (g.absorb (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) a2)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a2) ch2 (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a2)).2
  rw [hl, hh, hp]

/-- (3) The paired message's length is the grinder's own payload budget, divided
by the twenty-four bytes of a field element.

THE PAYLOAD BOUND IS REQUIRED ONLY AT THE COUPLED STAGES `22 + 5 r`, because the
paired lane never reads the absorb anywhere else.  A hypothesis quantified over
EVERY stage index would be strictly stronger, and it would exclude legal
`GrindingBounded`, `ChallengeRestricted` provers: `mixedGrinder` (section 6)
absorbs a long payload at the non-coupled stage `0` and a short one at every
coupled stage. -/
theorem grinder_message_length_le (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (p : Nat)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (g.absorb (22 + 5 * r) h ch pa).2.length ≤ p)
    (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block) :
    (grinderMessage e0 q g r a ch).length ≤ (p + 23) / 24 :=
  decode_elements_length_le_of_payload _ p (hp r _ _ _)

/-- **THE LANE THAT CARRIES THE GRINDER'S OWN ROUND MESSAGES.**  `truth` is a free
causal column, exactly as the adopted `RawBlockLanes.rawLogLaneOfStrategy` leaves
it free; `claim` and `truthClaim` are the initial running claims. -/
def grinderLane (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (cl tcl : Element) : GrindLane where
  message := grinderMessage e0 q g
  truth := tr
  claim := cl
  truthClaim := tcl

theorem grinder_lane_causal (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (htr : GrindCausal q tr)
    (cl tcl : Element) : GrindLaneCausal q (grinderLane e0 q g tr cl tcl) :=
  ⟨grinder_message_causal e0 q g, htr⟩

/-- (3) **THE LANE'S DEGREE BOUND, PAID FOR ONLY AT THE COUPLED STAGES.**  The
paired lane reads `g.absorb` at the stage indices `22 + 5 r` and nowhere else, so
this is the weakest payload hypothesis that gives the adopted `GrindLaneBounded`.
A prover that absorbs a WHIR Merkle root or a final polynomial at a NON-COUPLED
stage still satisfies it. -/
theorem grinder_lane_bounded_at_coupled_stages (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (p bd : Nat)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (g.absorb (22 + 5 * r) h ch pa).2.length ≤ p)
    (hfit : (p + 23) / 24 ≤ bd)
    (htr : ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block), (tr r a ch).length ≤ bd) :
    GrindLaneBounded (grinderLane e0 q g tr cl tcl) bd :=
  fun r a ch =>
    ⟨le_trans (grinder_message_length_le e0 q g p hp r a ch) hfit, htr r a ch⟩

/-! ## 4. THE PAIRING: THE LANE'S ROUND MESSAGE IS THE GRINDER'S OWN ABSORB -/

/-- (4) **THE TRUNCATED HISTORY THE LANE REBUILDS IS THE HISTORY THE RUN HANDS
THE ABSORB.**  Below stage `k` the run's answer list reports the real stage
digests; at and beyond it the adopted `GrindingQueryBound.run_ans_eq` makes the
list constant, and that constant's digest is the base digest.  So the truncation
is not a modelling choice: it is what the run does. -/
theorem grinder_hist_is_run_history (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    grinderHist e0 q k (grindRunView L hL e0 q g hb T)
      = stateOf e0 q (runAns L hL e0 q g hb (slotPos q k q) T) := by
  funext j
  cases j with
  | zero =>
      show (if (0 : Nat) ≤ k then stateOf e0 q (grindRunView L hL e0 q g hb T) 0 else e0)
        = stateOf e0 q (runAns L hL e0 q g hb (slotPos q k q) T) 0
      rw [if_pos (Nat.zero_le k)]
      rfl
  | succ j2 =>
      have hrun := run_ans_eq L hL e0 q g hb (slotPos q k q) T (slotPos q j2 q)
      show (if j2 + 1 ≤ k then blockDigest (grindRunView L hL e0 q g hb T (slotPos q j2 q))
          else e0)
        = blockDigest (runAns L hL e0 q g hb (slotPos q k q) T (slotPos q j2 q))
      rw [hrun]
      by_cases hj : j2 < k
      · rw [if_pos (by omega : j2 + 1 ≤ k), if_pos (slot_pos_mono q hj)]
        rfl
      · have hge : ¬ (slotPos q j2 q < slotPos q k q) := by
          intro hlt
          have hkj : k ≤ j2 := by omega
          have hmul : k * (q + 1) ≤ j2 * (q + 1) := Nat.mul_le_mul_right _ hkj
          rw [slotPos, slotPos] at hlt
          omega
        rw [if_neg (by omega : ¬ (j2 + 1 ≤ k)), if_neg hge]
        exact (block_digest_digest_block e0).symm

/-- (4) **AND THE TRUNCATED PROBE ANSWERS ARE THE PROBE ANSWERS THE RUN HANDS
THE ABSORB.** -/
theorem grinder_probes_is_run_probes (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    grinderProbes e0 q k (grindRunView L hL e0 q g hb T)
      = probeAnsOf q (runAns L hL e0 q g hb (slotPos q k q) T) := by
  funext k2 i
  show (if slotPos q k2 i < slotPos q k q
      then grindRunView L hL e0 q g hb T (slotPos q k2 i)
      else OuterChallenge.digestBlock e0)
    = runAns L hL e0 q g hb (slotPos q k q) T (slotPos q k2 i)
  rw [run_ans_eq]
  rfl

/-- (4) The raw challenge view's stage-`j` column IS the whole challenge oracle
evaluated at the chain's stage-`j` digest. -/
theorem grind_table_view_is_challenges_of (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (j : Nat)
    (T : OracleTable (boundedQueries L)) :
    grindTableView L hL e0 q g hb T j
      = challengesOf L hL T (grindState L hL e0 q g hb j T) := rfl

theorem grinder_hist_is_state (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) (j : Nat) (hj : j ≤ k) :
    grinderHist e0 q k (grindRunView L hL e0 q g hb T) j
      = grindState L hL e0 q g hb j T := by
  rw [grinder_hist_is_run_history]
  exact state_of_run_ans_at L hL e0 q g hb k j hj T

/-- (4) **ON THE CHAIN'S NO-CLASH EVENT THE REBUILT HISTORY IS INJECTIVE** up to
stage `k`, which is what makes the digest lookup of section 2 well behaved. -/
theorem grinder_hist_injective_on_no_clash (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) (hT : T ∈ grindingNoClash L hL e0 q g hb k) :
    ∀ i j, i ≤ k → j ≤ k →
      grinderHist e0 q k (grindRunView L hL e0 q g hb T) i
        = grinderHist e0 q k (grindRunView L hL e0 q g hb T) j → i = j := by
  intro i j hi hj hEq
  rw [grinder_hist_is_state L hL e0 q g hb k T i hi,
    grinder_hist_is_state L hL e0 q g hb k T j hj] at hEq
  by_contra hne
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact (mem_grind_no_clash L hL e0 q g hb k T).mp hT i j hlt hj hEq
  · exact (mem_grind_no_clash L hL e0 q g hb k T).mp hT j i (by omega) hi hEq.symm

/-- (4) **THE RAW VIEW'S COLUMN IS A FUNCTION OF THE STAGE DIGEST**, because it IS
the challenge oracle evaluated at that digest.  So two stages carrying the same
digest carry the same column -- no distinctness is needed. -/
theorem grinder_table_view_determined (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) :
    ∀ i j, i ≤ k → j ≤ k →
      grinderHist e0 q k (grindRunView L hL e0 q g hb T) i
        = grinderHist e0 q k (grindRunView L hL e0 q g hb T) j →
      grindTableView L hL e0 q g hb T i = grindTableView L hL e0 q g hb T j := by
  intro i j hi hj hEq
  rw [grinder_hist_is_state L hL e0 q g hb k T i hi,
    grinder_hist_is_state L hL e0 q g hb k T j hj] at hEq
  rw [grind_table_view_is_challenges_of, grind_table_view_is_challenges_of, hEq]

/-- (4) **THE REBUILT ORACLE AGREES WITH THE RUN'S OWN AT EVERY DIGEST THE ABSORB
IS ALLOWED TO READ.**  This is where `ChallengeRestricted` is paid for: the absorb
may consult the challenge oracle only at the stage digests `0, …, k`, and at those
the lookup of section 2 returns exactly the run's own columns -- AT EVERY TABLE,
with no conditioning event, because the columns are determined by the digests. -/
theorem grinder_lookup_is_challenges (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat)
    (T : OracleTable (boundedQueries L)) (j : Nat) (hj : j ≤ k) :
    digestLookup (grinderHist e0 q k (grindRunView L hL e0 q g hb T))
        (grindTableView L hL e0 q g hb T) k
        (grinderHist e0 q k (grindRunView L hL e0 q g hb T) j)
      = challengesOf L hL T (grinderHist e0 q k (grindRunView L hL e0 q g hb T) j) := by
  rw [digest_lookup_at_of_determined _ _ k (grinder_table_view_determined L hL e0 q g hb k T)
      j hj, grinder_hist_is_state L hL e0 q g hb k T j hj]
  rfl

/-- (4) **THE PAIRING.**  AT EVERY TABLE, with NO conditioning event, the paired
lane's round-`r` message IS the decoding of the payload the grinder's
stage-`22 + 5 r` ABSORB emits, at the very history and the very probe answers the
run hands it.  This is the statement the adopted `GrindingUnionBound` HONESTY (v)
records as missing.

WHAT IT COSTS: exactly one hypothesis, `ChallengeRestricted g`, which the adopted
module already assumes everywhere in its sections 5 to 8.  It costs NO membership
in the grinding chain's no-clash event: the run's raw challenge view at stage `j`
IS the challenge oracle evaluated at the stage-`j` digest
(`grind_table_view_is_challenges_of`), so colliding digests carry identical
columns and `digest_lookup_at_of_determined` applies whether or not the digests
are distinct.  `digest_lookup_at` and `grinder_hist_injective_on_no_clash` state
the injective route but are not on this theorem's critical path. -/
theorem grinder_lane_message_is_absorbed_payload (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (r : Nat) (T : OracleTable (boundedQueries L)) :
    (grinderLane e0 q g tr cl tcl).message r (grindRunView L hL e0 q g hb T)
        (grindTableView L hL e0 q g hb T)
      = decodeElements (g.absorb (22 + 5 * r)
          (stateOf e0 q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))
          (challengesOf L hL T)
          (probeAnsOf q (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T))).2 := by
  have habs := hcr.2 (22 + 5 * r) (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
    (digestLookup (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
      (grindTableView L hL e0 q g hb T) (22 + 5 * r))
    (challengesOf L hL T)
    (grinderProbes e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
    (fun j hj => grinder_lookup_is_challenges L hL e0 q g hb (22 + 5 * r) T j hj)
  show decodeElements (g.absorb (22 + 5 * r)
      (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
      (digestLookup (grinderHist e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))
        (grindTableView L hL e0 q g hb T) (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) (grindRunView L hL e0 q g hb T))).2 = _
  rw [habs, grinder_hist_is_run_history, grinder_probes_is_run_probes]

/-- (4) **THE SAME, AGAINST THE RUN'S OWN QUERY AT THAT POSITION.**  The stage's
absorb is the query at position `slotPos q (22 + 5 r) q` of the interleaved
sequence, so the lane's round-`r` message is the decoding of that query's own
payload. -/
theorem grinder_lane_message_is_run_query_payload (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (r : Nat) (T : OracleTable (boundedQueries L)) :
    (grinderLane e0 q g tr cl tcl).message r (grindRunView L hL e0 q g hb T)
        (grindTableView L hL e0 q g hb T)
      = decodeElements (grindQuery e0 q g
          (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T) (challengesOf L hL T)
          (slotPos q (22 + 5 * r) q)).2.2 := by
  rw [grinder_lane_message_is_absorbed_payload L hL e0 q g hb hcr tr cl tcl r T,
    grind_query_absorb]

/-- (4) **AND THAT PAYLOAD IS THE ONE INSIDE THE BYTE STRING THE RUN ACTUALLY
ASKED.**  The stage's query is a frame at the chain's own stage digest, carrying
the absorb's tag and the absorb's payload, and the lane's round-`r` message is
that payload decoded. -/
theorem grinder_run_frame_carries_the_lane_message (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (r : Nat) (T : OracleTable (boundedQueries L)) :
    ∃ (t : Transcript.Byte) (p : Transcript.Bytes),
      (grindSelSeq L hL e0 q g hb (slotPos q (22 + 5 * r) q) T).val
          = Transcript.frame (grindState L hL e0 q g hb (22 + 5 * r) T) t p ∧
        (grinderLane e0 q g tr cl tcl).message r (grindRunView L hL e0 q g hb T)
            (grindTableView L hL e0 q g hb T) = decodeElements p := by
  refine ⟨(grindQuery e0 q g (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T)
      (challengesOf L hL T) (slotPos q (22 + 5 * r) q)).2.1,
    (grindQuery e0 q g (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T)
      (challengesOf L hL T) (slotPos q (22 + 5 * r) q)).2.2, ?_,
    grinder_lane_message_is_run_query_payload L hL e0 q g hb hcr tr cl tcl r T⟩
  show Transcript.frame (grindQuery e0 q g
      (runAns L hL e0 q g hb (slotPos q (22 + 5 * r) q) T) (challengesOf L hL T)
      (slotPos q (22 + 5 * r) q)).1 _ _ = _
  rw [grind_query_absorb_digest L hL e0 q g hb (22 + 5 * r) T]

/-! ## 5. THE UNION BOUND, RESTATED AT THE GRINDER'S OWN LANES

### 5a. THE BYTE BUDGET, AS A THEOREM

The two `hfit` hypotheses of the headline below are not qualitative: each is
EXACTLY a byte bound on the prover's absorb payload, and at the adopted `quo = 8`
the two together are exactly "at most 120 bytes", i.e. five encoded field
elements per absorb. -/

/-- (5a) **THE LOG-LANE BUDGET IS EXACTLY 120 BYTES.** -/
theorem fitlog_iff (p : Nat) : ((p + 23) / 24 ≤ 5) ↔ p ≤ 120 := by omega

/-- (5a) **AND THE GATE-LANE BUDGET IS EXACTLY `24 * (quo + 2)` BYTES.** -/
theorem fitgate_iff (p quo : Nat) : ((p + 23) / 24 ≤ quo + 2) ↔ p ≤ 24 * (quo + 2) := by omega

/-- (5a) **SO THE CONJUNCTION IS EXACTLY `p ≤ 120` AT EVERY `quo ≥ 3`**, and in
particular at the adopted `quo = 8`: the covered class is the grinders whose
absorb payload is at most `min 120 (24 * (quo + 2))` bytes, which is 120 bytes,
which is FIVE encoded field elements. -/
theorem budget_is_five_elements (quo : Nat) (hq : 3 ≤ quo) (p : Nat) :
    ((p + 23) / 24 ≤ 5 ∧ (p + 23) / 24 ≤ quo + 2) ↔ p ≤ 120 := by
  constructor
  · intro h; omega
  · intro h; omega

/-- (5a) **AND AT THE ADOPTED QUOTIENT THE HYPOTHESIS `3 ≤ quo` IS DISCHARGED.**
The closed instance of section 6 runs at `quo = 8`, so the budget that section
actually pays is exactly `p ≤ 120`. -/
theorem budget_at_adopted_quotient (p : Nat) :
    ((p + 23) / 24 ≤ 5 ∧ (p + 23) / 24 ≤ 8 + 2) ↔ p ≤ 120 :=
  budget_is_five_elements 8 (by norm_num) p

/-- (5a) **FIVE ENCODED ELEMENTS ARE INSIDE THE BUDGET**: the boundary is not one
element and not two. -/
theorem five_elements_fit : ((unitRepeat 5).length + 23) / 24 ≤ 5 := by
  rw [unit_repeat_length]

/-- (5a) **AND SIX ARE OUTSIDE IT**, by exactly one element.  This is the
boundary `longMessageGrinder` of section 8 sits on. -/
theorem six_elements_do_not_fit : ¬ (((unitRepeat 6).length + 23) / 24 ≤ 5) := by
  rw [unit_repeat_length]
  decide

/-- (5a) And a five-element payload really does produce a five-element lane
message, so the covered class genuinely reaches the adopted degree budget rather
than stopping short of it. -/
theorem five_element_message_length : (decodeElements (unitRepeat 5)).length = 5 :=
  decode_unit_repeat_length 5

/-! ### 5b. THE RESTRICTION THAT BOTH OUTER LANES CARRY THE SAME MESSAGE -/

/-- (5b) **THE TWO PAIRED LANES CARRY THE SAME ROUND MESSAGE**, definitionally,
whatever honest columns and initial claims they are given.  A `GrindingStrategy`
emits ONE payload at stage `22 + 5 r`, and `grinderMessage` is the only message
`grinderLane` ever installs.

THIS IS THE LARGEST RESTRICTION ON THE HEADLINE BELOW.  In the deployed protocol
the coupled log-lane message and the coupled gate-lane message are two DISTINCT
prover messages at the same round; in the headline they are definitionally the
same list.  So section 5 covers only those grinders whose two coupled messages
coincide at every round.  Nothing here widens `GrindingStrategy` to emit two
payloads per coupled stage, and no adopted lemma bounds the bad-draw mass of the
paired lanes of a prover whose two coupled messages differ. -/
theorem both_paired_lanes_carry_the_same_message (e0 : Transcript.Digest) (q : Nat)
    (g : GrindingStrategy)
    (tr1 tr2 : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (cl1 tcl1 cl2 tcl2 : Element) :
    (grinderLane e0 q g tr1 cl1 tcl1).message = (grinderLane e0 q g tr2 cl2 tcl2).message := rfl

/-! ### 5c. THE HEADLINE -/

open Classical in
/-- (5) **THE ADOPTED HEADLINE, WITH THE FREE LANES REPLACED BY THE GRINDER'S OWN.**
The adopted `GrindingUnionBound.grinding_union_bad_draw_probability_le_combined`
is quantified over a FREE pair of grind lanes; here the two lanes are the PAIRED
ones, whose round-`r` messages are the payloads `g`'s own stage-`22 + 5 r` absorb
emits (`grinder_lane_message_is_absorbed_payload`).  The constant is unchanged --
the adopted `ChallengeUnionBound.combinedBound` plus the adopted grinding chain's
clash term -- and nothing is added or dropped.

WHAT THIS IS NOT.  It is NOT a demonstration that grinding buys the prover
anything, and no SEARCHING prover is exhibited anywhere in this module.  The
witness `selectorGrinder` reads probe `0` and branches to one of two CONSTANT
messages; it never re-probes and it never searches.  The adopted
`GrindingUnionBound` says exactly the same of its own `probeGrinder`.  The prover
that WOULD search is that module's `preReadGrinder`, and what excludes it from
the headline below is the hypothesis `ChallengeRestricted g` -- NOT the byte
budget, which `preReadGrinder` would satisfy.  So the exclusion that does the work
here is the adopted one, and it is still undischarged: GUB's
`echo_grinder_pre_read_mass_one` shows the pre-read event cannot be conditioned
away, and no adopted lemma charges a constant for it.

WHAT IS STILL FREE, AND WHY: the `truth` column of each lane, and the two initial
claims.  Those are not the prover's data at all -- the adopted `RawBlockLanes`
section 7 leaves them free in exactly the same way -- so pairing them with `g`
is not attempted here and no adopted lemma does it.

WHAT THE DEGREE HYPOTHESIS NOW MEANS -- THE BYTE BUDGET.  This bound covers
exactly those `ChallengeRestricted` grinders whose absorb payload is at most
`min 120 (24 * (quo + 2))` bytes at EVERY coupled stage -- at the adopted
`quo = 8`, at most 120 bytes, i.e. five encoded field elements per absorb, with
`unitRepeat 5` inside and `unitRepeat 6` exactly one element out.  A grinder that
absorbs six (`longMessageGrinder`) is outside it, and no adopted lemma bounds the
bad-draw mass of its paired lanes.  The budget is a theorem, not a reading:
`fitlog_iff`, `fitgate_iff`, `budget_is_five_elements`, `five_elements_fit`,
`six_elements_do_not_fit`.

AND THE LARGER RESTRICTION: BOTH LANES BELOW CARRY THE SAME ROUND MESSAGE.
`both_paired_lanes_carry_the_same_message` is a `rfl`; the log lane and the gate
lane of this statement differ only in their honest columns and initial claims.
In the protocol they are two distinct coupled prover messages.  A prover whose two
coupled messages differ is outside this headline whatever its payload lengths are.

`hp` IS REQUIRED ONLY AT THE COUPLED STAGES `22 + 5 r`, because the paired lane
never reads the absorb anywhere else.  This is strictly weaker than a bound at
every stage index and it matters: `mixedGrinder` of section 6 absorbs 144 bytes
at the non-coupled stage `0` and 24 at every coupled stage, so a uniform `hp`
would force `p ≥ 144` (`mixed_grinder_uniform_payload_needs_144`), which fails
`hfitlog`, while the coupled-only `hp` holds at `p = 24`
(`mixed_grinder_coupled_payload`).  A real prover absorbing a WHIR Merkle root or
a final polynomial at a non-coupled stage is covered here and would not have
been. -/
theorem grinder_paired_union_bad_draw_probability_le_combined (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (q : Nat) (g : GrindingStrategy) (hb : GrindingBounded L g)
    (hcr : ChallengeRestricted g)
    (trlog trgate : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element)
    (htrlog : GrindCausal q trlog) (htrgate : GrindCausal q trgate)
    (cl1 tcl1 cl2 tcl2 : Element) (d quo constraints p : Nat)
    (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit)
    (hp : ∀ (r : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (g.absorb (22 + 5 * r) h ch pa).2.length ≤ p)
    (hfitlog : (p + 23) / 24 ≤ 5) (hfitgate : (p + 23) / 24 ≤ quo + 2)
    (htrlogb : ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block),
      (trlog r a ch).length ≤ 5)
    (htrgateb : ∀ (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block),
      (trgate r a ch).length ≤ quo + 2)
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L hL e0 q g hb (grinderLane e0 q g trlog cl1 tcl1)
          (grinderLane e0 q g trgate cl2 tcl2) d (2 ^ d) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d quo d constraints
        + (((22 + 5 * d) * (q + 1) : Nat) : ℚ) * ((((22 + 5 * d) * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  grinding_union_bad_draw_probability_le_combined L hL e0 q g hb hcr
    (grinderLane e0 q g trlog cl1 tcl1) (grinderLane e0 q g trgate cl2 tcl2)
    (grinder_lane_causal e0 q g trlog htrlog cl1 tcl1)
    (grinder_lane_causal e0 q g trgate htrgate cl2 tcl2)
    d quo constraints gv coeffsOf hdu
    (grinder_lane_bounded_at_coupled_stages e0 q g trlog cl1 tcl1 p 5 hp hfitlog htrlogb)
    (grinder_lane_bounded_at_coupled_stages e0 q g trgate cl2 tcl2 p (quo + 2) hp hfitgate
      htrgateb)
    hclen

/-! ## 6. A GRINDER THAT SELECTS ON ITS PROBES, AND THE NON-DEGENERACY WITNESSES -/

/-- THE HONEST COLUMN OF A LANE THAT HAS NOTHING TO SAY, at the widened domain:
the adopted `RawBlockLanes.rawZeroTruth` with the run argument added. -/
def grindZeroTruth : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element :=
  fun _ _ _ => []

theorem grind_zero_truth_causal (q : Nat) : GrindCausal q grindZeroTruth :=
  fun _ _ _ _ _ _ _ => rfl

theorem grind_zero_truth_length (bd r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block) :
    (grindZeroTruth r a ch).length ≤ bd := Nat.zero_le _

/-- **A GRINDER THAT SELECTS ITS ROUND MESSAGE ON WHAT IT PROBED.**  It probes at
its own current digest exactly as the adopted `GrindingQueryBound.probeGrinder`
does, and its absorb emits the twenty-four bytes of the field element `1` WHEN AND
ONLY WHEN its first probe came back the constant table's block, and the bytes of
`0` otherwise.  So its round message is a genuine function of its own oracle
answers -- `selector_grinder_reads_probes` -- and its payload is always exactly
twenty-four bytes, which is what makes the degree hypothesis of section 5
dischargeable at it.

It never consults the challenge oracle, so it is `ChallengeRestricted`; it is
therefore INSIDE the class of section 5 and, by
`selector_grinder_is_not_transcript_restricted`, OUTSIDE the adopted
`StrategyChainBound.Strategy` class the adopted `RawBlockLanes` covers.

IT DOES NOT SEARCH.  It reads probe `0` once and branches to one of two CONSTANT
messages; it never re-probes and it never retries.  It is an instance of the
arithmetic of section 5, in the same sense in which the adopted
`GrindingQueryBound.probeGrinder` is an instance of the adopted arithmetic, and
it is NOT a demonstration that grinding buys a prover anything.  No searching
prover is exhibited in this module. -/
def selectorGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun k _ _ pa =>
    (0, if (pa k 0).val = unitTarget.val then bytesOfElement 1 else bytesOfElement 0)

theorem selector_grinder_payload_length (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (selectorGrinder.absorb k h ch pa).2.length ≤ 24 := by
  show (if (pa k 0).val = unitTarget.val then bytesOfElement 1
      else bytesOfElement 0).length ≤ 24
  by_cases hc : (pa k 0).val = unitTarget.val
  · rw [if_pos hc, bytes_of_element_length]
  · rw [if_neg hc, bytes_of_element_length]

theorem selector_grinder_bounded (L : Nat) (hL : 93 ≤ L) : GrindingBounded L selectorGrinder := by
  refine ⟨fun _ i _ _ _ => ?_, fun k h ch pa => ?_⟩
  · show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · exact le_trans (Nat.add_le_add_left (selector_grinder_payload_length k h ch pa) 61) (by omega)

theorem selector_grinder_challenge_restricted : ChallengeRestricted selectorGrinder :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- (6) **THE SELECTOR GRINDER READS ITS PROBE ANSWERS.**  Two probe histories
that differ at probe `0` of the stage give it different absorbs, at the same stage
digests and the same challenge answers. -/
theorem selector_grinder_reads_probes :
    ∃ (k : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
        (pa1 pa2 : Nat → Nat → Block),
      selectorGrinder.absorb k h ch pa1 ≠ selectorGrinder.absorb k h ch pa2 := by
  refine ⟨0, fun _ => OuterInitial.zeroDigest, fun _ _ => unitTarget,
    fun _ _ => unitTarget, fun _ _ => oneDigestBlock, ?_⟩
  intro hEq
  have hp : (if (unitTarget.val : Transcript.Bytes) = unitTarget.val then bytesOfElement 1
        else bytesOfElement 0)
      = (if (oneDigestBlock.val : Transcript.Bytes) = unitTarget.val then bytesOfElement 1
        else bytesOfElement 0) := congrArg Prod.snd hEq
  rw [if_pos rfl, if_neg one_block_ne_unit_target] at hp
  have hx : elementOfBytes (bytesOfElement 1) = elementOfBytes (bytesOfElement 0) :=
    congrArg elementOfBytes hp
  rw [element_of_bytes_of_element, element_of_bytes_of_element] at hx
  exact zero_ne_one hx.symm

/-- (6) **AND IS THEREFORE NOT THE LIFT OF ANY TRANSCRIPT-RESTRICTED PROVER**, by
the adopted `GrindingQueryBound.grinding_of_strategy_ignores_probes`.  So the
witness of this section is not a prover the adopted `RawBlockLanes` already
covers. -/
theorem selector_grinder_is_not_transcript_restricted (strat : StrategyChainBound.Strategy) :
    selectorGrinder ≠ grindingOfStrategy strat := by
  intro h
  obtain ⟨k, hh, ch, pa1, pa2, hne⟩ := selector_grinder_reads_probes
  refine hne ?_
  rw [h]
  exact grinding_of_strategy_ignores_probes strat k hh ch pa1 pa2

theorem selector_grinder_fits_log : (24 + 23) / 24 ≤ 5 := by norm_num

theorem selector_grinder_fits_gate (quo : Nat) : (24 + 23) / 24 ≤ quo + 2 := by omega

/-- (6) At the adopted `BirthdayClashBound.constantTable` and the base digest
`OuterInitial.zeroDigest`, every cell the reconstruction of section 2 reads is the
constant table's own block. -/
theorem grinder_probes_at_constant_table (L : Nat) (hL : 64 ≤ L) (q : Nat)
    (g : GrindingStrategy) (hb : GrindingBounded L g) (k : Nat) :
    grinderProbes OuterInitial.zeroDigest q k
        (grindRunView L hL OuterInitial.zeroDigest q g hb (constantTable L))
      = fun _ _ => unitTarget := by
  funext k2 i
  show (if slotPos q k2 i < slotPos q k q
      then grindRunView L hL OuterInitial.zeroDigest q g hb (constantTable L) (slotPos q k2 i)
      else OuterChallenge.digestBlock OuterInitial.zeroDigest) = unitTarget
  by_cases hs : slotPos q k2 i < slotPos q k q
  · rw [if_pos hs]
    rfl
  · rw [if_neg hs]
    rfl

/-- (6) **THE PAIRED LANE'S ROUND-`0` MESSAGE AT THE SELECTOR GRINDER AND THE
CONSTANT TABLE IS THE ADOPTED `separatedRawLane`'s.**  The grinder takes its
favourable branch, emits the twenty-four bytes of `1`, and the decoder of
section 1 turns them back into `[1]`. -/
theorem selector_grinder_paired_message_zero (L : Nat) (hL : 64 ≤ L) (hL2 : 93 ≤ L) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element) :
    (grinderLane OuterInitial.zeroDigest q selectorGrinder tr cl tcl).message 0
        (grindRunView L hL OuterInitial.zeroDigest q selectorGrinder
          (selector_grinder_bounded L hL2) (constantTable L))
        (grindTableView L hL OuterInitial.zeroDigest q selectorGrinder
          (selector_grinder_bounded L hL2) (constantTable L))
      = [1] := by
  have hpa := grinder_probes_at_constant_table L hL q selectorGrinder
    (selector_grinder_bounded L hL2) (22 + 5 * 0)
  show decodeElements (selectorGrinder.absorb (22 + 5 * 0) _ _
      (grinderProbes OuterInitial.zeroDigest q (22 + 5 * 0)
        (grindRunView L hL OuterInitial.zeroDigest q selectorGrinder
          (selector_grinder_bounded L hL2) (constantTable L)))).2 = [1]
  rw [hpa]
  show decodeElements (if (unitTarget.val : Transcript.Bytes) = unitTarget.val
      then bytesOfElement 1 else bytesOfElement 0) = [1]
  rw [if_pos rfl, decode_elements_of_element]

/-- (6) **SO THE PAIRED LANE'S ROUND-`0` TARGET IS INHABITED.**  At the adopted
`constantTable` the paired lane's own round-`0` bad set contains the adopted
`OuterLaneTransport.zeroDigestTriple`, at EVERY probe budget and EVERY counter
base -- so the round-`0` bad set is not empty.

WHAT THIS DOES NOT SAY.  The target is a `Finset` of DIGEST TRIPLES and the
bounded event is a `Finset` of TABLES; a non-empty target does not by itself give
a non-empty event, and nothing here or in the adopted `GrindingUnionBound` bridges
the two.  The adopted `RawBlockLanes` witnesses its own line the same way
(`grind_raw_target_zero_nonempty_of_agreement`), so this is adopted practice
rather than a gap opened here; the full bad event's inhabitation is not proved
here, as it is not proved in GUB. -/
theorem selector_grinder_paired_target_zero_nonempty (L : Nat) (hL : 64 ≤ L) (hL2 : 93 ≤ L)
    (q : Nat) (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (base : Nat)
    (htr : tr 0 (grindRunView L hL OuterInitial.zeroDigest q selectorGrinder
        (selector_grinder_bounded L hL2) (constantTable L))
      (grindTableView L hL OuterInitial.zeroDigest q selectorGrinder
        (selector_grinder_bounded L hL2) (constantTable L)) = []) :
    (grindRawTarget L hL OuterInitial.zeroDigest q selectorGrinder
      (selector_grinder_bounded L hL2)
      (grinderLane OuterInitial.zeroDigest q selectorGrinder tr 1 0) base 0
      (constantTable L)).Nonempty := by
  refine grind_raw_target_zero_nonempty_of_agreement L hL OuterInitial.zeroDigest q
    selectorGrinder (selector_grinder_bounded L hL2)
    (grinderLane OuterInitial.zeroDigest q selectorGrinder tr 1 0) base (constantTable L)
    zeroDigestTriple (fun h => zero_ne_one h.symm) ?_
  have hmsg := selector_grinder_paired_message_zero L hL hL2 q tr 1 0
  show (OuterRound.polynomial (1 : Element)
        ((grinderLane OuterInitial.zeroDigest q selectorGrinder tr 1 0).message 0 _ _)).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
    = (OuterRound.polynomial (0 : Element)
        ((grinderLane OuterInitial.zeroDigest q selectorGrinder tr 1 0).truth 0 _ _)).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
  rw [hmsg]
  show (OuterRound.polynomial (1 : Element) [1]).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
    = (OuterRound.polynomial (0 : Element) (tr 0 _ _)).eval
      (OuterChallenge.reduceTriple zeroDigestTriple)
  rw [htr]
  exact separated_raw_lane_agrees_at_zero
    (grindTableView L hL OuterInitial.zeroDigest q selectorGrinder
      (selector_grinder_bounded L hL2) (constantTable L))

open Classical in
/-- (6) **THE CLOSED INSTANCE, AT A PROVER THAT SELECTS ON ITS PROBES AND AT ITS
OWN LANES.**  Thirteen coupled rounds, `q` frame probes per stage, both outer
lanes carrying `selectorGrinder`'s OWN absorbed payloads, and the adopted
`ChallengeUnionBound.combinedBound 13 8 13 123` plus the adopted grinding chain's
clash mass at `N = 87 (q + 1)`.  Every hypothesis of section 5 is discharged here;
none is assumed. -/
theorem selector_grinder_paired_bound_at_thirteen (L : Nat) (hL : 93 ≤ L) (q : Nat)
    (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hclen : ∀ i, i < 2 ^ 13 → (coeffsOf i).length ≤ 123) :
    oracleProbability (boundedQueries L)
        (grindingFullBadEvent L (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q
          selectorGrinder (selector_grinder_bounded L hL)
          (grinderLane OuterInitial.zeroDigest q selectorGrinder grindZeroTruth 1 0)
          (grinderLane OuterInitial.zeroDigest q selectorGrinder grindZeroTruth 1 0)
          13 (2 ^ 13) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + ((87 * (q + 1) : Nat) : ℚ) * (((87 * (q + 1) : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := grinder_paired_union_bad_draw_probability_le_combined L
    (Nat.le_trans (by norm_num) hL) OuterInitial.zeroDigest q selectorGrinder
    (selector_grinder_bounded L hL) selector_grinder_challenge_restricted
    grindZeroTruth grindZeroTruth (grind_zero_truth_causal q) (grind_zero_truth_causal q)
    1 0 1 0 13 8 123 24 gv coeffsOf thirteen_counter_budget
    (fun r => selector_grinder_payload_length (22 + 5 * r))
    selector_grinder_fits_log (selector_grinder_fits_gate 8)
    (grind_zero_truth_length 5) (grind_zero_truth_length 10) hclen
  have harith : ((22 + 5 * 13) * (q + 1) : Nat) = 87 * (q + 1) := by omega
  rw [harith] at h
  exact h

/-- **A LEGAL GRINDER THAT ABSORBS A LONG PAYLOAD AT A NON-COUPLED STAGE.**  Six
encoded field elements at stage `0`, one at every other stage.  Stage `0` is not
of the form `22 + 5 r`, so the paired lane never reads that long payload; this is
the witness that the coupled-only payload hypothesis of section 5 is a genuine
weakening and not a cosmetic one.  A real prover absorbing a WHIR Merkle root or
a final polynomial outside the coupled schedule has this shape. -/
def mixedGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun k _ _ _ => (0, if k = 0 then unitRepeat 6 else bytesOfElement 1)

theorem mixed_grinder_payload_length (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (mixedGrinder.absorb k h ch pa).2.length ≤ 144 := by
  show (if k = 0 then unitRepeat 6 else bytesOfElement 1).length ≤ 144
  by_cases hk : k = 0
  · rw [if_pos hk, unit_repeat_length]
  · rw [if_neg hk, bytes_of_element_length]
    omega

theorem mixed_grinder_bounded (L : Nat) (hL : 205 ≤ L) : GrindingBounded L mixedGrinder := by
  refine ⟨fun _ i _ _ _ => ?_, fun k h ch pa => ?_⟩
  · show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · exact le_trans (Nat.add_le_add_left (mixed_grinder_payload_length k h ch pa) 61) (by omega)

theorem mixed_grinder_challenge_restricted : ChallengeRestricted mixedGrinder :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- (6) **AT EVERY COUPLED STAGE ITS PAYLOAD IS TWENTY-FOUR BYTES**, so the
coupled-only hypothesis of section 5 holds at it with `p = 24`, which satisfies
both `hfitlog` and `hfitgate`. -/
theorem mixed_grinder_coupled_payload (r : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (mixedGrinder.absorb (22 + 5 * r) h ch pa).2.length ≤ 24 := by
  show (if 22 + 5 * r = 0 then unitRepeat 6 else bytesOfElement 1).length ≤ 24
  rw [if_neg (by omega), bytes_of_element_length]

/-- (6) **BUT A PAYLOAD HYPOTHESIS QUANTIFIED OVER EVERY STAGE INDEX WOULD FORCE
`p ≥ 144` AT IT**, which fails `fitlog_iff`'s `p ≤ 120`.  So `mixedGrinder` is a
legal `GrindingBounded`, `ChallengeRestricted` prover that a uniform payload
hypothesis EXCLUDES and the coupled-only hypothesis of section 5 COVERS. -/
theorem mixed_grinder_uniform_payload_needs_144 (p : Nat)
    (hp : ∀ (k : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (mixedGrinder.absorb k h ch pa).2.length ≤ p) : 144 ≤ p := by
  have h := hp 0 (fun _ => OuterInitial.zeroDigest) (fun _ _ => unitTarget)
    (fun _ _ => unitTarget)
  have he : (mixedGrinder.absorb 0 (fun _ => OuterInitial.zeroDigest) (fun _ _ => unitTarget)
      (fun _ _ => unitTarget)).2 = unitRepeat 6 := by
    show (if (0 : Nat) = 0 then unitRepeat 6 else bytesOfElement 1) = unitRepeat 6
    rw [if_pos rfl]
  rw [he, unit_repeat_length] at h
  omega

/-- (6) **AND THAT HYPOTHESIS IS SATISFIABLE, AT `p = 144` AND NOWHERE LOWER**, so
the previous theorem is not vacuous; `144` is outside the log-lane budget of
section 5a, which `fitlog_iff` pins at `p ≤ 120`. -/
theorem mixed_grinder_uniform_payload_bound_is_tight :
    (∀ (k : Nat) (h : Nat → Transcript.Digest) (ch : Transcript.Digest → Nat → Block)
      (pa : Nat → Nat → Block), (mixedGrinder.absorb k h ch pa).2.length ≤ 144)
    ∧ ¬ ((144 : Nat) ≤ 120) :=
  ⟨mixed_grinder_payload_length, by decide⟩

/-! ## 7. THE ZERO-PROBE IDENTITY -/

/-- (7) **DEFINITIONAL.**  A lifted raw lane's round message ignores the run's own
answers, so it IS the raw lane's, with no proof. -/
theorem zero_probe_lane_message_is_raw (lane : RawLane) (r : Nat) (a : Nat → Block)
    (ch : Nat → Nat → Block) : (grindLaneOfRawLane lane).message r a ch = lane.message r ch := rfl

/-- (7) **DEFINITIONAL.**  And so does its honest column. -/
theorem zero_probe_lane_truth_is_raw (lane : RawLane) (r : Nat) (a : Nat → Block)
    (ch : Nat → Nat → Block) : (grindLaneOfRawLane lane).truth r a ch = lane.truth r ch := rfl

/-- (7) **DEFINITIONAL.**  Stage `0` of the grinding chain is the base digest, as
it is for the adopted chain. -/
theorem zero_probe_state_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    grindState L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) 0 T
      = strategyFrameState L hL e0 strat hb 0 T := rfl

/-- (7) **DEFINITIONAL.**  The running claims before round `0` are the lane's own
initial claims on both sides. -/
theorem zero_probe_claims_zero (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (lane : RawLane) (base : Nat) (T : OracleTable (boundedQueries L)) :
    grindRawClaims L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane lane) base T 0
      = rawClaims L hL e0 strat hb lane base T 0 := rfl

/-- (7) **NOT DEFINITIONAL: THE STAGE DIGESTS.**  This is the adopted
`GrindingQueryBound.grinding_chain_of_strategy_chain`, an induction on the stage
index; the two recursions are over different data (an interleaved answer list
against a truncated history) and no reduction identifies them. -/
theorem zero_probe_state_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (k : Nat) (T : OracleTable (boundedQueries L)) :
    grindState L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) k T
      = strategyFrameState L hL e0 strat hb k T :=
  grinding_chain_of_strategy_chain L hL e0 strat hb T k

/-- (7) **NOT DEFINITIONAL: THE CHALLENGE QUERY.**  It is the stage digest's
challenge input on both sides, so it follows from the digest identity and from
nothing else. -/
theorem zero_probe_challenge_sel_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (j c : Nat) (T : OracleTable (boundedQueries L)) :
    chainChallengeSel L hL (grindState L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb)) j c T
      = challengeSel L hL e0 strat hb j c T := by
  apply Subtype.ext
  show Transcript.challengeInput (grindState L hL e0 0 (grindingOfStrategy strat)
      (grinding_of_strategy_bounded L hL strat hb) j T) c
    = Transcript.challengeInput (strategyFrameState L hL e0 strat hb j T) c
  rw [zero_probe_state_eq L hL e0 strat hb j T]

/-- (7) **NOT DEFINITIONAL: THE RAW CHALLENGE VIEW.** -/
theorem zero_probe_table_view_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (T : OracleTable (boundedQueries L)) :
    grindTableView L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) T
      = tableView L hL e0 strat hb T := by
  funext j cnt
  show T (chainChallengeSel L hL (grindState L hL e0 0 (grindingOfStrategy strat)
      (grinding_of_strategy_bounded L hL strat hb)) j cnt T)
    = T (challengeSel L hL e0 strat hb j cnt T)
  rw [zero_probe_challenge_sel_eq L hL e0 strat hb j cnt T]

/-- (7) **NOT DEFINITIONAL: THE DIGEST TRIPLE.** -/
theorem zero_probe_triple_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (j base : Nat) (T : OracleTable (boundedQueries L)) :
    chainTriple L hL (grindState L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb)) j base T
      = stageTriple L hL e0 strat hb j base T := by
  show ((T _, T _, T _) : OuterChallenge.DigestTriple) = (T _, T _, T _)
  rw [zero_probe_challenge_sel_eq L hL e0 strat hb j base T,
    zero_probe_challenge_sel_eq L hL e0 strat hb j (base + 1) T,
    zero_probe_challenge_sel_eq L hL e0 strat hb j (base + 2) T]

theorem zero_probe_chain_val_is_state (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (s : Nat) (T : OracleTable (boundedQueries L)) :
    chainVal (strategySel L hL e0 strat hb) s T
      = OuterChallenge.digestBlock (strategyFrameState L hL e0 strat hb (s + 1) T) := by
  rw [strategy_state_succ, digest_block_block_digest]

/-- (7) **NOT DEFINITIONAL, AND NOT A CONGRUENCE EITHER: THE NO-CLASH EVENT.**
The two conditioning events have DIFFERENT SHAPES.  The adopted
`OuterLaneTransport.stageNoClash` is the adopted `BirthdayClashBound.noClash` of
the chain's `n` ANSWER BLOCKS, with the base digest carried by a SEPARATE
`avoidBase` clause; the adopted `GrindingQueryBound.grindingNoClash` is pairwise
distinctness of the `n + 1` STAGE DIGESTS, base digest included.  They coincide
only after the index shift `chainVal s = digestBlock (state (s + 1))` and the
injectivity of `OuterChallenge.digestBlock`, which is what this proof does. -/
theorem zero_probe_no_clash_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (n : Nat) :
    grindingNoClash L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) n
      = stageNoClash L hL e0 strat hb n := by
  apply Finset.ext
  intro T
  have hg : ∀ k, grindState L hL e0 0 (grindingOfStrategy strat)
      (grinding_of_strategy_bounded L hL strat hb) k T
        = strategyFrameState L hL e0 strat hb k T :=
    fun k => zero_probe_state_eq L hL e0 strat hb k T
  have hleft : T ∈ grindingNoClash L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) n ↔
      ∀ r s : Nat, r < s → s ≤ n →
        strategyFrameState L hL e0 strat hb r T ≠ strategyFrameState L hL e0 strat hb s T := by
    rw [mem_grind_no_clash]
    constructor
    · intro h r s hrs hsn hEq
      exact h r s hrs hsn (by rw [hg r, hg s]; exact hEq)
    · intro h r s hrs hsn hEq
      exact h r s hrs hsn (by rw [← hg r, ← hg s]; exact hEq)
  rw [hleft, stageNoClash, mem_no_clash]
  constructor
  · intro h
    refine ⟨fun r s hrs hsn hEq => ?_, fun s hsn hmem => ?_⟩
    · refine h (r + 1) (s + 1) (by omega) (by omega) (digest_block_inj _ _ ?_)
      rw [← zero_probe_chain_val_is_state L hL e0 strat hb r T,
        ← zero_probe_chain_val_is_state L hL e0 strat hb s T]
      exact hEq
    · rw [avoidBase, Finset.mem_singleton,
        zero_probe_chain_val_is_state L hL e0 strat hb s T] at hmem
      refine h 0 (s + 1) (by omega) (by omega) ?_
      rw [strategy_state_zero]
      exact (digest_block_inj _ _ hmem).symm
  · rintro ⟨h1, h2⟩ r s hrs hsn hEq
    obtain ⟨s2, rfl⟩ : ∃ s2, s = s2 + 1 := ⟨s - 1, by omega⟩
    cases r with
    | zero =>
        refine h2 s2 (by omega) ?_
        rw [zero_probe_chain_val_is_state L hL e0 strat hb s2 T, avoidBase,
          Finset.mem_singleton]
        rw [strategy_state_zero] at hEq
        exact congrArg OuterChallenge.digestBlock hEq.symm
    | succ r2 =>
        refine h1 r2 s2 (by omega) (by omega) ?_
        rw [zero_probe_chain_val_is_state L hL e0 strat hb r2 T,
          zero_probe_chain_val_is_state L hL e0 strat hb s2 T]
        exact congrArg OuterChallenge.digestBlock hEq

/-- (7) **NOT DEFINITIONAL: THE RUNNING CLAIMS.**  The recursion step is the same
adopted `OuterRound.evaluate`, but its two arguments -- the lane's message and the
round's reduced challenge -- have to be transported by the two identities above. -/
theorem zero_probe_claims_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (lane : RawLane) (base : Nat) (T : OracleTable (boundedQueries L)) (r : Nat) :
    grindRawClaims L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane lane) base T r
      = rawClaims L hL e0 strat hb lane base T r := by
  induction r with
  | zero => rfl
  | succ r2 ih =>
      rw [grind_raw_claims_succ, raw_claims_succ, ih,
        zero_probe_table_view_eq L hL e0 strat hb T,
        zero_probe_triple_eq L hL e0 strat hb (roundStage r2) base T]
      rfl

/-- (7) **NOT DEFINITIONAL: ROUND `r`'s BAD SET AND ITS DIGEST-TRIPLE
PULLBACK.** -/
theorem zero_probe_bad_set_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (lane : RawLane) (base r : Nat) (T : OracleTable (boundedQueries L)) :
    grindRawBadSet L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane lane) base r T
      = rawBadSet L hL e0 strat hb lane base r T := by
  rw [grindRawBadSet, rawBadSet, zero_probe_claims_eq L hL e0 strat hb lane base T r,
    zero_probe_table_view_eq L hL e0 strat hb T]
  rfl

theorem zero_probe_target_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (lane : RawLane) (base r : Nat) (T : OracleTable (boundedQueries L)) :
    grindRawTarget L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane lane) base r T
      = rawTarget L hL e0 strat hb lane base r T := by
  rw [grindRawTarget, rawTarget, zero_probe_bad_set_eq L hL e0 strat hb lane base r T]

open Classical in
/-- (7) **NOT DEFINITIONAL: ROUND `r`'s BAD EVENT.** -/
theorem zero_probe_round_bad_event_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (lane : RawLane) (base r : Nat) :
    grindRawRoundBadEvent L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane lane) base r
      = rawRoundBadEvent L hL e0 strat hb lane base r := by
  apply Finset.ext
  intro T
  simp only [grindRawRoundBadEvent, rawRoundBadEvent, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [zero_probe_triple_eq L hL e0 strat hb (roundStage r) base T,
    zero_probe_target_eq L hL e0 strat hb lane base r T]

open Classical in
theorem zero_probe_both_bad_event_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (logLane gateLane : RawLane) (r : Nat) :
    grindRawBothBadEvent L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane logLane)
        (grindLaneOfRawLane gateLane) r
      = rawBothBadEvent L hL e0 strat hb logLane gateLane r := by
  rw [grindRawBothBadEvent, rawBothBadEvent,
    zero_probe_round_bad_event_eq L hL e0 strat hb logLane 0 r,
    zero_probe_round_bad_event_eq L hL e0 strat hb gateLane 3 r]

open Classical in
/-- (7) **NOT DEFINITIONAL: THE OUTER BAD EVENT.** -/
theorem zero_probe_outer_bad_event_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (logLane gateLane : RawLane) (d : Nat) :
    grindRawOuterBadEvent L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane logLane)
        (grindLaneOfRawLane gateLane) d
      = rawOuterBadEvent L hL e0 strat hb logLane gateLane d := by
  rw [grindRawOuterBadEvent, rawOuterBadEvent]
  refine Finset.biUnion_congr rfl (fun r _ => ?_)
  exact zero_probe_both_bad_event_eq L hL e0 strat hb logLane gateLane r

/-- (7) **NOT DEFINITIONAL: THE GATE TAU COLUMN.** -/
theorem zero_probe_tau_read_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (d : Nat) (T : OracleTable (boundedQueries L)) :
    grindTauRead L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) d T
      = tauRead L hL e0 strat hb d T := by
  funext i
  exact zero_probe_triple_eq L hL e0 strat hb deriveStage (tauBase d i.val) T

open Classical in
theorem zero_probe_gate_tau_bad_event_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (d : Nat) (gv : Nat → Element) :
    grindGateTauBadEvent L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) d gv
      = gateTauBadEvent L hL e0 strat hb d gv := by
  apply Finset.ext
  intro T
  simp only [grindGateTauBadEvent, gateTauBadEvent, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [zero_probe_tau_read_eq L hL e0 strat hb d T]

open Classical in
theorem zero_probe_gate_alpha_bad_event_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (d rows : Nat) (coeffsOf : Nat → List Element) :
    grindGateAlphaBadEvent L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) d rows coeffsOf
      = gateAlphaBadEvent L hL e0 strat hb d rows coeffsOf := by
  apply Finset.ext
  intro T
  simp only [grindGateAlphaBadEvent, gateAlphaBadEvent, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [zero_probe_triple_eq L hL e0 strat hb deriveStage (alphaBase d) T]

open Classical in
/-- (7) **THE FULL BAD EVENT AT ZERO PROBES IS THE ADOPTED RAW ONE.**  This is the
identity the adopted `GrindingUnionBound` HONESTY (ii) and section 3 record as
NOT PROVED ANYWHERE IN THIS TREE: `grindingFullBadEvent` at `q = 0` and
`grindingOfStrategy strat` IS `RawBlockLanes.rawFullBadEvent` at `strat`, as
`Finset`s.  With it, the class of section 8 of that module genuinely CONTAINS the
adopted `RawBlockLanes` line rather than merely running alongside it. -/
theorem zero_probe_full_bad_event_eq (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (strat : StrategyChainBound.Strategy) (hb : StrategyChainBound.StrategyBounded L strat)
    (logLane gateLane : RawLane) (d rows : Nat) (gv : Nat → Element)
    (coeffsOf : Nat → List Element) :
    grindingFullBadEvent L hL e0 0 (grindingOfStrategy strat)
        (grinding_of_strategy_bounded L hL strat hb) (grindLaneOfRawLane logLane)
        (grindLaneOfRawLane gateLane) d rows gv coeffsOf
      = rawFullBadEvent L hL e0 strat hb logLane gateLane d rows gv coeffsOf := by
  rw [grindingFullBadEvent, rawFullBadEvent,
    zero_probe_outer_bad_event_eq L hL e0 strat hb logLane gateLane d,
    zero_probe_gate_tau_bad_event_eq L hL e0 strat hb d gv,
    zero_probe_gate_alpha_bad_event_eq L hL e0 strat hb d rows coeffsOf]

/-- (7) The grinding clash constant at `q = 0` IS the adopted chain's: `N = 22 + 5 d`,
not `N = (22 + 5 d) (q + 1)` for some collapsed `q`. -/
theorem zero_probe_clash_count (d : Nat) : (22 + 5 * d) * (0 + 1) = 22 + 5 * d := by omega

open Classical in
/-- (7) **THE REDUCTION.**  At `q = 0` the adopted
`GrindingUnionBound.grinding_union_bad_draw_probability_le_combined`, instantiated
at the lifted prover and the lifted lanes, IS the adopted
`RawBlockLanes.raw_full_bad_draw_probability_le_combined`: the same event, the
same `ChallengeUnionBound.combinedBound`, and a clash term that has collapsed to
the adopted chain's `N (N + 1) / 2` at `N = 22 + 5 d`.

The statement below is DERIVED FROM the grinding bound, not from the adopted raw
one: the proof calls `grinding_union_bad_draw_probability_le_combined` and then
rewrites the event and the count.  So it is a genuine sanity check on the
grinding class, not a restatement of what was already adopted. -/
theorem grinding_bound_at_zero_probes_is_the_adopted_raw_bound (L : Nat) (hL : 64 ≤ L)
    (e0 : Transcript.Digest) (strat : StrategyChainBound.Strategy)
    (hb : StrategyChainBound.StrategyBounded L strat) (logLane gateLane : RawLane)
    (hlcau : RawLaneCausal logLane) (hgcau : RawLaneCausal gateLane)
    (d quo constraints : Nat) (gv : Nat → Element) (coeffsOf : Nat → List Element)
    (hdu : 12 + 6 * d < Transcript.u64Limit) (hlog : RawLaneBounded logLane 5)
    (hgate : RawLaneBounded gateLane (quo + 2))
    (hclen : ∀ i, i < 2 ^ d → (coeffsOf i).length ≤ constraints) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL e0 strat hb logLane gateLane d (2 ^ d) gv coeffsOf)
      ≤ ChallengeUnionBound.combinedBound d quo d constraints
        + ((22 + 5 * d : Nat) : ℚ) * (((22 + 5 * d : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) := by
  have h := grinding_union_bad_draw_probability_le_combined L hL e0 0 (grindingOfStrategy strat)
    (grinding_of_strategy_bounded L hL strat hb)
    (grinding_of_strategy_challenge_restricted strat)
    (grindLaneOfRawLane logLane) (grindLaneOfRawLane gateLane)
    (grind_lane_of_raw_lane_causal 0 logLane hlcau)
    (grind_lane_of_raw_lane_causal 0 gateLane hgcau)
    d quo constraints gv coeffsOf hdu
    (grind_lane_of_raw_lane_bounded logLane 5 hlog)
    (grind_lane_of_raw_lane_bounded gateLane (quo + 2) hgate) hclen
  rw [zero_probe_full_bad_event_eq L hL e0 strat hb logLane gateLane d (2 ^ d) gv coeffsOf,
    zero_probe_clash_count d] at h
  exact h

theorem raw_lane_bounded_mono (lane : RawLane) (b1 b2 : Nat) (h : b1 ≤ b2)
    (hbd : RawLaneBounded lane b1) : RawLaneBounded lane b2 :=
  fun r ch => ⟨le_trans (hbd r ch).1 h, le_trans (hbd r ch).2 h⟩

/-- (7) **THE WITNESS FOR THE ZERO-PROBE IDENTITY.**  A concrete transcript-
restricted prover -- the adopted `StrategyChainBound.constStrategy` at the empty
payload -- a concrete stage count `d = 13`, the adopted `separatedRawLane` on both
outer lanes, whose round-`0` target the adopted
`RawBlockLanes.separated_raw_target_zero_nonempty` proves inhabited, and the
empty coefficient family.  Every hypothesis of the reduction is discharged, so
the reduction is not vacuous. -/
theorem zero_probe_reduction_at_thirteen (L : Nat) (hL : 64 ≤ L) (e0 : Transcript.Digest)
    (gv : Nat → Element) :
    oracleProbability (boundedQueries L)
        (rawFullBadEvent L hL e0 (constStrategy (fun _ => (0, [])))
          (const_strategy_bounded L (fun _ => (0, [])) (fun _ => by
            show 61 + ([] : Transcript.Bytes).length ≤ L
            simp only [List.length_nil]
            omega))
          separatedRawLane separatedRawLane 13 (2 ^ 13) gv (fun _ => []))
      ≤ ChallengeUnionBound.combinedBound 13 8 13 123
        + ((22 + 5 * 13 : Nat) : ℚ) * (((22 + 5 * 13 : Nat) : ℚ) + 1) / 2
            / (Fintype.card Block : ℚ) :=
  grinding_bound_at_zero_probes_is_the_adopted_raw_bound L hL e0
    (constStrategy (fun _ => (0, [])))
    (const_strategy_bounded L (fun _ => (0, [])) (fun _ => by
      show 61 + ([] : Transcript.Bytes).length ≤ L
      simp only [List.length_nil]
      omega))
    separatedRawLane separatedRawLane separated_raw_lane_causal separated_raw_lane_causal
    13 8 123 gv (fun _ => []) thirteen_counter_budget separated_raw_lane_bounded
    (raw_lane_bounded_mono separatedRawLane 5 (8 + 2) (by omega) separated_raw_lane_bounded)
    (fun _ _ => Nat.zero_le _)

/-! ## 8. WHAT THE PAIRED LANE IS, AND WHAT THE RESTATEMENT DOES NOT COVER -/

/-- (8) **THE PAIRED LANE GENUINELY READS THE GRINDER'S PROBE ANSWERS.**  Two run
views that differ only at probe `0` of stage `22` give `selectorGrinder`'s paired
lane DIFFERENT round-`0` messages, at the same challenge view.  The probe budget
is written `q + 1` because at `q = 0` there are no probes to read. -/
theorem selector_grinder_paired_lane_reads_probes (e0 : Transcript.Digest) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element) :
    ∃ (a1 a2 : Nat → Block) (ch : Nat → Nat → Block),
      (grinderLane e0 (q + 1) selectorGrinder tr cl tcl).message 0 a1 ch
        ≠ (grinderLane e0 (q + 1) selectorGrinder tr cl tcl).message 0 a2 ch := by
  refine ⟨fun _ => unitTarget, fun _ => oneDigestBlock, fun _ _ => unitTarget, ?_⟩
  have hcond : slotPos (q + 1) (22 + 5 * 0) 0 < slotPos (q + 1) (22 + 5 * 0) (q + 1) := by
    rw [slotPos, slotPos]
    omega
  have h1 : grinderProbes e0 (q + 1) (22 + 5 * 0) (fun _ => unitTarget) (22 + 5 * 0) 0
      = unitTarget := by
    show (if slotPos (q + 1) (22 + 5 * 0) 0 < slotPos (q + 1) (22 + 5 * 0) (q + 1)
      then unitTarget else OuterChallenge.digestBlock e0) = unitTarget
    rw [if_pos hcond]
  have h2 : grinderProbes e0 (q + 1) (22 + 5 * 0) (fun _ => oneDigestBlock) (22 + 5 * 0) 0
      = oneDigestBlock := by
    show (if slotPos (q + 1) (22 + 5 * 0) 0 < slotPos (q + 1) (22 + 5 * 0) (q + 1)
      then oneDigestBlock else OuterChallenge.digestBlock e0) = oneDigestBlock
    rw [if_pos hcond]
  show decodeElements (if (grinderProbes e0 (q + 1) (22 + 5 * 0)
        (fun _ => unitTarget) (22 + 5 * 0) 0).val = unitTarget.val
      then bytesOfElement 1 else bytesOfElement 0)
    ≠ decodeElements (if (grinderProbes e0 (q + 1) (22 + 5 * 0)
        (fun _ => oneDigestBlock) (22 + 5 * 0) 0).val = unitTarget.val
      then bytesOfElement 1 else bytesOfElement 0)
  rw [h1, h2, if_pos rfl, if_neg one_block_ne_unit_target, decode_elements_of_element,
    decode_elements_of_element]
  intro hEq
  injection hEq with hhead _
  exact zero_ne_one hhead.symm

/-- (8) **SO THE PAIRED LANE IS NOT A LIFTED ADOPTED RAW LANE.**  No adopted
`RawBlockLanes.RawLane`, lifted along `grindLaneOfRawLane`, is this lane: a
`RawLane`'s message does not take the run's own answers as an argument at all,
which is why the adopted `GrindingUnionBound` widened the domain, and why the
pairing is stated at the widened one. -/
theorem paired_lane_is_not_a_lifted_raw_lane (e0 : Transcript.Digest) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (lane : RawLane) :
    grinderLane e0 (q + 1) selectorGrinder tr cl tcl ≠ grindLaneOfRawLane lane := by
  intro hEq
  obtain ⟨a1, a2, ch, hne⟩ := selector_grinder_paired_lane_reads_probes e0 q tr cl tcl
  refine hne ?_
  rw [hEq]
  rfl

/-- (8) **AND THAT SCOPE CLAIM DOES NOT DEPEND ON A CHOICE OF LIFT.**  The paired
lane's message is not `fun r _ ch => f r ch` for ANY `f` at all -- not merely
outside the image of the one adopted embedding `grindLaneOfRawLane`.  So "the
paired lane is outside the adopted raw domain" is a statement about the message
itself, not about the particular way the adopted domain is embedded in the
widened one. -/
theorem paired_message_is_not_run_independent (e0 : Transcript.Digest) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (f : Nat → (Nat → Nat → Block) → List Element) :
    (grinderLane e0 (q + 1) selectorGrinder tr cl tcl).message
      ≠ (fun r (_ : Nat → Block) ch => f r ch) := by
  intro hEq
  obtain ⟨a1, a2, ch, hne⟩ := selector_grinder_paired_lane_reads_probes e0 q tr cl tcl
  exact hne (by rw [hEq])

/-- **A LEGAL GRINDER WHOSE ROUND MESSAGE IS TOO LONG FOR THE ADOPTED LOG-LANE
DEGREE BOUND.**  It absorbs six encoded field elements at every stage. -/
def longMessageGrinder : GrindingStrategy where
  probe := fun k i h _ _ => (h k, 1, Transcript.le 8 i)
  absorb := fun _ _ _ _ => (0, unitRepeat 6)

theorem long_message_grinder_bounded (L : Nat) (hL : 205 ≤ L) :
    GrindingBounded L longMessageGrinder := by
  have hlen := unit_repeat_length 6
  refine ⟨fun _ i _ _ _ => ?_, fun _ _ _ _ => ?_⟩
  · show 61 + (Transcript.le 8 i).length ≤ L
    rw [Transcript.le_length]
    omega
  · show 61 + (unitRepeat 6).length ≤ L
    omega

theorem long_message_grinder_absorb (k : Nat) (h : Nat → Transcript.Digest)
    (ch : Transcript.Digest → Nat → Block) (pa : Nat → Nat → Block) :
    (longMessageGrinder.absorb k h ch pa).2 = unitRepeat 6 := rfl

theorem long_message_grinder_paired_message (e0 : Transcript.Digest) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element)
    (r : Nat) (a : Nat → Block) (ch : Nat → Nat → Block) :
    (grinderLane e0 q longMessageGrinder tr cl tcl).message r a ch
      = decodeElements (unitRepeat 6) := by
  show decodeElements (longMessageGrinder.absorb (22 + 5 * r)
      (grinderHist e0 q (22 + 5 * r) a)
      (digestLookup (grinderHist e0 q (22 + 5 * r) a) ch (22 + 5 * r))
      (grinderProbes e0 q (22 + 5 * r) a)).2 = decodeElements (unitRepeat 6)
  rw [long_message_grinder_absorb]

/-- (8) **A NEGATIVE RESULT: THE RESTATEMENT DOES NOT COVER EVERY GRINDER.**  The
paired lane of `longMessageGrinder` violates the adopted log-lane degree bound `5`,
so the hypothesis `hfitlog` of section 5 CANNOT be discharged for it.

WHAT IS AND IS NOT UNBOUNDED HERE.  The adopted
`GrindingUnionBound.grinding_union_bad_draw_probability_le_combined` STILL APPLIES
to `longMessageGrinder` with FREE lanes -- it is a legal `GrindingBounded` prover.
What no adopted lemma and nothing in this module bounds is the bad-draw mass of
its PAIRED lanes, the ones carrying its own six-element absorbed message.

This is not a defect of the pairing: the adopted
`ConditionalSoundness.round_bad_set_card` is what needs the degree bound, and no
adopted lemma covers a coupled-round message of six elements.  But it IS the
precise scope of the restatement, and it is stated rather than left implicit:
`grinder_paired_union_bad_draw_probability_le_combined` charges the grinder's own
attack only for grinders whose absorbed round message fits the verifier's degree
budget -- 120 bytes at the adopted `quo = 8`, by `budget_is_five_elements`, with
`six_elements_do_not_fit` marking exactly where this prover falls out. -/
theorem long_message_grinder_paired_lane_is_not_log_bounded (e0 : Transcript.Digest) (q : Nat)
    (tr : Nat → (Nat → Block) → (Nat → Nat → Block) → List Element) (cl tcl : Element) :
    ¬ GrindLaneBounded (grinderLane e0 q longMessageGrinder tr cl tcl) 5 := by
  intro hbd
  have h := (hbd 0 (fun _ => unitTarget) (fun _ _ => unitTarget)).1
  rw [long_message_grinder_paired_message e0 q tr cl tcl 0 (fun _ => unitTarget)
    (fun _ _ => unitTarget), decode_unit_repeat_length] at h
  exact absurd h (by decide)

end Audit.Wire3.GrindLanePairing
