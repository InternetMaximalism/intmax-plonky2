import Audit.Wire3.WhirParameters
import Audit.Wire3.WhirTail

/-!
# One checked configuration supplies every modeled WHIR phase

`run` accepts ONE WhirParameters.Params. Only after its real checkBound succeeds
does it derive initial forms, initial round count/threshold, the consecutive
(previous opening,current round) pairs, and the final opening/count/size/PoW
arguments for WhirTail.run. None of those phase parameters is another input.
The source correspondence is _getOpenParams (1053–1079), _verifyWhirProof's call
sequence, _phaseIntermediateRounds, and the typed validation entry.

CallerProfile is the explicitly assumed 3-commitment/1-vector production route,
NOT a source runtime guard. Generic typed validation does not imply this profile.
Although run accepts generic Params, source correspondence is restricted to
CallerProfile: outside it the retained Tail split predicate is not claimed to
match the generic source verifier.
The executable projections retain the source initial columns=interleaving*numVectors;
later columns/interleaving and folding counts come from the PREVIOUS round.
Verifier.base packages a generator; successful source-domain checks prove that
this packaging leaves its raw scalar unchanged rather than silently reducing it.
Successful run plus CallerProfile derives every reached intermediate input
ProfileShape and the final WhirTail.ProfileShape/contextShape from those checks
and the actual state transitions; these shapes are not extra caller assumptions.

No ABI/global VK digest/protocol derivation, bounded-word/overflow, memory/gas,
_glPow/quicksort instruction refinement, Hash/FS/query probability or PCS theorem
is claimed. This is a manual typed composition of existing executable models.
-/
namespace Audit.Wire3.WhirConfigured
open Spongefish (Hash Bytes Digest Ext3)

abbrev Params := WhirParameters.Params
abbrev Round := WhirParameters.Round
abbrev OpenParams := WhirIntermediate.OpenParams
abbrev RoundParams := WhirIntermediate.RoundParams

def CallerProfile (p : Params) : Prop := p.numCommitments = 3 ∧ p.numVectors = 1

def openDomain (d : WhirParameters.Domain) (samples columns folding : Nat) : OpenParams :=
  ⟨d.codewordLength,d.merkleDepth,Verifier.base d.domainGenerator,d.numCosets,d.cosetSize,
    samples,columns,folding⟩

def initialOpen (p : Params) : OpenParams :=
  openDomain p.initialDomain p.inDomainSamples (p.initialInterleavingDepth*p.numVectors)
    p.initialSumcheckRounds

def roundOpen (r : Round) : OpenParams :=
  openDomain r.domain r.inDomainSamples r.interleavingDepth r.sumcheckRounds

def roundParams (r : Round) : RoundParams :=
  ⟨r.outDomainSamples,r.numVariables,r.powThreshold,r.sumcheckRounds,r.sumcheckPowThreshold⟩

def phasePairs : OpenParams → List Round → List (OpenParams × RoundParams)
  | _,[] => []
  | previous,r::rest => (previous,roundParams r)::phasePairs (roundOpen r) rest

def lastOpen : OpenParams → List Round → OpenParams
  | previous,[] => previous
  | _,r::rest => lastOpen (roundOpen r) rest

/-- Source _getOpenParams is partial only at an out-of-range round index.
The declared count is checked before this projection is used by run. -/
def sourceOpen (p : Params) : Nat → Option OpenParams
  | 0 => some (initialOpen p)
  | i+1 => (p.rounds.get? i).map roundOpen

def openAt (previous : OpenParams) (rounds : List Round) : Nat → Option OpenParams
  | 0 => some previous
  | i+1 => match rounds with
    | [] => none
    | r::rest => openAt (roundOpen r) rest i

def finalParams (p : Params) : WhirTail.Params :=
  ⟨lastOpen (initialOpen p) p.rounds,p.finalSize,p.finalSumcheckRounds,
    p.finalPowThreshold,p.finalSumcheckPowThreshold⟩

def run (hash : Hash) (protocolId sessionId instanceBytes source hints : Bytes)
    (p : Params) (roots : List Digest) (expected : List Ext3) (mask : Bytes) : Option WhirTail.Result := do
  let forms ← WhirParameters.checkBound p roots.length expected.length mask.length
  WhirTail.run hash protocolId sessionId instanceBytes source hints
    (WhirParameters.initialParams p forms) roots expected mask
    p.initialSumcheckRounds p.initialSumcheckPowThreshold
    (phasePairs (initialOpen p) p.rounds) (finalParams p)

theorem opening_projection_keeps_all_fields (d : WhirParameters.Domain) (samples columns folding : Nat) :
    let o := openDomain d samples columns folding
    o.codewordLength = d.codewordLength ∧ o.merkleDepth = d.merkleDepth ∧
      o.cosetSize = d.cosetSize ∧ o.numCosets = d.numCosets ∧
      o.inDomainSamples = samples ∧ o.columns = columns ∧ o.foldingRounds = folding :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem checked_generator_is_not_reduced (d : WhirParameters.Domain) (samples columns folding : Nat)
    (h : WhirParameters.checkDomain d = true) :
    (openDomain d samples columns folding).domainGenerator.val = d.domainGenerator := by
  have hd := (WhirParameters.domain_success_exact d).mp h
  exact Nat.mod_eq_of_lt hd.2.2.2.2.2.2.2.2.2

theorem initial_open_columns_and_count_are_source_fields (p : Params) :
    (initialOpen p).columns = p.initialInterleavingDepth*p.numVectors ∧
      (initialOpen p).foldingRounds = p.initialSumcheckRounds ∧
      (initialOpen p).inDomainSamples = p.inDomainSamples := ⟨rfl,rfl,rfl⟩

theorem round_projection_keeps_all_five_fields (r : Round) :
    (roundParams r).outDomainSamples = r.outDomainSamples ∧
      (roundParams r).numVariables = r.numVariables ∧ (roundParams r).powThreshold = r.powThreshold ∧
      (roundParams r).sumcheckRounds = r.sumcheckRounds ∧
      (roundParams r).sumcheckPowThreshold = r.sumcheckPowThreshold := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem final_projection_keeps_all_fields (p : Params) :
    (finalParams p).openParams = lastOpen (initialOpen p) p.rounds ∧
      (finalParams p).finalSize = p.finalSize ∧ (finalParams p).finalRounds = p.finalSumcheckRounds ∧
      (finalParams p).finalPowThreshold = p.finalPowThreshold ∧
      (finalParams p).finalSumcheckPowThreshold = p.finalSumcheckPowThreshold := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem phase_pairs_count (previous : OpenParams) (rounds : List Round) :
    (phasePairs previous rounds).length = rounds.length := by
  induction rounds generalizing previous with
  | nil => rfl
  | cons r rest ih => simp [phasePairs,ih]

theorem phase_pairs_round_params_exact (previous : OpenParams) (rounds : List Round) :
    (phasePairs previous rounds).map Prod.snd = rounds.map roundParams := by
  induction rounds generalizing previous with
  | nil => rfl
  | cons r rest ih => simp [phasePairs,ih]

theorem open_at_successor_is_previous_round (previous : OpenParams) (rounds : List Round) (i : Nat) :
    openAt previous rounds (i+1) = (rounds.get? i).map roundOpen := by
  induction rounds generalizing previous i with
  | nil => rfl
  | cons r rest ih =>
    cases i with
    | zero => simp [openAt]
    | succ i => exact ih (roundOpen r) i

theorem open_at_is_source_get_open_params (p : Params) (i : Nat) :
    openAt (initialOpen p) p.rounds i = sourceOpen p i := by
  cases i with
  | zero => simp [openAt,sourceOpen]
  | succ i => exact open_at_successor_is_previous_round _ _ i

theorem final_open_is_last_position (previous : OpenParams) (rounds : List Round) :
    openAt previous rounds rounds.length = some (lastOpen previous rounds) := by
  induction rounds generalizing previous with
  | nil => rfl
  | cons r _ ih => exact ih (roundOpen r)

theorem checked_final_open_matches_declared_round_index (p : Params) (roots evaluations maskLength : Nat)
    (forms : List (List Ext3)) (h : WhirParameters.checkBound p roots evaluations maskLength = some forms) :
    sourceOpen p p.numRounds = some (finalParams p).openParams := by
  have hc := WhirParameters.bound_success_entry_guards p roots evaluations maskLength forms h
  have hs := WhirParameters.core_success_implies_existing_schedule p _ forms hc.2.2.2.2.2.2
  have hl := WhirSchedule.accepted_declared_round_count_exact (WhirParameters.schedule p) hs
  simp only [WhirParameters.schedule,List.length_map] at hl
  rw [←hl,←open_at_is_source_get_open_params,final_open_is_last_position]
  rfl

theorem phase_pairs_each_position (previous : OpenParams) (rounds : List Round) (i : Nat) (r : Round)
    (h : rounds.get? i = some r) : ∃ o,
      openAt previous rounds i = some o ∧
      (phasePairs previous rounds).get? i = some (o,roundParams r) := by
  induction rounds generalizing previous i with
  | nil => simp at h
  | cons first rest ih =>
    cases i with
    | zero => cases h; exact ⟨previous,rfl,rfl⟩
    | succ i => exact ih (roundOpen first) i h

theorem phase_pairs_append_uses_previous_slice (previous : OpenParams) (first rest : List Round) :
    phasePairs previous (first++rest) =
      phasePairs previous first ++ phasePairs (lastOpen previous first) rest := by
  induction first generalizing previous with
  | nil => rfl
  | cons r first ih =>
    exact congrArg (List.cons (previous,roundParams r)) (ih (roundOpen r))

theorem last_open_append (previous : OpenParams) (first rest : List Round) :
    lastOpen previous (first++rest) = lastOpen (lastOpen previous first) rest := by
  induction first generalizing previous with
  | nil => rfl
  | cons r _ ih => exact ih (roundOpen r)

theorem intermediate_run_append_threads_same_state (hash : Hash) (source hints : Bytes)
    (first rest : List (OpenParams × RoundParams)) (s : WhirIntermediate.State) :
    WhirIntermediate.runRounds hash source hints (first++rest) s =
      (WhirIntermediate.runRounds hash source hints first s).bind
        (WhirIntermediate.runRounds hash source hints rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons pair first ih =>
    rcases pair with ⟨o,p⟩
    cases hr : WhirIntermediate.runRound hash source hints o p s <;>
      simp [WhirIntermediate.runRounds,hr,ih]

theorem actual_round_at_split_has_continuous_configuration_and_state (hash : Hash) (source hints : Bytes)
    (previous : OpenParams) (first rest : List Round) (r : Round) (s t : WhirIntermediate.State)
    (h : WhirIntermediate.runRounds hash source hints (phasePairs previous (first++r::rest)) s = some t) :
    ∃ before after,
      WhirIntermediate.runRounds hash source hints (phasePairs previous first) s = some before ∧
      WhirIntermediate.runRound hash source hints (lastOpen previous first) (roundParams r) before = some after ∧
      WhirIntermediate.runRounds hash source hints (phasePairs (roundOpen r) rest) after = some t := by
  rw [phase_pairs_append_uses_previous_slice,intermediate_run_append_threads_same_state] at h
  cases hf : WhirIntermediate.runRounds hash source hints (phasePairs previous first) s with
  | none => simp [hf] at h
  | some before =>
    simp only [hf,Option.bind,phasePairs] at h
    obtain ⟨after,hr,ht⟩ := WhirIntermediate.sequence_success_threads_actual_next hash source hints
      (lastOpen previous first) (roundParams r) (phasePairs (roundOpen r) rest) before t h
    exact ⟨before,after,rfl,hr,ht⟩

theorem configured_success_uses_only_checked_projection (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    ∃ forms, WhirParameters.checkBound p roots.length expected.length mask.length = some forms ∧
      WhirTail.run hash protocolId sessionId instanceBytes source hints
        (WhirParameters.initialParams p forms) roots expected mask p.initialSumcheckRounds
        p.initialSumcheckPowThreshold (phasePairs (initialOpen p) p.rounds) (finalParams p) = some result := by
  unfold run at h
  cases hc : WhirParameters.checkBound p roots.length expected.length mask.length with
  | none => simp [hc] at h
  | some forms => exact ⟨forms,rfl,by simpa only [hc,bind,Option.bind] using h⟩

theorem configured_success_has_valid_initial_parameters (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    ∃ forms, WhirParameters.checkBound p roots.length expected.length mask.length = some forms ∧
      WhirInitial.validatedParams (WhirParameters.initialParams p forms) roots expected mask := by
  obtain ⟨forms,hc,_⟩ := configured_success_uses_only_checked_projection hash protocolId sessionId
    instanceBytes source hints p roots expected mask result h
  exact ⟨forms,hc,WhirParameters.bound_success_initial_params_validated p roots expected mask forms hc⟩

theorem configured_success_initial_and_intermediate_provenance (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    ∃ forms, WhirParameters.checkBound p roots.length expected.length mask.length = some forms ∧
      WhirPrefix.run hash source (WhirParameters.initialParams p forms) roots expected mask
        p.initialSumcheckRounds p.initialSumcheckPowThreshold
        (Spongefish.init hash protocolId sessionId instanceBytes) = some result.retained.origin ∧
      WhirIntermediate.runRounds hash source hints (phasePairs (initialOpen p) p.rounds)
        (WhirIntermediate.fromPrefix result.retained.origin) = some result.retained.current ∧
      WhirTail.runTail hash source hints (finalParams p) result.retained = some result := by
  obtain ⟨forms,hc,hr⟩ := configured_success_uses_only_checked_projection hash protocolId sessionId
    instanceBytes source hints p roots expected mask result h
  exact ⟨forms,hc,WhirTail.whole_execution_retains_initial_and_intermediate_provenance hash
    protocolId sessionId instanceBytes source hints (WhirParameters.initialParams p forms)
    roots expected mask p.initialSumcheckRounds p.initialSumcheckPowThreshold
    (phasePairs (initialOpen p) p.rounds) (finalParams p) result hr⟩

/-- Configuration-only shape, without inventing a state's randomness/bindings. -/
def OpenShape (o : OpenParams) : Prop :=
  o.foldingRounds < 256 ∧ o.columns = 2^o.foldingRounds ∧ 0 < o.cosetSize ∧
    o.codewordLength = o.cosetSize*o.numCosets ∧ o.codewordLength = 2^o.merkleDepth ∧ o.merkleDepth < 256

theorem domain_and_folding_guards_supply_open_shape (d : WhirParameters.Domain) (samples columns folding : Nat)
    (hd : WhirParameters.checkDomain d = true) (hf : folding < 256) (hc : columns = 2^folding) :
    OpenShape (openDomain d samples columns folding) := by
  have h := (WhirParameters.domain_success_exact d).mp hd
  have hp := (WhirParameters.domain_success_partition_and_generator d hd).1
  exact ⟨hf,hc,h.2.2.2.2.1,hp,h.2.2.2.1,h.2.2.1⟩

theorem checked_profile_supplies_initial_open_shape (p : Params) (roots evaluations maskLength : Nat)
    (forms : List (List Ext3)) (hprofile : CallerProfile p)
    (h : WhirParameters.checkBound p roots evaluations maskLength = some forms) : OpenShape (initialOpen p) := by
  have hb := WhirParameters.bound_success_entry_guards p roots evaluations maskLength forms h
  have hc := WhirParameters.core_success_sequence p _ forms hb.2.2.2.2.2.2
  have hs := WhirParameters.core_success_implies_existing_schedule p _ forms hb.2.2.2.2.2.2
  have hi := WhirSchedule.accepted_initial_interleaving_exact (WhirParameters.schedule p) hs
  apply domain_and_folding_guards_supply_open_shape _ _ _ _ hc.2.1 hi.2.1
  simpa only [hprofile.2,Nat.mul_one] using hi.2.2

theorem checked_profile_supplies_each_later_open_shape (p : Params) (roots evaluations maskLength : Nat)
    (forms : List (List Ext3)) (r : Round) (hm : r ∈ p.rounds)
    (h : WhirParameters.checkBound p roots evaluations maskLength = some forms) : OpenShape (roundOpen r) := by
  have hb := WhirParameters.bound_success_entry_guards p roots evaluations maskLength forms h
  have hc := WhirParameters.core_success_checks_all_domains p _ forms hb.2.2.2.2.2.2
  have hs := WhirParameters.core_success_implies_existing_schedule p _ forms hb.2.2.2.2.2.2
  have hr := WhirSchedule.accepted_rounds_are_positive_and_bounded (WhirParameters.schedule p) r.folding hs
    (List.mem_map.mpr ⟨r,hm,rfl⟩)
  exact domain_and_folding_guards_supply_open_shape _ _ _ _ (hc.2 r hm) hr.2.1 hr.2.2.2

theorem prefix_success_supplies_binding_dimensions (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (forms : List (List Ext3))
    (start : Spongefish.State) (origin : WhirPrefix.Result) (hp : CallerProfile p)
    (hc : WhirParameters.checkBound p roots.length expected.length mask.length = some forms)
    (hr : WhirPrefix.run hash source (WhirParameters.initialParams p forms) roots expected mask
      p.initialSumcheckRounds p.initialSumcheckPowThreshold start = some origin) :
    (WhirIntermediate.fromPrefix origin).initialRoots.length = 3 ∧
      (WhirIntermediate.fromPrefix origin).vectorRlc.length = 3 ∧
      origin.sumcheck.finalRandomness.length = p.initialSumcheckRounds := by
  have hv := WhirParameters.bound_success_initial_params_validated p roots expected mask forms hc
  obtain ⟨afterInitial,hi,_,_⟩ := WhirPrefix.successful_prefix_is_one_execution hash source
    (WhirParameters.initialParams p forms) roots expected mask p.initialSumcheckRounds
    p.initialSumcheckPowThreshold start origin hr
  have hd := WhirInitial.initial_output_shapes hash source (WhirParameters.initialParams p forms)
    roots expected mask start afterInitial origin.initial hv hi
  have hn := (WhirPrefix.successful_prefix_exact_consumption hash source (WhirParameters.initialParams p forms)
    roots expected mask p.initialSumcheckRounds p.initialSumcheckPowThreshold start origin hr).2.1
  simp only [WhirIntermediate.fromPrefix,List.length_map,WhirParameters.initialParams,
    WhirInitial.totalVectors,hp.1,hp.2,Nat.mul_one] at hd ⊢
  exact ⟨hd.1,hd.2.2.2.2.1,hn⟩

theorem prefix_success_derives_initial_profile_shape (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (forms : List (List Ext3))
    (start : Spongefish.State) (origin : WhirPrefix.Result) (hp : CallerProfile p)
    (hc : WhirParameters.checkBound p roots.length expected.length mask.length = some forms)
    (hr : WhirPrefix.run hash source (WhirParameters.initialParams p forms) roots expected mask
      p.initialSumcheckRounds p.initialSumcheckPowThreshold start = some origin) :
    WhirIntermediate.ProfileShape (WhirIntermediate.fromPrefix origin) (initialOpen p) := by
  have hd := prefix_success_supplies_binding_dimensions hash source p roots expected mask forms start origin hp hc hr
  have ho := checked_profile_supplies_initial_open_shape p roots.length expected.length mask.length forms hp hc
  exact ⟨hd.1,hd.2.1,by simp [WhirIntermediate.fromPrefix,initialOpen,openDomain,hd.2.2],ho⟩

theorem last_open_keeps_checked_shape (previous : OpenParams) (rounds : List Round)
    (hp : OpenShape previous) (hr : ∀ r ∈ rounds, OpenShape (roundOpen r)) :
    OpenShape (lastOpen previous rounds) := by
  induction rounds generalizing previous with
  | nil => exact hp
  | cons r rest ih =>
    exact ih (roundOpen r) (hr r (by simp)) (by intro x hx; exact hr x (by simp [hx]))

theorem actual_round_derives_next_profile_shape (hash : Hash) (source hints : Bytes)
    (previous : OpenParams) (r : Round) (s t : WhirIntermediate.State)
    (hs : WhirIntermediate.ProfileShape s previous) (ho : OpenShape (roundOpen r))
    (h : WhirIntermediate.runRound hash source hints previous (roundParams r) s = some t) :
    WhirIntermediate.ProfileShape t (roundOpen r) := by
  have hb := WhirIntermediate.round_success_preserves_initial_roots_and_rlc hash source hints
    previous (roundParams r) s t h
  have hn := (WhirIntermediate.round_success_adds_exact_rounds_and_constraint hash source hints
    previous (roundParams r) s t h).1
  simp only [roundParams] at hn
  exact ⟨by simpa only [hb.1] using hs.1,by simpa only [hb.2] using hs.2.1,by
    change r.sumcheckRounds ≤ t.sumcheck.finalRandomness.length
    omega,ho⟩

theorem actual_sequence_derives_final_profile_shape (hash : Hash) (source hints : Bytes)
    (previous : OpenParams) (rounds : List Round) (s t : WhirIntermediate.State)
    (hs : WhirIntermediate.ProfileShape s previous) (ho : ∀ r ∈ rounds, OpenShape (roundOpen r))
    (h : WhirIntermediate.runRounds hash source hints (phasePairs previous rounds) s = some t) :
    WhirIntermediate.ProfileShape t (lastOpen previous rounds) := by
  induction rounds generalizing previous s with
  | nil => cases h; exact hs
  | cons r rest ih =>
    obtain ⟨next,hr,ht⟩ := WhirIntermediate.sequence_success_threads_actual_next hash source hints
      previous (roundParams r) (phasePairs (roundOpen r) rest) s t h
    exact ih (roundOpen r) next
      (actual_round_derives_next_profile_shape hash source hints previous r s next hs (ho r (by simp)) hr)
      (by intro x hx; exact ho x (by simp [hx])) ht

theorem actual_sequence_folding_count_exact (hash : Hash) (source hints : Bytes)
    (previous : OpenParams) (rounds : List Round) (s t : WhirIntermediate.State)
    (h : WhirIntermediate.runRounds hash source hints (phasePairs previous rounds) s = some t) :
    t.sumcheck.finalRandomness.length = s.sumcheck.finalRandomness.length +
      WhirSchedule.roundSum (rounds.map WhirParameters.Round.folding) := by
  induction rounds generalizing previous s with
  | nil => cases h; simp [WhirSchedule.roundSum]
  | cons r rest ih =>
    obtain ⟨next,hr,ht⟩ := WhirIntermediate.sequence_success_threads_actual_next hash source hints
      previous (roundParams r) (phasePairs (roundOpen r) rest) s t h
    have hn := (WhirIntermediate.round_success_adds_exact_rounds_and_constraint hash source hints
      previous (roundParams r) s next hr).1
    have hh := ih (roundOpen r) next ht
    simp only [roundParams,WhirSchedule.roundSum,List.map_cons,WhirParameters.Round.folding] at hn ⊢
    omega

def ConstraintsShape (total : Nat) (entries : List WhirFinal.RoundConstraint) : Prop :=
  ∀ entry ∈ entries, entry.coefficients.length = entry.points.length ∧ entry.numVariables ≤ total

theorem actual_round_preserves_constraint_shape (hash : Hash) (source hints : Bytes)
    (previous : OpenParams) (r : Round) (s t : WhirIntermediate.State) (total : Nat)
    (hs : ConstraintsShape total s.constraints) (hv : r.numVariables ≤ total)
    (h : WhirIntermediate.runRound hash source hints previous (roundParams r) s = some t) :
    ConstraintsShape total t.constraints := by
  obtain ⟨message,opening,claims,afterMerkle,afterRlc,_,he,hlen,hnum⟩ :=
    WhirIntermediate.stored_constraint_same_points_and_rlc hash source hints previous (roundParams r) s t h
  intro entry hm
  rw [he] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hs entry hm
  · simp only [List.mem_singleton] at hm
    subst entry
    exact ⟨hlen,by simpa only [hnum,roundParams] using hv⟩

theorem actual_sequence_preserves_constraint_shape (hash : Hash) (source hints : Bytes)
    (previous : OpenParams) (rounds : List Round) (s t : WhirIntermediate.State) (total : Nat)
    (hs : ConstraintsShape total s.constraints) (hv : ∀ r ∈ rounds, r.numVariables ≤ total)
    (h : WhirIntermediate.runRounds hash source hints (phasePairs previous rounds) s = some t) :
    ConstraintsShape total t.constraints := by
  induction rounds generalizing previous s with
  | nil => cases h; exact hs
  | cons r rest ih =>
    obtain ⟨next,hr,ht⟩ := WhirIntermediate.sequence_success_threads_actual_next hash source hints
      previous (roundParams r) (phasePairs (roundOpen r) rest) s t h
    exact ih (roundOpen r) next
      (actual_round_preserves_constraint_shape hash source hints previous r s next total hs (hv r (by simp)) hr)
      (by intro x hx; exact hv x (by simp [hx])) ht

theorem checked_round_annotations_bounded_by_original (p : Params) (roots evaluations maskLength : Nat)
    (forms : List (List Ext3)) (r : Round) (hm : r ∈ p.rounds)
    (h : WhirParameters.checkBound p roots evaluations maskLength = some forms) : r.numVariables ≤ p.numVariables := by
  have hb := WhirParameters.bound_success_entry_guards p roots evaluations maskLength forms h
  have hs := WhirParameters.core_success_implies_existing_schedule p _ forms hb.2.2.2.2.2.2
  have hr := (WhirSchedule.schedule_success_exact (WhirParameters.schedule p)).mp hs
  have ht := WhirSchedule.checked_round_member_guards p.foldingFactor (p.numVariables-p.initialSumcheckRounds)
    p.finalSumcheckRounds (p.rounds.map WhirParameters.Round.folding) r.folding hr.2.1
    (List.mem_map.mpr ⟨r,hm,rfl⟩)
  exact Nat.le_trans ht.2.2.2.2 (Nat.sub_le _ _)

theorem prefix_success_derives_forms_and_initial_constraint_shape (hash : Hash) (source : Bytes) (p : Params)
    (roots : List Digest) (expected : List Ext3) (mask : Bytes) (forms : List (List Ext3))
    (start : Spongefish.State) (origin : WhirPrefix.Result)
    (hc : WhirParameters.checkBound p roots.length expected.length mask.length = some forms)
    (hr : WhirPrefix.run hash source (WhirParameters.initialParams p forms) roots expected mask
      p.initialSumcheckRounds p.initialSumcheckPowThreshold start = some origin) :
    origin.initial.initialRoundConstraint.numVariables = p.numVariables ∧
      0 < origin.initial.forms.length ∧
      (∀ form ∈ origin.initial.forms, form.point.length = p.numVariables) ∧
      ConstraintsShape p.numVariables (WhirIntermediate.fromPrefix origin).constraints := by
  have hv := WhirParameters.bound_success_initial_params_validated p roots expected mask forms hc
  have hb := WhirParameters.bound_success_entry_guards p roots.length expected.length mask.length forms hc
  have hs := WhirSchedule.accepted_original_counts_match (WhirParameters.schedule p)
    (WhirParameters.core_success_implies_existing_schedule p _ forms hb.2.2.2.2.2.2)
  simp only [WhirParameters.schedule] at hs
  obtain ⟨afterInitial,hi,_,_⟩ := WhirPrefix.successful_prefix_is_one_execution hash source
    (WhirParameters.initialParams p forms) roots expected mask p.initialSumcheckRounds
    p.initialSumcheckPowThreshold start origin hr
  have hout := WhirInitial.initial_output_shapes hash source (WhirParameters.initialParams p forms)
    roots expected mask start afterInitial origin.initial hv hi
  have hdata := WhirInitial.initial_sum_and_constraints_same_data hash source (WhirParameters.initialParams p forms)
    roots expected mask start afterInitial origin.initial hi
  have hpoints := WhirInitial.initial_forms_use_supplied_points hash source (WhirParameters.initialParams p forms)
    roots expected mask start afterInitial origin.initial hv hi
  have hconstraint := WhirPrefix.projected_initial_constraints_have_exact_shape hash source
    (WhirParameters.initialParams p forms) roots expected mask p.initialSumcheckRounds
    p.initialSumcheckPowThreshold start origin hv hr
  refine ⟨hdata.2.2.2.1.trans hs.2.2,?_,?_,?_⟩
  · have hpos := hv.2.2.2.2.2.1
    have hlen := hout.2.2.2.2.2.2.2.2
    simp only [WhirParameters.initialParams] at hpos hlen
    omega
  · intro form hm
    exact (hpoints form hm).2.trans hs.2.2
  · intro entry hm
    simp only [WhirIntermediate.fromPrefix,List.mem_singleton] at hm
    subst entry
    exact ⟨hconstraint.1.trans hconstraint.2.1.symm,by
      rw [hconstraint.2.2.1]
      change p.initialNumVariables ≤ p.numVariables
      omega⟩

/-- Full terminal shape follows from this single checked config and its actual
execution, plus ONLY the explicit production caller profile. It is not an
independently supplied Context/shape hypothesis or a new runtime guard. -/
theorem configured_success_derives_tail_profile_shape (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result) (hp : CallerProfile p)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    WhirTail.ProfileShape result.retained (finalParams p) := by
  obtain ⟨forms,hc,hi,hr,_⟩ := configured_success_initial_and_intermediate_provenance hash protocolId sessionId
    instanceBytes source hints p roots expected mask result h
  have hb := WhirParameters.bound_success_entry_guards p roots.length expected.length mask.length forms hc
  have hs := WhirParameters.core_success_implies_existing_schedule p _ forms hb.2.2.2.2.2.2
  have hcounts := WhirSchedule.accepted_original_counts_match (WhirParameters.schedule p) hs
  have hfinal := WhirSchedule.accepted_final_size_exact (WhirParameters.schedule p) hs
  have hpartition := WhirSchedule.accepted_schedule_partitions_original_variables (WhirParameters.schedule p) hs
  have hshape := prefix_success_derives_initial_profile_shape hash source p roots expected mask forms
    (Spongefish.init hash protocolId sessionId instanceBytes) result.retained.origin hp hc hi
  have ht := actual_sequence_derives_final_profile_shape hash source hints (initialOpen p) p.rounds
    (WhirIntermediate.fromPrefix result.retained.origin) result.retained.current hshape
    (fun r hm => checked_profile_supplies_each_later_open_shape p _ _ _ forms r hm hc) hr
  have hf := prefix_success_derives_forms_and_initial_constraint_shape hash source p roots expected mask forms
    (Spongefish.init hash protocolId sessionId instanceBytes) result.retained.origin hc hi
  have hconst := actual_sequence_preserves_constraint_shape hash source hints (initialOpen p) p.rounds
    (WhirIntermediate.fromPrefix result.retained.origin) result.retained.current p.numVariables hf.2.2.2
    (fun r hm => checked_round_annotations_bounded_by_original p _ _ _ forms r hm hc) hr
  have hinitCount := (prefix_success_supplies_binding_dimensions hash source p roots expected mask forms
    (Spongefish.init hash protocolId sessionId instanceBytes) result.retained.origin hp hc hi).2.2
  have hroundCount := actual_sequence_folding_count_exact hash source hints (initialOpen p) p.rounds
    (WhirIntermediate.fromPrefix result.retained.origin) result.retained.current hr
  simp only [WhirParameters.schedule,WhirIntermediate.fromPrefix] at hpartition hcounts hfinal hroundCount
  unfold WhirTail.ProfileShape WhirTail.totalVariables
  rw [hf.1]
  exact ⟨ht,hfinal.2,hfinal.1,by change p.numVariables = _; dsimp only [finalParams]; omega,
    hcounts.1,hcounts.2.1,hf.2.1,hf.2.2.1,hconst⟩

theorem configured_success_derives_existing_context_shape (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result) (hp : CallerProfile p)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    WhirFinal.contextShape (WhirTail.context (finalParams p) result.retained result.rows) = true :=
  WhirTail.fixed_profile_supplies_context_shape _ _ _
    (configured_success_derives_tail_profile_shape hash protocolId sessionId instanceBytes source hints
      p roots expected mask result hp h)

theorem configured_success_final_counts_and_both_eof (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    result.finalSumcheck.finalRandomness.length = p.finalSumcheckRounds ∧
      result.rows.vector.length = p.finalSize ∧
      result.finalSumcheck.cursor.transcriptPos = source.length ∧ result.rows.afterRows.hintPos = hints.length := by
  obtain ⟨_,_,_,_,ht⟩ := configured_success_initial_and_intermediate_provenance hash protocolId sessionId
    instanceBytes source hints p roots expected mask result h
  have he := WhirTail.accepted_tail_has_exact_final_rounds_and_both_eof hash source hints (finalParams p)
    result.retained result ht
  have hv := (WhirTail.accepted_tail_every_sample_compared_with_same_vector hash source hints (finalParams p)
    result.retained result ht).1
  exact ⟨he.1,hv,he.2⟩

theorem checked_projection_preserves_all_generator_scalars (p : Params) (roots evaluations maskLength : Nat)
    (forms : List (List Ext3)) (h : WhirParameters.checkBound p roots evaluations maskLength = some forms) :
    (initialOpen p).domainGenerator.val = p.initialDomain.domainGenerator ∧
      ∀ r ∈ p.rounds, (roundOpen r).domainGenerator.val = r.domain.domainGenerator := by
  have hb := WhirParameters.bound_success_entry_guards p roots evaluations maskLength forms h
  have hd := WhirParameters.core_success_checks_all_domains p _ forms hb.2.2.2.2.2.2
  exact ⟨checked_generator_is_not_reduced _ _ _ _ hd.1,fun r hm =>
    checked_generator_is_not_reduced _ _ _ _ (hd.2 r hm)⟩

theorem configured_success_completed_round_count_exact (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    result.retained.current.completedRounds = p.numRounds := by
  obtain ⟨forms,hc,_,hr,_⟩ := configured_success_initial_and_intermediate_provenance hash protocolId sessionId
    instanceBytes source hints p roots expected mask result h
  have hb := WhirParameters.bound_success_entry_guards p roots.length expected.length mask.length forms hc
  have hs := WhirParameters.core_success_implies_existing_schedule p _ forms hb.2.2.2.2.2.2
  have hl := WhirSchedule.accepted_declared_round_count_exact (WhirParameters.schedule p) hs
  have hcount := (WhirIntermediate.all_rounds_keep_initial_binding_and_constraint_count hash source hints
    (phasePairs (initialOpen p) p.rounds) (WhirIntermediate.fromPrefix result.retained.origin)
    result.retained.current hr).2.2.1
  simp only [WhirIntermediate.fromPrefix,phase_pairs_count,Nat.zero_add] at hcount
  simp only [WhirParameters.schedule,List.length_map] at hl
  exact hcount.trans hl

theorem configured_split_branch_matches_source_predicate (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result) (hp : CallerProfile p)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    result.retained.current.completedRounds = 0 ↔ p.numRounds = 0 ∧ 1 < p.numCommitments := by
  rw [configured_success_completed_round_count_exact hash protocolId sessionId instanceBytes source hints
    p roots expected mask result h,hp.1]
  simp

theorem configured_success_each_round_derives_its_input_profile (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes) (result : WhirTail.Result) (hp : CallerProfile p)
    (first rest : List Round) (r : Round) (he : p.rounds = first++r::rest)
    (h : run hash protocolId sessionId instanceBytes source hints p roots expected mask = some result) :
    ∃ before after,
      WhirIntermediate.runRounds hash source hints (phasePairs (initialOpen p) first)
        (WhirIntermediate.fromPrefix result.retained.origin) = some before ∧
      WhirIntermediate.ProfileShape before (lastOpen (initialOpen p) first) ∧
      WhirIntermediate.runRound hash source hints (lastOpen (initialOpen p) first) (roundParams r) before = some after ∧
      WhirIntermediate.runRounds hash source hints (phasePairs (roundOpen r) rest) after =
        some result.retained.current := by
  obtain ⟨forms,hc,hi,hr,_⟩ := configured_success_initial_and_intermediate_provenance hash protocolId sessionId
    instanceBytes source hints p roots expected mask result h
  have hs := prefix_success_derives_initial_profile_shape hash source p roots expected mask forms
    (Spongefish.init hash protocolId sessionId instanceBytes) result.retained.origin hp hc hi
  rw [he] at hr
  obtain ⟨before,after,hfirst,hround,hrest⟩ := actual_round_at_split_has_continuous_configuration_and_state
    hash source hints (initialOpen p) first rest r (WhirIntermediate.fromPrefix result.retained.origin)
    result.retained.current hr
  have ho : ∀ x ∈ first, OpenShape (roundOpen x) := by
    intro x hx
    apply checked_profile_supplies_each_later_open_shape p _ _ _ forms x _ hc
    rw [he]
    exact List.mem_append_left _ hx
  exact ⟨before,after,hfirst,actual_sequence_derives_final_profile_shape hash source hints (initialOpen p) first
    (WhirIntermediate.fromPrefix result.retained.origin) before hs ho hfirst,hround,hrest⟩

theorem invalid_parameters_do_not_reach_any_phase (hash : Hash)
    (protocolId sessionId instanceBytes source hints : Bytes) (p : Params) (roots : List Digest)
    (expected : List Ext3) (mask : Bytes)
    (h : WhirParameters.checkBound p roots.length expected.length mask.length = none) :
    run hash protocolId sessionId instanceBytes source hints p roots expected mask = none := by
  simp [run,h]

def exampleDomain : WhirParameters.Domain := ⟨1,0,1,1,1⟩
def exampleRound : Round := ⟨exampleDomain,1,0,1,2,2,Spongefish.maxCounter,Spongefish.maxCounter⟩
def exampleNoRounds : Params :=
  { numVariables := 1
    foldingFactor := 1
    numVectors := 1
    numCommitments := 3
    outDomainSamples := 0
    inDomainSamples := 1
    initialSumcheckRounds := 1
    numRounds := 0
    finalSumcheckRounds := 0
    finalSize := 1
    initialDomain := exampleDomain
    initialInterleavingDepth := 2
    initialNumVariables := 1
    initialSumcheckPowThreshold := Spongefish.maxCounter
    finalPowThreshold := Spongefish.maxCounter
    finalSumcheckPowThreshold := Spongefish.maxCounter
    evaluationPoint := [Arithmetic.zero]
    evaluationPoint2 := []
    additionalEvaluationPoints := []
    rounds := [] }
def exampleOneRound : Params :=
  { exampleNoRounds with
    numVariables := 3
    initialNumVariables := 3
    numRounds := 1
    finalSumcheckRounds := 1
    finalSize := 2
    evaluationPoint := List.replicate 3 Arithmetic.zero
    rounds := [exampleRound] }

theorem no_round_projection_uses_initial_open :
    phasePairs (initialOpen exampleNoRounds) exampleNoRounds.rounds = [] ∧
      (finalParams exampleNoRounds).openParams = initialOpen exampleNoRounds := ⟨rfl,rfl⟩

theorem nonzero_round_projection_uses_previous_slice :
    phasePairs (initialOpen exampleOneRound) exampleOneRound.rounds =
      [(initialOpen exampleOneRound,roundParams exampleRound)] ∧
      (finalParams exampleOneRound).openParams = roundOpen exampleRound := ⟨rfl,rfl⟩

theorem ordinary_profiles_and_parameter_checks_succeed :
    CallerProfile exampleNoRounds ∧ CallerProfile exampleOneRound ∧
      (WhirParameters.checkBound exampleNoRounds 3 3 1).isSome = true ∧
      (WhirParameters.checkBound exampleOneRound 3 3 1).isSome = true := by
  unfold CallerProfile
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Toy constant Hash, not a production proof. The SAME existing nonzero final
claim example now reaches all phases through one checked source-shaped config. -/
theorem configured_zero_intermediate_round_execution_example :
    (run (fun _ => Spongefish.zeroDigest) [] [] []
      (WhirTail.exampleInitialSource ++ WhirTail.exampleExt 1) WhirTail.exampleBaseHints
      exampleNoRounds (List.replicate 3 Spongefish.zeroDigest) WhirTail.exampleClaims [⟨7,by decide⟩]).map
      (fun result => (result.retained.current.completedRounds,result.rows.vector.length,
        result.finalSumcheck.cursor.transcriptPos,result.rows.afterRows.hintPos)) = some (0,1,336,72) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem configured_one_intermediate_round_execution_example :
    (run (fun _ => Spongefish.zeroDigest) [] [] [] WhirTail.exampleSingleSource WhirTail.exampleSingleHints
      exampleOneRound (List.replicate 3 Spongefish.zeroDigest) WhirTail.exampleClaims [⟨7,by decide⟩]).map
      (fun result => (result.retained.current.completedRounds,result.rows.vector.length,
        result.finalSumcheck.finalRandomness.length,result.finalSumcheck.cursor.transcriptPos,
        result.rows.afterRows.hintPos)) = some (1,2,1,488,128) := by rfl

end Audit.Wire3.WhirConfigured
