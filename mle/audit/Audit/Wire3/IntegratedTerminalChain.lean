import Audit.Wire3.Integrated
import Audit.Wire3.OuterClaimChain
import Audit.Wire3.NormTerminalBinding
import Audit.Wire3.GateTerminalBinding
import Audit.Wire3.OpenedClaimFold

/-!
# Terminal chain glue into the adopted `Integrated.verify`

Sources reviewed:
* mle/src/verifier_v2.rs 277-301 (coupled rounds from zero claims), 303-311
  (index sampling), 313-375 (five folds, mask, packed points), 386-395
  (`verify_grouped`, i.e. WHIR, BEFORE the norm terminal), 397-420 (norm
  terminal `log_terminal == log_final_claim`), 422-434 (gate terminal
  `eq(gate_tau, gate_point) * gate_terminal == gate_final_claim`);
* mle/contracts/src/MleVerifierV2.sol 303-392 (`_verifyAtomic`: rounds AND
  the norm terminal inside `OuterLogupExt3Verifier.verifyPrevalidated`
  344-346 FIRST, then claims/indices 348-349, folds 350-355, WHIR 357-376,
  gate terminal 378-391);
* mle/contracts/src/OuterLogupExt3Verifier.sol 150-153 (norm terminal
  compared with `logFinalClaim`), 211-228 (`verifyGateTerminal`), 254-287
  (`_verifyCoupledSumchecksUnchecked`, zero initial claims), 289-321 (round
  evaluation), 323-330 (`_evaluateTerminalUnchecked`).

Adopted Lean reused, never re-implemented: `Integrated.verify`/`modelEngine`/
`normResult`/`gateResult` (Integrated.lean 43-66), `Verifier.verify`/
`verify_success_checks`/`derivedRounds`/`derivedIndices`/`derivedContext`/
`gateTerminal`/`Engine.logTerminal` (Verifier.lean 362-425, 459-477),
`OuterClaimChain.honestRun`/`Lockstep`/`chain_initial_claim`/
`honest_step_exact`/`honest_log_chain_step`/`honest_run_is_derived_rounds`/
`gate_lane_chain_step`, `NormTerminalBinding.honest_prover_terminal`/
`last_round_target_is_bound_terminal`/`bind_tables_positive`/
`evaluate_with_exact`, `GateTerminalBinding.honest_last_round_is_engine_gate_terminal`/
`shape_gives_table_shape`, `GateSuffixPolynomial.captured_round_polynomial`,
`OpenedClaimFold.expected_claim_cell_is_full_table_evaluation`/
`sixth_cell_opens_nothing`.

What this module adds (all deterministic identities; no soundness claim):
1. `honest_log_terminal_matches_chain` (HONEST PROVER): the verifier's own
   `Engine.logTerminal` on the proof's used claims equals the last `logClaim`
   of `derivedRounds`, under the ONE hypothesis structure
   `NormChainHypotheses` (honest-prover fields, VK/configuration fields,
   provenance fields, all named and documented on the structure).
2. `honest_gate_terminal_matches_claim` (HONEST PROVER): the gate lane, under
   `GateChainHypotheses`, which carries OuterClaimChain's explicit
   grid-agreement hypothesis VISIBLY (field `grid`).
3. `honest_expected_claims_are_table_evaluations` (HONEST PROVER opening
   relation `HonestOpenings`): the five WHIR expected claims of the concrete
   engine's `derivedContext` are dense evaluations of the padded prover tables
   at the reversed packed points; the sixth cell is `none`.
4. `honest_prover_passes_deterministic_checks` (HONEST PROVER): (1)-(3) with
   the adopted `verify_success_checks` conjunct list give `Verifier.verify`
   and `Integrated.verify` acceptance, with EXACTLY the observation-only
   conjuncts enumerated in `ObservationOnly` (chain id, configuration hash,
   envelope, deployment validity, proof shape, transcript lengths, WHIR
   parse/tail acceptance, seven-challenge layout, norm `shapeValid`). The
   four-limb public-input hash length is the `hashLength` field of
   `GateChainHypotheses`.
5. `verify_order_swap`: the Rust order (WHIR before the norm terminal) and
   the Solidity/Lean order accept the same proofs, as a Prop-level `Iff` on
   the adopted conjunct list (`rustOrderChecks ↔ solidityOrderChecks`, and
   both `↔ Verifier.verify e pin chain c p = .ok ()` via the new converse
   `verify_of_checks`). Nothing about revert reasons, exception order or gas.
6. `Example`: every hypothesis structure is inhabited on the adopted
   `Integrated.exampleEngine`/`exampleConfig`/`exampleProof` with an honest
   NormDenseRound prover and an honest gate prover state whose lockstep run
   produces exactly that proof's round messages; (4) then re-derives the
   adopted `positive_integrated_norm_helper_path` through the glue.

Not proved here (explicit boundaries): that the honest endpoint sum is zero
(the norm/logUp cube relation, field `zeroSum`); provenance of the eq and
subgroup cells from `tau`/the VK powers (`eqCell`, `subgroupCell`, gate
`eqCell`); the gate prover's coefficient interpolation and multi-round
claim chain (field `grid`, exactly OuterClaimChain's gate-lane hypothesis);
that the opened cells are true PCS openings (`HonestOpenings.opened`);
transcript derivation of challenges (`challenges`, `alpha`); Rust/EVM
refinement; any statement about dishonest provers, sumcheck/PCS soundness or
Fiat--Shamir. Every theorem that quantifies over the honest prover's own
tables says "honest prover" in its docstring.
-/
namespace Audit.Wire3.IntegratedTerminalChain
open Audit.Wire3 GoldilocksExt3Field NormDenseRound NormTerminalBinding

/-! ## 1. The honest run binds the tables over the verifier's log challenges -/

/-- Honest prover only. A successful lockstep run over `gates` extends the
prover's point by exactly the verifier's log challenges `chals`, and the
final tables are `bindTablesMany chals` of the initial tables (each step is
the adopted `bindTables` at that step's challenge, `honest_step_exact`). -/
theorem honest_run_binds_tables (commit : Verifier.CommitRound) (gates : List (List Verifier.Ext3)) :
    ∀ (v : Verifier.RoundState) (s : ProverState) (v' : Verifier.RoundState) (s' : ProverState),
      OuterClaimChain.Lockstep v s → gates.length ≤ s.tables.remaining →
      OuterClaimChain.honestRun commit v s gates = .ok (v', s') →
      ∃ chals : List Element, s'.point = s.point ++ chals ∧ chals.length = gates.length ∧
        bindTablesMany chals s.tables = some s'.tables := by
  induction gates with
  | nil =>
      intro v s v' s' _ _ h
      simp only [OuterClaimChain.honestRun, Outcome.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], by simp, rfl, rfl⟩
  | cons g gs ih =>
      intro v s v' s' hl hlen h
      simp only [List.length_cons] at hlen
      have hn : ¬isComplete s := OuterClaimChain.incomplete_of_remaining s hl.consistent (by omega)
      obtain ⟨message, s₁, hstep, _, _, _, _, _, _, _, hpt₁, hrem₁, htab, _, hl₁⟩ :=
        OuterClaimChain.honest_step_exact commit g v s hl hn
      simp only [OuterClaimChain.honestRun, hstep] at h
      obtain ⟨chals, hpt, hcl, hb⟩ := ih _ s₁ v' s' hl₁ (by omega) h
      refine ⟨OuterClaimChain.logChallenge commit v message g :: chals, ?_, ?_, ?_⟩
      · rw [hpt, hpt₁, List.append_assoc]
        rfl
      · simp [hcl]
      · simp only [bindTablesMany, htab, bind, Option.bind]
        exact hb

/-! ## 2. The norm lane: hypothesis structure and the terminal identity -/

/-- The honest NormDenseRound prover as constructed by the source
(`new_with_public_inputs`, norm_logup.rs 644-680; `from_base` 425-444;
`PreparedChallenges::new` 288-297), plus the VK/configuration
correspondence NormTerminalBinding needs. HONEST-PROVER fields: `shape`,
`fresh`, `positive`, `bindings`, `rounds`, `zeroSum`. `zeroSum` is the
norm/logUp relation over the cube (the source's zero initial claim); it is
NOT proved anywhere in the audit (`OuterClaimChain.chain_initial_claim`
only characterises it). VK/CONFIGURATION fields: `compatible` (routed
count, constant offset, `kIs`), `lambda` (lambda powers are `lambda^j`),
`wireMap` (the PI wire-map bytes decode to the bindings' rows/columns). -/
structure HonestNormProver (c : Verifier.Config) (t : Tables) (pr : Prepared)
    (gates : List (List Verifier.Ext3)) (constants : List Verifier.Ext3)
    (pairs : List (Nat × Nat × Verifier.Base)) : Prop where
  shape : Shape t pr
  fresh : t.boundVariables = 0
  positive : 0 < t.remaining
  bindings : t.bindings = buildBindings (NormPolynomial.lift pr.challenges.eta) 1 pairs
  rounds : gates.length = t.remaining
  zeroSum : OuterClaimChain.endpointSum t pr = Verifier.zero
  compatible : Compatible c t pr constants
  lambda : LambdaProvenance pr
  wireMap : WireMapMatches c.publicInputWireMap t.bindings

/-- PROVENANCE fields relating the verifier's view of the proof to the honest
prover's fully bound tables `tEnd` at the verifier's log challenges `chals`:
`eqCell`/`subgroupCell` (the bound eq and subgroup cells ARE
`Norm.eqEvaluation tau point` / `Norm.subgroupEvaluation powers point`;
`eq_evals_ext3(tau)` and the VK subgroup table are not modelled by the
adopted audit), `challenges` (the transcript's seven log challenges and
`tau` are the prover's), `logRounds`/`gateRounds` (the proof carries the
honest messages and the externally supplied gate messages), `claims` (the
proof's `logPreprocessed`/`logWitness`/`logNormInverse`/`publicInputs` are
the fully bound cells `toTerminalInput tEnd constants extra`, i.e. the
packed folds of the prover columns by
`NormTerminalBinding.fully_bound_cells_are_packed_folds`). -/
structure NormTerminalProvenance (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (pr : Prepared) (gates : List (List Verifier.Ext3)) (constants extra : List Verifier.Ext3)
    (tEnd : Tables) (sent : List (List Element)) (chals : List Element) : Prop where
  eqCell : (cell tEnd.eq).toVerifier = Norm.eqEvaluation pr.challenges.tau (chals.map Element.toVerifier)
  subgroupCell : (cell tEnd.subgroup).toVerifier =
    Norm.subgroupEvaluation c.subgroupPowers (chals.map Element.toVerifier)
  challenges : Norm.challengesFromInitial (e.initialTranscript c p) = pr.challenges
  logRounds : p.logRounds = sent.map (List.map Element.toVerifier)
  gateRounds : p.gateRounds = gates
  claims : Verifier.normTerminalInput p = toTerminalInput tEnd constants extra

/-- The ONE named hypothesis set of `honest_log_terminal_matches_chain`:
the honest-prover/VK half `HonestNormProver` and the provenance half
`NormTerminalProvenance`, stated at the final tables `tEnd`, the extracted
messages `sent` and the extracted point `chals` of the run. -/
structure NormChainHypotheses (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (t : Tables) (pr : Prepared) (gates : List (List Verifier.Ext3))
    (constants extra : List Verifier.Ext3) (pairs : List (Nat × Nat × Verifier.Base))
    (tEnd : Tables) (sent : List (List Element)) (chals : List Element)
    extends HonestNormProver c t pr gates constants pairs,
      NormTerminalProvenance e c p pr gates constants extra tEnd sent chals : Prop

/-- Honest prover only. The honest lockstep run from the source's fresh
state exists (`OuterClaimChain.honest_run_is_derived_rounds`): it succeeds,
`into_proof_and_point` returns the sent messages and the verifier's log
point. Only the honest-prover fields are needed. -/
theorem honest_norm_run_exists (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (t : Tables) (pr : Prepared) (gates : List (List Verifier.Ext3)) (constants : List Verifier.Ext3)
    (pairs : List (Nat × Nat × Verifier.Base)) (hyp : HonestNormProver c t pr gates constants pairs) :
    ∃ (v' : Verifier.RoundState) (s' : ProverState) (sent : List (List Element)) (chals : List Element),
      OuterClaimChain.honestRun e.commitRound (Verifier.start (e.initialTranscript c p))
        (initialState t pr) gates = .ok (v', s') ∧
      intoProofAndPoint s' = .ok (sent, chals) ∧ v'.logPoint = chals.map Element.toVerifier := by
  obtain ⟨v', s', sent, chals, hrun, hext, hlp, _⟩ :=
    OuterClaimChain.honest_run_is_derived_rounds e c p t pr gates hyp.shape hyp.fresh hyp.zeroSum hyp.rounds
  exact ⟨v', s', sent, chals, hrun, hext, hlp⟩

/-- (1) HONEST PROVER ONLY. For the honest norm prover driven by the
verifier's own log challenges (`OuterClaimChain.honestRun`), whose run
succeeded with `(v', s')` and extracted `(sent, chals)`, under
`NormChainHypotheses` at the final tables `s'.tables`:
`Verifier.derivedRounds e c p` is the lockstep verifier state, its log point
is `chals`, the final tables are `bindTablesMany chals t` and fully bound,
the prover's terminal target on them is the final `logClaim`
(`last_round_target_is_bound_terminal` on the last lockstep step), that
claim is `Norm.evaluate` on the assembled input, and therefore the concrete
engine's `Engine.logTerminal` (Verifier.lean 362-363 under
`Integrated.modelEngine`, i.e. `Norm.normEvaluation`) on the proof's used
claims at `derivedRounds.logPoint` equals `derivedRounds.logClaim`: the
norm-terminal conjunct of `Verifier.verify` (line 422). -/
theorem honest_log_terminal_matches_chain (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (t : Tables) (pr : Prepared)
    (gates : List (List Verifier.Ext3)) (constants extra : List Verifier.Ext3)
    (pairs : List (Nat × Nat × Verifier.Base)) (v' : Verifier.RoundState) (s' : ProverState)
    (sent : List (List Element)) (chals : List Element)
    (hrun : OuterClaimChain.honestRun e.commitRound (Verifier.start (e.initialTranscript c p))
      (initialState t pr) gates = .ok (v', s'))
    (hext : intoProofAndPoint s' = .ok (sent, chals))
    (hyp : NormChainHypotheses e c p t pr gates constants extra pairs s'.tables sent chals) :
    Verifier.derivedRounds e c p = v' ∧ v'.logPoint = chals.map Element.toVerifier ∧
    bindTablesMany chals t = some s'.tables ∧ FullyBound s'.tables ∧
    terminalTarget s'.tables pr = some v'.logClaim ∧
    v'.logClaim = Norm.evaluate c pr.challenges (toTerminalInput s'.tables constants extra)
      (chals.map Element.toVerifier) ∧
    (Integrated.modelEngine e decode).logTerminal c (e.initialTranscript c p) p
        (Verifier.derivedRounds e c p).logPoint = (Verifier.derivedRounds e c p).logClaim := by
  have hl : OuterClaimChain.Lockstep (Verifier.start (e.initialTranscript c p)) (initialState t pr) :=
    (OuterClaimChain.chain_initial_claim t pr _ hyp.shape hyp.fresh hyp.positive).mpr hyp.zeroSum
  -- the run is the derived verifier state and the extraction is what it consumed
  obtain ⟨v'', s'', sent'', chals'', hrun'', hext'', hlp'', hder''⟩ :=
    OuterClaimChain.honest_run_is_derived_rounds e c p t pr gates hyp.shape hyp.fresh hyp.zeroSum hyp.rounds
  rw [hrun] at hrun''
  simp only [Outcome.ok.injEq, Prod.mk.injEq] at hrun''
  obtain ⟨rfl, rfl⟩ := hrun''
  rw [hext] at hext''
  simp only [Outcome.ok.injEq, Prod.mk.injEq] at hext''
  obtain ⟨rfl, rfl⟩ := hext''
  have hder : Verifier.derivedRounds e c p = v' := hder'' hyp.logRounds hyp.gateRounds
  -- the tables after the run are the iterated binds at the extracted point
  obtain ⟨chals', hpt', hcl', hbind'⟩ :=
    honest_run_binds_tables e.commitRound gates _ _ v' s' hl
      (by have h := hyp.rounds; show gates.length ≤ t.remaining; omega) hrun
  -- the last lockstep step
  obtain ⟨pre, g, hsplit⟩ : ∃ pre g, gates = pre ++ [g] := by
    rcases List.eq_nil_or_concat gates with h | ⟨pre, g, h⟩
    · exfalso
      have hr := hyp.rounds
      rw [h] at hr
      simp only [List.length_nil] at hr
      have := hyp.positive
      omega
    · exact ⟨pre, g, by rw [h, List.concat_eq_append]⟩
  have hlen : pre.length + 1 = t.remaining := by
    have hr := hyp.rounds
    rw [hsplit] at hr
    simpa only [List.length_append, List.length_cons, List.length_nil] using hr
  have hn : (pre ++ g :: []).length ≤ (initialState t pr).tables.remaining := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    show _ ≤ t.remaining
    omega
  obtain ⟨vᵢ, sᵢ, message, sNext, _, hlock, hprep, _, hremᵢ, _, hrun', _, _, hclaim, htab, _, _,
    hcons, hrem'⟩ := OuterClaimChain.honest_log_chain_step e.commitRound _ _ hl pre g [] hn
  have hrun0 := hrun
  rw [hsplit, hrun'] at hrun0
  simp only [Outcome.ok.injEq, Prod.mk.injEq] at hrun0
  obtain ⟨hv', hs'⟩ := hrun0
  subst hs'
  have hrem1 : sᵢ.tables.remaining = 1 := by
    have h1 : sᵢ.tables.remaining + pre.length = t.remaining := hremᵢ
    omega
  have hshapeᵢ : Shape sᵢ.tables pr := by
    have h := hlock.consistent.2.2.2
    rw [hprep] at h
    exact h
  -- the final tables are the last tables bound at the last challenge
  have hboundEq : sNext.tables =
      NormTerminalBinding.boundTables sᵢ.tables (OuterClaimChain.logChallenge e.commitRound vᵢ message g) := by
    have h := NormTerminalBinding.bind_tables_positive sᵢ.tables
      (OuterClaimChain.logChallenge e.commitRound vᵢ message g) (by omega)
    rw [htab] at h
    exact Option.some.inj h
  have hterm0 := (NormTerminalBinding.last_round_target_is_bound_terminal sᵢ.tables pr
    (OuterClaimChain.logChallenge e.commitRound vᵢ message g) hshapeᵢ hrem1).2
  rw [← hboundEq] at hterm0
  have hclaim' : v'.logClaim =
      roundValue sᵢ.tables pr (OuterClaimChain.logChallenge e.commitRound vᵢ message g) := by
    rw [← hv']
    exact hclaim
  have hlast : terminalTarget sNext.tables pr = some v'.logClaim := by
    rw [hclaim']
    exact hterm0
  -- the extracted point is the verifier's challenge list
  have hcomplete : isComplete sNext := by
    have h1 := hcons.1
    have h2 := hcons.2.1
    unfold isComplete
    omega
  have hext' := proof_extraction_exact sNext hcomplete
  rw [hext] at hext'
  simp only [Outcome.ok.injEq, Prod.mk.injEq] at hext'
  obtain ⟨_, hchals⟩ := hext'
  have hchals' : chals = chals' := by
    rw [hchals, hpt']
    rfl
  subst hchals'
  have hbind : bindTablesMany chals t = some sNext.tables := hbind'
  have hchalsLen : chals.length = t.remaining := by rw [hcl', hyp.rounds]
  -- the fully bound target is the verifier's formula on the cells
  obtain ⟨t'', hb'', hfull, _, hterm⟩ :=
    NormTerminalBinding.honest_prover_terminal t pr c constants extra chals pairs hyp.shape hyp.fresh
      hchalsLen hyp.bindings hyp.compatible hyp.lambda hyp.wireMap
  have ht'' : t'' = sNext.tables := by
    have h := hbind
    rw [hb''] at h
    exact Option.some.inj h
  subst ht''
  have hval : v'.logClaim = Norm.evaluate c pr.challenges (toTerminalInput sNext.tables constants extra)
      (chals.map Element.toVerifier) := by
    rw [NormTerminalBinding.evaluate_with_exact, ← hyp.eqCell, ← hyp.subgroupCell]
    have h := hlast
    rw [hterm] at h
    exact (Option.some.inj h).symm
  refine ⟨hder, hlp'', hbind, hfull, hlast, hval, ?_⟩
  show Norm.evaluate c (Norm.challengesFromInitial (e.initialTranscript c p)) (Verifier.normTerminalInput p)
    (Verifier.derivedRounds e c p).logPoint = (Verifier.derivedRounds e c p).logClaim
  rw [hyp.challenges, hyp.claims, hder, hlp'']
  exact hval.symm

/-! ## 3. The gate lane -/

/-- The verifier state after the coupled rounds `pre` (verifier_v2.rs
281-301 / OuterLogupExt3Verifier.sol 274-284 up to the last round). -/
def lastState (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (pre : List Verifier.CoupledMessage) : Verifier.RoundState :=
  Verifier.runRounds e.commitRound (Verifier.start (e.initialTranscript c p)) pre

/-- The verifier's gate challenge of the last coupled round. -/
def lastGateChallenge (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (pre : List Verifier.CoupledMessage) (mLog gLast : List Verifier.Ext3) : Verifier.Ext3 :=
  (e.commitRound (lastState e c p pre).transcript (lastState e c p pre).roundIndex mLog gLast).gate

/-- `derivedRounds` with the last coupled round split off (`runRounds_append`). -/
theorem derived_rounds_last_step (e : Verifier.Engine) (c : Verifier.Config) (p : Verifier.Proof)
    (pre : List Verifier.CoupledMessage) (mLog gLast : List Verifier.Ext3)
    (h : p.logRounds.zip p.gateRounds = pre ++ [(mLog, gLast)]) :
    Verifier.derivedRounds e c p = Verifier.roundStep e.commitRound (lastState e c p pre) (mLog, gLast) ∧
    (Verifier.derivedRounds e c p).gatePoint =
      (lastState e c p pre).gatePoint ++ [lastGateChallenge e c p pre mLog gLast] := by
  have h1 : Verifier.derivedRounds e c p =
      Verifier.roundStep e.commitRound (lastState e c p pre) (mLog, gLast) := by
    rw [Verifier.derivedRounds, h, Verifier.runRounds_append]
    rfl
  exact ⟨h1, by rw [h1]; rfl⟩

/-- Hypotheses of the gate lane. HONEST-PROVER fields: `shape` (the gate
prover state with one variable left, gate_ext3_v2.rs 70-79), `bind` (it
binds the verifier's last gate challenge), `cells`, and `grid`. `grid` is
OuterClaimChain's explicit gate-lane hypothesis carried visibly: the
verifier's reconstruction of the last gate message from ITS running gate
claim (`Verifier.evaluateRound`, i.e. `evaluate_ext3_coefficient_round` /
`_evaluateExt3RoundDynamic`) agrees with the honest prover's last-round
value at the `quotientDegree+3` integer grid nodes
(`GateSlotRound.gridPoint`, the grid `current_round` samples). Because the
verifier's reconstruction recovers the constant coefficient from its running
claim, this agreement also entails that the running gate claim equals the
honest endpoint sum f(0)+f(1), i.e. honesty of the whole gate chain. No gate
prover with coefficient interpolation and `bind_challenge` chaining is
adopted, so this is NOT derived; the running claim of the earlier rounds
enters only through it. VK/CONFIGURATION fields: `split` (the proof has
`pre.length+1` coupled rounds), `decode`, `rows`, `valid`, `messageLength`
(`shape` gives `= quotientDegree+2`). OBSERVATION/PROVENANCE fields:
`hashLength` (the four-limb `publicInputsHash`), `claims`
(`GateTerminalBinding.CellsMatchClaims`: the bound wire/constant cells are the
proof's `gateWitness` / `gatePreprocessed.take numConstants`),
`alphaMatches`, and `eqCell` (the bound eq cell is `eq(gateTau, gatePoint)`; `ext3_eq_evals(tau)`
is not modelled). -/
structure GateChainHypotheses (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (pre : List Verifier.CoupledMessage)
    (mLog gLast : List Verifier.Ext3) (gates : List Gates.GateInfo)
    (s t : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells) (alpha : Element) : Prop where
  split : p.logRounds.zip p.gateRounds = pre ++ [(mLog, gLast)]
  shape : GateTerminalBinding.ProverShape (Integrated.gateConfig c) 1 s
  bind : GateTerminalBinding.bindChallenge s gLast
    (OuterRound.lift (lastGateChallenge e c p pre mLog gLast)) = some t
  cells : t.tables = k.tables
  decode : decode c.gatesEncoding = some gates
  rows : gates.length = c.gateRows
  valid : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ()
  hashLength : (e.publicInputsHash p.publicInputs).length = 4
  claims : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p)
  alphaMatches : alpha.toVerifier = (e.initialTranscript c p).gateAlpha
  eqCell : k.eq.toVerifier =
    Norm.eqEvaluation (e.initialTranscript c p).gateTau (Verifier.derivedRounds e c p).gatePoint
  messageLength : gLast.length ≤ c.quotientDegree + 2
  grid : ∀ i, i ≤ c.quotientDegree + 2 →
    GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs)) alpha
        (GateSlotRound.gridPoint i) s.tables 1 =
      some (Verifier.evaluateRound (lastState e c p pre).gateClaim gLast (Norm.embed i))

/-- (2) HONEST PROVER ONLY. Under `GateChainHypotheses`: `gateResult`
executes, the concrete engine's `Verifier.gateTerminal` is `eq_cell * gate`
(`GateTerminalBinding.honest_last_round_is_engine_gate_terminal`), the
honest last-round polynomial (`captured_round_polynomial`, degree
`≤ quotientDegree+2`) agrees with the verifier's reconstruction on the grid,
hence (`OuterClaimChain.gate_lane_chain_step`, interpolation uniqueness)
at the verifier's last gate challenge; so the honest last-round value at that
challenge is the derived `gateClaim`, and the gate-terminal conjunct of
`Verifier.verify` (line 424) holds. -/
theorem honest_gate_terminal_matches_claim (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (pre : List Verifier.CoupledMessage)
    (mLog gLast : List Verifier.Ext3) (gates : List Gates.GateInfo)
    (s t : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells) (alpha : Element)
    (hyp : GateChainHypotheses e decode c p pre mLog gLast gates s t k alpha) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p = Verifier.mul k.eq.toVerifier gate ∧
      GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
          (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs)) alpha
          (OuterRound.lift (lastGateChallenge e c p pre mLog gLast)) s.tables 1 =
        some (Verifier.derivedRounds e c p).gateClaim ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p = (Verifier.derivedRounds e c p).gateClaim := by
  obtain ⟨hder, _⟩ := derived_rounds_last_step e c p pre mLog gLast hyp.split
  have ht : GateSuffixPolynomial.TableShape (Integrated.gateConfig c) 1 s.tables := by
    simpa using GateTerminalBinding.shape_gives_table_shape _ 1 s hyp.shape Nat.one_pos
  obtain ⟨f, _, hdeg, hval⟩ := GateSuffixPolynomial.captured_round_polynomial (Integrated.gateConfig c) gates
    (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs)) alpha s.tables 1 hyp.valid ht
  have henv := (Gates.validate_configuration_success _ _ hyp.valid).1
  have h8 : c.quotientDegree ≤ 8 := henv.2.2.2.2.2.2.2.2.2
  have hd : c.quotientDegree + 2 < Arithmetic.modulus := by
    have h10 : (10 : Nat) < Arithmetic.modulus := by decide
    omega
  have hgrid : ∀ i ≤ c.quotientDegree + 2,
      Verifier.evaluateRound (lastState e c p pre).gateClaim gLast (Norm.embed i) =
        (f.eval (i : Element)).toVerifier := by
    intro i hi
    have h := hyp.grid i hi
    rw [hval (GateSlotRound.gridPoint i)] at h
    exact (Option.some.inj h).symm
  have hclaim : (Verifier.derivedRounds e c p).gateClaim =
      (f.eval (OuterRound.lift (lastGateChallenge e c p pre mLog gLast))).toVerifier := by
    rw [hder]
    exact OuterClaimChain.gate_lane_chain_step e.commitRound (lastState e c p pre) (mLog, gLast) f
      (c.quotientDegree + 2) hd hdeg hyp.messageLength hgrid
  obtain ⟨gate, hres, hround, hengine⟩ :=
    GateTerminalBinding.honest_last_round_is_engine_gate_terminal e decode c p gates s t gLast
      (OuterRound.lift (lastGateChallenge e c p pre mLog gLast)) k alpha hyp.shape hyp.valid hyp.bind
      hyp.cells hyp.decode hyp.rows hyp.hashLength hyp.claims hyp.alphaMatches hyp.eqCell
  have hfx : (f.eval (OuterRound.lift (lastGateChallenge e c p pre mLog gLast))).toVerifier =
      Verifier.mul k.eq.toVerifier gate := by
    have h := hround
    rw [hval] at h
    exact Option.some.inj h
  refine ⟨gate, hres, hengine, ?_, ?_⟩
  · rw [hround, hclaim, hfx]
  · rw [hengine, hclaim, hfx]

/-! ## 4. The WHIR expected claims -/

/-- The HONEST-PROVER opening relation of OpenedClaimFold, for all five bound
cells at once: for cell `i`, `cols i` are the committed constituent columns
of that group (full tables for the row point), the group fits the index
capacity, and the proof's opened cells are the per-column row folds
(`rowOpenings`). Nothing says these are true PCS openings. -/
structure HonestOpenings (c : Verifier.Config) (p : Verifier.Proof) (s : Verifier.RoundState)
    (idx : Verifier.IndexPoints) (cols : Fin 5 → List (List Element)) : Prop where
  full : ∀ i : Fin 5, ∀ col ∈ cols i, col.length = 2 ^ (OpenedClaimFold.cellRow s i).length
  capacity : ∀ i : Fin 5, (cols i).length ≤ 2 ^ (OpenedClaimFold.boundCell p.used idx i).2.length
  opened : ∀ i : Fin 5, (OpenedClaimFold.boundCell p.used idx i).1.map Subtype.val =
    OpenedClaimFold.rowOpenings (cols i) (OpenedClaimFold.lift (OpenedClaimFold.cellRow s i))

/-- The concrete engine's context is `whirContext` with the executable
`Connections.packedFold` at the abstract engine's rounds and indices
(Integrated.lean 45; `modelEngine` keeps `commitRound`/`sampleIndices`). -/
theorem concrete_engine_context (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.derivedContext (Integrated.modelEngine e decode) c p =
      Verifier.whirContext Connections.packedFold c p (Verifier.derivedRounds e c p)
        (Verifier.derivedIndices e c p) := rfl

/-- (3) HONEST PROVER ONLY (opening relation). Under `HonestOpenings` at the
derived rounds and indices, each of the five bound expected claims of the
concrete engine's `derivedContext` is the dense evaluation of the padded
prover table at the packed point `row ++ index`, whose complete reversal is
the context's native WHIR point (`CellOpensFullTable`); the sixth cell is
`none` and the mask is the protocol constant. -/
theorem honest_expected_claims_are_table_evaluations (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (cols : Fin 5 → List (List Element))
    (hyp : HonestOpenings c p (Verifier.derivedRounds e c p) (Verifier.derivedIndices e c p) cols) :
    (∀ i : Fin 5, OpenedClaimFold.CellOpensFullTable
      (Verifier.derivedContext (Integrated.modelEngine e decode) c p) i.val (OpenedClaimFold.cellPoint i)
      (cols i) (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2)) ∧
    (Verifier.derivedContext (Integrated.modelEngine e decode) c p).expectedClaims[5]? = some none ∧
    (Verifier.derivedContext (Integrated.modelEngine e decode) c p).expectedClaims.map Option.isSome =
      [true, true, true, true, true, false] := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [concrete_engine_context]
    exact OpenedClaimFold.expected_claim_cell_is_full_table_evaluation c p _ _ i (cols i)
      (hyp.full i) (hyp.capacity i) (hyp.opened i)
  · exact (OpenedClaimFold.sixth_cell_opens_nothing Connections.packedFold c p
      (Verifier.derivedIndices e c p)).2.1
  · exact Verifier.context_bound_mask_exact _ _ _ _

/-- A bound entry of `claimsMatch` is carried to the parsed claim list. -/
theorem claims_match_bound_entry {xs : List (Option Verifier.Ext3)} {ys : List Verifier.Ext3}
    (h : Verifier.claimsMatch xs ys = true) :
    ∀ (i : Nat) (x : Verifier.Ext3), xs[i]? = some (some x) → ys[i]? = some x := by
  induction xs generalizing ys with
  | nil => intro i x hx; simp at hx
  | cons a xs ih =>
      cases ys with
      | nil => cases a <;> simp [Verifier.claimsMatch] at h
      | cons y ys =>
          intro i x hx
          cases a with
          | none =>
              cases i with
              | zero => simp at hx
              | succ i =>
                  simp only [List.getElem?_cons_succ] at hx ⊢
                  exact ih h i x hx
          | some a =>
              simp only [Verifier.claimsMatch, Bool.and_eq_true, decide_eq_true_eq] at h
              cases i with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hx ⊢
                  exact h.1.symm.trans hx
              | succ i =>
                  simp only [List.getElem?_cons_succ] at hx ⊢
                  exact ih h.2 i x hx

/-- HONEST PROVER ONLY (opening relation). Whatever `whirTail` verifies when
the concrete engine's WHIR check accepts, the five bound claims it was
handed are exactly the dense evaluations of the padded prover tables
(`claimsMatch` forces the parsed claims to equal the expected claims). -/
theorem accepted_whir_claims_are_table_evaluations (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (cols : Fin 5 → List (List Element))
    (hyp : HonestOpenings c p (Verifier.derivedRounds e c p) (Verifier.derivedIndices e c p) cols)
    (hw : Verifier.verifyWhir (Integrated.modelEngine e decode)
      (Verifier.derivedContext (Integrated.modelEngine e decode) c p) p = true) :
    ∃ parsed, (Integrated.modelEngine e decode).parseWhir
        (Verifier.derivedContext (Integrated.modelEngine e decode) c p) p.whirTranscript p.whirHints =
        some parsed ∧
      ∀ i : Fin 5, ∃ result,
        DenseMleIndexed.evaluate
          (OpenedClaimFold.paddedTable (cols i)
            (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i)).length
            (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2).length)
          (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i) ++
            OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2) =
          some result ∧
        parsed.claims[i.val]? = some result.toVerifier := by
  obtain ⟨parsed, hp, _, _, hc, _⟩ := Verifier.whir_acceptance_requires_bound_statement _ _ _ hw
  refine ⟨parsed, hp, fun i => ?_⟩
  obtain ⟨result, _, he, hcell⟩ := (honest_expected_claims_are_table_evaluations e decode c p cols hyp).1 i
  exact ⟨result, he, claims_match_bound_entry hc i.val _ hcell⟩

/-! ## 5. The adopted conjunct list, its converse, and the order swap -/

/-- The conjunct list of the adopted `Verifier.verify_success_checks`
(Verifier.lean 459-470), in the Solidity/Lean check order: norm terminal,
WHIR, gate terminal. -/
def solidityOrderChecks (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) : Prop :=
  chain = pin.chainId ∧ e.configurationHash c = pin.configDigest ∧ Verifier.envelope c = true ∧
  e.deploymentValid c = true ∧ Verifier.shape pin c p = true ∧
  (e.initialTranscript c p).logTau.length = c.degreeBits ∧
  (e.initialTranscript c p).gateTau.length = c.degreeBits ∧
  (Verifier.derivedIndices e c p).log.length = c.indexBits ∧
  (Verifier.derivedIndices e c p).gate.length = c.indexBits ∧
  e.logTerminal c (e.initialTranscript c p) p (Verifier.derivedRounds e c p).logPoint =
    (Verifier.derivedRounds e c p).logClaim ∧
  Verifier.verifyWhir e (Verifier.derivedContext e c p) p = true ∧
  Verifier.gateTerminal e c p = (Verifier.derivedRounds e c p).gateClaim

/-- The same conjuncts in the Rust order (verifier_v2.rs 386-395 verifies
WHIR before the norm terminal at 417): WHIR, norm terminal, gate terminal. -/
def rustOrderChecks (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) : Prop :=
  chain = pin.chainId ∧ e.configurationHash c = pin.configDigest ∧ Verifier.envelope c = true ∧
  e.deploymentValid c = true ∧ Verifier.shape pin c p = true ∧
  (e.initialTranscript c p).logTau.length = c.degreeBits ∧
  (e.initialTranscript c p).gateTau.length = c.degreeBits ∧
  (Verifier.derivedIndices e c p).log.length = c.indexBits ∧
  (Verifier.derivedIndices e c p).gate.length = c.indexBits ∧
  Verifier.verifyWhir e (Verifier.derivedContext e c p) p = true ∧
  e.logTerminal c (e.initialTranscript c p) p (Verifier.derivedRounds e c p).logPoint =
    (Verifier.derivedRounds e c p).logClaim ∧
  Verifier.gateTerminal e c p = (Verifier.derivedRounds e c p).gateClaim

/-- Converse of the adopted `verify_success_checks`: the conjunct list is
sufficient for acceptance (every guard of `Verifier.verify` is a total,
side-effect-free predicate on the same inputs). -/
theorem verify_of_checks (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) (h : solidityOrderChecks e pin chain c p) :
    Verifier.verify e pin chain c p = .ok () := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  simp [Verifier.verify, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- Acceptance is exactly the adopted conjunct list. -/
theorem verify_iff_solidity_order (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.verify e pin chain c p = .ok () ↔ solidityOrderChecks e pin chain c p :=
  ⟨Verifier.verify_success_checks e pin chain c p, verify_of_checks e pin chain c p⟩

/-- (5) The Rust order (WHIR before the norm terminal, verifier_v2.rs
386-420) and the Solidity/Lean order (norm terminal inside
`verifyPrevalidated` before WHIR, MleVerifierV2.sol 344-376) accept the same
proofs: both are conjunctions of the same side-effect-free predicates, so the
check order is a permutation of `∧`. Stated on the adopted conjunct list;
nothing about revert reasons, exception classification or gas. -/
theorem verify_order_swap (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) :
    rustOrderChecks e pin chain c p ↔ solidityOrderChecks e pin chain c p := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hw, hl, hg⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hl, hw, hg⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hl, hw, hg⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hw, hl, hg⟩

/-- The Rust-order conjunct list is acceptance by the adopted `Verifier.verify`. -/
theorem rust_order_accepts_iff (e : Verifier.Engine) (pin : Verifier.Pinned) (chain : Nat)
    (c : Verifier.Config) (p : Verifier.Proof) :
    rustOrderChecks e pin chain c p ↔ Verifier.verify e pin chain c p = .ok () :=
  (verify_order_swap e pin chain c p).trans (verify_iff_solidity_order e pin chain c p).symm

/-! ## 6. The honest prover against `Integrated.verify` -/

/-- EXACTLY the remaining observation-only conjuncts of `Integrated.verify`
for the honest prover: chain id, configuration hash, envelope, deployment
validity (Verifier.lean 412-414; Rust call-time, Solidity constructor +
hash), proof shape (415), the four transcript/index lengths (420-421), WHIR
parse/root/tail acceptance (423; `parseWhir` and `whirTail` are Engine
observations), and Integrated's norm preflight (Integrated.lean 55-57,
62-63): the seven-value challenge layout and `Norm.shapeValid` (mostly
shape/envelope facts, plus the VK obligation that every PI wire-map target
is a routed column with an in-range row). None of these is a terminal or
claim identity; none is hidden. -/
structure ObservationOnly (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof) : Prop where
  chain : chain = pin.chainId
  configurationHash : e.configurationHash c = pin.configDigest
  envelope : Verifier.envelope c = true
  deployment : e.deploymentValid c = true
  shape : Verifier.shape pin c p = true
  logTau : (e.initialTranscript c p).logTau.length = c.degreeBits
  gateTau : (e.initialTranscript c p).gateTau.length = c.degreeBits
  logIndex : (Verifier.derivedIndices e c p).log.length = c.indexBits
  gateIndex : (Verifier.derivedIndices e c p).gate.length = c.indexBits
  whir : Verifier.verifyWhir (Integrated.modelEngine e decode)
    (Verifier.derivedContext (Integrated.modelEngine e decode) c p) p = true
  sevenChallenges : (e.initialTranscript c p).logChallenges.length = 7
  normShape : Norm.shapeValid c (Norm.challengesFromInitial (e.initialTranscript c p))
    (Verifier.normTerminalInput p) (Verifier.derivedRounds e c p).logPoint = true

/-- (4) HONEST PROVER ONLY. Combining (1), (2), (3) with the adopted
`verify_success_checks` list: for the honest norm prover (run `hrun`/`hext`
under `NormChainHypotheses`), the honest gate prover (`GateChainHypotheses`)
and the honest openings (`HonestOpenings`), Integrated's two preflights
execute, every terminal/claim conjunct holds (norm terminal, gate terminal,
and the five WHIR expected claims are the padded-table evaluations), and with
the observation-only conjuncts `ObservationOnly` as the ONLY remaining
hypotheses the concrete `Verifier.verify` and `Integrated.verify` accept.
No converse: nothing says an accepted proof came from such a prover. -/
theorem honest_prover_passes_deterministic_checks (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (t : Tables) (pr : Prepared) (gates : List (List Verifier.Ext3)) (constants extra : List Verifier.Ext3)
    (pairs : List (Nat × Nat × Verifier.Base)) (v' : Verifier.RoundState) (s' : ProverState)
    (sent : List (List Element)) (chals : List Element)
    (hrun : OuterClaimChain.honestRun e.commitRound (Verifier.start (e.initialTranscript c p))
      (initialState t pr) gates = .ok (v', s'))
    (hext : intoProofAndPoint s' = .ok (sent, chals))
    (hn : NormChainHypotheses e c p t pr gates constants extra pairs s'.tables sent chals)
    (pre : List Verifier.CoupledMessage) (mLog gLast : List Verifier.Ext3) (gateInfos : List Gates.GateInfo)
    (gs gt : GateTerminalBinding.ProverState) (k : GateTerminalBinding.Cells) (alpha : Element)
    (hg : GateChainHypotheses e decode c p pre mLog gLast gateInfos gs gt k alpha)
    (cols : Fin 5 → List (List Element))
    (ho : HonestOpenings c p (Verifier.derivedRounds e c p) (Verifier.derivedIndices e c p) cols)
    (obs : ObservationOnly e decode pin chain c p) :
    (∃ norm, Integrated.normResult (Integrated.modelEngine e decode) c p = some norm) ∧
    (∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate) ∧
    (∀ i : Fin 5, OpenedClaimFold.CellOpensFullTable
      (Verifier.derivedContext (Integrated.modelEngine e decode) c p) i.val (OpenedClaimFold.cellPoint i)
      (cols i) (OpenedClaimFold.lift (OpenedClaimFold.cellRow (Verifier.derivedRounds e c p) i))
      (OpenedClaimFold.lift (OpenedClaimFold.boundCell p.used (Verifier.derivedIndices e c p) i).2)) ∧
    solidityOrderChecks (Integrated.modelEngine e decode) pin chain c p ∧
    Verifier.verify (Integrated.modelEngine e decode) pin chain c p = .ok () ∧
    Integrated.verify e decode pin chain c p = .ok () := by
  obtain ⟨_, _, _, _, _, _, hlog⟩ :=
    honest_log_terminal_matches_chain e decode c p t pr gates constants extra pairs v' s' sent chals hrun hext hn
  obtain ⟨gate, hgate, _, _, hgt⟩ :=
    honest_gate_terminal_matches_claim e decode c p pre mLog gLast gateInfos gs gt k alpha hg
  have hopen := (honest_expected_claims_are_table_evaluations e decode c p cols ho).1
  have hnorm : ∃ norm, Integrated.normResult (Integrated.modelEngine e decode) c p = some norm := by
    refine ⟨Norm.evaluate c (Norm.challengesFromInitial (e.initialTranscript c p)) (Verifier.normTerminalInput p)
      (Verifier.derivedRounds e c p).logPoint, ?_⟩
    show Norm.checkedNormEvaluation c (e.initialTranscript c p) (Verifier.normTerminalInput p)
      (Verifier.derivedRounds e c p).logPoint = some _
    rw [Norm.checkedNormEvaluation, if_pos obs.sevenChallenges, Norm.checkedEvaluate, if_pos obs.normShape]
  have hchecks : solidityOrderChecks (Integrated.modelEngine e decode) pin chain c p :=
    ⟨obs.chain, obs.configurationHash, obs.envelope, obs.deployment, obs.shape, obs.logTau, obs.gateTau,
      obs.logIndex, obs.gateIndex, hlog, obs.whir, hgt⟩
  have hverify := verify_of_checks _ pin chain c p hchecks
  refine ⟨hnorm, ⟨gate, hgate⟩, hopen, hchecks, hverify, ?_⟩
  obtain ⟨norm, hnorm'⟩ := hnorm
  simp only [Integrated.verify, hnorm', hgate]
  exact hverify

/-! ## 7. A concrete, non-vacuous instance on the adopted Integrated example -/

/-! Every hypothesis structure above is inhabited on
`Integrated.exampleEngine`/`exampleConfig`/`exampleProof` (Integrated.lean
188-205: one routed wire, `k = 1`, subgroup power 1, one variable, no public
inputs, all challenges zero except `beta = 1`, constant transcript). The
honest norm prover below is the source's fresh state for that circuit and
its lockstep run produces exactly the proof's single log message
`[0,0,0,0,0]` at the verifier's challenge `0`; the honest gate prover state
binds the gate challenge `0` into the proof's claimed cells. -/
namespace Example

def el (n : Nat) : Element := ⟨Norm.embed n⟩

def config : Verifier.Config := Integrated.exampleConfig
def proof : Verifier.Proof := Integrated.exampleProof
def engine : Verifier.Engine := Integrated.exampleEngine
def decoder : Integrated.DecodeGates := Integrated.exampleDecoder
def pin : Verifier.Pinned := ⟨1, Verifier.testRoot, Verifier.testRoot⟩
def initial : Verifier.Initial := engine.initialTranscript config proof

/-- `tau = [0]`: eq table `[1 - 0, 0]`; generator power 1: subgroup `[1, 1]`;
the routed wire, its sigma and both helper columns are constant. -/
def tables : Tables :=
  { eq := [el 1, el 0], subgroup := [el 1, el 1],
    wires := [[el 0, el 0]], sigmas := [[el 0, el 0]],
    identityHelpers := [[el 1, el 1]], sigmaHelpers := [[el 1, el 1]],
    bindings := buildBindings (el 0) 1 [],
    boundVariables := 0, remaining := 1 }

/-- The verifier's own seven challenges and `tau` (Integrated.lean 200). -/
def challenges : Norm.Challenges := Norm.challengesFromInitial initial

def prepared : Prepared :=
  ⟨challenges, [Verifier.base 1], runningPowers (NormPolynomial.lift challenges.lambda) 1 1⟩

def logMessage : List Verifier.Ext3 := List.replicate 5 Verifier.zero
def gateMessage : List Verifier.Ext3 := List.replicate 3 Verifier.zero
def gates : List (List Verifier.Ext3) := [gateMessage]
def constants : List Verifier.Ext3 := [Verifier.zero]
def message : List Element := [0, 0, 0, 0, 0]
def bound : Tables := NormTerminalBinding.boundTables tables 0

theorem tables_shape : Shape tables prepared := by
  unfold Shape ColumnShape
  decide

/-- The honest prover's cube sum on the example is zero (evaluated; in general
this is the unproved `zeroSum` hypothesis). -/
theorem zero_sum : OuterClaimChain.endpointSum tables prepared = Verifier.zero := by decide

/-- The honest first (and only) message: the interpolated tail of the
all-zero samples (kernel evaluation of the adopted Gaussian model). -/
theorem round_message : computeRound tables prepared = some message := by rfl

theorem compatible : Compatible config tables prepared constants := by
  unfold Compatible
  decide

theorem wire_map : WireMapMatches config.publicInputWireMap tables.bindings :=
  fun pair hp => absurd hp (List.not_mem_nil pair)

/-- The honest-prover/VK half of the norm hypotheses, inhabited. Honest prover only. -/
theorem honest_norm_prover : HonestNormProver config tables prepared gates constants [] :=
  { shape := tables_shape, fresh := rfl, positive := by decide, bindings := rfl, rounds := rfl,
    zeroSum := zero_sum, compatible := compatible,
    lambda := running_powers_lambda_provenance challenges [Verifier.base 1] 1, wireMap := wire_map }

/-- Honest prover only. The lockstep run on the example: one step, message
`[0,0,0,0,0]`, the verifier's log challenge `0`, final tables `bound`. -/
theorem run : ∃ (v' : Verifier.RoundState) (s' : ProverState),
    OuterClaimChain.honestRun engine.commitRound (Verifier.start initial) (initialState tables prepared) gates =
      .ok (v', s') ∧
    intoProofAndPoint s' = .ok ([message], [0]) ∧ s'.tables = bound := by
  have hl : OuterClaimChain.Lockstep (Verifier.start initial) (initialState tables prepared) :=
    (OuterClaimChain.chain_initial_claim tables prepared initial tables_shape rfl (by decide)).mpr zero_sum
  obtain ⟨vᵢ, sᵢ, msg, sNext, hrun0, _, _, _, _, _, hrun', hcr, _, _, htab, hpt, hcompl, hcons, hrem'⟩ :=
    OuterClaimChain.honest_log_chain_step engine.commitRound _ _ hl [] gateMessage [] (by decide)
  simp only [OuterClaimChain.honestRun, Outcome.ok.injEq, Prod.mk.injEq] at hrun0
  obtain ⟨rfl, rfl⟩ := hrun0
  have hmsg : msg = message := by
    have h : computeRound tables prepared = some msg := hcr
    rw [round_message] at h
    exact (Option.some.inj h).symm
  subst hmsg
  have hlc : OuterClaimChain.logChallenge engine.commitRound (Verifier.start initial) message gateMessage = 0 := rfl
  rw [hlc] at htab hpt
  have htables : sNext.tables = bound := by
    have h := NormTerminalBinding.bind_tables_positive tables 0 (by decide)
    have htab' : bindTables tables 0 = some sNext.tables := htab
    rw [htab'] at h
    exact Option.some.inj h
  have hcomplete : isComplete sNext := by
    have h1 := hcons.1
    have h2 := hcons.2.1
    have h3 : sNext.tables.remaining + 1 = 1 := hrem'
    unfold isComplete
    omega
  refine ⟨_, sNext, hrun', ?_, htables⟩
  rw [proof_extraction_exact sNext hcomplete, hcompl, hpt]
  rfl

theorem eq_cell : (cell bound.eq).toVerifier = Norm.eqEvaluation prepared.challenges.tau ([0].map Element.toVerifier) := by
  decide

theorem subgroup_cell :
    (cell bound.subgroup).toVerifier = Norm.subgroupEvaluation config.subgroupPowers ([0].map Element.toVerifier) := by
  decide

theorem log_rounds : proof.logRounds = [message].map (List.map Element.toVerifier) := by decide

/-- The proof's used log claims ARE the bound cells: `[constant, sigma]`,
`[wire]`, `[identity helper, sigma helper]`, no public inputs. -/
theorem claims : Verifier.normTerminalInput proof = toTerminalInput bound constants [] := by rfl

/-- The complete norm hypothesis set, inhabited at the run's final tables
`bound`, message list `[message]` and point `[0]`. Honest prover only. -/
theorem norm_hypotheses :
    NormChainHypotheses engine config proof tables prepared gates constants [] [] bound [message] [0] :=
  { honest_norm_prover with
    eqCell := eq_cell, subgroupCell := subgroup_cell, challenges := rfl,
    logRounds := log_rounds, gateRounds := rfl, claims := claims }

/-- (1) instantiated: the honest run of the example meets the norm-terminal
conjunct through the glue (the same fact the adopted positive path checks by
evaluation). Honest prover only. -/
theorem log_terminal_instance :
    (Integrated.modelEngine engine decoder).logTerminal config initial proof
        (Verifier.derivedRounds engine config proof).logPoint =
      (Verifier.derivedRounds engine config proof).logClaim := by
  obtain ⟨v', s', hrun, hext, htables⟩ := run
  have hyp : NormChainHypotheses engine config proof tables prepared gates constants [] [] s'.tables
      [message] [0] := by
    rw [htables]
    exact norm_hypotheses
  exact (honest_log_terminal_matches_chain engine decoder config proof tables prepared gates constants [] []
    v' s' [message] [0] hrun hext hyp).2.2.2.2.2.2

/-! ### The gate lane on the example -/

def gateInfo : Gates.GateInfo := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩

/-- One variable left: one wire pair, one constant pair, the eq pair
`[1 - 0, 0]` for `gateTau = [0]`, degree `quotientDegree + 2 = 3`. -/
def gateState : GateTerminalBinding.ProverState :=
  ⟨[⟨1, [0, 0]⟩], [⟨1, [0, 0]⟩], ⟨1, [1, 0]⟩, 3, [], []⟩

def gateBound : GateTerminalBinding.ProverState :=
  ⟨[⟨0, [0]⟩], [⟨0, [0]⟩], ⟨0, [1]⟩, 3, [gateMessage], [0]⟩

def gateCells : GateTerminalBinding.Cells := ⟨[0], [0], 1⟩

theorem gate_shape : GateTerminalBinding.ProverShape (Integrated.gateConfig config) 1 gateState := by decide

theorem gate_valid : Gates.validateConfiguration (Integrated.gateConfig config) [gateInfo] = some () := by
  decide

theorem gate_challenge : lastGateChallenge engine config proof [] logMessage gateMessage = Verifier.zero := rfl

theorem gate_bind : GateTerminalBinding.bindChallenge gateState gateMessage
    (OuterRound.lift (lastGateChallenge engine config proof [] logMessage gateMessage)) = some gateBound := by
  rw [gate_challenge]
  decide

theorem gate_cells : gateBound.tables = gateCells.tables := by decide

theorem gate_claims : GateTerminalBinding.CellsMatchClaims config gateCells (GateTerminalBinding.gateTerminalInput proof) := by
  unfold GateTerminalBinding.CellsMatchClaims GateTerminalBinding.claimedConstants
  decide

theorem gate_point : (Verifier.derivedRounds engine config proof).gatePoint = [Verifier.zero] := rfl

theorem gate_eq_cell : gateCells.eq.toVerifier =
    Norm.eqEvaluation initial.gateTau (Verifier.derivedRounds engine config proof).gatePoint := by
  rw [gate_point]
  decide

/-- The honest last-round value on every grid node (and at the challenge). -/
theorem gate_round_value (i : Nat) (hi : i ≤ 3) :
    GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig config) [gateInfo]
      (GateTerminalBinding.publicHashFunction (engine.publicInputsHash proof.publicInputs)) 0
      (GateSlotRound.gridPoint i) gateState.tables 1 = some Verifier.zero := by
  interval_cases i <;> decide

/-- The verifier's reconstruction of the all-zero message from the zero claim. -/
theorem gate_reconstruction (i : Nat) (hi : i ≤ 3) :
    Verifier.evaluateRound Verifier.zero gateMessage (Norm.embed i) = Verifier.zero := by
  interval_cases i <;> decide

/-- The complete gate hypothesis set, inhabited; the grid agreement holds
because both the honest last-round value and the verifier's reconstruction of
the all-zero message from the zero claim are zero at every node. Honest prover only. -/
theorem gate_hypotheses :
    GateChainHypotheses engine decoder config proof [] logMessage gateMessage [gateInfo] gateState gateBound
      gateCells 0 :=
  { split := rfl, shape := gate_shape, bind := gate_bind, cells := gate_cells, decode := rfl, rows := rfl,
    valid := gate_valid, hashLength := rfl, claims := gate_claims, alphaMatches := rfl, eqCell := gate_eq_cell,
    messageLength := by decide,
    grid := fun i hi => by
      have hi' : i ≤ 3 := hi
      rw [gate_round_value i hi']
      show some Verifier.zero = some (Verifier.evaluateRound Verifier.zero gateMessage (Norm.embed i))
      rw [gate_reconstruction i hi'] }

/-- (2) instantiated. Honest prover only. -/
theorem gate_terminal_instance :
    Verifier.gateTerminal (Integrated.modelEngine engine decoder) config proof =
      (Verifier.derivedRounds engine config proof).gateClaim :=
  (honest_gate_terminal_matches_claim engine decoder config proof [] logMessage gateMessage [gateInfo]
    gateState gateBound gateCells 0 gate_hypotheses).choose_spec.2.2.2

/-! ### The openings on the example -/

/-- The committed constituent columns (two rows each): log preprocessed
`[constant, sigma]`, log witness `[wire]`, log norm-inverse `[identity
helper, sigma helper]`, gate preprocessed, gate witness. -/
def cols : Fin 5 → List (List Element)
  | 0 => [[0, 0], [0, 0]]
  | 1 => [[0, 0]]
  | 2 => [[1, 1], [1, 1]]
  | 3 => [[0, 0], [0, 0]]
  | 4 => [[0, 0]]

/-- The honest opening relation, inhabited: the proof's used claims are the
row folds of `cols` at the row point `[0]`. Honest prover only. -/
theorem openings :
    HonestOpenings config proof (Verifier.derivedRounds engine config proof)
      (Verifier.derivedIndices engine config proof) cols :=
  { full := fun i => by fin_cases i <;> decide,
    capacity := fun i => by fin_cases i <;> decide,
    opened := fun i => by fin_cases i <;> decide }

/-! ### The observation-only conjuncts on the example -/

/-- The observation-only conjuncts, all evaluated on the example's stand-in
observations (Integrated.lean 185-187: not a cryptographic proof). -/
theorem observation : ObservationOnly engine decoder pin 1 config proof :=
  { chain := rfl, configurationHash := rfl, envelope := by decide, deployment := rfl, shape := by decide,
    logTau := rfl, gateTau := rfl, logIndex := rfl, gateIndex := rfl, whir := by decide,
    sevenChallenges := rfl, normShape := by decide }

/-- (4) instantiated: the honest example prover passes `Integrated.verify`
through the glue; this is the proposition of the adopted
`Integrated.positive_integrated_norm_helper_path`, now derived from the
hypothesis structures instead of by evaluation. Honest prover only. -/
theorem integrated_accepts : Integrated.verify engine decoder pin 1 config proof = .ok () := by
  obtain ⟨v', s', hrun, hext, htables⟩ := run
  have hyp : NormChainHypotheses engine config proof tables prepared gates constants [] [] s'.tables
      [message] [0] := by
    rw [htables]
    exact norm_hypotheses
  exact (honest_prover_passes_deterministic_checks engine decoder pin 1 config proof tables prepared gates
    constants [] [] v' s' [message] [0] hrun hext hyp [] logMessage gateMessage [gateInfo] gateState gateBound
    gateCells 0 gate_hypotheses cols openings observation).2.2.2.2.2

theorem agrees_with_adopted_positive_path :
    Integrated.verify engine decoder pin 1 config proof = .ok () ↔
      Integrated.verify Integrated.exampleEngine Integrated.exampleDecoder ⟨1, Verifier.testRoot, Verifier.testRoot⟩ 1
        Integrated.exampleConfig Integrated.exampleProof = .ok () :=
  Iff.rfl

end Example

end Audit.Wire3.IntegratedTerminalChain
