import Audit.Wire3.GateSlotRound
import Audit.Wire3.Integrated

/-!
Rust mle/src/sumcheck/gate_ext3_v2.rs:142-161 (`bind_challenge`: the
`non_constant.len() == degree` ensure (147-150), `bind_variable_in_place`
on the eq table (151), then on every wire table (152-154) and every constant
table (155-157) with the SAME challenge, then `rounds.push` (158) and
`point.push` (159)) and 163-170 (`into_proof_and_point`: the
`eq.num_vars == 0` ensure). The prover-state shape is the constructor's
ensures at 70-79 (`wires.len() == num_wires`, `constants.len() ==
num_constants`, every table `num_vars == tau.len()`); the separate
`degree == quotient_degree_factor + 2` ensure at 80-83 is not modelled here, and the eq table is
`Ext3DenseMle::new(ext3_eq_evals(tau))` (95) whose CONTENTS are not modelled
(GateSlotRound header: eq-table provenance from tau is outside the model).
Every per-table bind is the adopted `DenseMleIndexed.bindVariable`
(ext3.rs:47-58), so the fully bound single cells are the adopted
`DenseMleIndexed.evaluate` / packed fold of the original columns at the
pushed point.

Then the LAST round: when one Boolean variable is left (`half = 1`, one
suffix), the GateSlotRound iteration body at the grid point and the
GateSuffixPolynomial round value at ANY x are `eq_cell * evalCombined(cells)`
where the cells are the tables bound at x (`slot_slice_equals_complete`,
`grid_term_equals_suffix_slice` reused). This is compared with the verifier's
terminal expression `eq(tau, point) * gateEvaluation` of
MleVerifierV2.sol:378-391 (constants = `gatePreprocessed[0..numConstants]`,
`PoseidonPublicInputsHash.hashNoPad(publicInputs)`, `evalCombinedPrevalidated`,
`verifyGateTerminal`), OuterLogupExt3Verifier.sol:211-228 and
verifier_v2.rs:422-434, as modelled by `Verifier.gateTerminal`
(Verifier.lean:395-399) under `Integrated.modelEngine` (Integrated.lean:43-49).

The correspondence of the prover's bound cells to the claimed `gateWitness`
and `gatePreprocessed.take numConstants` is the explicit definition
`CellsMatchClaims`. That the bound eq cell equals
`Norm.eqEvaluation gateTau gatePoint` is NOT proved: it is the visible
hypothesis `heq` of every verifier-facing theorem. Theorems quantifying over
the prover's own tables are HONEST-PROVER statements: they say what an honest
prover's last-round value is, never that a verifier-accepted claim came from
such a prover. No WHIR/PCS, transcript or soundness claim is made; none of
the source's checks is added to or removed from the model.
-/
namespace Audit.Wire3.GateTerminalBinding
open Audit.Wire3 GoldilocksExt3Field Audit.Wire3.GateSuffixPolynomial Audit.Wire3.GateSlotRound
open Audit.Wire3.GateSlotCommutation Audit.Wire3.GateAggregatePolynomial

/-! ### Option-valued map over a column list, in list order -/

/-- `for mle in &mut tables { mle.bind(...) }` where each iteration may fail:
the list-order sequencing of independent per-column results. -/
def mapOption {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: rest => do
      let b ← f a
      let bs ← mapOption f rest
      pure (b :: bs)

theorem map_option_nil_success {α β : Type} (f : α → Option β) (ys : List β)
    (h : mapOption f [] = some ys) : ys = [] := by
  simp only [mapOption, Option.some.injEq] at h
  exact h.symm

theorem map_option_cons_success {α β : Type} (f : α → Option β) (a : α) (rest : List α) (ys : List β)
    (h : mapOption f (a :: rest) = some ys) :
    ∃ b bs, f a = some b ∧ mapOption f rest = some bs ∧ ys = b :: bs := by
  simp only [mapOption, Option.bind_eq_bind, Option.pure_def] at h
  cases hf : f a with
  | none => rw [hf, Option.none_bind] at h; exact Option.noConfusion h
  | some b =>
      rw [hf, Option.some_bind] at h
      cases hr : mapOption f rest with
      | none => rw [hr, Option.none_bind] at h; exact Option.noConfusion h
      | some bs =>
          rw [hr, Option.some_bind, Option.some.injEq] at h
          exact ⟨b, bs, rfl, rfl, h.symm⟩

theorem map_option_length {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : mapOption f xs = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => rw [map_option_nil_success f ys h]; rfl
  | cons a rest ih =>
      obtain ⟨b, bs, _, hr, rfl⟩ := map_option_cons_success f a rest ys h
      simp only [List.length_cons, ih bs hr]

theorem map_option_get {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : mapOption f xs = some ys) (i : Nat) (x : α) (hx : xs.get? i = some x) :
    ∃ y, ys.get? i = some y ∧ f x = some y := by
  induction xs generalizing ys i with
  | nil => simp at hx
  | cons a rest ih =>
      obtain ⟨b, bs, hb, hr, rfl⟩ := map_option_cons_success f a rest ys h
      cases i with
      | zero =>
          simp only [List.get?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨b, rfl, hb⟩
      | succ i =>
          simp only [List.get?_cons_succ] at hx ⊢
          exact ih bs hr i hx

theorem map_option_mem {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : mapOption f xs = some ys) : ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => rw [map_option_nil_success f ys h]; intro y hy; simp at hy
  | cons a rest ih =>
      obtain ⟨b, bs, hb, hr, rfl⟩ := map_option_cons_success f a rest ys h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨a, by simp, hb⟩
      · obtain ⟨x, hx, hfx⟩ := ih bs hr y hy'
        exact ⟨x, by simp [hx], hfx⟩

theorem map_option_total {α β : Type} (f : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, mapOption f xs = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
      obtain ⟨b, hb⟩ := h a (by simp)
      obtain ⟨bs, hbs⟩ := ih (fun x hx => h x (by simp [hx]))
      exact ⟨b :: bs, by simp only [mapOption, hb, hbs, Option.bind_eq_bind, Option.some_bind, Option.pure_def]⟩

theorem map_option_map {α β γ : Type} (f : α → Option β) (g : β → γ) (h : α → γ) (xs : List α)
    (ys : List β) (ht : mapOption f xs = some ys) (hfg : ∀ x y, f x = some y → g y = h x) :
    ys.map g = xs.map h := by
  induction xs generalizing ys with
  | nil => rw [map_option_nil_success f ys ht]; rfl
  | cons a rest ih =>
      obtain ⟨b, bs, hb, hr, rfl⟩ := map_option_cons_success f a rest ys ht
      simp only [List.map_cons, hfg a b hb, ih bs hr]

theorem map_option_id {α : Type} (f : α → Option α) (xs : List α) (hf : ∀ x, f x = some x) :
    mapOption f xs = some xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [mapOption, hf a, ih, Option.bind_eq_bind, Option.some_bind, Option.pure_def]

/-- Sequencing two per-column maps is one per-column map of the sequenced steps. -/
theorem map_option_bind {α β γ : Type} (f : α → Option β) (g : β → Option γ) (xs : List α) :
    mapOption (fun x => (f x).bind g) xs = (mapOption f xs).bind (mapOption g) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp only [mapOption, Option.bind_eq_bind, Option.pure_def]
      cases f a with
      | none => rfl
      | some b =>
          simp only [Option.some_bind]
          rw [ih]
          cases mapOption f rest with
          | none => cases g b <;> rfl
          | some bs =>
              simp only [Option.some_bind, mapOption, Option.bind_eq_bind, Option.pure_def]

/-! ### The prover state and `bind_challenge` (gate_ext3_v2.rs:142-170) -/

deriving instance DecidableEq for DenseMleIndexed.State

/-- The `GateExt3ProverState` fields touched by 142-170: the three table kinds
(each an `Ext3DenseMle`, the adopted `DenseMleIndexed.State`), `degree`,
`rounds` (each `Ext3CoefficientRound.non_constant`) and `point`. The fixed
`gate_context`, `public_inputs_hash` and `alpha` are the round parameters
`c gates publicHash alpha` of GateSlotRound. -/
structure ProverState where
  wires : List DenseMleIndexed.State
  constants : List DenseMleIndexed.State
  eq : DenseMleIndexed.State
  degree : Nat
  rounds : List (List Verifier.Ext3)
  point : List Element
  deriving DecidableEq

/-- The state's tables as GateSlotRound reads them (`tablesOf`). -/
def ProverState.tables (s : ProverState) : Tables :=
  tablesOf (s.wires.map DenseMleIndexed.State.evaluations)
    (s.constants.map DenseMleIndexed.State.evaluations) s.eq

theorem bind_variable_success (s t : DenseMleIndexed.State) (x : Element)
    (h : DenseMleIndexed.bindVariable s x = some t) :
    0 < s.numVars ∧ t = ⟨s.numVars - 1, DenseMleIndexed.bindBuffer s.evaluations x⟩ := by
  unfold DenseMleIndexed.bindVariable at h
  split at h
  · exact h.elim
  · rename_i hn
    simp only [Option.some.injEq] at h
    exact ⟨Nat.pos_of_ne_zero hn, h.symm⟩

/-- `for mle in &mut self.wires { mle.bind_variable_in_place(challenge); }`
(151-153, and 154-156 for constants): each table bound by the adopted
`bindVariable`, in list order. -/
def bindColumns (challenge : Element) (columns : List DenseMleIndexed.State) :
    Option (List DenseMleIndexed.State) :=
  mapOption (fun column => DenseMleIndexed.bindVariable column challenge) columns

theorem bind_columns_execute (x : Element) (columns : List DenseMleIndexed.State)
    (h : ∀ column ∈ columns, 0 < column.numVars) : ∃ bound, bindColumns x columns = some bound :=
  map_option_total _ columns
    (fun column hc => ⟨_, DenseMleIndexed.positive_binding_exact column x (h column hc)⟩)

theorem bind_columns_evaluations (x : Element) (columns bound : List DenseMleIndexed.State)
    (h : bindColumns x columns = some bound) :
    bound.map DenseMleIndexed.State.evaluations =
      columns.map (fun column => DenseMleIndexed.bindBuffer column.evaluations x) :=
  map_option_map _ _ _ columns bound h
    (fun column t ht => by rw [(bind_variable_success column t x ht).2])

/-- `bind_challenge` 142-161: the degree ensure (147-150), the eq bind (151),
the wire binds (152-154), the constant binds (155-157), the two pushes
(157-158). `none` is the ensure's `Err` or a table's `num_vars == 0` panic. -/
def bindChallenge (s : ProverState) (round : List Verifier.Ext3) (challenge : Element) :
    Option ProverState :=
  if round.length ≠ s.degree then none else do
    let eq ← DenseMleIndexed.bindVariable s.eq challenge
    let wires ← bindColumns challenge s.wires
    let constants ← bindColumns challenge s.constants
    pure ⟨wires, constants, eq, s.degree, s.rounds ++ [round], s.point ++ [challenge]⟩

theorem bind_challenge_success (s t : ProverState) (round : List Verifier.Ext3) (x : Element)
    (h : bindChallenge s round x = some t) :
    round.length = s.degree ∧ DenseMleIndexed.bindVariable s.eq x = some t.eq ∧
      bindColumns x s.wires = some t.wires ∧ bindColumns x s.constants = some t.constants ∧
      t.degree = s.degree ∧ t.rounds = s.rounds ++ [round] ∧ t.point = s.point ++ [x] := by
  unfold bindChallenge at h
  split at h
  · exact h.elim
  · rename_i hl
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    cases he : DenseMleIndexed.bindVariable s.eq x with
    | none => rw [he, Option.none_bind] at h; exact Option.noConfusion h
    | some eq =>
        rw [he, Option.some_bind] at h
        cases hw : bindColumns x s.wires with
        | none => rw [hw, Option.none_bind] at h; exact Option.noConfusion h
        | some wires =>
            rw [hw, Option.some_bind] at h
            cases hc : bindColumns x s.constants with
            | none => rw [hc, Option.none_bind] at h; exact Option.noConfusion h
            | some constants =>
                rw [hc, Option.some_bind, Option.some.injEq] at h
                subst h
                exact ⟨Decidable.of_not_not hl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The whole sumcheck's binds: one `bind_challenge` per (round message,
challenge) pair, in round order. Coefficient interpolation and transcript
derivation of the challenges are outside this module. -/
def bindAll : ProverState → List (List Verifier.Ext3 × Element) → Option ProverState
  | s, [] => some s
  | s, step :: rest => do
      let next ← bindChallenge s step.1 step.2
      bindAll next rest

/-- `into_proof_and_point` 163-170: the `eq.num_vars == 0` ensure. -/
def intoProofAndPoint (s : ProverState) : Option (List (List Verifier.Ext3) × List Element) :=
  if s.eq.numVars = 0 then some (s.rounds, s.point) else none

theorem into_proof_and_point_exact (s : ProverState) (h : s.eq.numVars = 0) :
    intoProofAndPoint s = some (s.rounds, s.point) := by simp [intoProofAndPoint, h]

theorem incomplete_sumcheck_rejected (s : ProverState) (h : 0 < s.eq.numVars) :
    intoProofAndPoint s = none := by simp [intoProofAndPoint, show s.eq.numVars ≠ 0 by omega]

/-- Every column after `bindAll` is the adopted `bindMany` of the original
column at the pushed challenges; nothing else touches the tables. -/
theorem bind_all_columns (s t : ProverState) (steps : List (List Verifier.Ext3 × Element))
    (h : bindAll s steps = some t) :
    mapOption (DenseMleIndexed.bindMany (steps.map Prod.snd)) s.wires = some t.wires ∧
    mapOption (DenseMleIndexed.bindMany (steps.map Prod.snd)) s.constants = some t.constants ∧
    DenseMleIndexed.bindMany (steps.map Prod.snd) s.eq = some t.eq := by
  induction steps generalizing s with
  | nil =>
      simp only [bindAll, Option.some.injEq] at h
      subst h
      exact ⟨map_option_id _ _ (fun _ => rfl), map_option_id _ _ (fun _ => rfl), rfl⟩
  | cons step rest ih =>
      simp only [bindAll, Option.bind_eq_bind] at h
      cases hb : bindChallenge s step.1 step.2 with
      | none => rw [hb, Option.none_bind] at h; exact Option.noConfusion h
      | some next =>
          rw [hb, Option.some_bind] at h
          obtain ⟨_, he, hw, hc, _, _, _⟩ := bind_challenge_success s next step.1 step.2 hb
          obtain ⟨ihw, ihc, ihe⟩ := ih next h
          have hstep : DenseMleIndexed.bindMany ((step :: rest).map Prod.snd) =
              fun column => (DenseMleIndexed.bindVariable column step.2).bind
                (DenseMleIndexed.bindMany (rest.map Prod.snd)) := funext (fun _ => rfl)
          have hw' : mapOption (fun column => DenseMleIndexed.bindVariable column step.2) s.wires =
              some next.wires := hw
          have hc' : mapOption (fun column => DenseMleIndexed.bindVariable column step.2) s.constants =
              some next.constants := hc
          refine ⟨?_, ?_, ?_⟩
          · rw [hstep, map_option_bind, hw', Option.some_bind]; exact ihw
          · rw [hstep, map_option_bind, hc', Option.some_bind]; exact ihc
          · rw [hstep]; show (DenseMleIndexed.bindVariable s.eq step.2).bind _ = some t.eq
            rw [he, Option.some_bind]; exact ihe

/-! ### The prover-state shape (constructor ensures 74-83) and its preservation -/

/-- One table with the adopted power-of-two validity and `num_vars = n`. -/
def ColumnShape (n : Nat) (column : DenseMleIndexed.State) : Prop :=
  DenseMleIndexed.Valid column ∧ column.numVars = n

/-- gate_ext3_v2.rs:70-79 plus the eq table's `Ext3DenseMle::new` validity with
`n` variables left. A supplied caller invariant of the prover state, not a
new source runtime check; it says nothing about the table CONTENTS. -/
def ProverShape (c : Gates.Config) (n : Nat) (s : ProverState) : Prop :=
  s.wires.length = c.numWires ∧ s.constants.length = c.numConstants ∧ ColumnShape n s.eq ∧
    (∀ column ∈ s.wires, ColumnShape n column) ∧ (∀ column ∈ s.constants, ColumnShape n column)

instance (s : DenseMleIndexed.State) : Decidable (DenseMleIndexed.Valid s) :=
  inferInstanceAs (Decidable (_ = _))
instance (n : Nat) (column : DenseMleIndexed.State) : Decidable (ColumnShape n column) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (c : Gates.Config) (n : Nat) (s : ProverState) : Decidable (ProverShape c n s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem bound_column_shape (n : Nat) (column bound : DenseMleIndexed.State) (x : Element)
    (h : ColumnShape (n+1) column) (hb : DenseMleIndexed.bindVariable column x = some bound) :
    ColumnShape n bound := by
  have hs := DenseMleIndexed.successful_binding_shape_and_layer column bound x h.1 hb
  exact ⟨hs.1, by have := hs.2.1; have := h.2; omega⟩

theorem bind_challenge_executes (c : Gates.Config) (n : Nat) (s : ProverState)
    (round : List Verifier.Ext3) (x : Element) (hs : ProverShape c (n+1) s)
    (hr : round.length = s.degree) :
    ∃ t, bindChallenge s round x = some t ∧ ProverShape c n t := by
  obtain ⟨hw, hc, heq, hwires, hconstants⟩ := hs
  obtain ⟨wires, hwb⟩ := bind_columns_execute x s.wires
    (fun column hm => by have := (hwires column hm).2; omega)
  obtain ⟨constants, hcb⟩ := bind_columns_execute x s.constants
    (fun column hm => by have := (hconstants column hm).2; omega)
  have hn : 0 < s.eq.numVars := by have := heq.2; omega
  have he := DenseMleIndexed.positive_binding_exact s.eq x hn
  refine ⟨⟨wires, constants, ⟨s.eq.numVars - 1, DenseMleIndexed.bindBuffer s.eq.evaluations x⟩,
    s.degree, s.rounds ++ [round], s.point ++ [x]⟩, ?_, ?_⟩
  · simp only [bindChallenge, hr, ne_eq, not_true_eq_false, ↓reduceIte, he, hwb, hcb,
      Option.bind_eq_bind, Option.some_bind, Option.pure_def]
  · refine ⟨(map_option_length _ _ _ hwb).trans hw, (map_option_length _ _ _ hcb).trans hc, ?_, ?_, ?_⟩
    · exact ⟨DenseMleIndexed.binding_retains_power_two_shape s.eq x heq.1 hn,
        by show s.eq.numVars - 1 = n; have := heq.2; omega⟩
    · intro column hm
      obtain ⟨original, ho, hb⟩ := map_option_mem _ _ _ hwb column hm
      exact bound_column_shape n original column x (hwires original ho) hb
    · intro column hm
      obtain ⟨original, ho, hb⟩ := map_option_mem _ _ _ hcb column hm
      exact bound_column_shape n original column x (hconstants original ho) hb

theorem bind_all_executes (c : Gates.Config) (n : Nat) (s : ProverState)
    (steps : List (List Verifier.Ext3 × Element)) (hs : ProverShape c n s) (hlen : steps.length = n)
    (hdeg : ∀ step ∈ steps, step.1.length = s.degree) :
    ∃ t, bindAll s steps = some t ∧ ProverShape c 0 t ∧ t.degree = s.degree ∧
      t.rounds = s.rounds ++ steps.map Prod.fst ∧ t.point = s.point ++ steps.map Prod.snd := by
  induction steps generalizing s n with
  | nil =>
      simp only [List.length_nil] at hlen
      subst hlen
      exact ⟨s, rfl, hs, rfl, by simp, by simp⟩
  | cons step rest ih =>
      cases n with
      | zero => simp at hlen
      | succ n =>
          obtain ⟨next, hb, hshape⟩ :=
            bind_challenge_executes c n s step.1 step.2 hs (hdeg step (by simp))
          obtain ⟨_, _, _, _, hdegree, hrounds, hpoint⟩ := bind_challenge_success s next step.1 step.2 hb
          obtain ⟨t, ht, htshape, hdeg', hrounds', hpoint'⟩ := ih n next hshape (by simpa using hlen)
            (fun st hm => by rw [hdegree]; exact hdeg st (by simp [hm]))
          refine ⟨t, ?_, htshape, hdeg'.trans hdegree, ?_, ?_⟩
          · simp only [bindAll, hb, Option.bind_eq_bind, Option.some_bind, ht]
          · rw [hrounds', hrounds]; simp
          · rw [hpoint', hpoint]; simp

/-! ### Fully bound tables are single cells -/

theorem single_cell (column : DenseMleIndexed.State) (h : ColumnShape 0 column) :
    ∃ v, column.evaluations = [v] := by
  have hl : column.evaluations.length = 1 := by
    have hv : column.evaluations.length = 2^column.numVars := h.1
    rw [hv, h.2]
    rfl
  exact List.length_eq_one.mp hl

/-- The fully bound cells, one per column. -/
structure Cells where
  wires : List Element
  constants : List Element
  eq : Element
  deriving DecidableEq

deriving instance DecidableEq for Tables

/-- The cells as single-entry tables (`num_vars = 0`, length `2^0 = 1`). -/
def Cells.tables (k : Cells) : Tables :=
  ⟨k.wires.map (fun v => [v]), k.constants.map (fun v => [v]), [k.eq]⟩

theorem single_cells (columns : List DenseMleIndexed.State)
    (h : ∀ column ∈ columns, ColumnShape 0 column) :
    ∃ values : List Element,
      columns.map DenseMleIndexed.State.evaluations = values.map (fun v => [v]) ∧
      values.length = columns.length := by
  induction columns with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons column rest ih =>
      obtain ⟨v, hv⟩ := single_cell column (h column (by simp))
      obtain ⟨values, hvals, hlen⟩ := ih (fun c hc => h c (by simp [hc]))
      exact ⟨v :: values, by simp only [List.map_cons, hv, hvals], by simp [hlen]⟩

theorem fully_bound_cells (c : Gates.Config) (s : ProverState) (hs : ProverShape c 0 s) :
    ∃ k : Cells, s.tables = k.tables ∧ k.wires.length = c.numWires ∧
      k.constants.length = c.numConstants := by
  obtain ⟨hw, hc, heq, hwires, hconstants⟩ := hs
  obtain ⟨e, he⟩ := single_cell s.eq heq
  obtain ⟨ws, hws, hwl⟩ := single_cells s.wires hwires
  obtain ⟨cs, hcs, hcl⟩ := single_cells s.constants hconstants
  exact ⟨⟨ws, cs, e⟩, by simp only [ProverState.tables, tablesOf, Cells.tables, hws, hcs, he],
    hwl.trans hw, hcl.trans hc⟩

/-- (3) Binding a point of length `n` from an `n`-variable shaped state
executes, leaves every table a single cell, and `into_proof_and_point`
returns exactly the pushed rounds and point. -/
theorem fully_bound_shape (c : Gates.Config) (n : Nat) (s : ProverState)
    (steps : List (List Verifier.Ext3 × Element)) (hs : ProverShape c n s) (hlen : steps.length = n)
    (hdeg : ∀ step ∈ steps, step.1.length = s.degree) :
    ∃ t, bindAll s steps = some t ∧ ProverShape c 0 t ∧
      (∃ k : Cells, t.tables = k.tables ∧ k.wires.length = c.numWires ∧
        k.constants.length = c.numConstants) ∧
      intoProofAndPoint t = some (s.rounds ++ steps.map Prod.fst, s.point ++ steps.map Prod.snd) := by
  obtain ⟨t, ht, hshape, _, hrounds, hpoint⟩ := bind_all_executes c n s steps hs hlen hdeg
  refine ⟨t, ht, hshape, fully_bound_cells c t hshape, ?_⟩
  rw [into_proof_and_point_exact t hshape.2.2.1.2, hrounds, hpoint]

/-- With `n > 0` variables left, the shaped state supplies exactly the
`TableShape` at `half = 2^(n-1)` that the adopted round theorems consume. -/
theorem shape_gives_table_shape (c : Gates.Config) (n : Nat) (s : ProverState)
    (hs : ProverShape c n s) (hn : 0 < n) : TableShape c (2^(n-1)) s.tables := by
  obtain ⟨hw, hc, heq, hwires, hconstants⟩ := hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  have hpow : 2^(m+1) = 2*2^(m+1-1) := by
    rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
  simp only [TableShape, ProverState.tables, tablesOf, List.length_map, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine ⟨hw, hc, ?_, ?_, ?_⟩
  · rw [← hpow, ← heq.2]; exact heq.1
  · intro column hm
    have h := hwires column hm
    rw [← hpow, ← h.2]; exact h.1
  · intro column hm
    have h := hconstants column hm
    rw [← hpow, ← h.2]; exact h.1

/-! ### (2) Bound cells are the adopted `evaluate` / packed fold -/

theorem bound_column_is_packed_fold (n : Nat) (column bound : DenseMleIndexed.State)
    (point : List Element) (hc : ColumnShape n column) (hp : point.length = n)
    (hb : DenseMleIndexed.bindMany point column = some bound) :
    ∃ v, bound.evaluations = [v] ∧ DenseMleIndexed.evaluate column point = some v ∧
      v.toVerifier.val =
        Packed.fold (DenseMleIndexed.raw column.evaluations) (DenseMleIndexed.raw point) := by
  obtain ⟨t, ht, hvalid, hcount, _⟩ :=
    DenseMleIndexed.all_bindings_execute column point hc.1 (by rw [hp, hc.2])
  have hbt : bound = t := Option.some.inj (hb.symm.trans ht)
  subst hbt
  obtain ⟨v, hv⟩ := single_cell bound ⟨hvalid, by have := hc.2; omega⟩
  obtain ⟨result, he, hraw⟩ :=
    DenseMleIndexed.evaluate_full_table_same_packed_fold column point hc.1 (by rw [hp, hc.2])
  have hev : DenseMleIndexed.evaluate column point = some v := by
    simp only [DenseMleIndexed.evaluate, hp, hc.2, ne_eq, not_true_eq_false, ↓reduceIte, ht,
      Option.bind_eq_bind, Option.some_bind, hv, List.getElem?_cons_zero]
  rw [hev, Option.some.injEq] at he
  subst he
  exact ⟨v, hv, hev, hraw⟩

/-- (2) After `bindAll` over a full-length point, every wire, constant and eq
column is a single cell equal to the adopted `DenseMleIndexed.evaluate` of the
original column at the pushed point, whose raw value is the adopted packed fold
`Packed.fold` of the raw original column at the raw point. -/
theorem bound_gate_columns_are_packed_folds (c : Gates.Config) (n : Nat) (s t : ProverState)
    (steps : List (List Verifier.Ext3 × Element)) (hs : ProverShape c n s)
    (hlen : steps.length = n) (hb : bindAll s steps = some t) :
    (∀ i column, s.wires.get? i = some column →
      ∃ bound v, t.wires.get? i = some bound ∧ bound.evaluations = [v] ∧
        DenseMleIndexed.evaluate column (steps.map Prod.snd) = some v ∧
        v.toVerifier.val = Packed.fold (DenseMleIndexed.raw column.evaluations)
          (DenseMleIndexed.raw (steps.map Prod.snd))) ∧
    (∀ i column, s.constants.get? i = some column →
      ∃ bound v, t.constants.get? i = some bound ∧ bound.evaluations = [v] ∧
        DenseMleIndexed.evaluate column (steps.map Prod.snd) = some v ∧
        v.toVerifier.val = Packed.fold (DenseMleIndexed.raw column.evaluations)
          (DenseMleIndexed.raw (steps.map Prod.snd))) ∧
    (∃ v, t.eq.evaluations = [v] ∧ DenseMleIndexed.evaluate s.eq (steps.map Prod.snd) = some v ∧
      v.toVerifier.val = Packed.fold (DenseMleIndexed.raw s.eq.evaluations)
        (DenseMleIndexed.raw (steps.map Prod.snd))) := by
  obtain ⟨hw, hc, he⟩ := bind_all_columns s t steps hb
  have hpoint : (steps.map Prod.snd).length = n := by rw [List.length_map]; exact hlen
  refine ⟨fun i column hi => ?_, fun i column hi => ?_, ?_⟩
  · obtain ⟨bound, hbound, hbm⟩ := map_option_get _ _ _ hw i column hi
    obtain ⟨v, hv, hev, hraw⟩ := bound_column_is_packed_fold n column bound _
      (hs.2.2.2.1 column (List.mem_iff_get?.mpr ⟨i, hi⟩)) hpoint hbm
    exact ⟨bound, v, hbound, hv, hev, hraw⟩
  · obtain ⟨bound, hbound, hbm⟩ := map_option_get _ _ _ hc i column hi
    obtain ⟨v, hv, hev, hraw⟩ := bound_column_is_packed_fold n column bound _
      (hs.2.2.2.2 column (List.mem_iff_get?.mpr ⟨i, hi⟩)) hpoint hbm
    exact ⟨bound, v, hbound, hv, hev, hraw⟩
  · exact bound_column_is_packed_fold n s.eq t.eq _ hs.2.2.1 hpoint he

/-! ### (1) The last round (`half = 1`, one suffix) -/

/-- The tables after one `bind_challenge` at x, at table level: the adopted
`bindBuffer` on every column (150-156 without the ensure and the pushes). -/
def bindTables (t : Tables) (x : Element) : Tables :=
  ⟨t.wires.map (fun column => DenseMleIndexed.bindBuffer column x),
   t.constants.map (fun column => DenseMleIndexed.bindBuffer column x),
   DenseMleIndexed.bindBuffer t.eq x⟩

theorem bind_challenge_tables (s t : ProverState) (round : List Verifier.Ext3) (x : Element)
    (h : bindChallenge s round x = some t) : t.tables = bindTables s.tables x := by
  obtain ⟨_, he, hw, hc, _, _, _⟩ := bind_challenge_success s t round x h
  simp only [ProverState.tables, tablesOf, bindTables, bind_columns_evaluations x _ _ hw,
    bind_columns_evaluations x _ _ hc, (bind_variable_success _ _ _ he).2, List.map_map,
    Function.comp_def]

/-- Binding a two-entry column is the single blended cell. -/
theorem bind_pair (a b x : Element) :
    DenseMleIndexed.bindBuffer [a, b] x = [DenseMleIndexed.blend a b x] := by
  have hl : (DenseMleIndexed.bindBuffer [a, b] x).length = 1 := by
    simpa using DenseMleIndexed.bind_buffer_length [a, b] x
  have hr := DenseMleIndexed.bind_buffer_reads_exact_line [a, b] x 0 (by simp)
  obtain ⟨v, hv⟩ := List.length_eq_one.mp hl
  rw [hv] at hr ⊢
  simp only [DenseMleIndexed.line, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero,
    List.getD_cons_succ] at hr
  rw [hr]

/-- The GateSuffixPolynomial affine read of a pair at x IS the bound cell. -/
theorem affine_weight_blend (a b x : Element) :
    affineWeight a b x = (DenseMleIndexed.blend a b x).toVerifier := rfl

/-- The GateSlotRound literal adjacent read of a pair at x IS the bound cell. -/
theorem interpolate_pair (a b x : Element) :
    interpolateRead [a, b] 0 x = (DenseMleIndexed.blend a b x).toVerifier := rfl

theorem pairs_bind_to_cells (columns : List (List Element)) (x : Element)
    (hlen : ∀ column ∈ columns, column.length = 2) :
    ∃ values : List Element,
      columns.map (fun column => DenseMleIndexed.bindBuffer column x) = values.map (fun v => [v]) ∧
      values.length = columns.length := by
  induction columns with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons column rest ih =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hlen column (by simp))
      obtain ⟨values, hv, hl⟩ := ih (fun c hc => hlen c (by simp [hc]))
      exact ⟨DenseMleIndexed.blend a b x :: values, by simp only [List.map_cons, bind_pair, hv],
        by simp [hl]⟩

theorem bound_pairs_are_affine_reads (columns : List (List Element)) (values : List Element)
    (x : Element) (hlen : ∀ column ∈ columns, column.length = 2)
    (h : columns.map (fun column => DenseMleIndexed.bindBuffer column x) = values.map (fun v => [v])) :
    affineValues (captureAdjacent columns 0) x = values.map Element.toVerifier := by
  induction columns generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons v vs => simp at h
  | cons column rest ih =>
      cases values with
      | nil => simp at h
      | cons v vs =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp (hlen column (by simp))
          rw [bind_pair] at h
          have hv : v = DenseMleIndexed.blend a b x := by simpa using h.1.symm
          simp only [affineValues, captureAdjacent, List.map_cons]
          refine List.cons_eq_cons.mpr ⟨?_, ih vs (fun c hc => hlen c (by simp [hc])) h.2⟩
          show affineWeight a b x = v.toVerifier
          rw [affine_weight_blend, hv]

theorem bound_tables_are_cells (c : Gates.Config) (t : Tables) (x : Element)
    (ht : TableShape c 1 t) :
    ∃ k : Cells, bindTables t x = k.tables ∧ k.wires.length = c.numWires ∧
      k.constants.length = c.numConstants := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by simpa using ht.2.2.1)
  obtain ⟨ws, hws, hwl⟩ := pairs_bind_to_cells t.wires x
    (fun column hc => by simpa using ht.2.2.2.1 column hc)
  obtain ⟨cs, hcs, hcl⟩ := pairs_bind_to_cells t.constants x
    (fun column hc => by simpa using ht.2.2.2.2 column hc)
  exact ⟨⟨ws, cs, DenseMleIndexed.blend a b x⟩,
    by simp only [bindTables, Cells.tables, hws, hcs, hab, bind_pair],
    hwl.trans ht.1, hcl.trans ht.2.1⟩

theorem cells_lengths (c : Gates.Config) (t : Tables) (x : Element) (k : Cells)
    (ht : TableShape c 1 t) (hk : bindTables t x = k.tables) :
    k.wires.length = c.numWires ∧ k.constants.length = c.numConstants := by
  have hw := congrArg (fun t : Tables => t.wires.length) hk
  have hc := congrArg (fun t : Tables => t.constants.length) hk
  simp only [bindTables, Cells.tables, List.length_map] at hw hc
  exact ⟨hw ▸ ht.1, hc ▸ ht.2.1⟩

/-- The suffix-0 captured reads at x of a pair-shaped table are the bound cells. -/
theorem bound_tables_cells (c : Gates.Config) (t : Tables) (x : Element) (k : Cells)
    (ht : TableShape c 1 t) (hk : bindTables t x = k.tables) :
    affineValues (captureAdjacent t.wires 0) x = k.wires.map Element.toVerifier ∧
    affineValues (captureAdjacent t.constants 0) x = k.constants.map Element.toVerifier ∧
    affineWeight (t.eq.getD 0 0) (t.eq.getD 1 0) x = k.eq.toVerifier := by
  simp only [bindTables, Cells.tables, Tables.mk.injEq] at hk
  obtain ⟨hw, hc, he⟩ := hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by simpa using ht.2.2.1)
  refine ⟨bound_pairs_are_affine_reads t.wires k.wires x
      (fun column hc => by simpa using ht.2.2.2.1 column hc) hw,
    bound_pairs_are_affine_reads t.constants k.constants x
      (fun column hc => by simpa using ht.2.2.2.2 column hc) hc, ?_⟩
  rw [hab, bind_pair] at he
  simp only [List.cons.injEq, and_true] at he
  rw [hab]
  show affineWeight a b x = k.eq.toVerifier
  rw [affine_weight_blend, he]

/-- `eq_cell * evalCombined(cells)`: the verifier-shaped terminal expression
on the fully bound cells, with GatesComplete's actual `evalCombined`
(the same evaluator the verifier model uses) and the SAME gates, public hash
and alpha as the prover round. `none` is `evalCombined`'s own failure. -/
def boundTerminal (c : Gates.Config) (gates : List Gates.GateInfo) (publicHash : Nat → Verifier.Base)
    (alpha : Element) (k : Cells) : Option Verifier.Ext3 := do
  let gate ← GatesComplete.evalCombined c gates (k.wires.map Element.toVerifier)
    (k.constants.map Element.toVerifier) publicHash alpha.toVerifier
  pure (Verifier.mul k.eq.toVerifier gate)

theorem eval_slice_last_round (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (x : Element) (k : Cells)
    (ht : TableShape c 1 t) (hk : bindTables t x = k.tables) :
    evalSlice c gates publicHash alpha x (captureSlice t 0) = boundTerminal c gates publicHash alpha k := by
  obtain ⟨hw, hc, he⟩ := bound_tables_cells c t x k ht hk
  simp only [evalSlice, evaluateWeighted, captureSlice, boundTerminal, Nat.mul_zero, Nat.zero_add,
    hw, hc, he]

/-- The slot-first weighted evaluator of the one suffix at x
(`slot_slice_equals_complete` reused). -/
theorem slot_slice_last_round (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (x : Element) (k : Cells)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c 1 t)
    (hk : bindTables t x = k.tables) :
    slotSlice c gates publicHash alpha x (captureSlice t 0) = boundTerminal c gates publicHash alpha k :=
  (slot_slice_equals_complete c gates publicHash alpha x (captureSlice t 0) hv).trans
    (eval_slice_last_round c gates publicHash alpha t x k ht hk)

/-- The literal iteration body 114-132 at `suffix = 0` and the integer grid
point (`grid_term_equals_suffix_slice` reused): `eq_value * aggregate` IS the
terminal expression on the tables bound at that grid point. -/
theorem grid_term_last_round (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (integer : Nat) (k : Cells)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c 1 t)
    (hk : bindTables t (gridPoint integer) = k.tables) :
    gridTerm c gates publicHash alpha t 0 integer = boundTerminal c gates publicHash alpha k :=
  (grid_term_equals_suffix_slice c gates publicHash alpha t 0 integer hv).trans
    (eval_slice_last_round c gates publicHash alpha t (gridPoint integer) k ht hk)

theorem sum_single_suffix (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha x : Element) (s : Slice) :
    sumSuffixes c gates publicHash alpha x [s] Verifier.zero = evalSlice c gates publicHash alpha x s := by
  simp only [sumSuffixes, Option.bind_eq_bind]
  cases evalSlice c gates publicHash alpha x s with
  | none => rfl
  | some term => simp only [Option.some_bind, Gates.zero_add]

/-- The round value (per-integer suffix-first sum, here of the single suffix)
at ANY x is the terminal expression on the tables bound at x. -/
theorem round_value_last_round (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (x : Element) (k : Cells)
    (ht : TableShape c 1 t) (hk : bindTables t x = k.tables) :
    currentRoundValue c gates publicHash alpha x t 1 = boundTerminal c gates publicHash alpha k := by
  have h1 : captureSuffixes t 1 = [captureSlice t 0] := rfl
  simp only [currentRoundValue, h1, sum_single_suffix]
  exact eval_slice_last_round c gates publicHash alpha t x k ht hk

/-- (1) With one variable left, the accumulated `eq_value * aggregate` of
GateSlotRound (slot-first evaluator, at the one suffix) and the
GateSuffixPolynomial round value at x both equal
`mul (eq cell) (evalCombined cells)` for the cells of the tables bound at x,
and `evalCombined` executes on those cells. -/
theorem fully_bound_grid_is_eq_times_evalCombined (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (t : Tables) (x : Element) (k : Cells)
    (hv : Gates.validateConfiguration c gates = some ()) (ht : TableShape c 1 t)
    (hk : bindTables t x = k.tables) :
    ∃ gate, GatesComplete.evalCombined c gates (k.wires.map Element.toVerifier)
        (k.constants.map Element.toVerifier) publicHash alpha.toVerifier = some gate ∧
      slotSlice c gates publicHash alpha x (captureSlice t 0) = some (Verifier.mul k.eq.toVerifier gate) ∧
      currentRoundValue c gates publicHash alpha x t 1 = some (Verifier.mul k.eq.toVerifier gate) := by
  obtain ⟨hw, hc⟩ := cells_lengths c t x k ht hk
  obtain ⟨gate, hg⟩ := GatesComplete.valid_configuration_always_evaluates c gates
    (k.wires.map Element.toVerifier) (k.constants.map Element.toVerifier) publicHash alpha.toVerifier hv
    (by rw [List.length_map]; exact hw) (by rw [List.length_map]; exact hc)
  refine ⟨gate, hg, ?_, ?_⟩
  · rw [slot_slice_last_round c gates publicHash alpha t x k hv ht hk]
    simp only [boundTerminal, hg, Option.bind_eq_bind, Option.some_bind, Option.pure_def]
  · rw [round_value_last_round c gates publicHash alpha t x k ht hk]
    simp only [boundTerminal, hg, Option.bind_eq_bind, Option.some_bind, Option.pure_def]

/-- The executed last-round body (`current_round` 105-134 with one variable
left): every accumulator cell is the terminal expression on the tables bound
at that integer grid point. -/
theorem last_round_grid_cells (c : Gates.Config) (gates : List Gates.GateInfo)
    (publicHash : Nat → Verifier.Base) (alpha : Element) (s : ProverState) (degree : Nat)
    (hv : Gates.validateConfiguration c gates = some ()) (hs : ProverShape c 1 s) :
    ∃ evaluations, currentRoundEvaluations c gates publicHash alpha
        (s.wires.map DenseMleIndexed.State.evaluations)
        (s.constants.map DenseMleIndexed.State.evaluations) s.eq degree = some evaluations ∧
      evaluations.length = degree+1 ∧
      ∀ integer, integer ≤ degree → ∃ k : Cells, bindTables s.tables (gridPoint integer) = k.tables ∧
        boundTerminal c gates publicHash alpha k = some (evaluations.getD integer Verifier.zero) := by
  have hn : 0 < s.eq.numVars := by rw [hs.2.2.1.2]; exact Nat.one_pos
  have ht : TableShape c 1 s.tables := by simpa using shape_gives_table_shape c 1 s hs Nat.one_pos
  have hhalf : sourceHalf s.eq = 1 := by
    rw [(valid_source_half s.eq hs.2.2.1.1 hn).1, hs.2.2.1.2]
    rfl
  obtain ⟨evaluations, he⟩ := configured_grid_executes c gates publicHash alpha s.tables degree 1 hv ht
  obtain ⟨hlen, hcells⟩ :=
    grid_entries_are_suffix_sums c gates publicHash alpha s.tables degree 1 evaluations hv he
  refine ⟨evaluations, ?_, hlen, fun integer hi => ?_⟩
  · rw [positive_round_exact c gates publicHash alpha _ _ s.eq degree hn, hhalf]
    exact he
  · obtain ⟨k, hk, _, _⟩ := bound_tables_are_cells c s.tables (gridPoint integer) ht
    exact ⟨k, hk, (round_value_last_round c gates publicHash alpha s.tables (gridPoint integer) k ht hk).symm.trans
      (hcells integer hi)⟩

/-! ### The verifier's terminal expression (MleVerifierV2.sol:378-391,
OuterLogupExt3Verifier.sol:211-228, verifier_v2.rs:422-434) -/

/-- The proof fields the gate terminal reads, the gate analogue of
`Verifier.NormTerminalInput`: the claimed gate-witness and gate-preprocessed
constituent values (both WHIR-bound in `expectedClaims`; that binding is
not used here) and the public inputs hashed to `publicInputsHash`. -/
structure GateTerminalInput where
  witness : List Verifier.Ext3
  preprocessed : List Verifier.Ext3
  publicInputs : List Verifier.Base

def gateTerminalInput (p : Verifier.Proof) : GateTerminalInput :=
  ⟨p.used.gateWitness, p.used.gatePreprocessed, p.publicInputs⟩

/-- MleVerifierV2.sol:378-381 / verifier_v2.rs:426-427: the gate constants are
the first `numConstants` gate-preprocessed claims (`Verifier.gateTerminal`
line 398, `gatePreprocessed.take numConstants`). -/
def claimedConstants (c : Verifier.Config) (input : GateTerminalInput) : List Verifier.Ext3 :=
  input.preprocessed.take c.numConstants

/-- The EXPLICIT correspondence of the prover's fully bound wire/constant cells
to the verifier's claimed inputs. It is a definition to be discharged by whoever
relates prover tables to proof claims; it is not derived here. -/
def CellsMatchClaims (c : Verifier.Config) (k : Cells) (input : GateTerminalInput) : Prop :=
  k.wires.map Element.toVerifier = input.witness ∧
    k.constants.map Element.toVerifier = claimedConstants c input

/-- Integrated.lean:46, the adopted conversion of the four-limb public-input
hash into GatesComplete's `Nat → Base` (its length-4 check is Integrated's). -/
def publicHashFunction (hash : List Verifier.Base) : Nat → Verifier.Base :=
  fun i => hash.getD i (Verifier.base 0)

/-- Verifier.lean:395-399 under Integrated.lean:43-49: the model engine's gate
terminal is `eq(gateTau, gatePoint) * gateResult`, where `gateResult` is
Integrated's `evaluateGate` on `gateWitness`, `gatePreprocessed.take
numConstants`, the public-inputs hash and `gateAlpha`. The `getD zero` is the
adopted totalization of the Engine interface (Integrated header); it is
eliminated below whenever `gateResult` is `some`. -/
theorem engine_gate_terminal_unfolds (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) :
    Verifier.gateTerminal (Integrated.modelEngine e decode) c p =
      Verifier.mul (Norm.eqEvaluation (e.initialTranscript c p).gateTau (Verifier.derivedRounds e c p).gatePoint)
        ((Integrated.gateResult (Integrated.modelEngine e decode) decode c p).getD Verifier.zero) := rfl

/-- (1, verifier side) Under the explicit eq-cell hypothesis `heq` and the
explicit cell/claim correspondence, the bound terminal expression IS the
model engine's gate terminal, and `gateResult` executes with the same gate
value. `heq` is a hypothesis, not a conclusion: eq-table provenance from
`gateTau` is not modelled. -/
theorem bound_terminal_is_engine_gate_terminal (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo) (k : Cells) (alpha : Element)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hp : (e.publicInputsHash p.publicInputs).length = 4)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hk : CellsMatchClaims c k (gateTerminalInput p))
    (hw : k.wires.length = c.numWires) (hc : k.constants.length = c.numConstants)
    (halpha : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript c p).gateTau (Verifier.derivedRounds e c p).gatePoint) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      boundTerminal (Integrated.gateConfig c) gates (publicHashFunction (e.publicInputsHash p.publicInputs))
        alpha k = some (Verifier.mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p = Verifier.mul k.eq.toVerifier gate := by
  obtain ⟨gate, hg⟩ := GatesComplete.valid_configuration_always_evaluates (Integrated.gateConfig c) gates
    (k.wires.map Element.toVerifier) (k.constants.map Element.toVerifier)
    (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha.toVerifier hv
    (by rw [List.length_map]; exact hw) (by rw [List.length_map]; exact hc)
  have hres : Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate := by
    have hg' := hg
    rw [hk.1, hk.2, halpha] at hg'
    show Integrated.evaluateGate decode c p.used.gateWitness (p.used.gatePreprocessed.take c.numConstants)
      (e.publicInputsHash p.publicInputs) (e.initialTranscript c p).gateAlpha = some gate
    simp only [Integrated.evaluateGate, hd, Option.bind_eq_bind, Option.some_bind, hr, hp, ne_eq,
      not_true_eq_false, or_self, ↓reduceIte]
    exact hg'
  refine ⟨gate, hres, ?_, ?_⟩
  · simp only [boundTerminal, hg, Option.bind_eq_bind, Option.some_bind, Option.pure_def]
  · rw [engine_gate_terminal_unfolds, hres, Option.getD_some, heq]

/-- HONEST-PROVER ONLY. An honest prover state with one variable left, bound at
the final challenge x into cells that match the proof's claimed gate
witness/constants (`CellsMatchClaims`), with the prover's alpha equal to the
transcript's `gateAlpha` and the bound eq cell equal to `eq(gateTau, gatePoint)`
(explicit hypothesis): the prover's last-round polynomial value at x is exactly
the model engine's gate terminal. This is what an honest prover's message means;
it is not a statement about arbitrary accepted proofs. -/
theorem honest_last_round_is_engine_gate_terminal (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo) (s t : ProverState)
    (round : List Verifier.Ext3) (x : Element) (k : Cells) (alpha : Element)
    (hs : ProverShape (Integrated.gateConfig c) 1 s)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hb : bindChallenge s round x = some t) (hkt : t.tables = k.tables)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hp : (e.publicInputsHash p.publicInputs).length = 4)
    (hk : CellsMatchClaims c k (gateTerminalInput p))
    (halpha : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript c p).gateTau (Verifier.derivedRounds e c p).gatePoint) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      currentRoundValue (Integrated.gateConfig c) gates
        (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha x s.tables 1 =
        some (Verifier.mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p = Verifier.mul k.eq.toVerifier gate := by
  have ht : TableShape (Integrated.gateConfig c) 1 s.tables := by
    simpa using shape_gives_table_shape _ 1 s hs Nat.one_pos
  have hbt : bindTables s.tables x = k.tables := (bind_challenge_tables s t round x hb).symm.trans hkt
  obtain ⟨hw, hc⟩ := cells_lengths _ _ _ _ ht hbt
  obtain ⟨gate, hres, hterm, hengine⟩ :=
    bound_terminal_is_engine_gate_terminal e decode c p gates k alpha hd hr hp hv hk hw hc halpha heq
  refine ⟨gate, hres, ?_, hengine⟩
  rw [round_value_last_round _ gates _ alpha s.tables x k ht hbt]
  exact hterm

/-- HONEST-PROVER ONLY, against acceptance. If the integrated verifier accepts
`p`, then (`accepted_concrete_terminal_equations`) the engine's gate terminal
is the derived `gateClaim`, so an honest prover's last-round value at the final
challenge, under the same explicit correspondences, is that derived claim. The
metadata facts (gate rows, hash length, configuration validity) are DERIVED
from acceptance. No converse and no soundness is claimed. -/
theorem honest_last_round_meets_accepted_claim (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s t : ProverState) (round : List Verifier.Ext3) (x : Element)
    (k : Cells) (alpha : Element)
    (hacc : Integrated.verify e decode pin chain c p = .ok ())
    (hs : ProverShape (Integrated.gateConfig c) 1 s) (hd : decode c.gatesEncoding = some gates)
    (hb : bindChallenge s round x = some t) (hkt : t.tables = k.tables)
    (hk : CellsMatchClaims c k (gateTerminalInput p))
    (halpha : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (heq : k.eq.toVerifier =
      Norm.eqEvaluation (e.initialTranscript c p).gateTau (Verifier.derivedRounds e c p).gatePoint) :
    currentRoundValue (Integrated.gateConfig c) gates
      (publicHashFunction (e.publicInputsHash p.publicInputs)) alpha x s.tables 1 =
      some (Verifier.derivedRounds e c p).gateClaim := by
  obtain ⟨_, gate0, _, hg, _, hclaim⟩ :=
    Integrated.accepted_concrete_terminal_equations e decode pin chain c p hacc
  obtain ⟨gates', hd', hr, hp, _, _, hv⟩ :=
    Integrated.successful_gate_evaluation_checks_all_metadata decode c _ _ _ _ gate0 hg
  rw [hd, Option.some.injEq] at hd'
  subst hd'
  obtain ⟨gate, hres, hval, _⟩ := honest_last_round_is_engine_gate_terminal e decode c p gates s t round
    x k alpha hs hv hb hkt hd hr hp hk halpha heq
  rw [hres, Option.some.injEq] at hg
  subst hg
  rw [hval, heq, hclaim]

/-! ### A concrete non-vacuous example -/

/-- The arithmetic gate of Gates.lean (`exampleArithmetic`, gateId 3, one
constraint `output - (c0*a*b + c1*addend)`) in the configuration
`⟨1, 3, 1, 4, 2⟩` already validated there. -/
def exampleConfig : Gates.Config := ⟨1, 3, 1, 4, 2⟩
def exampleGate : Gates.GateInfo := Gates.exampleArithmetic
def examplePublicHash : Nat → Verifier.Base := fun _ => Verifier.base 0
def exampleAlpha : Element := 9

/-- One variable left: four wire pairs, three constant pairs (selector, c0,
c1), the eq pair; `degree = quotientDegree + 2 = 4`, nothing pushed yet. -/
def exampleState : ProverState :=
  ⟨[⟨1, [5, 1]⟩, ⟨1, [7, 1]⟩, ⟨1, [11, 1]⟩, ⟨1, [103, 1]⟩],
   [⟨1, [0, 0]⟩, ⟨1, [2, 2]⟩, ⟨1, [3, 3]⟩], ⟨1, [4, 6]⟩, 4, [], []⟩
def exampleRound : List Verifier.Ext3 := List.replicate 4 Verifier.zero
def exampleChallenge : Element := 2

/-- The cells bound at x = 2: `(1-2)*left + 2*right`. -/
def exampleCells : Cells := ⟨[-3, -5, -9, -101], [0, 2, 3], 8⟩

/-- `8 * (-101 - (2*(-3)*(-5) + 3*(-9))) = 8 * (-104) = -832`. -/
def exampleTerminal : Verifier.Ext3 := Norm.embed 18446744069414583489

theorem example_configuration : Gates.validateConfiguration exampleConfig [exampleGate] = some () := by
  decide

theorem example_shape : ProverShape exampleConfig 1 exampleState := by decide

theorem example_bind :
    (bindChallenge exampleState exampleRound exampleChallenge).map ProverState.tables =
      some exampleCells.tables := by decide

theorem example_bind_tables : bindTables exampleState.tables exampleChallenge = exampleCells.tables := by
  decide

theorem example_round_value :
    currentRoundValue exampleConfig [exampleGate] examplePublicHash exampleAlpha exampleChallenge
      exampleState.tables 1 = some exampleTerminal := by decide

theorem example_bound_terminal :
    boundTerminal exampleConfig [exampleGate] examplePublicHash exampleAlpha exampleCells =
      some exampleTerminal := by decide

theorem example_terminal_nonzero : exampleTerminal ≠ Verifier.zero := by decide

/-- The general theorem instantiated on the example agrees with the literal values. -/
theorem example_instantiates_binding :
    ∃ gate, GatesComplete.evalCombined exampleConfig [exampleGate]
        (exampleCells.wires.map Element.toVerifier) (exampleCells.constants.map Element.toVerifier)
        examplePublicHash exampleAlpha.toVerifier = some gate ∧
      currentRoundValue exampleConfig [exampleGate] examplePublicHash exampleAlpha exampleChallenge
        exampleState.tables 1 = some (Verifier.mul exampleCells.eq.toVerifier gate) :=
  have ht : TableShape exampleConfig 1 exampleState.tables := by
    simpa using shape_gives_table_shape exampleConfig 1 exampleState example_shape Nat.one_pos
  let ⟨gate, hg, _, hval⟩ := fully_bound_grid_is_eq_times_evalCombined exampleConfig [exampleGate]
    examplePublicHash exampleAlpha exampleState.tables exampleChallenge exampleCells
    example_configuration ht example_bind_tables
  ⟨gate, hg, hval⟩

/-- The bound wire cell `-3` is the adopted `evaluate` and packed fold of `[5, 1]` at `[2]`. -/
theorem example_packed_fold :
    DenseMleIndexed.evaluate ⟨1, [5, 1]⟩ [2] = some (-3 : Element) ∧
    Packed.fold (DenseMleIndexed.raw [5, 1]) (DenseMleIndexed.raw [2]) = (-3 : Element).toVerifier.val := by
  decide

theorem example_into_proof_and_point :
    (bindChallenge exampleState exampleRound exampleChallenge).bind intoProofAndPoint =
      some ([exampleRound], [exampleChallenge]) := by decide

end Audit.Wire3.GateTerminalBinding
