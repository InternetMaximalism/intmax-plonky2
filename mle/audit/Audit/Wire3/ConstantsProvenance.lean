import Audit.Wire3.GateDerivedRejection
import Audit.Wire3.OpeningBinding

/-!
# Constants provenance: how far PARTIAL SELECTOR ZEROING can be closed (wire v3)

## The attack this module addresses

The adopted `Audit.Wire3.GateRejectionPower` and `Audit.Wire3.GateDerivedRejection`
both record, in their headers, the one attack that survives the eq-table fix:

> PARTIAL SELECTOR ZEROING SURVIVES. … Zeroing the filters on the rows that
> matter while leaving some gate active elsewhere satisfies `activeFilter` and is
> NOT excluded.  Excluding it is a CONSTANTS-PROVENANCE obligation (the constants
> columns must be the committed preprocessed columns), part of the open
> extraction join.

The mechanism is exact and is already adopted Lean: `GatesComplete.contribution`
short-circuits to `some zero` whenever `Gates.computeFilter` returns zero, and
that filter is computed from `Gates.readValue constants g.selectorIndex` — an
entry of the SUPPLIED CONSTANTS COLUMNS (`GateRejectionPower.rowFilter`,
`GateSlotCommutation.rowFilter`).  §10 below exhibits a validated,
constraint-positive, eq-provenanced, `activeFilter`-satisfying state carrying a
FALSE witness whose every row's gate aggregate is nevertheless zero.

## THE CHAIN, LINK BY LINK, AND THE STATUS OF EACH LINK

Read `A ← B` as "A is determined by B".

| # | link | status |
|---|---|---|
| L1 | selector values ← constants columns | **PROVED HERE** (`rowFilter_reads_one_constants_entry`, `rowFilter_depends_only_on_constants`, `selector_index_inside_constants`) |
| L2 | constants columns ← fully bound cells `k.constants` | **PROVED HERE** (`bindAll_tables`, `bindAlong_constants`, `constants_cells_are_bound_columns`, `constants_column_bound_cell`) from the adopted `GateDerivedRejection.EqCellBinding` |
| L3 | `k.constants` ← `p.used.gatePreprocessed.take numConstants` | **ADOPTED, definitional** (`GateTerminalBinding.CellsMatchClaims`, adopted gate assumption 6) — re-expressed with `get?` reads in `constants_cell_is_a_gate_preprocessed_claim` |
| L4 | `gatePreprocessed` claims ← fully bound cells of the COMMITTED preprocessed columns | **PROVED HERE** (`gate_preprocessed_claims_are_committed_cells`, `committed_column_claim`) from the adopted `OpeningBinding.OpensCommittedTable` at bound cell `3` |
| L5 | that group is opened under the PREPROCESSED root | **PROVED HERE** (`gate_preprocessed_is_cell_three`, `preprocessed_group_is_the_pinned_root`, `accepted_whir_binds_the_pinned_root`) |
| L6 | the preprocessed root is PINNED | **PROVED HERE** from adopted acceptance (`accepted_root_is_pinned`, `wrong_root_never_accepted`) |
| R1 | the outer engine's WHIR observation ↔ a concrete `WhirRows`/`Merkle` execution | **NOT PROVABLE IN THIS MODEL** — adopted `OpeningBinding.blind_engine_accepts_every_context` |
| R2 | the opening relation itself (`OpensCommittedTable`) | **VISIBLE HYPOTHESIS** — adopted `OpeningBinding` residue R2 |
| R3 | a map `Verifier.Root → columns` | **VISIBLE HYPOTHESIS** (`ConstantsColumnsOfRoot`) — adopted `OpeningBinding` residue R3 |
| R4 | fold-level agreement ⇒ column identification | **FALSE in general**, proved so here (`bound_cell_agreement_is_not_column_equality`); kept as `SuppliedConstantsAreCommitted` |

L1-L6 compose into `forged_constants_cell_is_the_committed_cell`, which is the
strongest unconditional statement available: at every constants index below
`numConstants`, the SUPPLIED column and the column the PINNED commitment covers
have THE SAME FULLY BOUND CELL at the verifier's own derived gate point.

## HOW THE PREPROCESSED ROOT IS PINNED — THE KEY SOURCE FACT

IT IS NOT A FREE PROOF FIELD.  It is a proof field COMPARED AGAINST A DEPLOYMENT
CONSTANT, on both implementations, and the adopted Lean model already carries the
comparison:

* `Verifier.Pinned` (Verifier.lean 107-110) has the field `preprocessedRoot`,
  alongside `chainId` and `configDigest`.
* `Verifier.shape` (Verifier.lean 134-144) contains the conjunct
  `p.preprocessedRoot = pin.preprocessedRoot`, and `Verifier.verify`
  (Verifier.lean 415) rejects with `.invalidProof` when `shape` is false
  (`verifyCall` in the same file checks `shape` as well, so both entry points
  pin the root).  The
  adopted `Verifier.acceptance_protocol_and_pinned_root` (Verifier.lean 479-484)
  therefore already proves it from acceptance; `accepted_root_is_pinned` below
  pulls it through the `Integrated.verify` wrapper.
* Rust `verifier_v2.rs` 184-187: `ensure!(proof.preprocessed_root ==
  vk.preprocessed_commitment_root, "v2 preprocessed root is not VK-bound")`.
* Solidity `MleVerifierV2.sol` 76 (`bytes32 public immutable
  preprocessedCommitmentRoot`), 130/179 (constructor parameter, assigned once,
  rejected if `bytes32(0)`), 563 (`if (proof.preprocessedRoot !=
  preprocessedCommitmentRoot) revert InvalidMleProof();`).  There is no update
  path.
* Where the pinned value comes from: `prover_v2.rs` 240-241 builds the
  preprocessed group as `preprocessed_mles(constants, sigmas)` from
  `prover_data.constant_evals` — the CIRCUIT's constants, at key generation — and
  275 stores `preprocessed_commitment_root: committed.roots[0]` in the VK.  A
  per-proof prover recomputes the same group from `tables.constant_values`
  (`prover_v2.rs` 345, 405-409); a different constants table gives a different
  root and is rejected at 184-187.

So the constants columns are NOT prover-chosen data in the source.  What the
adopted MODEL cannot yet do is get from "the root is pinned" to "the columns are
these": that is R1/R2/R3 above, and it is the same wall the adopted
`OpeningBinding` hits on the norm lane.

## THE ATTACK THEOREM (§7)

`partial_zeroing_forces_one_of_three`.  Whenever a supplied constants column's
fully bound cell at the derived gate point differs from that of the column the
PINNED root's commitment covers, at least one of these holds:

* **(C)** `p.preprocessedRoot ≠ pin.preprocessedRoot` — closed by the pin,
  `wrong_root_never_accepted`;
* **(A)** `¬ GateTerminalBinding.CellsMatchClaims` — the extraction join rejects;
* **(B)** `¬ OpeningBinding.OpensCommittedTable` — the preprocessed root is
  opened to different cells at bound cell `3`.

`accepted_partial_zeroing_forces_join_or_opening` removes (C) under acceptance.
Branch (B) is given teeth at the concrete opening level by
`preprocessed_rows_bind_or_collision` / `preprocessed_rows_bind_under_no_collision`,
which STRENGTHEN the adopted
`OpeningBinding.accepted_groups_position_rows_bind_or_collision`: that theorem
needs the two blocks to open the SAME THREE-ROOT LIST, whereas two proofs against
one deployment share only the PREPROCESSED position — the witness and
norm-inverse roots are free.  Here only `roots.get? 0 = otherRoots.get? 0` is
required.

NOTHING MORE IS CLAIMED.  The disjunction has exactly three branches and is not a
proof that partial selector zeroing is impossible.

## WHAT IS NOT PROVED

* **THE RESIDUE IS FOLD-LEVEL, NOT COLUMN-LEVEL.**  The chain pins ONE linear
  functional of each constants column.  `bound_cell_agreement_is_not_column_equality`
  exhibits two different columns with the same bound cell, so a forger whose
  selector edit is invisible at the derived gate point falsifies the hypothesis of
  the attack theorem.  Excluding that needs a zero check over the gate point,
  which is a SUMCHECK challenge; no such argument is attempted here and none of
  the adopted bad-set machinery is composed with it.
* **R1.**  Nothing connects `Verifier.Engine.parseWhir` / `whirTail` to
  `WhirRows.openGroups` or `Merkle.verify`; the adopted
  `blind_engine_accepts_every_context` exhibits an engine accepting every context.
  §7's concrete binding theorems therefore do not yet reach the outer chain.
* **R2/R3.**  `OpensCommittedTable` and `ConstantsColumnsOfRoot` are visible
  hypotheses.  The adopted `opening_relation_ignores_the_commitment` and
  `example_two_committed_tables_open_the_same_proof` show R3 cannot be obtained
  from binding.
* **`activeFilter` IS NOT DERIVED.**  §9 shows it becomes a DEPLOYMENT property
  under `SuppliedConstantsAreCommitted` (`activeFilter_is_a_deployment_property`),
  which is the residue, not a discharge.
* **NO PROBABILITY, NO FIAT--SHAMIR, NO WHIR SOUNDNESS.**  `NoCollision` is
  deterministic injectivity on an execution-computed finite list, exactly as
  adopted.  Nothing here says a root, a challenge or a hash is unpredictable.
* **CIRCUIT TRUTH, sumcheck soundness, PCS extractability, Rust/EVM refinement,
  gas and the WHIR profile** are all outside, as in the adopted modules.
* `partial_zeroing_forces_one_of_three` is CONDITIONAL in the same way the
  adopted gate theorems are; no assumption set is shown inhabited.

Tactic note, inherited: `simp`/`ring`/`norm_num` must never see
`Fintype.card Element`; nothing below mentions it.  No tuple `Finset` is
instantiated at a literal arity and no lambda over `alphaBadSet` appears.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Audit.Wire3.ConstantsProvenance

open Audit.Wire3 GoldilocksExt3Field
open Audit.Wire3.GateSuffixPolynomial (Tables)
open Audit.Wire3.GateTerminalBinding (ProverState Cells)

/-! ## 0. Totalisation-free list reads -/

theorem getD_of_get {α : Type} : ∀ (l : List α) (n : Nat) (d a : α),
    l.get? n = some a → l.getD n d = a
  | [], _, _, _, h => by simp at h
  | x :: _, 0, _, _, h => by simpa using h
  | _ :: xs, n + 1, d, a, h => getD_of_get xs n d a h

theorem get_map {α β : Type} (f : α → β) : ∀ (l : List α) (n : Nat),
    (l.map f).get? n = (l.get? n).map f
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => get_map f xs n

theorem get_of_map_eq {α β : Type} (f : α → β) (l : List α) (m : List β) (n : Nat) (a : α)
    (hm : l.map f = m) (h : l.get? n = some a) : m.get? n = some (f a) := by
  rw [← hm, get_map, h]
  rfl

theorem get_of_eq_map {α β : Type} (f : α → β) (l : List α) (m : List β) (n : Nat) (b : β)
    (hm : l.map f = m) (h : m.get? n = some b) : ∃ a, l.get? n = some a ∧ f a = b := by
  rw [← hm, get_map] at h
  cases hl : l.get? n with
  | none => rw [hl] at h; simp at h
  | some a => rw [hl] at h; exact ⟨a, rfl, by simpa using h⟩

/-! ## 1. THE PIN -/

/-- The preprocessed root a proof carries is NOT a free field: `Verifier.shape`
compares it with the DEPLOYMENT-pinned `Verifier.Pinned.preprocessedRoot`.  This
is `Verifier.acceptance_protocol_and_pinned_root` pulled through the adopted
`Integrated.verify` wrapper. -/
theorem accepted_root_is_pinned (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (vc : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ()) :
    p.preprocessedRoot = pin.preprocessedRoot := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier e decode pin
    chain vc p hacc
  exact (Verifier.acceptance_protocol_and_pinned_root (Integrated.modelEngine e decode) pin chain
    vc p hv).2

/-- THE ROOT BRANCH IS CLOSED.  A supplier who presents any preprocessed root
other than the pinned one is rejected. -/
theorem wrong_root_never_accepted (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (vc : Verifier.Config) (p : Verifier.Proof)
    (h : p.preprocessedRoot ≠ pin.preprocessedRoot) :
    Integrated.verify e decode pin chain vc p ≠ .ok () :=
  fun hacc => h (accepted_root_is_pinned e decode pin chain vc p hacc)

/-- The WHIR context's root list of an accepting run BEGINS with the pinned
preprocessed root, in both copies the parse produces. -/
theorem accepted_whir_binds_the_pinned_root (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (vc : Verifier.Config) (p : Verifier.Proof)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ()) :
    ∃ parsed,
      (Integrated.modelEngine e decode).parseWhir
          (Verifier.derivedContext (Integrated.modelEngine e decode) vc p)
          p.whirTranscript p.whirHints = some parsed ∧
      parsed.actualRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] ∧
      parsed.boundRoots = [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot] := by
  obtain ⟨_, _, _, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier e decode pin
    chain vc p hacc
  obtain ⟨parsed, hp, ha, hb, _, _, _, _⟩ :=
    Verifier.acceptance_exact_whir_and_terminal_binding (Integrated.modelEngine e decode) pin chain
      vc p hv
  exact ⟨parsed, hp, ha, hb⟩

/-- The gate lane's PREPROCESSED group sits at root-list position
`OpenedClaimFold.groupPreprocessed = 0`, i.e. at the pinned root. -/
theorem preprocessed_group_is_the_pinned_root (pin : Verifier.Pinned) (p : Verifier.Proof) :
    ([pin.preprocessedRoot, p.witnessRoot,
      p.normInverseRoot]).get? OpenedClaimFold.groupPreprocessed = some pin.preprocessedRoot :=
  rfl

/-- The proof's `gatePreprocessed` claims are bound cell `3`, which is the
PREPROCESSED group at the GATE point, with row point `s.gatePoint`.  Rust slot
`POINT_GATE_V2 * NUM_PCS_GROUPS_V2 + GROUP_PREPROCESSED_V2 = 3`. -/
theorem gate_preprocessed_is_cell_three (u : Verifier.UsedClaims) (idx : Verifier.IndexPoints)
    (s : Verifier.RoundState) :
    OpenedClaimFold.boundCell u idx 3 = (u.gatePreprocessed, idx.gate) ∧
    OpenedClaimFold.cellRow s 3 = s.gatePoint ∧
    OpenedClaimFold.cellGroup 3 = OpenedClaimFold.groupPreprocessed ∧
    OpenedClaimFold.cellPoint 3 = OpenedClaimFold.pointGate ∧
    OpenedClaimFold.rustSlot OpenedClaimFold.pointGate OpenedClaimFold.groupPreprocessed = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. LINK 1: the selector values ARE entries of the constants columns -/

/-- LINK 1, WITH SOURCE BOUNDS AND NO DEFAULT READ.  The filter the adopted
`GatesComplete.contribution` computes for gate `g` at Boolean row `i` — the
adopted `GateRejectionPower.rowFilter` — is `Gates.computeFilter` applied to the
entry at row `i` of the constants column at index `g.selectorIndex`.  Both reads
are supplied as `get?` successes, so no `getD`/zero default stands in for a
source bound. -/
theorem rowFilter_reads_one_constants_entry (c : Gates.Config) (g : Gates.GateInfo)
    (t : Tables) (i : Nat) (col : List Element) (v : Element)
    (hcol : t.constants.get? g.selectorIndex = some col) (hv : col.get? i = some v) :
    GateRejectionPower.rowFilter c g t i
      = Gates.computeFilter g v.toVerifier (decide (1 < c.numSelectors)) := by
  unfold GateRejectionPower.rowFilter Gates.readValue
  rw [getD_of_get (t.constants.map (fun column => (column.getD i 0).toVerifier)) g.selectorIndex
    Verifier.zero ((col.getD i 0).toVerifier)
    (get_of_map_eq (fun column : List Element => (column.getD i 0).toVerifier) t.constants _
      g.selectorIndex col rfl hcol),
    getD_of_get col i 0 v hv]

/-- LINK 1, DEPENDENCE FORM.  The filters read the CONSTANTS columns and nothing
else: two supplied table families with the same constants columns have the same
filter at every gate and every row, whatever their wire and eq columns are. -/
theorem rowFilter_depends_only_on_constants (c : Gates.Config) (g : Gates.GateInfo)
    (t u : Tables) (h : t.constants = u.constants) (i : Nat) :
    GateRejectionPower.rowFilter c g t i = GateRejectionPower.rowFilter c g u i := by
  unfold GateRejectionPower.rowFilter
  rw [h]

/-- The selector column index of every configured gate is inside the constants
columns of a `Consistent` supplied state: `validateGate` gives
`selectorIndex < numSelectors` (Gates.lean:95) and the adopted
`Verifier.envelope` gives `numSelectors ≤ numConstants` (Verifier.lean:100). -/
theorem selector_index_inside_constants (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (vc : Verifier.Config) (p : Verifier.Proof)
    (gates : List Gates.GateInfo) (s0 : ProverState) (n : Nat) (g : Gates.GateInfo)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hd : decode vc.gatesEncoding = some gates)
    (hcons : GateDenseRound.Consistent (Integrated.gateConfig vc) s0)
    (hg : gates.get? n = some g) :
    g.selectorIndex < s0.tables.constants.length := by
  obtain ⟨_, _, hv⟩ := Integrated.accepted_preflights_and_original_verifier e decode pin chain vc p hacc
  have henv := (Verifier.verify_success_checks (Integrated.modelEngine e decode) pin chain vc p
    hv.2.2).2.2.1
  simp only [Verifier.envelope, decide_eq_true_eq] at henv
  have hvalid := GateClaimChain.accepted_gate_configuration_valid e decode pin chain vc p gates hacc hd
  obtain ⟨r, hvg, _⟩ := Gates.every_configured_gate_checked (Integrated.gateConfig vc) gates hvalid n g hg
  have hloc := (Gates.validate_gate_success (Integrated.gateConfig vc) n gates.length g r hvg).2.1
  have hlen : s0.tables.constants.length = vc.numConstants := by
    show (s0.constants.map DenseMleIndexed.State.evaluations).length = _
    rw [List.length_map]
    exact hcons.1.2.1
  have hsel : g.selectorIndex < vc.numSelectors := hloc.2.1
  have hle : vc.numSelectors ≤ vc.numConstants := henv.2.2.2.2.2.2.2.2.1
  rw [hlen]
  exact Nat.lt_of_lt_of_le hsel hle

/-! ## 3. LINK 2: the constants columns' FULLY BOUND CELLS are the cell tuple `k` -/

/-- Iterated `GateTerminalBinding.bindTables`, the table-level form of the gate
prover's `bind_challenge` loop. -/
def bindAlong : Tables → List Element → Tables
  | t, [] => t
  | t, x :: xs => bindAlong (GateTerminalBinding.bindTables t x) xs

theorem map_bindColumn_nil (cols : List (List Element)) :
    cols.map (fun col => NormTerminalBinding.bindColumn col []) = cols := by
  induction cols with
  | nil => rfl
  | cons a as ih =>
      show a :: as.map (fun col => NormTerminalBinding.bindColumn col []) = a :: as
      rw [ih]

/-- Column-wise form: after binding a whole challenge list, every constants
column is the adopted `NormTerminalBinding.bindColumn` of the original column at
that list. -/
theorem bindAlong_constants : ∀ (xs : List Element) (t : Tables),
    (bindAlong t xs).constants
      = t.constants.map (fun col => NormTerminalBinding.bindColumn col xs)
  | [], t => (map_bindColumn_nil t.constants).symm
  | x :: xs, t => by
      show (bindAlong (GateTerminalBinding.bindTables t x) xs).constants = _
      rw [bindAlong_constants xs (GateTerminalBinding.bindTables t x)]
      show (t.constants.map (fun col => DenseMleIndexed.bindBuffer col x)).map
          (fun col => NormTerminalBinding.bindColumn col xs) = _
      rw [List.map_map]
      exact List.map_congr_left (fun col _ =>
        (NormTerminalBinding.bind_column_cons col x xs).symm)

/-- The adopted `GateTerminalBinding.bindAll` moves the tables exactly along the
challenge list it consumes. -/
theorem bindAll_tables : ∀ (steps : List (List Verifier.Ext3 × Element)) (s t : ProverState),
    GateTerminalBinding.bindAll s steps = some t →
    t.tables = bindAlong s.tables (steps.map Prod.snd)
  | [], s, t, h => by
      have : t = s := (Option.some.inj h).symm
      rw [this]
      rfl
  | step :: rest, s, t, h => by
      unfold GateTerminalBinding.bindAll at h
      cases hb : GateTerminalBinding.bindChallenge s step.1 step.2 with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some next =>
          rw [hb] at h
          simp only [Option.bind_eq_bind, Option.some_bind] at h
          rw [bindAll_tables rest next t h,
            GateTerminalBinding.bind_challenge_tables s next step.1 step.2 hb]
          rfl

/-- The verifier's derived gate point, as the adopted `TranscriptProvenance`
column and as the adopted `OpenedClaimFold` lift, is the SAME list. -/
theorem gatePointColumn_is_lift (e : Verifier.Engine) (vc : Verifier.Config) (p : Verifier.Proof) :
    TranscriptProvenance.gatePointColumn e vc p
      = OpenedClaimFold.lift (Verifier.derivedRounds e vc p).gatePoint := rfl

/-- LINK 2.  Under the adopted `GateDerivedRejection.EqCellBinding` — the binding
data of the reduced gate assumption list — the cell tuple `k` is exactly the
supplied state bound along the VERIFIER'S OWN derived gate point, so every
constants column's fully bound cell is the corresponding entry of `k.constants`. -/
theorem constants_cells_are_bound_columns (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (s0 : ProverState) (k : Cells)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k) :
    k.constants.map (fun v => [v])
      = s0.tables.constants.map
          (fun col => NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p)) := by
  obtain ⟨t, steps, _, hb, hkt, hpoint⟩ := hbind
  have h : k.tables = bindAlong s0.tables (TranscriptProvenance.gatePointColumn e vc p) := by
    rw [← hkt, bindAll_tables steps s0 t hb, hpoint]
  have := congrArg Tables.constants h
  rw [bindAlong_constants] at this
  exact this

/-- LINK 2, at one column, with `get?` reads only. -/
theorem constants_column_bound_cell (e : Verifier.Engine) (vc : Verifier.Config)
    (p : Verifier.Proof) (s0 : ProverState) (k : Cells) (j : Nat) (col : List Element)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcol : s0.tables.constants.get? j = some col) :
    ∃ v, k.constants.get? j = some v ∧
      NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p) = [v] := by
  obtain ⟨v, hv, hvv⟩ := get_of_eq_map (fun v : Element => [v]) k.constants _ j
    (NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p))
    (constants_cells_are_bound_columns e vc p s0 k hbind)
    (get_of_map_eq
      (fun col : List Element =>
        NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p))
      s0.tables.constants _ j col rfl hcol)
  exact ⟨v, hv, hvv.symm⟩

/-! ## 4. LINK 3: the cells ARE the proof's `gatePreprocessed.take numConstants` -/

theorem get_take {α : Type} : ∀ (n : Nat) (l : List α) (j : Nat), j < n →
    (List.take n l).get? j = l.get? j
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, 0, _ => rfl
  | n + 1, _ :: xs, j + 1, h => get_take n xs j (Nat.lt_of_succ_lt_succ h)

/-- LINK 3.  The adopted `GateTerminalBinding.CellsMatchClaims` (adopted gate
assumption 6) says exactly that the constants cells are the first `numConstants`
gate-preprocessed claims (`Verifier.gateTerminal` line 398 /
`MleVerifierV2.sol` 378-381 / `verifier_v2.rs` 426-427). -/
theorem constants_cell_is_a_gate_preprocessed_claim (vc : Verifier.Config) (p : Verifier.Proof)
    (k : Cells) (j : Nat) (v : Element)
    (hk : GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p))
    (hv : k.constants.get? j = some v) :
    (p.used.gatePreprocessed.take vc.numConstants).get? j = some v.toVerifier :=
  get_of_map_eq Element.toVerifier k.constants _ j v hk.2 hv

/-- LINKS 1-3 COMPOSED.  The selector value the gate lane reads at row `i` is an
entry of a constants column whose FULLY BOUND CELL (at the verifier's own derived
gate point) is the corresponding entry of `p.used.gatePreprocessed.take
numConstants`. -/
theorem selector_source_is_a_claimed_constants_column (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (s0 : ProverState) (k : Cells)
    (g : Gates.GateInfo) (i : Nat) (col : List Element) (v : Element)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hk : GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p))
    (hcol : s0.tables.constants.get? g.selectorIndex = some col)
    (hv : col.get? i = some v) :
    GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i
        = Gates.computeFilter g v.toVerifier (decide (1 < vc.numSelectors)) ∧
      ∃ cell, NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p)
            = [cell] ∧
        (p.used.gatePreprocessed.take vc.numConstants).get? g.selectorIndex
          = some cell.toVerifier := by
  obtain ⟨cell, hcell, hbc⟩ := constants_column_bound_cell e vc p s0 k g.selectorIndex col hbind hcol
  exact ⟨rowFilter_reads_one_constants_entry (Integrated.gateConfig vc) g s0.tables i col v hcol hv,
    cell, hbc, constants_cell_is_a_gate_preprocessed_claim vc p k g.selectorIndex cell hk hcell⟩

/-! ## 5. LINK 4: the claims are the fully bound cells of the COMMITTED columns -/

/-- LINK 4.  Under the adopted opening relation `OpeningBinding.OpensCommittedTable`
(= `IntegratedTerminalChain.HonestOpenings`), the proof's `gatePreprocessed`
claims — bound cell `3`, the PREPROCESSED group at the GATE point — are the
fully bound cells of the columns that group's commitment covers.  This is the
adopted `OpeningBinding.opened_cells_are_bound_cells` at `i = 3`; the log-point
instance at `i = 0` is the adopted
`norm_claims_from_openings_and_column_identification`. -/
theorem gate_preprocessed_claims_are_committed_cells (vc : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (cols : Fin 5 → List (List Element))
    (hyp : OpeningBinding.OpensCommittedTable vc p s idx cols) :
    p.used.gatePreprocessed = NormTerminalBinding.cellValues
      ((cols 3).map (fun col =>
        NormTerminalBinding.bindColumn col (OpenedClaimFold.lift s.gatePoint))) := by
  have hlen : (OpenedClaimFold.lift s.gatePoint).length = s.gatePoint.length := List.length_map _ _
  exact OpeningBinding.opened_cells_are_bound_cells p.used.gatePreprocessed (cols 3)
    (OpenedClaimFold.lift s.gatePoint)
    (by show ∀ col ∈ cols 3, col.length = 2 ^ (OpenedClaimFold.lift s.gatePoint).length
        rw [hlen]
        exact hyp.full 3)
    (hyp.opened 3)

/-- LINK 4, at one committed column, with `get?` reads only. -/
theorem committed_column_claim (vc : Verifier.Config) (p : Verifier.Proof)
    (s : Verifier.RoundState) (idx : Verifier.IndexPoints) (cols : Fin 5 → List (List Element))
    (j : Nat) (committedCol : List Element)
    (hyp : OpeningBinding.OpensCommittedTable vc p s idx cols)
    (hcc : (cols 3).get? j = some committedCol) :
    p.used.gatePreprocessed.get? j =
      some (NormTerminalBinding.cell
        (NormTerminalBinding.bindColumn committedCol (OpenedClaimFold.lift s.gatePoint))).toVerifier := by
  rw [gate_preprocessed_claims_are_committed_cells vc p s idx cols hyp]
  show ((((cols 3).map (fun col =>
      NormTerminalBinding.bindColumn col (OpenedClaimFold.lift s.gatePoint))).map
        NormTerminalBinding.cell).map Element.toVerifier).get? j = _
  rw [get_map, get_map, get_map, hcc]
  rfl

/-! ## 6. THE CHAIN, COMPOSED -/

/-- **THE CONSTANTS-PROVENANCE CHAIN.**  For every constants column index `j`
below `numConstants`: the supplied (extracted) constants column and the column
the PINNED preprocessed commitment covers have THE SAME FULLY BOUND CELL at the
verifier's own derived gate point.

Read with `selector_source_is_a_claimed_constants_column`: the selector value a
gate reads at a row is an entry of a supplied constants column, and that
column's bound cell is forced to agree with the committed column's bound cell.

WHAT THIS IS NOT: it is a FOLD-level identity, exactly as the adopted
`OpeningBinding` section 7 records for the norm lane.  It does NOT say the two
columns are equal; see `bound_cell_agreement_is_not_column_equality`. -/
theorem forged_constants_cell_is_the_committed_cell (e : Verifier.Engine)
    (vc : Verifier.Config) (p : Verifier.Proof) (s0 : ProverState) (k : Cells)
    (cols : Fin 5 → List (List Element)) (j : Nat) (col committedCol : List Element)
    (hj : j < vc.numConstants)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hk : GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p))
    (hyp : OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
      (Verifier.derivedIndices e vc p) cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (cols 3).get? j = some committedCol) :
    NormTerminalBinding.cell
        (NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p))
      = NormTerminalBinding.cell
        (NormTerminalBinding.bindColumn committedCol (TranscriptProvenance.gatePointColumn e vc p)) := by
  obtain ⟨v, hv, hbc⟩ := constants_column_bound_cell e vc p s0 k j col hbind hcol
  have hclaim : p.used.gatePreprocessed.get? j = some v.toVerifier := by
    rw [← get_take vc.numConstants p.used.gatePreprocessed j hj]
    exact constants_cell_is_a_gate_preprocessed_claim vc p k j v hk hv
  have hcommitted := committed_column_claim vc p (Verifier.derivedRounds e vc p)
    (Verifier.derivedIndices e vc p) cols j committedCol hyp hcc
  rw [gatePointColumn_is_lift] at hbc ⊢
  rw [hbc]
  refine GoldilocksExt3Field.element_eq _ _ ?_
  have := hclaim.symm.trans hcommitted
  exact (Option.some.inj this)

/-! ## 7. THE ATTACK THEOREM -/

/-- THE ROOT-TO-COLUMNS MAP, A NAMED VISIBLE HYPOTHESIS.  The adopted audit has
NO map from a `Verifier.Root` to a column list — that is residue R3 of the
adopted `OpeningBinding`, and `OpeningBinding.opening_relation_ignores_the_commitment`
plus `example_two_committed_tables_open_the_same_proof` show why it cannot be
manufactured from binding.  `committedBy` is that map, supplied from outside;
this predicate says only that the columns the gate lane's PREPROCESSED group
(bound cell `3`) opens are the ones THIS proof's preprocessed root names.

NOT PROVED HERE and not provable in this model. -/
def ConstantsColumnsOfRoot (committedBy : Verifier.Root → List (List Element))
    (p : Verifier.Proof) (cols : Fin 5 → List (List Element)) : Prop :=
  cols 3 = committedBy p.preprocessedRoot

/-- **THE ATTACK THEOREM.  A partial-selector-zeroing supplier must break one of
exactly three things.**

The hypothesis is the sharp form of "the forged constants column is not the
committed one": at some constants index `j < numConstants`, the supplied column's
FULLY BOUND CELL at the verifier's derived gate point differs from the bound cell
of the column that the PINNED root's commitment covers.  Then at least one of

* (C) the proof's preprocessed root is NOT the pinned one — killed outright by
  `wrong_root_never_accepted`;
* (A) the extraction join fails: the supplied cells are not the accepted
  `gatePreprocessed.take numConstants` claims (adopted gate assumption 6
  `CellsMatchClaims`);
* (B) the opening relation fails at bound cell `3`: the accepted claims are not
  the folds of the committed preprocessed columns at the gate point.

NOTHING MORE IS CLAIMED.  In particular this is NOT a proof that partial selector
zeroing is impossible: a forged column whose bound cell HAPPENS to equal the
committed column's bound cell falsifies the hypothesis, and section 8 shows such
columns exist. -/
theorem partial_zeroing_forces_one_of_three (e : Verifier.Engine) (pin : Verifier.Pinned)
    (vc : Verifier.Config) (p : Verifier.Proof) (s0 : ProverState) (k : Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (hdiff : NormTerminalBinding.cell
        (NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p))
      ≠ NormTerminalBinding.cell
        (NormTerminalBinding.bindColumn committedCol
          (TranscriptProvenance.gatePointColumn e vc p))) :
    p.preprocessedRoot ≠ pin.preprocessedRoot ∨
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hroot, hk, hyp⟩ := hcon
  refine hdiff (forged_constants_cell_is_the_committed_cell e vc p s0 k cols j col committedCol hj
    hbind hk hyp hcol ?_)
  rw [hcols, hroot]
  exact hcc

/-- **THE ATTACK THEOREM UNDER ACCEPTANCE.**  Branch (C) is closed by the pin, so
an ACCEPTED partial-zeroing proof must break the extraction join or the opening
relation.  Two branches remain, and both are named residues of the adopted
audit. -/
theorem accepted_partial_zeroing_forces_join_or_opening (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (pin : Verifier.Pinned) (chain : Nat)
    (vc : Verifier.Config) (p : Verifier.Proof) (s0 : ProverState) (k : Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (j : Nat) (col committedCol : List Element) (hj : j < vc.numConstants)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hbind : GateDerivedRejection.EqCellBinding e vc p s0 k)
    (hcols : ConstantsColumnsOfRoot committedBy p cols)
    (hcol : s0.tables.constants.get? j = some col)
    (hcc : (committedBy pin.preprocessedRoot).get? j = some committedCol)
    (hdiff : NormTerminalBinding.cell
        (NormTerminalBinding.bindColumn col (TranscriptProvenance.gatePointColumn e vc p))
      ≠ NormTerminalBinding.cell
        (NormTerminalBinding.bindColumn committedCol
          (TranscriptProvenance.gatePointColumn e vc p))) :
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  rcases partial_zeroing_forces_one_of_three e pin vc p s0 k cols committedBy j col committedCol
    hj hbind hcols hcol hcc hdiff with hroot | hrest
  · exact absurd (accepted_root_is_pinned e decode pin chain vc p hacc) hroot
  · exact hrest

/-! ### Branch (B) at the concrete opening level -/

/-- **TWO OPENINGS OF THE PINNED PREPROCESSED ROOT BIND OR COLLIDE.**  This
STRENGTHENS the adopted `OpeningBinding.accepted_groups_position_rows_bind_or_collision`,
which requires the two blocks to open the SAME root list: here only the
PREPROCESSED position (group `0`) carries the same root — which is exactly what
the deployment pin guarantees across two different proofs, whose witness and
norm-inverse roots are free.  Same index, same depth: the returned raw rows agree
or a concrete unequal pair of actual hash inputs is exhibited.  No injectivity
and no probability is used. -/
theorem preprocessed_rows_bind_or_collision (hash : Spongefish.Hash) (depth index : Nat)
    (indices otherIndices : List Nat) (layout otherLayout : WhirRows.Layout)
    (hints otherHints : Spongefish.Bytes) (roots otherRoots : List Spongefish.Digest) (preRoot : Spongefish.Digest)
    (s t otherS otherT : Spongefish.State) (groups otherGroups : List (List WhirRows.RawRow))
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (h : WhirRows.openGroups hash depth indices layout hints roots s = some (groups, t))
    (h' : WhirRows.openGroups hash depth otherIndices otherLayout otherHints otherRoots otherS
      = some (otherGroups, otherT))
    (hr : roots.get? OpenedClaimFold.groupPreprocessed = some preRoot)
    (hr' : otherRoots.get? OpenedClaimFold.groupPreprocessed = some preRoot)
    (hg : groups.get? OpenedClaimFold.groupPreprocessed = some rows)
    (hg' : otherGroups.get? OpenedClaimFold.groupPreprocessed = some otherRows)
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows) :
    row.bytes = otherRow.bytes ∨ WhirRowBinding.RowCollision hash row.bytes otherRow.bytes := by
  obtain ⟨rows2, before, after, hi, ho, _⟩ := OpeningBinding.groups_position_inputs_recorded hash
    depth indices layout hints roots s t groups OpenedClaimFold.groupPreprocessed preRoot h hr
  obtain ⟨others2, before2, after2, hi2, ho2, _⟩ := OpeningBinding.groups_position_inputs_recorded
    hash depth otherIndices otherLayout otherHints otherRoots otherS otherT otherGroups
    OpenedClaimFold.groupPreprocessed preRoot h' hr'
  rw [Option.some.inj (hi.symm.trans hg)] at ho
  rw [Option.some.inj (hi2.symm.trans hg')] at ho2
  exact WhirRowBinding.accepted_raw_rows_bind_or_collision hash preRoot depth index indices
    otherIndices layout otherLayout hints otherHints before after before2 after2 rows otherRows
    row otherRow ho ho2 hm hm'

/-- The same, with the collision alternative REMOVED by the adopted
execution-bound `OpeningBinding.NoCollision`: injectivity of `hash` on the finite
list of byte strings THESE TWO EXECUTIONS actually hash. -/
theorem preprocessed_rows_bind_under_no_collision (hash : Spongefish.Hash) (depth index : Nat)
    (indices otherIndices : List Nat) (layout otherLayout : WhirRows.Layout)
    (hints otherHints : Spongefish.Bytes) (roots otherRoots : List Spongefish.Digest) (preRoot : Spongefish.Digest)
    (s t otherS otherT : Spongefish.State) (groups otherGroups : List (List WhirRows.RawRow))
    (rows otherRows : List WhirRows.RawRow) (row otherRow : WhirRows.RawRow)
    (h : WhirRows.openGroups hash depth indices layout hints roots s = some (groups, t))
    (h' : WhirRows.openGroups hash depth otherIndices otherLayout otherHints otherRoots otherS
      = some (otherGroups, otherT))
    (hr : roots.get? OpenedClaimFold.groupPreprocessed = some preRoot)
    (hr' : otherRoots.get? OpenedClaimFold.groupPreprocessed = some preRoot)
    (hg : groups.get? OpenedClaimFold.groupPreprocessed = some rows)
    (hg' : otherGroups.get? OpenedClaimFold.groupPreprocessed = some otherRows)
    (hm : (index, row) ∈ indices.zip rows) (hm' : (index, otherRow) ∈ otherIndices.zip otherRows)
    (hno : OpeningBinding.NoCollision hash
      (OpeningBinding.executedGroupsInputs hash depth indices layout hints roots s ++
        OpeningBinding.executedGroupsInputs hash depth otherIndices otherLayout otherHints
          otherRoots otherS)) :
    row.bytes = otherRow.bytes := by
  obtain ⟨rows2, before, after, hi, ho, hsub⟩ := OpeningBinding.groups_position_inputs_recorded hash
    depth indices layout hints roots s t groups OpenedClaimFold.groupPreprocessed preRoot h hr
  obtain ⟨others2, before2, after2, hi2, ho2, hsub2⟩ :=
    OpeningBinding.groups_position_inputs_recorded hash depth otherIndices otherLayout otherHints
      otherRoots otherS otherT otherGroups OpenedClaimFold.groupPreprocessed preRoot h' hr'
  rw [Option.some.inj (hi.symm.trans hg)] at ho
  rw [Option.some.inj (hi2.symm.trans hg')] at ho2
  refine OpeningBinding.accepted_group_rows_bind_under_no_collision hash preRoot depth index
    indices otherIndices layout otherLayout hints otherHints before after before2 after2 rows
    otherRows row otherRow ho ho2 hm hm' (OpeningBinding.noCollision_of_subset hash _ _ ?_ hno)
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (hsub x hx)
  · exact List.mem_append_right _ (hsub2 x hx)

/-! ## 8. THE RESIDUE: fold-level agreement is NOT column identification -/

/-- Two DIFFERENT columns … -/
def residueColumnA : List Element := [5, 3]
/-- … and the column a forger could substitute for it. -/
def residueColumnB : List Element := [9, 3]
/-- A one-variable point. -/
def residuePoint : List Element := [1]

theorem residue_columns_differ : residueColumnA ≠ residueColumnB := by decide

/-- **THE RESIDUE, EXHIBITED.**  The chain of sections 2-6 pins the constants
columns only through ONE linear functional each — the fully bound cell at the
derived gate point.  Two different columns can share that cell, and here two do.
So `forged_constants_cell_is_the_committed_cell` does NOT exclude every partial
selector zeroing: it excludes exactly those whose column change is visible at the
gate point.  This is the same fold-vs-column gap the adopted `OpeningBinding`
section 7 records for the norm lane. -/
theorem residue_columns_share_bound_cell :
    NormTerminalBinding.bindColumn residueColumnA residuePoint
      = NormTerminalBinding.bindColumn residueColumnB residuePoint := by decide

theorem bound_cell_agreement_is_not_column_equality :
    ∃ a b : List Element, ∃ point : List Element,
      a ≠ b ∧ NormTerminalBinding.bindColumn a point = NormTerminalBinding.bindColumn b point :=
  ⟨residueColumnA, residueColumnB, residuePoint, residue_columns_differ,
    residue_columns_share_bound_cell⟩

/-! ## 9. THE STRONGEST ADOPTED GATE THEOREM, WITH THE FILTER GUARDS MOVED TO THE
PINNED COLUMNS -/

/-- The supplied tables with the constants columns REPLACED by the ones the
DEPLOYMENT-PINNED preprocessed root commits to. -/
def pinnedConstantsTables (committedBy : Verifier.Root → List (List Element))
    (pin : Verifier.Pinned) (t : Tables) : Tables :=
  ⟨t.wires, committedBy pin.preprocessedRoot, t.eq⟩

/-- **THE EXACT RESIDUE THAT REMAINS.**  Column identification: the supplied
(extracted) constants columns ARE the columns the pinned commitment covers.  This
is NOT proved anywhere in the adopted audit or here; sections 2-6 prove only its
fold-level shadow, and section 8 shows the shadow is strictly weaker.  It is the
extraction step from binding to a single committed table — adopted residue R3
(`OpeningBinding`: "the adopted audit contains no map from a `Verifier.Root` to a
column list"). -/
def SuppliedConstantsAreCommitted (committedBy : Verifier.Root → List (List Element))
    (pin : Verifier.Pinned) (s0 : ProverState) : Prop :=
  s0.tables.constants = committedBy pin.preprocessedRoot

/-- Under column identification EVERY filter, at EVERY gate and EVERY row — not
merely the bound cell — is a function of the PINNED columns alone. -/
theorem pinned_filters_transfer (committedBy : Verifier.Root → List (List Element))
    (pin : Verifier.Pinned) (s0 : ProverState)
    (hident : SuppliedConstantsAreCommitted committedBy pin s0)
    (c : Gates.Config) (g : Gates.GateInfo) (i : Nat) :
    GateRejectionPower.rowFilter c g s0.tables i
      = GateRejectionPower.rowFilter c g (pinnedConstantsTables committedBy pin s0.tables) i :=
  rowFilter_depends_only_on_constants c g s0.tables
    (pinnedConstantsTables committedBy pin s0.tables)
    (show s0.tables.constants = committedBy pin.preprocessedRoot from hident) i

/-- **`activeFilter` BECOMES A DEPLOYMENT PROPERTY.**  The adopted strong field
S2 is a condition on SUPPLIER-CHOSEN data; under column identification it is
equivalent to the same condition on the pinned commitment's columns, which the
supplier cannot touch. -/
theorem activeFilter_is_a_deployment_property (committedBy : Verifier.Root → List (List Element))
    (pin : Verifier.Pinned) (vc : Verifier.Config) (gates : List Gates.GateInfo)
    (s0 : ProverState) (hident : SuppliedConstantsAreCommitted committedBy pin s0) :
    (∃ i, i < 2 ^ vc.degreeBits ∧ ∃ g ∈ gates,
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g s0.tables i ≠ Verifier.zero) ↔
      (∃ i, i < 2 ^ vc.degreeBits ∧ ∃ g ∈ gates,
        GateRejectionPower.rowFilter (Integrated.gateConfig vc) g
          (pinnedConstantsTables committedBy pin s0.tables) i ≠ Verifier.zero) := by
  constructor
  · rintro ⟨i, hi, g, hg, hne⟩
    exact ⟨i, hi, g, hg, fun h => hne
      ((pinned_filters_transfer committedBy pin s0 hident _ g i).trans h)⟩
  · rintro ⟨i, hi, g, hg, hne⟩
    exact ⟨i, hi, g, hg, fun h => hne
      ((pinned_filters_transfer committedBy pin s0 hident _ g i).symm.trans h)⟩

section Restatement
variable {e : Verifier.Engine} {decode : Integrated.DecodeGates} {vc : Verifier.Config}
  {p : Verifier.Proof} {pre post : List Gates.GateInfo} {g : Gates.GateInfo}
  {s0 sLast : ProverState} {x : Element} {k : Cells} {gateTruths : List (List Element)}

/-- **THE STRONGEST ADOPTED GATE THEOREM, RESTATED THROUGH THE PROVENANCE
LINKS.**  This is the adopted
`GateDerivedRejection.derived_selected_gate_constraints_vanish` with its three
FILTER premises — the selector-zeroing residue, of which `activeFilter` is the
crude form — moved off the supplied tables and onto the columns the
DEPLOYMENT-PINNED preprocessed root commits to.  The conclusion is unchanged:
every constraint of the gate selected at row `i` is zero, and its evaluator
succeeds there.

WHAT CHANGED: nothing about the challenges, the bad sets or the sumcheck.  What
changed is WHO CHOOSES the filters.  In the adopted statement `hpre`, `hpost` and
`hactive` are conditions on `s0.tables`, which the supplier picks; here they are
conditions on `committedBy pin.preprocessedRoot`, which the deployment picks.

THE EXACT RESIDUE: the hypothesis `hident` (`SuppliedConstantsAreCommitted`).
It is the only premise that is NEW relative to the adopted statement; the
statement still carries the adopted `EqCellBinding` inside `D` (residue L2's
binding side), the visible `committedBy` map (R3), and it sits behind R1 like
every theorem in this file.  Sections 2-6 prove the FOLD-LEVEL shadow of `hident`
unconditionally from acceptance plus the adopted join and opening relations; the
step from that shadow to `hident` itself is the extraction step from binding to a
single committed table, and section 8 proves the shadow does not imply it. -/
theorem provenanced_selected_gate_constraints_vanish (hash : TranscriptProvenance.Hash)
    (pin : Verifier.Pinned) (chain : Nat) (committedBy : Verifier.Root → List (List Element))
    (hderiv : TranscriptProvenance.DerivedInitial hash e vc p)
    (D : GateDerivedRejection.DerivedGateAssumptions hash e decode vc p (pre ++ g :: post) s0
      sLast x k gateTruths)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hfree : ConditionalSoundness.BadEventFree 0
      (GateClaimChain.endpointSum (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement hash vc p) s0)
      (ConditionalSoundness.gateLaneOf e vc p gateTruths))
    (hgoodTau : GateDerivedRejection.GoodDerivedTau hash vc p
      (ZeroCheckSemantics.gateValue (Integrated.gateConfig vc) (pre ++ g :: post)
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (TranscriptProvenance.gateAlphaElement hash vc p) s0.tables))
    (i : Nat) (hi : i < 2 ^ vc.degreeBits) (coeffs : List Element)
    (hcoeffs : AlphaZeroCheck.slotCoefficients (Integrated.gateConfig vc) (pre ++ g :: post)
      (AlphaZeroCheck.rowWires s0.tables i) (AlphaZeroCheck.rowConstants s0.tables i)
      (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs)) = some coeffs)
    (hgoodAlpha : GateDerivedRejection.GoodDerivedAlpha hash vc p coeffs)
    (hident : SuppliedConstantsAreCommitted committedBy pin s0)
    (hpre : ∀ g' ∈ pre, GateRejectionPower.rowFilter (Integrated.gateConfig vc) g'
      (pinnedConstantsTables committedBy pin s0.tables) i = Verifier.zero)
    (hpost : ∀ g' ∈ post, GateRejectionPower.rowFilter (Integrated.gateConfig vc) g'
      (pinnedConstantsTables committedBy pin s0.tables) i = Verifier.zero)
    (hactive : GateRejectionPower.rowFilter (Integrated.gateConfig vc) g
      (pinnedConstantsTables committedBy pin s0.tables) i ≠ Verifier.zero) :
    ∃ terms, GatesComplete.evaluateUnfiltered g (AlphaZeroCheck.rowWires s0.tables i)
        (AlphaZeroCheck.rowConstants s0.tables i)
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        (Integrated.gateConfig vc).numSelectors = some terms ∧
      ∀ y ∈ terms, y = Verifier.zero := by
  refine GateDerivedRejection.derived_selected_gate_constraints_vanish hash pin chain hderiv D
    hacc hfree hgoodTau i hi coeffs hcoeffs hgoodAlpha ?_ ?_ ?_
  · exact fun g' hg' =>
      (pinned_filters_transfer committedBy pin s0 hident _ g' i).trans (hpre g' hg')
  · exact fun g' hg' =>
      (pinned_filters_transfer committedBy pin s0 hident _ g' i).trans (hpost g' hg')
  · exact fun h => hactive ((pinned_filters_transfer committedBy pin s0 hident _ g i).symm.trans h)

end Restatement

/-! ## 10. A CONCRETE PARTIAL-SELECTOR-ZEROING FORGERY -/

namespace Example

open Audit.Wire3.GateRejectionPower (selectorConfig selectorGates honestEqColumn exampleTau)
open Audit.Wire3.GateDenseRound (Consistent cubeSum examplePublicHash exampleAlpha)
open Audit.Wire3.ZeroCheckSemantics (gateValue)

/-- Four wire columns over four Boolean rows.  Rows `1` and `3` SATISFY the
arithmetic gate (`3*a*b + addend = output`: `3*1*1+1 = 4`, `3*3*2+5 = 23`); rows
`0` and `2` DO NOT (`3*5*7+11 = 116 ≠ 103`, `3*2*1+4 = 10 ≠ 9`). -/
def exampleWires : List DenseMleIndexed.State :=
  [⟨2, [5, 1, 2, 3]⟩, ⟨2, [7, 1, 1, 2]⟩, ⟨2, [11, 1, 4, 5]⟩, ⟨2, [103, 4, 9, 23]⟩]

/-- THE HONEST selector column: gate row `0` is selected at Boolean rows `0` and
`2`, gate row `1` at Boolean rows `1` and `3`. -/
def honestSelector : List Element := [0, 1, 0, 1]

/-- THE PARTIALLY ZEROED selector column: the UNUSED selector value
`4294967295` (`Gates.unused_selector_zero_filter`) at exactly the two rows where
the witness is false, the honest value everywhere else. -/
def forgedSelector : List Element := [4294967295, 1, 4294967295, 1]

def exampleConstants (selector : List Element) : List DenseMleIndexed.State :=
  [⟨2, selector⟩, ⟨2, [2, 2, 2, 2]⟩, ⟨2, [3, 3, 3, 3]⟩, ⟨2, [1, 1, 1, 1]⟩]

def exampleState (selector : List Element) : ProverState :=
  ⟨exampleWires, exampleConstants selector, ⟨2, honestEqColumn⟩, 6, [], []⟩

/-- The point at which the example's bound cells are compared. -/
def examplePoint : List Element := [3, 5]

theorem states_are_consistent :
    Gates.validateConfiguration selectorConfig selectorGates = some () ∧
      0 < selectorConfig.numGateConstraints ∧
      Consistent selectorConfig (exampleState honestSelector) ∧
      Consistent selectorConfig (exampleState forgedSelector) :=
  ⟨by decide, by decide, ⟨by decide, rfl, rfl⟩, ⟨by decide, rfl, rfl⟩⟩

/-- The eq column is a GENUINE `ext3_eq_evals(tau)` in both states, so the
adopted strong field S1 (`GateEqProvenance`) is satisfied by the forgery. -/
theorem forged_state_has_eq_provenance :
    EqTableProvenance.GateEqProvenance (exampleState forgedSelector) exampleTau :=
  ⟨GateRejectionPower.honest_eq_column_is_eq_table, rfl⟩

/-- THE FORGERY IS PARTIAL, not total: the gate at gate row `1` is ACTIVE at
Boolean row `1`, so the adopted strong field S2 (`activeFilter`) is SATISFIED —
the guard the adopted modules rely on does not fire. -/
theorem forgery_satisfies_activeFilter :
    ∃ g ∈ selectorGates,
      GateRejectionPower.rowFilter selectorConfig g (exampleState forgedSelector).tables 1
        ≠ Verifier.zero :=
  ⟨⟨3, 0, 0, 2, 1, 1, 1, 0, 0⟩, by decide, by decide⟩

/-- …while the filters ARE zeroed at exactly the two rows that carry the false
witness. -/
theorem forgery_zeroes_the_rows_that_matter :
    (∀ g ∈ selectorGates,
      GateRejectionPower.rowFilter selectorConfig g (exampleState forgedSelector).tables 0
        = Verifier.zero) ∧
    (∀ g ∈ selectorGates,
      GateRejectionPower.rowFilter selectorConfig g (exampleState forgedSelector).tables 2
        = Verifier.zero) := by
  constructor <;> decide

/-- WHAT THE HONEST COLUMN DOES: the false witness is VISIBLE — rows `0` and `2`
carry a nonzero gate aggregate and the cube sum does not vanish. -/
theorem honest_selector_detects_the_false_witness :
    gateValue selectorConfig selectorGates examplePublicHash exampleAlpha
        (exampleState honestSelector).tables 0 ≠ 0 ∧
    gateValue selectorConfig selectorGates examplePublicHash exampleAlpha
        (exampleState honestSelector).tables 2 ≠ 0 ∧
    cubeSum selectorConfig selectorGates examplePublicHash exampleAlpha
        (exampleState honestSelector).tables 4 ≠ 0 :=
  ⟨by decide, by decide, by decide⟩

/-- **WHAT THE OLD ASSUMPTIONS ACCEPT.**  With the partially zeroed selector
column the SAME witness produces a zero gate aggregate at EVERY Boolean row and a
vanishing cube sum — so the adopted
`GateDerivedRejection.derived_selected_gate_constraints_vanish` and the adopted
`GateRejectionPower.strong_gate_rows_vanish` would detect nothing: their
CONCLUSIONS already hold at this witness (the theorems themselves are not
instantiated here — the two `decide` conjuncts below are exactly the conclusions
they would deliver), even though the configuration is validated, the constraint count is positive, the
eq column has full provenance and `activeFilter` holds. -/
theorem old_assumptions_accept_the_forgery :
    (∀ i, i < 4 → gateValue selectorConfig selectorGates examplePublicHash exampleAlpha
        (exampleState forgedSelector).tables i = 0) ∧
    cubeSum selectorConfig selectorGates examplePublicHash exampleAlpha
        (exampleState forgedSelector).tables 4 = 0 :=
  ⟨by decide, by decide⟩

/-- **WHERE THE NEW CHAIN CATCHES IT.**  The forged and honest selector columns
have DIFFERENT fully bound cells at the example point, so
`forged_constants_cell_is_the_committed_cell` cannot hold for both. -/
theorem forged_and_honest_bound_cells_differ :
    NormTerminalBinding.cell (NormTerminalBinding.bindColumn forgedSelector examplePoint)
      ≠ NormTerminalBinding.cell (NormTerminalBinding.bindColumn honestSelector examplePoint) := by
  decide

/-- **THE FORGERY HITS ONE OF THE THREE BRANCHES.**  Instantiation of
`partial_zeroing_forces_one_of_three` at the state above, with the pinned
commitment covering the HONEST selector column.  The only extra data is that the
verifier's derived gate point is the example point. -/
theorem forgery_hits_a_branch (e : Verifier.Engine) (pin : Verifier.Pinned)
    (vc : Verifier.Config) (p : Verifier.Proof) (k : Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (hnc : 0 < vc.numConstants)
    (hpoint : TranscriptProvenance.gatePointColumn e vc p = examplePoint)
    (hbind : GateDerivedRejection.EqCellBinding e vc p (exampleState forgedSelector) k)
    (hcols : ConstantsColumnsOfRoot committedBy p cols)
    (hcommitted : (committedBy pin.preprocessedRoot).get? 0 = some honestSelector) :
    p.preprocessedRoot ≠ pin.preprocessedRoot ∨
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) ∨
    ¬ OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
        (Verifier.derivedIndices e vc p) cols := by
  refine partial_zeroing_forces_one_of_three e pin vc p (exampleState forgedSelector) k cols
    committedBy 0 forgedSelector honestSelector hnc hbind hcols rfl hcommitted ?_
  rw [hpoint]
  exact forged_and_honest_bound_cells_differ

/-- **THE SPECIFIC BRANCH.**  An ACCEPTED run kills the root branch (the pin),
and an honest PCS opening kills the opening branch, so the forgery is rejected at
the EXTRACTION JOIN: the adopted gate assumption 6
(`GateTerminalBinding.CellsMatchClaims`) must FAIL. -/
theorem forgery_rejected_at_the_join (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (pin : Verifier.Pinned) (chain : Nat) (vc : Verifier.Config) (p : Verifier.Proof) (k : Cells)
    (cols : Fin 5 → List (List Element)) (committedBy : Verifier.Root → List (List Element))
    (hnc : 0 < vc.numConstants)
    (hacc : Integrated.verify e decode pin chain vc p = .ok ())
    (hpoint : TranscriptProvenance.gatePointColumn e vc p = examplePoint)
    (hbind : GateDerivedRejection.EqCellBinding e vc p (exampleState forgedSelector) k)
    (hcols : ConstantsColumnsOfRoot committedBy p cols)
    (hcommitted : (committedBy pin.preprocessedRoot).get? 0 = some honestSelector)
    (hyp : OpeningBinding.OpensCommittedTable vc p (Verifier.derivedRounds e vc p)
      (Verifier.derivedIndices e vc p) cols) :
    ¬ GateTerminalBinding.CellsMatchClaims vc k (GateTerminalBinding.gateTerminalInput p) := by
  rcases forgery_hits_a_branch e pin vc p k cols committedBy hnc hpoint hbind hcols hcommitted with
    hroot | hk | hopen
  · exact absurd (accepted_root_is_pinned e decode pin chain vc p hacc) hroot
  · exact hk
  · exact absurd hyp hopen

end Example

end Audit.Wire3.ConstantsProvenance
