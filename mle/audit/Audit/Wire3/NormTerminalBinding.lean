import Audit.Wire3.NormDenseRound
import Audit.Wire3.Connections

/-!
# Fully bound norm/logUp tables against the verifier's terminal formula

Sources reviewed:
* mle/src/permutation/norm_logup.rs 270-316 (`PreparedChallenges::new`:
  lambda powers by a running product from ONE), 319-359
  (`evaluate_target_from_values`), 386-390 (`line_value`), 414-491
  (`from_base`), 493-540 (`round_sum_at`), 542-563 (`bind`), 855-899
  (`evaluate_joint_norm_logup_terminal_with_public_inputs`, called from
  mle/src/verifier_v2.rs 398-420 with the verifier's own `subgroup_eval` and
  `eq_eval_ext3(tau, point)`, the routed witness slice, the preprocessed
  slice `[num_constants..num_constants+num_routed]`, and the two halves of
  `log_norm_inverse_evals`);
* mle/contracts/src/OuterLogupExt3Verifier.sol 323-441
  (`_evaluateTerminalUnchecked`, `_permutationTerminalUnchecked`,
  `_publicInputBinding`);
* Audit.Wire3.Norm (wireStep 180-193, permutationTerminal 243-245, piStep
  267-272, publicInputBinding 277-278, evaluate 308-309, checkedEvaluate
  321-328, engine_uses_same_statement_inputs 380-383),
  Audit.Wire3.NormDenseRound (Tables/Shape 56-96, line 101-102, wireValues
  122-127, piValue 171-173, roundValue 209-213, targetValue 275-285,
  roundSumAt 472-483, bindTables 606-616, bind_tables_shaped 647-678,
  bound_prefix_is_boolean_row_eq 688-694, buildBindings 700-759),
  Audit.Wire3.DenseMleIndexed (bindMany 225-229, evaluate 254-257,
  evaluate_full_table_same_packed_fold 262-277), Audit.Wire3.Packed (fold
  31), Audit.Wire3.Connections (packedFold 75-81), Audit.Wire3.Verifier
  (NormTerminalInput 297-304, Engine.logTerminal 362-363).

What is proved.
1. `fully_bound_round_target_is_norm_evaluate`: on `Shape` tables with
   `remaining = 0` (every constituent a single cell) the prover's
   `evaluate_target_from_values` on those cells together with the fully
   accumulated PI bindings (`terminalTarget`) is exactly the verifier's
   `Norm.evaluate` formula on the `NormTerminalInput` assembled from the
   cells (`toTerminalInput`), with the eq and subgroup values taken AS THE
   CELLS THE TABLES HOLD (`evaluateWith`). The assembled witness is the
   routed wire cells followed by an arbitrary tail `extra` standing for the
   non-routed wires: the source witness vector has `num_wires` entries and
   the terminal reads only its routed prefix (`log_witness[..num_routed]`,
   verifier_v2.rs 406; `Norm.shapeValid` requires
   `witness.length = numWires`), so every theorem holds for every `extra`
   and the checked/engine forms are reachable with `numWires > numRouted`.
   `wire_step_is_slice_contribution` and `pi_step_exact` are the per-wire /
   per-PI term identities: the two sides read the same operands in the same
   order. No operand-order difference between
   `NormDenseRound.wireValues`/`piValue` and `Norm.wireStep`/`piStep` was
   found; `identityPosition` is `scalar subgroup k` on both sides. The PI
   loop is matched in the Rust order (`Norm.piStep`); the Solidity
   `_publicInputBinding` groups the terms by row (shared-bit factoring of
   the eq-row products), a rearrangement modelled by the adopted
   `Audit.Wire3.PiSharedBits`, not by this file.
2. `bound_column_is_packed_fold`, `bound_cell_is_connections_packed_fold`:
   binding all `n` variables of a `2^n` column at a point leaves one cell,
   which is the adopted `DenseMleIndexed.evaluate` and
   `Packed.fold`/`Connections.packedFold` of the original column at the point.
3. `fully_bound_tables_from_initial`, `fully_bound_cells_are_packed_folds`:
   iterating `bindTables` over a point of length `remaining` succeeds, keeps
   `Shape`, and yields `remaining = 0` with every column a single cell equal
   to the packed fold of its original column.
4. Provenance is explicit and NOT proved: that the eq cell is
   `Norm.eqEvaluation tau point`, that the subgroup cell is
   `Norm.subgroupEvaluation powers point`, that the lambda powers are
   `lambda^j`, that the eta weights are `eta^i`, that the wire-map bytes
   decode to the bindings' rows/columns, and that `kIs` agree, are the
   hypotheses `LambdaProvenance`, `EtaProvenance`, `WireMapMatches`,
   `Compatible`, `PrefixAt`, and the two cell equalities of
   `fully_bound_target_is_norm_evaluate_of_cells`. The eq table's
   construction from `tau` (`eq_evals_ext3`) is not modelled by the adopted
   audit, so nothing here relates the packed fold of the eq column to the
   verifier's eq-MLE.
5. `last_round_target_is_bound_terminal` (HONEST PROVER ONLY): at
   `remaining = 1`, `round_sum_at` at the final challenge is the terminal
   target of the tables bound at that challenge.
6. `honest_prover_terminal` (HONEST PROVER ONLY): from a fresh `Shape` table
   with `buildBindings`, binding the whole point discharges `PrefixAt` and
   `EtaProvenance`, leaving only the eq/subgroup/lambda/wire-map/kIs
   hypotheses.
7. A concrete one-variable, one-wire, one-PI example evaluated by `decide`.

Reads are the adopted zero-totalized `getD`; `fully_bound_reads_in_bounds`
shows each cell read of a fully bound table is the whole column. Not claimed:
anything about the WHIR context, that PCS-claimed values equal the prover's
cells, dishonest provers, soundness, or Rust/EVM refinement.
-/
namespace Audit.Wire3.NormTerminalBinding
open Audit.Wire3 GoldilocksExt3Field NormDenseRound

/-! ## Cells of fully bound columns -/

/-- `evaluations[0]` of a `num_vars = 0` table. Zero-totalized like every
adopted read; `fully_bound_reads_in_bounds` supplies `length = 1`. -/
def cell (column : List Element) : Element := column.getD 0 0

def cells (columns : List (List Element)) : List Element := columns.map cell

def cellValues (columns : List (List Element)) : List Verifier.Ext3 := values (cells columns)

theorem cells_length (columns : List (List Element)) : (cells columns).length = columns.length :=
  List.length_map _ _

theorem cell_values_length (columns : List (List Element)) :
    (cellValues columns).length = columns.length := by
  rw [cellValues, values_length, cells_length]

theorem cells_getD (columns : List (List Element)) (j : Nat) :
    (cells columns).getD j 0 = cell (columnAt columns j) := by
  have h := List.getD_map columns ([] : List Element) (n := j) cell
  exact h

theorem cell_values_getD (columns : List (List Element)) (j : Nat) :
    (cellValues columns).getD j Verifier.zero = (cell (columnAt columns j)).toVerifier := by
  rw [cellValues, values_getD, cells_getD]

/-- `remaining = 0` under the constructor shape: `1 << 0 = 1` entry everywhere. -/
def FullyBound (t : Tables) : Prop :=
  t.remaining = 0 ∧ t.eq.length = 1 ∧ t.subgroup.length = 1 ∧
  ColumnShape t.wires t.wires.length 1 ∧ ColumnShape t.sigmas t.wires.length 1 ∧
  ColumnShape t.identityHelpers t.wires.length 1 ∧ ColumnShape t.sigmaHelpers t.wires.length 1

theorem shape_zero_remaining_fully_bound (t : Tables) (p : Prepared) (h : Shape t p)
    (hr : t.remaining = 0) : FullyBound t := by
  rcases h with ⟨he,hg,hw,hs,hi,hh,_,_,_⟩
  rw [hr, Nat.pow_zero] at he hg hw hs hi hh
  exact ⟨hr,he,hg,hw,hs,hi,hh⟩

theorem exists_singleton_of_length_one {α : Type} (l : List α) (h : l.length = 1) : ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => exact ⟨a, rfl⟩
      | cons b rest => simp at h

theorem singleton_cell (column : List Element) (h : column.length = 1) : column = [cell column] := by
  obtain ⟨a, rfl⟩ := exists_singleton_of_length_one column h
  rfl

/-- Every cell read of a fully bound table is the whole column. -/
theorem fully_bound_reads_in_bounds (t : Tables) (h : FullyBound t) :
    t.eq = [cell t.eq] ∧ t.subgroup = [cell t.subgroup] ∧
    ∀ j, j < t.wires.length →
      columnAt t.wires j = [cell (columnAt t.wires j)] ∧
      columnAt t.sigmas j = [cell (columnAt t.sigmas j)] ∧
      columnAt t.identityHelpers j = [cell (columnAt t.identityHelpers j)] ∧
      columnAt t.sigmaHelpers j = [cell (columnAt t.sigmaHelpers j)] := by
  rcases h with ⟨_,he,hg,hw,hs,hi,hh⟩
  refine ⟨singleton_cell _ he, singleton_cell _ hg, fun j hj => ?_⟩
  exact ⟨singleton_cell _ (column_at_shape _ _ _ j hw hj).2,
    singleton_cell _ (column_at_shape _ _ _ j hs hj).2,
    singleton_cell _ (column_at_shape _ _ _ j hi hj).2,
    singleton_cell _ (column_at_shape _ _ _ j hh hj).2⟩

/-! ## The verifier's wire loop as an explicit ordered fold -/

theorem lift_exact (x : Verifier.Ext3) : (NormPolynomial.lift x).toVerifier = x := rfl

/-- The verifier's running `lambdaPower` after `index` wires: `lambda^index`. -/
def lambdaAt (ch : Norm.Challenges) (index : Nat) : Verifier.Ext3 :=
  ((NormPolynomial.lift ch.lambda)^index).toVerifier

theorem lambda_at_zero (ch : Norm.Challenges) : lambdaAt ch 0 = Norm.one := by
  simp only [lambdaAt, pow_zero, one_exact]

theorem lambda_at_succ (ch : Norm.Challenges) (n : Nat) :
    lambdaAt ch (n+1) = Verifier.mul (lambdaAt ch n) ch.lambda := by
  simp only [lambdaAt, pow_succ, mul_exact, lift_exact]

/-- The same weight as the adopted `Norm.run_wires_lambda_power` running product. -/
theorem lambda_at_is_repeated (ch : Norm.Challenges) (n : Nat) :
    lambdaAt ch n = Norm.multiplyRepeated Norm.one ch.lambda n := by
  have h := congrArg Element.toVerifier (NormPolynomial.lift_repeated_multiplication Norm.one ch.lambda n)
  rw [lift_exact] at h
  rw [h, lambdaAt]
  have h1 : NormPolynomial.lift Norm.one = (1 : Element) := rfl
  rw [h1, one_mul]

/-- One wire's two accumulator increments as the verifier computes them. -/
def wireTerm (c : Verifier.Config) (ch : Norm.Challenges) (t : Verifier.NormTerminalInput)
    (subgroup : Verifier.Ext3) (j : Nat) : Verifier.Ext3 × Verifier.Ext3 :=
  NormPolynomial.actualContribution ch (lambdaAt ch j) (NormPolynomial.actualWireValues c t subgroup j)

theorem run_wires_accumulators (c : Verifier.Config) (ch : Norm.Challenges) (t : Verifier.NormTerminalInput)
    (subgroup : Verifier.Ext3) (count : Nat) :
    ∀ (index : Nat) (s : Norm.WireState), s.lambdaPower = lambdaAt ch index →
      (Norm.runWires c ch t subgroup index count s).helperChecks =
        (List.range' index count).foldl (fun acc j => Verifier.add acc (wireTerm c ch t subgroup j).1) s.helperChecks ∧
      (Norm.runWires c ch t subgroup index count s).logupSum =
        (List.range' index count).foldl (fun acc j => Verifier.add acc (wireTerm c ch t subgroup j).2) s.logupSum := by
  induction count with
  | zero =>
      intro index s _
      simp only [Norm.runWires]
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      intro index s hs
      have hl : (Norm.wireStep c ch t subgroup index s).lambdaPower = lambdaAt ch (index+1) := by
        rw [Norm.wire_step_lambda, hs, lambda_at_succ]
      have hrest := ih (index+1) (Norm.wireStep c ch t subgroup index s) hl
      have e1 : (Norm.wireStep c ch t subgroup index s).helperChecks =
          Verifier.add s.helperChecks (wireTerm c ch t subgroup index).1 := by
        show _ = Verifier.add s.helperChecks (NormPolynomial.actualContribution ch (lambdaAt ch index)
          (NormPolynomial.actualWireValues c t subgroup index)).1
        rw [← hs]
        rfl
      have e2 : (Norm.wireStep c ch t subgroup index s).logupSum =
          Verifier.add s.logupSum (wireTerm c ch t subgroup index).2 := by
        show _ = Verifier.add s.logupSum (NormPolynomial.actualContribution ch (lambdaAt ch index)
          (NormPolynomial.actualWireValues c t subgroup index)).2
        rw [← hs]
        rfl
      simp only [Norm.runWires, List.range'_succ, List.foldl_cons]
      rw [hrest.1, hrest.2, e1, e2]
      exact ⟨rfl, rfl⟩

theorem permutation_loop_exact (c : Verifier.Config) (ch : Norm.Challenges) (t : Verifier.NormTerminalInput)
    (subgroup : Verifier.Ext3) :
    (Norm.runWires c ch t subgroup 0 c.numRouted Norm.wireStart).helperChecks =
      (List.range c.numRouted).foldl (fun acc j => Verifier.add acc (wireTerm c ch t subgroup j).1) Verifier.zero ∧
    (Norm.runWires c ch t subgroup 0 c.numRouted Norm.wireStart).logupSum =
      (List.range c.numRouted).foldl (fun acc j => Verifier.add acc (wireTerm c ch t subgroup j).2) Verifier.zero := by
  rw [List.range_eq_range']
  exact run_wires_accumulators c ch t subgroup c.numRouted 0 Norm.wireStart (by rw [lambda_at_zero]; rfl)

/-- `Norm.permutationTerminal` with the eq and subgroup values as explicit
arguments instead of being recomputed from `point`. -/
def permutationTerminalWith (c : Verifier.Config) (ch : Norm.Challenges) (t : Verifier.NormTerminalInput)
    (eqValue subgroup : Verifier.Ext3) : Verifier.Ext3 :=
  Verifier.add
    (Verifier.mul eqValue (Norm.runWires c ch t subgroup 0 c.numRouted Norm.wireStart).helperChecks)
    (Verifier.mul ch.kappa (Norm.runWires c ch t subgroup 0 c.numRouted Norm.wireStart).logupSum)

theorem permutation_terminal_with_exact (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3) :
    Norm.permutationTerminal c ch t point =
      permutationTerminalWith c ch t (Norm.eqEvaluation ch.tau point)
        (Norm.subgroupEvaluation c.subgroupPowers point) := rfl

/-- `Norm.evaluate` with explicit eq and subgroup values; `point` is still
used by the PI Boolean-row factors. -/
def evaluateWith (c : Verifier.Config) (ch : Norm.Challenges) (t : Verifier.NormTerminalInput)
    (eqValue subgroup : Verifier.Ext3) (point : List Verifier.Ext3) : Verifier.Ext3 :=
  Verifier.add (permutationTerminalWith c ch t eqValue subgroup)
    (Verifier.mul ch.xi (Norm.publicInputBinding c t point ch.eta))

theorem evaluate_with_exact (c : Verifier.Config) (ch : Norm.Challenges)
    (t : Verifier.NormTerminalInput) (point : List Verifier.Ext3) :
    Norm.evaluate c ch t point =
      evaluateWith c ch t (Norm.eqEvaluation ch.tau point)
        (Norm.subgroupEvaluation c.subgroupPowers point) point := rfl

/-! ## Tables to NormTerminalInput -/

/-- The verifier's terminal input assembled from the single cells. The
witness is the routed wire cells followed by `extra`, the values of the
non-routed wires: the source witness vector has `num_wires` entries
(`Norm.shapeValid` requires `witness.length = numWires`, Verifier.lean 139
on every accepted proof) and the terminal reads only its routed prefix
(`log_witness[..num_routed]`, verifier_v2.rs 406), so `extra` is left
unconstrained. Sigmas follow `constants` in `preprocessed`
(`log_preprocessed_evals[num_constants..num_constants+num_routed]`,
verifier_v2.rs 407-408), identity helpers then sigma helpers form
`normInverse` (`[..num_routed]` and `[num_routed..]`, 409-410), and the raw
public inputs are the bindings' values in order. -/
def toTerminalInput (t : Tables) (constants extra : List Verifier.Ext3) : Verifier.NormTerminalInput :=
  ⟨constants ++ cellValues t.sigmas, cellValues t.wires ++ extra,
   cellValues t.identityHelpers ++ cellValues t.sigmaHelpers, t.bindings.map Binding.publicValue⟩

theorem to_terminal_input_witness_length (t : Tables) (constants extra : List Verifier.Ext3) :
    (toTerminalInput t constants extra).witness.length = t.wires.length + extra.length := by
  show (cellValues t.wires ++ extra).length = _
  rw [List.length_append, cell_values_length]

/-- A witness read at a routed index never reaches `extra`. -/
theorem routed_witness_getD (t : Tables) (extra : List Verifier.Ext3) (j : Nat) (hj : j < t.wires.length) :
    (cellValues t.wires ++ extra).getD j Verifier.zero = (cellValues t.wires).getD j Verifier.zero :=
  List.getD_append _ _ _ _ (by rw [cell_values_length]; exact hj)

/-- Config/prepared correspondence: routed count, constant offset, `kIs`. -/
def Compatible (c : Verifier.Config) (t : Tables) (p : Prepared) (constants : List Verifier.Ext3) : Prop :=
  c.numRouted = t.wires.length ∧ c.numConstants = constants.length ∧ c.kIs = p.kIs

/-- `PreparedChallenges::new` (270-316): `lambda_powers[j] = lambda^j` by a
running product from ONE. A hypothesis on the adopted `Prepared`, whose
lambda powers are only length-constrained by `Shape`. -/
def LambdaProvenance (p : Prepared) : Prop :=
  ∀ j, j < p.lambdaPowers.length → p.lambdaPowers.getD j 0 = (NormPolynomial.lift p.challenges.lambda)^j

/-- The verifier decodes PI `i`'s `(row, column)` from three bytes
(`Norm.targetAt`); the prover carries them as `Nat` fields (`from_base`
446-460). Their agreement is a hypothesis. -/
def WireMapMatches (wireMap : Verifier.Bytes) (bindings : List Binding) : Prop :=
  ∀ pair ∈ bindings.enum, Norm.targetAt wireMap pair.1 = ⟨pair.2.row, pair.2.column⟩

/-- `eta_power` of PI `i` is `eta^i` (`from_base` 446-460). -/
def EtaProvenance (eta : Element) (bindings : List Binding) : Prop :=
  ∀ pair ∈ bindings.enum, pair.2.etaPower = eta^pair.1

/-- Every prefix is the verifier's Boolean-row factor product over `point`
(`NormDenseRound.PrefixProvenance` at the tables level). -/
def PrefixAt (point : List Verifier.Ext3) (bindings : List Binding) : Prop :=
  ∀ b ∈ bindings, b.prefixEq.toVerifier = Norm.booleanRowEq b.row point

/-- `PreparedChallenges::new` (288-297): `power = ONE; push power; power *= lambda`. -/
def runningPowers (x : Element) : Nat → Element → List Element
  | 0, _ => []
  | n+1, power => power :: runningPowers x n (power*x)

theorem running_powers_length (x : Element) (n : Nat) (power : Element) :
    (runningPowers x n power).length = n := by
  induction n generalizing power with
  | zero => rfl
  | succ n ih => simp only [runningPowers, List.length_cons, ih]

theorem running_powers_getD (x : Element) (n : Nat) :
    ∀ (power : Element) (j : Nat), j < n → (runningPowers x n power).getD j 0 = power*x^j := by
  induction n with
  | zero => intro power j hj; simp at hj
  | succ n ih =>
      intro power j hj
      cases j with
      | zero => simp [runningPowers]
      | succ j =>
          simp only [runningPowers, List.getD_cons_succ]
          rw [ih (power*x) j (by omega), pow_succ]
          ring

/-- The source running product satisfies `LambdaProvenance`. -/
theorem running_powers_lambda_provenance (ch : Norm.Challenges) (kIs : List Verifier.Base) (n : Nat) :
    LambdaProvenance ⟨ch, kIs, runningPowers (NormPolynomial.lift ch.lambda) n 1⟩ := by
  intro j hj
  rw [running_powers_length] at hj
  show (runningPowers (NormPolynomial.lift ch.lambda) n 1).getD j 0 = _
  rw [running_powers_getD _ n 1 j hj, one_mul]

/-! ## evaluate_target_from_values on the fully bound cells -/

/-- One PI term with the fully accumulated prefix and the bound wire cell:
`eta_power * eq_row * (wire - value)` (norm_logup.rs 882-883,
OuterLogupExt3Verifier._accumulatePublicInputInPlace). -/
def terminalPiTerm (t : Tables) (b : Binding) : Verifier.Ext3 :=
  Verifier.mul (Verifier.mul b.etaPower.toVerifier b.prefixEq.toVerifier)
    (Verifier.sub (cell (columnAt t.wires b.column)).toVerifier (Norm.embed b.publicValue.val))

def terminalBinding (t : Tables) : Verifier.Ext3 :=
  t.bindings.foldl (fun acc b => Verifier.add acc (terminalPiTerm t b)) Verifier.zero

/-- `evaluate_target_from_values` (319-359) on the single cells, with the eq
and subgroup values AS HELD BY THE TABLES and the PI binding above. -/
def terminalTarget (t : Tables) (p : Prepared) : Option Verifier.Ext3 :=
  targetValue p (cell t.eq).toVerifier (cellValues t.wires) (cellValues t.sigmas)
    (cellValues t.identityHelpers) (cellValues t.sigmaHelpers) (cell t.subgroup).toVerifier
    (terminalBinding t)

theorem base_zero_exact : baseZero = Verifier.base 0 := rfl

/-- The five reads of one routed wire agree operand by operand: witness,
`scalar subgroup k`, `preprocessed[numConstants + j]`, `normInverse[j]`,
`normInverse[numRouted + j]`. -/
theorem fully_bound_wire_values (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (subgroup : Verifier.Ext3) (j : Nat)
    (hc : Compatible c t p constants) (h : Shape t p) (hj : j < t.wires.length) :
    sliceWireValues p (cellValues t.wires) (cellValues t.sigmas) (cellValues t.identityHelpers)
        (cellValues t.sigmaHelpers) subgroup j =
      NormPolynomial.actualWireValues c (toTerminalInput t constants extra) subgroup j := by
  obtain ⟨hn, hk, hkis⟩ := hc
  have h0 := routed_witness_getD t extra j hj
  have hid : (cellValues t.identityHelpers).length = t.wires.length := by
    rw [cell_values_length, h.2.2.2.2.1.1]
  have h1 : (constants ++ cellValues t.sigmas).getD (constants.length + j) Verifier.zero =
      (cellValues t.sigmas).getD j Verifier.zero := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have h2 : (cellValues t.identityHelpers ++ cellValues t.sigmaHelpers).getD j Verifier.zero =
      (cellValues t.identityHelpers).getD j Verifier.zero :=
    List.getD_append _ _ _ _ (by rw [hid]; exact hj)
  have h3 : (cellValues t.identityHelpers ++ cellValues t.sigmaHelpers).getD (t.wires.length + j) Verifier.zero =
      (cellValues t.sigmaHelpers).getD j Verifier.zero := by
    rw [List.getD_append_right _ _ _ _ (by rw [hid]; exact Nat.le_add_right _ _), hid, Nat.add_sub_cancel_left]
  simp only [sliceWireValues, NormPolynomial.actualWireValues, toTerminalInput, hkis, hn, hk,
    base_zero_exact, h0, h1, h2, h3]

/-- `Norm.wireStep` on the assembled input adds exactly the prover's
`sliceWireValues` contribution of the same wire. -/
theorem wire_step_is_slice_contribution (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (subgroup : Verifier.Ext3) (j : Nat) (s : Norm.WireState)
    (hc : Compatible c t p constants) (h : Shape t p) (hj : j < t.wires.length) :
    ((Norm.wireStep c p.challenges (toTerminalInput t constants extra) subgroup j s).helperChecks,
     (Norm.wireStep c p.challenges (toTerminalInput t constants extra) subgroup j s).logupSum) =
      (Verifier.add s.helperChecks (NormPolynomial.actualContribution p.challenges s.lambdaPower
        (sliceWireValues p (cellValues t.wires) (cellValues t.sigmas) (cellValues t.identityHelpers)
          (cellValues t.sigmaHelpers) subgroup j)).1,
       Verifier.add s.logupSum (NormPolynomial.actualContribution p.challenges s.lambdaPower
        (sliceWireValues p (cellValues t.wires) (cellValues t.sigmas) (cellValues t.identityHelpers)
          (cellValues t.sigmaHelpers) subgroup j)).2) := by
  rw [NormPolynomial.wire_step_contribution_exact, fully_bound_wire_values t p c constants extra subgroup j hc h hj]

theorem fully_bound_contribution (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (subgroup : Verifier.Ext3) (j : Nat)
    (hc : Compatible c t p constants) (h : Shape t p) (hlam : LambdaProvenance p) (hj : j < t.wires.length) :
    sliceContribution p (cellValues t.wires) (cellValues t.sigmas) (cellValues t.identityHelpers)
        (cellValues t.sigmaHelpers) subgroup j =
      wireTerm c p.challenges (toTerminalInput t constants extra) subgroup j := by
  have hl : j < p.lambdaPowers.length := by rw [h.2.2.2.2.2.2.2.1]; exact hj
  simp only [sliceContribution, wireTerm, lambdaAt, hlam j hl,
    fully_bound_wire_values t p c constants extra subgroup j hc h hj]

theorem fully_bound_loop (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (subgroup : Verifier.Ext3)
    (hc : Compatible c t p constants) (h : Shape t p) (hlam : LambdaProvenance p) :
    targetLoop p (cellValues t.wires) (cellValues t.sigmas) (cellValues t.identityHelpers)
        (cellValues t.sigmaHelpers) subgroup =
      ((List.range c.numRouted).foldl
        (fun acc j => Verifier.add acc (wireTerm c p.challenges (toTerminalInput t constants extra) subgroup j).1) Verifier.zero,
       (List.range c.numRouted).foldl
        (fun acc j => Verifier.add acc (wireTerm c p.challenges (toTerminalInput t constants extra) subgroup j).2) Verifier.zero) := by
  have hn : p.lambdaPowers.length = c.numRouted := by rw [h.2.2.2.2.2.2.2.1, hc.1]
  rw [target_loop_splits, hn]
  have hcong := foldl_pair_congr
    (fun j => sliceContribution p (cellValues t.wires) (cellValues t.sigmas) (cellValues t.identityHelpers)
      (cellValues t.sigmaHelpers) subgroup j)
    (fun j => wireTerm c p.challenges (toTerminalInput t constants extra) subgroup j)
    (List.range c.numRouted)
    (fun j hj => fully_bound_contribution t p c constants extra subgroup j hc h hlam
      (by rw [← hc.1]; exact List.mem_range.mp hj))
    Verifier.zero Verifier.zero
  exact Prod.ext hcong.1 hcong.2

/-! ## The verifier's PI loop against the bindings -/

theorem snd_mem_of_mem_enumFrom {α : Type} (xs : List α) :
    ∀ (start : Nat) (pair : Nat × α), pair ∈ xs.enumFrom start → pair.2 ∈ xs := by
  induction xs with
  | nil => intro start pair h; simp at h
  | cons a rest ih =>
      intro start pair h
      rw [List.enumFrom_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self _ _
      · exact List.mem_cons_of_mem _ (ih (start+1) pair h)

theorem snd_mem_of_mem_enum {α : Type} (xs : List α) (pair : Nat × α) (h : pair ∈ xs.enum) : pair.2 ∈ xs :=
  snd_mem_of_mem_enumFrom xs 0 pair h

/-- One verifier `piStep` on a binding whose target bytes, eta weight and
prefix are the prover's adds exactly `terminalPiTerm`: the same
`eta_power * eq_row * (wire - value)` in the same order. The witness is the
routed cells plus any tail `extra`; the PI column is routed (`Shape`,
`shapeValid`: `column < numRouted`), so the read never reaches `extra`. -/
theorem pi_step_exact (t : Tables) (extra : List Verifier.Ext3) (wireMap : Verifier.Bytes)
    (point : List Verifier.Ext3) (eta : Element) (s : Norm.PiState) (i : Nat) (b : Binding)
    (hcol : b.column < t.wires.length)
    (hs : s.etaPower = (eta^i).toVerifier)
    (hmap : Norm.targetAt wireMap i = ⟨b.row, b.column⟩)
    (heta : b.etaPower = eta^i)
    (hprefix : b.prefixEq.toVerifier = Norm.booleanRowEq b.row point) :
    Norm.piStep wireMap (cellValues t.wires ++ extra) point eta.toVerifier s (i, b.publicValue) =
      { binding := Verifier.add s.binding (terminalPiTerm t b),
        etaPower := (eta^(i+1)).toVerifier, processed := s.processed + 1 } := by
  simp only [Norm.piStep, hmap, routed_witness_getD t extra b.column hcol, cell_values_getD, hs,
    terminalPiTerm, heta, ← hprefix, pow_succ, mul_exact]

theorem pi_fold_exact (t : Tables) (extra : List Verifier.Ext3) (wireMap : Verifier.Bytes)
    (point : List Verifier.Ext3) (eta : Element) (bs : List Binding) :
    ∀ (start : Nat) (s : Norm.PiState), s.etaPower = (eta^start).toVerifier →
      (∀ pair ∈ bs.enumFrom start, Norm.targetAt wireMap pair.1 = ⟨pair.2.row, pair.2.column⟩ ∧
        pair.2.etaPower = eta^pair.1 ∧ pair.2.prefixEq.toVerifier = Norm.booleanRowEq pair.2.row point ∧
        pair.2.column < t.wires.length) →
      (((bs.map Binding.publicValue).enumFrom start).foldl
          (Norm.piStep wireMap (cellValues t.wires ++ extra) point eta.toVerifier) s).binding =
        bs.foldl (fun acc b => Verifier.add acc (terminalPiTerm t b)) s.binding := by
  induction bs with
  | nil => intro start s _ _; rfl
  | cons b rest ih =>
      intro start s hs hb
      have hb0 := hb (start, b) (List.mem_cons_self _ _)
      have hrest : ∀ pair ∈ rest.enumFrom (start+1),
          Norm.targetAt wireMap pair.1 = ⟨pair.2.row, pair.2.column⟩ ∧
          pair.2.etaPower = eta^pair.1 ∧ pair.2.prefixEq.toVerifier = Norm.booleanRowEq pair.2.row point ∧
          pair.2.column < t.wires.length :=
        fun pair hp => hb pair (List.mem_cons_of_mem _ hp)
      rw [List.map_cons, List.enumFrom_cons, List.foldl_cons, List.foldl_cons,
        pi_step_exact t extra wireMap point eta s start b hb0.2.2.2 hs hb0.1 hb0.2.1 hb0.2.2.1]
      exact ih (start+1) _ rfl hrest

/-- `hcol` (every PI column is routed) is the bindings half of `Shape`. -/
theorem public_input_binding_is_terminal_binding (t : Tables) (c : Verifier.Config) (ch : Norm.Challenges)
    (constants extra : List Verifier.Ext3) (point : List Verifier.Ext3)
    (hcol : ∀ b ∈ t.bindings, b.column < t.wires.length)
    (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (heta : EtaProvenance (NormPolynomial.lift ch.eta) t.bindings)
    (hprefix : PrefixAt point t.bindings) :
    Norm.publicInputBinding c (toTerminalInput t constants extra) point ch.eta = terminalBinding t := by
  have h := pi_fold_exact t extra c.publicInputWireMap point (NormPolynomial.lift ch.eta) t.bindings 0 Norm.piStart
    (by rw [pow_zero]; rfl)
    (fun pair hp => ⟨hmap pair hp, heta pair hp, hprefix pair.2 (snd_mem_of_mem_enum _ pair hp),
      hcol pair.2 (snd_mem_of_mem_enum _ pair hp)⟩)
  exact h

/-! ## The terminal identity -/

theorem target_identity (t : Tables) (p : Prepared) (c : Verifier.Config) (constants extra : List Verifier.Ext3)
    (point : List Verifier.Ext3) (h : Shape t p) (hc : Compatible c t p constants)
    (hlam : LambdaProvenance p) (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (heta : EtaProvenance (NormPolynomial.lift p.challenges.eta) t.bindings)
    (hprefix : PrefixAt point t.bindings) :
    terminalTarget t p = some (evaluateWith c p.challenges (toTerminalInput t constants extra)
      (cell t.eq).toVerifier (cell t.subgroup).toVerifier point) := by
  have hl := h.2.2.2.2.2.2.2.1
  have hcol : ∀ b ∈ t.bindings, b.column < t.wires.length := fun b hb => (h.2.2.2.2.2.2.2.2 b hb).2
  have hlw : (cellValues t.wires).length = p.lambdaPowers.length := by
    rw [cell_values_length, hl]
  have hls : (cellValues t.sigmas).length = p.lambdaPowers.length := by
    rw [cell_values_length, h.2.2.2.1.1, hl]
  have hli : (cellValues t.identityHelpers).length = p.lambdaPowers.length := by
    rw [cell_values_length, h.2.2.2.2.1.1, hl]
  have hlh : (cellValues t.sigmaHelpers).length = p.lambdaPowers.length := by
    rw [cell_values_length, h.2.2.2.2.2.1.1, hl]
  have hloop := permutation_loop_exact c p.challenges (toTerminalInput t constants extra) (cell t.subgroup).toVerifier
  simp only [terminalTarget, targetValue, hlw, hls, hli, hlh, and_self, if_true,
    fully_bound_loop t p c constants extra (cell t.subgroup).toVerifier hc h hlam,
    evaluateWith, permutationTerminalWith, hloop.1, hloop.2,
    public_input_binding_is_terminal_binding t c p.challenges constants extra point hcol hmap heta hprefix]

/-- (1) Fully bound tables: the prover's target on the single cells IS the
verifier's terminal formula on the assembled input, with the eq and subgroup
values being whatever cells the tables hold. Their provenance from `tau`
and the VK subgroup powers is NOT assumed here; see
`fully_bound_target_is_norm_evaluate_of_cells`. -/
theorem fully_bound_round_target_is_norm_evaluate (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (point : List Verifier.Ext3)
    (h : Shape t p) (hr : t.remaining = 0) (hc : Compatible c t p constants)
    (hlam : LambdaProvenance p) (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (heta : EtaProvenance (NormPolynomial.lift p.challenges.eta) t.bindings)
    (hprefix : PrefixAt point t.bindings) :
    FullyBound t ∧
    terminalTarget t p = some (evaluateWith c p.challenges (toTerminalInput t constants extra)
      (cell t.eq).toVerifier (cell t.subgroup).toVerifier point) :=
  ⟨shape_zero_remaining_fully_bound t p h hr, target_identity t p c constants extra point h hc hlam hmap heta hprefix⟩

/-- (4) The conditional form: IF the fully bound eq cell equals
`Norm.eqEvaluation tau point` and the subgroup cell equals
`Norm.subgroupEvaluation powers point`, the target is `Norm.evaluate`. Both
equalities are hypotheses; neither is derived from the tables. -/
theorem fully_bound_target_is_norm_evaluate_of_cells (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (point : List Verifier.Ext3)
    (h : Shape t p) (hc : Compatible c t p constants)
    (hlam : LambdaProvenance p) (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (heta : EtaProvenance (NormPolynomial.lift p.challenges.eta) t.bindings)
    (hprefix : PrefixAt point t.bindings)
    (heq : (cell t.eq).toVerifier = Norm.eqEvaluation p.challenges.tau point)
    (hsub : (cell t.subgroup).toVerifier = Norm.subgroupEvaluation c.subgroupPowers point) :
    terminalTarget t p = some (Norm.evaluate c p.challenges (toTerminalInput t constants extra) point) := by
  rw [evaluate_with_exact, ← heq, ← hsub]
  exact target_identity t p c constants extra point h hc hlam hmap heta hprefix

/-- The checked verifier entry point, under its own `shapeValid` guard.
`shapeValid` needs `witness.length = numWires`, i.e.
`t.wires.length + extra.length = c.numWires` (`to_terminal_input_witness_length`);
`extra` carries the `numWires - numRouted` non-routed wire values. -/
theorem fully_bound_target_is_checked_evaluate (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (point : List Verifier.Ext3)
    (h : Shape t p) (hc : Compatible c t p constants)
    (hlam : LambdaProvenance p) (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (heta : EtaProvenance (NormPolynomial.lift p.challenges.eta) t.bindings)
    (hprefix : PrefixAt point t.bindings)
    (heq : (cell t.eq).toVerifier = Norm.eqEvaluation p.challenges.tau point)
    (hsub : (cell t.subgroup).toVerifier = Norm.subgroupEvaluation c.subgroupPowers point)
    (hvalid : Norm.shapeValid c p.challenges (toTerminalInput t constants extra) point = true) :
    terminalTarget t p = Norm.checkedEvaluate c p.challenges (toTerminalInput t constants extra) point := by
  rw [Norm.checkedEvaluate, if_pos hvalid]
  exact fully_bound_target_is_norm_evaluate_of_cells t p c constants extra point h hc hlam hmap heta hprefix heq hsub

/-- The concrete engine hook (`Norm.withNormEvaluation`) computes this same
value when the proof's used claims are the cells and the initial transcript
carries these challenges; both are hypotheses. -/
theorem fully_bound_target_is_engine_terminal (e : Verifier.Engine) (i : Verifier.Initial) (proof : Verifier.Proof)
    (t : Tables) (p : Prepared) (c : Verifier.Config) (constants extra : List Verifier.Ext3) (point : List Verifier.Ext3)
    (h : Shape t p) (hc : Compatible c t p constants)
    (hlam : LambdaProvenance p) (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (heta : EtaProvenance (NormPolynomial.lift p.challenges.eta) t.bindings)
    (hprefix : PrefixAt point t.bindings)
    (heq : (cell t.eq).toVerifier = Norm.eqEvaluation p.challenges.tau point)
    (hsub : (cell t.subgroup).toVerifier = Norm.subgroupEvaluation c.subgroupPowers point)
    (hi : Norm.challengesFromInitial i = p.challenges)
    (hp : Verifier.normTerminalInput proof = toTerminalInput t constants extra) :
    terminalTarget t p = some ((Norm.withNormEvaluation e).logTerminal c i proof point) := by
  show terminalTarget t p = some (Norm.evaluate c (Norm.challengesFromInitial i) (Verifier.normTerminalInput proof) point)
  rw [hi, hp]
  exact fully_bound_target_is_norm_evaluate_of_cells t p c constants extra point h hc hlam hmap heta hprefix heq hsub

/-! ## (2) Binding all variables of one column -/

def bindColumn (column : List Element) (point : List Element) : List Element :=
  point.foldl (fun column r => DenseMleIndexed.bindBuffer column r) column

theorem bind_column_nil (column : List Element) : bindColumn column [] = column := rfl

theorem bind_column_cons (column : List Element) (r : Element) (rs : List Element) :
    bindColumn column (r :: rs) = bindColumn (DenseMleIndexed.bindBuffer column r) rs := rfl

theorem bind_buffer_nil (r : Element) : DenseMleIndexed.bindBuffer [] r = [] := rfl

theorem bind_column_empty (point : List Element) : bindColumn [] point = [] := by
  induction point with
  | nil => rfl
  | cons r rs ih => rw [bind_column_cons, bind_buffer_nil, ih]

/-- The adopted `bindMany` on a `⟨n, column⟩` state is the iterated
`bindBuffer` whenever the width suffices. -/
theorem bind_many_is_bind_column (point : List Element) :
    ∀ (n : Nat) (column : List Element), point.length ≤ n →
      DenseMleIndexed.bindMany point ⟨n, column⟩ = some ⟨n - point.length, bindColumn column point⟩ := by
  induction point with
  | nil => intro n column _; rfl
  | cons r rs ih =>
      intro n column hn
      have hpos : 0 < n := by rw [List.length_cons] at hn; omega
      have hsub : n - 1 - rs.length = n - (r :: rs).length := by rw [List.length_cons]; omega
      simp only [DenseMleIndexed.bindMany, DenseMleIndexed.positive_binding_exact ⟨n, column⟩ r hpos,
        bind, Option.bind]
      rw [ih (n-1) _ (by rw [List.length_cons] at hn; omega), hsub, bind_column_cons]

theorem bound_column_is_packed_fold (column point : List Element) (n : Nat)
    (hlen : column.length = 2^n) (hpoint : point.length = n) :
    (bindColumn column point).length = 1 ∧
    DenseMleIndexed.evaluate ⟨n, column⟩ point = some (cell (bindColumn column point)) ∧
    (cell (bindColumn column point)).toVerifier.val =
      Packed.fold (DenseMleIndexed.raw column) (DenseMleIndexed.raw point) := by
  have hv : DenseMleIndexed.Valid ⟨n, column⟩ := hlen
  obtain ⟨t, ht, hvalid, _, hraw⟩ := DenseMleIndexed.all_bindings_execute ⟨n, column⟩ point hv (by show point.length ≤ n; omega)
  rw [bind_many_is_bind_column point n column (by omega)] at ht
  have e : t = ⟨n - point.length, bindColumn column point⟩ := (Option.some.inj ht).symm
  subst e
  have h1 : (bindColumn column point).length = 1 := by
    have hv' : (bindColumn column point).length = 2^(n - point.length) := hvalid
    rw [hv', hpoint, Nat.sub_self, Nat.pow_zero]
  refine ⟨h1, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_singleton_of_length_one _ h1
    simp only [DenseMleIndexed.evaluate, hpoint, ne_eq, not_true_eq_false, if_false,
      bind_many_is_bind_column point n column (by omega), bind, Option.bind, ha]
    rfl
  · have h0 := congrArg (fun xs : List Arithmetic.Ext3 => xs.getD 0 Arithmetic.zero) hraw
    simp only [DenseMleIndexed.raw_getD] at h0
    exact h0

theorem raw_is_values (xs : List Element) : DenseMleIndexed.raw xs = (values xs).map Subtype.val := by
  rw [DenseMleIndexed.raw, values, List.map_map]
  rfl

/-- The single cell is the verifier's concrete `Connections.packedFold` of
the original column at the point (the width argument only pads). -/
theorem bound_cell_is_connections_packed_fold (column point : List Element) (n width : Nat)
    (hlen : column.length = 2^n) (hpoint : point.length = n) :
    (cell (bindColumn column point)).toVerifier = Connections.packedFold (values column) width (values point) := by
  apply Subtype.eq
  rw [Connections.packedFold_exact, ← raw_is_values, ← raw_is_values]
  exact (bound_column_is_packed_fold column point n hlen hpoint).2.2

/-! ## (3) Binding every variable of the tables -/

/-- The successful branch of the adopted `bindTables`. -/
def boundTables (t : Tables) (r : Element) : Tables :=
  { eq := DenseMleIndexed.bindBuffer t.eq r,
    subgroup := DenseMleIndexed.bindBuffer t.subgroup r,
    wires := t.wires.map (fun column => DenseMleIndexed.bindBuffer column r),
    sigmas := t.sigmas.map (fun column => DenseMleIndexed.bindBuffer column r),
    identityHelpers := t.identityHelpers.map (fun column => DenseMleIndexed.bindBuffer column r),
    sigmaHelpers := t.sigmaHelpers.map (fun column => DenseMleIndexed.bindBuffer column r),
    bindings := t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b r }),
    boundVariables := t.boundVariables+1,
    remaining := t.remaining-1 }

theorem bind_tables_positive (t : Tables) (r : Element) (hr : 0 < t.remaining) :
    bindTables t r = some (boundTables t r) := by
  rw [bindTables, if_neg (show t.remaining ≠ 0 by omega)]
  rfl

theorem bound_tables_shape (t : Tables) (p : Prepared) (r : Element) (h : Shape t p) (hr : 0 < t.remaining) :
    Shape (boundTables t r) p := by
  obtain ⟨t', ht', hs', _⟩ := bind_tables_shaped t p r h hr
  rw [bind_tables_positive t r hr] at ht'
  rw [← Option.some.inj ht'] at hs'
  exact hs'

/-- `bind_challenge` repeated over a whole point (the algebraic table part). -/
def bindTablesMany : List Element → Tables → Option Tables
  | [], t => some t
  | r :: rs, t => do
      let t' ← bindTables t r
      bindTablesMany rs t'

theorem bind_tables_many_cons (t : Tables) (r : Element) (rs : List Element) (hr : 0 < t.remaining) :
    bindTablesMany (r :: rs) t = bindTablesMany rs (boundTables t r) := by
  simp only [bindTablesMany, bind_tables_positive t r hr, bind, Option.bind]

theorem bind_tables_many_shaped (point : List Element) :
    ∀ (t : Tables) (p : Prepared), Shape t p → point.length ≤ t.remaining →
    ∃ t', bindTablesMany point t = some t' ∧ Shape t' p ∧
      t'.remaining + point.length = t.remaining ∧ t'.boundVariables = t.boundVariables + point.length ∧
      t'.eq = bindColumn t.eq point ∧ t'.subgroup = bindColumn t.subgroup point ∧
      t'.wires = t.wires.map (fun column => bindColumn column point) ∧
      t'.sigmas = t.sigmas.map (fun column => bindColumn column point) ∧
      t'.identityHelpers = t.identityHelpers.map (fun column => bindColumn column point) ∧
      t'.sigmaHelpers = t.sigmaHelpers.map (fun column => bindColumn column point) ∧
      ∃ pre : Binding → Element, t'.bindings = t.bindings.map (fun b => { b with prefixEq := pre b }) := by
  induction point with
  | nil =>
      intro t p h _
      refine ⟨t, rfl, h, by simp, by simp, rfl, rfl, ?_, ?_, ?_, ?_, ⟨Binding.prefixEq, ?_⟩⟩
      · exact (List.map_id' t.wires).symm
      · exact (List.map_id' t.sigmas).symm
      · exact (List.map_id' t.identityHelpers).symm
      · exact (List.map_id' t.sigmaHelpers).symm
      · exact (List.map_id' t.bindings).symm
  | cons r rs ih =>
      intro t p h hlen
      have hr : 0 < t.remaining := by rw [List.length_cons] at hlen; omega
      obtain ⟨t', ht', hshape', hrem', hbound', heq', hsub', hw', hs', hi', hh', φ, hb'⟩ :=
        ih (boundTables t r) p (bound_tables_shape t p r h hr) (by
          show rs.length ≤ t.remaining - 1
          rw [List.length_cons] at hlen
          omega)
      refine ⟨t', ?_, hshape', ?_, ?_, heq'.trans rfl, hsub'.trans rfl, ?_, ?_, ?_, ?_,
        ⟨fun b => φ { b with prefixEq := prefixUpdate t b r }, ?_⟩⟩
      · rw [bind_tables_many_cons t r rs hr, ht']
      · have e : t'.remaining + rs.length = t.remaining - 1 := hrem'
        rw [List.length_cons]
        omega
      · have e : t'.boundVariables = t.boundVariables + 1 + rs.length := hbound'
        rw [List.length_cons]
        omega
      · refine hw'.trans ?_
        show (t.wires.map (fun column => DenseMleIndexed.bindBuffer column r)).map (fun column => bindColumn column rs) = _
        rw [List.map_map]
        rfl
      · refine hs'.trans ?_
        show (t.sigmas.map (fun column => DenseMleIndexed.bindBuffer column r)).map (fun column => bindColumn column rs) = _
        rw [List.map_map]
        rfl
      · refine hi'.trans ?_
        show (t.identityHelpers.map (fun column => DenseMleIndexed.bindBuffer column r)).map (fun column => bindColumn column rs) = _
        rw [List.map_map]
        rfl
      · refine hh'.trans ?_
        show (t.sigmaHelpers.map (fun column => DenseMleIndexed.bindBuffer column r)).map (fun column => bindColumn column rs) = _
        rw [List.map_map]
        rfl
      · refine hb'.trans ?_
        show (t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b r })).map (fun b => { b with prefixEq := φ b }) = _
        rw [List.map_map]
        rfl

/-- (3) A point of length `remaining` binds everything: the result keeps
`Shape`, has `remaining = 0`, every column is a single cell, and each column
is the iterated `bindBuffer` of its original. -/
theorem fully_bound_tables_from_initial (t : Tables) (p : Prepared) (point : List Element)
    (h : Shape t p) (hpoint : point.length = t.remaining) :
    ∃ t', bindTablesMany point t = some t' ∧ Shape t' p ∧ FullyBound t' ∧
      t'.boundVariables = t.boundVariables + t.remaining ∧ t'.wires.length = t.wires.length ∧
      t'.eq = bindColumn t.eq point ∧ t'.subgroup = bindColumn t.subgroup point ∧
      t'.wires = t.wires.map (fun column => bindColumn column point) ∧
      t'.sigmas = t.sigmas.map (fun column => bindColumn column point) ∧
      t'.identityHelpers = t.identityHelpers.map (fun column => bindColumn column point) ∧
      t'.sigmaHelpers = t.sigmaHelpers.map (fun column => bindColumn column point) ∧
      ∃ pre : Binding → Element, t'.bindings = t.bindings.map (fun b => { b with prefixEq := pre b }) := by
  obtain ⟨t', ht', hshape', hrem', hbound', heq', hsub', hw', hs', hi', hh', hb'⟩ :=
    bind_tables_many_shaped point t p h (by omega)
  have hr0 : t'.remaining = 0 := by omega
  refine ⟨t', ht', hshape', shape_zero_remaining_fully_bound t' p hshape' hr0, by omega, ?_,
    heq', hsub', hw', hs', hi', hh', hb'⟩
  rw [hw', List.length_map]

theorem column_at_map (f : List Element → List Element) (hf : f [] = []) (columns : List (List Element)) (j : Nat) :
    columnAt (columns.map f) j = f (columnAt columns j) := by
  unfold columnAt
  have h := List.getD_map columns ([] : List Element) (n := j) f
  rw [hf] at h
  exact h

/-- Every fully bound cell is the packed fold of its original column at the
bound point (LSB-first, the adopted `Packed.fold` order). -/
theorem fully_bound_cells_are_packed_folds (t t' : Tables) (p : Prepared) (point : List Element)
    (h : Shape t p) (hpoint : point.length = t.remaining) (hb : bindTablesMany point t = some t') :
    (cell t'.eq).toVerifier.val = Packed.fold (DenseMleIndexed.raw t.eq) (DenseMleIndexed.raw point) ∧
    (cell t'.subgroup).toVerifier.val = Packed.fold (DenseMleIndexed.raw t.subgroup) (DenseMleIndexed.raw point) ∧
    ∀ j, j < t.wires.length →
      (cell (columnAt t'.wires j)).toVerifier.val =
        Packed.fold (DenseMleIndexed.raw (columnAt t.wires j)) (DenseMleIndexed.raw point) ∧
      (cell (columnAt t'.sigmas j)).toVerifier.val =
        Packed.fold (DenseMleIndexed.raw (columnAt t.sigmas j)) (DenseMleIndexed.raw point) ∧
      (cell (columnAt t'.identityHelpers j)).toVerifier.val =
        Packed.fold (DenseMleIndexed.raw (columnAt t.identityHelpers j)) (DenseMleIndexed.raw point) ∧
      (cell (columnAt t'.sigmaHelpers j)).toVerifier.val =
        Packed.fold (DenseMleIndexed.raw (columnAt t.sigmaHelpers j)) (DenseMleIndexed.raw point) := by
  obtain ⟨t'', ht'', _, _, _, _, heq, hsub, hw, hs, hi, hh, _⟩ := fully_bound_tables_from_initial t p point h hpoint
  rw [ht''] at hb
  have e : t'' = t' := Option.some.inj hb
  subst e
  rcases h with ⟨he, hg, hws, hss, his, hhs, _, _, _⟩
  refine ⟨?_, ?_, fun j hj => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [heq]
    exact (bound_column_is_packed_fold t.eq point t.remaining he hpoint).2.2
  · rw [hsub]
    exact (bound_column_is_packed_fold t.subgroup point t.remaining hg hpoint).2.2
  · rw [hw, column_at_map (fun column => bindColumn column point) (bind_column_empty point)]
    exact (bound_column_is_packed_fold _ point t.remaining (column_at_shape _ _ _ j hws hj).2 hpoint).2.2
  · rw [hs, column_at_map (fun column => bindColumn column point) (bind_column_empty point)]
    exact (bound_column_is_packed_fold _ point t.remaining (column_at_shape _ _ _ j hss hj).2 hpoint).2.2
  · rw [hi, column_at_map (fun column => bindColumn column point) (bind_column_empty point)]
    exact (bound_column_is_packed_fold _ point t.remaining (column_at_shape _ _ _ j his hj).2 hpoint).2.2
  · rw [hh, column_at_map (fun column => bindColumn column point) (bind_column_empty point)]
    exact (bound_column_is_packed_fold _ point t.remaining (column_at_shape _ _ _ j hhs hj).2 hpoint).2.2

/-! ## (5) The last round evaluates to the bound terminal target -/

theorem foldl_add_congr {α : Type} (f g : α → Verifier.Ext3) (xs : List α) (h : ∀ a ∈ xs, f a = g a) :
    ∀ acc : Verifier.Ext3,
      xs.foldl (fun acc x => Verifier.add acc (f x)) acc = xs.foldl (fun acc x => Verifier.add acc (g x)) acc := by
  induction xs with
  | nil => intro acc; rfl
  | cons x xs ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, h x (List.mem_cons_self _ _)]
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

theorem bound_cell_is_line (column : List Element) (x : Element) (h : column.length = 2^1) :
    cell (DenseMleIndexed.bindBuffer column x) = line column 0 x :=
  bound_cell_is_round_line column 0 x (by rw [h]; decide)

/-- At `remaining = 1` the prover's `wireValues` of the single suffix are the
slice reads of the tables bound at `x`. -/
theorem last_round_wire_values (t : Tables) (p : Prepared) (x : Element) (j : Nat)
    (h : Shape t p) (hr : t.remaining = 1) (hj : j < t.wires.length) :
    sliceWireValues p (cellValues (boundTables t x).wires) (cellValues (boundTables t x).sigmas)
        (cellValues (boundTables t x).identityHelpers) (cellValues (boundTables t x).sigmaHelpers)
        (cell (boundTables t x).subgroup).toVerifier j =
      wireValues t p 0 j x := by
  rcases h with ⟨_, hg, hw, hs, hi, hh, _, _, _⟩
  rw [hr] at hg hw hs hi hh
  have hwl := (column_at_shape _ _ _ j hw hj).2
  have hsl := (column_at_shape _ _ _ j hs hj).2
  have hil := (column_at_shape _ _ _ j hi hj).2
  have hhl := (column_at_shape _ _ _ j hh hj).2
  simp only [sliceWireValues, wireValues, boundTables, cell_values_getD,
    column_at_map (fun column => DenseMleIndexed.bindBuffer column x) (bind_buffer_nil x),
    bound_cell_is_line _ x hwl, bound_cell_is_line _ x hsl, bound_cell_is_line _ x hil,
    bound_cell_is_line _ x hhl, bound_cell_is_line _ x hg]

/-- At `remaining = 1` the prover's `piValue` of a binding is the terminal
PI term of that binding after the bind (prefix updated, wire bound). -/
theorem last_round_pi_term (t : Tables) (p : Prepared) (x : Element) (b : Binding)
    (h : Shape t p) (hr : t.remaining = 1) (hb : b ∈ t.bindings) :
    terminalPiTerm (boundTables t x) { b with prefixEq := prefixUpdate t b x } = piValue t b x := by
  have hbd := h.2.2.2.2.2.2.2.2 b hb
  rw [hr] at hbd
  have hcol := (column_at_shape _ _ _ b.column h.2.2.1 hbd.2).2
  rw [hr] at hcol
  have hsuf : piSuffix t b = 0 := Nat.div_eq_of_lt hbd.1
  simp only [terminalPiTerm, piValue, boundTables, prefix_update_is_pi_factor,
    column_at_map (fun column => DenseMleIndexed.bindBuffer column x) (bind_buffer_nil x),
    bound_cell_is_line _ x hcol, hsuf]

theorem bound_tables_bindings (t : Tables) (r : Element) :
    (boundTables t r).bindings = t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b r }) := rfl

/-- HONEST PROVER ONLY. At `remaining = 1`, `round_sum_at` at the final
challenge `x` (the prover's single-suffix target plus its PI terms) is the
terminal target of the tables bound at `x`. This is the honest last-round
value; no statement about a dishonest prover's messages is made. -/
theorem last_round_target_is_bound_terminal (t : Tables) (p : Prepared) (x : Element)
    (h : Shape t p) (hr : t.remaining = 1) :
    roundSumAt t p x = some (roundValue t p x) ∧
    terminalTarget (boundTables t x) p = some (roundValue t p x) := by
  refine ⟨round_sum_at_shaped t p x h (by omega), ?_⟩
  have hl := h.2.2.2.2.2.2.2.1
  have he : t.eq.length = 2^1 := by rw [h.1, hr]
  have hrange : List.range (t.eq.length / 2) = [0] := by rw [he]; decide
  have heqcell : cell (boundTables t x).eq = line t.eq 0 x := bound_cell_is_line t.eq x he
  have hlw : (cellValues (boundTables t x).wires).length = p.lambdaPowers.length := by
    rw [cell_values_length, hl]
    exact List.length_map _ _
  have hls : (cellValues (boundTables t x).sigmas).length = p.lambdaPowers.length := by
    rw [cell_values_length, hl, ← h.2.2.2.1.1]
    exact List.length_map _ _
  have hli : (cellValues (boundTables t x).identityHelpers).length = p.lambdaPowers.length := by
    rw [cell_values_length, hl, ← h.2.2.2.2.1.1]
    exact List.length_map _ _
  have hlh : (cellValues (boundTables t x).sigmaHelpers).length = p.lambdaPowers.length := by
    rw [cell_values_length, hl, ← h.2.2.2.2.2.1.1]
    exact List.length_map _ _
  have hloop : targetLoop p (cellValues (boundTables t x).wires) (cellValues (boundTables t x).sigmas)
      (cellValues (boundTables t x).identityHelpers) (cellValues (boundTables t x).sigmaHelpers)
      (cell (boundTables t x).subgroup).toVerifier =
      ((List.range t.wires.length).foldl (fun acc j => Verifier.add acc (contribution t p 0 x j).1) Verifier.zero,
       (List.range t.wires.length).foldl (fun acc j => Verifier.add acc (contribution t p 0 x j).2) Verifier.zero) := by
    rw [target_loop_splits, hl]
    have hc := foldl_pair_congr
      (fun j : Nat => sliceContribution p (cellValues (boundTables t x).wires) (cellValues (boundTables t x).sigmas)
        (cellValues (boundTables t x).identityHelpers) (cellValues (boundTables t x).sigmaHelpers)
        (cell (boundTables t x).subgroup).toVerifier j)
      (fun j : Nat => contribution t p 0 x j) (List.range t.wires.length)
      (fun j hj => by
        simp only [sliceContribution, contribution, last_round_wire_values t p x j h hr (List.mem_range.mp hj)])
      Verifier.zero Verifier.zero
    exact Prod.ext hc.1 hc.2
  have hpi : terminalBinding (boundTables t x) =
      t.bindings.foldl (fun acc b => Verifier.add acc (piValue t b x)) Verifier.zero := by
    have hcongr := foldl_add_congr
      (fun b : Binding => terminalPiTerm (boundTables t x) { b with prefixEq := prefixUpdate t b x })
      (fun b : Binding => piValue t b x) t.bindings (fun b hb => last_round_pi_term t p x b h hr hb) Verifier.zero
    rw [terminalBinding, bound_tables_bindings, List.foldl_map]
    exact hcongr
  rw [terminalTarget, targetValue, if_pos ⟨hlw, hls, hli, hlh⟩, hloop, hpi, heqcell, roundValue, hrange,
    List.foldl_cons, List.foldl_nil, Algebra.vzero_add, rowValue]

/-! ## (6) Honest prover: provenance of the prefixes and eta weights -/

theorem bind_tables_many_prefix (point : List Element) :
    ∀ (t t' : Tables) (pre : List Element),
      pre.length = t.boundVariables → point.length ≤ t.remaining → bindTablesMany point t = some t' →
      (∀ b ∈ t.bindings, b.prefixEq.toVerifier = Norm.booleanRowEq b.row (pre.map Element.toVerifier)) →
      ∀ b ∈ t'.bindings, b.prefixEq.toVerifier = Norm.booleanRowEq b.row ((pre ++ point).map Element.toVerifier) := by
  induction point with
  | nil =>
      intro t t' pre _ _ hb hp
      have e : t = t' := Option.some.inj hb
      subst e
      simpa using hp
  | cons r rs ih =>
      intro t t' pre hlen hrem hb hp
      have hr : 0 < t.remaining := by rw [List.length_cons] at hrem; omega
      rw [bind_tables_many_cons t r rs hr] at hb
      have hp' : ∀ b ∈ (boundTables t r).bindings,
          b.prefixEq.toVerifier = Norm.booleanRowEq b.row ((pre ++ [r]).map Element.toVerifier) := by
        intro b' hb'
        have hb'' : b' ∈ t.bindings.map (fun b => { b with prefixEq := prefixUpdate t b r }) := hb'
        obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hb''
        exact bound_prefix_is_boolean_row_eq t b r pre hlen (hp b hbm)
      have hnext := ih (boundTables t r) t' (pre ++ [r])
        (by
          show (pre ++ [r]).length = t.boundVariables + 1
          rw [List.length_append, List.length_singleton, hlen])
        (by
          show rs.length ≤ t.remaining - 1
          rw [List.length_cons] at hrem
          omega)
        hb hp'
      rw [List.append_assoc, List.singleton_append] at hnext
      exact hnext

theorem eta_provenance_map (eta : Element) (φ : Binding → Element) (bs : List Binding)
    (h : EtaProvenance eta bs) : EtaProvenance eta (bs.map (fun b => { b with prefixEq := φ b })) := by
  intro pair hp
  rw [List.enum_map] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h q hq

theorem wire_map_matches_map (wireMap : Verifier.Bytes) (φ : Binding → Element) (bs : List Binding)
    (h : WireMapMatches wireMap bs) : WireMapMatches wireMap (bs.map (fun b => { b with prefixEq := φ b })) := by
  intro pair hp
  rw [List.enum_map] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h q hq

theorem build_bindings_eta_provenance_from (eta : Element) (pairs : List (Nat × Nat × Verifier.Base)) :
    ∀ start, ∀ pair ∈ (buildBindings eta (eta^start) pairs).enumFrom start, pair.2.etaPower = eta^pair.1 := by
  induction pairs with
  | nil => intro start pair hp; simp [buildBindings] at hp
  | cons entry rest ih =>
      obtain ⟨row, column, value⟩ := entry
      intro start pair hp
      rw [buildBindings, List.enumFrom_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · rw [← pow_succ] at hp
        exact ih (start+1) pair hp

/-- `from_base` (446-460) produces `eta^i` weights. -/
theorem build_bindings_eta_provenance (eta : Element) (pairs : List (Nat × Nat × Verifier.Base)) :
    EtaProvenance eta (buildBindings eta 1 pairs) := by
  have h := build_bindings_eta_provenance_from eta pairs 0
  rw [pow_zero] at h
  exact h

/-- HONEST PROVER ONLY. A fresh `Shape` table (no bound variables, bindings
from `buildBindings`) bound over the whole point reaches a fully bound state
whose terminal target is the verifier's formula on its cells, with the eq
and subgroup values being the cells the tables hold. Remaining hypotheses:
`Compatible`, `LambdaProvenance`, `WireMapMatches` (VK/config
correspondence). Eq/subgroup provenance is still separate, as in
`fully_bound_target_is_norm_evaluate_of_cells`. -/
theorem honest_prover_terminal (t : Tables) (p : Prepared) (c : Verifier.Config) (constants extra : List Verifier.Ext3)
    (point : List Element) (pairs : List (Nat × Nat × Verifier.Base))
    (h : Shape t p) (h0 : t.boundVariables = 0) (hpoint : point.length = t.remaining)
    (hbuild : t.bindings = buildBindings (NormPolynomial.lift p.challenges.eta) 1 pairs)
    (hc : Compatible c t p constants) (hlam : LambdaProvenance p)
    (hmap : WireMapMatches c.publicInputWireMap t.bindings) :
    ∃ t', bindTablesMany point t = some t' ∧ FullyBound t' ∧
      PrefixAt (point.map Element.toVerifier) t'.bindings ∧
      terminalTarget t' p = some (evaluateWith c p.challenges (toTerminalInput t' constants extra)
        (cell t'.eq).toVerifier (cell t'.subgroup).toVerifier (point.map Element.toVerifier)) := by
  obtain ⟨t', ht', hshape', hfull, _, hwl, _, _, _, _, _, _, φ, hb'⟩ :=
    fully_bound_tables_from_initial t p point h hpoint
  have hc' : Compatible c t' p constants := ⟨by rw [hwl]; exact hc.1, hc.2.1, hc.2.2⟩
  have hprefix : PrefixAt (point.map Element.toVerifier) t'.bindings := by
    have hp := bind_tables_many_prefix point t t' [] (by simp [h0]) (by omega) ht' (by
      intro b hb
      rw [hbuild] at hb
      exact initial_prefix_provenance _ pairs b hb)
    simpa using hp
  have heta : EtaProvenance (NormPolynomial.lift p.challenges.eta) t'.bindings := by
    rw [hb', hbuild]
    exact eta_provenance_map _ φ _ (build_bindings_eta_provenance _ pairs)
  have hmap' : WireMapMatches c.publicInputWireMap t'.bindings := by
    rw [hb']
    exact wire_map_matches_map _ φ _ hmap
  exact ⟨t', ht', hfull, hprefix,
    target_identity t' p c constants extra (point.map Element.toVerifier) hshape' hc' hlam hmap' heta hprefix⟩

/-! ## (7) A concrete example: one variable, one routed wire, one public input -/

namespace Example

def e (n : Nat) : Element := ⟨Norm.embed n⟩

/-- eq table for `tau = [3]`: `[1 - 3, 3]`; subgroup table for generator 7: `[1, 7]`. -/
def tables : Tables :=
  { eq := [e 1 - e 3, e 3], subgroup := [e 1, e 7],
    wires := [[e 5, e 9]], sigmas := [[e 2, e 4]],
    identityHelpers := [[e 11, e 13]], sigmaHelpers := [[e 17, e 19]],
    bindings := buildBindings (e 13) 1 [(1, 0, ⟨23, by decide⟩)],
    boundVariables := 0, remaining := 1 }

/-- `[beta, gamma, lambda, rho, kappa, eta, xi, tau]`. -/
def challenges : Norm.Challenges :=
  ⟨Norm.embed 2, Norm.embed 3, Norm.embed 5, Norm.embed 7, Norm.embed 11, Norm.embed 13, Norm.embed 17,
   [Norm.embed 3]⟩

def prepared : Prepared := ⟨challenges, [⟨4, by decide⟩], runningPowers (e 5) 1 1⟩

def config : Verifier.Config :=
  { degreeBits := 1, numConstants := 0, numRouted := 1, numWires := 1, numPublicInputs := 1,
    numSelectors := 0, numGateConstraints := 0, quotientDegree := 0, gateRows := 0, indexBits := 0,
    kIs := [⟨4, by decide⟩], subgroupPowers := [⟨7, by decide⟩], publicInputWireMap := [1, 0, 0],
    gatesEncoding := [], whirEncoding := [], circuitDigest := [], circuitConfigDigest := ⟨0, by decide⟩,
    whirProtocolId := [], whirSessionId := [] }

def point : List Verifier.Ext3 := [(e 6).toVerifier]

def bound : Tables := boundTables tables (e 6)

theorem tables_shape : Shape tables prepared := by
  unfold Shape ColumnShape
  decide

theorem binds : bindTablesMany [e 6] tables = some bound := rfl

theorem bound_shape : Shape bound prepared := bound_tables_shape tables prepared (e 6) tables_shape (by decide)

theorem bound_fully : FullyBound bound := by
  unfold FullyBound ColumnShape
  decide

theorem compatible : Compatible config bound prepared [] := by
  unfold Compatible
  decide

theorem lambda_provenance : LambdaProvenance prepared :=
  running_powers_lambda_provenance challenges [⟨4, by decide⟩] 1

theorem wire_map : WireMapMatches config.publicInputWireMap bound.bindings := by
  unfold WireMapMatches
  decide

theorem eta_provenance : EtaProvenance (NormPolynomial.lift challenges.eta) bound.bindings := by
  unfold EtaProvenance
  decide

theorem prefix_at : PrefixAt point bound.bindings := by
  unfold PrefixAt
  decide

/-- Here the eq cell really is the verifier's eq-MLE: the table was `[1-tau, tau]`. -/
theorem eq_cell : (cell bound.eq).toVerifier = Norm.eqEvaluation challenges.tau point := by decide

theorem subgroup_cell : (cell bound.subgroup).toVerifier = Norm.subgroupEvaluation config.subgroupPowers point := by
  decide

theorem terminal_is_verifier :
    terminalTarget bound prepared = some (Norm.evaluate config challenges (toTerminalInput bound [] []) point) :=
  fully_bound_target_is_norm_evaluate_of_cells bound prepared config [] [] point bound_shape compatible
    lambda_provenance wire_map eta_provenance prefix_at eq_cell subgroup_cell

theorem last_round : roundSumAt tables prepared (e 6) = some (roundValue tables prepared (e 6)) ∧
    terminalTarget bound prepared = some (roundValue tables prepared (e 6)) :=
  last_round_target_is_bound_terminal tables prepared (e 6) tables_shape rfl

/-- The explicit value (base-field only because every input is a base
embedding), computed by the prover-side formula. -/
theorem terminal_value :
    terminalTarget bound prepared = some ⟨⟨71285243690, 0, 0⟩, ⟨by decide, by decide, by decide⟩⟩ := by decide

/-- The verifier's `Norm.evaluate` on the assembled input yields the same
explicit value, through `terminal_is_verifier` rather than by evaluating the
well-founded `runWires` loop. -/
theorem verifier_value :
    Norm.evaluate config challenges (toTerminalInput bound [] []) point =
      ⟨⟨71285243690, 0, 0⟩, ⟨by decide, by decide, by decide⟩⟩ := by
  have h := terminal_is_verifier
  rw [terminal_value] at h
  exact (Option.some.inj h).symm

/-- A non-routed witness tail: the same circuit with `numWires = 2 >
numRouted = 1` and the witness `[wire cell, 99]`. -/
def extra : List Verifier.Ext3 := [(e 99).toVerifier]

def configWide : Verifier.Config := { config with numWires := 2 }

theorem compatible_wide : Compatible configWide bound prepared [] := by
  unfold Compatible
  decide

/-- The checked entry point's guard accepts the two-entry witness (it would
reject the routed cells alone, whose length is 1 ≠ `numWires`). -/
theorem shape_valid_wide :
    Norm.shapeValid configWide challenges (toTerminalInput bound [] extra) point = true := by
  decide

/-- The non-routed tail does not change the verifier's value. -/
theorem checked_value_wide :
    Norm.checkedEvaluate configWide challenges (toTerminalInput bound [] extra) point =
      some ⟨⟨71285243690, 0, 0⟩, ⟨by decide, by decide, by decide⟩⟩ := by
  exact (fully_bound_target_is_checked_evaluate bound prepared configWide [] extra point bound_shape
    compatible_wide lambda_provenance wire_map eta_provenance prefix_at eq_cell subgroup_cell
    shape_valid_wide).symm.trans terminal_value

end Example

end Audit.Wire3.NormTerminalBinding
