import Audit.Wire3.NormTerminalBinding
import Audit.Wire3.GateTerminalBinding

/-!
# Provenance of the eq and subgroup columns (wire v3)

This module DISCHARGES the two provenance hypotheses that the adopted
`Audit.Wire3.NormTerminalBinding`, `Audit.Wire3.GateTerminalBinding` and the
glue `Audit.Wire3.IntegratedTerminalChain` keep visible: that the fully bound
eq cell equals `Norm.eqEvaluation tau point`, and (norm side) that the fully
bound subgroup cell equals `Norm.subgroupEvaluation powers point`.

## Rust/Solidity sources reviewed (worktree intmax-plonky2-lean-wire3)

* `mle/src/sumcheck/gate_ext3_v2.rs:26-39` (`ext3_eq_evals`) and
  `mle/src/permutation/norm_logup.rs:360-374` (`eq_evals_ext3`): the two Ext3
  builders on the wire-v3 path. They are the SAME loop nest with renamed
  binders, not byte-identical copies. `mle/src/eq_poly.rs:13-39` (`eq_evals`)
  is the generic base-field builder on the older path (callers `prover.rs`,
  `dense_mle.rs`); it has an `n == 0` early return and a statement-form branch,
  and is modelled here only in so far as the nest coincides. The table is
  `vec![ONE; 1 << tau.len()]`, then for each coordinate `j` (outer loop, in
  `tau` order) every entry `i` is multiplied ON THE RIGHT by `1 - tau_j` when
  `(i >> j) & 1 == 0` and by `tau_j` otherwise. `eqPass`/`eqTableFrom`/`eqTable`
  below are that loop nest, in that order, with that multiplication order.
* `mle/src/sumcheck/ext3.rs:22-45` (`Ext3DenseMle::new`, `from_base`),
  `47-57` (`bind_variable_in_place`: `evaluations[i] = (1-x)*evaluations[2i] +
  x*evaluations[2i+1]` for `i < half`, then truncate), `59-66` (`evaluate`).
  Binding is the adopted `DenseMleIndexed.bindBuffer`; the pairing `2i`/`2i+1`
  is why the LOW index bit — i.e. coordinate `0`, `tau.head` — binds FIRST.
* `mle/src/permutation/norm_logup.rs:414-491` (`NormLogupMleState::from_base`):
  `eq: Ext3DenseMle::new(eq_evals_ext3(tau))` and
  `subgroup: Ext3DenseMle::from_base(subgroup)` (487-488).
* `mle/src/prover_v2.rs:250-258` and `369-377`: `subgroup_gen_powers` is
  `let mut value = subgroup[1]; for _ in 0..degree_bits { push value; value *= value }`.
  `mle/src/prover_v2.rs:439,481` pass `tables.subgroup` to the norm prover.
* `plonky2/src/plonk/circuit_data.rs:691-717` (`EvaluationTables.subgroup`,
  "evaluation domain subgroup of order `degree`"),
  `plonky2/src/plonk/prover.rs:241`, `plonky2/src/plonk/circuit_builder.rs:1214`
  (`F::two_adic_subgroup(degree_bits)`) and `field/src/types.rs:274-283,429-433`
  (`two_adic_subgroup` = `generator.powers().take(1 << n_log)`, `powers()` =
  `shifted_powers(ONE)`): the subgroup table IS `[g^0, g^1, ..., g^(2^n-1)]`.
* `mle/src/verifier_v2.rs:131-146` (the VK's `subgroup_gen_powers` are
  re-derived and compared), `396-412` (`subgroup_eval = Π_j ((1 - r_j) +
  r_j * g_j)` over `log_point.zip(vk.subgroup_gen_powers)`, then the joint norm
  terminal), `422-434` (`ext3_eq_eval(gate_tau, gate_point) * gate_terminal`).
* `mle/contracts/src/OuterLogupExt3Verifier.sol:860-877` (`_eqEvaluation`,
  the `1 - tau - x + 2*tau*x` form) and `878-893` (`_subgroupEvaluation`,
  `1 + x*(g-1)` with a base-field scalar multiply), used at 226 and 342-343.

## Adopted Lean reused

`Audit.Wire3.Norm` (`eqFactor`/`subgroupFactor`/`productLoop`/`eqEvaluation`/
`subgroupEvaluation` 105-117, `booleanFactor`/`booleanRowEq` 139-142),
`Audit.Wire3.Algebra` (`norm_eq_factor_matches_product_form` 215-220,
`norm_subgroup_factor_matches_rust` 234-238) and the `CommRing`/`Field`
instances of `Audit.Wire3.GoldilocksExt3Field.Element` (58-83, 143-148),
`Audit.Wire3.DenseMleIndexed` (`bindBuffer` 90-91,
`bind_buffer_reads_exact_line` 100-108, `bind_buffer_length` 93-98, `State`,
`Valid`, `bindMany`, `evaluate`), `Audit.Wire3.Packed` (`fold` 31),
`Audit.Wire3.NormDenseRound` (`Tables`/`Shape` 56-96, `values` 236),
`Audit.Wire3.NormTerminalBinding` (`cell` 95, `bindColumn` 595-596,
`bind_many_is_bind_column` 612-623, `bound_column_is_packed_fold` 625-647,
`bindTablesMany` 688-693, `fully_bound_tables_from_initial` 758-774,
`fully_bound_target_is_norm_evaluate_of_cells` 546-557,
`honest_prover_terminal` 998-1020),
`Audit.Wire3.GateTerminalBinding` (`ProverState` 163-171, `bindAll` 245-253,
`bind_all_columns` 263-265, `Cells` 362-366, `bound_terminal_is_engine_gate_terminal`
770-799, `honest_last_round_is_engine_gate_terminal` 807-832).

## What is proved

1. `eqTable` is the source loop nest verbatim; `eq_table_length` gives
   `2 ^ tau.length`; `eq_table_getD`/`eq_table_entry_is_boolean_row_eq` give
   that entry `i` IS the adopted per-row product `Norm.booleanRowEq i tau`.
   `row_prod_even`/`row_prod_odd`/`eq_table_pair_split`/
   `first_binding_uses_head_coordinate` prove the bit convention: the pair
   `bind_variable_in_place` reads (`2k`, `2k+1`) is exactly the
   `1 - tau_0` / `tau_0` split of one higher-coordinate row, so the LOW index
   bit binds first.
2. `bound_eq_table` / `bound_eq_table_is_eq_evaluation`: binding the eq table
   over a full-width point with the adopted `bindColumn` leaves ONE cell equal
   to `Norm.eqEvaluation tau point`. The route is the direct doubling
   recursion `bound_column_of_row_products`; all field identities come from the
   adopted `CommRing Element` instance (i.e. from `Audit.Wire3.Algebra`).
3. `subgroupTable` is `powers().take(2^n)`; `bound_subgroup_table_is_subgroup_evaluation`
   proves the exact relation that holds. NOTE: the verifier does NOT fold the
   subgroup table at all — it multiplies `(1 - r_j) + r_j * g^(2^j)` over the
   VK's `subgroup_gen_powers`. What is proved is that this product IS the
   fully bound cell (equivalently, by `subgroup_table_packed_fold`, the adopted
   `Packed.fold`) of the prover's geometric table.
4. `fully_bound_target_is_norm_evaluate_of_columns`,
   `honest_prover_terminal_of_columns`,
   `bound_terminal_is_engine_gate_terminal_of_eq_table` and
   `honest_last_round_is_engine_gate_terminal_of_eq_table` restate the adopted
   theorems with `heq` (and, on the norm side, `hsub`) REPLACED by "the eq
   column IS `eqTable tau`" / "the subgroup column IS `subgroupTable g n`".
5. Concrete `tau`-length 1 and 2 examples for both tables.

## Boundaries (explicitly NOT proved)

* `SubgroupPowersProvenance` is a NAMED VISIBLE HYPOTHESIS: that the VK's
  `subgroup_gen_powers` embed to the repeated squares of the generator whose
  powers fill the prover's subgroup table. Rust checks exactly this at
  verifier_v2.rs:131-146 by recomputing `F::two_adic_subgroup(degree_bits)`,
  but the adopted model has no model of plonky2's `two_adic_subgroup` or of
  the VK's generator derivation, so nothing in the adopted audit determines
  those powers; the predicate itself IS stated here (via `Arithmetic.mul` on
  `Base.val`), it simply cannot be discharged. It is kept as a visible
  hypothesis rather than proving something weaker silently.
* `NormColumnProvenance.tauValues` / the gate `htau`, `hpt` hypotheses connect
  the prover's challenge lists to the transcript-derived `tau`/`point`. That is
  Fiat--Shamir/transcript plumbing, outside this module.
* Nothing here is a soundness, WHIR/PCS, transcript, memory-refinement or
  Rust/Yul-compilation statement. `bind_variable_in_place`'s in-place mutation
  is the adopted functional model, not a memory refinement.
* The `_of_columns` / `honest_*` corollaries built on
  `honest_prover_terminal` and `honest_last_round_is_engine_gate_terminal` are
  HONEST-PROVER-ONLY, exactly as the adopted theorems they restate: they say
  what an honest prover's tables evaluate to, never that a verifier-accepted
  claim came from such a prover.
-/

namespace Audit.Wire3.EqTableProvenance

open Audit.Wire3 GoldilocksExt3Field NormDenseRound NormTerminalBinding

/-! ## 1. The eq-evaluation table builder -/

def bitFactor (t : Element) (j i : Nat) : Element :=
  if i / 2 ^ j % 2 = 0 then 1 - t else t

def eqPass (t : Element) (j : Nat) : Nat → List Element → List Element
  | _, [] => []
  | i, e :: rest => e * bitFactor t j i :: eqPass t j (i + 1) rest

def eqTableFrom : Nat → List Element → List Element → List Element
  | _, [], table => table
  | j, t :: rest, table => eqTableFrom (j + 1) rest (eqPass t j 0 table)

def eqTable (tau : List Element) : List Element :=
  eqTableFrom 0 tau (List.replicate (2 ^ tau.length) 1)

theorem eq_pass_length (t : Element) (j : Nat) :
    ∀ (i : Nat) (xs : List Element), (eqPass t j i xs).length = xs.length
  | _, [] => rfl
  | i, _ :: rest => by simp only [eqPass, List.length_cons, eq_pass_length t j (i+1) rest]

theorem eq_pass_getD (t : Element) (j : Nat) :
    ∀ (i : Nat) (xs : List Element) (k : Nat),
      (eqPass t j i xs).getD k 0 = xs.getD k 0 * bitFactor t j (i + k)
  | _, [], k => by simp only [eqPass, List.getD_nil, zero_mul]
  | i, e :: _rest, 0 => by simp only [eqPass, List.getD_cons_zero, Nat.add_zero]
  | i, e :: rest, k+1 => by
      simp only [eqPass, List.getD_cons_succ, eq_pass_getD t j (i+1) rest k]
      rw [show i + 1 + k = i + (k+1) by omega]

def rowProdFrom : Nat → List Element → Nat → Element
  | _, [], _ => 1
  | j, t :: rest, i => bitFactor t j i * rowProdFrom (j+1) rest i

theorem eq_table_from_length :
    ∀ (tau : List Element) (j : Nat) (table : List Element),
      (eqTableFrom j tau table).length = table.length
  | [], _, _ => rfl
  | t :: rest, j, table => by
      simp only [eqTableFrom, eq_table_from_length rest (j+1) (eqPass t j 0 table), eq_pass_length]

theorem eq_table_from_getD :
    ∀ (tau : List Element) (j : Nat) (table : List Element) (i : Nat),
      (eqTableFrom j tau table).getD i 0 = table.getD i 0 * rowProdFrom j tau i
  | [], _, table, i => by simp only [eqTableFrom, rowProdFrom, mul_one]
  | t :: rest, j, table, i => by
      rw [eqTableFrom, eq_table_from_getD rest (j+1) (eqPass t j 0 table) i, eq_pass_getD,
        Nat.zero_add, rowProdFrom, mul_assoc]

theorem replicate_one_getD (n i : Nat) (h : i < n) :
    (List.replicate n (1 : Element)).getD i 0 = 1 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by omega)

theorem eq_table_length (tau : List Element) : (eqTable tau).length = 2 ^ tau.length := by
  rw [eqTable, eq_table_from_length, List.length_replicate]

/-- (1) Entry `i` of the built table is exactly the per-row product
`Π_j (bit j of i ? tau_j : 1 - tau_j)`, accumulated in the source's
coordinate order. -/
theorem eq_table_getD (tau : List Element) (i : Nat) (hi : i < 2 ^ tau.length) :
    (eqTable tau).getD i 0 = rowProdFrom 0 tau i := by
  rw [eqTable, eq_table_from_getD, replicate_one_getD _ _ hi, one_mul]


/-! ### The adopted per-row eq product -/

theorem boolean_factor_exact (t : Element) (j i : Nat) :
    Norm.booleanFactor i j t.toVerifier = (bitFactor t j i).toVerifier := by
  unfold Norm.booleanFactor bitFactor
  by_cases h : i / 2 ^ j % 2 = 0
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]

theorem row_prod_fold (i : Nat) :
    ∀ (tau : List Element) (j : Nat) (acc : Element),
      (List.enumFrom j (values tau)).foldl
          (fun a pair => Verifier.mul a (Norm.booleanFactor i pair.1 pair.2)) acc.toVerifier
        = (acc * rowProdFrom j tau i).toVerifier
  | [], _, acc => by
      have hv : values ([] : List Element) = [] := rfl
      simp only [hv, List.enumFrom_nil, List.foldl_nil, rowProdFrom, mul_one]
  | t :: rest, j, acc => by
      have hstep : Verifier.mul acc.toVerifier (Norm.booleanFactor i j t.toVerifier)
          = (acc * bitFactor t j i).toVerifier := by
        rw [boolean_factor_exact]
        rfl
      have hv : values (t :: rest) = t.toVerifier :: values rest := rfl
      simp only [hv, List.enumFrom_cons, List.foldl_cons, hstep]
      rw [row_prod_fold i rest (j+1) (acc * bitFactor t j i), rowProdFrom, mul_assoc]

/-- (1) Entry `i` of the built table IS the adopted per-row eq product
`Norm.booleanRowEq i tau`, in the adopted left-to-right coordinate order. -/
theorem eq_table_entry_is_boolean_row_eq (tau : List Element) (i : Nat) (hi : i < 2 ^ tau.length) :
    ((eqTable tau).getD i 0).toVerifier = Norm.booleanRowEq i (values tau) := by
  rw [eq_table_getD tau i hi]
  have h := row_prod_fold i tau 0 1
  rw [one_mul] at h
  simp only [Norm.booleanRowEq, Norm.productLoop, List.enum]
  exact h.symm


/-! ### The row-index bit convention versus the binding order -/

theorem shift_div (i b j : Nat) (hb : b < 2) : (2 * i + b) / 2 ^ (j+1) = i / 2 ^ j := by
  have hp : (2:Nat) ^ (j+1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
  have h2 : (2 * i + b) / 2 = i := by omega
  rw [hp, ← Nat.div_div_eq_div_mul, h2]

theorem row_prod_shift (i b : Nat) (hb : b < 2) :
    ∀ (tau : List Element) (j : Nat), rowProdFrom (j+1) tau (2 * i + b) = rowProdFrom j tau i
  | [], _ => rfl
  | t :: rest, j => by
      have hf : bitFactor t (j+1) (2*i+b) = bitFactor t j i := by
        unfold bitFactor
        rw [shift_div i b j hb]
      rw [rowProdFrom, rowProdFrom, hf, row_prod_shift i b hb rest (j+1)]

/-- The LOW index bit carries the coordinate-`0` factor: `tau.head`'s factor is
selected by `i % 2`, which is exactly the bit `bindVariable` consumes first
(`bind_variable_in_place` pairs `2i` with `2i+1`, ext3.rs:47-57). -/
theorem row_prod_even (t : Element) (tau : List Element) (k : Nat) :
    rowProdFrom 0 (t :: tau) (2 * k) = (1 - t) * rowProdFrom 0 tau k := by
  have h : rowProdFrom 1 tau (2 * k) = rowProdFrom 0 tau k := by
    have := row_prod_shift k 0 (by omega) tau 0
    rwa [Nat.add_zero] at this
  rw [rowProdFrom, h]
  congr 1
  unfold bitFactor
  rw [if_pos (by omega)]

theorem row_prod_odd (t : Element) (tau : List Element) (k : Nat) :
    rowProdFrom 0 (t :: tau) (2 * k + 1) = t * rowProdFrom 0 tau k := by
  rw [rowProdFrom, row_prod_shift k 1 (by omega) tau 0]
  congr 1
  unfold bitFactor
  rw [if_neg (by omega)]

/-- (1, bit convention) The two entries `bindVariable` pairs are exactly the
`1 - tau_0` and `tau_0` halves of the same higher-coordinate row. -/
theorem eq_table_pair_split (t : Element) (tau : List Element) (k : Nat)
    (hk : k < 2 ^ tau.length) :
    (eqTable (t :: tau)).getD (2*k) 0 = (1 - t) * (eqTable tau).getD k 0 ∧
    (eqTable (t :: tau)).getD (2*k+1) 0 = t * (eqTable tau).getD k 0 := by
  have hlen : (t :: tau).length = tau.length + 1 := rfl
  have h2 : 2 * k < 2 ^ (t :: tau).length := by
    rw [hlen, Nat.pow_succ]
    omega
  have h3 : 2 * k + 1 < 2 ^ (t :: tau).length := by
    rw [hlen, Nat.pow_succ]
    omega
  rw [eq_table_getD _ _ h2, eq_table_getD _ _ h3, eq_table_getD tau k hk,
    row_prod_even, row_prod_odd]
  exact ⟨rfl, rfl⟩

/-! ## 2. Binding the eq table over a full point -/

/-- The verifier's single eq factor, in Rust's product form
`tau*x + (1-tau)*(1-x)` (eq_poly.rs:43-49, norm_logup.rs:376-384). -/
def eqFactorE (t r : Element) : Element := t * r + (1 - t) * (1 - r)

/-- The ordered eq product over the zipped coordinate lists. -/
def eqProd : List Element → List Element → Element
  | t :: ts, r :: rs => eqFactorE t r * eqProd ts rs
  | _, _ => 1

theorem bind_buffer_getD (col : List Element) (r : Element) (k : Nat)
    (hk : k < col.length / 2) :
    (DenseMleIndexed.bindBuffer col r).getD k 0
      = (1 - r) * col.getD (2*k) 0 + r * col.getD (2*k+1) 0 :=
  DenseMleIndexed.bind_buffer_reads_exact_line col r k hk

/-- (1, bit convention) The FIRST `bindVariable` consumes exactly `tau`'s HEAD
coordinate: the pair `(2k, 2k+1)` that `bind_variable_in_place` blends is the
`1 - tau_0` / `tau_0` split of row `k` of the remaining table. -/
theorem first_binding_uses_head_coordinate (t r : Element) (tau : List Element) (k : Nat)
    (hk : k < 2 ^ tau.length) :
    (DenseMleIndexed.bindBuffer (eqTable (t :: tau)) r).getD k 0
      = eqFactorE t r * (eqTable tau).getD k 0 := by
  have hlen : (eqTable (t :: tau)).length / 2 = 2 ^ tau.length := by
    rw [eq_table_length]
    simp [List.length_cons, Nat.pow_succ]
  obtain ⟨he, ho⟩ := eq_table_pair_split t tau k hk
  rw [bind_buffer_getD _ r k (by rw [hlen]; exact hk), he, ho]
  unfold eqFactorE
  ring


/-- (2, core) Any column whose entry `i` is `s` times the per-row eq product of
`tau` collapses, under the adopted `bindColumn` over a point of the same width,
to the single cell `s * eqProd tau point`. -/
theorem bound_column_of_row_products :
    ∀ (tau col point : List Element) (s : Element),
      col.length = 2 ^ tau.length →
      (∀ i, i < 2 ^ tau.length → col.getD i 0 = s * rowProdFrom 0 tau i) →
      point.length = tau.length →
      bindColumn col point = [s * eqProd tau point]
  | [], col, point, s, hlen, hcol, hp => by
      have hpn : point = [] := List.eq_nil_of_length_eq_zero (by simpa using hp)
      subst hpn
      have h0 := hcol 0 (by simp)
      simp only [rowProdFrom, mul_one] at h0
      rw [bind_column_nil, singleton_cell col (by simpa using hlen)]
      show [col.getD 0 0] = _
      rw [h0]
      simp only [eqProd, mul_one]
  | t :: rest, col, point, s, hlen, hcol, hp => by
      cases point with
      | nil => simp at hp
      | cons r rs =>
          have hrs : rs.length = rest.length := by simpa using hp
          have hcl : col.length = 2 ^ rest.length * 2 := by
            rw [hlen]
            simp [List.length_cons, Nat.pow_succ]
          have hhalf : col.length / 2 = 2 ^ rest.length := by rw [hcl]; omega
          have hnext : (DenseMleIndexed.bindBuffer col r).length = 2 ^ rest.length := by
            rw [DenseMleIndexed.bind_buffer_length, hhalf]
          have hentry : ∀ k, k < 2 ^ rest.length →
              (DenseMleIndexed.bindBuffer col r).getD k 0
                = (s * eqFactorE t r) * rowProdFrom 0 rest k := by
            intro k hk
            have hk2 : 2 * k < 2 ^ (t :: rest).length := by
              simp only [List.length_cons, Nat.pow_succ]
              omega
            have hk3 : 2 * k + 1 < 2 ^ (t :: rest).length := by
              simp only [List.length_cons, Nat.pow_succ]
              omega
            rw [bind_buffer_getD col r k (by rw [hhalf]; exact hk), hcol _ hk2, hcol _ hk3,
              row_prod_even, row_prod_odd]
            unfold eqFactorE
            ring
          rw [bind_column_cons,
            bound_column_of_row_products rest (DenseMleIndexed.bindBuffer col r) rs
              (s * eqFactorE t r) hnext hentry hrs]
          simp only [eqProd, mul_assoc]

/-- (2) Binding the ACTUAL eq table over a full point leaves one cell,
the ordered eq product of `tau` against the point. -/
theorem bound_eq_table (tau point : List Element) (hp : point.length = tau.length) :
    bindColumn (eqTable tau) point = [eqProd tau point] := by
  have h := bound_column_of_row_products tau (eqTable tau) point 1 (eq_table_length tau)
    (fun i hi => by rw [eq_table_getD tau i hi, one_mul]) hp
  rw [h, one_mul]


/-! ### The bound eq cell is the verifier's eq evaluation -/

theorem eq_factor_exact (t r : Element) :
    Norm.eqFactor t.toVerifier r.toVerifier = (eqFactorE t r).toVerifier := by
  rw [Algebra.norm_eq_factor_matches_product_form]
  rfl

theorem eq_prod_fold :
    ∀ (tau point : List Element) (acc : Element),
      ((values tau).zip (values point)).foldl
          (fun a pair => Verifier.mul a (Norm.eqFactor pair.1 pair.2)) acc.toVerifier
        = (acc * eqProd tau point).toVerifier
  | [], point, acc => by
      have hv : values ([] : List Element) = [] := rfl
      simp only [hv, List.zip_nil_left, List.foldl_nil, eqProd, mul_one]
  | t :: ts, [], acc => by
      have hv : values ([] : List Element) = [] := rfl
      simp only [hv, List.zip_nil_right, List.foldl_nil, eqProd, mul_one]
  | t :: ts, r :: rs, acc => by
      have hv1 : values (t :: ts) = t.toVerifier :: values ts := rfl
      have hv2 : values (r :: rs) = r.toVerifier :: values rs := rfl
      simp only [hv1, hv2, List.zip_cons_cons, List.foldl_cons, eq_factor_exact]
      have hstep : Verifier.mul acc.toVerifier (eqFactorE t r).toVerifier
          = (acc * eqFactorE t r).toVerifier := rfl
      rw [hstep, eq_prod_fold ts rs (acc * eqFactorE t r)]
      simp only [eqProd, mul_assoc]

theorem eq_prod_is_norm_eq_evaluation (tau point : List Element) :
    (eqProd tau point).toVerifier = Norm.eqEvaluation (values tau) (values point) := by
  have h := eq_prod_fold tau point 1
  rw [one_mul] at h
  simp only [Norm.eqEvaluation, Norm.productLoop]
  exact h.symm

/-- (2) THE eq provenance theorem: the fully bound cell of the ACTUAL
`eq_evals` table is the verifier's `Norm.eqEvaluation tau point`. -/
theorem bound_eq_table_is_eq_evaluation (tau point : List Element)
    (hp : point.length = tau.length) :
    (cell (bindColumn (eqTable tau) point)).toVerifier
      = Norm.eqEvaluation (values tau) (values point) := by
  rw [bound_eq_table tau point hp]
  exact eq_prod_is_norm_eq_evaluation tau point

/-! ## 3. The subgroup table -/

/-- `Powers` (plonky2 field/src/types.rs:429-433) as consumed by
`two_adic_subgroup`'s `generator.powers().take(1 << n_log)`
(field/src/types.rs:280-283): the running product `v, v*g, v*g^2, ...`. -/
def powersFrom (g : Element) : Element → Nat → List Element
  | _, 0 => []
  | v, k+1 => v :: powersFrom g (v * g) k

/-- `prover_data.subgroup` / `tables.subgroup`, the table handed to
`Ext3DenseMle::from_base` at norm_logup.rs:487. -/
def subgroupTable (g : Element) (n : Nat) : List Element := powersFrom g 1 (2 ^ n)

/-- `vk.subgroup_gen_powers` (prover_v2.rs:250-258 and 369-377):
`let mut value = subgroup[1]; for _ in 0..degree_bits { push value; value *= value }`. -/
def generatorPowers (g : Element) : Nat → List Element
  | 0 => []
  | k+1 => g :: generatorPowers (g * g) k

theorem powers_from_length (g : Element) : ∀ (v : Element) (m : Nat),
    (powersFrom g v m).length = m
  | _, 0 => rfl
  | v, m+1 => by simp only [powersFrom, List.length_cons, powers_from_length g (v*g) m]

theorem powers_from_getD (g : Element) : ∀ (m : Nat) (v : Element) (i : Nat), i < m →
    (powersFrom g v m).getD i 0 = v * g ^ i
  | 0, _, _, h => absurd h (by omega)
  | _m+1, v, 0, _ => by simp only [powersFrom, List.getD_cons_zero, pow_zero, mul_one]
  | m+1, v, i+1, h => by
      rw [powersFrom, List.getD_cons_succ, powers_from_getD g m (v*g) i (by omega), pow_succ,
        mul_assoc, mul_comm g (g ^ i)]

theorem subgroup_table_length (g : Element) (n : Nat) : (subgroupTable g n).length = 2 ^ n :=
  powers_from_length g 1 (2 ^ n)

theorem subgroup_table_getD (g : Element) (n i : Nat) (hi : i < 2 ^ n) :
    (subgroupTable g n).getD i 0 = g ^ i := by
  rw [subgroupTable, powers_from_getD g (2 ^ n) 1 i hi, one_mul]

theorem generator_powers_length (g : Element) : ∀ n : Nat, (generatorPowers g n).length = n
  | 0 => rfl
  | n+1 => by simp only [generatorPowers, List.length_cons, generator_powers_length (g*g) n]

theorem generator_powers_getD (g : Element) : ∀ (n i : Nat), i < n →
    (generatorPowers g n).getD i 0 = g ^ (2 ^ i)
  | 0, _, h => absurd h (by omega)
  | _n+1, 0, _ => by simp only [generatorPowers, List.getD_cons_zero, pow_zero, pow_one]
  | n+1, i+1, h => by
      rw [generatorPowers, List.getD_cons_succ, generator_powers_getD (g*g) n i (by omega),
        ← pow_two, ← pow_mul, ← pow_succ']

/-- The doubling recursion of the subgroup column: `Π_j ((1-r_j) + r_j g^(2^j))`
written as a recursion that squares the generator at every step. -/
def subProd : Element → List Element → Element
  | _, [] => 1
  | g, r :: rs => ((1 - r) + r * g) * subProd (g * g) rs

/-- The verifier's own loop shape (`verifier_v2.rs:398-402`,
`_subgroupEvaluation` OuterLogupExt3Verifier.sol:878-893): one factor per
supplied generator power. -/
def subEval : List Element → List Element → Element
  | gp :: gs, r :: rs => ((1 - r) + r * gp) * subEval gs rs
  | _, _ => 1

/-- (3, core) Any column whose entry `i` is `s * g^i` collapses under the
adopted binding to `s * Π_j ((1-r_j) + r_j g^(2^j))`. -/
theorem bound_column_of_geometric :
    ∀ (n : Nat) (col point : List Element) (g s : Element),
      col.length = 2 ^ n →
      (∀ i, i < 2 ^ n → col.getD i 0 = s * g ^ i) →
      point.length = n →
      bindColumn col point = [s * subProd g point]
  | 0, col, point, g, s, hlen, hcol, hp => by
      have hpn : point = [] := List.eq_nil_of_length_eq_zero hp
      subst hpn
      have h0 := hcol 0 (by simp)
      rw [pow_zero, mul_one] at h0
      rw [bind_column_nil, singleton_cell col (by simpa using hlen)]
      show [col.getD 0 0] = _
      rw [h0]
      simp only [subProd, mul_one]
  | n+1, col, point, g, s, hlen, hcol, hp => by
      cases point with
      | nil => simp at hp
      | cons r rs =>
          have hrs : rs.length = n := by simpa using hp
          have hcl : col.length = 2 ^ n * 2 := by rw [hlen, Nat.pow_succ]
          have hhalf : col.length / 2 = 2 ^ n := by rw [hcl]; omega
          have hnext : (DenseMleIndexed.bindBuffer col r).length = 2 ^ n := by
            rw [DenseMleIndexed.bind_buffer_length, hhalf]
          have hentry : ∀ k, k < 2 ^ n →
              (DenseMleIndexed.bindBuffer col r).getD k 0
                = (s * ((1 - r) + r * g)) * (g * g) ^ k := by
            intro k hk
            have hk2 : 2 * k < 2 ^ (n+1) := by rw [Nat.pow_succ]; omega
            have hk3 : 2 * k + 1 < 2 ^ (n+1) := by rw [Nat.pow_succ]; omega
            have hg1 : g ^ (2*k) = (g*g) ^ k := by rw [pow_mul, pow_two]
            have hg2 : g ^ (2*k+1) = (g*g) ^ k * g := by rw [pow_succ, hg1]
            rw [bind_buffer_getD col r k (by rw [hhalf]; exact hk), hcol _ hk2, hcol _ hk3,
              hg1, hg2]
            ring
          rw [bind_column_cons,
            bound_column_of_geometric n (DenseMleIndexed.bindBuffer col r) rs (g*g)
              (s * ((1 - r) + r * g)) hnext hentry hrs]
          simp only [subProd, mul_assoc]

theorem sub_prod_is_generator_powers : ∀ (g : Element) (point : List Element),
    subProd g point = subEval (generatorPowers g point.length) point
  | _, [] => rfl
  | g, r :: rs => by
      rw [subProd, List.length_cons, generatorPowers, subEval,
        sub_prod_is_generator_powers (g*g) rs]


/-- The Ext3 embedding of a base-field VK generator power. -/
def baseElement (b : Verifier.Base) : Element := ⟨Norm.embed b.val⟩

theorem subgroup_factor_exact (b : Verifier.Base) (x : Element) :
    Norm.subgroupFactor b x.toVerifier = ((1 - x) + x * baseElement b).toVerifier := by
  rw [Algebra.norm_subgroup_factor_matches_rust]
  rfl

theorem sub_eval_fold :
    ∀ (powers : List Verifier.Base) (point : List Element) (acc : Element),
      (powers.zip (values point)).foldl
          (fun a pair => Verifier.mul a (Norm.subgroupFactor pair.1 pair.2)) acc.toVerifier
        = (acc * subEval (powers.map baseElement) point).toVerifier
  | [], _point, acc => by
      simp only [List.zip_nil_left, List.foldl_nil, List.map_nil, subEval, mul_one]
  | b :: bs, [], acc => by
      have hv : values ([] : List Element) = [] := rfl
      simp only [hv, List.zip_nil_right, List.foldl_nil, List.map_cons, subEval, mul_one]
  | b :: bs, r :: rs, acc => by
      have hv : values (r :: rs) = r.toVerifier :: values rs := rfl
      simp only [hv, List.zip_cons_cons, List.foldl_cons, List.map_cons, subgroup_factor_exact]
      have hstep : Verifier.mul acc.toVerifier ((1 - r) + r * baseElement b).toVerifier
          = (acc * ((1 - r) + r * baseElement b)).toVerifier := rfl
      rw [hstep, sub_eval_fold bs rs (acc * ((1 - r) + r * baseElement b))]
      simp only [subEval, mul_assoc]

theorem sub_eval_is_norm_subgroup_evaluation (powers : List Verifier.Base) (point : List Element) :
    (subEval (powers.map baseElement) point).toVerifier
      = Norm.subgroupEvaluation powers (values point) := by
  have h := sub_eval_fold powers point 1
  rw [one_mul] at h
  simp only [Norm.subgroupEvaluation, Norm.productLoop]
  exact h.symm

/-- The only genuinely non-derivable link in the subgroup chain: the VK's
`subgroup_gen_powers` are the repeated squares of the generator whose powers
fill the prover's subgroup table. Rust checks this at verifier_v2.rs:131-146
by recomputing `F::two_adic_subgroup(degree_bits)`, i.e. in BASE-field
arithmetic, which the adopted audit does not model (`Verifier.Base` carries no
multiplication); it is therefore kept as a named, visible hypothesis. -/
def SubgroupPowersProvenance (powers : List Verifier.Base) (g : Element) (n : Nat) : Prop :=
  powers.map baseElement = generatorPowers g n

/-- (3) THE subgroup provenance theorem. The verifier never folds the subgroup
table: it multiplies `(1 - r_j) + r_j * g^(2^j)` over the VK's generator powers
(verifier_v2.rs:398-402, `_subgroupEvaluation` Sol:878-893). The exact relation
that holds is that this product IS the fully bound cell of the prover's
geometric table `[g^0, g^1, ..., g^(2^n - 1)]`. -/
theorem bound_subgroup_table_is_subgroup_evaluation (g : Element) (n : Nat)
    (point : List Element) (powers : List Verifier.Base)
    (hp : point.length = n) (hpow : SubgroupPowersProvenance powers g n) :
    (cell (bindColumn (subgroupTable g n) point)).toVerifier
      = Norm.subgroupEvaluation powers (values point) := by
  rw [bound_column_of_geometric n (subgroupTable g n) point g 1 (subgroup_table_length g n)
    (fun i hi => by rw [subgroup_table_getD g n i hi, one_mul]) hp]
  show (1 * subProd g point).toVerifier = _
  rw [one_mul, sub_prod_is_generator_powers, hp, ← hpow, sub_eval_is_norm_subgroup_evaluation]

/-- The honest eq column's fully bound cell as the adopted packed fold. -/
theorem eq_table_packed_fold (tau point : List Element) (hp : point.length = tau.length) :
    Packed.fold (DenseMleIndexed.raw (eqTable tau)) (DenseMleIndexed.raw point)
      = (Norm.eqEvaluation (values tau) (values point)).val := by
  have h := (bound_column_is_packed_fold (eqTable tau) point tau.length
    (eq_table_length tau) hp).2.2
  rw [← h]
  exact congrArg Subtype.val (bound_eq_table_is_eq_evaluation tau point hp)

theorem subgroup_table_packed_fold (g : Element) (n : Nat) (point : List Element)
    (powers : List Verifier.Base) (hp : point.length = n)
    (hpow : SubgroupPowersProvenance powers g n) :
    Packed.fold (DenseMleIndexed.raw (subgroupTable g n)) (DenseMleIndexed.raw point)
      = (Norm.subgroupEvaluation powers (values point)).val := by
  have h := (bound_column_is_packed_fold (subgroupTable g n) point n
    (subgroup_table_length g n) hp).2.2
  rw [← h]
  exact congrArg Subtype.val
    (bound_subgroup_table_is_subgroup_evaluation g n point powers hp hpow)

/-! ## 4. Discharging the adopted provenance hypotheses -/

/-- The norm prover's two structural columns exactly as
`NormLogupMleState::from_base` builds them (norm_logup.rs:414-491):
`eq: Ext3DenseMle::new(eq_evals_ext3(tau))` (487, builder 360-374) and
`subgroup: Ext3DenseMle::from_base(subgroup)` (487), the evaluation-domain
table `[g^0, ..., g^(2^n-1)]` of plonky2's `two_adic_subgroup`. -/
structure NormColumnProvenance (t : Tables) (c : Verifier.Config) (ch : Norm.Challenges)
    (tau : List Element) (g : Element) : Prop where
  eqColumn : t.eq = eqTable tau
  tauValues : values tau = ch.tau
  tauWidth : tau.length = t.remaining
  subgroupColumn : t.subgroup = subgroupTable g t.remaining
  powers : SubgroupPowersProvenance c.subgroupPowers g t.remaining

/-- (4) `NormTerminalBinding.fully_bound_target_is_norm_evaluate_of_cells` with
`heq` and `hsub` GONE: the eq/subgroup cells' provenance is now derived from the
columns the prover actually builds. -/
theorem fully_bound_target_is_norm_evaluate_of_columns
    (t t' : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (point : List Element)
    (tau : List Element) (g : Element)
    (h : Shape t p) (hpoint : point.length = t.remaining)
    (hb : bindTablesMany point t = some t')
    (hprov : NormColumnProvenance t c p.challenges tau g)
    (hc : Compatible c t' p constants) (hlam : LambdaProvenance p)
    (hmap : WireMapMatches c.publicInputWireMap t'.bindings)
    (heta : EtaProvenance (NormPolynomial.lift p.challenges.eta) t'.bindings)
    (hprefix : PrefixAt (values point) t'.bindings) :
    Shape t' p ∧ FullyBound t' ∧
      terminalTarget t' p
        = some (Norm.evaluate c p.challenges (toTerminalInput t' constants extra) (values point)) := by
  obtain ⟨t'', ht'', hshape, hfull, _, _, heqc, hsubc, _, _, _, _, _⟩ :=
    fully_bound_tables_from_initial t p point h hpoint
  have e : t'' = t' := Option.some.inj (ht''.symm.trans hb)
  subst e
  refine ⟨hshape, hfull, ?_⟩
  refine fully_bound_target_is_norm_evaluate_of_cells t'' p c constants extra (values point)
    hshape hc hlam hmap heta hprefix ?_ ?_
  · rw [heqc, hprov.eqColumn,
      bound_eq_table_is_eq_evaluation tau point (by rw [hprov.tauWidth]; exact hpoint),
      hprov.tauValues]
  · rw [hsubc, hprov.subgroupColumn]
    exact bound_subgroup_table_is_subgroup_evaluation g t.remaining point c.subgroupPowers
      hpoint hprov.powers

/-- (4) HONEST PROVER ONLY. `NormTerminalBinding.honest_prover_terminal` with the
eq/subgroup cell hypotheses discharged: from a fresh shaped table whose eq and
subgroup columns are the ones `from_base` builds, binding the whole point gives
exactly the verifier's `Norm.evaluate`. Remaining hypotheses are the VK/config
correspondences `Compatible`, `LambdaProvenance`, `WireMapMatches` and the
column provenance itself. -/
theorem honest_prover_terminal_of_columns (t : Tables) (p : Prepared) (c : Verifier.Config)
    (constants extra : List Verifier.Ext3) (point : List Element)
    (pairs : List (Nat × Nat × Verifier.Base)) (tau : List Element) (g : Element)
    (h : Shape t p) (h0 : t.boundVariables = 0) (hpoint : point.length = t.remaining)
    (hbuild : t.bindings = buildBindings (NormPolynomial.lift p.challenges.eta) 1 pairs)
    (hc : Compatible c t p constants) (hlam : LambdaProvenance p)
    (hmap : WireMapMatches c.publicInputWireMap t.bindings)
    (hprov : NormColumnProvenance t c p.challenges tau g) :
    ∃ t', bindTablesMany point t = some t' ∧ FullyBound t' ∧
      PrefixAt (point.map Element.toVerifier) t'.bindings ∧
      terminalTarget t' p
        = some (Norm.evaluate c p.challenges (toTerminalInput t' constants extra) (values point)) := by
  obtain ⟨t', ht', hfull, hprefix, hterm⟩ :=
    honest_prover_terminal t p c constants extra point pairs h h0 hpoint hbuild hc hlam hmap
  obtain ⟨t'', ht'', _, _, _, _, heqc, hsubc, _, _, _, _, _⟩ :=
    fully_bound_tables_from_initial t p point h hpoint
  have e : t'' = t' := Option.some.inj (ht''.symm.trans ht')
  subst e
  refine ⟨t'', ht', hfull, hprefix, ?_⟩
  have heqcell : (cell t''.eq).toVerifier = Norm.eqEvaluation p.challenges.tau (values point) := by
    rw [heqc, hprov.eqColumn,
      bound_eq_table_is_eq_evaluation tau point (by rw [hprov.tauWidth]; exact hpoint),
      hprov.tauValues]
  have hsubcell : (cell t''.subgroup).toVerifier
      = Norm.subgroupEvaluation c.subgroupPowers (values point) := by
    rw [hsubc, hprov.subgroupColumn]
    exact bound_subgroup_table_is_subgroup_evaluation g t.remaining point c.subgroupPowers
      hpoint hprov.powers
  rw [hterm, evaluate_with_exact, heqcell, hsubcell]
  rfl

/-! ### Gate side -/

/-- The gate prover's eq table, `Ext3DenseMle::new(ext3_eq_evals(tau))`
(gate_ext3_v2.rs:95, builder 26-39; same loop nest as norm_logup.rs:360-374). -/
def GateEqProvenance (s : GateTerminalBinding.ProverState) (tau : List Element) : Prop :=
  s.eq.evaluations = eqTable tau ∧ tau.length = s.eq.numVars

/-- The fully bound gate eq cell is `Norm.eqEvaluation tau point`, derived from
the table the constructor builds. -/
theorem bound_gate_eq_cell (n : Nat) (s t : GateTerminalBinding.ProverState)
    (steps : List (List Verifier.Ext3 × Element)) (tau : List Element)
    (k : GateTerminalBinding.Cells)
    (hn : s.eq.numVars = n) (hsteps : steps.length = n)
    (hprov : GateEqProvenance s tau)
    (hb : GateTerminalBinding.bindAll s steps = some t)
    (hkt : t.tables = k.tables) :
    k.eq.toVerifier = Norm.eqEvaluation (values tau) (values (steps.map Prod.snd)) := by
  obtain ⟨_, _, he⟩ := GateTerminalBinding.bind_all_columns s t steps hb
  have hplen : (steps.map Prod.snd).length = tau.length := by
    rw [List.length_map, hsteps, ← hn, hprov.2]
  have hcol : DenseMleIndexed.bindMany (steps.map Prod.snd)
      ⟨s.eq.numVars, s.eq.evaluations⟩
      = some ⟨s.eq.numVars - (steps.map Prod.snd).length,
        bindColumn s.eq.evaluations (steps.map Prod.snd)⟩ :=
    bind_many_is_bind_column (steps.map Prod.snd) s.eq.numVars s.eq.evaluations
      (by rw [List.length_map, hsteps, ← hn])
  rw [hcol] at he
  have hev : t.eq.evaluations = bindColumn s.eq.evaluations (steps.map Prod.snd) :=
    congrArg DenseMleIndexed.State.evaluations (Option.some.inj he).symm
  have hcell : t.eq.evaluations = [k.eq] :=
    congrArg GateSuffixPolynomial.Tables.eq hkt
  rw [hev, hprov.1, bound_eq_table tau (steps.map Prod.snd) hplen] at hcell
  have hk : k.eq = eqProd tau (steps.map Prod.snd) := (List.cons.inj hcell).1.symm
  rw [hk]
  exact eq_prod_is_norm_eq_evaluation tau (steps.map Prod.snd)

/-- (4) `GateTerminalBinding.bound_terminal_is_engine_gate_terminal` with `heq`
GONE: the eq cell's provenance now comes from the prover's actual eq table. -/
theorem bound_terminal_is_engine_gate_terminal_of_eq_table
    (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (n : Nat) (s t : GateTerminalBinding.ProverState)
    (steps : List (List Verifier.Ext3 × Element)) (tau : List Element)
    (k : GateTerminalBinding.Cells) (alpha : Element)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hp : (e.publicInputsHash p.publicInputs).length = 4)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hk : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (hw : k.wires.length = c.numWires) (hcst : k.constants.length = c.numConstants)
    (halpha : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (hn : s.eq.numVars = n) (hsteps : steps.length = n)
    (hprov : GateEqProvenance s tau)
    (hb : GateTerminalBinding.bindAll s steps = some t) (hkt : t.tables = k.tables)
    (htau : values tau = (e.initialTranscript c p).gateTau)
    (hpt : values (steps.map Prod.snd) = (Verifier.derivedRounds e c p).gatePoint) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      GateTerminalBinding.boundTerminal (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        alpha k = some (Verifier.mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p
        = Verifier.mul k.eq.toVerifier gate :=
  GateTerminalBinding.bound_terminal_is_engine_gate_terminal e decode c p gates k alpha
    hd hr hp hv hk hw hcst halpha
    (by rw [bound_gate_eq_cell n s t steps tau k hn hsteps hprov hb hkt, htau, hpt])

/-- (4) HONEST PROVER ONLY. The gate last-round value against the engine's gate
terminal, with the eq-cell hypothesis discharged from the eq table. -/
theorem honest_last_round_is_engine_gate_terminal_of_eq_table
    (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (c : Verifier.Config) (p : Verifier.Proof) (gates : List Gates.GateInfo)
    (n : Nat) (s0 t0 : GateTerminalBinding.ProverState)
    (steps : List (List Verifier.Ext3 × Element)) (tau : List Element)
    (s t : GateTerminalBinding.ProverState) (round : List Verifier.Ext3) (x : Element)
    (k : GateTerminalBinding.Cells) (alpha : Element)
    (hs : GateTerminalBinding.ProverShape (Integrated.gateConfig c) 1 s)
    (hv : Gates.validateConfiguration (Integrated.gateConfig c) gates = some ())
    (hbc : GateTerminalBinding.bindChallenge s round x = some t)
    (hkt : t.tables = k.tables)
    (hd : decode c.gatesEncoding = some gates) (hr : gates.length = c.gateRows)
    (hp : (e.publicInputsHash p.publicInputs).length = 4)
    (hk : GateTerminalBinding.CellsMatchClaims c k (GateTerminalBinding.gateTerminalInput p))
    (halpha : alpha.toVerifier = (e.initialTranscript c p).gateAlpha)
    (hn : s0.eq.numVars = n) (hsteps : steps.length = n)
    (hprov : GateEqProvenance s0 tau)
    (hb : GateTerminalBinding.bindAll s0 steps = some t0) (hkt0 : t0.tables = k.tables)
    (htau : values tau = (e.initialTranscript c p).gateTau)
    (hpt : values (steps.map Prod.snd) = (Verifier.derivedRounds e c p).gatePoint) :
    ∃ gate, Integrated.gateResult (Integrated.modelEngine e decode) decode c p = some gate ∧
      GateSuffixPolynomial.currentRoundValue (Integrated.gateConfig c) gates
        (GateTerminalBinding.publicHashFunction (e.publicInputsHash p.publicInputs))
        alpha x s.tables 1 = some (Verifier.mul k.eq.toVerifier gate) ∧
      Verifier.gateTerminal (Integrated.modelEngine e decode) c p
        = Verifier.mul k.eq.toVerifier gate :=
  GateTerminalBinding.honest_last_round_is_engine_gate_terminal e decode c p gates s t round x k
    alpha hs hv hbc hkt hd hr hp hk halpha
    (by rw [bound_gate_eq_cell n s0 t0 steps tau k hn hsteps hprov hb hkt0, htau, hpt])

/-! ## 5. Concrete examples -/

theorem bit_factor_low_even (a : Element) : bitFactor a 0 0 = 1 - a := by
  unfold bitFactor
  rw [if_pos (by decide)]

theorem bit_factor_low_odd (a : Element) : bitFactor a 0 1 = a := by
  unfold bitFactor
  rw [if_neg (by decide)]

/-- `tau` of length 1: the built table is `[1 - tau_0, tau_0]`. -/
theorem eq_table_one (a : Element) : eqTable [a] = [1 - a, a] := by
  show eqPass a 0 0 [1, 1] = _
  simp only [eqPass, Nat.zero_add, bit_factor_low_even, bit_factor_low_odd, one_mul]

/-- `tau` of length 2, LOW bit first: index `i` selects `tau_0` by `i % 2`. -/
theorem eq_table_two (a b : Element) :
    eqTable [a, b] = [(1 - a) * (1 - b), a * (1 - b), (1 - a) * b, a * b] := by
  show eqPass b 1 0 (eqPass a 0 0 [1, 1, 1, 1]) = _
  have h0 : bitFactor a 0 2 = 1 - a := by unfold bitFactor; rw [if_pos (by decide)]
  have h1 : bitFactor a 0 3 = a := by unfold bitFactor; rw [if_neg (by decide)]
  have h2 : bitFactor b 1 0 = 1 - b := by unfold bitFactor; rw [if_pos (by decide)]
  have h3 : bitFactor b 1 1 = 1 - b := by unfold bitFactor; rw [if_pos (by decide)]
  have h4 : bitFactor b 1 2 = b := by unfold bitFactor; rw [if_neg (by decide)]
  have h5 : bitFactor b 1 3 = b := by unfold bitFactor; rw [if_neg (by decide)]
  simp only [eqPass, Nat.zero_add, bit_factor_low_even, bit_factor_low_odd, h0, h1, h2, h3, h4, h5, one_mul]

theorem example_bound_one_variable (a r : Element) :
    cell (bindColumn (eqTable [a]) [r]) = a * r + (1 - a) * (1 - r) := by
  rw [bound_eq_table [a] [r] rfl]
  show eqProd [a] [r] = _
  simp only [eqProd, eqFactorE, mul_one]

theorem example_bound_two_variables (a b r0 r1 : Element) :
    cell (bindColumn (eqTable [a, b]) [r0, r1])
      = (a * r0 + (1 - a) * (1 - r0)) * (b * r1 + (1 - b) * (1 - r1)) := by
  rw [bound_eq_table [a, b] [r0, r1] rfl]
  show eqProd [a, b] [r0, r1] = _
  simp only [eqProd, eqFactorE, mul_one]

theorem example_eq_evaluation_one_variable (a r : Element) :
    (cell (bindColumn (eqTable [a]) [r])).toVerifier
      = Norm.eqEvaluation [a.toVerifier] [r.toVerifier] :=
  bound_eq_table_is_eq_evaluation [a] [r] rfl

theorem example_eq_evaluation_two_variables (a b r0 r1 : Element) :
    (cell (bindColumn (eqTable [a, b]) [r0, r1])).toVerifier
      = Norm.eqEvaluation [a.toVerifier, b.toVerifier] [r0.toVerifier, r1.toVerifier] :=
  bound_eq_table_is_eq_evaluation [a, b] [r0, r1] rfl

theorem subgroup_table_one (g : Element) : subgroupTable g 1 = [1, g] := by
  show powersFrom g 1 2 = _
  simp only [powersFrom, one_mul]

theorem subgroup_table_two (g : Element) : subgroupTable g 2 = [1, g, g * g, g * g * g] := by
  show powersFrom g 1 4 = _
  simp only [powersFrom, one_mul]

theorem generator_powers_two (g : Element) : generatorPowers g 2 = [g, g * g] := by
  simp only [generatorPowers]

theorem example_subgroup_one_variable (g r : Element) :
    cell (bindColumn (subgroupTable g 1) [r]) = (1 - r) + r * g := by
  rw [bound_column_of_geometric 1 (subgroupTable g 1) [r] g 1 (subgroup_table_length g 1)
    (fun i hi => by rw [subgroup_table_getD g 1 i hi, one_mul]) rfl]
  show (1 : Element) * subProd g [r] = _
  simp only [subProd, one_mul, mul_one]

theorem example_subgroup_two_variables (g r0 r1 : Element) :
    cell (bindColumn (subgroupTable g 2) [r0, r1])
      = ((1 - r0) + r0 * g) * ((1 - r1) + r1 * (g * g)) := by
  rw [bound_column_of_geometric 2 (subgroupTable g 2) [r0, r1] g 1 (subgroup_table_length g 2)
    (fun i hi => by rw [subgroup_table_getD g 2 i hi, one_mul]) rfl]
  show (1 : Element) * subProd g [r0, r1] = _
  simp only [subProd, one_mul, mul_one]

end Audit.Wire3.EqTableProvenance
