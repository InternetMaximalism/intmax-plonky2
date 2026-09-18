# Verification Report — Lean 4 Formal Audit of the WHIR-based Multilinear Proof System

> Historical report: this is not a wire-v3 audit or production approval.
> Current implementation scope and release limitations: [mle/README.md](../README.md).

Date: 2026-07-06 / Target commit: ee80ee6d / Branch: claude/gifted-germain-0283dd
Deliverable: `mle/audit/` (Lean 4.10.0, no Mathlib dependency, `lake build` with 0 warnings,
**46 theorems, 0 `sorry`, 1 explicit axiom**)

## Target, Version, and Mode

**Audit mode.** The target is the WHIR-based multilinear (MLE) proof system in `mle/`:

- Specification: `mle/paper/plonky2_mle_paper_v2.md` (theory, layer 0)
- Rust implementation: `mle/src/` (in particular `verifier.rs`)
- Solidity implementation: `mle/contracts/src/` (in particular `MleVerifier.sol`)

## Scope (result of the stage-0 interview; details in [SCOPE.md](HISTORICAL-SCOPE.md))

- WHIR is formalized as a black-box PCS, with its internals also formalized as abstract
  invariants (re-proving the internal proximity soundness is out of scope).
- Verification properties: Soundness (Theorem 1), Completeness, Fiat-Shamir binding,
  absence of a binding gap.
- Consistency with both the Rust and Solidity implementations is checked as well.
- Out of scope: prover efficiency, ZK, recursive verification cost, re-proving the WHIR
  paper itself.

## Method (4 stages + a cleanup before stage 3)

1. **Stage 1**: Formalize the abstract construction of the specification in Lean ([Audit/*.lean](Audit/)).
2. **Stage 2**: Line-by-line comparison of Rust/Solidity ([Audit/Impl/*.lean](Audit/Impl/)),
   stating the divergences among the three as propositions D1–D11.
3. **Cleanup**: Give substance to vacuous propositions (vacuous `True`/`∃ BadEvent,True`),
   and remove dead code.
4. **Stage 3**: Prove the principal properties ([Audit/Proofs/*.lean](Audit/Proofs/)).

## Key Finding: the Specification Has a 4-Layer Structure

Initially paper v2 was taken as the sole specification, but there are four layers of
definitional documents that are closer to the implementation. Divergence judgments are
made against this hierarchy:

| Layer | Document | Role |
|---|---|---|
| Layer 0 theory | `paper/plonky2_mle_paper_v2.md` | The ideal, including batching sumcheck (§4.4). Partly **not implemented** |
| Layer 1 v1 design | `README.md` L191-424 | Formally documents aux commit + combined sumcheck |
| Layer 2 v2 design | `soundnessgame/MleVerifier.vol.md` | Definitional document for Φ_inv/Φ_h/Φ_gate + inverse helpers (R2-#1 through #8) |
| Layer 3 threat analysis | `tasks/todo.md` and others | C1/C2 CRITICAL + PoC + fixes; a HIGH still present in Phase6 |

The implementation is not "the theory of layer 0" but a **stack of layer 1 + layer 2**, and
**no unified soundness theorem exists at any layer**. The Lean formalization in this audit
is the first step toward that unification.

## List of Assumptions (axiom / idealization / UNDERSPECIFIED)

| Kind | Content | Location |
|---|---|---|
| Axiom | A nonzero polynomial of degree ≤ d has ≤ d distinct roots (a standard fact; stated because Mathlib is not used) | `Poly.roots_le_degree` |
| Idealization | PCS binding (ε_PCS): a commitment determines a unique polynomial and a successful verify implies agreement of the evaluation | `Pcs.lean` / `ProtocolPCS.verify_sound` |
| Idealization | Merkle collision resistance; Keccak = random oracle | `Whir.lean` / `Transcript.lean` |
| Trust assumption | The VK (circuit_digest, preprocessed_root, kIs, subgroupGenPowers) has been correctly generated | D8 |
| Abstraction (4) | Transcript re-derivation order, empty lookup check, WHIR internals (both models) | the remaining `True` in `*VerifyAccepts` |
| UNDERSPEC | The inverse reconstruction in §5.3 step7, the column-combining scalar in §4.3 (→ the implementation substitutes WHIR multi-point, D7) | note in `Statements.lean` |

## By File and by Finding (divergences D1–D11)

| ID | Severity | Content | Status |
|---|---|---|---|
| **D1** | Spec-bug | The closed form of g_sub in paper §4.2.2 is wrong, given in Σ form. Both Rust and Sol use the correct Π form | The implementation is correct; the specification needs correction |
| **D2** | Medium | The degree-bound check for the combined sumcheck is **absent in Rust** (Sol fixed it in R2-#8) | Residual on the Rust side |
| **D3** | **CRITICAL (confirmed)** | The inverse helpers a_j,b_j are not PCS-bound, and only the single linear relation of Φ_inv is imposed. The verifier accepts an incorrect inverse | **The strong version is formally proved** (`d3_strong`, below) |
| **D4** | Info | The unweighted Σ of Φ_h is faithful to the design of the layer-2 vol.md (the divergence is only against layer 0 §4.2.3). λ_h is a dead challenge | The implementation is faithful to its own design |
| **D5** | Info | 96-bit truncation in the transcript. The comment "256bit/2^-192" is a misstatement; the implementation is consistent between Rust and Sol | Interoperability OK |
| **D6** | Info | The domain separation labels disagree between layer 0 and the implementation; the implementations agree with each other | Interoperability OK |
| **D7** | Structural | The layer-0 §4.4 batching is not implemented, and is substituted by WHIR multi-point. The implementation is a layer 1 + layer 2 stack | Design understanding |
| **D8** | Trust assumption | The kIs/subgroupGenPowers in Sol are not transcript-bound (caller's responsibility) | Presupposes an operational wrapper |
| **D9** | Low | τ_perm is squeezed but unused (a remnant of layer 1) | Harmless |
| **D10** | **High, unresolved** | publicInputsHash is not bound to publicInputs (layer 3 Phase6 Finding1; Poseidon not implemented in Sol) | **Still present, not fixed** |
| **D11** | Info/follow-up | Sites of the same kind of non-canonical sub(p,X) inside the WHIR/Sumcheck library | out-of-scope |

## Properties Proved (stage 3)

The algebra of the field class is built from axioms without depending on Mathlib
([Audit/Algebra.lean](Audit/Algebra.lean)).

| Property | Theorem | Content |
|---|---|---|
| **Soundness core** | `sumcheck_telescope` | Telescoping: acceptance + agreement of the final value + disagreement of the initial claim ⇒ somewhere in the actual challenges one hits a root of the difference polynomial (nonzero, degree ≤ d). The deterministic part of Theorem 1 |
| **Implementation Soundness** | `rustSoundness` / `solSoundness` | Acceptance ⇒ fixed-version soundness for each of the 4 sumchecks (fixed to the stored/re-derived challenges) |
| **FS binding** | `domainSeparation` / `fsOrdering` | Injectivity of the label embedding, determinism of challenge-after-commit |
| **Absence of a binding gap (§4.5)** | `linearCommutes` | MLE commutes with respect to the linear combination at the terminal |
| **Existence of a binding gap (§3)** | `bindingGapExists` | **Under \|F\|>2 (non-idempotent elements)**, MLE(W²)(r) ≠ (MLE(W)(r))². It does not hold in characteristic 2 (Goldilocks satisfies the condition) |
| **Basic MLE properties** | `eq_diag` / `eq_sum` / `mleEval_bit1` / `hsum_vprod_factor` | eq(b,b)=1, Σeq=1, tensor sum |
| **D3 weak version** | `d3_substitutable` | Existence of 2 proofs that differ only in the evaluation values of the inverse helpers while agreeing on the witness batch consistency |
| **D3 strong version (CRITICAL confirmed)** | `d3_strong` | **Two proofs that completely satisfy the verifier (all fields of `RustVerifyAccepts`), where one claims the honest inverse (1,1) and the other the incorrect inverse (0,2), with identical witnesses** — the verifier accepts both ⇒ soundness is broken |

As auxiliaries, `polySub_eval`, `isZero_eval`, `accepts_length`, `hsum_add`,
`hsum_mul_left`, etc. are also proved.

## Findings (summary by severity)

- **CRITICAL (confirmed)**:
  - **D3** (break in the binding chain of the inverse helpers): the implementation violates
    "all terminal values are PCS-bound" from paper §4.5. This has been **formally confirmed**
    by `d3_strong`: there exist two proofs that completely satisfy the verifier
    (all fields of `RustVerifyAccepts`) and whose witnesses are identical, yet
    one claims the honest inverse (a₀,b₀)=(1,1) and the other the incorrect inverse (0,2).
    Both being accepted ⇒ the inverse helpers are not bound by the PCS, and the soundness
    of the permutation argument (copy constraints) is broken. The cause is that the inverse
    helpers have no batch consistency check like the one for witness/preprocessed, and only
    the single linear relation a₀+b₀=2 at the Φ_inv terminal is imposed
    (both of the 2 solutions (1,1)/(0,2) pass).
    **Recommended fix**: additionally impose WHIR/batch consistency binding on the individual
    evaluation values of the inverse helpers.
- **High**:
  - **D10** (publicInputsHash not bound): layer 3 Phase6 identified it as a HIGH still present;
    **not fixed**, because Poseidon is not implemented in Solidity.
- **Medium**: D2 (missing degree bound in the Rust combined sumcheck).
- **Spec-bug**: D1 (the Σ misstatement of g_sub in §4.2.2; the implementation is correct).
- **Info/Low**: D4, D5, D6, D9, D11.
- **Structural/assumptions**: D7 (stacked protocol, no unified theorem), D8 (perm context not bound).

## List and Interpretation of `sorry` and Unproved Points

There are **0** occurrences of `sorry`. The only axiom is `Poly.roots_le_degree` (a standard
mathematical fact). The following remain as "unproved Prop definitions" (the residue of stage 3):

- The body of `SoundnessProp` (paper version) — the proof connecting the existential
  quantification to the telescope. Since the implementation versions
  `rustSoundness`/`solSoundness` are proved, the substance of soundness is secured.
- `mle_agrees_on_hypercube_prop` / `mle_is_multilinear_prop` / `mle_unique_prop`
  — the uniqueness family for MLE (eq_diag/eq_sum are proved).
- End-to-end Completeness — it would require formalizing the prover and is outside SCOPE.
- The **strong version** of D3.

## Conclusions

1. **The deterministic core of soundness has been formally established** (`sumcheck_telescope`
   and its implementation counterparts `rustSoundness`/`solSoundness`). As long as the
   implementation accepts, a false statement reduces to a root-hit in one of the 4 sumchecks,
   and that probability is bounded per round by ≤ deg/|F| via `Poly.roots_le_degree`.

2. **The most important finding is D3 (CRITICAL, confirmed)**: via `d3_strong` we have
   **formally proved** the existence of 2 proofs that completely satisfy the verifier
   (identical witnesses, differing only in the inverse helper, one of them claiming the
   incorrect inverse (0,2)). The verifier accepts an incorrect inverse = the soundness of
   the permutation argument is broken. Paper §4.5, "all terminal values are PCS-bound",
   does not hold in the implementation. The fix is to add batch/WHIR binding on the
   individual evaluation values of the inverse helpers.

3. **D10 (publicInputsHash not bound) is a HIGH that is still present**, and is specific to
   on-chain verification. A Solidity Poseidon implementation is the correct fix.

4. For specification §4.2.2 (D1, the Σ misstatement of g_sub), **correcting the document**
   is recommended (the implementation is correct).

5. The implementation is not the single protocol of the paper but a **stack of layer 1 + layer 2**,
   and no unified soundness theorem exists in the literature. The Lean formalization of this
   audit provides the foundation for that unification.

### Fix Status (2026-07-06)

- **D3 (CRITICAL) fixed**: batch consistency binding was added on the individual evaluation
  values of the inverse helpers.
  - Rust: added the `inverse_helpers_eval_value_at_r_{inv,h}` fields to `proof.rs`,
    output the batched values in `prover.rs`, and changed the discarding fold in 5g/5h of
    `verifier.rs` into an `ensure!` (symmetric with 5e/5f for the witness). Added 2 regression tests.
    **All 59 Rust lib tests pass** (honest roundtrip preserved + D3 tampering is rejected).
  - Solidity: added the corresponding fields + a `require` in `MleVerifier.sol`.
    **All 79 forge tests pass** (including E2E 7 + boundary 10).
  - Specification: stated in `plonky2_mle_paper_v2.md` §4.2.2 that inverse-helper binding is
    mandatory, and added verifier step 7b (batch consistency) to §5.3.
  - Lean: proved `d3_fix_distinguishes` (under a non-degenerate batch challenge `r≠1`, the
    honest inverse [1,1] and the incorrect inverse [0,2] give different batched values and
    cannot both be consistent with a single WHIR-bound value ⇒ the new `ensure!` necessarily
    rejects one of them).
- **D1 (Spec-bug) fixed**: corrected g_sub in `plonky2_mle_paper_v2.md` §4.2.2 from the Σ form
  to the correct Π form (the implementation was correct from the start).

### Remaining Work (in priority order)

1. Fixing D10 via Solidity Poseidon
2. Adding the degree bound on the Rust side for D2
3. Completing the proof of the body of the `SoundnessProp` paper version + the MLE uniqueness family

Note: with the current code, the coset E2E fixture runs into the WHIR duplicate-index problem
(SpongefishWhirVerify finding #1) (unrelated to D3; it has been confirmed that the transcript
matches byte-for-byte with and without the D3 change). That fixture keeps the existing passing
WHIR proof and injects only the new D3 fields, so as to stay green.
