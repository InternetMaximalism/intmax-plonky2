# mle/audit — Lean 4 formal verification (lean-formal-audit)

> **Historical scope, retained during main integration (2026-09-06).** These models
> target the July `ee80ee6d` lineage, not current wire v3. Their theorems are not a
> soundness certificate for `*_v2` / `MLEWHIR3`. See [current scope](../README.md).

Lean 4 formalization of the WHIR-based multilinear proof system of
`mle/paper/plonky2_mle_paper_v2.md`. Scope, assumptions and threat model are in [SCOPE.md](HISTORICAL-SCOPE.md).

## Build

```
cd mle/audit && lake build   # Lean 4.10.0, Mathlib not used (self-contained)
```

Current status: **Stages 1+2 complete + pre-stage-3 cleanup done. All files build
successfully (0 warnings), 0 `sorry`, 1 explicit axiom**

### Pre-stage-3 cleanup (2026-07-06)

Before stage 3 (starting the proofs), the propositions were made non-vacuous and dead code was removed:

1. **Making `SoundnessProp` non-vacuous**: the old version's conclusion `∃ _e : BadEvent, True`
   was vacuously provable because BadEvent is unconditionally inhabited. It was replaced by a
   disjunction of `SumcheckHitInProof`
   (a root-hit fixed to the round-poly sequence of the proof) and a `logupSum` collision,
   eliminating trivial satisfaction.
2. **Making the sumcheck soundness core concrete**: added to [Sumcheck.lean](Audit/Sumcheck.lean)
   `polySub` / `foldEval` / `SumcheckAccepts` / `SumcheckHitSomewhere` /
   `SumcheckTelescopeHit` (the actual proposition of deterministic soundness via telescoping).
   The weak placeholder `sumcheck_soundness_core_prop` was removed.
3. **Making the Solidity model concrete**: the 12 `True`s in `SolVerifyAccepts` were fixed to
   the terminal checks (Φ_inv/Φ_h/Φ_gate/combined/g_sub) + sumcheck
   acceptance, by introducing the re-derivation bundle `SolDerived`. The only remaining `True`
   is `whirOk`, which is WHIR-internal (out of scope).
4. **New implementation-target propositions**: added to [Impl/ImplStatements.lean](Audit/Impl/ImplStatements.lean)
   `RustSoundnessProp` (fixed to the actual challenges stored in the proof) / `SolSoundnessProp`
   (fixed to SolDerived) / `RustCompletenessDecomp` / the counterexample-existence proposition for D3,
   `D3_inverse_helpers_substitutable_prop`.
5. **Dead code removal**: removed `lsum` / `IsPolyOfDegLE` / `honestRoundValue` /
   `WhirBinding` / `BadEvent` (inductive).

The remaining abstract `True`s (4 in total) are only legitimate abstractions: transcript
re-derivation order (Rust/Sol),
the empty lookup check, and WHIR internals (both models, outside SCOPE).

### Stage 3: proofs / Stage 4: report (2026-07-06)

The proofs were carried out without depending on Mathlib. **54 theorems, 0 `sorry`, 1 axiom** (`Poly.roots_le_degree`).
The final report is [REPORT.md](HISTORICAL-REPORT.md).

| File | What is proved |
|---|---|
| [Audit/Algebra.lean](Audit/Algebra.lean) | Basic algebra of the field class (notation wrappers + distributivity etc. for sub/neg/mul) derived from the axioms |
| [Audit/Proofs/SumcheckCore.lean](Audit/Proofs/SumcheckCore.lean) | **The core `sumcheck_telescope`** (deterministic soundness via telescoping), `polySub_eval`, `isZero_eval`, `accepts_length` |
| [Audit/Proofs/Statements.lean](Audit/Proofs/Statements.lean) | **`rustSoundness` / `solSoundness`** (fixed to the actual challenges, corollaries of telescope), `domainSeparation`, `fsOrdering`, `rustCompletenessDecomp` |
| [Audit/Proofs/MleLemmas.lean](Audit/Proofs/MleLemmas.lean) | **`linearCommutes`** (§4.5 leg 2: linear combinations of MLEs commute = the positive claim that there is no binding gap), `hsum_add`, `hsum_mul_left` |
| [Audit/Proofs/EqPoly.lean](Audit/Proofs/EqPoly.lean) | **`eq_diag`** (eq(b,b)=1), **`eq_sum`** (Σeq=1), `hsum_vprod_factor` (tensor sum), `mleEval_bit1`, **`bindingGapExists`** (§3: a gap really exists when \|F\|>2) |
| [Audit/Proofs/D3.lean](Audit/Proofs/D3.lean) | **`d3_substitutable`** (weak version of finding D3: 2 proofs that differ only in the inverse helper values yet agree on witness batch consistency) |
| [Audit/Proofs/D3Strong.lean](Audit/Proofs/D3Strong.lean) | **`d3_strong` (CRITICAL confirmed)**: 2 proofs satisfying every field of `RustVerifyAccepts`, with identical witness and differing only in the inverse helper; one of them claims an incorrect inverse (0,2) and is accepted |

**Main properties proved**:
- Soundness core (the deterministic part of Theorem 1): sumcheck telescoping. Acceptance + agreement of the final value + disagreement of the initial claim ⇒ a hit on a root of the difference polynomial somewhere among the actual challenges.
- Implementation soundness: from acceptance by Rust / Solidity, the fixed-version soundness (fixed to the stored / re-derived challenges) for each of the 4 sumchecks.
- FS binding: injectivity of the domain-separation labels, determinism of challenge-after-commit.
- Absence of a binding gap (§4.5): MLE commutation for the terminal linear combination.

**What remains in stage 3** (future work):
- Proof of the body of `SoundnessProp` (the paper version) (connecting the existential quantification to telescope).
  Since the implementation versions `rustSoundness`/`solSoundness` are proved, the substance of soundness is secured.
- The MLE uniqueness family (`mle_agrees_on_hypercube_prop` / `mle_is_multilinear_prop` /
  `mle_unique_prop`) — `eq_diag`/`eq_sum` are proved.
- End-to-end completeness (formalization of the prover, outside SCOPE)

**D3 (CRITICAL) is confirmed by `d3_strong`**: 2 proofs that fully satisfy the verifier, with
identical witness and differing only in the inverse helper; one of them claims an incorrect inverse (0,2) and is accepted.
(`Poly.roots_le_degree` — a nonzero polynomial of degree ≤ d has at most d roots. A standard
mathematical fact, axiomatized because Mathlib is not used). The other cryptographic assumptions (PCS binding,
Merkle collision resistance, injectivity of canonical encoding) are by design not axioms but
Props held as structure fields, so that they become explicit assumptions at their use sites.

## File layout (stage 1: Lean-ification of the abstract design)

| File | Content | Paper correspondence |
|---|---|---|
| `Audit/Field.lean` | Field class (abstraction of Goldilocks/Ext3) | §2.1, §6.1 |
| `Audit/Prelude.lean` | Vec / Bits / hypercube sums and products | §2.1 |
| `Audit/Poly.lean` | Univariate polynomials (sumcheck messages) + axiom on the number of roots | §2.4 |
| `Audit/Mle.lean` | eq polynomial, MLE evaluation, multilinearity; propositions for the basic properties | §2.1, §2.3 |
| `Audit/Pcs.lean` | PCS abstraction (WHIR as a black box) + split-commit | §2.5, §4.3, §7.4 |
| `Audit/Transcript.lean` | Fiat-Shamir sponge abstraction + §5.4 labels + canonical encoding | §5.4, §6.2 |
| `Audit/Sumcheck.lean` | Round checks, FS-version sumcheck verifier | §2.4, §5.3 |
| `Audit/Whir.lean` | Abstract structure of WHIR internals + turning soundnessgame findings #1–#4 into invariants | §2.5, SpongefishWhirVerify.vol.md |
| `Audit/Protocol.lean` | Circuit, statement, VK, Proof, verifier — all 11 steps of §5.3 | §4, §5 |
| `Audit/Statements.lean` | Propositions for the 4 properties under verification + stage-1 finding notes | §3, §4.5, §6 |

### Stage 2: implementation correspondence (Rust mle/src + Solidity mle/contracts)

| File | Content | Implementation correspondence |
|---|---|---|
| `Audit/Impl/RustTranscript.lean` | Line-by-line transcription of the Keccak transcript | `mle/src/transcript.rs` |
| `Audit/Impl/RustSumcheck.lean` | Round poly in evaluation-value representation + Lagrange interpolation + verify_sumcheck | `mle/src/sumcheck/{types,verifier}.rs` |
| `Audit/Impl/RustVerifier.lean` | Transcribes all 11 steps of mle_verify into the proposition bundle `RustVerifyAccepts` | `mle/src/verifier.rs` (849 lines) |
| `Audit/Impl/SolVerifier.lean` | Transcribes the verify of MleVerifier.sol into `SolVerifyAccepts` | `mle/contracts/src/MleVerifier.sol` (853 lines) |
| `Audit/Impl/Divergences.lean` | **Turns the spec ⇔ Rust ⇔ Solidity divergences D1–D9 into propositions** | Three-way comparison |

### The specification is 4-layered (stage-2 addendum, 2026-07-06)

Divergence judgements must always be made against this hierarchy. Details in [SCOPE.md](HISTORICAL-SCOPE.md):
- **Layer 0 (theory)**: `paper/plonky2_mle_paper_v2.md` (§4.4 batching is unimplemented)
- **Layer 1 (v1 design)**: `README.md` L191-424 (officially documents aux commit + combined sumcheck)
- **Layer 2 (v2 design)**: `soundnessgame/MleVerifier.vol.md` (the document defining Φ_inv/Φ_h/Φ_gate)
- **Layer 3 (threat analysis)**: `tasks/todo.md` and others (C1/C2 CRITICAL + PoC + fixes)

### Divergences identified in stage 2 (D1–D11; details in `Audit/Impl/Divergences.lean`)

| ID | Severity (provisional) | Content |
|---|---|---|
| **D1** | Spec-bug | The g_sub of layer 0 §4.2.2 is wrong, in Σ form. Both Rust and Sol use the correct Π form |
| **D2** | Medium | The degree-bound check of the combined sumcheck is **absent in Rust**. It is recognized in layer 2 R2-#8 and **Sol is already fixed**; the Rust side is the leftover |
| **D3** | **High/Critical candidate** | Only the individual↔batched consistency check of the individual evaluation values a_j, b_j of the inverse helpers is missing, asymmetrically with witness/preproc. Ext3 binding is claimed in the design (R2-#2), but the chain down to the individual evaluation values is broken |
| **D4** | Info | The unweighted Σ of Φ_h is faithful to the design of the layer-2 vol.md (the divergence is only with layer 0 §4.2.3). λ_h is a dead challenge |
| **D5** | Info | 96-bit reduction of the transcript. The comment "256bit/bias 2^-192" is a misstatement. Rust/Sol are consistent |
| **D6** | Info | The domain-separation labels disagree between layer 0 and the implementations. The implementations agree with each other |
| **D7** | Structural | The layer-0 §4.4 batching is unimplemented. The implementation is a **stacking** of layer 1 (aux+combined, documented in README) + layer 2 (v2 logup). No unified soundness theorem exists |
| **D8** | Trust assumption | Solidity's kIs / subgroupGenPowers are not bound to the transcript (caller's responsibility) |
| **D9** | Low | τ_perm is squeezed but unused (a remnant of layer 1) |
| **D10** | **High, unresolved** | publicInputsHash is not bound to publicInputs. Layer 3 Phase6 Finding1; because Poseidon is unimplemented in Solidity it is **still unfixed** |
| **D11** | Info/follow-up | There are sites of the same kind of non-canonical sub(p,X) inside the WHIR/Sumcheck libraries (layer 3 Phase6 Finding4, out-of-scope) |

**Most important**: D3 (the broken binding chain of the inverse helpers) and D10 (publicInputsHash not bound,
which layer 3 acknowledges as a currently existing HIGH). These two are expected to be the breaking points in the stage-3 soundness proof.

## Findings already raised in stage 1 (details: end of `Audit/Statements.lean`)

1. **Confirmed — specification misstatement (§4.2.2)**: the closed form of `g_sub` is
   `Σ_i r_i·ω^{2^i}` in the paper, but the correct closed form for the MLE is `Π_i ((1-r_i) + r_i·ω^{2^i})`.
   The Rust implementation (`mle/src/verifier.rs` L466-469) uses the correct Π form.
2. **SUSPICION (§4.4/§7.3)**: the paper claims the degree of the batching sumcheck is "1",
   but the summand `eq(r_*,b)·P(b)` should have degree 2 per variable.
3. **UNDERSPECIFIED (§5.3 step 7)**: the algorithm for back-reconstructing the 3-point evaluations
   from the batched claim is not described in the paper.
4. **UNDERSPECIFIED (§4.3)**: the derivation of the scalars that combine multiple columns into a single
   batching sumcheck is not described (modelled by interpreting them as powers of ρ).
5. **NOTE (§6.1)**: doubt about the aggregation of the error term `3/|F|` (τ, τ_inv, β·γ) of Theorem 1
   (the SZ for τ ∈ F^n should be n/|F|).

## Next steps

- **Stage 2**: line-by-line Lean-ification of Rust (`mle/src/`) / Solidity (`mle/contracts/src/`)
  (with line-number comments).
- **Stage 3**: proofs of completeness / soundness / FS binding / absence of a binding gap
  (`Soundness.lean`, `Safety.lean`). Findings 1 and 2 are expected to surface as the breaking points
  of the completeness proof.
- **Stage 4**: per-file full review + `REPORT.md`.
