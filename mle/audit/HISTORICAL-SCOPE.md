# Lean formal verification scope (lean-formal-audit stage 0 deliverable)

> Historical scope: the definitions below are retained for the July target and
> do not model current wire v3. See [current scope](../README.md).

Date: 2026-07-06 / target commit: ee80ee6d (branch claude/gifted-germain-0283dd)

## Mode

**Audit mode** (formalization of an existing specification and implementation).

### Hierarchy of specification documents (discovered at stage 2; added 2026-07-06)

Initially only paper v2 was taken as the specification, but there exist 4 layers of definition documents closer to the implementation.
Divergence judgments must always be made against this hierarchy (mistaking the baseline leads to false detections):

- **Layer 0 (theory)**: `mle/paper/plonky2_mle_paper_v2.md` — the ideal protocol including
  the batching sumcheck (§4.4). **Partly unimplemented**.
- **Layer 1 (v1 design)**: `mle/README.md` L191-424 — formally documents "3-vector phased WHIR + combined
  sumcheck + aux commit (P_aux = C̃ + r·h̃)". The transcript order is also stated.
  However, the v2 logup addition is **not described** (stale).
- **Layer 2 (v2 design + audit)**: `mle/soundnessgame/MleVerifier.vol.md` — defines the background of introducing
  Φ_inv/Φ_h/Φ_gate + inverse helpers in Round 2 (vulcheck417).
  R2-#1 through #8. **This is the de facto definition document for v2**.
- **Layer 3 (threat analysis)**: `mle/tasks/todo.md`, `phase3_c1/c2_threat_model.md`,
  `phase2_c2_poc_report.md` — C1 (gate metadata not bound to the VK) / C2 (non-canonical injection) analyzed
  as CONFIRMED CRITICAL with PoCs, and fixed. Includes Phase 6 Finding 1
  (publicInputsHash not bound, HIGH, **unresolved**).

Auxiliary: `mle/paper/whir_optimization_report.md` (WHIR query characteristics),
`mle/soundnessgame/*.vol.md` (audit findings for each component).

By user instruction, consistency with both the Rust and Solidity implementations is also checked.

## Components in scope

Following the structure of paper v2:

| Component | Paper section | Lean file |
|---|---|---|
| Finite fields (Goldilocks / Ext3) | §2.1, §6.1 | `Audit/Field.lean` |
| MLE, eq polynomial, hypercube | §2.1, §2.3 | `Audit/Mle.lean` |
| Univariate polynomials (sumcheck round messages) | §2.4 | `Audit/Poly.lean` |
| Sumcheck verifier | §2.4, §5.3 | `Audit/Sumcheck.lean` |
| Abstract PCS interface (WHIR black box) | §2.5, §7.4 | `Audit/Pcs.lean` |
| Abstract structure inside WHIR + audit invariants | §2.5, SpongefishWhir*.vol.md | `Audit/Whir.lean` |
| Fiat-Shamir transcript | §5.4, §6.2 | `Audit/Transcript.lean` |
| Protocol proper (VK / Proof / Verifier §5.3) | §5 | `Audit/Protocol.lean` |
| Properties to be verified (propositions) | §3, §4.5, §6 | `Audit/Statements.lean` |

## Properties to be verified

1. **Soundness (Theorem 1, §6.1)** — deterministic core:
   verifier accepts ∧ statement does not hold ⇒ one of the enumerated Schwartz-Zippel-type
   bad events occurs (recording the "size" of each event = the numerator of the error probability).
2. **Completeness** — a proof from an honest prover is always accepted.
3. **Fiat-Shamir binding (§6.2)** — that challenges are deterministic functions of the preceding absorptions,
   domain separation, and injectivity of the canonical encoding.
4. **Absence of a binding gap (§3, §4.5)** —
   both that `MLE(b ↦ formula(W(b)))(r) ≠ formula(MLE(W)(r))` holds in general (the existence of the gap
   in §3), and that every terminal check of this construction is an "evaluation at the same point of a polynomial
   bound to the PCS" and therefore does not step into the gap (§4.5).

## Assumptions and threat model (managed centrally as axioms/hypotheses)

- **Adversarial prover**: the proof and all transcript messages are adversarial.
- **PCS binding**: WHIR is ε_PCS-binding. In Lean it is placed as an assumption in the idealized form
  "each commitment determines a unique polynomial table, and verification success implies evaluation agreement", and
  the ε_PCS error is recorded as a bad event (a structure field in `Pcs.lean`).
- **Random Oracle**: the Keccak256 sponge is parameterized as an oracle structure `FSOracle`.
  Properties in the ROM (unpredictability of a challenge after the preceding absorptions are fixed) are
  stated explicitly as assumptions.
- **Axiomatization of mathematical facts**: since Mathlib is not used, standard facts such as "a nonzero univariate
  polynomial of degree d has at most d roots" are axiomatized with explicit comments and listed in the assumption inventory.
- **What is trusted**: the verification key (circuit_digest, preprocessed_root) has been correctly generated.

## Out of scope

- Prover-side computational efficiency and memory (the performance description in §7)
- Quantitative analysis of WHIR's proximity gap (the WHIR paper itself is not re-proved —
  only up to a black box + abstract invariants)
- Zero-knowledge (explicitly stated as future work in §9)
- Circuit cost of recursive verification
- Verification of the improvement proposals (P0-P3) in `whir_optimization_report.md` is itself out of scope, but
  the soundness caveats of the on-the-fly method in §7.1 are mentioned in a comment in Statements

## Environment

Lean 4.10.0 (elan), Mathlib not used (self-contained). A lake package under `mle/audit/`.
