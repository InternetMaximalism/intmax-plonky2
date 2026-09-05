# Main PCS repair integration evidence — 2026-09-05

**Engineering integration record; production release remains NO-GO.** This
record maps the six defects reviewed on main to the integrated repair and
records local validation. It is not an independent cryptographic audit or a
proof that no critical defect remains.

## Integration scope

The integration starts from main
`970ae6d51d272feeb46f9d1b542dfc127185d0da` and merges the complete repair
history through `5b1c28ae8b4da55eabd8928120712d3735ffb82a`. The repaired PCS
architecture and regenerated fixtures are taken together; the old D3 scalar
fields are not combined with the replacement proof schema. Main's historical
Lean files and the correct D1 subgroup-MLE product formula are preserved.

The supported default is wire v3 through the historical `V2` API names and
compact magic `MLEWHIR3`. The prior protocol is not a production fallback:

- Rust historical prover/verifier entry points and the optional-evaluation
  standalone WHIR verifier require the non-default `legacy-conformance`
  feature. Default-build doctests check that these APIs cannot be imported or
  called. Historical integration targets declare their feature requirement.
- Solidity `MleVerifier` is abstract and has no deployable implementation
  artifact. Its concrete `LegacyMleVerifierHarness` lives under
  `contracts/test/`. Deployable integrations use `MleVerifierV2` and
  `PinnedMleVerifierV2`.

No parent gitlink, deployment, or on-chain transaction was changed by this
submodule integration. Parent proof/configuration migration remains separate
required work.

## Mapping the six reviewed gaps

| Main finding | Integrated check or construction |
|---|---|
| C1: terminal constituent evaluations were disconnected from WHIR evaluations | [`mle_verify_v2`](../src/verifier_v2.rs) derives full-Ext3 constituent folds, the bound-cell mask, and packed row/index points before `WhirPCS::verify_grouped`. Solidity [`MleVerifierV2._verifyAtomic`](../contracts/src/MleVerifierV2.sol) folds the same `UsedClaims` consumed by the terminal equations through `PackedClaimExt3`, then supplies them to the bound WHIR verifier. |
| C2: constituent batching challenges preceded commitment of the constituents | [`mle_prove_v2_from_tables`](../src/prover_v2.rs) packs and commits the preprocessed/witness tables before their challenges and commits the challenge-dependent norm-inverse table before the outer relation challenges. `absorb_v2_claims_and_sample_indices` absorbs ordered individual claims before sampling constituent-index points; Solidity `_deriveInitialTranscript` and `_absorbClaimsAndSampleIndices` reproduce that order. |
| C3: outer/VK roots were disconnected from roots inside WHIR | `mle_verify_v2` checks the preprocessed root against the VK and passes all three ordered roots to [`WhirPCS::verify_grouped`](../src/commitment/whir_pcs.rs). Solidity `_verifyAtomic` passes the same ordered roots to [`verifyWhirProofBound`](../contracts/src/spongefish/SpongefishWhirVerify.sol); `_receiveCommitmentsAndOod` checks the received commitment roots against those expected roots. |
| C4: the Solidity final polynomial was not tied to authenticated final rows | [`_phaseFinalVectorAndMerkle` and `_verifyFinalSplit`](../contracts/src/spongefish/SpongefishWhirVerify.sol) check final openings in both ordinary-round and split-initial-commitment paths. `_requireFinalOpening` compares each authenticated folded opening with the final polynomial's evaluation. |
| C5: raw public inputs and the circuit's public-input hash were independent | `mle_verify_v2` and `_verifyAtomic` recompute the Poseidon hash from the raw inputs. Wire v3 additionally binds raw inputs directly to committed witness cells through [`evaluate_joint_norm_logup_terminal_with_public_inputs`](../src/permutation/norm_logup.rs) and [`OuterLogupExt3Verifier`](../contracts/src/OuterLogupExt3Verifier.sol). The canonical PI wire map is generated at setup and bound into the circuit configuration digest. |
| C6: Rust permutation dimensions and identity parameters were proof-controlled | `mle_verify_v2` checks VK dimensions and coset shifts against trusted `CommonCircuitData`, derives the subgroup powers canonically, checks gate metadata, recomputes the circuit configuration digest, and enforces exact proof shapes. The current proof cannot supply independent permutation identity parameters. |

These checks remove the specific missing validation paths identified on the
reviewed main. Their composition and quantitative security claims still need
the independent review listed below. The current specification is the
[wire-v3 addendum](../paper/mle_whir_v1_security.md#2026-09-03-wire-v3-superseding-addendum).

## Reproducibility and documentation

Canonical fixture bytes, protocol-schema values, and testdata remain unchanged
from `5b1c28ae`. The integration does not edit proof values to make checks pass.
The obsolete `xlarge_mul.json` fixture is removed as in that repair history;
its previous contents remain recoverable from the pre-integration main commit.
The stale duplicated Solidity terminal-transcript expectation is replaced by
[`TranscriptV1Golden.sol`](../contracts/test/TranscriptV1Golden.sol), generated
and drift-checked by [`transcript_e2e_trace.rs`](../tests/transcript_e2e_trace.rs)
against the retained canonical packed-v1 trace. This is historical conformance
data, not a wire-v3 protocol constant. Generated Rust line wrapping was aligned
with its generator; the generated values are unchanged.

`Cargo.lock` and the WHIR revision are pinned. CI uses `nightly-2025-03-23` and
Cargo `--locked`, checks the default and explicitly enabled historical MLE
paths separately, and adds the ordinary Solidity suite and deployment-size
checks with Foundry `v1.5.1` and Solidity `0.8.29`.

The root/MLE guides now describe the API and atomic proof/VK/config migration.
The [Lean archive](README.md) explicitly targets `ee80ee6d` and its `bee025f9`
D3 follow-up: PCS binding is assumed and portions of WHIR/transcript handling
are abstracted. The historical paper preserves D1's correct product formula
but replaces the misleading scalar-only binding argument with the current
constituent commitment/opening requirements. Historical theorem names and
passing Lean builds are not wire-v3 certification.

## Local validation status

| Check | Result at this checkpoint |
|---|---|
| Default `cargo test -p plonky2_mle --all-targets --locked --offline` | PASS on the final source, including wire-v3 positive, mutation, cross-language, schema, and resource-envelope checks. Eight explicit opt-in generators/diagnostics remain ignored. |
| Default `cargo test -p plonky2_mle --doc --locked --offline` | PASS, 4/4. |
| Workspace-root `cargo check --all-targets --locked --offline` | PASS. |
| `forge test --offline` | PASS, 349/349 tests across 28 suites. |
| `forge build --sizes --offline` | PASS: runtime bytes `MleVerifierV2` 20,782; `PinnedMleVerifierV2` 12,285; `SpongefishWhirVerify` 23,771. |
| `cargo test -p plonky2_mle --all-targets --features legacy-conformance --locked --offline` | PASS, including all seven honest fixture generations/verifications (354.40 s), all 16 integration tests, and the generated transcript golden. Eight explicit opt-in generators/diagnostics remain ignored. |
| `cargo clippy --all-features --all-targets --locked --offline -- -D warnings -A incomplete-features -A clippy::uninlined_format_args` | PASS on the final source. |
| `cargo fmt --all --check`, workflow YAML parsing, local document links/anchors, and `git diff --check` | PASS. |

Both Rust suites completed successfully, and fixture/schema/testdata byte
integrity was checked again after the legacy suite. These are local results;
hosted CI has not yet been verified. No public-chain deployment or parent
end-to-end acceptance result is implied by these checks.

## Remaining release conditions

Production remains NO-GO until the external wire-v3 cryptographic review,
protocol-specific Fiat--Shamir/grinding and composition analysis, and full
parent proof/configuration migration and acceptance matrix are complete. The
target-133 WHIR result is a generic-work estimate, not an unconditional
`2^-128` failure-probability guarantee. The parent Goldilocks/Poseidon recursion
estimate remains approximately 95 bits, independently of the local PCS work
factor. Keep existing chain/configuration pins and deployment containment in
place; this integration does not grant release approval.
