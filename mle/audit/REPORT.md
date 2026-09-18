# Current wire-v3 Lean audit update report

2026-09-06 / source base `becfe98e37c76e62f02f1aa7a417c7b06840db67`.

## Conclusion

**We have added executable models and deterministic proofs for the important parts of the current implementation.
The overall goal of "rewriting the entire current implementation in Lean and proving its safety" is incomplete.**

By means of a manifest enumerating all sources, unformalized files are managed without being hidden.
Source hashes, type consistency, and the success of existing tests are not used as a substitute for implementation refinement or cryptographic soundness.

## Practical results obtained in this update

- Connected canonical field arithmetic, strict byte reading, 24-byte Ext3 encoding and representation conversion.
- Proved that Rust's zero-padded constituent fold and Solidity's sparse-prefix fold return the same result
  for arbitrary padding/challenge in a functional loop model.
- Proved that, under the same old digest, the tag/payload of a typed transcript frame is unambiguous before hashing,
  and proved the order of the function that generates a challenge at a designated counter after absorbing both lanes / all claims.
- Proved the checking conditions on actual bytes regarding truncation, non-canonical limbs, wrong headers, and surplus bytes
  of the outer compact grammar. Clearly separated from the opaque WHIR interior.
- Defined coupled rounds as an actual transition sequence and proved the uniqueness of length and result by induction.
- Proved that acceptance of atomic verify requires roots/claims matching against the same derived context,
  WHIR tail observation, and terminal agreement on both the norm and gate sides.
- In a limited model of the WHIR terminal row, derived from the success condition that the fold value of the same row passed to
  authentication and the evaluation of the final polynomial at the derived domain point agree for all queries.
  In WhirFinal we connected the same vector onward to the final sumcheck, the final claim, and EOF, but observations such as
  authentication / prior-stage state / decoder remain, so this is not a proof of all of WHIR.
- Proved that if a candidate/true sumcheck chain reaching the same terminal value has different initial values, then
  evaluations of different round functions agree at the actual challenge.
  We have not derived the probability of that event nor the existence of a circuit witness.

Although we have confirmed executable acceptance paths including positive ordinary examples, examples with observation functions
are not a substitute for actually generated cryptographic proofs.

## Previous continuation update (as of 69516414)

At this stage 6 models / 202 theorems were added, extending to a total of 14 models / 372 theorems.
The unaddressed items described below are the state at that time; subsequent updates are recorded in the next section.

- **WHIR terminal**: Connected the actual quadratic update, reverse-order fold of the final randomness, non-zeroness, the concrete
  norm/adjugate-style inverse computation, all round constraints, all linear forms, and the EOF of both cursors.
  The inverse identity, and that the observed decoder read all bytes correctly, are not proved.
- **Merkle**: Raw-byte hint boundaries, layerwise computation for paired/lone nodes and offset updates, computed-root checking.
  Reduced reaching the same root from different leaf hashes at the same index/depth to an actual 64-byte compression-input collision.
  The binding of the whole multi-opening and the collision probability have not yet been derived.
- **norm/logUp**: Made concrete the formal norm/adjugate, helper aggregation, kIs/subgroup/PI map of a fixed Config,
  and PI aggregation preserving order and duplicates, and connected them to the agreement of computed results at acceptance.
- **gate**: Proved configuration validation for all 14 families, concrete evaluation for 6 families, selector/Horner,
  and the equivalence of zero difference and exact 3-limb agreement. Active evaluation of the remaining 8 families is unaddressed.
- **Algebraic equivalence**: Proved commutativity, associativity, distributivity, and additive inverse of Ext3 from concrete Nat.mod expressions.
  Resolved the in-model equivalence of Rust's/Solidity's differently-shaped eq/subgroup expressions and square.
  Full recombination of the PI cache and equivalence with the actual bytecode are not proved.
- **Integration entry point**: Made concrete the 4 observations packed/norm/eq/gate. By a checked preflight,
  a `none` for an unsupported gate is not accepted with a zero fallback. We also checked an ordinary success example
  using non-empty routed wires/helpers. It comes with WHIR / initial FS / hash observations, and is not an example of generating a real cryptographic proof.

The 6 added models also underwent an independent read-only review by a separate party.
The error classification/order of Integrated is within the model and is not an agreement with the implementation's exceptions or slashing evidence.

## Second checkpoint (4422b4c7)

14 models were added, and together with 2 theorems added to the existing integration entry point, 326 theorems were added.
The root at this point has a total of 28 models / 698 named theorems. The counts are not treated as a safety attainment rate.

- **Concrete evaluation and integration of all 14 gates**: Completed evaluation of the remaining 8 families and connected GatesComplete
  to Integrated. Proved that a `Some` actual evaluation result is obtained from a valid configuration and input lengths.
  The unaddressed `None` and zero fallback of the old partial gate are not treated as a "proof of soundness".
  However, the polynomial degrees of all gates, circuit semantics, and the probabilistic soundness of aggregation are still separate problems.
- **Verification of actual constants and all rounds**: Included all 1023 Poseidon words and all 124 Coset words.
  Added a continuous check comparing all 18 tables verbatim against Solidity, with Poseidon also compared against Rust.
  The normal 135-wire Poseidon witness executes all 30 rounds and we checked 123 zero constraints and
  the existing Rust standard 12 outputs in the ordinary Lean kernel. This is not by itself a proof of hash security.
- **Concrete algebra of norm/inverse**: Proved the adjugate identity for actual Ext3 coefficients over the formal variable T³=2.
  Connected recomposition, the product with the inverse candidate, and the exact value / fuel condition of binary exponentiation,
  and reduced the product at actual inverse success to norm^(p−1) mod p. Fermat and non-zero norm are not filled in by assumption.
  Also proved the in-model equivalence of the WHIR final sum-form fold and the Packed difference-form fold.
- **Equivalence of the public input optimization**: Made concrete the actual OR/XOR mask and common-bit separation, newest-first cache search,
  summation of the same row, and the omission of order, duplicates, and the last eta update, and proved without assumptions that the cached
  PI aggregation returns the same value as the Rust direct-sum model.
  What is unconditional is a functional equation of the raw model; it does not mean that the actual code's input shape / memory conditions are unnecessary.
- **Inner WHIR byte processing**: Made concrete the raw hash chain, BE counter, 120-byte bulk challenge,
  24-byte canonical read, geometric RLC, PoW, and hint Vec prefix.
  Connected the initial phase's root / own-OOD / checked-unchecked claims / cross-OOD through to the actual initial sum,
  and checked a 272-byte non-empty initial processing example and a 320-byte example including the following sumcheck.
- **Reduced terminal observations**: Replaced all of WhirFinal's readMessage/checkPow/challenge with concrete byte processing.
  On success it reads 48 bytes in the same state, 56 bytes when PoW is enabled, and generates a challenge from 120 bytes.
  The already-read hint position is preserved, and the exact suffix length at acceptance and hint EOF were derived.
  The initial phase → first sumcheck is also connected to the same bytes, computed sum, and sponge.
  Unifying the intermediate rounds, raw row authentication, and sampling through to the final Context is incomplete.
- **Preparation for a field proof**: Stored the factor product of p−1, the exponentiation/gcd checks for 6 tuples at base 7,
  and `2^((p−1)/3) mod p = 4294967295` as a concrete certificate.
  The soundness of the primality test method, the primality of the small factors, and the general Fermat theorem are incomplete, and we do not yet conclude that p is prime.

The new gate group, Poseidon constants/rounds, Spongefish, WhirInitial, WhirFinalSpongefish,
WhirPrefix, PI cache/shared bits, algebra/exponentiation/numeric certificates, integration entry point, and constant checks
underwent a read-only cross-check by the implementer and a separate party.
No unresolved required fixes remain, but a manual cross-check is not a formal refinement.
The constant extractor is a limited lexer that removes comments and preserves strings; it is not a compiler.
The normal example of the PI cache is a computation example of the PI aggregation part, not an acceptance example of a complete Norm terminal/verifier.

At this checkpoint we have not modified the implementation proper, dependency configuration, main, or the parent pin. We also do not publish/push.
The results are saved as a checkpoint on the dedicated local branch `codex/lean-wire3-audit-20260906`.
The overall goal is still in progress and is not declared complete at this stage.

## Third checkpoint (f7236217)

Connected the current raw hint / Merkle processing, and added 6 models / 184 theorems.
The root at this point is 34 models / 882 theorems. The overall goal remains incomplete.

- **Path extraction from an actual multiproof**: Traced the actual layer processing for both paired and lone cases, deriving a
  depth-length path from every input leaf to the actually-checked root. The correctness of an independent authentication path is not assumed.
- **Binding from the original row bytes**: Connected the Vec element count, the contiguous hint slice, the raw hash, and the existing Merkle
  same-root/indices/cursor. Proved that for actual openGroup rows with the same root/depth/index, either the bytes, the canonical decoded values
  of the same Layout, and the full-column dots with the same weights agree, or there is a concrete hash collision.
  This is not an evaluation of collision probability, nor the acceptance soundness of all of WHIR.
- **sampling**: Made concrete the actual raw query generation that calls the hash byte by byte and advances the counter, BE order, mask,
  special branches, and the upper bound. The reordering is an executable reference version of insertion sort, and its equivalence with
  the source's in-place quicksort is explicitly not proved. Sortedness in the reference version is not diverted into a proof about the implementation.
- **Conditional connection of the inverse**: Proved the execution of the actual inverse, left/right inverses,
  cancellation, and division from the explicitly stated FermatAt(norm). Also obtained an unconditional inverse example from the concrete certificate for 7.
  Fermat for all non-zero values, non-zero norm, and irreducibility are not regarded as proved.
- **folding schedule**: From the projection of the actual configuration guard, proved that the initial + all intermediate + terminal equals
  the original number of variables, that the numVariables of each round agrees with the remaining suffix, the safety of subtraction,
  and the interleaving/final size. This is not a complete configuration validation including domains and point arrays.

Raw authentication success and canonical decode success are separate conditions. The branch order in which the final split's decode/aggregation
precedes Merkle is also not hidden, and we do not call the current openGroup a completed model of that.
The added models were cross-checked in full text, against the original source, and on the main theorems by a party other than the implementer.
Manual review is not a substitute for formal cross-language refinement.

## Model-correspondence discrepancies fixed by independent review

1. **Timing of configuration checks**:
   So that Solidity's constructor-only checks are not treated as call-time guards,
   we separated the composite boundary from the call boundary and made the deployment invariant explicit.
2. **Variable order of WHIR**:
   Separated the logical MLE order `row ++ index` from the native WHIR order,
   and corrected the model to actually call `Packed.whirPoint` and reverse the whole thing.

These are issues of the model's correspondence accuracy, and are not a report that a new implementation vulnerability was demonstrated this time.

## Entry points of the main theorems

| Theme | Theorem |
|---|---|
| canonical arithmetic | `Arithmetic.emul_canonical`, `Arithmetic.canonical_equality_iff` |
| zero padding | `Packed.sparse_fold_equals_zero_padded_fold`, `Packed.full_table_final_shape` |
| bytes / framing | `Transcript.fromLe_le_roundtrip`, `Transcript.frame_tag_and_payload_are_unambiguous` |
| exact outer parsing | `Compact.validation_requires_exact_exhaustion`, `Compact.strict_validation_all_fields_canonical` |
| sumcheck reduction | `Sumcheck.mismatch_requires_evaluation_collision` |
| verification boundary | `Verifier.acceptance_exact_whir_and_terminal_binding`, `Verifier.call_acceptance_yields_checked_acceptance` |
| concrete model connection | `Connections.verifier_transcript_roundtrip`, `Connections.packedFold_padding_invariant` |
| WHIR terminal row slice | `WhirTerminal.successful_each_query_exact_equality`, `WhirTerminal.verified_groups_authenticate_each_pair` |
| final sumcheck / claim | `WhirFinal.end_success_same_vector_and_all_checks`, `WhirFinal.end_success_final_fold_is_singleton` |
| Merkle bytes / reduction | `Merkle.accepted_opening_stays_in_slice`, `Merkle.same_root_same_leaf_or_path_collision` |
| concrete norm / PI | `Norm.acceptance_requires_computed_terminal`, `Norm.public_inputs_all_processed` |
| gate configuration / formulas | `Gates.every_configured_gate_checked`, `Gates.arithmetic_constraints_exact` |
| concrete algebra | `Algebra.emul_assoc`, `Algebra.norm_eq_loop_matches_rust`, `Algebra.norm_subgroup_loop_matches_rust` |
| checked integration | `Integrated.accepted_concrete_terminal_equations`, `Integrated.unavailable_gate_never_uses_zero_fallback` |
| all gate families | `GatesComplete.combined_has_output_iff_valid`, `Integrated.valid_decoded_gate_configuration_evaluates` |
| formal adjugate / inverse | `NormIdentity.formal_adjugate_identity`, `ModularPower.inverse_success_product_is_fermat_power` |
| inner transcript / PoW | `Spongefish.verifier_ext3_exact_cursor_and_bytes`, `Spongefish.pow_success_checks_actual_digest` |
| concrete WHIR initial | `WhirInitial.initial_all_roots_and_checked_claims`, `WhirInitial.initial_exact_read_count` |
| concrete WHIR sumcheck / EOF | `WhirFinalSpongefish.round_success_actual_sequence`, `WhirFinalSpongefish.end_success_exact_transcript_and_hint_eof` |
| connected initial prefix | `WhirPrefix.successful_prefix_is_one_execution`, `WhirPrefix.successful_prefix_exact_consumption` |
| cached PI equivalence | `PiCache.cached_binding_equals_direct_norm`, `PiSharedBits.actual_varying_mask_factoring` |
| numeric field certificate only | `GoldilocksCertificate.all_factor_checks_accept`, `GoldilocksCertificate.base_two_third_exponent_value` |
| actual multiproof extraction | `MerkleExtraction.accepted_nonempty_opening_extracts_paths`, `MerkleExtraction.accepted_raw_rows_bind_or_hash_collision` |
| bytewise sampling / reference boundary | `WhirSampling.raw_nontrivial_success`, `WhirSampling.reference_sampling_output_properties` |
| raw row / cursor connection | `WhirRows.group_success_same_merkle_inputs`, `WhirRows.empty_group_consumes_exactly_eight` |
| actual decoded row / dot binding | `WhirRowBinding.accepted_decoded_rows_bind_or_collision`, `WhirRowBinding.accepted_full_column_dot_binding` |
| conditional inverse units | `FermatBridge.norm_fermat_gives_actual_two_sided_unit`, `FermatBridge.actual_division_equation_iff` |
| folding schedule projection | `WhirSchedule.accepted_schedule_partitions_original_variables`, `WhirSchedule.accepted_round_annotations_equal_remaining_suffix` |

The names in the table above omit the common prefix `Audit.Wire3.`.
Only the headings of the initial modules are placed here; subsequent ones are recorded in each "Continuation update #N".
The headings of the most recent batches 40 and 41 are as follows.

| Theme | Theorem |
|---|---|
| concrete success of the installed WHIR | `WhirTailWitness.configured_six_claim_execution_example`, `WhirTailWitness.installed_whir_pair_accepts_a_full_verification` |
| tailRun at the deployed claim count | `WhirTailWitness.installed_tail_succeeds_at_a_six_claim_context`, `WhirTailWitness.six_verify_whir_is_true` |
| masks agree up to the claim count | `WhirTailWitness.configured_run_mask_congruent`, `WhirTailWitness.the_two_masks_agree_below_three` |
| toy hash / not derivedConfig | `WhirTailWitness.the_witness_hash_ignores_every_input`, `WhirTailWitness.the_accepting_configuration_is_not_the_derived_one` |
| acceptance at `numRouted = 80` | `RoutedAcceptance.routed_acceptance`, `RoutedAcceptance.routed_integrated_acceptance` |
| digest ignoring and collision | `RoutedAcceptance.routed_hash_is_a_transcript_collision`, `RoutedAcceptance.rho_ignores_the_statement` |
| gate 7 does not distinguish a difference of roots | `RoutedAcceptance.alt_proof_is_also_accepted`, `RoutedAcceptance.routed_wire_loop_runs_eighty_times` |
| routed acceptance that reads the digest | `DigestRoutedAcceptance.fixed_acceptance`, `DigestRoutedAcceptance.fixed_initial_transcript_separates_the_two_proofs` |
| the old hash does not separate the two proofs | `DigestRoutedAcceptance.routed_initial_transcripts_do_not_separate_the_two_proofs` |
| the chain is one byte wide | `DigestRoutedAcceptance.derive_digest_tail_is_thirty_one_zero_bytes`, `DigestRoutedAcceptance.fixed_hash_is_still_a_transcript_collision` |

All named theorems are managed in the [manifest](wire3-manifest.json), and checks are performed against all of them, not an excerpt.

## Correspondence status of all sources

| Rust/Solidity files in this checkout | Total | With partial model correspondence | Without model correspondence |
|---|---:|---:|---:|
| MLE Rust (`mle/src/`, including the old implementation) | 35 | 14 | 21 |
| MLE Solidity (`mle/contracts/src/`, including the old implementation) | 33 | 23 | 10 |
| Others (including tests, examples, other crates) | 222 | 3 | 219 |
| Total | 290 | 40 | 250 |

"With partial model correspondence" does not mean translation/proof of the whole file.
Nor is it a line-based coverage or a safety attainment rate.
For external WHIR dependencies we track dependency information with a fixed revision, but we have not
enumerated or formalized all of their sources in this table. No file is certified as having its entire implementation formally proved.

## Treatment of the old audit

The July root is stored in `HistoricalAudit.lean`, and the old README/REPORT/SCOPE are stored in
`HISTORICAL-*.md`. The mathematics, findings, and axioms of the old models are retained as historical material, but
they are not imported from the current root. Old axioms including `Poly.roots_le_degree` are not
diverted as grounds for the current proofs.

## Checks and reproduction

```sh
python3 -B mle/audit/test-check-wire3.py
python3 -B mle/audit/check-wire3.py
git diff --check
```

Lean 4.10.0's `lake` must be on PATH. The guard checks the hashes before and after the build, the full source inventory,
reachability of the entire current root, and the types and transitive axioms of all named theorems.
The only permitted global axioms are the 3 Lean standard ones.
**Explicit assumptions of the Engine and of theorem arguments remain separately from this.**

As of the previous 69516414, the following were executed in this working checkout.

| Check | Result |
|---|---|
| Build of the current Lean root | PASS — 15 files in total: 14 models and the root |
| Resolution and transitive-axiom check of all named theorems | PASS — 372, no custom axioms and no unproved holes |
| Source inventory and pre/post-build hash check | PASS — 356 files including 290 sources |
| Unit tests of the guard | PASS — 21 |
| YAML syntax of the CI workflow | PASS |
| Whitespace-error check of the diff | PASS |
| Diff of Rust/Solidity and dependency configuration from the target base | none |

The 356 files also include models, documents, checkers, and historical material.
The CI job checks the current root and the guard, but remote CI was not run in this work.
Since the implementation was not modified, all Rust/Solidity tests were also not re-run this time.
These Lean checks are not treated as completion of the whole cryptographic audit.

### Checks of the second checkpoint

On 2026-09-06 the integrated guard was run in this working checkout and the following were confirmed.

| Check | Result |
|---|---|
| Build of the current root | PASS — 28 models and the root |
| Resolution and transitive axioms of all named theorems | PASS — 698, only the 3 standard axioms |
| Source inventory and pre/post-build hashes | PASS — 370 files including 290 sources |
| Verbatim comparison of Poseidon/Coset constants | PASS — 18 tables / 1147 words, Poseidon also agrees with Rust |
| Guard unit tests | PASS — 27 |
| YAML syntax of the CI workflow / whitespace check of the diff | PASS |
| Diff of the implementation proper and dependency configuration from the target base | none |

There are no custom axioms, no unproved holes, and no substitution of proofs by native evaluation.
However, the remaining premises of theorem arguments / the Engine, the unconnected WHIR stages, and language refinement and
cryptographic soundness are incomplete items independent of this PASS. Remote CI and all Rust/Solidity tests were not run this time.

### Dependency investigation for the finite field proof

At the second checkpoint, the current audit and the parent's two audits use Lean 4.10 with no dependency packages. No available 4.10-compatible Mathlib
checkout or concrete Goldilocks primality proof was found. A binary cache apparently originating from another version was not adopted because
the corresponding source/toolchain/lock could not be confirmed, and at that point there was also no network use.

In the third continuation we investigated official Mathlib v4.10.0 in a temporary area. The commit is
`a719ba5c3115d47b68bf0497a9dd1bcbb21ea663`, and the HEADs of the 6 transitive dependencies of the official lock also agree.
LucasPrimality/Finite.Basic/NormNum.Prime and their 1333 dependent build targets succeeded.
Mathlib cache get was not used, but ProofWidgets fetched a release archive due to the package configuration.
**We do not describe this build as all-dependencies source-only.** The primality/Fermat candidates are still experiments outside the current root
and are not included in the 882 theorems. They have also not yet been adopted into the audit lakefile/lock or into the production dependency configuration.
The 10 isolated candidate theorems compiled successfully, and the axioms of the 6 main theorems were only the 3 standard ones.
From Lucas we derive the primality of the concrete p, general Fermat, the exclusion of a cube root of 2, and the two-sided inverse at actual inverse success, but
before adopting these candidates we do not change the current root's unproved scope to "resolved".
Before adoption we will clarify complete pinning / actual file contents / untracked sources / imports / search paths / axiom checks, and
the trust boundary of the release artifact or a procedure for regenerating it from source.

The primality, Fermat, inverses of all non-zero canonical Ext3, and the field construction that remained at this point
are addressed in the next, fourth continuation update. The above is a record at the time of the candidate investigation, and is distinguished from the later check results.

### Checks of the third checkpoint

On 2026-09-06 the integrated guard for the current root was run.

| Check | Result |
|---|---|
| Build of the current root and transitive-axiom check of all named theorems | PASS — 34 models / 882, only the 3 standard axioms |
| Source inventory and pre/post-build hashes | PASS — 376 files including 290 sources |
| Verbatim comparison of the actual constants | PASS — 18 tables / 1147 words, Poseidon also agrees with Rust |
| Guard unit tests | PASS — 27 |
| CI YAML syntax / whitespace check of the diff | PASS |
| Diff of Rust/Solidity / runtime dependencies from the target base | none |

The Mathlib candidates and the dependency checker being prepared for adoption are not included in this result. The root at this point is Std-only.
Remote CI and all Rust/Solidity tests were not re-run. main/push/parent pin are also not modified.

## Fourth checkpoint (da3df4ed)

Added 3 models / 55 theorems, extending to 37 models / 937 theorems.
Without touching the production Rust/Solidity dependencies, we introduced an audit-only Lean mathematics dependency.

- **Concrete primality and Fermat**: Decomposed all prime divisors of p−1 into 6 small prime factors, and
  passed the existing actual binary-exponentiation certificate to the proved Lucas criterion to derive the primality of p.
  The Fact instance is constructed from that theorem; primality has not been moved into an assumption.
  Fermat for all non-zero residues and the non-existence of a cube root of 2 were also connected to concrete Nat.mod.
- **Actual inverse of all non-zero Ext3**: From the double-adjugate identity over the base ZMod we derived the non-degeneracy of the norm,
  and returned it to the equivalence with the actual norm expression and canonical coordinates. Proved that success of the actual WhirFinal.inverse iff non-zero,
  and the canonical output and left/right product = 1. This is not generalized to off-cube Ext3 coefficients of the formal norm.
- **Finite field by actual operations**: Constructed a Field on a wrapper of Verifier.Ext3 using the actual add/sub/neg/mul and the actual inverse.
  We do not substitute operations from some other abstract field, and we make explicit the totalization inverse = 0 on failure.
  Proved the bijection with the three coordinates, characteristic p, cardinality p³, and finite-field Fermat/Frobenius.
  Positive computation examples of θ³=2 and the actual θ inverse are also included.

The main entry points are `GoldilocksFoundation.modulus_prime`, `general_fermat_nat`,
`GoldilocksNorm.actual_inverse_has_output_iff_nonzero`, `nonzero_actual_inverse_exists`,
`GoldilocksExt3Field.field_inverse_executes_when_nonzero`, `cardinality_exact`.
The common prefix is `Audit.Wire3.`. WHIR as a whole / circuits / language refinement / cryptographic probability are incomplete.

### Fixed audit dependencies and reproduction procedure

Mathlib v4.10.0 `a719ba5c3115d47b68bf0497a9dd1bcbb21ea663` and the 6 dependencies of its official lock
were all pinned by commit. The exact URLs/SHAs are cross-checked by the tracked `lake-manifest.json` and
the independent policy of `check-proof-dependencies.py`. Direct external imports are limited to the 3 names of Foundation
and the Ring of Norm (in the fifth continuation, Roots of WhirPolynomial was added).
Unrestricted Mathlib imports and axioms from historical material are not permitted.

```sh
python3 -B mle/audit/test-check-wire3.py
python3 -B mle/audit/test-proof-dependencies.py
python3 -B mle/audit/test-provision-proof-dependencies.py
python3 -B mle/audit/provision-proof-dependencies.py
python3 -B mle/audit/check-wire3.py
```

provision, after checking all existing dependencies, fetches only the missing ones from the fixed origin/SHA, and does not
reset/delete/repair existing modified or incomplete repos. The checker checks all 5601 tracked files,
the actual Git blobs of 64,398,270 bytes, and HEAD/origin/index. It also rejects
assume-unchanged/skip-worktree modifications hidden by ordinary status, additional Lean/config sources, symlinks, and external search paths.

On the first fresh build, `--no-tags` meant that the tag needed for ProofWidgets' release selection was missing and it failed.
We confirmed at the publisher that `v0.0.40` points at the pinned commit, and added only that one tag for new fetches.
Existing repos are also checked on the tag set and peeled targets, and a change to a different release name is not accepted.
This fix does not loosen the source/HEAD pinning.

**Source verification of dependencies is not provenance authentication of generated .oleans or release archives.**
Since an ordinary Lake build uses a ProofWidgets release, we do not call it a source-only regeneration of all dependencies.
Mathlib cache get and existing binary caches of unknown compatibility are not used.
The 3 standard axioms and the check of all theorems are maintained, but trust in the Lean toolchain, imported objects, and the execution environment is a separate boundary.
We are separately investigating a procedure for source regeneration with fresh output, and we do not mix the results of that investigation into the current PASS.

### Checks of the fourth checkpoint

The unit tests — 34 for the dependency guard, 20 for provision, and 33 for the main guard — PASS.
The actual source pin verification of the 7 dependencies, the CI YAML/whitespace diff, and the absence of changes to executable code were also confirmed.
The integrated check of the adopted 37 models / all 937 theorems also PASSes. All theorems were resolved in the actual environment and
their `.thmInfo` and transitive axiom dependencies were confirmed. There are no custom axioms and no unproved holes, only the 3 permitted standard axioms.
384 reviewed hashes, a complete inventory of 290 runtime sources, verbatim comparison of 18 tables / 1147 words of constants,
and verification of the 5601 tracked files of the 7 dependencies before and after the build also PASS. These are not proofs of language refinement or PCS probability.
Independent review also confirmed that Python's `-B` does not prohibit loading existing pyc, and
the helper was changed to explicitly compile and load checked source bytes.
We unit-check that no cache loader is used. The dependency source pins and Lean's axiom conditions are not loosened.
Remote CI and all Rust/Solidity tests were not run. main/push/parent pin were not modified.

## Continuation update #5 (after da3df4ed)

Added 3 models / 82 theorems, extending to 40 models / 1019 named theorems.

- **Meaning of the final polynomial and the number of agreement points**: Proved that the actual reverse-Horner and Polynomial.eval over the concrete Ext3 field
  return the same raw value. Coefficients are not reversed, and all canonical raw coefficients are lifted without loss.
  For two fixed vectors of the same length that are unequal, the number of distinct points at which their evaluations agree is at most length−1.
  We also exhibit examples where the empty sequence / singleton zero and different lengths give the same polynomial.
  The number of roots is derived from a proved Mathlib theorem; the old Poly root-count axiom is not used.
  This is not a proof of fixedness / FS / query distribution / adaptive choice / PCS probability.
- **Actual inverse connection of evalL0**: Derived x^(2^bits) from iteration of the actual specialized square.
  Proved 0<n<p and the uint64 range from degreeBits<64, and connected to the agreement of the rational expression using the actual denominator inverse.
  Output exists iff bits<64 and x≠1. x=1 is not replaced by the mathematical interpolation value 1; it is `none` exactly as in the actual source.
  We distinguish legitimate zero output at other n-th roots from the case where the inverse does not exist.
- **Same execution of intermediate WHIR**: Starting from the actual WhirPrefix, connected the new root / all OOD challenges / all answers / PoW,
  reference sampling, the actual raw Merkle of the previous root, the actual RLC, canonical decode and full-column dots,
  constraint preservation, the concrete sumcheck, and the previous-root update into a single state sequence.
  Also implemented the switch from 3 base roots × 1 vector at the first stage to a single Ext3 root at later stages.
  Proved, on success, all queries / all groups / all columns, the same RLC index, the original 32-byte slice of the root,
  the random prefix, the constraint count, and the transcript/hint cursors.
  A normal toy example of initial processing + the first sumcheck + 2 intermediate rounds consumes 736 transcript bytes / 128 hint bytes.
  It is an execution example with a toy hash, not an example of generating a production cryptographic proof.

WhirIntermediate's ProfileShape is a projection of the previous-round settings originating from the VK/config, and does not
add a guard that does not exist in the source. Nat.pow of the domain point is a model of the mathematical
result of _glPow; language refinement of the binary loop is still a separate problem.
The instruction-level correspondence between pure decode→dot and the source's sequential decode/arithmetic, and the in-place quicksort, are also not proved.
Connecting the final vector/read/Merkle to the Final.Context originating from the original prefix, and on to the final sumcheck/claim/EOF,
is the next step; the intermediate-round proof alone in this update is not treated as completing all of WHIR.

WhirPolynomial/GoldilocksLagrange underwent an independent review of the full text, actual source, and premises by a separate party and PASSed.
For WhirIntermediate the root also cross-checked all definitions, theorems, and each source phase of the original.
As an external import, only WhirPolynomial's Mathlib.Algebra.Polynomial.Roots is additionally permitted.
The integrated guard and the check of all 1019 theorems PASS. 40 models / 387 reviewed hashes, runtime 290 / 28 partially corresponded,
18 tables / 1147 words, and verification of the 5601 tracked files of the 7 dependencies before and after the build also PASS.
The 33 main-guard tests, CI YAML/whitespace diff, and absence of changes to executable code were also re-confirmed.
This is a check using ordinary Lake artifacts, and does not yet include the check results of fresh source regeneration.
The implementation, main, push, and parent pin are not modified.

When connecting the premise of distinct evaluation points to actual queries, we statically confirmed that `_validateDomain` alone does not
check the order of the generator. It is necessary to prove the order from the generator-generation path of the fixed VK/config, and
a mere shape check is not reinterpreted as a proof of a primitive root. This is not a demonstration of an attack, nor a judgment of the
safety/unsafety of all fixed configs; it is a boundary of configuration generation that should be closed in future soundness proofs.

## Continuation update #6 (after 88d8a135)

Added 5 models / 172 theorems, extending to 45 models / 1191 named theorems.
The following are deterministic proofs within the model, and are not the completion of the soundness of the whole implementation.

- **Same execution through to the terminal**: WhirTail.run retains the results of init / the actual prefix / the actual intermediate sequence, and connects
  a single read of the final vector, PoW / reference sampling, both terminal branches, the Horner comparison,
  the final fold of the same vector, and the sumcheck / all claims / both EOFs under the same derived Context.
  The final split preserves the source order hash → canonical dot → vector RLC addition → cursor → Merkle for each root, and
  standard preserves raw authentication → decode/Horner for each row.
  The 32-byte projection of the root is lossless. Normal toy examples that make all initial claims checked are 336/72 and 488/128 bytes.
  We do not regard an arbitrary runTail State as originating from the earlier stage; we use the provenance theorem of run success.
- **Actual deduplication**: Formalized the actual loop that compares the current buffer[i]/[i−1] and overwrites at the write position.
  Proved all read/write bounds, termination in n−1 steps, preservation of the unread suffix, and agreement of the final write length with the reference dedup.
  The assumption of sorted input is unnecessary for this equivalence, and is used only in the corollary about strictness. quicksort is not proved.
- **Order of the fixed evaluation point**: Derived order(7)=p−1 from the concrete certificate of 6 prime factors, and for k≤32
  proved that 7^((p−1)/2^k) has order 2^k and the injectivity of powers. Composed with the range of the transpose exponent, the inverse transform, and injectivity.
  This is not applied unconditionally to an arbitrary shape-valid generator or digest-accepted config.
- **Degree of the actual sumcheck**: Proved the actual c1 recovery, Horner, actual endpoint sum = claim, and degree ≤2 over the concrete field.
  Two actual quadratics with different fixed canonical claims agree at at most 2 points.
  Preserves the same message/challenge/state of a successful round, and also connects to the conditional disagreement of two existing chains.
  The true circuit semantics of the comparison-side chain, fixedness / FS / query distribution / probability are not proved.
- **All typed configuration checks**: Preserving all source scalars and raw evaluation points, checks the initial fold/domain, each round,
  the final remainder/size, and single/multi-point, in that order. The original limbs are not changed even after canonicity is confirmed.
  Distinguishes the bound and deployment entry points, and from success derives the existing Schedule, all domains, all points, the exact counts, and
  WhirInitial.validatedParams. It does not add constraints on samples/threshold/trailing mask bits that the source does not check.
  ABI/uint widths/overflow, complete projection from the immutable VK, and the 3×1 profile continue to be separate boundaries.

The 5 added models were confirmed in full text, against the source, and on the explicit premises by a root different from the implementer.
WhirDedup/WhirTail/WhirParameters additionally PASSed an independent read-only review by yet another party.
We also stated in the docs of the relevant theorems that the expected evaluation value is a boundary where the typed caller already passes canonical input,
and that we do not claim to have derived the canonicity of the expected value itself from the raw check of the configuration points.
The direct build of the 5 models moved to the adopted names and all integrated guards PASS.
We checked all 1191 named actual theorems/types/transitive axioms, 392 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.
The current source inventory is 29 partially corresponded / 261 uncorresponded out of 290 files, and we do not certify formal correspondence for all files.
The 33 guard / 34 dependency / 20 provision tests, CI YAML, whitespace diff, and runtime-unchanged checks also PASS.
The 45-model check here is ordinary Lake output, and its scope is distinguished from the 40-model fresh check in the next section.

## Fresh Lean source regeneration check of the 40-model checkpoint

Before adding the 45 models, we froze `88d8a1356eb1a83eda1b7fa8784e5570eca9a507` and
performed a separate check that does not reference existing non-toolchain `.olean`s. The result was PASS (777.405 seconds).

- manifest SHA256: `f11c4729b3bb077bf11b333fd95e70e6adcddc1fcc9e7e923e87fc0be9b3e6c9`.
- 1370 non-toolchain modules: audit/root 41, Mathlib 1091, Batteries 99, Aesop 108,
  Qq 11, ProofWidgets 18, ImportGraph 2. All regenerated from source into a new output location.
- For all 1019 theorems, re-checked `.thmInfo`, types, and transitive axioms with a search path containing only the fresh output.
  No custom axioms / unproved holes; only the 3 permitted standard axioms. The 5 new models are not mixed into this count.
- At start and end, verified 387 reviewed hashes, the full source inventory, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.
  For each actual compile, import resolution agreed with the existing source graph, and all generated artifacts/sources/JS were re-hashed.
- Lean 4.10 commit `c375e19f6b656fcd594cdca3a38b8578634df8cd`, binary SHA256
  `2af8d3dec15cf5a79a9521cbdf692fa3fdf3110704c4fac2e7fe3c92b36d415b`.
  We do not claim that `--trust=0` alone enables source re-verification of old imported artifacts.

The storage location of that local check is `/private/tmp/wire3-fresh-source-build.497h73wc/`.
The receipt SHA256 is `bfa4ec60d782fc0de20d6ff9f3462e353801eb2d8b1e09021390aae13648299f`,
and the graph SHA256 is `edb9a9d17980ae0d298e7a48d1ad6d58b3c75c58373f71c6268c914a3c152cb1`.
The temporary runner used was `/private/tmp/wire3-fresh-source-runner.iXATos/fresh_audit.py`,
with SHA256 `9128f90b80becc4a43cae970567362887ce42da1970debad150e196fea0b46ed`.
We do not treat retention of this temporary path as a substitute for reproducibility in another environment.

The runner underwent an independent review of all sources and failure paths, and its 12 auxiliary self-checks also PASS.
However, we record the weakness that the check with an invalid `.pyc` fixture cannot detect a regression to ordinary import.
The current loader compiles/execs the actual source bytes and does not read existing bytecode caches.
Even on an intermediate failure it attempts the end-of-run source check. It does not use the network, Lake, release fetching, or writing to existing artifacts.

**The claim is limited to "Lean source regeneration using fixed JS data and a check of all theorems."**
The 11 ProofWidgets display JS files are used with their existing bytes fixed and are not regenerated from their source.
That there is no malicious FS modification conflicting with the Lean toolchain/core artifacts, Python/Git, or the fixed metaprograms
remains in the trust boundary. This is not treated as having proved implementation refinement, cryptographic soundness, or a fresh check of later models.

## Continuation update #7 (after ac3476bb)

Added 2 models / 59 theorems, extending to 47 models / 1250 named theorems.

- **Number of agreeing queries at the actual evaluation points**: Wrapped the same raw Ext3 value of WhirIntermediate.domainPoint
  into the concrete Field, and proved its agreement with the post-transpose point originating from the fixed generator.
  Under the explicit conditions k≤32, agreement of the actual generator with the fixed value, positive coset dimension, and product = 2^k, derived injectivity, and
  proved that the number of distinct queries at which two fixed canonical vectors of the same length that are unequal agree is ≤ length−1.
  Connected to both the actual raw Horner and the normalized comparison. This is not a proof about the actual query range or configuration generation.
- **Conditional upper bound including the actual remainder conversion**: Proved a bijection between all 120-byte inputs and 3 40-byte LE integers,
  and connected it to the actual reduceChallenge on the same input. Using the injectivity of quotient/remainder, derived that the number of
  inputs reduced to d points is ≤ d·ceil(2^320/p)³, without enumerating the huge full input space.
  Under a finite uniform law that defines all 120-byte inputs as equiprobable, the probability that fixed unequal WHIR quadratics
  agree is ≤2(ceil(2^320/p)/2^320)³. This does not prove the distribution or independence of the actual Keccak/FS.
  The outer MLE uses a 3×32-byte squeeze and a different coefficient recovery formula, so we distinguish it from this inner theorem.

The 2 added models were cross-checked by the root in full text, against the actual source, dependent models, and explicit premises, and built directly under the adopted names.
An independent read-only review by a separate party also found no required fixes. An explanation not to confuse the inner and outer challenge distributions
was also added at the head of WhirChallenge. The integrated guard checked all 1250 named actual theorems/types/transitive axioms, 394 hashes,
18 tables / 1147 words, and the 5601 files of the 7 dependencies, and PASSes. The source inventory is 29 partially corresponded / 261 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests, whitespace diff, and runtime-unchanged checks also PASS.
The overall implementation/PCS soundness is incomplete, and
the 40-model fresh check is not reinterpreted as a fresh-regeneration record for these 47 models.

## Continuation update #8 (after 6642bd83)

Added 5 models / 181 theorems, extending to 52 models / 1431 named theorems.

- **From a single configuration to all phases**: From the same checkBound-ed p, projected the initial / previous-round opening / current round / terminal.
  Without any separate shape assumption, from execution success and the explicit 3×1 condition, derived the shapes of all reachable intermediate phases and the terminal Context,
  continuity of the same state, fold splitting, and exact counts and both EOFs. The raw generator is preserved by the canonicity check.
  Even for types that take generic Params, the source correspondence is not extended beyond 3×1.
- **General proof of the actual indexed sort**: From the actual scan/swap with a midpoint pivot, maintained the sentinel and partition classification, and
  from the fact that the first swap increases i and decreases j, proved strict shrinking of the recursion width and total termination.
  Using out-of-range invariants and preservation of elements within the interval, derived sortedness of all recursions, and only at the end concluded agreement with the reference sort.
  We do not substitute examples given large fuel or an external sortedness assumption for generality.
- **Full execution in actual sampling**: Connected actual sort → indexed compaction → raw query, preserving the early branches for count=0 and single leaf.
  The reference version agrees on the whole Option, all States, and failures, and all results of initial → intermediate → terminal with both sampling sites swapped also agree.
  The single checked configuration entry point and its contextShape are also connected.
- **Connection with the actual bitwise exponentiation**: Identified the 64-bit mask, low-bit branch, right shift, and the scalar loop of each mulmod
  with the existing exponentiation runner. Proved termination within 256 fuel and the exact value for all Fin64 inputs / Fin256 exponents, that the returned value < p < 2^64, and
  agreement with the existing domainPoint for transpose queries within the same range. The order of an arbitrary generator is not concluded.

The full text, source, and dependent models of all added candidates were cross-checked by the root and a separate party, and no required fixes remained.
Ambiguous import names arising from the migration to the adopted namespace were fixed to fully qualified ones, and all model/root builds were re-checked.
The integrated guard PASSes the check of all 1431 named actual theorems/types/transitive axioms, 399 reviewed hashes, 18 tables / 1147 words,
and the 5601 files of the 7 dependencies. The source inventory maintains 29 partially corresponded / 261 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests, CI YAML, whitespace diff, and runtime-unchanged also PASS.
These are correspondences within manual models, and are not formal refinements of source/compiler/Yul/EVM, memory, or gas, nor proofs of
provenance from the immutable VK, the true circuit polynomial, or ROM/PCS soundness. They are also distinguished from the 40-model fresh check.

## Continuation update #9 (after 4063db74)

Added 6 models / 140 theorems, extending to 58 models / 1571 named theorems.

- **Actual outer update formula**: Identified evaluateRound's coefficient sum, concrete inverse-two, and reverse Horner with
  evaluation of a polynomial over the concrete Ext3 field. Proved endpoint sum = claim, the degree upper bound by the number of transmitted non-constant coefficients,
  and the number of agreement points of polynomials with fixed unequal claims. Both actual updates and states of a coupled round are also preserved.
  The fixed 5-coefficient loop of the log source requires the existing coefficient-length preflight, and an arbitrary-length helper is not substituted.
- **Distinguishing outer challenges**: Connected the actual 3×32-byte squeeze's same digest, consecutive counters, and remainder.
  Connected log 0..2 / gate 3..5 after absorbing both coefficient sequences to the same update polynomial. Under an explicit uniform triple law,
  the probability that a fixed polynomial agrees is ≤ d(ceil(2^256/p)/2^256)³. log 5 / gate q+2 have separate upper bounds, and
  the uniformity, independence, adaptive fixedness of the actual Hash/FS, and multiplicative amplification of probabilities are not proved.
- **Actual degrees of 7 families**: After identifying the zero-filter branches of all 14 families with the same concrete constraint/Horner,
  proved agreement of the actual constraint expressions of IDs 0,1,2,3,5,6,7 with polynomial evaluation. When both the wire and constant sequences are affine,
  the degrees are at most 0,1,1,3,1,3,3. Local constants are also preserved as variables, and the non-residue 7 of Ext2 and the actual constants and order of the MDS are preserved.
  From the actual configuration check / input lengths, derived selected-row contribution ≤ q+1, and ≤ q+2 after explicit affine weights.
  The remaining 7 families are symbolic NONE, and gate truth, all-row sums, authentication endpoints, and interpolation coefficients are not filled in by assumption.

The 6 added models were cross-checked by the root and a separate party in full text, against the actual source, dependent models, and assumptions.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 1571 named actual theorems/types/transitive axioms,
405 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.
The source inventory is 30 partially corresponded / 260 uncorresponded out of 290 files (added the partial correspondence of coefficients.rs).
The 33 guard / 34 dependency / 20 provision tests, CI YAML, whitespace diff, and runtime-unchanged also PASS.
The scopes of the ordinary Lake check and the 40-model fresh check are distinguished, and this is not treated as completion of the whole implementation/PCS soundness.

## Continuation update #10 (after 80b63289)

Added 5 models / 145 theorems, extending to 63 models / 1716 named theorems.

- **Actual degrees of the formal Norm**: Treating the 3 coordinates of the denominator also as affine polynomials in the Ext3 coefficients,
  derived formal adjugate ≤2 / norm ≤3 / helper ≤4 / logUp ≤3, eq-weighted rows and finite sums ≤5, and PI ≤2.
  Also proved the single contribution of the actual Norm.wireStep and its evaluation agreement, and a weight builder matching the actual number of lambda/eta multiplications.
  The canonical Ext3 non-zero norm theorem is not diverted to off-cube formal coordinates. We also confirmed an algebraic example of degree 5 that becomes X^5−X.
  round_evaluation_actual is an agreement with in-candidate row / PI expressions, and is not a complete connection to endpoint extraction from mutable arrays,
  application of all weight builders, provenance from PI suffix/column/prefix, or interpolation/transmitted coefficients.
- **Gate degrees up to 12 families**: Added Exponentiation ≤4, BaseSum ≤ fixed base, the 2 Reducing kinds ≤2, and
  RandomAccess ≤ bits+1. Preserves high-order bit order, the full range product, the variable alpha wire and reset to claimed-next,
  recursive scratch folding, and the order of trailing extra constants. Booleanness and constraint satisfaction are not assumed.
  Connects the actual validateGate / all configurations / both column lengths to actual contribution ≤ q+1, and ≤ q+2 after explicit affine weights.
  The nonlinear Poseidon4 / Coset13 remain symbolic NONE. Actual evaluation of all 14 families and the degree proof are not conflated.
- **Actual RLC of WHIR**: Identified the actual geometricPowers and increasing-order row dot with the same concrete Field polynomial.
  Proved that the number of agreement points of fixed unequal canonical vectors of the same length is ≤ n−1, and a bias-inclusive upper bound under an explicit uniform law
  for the actual 120-byte / 3×40 LE reduction. count 0/1 consume nothing; 2 or more consume the same four blocks and counter+4.
  Preserves the actual phase order and sizes: after reading all claims/cross, vector RLC → constraint RLC of the next state.
  Hash uniformity / independence of the 2 RLCs, vector extraction from the root, adaptive fixedness, and the soundness of nested total sums are not proved.

All 5 added models were cross-checked by the root in full text, against the source, dependencies, and assumptions, and an independent read-only review by a separate party also PASSed.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 1716 named actual theorems/types/transitive axioms,
410 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.
The source inventory maintains 30 partially corresponded / 260 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests, CI YAML, whitespace diff, and runtime-unchanged also PASS.
The implementation, main, push, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

## Continuation update #11 (after c2b3684a)

Added 10 models / 322 theorems, extending to 73 models / 2038 named theorems.

- **Gate degrees of all 14 families**: Executed Poseidon4's actual state (swap/delta, a fresh wire before each S-box, omission of the constant in the
  final partial round, circulant/sparse MDS and the partial-initial matrix) using the existing actual constant tables, and without assuming constraint vanishing
  derived 123 constraints and degree ≤7. For Coset13, from old-product evaluation → update, intermediate claimed E/P constraints → reset, and clamped next
  count ≤ D−1, derived degree ≤ D and 4+4·intermediates constraints at the actual metadata's D≥2. From the success of actual validateGate for all 14 families, proved
  the existence of the symbolic term list, evaluation agreement with GatesComplete.evaluateUnfiltered, and per-family upper bounds
  0,1,1,3,7,1,3,3,4,base,2,2,bits+1,D, selected-row contribution ≤ q+1, and ≤ q+2 after explicit affine weights.
  The NONE of the 12-family dispatcher does not remain in this all-family wrapper, but gate truth and endpoint provenance are separate boundaries.
- **All-row aggregation and Boolean suffix sums**: Connected the ordered aggregation in which all rows of the actual combineRows use the same wires/constants/publicHash/alpha
  to a single polynomial fixed before the evaluation point, and from validateRows derived degree q+1, agreement with the complete evalCombined,
  and ≤10 after weights from the actual configuration envelope q≤8. The actual 2s/2s+1 reads, the executable interpolation at the same challenge, and
  the increasing-order suffix sum over 0..2^remaining−1 (including remaining=0) are also proved with the same polynomial, and under an explicit TableShape
  the fallback read does not occur. Commutation with Rust's slot-first / forward alpha, the mutable grid transpose,
  provenance from DenseMle endpoints, and connection with interpolation are not proved.
- **Actual Gauss elimination and totality of the outer interpolation**: Modeled with indices the natural nodes of coefficients.rs, increasing-order powers, RHS column n, no pivot exchange,
  diagonal inverse, normalization over pivot..=n, cloning of the pivot row, capture of the factor before writing, increasing-order column subtraction, coefficient-order extraction, and rejection of empty input,
  and proved that all accesses are within n×(n+1) and that the nodes fit in u64. With a proof-only ghost RHS, identified the reached pivot = ∏_{j<p}(p−j),
  so that for n≤p all prefixes / all n stages succeed, the actual WhirFinal.inverse is executed, and it is total on non-empty input. For degree<p,
  from samples over 0..degree, the exact coefficients and the omitted constant message, and that the actual Verifier.evaluateRound returns f(r).
  Specialized to norm degree 5 and checked gate q+2 (q>0, q+2≤10).
- **Indexed DenseMle bind**: Proved that in the bind loop of ext3.rs each i reads 2i/2i+1 before writing, writes in increasing order, and finally
  truncates, that the unwritten suffix is invariant, Valid length = 2^numVars, the source numVars>0 guard, the execution of all bindMany, agreement with
  Packed.layer/fold, and the bridge to affine Norm. constructor/from_base/usize/memory refinement remain.
- **Outer initial transcript and adapter**: Proved the actual order of 16 frames (circuit digest, raw PI, 15-word u64-LE metadata,
  bytes32-BE config digest, 64/32-byte identifiers, preprocessed/witness root), the exact counters for eta → beta/gamma, then
  norm-inverse root absorption → xi → lambda/rho/kappa → log tau → gate alpha → gate tau, that for d≤13
  all checked squeezes succeed, the identifier-length guard, the toInitial round trip, and the losslessness of the 40-byte internal snapshot.
  OuterAdapter connects the actual coupledRound's 6 limbs/counter, 5 claims + an empty 6th cell → index domain → log/gate index sequences
  (all limbs agreeing with the existing constituentIndices), a checked loop definitionally identical to Verifier.roundStep, and
  the Option prefix initial → coupled rounds → claim/index → packed fold → whirContext, and has success from
  envelope/shape/InputSizes and a non-empty example at an arbitrary Hash. It does not totalize malformed decodes to zero/default.
  Agreement with the existing total Engine is conditional with CommitAgrees/SamplesAgree/initial/fold agreement made explicit.
  PI hash recomputation, config digest, VK/config semantics, Hash security, complete acceptance, and the PCS/WHIR connection are not proved.

The 10 added models PASSed independent read-only review by the root and a separate party at the candidate stage (the source cross-check review of OuterInterpolation/Total and
OuterAdapter was performed in this update, with no required fixes).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2038 named actual theorems/types/transitive axioms, 420 reviewed hashes,
18 tables / 1147 words, and the 5601 files of the 7 dependencies.
The source inventory is 31 partially corresponded / 259 uncorresponded out of 290 files (added the partial correspondence of sumcheck/ext3.rs).
The 33 guard / 34 dependency / 20 provision tests, CI YAML, whitespace diff, and runtime-unchanged also PASS.
The implementation, main, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

For this state of 73 models / 2038 theorems, using the same temporary runner as at the 40-model point
(`/private/tmp/wire3-fresh-source-runner.iXATos/fresh_audit.py`, SHA256
`9128f90b80becc4a43cae970567362887ce42da1970debad150e196fea0b46ed`),
we regenerated all non-toolchain dependencies from source into an empty new output location, and checked all theorems using only that output.

- 1403 non-toolchain modules: audit/root 74, Mathlib 1091, Batteries 99, Aesop 108,
  Qq 11, ProofWidgets 18, ImportGraph 2. All regenerated from source into the new output location.
- Re-checked the `.thmInfo`, types, and transitive axioms of all 2038 theorems using only the fresh output. No errors,
  and only the 3 permitted standard axioms. Elapsed 1072.292 seconds.
- At start and end, verified 420 reviewed hashes, the full source inventory, 18 tables / 1147 words,
  and the 5601 files / 64,398,270 bytes of the 7 dependencies, with agreement.
- Storage location `/private/tmp/wire3-fresh-source-build.g45kkble/`. Receipt SHA256
  `d7404564544658ad1a1958ca2530eaa540e376976139bc6a90c2cf1b9bdcd437`, graph SHA256
  `8ef2043045aa89602b5e84ffbe2cbffeca9d4f49a8a46841f8cd455d3b4b2c89`. The manifest SHA256 at run time was
  `1522e8c7afe3e7e43706fd4a073b2e275ab32c474886c218c016243f9d8b5fbe`, and the only subsequent difference is
  the REPORT/manifest hashes accompanying the appending of this record.
- The 11 ProofWidgets JS files are fixed existing bytes. The Lean toolchain/core, Python/Git, the fixed metaprograms, and
  a non-adversarial FS remain in the trust boundary. We do not treat retention of this temporary path as a substitute for reproducibility in another environment,
  and do not reinterpret the fresh PASS as a proof of implementation refinement or PCS soundness.

## Continuation update #12 (after daa945d1)

Added 4 models / 137 theorems, extending to 77 models / 2175 named theorems.

- **Commutation with Rust's slot-first order**: Models with indices each gate evaluation of gate_ext3.rs 543-608 (evaluated even when the filter is zero), the output-count ensure,
  the fixed-width buffer write accumulated[slot]+=filter·value, and the reduction by forward alpha powers.
  An out-of-range write is `none` exactly as the source panics, and we do not claim that the totalized List.set is the source's behavior.
  From validateRows/validateConfiguration, proved that all writes are in range, that the slot-first result agrees with the actual combineRows/evalCombined, and
  that they have the same fixed polynomial (≤ q+1, ≤ q+2 after affine weights).
- **Grid transpose of current_round**: Models gate_ext3_v2.rs 105-134's numVars>0 ensure, half=len/2, the degree+1 cells initialized to zero,
  the mutable accumulation with suffix outer and integer inner, and the actual reads of (1−x)·t[2s]+x·t[2s+1] with the same slot evaluator, and proves that the
  iteration body equals the slice value of GateSuffixPolynomial, that the executed mutable loop equals the lockstep form, that the transpose loop equals the
  per-integer suffix-first sum currentRoundValue, that half = 2^(numVars−1) on a Valid eq table, and that under TableShape every cell is
  the value of a single polynomial (≤ q+2 ≤ 10). The interpolation call (136) and the degree-construction check (80-83) are separate.
- **Prover round of Norm/logUp**: Repaired and extended the candidate that previously failed to compile, on top of the adopted DenseMleIndexed/OuterInterpolationTotal.
  Models norm_logup.rs's line_value, evaluate_target_from_values (the width assert is `none`; two accumulations in a single loop,
  retaining the xi·ZERO term), round_sum_at (4 scratch vectors, the suffix loop, the shift/mask PI loop, sum+xi·binding),
  current_round (is_complete→Err, cache, samples of Field64_3::from(0..=5), the adopted interpolation, coefficients[1..]),
  bind (prefix update by the old bound_variables → +1 → bindBuffer over the whole table; num_vars=0 is `none`), and the prover state's
  Err/panic/Consistent/PrefixProvenance. Under Shape ∧ 0<remaining, proves roundSumAt = roundValue, that the 6 samples are
  samples of a degree-5 roundPolynomial, omitted constant = coeff 0 = the verifier's half-sum recovery, that the actual Verifier.evaluateRound recovers
  the round value from the endpoint-sum claim for the transmitted 5 coefficients, all read bounds, preservation of Shape after bind, and preservation of
  prefix = booleanRowEq(bound point). from_base's base → Ext3 transpose, eq_evals_ext3, weight provenance, a dishonest prover, round chaining, and PCS are not proved.

The 2 GateSlot candidates were, in an independent review by a separate party, criticized for the totalized slot write being more total than the source (required) and
for docstrings/line numbers; after fixes they PASSed re-review together with the new GateSlotRound.
NormDenseRound was, in the independent review after repair, criticized because 6 theorems premised only on Shape could reach Rust's panicking inputs when remaining=0 and
bindings is non-empty; it PASSed after adding 0<remaining as a premise.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2175 named actual theorems/types/transitive axioms, 424 reviewed hashes,
18 tables / 1147 words, and the 5601 files of the 7 dependencies. The source inventory maintains 31 partially corresponded / 259 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests, CI YAML, whitespace diff, and runtime-unchanged also PASS.
The implementation, main, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

For this state of 77 models / 2175 theorems as well, using the same temporary runner (SHA256
`9128f90b80becc4a43cae970567362887ce42da1970debad150e196fea0b46ed`), we regenerated all non-toolchain dependencies
from source into an empty new output location and checked all theorems using only that output.

- 1407 non-toolchain modules: audit/root 78, Mathlib 1091, Batteries 99, Aesop 108,
  Qq 11, ProofWidgets 18, ImportGraph 2. All regenerated from source into the new output location.
- Re-checked the `.thmInfo`, types, and transitive axioms of all 2175 theorems using only the fresh output. No errors,
  and only the 3 permitted standard axioms. Elapsed 1439.640 seconds (wall clock is not to be referenced because it includes host sleep during the run).
- At start and end, verified 424 reviewed hashes, the full source inventory, 18 tables / 1147 words,
  and the 5601 files / 64,398,270 bytes of the 7 dependencies, with agreement.
- Storage location `/private/tmp/wire3-fresh-source-build.kmfety_9/`. Receipt SHA256
  `3375f2b18dc8202529dc49c1339ccb78c615da78a80acddba15c1d409ad13714`, graph SHA256
  `2527787b924c4722988e0ad648814e3145e2a0b2968629fe4187f19d303979a7`. The manifest SHA256 at run time was
  `60b7a4a3879ea565bc3279dae8b80f8863ea3cbf6811e3b513a939a431ee933d`, and the only subsequent difference is
  the REPORT/manifest hashes accompanying the appending of this record.
- The trust boundary (fixed ProofWidgets JS, Lean toolchain/core, Python/Git, fixed metaprograms,
  a non-adversarial FS) and the point that the fresh PASS is not reinterpreted as implementation refinement / PCS soundness are the same as in the previous section.

## Continuation update #13 (after 71338df0)

Because a reboot lost the worktree, candidates, temporary runner, and fresh receipts in `/private/tmp`,
we recreated the worktree at `/Users/andropov/repos/intmax-plonky2-lean-wire3`, re-provisioned the 7 dependencies,
rebuilt the whole root, and confirmed that the ordinary guard PASSes (77 models / 2175 theorems / 424 hashes).
Commits `daa945d1` / `71338df0` remain in the submodule's object store and their contents are identical.

- **WHIR expected claims and whole-table evaluation**: OpenedClaimFold proves the row++index split of the adopted Packed.fold/packedFold/bindMany
  as an associativity law of the same function, and connects that the whole-table evaluation of pack_mles' column-major padded table equals
  the packed fold of each column's row opening, the correspondence of Solidity cells / Rust slots, and the reversal native point = dense point.
  Under the explicit honest-prover assumption that the 5 claimed cells equal the row fold of each column,
  each cell of expectedClaims agrees with the dense evaluation of the padded table at the WHIR point, and this also applies to the
  context at success of OuterAdapter.execute. The 6th cell is `none` and does not tie logNormInverse to the gate point.
  It has a concrete example where it does not agree with an incorrect cell, and does not claim PCS binding / WHIR acceptance / FS.
- **Re-implementation and tracking of the fresh source runner**: Re-implemented the lost temporary runner exactly as recorded in the REPORT and
  added it to tracking as `mle/audit/fresh-source-audit.py` (29 self-checks). Independent review confirmed that there is no
  contamination path from an existing `.lake/build`, no swallowing of failures, and no omission of pre/post guards, and we adopted the optional improvements suggested
  (making `lean --deps` mandatory, turning Lean panics into failures, excluding include_str inside comments,
  deriving the audit dir from `__file__`). The output location rejects `/private/tmp`, which disappears on reboot.

With the pre-adoption version of the re-implemented runner (SHA256 `0b7e3ad8b2b3f51bf2224dbf0e6d507fb73e5292940bf82ae5b56ca2a2bb0493`),
we re-checked the 77 models / 2175 theorems of commit `71338df0`, PASS (763.171 seconds).
We regenerated from source 1407 non-toolchain modules (audit/root 78, Mathlib 1091, Batteries 99, Aesop 108, Qq 11,
ProofWidgets 18, ImportGraph 2), and the axiom distribution agrees with the record of the lost old runner
(807/689/428/248/2/1). Manifest SHA256 at run time `9bca4717c0b7633cf18a325f71889b5b7ede95fefeacf129acc1ab018efe08ab`,
receipt `fd517c5fedbb09692667fa223cdb279bcdb2556134050f329637d3ca147de55e`, graph
`fa644927bfc7048f06cf083a1a0cc999a35cad3d80b5c4ab45a3a3b00944f1da`, storage location
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.g6r0xrb1/`.
The 78 models / 2214 theorems after adding OpenedClaimFold and a re-run with the tracked runner are carried over to the next record.

OpenedClaimFold had no required fixes in an independent read-only review by a separate party. The direct build under the adopted namespace and
all integrated guards PASS. We checked all 2214 named actual theorems/types/transitive axioms, 427 reviewed hashes (added 2 runner files),
18 tables / 1147 words, and the 5601 files of the 7 dependencies. The source inventory maintains 31 partially corresponded / 259 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests / 29 fresh-runner self-checks, CI YAML, whitespace diff, and
runtime-unchanged also PASS. The implementation, main, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

## Continuation update #14 (after 9e960c70)

With the tracked runner (SHA256 `56237ada14b4a29015199a6b3c9566d72bd3a175921cecb813f9f821fc4c744a`), we re-checked the
78 models / 2214 theorems of commit `9e960c70`, PASS (758.152 seconds). We regenerated from source 1408 non-toolchain modules (audit/root 79, Mathlib 1091,
Batteries 99, Aesop 108, Qq 11, ProofWidgets 18, ImportGraph 2), and the axioms of all theorems are
a subset of the 3 standard axioms (818/703/436/254/2/1). The manifest SHA256 at run time is the same as that commit's,
`f74472f78c43f5facdb42e474bd380055096c5d5599fc4430131ea0d592ac8ec`, receipt
`5542843f1d9ca96d2542a4077cd1eb877b628cd7162cd4840d70567f9792a2eb`, graph
`ce4e6ffd93eab565895f80cfa3942c1dccbb8b17e2fa86a5fcd548aa02f62d3f`, storage location
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.jvklnsxi/`.

- **Terminal connection of the gate prover**: GateTerminalBinding models bind_challenge (degree ensure → the adopted bind of eq / all wires / all constants
  → rounds/point push) and into_proof_and_point, and from ProverShape (constructor ensure 70-79) proves that
  after binding all variables each column is a single cell equal to the adopted packed fold, that the final round's eq·aggregate
  agrees with GatesComplete.evalCombined, and that under the explicit assumptions eq cell = eqEvaluation(gateTau, gatePoint), claimed cell = prover cell, and
  alpha = gateAlpha, it agrees with the acceptance formulas of Verifier.gateTerminal and Integrated.
  It also has an honest-prover-only theorem deriving the necessary metadata checks from the success of Integrated.verify.
  The tau provenance of the eq table, coefficient interpolation, transcript, and WHIR/PCS are not proved.
- **Terminal connection of the norm prover**: NormTerminalBinding explicitly maps the table after binding all variables to NormTerminalInput (constants++sigma,
  routed wire cells ++ the non-routed tail, identity/sigma helpers, PI values), and proves the term-by-term agreement of the prover's targetValue with the
  verifier-side Norm.evaluate/checkedEvaluate/Engine.logTerminal (cross-checking the lambda running product, powers of eta,
  PI eq_row, kappa/xi weights, and the order of the helper halves), that each bound cell = the adopted packed fold, bind success and
  a single cell per column, that the final round's roundValue = the terminal target of the bound table, and an end-to-end theorem for the honest prover.
  In independent review, the point that the witness was restricted to routed cells only with numWires = numRouted (required) was raised, and
  we fixed it by adding a non-routed tail while preserving all theorems, also adding a concrete example with numWires > numRouted.
  The tau provenance of the eq/subgroup cells, the provenance of lambda/eta/wire-map/kIs, shapeValid, and PCS claimed value = prover cell
  are visible assumptions.
- **Claim chain of the honest prover**: OuterClaimChain drives the adopted Verifier.roundStep/runRounds with the same commit arguments as the prover's
  currentRound → bindChallenge, and proves that the logClaim after each round = the roundValue of the immediately preceding table, that
  the next table's f'(0)+f'(1) = the previous table's roundValue(r) (the inter-round identity that NormDenseRound had left open, proving 2≤remaining and
  all read bounds), that an initial zero claim ⇔ zero endpoint sum, that intoProofAndPoint = the messages/challenges consumed by the verifier,
  agreement with derivedRounds/OuterAdapter.runChecked, and a concrete example with n=1. The gate lane is
  parameterized by explicit assumptions and no fake gate prover is placed. The soundness of arbitrary messages and FS are not claimed.

The 3 added models PASSed independent read-only review by a separate party (GateTerminalBinding only required fixes to cited line numbers,
NormTerminalBinding was re-reviewed after the required fix above, and OuterClaimChain had no required fixes).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2402 named actual theorems/types/transitive axioms, 430 reviewed hashes,
18 tables / 1147 words, and the 5601 files of the 7 dependencies. The source inventory maintains 31 partially corresponded / 259 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests / 29 fresh-runner self-checks, CI YAML, whitespace diff, and
runtime-unchanged also PASS. The implementation, main, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

## Continuation update #15 (after f9ada18b)

With the tracked runner we re-checked the 81 models / 2402 theorems of commit `f9ada18b`, PASS (771.879 seconds). We regenerated from source 1411 non-toolchain
modules (audit/root 82, Mathlib 1091, Batteries 99, Aesop 108, Qq 11, ProofWidgets 18, ImportGraph 2), and
the axiom distribution is 919/729/482/269/2/1. The manifest SHA256 at run time is the same as that commit's,
`5b772df15b2273893cde7e77841ebc41059d6b378ac68b5e6c80301fc4d3f113`, receipt
`39367c53af192fd1bcc648a4aeb1ca44a50194cbfad499e4a057f1ff0a0b01f7`, graph
`0ca3fba58ae89cd0a3526cb0933a0ad70bcf2e8e30c07ebeae1d6a68071e848f`, storage location
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.vvt12tjv/`.

- **Integration of the terminal chain**: IntegratedTerminalChain connects to Verifier.verify / Integrated.verify without re-implementing the
  4 adopted modules. Under a named assumption structure (honest norm prover, norm terminal provenance,
  gate chain assumptions, honest openings), it derives that the honest prover's logTerminal = the final logClaim of derivedRounds,
  gateTerminal = the final gateClaim, that the 5 WHIR expected claims = the dense evaluations of the padded table and the 6th is `none`, and
  by the reverse lemma of verify_success_checks shows acceptance of Verifier.verify / Integrated.verify. The remaining premises are enumerated as
  ObservationOnly (chain / config hash / envelope / deployment / shape / 4 lengths / verifyWhir / 7 challenges / normShape).
  Proved at the Prop level the acceptance equivalence of the Rust order (WHIR → norm) and the Solidity/Lean order.
  On the adopted Integer example (exampleEngine/Config/Proof), all assumption structures were satisfied from an actual honest-prover execution, and
  the existing positive path was re-derived via the connection. grid is an honest-prover assumption implying agreement of the endpoint sum of the gate running claim, and
  the tau provenance of the eq/subgroup cells, claimed value = prover cell, and PCS/WHIR soundness remain assumptions.

The 1 added model had no required fixes in an independent read-only review by a separate party (the implication of grid was added to the docstring).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2445 named actual theorems/types/transitive axioms, 431 reviewed hashes,
18 tables / 1147 words, and the 5601 files of the 7 dependencies. The source inventory maintains 31 partially corresponded / 259 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests / 29 fresh-runner self-checks, CI YAML, whitespace diff, and
runtime-unchanged also PASS. The implementation, main, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

## Continuation update #16 (after 03e69a20)

With the tracked runner we re-checked the 82 models / 2445 theorems of commit `03e69a20`, PASS (750.355 seconds). We regenerated from source 1412 non-toolchain
modules (audit/root 83, Mathlib 1091, Batteries 99, Aesop 108, Qq 11, ProofWidgets 18, ImportGraph 2), and
the axiom distribution is 936/735/490/281/2/1. The manifest SHA256 at run time is the same as that commit's,
`ccafd4b71c310c4f7491662044aa4fb073da8df9048517dc79b6341554bd4fa5`, receipt
`81e79f8c8a8e3dfe3c959e6340bf5b233bb8fb5581cd7172ced0adac2592c548`, graph
`501e10c44cc9dfe8ad9e941a6545b2c9286e597a7bc2c7d1ceb8f9a5c2c52d71`, storage location
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.jso0ljtj/`.

- **Provenance of the eq/subgroup tables**: EqTableProvenance models the loop nest of the actual eq table builder (outer loop in tau order, inner loop over index,
  left-side accumulation, factor selection by (i>>j)&1), and proves that each entry equals the adopted Norm.booleanRowEq, and that
  from the 2i/2i+1 pairing of the adopted bindBuffer the low-order bit is bound first. After binding all points,
  the eq cell equals Norm.eqEvaluation(tau, point). The subgroup column is a geometric sequence, and since the verifier does not fold it but
  takes the product of (1-r_j)+r_j·g^(2^j), we proved the exact relation that this product equals the cell after full binding / Packed.fold.
  This yields, from the main theorems of NormTerminalBinding/GateTerminalBinding, corollaries (including honest-prover versions) that remove
  the previously visible assumptions on the provenance of the eq cell / subgroup cell.
  That the VK's subgroup_gen_powers are repeated squarings of the table's generator was not resolved and remains a visible assumption, written only as a predicate,
  because the adopted models have no model of two_adic_subgroup and of the VK generator derivation.

The 1 added model had no defects on the Lean side in an independent read-only review by a separate party. We applied the 2 required documentation fixes raised
(the 3 eq builders are not byte-identical but the same loop nest / eq_poly.rs is the old path, and the real reason the subgroup assumption cannot be resolved)
and restored the PrefixAt conjunct that had been dropped from the conclusion of the corollary.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2500 named actual theorems/types/transitive axioms, 432 reviewed hashes,
18 tables / 1147 words, and the 5601 files of the 7 dependencies. The source inventory maintains 31 partially corresponded / 259 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests / 29 fresh-runner self-checks, CI YAML, whitespace diff, and
runtime-unchanged also PASS. The implementation, main, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

## Continuation update #17 (after c3719e61)

With the tracked runner we re-checked the 83 models / 2500 theorems of commit `c3719e61`, PASS (727.034 seconds). We regenerated from source 1413 non-toolchain
modules, and the axiom distribution is 971/744/500/282/2/1. The manifest SHA256 at run time is the same as that
commit's, `cc7b67fbcf0b2969aa2099146ee36acb9627e0e4db33797b8f31d489b8823ea5`, receipt
`05760f64b72b2529ef93bea6b4df3a45cbe19fbee45dea19b0a1255707bae119`, graph
`24ced6ff907622b015cc3dee2b1ccc175a05e5555090da8c37696d125f4c83ba`, storage location
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.5imen0_t/`.

- **Concretization of the public input hash**: PublicInputHashBinding constructs the actual hash-no-pad sponge on top of the adopted Poseidon permutation,
  and cross-checks the absorb order, overwrite mode, chunk count, short final chunk, 4-element digest, and zero permutations for empty input against the implementation.
  Proved layer by layer that over the Ext3 model c1=c2=0 is maintained across all 30 rounds and that
  the c0 readout is lossless (agreement with the adopted zeroInputWitness is by rfl,
  and the zero-input row of an external test vector is also reproduced). We newly modeled the preflight of raw public inputs (256-word cap, each word < p,
  no silent reduction on rejection). This yields a corollary that removes the
  hash-length assumption from the gate terminal theorem and fills in the hashLength field of GateChainHypotheses.
  The Solidity/Rust differences (Rust needs no range check since it is canonical by type; the 256-word cap is Solidity-only;
  since the hash reads calldata, `PoseidonGate.sol:77` guards the external library entry point, and within verify it is
  defense in depth) are stated in the header.

The 1 added model had no defects on the Lean side in an independent read-only review by a separate party. We applied the 2 required fixes raised
(an accurate rephrasing of the calldata read, and the cited line numbers of the adopted Lean/Solidity).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2579 named actual theorems/types/transitive axioms, 433 reviewed hashes,
18 tables / 1147 words, and the 5601 files of the 7 dependencies. The source inventory maintains 31 partially corresponded / 259 uncorresponded out of 290 files.
The 33 guard / 34 dependency / 20 provision tests / 29 fresh-runner self-checks, CI YAML, whitespace diff, and
runtime-unchanged also PASS. The implementation, main, and parent pin are not modified, and this is not treated as completion of the whole implementation/PCS soundness.

### Addendum to continuation update #17 (after 3d5880ed)

- **Resolution of the transcript provenance**: TranscriptProvenance proves, from the single premise DerivedInitial (the engine's initial transcript is
  the actual derivation itself; identical to the assumption the adopted OuterAdapter already takes, and rfl under withInitial), that
  challengesFromInitial returns the 7 derived challenges, that the log/gate tau sequences and the gate alpha are derived values, and
  that each challenge lands at the source's digest/counter position. ObservationOnly goes from 12 items to 9, and
  NormTerminalProvenance/GateChainHypotheses/NormColumnProvenance each lose 1 item as well.
  Since no property of the hash is used at all, this is identity of ordering and hand-off, not Fiat-Shamir soundness.
  We applied the 2 required fixes of the independent review (that the gate hpt is an equivalent rephrasing rather than a resolution,
  and that the honest-prover display is 5 items, not 6). DerivedInitial itself and agreement with the prover-side challenges remain.

### Addendum 2 to continuation update #17 (after 5dd688a6)

With the tracked runner we re-checked the 85 models / 2617 theorems of commit `5dd688a6`, PASS (873.732 seconds, 1415 modules,
manifest `ce2c6d30aa01e8b12716bd0eee1ad4e7940a4f2b7d08d637fe2848104683a802`, receipt
`ef28bde84e33e38daafa476a610f7f1da76741b75300ae807bada83787657f40`).

- **Resolution of the VK generator provenance**: VkSubgroupProvenance models plonky2's two_adic_subgroup and the VK generator derivation,
  and after establishing that the fixed two-adic generator has order 2^32 from a power certificate the kernel actually evaluated,
  proves in both directions that the recomputation check of verifier_v2.rs 130-147 is equivalent to "the VK's powers are repeated squarings of the derived generator".
  As a result, SubgroupPowersProvenance, which an earlier review had recorded as "unresolvable in the adopted models", became a theorem rather than an assumption.
  Since the adopted GoldilocksDomain's generator 7 is a different value from plonky2's two-adic generator, its order is proved independently here.
  The remaining assumptions are the agreement of degreeBits with the variable width, and the provenance of the prover-side subgroup column — both visible fields.
  The independent review had no required fixes. Following its suggestions, we noted that, since the source panics for n_log>32 while Lean's truncated subtraction
  accepts it, the iff is faithful for degreeBits ≤ 32 (unreachable, since the envelope forces degreeBits ≤ 13), and added the cited line numbers.

### Addendum 3 to continuation update #17 (after 1c2bc096)

With the tracked runner we re-checked the 86 models / 2688 theorems of commit `1c2bc096`, PASS (858.808 seconds, 1416 modules,
manifest `d89e078087f53f5d3b8c6c3bec9b70cc5f485585b9f3fe304c2b86b85ed9a839`, receipt
`5d41b90d3490e861906f854f552b6183a544fef60884965523faf04a4a8fb3c8`).

- **Conditional soundness under explicit cryptographic assumptions**: ConditionalSoundness enumerates 18 assumptions as visible fields,
  and derives that if Integrated.verify accepts and no bad event of the log lane has occurred, then the extracted table's
  endpointSum is 0. This is the proposition that IntegratedTerminalChain assumed as zeroSum, and it is derived without circularity after confirming that
  none of the fields mentions endpointSum as a value.
  The shape of the theorem is "endpointSum = 0, or at some round the drawn challenge fell into the bad set", and
  this is the correct shape of sumcheck soundness. The bad-set cardinality upper bound 195·⌈2^256/p⌉³ obtains 195 from
  degreeBits ≤ 13 and quotientDegree+2 ≤ 10 derived from acceptance; it is not an assumption.

  **We state explicitly what this theorem does not prove.** The gate lane is not proved. The first draft also concluded the
  cube sum on the gate side, but adversarial review revealed that with gateTruths := [] the assumption holds for any accepted proof, making it a degenerate
  conjunction; so after confirming that the adopted gate prover has none of coefficient interpolation, Boolean cube sum,
  round chaining, or eq-table provenance, it was deleted.
  195·(⌈2^256/p⌉/2^256)³ ≈ 2^-184 is a value counting only the agreement event of the outer sumcheck, and
  does not include the dominant WHIR/Merkle terms. Since the design point is about 100 bits, citing this number as the system's
  soundness error would overstate it by about 80 bits. failure is a free rational and only an upper bound is given, and
  no field supplies a bridge to the actual probability. The first and fourth conjuncts are not composed, and
  a probability space concerning execution does not exist in this file. The satisfiability of the Assumptions as a whole is also not shown.
  The seam between extraction and commitment (terminal claimed value = prover cell) remains an assumption.

  It went through two adversarial independent reviews. The first raised the above degenerate connective, vacuity due to 2 unused assumptions and free variables,
  a final-round bridge that remains at the scalar level, exaggeration of satisfiability, and the risk of misquoting the numbers, and
  all were fixed (deleted the gate conjunct and 2 assumptions, structured the final-round bridge to derive a value equality,
  retitled §12 as a partial non-vacuity check, and put warnings in 3 places). Re-review confirmed the effectiveness of the fixes, and
  the remaining 4 exaggerated expressions (such as wording that could be read as failure bounding the actual probability from above) were also fixed.

### Addendum 4 to continuation update #17 (after 746ed942)

With the tracked runner we re-checked the 87 models / 2742 theorems of commit `746ed942`, PASS (801.944 seconds, 1417 modules,
manifest `bbc6dd9d869a7cb4ec7eba545f3dcac20a9a1e5e0acbfa4a761033a62a82febe`, receipt
`6b2b46bae6e8bffe40a5c4417ad0deb151d1104033d0b09d9b288c46b01a8b97`).

- **Round model on the gate side**: GateDenseRound, as the gate version of NormDenseRound, models current_round to the end with the adopted
  grid and the adopted interpolation (no re-implementation), and proves that the length of the transmitted message agrees with the re-check value of bind_challenge,
  that the omitted constant coefficient agrees with the verifier's half-sum recovery, and that the actual Verifier.evaluateRound reproduces
  the round value. We also proved the Consistent invariant and the inter-round endpoint identity, as well as the Boolean cube sum
  defined at a single index and its endpoint-sum agreement at the first round. Multi-round induction has not been carried out, and
  cube sum = 0 is not claimed (that is circuit truth). This resolved 3 of the 4 gate obstacles listed by the capstone.
  The remaining 5 points (multi-round induction, orientation, extraction/transcript, terminal bridge, and the distinction between the weighted sum and
  each constraint) are enumerated in SCOPE.
- **Binding of openings**: OpeningBinding reduces the fact that two accepted openings with the same root/index/depth return the same raw row,
  decoded values, and dot, solely to the injectivity of the hash on a finite list computed from the execution.
  This predicate is not a free variable but is computed from the results of the calls, and the Merkle cursor is also fixed by an adopted theorem.
  Assumption 17 is rewritten as a biconditional, but the residue is at the fold level and is weaker than identification of the column.
  Furthermore, we proved the limitation itself as a theorem. The WHIR check of the opaque engine accepts any context, and
  the opening relation holds even if the 3 roots are replaced. Therefore extraction cannot be derived from binding.

The 2 added models both went through adversarial independent review. GateDenseRound had no required fixes (2 documentation items applied),
and OpeningBinding had 2 required fixes applied (having written the fold-level residue as identification of the column, and
overstating the mathematical content of the biconditional), and we also stated the previously unrecorded gap that the decoded row and p.used are unconnected.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2834 named actual theorems/types/transitive axioms,
438 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

### Addendum 5 to continuation update #17 (after 118caab2)

With the tracked runner we re-checked the 89 models / 2834 theorems of commit `118caab2`, PASS (1427.517 seconds, 1419 modules,
manifest `17a71c4a1c340b182a88bd184c5f8dc5f862d9944131d6e4c5ef28554aa23ea4`, receipt
`63cb1cc80dd9b9d25ee32b3429e9c5d66724579c1886940d7362f5366ee42ec5`).

- **Semantic stage**: ZeroCheckSemantics shows that the multilinear extension by the adopted eq interpolates g on the cube, that
  if there is a non-zero value the extension is not identically zero, and that the density of zeros is at most n/|F|
  (Schwartz-Zippel, total degree ≤ n, the induction is completed with no assumption stage, and the n=0 edge is also proved).
  It gives a corollary that for tau outside the bad set each row value of GateDenseRound becomes 0, under the adopted derived tau and
  the eq assumption that EqTableProvenance resolves.
  It is not composed with the adopted badSets (a single challenge versus an n-tuple).
- **Chaining of the gate lane and the reversal of orientation**: GateClaimChain chains the gate lane over multiple rounds with the actual Verifier.roundStep,
  derives the gate row count, hash length, and validateConfiguration from acceptance to cross the terminal bridge, and
  derives from acceptance and the absence of a gate-lane bad event that the cube sum of the extracted table = 0. It reuses the adopted bad-event machinery and
  does not create a duplicate definition. It also re-concretizes the gate-lane-specific upper bound (q+2)·degreeBits
  (stating explicitly that ConditionalSoundness's 195 does not apply to this lane).
  We showed by theorem that `gateTruths := []`, which previously degenerated the gate conjunct, is unsatisfiable because the truth chain is bound to the execution.

  **Limitations that should be honestly recorded**: this theorem still has no rejection power against an adversarial supplier.
  The assumption fixes only one linear functional of the eq table, and since the row sums of the cube weights are independent, one can choose an eq table
  that has the correct bound cells while having row sum 0. A degeneracy of the same kind is `numGateConstraints=0`
  (the envelope imposes no lower bound, and the adopted example config sets this), which
  the review discovered; we proved it as a theorem and then excluded it via visible assumption 4. This is not exhaustive, and
  a path that zeroes out all selector filters also remains. These are stated in the header and the body.

The 2 added models both went through adversarial independent review. ZeroCheckSemantics had no required fixes (3 documentation items applied,
including correction of the error of composing with badSets). GateClaimChain had 4 required fixes applied
(removal of overstatement, re-concretization of the upper bound, proof of the degeneracy and its exclusion by a visible assumption, and stating the absence of rejection power),
and after re-confirmation in a verification review we also corrected wording that could be read as there being only 2 degeneracies.
At this time the gate-lane description of the adopted ConditionalSoundness had become stale, so only the comment was updated.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 2923 named actual theorems/types/transitive axioms,
440 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

### Addendum 6 to continuation update #17 (after c89d8ea7)

With the tracked runner we re-checked the 91 models / 2923 theorems of commit `c89d8ea7`, PASS (1129.262 seconds, 1421 modules,
manifest `2470b854fbca0265d5e3acea62c4cd915f4bb6cdf77aec7c68253ea4c28a5d06`, receipt
`bbcebcc6d799c6b14e1fac5184299e46855dbf9a1f8db136b9b91d19c86ec97f`).

Under the policy of "identify scenarios where soundness is problematic, and prove soundness in the process of showing that they are not the case", 2 modules were added.

- **Enumeration of attack scenarios and rejection power**: GateRejectionPower enumerates attack scenarios as definitions and shows by theorem that each of them
  actually exists. In particular, we proved that zeroing the eq column makes the adopted conclusion hold for any table while
  the gateValue of each row is unchanged (a formal proof that the old theorem was rejecting nothing).
  On top of that, we proved the unit decomposition of the adopted eq (the row sum on the cube is identically 1), and derived that if the eq column is fixed across all rows,
  an eq table with row sum zero cannot exist. Under a strengthened assumption, we showed by composing with ZeroCheckSemantics that the aggregate of each row is 0,
  stated by contraposition that there is rejection power, and gave concrete examples of 2 forged states that the old assumption accepted and
  the new assumption rejects.
- **Zero-check of alpha**: AlphaZeroCheck treats the row aggregate as a polynomial in alpha and identifies its coefficients as the adopted slot values
  themselves (not merely a degree upper bound). It derives the root-count upper bound as ≤122 from the envelope-derived
  numGateConstraints ≤ 123, and shows that for alpha outside the bad set each slot value is 0 and that for gates whose filter is non-zero
  the constraint itself is 0. We proved the composition of the zero-checks in both tau and alpha for the adopted transcript's alpha and tau
  (alpha is drawn at a counter earlier than the gate tau).

  **Attack surfaces stated as unresolved**: partial zeroing of selectors (total zeroing is excluded by activeFilter, but
  an attack that zeroes only important rows while leaving gates elsewhere remains. This is the provenance of the constants column, i.e. the problem of the extraction seam).
  Since tau is a free variable in both modules and is not bound to the transcript, an adaptive attack that chooses tau after fixing the
  table is excluded only by the hgood assumption. The probability is not computed, and since alpha's bad set is per row,
  a union bound over 2^n rows is needed for the whole cube.

The 2 added modules both went through adversarial independent review. AlphaZeroCheck had no required fixes (4 recommendations applied).
GateRejectionPower had 1 required fix (tau had been written as "drawn", but it is a free variable) and
a correction of the scope of selector forgery (the exhibited state is excluded by activeFilter, and what remains is partial zeroing) applied.
At adoption we discovered that `?` and trailing primes in theorem names collide with the identifier regular expression of the adopted guard, and
renamed 2 of them (the guard misreads `get?_append_cons` as `get`, and misidentifies `x'` and `x` as duplicates).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3021 named actual theorems/types/transitive axioms,
442 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #18 (after f5424f98)

With the tracked runner we re-checked the 93 models / 3021 theorems of commit `f5424f98`, PASS (1279.663 seconds, 1423 modules,
manifest `83a68fcedb8deb2ad9cb2c4568c5525defeb649b41b2b60fe7d55ccb32cebdf5`, receipt
`3a48e1165b0466016fe20a3cbadc0ac60618e9a6e6f5172579df67f198f8ab2a`, graph
`e43331323b2d7e39d37198ba817c5663fa8dc489117bfa98947d816a64d16114`).

From this update we moved to the loop method. Fable 5.1 handles planning and result verification, Opus 5 handles implementation, and
each candidate goes through an independent adversarial review before adoption. This round targeted two points: the room to
"choose the challenge after fixing the table", and the bridge to a probabilistic reading.

- **Transcript binding of challenges**: GateDerivedRejection restates the rejection theorem and the composition theorem with the transcript-derived
  gate tau/alpha, and derives the bound-cell assumption from whole-table eq provenance and a structural binding field, giving a reduced assumption set of 9 fields
  containing no free challenge values. §2 is an exception and retains a free alpha.
  The remaining challenge-side assumptions are 3: the two hgoods concerning the derived tau/alpha, and the adopted BadEventFree of the sumcheck round.
- **The deterministic half of adaptivity**: CommitmentOrder proves, by cross-checking with the implementation, that the prefix before the squeeze of gate alpha/tau consists of 22 frames and
  agrees with the adopted relationState, that the 3 roots are the 13th/15th/19th, and that between the final root and the squeeze there are only 2 fixed domain tags.
  The gate's bad set does not depend on the eq column, and to change the table while preserving the
  prefix digest requires a concrete transcript collision (collision resistance is not assumed).
  The probabilistic half is negated by a counterexample with a constant hash, and remains as a hash assumption not obtainable by an ordering argument.
- **union bound**: ChallengeUnionBound lifts tau's bad set to a product event of n independent digest triples, alpha's per-row bad set to a union over 2^n rows, and
  together with the outer sumcheck term bounds the sum of the three masses.
  It expands to an equality at the envelope extremes, and proved ≤2^-172 by exact rational computation.
  **This number does not include the WHIR/Merkle terms and is not the system's soundness error**. By independent recomputation the total is 2^-172.07, and
  the margin is about 0.07 bits, right at the edge of the envelope. The 3 terms are a sum of masses on separate sample spaces, and
  the joint event is not formalized. The parameters of the product event and the row union are not bound to the table of an accepting execution.

The 3 added models all went through adversarial verification on the Fable side. GateDerivedRejection had 3 required wording fixes
(§2's free alpha, the overstatement "there are only 2 challenge assumptions", and the point that the binding field contains an equality of the challenge sequence),
CommitmentOrder had 2 tightenings, and ChallengeUnionBound had 3 required fixes applied (the incorrect expression "mass of a disjunction",
making free parameters explicit, and quantification of the margin).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3129 named actual theorems/types/transitive axioms,
445 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #19 (after d937d15f)

With the tracked runner we re-checked the 96 models / 3129 theorems of commit `d937d15f`, PASS (1483.923 seconds, 1426 modules,
manifest `29d29f182cbcda02a269ec76b782b0252aac9744c7b67211563f9d527c7bfb06`, receipt
`0af02e6adc74c31dc52405ac55438683bc354b2010e595277abda0f2bbb5bc71`, graph
`74a4b58940642560ced5a047d92f700d61ee3e440bfa73a46272d330a02ccac7`).

The second round of the loop method. It targeted the 3 points left from last time: "free parameters of the union bound", "provenance of selector partial zeroing",
and "the 3 terms are on separate sample spaces".

- **Binding to an accepting execution**: AttachedUnionBound binds ChallengeUnionBound's free parameters (n, g, the coefficient family) to
  an accepting execution. The tau arity is derived from degreeBits, the row value is gateValue, the coefficient family is the acceptance-derived
  slotCoefficients, and the constraint count ≤ 123 is derived from acceptance, and it shows that the attached tuple is the transcript's derived tau sequence itself
  (attached_tau_tuple_ofFn). combinedBound is monotone in all 4 arguments
  (⌈2^256/p⌉·p ≥ 2^256), and under the envelope ≤ combinedBound 13 8 13 123 ≤ 2^-172. attached_seam combines into one theorem
  the counting upper bound and "if the derived tau/alpha are outside the attached bad set then the constraints of the selected gate vanish on all rows".
  **The numbers do not include the WHIR/Merkle terms and are not the system's soundness error**. The margin of about 0.07 bits holds up to constraint count 128,
  and only breaks at 129 (the old description "125" in SCOPE was an error and has been corrected. The envelope caps at 123).
- **Provenance chain of selector partial zeroing**: ConstantsProvenance proves the 6 links selector value ← supplied constants column ← bound cell at the derived gate point
  ← gatePreprocessed claim ← bound cell of the committed column ← opening under the preprocessed root ←
  deployment pin, starting from the pin (Verifier.shape, verifier_v2.rs 184-187, MleVerifierV2.sol 563).
  The attack theorem partial_zeroing_forces_one_of_three shows that if the bound cells of the supplied column and the pinned column differ
  at the derived gate point, then necessarily one of the following occurs: a root mismatch (closed by the pin), a violation of the extraction seam CellsMatchClaims, or a violation of the opening relation
  OpensCommittedTable; and with a concrete forgery example it shows that the old assumption does not detect it while the new chain catches it at the seam. The residues are "bound-cell agreement is weaker than column identification" (with a counterexample),
  engine opacity R1, the opening relation R2, and the root → column map R3, all of which remain visible assumptions. To exclude a column modification
  invisible at the derived gate point requires a zero-check by a sumcheck challenge, which has not been started.
- **Formalization of the joint event**: JointChallengeSpace places the 3 masses on a single sample space. It defines a uniform counting measure on
  `Draw d → DigestTriple` indexed by the squeeze schedule (gate alpha, gate tau × d, outer log/gate round × d, for a total of 3d+1 coordinates),
  proves by counting the masses of the coordinate events and the tau product event, and proves that the mass of the true disjunction event
  ≤ combinedBound (the outer term covers the 2d coordinates of both lanes). 2^-173 ≤ bound 13 8 13 123 ≤ 2^-172.
  The seam `DrawEncodesRun` is not a hash assumption but a claim about coordinate encoding, and we show as a lemma that it is inhabited for all hashes and all accepting executions.
  The Fiat–Shamir half (B), "the encoded draw is distributed as jointProbability", remains unformalized, and
  the composition theorem composed_gate_constraints_vanish_on_the_joint_space carries no cryptographic assumption at all. The outer bad set is
  relative to the realized challenges/messages and is not a prefix constant. **The numbers do not include the WHIR/Merkle terms and are not the system's soundness error**.

The 3 added models all went through adversarial verification on the Fable side. AttachedUnionBound had a required fix (the misstatement "breaks at 125"
→ 129, with the same description in SCOPE also corrected), ConstantsProvenance had 3 wording items (enumeration of the residues, the old theorem's
"true" → "the conclusion holds", and that verifyCall also checks shape), and JointChallengeSpace had 3 required fixes (that the seam originally named
`TranscriptIsUniform` is not a hash assumption but is inhabited for all hashes, the error of calling the outer bad set
a "prefix constant", and overstatement of the probabilistic reading of the composition theorem) and 5 notes (renaming of the composition theorem, binding of the log lane
comparison value, the expression of the margin, the character of the schedule map, and maxHeartbeats in 2 places) applied. No soundness defects were
detected in any of the 3 models.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3268 named actual theorems/types/transitive axioms,
448 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #20 (after 15d2ee8f)

With the tracked runner we re-checked the 99 models / 3268 theorems of commit `15d2ee8f`, PASS (790.780 seconds, 1429 modules,
manifest `6aab14eb581a8fd56c27e41423d6504bba7e98c6c83a6430c0dd4cbf1de4056a`, receipt
`0aeac5a0e2ac6914bf9f4866f3eb8ab99a3aedd7a6eb833233372048d41a88e3`, graph
`07321f04a0fc2f950c3217445b4eeebb740ae441fed24be1e8dd4f12a53708e3`).

The third round of the loop method. It targeted the 2 points left from last time: "bound-cell agreement is weaker than column identification" and "the outer bad set is not a prefix constant".

- **Zero-check on the gate point**: GatePointZeroCheck closes ConstantsProvenance's residue with Schwartz–Zippel on the derived gate point.
  The bridge between the bound cell and the multilinear extension holds under 2^|point| ≤ |col| (for short columns we proved a counterexample where
  bindColumn's truncation and the extension's zero padding disagree), and the agreement set of 2 columns is the zero set of the difference column with
  density ≤ n/|F| and uniform mass ≤ tauTerm. The composition theorem shows that if the columns differ and the derived gate point is outside the agreement set, then under acceptance either the extraction seam or
  the opening relation is violated. In review it turned out that the bridge assumption needs only an inequality rather than an equality, that the width assumption for the committed column
  can be derived from the opening relation, and that the width of the supplied column is fixed by the adopted Consistent + EqCellBinding,
  so all width assumptions were dropped. We proved in an abstract engine that the gate point sequence is the round-challenge sequence of the gate lane, and
  obtained mass ≤ tauTerm d as the 4th family (outerGate coordinates) of JointChallengeSpace. The residues are: that the supplied column is not bound to the root
  other than by the 2 branches of the conclusion (density is meaningful only under the reading where col is fixed before the point), that the round digest chain is
  documented only for the concrete engine, R1–R3, and half (B).
- **Sequential conditioning**: OuterSequentialConditioning handles the adaptivity of the outer coordinates. With a general engine over a finite product space
  (a Nodup coordinate sequence, a PrefixDependent family of bad sets, Fubini peeling) it proves mass ≤ Σ c_k/|A|, and concretizes it to both lanes with a `Lane` that makes the round message
  a function of the preceding challenges. The traversal order is log → gate per round, exactly as in the implementation (both challenges come from
  counters 0/3 of the same round digest, and both messages are fixed by a single commit. The model's adversary is stronger than the real one = on the safe side).
  The mass of the adaptive outer event is ≤ outerTerm, the same number as the prefix-frozen version, the adaptive joint bad event is ≤ combinedBound, and the frozen
  laneEvent is a special case of the engine, re-deriving the adopted joint_union_bound with the same type. In review, `ownsNext`
  (formerly `active`) being a phase bit of the alternating traversal, and the gate lane's bad set appearing at all gate coordinates, were confirmed by expanding at d=1.
  The Lane-level frozen comparison requires DrawEncodesRun and is not proved. The law is still the ideal uniform distribution, half (B) is
  unformalized, and **it does not include the WHIR/Merkle terms and is not the system's soundness error**.

The 2 added models both went through adversarial verification on the Fable side. GatePointZeroCheck had 3 required fixes (turning the bridge assumption into
an inequality, removal of the committed-column width assumption and derivation of the supplied-column width from an adopted assumption, and overstatement in the half (A) paragraph), and
OuterSequentialConditioning had 3 documentation fixes (`active` → `ownsNext` and the explanation of the phase bit, that the frozen family is not a Lane but
an instance of the engine, and a misstatement of the message order) applied. No soundness defects were detected in either model.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3390 named actual theorems/types/transitive axioms,
450 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #21 (after 1f3ffbf1)

With the tracked runner we re-checked the 101 models / 3390 theorems of commit `1f3ffbf1`, PASS (799.855 seconds, 1431 modules,
manifest `1a3f5013728838f9d1e4a087ed58dedff2f0143e4611f6d44c1319e8f90422dd`, receipt
`5498858df20a074cfe5ad952d763ede2638a1ff82e7dfb58669f6b66bb41b1e4`, graph
`d1e15da16349989dca5ba0f1e273caf6f8769fcd52c6fc3a74505a7cd86a7cd5`).
The fourth round of the loop method. It targeted residue R1 (engine opacity), the formalization of the reading "the supplied column is fixed before the point" left from iteration 3, and
the Lane-level frozen comparison that OuterSequentialConditioning left unproved.

- **Engine opacity**: InstalledWhirTail installs the adopted manual WHIR tail model `WhirConfigured.run` into
  Integrated.modelEngine's `whirTail`. It derives from acceptance the success of the concrete tail execution and the agreement of the 3 roots, that the initial evaluation value is
  the packed fold of the bound cell, that in the deployment profile (numRounds ≥ 1) the 3 roots are opened at intermediate round 1 and each row is Merkle-authenticated, and
  that rows with the same root and same leaf in 2 accepting executions either agree or collide.
  Review went two rounds. The first pointed out the error of "treating numRounds=0 as the production path" (all fixtures have numRounds ≥ 1), a defect where the R1b predicate was
  inhabited independently of WHIR, and that `wp` is free; we added the round-1 path theorems and reformulated R1b with respect to the execution result.
  The second pointed out a defect where the reformulated `extract` ignores the commitment root and forces cell agreement between different commitments
  (false even for an honest execution); we added a root argument and a root-agreement assumption.
  Since R1b in per-column form subsumes R3, a fold-level variant is also given. R2 is unchanged.
- **Adaptive supplied columns**: AdaptiveAgreementFamily decomposes GatePointZeroCheck's agreement set into per-coordinate
  Schwartz–Zippel and places it on OuterSequentialConditioning's adaptive engine, obtaining mass ≤ tauTerm d for a supplied column that is a function of only the first `cut` coordinates, and a joint bad event including the 5th family ≤ combinedBound + tauTerm d (≤2^-171 at the envelope extremes).
  The Lane-level frozen comparison was also proved as a two-way equivalence per lane under DrawEncodesRun, closing OSC's unproved item.
  Review showed by constructing a counterexample that the heading "adaptively chosen columns are also covered" is an overstatement. A forger can, from seeing
  only 1 coordinate, construct a column making the residue identically zero (of the form cc+(x0 / −(1−x0))), and then the 5th family is empty. Therefore what is
  closed is a dichotomy (identically zero on the slice = the residue class of R2/R3, or mass ≤ tauTerm); we revised the heading,
  added the escape construction as a formal residue witness, and also turned the empty event at cut=d and the fixed-column agreement at cut=0 into theorems.

The 2 added models both went through adversarial verification on the Fable side (InstalledWhirTail in 2 rounds, 8 required fixes in total;
AdaptiveAgreementFamily in 1 round, 1 required fix plus notes). No soundness defects were detected in either model, and the points raised
all concerned the coverage scope, inhabitedness, and accuracy of headings.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3508 named actual theorems/types/transitive axioms,
452 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #22 (after 70eed7fa)

With the tracked runner we re-checked the 103 models / 3508 theorems of commit `70eed7fa`, PASS (809.497 seconds, 1433 modules,
manifest `66894f315b3846e4e86e18d511eea0586f4afce43148cc45570893637df092d5`, receipt
`dcbd788f0e98ee3e9e43aebf33ec4cdb1336e52ab09e1034f783595bec8cafbc`, graph
`8ce127fc76aa71e44913d54c1fb756e15a14df9f2d6485924970cff743b813cf`).
The fifth round of the loop method. It targeted the 2 points left by InstalledWhirTail: "`wp` is free" and "the sampler of the index point is an observation".

- **Pinning of the WHIR profile**: PinnedWhirProfile installs the 4 constraints of `CanonicalWhirProfileV2.validateCanonical` as a
  concretization of `deploymentValid`, and derives from acceptance the canonicity of the decoded wp and the agreement of the tail execution record.
  Since the source does not syntactically enforce `inDomainSamples>0`, positivity and numRounds ≥ 1 are derived only for the 2
  transcribed rows (n=10, n=21) under the semantic assumption of the table, and the hsamples/hrounds of the round-1 authentication theorem were removed. Review
  confirmed the faithfulness of the 4 constraints and the keccak recomputation agreement of the 2 rows, and made us correct the erroneous
  design rationale "whirTail cannot access the config" (in fact ctx.parameters = c.whirEncoding) and the overstatement "deployment dimension".
- **Concretization of the index point sampler**: InstalledIndexSampler totalizes the adopted checked sampler over decode and
  installs it into the installed engine, proving that the prefix before the index squeeze is round state ++ claim frames (6 frames, counter 3i /
  3·indexBits+3i), that agreement of the index digest forces agreement of the used claims or a concrete collision, and that the lengths of both lanes
  are indexBits, thereby turning "the index is drawn after the cells" (the ordering aspect of R3) into a theorem.
  The probabilistic stage (a forged cell family failing at a fresh index point) remains unproved. Review confirmed source faithfulness, and
  made us add a proof that the decode assumption is inhabited in execution (under the adopted CommitAgrees, and also on fixtures), and
  state that the block numbers on the schedule are merely labels.

The 2 added models both went through adversarial verification on the Fable side (the required fixes were all documentation and the addition of inhabitedness lemmas, and
no soundness defects were detected).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3575 named actual theorems/types/transitive axioms,
454 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #23 (after bdfa02e2)

With the tracked runner we re-checked the 105 models / 3575 theorems of commit `bdfa02e2`, PASS (808.547 seconds, 1435 modules,
manifest `a9e492060bd42f74a1b51d81f2edf3f61c6ab5d56964b9ad821890db757313f6`, receipt
`d9e26bb39f4f278c246f82575e3d86b62640a97ab4524786e34e193e8f227f3b`, graph
`ce026c0feebded75d5819c5b84bb3d623459f3348a94d265495b702d74804af8`).
The sixth round of the loop method. Among the observations remaining in the engine, it targeted the initial transcript / public input hash and the round commit.

- **Installation of the initial transcript**: InstalledInitialTranscript places `OuterInitial.derive` and
  `hashNoPad` on top of the sampler engine, giving a single engine in which 8 fields are simultaneously concretized. Since `DerivedInitial` itself was already
  given by the adopted `withInitial_derived` by rfl, the novelty lies in the composition (review corrected an overstated novelty claim), and
  in this engine the 36 downstream occurrences of `hderiv` and PublicInputHashBinding's `hsub` become unconditional. We restated the main theorems
  without `hderiv`, and showed that the prefix consists of CommitmentOrder's 22 frames with respect to the engine's own transcript.
  We also turned into a theorem that the public inputs of an accepted proof satisfy Solidity's cap and word checks.
- **Installation of the round commit**: InstalledRoundCommit totalizes and installs the adopted checked round commit,
  turns `CommitAgrees` into a theorem, proves that the derived round agrees with the adopted execute (the remaining assumptions are the initial-transcript observation and
  degreeBits ≤ 13), the unconditionalization of the decode assumption, that the round digests chain 5 frames at a time after the 22-frame prefix and
  are drawn from counters 0/3, and the non-malleability of round messages. RES-4 and JCS's counter labels become theorems in this
  engine, and we also proved a concrete instance of DrawEncodesRun for draws whose coordinates are the actual digests. Review pointed out that the envelope permits indexBits=0 at width c=1, and made us state as a theorem the limitation that in that setting
  the index-length guard lets the decode-failure path through (though it is unreachable in this module's theorems).

The 2 added models both went through adversarial verification on the Fable side (the required fixes were all descriptions of novelty, coverage, and limitations, and
the addition of lemmas; no soundness defects were detected).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3659 named actual theorems/types/transitive axioms,
456 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #24 (after 3efafd4c)

With the tracked runner we re-checked the 107 models / 3659 theorems of commit `3efafd4c`, PASS (810.778 seconds, 1437 modules,
manifest `3e92472ca8f048d02592429233f36e9021d3909c0bb9c6321a2435d6c38ecc6c`, receipt
`b9f35b7157061f3ebda7c2ae15ab35bebc4bbbf88eb547058cdd9312c04b060e`, graph
`5d78a9de153572488476087bf45923df70c353168779e71dab70af815d1f9de9`).
The seventh round of the loop method. It targeted the composition of the installed fields and parseWhir, one of the last remaining observations.

- **Composition of the engine**: ComposedEngine gives a single engine with 10 fields concretized, leaving only parseWhir and
  configurationHash as observations. By 5 rfl identities it agrees with each installed engine, InstalledRoundCommit's
  initial-transcript assumption disappears by rfl, and degreeBits ≤ 13 and the shape assumptions are derived from acceptance. The summary theorem derives 16 conjuncts from acceptance
  (each conjunct is merely an application of an adopted theorem). We also turned into a theorem that an abstract parseWhir cannot pass a wrong root. Review
  traced each of the 16 conjuncts back to its source theorem and the base engine to confirm correctness, and made us fix documentation inaccuracies (describing an adopted module
  as "staged", the number of theorems carrying `hi`, and the expression "pinned triple").
- **Installation of parseWhir**: InstalledWhirParse concretizes parseWhir as a projection of the adopted WhirInitial's prefix reading, and
  proved the equivalence of verifyWhir, the redundancy of the root condition, the root positions in the transcript byte sequence, rejection of a wrong root, and that parse and
  tail read the same prefix execution. Review confirmed source faithfulness (stride, the order of the 2 roots, the position of the OOD answers,
  and the mask), and requested removal of 4 deprecation warnings of lemmas and explicit statements that the prefix includes up to the intermediate rounds and that the leading
  root of derivedContext is on the proof side (agreement with the pin was added via shape). After composition the only remaining observation is configurationHash.

The 2 added models both went through adversarial verification on the Fable side (the required fixes were documentation and warning removal, and no soundness defects were
detected).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3726 named actual theorems/types/transitive axioms,
458 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #25 (after 327d52da)

With the tracked runner we re-checked the 109 models / 3726 theorems of commit `327d52da`, PASS (818.525 seconds, 1439 modules,
manifest `6f4ffcd8465c06a2c2a3999fb60bd8f91a0b8d68a3b7b46ae2ae699fe91187e6`, receipt
`98d903428b68d3d5ff67a3249f9845864a3c2fc1e1984feeb8c485b08efc2f50`, graph
`8df8d7d544dc4cbfc3c6e8e3b67b25b88e132025213f85db48b42b6aaf9ea319`).
The eighth round of the loop method. It targeted the engine's last observation configurationHash and the probabilistic stage of R3.

- **Zero-check on the index point**: IndexPointZeroCheck gives the dichotomy of R3. It proved the bridge between the packed fold and the multilinear extension
  (no reversal, confirmed by a numeric probe at indexBits=2), that the density of the agreement set is ≤ indexBits/|F|, and that under a fold-level relation
  either per-column identification holds or the derived index point falls into a bounded set, and that for the same width the residue class is empty.
  Review made us clarify that since the committed width cannot be derived (capacity is only ≤), the residue is "a width mismatch (identification up to trailing zeros)",
  and made us fix a citation of a non-existent theorem and an unqualified title.
- **Explicit engine**: ExplicitEngine installs the last observation configurationHash as `khash ∘ encodeConfig`, giving a verifier model with no
  abstract base engine (all 12 fields are functions of explicit parameters). The encoding is injective on the 13 core fields,
  digest agreement forces core agreement or a concrete khash collision, and PinnedWhirProfile's idealization assumption became a theorem up to
  collisions. Review confirmed the faithfulness of the encoding's field order, made us correct the residues to the 2 items circuitDigest/circuitConfigDigest
  since gateRows is fixed by acceptance, and made us state that verification of the gate evaluator remains as a consequence of acceptance
  and that the treatment of deployment validation is a model of the Solidity path only (Rust re-verifies kIs etc. on every call).

The 2 added models both went through adversarial verification on the Fable side (the required fixes were classification and wording, and the addition of inhabitedness lemmas, and
no soundness defects were detected). With this, no observation fields remain in the engine of the adopted models, but that only means
"given that hashes are arbitrary deterministic functions and the WHIR tail is a manual model, all checking paths are explicit";
R1b (WHIR proximity + sumcheck soundness), R2 (extraction), Fiat–Shamir half (B), circuit truth, and Rust/Solidity
refinement remain unresolved.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3864 named actual theorems/types/transitive axioms,
460 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #26 (after c2141566)

With the tracked runner we re-checked the 111 models / 3864 theorems of commit `c2141566`, PASS (828.666 seconds, 1441 modules,
manifest `5fe36c22f984e419977de0a973408e862ca4e0ffe231f7f74ab482c5b184dbb7`, receipt
`84c157199baad093b2d86da3331f91f1e2feb4d80b499902b8de393f7f1a1cb7`, graph
`072d5962e491dd939676706e1eedd675f78068f472afaee95b6aff983da8b52f`).
The ninth round of the loop method. It targeted an assembly that fixes the audit's residue inventory as the assumptions of a single theorem, and the coverage of the gate evaluator.

- **Coverage of the gate evaluator**: GateEvaluatorCoverage fixes as a theorem that the complete dispatcher used by Integrated evaluates all 14 families
  and that the degree upper bounds also line up ("only ids 0,1,2,3,6,7" is
  correct only for the partial dispatcher of the base Gates), and shows the transcription of the declaration table and its agreement proof, the shape-checked
  evaluator, the exclusion of the 124-constraint row, and the impossibility of configuring a large BaseSum base. Review pointed out that the statement
  "there is no counterpart of the degrees on the Rust side" is wrong (validate_gate_ext3_context checks the same inequality with Gate::degree()) and made us correct it.
- **Assembly**: SoundnessAssembly gives a single theorem deriving constraint vanishing, per-column identification,
  profile rows, and core agreement from acceptance + the residual assumption structure + a good draw condition. The first draft had an unguarded index bad event, so the conclusion contradicted the assumptions and the forgery premise
  was mixed into the residues, so verification on the Fable side FAILed (deriving False from the assumptions in Lean); we fixed it with a guard and separated the attack
  into a conditional corollary, and in re-review confirmed that the refutation does not type-check and that with honest extraction the bad event is empty, making it
  PASS-WITH-FIXES. Simultaneous satisfiability of acceptance and the residues is not presented, and the name was made "good draw".

The 2 added models both went through adversarial verification on the Fable side. The rejection of SoundnessAssembly's first draft is an example of the review process
detecting the heaviest defect, "the main theorem is vacuous", and is the most important record of this update.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 3962 named actual theorems/types/transitive axioms,
462 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #27 (after 2016206f)

With the tracked runner we re-checked the 113 models / 3962 theorems of commit `2016206f`, PASS (833.92 seconds, 1443 modules,
manifest `f15c914f43bfbdc698c28ea01516e58fc9ad6b866dd2b9cbb46347e59a696ca5`, receipt
`1c16975af9aa7fef557a922bab3bf3cd7b1d7accc409f9376807fdb153aa9330`, graph
`864d79f348c8413b23faa055d438874b20d89dad94554efd87c285e4435237ce`).
The tenth round of the loop method. It targeted the 2 digest residues remaining in ExplicitEngine and the constructive digestion of the extraction seam (R2).

- **Canonical proof check**: CanonicalProofCheck models Solidity's `_requireCanonicalProof`, and pinned to deployment values the previously unmodeled
  immutable comparison of circuitDigest and the circuitConfigDigest absorbed into the transcript. Acceptance forces, for all 19 fields, either c = c₀ or a concrete khash collision, and no free fields remain in Config. Review
  traced the 10-comparison table and the provenance of the 19 fields, and requested the positioning in the verifyCall reading and a citation of the canonicity check of the digest words.
- **Construction of the extractor**: ExtractorConstruction defines the extraction state from the used claims of an accepted proof and the output of the R1b extractor,
  and after confirming that TruthChain is definitional, turned 10 of SoundnessAssembly's 19 residues into theorems by construction or from R1b.
  The remaining assumptions are only acceptance, R1b, the table and rows, deployment digests and boundedness, gate decoding, positivity of the constraint count, and the active filter.
  Review confirmed that fitColumn is the identity under hop.full, the consistency of the lanes' concretization, and irrefutability, and made us fix the
  rounds/point of the initial state to be empty (bound history under the adopted semantics) and the description of the diagonal of roundBadSet.

The 2 added models both went through adversarial verification on the Fable side (the required fixes were definitional hygiene and documentation, and no soundness defects were
detected). With this update, no free fields remain in Config, and most of the extraction seam has been digested by construction. What remains is
R1b (WHIR proximity + sumcheck soundness), Fiat–Shamir half (B), circuit truth, hashes, Rust/Solidity refinement,
and the presentation of simultaneous satisfiability of acceptance and the residual assumptions.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 4024 named actual theorems/types/transitive axioms,
464 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #28 (after 917e2cde)

With the tracked runner we re-checked the 115 models / 4024 theorems of commit `917e2cde`, PASS (836.35 seconds, 1445 modules,
manifest `9052117b5b14fc5f9f6bc5d090c8427343e2616e887e3268bee021bb18630629`, receipt
`66cfeff187cba129d908bdd75567cedf4bf19ec9099af82d6f8faa21bc505d7c`, graph
`e0d7e1c579f195daf593899226630c55a665a282f5eb0be6a3f0c127b718d988`).
The eleventh round of the loop method. It targeted the Rust-side call boundary and a first formalization of Fiat–Shamir half (B). At the same time we made documentation fixes to
the adopted SoundnessAssembly's committedWidth note (derivable from HonestOpenings.opened) and ExplicitEngine's
coverage note (the complete dispatcher is 14 families) (no change to theorems).

- **Rust-side boundary**: RustCallBoundary maps Rust's per-call checks, models the kIs canonicity chain and the circuit_config_digest
  recomputation, and shows that the Rust checks follow from Solidity-side acceptance, that the converse does not hold (the VK is deployed), and that on a deployment
  config both engines agree. Review made us state the direction of the kIs approximation (a lower approximation stricter than the source) and
  that rustEngine also reads Solidity's pins via the verify skeleton.
- **Localization of collision predicates**: LocalizedCollisions proves that global collision predicates such as `TranscriptCollision` are
  pigeonhole tautologies, states explicitly that the 54 affected adopted theorems are trivial as statements, and then restates the main theorems with localized
  refutable predicates. Review requested that the RowCollision family also be included in the table, that
  `ConditionalSoundness.no_row_collision_binds_opened_dot` is vacuous because its assumption is unsatisfiable (recorded as a required fix on the adopted tree), and a citation of the preceding note at ConditionalSoundness 685-692. In this update's REPORT/SCOPE, descriptions of
  "concrete collision" are to be reinterpreted in the sense of the localized predicates.
- **Squeezes of the random oracle**: RandomOracleSqueezes treats the hash as a uniformly random table on a finite set, and shows that, conditioned on fixing the block digest,
  the scheduled squeezes are uniform and the bad-draw mass is ≤ combinedBound (with a closed instance at d=13),
  a congruence lemma via separation of the frame/challenge inputs, and a run-level upper bound by Fubini on the frame fibre,
  P[bad draw] ≤ combinedBound + P[local collision of the round digest]. The first draft's non-adaptive theorem FAILed as review derived a contradiction in the assumptions
  (all digests forced to zeroDigest) in Lean, and re-review after reformulation raised the cross-cutting finding that "the global collision
  predicate is a tautology" and the limitation that "the additive term is 1 for the minimal closure witness", converging on replacement by localized predicates
  and an existence proof of a Q making the additive term < 1, with honest descriptions. A small upper bound and an adaptive prover remain unresolved.

The 3 added models all went through adversarial verification on the Fable side (RandomOracleSqueezes in 4 rounds, 1 of which was a FAIL;
LocalizedCollisions in 1 round; RustCallBoundary in 1 round). The required fixes on the adopted tree detected in this update are
the vacuity of `ConditionalSoundness.no_row_collision_binds_opened_dot` (the assumption ¬RowCollision is unsatisfiable) and
the reinterpretation of "concrete collision" descriptions as localized predicates.
The direct build under the adopted namespace and all integrated guards PASS. We checked all 4292 named actual theorems/types/transitive axioms,
467 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #29 (after 2d8de2d1)

With the tracked runner we re-checked the 118 models / 4292 theorems of commit `2d8de2d1`, PASS (894.88 seconds, 1448 modules,
manifest `1a98c5af11f6728ef9ba023b3c56aad6f8b4dcd6005bbd1b93722cde05bf3094`, receipt
`c0bcbb4407930c4f14f846e5d2318e74d9d1d25844194a1fe466b90dbc6301e0`, graph
`bab5f012649fef549d25ae80d3fe2cb8c412496a6602962d8670eca65ad5c1e3`).
The thirteenth round of the loop method. It targeted the repair of the vacuous adopted theorem pointed out by LocalizedCollisions and a birthday-type upper bound for the
additive term (round digest collision probability) left in RandomOracleSqueezes.

- **Repair of the vacuous theorem**: OpenedDotBinding confirmed by inventory that `no_row_collision_binds_opened_dot` has no use sites,
  and gives a replacement theorem assuming injectivity on a finite list computed from the execution, a localized form for leaf collisions, and non-degenerate
  concrete and refuting examples. Review made us make the description of the scope of the assumption more precise (for a multi-index opening, other rows/paths are also included).
- **Birthday-type upper bound**: BirthdayClashBound proves a fresh-query lemma and its adaptive version, an upper bound on the collision probability of a causal chain, and
  a collision probability ≤ 5d(5d+1)/2/|Block| for a round-fold chain model over a bounded-length query set. Review
  confirmed that the counting core is sound and non-vacuous, and made us fix the insufficient coverage in Check.lean, that the connection between the chain model and the execution is incomplete,
  and that the statement of the localized theorem still used the global collision predicate. In the fix we further proved that the starting point of the chain connecting the 22-frame prefix
  agrees with derive's digest (at 87 stages, ≤3828/|Block|), and only the induction of concreteChain remains.
  The run-level additive term is still an assumption, and 2145/|Block| must not be cited as a value of the execution.

The 2 added models both went through adversarial verification on the Fable side. As a fix on the adopted tree, we deprecated the docstring of the vacuous
`ConditionalSoundness.no_row_collision_binds_opened_dot` and made it refer to OpenedDotBinding (no change to theorems, no use sites).
The direct build under the adopted namespace and all integrated guards PASS. We checked all 4431 named actual theorems/types/transitive axioms,
469 reviewed hashes, 18 tables / 1147 words, and the 5601 files of the 7 dependencies.

## Continuation update #30 (after 94989dd5)

With the tracked runner we re-checked the 120 models / 4431 theorems of commit `94989dd5`, PASS (1116.97 seconds, 1450 modules,
manifest `988316051e4fa86ff372fd3b430b39f682acb4e10f73fbb31d3475cc7902bbd4`, receipt
`d546da99ae1a2948b8fc020e66519438b72c823a1ebf8a6576bd69d404c629ac`, graph
`ed485185cd626206d3ef8ded95c2c4df8bdf7646a260c7677eeebf0e82a5bb9e`).
The fourteenth round of the loop method. It targeted the connection between the chain model left by BirthdayClashBound and the execution, and the treatment of the index lane under the ROM law.

- **Identification of the chain with the execution**: ConcreteChainThreading, via `chain_model_is_the_run_chain` (by induction), identifies
  the digest at stage 22+5r of the chain with the digest after the first r messages of the adopted `concreteFinal`, reads the adopted
  `sourceDigest` as stage 22+5r+5 of the chain, and shows that `clashEvent` and `prefixRoundDigestClashEvent` are the same Finset.
  As a result, the assumption of the additive term remaining in RandomOracleSqueezes' run-level upper bound is abandoned, and
  `run_bad_draw_probability_le_birthday` became a run-level upper bound leaving no probabilistic side condition under the ROM for a fixed (non-adaptive) prover
  (≤ combinedBound + (22+5d)(22+5d+1)/2/|Block|, 3828/|Block| ≤ 2^-244 at d=13). It comes with a closed witness for the length budget
  (L=381) and a closed instance, its RHS<1 (`closed_bound_lt_one`), and non-emptiness (the constant table ∈ the clash event, not frame-free).
  Review fully reproduced the mathematics (an independently reconstructed olean matched the author's), and confirmed that absorb does not read the input counter,
  that getD's degenerate branch is not taken, and that the event equality is a true equality. The fixes were the reference SHA, explicit
  "fixed prover, ROM" qualifiers in the heading sentence, the frame count (statement vector 2 + root 3), the addition of the RHS<1 theorem, and the number of axiom-free theorems.
- **ROM law of the index lane**: IndexLanesOracle shows that stage 22+5d+8 of the extended chain with the adopted 8 claim frames added is the adopted
  `indexDigest`, and by the bridging lemma requested in review identified stages 22 and 22+5i+5 of the extended chain with the adopted derive /
  roundCommitted digests. Under a fixed index digest, the pushforward of `actualIndexDraw` is strictly
  equal to the adopted `indexProbability` (3 squeezes per coordinate; the mod-p bias is already accounted for on the adopted tauTerm side), the guarded index bad event is ≤ 2·tauTerm, and the union of the joint family and
  the index family is ≤ combinedBound + 2·tauTerm under a fixed digest (since the index counters numerically overlap the outer counters, the separation is
  by digest only. The union bound consumes only the injectivity of each family, and we state that the distinctness of the intersection is used only on the satisfiability path), and
  the birthday upper bound of the extended chain is 4560/|Block| at d=13. Review confirmed that in both the Lean model and Solidity/Rust, stage 22+5d is the
  snapshot passed to the index sampler (there is no other transcript operation between the last round commit and the index absorb), and that the pushforward equality is exact without
  a divisibility assumption. Not carried out are the run-level Fubini of the union, and the Lean-level connection of `hst` (ConcreteChainThreading proves
  the same fact but there is no mutual import).
  The two modules together are 122 models / 4530 theorems. This too is a result under the ROM law and for a fixed prover, and is neither a property of keccak nor the system's soundness
  error. An adaptive prover, R1b (WHIR proximity + sumcheck soundness), the true value of the circuit, and simultaneous satisfiability of an accepting proof and the residues are untouched.

## Continuation update #31 (after 5e55b602)

With the tracked runner we re-checked the 122 models / 4530 theorems of commit `5e55b602`, PASS (854.581 seconds, 1452 modules,
manifest `d880585491d008e94f5b39a4cfeba31441f20373e89e122435be788954104346`, receipt
`e06033d3d393f681e975e820cf3ce362ad1deb36250ed2ef1a5bb4365a10ec8a`, graph
`65480d4334a2ee54b091f5c44bf8526dc910427ab4c95f0b0fec98be5d84ee3f`).
The fifteenth round of the loop method. It targeted the junction of ConcreteChainThreading and IndexLanesOracle (the run-level union bound) and a first step toward an adaptive prover (the chain's birthday term).

- **Run-level union bound**: RunLevelUnionBound abandons ILO's `hst` via CCT (stage 22+5d+8 of the extended chain = the assembly's actual index digest, rfl), and
  re-runs RandomOracleSqueezes' frame fibre Fubini once for both families simultaneously to obtain P[jointBad ∪ guardedIndexBad] ≤ combinedBound + 2·tauTerm +
  P[clash of the extended chain] (4560/|Block| at d=13). With a closed instance (L=381) it shows RHS<1 and the existence of a good table. The failure set of the explicit engine's
  assembly conclusion is contained in the hash-indexed union event (unconditionally). Review confirmed the actual use of the split and prefix separation, joint
  injectivity outside a clash (including block 0's digest = derive digest), the exact fibre counting, and the total of the ≤s, while judging that the covering assumption on which the first draft's mass corollary depended
  (that a fixed event dominates for all hashes) is not known to be satisfied even for a fixed prover in a non-degenerate execution (the hash enters the
  bad event only via the gate alpha coordinate and the outer row point), and by the anti-vacuity policy had the covering theorem and the mass corollary deleted. We stated in the heading that the remaining bridge is a two-stage conditional count and is not a problem of
  adaptivity. We also disclosed the additional cost of `hlenI` (an upper bound on the width of p.used; L=381 is only for width ≤13) and that the index half of the closed witness is ∅.
- **Birthday upper bound against strategies**: StrategyChainBound re-runs the fresh-query induction against strategies (functions choosing the next frame from
  previously seen digests and their challenge answers; causality is built into the type), obtaining for any strategy a chain clash probability ≤ n(n+1)/2/|Block| (3828/|Block| at 87 stages,
  the same constant as for a fixed prover). The keys are the adopted `frame_ne_challenge_input` (rewriting a frame answer does not move a challenge answer) and
  the distinctness of digests under no-clash. It also shows the uniformity of challenge answers conditioned on the chain's own no-clash event (single / finite-set version), and that the chain of a strategic outer
  prover agrees with concreteFinal on the realized messages per table. Review made us state in the heading that the strategy is a transcript-restricted model with no oracle queries of its own (grinding provers are out of scope; the mass is proportional to the number of queries), and corrected the expression "conditioning on the history"
  to conditioning on the no-clash event. Not achieved is the union bound for an adaptive prover
  (transport of OuterSequentialConditioning's sequential conditioning counting to the oracle table), which is stated explicitly in the heading.
  The two modules together are 124 models / 4637 theorems. Both RunLevelUnionBound's first-draft covering assumption and StrategyChainBound's expression "the very
  information a Fiat–Shamir prover has" were rejected in review (the former an assumption not known to be satisfied in a non-degenerate execution, the latter having silently excluded grinding provers with their own
  oracle queries). This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
  What remains is the two-stage conditional count for a fixed prover, the union bound for an adaptive prover (transport of sequential conditioning to the oracle table), the query counting of a grinding prover,
  R1b, the true value of the circuit, and simultaneous satisfiability of an accepting proof and the residues.

## Continuation update #32 (after c2b5bc53)

With the tracked runner we re-checked the 124 models / 4637 theorems of commit `c2b5bc53`, PASS (875.055 seconds, 1454 modules,
manifest `a42ad65a94eb376744257475a45bc82f565ab22adde7422a2d5a8bebe50b2f34`, receipt
`baf9c8f84601c50fffa062a2d9d0733f8b3179bfb64302af71079bd0b9f18af2`, graph
`ca1b2c730dee823ab5a50a75eda72564f9fc51b443d8e37769706164d2102972`).
The sixteenth round of the loop method. It targeted the two-stage conditional count for a fixed prover that RunLevelUnionBound had left as a contract, and the grinding provers that StrategyChainBound excluded.

- **Outer stage of the two-stage conditional count**: TwoStageConditionalCount shows that the explicit engine's outer bad event depends on the hash only via the gate alpha coordinate
  (absorbing also the engine's own dependence), evaluates the diagonal event with a single-coordinate conditional count keeping the adopted combinedBound, and transports it to the oracle table by RLUB's fibre Fubini
  (`run_outer_stage_mass_le`). Review confirmed the legitimacy of the conditioning (the effective assumption being that each fixed alpha event is a cylinder independent of the alpha coordinate, so
  adversarial families {w | w_α = a} are excluded) and the agreement of the constants, while refuting with an adopted lemma the obstacle claim at the index stage that "the row point is not a function of the outer draw (log-tau sequence)".
  After the fix we turned into a theorem that the row point is a function of the outer draw, paid out the index stage's conditional count with `RowPointFixed` as an explicit assumption
  (non-degenerately satisfied by a constant column; we state that the payoff is only for a constant committed column), recorded as a theorem that the index half of the closed instance is ∅, and
  added a second closed instance in which the guard is live.
- **Chain upper bound for grinding provers**: GrindingQueryBound formalizes a prover with q probe queries of its own at each stage, found that the adopted Causal does not withstand re-querying,
  replaced it with FreshCausal conditioned on a freshness event, and via an upper bound on the event of answer agreement between different strings obtained
  a chain collision mass ≤ N(N+1)/2/|Block| (N=(q+1)n; 3828/|Block| at q=0). It exhibits a strategy that reads the probe answers, and shows agreement with SCB per table at q=0.
  At review's request we generalized the reading of the challenge input to an arbitrary digest (only the position in the sequence is in frame form), and stated that the upper bound is quadratic in q with
  a leading term about (q+1) times looser (SCB's "q·n" is heuristic).
  The two modules together are 126 models / 4780 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error. What remains is
  the finer splitting of the index stage (a 3-stage contract), the union bound for adaptive/grinding provers, linearization in q of the grinding bound, R1b, the true value of the circuit, and
  simultaneous satisfiability.

## Continuation update #33 (after 3a5fedba)

With the tracked runner we re-checked the 126 models / 4780 theorems of commit `3a5fedba`, PASS (883.049 seconds, 1456 modules,
manifest `b04b24cb68d71f05e5a74468b0f1d8311bfb204e368a8accaf59347b22bda9cc`, receipt
`6e0cf2860eaa8c94a2923190a2a5039ba12c0827eba57b53b41372232a96d7f7`, graph
`c600a127f60b34f5ab9eba36e01d894a5f5b8491cb72f590b56e0c1730077cb5`). The 2 preceding runs against the same commit failed because an implementation agent running in parallel
issued `pkill -f "[l]ean --root"` and stopped the runner's lean processes from outside (`lean exited -15`, no output), and
are not audit findings (the records are the candidate directory's fresh-run-3a5fedba-FAIL-run1/2.log and receipt copies).
The seventeenth round of the loop method. It targeted the finer splitting of the index stage that TwoStageConditionalCount left as a contract, and the adaptive-prover union bound that StrategyChainBound left.

- **Finer splitting of the index stage**: IndexStageFinerSplit constructs the 3 stages — out-of-clash injectivity of the joint schedule, restrict_ratio at the joint selector, a 2-group conditional count, and frame fibre
  Fubini — and abandoned `RowPointFixed` by counting. The headings are `run_index_stage_mass_le ≤ 2·tauTerm + P[extended clash]` and
  `assembly_failure_mass_le_unconditional` (no condition on the committed column; RHS is combinedBound + 2·tauTerm + P[extended clash], 4560/|Block| at d=13,
  RHS<1 on the closed instance). Review confirmed the diagonal counting (u is the complementary K1 half and not a fibre constant; F u is literally the guarded index bad event at the row point), character-level agreement with RLUB's hash-indexed family,
  a single additive term from a single Fubini, and that the assumptions are just TSCC minus `RowPointFixed` (and `committed0`), and made it PASS.
  Wording remarks (unused arguments, qualifiers of derived forms, and that "abandonment" is removal of an assumption by counting and not a proof of the predicate) were reflected.
- **Transport of the outer lane's conditioning**: OuterLaneTransport (first-draft name AdaptiveUnionTransport) transports each round's conditioning in OSC to the oracle table with a diagonal fresh step (splitting the conditioning event by the target's value) and
  nested no-clash events, obtaining ≤ outerTerm + a chain collision term for any strategy-driven chain. Review
  confirmed the correctness of the counting (the ceiling upper bound of the adopted laneBad_card_le; the sum agrees exactly with outerTerm), while pointing out that the general form's heading handles **lane bad sets quantified independently of the strategy**
  (verdict iii), not closing SCB (iii)'s "the round's bad set is determined by the messages the prover chose", and that
  the closed instance's bad set was claimed non-empty although it is empty at early rounds. In the fix we renamed the module, stated non-constructibility (domain and loss)
  in the heading, made non-emptiness a two-directional theorem, and proved agreement of the lane message with the realized message for a reduced-history subclass (ReducedStrategy), adding
  a genuine adaptive union bound restricted to that subclass, `reduced_outer_lane_bad_draw_probability_le`. Re-verification confirmed that the joining lemma is a true identity (the input of the lane-side bad set = the message the strategy absorbed at round r, and the gate-side take bookkeeping also agrees), and
  rated the subclass theorem as verdict (i) (a genuine adaptive upper bound) and the general form as verdict (iii), and made it PASS. That the truth function and the claims are free is the correct shape for a ∀-quantification
  (for honest messages the bad set is empty).
  The two modules together are 128 models / 4895 theorems. Thanks to IndexStageFinerSplit, the failure set of the explicit engine's assembly conclusion under the ROM for a fixed prover now has
  a mass upper bound with no condition on the committed column. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error. What remains is
  an adaptive upper bound for raw-block-reading strategies, transport of tauTerm/alphaTerm, the union bound for grinding, guard liveness for non-constant columns, R1b, the true value of the circuit, and
  the presentation of acceptance.

## Continuation update #34 (after 63722788)

With the tracked runner we re-checked the 128 models / 4895 theorems of commit `63722788`, PASS (900.365 seconds, 1458 modules,
manifest `80c5a0ac065ce87206d173e1136033167eac1fd4a95c1f9179c54234ecf6b61d`, receipt
`1b84c594fd49c83780b75d77ef449323949a65e5da1ba314c94e5a0efa6a9623`, graph
`605078e3db6f3659a66ee5baad7fcacdd4c8975f0096c00a024761ee82b5cc7e`).
The nineteenth round of the loop method. It targeted extension of the constant of OuterLaneTransport's reduced-subclass upper bound, linearization in q of the grinding bound, and an explanation of the liveness/deadness of the index guard.

- **Completion of the reduced-subclass upper bound**: ReducedFullTransport adds the gate tau / gate alpha events at the derive digest as fixed targets (the adopted tau/alpha
  bad events depend only on g/coeffsOf and do not read the table), and by simultaneous peeling of the 3d counters and a shared collision term from nested no-clash obtains
  `reduced_full_bad_draw_probability_le ≤ combinedBound + a chain collision term` (RHS<1 on the closed instance). The index lane is not included because for an adaptive prover the used claims
  become a function of the table, and the reason is stated. Review confirmed that the reads of gate tau / gate alpha read the derive digest at the adopted sourceCounter (12+3d+3i, 9+3d), that the events are pullbacks of the adopted tauBadEvent/alphaBadEvent, and that there is a single collision term, made it PASS-WITH-FIXES, and made "stage 22 = derive digest" and the 2 pullbacks theorems rather than prose (`derive_stage_is_derive_digest`, `gate_tau_bad_event_is_pullback`, `gate_alpha_bad_event_is_pullback`).
- **Linearization of the grinding bound**: GrindingLinearBound restates the push-down over query strings and, with formed stage digests as position-dependent targets, obtains
  (q+1)n(n+1)/2/|Block|. However, this is limited to state-framed provers whose probes frame on formed stage digests, and attackers who simulate candidate chains within the probe budget are explicitly
  excluded (GQB's quadratic bound covers them). At q=0 it agrees with the adopted constant with no restriction. Review confirmed the inclusion (strong induction over later stages; progress is automatic since stage r is formed by stage r−1's absorb), the counting, the strategy-level assumptions, the residual form, and the numbers, and made it PASS-WITH-FIXES (wording: the number of defs, the constraint that StateFramed is limited to "strings that subsequent absorbs ask about", and that the residual term is "almost the whole space").
- **Liveness of the index guard**: IndexGuardLiveness turns into theorems that the guard dies only when "claimed cell = committed cell" at a common width (the honest case; the index event is ∅), and
  that for a non-constant column (spikeColumn) dead ↔ eqAtZero(row) = (x−v)/(w−v), a single field equation, closing ISFS's open item
  as an explanation (the upper bound is unchanged). Review confirmed the characterization and the index convention of the extension and made it PASS-WITH-FIXES, correcting "all downstream consumers are in 1-cell form" (wrong: ISFS's indexBadAt does not assume width agreement; the dead condition is agreement after zero padding) and the heading's "non-empty" claim (unproved).
  The three modules together are 131 models / 5002 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error. What remains is
  the adaptive treatment of the index lane (diagonal form), raw-block-reading strategies, attackers simulating a chain within the probe budget, the joining of g/coeffsOf with the deployment table, R1b, the true value of the circuit, and
  the presentation of acceptance.

## Continuation update #35 (after a5f73b35)

With the tracked runner we re-checked the 131 models / 5002 theorems of commit `a5f73b35`, PASS (1394.096 seconds, 1461 modules,
manifest `cfb7c94f799310747fb97688a054d4d49ce5cf348c078d9197aa40d120e2f779`, receipt
`3ac5415e12fab3d64d2292dfbeb76adf25440108595e02054588262cc4abfd8f`, graph
`a31ef1dcf2b4e847e7b686811bb7bb2a9c71cecd861fe370743039ae9378ba59`).
The twentieth round of the loop method. It targeted the index lane of the reduced-history adaptive prover and a query-graph view of grinding provers.

- **Index lane of the reduced adaptive prover**: ReducedIndexLanes shows that stage 22+5d+8 of the chain of an extended strategy that absorbs history-dependent used-claims selection as 8 claim frames is
  the adopted indexDigest at the realized claims, and via a diagonal fresh step at the index digest (separation by digests under no-clash), a density lemma, and simultaneous peeling of the 6·bits counters,
  obtains `≤ combinedBound + 2·tauTerm + (22+5d+8)(22+5d+9)/2/|Block|` with an index term of 2·tauTerm added (RHS<1 on the closed instance). The committed cell
  is a parameter of a function of the history and transfer to a realized proof has not been carried out; we disclose that the index term is for 1 bound cell. Review confirmed the identification of the extended chain (8 claim frames; U reads only the reduced round history), separation by digests under no-clash, the rigor of the density lemma and the peeling of the 6·bits counters, and the single collision term, made it PASS-WITH-FIXES (documentation only), and made us correct HONESTY (iii) to "what the transfer needs are the prefix congruence lemma, the realized-draw identification of OLT §6, TSCC's row point theorem, and the existing assumption that the columns are fixed data; RowPointFixed is unnecessary".
- **Query graph of grinding**: GrindingGraphBound reduces a stage collision to a collision of position pairs on the absorb path, gives a unified charging theorem having GQB/GLB as instances, and
  then records as a theorem that for a chain-simulating prover the eligible set coincides with all pairs so that this method does not improve the constant (a negative conclusion;
  it does not claim a lower bound on the collision mass). Review confirmed that the unified theorem is a position-dependent-target version of GQB's fresh-position induction, that the 3 instances agree term by term with the adopted theorems, that the reachability limit is m rather than n, and that there are no traces of contamination, and made it PASS (2 docstring items supplemented).
  The two modules together are 133 models / 5115 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error. What remains is
  transfer of the committed cell to a realized proof, an index term for multiple bound cells, raw-block-reading strategies, a linear bound for general grinding provers (outside the charging method),
  the joining of g/coeffsOf with the deployment table, R1b, the true value of the circuit, and the presentation of acceptance.

## Continuation update #36 (after d523eecd)

With the tracked runner we re-checked the 133 models / 5115 theorems of commit `d523eecd`, PASS (1181.923 seconds, 1463 modules,
manifest `cfd8dc008e434a455cd787bd2d38d2fcc94e4b35ddf81a5066b93f62fef31ffa`, receipt
`4a3b0a6fdd5fa05305cf86d39f0658849700aad9d4289242170d5ba2b84e2ac5`, graph
`73765b5d7ce76b9f3365fc820fb3e48620185de65eac0bb1eaf2218459767d77`).
The twenty-first round of the loop method. It targeted the transfer left by ReducedIndexLanes and the lifting of the reduced-history restriction.

- **Transfer to the engine's own index event**: ReducedEngineIndex combines a two-strategy, same-table congruence lemma, OLT §6's draw identification, and TSCC's row point theorem on a realized proof,
  shows that the committed cell is a function of the reduced history, obtains a Finset identity with the engine's own index bad event, and makes the reduced adaptive upper bound
  ≤ combinedBound + 2·tauTerm + a chain collision term hold on the engine's own event (the multi-cell version is 5·2·tauTerm, with a single collision term. RIL's hst is also abandoned).
  Review confirmed that the left-hand side of the Finset identity is exactly the event consumed by `explicit_good_draw_assembly`'s hidx (actually abandoning hidx by probe), that all three identifications are theorems, the function-level quantification of the congruence lemma, the side conditions of realizedRun, and the single collision term of the multi-cell version, and made it PASS-WITH-FIXES (only the REPORT's line count).
- **Lifting of the reduced-history restriction**: RawBlockLanes uses the fact that all the diagonal fresh step needs is RoundCausal, and with a raw lane not going through OSC's Lane
  (raw messages, evaluation at the reduced challenge) obtains an outer + block-0 upper bound ≤ combinedBound + a chain collision term for any RoundCausal strategy, recovers OLT §8 as a special case, and
  gives a closed instance with challengeTruncatedMessage, which OLT could not map. The raw version of the index half is explicitly not achieved. Review confirmed that one stage of the raw lane agrees with a stage of the adopted verifier (polynomial evaluation at the reduced challenge), the joining, the recovery of OLT §8, the single collision term, and the closed instance, and made it PASS-WITH-FIXES (wording), correcting the heading to "closes **half of each round decomposition** of SCB (iii) with the combinedBound lane (run-level transport not started)".
  The two modules together are 135 models / 5223 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error. What remains is
  the raw version of the index half, the union bound for grinding provers, the joining of columns / g/coeffsOf with the deployment table (CommitmentOrder), R1b, the true value of the circuit, and the presentation of acceptance.

## Continuation update #37 (after d6603b5c)

With the tracked runner we re-checked the 135 models / 5223 theorems of commit `d6603b5c`, PASS (1401.11 seconds, 1465 modules,
manifest `675137424184c1cd832a5056d58563def95cadc9aabc5b2ad12963dda487e079`, receipt
`f407c41b37cc38204335d5871b5819e881d7e363c31c0c0b63368444ec6124f7`, graph
`01d65a87670b039fa86501fbbac7ecd75cfa5340302213b86d2e7e6f56b948ef`).
The twenty-second round of the loop method. It targeted the index half for raw strategies and settling the run-level transport at the end of SCB HONESTY (iii).

- **Raw index half and engine transfer**: RawIndexLanes defines a raw extended chain with ClaimsCausal used-claims selection, and by verbatim reuse of RIL's counting stack and REI's transfer lemmas
  (the new items are 2 invariance lemmas), obtains for any RoundCausal S and ClaimsCausal U, on the explicit engine's own event,
  ≤ combinedBound + 2·tauTerm + a chain collision term (5·2·tauTerm for the 5-cell version). The closed instance has RHS<1 with a raw-block-reading strategy and a claims selection.
  Review confirmed that ClaimsCausal definitionally agrees with the stage-d version of RoundCausal, the identification of the claim frames and indexDigest, the separation by digests under no-clash (invariant across all counters), the strategy-independence of RIL's counting stack, the Finset identity with the engine event (abandoning hidx by probe), and the single collision term and the 5-cell version, and made it PASS-WITH-FIXES (documentation only).
- **Settling the run-level transport**: RunLevelTransportAudit shows, from the fact that the outer part of the adopted `jointBadEvent` takes a frozen LaneRound list and the recursion of the claim
  advances at each round's challenge field, that RBL's raw total event equals as a Finset the run-level bad event of `actualDigestDraw` on a realized proof, obtaining
  an adaptive run-level upper bound in the same shape as the fixed-prover theorem (RHS<1 on the closed instance). It turns into a theorem that whole-schedule uniformity is unnecessary, and does not claim a product law.
  The proposed corrected text was reflected in the docstrings of SCB (iii) / OLT (vi) / RBL (vi). Review confirmed that the outer part of `jointBadEvent` takes a frozen LaneRound list and recurses on its own challenge field, that the realized lane satisfies the seam predicate of the adopted `DrawEncodesRun` at the realized draw, the per-coordinate transport, and that the event is the diagonal of the fixed-prover family (the same statement shape), and made it PASS-WITH-FIXES (prose): we changed the unproved negation "the no-clash event is not closed under reassignment of inner stages" to "closedness is not known, and whether the product law holds is undecided here", and made us state in the proposed corrected text the scope (outer + block-0, transcript-restricted causal provers, claimed start 0, index via RawIndexLanes, ROM, grinding excluded. The OLT side is limited to the heading of the reduced subclass).
  The two modules together are 137 models / 5317 theorems. With this, the ROM adaptive upper bound holds, for transcript-restricted (no own queries) causal provers,
  on the explicit engine's own events in all of the outer, block-0, and index lanes, and has also been stated in run-level form. This too is a result under the ROM law, and is
  neither a property of keccak nor the system's soundness error. What remains is the union bound for grinding provers, the joining of columns/tables with deployment (CommitmentOrder), R1b,
  the true value of the circuit, and the presentation of acceptance.

## Continuation update #38 (after 2cf506f6)

With the tracked runner we re-checked the 137 models / 5317 theorems of commit `2cf506f6`, PASS (1534.183 seconds, 1467 modules,
manifest `4a84b12770f6c6ec43f9d20dd9c90bf32de3ba99e64526570eb62fffdd16e977`, receipt
`1b1cfb8725f8aef6f143ca50496a1df0019b6972e60cdbf03ea0d86e94c05ec8`, graph
`e1eb1d0e3cdedded09f0ea7b35b9941b7fc0e01aaa4c2f51c66a3fb5e1d71b16`).
The twenty-third round of the loop method. It targeted the classification of the "fixed data" residues, the union bound for grinding provers, and the alpha diagonal of the tau events that the classification exposed.

- **Classification of the fixed-data residues**: CommitmentOrderSurvey showed that the gate alpha is a squeeze of the derive digest (a challenge coordinate) and that the assembly's tau table g
  reads it. Review rejected the first draft's classification of alpha as "prefix data" (even a deterministic function of the prefix digest is not a value bound outside
  the oracle law), and established that the tau event of a fixed g in the ROM series is merely an alpha-fixed slice of the engine's own tau event with the diagonal unevaluated, and
  that what REI/RXL may call "the engine's own event" is only the index event. The committed column depends on the round-one opening (absorbed after the index squeeze)
  and is not prefix data, and "fixed" turned out to be an R1b-type rootDetermined assumption. We fixed overstated wording in 12 places across 6 adopted files (RFT, JointChallengeSpace,
  OuterSequentialConditioning, RIL, REI, RXL).
- **Union bound for grinding**: GrindingUnionBound obtains, for ChallengeRestricted grinding provers (challenges are read only at their own stage digest),
  an outer + block-0 union bound ≤ combinedBound + N(N+1)/2/|Block| (peeling over an abstract stage digest family, with a GrindLane that can also read probe answers). Review
  pointed out that the first draft's preReadGrinder does not perform the attack it names (tag mismatch) and that the inclusion of "a broader class" was unproved, and made us
  fix it with a selector version and an inclusion theorem, and state in the heading that the joining in which the bad set carries the grinder's own messages is incomplete. The orchestrator's proposal of an "extended clash event" was
  refuted on the point that probe → absorb are the same string, and it was established that pre-read (FS challenge grinding) is outside this method. Re-verification confirmed that the causality clause of the extended lane is a cut strictly below the round's challenge stage (a prover that inserts probes between a round's 5 frames is unmodeled; the diagonal step goes through even with a loose cut), that the selector version preReadGrinder does move to the pre-read digest under a favorable reading, the inclusion theorem, and the honesty about the joining being incomplete, and made it PASS-WITH-FIXES (1 docstring location).
- **Alpha diagonal of the tau events**: EngineTauDiagonal splits the conditioning event by alpha triples and applies RFT's simultaneous peeling in each block to show that the mass of the engine's own tau event
  is ≤ tauTerm d for any strategy and any G (the diagonal does not increase the constant), and reconstructs the RXL path to obtain
  ≤ combinedBound + 2·tauTerm + a chain collision term on the engine's own tau + index events. It states explicitly that what remains in ∀-lane form in the final theorem is the outer (the alpha-dependent outer diagonal in the adaptive series is unresolved) and
  alpha (no diagonal needed). Review confirmed the diagonal counting (splitting by alpha triples, stage stability of each block, the adopted per-value density upper bound) and the reconstruction of the RXL path (the assumptions are identical to RXL's, with a single collision term), made it PASS-WITH-FIXES, and made us add as a theorem the identification that `alphaRead` equals the realized proof's `gateAlphaElement` (derived from RLTA). With this the only unproved residue is tables = s0.tables (the CommittedTables joining).
  The three modules together are 140 models / 5469 theorems. Thanks to CommitmentOrderSurvey's classification and EngineTauDiagonal, the ROM adaptive upper bound for transcript-restricted causal provers
  is stated on the engine's own tau and index events, and the outer (alpha-dependent diagonal, unresolved in the adaptive series) and alpha (no diagonal needed) are in ∀-lane form.
  This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error. What remains is the outer alpha diagonal of the adaptive series, the query counting of pre-read provers,
  the joining with the grinder's own messages, CommittedTablesJoin (rootDetermined, preprocessedPinned, configDeployed), R1b,
  the true value of the circuit, and the presentation of acceptance.

## Continuation update #39 (after be012e44)

With the tracked runner we re-checked the 140 models / 5469 theorems of commit `be012e44`, PASS (1433.378 seconds, 1470 modules,
manifest `47e3a0c1cac5e6bc0573c674762d9a8a8ac1e521e0015b12a47c8a039b0dca59`, receipt
`0130324cafcff44a7b19a8160e9f44205924a4e55df008caa03aaed0ac067e33`, graph
`049d621b851d3edd1345b324fd008517201392ce5383f9547dbc9610d851e974`).
The twenty-fourth round of the loop method. It targeted the outer alpha diagonal of the adaptive series and the query counting of pre-read grinding.

- **Outer alpha diagonal**: EngineOuterDiagonal shows that alpha enters the outer event only via the gate lane's initial truth claim, defines the engine's own outer event with a raw lane family indexed by alpha, and
  since alpha is read at a stage strictly earlier than the round cell, OLT's diagonal fresh step applies unchanged, obtaining ≤ outerTerm.
  With this, all 4 events are the engine's own, and ≤ combinedBound + 2·tauTerm + a chain collision term (RHS<1 on the closed instance). We state that a corollary to the assembly failure set is
  not reached because 2 legs remain: the validity of DrawEncodesRun at the realized draw, and the identification of the lane sequence. Review confirmed all proofs (the alpha-dependent rfl decomposition, invariance via 22 < 27+5r, no need for splitting due to the uniform cardinality, and the fully-owned union with the same assumptions as ETD), rejected the diagnosis of "2 remaining legs" (DrawnAt holds constructively on the realized lane) and reduced it to the single leg of lane-sequence identification, and corrected an overstatement in the summary sentence (not only tables = s0.tables). PASS-WITH-FIXES. The fix added 4 theorems on DrawnAt / the frozen walk (45 theorems).
- **Charging of pre-read**: PreReadCharge proves (q+1)·outerTerm for a class including the pre-read provers that GUB excluded, with a two-stage fresh peel that charges probes.
  It shows that on the favorable branch the round's challenge digest is the probe's digest itself, and turns into theorems the reason absorbs (repetitions) are not charged and
  the reason charging probes charges the attack. The joining (the grinder's own messages) and the other lanes are not achieved. Review confirmed the soundness of the two-stage peel and the arithmetic, and then made us correct that the gap in the joining is not "the absence of a decoder" but **structural** (GrindLane can read only the cells of the stage digests and cannot express pre-read's realized messages / running claim), that "bounds it" is an upper bound for a candidate-family surrogate, and that the absorb slot is empty for the provers under test. The fix added a dichotomy lemma and a loose cut (60 theorems).
  The two modules together are 142 models / 5574 theorems. Thanks to EngineOuterDiagonal, the ROM adaptive upper bound for transcript-restricted causal provers is stated with all 4 events
  as the engine's own (a corollary to the assembly failure set still has 2 legs remaining). Thanks to PreReadCharge, FS challenge grinding was evaluated with the expected factor (q+1)
  (the joining is incomplete). This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error. What remains is the lane-sequence identification (the assembly corollary of the adaptive series), the joining with the grinder's messages, CommittedTablesJoin, R1b, the true value of the circuit, and the presentation of acceptance.

## Continuation update #40 (after ac1fb665)

With the tracked runner we re-checked the 142 models / 5574 theorems of commit `ac1fb665`, PASS (1362.576 seconds, 1472 modules,
manifest `ceca92d3edcf8dc73203c659e4f6cd71321628596569308a57a3e8a8dc72d53b`, receipt
`50176f39ed12391bb75edbefe9ce91e6c580b8b7eaeb274739bc03997ddd01bc`, graph
`82d864633ee6423d5f8c76e9934c678e6a195337c3137f73c5ab16e49bed6cd3`).
The twenty-fifth round of the loop method. It targeted the lane-sequence identification left by EngineOuterDiagonal and the per-clause verdicts on the `CommittedTables` joining.

- **Assembly failure upper bound for the adaptive series**: AdaptiveAssemblyFailure shows that the realized lane sequence and the adopted engine lane sequence agree on the projection that `frozenLane` reads, closing
  EOD's last leg, and proved that the fully-owned event agrees as a Finset with `SoundnessAssembly.outerBadEvent` on the realized run. As a result the
  assembly failure set is contained, with no assumptions, in the union of that event and the index event, and the mass is ≤ combinedBound + a chain collision term + P[index event]. The mass of the index half is
  still carried, and we state in the heading that transporting the proof record to the evaluation point of the adopted index modules (the extended-shape chain / a different used record) is the remaining step.
  Review (adversarial verification by Opus) independently re-derived that frozenLane reads only `.message`/`.truth`, that there is no index shift in the truth sequence, that the engine is free, that `thash` does not enter by any path other than `gateAlphaElement` (the public input hash is hash-independent), and that the payoff is exactly the contrapositive of the adopted assembly theorem, and made it PASS-WITH-FIXES. It made us state that the closed instance's heading covers **only the first 2 terms** (including the index term, only mass < 1 + P[index event] follows).
- **Per-clause verdicts on the `CommittedTables` joining**: CommittedTablesClauses derives preprocessedPinned from acceptance for any engine, derives configDeployed
  on the Solidity path up to a single local configuration-encoding collision, and shows that rootDetermined is R1b itself and moreover that for an extractor reading the disclosure there exists no table map satisfying the clause
  (hence COS's degenerate witness had been forced). The adopted binding lemma reaches only the opened cells, where
  root determinacy holds up to a local leaf/path collision. In conclusion, "the tables are fixed data" is reduced to R1b + 2 local collisions, and `g` is still
  not fixed data (it reads block-0's alpha). Review (adversarial verification by Opus) confirmed that the derivations of clauses 1 and 2 are rigorous and that the impossibility of clause 3 is genuine with the adopted extractor (`0 < numWires` being effective), made it PASS-WITH-FIXES, and made us correct that the acceptance/collision assumptions of the tau-table corollary are inert (they follow from R1b alone), that the fixture theorem is trivially true, that "2 different hint buffers" is only a difference in unconsumed trailing bytes, that the corrected text had dropped the qualifier about the Solidity path and the proviso about local collisions, and that "nothing is restated" is wrong (35 theorems).
  The two modules together are 144 models / 5642 theorems. With this, the assembly failure set of the adaptive series has an upper bound (while still carrying the mass of the index half), and
  the residue that the ROM series had consistently called "fixed data" has been decomposed into R1b and 2 local collisions. This too is a result under the ROM law, and is neither a property of keccak nor the system's
  soundness error. What remains is the transport of the index half, R1b (root determinacy of all columns), the true value of the circuit, the presentation of acceptance, and the joining for grinding provers.

## Continuation update #41 (after cf5154da)

With the tracked runner we re-checked the 144 models / 5642 theorems of commit `cf5154da`, PASS (976.283 seconds, 1474 modules,
manifest `c73e62e7fede78e845ce185f280ea96bfd89b1bef20e3b26dabc4ac250daa4a6`, receipt
`dc57d67e22ea1d701164a0b9f09dd0d366c8710b7886e95877e1ec063385f6d6`, graph
`1999c10334e6cd13ded4f935811c1dc7a9c67fd1df3eca43591d498d276629f7`).
## Continuation update #42 (after cf5154da)

In iteration 27 we adopted the transport of the index half and the mass computation of the 2 localized collisions. Both went through adversarial review by Opus, and
**both reviews pointed out substantive defects**.

`Audit.Wire3.IndexHalfTransport` (38 theorems / 8 definitions): evaluated the index term that AdaptiveAssemblyFailure was carrying as an unevaluated `oracleProbability`,
making the assembly failure upper bound of the adaptive series a single constant. Essentially it is 2 `rfl`s —
`realized_run_proof_used` (the realized run's `used` is `defaultClaims`) and the chain comparison `raw_extended_no_clash_subset`
(the no-clash event of the extended shape is contained in that of the `22+5d` stages of the adopted strategic shape). The complement is charged only once, and
the result is `combinedBound + 2·tauTerm + indexStage(indexStage+1)/2/|Block|`, with no `oracleProbability` remaining on the right-hand side.
**Review discovered a vacuity going back to the adopted tree**: `adaptiveAssemblyFailureEvent` has acceptance as a conjunct
(the negation of an implication makes its antecedent `Integrated.verify … = .ok ()`). The adopted `Integrated.verify` ends in `Verifier.verify`
(`Integrated.lean:59-66`), which rejects unless `Verifier.shape pin c p = true` (`Verifier.lean:415`), and shape fixes
the 3 lengths of `p.used` to the configuration (`Verifier.lean:139-141`). However, the realized run's `used` is still the fixture's
`Verifier.testProof.used` (lengths `1, 1, 0`) (`Verifier.lean:596-600`, `RunLevelTransportAudit.lean:582-587`).
Therefore acceptance forces `numRouted = 0 ∧ numConstants = 1 ∧ numWires = 1`, and **for every other configuration the failure event is empty**,
so the upper bound, including the adopted AAF's closed instance `adaptive_assembly_bound_at_thirteen`, was vacuously true. `degreeBits` and `numPublicInputs` are
not fixed (`logRounds`/`gateRounds`/`publicInputs` are overwritten), and in the degenerate configuration `Verifier.width c = 1`, so
`constituentWidth := 1` gives no additional fixing. This module handled it in both directions. First, it records the vacuity as theorems
(`shape_forces_degenerate_config_at_fixture_claims`, `acceptance_forces_degenerate_config_at_fixture_claims`,
`adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`). Second, it removes the obstacle by making `used` a parameter:
`realizedRunProofWith u` **definitionally agrees** with the adopted `realizedRunProof` at `defaultClaims` and with the adopted `rawRealizedRun` at `constantClaims u`
(both `rfl`), so the adopted lemmas transport as they are, and the outer half needs no modification since it does not read `used`
(`outer_bad_event_at_claims`). The payoff is `shape_satisfiable_at_matching_claims` — at `matchingClaims c`, **all 5 `used` conjuncts** of shape
hold at `c` itself, and the length obstacle disappears. We do not claim that acceptance has been presented (the remaining shape conjuncts and
`Verifier.envelope` are explicitly left undecided). The adaptive prover's freedom is only the coupled round messages and the 5 statement fields;
`used`/`whirTranscript`/`whirHints`/`protocolVersion`/`constituentWidth` are fixture constants.

`Audit.Wire3.LocalizedCollisionMasses` (80 theorems / 19 definitions + 4 abbreviations): computed the ROM masses of the 2 localized collisions that CommittedTablesClauses left.
The collision mass of a fixed pair is **exactly** `1/|Block|` (`adaptive_fresh_step_card` itself is an equality with a singleton target;
the one-sided version is `fresh_coordinate_probability`). The degenerate branch really exists: since the ROM oracle's default value outside `Q` is `zeroDigest`, if both strings are outside `Q` the
mass is 1 (`degenerate_branch_has_mass_one`). **Review proved and returned a stronger theorem, which we adopted**:
the surrogate for the union is not a family `F` of configurations but **the query set**. Configurations whose encoded query falls inside `Q` are indexed by `Q.erase (configQuery c₀)`
with each term `≤ 1/|Block|`, and configurations falling outside `Q` collapse to **a single fixed event** by the off-`Q` default value. Hence
`any_config_collision_mass_le` bounds the mass that "**some** configuration collides with the deployed `c₀`" by `≤ (Q.card + 1)/|Block|` —
quantifying over all of `Verifier.Config` and naming no family at all. The only premise is `configQuery c₀ ∈ Q`.
`any_config_collision_mass_le_at_the_bounded_queries` substitutes `Q := boundedQueries L` and discharges the assumption with the existing
`config_query_mem_bounded_queries`, and the union term becomes a quantity owned by the adopted query-length model. The row side follows similarly
from `hR : R ⊆ Q`. The `F` version is left as a "coarse per-family reading", and we showed via `config_family_collision_event_subset_any` that it
can be discarded without loss. **A negative result is also recorded**: `joinFailureEvent` has `CanonicalProofCheck.DeployedFacts` as a
conjunct, and since its `pinnedDigest` field fixes the table coordinate to `configQuery c₀`, for **any** predicate `X`
`deployed_facts_alone_costs_the_whole_birthday_term` gives mass `≤ 1/|Block|`. Since the signboard holds even for `X := True`,
the number in `fixed_tables_costs_a_birthday_term` comes not from a birthday term but from the conditioning, and the substance of that clause lies on the side of the inclusion
`join_failure_event_subset`. R1b always remains an assumption, neither proved nor weakened nor supplied, the join is not claimed, and we do not claim that `joinFailureEvent` is
non-empty. `hc₀ : configQuery c₀ ∈ Q` is an **additional assumption** with no adopted counterpart (the adopted
`committed_tables_join_up_to_collisions` imposes no condition on the query-set side of khash).

This batch also corrected the wording of 2 adopted modules. `RunLevelTransportAudit`'s honesty item (vii) stated
"all of the following theorems read the proof only via `Verifier.statement` and `roundMessages` …… `Verifier.shape` is never asserted against it", but although this is true
for that module's own theorems, it **is broken downstream**. The breakage is of 2 kinds:
(a) fixture fields are read (AAF's `suppliedCellsAt` reads `p.used`), and (b) shape is asserted (the failure event has acceptance as a conjunct, and
acceptance implies shape). We fully replaced (vii) and stated that downstream modules that read fixture-inherited fields or assert shape/acceptance must
parameterize those fields or disclose the vacuity. We added a vacuity item to `AdaptiveAssemblyFailure` and stated that
the **inference itself** in `adaptive_payoff_hypotheses_satisfiable` — "therefore none of the above is vacuous" — is **invalid**
(satisfiability of the assumptions is not non-emptiness of the event that was upper-bounded).

The two modules together are 146 models / 5760 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
What remains is R1b (root determinacy of all columns), the true value of the circuit, the presentation of acceptance, and the joining for grinding provers.

## Continuation update #43 (after 9c52fd74)

With the tracked runner we re-checked the 146 models / 5760 theorems of commit `9c52fd74`, PASS (1001.957 seconds, 1476 modules,
manifest `4da8af10a07d7d36376d43c85863112e52f0c4e19939fd293c3e62bb6420f95a`, receipt
`595a8b2ff9be2ca8ba49a9cf3aa8e24b3a2bce2cc8d68479e1c90e50ddb5c480`, graph
`10ab26d5cd043f6b9096a619648f4e645ef28f0bff86034ca1949252dadf3fc2`).

As of this update, it is known that there are **2 independent causes of degeneracy** in the acceptance antecedent of the adaptive series.
The first is the fixture of the `used` claims (discovered by this batch's review): since shape fixes the lengths of the 3 claim lists to the configuration, it forces
`numWires = 1 ∧ numRouted = 0 ∧ numConstants = 1`. This was removed by IndexHalfTransport's `realizedRunProofWith` /
`matchingClaims`. The second is the trivial engine's index sampling, and this has not been removed:
`Verifier.testEngine.sampleIndices = fun _ _ _ => ⟨[], []⟩` (`Verifier.lean:605`), and while
`derivedIndices e c p = e.sampleIndices … c.indexBits` (`:389-391`), `verify` rejects unless
`idx.log.length = c.indexBits ∧ idx.gate.length = c.indexBits` (`:420-421`), so `c.indexBits = 0` is forced.
However, `envelope` requires `width c ≤ 2 ^ c.indexBits` (`:104`, checked at `:413`), so `indexBits = 0 ⇒ width c ≤ 1 ⇒ numWires ≤ 1`,
reaching the same degeneracy without touching `used` at all. Therefore, presenting acceptance at a non-degenerate configuration requires **both** a parameterized `used` record and
an engine returning lists of length `c.indexBits`. Since `sampleIndices` receives `c.indexBits` as an argument,
the second cause is expected to come off cheaply for a model engine. The only adopted acceptance instance, `positive_model_verification`
(`Verifier.lean:612`), holds at `testConfig` (degreeBits 1, numWires 1, indexBits 0), and acceptance at the explicit engine
(`SoundnessAssembly.engine`) is a goal of a different order requiring the WHIR tail and gate evaluation.

## Continuation update #44 (after 9c52fd74)

In iteration 28 we adopted the presentation of acceptance and the lane pairing for grinding provers. Both went through adversarial review by Opus, and
**both reviews proved and returned theorems stronger than the modules themselves, while at the same time pointing out errors**.

`Audit.Wire3.NonDegenerateAcceptance` (68 theorems / 15 definitions): as of continuation update #43 we thought there were 2 reasons why the acceptance antecedent of the adaptive series was
unsatisfiable at a realistic configuration, but **there were actually 4**. (1) the fixture of `used`, (2) the trivial engine's index sampling,
(3) the fixture's `initialObservation` returning 1-element `logTau`/`gateTau` (since `verify` rejects unless `i.logTau.length = c.degreeBits`
(`Verifier.lean:420`), `degreeBits = 1` is forced), and (4) on the integrated path, `Norm.checkedNormEvaluation` requires
`logChallenges.length = 7` (`Norm.lean:353`) while the fixture's list is empty, so
`Integrated.verify Verifier.testEngine … = .error .configuration` holds **unconditionally**. (4) is a stronger fact than any previously known cause.
(1)(2)(3) were turned into theorems for any engine, pin, chain, configuration, and proof.

The payoff is `model_acceptance_at_the_maximal_config` (`rfl`). The engine fields moved are **only 2**, `sampleIndices` and `initialObservation`, and
`Verifier.verify` accepts at the configuration `degreeBits 13`, `numConstants 80`, `numRouted 80`, `numWires 160`, `numSelectors 4`, `numGateConstraints 123`,
`quotientDegree 8`, `gateRows 255`, `indexBits 8` (width 160) — **exactly the upper limits of `Verifier.envelope`**.
`degreeBits + indexBits = 21` exactly matches `PinnedWhirProfile.maxProfileVariables`.
This instance is at the same time a **constructive** proof that none of the fixture fields left unmoved fixes a configuration quantity inside `Verifier.verify`, and
is stronger than a field-by-field enumeration. We newly created the **constructor** `verify_of_checks` corresponding to the destructor `Verifier.verify_success_checks` in the adopted tree,
and with it also gave parametric acceptance for all WHIR transcripts / hint sequences within the limits. `Integrated.verify` also
reaches up to 15 wires with the same engine and the same surrogate decoder.

The limitations are strict. These are model engines, not the adopted `SoundnessAssembly.engine`. Of the 9 gates of `Verifier.verify`,
in §5 **only 3 actually compute** (envelope, shape, tau/index lengths), and 6 are fiat (chainId, `configurationHash` is the constant `testRoot`,
`deploymentValid` is the constant `true`, the log/gate terminals are the constant `zero` for any arguments, and `whirTail` is the constant `true`). Moreover there are
2 degeneracies that do not look at any gate: the derived transcript is **the empty byte sequence** for any configuration and proof, so this instance has no Fiat–Shamir dependence at all.
Also, the repaired sampler returns **all-zero index points** — what was repaired is the **length** of the lanes, not their **contents**. In §6, 7 of the 11 gates
actually compute, `normResult` and `gateResult` are actually computed, and with a zero norm helper it actually failed (which is why `Norm.one` appears), but
that WHIR gate is unfalsifiable by construction (the echoing `parseWhir` makes `verifyWhir` true for any context and any proof).
Therefore this module does not make the adopted `AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent` non-empty, and does not lift
the vacuity recorded by `IndexHalfTransport`. The claim is limited to "**the length fixing of `Verifier.shape` and `Verifier.envelope` alone
no longer make acceptance at a non-degenerate configuration impossible**". We also do not claim to localize the remaining obstacles for the explicit engine:
its `deploymentValid` (`PinnedWhirProfile.canonicalProfileCheck`) contains the **numeric** constraint `1 ≤ numVariables ≤ 21`, which is
arithmetic of the same kind as the envelope. Review enumerated the breakdown of the 9 gates and pointed out **2 false claims** — "proved independently" (in fact a definitional transcription of adopted theorems,
adding nothing to the adopted tree) and "a parametric version cannot be produced because it exceeds Lean's recursion depth" — and made them withdrawn.
The latter was refuted by the reviewer itself proving it without `set_option`. **A negative claim that Lean cannot prove something is not checked
by the kernel** — "my script did not close it" is evidence about the script, not evidence about provability.

`Audit.Wire3.GrindLanePairing` (102 theorems / 15 definitions): closed the 2 holes that the adopted `GrindingUnionBound` itself stated as "not provided".
**(A) Identity at q=0**: a grinding prover that performs no probes agrees with the adopted raw strategy, and from GUB's heading the adopted
`RawBlockLanes.raw_full_bad_draw_probability_le_combined` **is derived** (the collision term collapses to `(22+5d)(0+1) = 22+5d`).
The agreement of the no-clash events is not a congruence: the adopted `stageNoClash` is the `noClash` of the chain's `n` **answer blocks** plus an `avoidBase` clause, whereas
`grindingNoClash` is pairwise distinctness of `n+1` **stage digests**, and the two agree only via an index shift and the injectivity of `digestBlock`.
That this reduction is not circular was confirmed by a **transitive constant dependency scan** over the stored proof terms: it does not reach the adopted raw upper bound, and
does reach GUB's heading (the only `RawBlockLanes` constant it touches is `rawFullBadEvent`, which appears in the statement).
**(B) Pairing**: via `elementOfBytes`, a totalization of the adopted partial decoder `Spongefish.decodeCanonicalExt3`, we showed
that the lane's round `r` message is **exactly** the absorbed payload at the grinder's stage `22+5r`. It is the content of the byte sequence the run actually asks about,
not a re-encoding. Moreover **no conditioning event is needed**: the sequence at stage `j` is a pullback of the oracle along the stage-`j` digest (`rfl`), and
even if digests collide no information is lost (structurally different from a hash collision). The type mismatch between digest indices and stage indices is
closed by definition through the totality of `digestLookup`, but its **correctness** is carried by `grinder_table_view_determined`, and we also showed by counterexample that this is
essential.

The scope of application was pinned down exactly: grinders that are `ChallengeRestricted` and whose absorbed payload at every stage is at most `min 120 (24*(quo+2))` bytes.
At the adopted `quo = 8` this is 120 bytes, i.e. **5 encoded elements**, and the budget is exactly the adopted degree budget. The `longMessageGrinder` that absorbs 6
is exactly 1 element outside, and nothing is bounded for the mass of its paired lane. The payload upper bound is needed **only at the joining stages**, and
`mixedGrinder`, which absorbs 144 bytes at a non-joining stage, is excluded under a uniform assumption and covered under a joining-stage-only assumption — realistic provers that absorb WHIR Merkle roots or
the final polynomial at non-joining stages fall into this. We also record **a restriction larger than the byte budget**: since the message `grinderLane` puts in is
the unique payload of stage `22+5r`, the log lane and the gate lane carry **the same** round message. In the protocol these two are separate
coupled prover messages. `truth` and `claim` remain free, just as in the adopted `RawBlockLanes`. The decoder's agreement with the adopted partial decoder is
**one-directional**, and outside its domain (length exactly 24 and all 3 limbs less than the modulus) the totalization invents values:
2 different payloads that the deployed parser rejects yield the same non-empty message. This is conservative and not unsound, but
the lane message outside the domain is a modeling choice and not the verifier's reading. `selectorGrinder` is **not an attack**:
it merely reads probe 0 and branches to 2 constant messages, with no re-search and no search (GUB itself says the same about its own `probeGrinder`).
What excludes the searching prover `preReadGrinder` is not the byte budget but `ChallengeRestricted`, and
GUB's pre-read hole remains as it is.

The two modules together are 148 models / 5930 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
What remains is R1b (root determinacy of all columns), the true value of the circuit, acceptance at the explicit engine, and the charging of Fiat–Shamir challenge grinding.

## Continuation update #45 (after d0f31900)

With the tracked runner we re-checked the 148 models / 5930 theorems of commit `d0f31900`, PASS (997.077 seconds, 1478 modules,
manifest `5a9f257ef5c0cd88f5b0182aa54df1bca5639a09d90ae71b1480453adaa41c5e`, receipt
`eb84d036965584f4e411e8587db562c73f9234e5989045fc18e08c6fb78636c6`, graph
`8d2eb3616f040965d20fbcaef6c4e6843e832f37887506515e64e16976c93017`).

As of this update, acceptance is presented at the envelope's upper-limit configuration, but **what was repaired is the lanes' length, not the lanes' contents**.
The derived transcript of the acceptance instance is the empty byte sequence for any configuration and proof, with no Fiat–Shamir dependence at all. Also, the index sampler
returns all-zero index points. Therefore the next substantive step is to re-derive acceptance with an engine (not necessarily the explicit engine) in which
`initialTranscript` and `sampleIndices` are genuine functions of the proof, and only then does acceptance at the explicit engine, requiring the WHIR tail and actual gate evaluation, come
into range. The numeric part of the explicit engine's `deploymentValid` (`1 ≤ degreeBits + indexBits ≤ 21`) is known to be satisfiable at the upper-limit configuration.

## Continuation update #46 (after d0f31900)

In iteration 29 we pushed the acceptance instance up to the explicit engine and split the grinding lane pairing into 2. Both went through adversarial review by Opus, and
**both reviews proved and returned results stronger than the modules themselves, while at the same time pointing out errors**.

`Audit.Wire3.DerivedAcceptance` (104 theorems / 16 definitions): continuation update #45 stated "what was repaired is the lanes' length, not the lanes' contents".
This module resolves that. The accepting engine is `ExplicitEngine.explicitEngine` with **only 2 fields**, `parseWhir` and `whirTail`, returned to
the fixture, and this holds by `rfl` (`derived_engine_is_the_explicit_engine_minus_the_whir_pair`). 10 of the 12 fields are
adopted real components. The heading `derived_acceptance` **universally quantifies** `thash` and `khash` and uses no property of the hash at all.
A version via `Integrated.verify` also holds. The dependence is recorded by 4 theorems. Among them, `derived_transcript_depends_on_the_proof` is
shipped in the form "or `thash` collides", and records **positively**, by a witness, that the unconditional version is **refuted** by `constantHash`
(a practice for not writing a negation as a claim; review rated this the best disclosure practice in this audit).

**The honest gate count is 4 out of 9.** The only ones with arithmetic that could actually fail are (3) envelope, (5) shape, (6) tau/index lengths, and (9) gate dispatcher.
(2) and (4) close by `rfl`: since `derivedPin` is **defined** as `khash (encodeConfig derivedConfig)`, the configuration-hash gate cannot
fail, and the deployment pin is reflexive at `c = derivedConfig`. Moreover, (2)'s bindingness has **a loophole inside this module's own quantifier**:
with a constant `khash`, a pin computed from `derivedConfig` accepts **a different configuration**. (7), because `numRouted = 0`, runs `Norm.runWires`
0 times, so none of `denominatorTerms`, `formalNorm`, `formalAdjugate`, the logup pairs, or the λ ladder is executed. As a result the terminal is
zero for **any** observation, point, or claim record, and **no two proofs can be distinguished** — something that cannot distinguish 2 proofs is not a guard.
(9) actually runs but is minimal (1 of the 14 gate families, 2 of the 255 rows, 1 of the 123 constraints). Universal quantification is logically stronger than any instantiation, but
at the same time it makes the hash-dependent gates **non-binding**. "For every transcript and configuration hash" is a claim about the generality of acceptance,
not a claim about the strength of the guards.

The configuration reaches `degreeBits 13`, `numWires 160`, `numConstants 80`, `indexBits 8`, `quotientDegree 8` (the envelope upper limits, equivalent to the adopted
`maximalConfig`), but **`numRouted = 0`**. This is a **regression** to one of the 3 pins forced by the original degeneracy
(`numWires = 1 ∧ numRouted = 0 ∧ numConstants = 1`), returning to the very degeneracy the adopted tree had specifically repaired.
Therefore **this instance does not dominate the adopted `maximalConfig`, and the two are incomparable**. This module is superior in the engine, and the adopted instance is superior in
`numRouted`, `numSelectors`, `numGateConstraints`, and `gateRows`. One cannot combine the two to draw a conclusion.
Review also showed that the regression is in fact an **overstatement**: with the same engine and the same all-zero claim record, acceptance was re-presented at `numPublicInputs = 3`
and at `quotientDegree = 8`, and the latter was incorporated into `derivedConfig` itself. What the real components force is only `numRouted = 0`;
`numPublicInputs = 0` applies only to `Integrated.verify`, and moreover is forced as a **downstream consequence** of `numRouted = 0`
(`Norm.shapeValid`'s `column < c.numRouted` is unsatisfiable at 0). `gateRows`, `numSelectors`, and `numGateConstraints` come from
the **surrogate decoder**, not from the real components.

Acceptance at `numRouted = 1` was made a **theorem** rather than "no instance was found": with the all-zero sequences of `matchingClaims`,
`idHelper = sigmaHelper = 0`, hence `idZero = sigmaZero = -1` and `logupSum = 0`, so the terminal is `eq(τ,point)·(-(1+ρ))` and is not
identically zero. Hence acceptance is **equivalent to an accidental coincidence among the derived challenges**. The loophole (a non-zero sequence inverting `denominatorTerms.1`) is blocked because
gate 8 forces `packedFold p.used.logNormInverse (width c) idx.log = zero` at the derived index point, and repairing it requires
a non-zero sequence whose packed fold vanishes at a `thash`-dependent point.

The only remaining obstacle is the WHIR parse/tail. In the adopted tree there **do exist** concrete `rfl` success instances of `WhirConfigured.run` called by
`InstalledWhirTail.tailRun` (`WhirConfigured.lean:637,646`, `WhirTail.lean:902,921`). However, they run with mask `[⟨7⟩]` and 3 claims, whereas
`tailRun`'s mask is fixed to `[⟨31⟩]` and this context carries 5 claims, so they **cannot be reused**. We named the missing lemmas. In addition we record an important tension:
since `WhirInitial.readClaims` binds the transcript to the verifier's own `packedFold` value (the value at the derived index point),
such a witness is `thash`-dependent, and **a WHIR-complete instance cannot preserve this module's universal quantification over `thash`**.
This module does not make the adopted `AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent` non-empty, nor does it lift the vacuity recorded by
`IndexHalfTransport`. That event is indexed by **both** the explicit engine and the fixture used-claims, and since this module uses `matchingClaims`
and the WHIR pair is the fixture's, it **misses both indices**.

`Audit.Wire3.TwoLaneMessages` (91 theorems / 13 definitions): removes honesty item (v) of the adopted `GrindLanePairing`. However, the most important content this module
carries is a **discovery about the adopted grinding model**. In the transcript chain the 2 coupled cells are separate absorbs
(`BirthdayClashBound.roundShapeAt`'s frame 2 is the LOG at stage `22+(5r+2)`, and frame 3 is the GATE at `22+(5r+3)`), yet at the lane layer both are
projections of the same `S r ch : CoupledMessage`. And `GrindCausal`'s cut **lets the lane of round `r` read neither cell stage**.
Therefore the grinding line is at a **strictly coarser granularity** than the protocol, and no way of splitting the single payload fixes this — a split can only
model it. The missing lemma is a GUB heading cutting at `roundStage r * (q+1)`, and since GUB's own note records that
`grind_run_view_reassign_lower` needs only `22+5r < j`, the diagonal stage survives. We also identified which part of the cut is effective:
the history side permits stage `22+5r+1`, and it is the challenge side (`digestLookup`), and for `0 < q` also the probe side, that forces the cut.

The split itself is `logHalf = take 120` / `gateHalf = drop 120`, and the pairing of both lanes is proved for all tables **with no conditioning event**.
`hfitlog` **disappears** (the log-side half is at most 120 bytes by construction), and the budget **rises** to `p ≤ 360` (from 5 elements to 15, since the halves are coprime to each other).
The constants are identical term by term with GLP, and the joining-stage-only `hp` is maintained. **However, the 2 lanes separate only above 120 bytes.**
Below that, the gate-side message becomes **empty**, that is, over the entire class GLP covers (including GLP's own witness), the 2 lanes differ because
the gate side is **silenced**, not because a second protocol message is given. An empty gate cell is not a legal round message
(acceptance implies the gate round has length `quotientDegree + 2` and the log round has length 5). Both become legal lengths only at exactly 360 bytes,
and we also produced a closed instance there. This length illegality is **inherited** from GLP and was not opened by this module (`GrindLaneBounded` is `≤`).
The negation about causality was corrected to an **existential rather than a universal** claim: with `blindGrinder` it is causal for every stage function, so
the universal claim that a lane reading a later stage is non-causal is false. The existential form suffices to show that a uniform construction cannot be passed to the adopted heading, and the obstacle is not an artifact of a particular
offset either (all stages 24 and above, including the gate cell's own stage). The witness does not search (we turned into a theorem that it is a function of the answer to probe 0 only).

The two modules together are 150 models / 6125 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
What remains is a success witness for the WHIR tail, R1b (root determinacy of all columns), the true value of the circuit, acceptance at `numRouted > 0`, and the charging of Fiat–Shamir
challenge grinding.

## Continuation update #47 (after 175c8a4e)

With the tracked runner we re-checked the 150 models / 6125 theorems of commit `175c8a4e`, PASS (1340.382 seconds, 1480 modules,
manifest `55fc196a60662092fcdd3f40c68b8570f716a5b6629df39fa26c07e8c682f773`, receipt
`e6288e36a10df0e5736f29ac0957ea34208e01935845f1837fec7c4f9f3469d4`, graph
`36e5aea3a308a618d6f68274883f857edd23da4d028183e47699712f1f298823`).

As of this update, the only obstacle remaining on the acceptance line is **the WHIR parse/tail alone**. The next step is its success witness, namely
`InstalledWhirTail.tailRun … .isSome = true` in a context with mask `[⟨31⟩]` carrying 5 claims (the dual of `= none` at `InstalledWhirTail.lean:1122-1130`).
The known obstacles are strict EOF of both streams (`WhirFinal.exhausted`), that the 3 pinned roots appear literally in the transcript and
pass `Merkle.verify`, and that the actual PoW threshold of the deployment profile requires an actual nonce.
**There is a tension that should be recorded in advance**: since `WhirInitial.readClaims` binds the transcript to the verifier's own `packedFold` value
(the value at the derived index point), such a witness will necessarily be `thash`-dependent. Therefore a WHIR-complete instance **cannot preserve**
DerivedAcceptance's universal quantification over `thash`. In the next iteration we will have to choose which of the two to take, and to make that choice explicit.

Iteration 30 took both, and recorded which was taken as a theorem.

`Audit.Wire3.WhirTailWitness` (56 theorems / 11 definitions): the first concrete demonstration of WHIR success at the installed level. All adopted concrete evaluations were
negative (`InstalledWhirTail.example_empty_hints_fail_the_concrete_tail`'s `tailRun = none`,
`InstalledWhirParse.example_concrete_parse_rejects_the_empty_transcript`). Success existed only as a hypothesis or as an existential conclusion of an acceptance premise.

**Stages 1–2.** At 3 claims, `installed_tail_succeeds_on_a_concrete_transcript` and `witness_verify_whir_is_true` produce
`InstalledWhirTail.tailRun … .isSome = true` and `Verifier.verifyWhir = true`. At 6 claims (the deployed arity of `Verifier.expectedClaims`),
`configured_six_claim_execution_example` produces the success of `WhirConfigured.run` by `rfl` (408 transcript bytes, 72 hint bytes,
exact EOF on both streams. The layout is 192 zero bytes of commitment authentication + 144 bytes of 6 claims + initial sumcheck `(1,0)` + terminal vector `1`).
`installed_tail_succeeds_at_a_six_claim_context` / `six_verify_whir_is_true` lift it to `tailRun` and `verifyWhir`.
By `six_context_is_the_derived_context_of_the_installed_engine`, the 6-claim context is exactly the `derivedContext` that the outer verifier derives over `Verifier.testConfig`, and
`installed_whir_gate_is_true_at_its_own_derived_context` has the engine's own WHIR gate return `true` rather than a hand-passed context.

**Stage 3.** `installed_whir_pair_accepts_a_full_verification` produces by `rfl`
`Verifier.verify (sixEngine …) ⟨1, testRoot, testRoot⟩ 1 Verifier.testConfig sixProof = .ok ()` with both `parseWhir` and `whirTail` installed.
We narrowed `set_option maxRecDepth 8192` / `maxHeartbeats 1000000` to that declaration alone (adopted theorems of the same kind are 65536).

**Correction of a premise.** The mask `[⟨31⟩]` versus `[⟨7⟩]` is not a blocker. `WhirInitial.readClaims` looks only at `0..expected.length-1`, and
they agree bitwise at 0,1,2 (`the_two_masks_agree_below_three`). `configured_run_mask_congruent` is the general form, showing that the mask
enters `WhirConfigured.run` only via `checkBound`'s length guard and `readClaims`. The real obstacle is the claim count, and
`the_two_masks_do_not_agree_below_six` shows the agreement breaks at 6 claims, while `configured_six_claim_execution_example` circumvents it.

**This is not acceptance at the explicit engine.** `accepting_engine_field_ledger` enumerates the fields: `sixEngine` is `testEngine` with
`parseWhir` / `whirTail` / `commitRound` / `sampleIndices` placed on it, and `foldClaim`, `normEvaluation`, and `eqEvaluation` are also concrete, but
the 4 fields `initialObservation`, `publicInputsHash`, `configurationHash`, and `deploymentValid` remain abstract observations. This is the
**complement** of `DerivedAcceptance` (10 concrete fields, WHIR pair from the fixture), and neither is all 12 fields.
The configuration is `Verifier.testConfig` (`degreeBits = 1`, `indexBits = 0`), not `DerivedAcceptance.derivedConfig` (21 variables)
(`the_accepting_configuration_is_not_the_derived_one`). The hash is a constant toy (`the_witness_hash_is_constant`,
`the_witness_hash_ignores_every_input`: an additional 72 bytes of claims cannot move the sponge digest).
The profile is `exampleNoRounds` (all PoW thresholds are `maxCounter`. `the_witness_profile_is_not_the_deployed_shape`).
`thash` is universally quantified together with `e` and `gdec` in the supplied-context statements (`witness_verify_whir_is_true` / `six_verify_whir_is_true`), and
in the derived context it is instantiated to `InstalledRoundCommit.toyHash`. A 21-variable witness is not constructed, and is not claimed impossible.
Adversarial review was PASS-WITH-FIXES (write NOT derivedConfig / NOT explicitEngine first in the heading,
and add `the_witness_hash_ignores_every_input`).

`Audit.Wire3.RoutedAcceptance` (111 theorems / 13 definitions): shows acceptance at `numRouted = 80` (the envelope upper limit, equivalent to the adopted `maximalConfig`),
keeping the adopted `DerivedAcceptance.derivedEngine` and the adopted `IndexHalfTransport.matchingClaims` unchanged. The heading is

    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash P) (routedPin khash) 1
      routedConfig routedProof = .ok ()

(`routed_acceptance`. `khash` and the profile `P` are universally quantified, the latter under the `profileOk` hypothesis. The hypothesis is discharged with a stand-in and with the sharp profile:
`routed_acceptance_at_the_profile_witness` / `routed_acceptance_at_the_sharp_profile`). There is also an `Integrated.verify` version
(`routed_integrated_acceptance`). `routedConfig` is `derivedConfig` with only `numRouted` moved 0→80 and `kIs` aligned, with
no other fields moved (`routed_config_agrees_with_the_derived_config_off_the_routed_wires`).
The second instance with `numPublicInputs = 3` (`routedPublicConfig`) is possible only with `numRouted > 0`, and `routed_public_targets_are_in_range` discharges
`Norm.shapeValid`'s `column < numRouted`.

The route is (b): eliminate the second factor `1+ρ` of the adopted `probe_acceptance_at_one_routed_wire_forces_a_challenge_coincidence`.
`routedHash` looks only at the last 8 bytes of the challenge input (the counter), returning `modulus-1` at counter 3, 0 at 4 and 5, and 2 otherwise.
Since counters 3,4,5 of the relation state are `ρ`, for every configuration and statement `ρ = -1` (`routed_rho_is_minus_one`).
The digest chain is not evaluated. Route (a) (a non-zero norm-inverse sequence folding to 0 at the derived index point) has not been found and is not claimed impossible.

Gate 7 executes an 80-iteration wire loop (`routed_wire_loop_runs_eighty_times`), 160 `denominatorTerms`, and an 80-stage λ ladder
(`routed_lambda_ladder_runs`). The assembly is gate by gate with `NonDegenerateAcceptance.verify_of_checks`, with no `set_option`.

**However, this is not the removal of the last degenerate pin.** Facts confirmed by adversarial review (PARTIAL; the heading's reading "last pin removed" is false) and
adopted into the module: `routed_hash_is_a_transcript_collision` (since it ignores the digest, different digests at the same counter collide),
`rho_ignores_the_statement`, and `routed_lambda_is_two_everywhere` / `routed_kappa_is_two_everywhere` /
`routed_beta_is_two_everywhere` (all universally quantified over configuration and statement, so the derived challenges do not depend on the statement),
`alt_proof_is_also_accepted` (a second proof differing only in `normInverseRoot` is also accepted. What `Verifier.shape` pins is
only `preprocessedRoot`). `dependence_implication_holds_because_the_hash_collides` shows that the collision disjunct of the adopted dependence implication is true here.
The same degenerate hash family that `DerivedAcceptance` used as a **refuting witness** for dependence, this module uses as the
**accepting hash**. **Heading: the acceptance line does not yet have both routed wires and proof-dependent challenges.**
The 3 instances are all incomparable: derived quantifies over `thash` universally, while this instance uses a collapsing hash for acceptance. maximal uses the fixture engine and is superior in
`numSelectors`/`numGateConstraints`/`gateRows`. The WHIR pair is still the fixture's. Gate 2 still closes by `rfl` because `routedPin` is defined from `khash`.

The two modules together are 152 models / 6292 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
What remains is a 21-variable WHIR success witness (connection to derivedConfig), `numRouted > 0` with a `thash` that actually uses the digest,
a concrete rejection instance in which gate 7 distinguishes 2 proofs, R1b (root determinacy of all columns), the true value of the circuit, and the charging of Fiat–Shamir
challenge grinding.

## Continuation update #48 (after 84e7c54c)

With the tracked runner we re-checked the 152 models / 6292 theorems of commit `84e7c54c`, PASS (1054.723 seconds, 1482 modules,
manifest `fdeb30545b31e6e7387c0eaea9789c11a3e60e0b8a990ca3e18855abfdb26469`, receipt
`1762988f8561a9e65fa340383a3ed2eda1b56d6c004dbdb87c1d8e62ce0a6d06`, graph
`7be1b47866c711e4c5f9d813917ed8cc00167bd2125c64ea657b7682cf3b1854`).

As of this update, the acceptance line does not have both routed wires and proof-dependent challenges.
The theorem names, stages, engine fields, and hash definitions of batch 40 were written in continuation update #47 and in the most recent table of "Entry points of the main theorems".
WHIR success was made concrete at the installed level, but the configuration is `Verifier.testConfig` (1 variable), the hash is a constant toy, and
the connection to `DerivedAcceptance.derivedConfig` (21 variables) is not constructed. The next steps are `numRouted > 0` with a
`thash` that actually uses the digest, a concrete rejection instance in which gate 7 distinguishes 2 proofs, a 21-variable WHIR success witness,
R1b, the true value of the circuit, and the charging of Fiat–Shamir challenge grinding.

## Continuation update #49 (after 057d4b98)

Iteration 31 was a single candidate following the user's instruction (actually repair RoutedAcceptance's trade), and we adopted
`Audit.Wire3.DigestRoutedAcceptance` (119 theorems / 12 definitions). It went through adversarial review by Opus, and
the review confirmed that the core of the repair is genuine, while pointing out 3 calibration defects in the prose and having them corrected.

**Content of the repair.** `fixedHash` domain-separates the frame and challenge inputs using the fact that the adopted `framePrefix` (length 20) and
`challengePrefix` (length 24) differ at byte 15 (`challenge_mark`/`frame_mark` are `rfl` for any digest, tag, payload, and counter).
On the challenge side, only counters 3/4/5 are fixed (ρ = −1, which the vanishing argument of acceptance requires, and its neighboring values); otherwise `mixFrom` actually reads the digest.
The frame side always reads the digest. During design 2 facts were established: (i) the body of the old `routedHash`'s degeneracy is on the frame side, and
since essentially every frame maps to the constant `twoDigest`, **the whole chain was constant** (`routed_hash_on_a_long_frame`. It was also proved that round 3's
commit frame exceptionally collapses to `minusOneDigest`). (ii) If one branches only on the counter encoding, then since the last 8 bytes of `le 8 round` that `commitRound`
absorbs are exactly `counterTag round`, the chain collapses at rounds 3–5 — the byte-15 discriminator is
not decoration but necessary.

**Heading `fixed_acceptance`**: with the adopted `routedConfig`, `routedProof`, `routedPin`, and `matchingClaims` all unchanged and
only the hash replaced, `Verifier.verify` accepts at `numRouted = 80`. `khash` and the profile `P` are universally quantified (discharged at both the stand-in and the sharp profile),
and the `Integrated.verify` version and the `numPublicInputs = 3` configuration are also inherited. The assembly is gate by gate with `verify_of_checks`, with no `set_option`.

**A contrasting theorem pair showing the repair is genuine**: with the old hash, the derived initial transcripts of `routedProof` and of `altProof`, which differs only in
`normInverseRoot`, **agree** (`routed_initial_transcripts_do_not_separate_the_two_proofs`), whereas with the new hash they **separate**
(`fixed_initial_transcript_separates_the_two_proofs`, for any configuration, `khash`, and `P`). Digest injectivity is a theorem on both branches
(`fixed_hash_is_injective_in_the_digest`, `frame_hash_is_injective_in_the_digest` — mixByte is left-cancellable as addition mod 256, and
`clip 31` is applied to a list of exactly 31 bytes and loses no information. Verified by review).

**Ledger of residues (confirmed "correct" by review's verification)**: of the 102 derive + 78 round + 48 index = 228 squeezes,
the digest-blind ones are the 48 at counters 3/4/5 (ρ, γ, and 3/4/5 of each stage), and 180 read the chain (old `routedHash`: 0/228).
The first 2 sums were turned into theorems (`derive_squeeze_counts`, `a_round_squeezes_six_from_counter_zero`). The description of counter blindness is
scoped to the 8-byte LE encoding: `counterTag (2^64+3) = counterTag 3` (since `le 8` is mod 2^64), but that alias is
unreachable outside the counter range of the squeezes (`the_aliased_counter_is_out_of_squeeze_range`).

**The chain state is one byte wide (disclosed with heading weight)**: `mixFrom` reads 32 bytes but writes only 1, and the last 31 bytes
carry over those of the input digest. Since the start state is all zero, for any configuration and statement the derived chain's digests are 1 variable byte +
31 zero bytes (`derive_digest_tail_is_thirty_one_zero_bytes`) — the chain passes through at most **256** digests.
"180 of 228 read the chain" means they read that 1-byte state. What was restored is the **structure** of Fiat–Shamir dependence
(which challenge is a function of which absorb), not quantitative collision resistance (we deliberately proved
`fixed_hash_is_still_a_transcript_collision` and do not claim collision freeness).

**The separation is fold-specific (placed right next to the contrasting pair)**: the separation theorem is a fact about the single pair fold 34 versus 35. For a pair with equal folds
(`normInverseRoot` 1 and 256, both fold 35), the entire derived initial transcript agrees even under the new hash
(`fixed_hash_does_not_separate_the_other_root_pair`). Which pairs separate is a property of the 1-byte fold, not a property of the
distinctness of the statements.

**Honest negatives**: `alt_proof_is_still_accepted` — gate 7 reads only the norm-inverse sequence (zero in both proofs) and ρ (−1 in both), and
gate 8 should compare `normInverseRoot`, but the fixture's `parseWhir` echoes the context roots
(`fixture_parse_echoes_the_context_roots`). Separating the 2 proofs requires route (a) (a non-zero norm-inverse sequence) or the installed WHIR parse —
neither constructed nor claimed impossible.

**Trade ledger**: strictly better than RoutedAcceptance in the hash and identical otherwise (`same_instance_as_the_adopted_routed_acceptance`,
all `rfl`). Still incomparable with DerivedAcceptance (`thash` is instantiated here and universally quantified there — we state with heading weight that that quantifier is still a price).
The maximalConfig ledger is re-exported as is. **Nowhere is it written that the last degenerate pin has been removed**:
the honest claim is "routed wires and (180 of 228) proof-dependent challenges have become compatible, naming the remaining 48 squeezes, the 1-byte state width, and
the fixture WHIR pair".

With 1 module, 153 models / 6411 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
What remains is a hash with a wider state (or concrete chain programming that also removes ρ's blindness), a concrete rejection instance in which gate 7 distinguishes 2 proofs
(route (a) or the installed WHIR parse), a 21-variable WHIR success witness, R1b, the true value of the circuit, and
the charging of Fiat–Shamir challenge grinding.

## Continuation update #50 (after c0572083)

With the tracked runner we re-checked the 153 models / 6411 theorems of commit `c0572083`, PASS (1018.227 seconds, 1483 modules,
manifest `898d80048d4b1ef366f5f401053ea9c130f80eab38d16eb47901b442022c8476`, receipt
`a42b3766ced743fb5efd8c2990495aa78e70dda143b4535787c3f3f46866c169`, graph
`b5bd65577bee19cab4d8b751e5947749102e344b0719583a93eb8d96d233ca5c`).

As of this update, the honesty arc of the acceptance line is at the following stage: the verifier **executes** (done), the verifier **depends** on the proof
(done — but the chain state is 1 byte wide, and what was restored is the structure of Fiat–Shamir dependence, not quantitative collision resistance),
the verifier **rejects** a wrong proof (not achieved). The next step is that last one — separating 2 concrete proofs via route (a) (a non-zero
norm-inverse sequence whose packed fold vanishes at the derived index point) or via the installed WHIR parse — together with a hash with a wider state,
a 21-variable WHIR success witness, R1b, the true value of the circuit, and the charging of Fiat–Shamir challenge grinding.

## Continuation update #51 (after c7d285b0)

Iteration 32 was 3 candidates in parallel following the user's instruction (finish the 3 proofs that are "practically necessary"), and all went through adversarial review and repair by Opus.
The policy was settled with the user: the mathematics of the WHIR protocol is underwritten by the literature, and the Lean audit is responsible for implementation faithfulness.

`Audit.Wire3.RejectionWitness` (29 theorems / 7 definitions): **the first rejection theorem in this tree.**
`installed_engine_rejects_the_wrong_root_proof` shows by `rfl` that, with WhirTailWitness's `sixEngine` (both parse and tail being the adopted real installations),
a forged proof changing only `sixProof`'s `normInverseRoot` becomes `.error .invalidProof`. A locator theorem identifies in a single conjunction
that all other gates of `Verifier.verify` pass, and that the failure is the WHIR gate and, inside it, parse's root comparison
(the installed parse compares the literal commitment bytes of the transcript against the context's root — the fixture's parse
echoes the context's root, which was the cause of DigestRoutedAcceptance's `alt_proof_is_still_accepted`). The absence of confounding is a theorem:
of the arguments reaching `runPrefix`, everything other than the root list is literally identical to the accepting case, and putting the root back revives parse. It also rejects with the other
non-pinned root (`witnessRoot`), and the fixture pair accepts that too. **The attribution was sharpened by review**: each half of the WHIR pair,
even on its own, rejects the forged proof and accepts the honest proof (4 half-install theorems), and accepting the forgery requires both halves to be fixture.
As a quantified version, we also showed that for any proof accepted by this engine, the roots read (actual and bound) are fixed to
the digests of `[testRoot, p.witnessRoot, p.normInverseRoot]` (`rootDigest` is injective).
The r-family form (rejection over the whole range of root values) is not achieved, and we named the missing lemma: `WhirInitial.receiveOne` forces expected = root, but
`receive_one_success` does not export that byte equality. Scope: `Verifier.testConfig` (1 variable), a constant toy hash,
4 fields remaining abstract observations, and a statement about the model of the installed parse, not about the deployed Solidity.

`Audit.Wire3.R1bBridge` (28 theorems / 15 definitions + 2 structures): closes R1b (the `rootDetermined` clause) **as a bridge rather than a proof**.
The first version placed the no-collision requirement inside the structure with a ∀-quantification over all executions, but **that form was refuted by review with `decide` on this tree's own depth-1 fixture**
(`Merkle.exampleHash` is `take 32`, and the compression input at odd index 1 is `sibling ++ current` — a depth-1 root does not depend on the leaf, a second row opens to the same root, and
the execution inputs of 2 runs collide). The repaired form is the computationally correct scope:
`RunPairNoCollision r₁ r₂` (no collision on the inputs that **the 2 runs being compared** actually hashed. The `Run` structure exposes hints/start —
existential hiding was forcing the wrong ∀ form) is carried visibly as a per-pair hypothesis of each bridge theorem, and the structure shrinks to a single field,
`WhirDecodeUniqueness` (a column reads the disclosure only via its row bytes. Quantified over runs. With a literature citation; an assumption, not proved, and
not a Lean axiom). The refuted old form was not deleted but preserved as a theorem in §7, and we noted that the per-pair form is also refuted on that particular fixture pair —
as it should be, since that commitment really is not binding. The substance of the bridge is
`opened_rows_determined_of_pairwise_no_collision` (closing the cell-level agreement of the adopted `opened_cells_root_determined_or_collision` into agreement of the whole row list by
`group_success_contiguous_rows`'s length equality and `List.ext_getElem`). The consumption plugs into the hr1b slot of the adopted
`committed_tables_join_up_to_collisions` with **argument-level agreement** (review read the signature and confirmed it — that slot takes
a single opening and does not require an OpeningFreeExtractor), and the 2 tau-table slots are also discharged from a single `tablesOf`. The resulting conditional statement:
for 2 accepted runs with the same root, under RunPairNoCollision and decode uniqueness, for each accepted Solidity call there exists a `tablesOf`
satisfying all of `CommittedTablesJoin` — with exceptions only `ConfigEncodingCollision` and `OpenedLeafCollision` on the 2 rows actually opened.
The pricing is partly connected (instantiation at the sample table's own `leafHashOf Q T` plus query membership in `boundedQueries L`).
Explicitly not established: identification of the deployment hash with the sample table hash, and a row-length upper bound for deployment rows. The proviso on root naming
(`opening_relation_is_root_blind`), non-run openings, and the single-root scope are inherited.

`Audit.Wire3.DeployedWhirWitness` (49 theorems / 31 definitions): the WHIR execution witness reached the **full 21 variables** (the deployed variable count).
`configured_twenty_one_variable_execution_example` shows by `rfl` the success of `WhirConfigured.run` with 4 actual folding rounds on the schedule of the real transcription
`canonicalRow21` (4 | 4,4,4,4 | 1, residues 17/13/9/5, interleaving depth 16), 6 claims under the deployment mask `[⟨31⟩]`, 1904 transcript bytes
(exactly the shape's upper limit) / 1976 hint bytes, with strict EOF on both streams.
`installed_tail_succeeds_at_twenty_one_variables` and `deployed_verify_whir_is_true` (with both parse and tail real) follow.
The parameter admission is done with the real transcription row itself, and a non-vacuity contrast was also turned into a theorem: since the transcription row is shipped with empty points, it is
rejected at 6 claims, while the real 2^23 domain and the query count 29 pass all structural checks — the obstacle is the points alone.

**Disclosure of scale (heading weight, as theorems)**: the canonical row-21's in-domain query budget is 84 over 5 stages (29/19/14/12/10), and this witness uses 5 —
a 16.8× reduction, which says nothing about WHIR's list-decoding soundness margin. The surrogate domain has `merkleDepth = 0` /
`codewordLength = 1`, and the Merkle authentication paths within the 1976 hint bytes are **all empty** (canonically they would be about 54 kB of
sibling hashes at depths 23/22/21/20/19 plus actual path verification). The surrogates are only these 2 families; every other field, including all 6 PoW thresholds, is a transcribed value.

**Establishing model faithfulness (the answer to review's most important question)**: that the intermediate sumcheck rounds impose no equation is not a gap in the model but
a faithful transcription of the deployed wire format. The prover sends only 2 of the 3 quadratic coefficients (c0, c2), and the verifier
**reconstructs** `c1 = claim − 2c0 − c2` (`WhirFinal.lean:144-146`, `SpongefishWhirVerify.sol:454`, and vendored
`whir/sumcheck.rs:124` — a 3-layer cross-check, down to the agreement of 48 bytes per round). Hence `h(0)+h(1) = claim` holds identically and there is nothing to check.
Soundness is preserved by the coefficients' degrees of freedom being reduced from 3 to 2. The only cross-check is the final RLC equation (`sol:737` /
`WhirFinal.finalClaim`). We also turned into a theorem that the success of `roundStep` is provably independent of the running claim.

PoW: it carries the 5 real canonical thresholds (non-sentinel) and actually consumes 40 nonce bytes, but with the constant hash `powValue = 0` and the comparison is
provably vacuous (with a contrast where grinding is effective under a different constant hash — the vacuity is a property of `toyHash`, not of the model).
Identification with `derivedConfig`'s derived context is 5 of 7 fields (the 6 claim cells, protocol id, session id, encoding, variable count, and the 3 roots,
for all thash/khash/P). The remaining 2 fields are the packed points, which is a record of the heartbeat budget rather than a claim about provability, and we named the missing lemma
(the points version of `derived_expected_claims_are_zero`). The 6 claim cells are all zero, originating from the zero proof (toy-ness inherited from the adopted
DerivedAcceptance — it must not be read as a non-trivial claim). Honest one-line summary: a transcript satisfying the only
equation the deployed verifier checks, with a degenerate hash, an empty-path domain, and 5 of 84 queries — a genuine execution witness and nothing more.

The three modules together are 156 models / 6517 theorems. The honesty arc of the acceptance line is complete: the verifier executes, depends on the proof, and
**rejects a wrong proof**. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
What remains is the r-family rejection form (exporting receiveOne's byte equality), identification of the deployment hash with the sample table hash, the 2 packed-points fields,
a hash with a wider state, the true value of the circuit, and the charging of Fiat–Shamir challenge grinding.

## Continuation update #52 (after 644326a0)

With the tracked runner we re-checked the 156 models / 6517 theorems of commit `644326a0`, PASS (1057.088 seconds, 1486 modules,
manifest `144da1b5e3f82f5cf5bf26520aff8f96c256e50dd819010566c0b3754315e0d0`, receipt
`631c7824d1044b392781ed68cd99a582601558841ab066f0ca8909f17a35b6f5`, graph
`058bac9228d4253e81196a1fb8171900e78022ab83ce697f5ce6a27d20d3e2b6`).

## Continuation update #53 (after 5b1d26f2)

Iteration 33 was a single candidate following the user's instruction (advance the true value of the circuit), and we adopted `Audit.Wire3.CircuitTruth` (25 theorems / 10 definitions + 1 structure).
It went through adversarial review and repair by Opus. Review confirmed that all the proofs are correct, and then showed by compilation that **the commitment-side
conjunct of the heading is a tautology**: since `CommitmentOrder.CommittedTables` has only 2 fields that are filled by `rfl`,
`∃ tablesOf, CommittedTables tablesOf s t` is provable with no assumptions, and the old conclusion form holds even with all the bridges deleted. Both facts were preserved as recording theorems rather than deleted
(`committed_tables_existential_is_a_tautology`,
`the_former_conclusion_shape_holds_without_the_bridge`).

The repaired heading `extracted_tables_satisfy_the_selected_gate_constraints_and_are_pairwise_run_independent` concludes, under acceptance,
`AssemblyResidue` (at R1bBridge's extraction state), a good draw, `WhirDecodeUniqueness`, and `gates.Nodup`,
(i) **pairwise run independence** — for any second run rp with `RunPairNoCollision r rp`, rp's extracted table equals r's extracted table,
or there is an `OpenedLeafCollision` on the 2 rows actually opened — this being the computationally honest meaning of "the commitment determines the table", and
(ii) that for all rows (< 2^degreeBits) × all selected gates, every constraint term of `GateEvaluatorCoverage.evaluateGateFull` is zero.
A proposed strengthening to a uniform `tablesOf` (`∀ r, RunPairNoCollision r r₀`) was checked before shipping and recorded as a theorem that it is refuted at the depth-1 fixture
(`the_uniform_no_collision_family_fails_at_the_depth_one_fixture`) — an instance of the ∀-over-all-executions trap refuted in R1bBridge
re-entering wearing the face of a "uniform extractor"; this audit has caught this trap twice and both times preserved the refutation as a theorem.

**Unique selection was proved from the tree.** `unique_selection_of_plonky2_selector_row` is a composition of the adopted `Gates.other_row_zero_filter` /
`unused_selector_zero_filter`, and only what is not in the tree (what the constants column holds at a row) was separated into the 5-field structure `SelectorRowIsPlonky2`.
Its content has been cross-checked against plonky2's implementation: the unused-selector constant `4294967295 = u32::MAX` agrees with `mle/src/gate_ext3.rs:33`
(the filter computation is at `:629-647`) and with 2 Solidity mirrors, and review also completed a counterexample showing that dropping `manySelectors` breaks unique selection, and
a check that the structure does not smuggle in the conclusion. Column identification is inherited undischarged from `ConstantsProvenance` (stated explicitly).

**The semantics** puts all 14 families into `evaluateGateFull` form (`validateConfiguration` from acceptance, the widths from `extractedStateConsistent`,
and `numSelectors ≤ numConstants` from the envelope). Full field-equation expansion is only for ids 0–3, and id 13 is a coset-layout shape gate where
`none` is possible. The transcription proviso (a cross-check against the audited Rust, not against plonky2 proper) is inherited verbatim.

**One additional deployment assumption was named**: `gates.Nodup`. Since the adopted single-gate theorem requires filter vanishing for all pre/post elements,
a duplicate structurally identical to the selected gate is not covered there and remains. `Gates.validateConfiguration` has no distinctness check, and `distinctRows` is vacuous for
duplicates (with a counterexample theorem). The honest weak form is `count = 1` for each selected gate.

**The deepest conditional layer was stated explicitly**: an instance of `AssemblyResidue` has never once been presented in this tree. The closest is
`ExtractorConstruction` §8 (discharging 10 of 19 fields; keccak 2 fields, deployment/ABI 4 fields, `gatesDecode`, `gateConstraintsPositive`,
`activeFilter`, and R1b remaining assumptions), and `SoundnessAssembly` itself says "there is nothing here showing that `hacc` and `AssemblyResidue` can be
compatible". That is, simultaneous satisfaction of `{hacc, H, hdraw, hidx}` is not presented, and the text is a statement under that condition.
A 12-item ledger: copy/routing (the missing statement is exactly "the committed tables are constant on each permutation orbit of the circuit's routing"), public input binding
(up to the row equation of PublicInputGate), the freedom of the truth sequence and `coeffsOf`, root blindness, the contents of the selector column, that unselected rows are entirely unconstrained,
the coset layout gate, the transcription proviso, the mass side, `hdec`, `Nodup`, and simultaneous satisfaction.

With 1 module, 157 models / 6542 theorems. This too is a result under the ROM law, and is neither a property of keccak nor the system's soundness error.
What remains is the semantics of the copy/routing constraints (constancy on permutation orbits), public input binding, an instance of `AssemblyResidue` (simultaneous satisfaction with acceptance),
the r-family rejection form, the 2 packed-points fields, and the charging of Fiat–Shamir challenge grinding.

## Continuation update #54 (after 1f3fff17)

With the tracked runner we re-checked the 157 models / 6542 theorems of commit `1f3fff17`, PASS (1029.306 seconds, 1487 modules,
manifest `0da9172dfc13f908e4b9374a3c9dfda5e179e1f6e536e534740fb2fc60ddf582`, receipt
`57baa9ee1d865ce9ebd127f830eafda7cc38f3271d0a501b976c09a05b82abbd`, graph
`933eccabf42609b587017b2dcf9cb085ed96fda8636751acc35adba6146f0d28`).

As of this update the next steps, in priority order, are: the semantics of the copy/routing constraints ("the committed tables are constant on each permutation orbit of the circuit's routing" —
the copy-constraint half of circuit truth. A semantic bridge from the terminal-expression agreement of the norm/logup lane to orbit constancy), an instance of `AssemblyResidue`
(the deepest conditional layer. `ExtractorConstruction` §8 has discharged 10 of 19 fields, and simultaneous satisfaction of the remaining 9 — keccak 2, deployment/ABI 4, `gatesDecode`,
`gateConstraintsPositive`, `activeFilter`, R1b (bridged)), the r-family rejection form (exporting `receiveOne`'s byte equality),
a closed form for the packed points, public input binding, and the charging of Fiat–Shamir challenge grinding.

## Continuation update #55 (after e5ece29e) — adversarial re-audit of the deployed code (outside the Lean model)

This is not an addition to the Lean model but a record of an adversarial re-audit against the actual Rust/Solidity code identical to the deployment pin `b569e0d7`
(details in `mle/tasks/reaudit_wire3_soundness_2026-09-18.md`). The attacker controls only the proof byte sequence, and the VK, configuration, and
WHIR profile were taken to be code-resident and honest. We carried out four strands — (1) differential testing of the 14 gate families against plonky2's
`evaluate_gate_constraints` as ground truth (production parameters, down to the Rust→Solidity Ext3 evaluator), (2) the inner WHIR Fiat–Shamir order, Merkle,
folding, and profile pinning, (3) the mirroring of all `ensure!`s of the outer Solidity's `verifier_v2.rs`, the transcript, canonicity, and the fraud decision, and
(4) derivation of the identities of the norm/logUp permutation argument (irreducibility of `x³−2`, uniqueness of the partial fractions) and public input binding — and
found no CRITICAL/HIGH. The 2 past pre-repair forgeries (an RLC before root absorption, and a public input hash not recomputed) are
closed by the RLC squeeze at byte 552 of narg and the Poseidon recomputation at `MleVerifierV2.sol:382`.
The PoCs were implemented as 10 new files (5 `mle/tests/poc_*.rs`, 5 `mle/contracts/test/Poc*.t.sol`) and registered in the implementation inventory
with `kind: implementation` (Rust 8 passed, Solidity 36 passed, re-run by the orchestrator). These are executed tests, not Lean theorems,
and they do not discharge the Lean incomplete items (simultaneous satisfaction of `AssemblyResidue`, formalization of public input binding, grinding charging).
Non-critical items recorded: the liveness margin of the fraud decision (its relation to the parent-side `MIN_MLE_VERIFY_GAS`, unmeasured),
insufficient bounds in `_dotEqWithRow` (unreachable at `numCommitments==3`), no leaf/node separation in Merkle (leaf lengths 128/384 ≠ 64),
a formal difference in the Poseidon partial round constants (identical in value since `FAST_PARTIAL_ROUND_CONSTANTS[21]==0`), and the safe-side over-counting of `epsilon_log`.
We do not declare "no critical soundness problems" on the basis of this update alone.

## Continuation update #56 (after 43a454fb)

Re-checked the 157 models / 6542 theorems of commit `43a454fb` (translation of `mle/audit/README.md`, `SCOPE.md`,
`REPORT.md`, `HISTORICAL-README.md`, `HISTORICAL-SCOPE.md` and `HISTORICAL-REPORT.md` from Japanese to English;
no technical claim, hedge, citation, identifier, hash, or numeric constant was altered, only prose) with the
tracked runner: PASS (1018.546 seconds, 1487 modules, audit-manifest digest
`34a564b8cd3be2337976521ee83cdd8ff9a83f93ff79a0291e28de3433b32253`, receipt-file digest
`fdc9daa14e641b0a0b59acec248534ff3af9ccde4e09c32bf531aa320a303e9b`). Guard rerun after the receipt edit: PASS.

%%B47%%











## Next steps

Proceed through the list of incomplete items in [SCOPE.md](SCOPE.md) in order.
In particular, it is necessary to advance the connection from the typed configuration / actual sampling path to the outer entry point, and to prove
the semantics and degrees of all gates, the execution semantics, the overall connection of the finite field proof, and probabilistic soundness.
We do not declare production use or "no critical soundness problems" on the basis of this update alone.
