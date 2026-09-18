# wire-v3 audit scope and trust boundaries

Target commit: `becfe98e37c76e62f02f1aa7a417c7b06840db67` (2026-09-06).
This work prioritizes the current MLE/WHIR path. All Rust/Solidity files are
enumerated in the correspondence table, but the old V1, the whole of the Plonky2
recursive circuits, the standalone Starky, and all dependency implementations are
not treated as formalized.

## What "proved" means

The Lean kernel checked that the conclusion of a theorem is derived from the
**described Lean functions/types and explicit hypotheses**. The following three
layers are distinct:

1. Properties internal to the Lean model — covered by this update.
2. That every execution of the real Rust/Solidity/Yul corresponds to the model — manual comparison only. Formal refinement is not proved.
3. Probabilistic soundness that a correct witness exists for an accepted proof — not proved.

The condition that the same initial claim, the same challenges, and the same
roots/points/claims were used is not a proof that they were generated and
authenticated in a cryptographically sound way.

## Explicit boundaries

- Arithmetic is mod arithmetic over Nat. uint64/uint256 wrapping, addmod/mulmod, memory,
  non-canonical internal representations of Rust fields, and correspondence with compilation results are separate issues.
  GoldilocksFoundation proves the primality of the concrete p, general Fermat, and the non-existence of a cube root of 2.
  GoldilocksNorm proves, for every nonzero canonical Ext3, the success of the real inverse and that it is a two-sided inverse.
  GoldilocksExt3Field constructs a Field on the wrapper of the real operations/real inverse, and proves characteristic p and cardinality p³.
  GoldilocksLagrange connects the real square iteration to powers of two, and proves that the existence of evalL0's output holds iff
  degreeBits<64 and x≠1, and the agreement with the rational expression after the real inverse succeeds. The failure at x=1 is retained.
  An explicit theorem that X^3-2 is Polynomial.Irreducible, and machine-word shift/cast/memory, are separate issues.
  In Algebra, commutativity/associativity/distributivity of addition and multiplication, additive inverses, and cancellation are proved from the actual c0/c1/c2 expressions.
  No record that assumes the ring laws is used. NormIdentity proves the formal adjugate/norm identities,
  and ModularPower proves the values of the concrete binary exponentiation and the fuel condition for success.
  The product on a successful inverse is reduced to norm^(p−1) mod p, and Foundation/Norm connect this to 1.
  Finite-field-ness is not hidden in a hypothesis record; it is constructed from the ring laws of the real Algebra and the real inverse.
  FermatBridge takes FermatAt(norm) as a visible theorem argument and connects the two-sided inverse property of the real inverse,
  canonical cancellation, and division. The concrete instance with base 7 discharges this hypothesis from a numerical certificate, but
  the condition for other inputs is discharged by the later Foundation/Norm. Canonicality remains an explicit condition.
  It does not derive nonzero-ness of raw Nat values, nor the same nonzero claim for off-cube formal norms with Ext3 coefficients.
- Packed is a functional loop model. It proves agreement of the result with padding, but does not include the safety of
  the real in-place memory operations. Applying it to the Rust array implementation requires connecting the input length, width, next power of two, and point length.
  DenseMleIndexed models the bind loop of ext3.rs as an indexed mutable buffer, and proves that at each i, 2i/2i+1 are read before being written,
  that writes go in increasing order and a truncate happens at the end, the invariance of the unwritten suffix, Valid table length = 2^numVars, the source numVars>0 guard,
  the agreement of every bindMany execution with Packed.layer/fold, and a bridge to the affine Norm.
  constructor/from_base/trailing_zeros, usize/memory/compiler refinement, and complete connection from the endpoints remain open.
- The hash in Transcript is an arbitrary deterministic function. From the uniqueness of the pre-hash tag/payload under the same
  old digest, injectivity and randomness after hashing are not derived.
  The counter results cover calls that succeed under checked.
  Raw helpers such as `commitClaims` target an environment where preflight has guaranteed canonical values and the u64 length bound on payloads,
  and that preflight connection itself is not proved.
  The full procedure for initial statement/root absorption and the connection to every Engine remain open.
  OuterInitial makes concrete the 16 frames of the outer initial transcript (initialization domain, statement domain, circuit digest,
  raw public inputs, packed schema and 15-word u64-LE metadata, config digest, the 64/32-byte WHIR identifiers,
  preprocessed/witness root), together with the order and counters of eta→beta/gamma→norm-inverse root absorption→xi→lambda/rho/kappa→
  log tau→gate alpha→gate tau, and proves that for d≤13 every checked squeeze succeeds with the same result,
  the none of the identifier-length guard, and the round trip of toInitial. The 40-byte snapshot is an internal adapter and not a proof wire field, and
  the recomputation of the PI hash, the computation of the config digest, VK/config semantics, collision resistance/uniformity of Hash, and every embedding into downstream Engines are not proved.
  OuterAdapter makes concrete the lossless decode of the 40-byte internal snapshot (anything other than length 40 is none), the checked delegation to the real coupledRound
  (round domain→u64-LE round→log vec→gate vec→challenge domain→log limbs 0..2/gate limbs 3..5, resulting counter 6),
  the 5 claim vectors and the empty 6th cell→index domain→log index sequence→gate index sequence (counters 3i/3·bits+3i),
  agreement of every limb with the existing Transcript.constituentIndices, a checked loop definitionally the same as Verifier.roundStep, and
  the Option prefix of initial identifier guard→checked derivation→coupled rounds→claim/index→packed fold→whirContext.
  It does not totalize malformed decodes to zero/default. Agreement with the existing total Engine is a conditional theorem that makes CommitAgrees/SamplesAgree/initial agreement/
  fold agreement explicit; it is not source equivalence, complete acceptance, or PCS/WHIR connection for an arbitrary Engine.
  Outside the shape, raw zip truncates unequal-length lists, so the conclusion about source correspondence is limited to the envelope/shape/InputSizes hypotheses.
- Spongefish is a separate chain, that of the inner WHIR. It makes concrete the 47-byte input state||squeeze||BE64counter, the challenge that
  generates 120 bytes at once and reduces them to 3 LE 40-byte values, the strict canonical reading of 24 bytes,
  PoW with challenge32 + nonce8 + zero24 and the LE leading-8-byte test, and the hint Vec prefix.
  A raw constant Hash argument is not an assumption of RO, collision resistance, or entropy. Real word loads/uint256/IO patterns are a separate boundary.
  WhirChallenge proves the bijection between the 0/40/80 slices of the same 120 bytes and the 3 LE integers, and
  bounds the number of inputs to the d points of the real reduceChallenge by d · ceil(2^320/p)³.
  Under a finite uniform law defining all 120-byte strings as equiprobable, the probability that a fixed pair of distinct inner-WHIR
  quadratics agree is at most 2(ceil(2^320/p)/2^320)³. This is not a theorem deriving uniformity of the real Keccak/FS,
  independence from previous messages, or fixedness under adaptive choice.
  This inner-WHIR theorem is not applied to the outer MLE's three 32-byte squeezes and its different coefficient-recovery formula.
  WhirRlc connects the same geometricPowers and the real dotRow to concrete polynomials, and derives that fixed, equal-length, distinct canonical
  vectors agree at ≤ n−1 points, together with a bias-inclusive upper bound under the explicit uniform 120-byte law.
  count0/1 consume nothing, as in the source; 2 or more use the same 120 bytes/four blocks/counter+4.
  It connects the initial phase's absorption of all claims/cross → vector RLC → constraint RLC of the next state, but
  independence of the two Hash outputs, extraction of a fixed vector from a commitment, and adaptive fixedness are not proved.
  The formula for an arbitrary row is a zero-totalization; for real statement rows a separate verified boundary theorem is used.
- WhirSampling.challengeRaw makes concrete 1 hash/counter update per byte, the BE query, and the power-of-two mask.
  It proves the no-consumption branch for count=0/numLeaves=1, the counter bound, and the raw range.
  challengeIndicesReference is a reference version with an executable insertion sort and adjacent dedup, not the source's
  in-place quicksort itself. Even having proved sortedness, membership, count, and non-emptiness, that does not mean equivalence
  with the source quicksort was obtained from this reference version alone.
  WhirQuicksort/Correctness proves, from the real indexed scan/swap/left-right recursion,
  the partition sentinel, the classification, out-of-range invariance, and preservation of the element count, and derives from the first real swap
  the strict shrinking of the recursion width and full termination with sufficient fuel. Only after proving sortedness and preservation of multiplicity is it identified with the reference sort.
  WhirSamplingExecution connects the real sort/compaction to raw sampling, preserves the branch order count=0→single leaf,
  and makes every Option result, every state, and every failure agree with the reference version. It also connected this to the whole WHIR
  execution with both sampling sites replaced and to the single checked configuration entry point. This discharged the boundary of the mathematical sort replacement, but
  array memory, uint256/overflow, gas, and source/compiler refinement are not proved.
  WhirDedup models the real indexed compaction after quicksort, and proves the current buffer[i]/[i−1] comparison,
  the conditional overwrite, all read/write bounds, termination after n−1 iterations, and the equivalence of the final length and the reference dedup.
  That equivalence does not require sortedness; only the corollary about strict ascending requires sorted input.
- Compact is not a complete decoder returning a typed Proof; it scans the byte grammar and returns chunks.
  Full validation of the trusted Shape, Rust's stricter variable cap, reconstruction of the debug WHIR pattern,
  the interior of the opaque WHIR bytes, and the EVM struct memory layout are not covered.
  Strict canonicality applies only to the outer field chunks. It is not guaranteed by the deferred canonical mode alone.
- The collision reduction in Sumcheck targets semantic message/truth functions.
  Correspondence with the honest truth chain is a hypothesis; the production verifier does not check truth.
  WhirQuadratic connects the c1 recovery and Horner of the real WhirFinal.quadratic to polynomials over a concrete field, and
  proves that the real endpoint sum = claim, degree ≤ 2, and that a fixed pair with distinct canonical claims agrees at ≤ 2 points.
  It preserves the real message/challenge/state of a successful round and also connects to the disagreement of two explicit chains, but
  that the comparison-side chain is the true value of the real circuit, the full connection to the gate/norm polynomials, and probability/FS transformation remain open.
  WhirPolynomial connects only the terminal real constant-first Horner to a Polynomial over the concrete Ext3 field, and
  proves that fixed canonical final vectors of equal length that are distinct agree at ≤ length−1 distinct points.
  A Finset is a set of points without duplicates; injectivity of the query list or of the source domain map is not assumed or substituted.
  Different lengths alone can yield the same polynomial because of trailing zeros. It distinguishes the noncomputability of symbolic Polynomial from
  the executability of the real Horner, and treats the point of fixing under FS, distributions, and the probability of adaptive choice as separate issues.
- Verifier is a success-boundary model for normalized typed inputs.
  OuterRound connects the forward coefficient sum of the same evaluateRound, the concrete inverse-two, and the backward Horner
  to polynomials over a concrete Field, and proves the endpoint sum, the degree, and the number of agreement points for a fixed distinct claim.
  Applying it to the source's fixed 5-coefficient loop for the outer log requires coefficient length 5 from the existing preflight.
  OuterChallenge connects, separately from the inner side, the real 3×32-byte squeeze and the same digest with consecutive counters, and
  preserves the same polynomial as log 0..2/gate 3..5 after both messages of coupledRound are absorbed.
  The upper bound on a fixed polynomial under the explicit uniform triple law is d(ceil(2^256/p)/2^256)³, and
  it does not claim independence or uniformity of the real hash, adaptive fixedness, or a product of the probabilities of both lanes.
  OuterInterpolation/Total model, with indices, the Gaussian elimination of coefficients.rs (natural nodes, increasing powers, RHS column n, no pivot exchange,
  diagonal inverse, normalization over pivot..=n, cloning of the pivot row, target rows other than the pivot in increasing order, capture of the factor before writing, subtraction of columns in increasing order,
  extraction in coefficient order). With a proof-only ghost RHS it identifies the reached pivot value ∏_{j<p}(p−j), and proves that if n≤p then every prefix/
  all n stages succeed and the real WhirFinal.inverse is executed, that it is total on nonempty input, and that empty input is rejected. For degree<p, from samples at 0..degree
  it obtains the exact coefficients and the omitted constant message, and the real evaluateRound returns f(r). It specializes to norm degree 5 and checked gate
  q+2 (q>0, q+2≤10). Vec/memory/compiler refinement, the dataflow of the real current_round,
  circuit truth, and FS/PCS are not included.
  It leaves configuration, the decoder, the initial transcript, gate/norm/eq evaluation, hash, the WHIR tail, etc.
  as function observations with inputs. The exception/gas classification is not the full classification of the real EVM.
- The Solidity envelope/deployment checks are done in the constructor, and on a call the configuration hash is compared.
  `verify` is the composite boundary of deployment + call; `verifyCall` is the boundary with the former checks removed.
  Their agreement takes the deployment invariant as an explicit hypothesis. That hypothesis is not derived from hash agreement alone.
- The coordinates into WHIR are `reverse(index) ++ reverse(row)`. It distinguishes the boundary where the native adapter reverses
  the Rust entry point's `row ++ index` from the boundary where Solidity reverses it.
- Of the 6 claims, the 5 used at the outer terminal are constrained. The 6th cell is unconstrained on the outside, and
  being an object of processing inside WHIR must not be conflated with agreement with the outer expected value.
  OpenedClaimFold proves the row++index split of the adopted Packed.fold/Connections.packedFold/DenseMleIndexed.bindMany
  (by associativity of the same function, not a reimplementation), that for pack_mles' column-major padded table
  (row bits low, index bits high, zero columns up to 2^indexBits) the whole-table evaluation = the packed fold of each column's row opening,
  the agreement of Solidity cells 0-2/log index point, 3-4/gate index point, and cell 5 none with the Rust slot point·3+group, and
  that the native point = the reversal of the dense point; and only under the explicit honest-prover assumption that the 5 claimed cells equal the
  row fold of each column does it derive that each cell of expectedClaims agrees with the dense evaluation of the padded table at the WHIR point.
  It also has a concrete example where incorrect cells do not agree. It does not claim that the opened values are true PCS openings,
  WHIR acceptance, FS, or Rust/EVM refinement.
- WhirTerminal is a slice of the terminal comparison. It is not a proof of the whole WHIR verifier, which includes
  Merkle/hash/FS/OOD/the preceding sumcheck/PoW/consumption of all bytes. In WhirFinal, the same finalVector is connected to the subsequent final
  sumcheck, the reverse-order fold, nonzero-ness, the inverse computation, the subtraction of all constraints, all linear forms, and both EOFs.
  The decoder/PoW/challenge of WhirFinal alone are observations, but WhirFinalSpongefish.engine replaces all three
  with concrete Spongefish calls and proves the 48/56-byte consumption of each round and the suffix length on acceptance.
  Context is still a trusted state that should be produced by the preceding stage, and it checks EOF while retaining the already-read hint positions.
  This adapter reads no additional hints, and does not amount to an independent proof of the preceding stage's hint authentication.
  NormIdentity also proves the equivalence of the sum-form final fold and the Packed difference-form on the complete table.
  It is not made into a model that independently forbids a zero total query count.
- WhirInitial makes concrete each commitment processing step root→OOD challenge→own answers→boundRoot,
  the mask check of all claims, the cross matrix, the vector/constraint RLC, and the initial sum.
  WhirPrefix passes those real results and the same byte sequence to the first sumcheck.
  The Params/form arrays are a projection from a validated caller, not fields newly stored at runtime.
  WhirIntermediate passes the same sum/roots/vector RLC/randomness/cursors from this same prefix to the intermediate round sequence.
  It makes concrete new root→all OOD challenges→all answers→PoW→sampling→raw Merkle of the previous root→round RLC→
  decoded dot of OOD/all queries→constraint preservation→sumcheck→previous-root update.
  Round 0 targets 3 base roots × 1 vector, and thereafter only a single Ext3 root. All queries/all groups/all columns and
  the real RLC index, the 32-byte slice of a root, the amount read, and the number of constraints are derived from a successful execution.
  ProfileShape is a projection of the validated caller's previous-round configuration, not an additional runtime guard.
  The source quicksort, the binary loop of domainPow, and formal correspondence of the instruction order of decode/arithmetic remain open.
  WhirTail.run preserves the same init/prefix/intermediate execution, reads the final vector exactly once, and
  connects to the final split or standard authentication, the Horner comparison, and the same vector's final fold/claim/both EOFs.
  Context is derived from that real prefix's forms/initial RLC and the real intermediate state, and does not receive independent observations.
  An arbitrary State for runTail/finish carries no guarantee from the preceding stage; the theorem about a successful run must be used.
  A 3×1 ProfileShape is not identified with complete VK/ABI validation. The connection to the outer WHIR arguments and to all configuration projections remains open.
- Merkle makes concrete raw 32-byte digests, left-right 64-byte compression, strict ascending order, and per-layer sibling processing.
  It proves the cursor bounds when there is a read, and that if two paths with the same index/same depth send different leaf hashes
  to the same root then there is a collision of compression inputs. Injectivity of the hash is not assumed.
  MerkleExtraction extracts, from this same successful execution, a depth-length path for each leaf.
  WhirRows connects the read/hash of the original hint rows directly to the existing Merkle, and WhirRowBinding reduces
  the real openGroup's same-root/index/depth rows to either agreement of the raw bytes, the decoded values under the same Layout, and the dot with the same weights, or
  a hash collision of the real raw leaf input or the 64-byte compression input.
  It does not assume and substitute independent leaf hashes/paths or injectivity of serialization.
  Replacement at every entry point of WhirTerminal.authenticate, collision probability, and the Yul array operations are incomplete.
- WhirRows.openGroup/openGroups are raw phase only. The canonical decode of base8/Ext3-24 is a separate operation, and
  the existence of canonical values is not derived from raw authentication success alone. WhirTail's dedicated final split preserves the order
  slice/hash→canonical decode/dot→vector RLC addition→hint cursor→Merkle of each root.
  The standard path performs raw authentication first, then decodes each row and immediately does the Horner comparison.
  An empty query also reads the 8-byte Vec=0 prefix, and an empty Merkle opening thereafter maintains the offset.
  Layout/weights/indices and the tail were connected via WhirTail's restricted 3×1 path, but this is not an instruction-level correspondence across languages.
- WhirSchedule is a projection of only the folding guard of the existing _validateParameters. It proves the complete partition of the
  number of variables among initial/intermediate/terminal, the remaining/suffix of each round, the absence of underflow, and the final power-of-two size.
  WhirParameters makes concrete, from typed Params retaining all source scalars, the fold/domain/point-array guards in the real order,
  and moves raw coordinates into the Subtype as-is after checking. It distinguishes the count/mask/roots checks at the bound entry point from
  the positive form-count check at the deployment entry point, and does not add nc/nv checks to the latter.
  From success it derives the existing Schedule, all domains, the length/canonicality of all points, the exact number of evaluations, and
  WhirInitial.validatedParams. It does not claim that the bound guard canonically checked the expected values.
  samples/PoW threshold/trailing mask bits are not independently constrained, because the source slice has no check for them.
  WhirParameters alone does not address ABI, integer widths/overflow, provenance from immutable config, the 3×1 profile, or projection to every phase.
  Projection to every typed phase is connected later in WhirConfigured. From a single checkBound-ed p it derives all phase arguments, and
  from execution success and the explicit CallerProfile (nc=3, nv=1) alone it derives every intermediate ProfileShape and the terminal contextShape.
  It adds no other shape assumption and no new runtime guard. Even with the generic Params type, the source correspondence is limited to the 3×1 case.
  Provenance from an immutable VK, ABI/integer width/overflow, and extension to a generic nc/nv profile remain a separate boundary.
  The source's _validateDomain alone checks only the nonzero-ness/canonicality of the generator and the shape; it does not check the order.
  To map query indices to distinct evaluation points, the required order must be derived separately from the generator's construction under a fixed VK.
  This condition must not be implicitly obtained from the success of the shape checks or from the no-duplicates condition of Finset.
  GoldilocksDomain proves, from a 6-prime-factor certificate, that order(7)=p−1, and for k≤32 that the fixed root 7^((p−1)/2^k) has
  order 2^k and that the powers at distinct indices/the canonical values after transposition are injective.
  Formal correspondence of Ark/native WHIR/codegen to this fixed generating expression, and digest binding, are separate issues.
  WhirDomainBridge connects the c0 of the real WhirIntermediate.domainPoint itself to this post-transposition
  canonical value. Only when k≤32, agreement with the real generator's fixed value, positive coset dimension, and product = 2^k are made
  explicit does it derive injectivity of the real points, cardinality preservation of the query image, and that fixed canonical final vectors
  of equal length that are distinct agree on ≤ length−1 queries. It treats both the raw Horner and the normalized comparison.
  The queries form a Finset (Fin (2^k)), and duplicate sample sequences, the connection to the real query range/config,
  the machine-word correspondence of _glPow, and FS probability must not be taken as implicitly obtained from this theorem.
  WhirDomainPower is a separate bitwise scalar loop, connecting the 64-bit mask, the real low-bit condition, right shift, and mulmod
  to the existing binary power. For a uint64 input and a uint256 exponent within the Fin bound it derives success within 256 fuel, the exact value, and
  output < p < 2^64. If the same transposition exponent is within 2^k, it agrees with the real domainPoint for k≤32.
  It retains an initial base ≥ p as long as it is within uint64, and returns 1 for a zero exponent. Fuel is not gas.
  It is a manual scalar model and does not amount to obtaining a formal correspondence with Yul/parser/compiler/bytecode.
  The values must be derived from the stored VK/config, and are not fields the prover can freely change.
- Norm makes concrete the formal-coordinate expressions and the helper/logUp aggregation. PI is Rust's ordered direct sum, and
  PiSharedBits/PiCache prove in-model equivalence with Solidity's row-cache/shared-bit optimizations.
  The OR/XOR mask, newest-first search, duplication/order, and the omission of the final eta update are also made concrete.
  The unconditional equivalence is a theorem about the raw totalization of both models; it does not guarantee that the implementation rejects malformed shapes.
  Formal correspondence between EVM pointers/aliasing/in-place writes and the Rust execution is still a separate issue.
  Via Algebra, Solidity's optimized expressions for eq/subgroup and the Rust expressions, and square = mul, are proved in-model.
  The formal adjugate/norm identities are proved in NormIdentity, but the correctness of the helpers and
  the probabilistic reduction to individual PI agreement remain open.
  NormPolynomial connects the real denominator/formal adjugate/norm/recomposition and the single contribution of wireStep to
  affine input polynomials over a concrete Field. Because the formal coordinates also have Ext3 coefficients, it does not use the
  nonzero-norm theorem for canonical Ext3. helper ≤ 4, rows including eq weights ≤ 5, logUp ≤ 3, PI ≤ 2, finite sum ≤ 5.
  It also proves the weight builder for the real number of multiplications of lambda/eta, but bulk application to the whole-row builder is not connected.
  The right-hand side of round_evaluation_actual is the candidate in-row/PI expression over captured endpoints, not an equivalence to Norm.checkedEvaluate or
  to the Rust mutable arrays as a whole.
  NormDenseRound models, with indices, norm_logup.rs's line_value, evaluate_target_from_values (the width assert is none; the two accumulations of a single
  loop; retention of the xi·ZERO term), round_sum_at (writing 4 scratch vectors of width wires.len() in an index loop, the suffix loop,
  the PI loop over row>>(bound+1)/(row>>bound)&1, sum+xi·binding), current_round (is_complete→Err, cache,
  samples from Field64_3::from(0..=5), the adopted OuterInterpolation.interpolate, coefficients[1..]),
  bind (prefix update by the old bound_variables → +1 → bindBuffer of the whole table; num_vars=0 is none), and the prover state's
  Err/panic/Consistent/PrefixProvenance. Under Shape it proves roundSumAt = roundValue, that the 6 samples are the samplePolynomial of the
  degree-5 roundPolynomial, the omitted constant = coeff 0 = the verifier's half-sum recovery, that the real
  Verifier.evaluateRound recovers the round value from the endpoint-sum claim for the transmitted 5 coefficients, all read bounds, preservation of Shape after bind, and
  preservation of prefix = booleanRowEq(bound point). Shape is a caller-side invariant of the constructor asserts and is
  not a new runtime guard; the base→Ext3 transposition of from_base, eq_evals_ext3, the provenance of the weights from PreparedChallenges,
  the interleaving order of the scratch writes, malicious prover/transcript/round chaining, and PCS are not proved. roundSumAt itself is a
  totalized read, so each per-round theorem under Shape assumes 0<remaining and stays within the scope of the boundary theorems, and
  the state theorems derive this from Consistent ∧ ¬isComplete.
  NormTerminalBinding explicitly maps the table after all variables are bound (remaining=0) to NormTerminalInput (constants++sigma cells,
  routed wire cells++non-routed tail extra, identity helper cells++sigma helper cells, the PI values of bindings), and proves
  term-by-term agreement between the prover's targetValue and the verifier-side Norm.permutationTerminal/evaluate (evaluateWith, which takes the eq/subgroup values
  as arguments, is the same by rfl), that each bound cell = the adopted DenseMleIndexed.evaluate/
  Packed.fold/Connections.packedFold, bind success with |point| = remaining and a single cell per column, that the final round's
  (remaining=1) roundValue = the terminal target of the post-bind table, and an end-to-end theorem for an honest prover.
  eq cell = Norm.eqEvaluation(tau,point), subgroup cell = subgroupEvaluation, the lambda running product,
  powers of eta, provenance of the wire map from bytes, kIs agreement, shapeValid, the normTerminalInput proof = the correspondence table, and challengesFromInitial =
  prover challenges are visible assumptions, and eq_evals_ext3(tau), the transposition of from_base, PCS claimed value = prover cell,
  malicious prover, transcript, and Rust/EVM refinement are not claimed.
  OuterClaimChain drives the honest prover's log lane using the adopted Verifier.roundStep/runRounds with the same commit arguments,
  combined with the prover's currentRound→bindChallenge, and proves logClaim_i = roundValue(t_i,p,r_i) after each round,
  the final claim = the value on the table on which round_sum_at last ran, that the next table's f'(0)+f'(1) = the previous table's roundValue(r) (proving 2≤remaining and
  all adjacency/PI read bounds), initial zero claim ⇔ zero endpoint sum (zero-ness is not assumed), intoProofAndPoint = the message sequence/challenge sequence
  the verifier consumed, agreement with Verifier.derivedRounds, and agreement with OuterAdapter.runChecked.
  Because the adopted gate prover has no bind_challenge model, the gate lane is parameterized by the explicit assumption that "the recovery agrees with
  a degree-≤d polynomial on the integer grid", and the gate prover is not forged. Soundness for arbitrary messages and FS are not claimed.
- Gates is the configuration validation of 14 families; GatesAdditional/Coset and Poseidon/Constants make concrete the remaining 8 families.
  GatesComplete actually computes all 14 families and proves that for a valid configuration and input lengths a Some is obtained.
  Integrated uses this complete dispatcher. Do not confuse it with the partial dispatcher of the base Gates alone.
  All 1147 constants are compared verbatim with the source, but the extraction check is not called a formal refinement.
  The zero-filter skip is retained. A proof of the polynomial degree of an expression is not derived from the degree budget check, and
  the reverse direction from aggregate value 0 to all constraints 0 is not claimed either.
  GatePolynomial identifies the zero-filter branches of all 14 families with the same concrete terms/Horner, and
  derives the real factors of the selector and the degree of the fixed alpha Horner. GateBasicPolynomial/Mds
  prove evaluation agreement with the real constraint expressions of IDs 0,1,2,3,5,6,7, and derive degrees 0,1,1,3,1,3,3 respectively
  from affine inputs over both the wire and constant columns. Arithmetic's local constants are also variables, so the upper bound is 3.
  GateCheckedPolynomial covers only these 7 families, and from the real validateGate/both input lengths/all configuration checks proves
  a selected-row contribution ≤ q+1 and ≤ q+2 after the explicit affine weight. The remaining 7 families are symbolic NONE.
  The provenance of the weights from the real eq sequence, the total row sum, interpolation/transmitted coefficients, the truth of each gate, and authenticated endpoints are a separate boundary.
  GateLoopPolynomial/Random/Twelve add IDs 8 through 12 and derive from actual computation Exponentiation ≤ 4, BaseSum ≤ base,
  the two Reducing kinds ≤ 2, and RandomAccess ≤ bits+1. Reducing's accumulator is reset each time to the
  claimed-next wire, and constraint satisfaction is not made a hypothesis of the degree. RandomAccess's scratch is
  actually recomputed, and the degree upper bound increases with each bit. Boolean-ness and range truth are not assumed.
  From the real metadata/all configurations/both input lengths it proves a contribution ≤ q+1 for the 12 families and ≤ q+2 after the affine weight.
  It distinguishes the preceding 7-family dispatcher from this 12-family dispatcher, and leaves the NONE for Poseidon 4/Coset 13.
  GateCoset/Poseidon/AllPolynomial prove, for all 30 rounds of Poseidon 4 (swap/delta, a fresh wire before each S-box, omission of the constants in the
  final partial round, circulant/sparse MDS), without assuming constraint vanishing, 123 constraints and degree ≤ 7, and for Coset 13 the old-product evaluation→
  update/reset/intermediate claimed E-P as 4+4·intermediates constraints with degree ≤ D for D≥2, and derive from the real validateGate of all 14 families
  a contribution ≤ q+1 and ≤ q+2 after the affine weight. No symbolic NONE remains in this all-family wrapper.
  GateAggregate/SuffixPolynomial connect the ordered aggregation of all rows of the real combineRows into a single polynomial, proving degree q+1, that from the real configuration envelope
  q≤8 it is ≤10 after weighting, and that the real reads of 2s/2s+1 with the same challenge interpolation and the Boolean suffix sum over 0..2^remaining−1
  (including remaining=0) are given by the same polynomial. TableShape is an explicit condition on the supplied table, not a new runtime guard.
  GateSlotAlgebra/Commutation/Round model, with indices, gate_ext3.rs 543-608 (each gate is evaluated even when the filter is zero,
  and after ensuring the output count, accumulated[slot]+=filter·value is written into a fixed-width buffer, reduced with forward alpha powers),
  and out-of-range writes are none, as the source panics (a totalized List.set is not claimed to be source behavior).
  From validateRows/validateConfiguration it proves that every write is in range, that the slot-first result agrees
  with the real combineRows/evalCombined, and that they have the same polynomial (≤ q+1, ≤ q+2 after weighting).
  It models gate_ext3_v2.rs 105-134's current_round (the numVars>0 ensure, half=len/2, degree+1 cells initialized to zero,
  mutable accumulation with suffix outer and integer inner, the real reads of (1−x)·t[2s]+x·t[2s+1]) with the same slot evaluator, and proves
  that the executed accumulation agrees with the per-integer suffix-first sum GateSuffixPolynomial.currentRoundValue,
  that for a Valid eq table half = 2^(numVars−1), and that under TableShape every cell is the value of a single polynomial (≤ q+2 ≤ 10).
  The ext3_evaluations_to_coefficients call (136) and the degree-configuration check (80-83), the DenseMle construction,
  the tau-derived eq table, the canonical publicHash preflight, the reduced emitter, the bridge from the success of Rust's validate_gate_ext3_context to
  Lean's validateConfiguration, and circuit truth/PCS/FS are not proved.
  GateTerminalBinding models gate_ext3_v2.rs 142-161's bind_challenge (degree ensure→eq table→all wires→the adopted bindVariable of all constants,
  rounds/point push, failure is none) and into_proof_and_point (the eq.num_vars=0 ensure), and
  treats the constructor ensures 70-79 as ProverShape, proving that after all variables are bound each column is a single cell equal to the adopted packed fold/
  DenseMleIndexed.evaluate, that the final round's (half=1) eq·aggregate agrees with GatesComplete.evalCombined, and that
  when eq cell = Norm.eqEvaluation(gateTau,gatePoint), claimed cell = prover cell, and alpha = gateAlpha are explicitly assumed,
  it agrees with the acceptance expression of Verifier.gateTerminal/Integrated. Theorems restricted to an honest prover are
  displayed as such. The degree ensure 80-83, the tau-provenance of the eq table, coefficient interpolation, the transcript, and WHIR/PCS are not proved.
- Integrated.verify checks the checked norm shape, the 7-challenge layout, and the Some of all gate computations on the same input,
  and then proceeds to Verifier.verify with packed/norm/eq/gate made concrete.
  Use of modelEngine alone does not carry this guarantee, and getD zero is merely a totalization to the old interface.
  The metadata decoder is an observation that accepts only the fixed Config.gatesEncoding, and it does not make concrete
  the initial FS, the configuration hash, or the WHIR tail.
  The public input hash was made concrete in PublicInputHashBinding. On top of the adopted Poseidon permutation it builds
  the real hash-no-pad sponge (rate 8/capacity 4/width 12, overwrite mode, ⌈len/8⌉ chunks,
  a short trailing chunk overwrites only the occupied slots, a 4-element digest, empty input means zero permutations), and proves that in all 30 rounds
  c1=c2=0 is maintained and that reading out c0 does not lose state. It also models the preflight on raw public inputs
  (a 256-word cap and each word < p, with no reduction performed on rejection), and shows that on accepted words it is the identity.
  This replaces the gate terminal's hash observation with a concrete function and gives a corollary that removes the hashLength assumption of GateChainHypotheses.
  Because Solidity hashes calldata at `MleVerifierV2.sol:382`,
  the check at `PoseidonGate.sol:77` protects the external library entry point, and within verify
  `_copyCanonicalBase` scans the same calldata first, so it is defense in depth. The order of the two scans is not modeled.
  Rust is canonical by type and so has no range check, and the 256-word cap is Solidity-only.
  The correctness of the permutation as a value depends on the claims of the adopted PoseidonConstants and on one row of external test vector.
  The failure classification/order of the additional preflight are model-level. They are not connected to implementation exceptions or slashing evidence.
  The lookup rejection of Gates.rustAdmission is also not connected to this entry point.
  IntegratedTerminalChain connects the adopted OuterClaimChain/NormTerminalBinding/GateTerminalBinding/
  OpenedClaimFold to Verifier.verify/Integrated.verify without reimplementing them. Under named assumption structures
  (HonestNormProver: shape/fresh/positive/bindings/rounds/zero cube sum; NormTerminalProvenance: eq/subgroup
  cells, challenges, rounds, claimed cell = prover cell; GateChainHypotheses: the gate table's shape/bind/cells and
  the grid-agreement assumption of OuterClaimChain; HonestOpenings: claimed cell = the row fold of each column), it derives for an honest prover that
  logTerminal = the final logClaim of derivedRounds, gateTerminal = the final gateClaim, the 5 WHIR expected claims = the dense evaluation of the padded table
  and that the 6th cell is none, and by the reverse lemma verify_of_checks of verify_success_checks it shows that
  Verifier.verify/Integrated.verify accept. The remaining hypotheses are only the observations enumerated as ObservationOnly
  (chain/config hash/envelope/deployment/shape/4 lengths/verifyWhir/7 challenges/normShape).
  The Rust order (WHIR→norm terminal) and the Solidity/Lean order of acceptance are equivalent at the level of Prop; revert reasons and gas are not addressed.
  The grid assumption is an honest-prover assumption implying the endpoint-sum agreement of the gate running claim, and agreement of claimed values with prover cells,
  and PCS/WHIR soundness, remain assumptions.
  EqTableProvenance models the real eq-table builder (the identical loop nest in gate_ext3_v2.rs 26-39 and norm_logup.rs 360-374;
  not byte-identical, differing only in binder names; eq_poly.rs is the base-field version of the old path), down to the tau-ordered outer loop, the index inner loop,
  left-side accumulation, and factor selection by (i>>j)&1, and proves that each entry is the adopted Norm.booleanRowEq, and that
  from the 2i/2i+1 pairing of the adopted bindBuffer the low-order bit is bound first.
  After all points are bound, the eq cell equals Norm.eqEvaluation(tau,point), and since the subgroup column is a geometric sequence that the verifier
  does not fold but instead takes the product of (1-r_j)+r_j·g^(2^j), it proves that this product equals the fully bound cell/Packed.fold.
  This gives a corollary that removes the eq/subgroup provenance assumptions of NormTerminalBinding/GateTerminalBinding.
  That the VK's subgroup_gen_powers are the repeated squarings of the table's generator was discharged in VkSubgroupProvenance.
  The transcript-provenance correspondence is treated in TranscriptProvenance.
- VkSubgroupProvenance models plonky2's two_adic_subgroup (TWO_ADICITY=32, the fixed two-adic generator,
  the order-2^k root via exp_power_of_2, the enumeration order of powers()) and the VK generator derivation (verifier_v2.rs 134-143,
  the identical loop in prover_v2.rs). Since the adopted GoldilocksDomain's generator 7 is a different object from plonky2's two-adic generator,
  the order 2^32 of the fixed generator was established from two power certificates actually evaluated by the kernel.
  On that basis it proves that the recomputation check of verifier_v2.rs 130-147 is equivalent (in both directions) to "the VK's powers are the repeated
  squarings of the derived generator", and moves EqTableProvenance's SubgroupPowersProvenance from an assumption to a theorem.
  Multiplication on the base side is handled by Arithmetic.mul without adding a new instance, and the reverse direction is closed by injectivity on canonical limbs.
  It also shows that the unwrap_or at verifier_v2.rs 136 is unreachable for 1≤nLog, and that for nLog=0 it agrees with the derived value.
  The remaining assumptions are two: that degreeBits agrees with the variable width of the norm state, and that the prover-side subgroup sequence is
  the embedded two_adic_subgroup; both are visible fields.
  The source panics for n_log>32 whereas Lean's truncated subtraction accepts it, so the iff is faithful to the implementation only in the
  range degreeBits≤32, and it is noted that this is unreachable because the envelope forces degreeBits≤13.
- TranscriptProvenance proves, from the single hypothesis DerivedInitial that "the engine's initial transcript is the real derivation of OuterInitial itself"
  (identical to the assumption already taken by the adopted OuterAdapter.execute_matches_existing_derived_context, and rfl under withInitial),
  that Norm.challengesFromInitial returns the 7 derived challenges as they are, that the log tau sequence, gate tau sequence, and gate alpha are the derived values, and that each challenge
  sits at the source's digest/counter position (eta 0, beta 0, gamma 3, xi 0, lambda 0, rho 3, kappa 6,
  log tau 9+3i, gate alpha 9+3d, gate tau 12+3d+3i).
  This reduces IntegratedTerminalChain's ObservationOnly from 12 items to 9, and
  reduces each of the assumption sets NormTerminalProvenance, GateChainHypotheses, and NormColumnProvenance by one.
  The hash remains an arbitrary deterministic function; injectivity, uniformity, and random-oracle properties are not used at all.
  That is, this is identity of ordering and hand-off, not Fiat-Shamir soundness.
  The gate's hpt is not a discharge but an equivalent restatement (hpoint), and remains an assumption.
  DerivedInitial itself, and agreement with the prover-side challenges, remain assumptions.
- Connections is the concrete connection of types and folds between Lean models. It does not mean that every Engine was concretely implemented.

## Incomplete overall proofs (in priority order)

1. Connect the already-concretized WHIR initial/first sumcheck, intermediate rounds, and inner bytes/PoW through to the terminal, and
   connect the authentication to Plan/Context and the fixed VK/root/point. Prove raw row bytes→leaf hash→multiproof→
   the disclosed path of each query→the terminal comparison as a single execution path. The binding of raw row→multiproof→path→
   decode/dot, the intermediate round sequence, and the derived Context of the restricted 3×1 tail are connected.
   The full-execution equivalence of the indexed quicksort/compaction, and the projection from a single typed configuration to all phases, are connected.
   Source/compiler refinement and the connection to the outer integration entry point remain open.
   The mathematical order of the fixed generator is proved, but the generation correspondence from native dependencies/codegen is also in scope.
   A concrete success at the installed level was first exhibited by WhirTailWitness: with both the 3-claim and the deployment-arity 6-claim versions,
   `WhirConfigured.run` / `InstalledWhirTail.tailRun` succeed, and `Verifier.verify` with both `parseWhir` and `whirTail` installed
   also accepts by `rfl` (`configured_six_claim_execution_example`,
   `installed_whir_pair_accepts_a_full_verification`). However, this uses a constant toy hash, `exampleNoRounds`, and
   `Verifier.testConfig` (1 variable), and the connection to `DerivedAcceptance.derivedConfig` (21 variables) and the real PoW of the
   deployment profile are not constructed. The mask `[⟨31⟩]` vs `[⟨7⟩]` was not the blocker; the number of claims was the actual obstacle.
2. Prove the connection from the expressions of all 14 gate evaluations to real polynomial degrees, gate semantics, and the sumcheck.
   The real expressions of all 14 families/the configured row degrees, the total row sum and the Boolean suffix sum, and the outer coefficient recovery and totality of interpolation
   are connected, and the commutation with Rust's slot-first ordering and the grid transposition of current_round are also connected, but
   this does not amount to having completed the unification of the interpolation calls, the provenance from the DenseMle endpoints, or the connection to the circuit truth chain.
   The proved equivalence of the PI cache and the entry-point connection of selector/lookup are also reflected in the overall path.
   Coverage was fixed as a theorem in GateEvaluatorCoverage. The complete dispatcher used by Integrated evaluates all 14 families and
   the degree bounds line up as well (the base Gates' partial dispatcher covers only ids 0,1,2,3,6,7. The note in ExplicitEngine gets this
   distinction wrong and will be corrected in the next doc update). The declaration table is transcribed from gate_ext3.rs and Plonky2GateEvaluatorExt3.sol,
   agrees with the adopted requirements, and also agrees with plonky2's num_constraints/num_wires/degree for each gate.
   For degrees there is no divergence, since in Rust too validate_gate_ext3_context checks the same inequality with Gate::degree().
   The shape-checked evaluator intrinsically excludes default-value evaluation of short rows, and on validated rows it agrees with the complete dispatcher.
   Finding: RandomAccessGate's 124-constraint row (bits 1, copies 18, extra 70) passes the individual checks but is excluded by configuration validation and
   the envelope's 123 (MAX_GATE_CONSTRAINTS_V2) (it does not affect the sumcheck round degree; it only increases the alpha-Horner
   root bound by 1). BaseSum with base 16 or more cannot be configured, by the accounting degree = base. The lookup family has no gate id.
   Circuit truth (constraint vanishing = satisfaction by a real witness) is still not claimed.
3. Connect setup/VK/config generation, the immutable store, the whole compact decoder, the metadata decoder,
   the initial transcript, the true challenges, and the public-input hash to Integrated.
   Do not mistake WhirFinal/Merkle, currently separate modules, for a replacement of the whole whirTail.
4. Connect the proved primality and the concrete Ext3 finite field/inverse to the execution semantics of Rust/Yul, and
   replace the manual comparison with formal refinement. Also apply the in-model proof of evalL0 to all call paths.
5. Prove all stages of the honest prover, completeness, and composition with the recursive circuits/parent statement.
6. Prove quantitative soundness of PCS/Fiat–Shamir/grinding with the cryptographic assumptions stated explicitly.
   Do not assume that every hash has unconditional mathematical security.
   ConditionalSoundness is a first step in this direction, not a completion.
   It enumerates 18 assumptions (adaptive fixedness, the challenge law, the extracted tables and their shape/truth chain/
   structural correspondence of the final round, the provenance of eq/subgroup/lambda/wire-map/transcript,
   the extraction seam that the terminal's claimed values = the prover cells) as visible fields, and derives that
   if Integrated.verify accepts and at no round of the log lane does the drawn challenge fall into the bad set, then
   the endpointSum of the extracted table is 0. This is the proposition that IntegratedTerminalChain assumed as
   HonestNormProver.zeroSum, and it is derived without circularity.
   The cardinality of the bad set is at most 195·⌈2^256/p⌉³ (195 is derived from degreeBits≤13 and quotientDegree+2≤10).
   **Serious limitation**: the gate lane is not proved. The first draft's gate conclusion was degenerate and has been deleted.
   GateDenseRound discharged three obstacles, and GateClaimChain handled (1) the multi-round induction, (2) the reversal of direction, and
   (4) the terminal bridge, while ZeroCheckSemantics handled (5) the semantic stage.
   GateClaimChain derives, from acceptance and the absence of gate-lane bad events, that the cube sum of the extracted table = 0, and
   also re-instantiates the gate-lane-specific bound (q+2)·degreeBits (ConditionalSoundness's 195 does not
   apply to this lane). ZeroCheckSemantics proves that the zero density of the multilinear extension of the adopted eq is ≤ n/|F|, and
   gives a corollary that for tau outside the bad set each row value is 0.
   **However, gate soundness is not complete.** At present the theorems of GateClaimChain have no rejection power against an adversarial
   supplier. The assumptions fix only one linear functional of the eq table (the bound cell), and since the row sums with cube weights are independent,
   one can choose an eq table with the correct bound cell but with row sum 0. There are other degeneracies of the same kind, and
   `numGateConstraints=0` (the envelope imposes no lower bound, and the adopted example config is this) was
   excluded by visible assumption 4, but a path that zeroes out all selector filters remains.
   Furthermore, ZeroCheckSemantics' bad set does not compose with the adopted badSets (it is a single challenge against an n-tuple, and
   the n-fold product event is not constructed). Because the bad set is indexed by the prover's own table, handling adaptive choice is also required.
   Fixing the gateTau provenance of the eq table across all rows was handled in GateRejectionPower.
   It proves the partition of unity of the adopted eq (the row sum over the cube is identically 1), and derives that if the eq column is
   fixed to `eqTable tau` for all rows then no eq table with row sum zero can exist. Attack scenarios (zero eq column, zero row sum,
   zero constraint count, shape mismatch, zeroing of all selectors) are each presented as theorems, and
   it is shown by concrete examples that the strengthened assumptions reject forged states that the old assumptions accepted.
   AlphaZeroCheck identifies the coefficients by treating the row aggregation as a polynomial in alpha (the coefficients are the slot values themselves),
   derives from the envelope that the number of roots is ≤ numGateConstraints−1 ≤ 122, and shows that for alpha outside the bad set each slot value is 0, and that
   a gate whose filter is nonzero has its constraint itself equal to 0. The composition of both zero-checks, for tau and for alpha, is also proved
   over the adopted challenges (alpha is drawn at a counter before the gate tau).
   Partial zeroing of the selector was made explicit as a provenance chain in ConstantsProvenance. selector value ← the supplied constants sequence
   (a source-bounded get? read, with no getD default) ← the bound cell at the derived gate point ← the claim of gatePreprocessed.take numConstants
   ← the bound cell of the committed column ← the opening under the preprocessed root ← the deployment pin (Verifier.shape's
   `p.preprocessedRoot = pin.preprocessedRoot`, verifier_v2.rs 184-187, MleVerifierV2.sol 563).
   Attack theorem partial_zeroing_forces_one_of_three: if the bound cells of the supplied column and the pinned column differ at the derived gate point, then
   necessarily one of root mismatch (closed by the pin), a break of the extraction seam CellsMatchClaims, or a break of the opening relation OpensCommittedTable
   occurs. With a concrete forgery example (zeroing only the important rows), it is shown that the old assumptions (activeFilter etc.) do not detect it but
   the new chain catches it at the seam. The strongest gate theorem was restated with the filter over the pinned column.
   The gap between bound-cell agreement and column identification was treated in GatePointZeroCheck as Schwartz–Zippel over the derived gate point.
   By the bridge cell(bindColumn col point) = extension col point (which holds for 2^|point|≤|col|; with a counterexample where it breaks for short columns because bindColumn
   truncates while extension zero-pads), the agreement set of two columns is the zero set of the multilinear extension of the difference column, so if the columns
   differ on the cube then the cardinality is ≤ n·|F|^(n-1) and the mass under the uniform product law is ≤ tauTerm n. Composition theorem: if the columns
   differ and the derived gate point is outside the agreement set, then under acceptance either the extraction seam CellsMatchClaims or the opening relation OpensCommittedTable
   is broken (the root branch is closed by the pin). The width 2^degreeBits of the supplied column is derived from the adopted Consistent+EqCellBinding, and
   the width of the committed column from the full condition of the opening relation; there is no additional width assumption. That the gate point sequence is the
   gate lane's round challenge sequence itself is proved in the abstract engine, and as the 4th family of JointChallengeSpace
   one obtains mass ≤ tauTerm d over the outerGate coordinates.
   The reading in which the supplied column is chosen after seeing part of the point was handled in AdaptiveAgreementFamily. It decomposes the agreement set into coordinatewise
   Schwartz–Zippel (each coordinate's bad set is the roots of the affine restriction, of cardinality ≤1; the identically-zero case is not counted but charged to a preceding coordinate),
   puts it on the adaptive engine of OuterSequentialConditioning, and, with the supplied column a function of only the first `cut` coordinates, obtains
   mass ≤ tauTerm d and a combined bad event including the 5th family ≤ combinedBound + tauTerm d (≤2^-171 at the envelope extremes).
   **However, it closes only in the form of a dichotomy**: either the extension of the difference column is identically zero on the affine slice through the realized prefix, or
   the point falls into a set of mass ≤ tauTerm. The former can be constructed by a forger who has seen only one coordinate
   (with a column of the form cc+(x0 / −(1−x0)) the 5th family becomes empty; proved as a formal residual witness), so the residue class passed to R2/R3
   is "columns that agree with the extension of the committed column on the slice through the realized prefix", and it is not necessary to wait for all coordinates.
   What is newly covered is only adaptive choices that preserve the residual (that the cost of choosing among many different columns is only tauTerm).
   At cut=d the event is empty and the bound is vacuous; at cut=0 with a constant colOf it coincides with GPZC's fixed-column reading.
   Lane-level frozen comparison was proved under DrawEncodesRun as a two-directional equivalence per lane (closing OSC's unproved item).
   **Still open**: the supplied column s0.tables.constants is not bound to a root except in the conclusion's two branches (R2/R3)
   (half (B) is not formalized).
   That the round digests chain after the prefix is documented only in the concrete engine (not derived in the abstract engine).
   Engine opacity R1, the opening relation R2, and the root→column map R3 remain visible assumptions.
   Binding of tau was treated in GateDerivedRejection. The rejection theorem and the composition theorem were restated with the
   transcript-derived gate tau/alpha (under DerivedInitial, the eq column fixed for all rows to the eqTable of the derived tau, the cube index derived
   from the adopted column length), and the bound-cell assumption was derived from whole-table eq provenance and structural binding fields, giving
   a reduced assumption set of 9 fields containing no free challenge values. Only §2 is an exception, where it keeps
   an implicit free alpha and only makes tau concrete. Three challenge-side assumptions remain: two hgood assumptions about the
   derived tau/alpha, and the adopted BadEventFree about the sumcheck round challenges.
   These remain assumptions, not probabilities.
   The deterministic half of adaptivity was handled in CommitmentOrder. The prefix absorbed before the squeeze of gate alpha/tau
   is 22 frames, agrees with the adopted relationState, and the preprocessed/witness/norm-inverse roots are
   the 13th/15th/19th, with only two fixed domain tags between the last root and the squeeze (checked against the implementation's
   MleVerifierV2.sol 400-455 and verifier_v2.rs 233-275). It shows, without assuming collision resistance, that the gate's bad set does not depend on the eq column and
   depends only on the committed wire/constant columns, and that changing the tables while preserving the prefix digest requires a concrete
   transcript collision. The probabilistic half (that the squeeze is uniform and independent relative to the prefix) is refuted by a counterexample for a constant hash,
   so it cannot be obtained by an ordering argument and remains a hash assumption. The gate list, the configuration, and the public input hash are fixed parameters, and
   their provenance from the config/VK digest is not proved here.
   The union bound was handled in ChallengeUnionBound. It lifts tau's zero-check bad set to the product event over n independent digest triples
   (applying the adopted single-coordinate fibre bound coordinatewise, exponent 3n; the independence of the n is
   an explicit product law, not a property of Keccak), lifts the per-row alpha bad set to a union over 2^n rows to derive cardinality ≤ 2^n·(numGateConstraints−1) ≤ 122·2^n, and
   together with the outer sumcheck terms (norm 5·d, gate (q+2)·d) bounds the sum of the three masses. At the envelope extremes
   (degreeBits 13, q 8, constraints 123) it is expanded as an equality and proved ≤2^-172 by exact rational computation.
   **How to read this number**: the margin is about 0.07 bits, right at the edge of the envelope (it breaks at degreeBits 14. For the constraint count it holds up to 123–128 and first breaks at 129; the earlier "125" was a typo), and
   since it does not include the WHIR/Merkle terms it is not the system's soundness error (the design point is about 100 bits). The three terms were a sum of masses
   over different sample spaces. Rows whose filter is zero are unconstrained, which is
   correct behavior for rows outside the selector range.
   The joint event was formalized in JointChallengeSpace. It defines a uniform counting measure on `Draw d → DigestTriple` indexed by the squeeze schedule
   (gate alpha, gate tau ×d, outer log round ×d, outer gate round ×d, for 3d+1 coordinates in total; the log/gate rounds are separate squeezes at counters 0 and 3 of the same round digest),
   proves the masses of the coordinate events and the tau product event by counting, and proves that the mass of the true disjunction event is ≤ combinedBound (joint_union_bound; the outer terms cover the 2d coordinates of both lanes).
   The seam `DrawEncodesRun` is a coordinate-encoding claim that "a run's challenges are the coordinatewise reduction of a single point", and it is shown as a lemma that
   by surjectivity of reduceTriple it is inhabited for every hash, every engine, and every accepting execution.
   Therefore it is **not a hash assumption**. The Fiat–Shamir half (B) = "the encoded draw follows the jointProbability distribution" is
   nowhere expressed in Lean, and the composition theorem carries no cryptographic assumption at all (the mass conjunction is a counting fact,
   and the conclusion's conjunction is the implication "if a run's draw is outside the bad set then the constraints vanish"). The outer rounds' bad sets are relative to the realized
   challenges and round messages; only the tau/alpha families are prefix-constant.
   Sequential conditioning was proved in OuterSequentialConditioning. It instantiates a general engine over a finite product space (a Nodup coordinate sequence,
   a PrefixDependent family where round k's bad set depends only on preceding coordinates, peeling by Fubini giving mass ≤ Σ c_k/|A|) to both lanes via a `Lane` that makes the
   round messages functions of the preceding challenges. The scan order is per round, log→gate, as in the implementation (both challenges are counters 0/3 of the same round digest, and both messages are fixed in advance by a single commit.
   The model allows the gate message to see the same round's log challenge, thus treating an adversary stronger than the real one). The mass of the adaptive
   outer event is ≤ outerTerm, the same number as the prefix-frozen version, and the adaptive combined bad event ≤ combinedBound. The frozen
   laneEvent is a special case of the engine and re-derives the adopted joint_union_bound (the lane-level frozen comparison requires
   DrawEncodesRun and is not proved). The sequential-conditioning part of ConditionalSoundness ASSUMPTION 3 is closed by this, but
   the law is still a hand-written ideal uniform distribution, and half (B) is not formalized. schedulePosition is the module's own map, and while alpha/tau are
   fixed via DerivedInitial, the labels of the outer round coordinates are only documented relative to the abstract engine.
   Binding to accepting executions was handled in AttachedUnionBound. The tau arity is derived from degreeBits (derived_gate_tau_width),
   the row values are gateValue, the alpha-side coefficient family is the acceptance-derived slotCoefficients, and the constraint count ≤123 is derived from acceptance, and it shows that
   the attached tuple is the transcript's derived tau sequence itself (attached_tau_tuple_ofFn) and that
   avoidance of the attached bad set is equivalent to the adopted GoodDerivedTau/GoodDerivedAlpha.
   combinedBound is monotone in all four arguments (by ⌈2^256/p⌉·p≥2^256), and under the envelope
   ≤ combinedBound 13 8 13 123 ≤ 2^-172. attached_seam combines the counting bound and "if the derived tau/alpha are outside the attached bad set then
   the constraints of the selected gate vanish on every row" into a single theorem. The law is still an explicit ideal uniform distribution, and
   the product structure of tau is itself the independence assumption; it gives no bridge to the real transcript (Fiat–Shamir half (B)).
   195·(⌈2^256/p⌉/2^256)³ ≈ 2^-184 is only the agreement event of the outer sumcheck, and does not include the dominant WHIR/Merkle terms.
   The implementation's design point is about 100 bits, and this number must not be quoted as the system's soundness error.
   failure is a free rational bounded only from above, and no field gives a bridge to a real probability.
   The 1st and 4th conjuncts are not composed, and the probability space concerning executions is not in this file.
   Satisfiability of the Assumptions as a whole is not shown, so depending on the instantiation it could be vacuous.
   The seam between extraction and commitment was partially handled in OpeningBinding. It reduces the statement that two accepting openings with the same root/index/depth
   return the same raw row, decoded values, and dot to injectivity of the hash on finite lists computed from the execution alone
   (not free variables; it is also confirmed that the theorem does not become vacuous under instantiation to the empty list).
   This is binding, not extraction. The extraction claim "there exists some committed table of which it is the evaluation" requires an extractor, and is not proved here.
   Assumption 17 is rewritten as a biconditional, but the residue is at the fold level
   (the bound cell value at a point), which is weaker than identification of the column. Further limitations are stated explicitly as theorems.
   Since an opaque engine's WHIR check accepts an arbitrary context and proof, the binding result does not connect to outer acceptance until it is replaced by a concrete
   WHIR verifier. Because the opening relation holds even when the three Merkle roots are replaced arbitrarily, this relation cannot be derived from
   sameness of roots. There is also as yet no theorem tying a decoded row to any field of p.used.
   Engine opacity was handled in InstalledWhirTail. It installs the adopted manual WHIR tail model `WhirConfigured.run` into
   Integrated.modelEngine's `whirTail` (parseWhir, configurationHash, deploymentValid,
   initialTranscript, commitRound, sampleIndices, publicInputsHash remain observations; transcript/round are unchanged),
   and derives from acceptance the success of the concrete tail execution, that the 3 roots are [pinned preprocessed, witness, normInverse], and that the initial evaluation value is
   the packed fold of the 5 bound cells. The session/instance (instance is empty), the claim mask `[31]`,
   the overwriting of the evaluation points by ctx.points, and the invertibility of the root byte conversion have been checked against the implementation. For the deployment profile (the v2 fixture has
   numRounds∈{1,2,3,4}) it proved, through OpeningBinding's entry point (openGroups), that the 3 roots are opened at intermediate round 1, that the row at each root position is
   Merkle-authenticated with `(initialOpen wp).merkleDepth`, and that two accepting executions either return the same row bytes for the same root and same leaf index or yield a concrete collision
   (non-emptiness of the indices is also derived under inDomainSamples>0). The final-split path for numRounds=0 is listed separately and is not the deployment case. This engine actually rejects the empty-hint example.
   **Still open (R1b)**: "if the final check passes then the expected value equals the multilinear evaluation of the authenticated rows" was made a visible assumption as the existence of a fixed function
   extracting the column family from the 3 roots and the round-1 opening alone (TailExtractsCommittedTables). It corresponds to WHIR proximity, list decoding, and
   sumcheck soundness (probabilistic), and is not formalized. Because the per-column form subsumes R3,
   a fold-level variant is also stated. `wp` (the WHIR parameters) is a free parameter of the engine; in the source it is fixed
   by the profile digest, but in Lean it remains an observation. R2 is unchanged.
   Fixing `wp` was handled in PinnedWhirProfile. It installs the 4 constraints of `CanonicalWhirProfileV2.validateCanonical`
   (1≤numVariables≤21, sessionId, `keccak256(abi.encode(config.whir))` = row[0:32] of the table, protocolId = row[32:96];
   MleVerifierV2.sol 150-153) as a concretization of `deploymentValid`, and derives from acceptance the canonicality of the decoded wp,
   agreement between the record on which the tail ran and the checked record, and numVariables = degreeBits+indexBits. Because the source does not
   syntactically enforce `inDomainSamples>0` anywhere, positivity and numRounds≥1 are derived only for the two transcribed rows
   (n=10, n=21; agreement confirmed by keccak recomputation of the fixture and the generated table) under the table's semantic assumption
   `TableIsCanonical` (correspondence of the row digests, with rowSeparates standing in for keccak injectivity). The other 19 rows are digest-only and
   not transcribed (they can be added mechanically from the generator). `c.whirEncoding=c₀.whirEncoding` is stated as an idealization of `_requirePinnedConfiguration`
   and a residue of keccak injectivity. keccak itself, the VK immutable store, and the Rust/Solidity refinement of the decoder are not modeled.
   The index-point sampler observation was made concrete in InstalledIndexSampler. The adopted checked sampler
   (OuterAdapter.sampleResult: absorbing the used claims with the domain separator "pcs-constituent-claims-v3", 5 frames of tag 6
   (log preprocessed/witness/normInverse, gate preprocessed/witness) and an empty vector, and the separator
   "pcs-constituent-index-v3", then squeezing from a single digest with counter 3i for log and 3·indexBits+3i for gate;
   checked against prover_v2.rs 144-164, verifier_v2.rs 303-311, MleVerifierV2.sol 458-476) was totalized over decode and
   installed into the installed engine. It proves that the prefix before the index squeeze is the round state ++ the claim frames, that if the index digests
   are equal then either the state digests and used claims are equal or a concrete transcript collision is produced, that both lanes have length indexBits,
   and that the logIndex/gateIndex items of ObservationOnlyDerived become theorems. With this,
   the ordering aspect of R3, "the index is drawn after the cells", became a theorem, but the probabilistic stage in which a forged cell family fails at a fresh index point
   is not proved, and R1b/R3 stand as they were. The decode assumption is inhabited by executions under the adopted CommitAgrees and by the fixture.
   The coordinate space of the index points carries only a coordinate claim, with no law attached. commitRound, parseWhir, configurationHash,
   initialTranscript, and publicInputsHash were installed in InstalledInitialTranscript. On top of the sampler engine it places
   `initialObservation := OuterInitial.derive` (the adopted derivation for `Verifier.statement p`) and
   `publicInputsHash := PublicInputHashBinding.hashNoPad`, obtaining a single engine in which 8 fields are simultaneously concretized.
   `DerivedInitial` itself was already given by the adopted `withInitial_derived` by rfl, so the novelty is in the composition,
   and in this engine the 36 downstream `hderiv` occurrences and PublicInputHashBinding's `hsub` become unconditional
   (restating the main theorems of GateDerivedRejection, AttachedUnionBound, JointChallengeSpace's composition theorem, ConstantsProvenance, and
   CommitmentOrder. `hacc` is a stronger hypothesis, being acceptance under the concrete engine). The derivation does not read the engine's other
   hooks (the public inputs are absorbed as raw values in frame 3), and verify reads the hooks only via initialTranscript.
   For an accepting proof it also derived that the public inputs satisfy Solidity's 256-word cap and the per-word < p check. The remaining observations are
   commitRound, parseWhir, configurationHash, and deploymentValid. Agreement with the prover-side challenges (an assumption about the prover's
   Prepared record) does not disappear with verifier-side installation. The hash remains an arbitrary deterministic function, and
   injectivity, uniformity, and random-oracle properties are not used (this is identity of ordering and plumbing, not Fiat–Shamir soundness).
   The round commit observation was made concrete in InstalledRoundCommit. The adopted checked round commit (5 frames:
   the domain separator, the round index (u64), tag-6 frames for the log/gate messages, and the separator; the log/gate challenges from
   counters 0 and 3 of the round digest; matching transcript_v2.rs 133-146 and TranscriptV2.sol 247-261) was
   totalized over decode and installed into the sampler engine, turning `CommitAgrees` into a theorem. The derived rounds agree with the adopted
   OuterAdapter.execute (the remaining assumptions are the initial transcript observation and degreeBits≤13), and it proved that the round digests
   chain 5 frames at a time after CommitmentOrder's 22-frame prefix and are drawn from counters 0/3, that the lanes'
   challenge sequences are reductions of the real digests, and that altering a round message requires a concrete transcript collision.
   With this, GatePointZeroCheck's RES-4 and JointChallengeSpace's outer counter labels became theorems in this engine
   (the sourceBlock numbering and the position of the index block remain labels). **Limitation**: the envelope allows
   indexBits=0 when the width c=1, and in that configuration the index-length guard lets through the decode-failure path (all-zero challenges, an empty index lane).
   However, under the initial transcript observation and degreeBits≤13, every snapshot decodes, so this module's theorems
   do not reach that path (it is live only in engines whose initialObservation is not derived). DrawEncodesRun remains
   a coordinate claim, and it shows as far as that the lanes' values are reductions of the real digests. Composition with the installation of the initial transcript and publicInputsHash
   (InstalledInitialTranscript) was carried out in ComposedEngine. It gives a single engine in which 10 fields — modelEngine's 4 evaluators, whirTail
   (PinnedWhirProfile's pinned record), sampleIndices, initialObservation, publicInputsHash, commitRound, and
   deploymentValid — are concretized, leaving only 2 observations, `parseWhir` and `configurationHash`.
   Identity with each installed engine is shown by 5 rfl's, the initial transcript assumption carried by InstalledRoundCommit's 9 theorems disappears by rfl,
   and degreeBits≤13 and the shape assumptions are derived from acceptance. The summary theorem derives 16 conjuncts from acceptance,
   TableIsCanonical, and the transcribed rows, and each conjunct is only an application of adopted theorems and contains no new proof content.
   The abstract parseWhir can drop a good proof but cannot let through an incorrect root (the tail does not read the parsed record; WhirInitial checks the root it reads
   from the transcript against ctx.roots. Only the preprocessed root is deployment-pinned).
   The lengths of protocolId/sessionId are included neither in the envelope nor in the canonical checks, and the existence of a checked execution requires those 2 assumptions.
   The indexBits=0 failure path is unreachable in this engine. The limitations of R1b/R2/R3, half (B), keccak, and TableIsCanonical are unchanged.
   The parseWhir observation was made concrete in InstalledWhirParse. It is defined as a projection of the adopted WhirInitial.phaseInitial→WhirPrefix.run→
   WhirTail.runPrefix (initial phase, initial sumcheck, intermediate rounds) (actualRoots is the first root of the transcript,
   boundRoots the second, claims the readClaims with mask 0x1f; checked against whir_pcs.rs 1514-1556/1586-1614 and
   SpongefishWhirVerify.sol 374/384-387. There is no new modeling), and it proved that verifyWhir is equivalent to prefix success ∧ root agreement ∧
   claim agreement ∧ tail acceptance, that the root condition is contained in prefix success and is redundant, that the transcript byte sequence carries 2 roots at
   positions k·stride (stride = 64+24·outDomainSamples·numVectors) and +32+24·(…), that a transcript whose leading 32 bytes differ from
   the encoding of the leading root (or are missing) is rejected, and that parse and tail read the same prefix execution
   (tailRun = prefixRun.bind runTail, definitionally). The leading root of derivedContext is the proof's
   preprocessedRoot, and under acceptance it agrees with the pin by the shape. Combined with ComposedEngine the remaining observation is
   only configurationHash (this module does not perform the composition). WhirContext's protocolId/sessionId/parameters and `wp` are
   still free (fixed by the profile digest in the source, observations in Lean). R1b/R2/R3 are unchanged.
   The probabilistic stage of R3 (per-column identification) was given as a dichotomy in IndexPointZeroCheck. By the bridge between the packed fold and the multilinear extension
   (cells length ≤ 2^indexBits, both LSB-first with no reversal), the set of index points at which the packed folds of two cell families agree
   is the zero set of the difference, of density ≤ indexBits/|F| and mass ≤ tauTerm indexBits under the uniform product law. Under the fold-level relation,
   either the supplied cells agree with the opening of the committed column (HonestOpenings.opened itself) or the derived index point falls into an explicitly
   bounded set, and the bound cells i∈Fin 5 cover both lanes. For equal widths, the agreement set is everything ⇔ the columns are
   equal (injectivity by Boolean-point interpolation), so the residue class is empty. The committed width is an assumption (HonestOpenings.capacity gives
   only ≤), and since a difference can be hidden by zero-padding if the widths differ, a variant concluding identification up to trailing zeros from the capacity alone
   is also stated as a theorem. The cells are
   absorbed before the index squeeze (the ordering of InstalledIndexSampler), but half (B) is not formalized.
   The law on IndexSpace exists only in joint form, with no sequential form. R1b (at the fold level) and R2 are unchanged.
   The last observation, configurationHash, was installed in ExplicitEngine, giving a verifier model with no abstract base engine.
   All 12 fields are functions of (gdec, hash, thash, khash, P, c₀). The config digest is `khash ∘ encodeConfig`, and
   `encodeConfig` mirrors the field order of Solidity's `abi.encode(VerificationConfig)` (8 circuit scalars,
   publicInputWireMap, kIs, subgroupGenPowers, gates, whir), but is not byte-identical, on 3 points: the omission of offset words, the opacity of gates/whir,
   and Nat vs uint256 (keccak is not modeled). The encoding is injective on the 13-field core (boundedness is derived from acceptance and the byte-length bounds of gates/whir), and
   digest agreement forces either core agreement or a concrete khash collision. Under acceptance the digest agrees with the pin's digest, and under the deployment assumption `pin.configDigest = khash (encodeConfig c₀)`,
   core c = core c₀ (up to collisions). PinnedWhirProfile's idealization assumption (whirEncoding agreement) becomes a theorem up to collisions,
   and it is recovered from acceptance even in an engine that drops that assumption. `deploymentValid` was reduced to just whirEncoding agreement and profileOk,
   on the grounds that the remaining deployment validation (the kIs/subgroup chain,
   gate evaluator and WHIR parameter validation, wire-map range) is constructor-only in Solidity. **This is a model of the Solidity path; Rust's mle_verify_v2
   revalidates kIs, subgroup powers, gates, circuit_config_digest, and the protocol/session ids on every call.**
   Validation of the gate evaluator remains as a consequence of acceptance. **Residue**: circuitDigest and circuitConfigDigest are not encoded
   (in Solidity they are fixed as immutables; in the model they are transcript inputs chosen by the attacker, belonging to the freedom of half (B)).
   gateRows is unencoded but is fixed by the length of the gates decoded on acceptance. hash/thash/khash are arbitrary deterministic functions, and
   all collision-type conclusions are explicit disjunctions.
   The remaining circuitDigest and circuitConfigDigest were fixed in CanonicalProofCheck. Of the 10 comparisons of
   `_requireCanonicalProof` that Solidity runs on every call, the only unmodeled one is the comparison of the proof's 4 circuitDigest words with the immutable, and
   circuitConfigDigest absorbs the immutable into the transcript at 430. Installing "both digests equal the deployment values" into
   `deploymentValid` (Integrated.verify checks deploymentValid via Verifier.verify. Under the verifyCall reading it is part of the deployment invariant, justified by immutables not being in calldata),
   acceptance forces, for all 19 fields, either `c = c₀` or a concrete khash collision (the 2 WHIR ids and the 2 digests have no disjunction).
   Frames 2/7 of the transcript absorb the deployment digests, and no free field remains in Config. Because `_validateConfiguration`
   enforces canonicality of the digest words, the `Fin modulus` model approximates Solidity's accepting set from below (on the safe side).
   What is fixed on the proof side is circuitDigest, protocolVersion, preprocessedRoot, and width; the witness/normInverse
   roots, the round polynomials, used, and the WHIR byte sequence are chosen by the attacker, constrained only by the shape's lengths and the tail.
   The Rust-side call boundary was handled in RustCallBoundary. It maps, line by line, the checks that `mle_verify_v2` runs on every call (the byte cap,
   digest lengths, the width profile, the caps on constraint count and degree, kIs, canonical subgroup powers, gates, recomputation of circuit_config_digest,
   the WHIR ids, the proof's circuit digest, etc.) to their Lean counterparts, and newly models the canonical chain of kIs (builder-derived values;
   a stricter under-approximation than the source because CommonCircuitData is unmodeled) and the recomputation of circuit_config_digest (a mirror image of the preimage,
   injective in 14 members) to define `rustDeployment`. Because the Rust boundary has no digest pin and
   the VK is the deployment itself, the Rust checks follow from Solidity-side acceptance (up to collisions), whereas the Rust checks alone do not
   yield Solidity's pin (whirEncoding has no input in Rust). On a deployment config both engines return the same result.
   rustEngine also reads the configurationHash/chainId guard and the pinned preprocessed root via the skeleton of Verifier.verify. Residue: the comparison of the VK dimensions and common_data, the wire-map range,
   the field order and D, and the absence of lookups are assumptions.
   **Cross-cutting finding (LocalizedCollisions)**: `TranscriptCollision`, `KhashCollision`, and `Khash2Collision`
   (∃ a b, a ≠ b ∧ hash a = hash b) are pigeonhole tautologies that hold for an arbitrary function from an infinite input domain to finite
   digests, and the second disjunct of `RowCollision` is likewise always true by a finite pigeonhole. The adopted theorems (37 + 17) described in this SCOPE and in the REPORT as
   "producing a concrete collision without assuming collision resistance" are, as statements,
   true without assumptions, and the audit content lies only in the two concrete inputs exhibited by the constructive proof. This is not a soundness defect but an
   overclaim in the form of the statement. The main theorems were restated with localized, falsifiable predicates (FrameFoldCollision, Index/RoundDigestClash,
   ConfigEncodingCollision, LeafCollision). To be fixed on the adopted-tree side:
   `ConditionalSoundness.no_row_collision_binds_opened_dot` is vacuous because its assumption ¬RowCollision is unsatisfiable
   (it should be replaced by local injectivity of the NoCollisionAmong type → already replaced in OpenedDotBinding. There are 0 use sites in Lean, so there is no consequence for soundness).
   Each description of a "concrete transcript collision" in this SCOPE is to be read as
   "a collision of two concrete inputs of that execution (a local predicate)".
   The first formalization of Fiat–Shamir half (B) was done in RandomOracleSqueezes. Taking the hash to be a uniformly random table over a finite set Q
   (the finite counting law of a random oracle), it showed uniformity of the projections at distinct inputs, uniformity of the scheduled squeezes conditioned on a fixed block digest, and a bad-draw mass ≤ combinedBound
   (proving satisfaction of the assumptions for d≤13, with a closed instance at d=13).
   It found that the block digest itself is an output of a frame query and is sequentially dependent, proved a congruence lemma from the prefix separation of frame/challenge inputs (the 15th byte), and obtained the run-level bound
   P[bad draw] ≤ combinedBound + P[a local collision of round digests] by Fubini over the frame fibre. **Limitation**: with the minimal closure witness the additive term is
   1 and vacuous; with a Q containing the execution's frame inputs it is <1 (existence only), a small bound is unproved (birthday-type counting), and an adaptive
   prover (p depending on T) is not covered. The first draft's non-adaptive theorem was discarded and reformulated because its assumptions forced every digest to zeroDigest, making it vacuous (the second detection of vacuity). It is ROM, not a property of keccak.
   The birthday-type counting of the additive term was advanced in BirthdayClashBound. It proved a fresh-query lemma (an equality for events not depending on the answer at q)
   and an adaptive version, an upper bound on the collision probability of a causal and fresh chain, and a collision probability ≤ 5d(5d+1)/2/|Block| for a chain model consisting of the
   5 frames of the round fold over a bounded-length query set (2145/|Block| at d=13) (freshness is proved from
   frame_injective, and the constant table belongs to the collision event). **Limitation**: the bound is over the chain model, and of the connection to the execution's
   actualChain, that the start of the chain threading the 22 frames of the relation prefix agrees with the digest of derive
   (collision probability ≤ 3828/|Block| over 87 stages) is proved, while the induction for concreteChain is incomplete and the run-level additive term remains an assumption (→ the induction was completed in ConcreteChainThreading and the additive term abandoned; see below).
   The localization theorems were strengthened to name the pair of frames at the same position in stageQueries.
   The connection between the chain model and the execution was completed in ConcreteChainThreading: stage 22+5r of the chain equals the digest after the first r messages of the adopted concreteFinal
   (by induction; since absorb reads only the digest of the input state, tracking the counter is unnecessary),
   `sourceDigest` is stage 22+5r+5 of the chain, and RandomOracleSqueezes' `clashEvent` is the same Finset as the chain model's
   `prefixRoundDigestClashEvent`, so the run-level bound's additive term is abandoned in favor of the birthday-type
   (22+5d)(22+5d+1)/2/|Block| (3828/|Block| ≤ 2^-244 at d=13), and `run_bad_draw_probability_le_birthday`
   leaves no probabilistic side condition under ROM for a fixed (non-adaptive) prover. With a closed witness (L=381) the RHS <1. What remains is
   the adaptive prover (fresh-query induction over strategies), the index lane (IndexLanesOracle handles it under a fixed digest),
   WHIR/Merkle, keccak itself, and the fact that these masses are not the system's soundness error.
   The index lane was placed under the same ROM law in IndexLanesOracle: stage 22+5d+8 of the extended chain with 8 claim frames added is
   the adopted indexDigest, and under a fixed index digest the pushforward of actualIndexDraw is exactly equal to the adopted indexProbability,
   the guarded index bad event is ≤ 2·tauTerm, the union of the joint family and the index family is ≤ combinedBound + 2·tauTerm under a fixed digest
   (since the index counters overlap the outer counters, separation is by digest only), and the extended chain's birthday bound is 4560/|Block| at d=13.
   What remains is the run-level Fubini for the union (the material for both draws having constant digests over the same frame fibre is in place), and
   the Lean-level connection of `hst` (that stage 22+5d is the post-rounds snapshot) (ConcreteChainThreading's `chain_model_is_the_run_chain` proves
   the same fact, but the two modules do not import each other).
   The run-level union bound was given in RunLevelUnionBound: ILO's `hst` was abandoned via CCT, and by running the frame-fibre Fubini once for both families simultaneously,
   P[jointBad ∪ guardedIndexBad] ≤ combinedBound + 2·tauTerm + P[clash of the extended chain] (4560/|Block| at d=13,
   RHS <1 in the closed instance, a good table exists). The failure set of the explicit engine's assembly conclusion is contained in a hash-indexed union event
   (unconditionally), but its mass bound is not attained: the covering assumption (that a fixed event dominates for every hash) is not known to be satisfiable on a non-degenerate execution and
   was deleted under this audit's anti-vacuity policy. The remaining bridge is the two-stage conditional counting for a fixed prover (the alpha-conditioned outer diagonal event, and
   index uniformity conditioned on the outer draw), which is a separate problem from the adaptive prover. The adaptive prover was begun in StrategyChainBound (only the chain's
   birthday term).
   The adaptive prover was begun in StrategyChainBound: even for a strategy (a function choosing the next frame from the digests seen so far and their challenge answers,
   with causality built into the type), the chain's clash probability is n(n+1)/2/|Block| (3828/|Block| over 87 stages, the same constant as the fixed prover),
   the challenge answers conditioned on the chain's own no-clash event are uniform (single, finite-set version), and a strategic outer prover's chain agrees with concreteFinal on the
   realized messages for each table. Because the strategy has no oracle queries of its own (transcript-restricted adaptivity), a grinding prover that hammers the hash itself looking for collisions is
   out of scope, and its collision mass is proportional to the number of queries q (q·n/|Block|). **Not attained**: an upper bound on the adaptive prover's jointBadEvent (the combinedBound side).
   The stage that transports the sequential-conditioning counting given by OuterSequentialConditioning in the ideal model to the oracle table under the nested
   no-clash events over the 13 round digests remains.
   The grinding prover was handled in GrindingQueryBound: even for a prover with q of its own probe queries at each stage (in frame form, sequentially adaptive),
   the chain's collision mass is N(N+1)/2/|Block| (N=(q+1)n), and q=0 returns to the adopted 3828/|Block|. Because the adopted Causal does not
   survive re-queries, it was replaced by FreshCausal, which conditions on a freshness event (the adopted results are not weakened). A probe on a challenge input
   does not become a position in the sequence, but reading a challenge input itself is free at any digest. The bound is quadratic in q and its leading term is ≈(q+1) times looser.
   A union bound for the adaptive/grinding prover is still not attained.
   The two-stage conditional counting for a fixed prover completed its outer stage in TwoStageConditionalCount: the explicit engine's outer bad event depends on the hash only via the gate alpha coordinate,
   the mass of the diagonal event is the adopted combinedBound by single-coordinate conditional counting, and it is transported to the oracle table by RLUB's fibre Fubini. The index stage was proved as far as the
   dependency fact (the row point is a function of the outer draw; the first draft's obstruction claim was refuted and withdrawn), and the conditional counting itself was given as `assembly_failure_mass_le` with `RowPointFixed` (satisfied non-degenerately by a constant committed column)
   as an explicit assumption (constant committed columns only). The remaining finer split (a fibre fixing the frame half plus the outer challenge
   cells and leaving the index cells free) is specified by the abstract counting `product_diagonal_card_le` and a three-stage contract.
   The finer split of the index stage was completed in IndexStageFinerSplit: from the clash-free injectivity of the joint schedule the outer cells and the index cells are disjoint, by restrict_ratio
   (outer draw, index draw) are simultaneously uniform, two-group conditional counting evaluates at each point, at ≤2·tauTerm, the diagonal event in which the index half depends on the run's own outer draw, and
   the frame-fibre Fubini carries this to the oracle table with a single additive term. With this, the mass bound for the failure set of the explicit engine's assembly conclusion,
   `assembly_failure_mass_le_unconditional ≤ combinedBound + 2·tauTerm + P[extended clash]` (4560/|Block| at d=13), holds under ROM for a fixed prover
   with no condition on the committed columns, and RHS <1 in the closed instance. What remains is guard liveness for non-constant columns (slack only), the adaptive prover
   (begun in AdaptiveUnionTransport), R1b, circuit truth, and exhibiting acceptance.
   The union bound for the adaptive prover was advanced in OuterLaneTransport: via a diagonal fresh step (splitting on the value of the target) and nested no-clash events,
   it transports OSC's per-round conditioning to the oracle table, giving ≤ outerTerm + the chain collision term for an arbitrary strategy-driven chain. However, the general form quantifies the lane and the strategy
   independently (prefix-dependent lane transport; for a general Strategy that reads raw blocks, laneOfStrategy is not constructible), so closing SCB (iii) is limited to
   the reduced-history subclass (ReducedStrategy, for which agreement of the lane messages with the realized messages is proved). What remains is strategies that read raw blocks,
   the transport of tauTerm/alphaTerm, and the union bound for the grinding prover.
   Liveness of the index guard was characterized in IndexGuardLiveness: at a common width, dead ↔ claimed cell = committed cell (the honest case), and the index event is ∅;
   for a non-constant column (spikeColumn), dead ↔ the single field equation eqAtZero(row) = (x−v)/(w−v). An upper bound on the mass of dead outer draws
   (Schwartz–Zippel type) and realization of an exhibited row point by an outer draw are not started.
   The q-linearization of the grinding bound was obtained in GrindingLinearBound: for a state-framed prover whose probes frame at an already-formed stage digest, (q+1)n(n+1)/2/|Block|
   (agreeing with the adopted constant at q=0). An attacker who simulates candidate chains within the probe budget is excluded (counting over the query graph is not started. GQB's quadratic bound
   covers him too).
   The adaptive bound for the reduced-history subclass reached the full combinedBound + chain collision term in ReducedFullTransport by adding the block-0 gate tau/gate alpha events (fixed targets at the derive digest)
   (RHS <1 in the closed instance). The index lane is not included for the adaptive prover, because the used claims become a function of the table
   (a diagonal form is needed). The joining of g/coeffsOf to the deployment table is incomplete.
   The index lane for the reduced-history adaptive prover was incorporated in ReducedIndexLanes: absorbing the history-dependent used-claims choice as 8 claim frames, a diagonal fresh step at the index digest
   (separation is by the digest under no-clash) and a density lemma give ≤ combinedBound + 2·tauTerm + the chain collision term (RHS <1 in the closed instance). The committed cell is
   a parameter of a function of the history (transport to a realized proof is not carried out), and the index term is for 1 bound cell.
   The chain-simulating grinding prover was handled in GrindingGraphBound, with a negative conclusion stated as a theorem: the unified charging theorem has 3 instances (GQB/GLB/graph-framed),
   but for chainSimulator the eligible set coincides with all pairs, so this approach does not improve beyond the all-pairs constant (no lower bound on the collision mass is claimed).
   A linear bound for a general grinding prover lies outside this approach.
   The assembly-failure bound for the adaptive series was given in AdaptiveAssemblyFailure by closing the identification of the lane sequences and showing that all of EOD's owned events coincide, as Finsets, with `SoundnessAssembly.outerBadEvent` on the realized run,
   giving assembly failure set ⊆ that event ∪ the index event, with mass ≤ combinedBound + the chain collision term + P[index event].
   The mass of the index half was transported in IndexHalfTransport, and by a comparison of chains (the no-clash event of the extended shape ⊆ that at stage 22+5d of the strategic shape) it
   closed to the single constant combinedBound + 2·tauTerm + the index stage's birthday term. A review of the same module discovered a vacuity reaching back into the adopted tree:
   the assembly failure event has acceptance as a conjunct, acceptance implies the shape, and the shape, through the fixture's `used` (lengths 1,1,0), forces
   `numRouted = 0 ∧ numConstants = 1 ∧ numWires = 1`, so for any other configuration the event is empty and the bound was vacuously true.
   This was recorded as a theorem, and the obstruction was removed by parameterizing `used` (for matching claims the shape's 5 conjuncts hold by the construction itself).
   Exhibiting acceptance itself is still incomplete.
   The ROM masses of the two localized collisions were computed in LocalizedCollisionMasses: a fixed pair is exactly `1/|Block|`, and the surrogate for the union is not a family of configurations but a
   query set, with the mass of "some configuration collides with the deployed configuration" at most `(Q.card + 1)/|Block|` (without naming the family), connected to the adopted model by `Q := boundedQueries L`. However, since `joinFailureEvent`
   has `DeployedFacts` as a conjunct, that alone makes its mass at most `1/|Block|`, so the headline number is not what the collision analysis earned; it comes essentially from the containment side (stated as a negative fact in theorem form).
   Exhibiting acceptance was carried out in NonDegenerateAcceptance. The causes of degeneracy turned out to be **four** (the fixture's used, index sampling in the trivial engine,
   the fixture's one-element logTau, and the empty list of logChallenges on the integrated path — the last being the fact, stronger than any previously known, that the adopted test engine unconditionally returns
   `.error .configuration`), all of which were stated as theorems for an arbitrary engine. On that basis, with only 2 engine fields exercised,
   it was shown by `rfl` that `Verifier.verify` accepts at the envelope's maximal configuration (degreeBits 13, numRouted 80, numWires 160, gateRows 255, quotientDegree 8, indexBits 8, with
   degreeBits + indexBits = 21 exactly the profile's upper limit), and a parametric version was also given for all WHIR byte sequences within the bounds. However, these are model engines, in which only 3 of the 9 gates are really computed and the derived transcript is always empty.
   Therefore it does not make the adopted adaptive events non-empty, and it does not claim localization to the explicit engine (whose `deploymentValid`
   includes the numeric constraint `1 ≤ numVariables ≤ 21`). The claim is limited to the fact that the shape and the envelope no longer prevent acceptance.
   The lane pairing for the grinding prover was carried out in GrindLanePairing: at q=0 the adopted raw bound is derived from GUB's headline (non-circularity was confirmed by a
   transitive constant-dependency scan), and it was shown without any conditioning event that the lane's messages are the grinder's absorbed payload itself.
   The scope of application is grinders whose joint-stage payload is at most 5 elements, and the restriction that the log lane and the gate lane carry the same message remains.
   Exclusion of searching provers is carried by `ChallengeRestricted`, and GUB's pre-read hole is as it was.
   Acceptance was pushed up to the explicit engine in DerivedAcceptance: the accepting engine is `ExplicitEngine.explicitEngine` with only the 2 fields `parseWhir` and
   `whirTail` reverted to the fixture (`rfl`), with 10 of the 12 fields being adopted real components and `thash` and `khash` universally quantified.
   The remaining obstacle is only the WHIR parse/tail; the adopted tree does contain a concrete success example of `WhirConfigured.run`, but the mask and the number of claims do not match so it
   cannot be reused. The missing lemma was named. However, the honest gate count is 4 out of 9, (2) and (4) close by `rfl`, and (7) cannot distinguish
   any two proofs because `numRouted = 0`. The configuration is maximal up to `quotientDegree` but has `numRouted = 0`, which is a return to the original degeneracy pin.
   It is incomparable with the adopted `maximalConfig`; neither dominates the other. It was stated as a theorem that acceptance at `numRouted = 1` is
   equivalent to an accidental agreement between derived challenges, and it was shown that gate 8 also closes that loophole. The tension that a WHIR-complete instance cannot preserve the universal quantification over `thash` was also recorded.
   TwoLaneMessages removed GLP's honesty item (v), but more important is a finding about the adopted grinding model:
   the protocol has two joint cells one stage apart, yet `GrindCausal` does not let it reach either of them, so the grinding line is strictly at a coarse granularity, and
   splitting a single payload does not fix it. The split itself raises the budget from 5 elements to 15, but the 2 lanes separate only when there are more than 120 bytes, and
   below that the gate side becomes empty (an empty gate cell is not a legal round message). This length invalidity is inherited from GLP.
   WhirTailWitness exhibited, for the first time concretely, a WHIR success at the installed level. The headlines are
   `configured_six_claim_execution_example` (6 claims, the deployment mask, 408/72 bytes, both EOFs) and
   `installed_whir_pair_accepts_a_full_verification` (`Verifier.verify` with both `parseWhir`/`whirTail` installed).
   The 6-claim context is exactly the form the outer derives, by `six_context_is_the_derived_context_of_the_installed_engine`.
   However, it uses a constant toy hash (`the_witness_hash_ignores_every_input`), a toy no-round profile, and
   `Verifier.testConfig` (1 variable), and the engine is the complement of `DerivedAcceptance` (4 fields remaining abstract observations,
   `accepting_engine_field_ledger`), not `ExplicitEngine.explicitEngine`.
   A 21-variable witness is not constructed. The mask `[⟨31⟩]` vs `[⟨7⟩]` was not the blocker; the number of claims was the actual obstacle
   (`configured_run_mask_congruent`). RoutedAcceptance accepts with `numRouted = 80` on the same derived engine
   (`routed_acceptance`), but `routedHash` ignores the digest (`routed_hash_is_a_transcript_collision`).
   The derived challenges are independent of the statement (`rho_ignores_the_statement`), and two proofs differing only in their roots are both accepted
   (`alt_proof_is_also_accepted`). This is not the removal of the last degeneracy pin, but an exchange for proof-dependent challenges.
   The three instances derived / routed / maximal are all mutually incomparable. Gate 7 executes an 80-iteration wire loop but does not distinguish the two proofs.
   That digest-ignoring was repaired in DigestRoutedAcceptance: `fixedHash` domain-separates frames/challenges at byte 15, and
   fixes only counters 3/4/5, which the vanishing argument for acceptance requires, while the rest actually read the digest. Without changing the adopted routedConfig/routedProof/
   routedPin/matchingClaims at all, replacing only the hash makes acceptance at `numRouted = 80` hold (`fixed_acceptance`), and
   it was shown by a pair of contrasting theorems that the derived transcripts of two proofs differing in a root agree under the old hash and separate under the new one.
   The residue is disclosed: of 228 squeezes, 180 read the chain and 48 remain sign-fixed, and the chain state is 1 byte wide
   (the trailing 31 bytes are zero in every derivation, and the chain has at most 256 digests). The recovery is a Fiat–Shamir-dependent structure, not quantitative collision resistance.
   The separation is fold-specific (for a pair of roots with equal folds, the entire transcript agrees), and altProof is still accepted — separating the two proofs
   requires a nonzero norm-inverse column or an installed WHIR parse. `thash` is an instantiation, not universally quantified.
   That separation was achieved in RejectionWitness — the first rejection theorem in this tree: with an engine having the installed WHIR pair, a forged proof with one root changed
   becomes `.error .invalidProof` (the locator identifies that all other gates pass; the failure is the root check inside parse), while the fixture pair accepts the same forged proof.
   Each half of the WHIR pair rejects on its own too, and acceptance of the forgery requires both halves to be fixtures. However, this is about testConfig (1 variable), a toy hash, and
   a model, and the r-family form is incomplete (the byte equality of receiveOne is not exported).
   R1b was closed as a bridge in R1bBridge: from no collision on the execution inputs of the two runs being compared (per-pair — it is preserved as a theorem that the ∀ form is refuted by this tree's depth-1 fixture)
   plus decoding uniqueness (an assumption with a literature citation), the complete rootDetermined clause for the opening-free tablesOf follows, up to a local collision on the two opened
   rows, and is plugged argument-by-argument into the hr1b slot of the adopted committed_tables_join.
   The WHIR execution witness reached the full 21 variables in DeployedWhirWitness: 4 real folding rounds on the schedule of the really transcribed canonicalRow21,
   a real PoW threshold (stated as a theorem that with a constant hash the comparison is vacuous), and a strict 1904/1976-byte EOF. There are only 2 families of substitutions (the RS domain and the query count 84→5;
   all Merkle authentication paths are empty — disclosed with headline weight). That there is no equality in the intermediate sumcheck was stated as a theorem to be a faithful transcription of the deployed wire format,
   by a three-layer cross-check of Lean/Solidity/Rust. Identification with the derived context covers 5 of 7 fields, with the 2 packed-points fields remaining.
   Circuit truth was bundled into a conditional statement in CircuitTruth: under acceptance + AssemblyResidue + a good draw + decoding uniqueness + gates.Nodup,
   the extracted tables are pairwise run-independent (equal to the extracted tables of any second run under the binding event, up to local collisions) and, for every row × every selected gate,
   every constraint term of evaluateGateFull is zero. Unique selection is proved from the tree's selector semantics, and only the contents of the constants column
   were isolated as SelectorRowIsPlonky2 (checked against u32::MAX). The old headline's CommittedTables existence statement turned out to be a tautology and was demoted to a recording theorem, and
   the uniform tablesOf proposal was refuted by the depth-1 fixture (a re-entry into the ∀-over-all-executions trap). No instance of AssemblyResidue is exhibited, and this is the statement's deepest
   conditional layer. The remaining missing statements are "the committed tables are constant on each permutation orbit of the circuit's routing" (copy constraints), public input binding, and
   the constraining of unselected rows.
   The `CommittedTables` join was adjudicated clause by clause in CommittedTablesClauses: preprocessedPinned is derived from acceptance for an arbitrary engine; configDeployed is derived on the
   Solidity path up to one local configuration-encoding collision; rootDetermined is R1b itself; and since for an extractor that reads the openings there exists no map satisfying the clause,
   COS's degenerate witness was forced. The adopted binding lemmas reach only the opened cells (up to local leaf/path collisions), and root-determinacy of unopened cells and of whole columns
   remains in R1b. Therefore "the tables are fixed data" is reduced to R1b + 2 local collisions, and `g` is still not fixed data.
   RIL's transport was carried out in ReducedEngineIndex: by a congruence lemma for two strategies with the same table, the draw identification on OLT §6's realized proof, and TSCC's row-point theorem, it showed that the
   committed cell is a function of the reduced history, and via a Finset identity with the engine's own index bad event obtained the reduced adaptive bound
   ≤ combinedBound + 2·tauTerm + the chain collision term (the multi-cell version is 5·2·tauTerm) (RHS <1 in the closed instance). What remains is the joining of the columns and g/coeffsOf to the deployment
   (CommitmentOrder), raw-block-reading strategies, grinding, R1b, and exhibiting acceptance.
   The reduced-history restriction was lifted in RawBlockLanes: not going through OSC's Lane, but with a raw lane having raw messages and evaluation at the reduced challenges,
   for an arbitrary RoundCausal transcript-restricted strategy one gets ≤ combinedBound + the chain collision term over outer + block-0 (the closed instance is the
   challengeTruncatedMessage that OLT could not pair up). What remains is the raw version of the index half (a mechanical re-derivation of RIL), grinding, and the joining of the columns/tables to the deployment.
   The index half for raw strategies and the engine transport were completed in RawIndexLanes: for an arbitrary causal transcript-restricted strategy (RoundCausal S, ClaimsCausal U),
   ≤ combinedBound + 2·tauTerm + the chain collision term (5·2·tauTerm for the 5-cell version) holds on the explicit engine's own events, with RHS <1 in the closed instance.
   With this, the ROM adaptive bound has reached every lane within the transcript-restricted scope. What remains is the union bound for grinding (own queries), the joining of the columns and tables to the
   deployment, R1b, circuit truth, and exhibiting acceptance.
   The run-level transport at the end of SCB HONESTY (iii) was settled in RunLevelTransportAudit: all of RBL's raw events are equal, as Finsets, to the run-level event that the `actualDigestDraw` on the realized proof
   falls into `jointBadEvent` (the realized lane), and the adaptive run-level bound holds in the same statement form as the fixed-prover theorem,
   with whole-schedule uniformity unnecessary (a sum of single-stage events). The product law itself is not claimed (closure is not known and its validity is undecided).
   The identity of the "fixed data" residue was classified in CommitmentOrderSurvey: gate alpha is a squeeze at the derive digest = a challenge coordinate, and since the tau table g
   reads it, the tau event for a fixed g is an alpha-fixed slice of the engine's own tau event (the diagonal is evaluated in EngineTauDiagonal); coeffsOf is a function of the tables only;
   the committed columns depend on the round-one opening (absorbed after the index squeeze) and are not prefix data; and "fixed" is an R1b-type rootDetermined assumption.
   12 overclaiming passages in 6 adopted files were corrected. What remains is CommittedTablesJoin itself (rootDetermined, preprocessedPinned,
   configDeployed), that is, the joining to the deployment including the CommonCircuitData mirror image and the VK/Rust boundary.
   The union bound for the grinding prover was obtained in GrindingUnionBound, under ChallengeRestricted (challenges are read only at their own stage digest), as
   ≤ combinedBound + N(N+1)/2/|Block| (N=(22+5d)(q+1)). The lane can also read the probe-answer history (GrindLane). What is excluded is the pre-read prover
   (reading challenges ahead at a probe-answer digest = FS challenge grinding. Since it is a repetition of the same string it cannot be evaluated by distinct-string collisions, and the event has mass 1), and
   a different argument of query-counting type is needed. The joining in which the bad set carries the grinder's own absorbed payload is incomplete.
   The diagonal of the engine's own tau event was evaluated in EngineTauDiagonal: splitting on the alpha triple and applying RFT's simultaneous peeling to each block gives ≤ tauTerm d
   (for an arbitrary strategy and arbitrary G), and rebuilding the RXL path gives ≤ combinedBound + 2·tauTerm + the chain collision term on the engine's own tau + index events.
   What remains in ∀-lane form in the final theorem is the outer part (the alpha-dependent diagonal of `SoundnessAssembly.outerBadEvent` is unresolved for the adaptive series. TSCC is for the fixed prover only)
   and alpha (no diagonal needed).
   The outer alpha diagonal for the adaptive series was completed in EngineOuterDiagonal, and the ROM adaptive bound for a transcript-restricted causal prover became ≤ combinedBound + 2·tauTerm + the chain collision term
   with **all 4 events — outer, tau, alpha, index — being the engine's own** (RHS <1 in the closed instance). The evaluated event agrees with the outerEvent event of `actualDigestDraw`
   on the realized proof (proved). The corollary for the failure set of `explicit_good_draw_assembly` is not reached, because one item remains: the identification of the lane sequences (the realized lane sequence = gateLaneOf at the realized run).
   The pre-read (FS challenge grinding) prover was handled in PreReadCharge, obtaining ≤ (q+1)·outerTerm by a two-stage fresh peel that charges the probes (for a general grinding
   prover, with no need for ChallengeRestricted). On the favorable branch the round's challenge digest is the probe's digest itself, so charging the probe charges the attack.
   What remains is the joining (the grinder's own messages), the tau/alpha/index lanes, and the unification of the constants.
   These results were assembled into a single theorem in SoundnessAssembly. From acceptance of the explicit engine, the named structures of residual assumptions
   (the table's semantics and the transcribed rows, the deployment digests and boundedness, fold-level openings, the height of the extracted columns and the committed width,
   GateDerivedRejection's 9 fields, the slot coefficients), the real digest draw being outside the 4 families of bad events, and the real index draw being outside
   the guarded index bad event, it derives the vanishing of the selected gates' constraints on every row, per-column identification, the pinned profile row, and
   core agreement (up to collisions). The mass is ≤ combinedBound + tauTerm d (≤2^-171) in the joint space, and ≤ 2·tauTerm bits (≤2^-187) in the index space, and
   since these are different spaces they are not added. (IndexLanesOracle gave ≤ combinedBound + 2·tauTerm for both as a union over the same table, under the ROM law with a fixed digest.) The first draft was discarded because the index bad event was unguarded and the conclusion contradicted the assumptions
   (the review derived False) and a forgery hypothesis had slipped into the residue; a re-review after the fix confirmed that
   the refutation does not typecheck and that on an honest extraction the bad events are empty. **Remaining limitations**: the simultaneous satisfiability of acceptance and
   the residual assumptions cannot be exhibited unless a proof accepted by the explicit engine is constructed; the conclusion is
   constraint vanishing and identification conditioned on a good draw, not circuit truth, WHIR proximity, or hash security; and R1b, R2,
   half (B), circuitDigest/circuitConfigDigest, and the Solidity-only deployment semantics remain.
   The extraction seam was constructively discharged in ExtractorConstruction. The extraction state is defined from the used claims of an accepting proof and the output of the R1b extractor
   (the eq column is the eq table of the derived tau; rounds/point are empty), and because TruthChain is a definitional predicate that does not mention messages,
   it is constructed for an arbitrary consistent state (message≠truth is absorbed by roundBadSet's off-diagonal of the operational claims).
   Of SoundnessAssembly's 19 residual items, 10 (Consistent, TruthChain, cellsMatchClaims, eqProvenance, slotCoefficients, and
   the structure of eqCellBinding are constructed; foldLevelOpening, column height, committed width, and lastCells come from R1b's HonestOpenings) become
   theorems, and the remaining assumptions are only acceptance, R1b, TableIsCanonical and the rows, the deployment digests and boundedness, gate decoding, positivity of the constraint count, and
   the active filter. The committed width can be derived from HonestOpenings.opened being a map, and is irreducible only
   under the fold-level predicate (consistent with the description in IndexPointZeroCheck. SoundnessAssembly's committedWidth note needs updating).
   **Remaining limitations**: R1b is an unformalized probabilistic claim positing WHIR proximity and sumcheck soundness, and its simultaneous satisfiability
   with acceptance cannot be exhibited unless a proof accepted by the explicit engine is constructed; the conclusion is constraint vanishing on the extracted tables conditioned on a good draw,
   not circuit truth; and the hash is unmodeled.

The current target-105 value of about 101.5 bits is the repository's generic-work estimate, not
128-bit/end-to-end security proved by Lean. Implementation changes and deployment approval are also not included in this update.

GoldilocksCertificate alone is a numerical certificate, and the grounds for primality are limited to its combination with
GoldilocksFoundation's application of Lucas, the enumeration of all prime divisors, and the proof of primality of the small factors.
The commit of Mathlib v4.10.0 and the 6 dependencies of the official lock are pinned for audit use only, and direct imports are permitted only for specific
modules/names (Foundation's 3 imports, Norm's Ring, WhirPolynomial's Roots,
WhirChallenge's Fintype.Card, WhirQuicksort's List.Perm, Correctness's List.Sort,
GatePolynomial's List.Count).
The standard 3-axiom allowlist and the check of all named theorems are maintained.
The dependency guard checks the real Git blobs of all tracked sources, HEAD, origin, the pinned release tags, and the additional sources.
This check does not authenticate the provenance of the generated .olean files or of the ProofWidgets release archive.
An ordinary Lake build has a trust boundary consisting of those artifacts and the Lean toolchain, and is not called a fully source-only reproduction.
Separately, at a checkpoint of 40 models / 1019 theorems, all 1370 non-toolchain Lean source modules of the 7 pinned dependencies were regenerated
into an empty fresh output directory, and all theorems were checked using only that output. The source/hashes/dependencies/JS before and after the run were
compared, and no existing dependency .olean files are used. However, 11 ProofWidgets JS files are pinned pre-existing data, and
regeneration of the JS sources, reproduction of the Lean toolchain/core artifacts, and all implementation/PCS proofs are not claimed.
That record also does not mean that subsequently added models have been freshly checked. See the REPORT for details.

The 10 PoC tests added in the 2026-09-18 re-audit of the deployed code (`mle/tasks/reaudit_wire3_soundness_2026-09-18.md`)
(`mle/tests/poc_*.rs`, `mle/contracts/test/Poc*.t.sol`) are executed tests registered in the implementation inventory as `implementation`,
and are neither Lean theorems nor formal refinement. The plonky2 `evaluate_gate_constraints` used there
is an external implementation trusted as ground truth and is not modeled in Lean.
