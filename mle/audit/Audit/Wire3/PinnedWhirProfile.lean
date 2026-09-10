import Audit.Wire3.InstalledWhirTail

/-!
# Pinning the WHIR parameter record to the deployed canonical profile

## The gap this module closes (InstalledWhirTail finding F3)

`InstalledWhirTail.installedEngine e decode hash wp` takes the WHIR parameter
record `wp : WhirParameters.Params` as a FREE argument.  Its own header says so:
"nothing in this module connects it to `c.whirEncoding`, to
`e.configurationHash` or to `e.deploymentValid`".  The only part of `wp` derived
from acceptance is that `WhirParameters.checkBound` succeeded, and `checkBound`
does not force `0 < wp.inDomainSamples`; an adversarial record with
`inDomainSamples = 0` samples no query index and makes every
`Merkle.verify hash root depth [] [] = some _` vacuously true.  Every Merkle
result there therefore carries an EXPLICIT hypothesis
`hsamples : 0 < wp.inDomainSamples`.

The source does not leave the record free.  `MleVerifierV2`'s constructor
computes `keccak256(abi.encode(config_.whir))` (MleVerifierV2.sol 150) and calls
`CanonicalWhirProfileV2.validateCanonical(config_.whir.numVariables,
computedWhirParametersDigest, whirProtocolId_, whirSessionId_)`
(MleVerifierV2.sol 151-153) against a 21-row generated allowlist.  This module
models that check, installs it, and discharges `hsamples` and `hrounds` from
outer acceptance on the two transcribed dimensions (n = 10 and n = 21).

## Exactly what the source enforces (every constraint cited)

`CanonicalWhirProfileV2.validateCanonical` (contracts/src/CanonicalWhirProfileV2.sol
20-46) enforces, and enforces only:

* `numVariables >= MIN_WHIR_PROFILE_VARIABLES_V2` and
  `numVariables <= MAX_WHIR_PROFILE_VARIABLES_V2` (CanonicalWhirProfileV2.sol 27);
  the two constants are `1` and `21`
  (contracts/src/generated/WhirProfilesV2.sol 7-8).
* `sessionId == CANONICAL_WHIR_SESSION_ID_V2` (CanonicalWhirProfileV2.sol 28,
  constant at WhirProfilesV2.sol 10).
* `parametersDigest == expectedDigest`, the first 32 bytes of the table row at
  offset `(numVariables - MIN) * 96` (CanonicalWhirProfileV2.sol 31-43).
* `protocolId[0] == expectedProtocolIdFirst` and
  `protocolId[1] == expectedProtocolIdSecond`, the next 64 bytes of that row
  (CanonicalWhirProfileV2.sol 43-44).

`parametersDigest` is `keccak256(abi.encode(config_.whir))`
(MleVerifierV2.sol 150); `protocolId` / `sessionId` are the constructor
immutables `whirProtocolId_` / `whirSessionId_` (MleVerifierV2.sol 131-132,
stored at 183-185).  There is NO folding-factor, round-count or sample-count
literal in `validateCanonical`: those values are pinned only through the digest.
It is a deliberate finding of this module that
`SpongefishWhirVerify._validateParameters`
(contracts/src/spongefish/SpongefishWhirVerify.sol 161-191) -- the routine
`WhirParameters.checkCore` models -- never mentions `inDomainSamples` either.
So the SOURCE ENFORCES NO SYNTACTIC POSITIVITY of the sample count anywhere;
positivity holds only because the canonical table rows for the two transcribed
dimensions (n = 10 and n = 21) carry a positive value.  Which dimension is
actually deployed is NOT established anywhere in this module.  That is modelled
honestly below.

## The two layers

`canonicalProfileCheck` is layer one: the four constraints above, with the
digest a function OBSERVATION `Profile.digest` (keccak is not modelled).  It
adds nothing the source lacks and drops nothing the source has.

`canonicalParams` is layer two: the SEMANTIC content of the generated table for
the two packed dimensions whose exact canonical record ships in the repository,
transcribed field by field from
`contracts/test/fixtures/v2_cross_language.json` (`/cases/0/whirParams`,
`numVariables = 10`) and `contracts/test/fixtures/v2_max_resource.json`
(`/verificationConfig/whir`, `numVariables = 21`).  Both are outputs of the one
production constructor `derive_whir_deployment_profile_for_packed_num_vars_v2`
(src/fixture_v2.rs 1734-1868), which is also what generates the on-chain table
(tests/whir_profile_v2_codegen.rs 34-40).  The evaluation points are EMPTY in
these records because the digest is taken over the empty-point encoding
(`params.require_empty_points()`, src/fixture_v2.rs 1875); the outer verifier's
own packed points are substituted afterwards by
`InstalledWhirTail.contextParams`.  The other nineteen rows exist in the
repository only as keccak digests, so they are not transcribed and the
positivity conclusion is not claimed for them.  Covering a further dimension is
purely mechanical: dump
`derive_whir_deployment_profile_for_packed_num_vars_v2(n).params`
(src/fixture_v2.rs 1734-1868) and transcribe its fields, together with its
digest, into `canonicalParams`; no proof in this module would change.

`TableIsCanonical` is the NAMED bridge between the layers: the deployed row is
the digest of the canonical record, and the digest separates records.  The
second component is the keccak collision-resistance idealisation.  It is an
assumption, stated as a structure, never proved.

## Which engine field becomes concrete

CONCRETE, new here: `deploymentValid`, replaced by `pinnedDeployment`, which is
the ADOPTED `e.deploymentValid` conjoined with (i) `c.whirEncoding =
c0.whirEncoding` and (ii) `profileOk`, the decode-then-canonical-check.

Fixing the record at engine-construction time is a DESIGN CHOICE, not something
the adopted `Verifier.Engine` record forces.  `Verifier.WhirContext` carries a
`parameters : Bytes` field (Verifier.lean 233) and `Verifier.whirContext` fills
it with `c.whirEncoding` (Verifier.lean 250), so the tail signature
`whirTail : WhirContext -> Bytes -> Bytes -> ParsedWhir -> Bool`
(Verifier.lean 357) does hand the tail the ACCEPTED configuration's WHIR bytes.
A tail of the shape

    fun ctx t h w =>
      match P.decodeParams ctx.parameters with
      | some wp => InstalledWhirTail.installedTail hash wp ctx t h w
      | none    => false

would therefore make the parameter record a function of the accepted `c` alone,
with no `c0` argument and no conjunct (i) at all.  The `c0` form is preferred
here for a different reason: it keeps the record syntactically fixed, so every
fixed-`wp` theorem of `InstalledWhirTail` -- in particular
`installed_acceptance_opens_authenticated_rows_round_one` -- is reusable
verbatim, at the price of carrying conjunct (i).

Conjunct (i) is an IDEALISED residue, on the same footing as
`TableIsCanonical.rowSeparates`, and it is the only thing this module adds to
the deployment observation beyond the source's own canonical check.  It stands
in for the observation `e.configurationHash c = pin.configDigest`
(Verifier.lean 413), which is the Lean model of `_requirePinnedConfiguration`'s
`keccak256(abi.encode(config)) != verificationConfigDigest`
(MleVerifierV2.sol 478-488), under keccak injectivity restricted to the WHIR
bytes.  Keccak is unmodelled in Lean, so conjunct (i) is ASSUMED, exactly as
`rowSeparates` is; it is not derived from the adopted configuration-hash check.

ALREADY CONCRETE, inherited unchanged from `InstalledWhirTail.installedEngine`:
`whirTail`, `foldClaim`, `normEvaluation`, `eqEvaluation`, `gateEvaluation`.

STILL OBSERVATIONS: `configurationHash`, `initialObservation`, `commitRound`,
`sampleIndices`, `publicInputsHash`, `parseWhir`, and the three `Profile`
components `decodeParams`, `digest`, `tableDigest` / `tableProtocolId` /
`sessionId`.

## Independent recomputation of the two transcribed digests (EVIDENCE, not proof)

Keccak is unmodelled in Lean, so `TableIsCanonical.rowDigest` cannot be proved
here.  It was, however, checked outside Lean by the reviewer, and the check is
recorded so a reader need not take the transcription on trust.  Feeding the
exact `SpongefishWhirVerify.WhirParams` tuple of each fixture record -- with all
three evaluation-point arrays EMPTY, matching `params.require_empty_points()`
(src/fixture_v2.rs 1875) -- through `cast abi-encode` and then `cast keccak`
reproduces the generated table rows byte for byte:

* n = 10, from `v2_cross_language.json` `/cases/0/whirParams` (1312 encoded
  bytes, i.e. 928 + 384 * 1):
  `0x49aa0048728b8e46ac9f1fe2a59a2a2f03f8a88697c915ac2a9b3b25a20bffc2`
  = bytes [0,32) of `CANONICAL_WHIR_PROFILE_TABLE_V2` row 10.  That row's
  protocol ID, bytes [32,96), equals the same fixture's verification-key
  `whirProtocolId`.
* n = 21, from `v2_max_resource.json` `/verificationConfig/whir` (2464 encoded
  bytes, i.e. 928 + 384 * 4):
  `0x966b03c9b06cc88e5aeeb7bbabdddb1d59ce885c06f6fd7b726413a398c30b31`
  = bytes [0,32) of row 21 = that fixture's `pinnedVerifier.whirParametersDigest`.
  That row's protocol ID equals the fixture's `pinnedVerifier.whirProtocolId`.

Both fixtures' `whirSessionId` is `CANONICAL_WHIR_SESSION_ID_V2`
(generated/WhirProfilesV2.sol 10).  This is EVIDENCE that the records
transcribed below are the ones the deployed table commits to; it is not a Lean
proof and does not weaken `TableIsCanonical`, which remains an assumption.

## What is NOT proved

The immutable store holding the digest and the two protocol-ID halves; the
deployment binding of `c` itself (`configurationHash` and the adopted part of
`deploymentValid` remain observations, and configuration-hash equality is not
configuration equality without collision resistance); any Rust or Solidity
refinement of `decodeParams` (no ABI decoder is modelled, and the adopted tree
contains none); keccak, hence the digest table's injectivity, which is an
explicit assumption; the WHIR-bytes pin, conjunct (i) of `pinnedDeployment`,
which is a SECOND explicit keccak-injectivity assumption of exactly the same
kind as `TableIsCanonical.rowSeparates` and is likewise never proved; the
nineteen untranscribed table rows.  No WHIR or PCS
soundness, no proximity or list decoding, no Fiat-Shamir independence, no hash
security -- `hash` is an arbitrary deterministic function and the examples use a
constant toy hash.  Nothing here is the deployed system's soundness error.  The
wire-v3 WHIR profile modelled is the ~100-bit design point.  No "125" claim is
made or implied anywhere.
-/

namespace Audit.Wire3.PinnedWhirProfile
open Spongefish (Hash)

abbrev VkParams := InstalledWhirTail.VkParams

/-! ## Section 1: the canonical-profile check, transcribed -/

/-- WhirProfilesV2.sol 7. -/
def minProfileVariables : Nat := 1

/-- WhirProfilesV2.sol 8. -/
def maxProfileVariables : Nat := 21

/-- The deployment-time profile allowlist as the source presents it: a decoder
    for the VK's WHIR bytes, the `keccak256(abi.encode(WhirParams))`
    observation, and the generated table's three per-row values plus the single
    canonical session identifier.  None of these five is modelled concretely;
    they are the module's observation boundary. -/
structure Profile where
  decodeParams : Verifier.Bytes → Option VkParams
  digest : VkParams → Verifier.Root
  tableDigest : Nat → Verifier.Root
  tableProtocolId : Nat → Verifier.Bytes
  sessionId : Verifier.Bytes

/-- The VK's WHIR parameter record, decoded from the configuration's own WHIR
    encoding.  This is the whole point: the record is a FUNCTION of `c`, not a
    free argument. -/
def paramsOfConfig (P : Profile) (c : Verifier.Config) : Option VkParams :=
  P.decodeParams c.whirEncoding

/-- `CanonicalWhirProfileV2.validateCanonical`, CanonicalWhirProfileV2.sol
    20-46, with the digest argument supplied by MleVerifierV2.sol 150 and the
    protocol/session arguments by MleVerifierV2.sol 152.  Exactly four
    constraints; no sample count, folding factor or round count appears, because
    none appears in the source. -/
def canonicalProfileCheck (P : Profile) (c : Verifier.Config) (wp : VkParams) : Bool := decide (
  minProfileVariables ≤ wp.numVariables ∧ wp.numVariables ≤ maxProfileVariables ∧
  c.whirSessionId = P.sessionId ∧
  P.digest wp = P.tableDigest wp.numVariables ∧
  c.whirProtocolId = P.tableProtocolId wp.numVariables)

/-- Decode the configuration's WHIR bytes, then apply the canonical check. -/
def profileOk (P : Profile) (c : Verifier.Config) : Bool :=
  match paramsOfConfig P c with
  | none => false
  | some wp => canonicalProfileCheck P c wp

theorem canonical_check_exact (P : Profile) (c : Verifier.Config) (wp : VkParams) :
    canonicalProfileCheck P c wp = true ↔
      minProfileVariables ≤ wp.numVariables ∧ wp.numVariables ≤ maxProfileVariables ∧
      c.whirSessionId = P.sessionId ∧
      P.digest wp = P.tableDigest wp.numVariables ∧
      c.whirProtocolId = P.tableProtocolId wp.numVariables := by
  simp [canonicalProfileCheck]

theorem profile_ok_exact (P : Profile) (c : Verifier.Config) :
    profileOk P c = true ↔
      ∃ wp, paramsOfConfig P c = some wp ∧ canonicalProfileCheck P c wp = true := by
  cases h : paramsOfConfig P c with
  | none => simp [profileOk, h]
  | some wp => simp [profileOk, h]

/-- The decoded record depends on the configuration only through its WHIR
    encoding, which is what makes the deployment pin below effective. -/
theorem params_depend_only_on_the_whir_encoding (P : Profile) (c d : Verifier.Config)
    (h : c.whirEncoding = d.whirEncoding) : paramsOfConfig P c = paramsOfConfig P d := by
  simp [paramsOfConfig, h]

/-! ## Section 2: the pinned engine -/

/-- The all-zero record, used only as the `Option.getD` fallback.  It never
    satisfies `canonicalProfileCheck` under a canonical table, since
    `canonicalParams 0 = none` and `minProfileVariables = 1`. -/
def defaultParams : VkParams :=
  { numVariables := 0, foldingFactor := 0, numVectors := 0, numCommitments := 0,
    outDomainSamples := 0, inDomainSamples := 0, initialSumcheckRounds := 0, numRounds := 0,
    finalSumcheckRounds := 0, finalSize := 0, initialDomain := ⟨0, 0, 0, 0, 0⟩,
    initialInterleavingDepth := 0, initialNumVariables := 0, initialSumcheckPowThreshold := 0,
    finalPowThreshold := 0, finalSumcheckPowThreshold := 0,
    evaluationPoint := [], evaluationPoint2 := [], additionalEvaluationPoints := [],
    rounds := [] }

/-- The record the deployed engine runs its WHIR tail under. -/
def pinnedParams (P : Profile) (c₀ : Verifier.Config) : VkParams :=
  (paramsOfConfig P c₀).getD defaultParams

theorem pinned_params_of_decode (P : Profile) (c₀ : Verifier.Config) (wp : VkParams)
    (h : paramsOfConfig P c₀ = some wp) : pinnedParams P c₀ = wp := by
  simp [pinnedParams, h]

/-- The adopted deployment observation, conjoined with the WHIR-bytes pin and
    the canonical-profile check.  See the header for why the pin is stated on
    `whirEncoding` and what it models. -/
def pinnedDeployment (P : Profile) (e : Verifier.Engine) (c₀ : Verifier.Config) :
    Verifier.Config → Bool :=
  fun c => e.deploymentValid c && decide (c.whirEncoding = c₀.whirEncoding) && profileOk P c

theorem pinned_deployment_exact (P : Profile) (e : Verifier.Engine) (c₀ c : Verifier.Config) :
    pinnedDeployment P e c₀ c = true ↔
      e.deploymentValid c = true ∧ c.whirEncoding = c₀.whirEncoding ∧ profileOk P c = true := by
  simp [pinnedDeployment, and_assoc]

/-- The adopted engine with only its deployment observation strengthened. -/
def pinnedBase (P : Profile) (e : Verifier.Engine) (c₀ : Verifier.Config) : Verifier.Engine :=
  { e with deploymentValid := pinnedDeployment P e c₀ }

/-- `InstalledWhirTail.installedEngine` whose WHIR parameter record is no longer
    free: it is the record decoded from the deployed configuration. -/
def pinnedEngine (P : Profile) (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (hash : Hash) (c₀ : Verifier.Config) : Verifier.Engine :=
  InstalledWhirTail.installedEngine (pinnedBase P e c₀) decode hash (pinnedParams P c₀)

abbrev pinnedContext (P : Profile) (e : Verifier.Engine) (decode : Integrated.DecodeGates)
    (hash : Hash) (c₀ c : Verifier.Config) (p : Verifier.Proof) : Verifier.WhirContext :=
  Verifier.derivedContext (pinnedEngine P e decode hash c₀) c p

theorem pinned_engine_fields (P : Profile) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (c₀ : Verifier.Config) :
    (pinnedEngine P e decode hash c₀).deploymentValid = pinnedDeployment P e c₀ ∧
    (pinnedEngine P e decode hash c₀).whirTail =
      InstalledWhirTail.installedTail hash (pinnedParams P c₀) ∧
    (pinnedEngine P e decode hash c₀).configurationHash = e.configurationHash ∧
    (pinnedEngine P e decode hash c₀).initialObservation = e.initialObservation ∧
    (pinnedEngine P e decode hash c₀).commitRound = e.commitRound ∧
    (pinnedEngine P e decode hash c₀).sampleIndices = e.sampleIndices ∧
    (pinnedEngine P e decode hash c₀).publicInputsHash = e.publicInputsHash ∧
    (pinnedEngine P e decode hash c₀).parseWhir = e.parseWhir ∧
    (pinnedEngine P e decode hash c₀).foldClaim = Connections.packedFold :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The pinned engine keeps every derived transcript object of the engine it was
    built from, so every adopted theorem quantified over an arbitrary engine
    still applies to it. -/
theorem pinned_engine_keeps_transcript (P : Profile) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (c₀ c : Verifier.Config)
    (p : Verifier.Proof) :
    (pinnedEngine P e decode hash c₀).initialTranscript c p = e.initialTranscript c p ∧
    Verifier.derivedRounds (pinnedEngine P e decode hash c₀) c p = Verifier.derivedRounds e c p ∧
    Verifier.derivedIndices (pinnedEngine P e decode hash c₀) c p =
      Verifier.derivedIndices e c p ∧
    pinnedContext P e decode hash c₀ c p =
      Verifier.derivedContext (Integrated.modelEngine e decode) c p :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 3: acceptance pins the profile -/

/-- The deployment facts an accepted call yields, before any table semantics. -/
theorem accepted_deployment_facts (P : Profile) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Integrated.verify (pinnedEngine P e decode hash c₀) decode pin chain c p = .ok ()) :
    e.deploymentValid c = true ∧ c.whirEncoding = c₀.whirEncoding ∧ profileOk P c = true := by
  obtain ⟨_, _, _, _, hv⟩ :=
    Integrated.accepted_preflights_and_original_verifier (pinnedEngine P e decode hash c₀) decode
      pin chain c p h
  have hd := (Verifier.verify_success_checks
    (Integrated.modelEngine (pinnedEngine P e decode hash c₀) decode) pin chain c p hv).2.2.2.1
  have hd : pinnedDeployment P e c₀ c = true := hd
  exact (pinned_deployment_exact P e c₀ c).mp hd

/-- **(a) ACCEPTANCE FORCES A CANONICAL PROFILE.**  An accepted call under the
pinned engine exhibits the parameter record DECODED FROM ITS OWN CONFIGURATION
and proves that record passed the source's canonical-profile check; the record
is also the one the engine's WHIR tail ran under.  This is the statement
`InstalledWhirTail` could not make: there `wp` was a free argument. -/
theorem accepted_profile_is_canonical (P : Profile) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (h : Integrated.verify (pinnedEngine P e decode hash c₀) decode pin chain c p = .ok ()) :
    ∃ wp, paramsOfConfig P c = some wp ∧ canonicalProfileCheck P c wp = true ∧
      paramsOfConfig P c₀ = some wp ∧ pinnedParams P c₀ = wp ∧
      minProfileVariables ≤ wp.numVariables ∧ wp.numVariables ≤ maxProfileVariables ∧
      wp.numVariables = c.degreeBits + c.indexBits := by
  obtain ⟨_, hwe, hok⟩ := accepted_deployment_facts P e decode hash c₀ pin chain c p h
  obtain ⟨wp, hdec, hcan⟩ := (profile_ok_exact P c).mp hok
  have hzero : paramsOfConfig P c₀ = some wp := by
    rw [← params_depend_only_on_the_whir_encoding P c c₀ hwe]; exact hdec
  have hpp : pinnedParams P c₀ = wp := pinned_params_of_decode P c₀ wp hzero
  have h' : Integrated.verify (InstalledWhirTail.installedEngine (pinnedBase P e c₀) decode hash
      (pinnedParams P c₀)) decode pin chain c p = .ok () := h
  obtain ⟨_, _, hvars, _, _, _, _⟩ :=
    InstalledWhirTail.installed_acceptance_runs_the_concrete_tail (pinnedBase P e c₀) decode hash
      (pinnedParams P c₀) pin chain c p h'
  rw [hpp] at hvars
  obtain ⟨hlo, hhi, _, _, _⟩ := (canonical_check_exact P c wp).mp hcan
  exact ⟨wp, hdec, hcan, hzero, hpp, hlo, hhi, hvars⟩

/-! ## Section 4: the semantic content of the generated table -/

/-- The canonical record for packed dimension 10, transcribed field by field
    from `contracts/test/fixtures/v2_cross_language.json` `/cases/0/whirParams`.
    Empty evaluation points, matching the empty-point digest encoding
    (src/fixture_v2.rs 1875) and `InstalledWhirTail.contextParams`, which
    substitutes the outer verifier's own packed points. -/
def canonicalRow10 : VkParams :=
  { numVariables := 10, foldingFactor := 4, numVectors := 1, numCommitments := 3,
    outDomainSamples := 1, inDomainSamples := 29, initialSumcheckRounds := 4, numRounds := 1,
    finalSumcheckRounds := 2, finalSize := 4,
    initialDomain := ⟨4096, 12, 64, 64, 17492915097719143606⟩,
    initialInterleavingDepth := 16, initialNumVariables := 10,
    initialSumcheckPowThreshold := 18446744073709551615,
    finalPowThreshold := 9845507893798,
    finalSumcheckPowThreshold := 18446744073709551615,
    evaluationPoint := [], evaluationPoint2 := [], additionalEvaluationPoints := [],
    rounds :=
      [{ domain := ⟨2048, 11, 4, 512, 455906449640507599⟩, inDomainSamples := 19,
         outDomainSamples := 1, sumcheckRounds := 4, interleavingDepth := 16, numVariables := 6,
         powThreshold := 17095827517592, sumcheckPowThreshold := 18446744073709551615 }] }

/-- The canonical record for packed dimension 21, transcribed field by field
    from `contracts/test/fixtures/v2_max_resource.json`
    `/verificationConfig/whir`.  This is the maximum supported dimension:
    `degreeBits <= 13` and `indexBits <= 8` (Verifier.lean 98-107). -/
def canonicalRow21 : VkParams :=
  { numVariables := 21, foldingFactor := 4, numVectors := 1, numCommitments := 3,
    outDomainSamples := 1, inDomainSamples := 29, initialSumcheckRounds := 4, numRounds := 4,
    finalSumcheckRounds := 1, finalSize := 2,
    initialDomain := ⟨8388608, 23, 131072, 64, 16905767614792059275⟩,
    initialInterleavingDepth := 16, initialNumVariables := 21,
    initialSumcheckPowThreshold := 18446744073709551615,
    finalPowThreshold := 345602437485497,
    finalSumcheckPowThreshold := 18446744073709551615,
    evaluationPoint := [], evaluationPoint2 := [], additionalEvaluationPoints := [],
    rounds :=
      [{ domain := ⟨4194304, 22, 8192, 512, 5416168637041100469⟩, inDomainSamples := 19,
         outDomainSamples := 1, sumcheckRounds := 4, interleavingDepth := 16, numVariables := 17,
         powThreshold := 17095827517592, sumcheckPowThreshold := 18446744073709551615 },
       { domain := ⟨2097152, 21, 512, 4096, 17654865857378133588⟩, inDomainSamples := 14,
         outDomainSamples := 1, sumcheckRounds := 4, interleavingDepth := 16, numVariables := 13,
         powThreshold := 9845507893798, sumcheckPowThreshold := 18446744073709551615 },
       { domain := ⟨1048576, 20, 32, 32768, 3511170319078647661⟩, inDomainSamples := 12,
         outDomainSamples := 1, sumcheckRounds := 4, interleavingDepth := 16, numVariables := 9,
         powThreshold := 4442624697085, sumcheckPowThreshold := 18446744073709551615 },
       { domain := ⟨524288, 19, 2, 262144, 18146160046829613826⟩, inDomainSamples := 10,
         outDomainSamples := 1, sumcheckRounds := 4, interleavingDepth := 16, numVariables := 5,
         powThreshold := 313471598626301, sumcheckPowThreshold := 7737125240129242112 }] }

/-- The transcribed part of the generated table.  Nineteen of the twenty-one
    rows ship only as keccak digests, so they are `none` here; that is a
    deliberate absence, not a claim that those dimensions are rejected. -/
def canonicalParams (n : Nat) : Option VkParams :=
  if n = 10 then some canonicalRow10 else if n = 21 then some canonicalRow21 else none

/-- Both transcribed rows sample a positive number of in-domain queries, run at
    least one intermediate round -- so the DEPLOYED route is round one, not
    `WhirTail`'s finalsplit branch -- and carry the three-commitment,
    one-vector production shape. -/
theorem canonical_rows_are_sampled (n : Nat) (wp : VkParams) (h : canonicalParams n = some wp) :
    0 < wp.inDomainSamples ∧ wp.rounds ≠ [] ∧ 0 < wp.numRounds ∧
      wp.numCommitments = 3 ∧ wp.numVectors = 1 ∧ wp.foldingFactor = 4 ∧
      wp.numVariables = n := by
  unfold canonicalParams at h
  split at h
  · rename_i h10
    subst h10
    obtain rfl := Option.some.inj h
    exact ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl⟩
  · split at h
    · rename_i h21
      subst h21
      obtain rfl := Option.some.inj h
      exact ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl⟩
    · simp at h

/-- The NAMED bridge from the digest table to its semantic content.  The first
    component says the generated row for a transcribed dimension really is the
    digest of the canonical record; the second is the keccak
    collision-resistance idealisation, restricted to canonical targets.  Neither
    is proved anywhere -- keccak is not modelled. -/
structure TableIsCanonical (P : Profile) : Prop where
  rowDigest : ∀ n wp, canonicalParams n = some wp → P.tableDigest n = P.digest wp
  rowSeparates : ∀ n wp wq, canonicalParams n = some wq → P.digest wp = P.digest wq → wp = wq

/-- Under the table assumption, passing the source's canonical check at a
    transcribed dimension identifies the record completely. -/
theorem canonical_profile_is_the_rust_row (P : Profile) (hT : TableIsCanonical P)
    (c : Verifier.Config) (wp wq : VkParams)
    (hrow : canonicalParams wp.numVariables = some wq)
    (h : canonicalProfileCheck P c wp = true) : wp = wq := by
  obtain ⟨_, _, _, hd, _⟩ := (canonical_check_exact P c wp).mp h
  rw [hT.rowDigest _ _ hrow] at hd
  exact hT.rowSeparates wp.numVariables wp wq hrow hd

/-- **(b) THE CANONICAL PROFILE SAMPLES.**  The source enforces no syntactic
positivity -- neither `CanonicalWhirProfileV2.validateCanonical` nor
`SpongefishWhirVerify._validateParameters` mentions `inDomainSamples` -- so
positivity is DERIVED from the one thing the source does enforce, digest
equality against the generated row, plus the named table assumption.  The same
derivation supplies `wp.rounds != []`, which selects the deployed round-one
route rather than `WhirTail`'s finalsplit branch. -/
theorem canonical_profile_has_positive_samples (P : Profile) (hT : TableIsCanonical P)
    (c : Verifier.Config) (wp wq : VkParams)
    (hrow : canonicalParams wp.numVariables = some wq)
    (h : canonicalProfileCheck P c wp = true) :
    wp = wq ∧ 0 < wp.inDomainSamples ∧ wp.rounds ≠ [] ∧ wp.numCommitments = 3 := by
  have heq : wp = wq := canonical_profile_is_the_rust_row P hT c wp wq hrow h
  obtain ⟨hs, hr, _, hc, _, _, _⟩ := canonical_rows_are_sampled wp.numVariables wq hrow
  exact ⟨heq, by rw [heq]; exact hs, by rw [heq]; exact hr, by rw [heq]; exact hc⟩

/-! ## Section 5: the discharged round-one authentication -/

/-- **(c) ROUND-ONE MERKLE AUTHENTICATION WITH NO PARAMETER HYPOTHESES.**
`InstalledWhirTail.installed_acceptance_opens_authenticated_rows_round_one`
restated for the pinned engine, with BOTH of its parameter hypotheses
discharged: `hrounds : wp.rounds != []` and `hsamples : 0 < wp.inDomainSamples`
now follow from acceptance plus the table assumption, because the record is the
one decoded from the accepted configuration and the canonical rows for the two
transcribed dimensions (n = 10 and n = 21) both have `numRounds >= 1` and
`inDomainSamples = 29`.  The only remaining hypothesis about parameters, `hrow`,
says the accepted call's packed dimension is one of those two; the other
nineteen rows are not in the repository in record form. -/
theorem pinned_round_one_authentication (P : Profile) (hT : TableIsCanonical P)
    (e : Verifier.Engine) (decode : Integrated.DecodeGates) (hash : Hash)
    (c₀ : Verifier.Config) (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config)
    (p : Verifier.Proof) (wq : VkParams)
    (hrow : canonicalParams (c.degreeBits + c.indexBits) = some wq)
    (h : Integrated.verify (pinnedEngine P e decode hash c₀) decode pin chain c p = .ok ())
    (position : Nat) (root : Verifier.Root)
    (hpos : [pin.preprocessedRoot, p.witnessRoot, p.normInverseRoot].get? position = some root) :
    paramsOfConfig P c = some wq ∧ pinnedParams P c₀ = wq ∧ 0 < wq.inDomainSamples ∧
    ∃ (r : WhirTail.Result) (opening : WhirIntermediate.Opening) (rows : List WhirRows.RawRow)
      (offset next : Nat),
      InstalledWhirTail.tailRun hash wq (pinnedContext P e decode hash c₀ c p)
        p.whirTranscript p.whirHints = some r ∧
      InstalledWhirTail.RoundOneOpening hash wq (InstalledWhirTail.outerBytes p.whirHints)
        r opening ∧
      opening.indices ≠ [] ∧
      opening.groups.get? position = some rows ∧
      Merkle.verify hash (InstalledWhirTail.rootDigest root)
        (WhirConfigured.initialOpen wq).merkleDepth opening.indices
        (WhirRows.rowHashes hash rows) (InstalledWhirTail.outerBytes p.whirHints) offset
        = some next := by
  obtain ⟨wp, hdec, hcan, _, hpp, _, _, hvars⟩ :=
    accepted_profile_is_canonical P e decode hash c₀ pin chain c p h
  rw [← hvars] at hrow
  obtain ⟨heq, hs, hr, _⟩ :=
    canonical_profile_has_positive_samples P hT c wp wq hrow hcan
  subst heq
  have hE : pinnedEngine P e decode hash c₀ =
      InstalledWhirTail.installedEngine (pinnedBase P e c₀) decode hash wp := by
    unfold pinnedEngine; rw [hpp]
  rw [hE] at h
  have h' : Integrated.verify (InstalledWhirTail.installedEngine (pinnedBase P e c₀) decode hash wp)
      decode pin chain c p = .ok () := h
  obtain ⟨r, opening, rows, offset, next, hrun, hopen, hne, hgroup, hmerkle⟩ :=
    InstalledWhirTail.installed_acceptance_opens_authenticated_rows_round_one (pinnedBase P e c₀)
      decode hash wp pin chain c p hr hs h' position root hpos
  refine ⟨hdec, hpp, hs, r, opening, rows, offset, next, ?_, hopen, hne, hgroup, hmerkle⟩
  have hctx : pinnedContext P e decode hash c₀ c p =
      InstalledWhirTail.installedContext (pinnedBase P e c₀) decode hash wp c p := by
    unfold pinnedContext; rw [hE]
  rw [hctx]; exact hrun

/-! ## Section 6: a proof cannot choose its own WHIR parameters -/

/-- **(d) PROFILE SUBSTITUTION REQUIRES CHANGING THE DEPLOYED CONFIGURATION.**
Two accepted calls under one pinned engine -- ANY two, with different pins,
chains, configurations and proofs -- decode the SAME WHIR parameter record, and
it is the record of the deployed configuration.  The decoder is a function of
the configuration's WHIR bytes and the deployment check pins those bytes, so
nothing a prover supplies can select a different profile.  This is exactly the
freedom `InstalledWhirTail`'s free `wp` argument left open.

The shared-record conclusion comes from conjunct (i) of `pinnedDeployment`
together with decoder determinism (`params_depend_only_on_the_whir_encoding`)
and NOTHING else: no `TableIsCanonical`, no table semantics, no positivity.
Its content is accordingly COHERENCE PLUMBING -- the record the engine's WHIR
tail actually ran under is the same record the accepted configuration's
canonical check validated, for both calls -- rather than a fresh cryptographic
claim.  The strength of the pin is exactly the strength of conjunct (i), which
the header lists as an assumption. -/
theorem profile_forgery_needs_config_change (P : Profile) (e : Verifier.Engine)
    (decode : Integrated.DecodeGates) (hash : Hash) (c₀ : Verifier.Config)
    (pin : Verifier.Pinned) (chain : Nat) (c : Verifier.Config) (p : Verifier.Proof)
    (pin' : Verifier.Pinned) (chain' : Nat) (c' : Verifier.Config) (p' : Verifier.Proof)
    (h : Integrated.verify (pinnedEngine P e decode hash c₀) decode pin chain c p = .ok ())
    (h' : Integrated.verify (pinnedEngine P e decode hash c₀) decode pin' chain' c' p' = .ok ()) :
    ∃ wp, paramsOfConfig P c = some wp ∧ paramsOfConfig P c' = some wp ∧
      paramsOfConfig P c₀ = some wp ∧ pinnedParams P c₀ = wp ∧
      canonicalProfileCheck P c wp = true ∧ canonicalProfileCheck P c' wp = true ∧
      c.whirEncoding = c'.whirEncoding := by
  obtain ⟨wp, hdec, hcan, hzero, hpp, _, _, _⟩ :=
    accepted_profile_is_canonical P e decode hash c₀ pin chain c p h
  obtain ⟨wp', hdec', hcan', hzero', _, _, _, _⟩ :=
    accepted_profile_is_canonical P e decode hash c₀ pin' chain' c' p' h'
  have hsame : wp' = wp := Option.some.inj (hzero'.symm.trans hzero)
  subst hsame
  obtain ⟨_, hwe, _⟩ := accepted_deployment_facts P e decode hash c₀ pin chain c p h
  obtain ⟨_, hwe', _⟩ := accepted_deployment_facts P e decode hash c₀ pin' chain' c' p' h'
  exact ⟨wp', hdec, hdec', hzero, hpp, hcan, hcan', hwe.trans hwe'.symm⟩

/-! ## Section 7: examples -/

set_option maxRecDepth 65536 in
/-- The canonical record for n = 21, the largest dimension in the allowlist,
    really is admissible for the Lean model of
    `SpongefishWhirVerify._validateParameters`, once the outer verifier's two
    terminal points are supplied -- which is what
    `InstalledWhirTail.contextParams` does.  So the results above are not vacuous
    on that transcribed profile. -/
theorem example_canonical_row_twenty_one_is_admissible :
    (WhirParameters.checkCore
      { canonicalRow21 with
        evaluationPoint := List.replicate 21 Arithmetic.zero,
        evaluationPoint2 := List.replicate 21 Arithmetic.zero } 2).isSome = true := by
  rfl

/-- The adopted `InstalledWhirTail.exampleVk` is a TOY: two packed variables and
    zero intermediate rounds, hence the finalsplit route.  No transcribed
    canonical row has either shape, so the example configuration cannot pass the
    canonical-profile check at a transcribed dimension. -/
theorem example_toy_profile_is_not_a_canonical_row :
    InstalledWhirTail.exampleVk.numVariables = 2 ∧
    InstalledWhirTail.exampleVk.numRounds = 0 ∧
    canonicalParams 2 = none ∧
    ∀ n wp, canonicalParams n = some wp → wp.rounds ≠ [] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro n wp h
  exact (canonical_rows_are_sampled n wp h).2.1

/-- **THE ZERO-SAMPLE FORGERY IS REJECTED.**  The adversarial record of finding
F3 -- the deployed canonical row with `inDomainSamples` set to zero, which passes
`WhirParameters.checkBound`, samples no query index and makes the Merkle results
vacuous -- fails `canonicalProfileCheck` under any canonical table, for
EVERY configuration.  The rejection is not a new syntactic guard: it comes from
the digest equality the source already enforces. -/
theorem example_zero_sample_forgery_is_rejected (P : Profile) (hT : TableIsCanonical P)
    (c : Verifier.Config) :
    canonicalProfileCheck P c { canonicalRow21 with inDomainSamples := 0 } = false := by
  cases hb : canonicalProfileCheck P c { canonicalRow21 with inDomainSamples := 0 } with
  | false => rfl
  | true =>
      have hrow : canonicalParams
          ({ canonicalRow21 with inDomainSamples := 0 } : VkParams).numVariables =
          some canonicalRow21 := rfl
      have heq := canonical_profile_is_the_rust_row P hT c _ canonicalRow21 hrow hb
      have : (0 : Nat) = 29 := congrArg WhirParameters.Params.inDomainSamples heq
      exact absurd this (by decide)

/-- The same for the smaller transcribed dimension, and for the record that
    keeps a positive sample count but deletes every intermediate round -- the
    other way to escape the deployed round-one route. -/
theorem example_round_deletion_forgery_is_rejected (P : Profile) (hT : TableIsCanonical P)
    (c : Verifier.Config) :
    canonicalProfileCheck P c { canonicalRow10 with rounds := [], numRounds := 0 } = false := by
  cases hb : canonicalProfileCheck P c { canonicalRow10 with rounds := [], numRounds := 0 } with
  | false => rfl
  | true =>
      have hrow : canonicalParams
          ({ canonicalRow10 with rounds := [], numRounds := 0 } : VkParams).numVariables =
          some canonicalRow10 := rfl
      have heq := canonical_profile_is_the_rust_row P hT c _ canonicalRow10 hrow hb
      have : (0 : Nat) = 1 := congrArg WhirParameters.Params.numRounds heq
      exact absurd this (by decide)

end Audit.Wire3.PinnedWhirProfile
