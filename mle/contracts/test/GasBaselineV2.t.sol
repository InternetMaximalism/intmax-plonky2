// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {MleVerifierV2} from "../src/MleVerifierV2.sol";
import {PinnedMleVerifierV2} from "../src/PinnedMleVerifierV2.sol";

/// @notice Tracked execution-gas baseline for the production V2 entry points.
/// @dev Every number is one `gasleft()` delta around one raw `staticcall` over a pre-encoded
/// calldata buffer, so the caller-side argument copy is excluded. Each entry point is measured
/// in its own test with a fresh deployment (the same deployment as V2ResourceEnvelope.t.sol) so
/// the first access to every linked library is cold, exactly as in a production transaction; the
/// figures are therefore comparable with the README table and with `mle/contracts/gasprof`.
/// Each execution number must stay at or below its `BUDGET_*` constant: the budgets are the
/// measurements at the commit that last touched them, rounded up by 0.5%. A regression fails
/// this test; an improvement is recorded by lowering the budget in the same commit.
/// Calldata is reported as the legacy intrinsic cost (21,000 + 4 per zero byte + 16 per non-zero
/// byte) and as the EIP-7623 floor (21,000 + 10 per token, 4 tokens per non-zero byte), both over
/// the full ABI-encoded calldata of the call.
contract GasBaselineV2Test is Test {
    // ---------------------------------------------------------------- budgets (execution gas)
    // v2_max_resource.json: degree-13 sampled resource maximum (max rows/wires/gate constraints).
    uint256 private constant BUDGET_MAX_VERIFY_COMPACT = 5_856_375;
    uint256 private constant BUDGET_MAX_VERIFY_COMPACT_PUBLIC_INPUTS = 5_857_014;
    uint256 private constant BUDGET_MAX_FRAUD_VERDICT_COMPACT = 5_914_981;
    uint256 private constant BUDGET_MAX_CORE_VERIFY = 5_872_006;
    // v2_cross_language.json cases[0]: the small cross-language parity circuit.
    uint256 private constant BUDGET_SMALL_VERIFY_COMPACT = 3_556_390;
    uint256 private constant BUDGET_SMALL_VERIFY_COMPACT_PUBLIC_INPUTS = 3_557_029;
    uint256 private constant BUDGET_SMALL_FRAUD_VERDICT_COMPACT = 3_575_386;
    uint256 private constant BUDGET_SMALL_CORE_VERIFY = 3_639_630;
    // v2_production_shape.json: the largest admitted parent profile (103 public inputs). The
    // fixture is generated separately: when it is absent the production tests log that and pass.
    // (A budget of 0 would mean "not yet measured": numbers logged, assertion skipped.)
    uint256 private constant BUDGET_PRODUCTION_VERIFY_COMPACT = 7_261_090;
    uint256 private constant BUDGET_PRODUCTION_VERIFY_COMPACT_PUBLIC_INPUTS = 7_290_330;
    uint256 private constant BUDGET_PRODUCTION_FRAUD_VERDICT_COMPACT = 7_342_482;
    uint256 private constant BUDGET_PRODUCTION_CORE_VERIFY = 7_261_206;

    string private constant MAX_FIXTURE = "test/fixtures/v2_max_resource.json";
    string private constant SMALL_FIXTURE = "test/fixtures/v2_cross_language.json";
    string private constant PRODUCTION_FIXTURE = "test/fixtures/v2_production_shape.json";

    uint8 private constant VERDICT_VALID = 1;
    uint8 private constant VERDICT_PI_MISMATCH = 4;

    enum Entry {
        VerifyCompact,
        VerifyCompactPublicInputs,
        FraudVerdictCompact,
        CoreVerify
    }

    struct Fixture {
        MleVerifierV2.MleProof proof;
        MleVerifierV2.VerificationConfig config;
        bytes compact;
        bytes32[2] whirProtocolId;
        bytes32 whirSessionId;
        uint64[4] circuitDigest;
    }

    // ---------------------------------------------------------------- v2_max_resource.json
    function test_gasBaseline_max_verifyCompact() external {
        _run("max", _loadMax(), Entry.VerifyCompact, BUDGET_MAX_VERIFY_COMPACT);
    }

    function test_gasBaseline_max_verifyCompactPublicInputs() external {
        _run("max", _loadMax(), Entry.VerifyCompactPublicInputs, BUDGET_MAX_VERIFY_COMPACT_PUBLIC_INPUTS);
    }

    function test_gasBaseline_max_fraudVerdictCompact() external {
        _run("max", _loadMax(), Entry.FraudVerdictCompact, BUDGET_MAX_FRAUD_VERDICT_COMPACT);
    }

    function test_gasBaseline_max_coreVerify() external {
        _run("max", _loadMax(), Entry.CoreVerify, BUDGET_MAX_CORE_VERIFY);
    }

    // ---------------------------------------------------------------- v2_cross_language.json cases[0]
    function test_gasBaseline_small_verifyCompact() external {
        _run("small", _loadSmall(), Entry.VerifyCompact, BUDGET_SMALL_VERIFY_COMPACT);
    }

    function test_gasBaseline_small_verifyCompactPublicInputs() external {
        _run("small", _loadSmall(), Entry.VerifyCompactPublicInputs, BUDGET_SMALL_VERIFY_COMPACT_PUBLIC_INPUTS);
    }

    function test_gasBaseline_small_fraudVerdictCompact() external {
        _run("small", _loadSmall(), Entry.FraudVerdictCompact, BUDGET_SMALL_FRAUD_VERDICT_COMPACT);
    }

    function test_gasBaseline_small_coreVerify() external {
        _run("small", _loadSmall(), Entry.CoreVerify, BUDGET_SMALL_CORE_VERIFY);
    }

    // ---------------------------------------------------------------- v2_production_shape.json (optional)
    function test_gasBaseline_production_verifyCompact() external {
        (bool present, Fixture memory fixture) = _loadProduction();
        if (present) _run("production", fixture, Entry.VerifyCompact, BUDGET_PRODUCTION_VERIFY_COMPACT);
    }

    function test_gasBaseline_production_verifyCompactPublicInputs() external {
        (bool present, Fixture memory fixture) = _loadProduction();
        if (present) {
            _run("production", fixture, Entry.VerifyCompactPublicInputs, BUDGET_PRODUCTION_VERIFY_COMPACT_PUBLIC_INPUTS);
        }
    }

    function test_gasBaseline_production_fraudVerdictCompact() external {
        (bool present, Fixture memory fixture) = _loadProduction();
        if (present) _run("production", fixture, Entry.FraudVerdictCompact, BUDGET_PRODUCTION_FRAUD_VERDICT_COMPACT);
    }

    function test_gasBaseline_production_coreVerify() external {
        (bool present, Fixture memory fixture) = _loadProduction();
        if (present) _run("production", fixture, Entry.CoreVerify, BUDGET_PRODUCTION_CORE_VERIFY);
    }

    // ---------------------------------------------------------------- measurement
    function _run(string memory label, Fixture memory fixture, Entry entry, uint256 budget) private {
        (MleVerifierV2 core, PinnedMleVerifierV2 pinned) = _deploy(fixture);

        if (entry == Entry.VerifyCompact) {
            bytes memory returned = _measure(
                label,
                "verifyCompact",
                address(pinned),
                abi.encodeCall(PinnedMleVerifierV2.verifyCompact, (fixture.compact)),
                budget
            );
            assertTrue(abi.decode(returned, (bool)), "verifyCompact must accept the honest proof");
        } else if (entry == Entry.VerifyCompactPublicInputs) {
            bytes memory returned = _measure(
                label,
                "verifyCompactPublicInputs",
                address(pinned),
                abi.encodeCall(PinnedMleVerifierV2.verifyCompactPublicInputs, (fixture.compact)),
                budget
            );
            uint256[] memory publicInputs = abi.decode(returned, (uint256[]));
            assertEq(publicInputs.length, fixture.proof.publicInputs.length, "authenticated public input length");
            for (uint256 i = 0; i < publicInputs.length; ++i) {
                assertEq(publicInputs[i], fixture.proof.publicInputs[i], "authenticated public input value");
            }
        } else if (entry == Entry.FraudVerdictCompact) {
            // Honest classifier path: a rollup-shaped (8 x 32-bit) public-input vector is bound to
            // its hash and reaches VALID; any other shape reaches PI_MISMATCH after full verification.
            (bytes32 expectedPiHash, uint8 expectedVerdict) = _honestClassifierInputs(fixture.proof.publicInputs);
            bytes memory returned = _measure(
                label,
                "fraudVerdictCompact",
                address(pinned),
                abi.encodeCall(PinnedMleVerifierV2.fraudVerdictCompact, (fixture.compact, expectedPiHash)),
                budget
            );
            assertEq(abi.decode(returned, (uint8)), expectedVerdict, "honest classifier verdict");
        } else {
            bytes memory returned = _measure(
                label,
                "coreVerify",
                address(core),
                abi.encodeCall(MleVerifierV2.verify, (fixture.proof, fixture.config)),
                budget
            );
            assertTrue(abi.decode(returned, (bool)), "core verify must accept the honest proof");
        }
    }

    /// @dev One raw staticcall over pre-encoded calldata. Logs the execution gas, the calldata
    /// size and both calldata pricings under stable `gas/<fixture>/<entry>/<metric>` names and
    /// enforces the budget (0 = log only).
    function _measure(string memory fixture, string memory entry, address target, bytes memory callData, uint256 budget)
        private
        returns (bytes memory returned)
    {
        (uint256 zeros, uint256 nonzeros) = _calldataStats(callData);
        string memory prefix = string.concat("gas/", fixture, "/", entry, "/");

        uint256 beforeGas = gasleft();
        (bool ok, bytes memory result) = target.staticcall(callData);
        uint256 used = beforeGas - gasleft();
        assertTrue(ok, string.concat(prefix, "call reverted"));

        emit log_named_uint(string.concat(prefix, "execution"), used);
        emit log_named_uint(string.concat(prefix, "calldataBytes"), callData.length);
        emit log_named_uint(string.concat(prefix, "calldataIntrinsic"), 21_000 + 4 * zeros + 16 * nonzeros);
        emit log_named_uint(string.concat(prefix, "calldataFloor7623"), 21_000 + 10 * (zeros + 4 * nonzeros));
        emit log_named_uint(string.concat(prefix, "budget"), budget);
        if (budget != 0) {
            assertLe(used, budget, string.concat(prefix, "execution exceeds BUDGET"));
        }
        return result;
    }

    function _calldataStats(bytes memory data) private pure returns (uint256 zeros, uint256 nonzeros) {
        for (uint256 i = 0; i < data.length; ++i) {
            if (data[i] == 0) ++zeros;
            else ++nonzeros;
        }
    }

    function _honestClassifierInputs(uint256[] memory publicInputs)
        private
        pure
        returns (bytes32 piHash, uint8 verdict)
    {
        if (publicInputs.length != 8) return (bytes32(0), VERDICT_PI_MISMATCH);
        uint256 hash;
        for (uint256 i = 0; i < 8; ++i) {
            if (publicInputs[i] >> 32 != 0) return (bytes32(0), VERDICT_PI_MISMATCH);
            hash |= publicInputs[i] << (224 - i * 32);
        }
        return (bytes32(hash), VERDICT_VALID);
    }

    // ---------------------------------------------------------------- fixtures
    function _loadMax() private view returns (Fixture memory) {
        return _load(vm.readFile(MAX_FIXTURE), "", ".pinnedVerifier");
    }

    function _loadSmall() private view returns (Fixture memory) {
        return _load(vm.readFile(SMALL_FIXTURE), ".cases[0]", ".cases[0].verificationKey");
    }

    /// @dev The production-shape fixture is optional: absent, empty or not (yet) parseable JSON is
    /// reported and skipped rather than failing, since it is generated by a separate process.
    function _loadProduction() private returns (bool present, Fixture memory fixture) {
        if (!vm.exists(PRODUCTION_FIXTURE)) {
            emit log_string("gas/production: fixture absent, skipped");
            return (false, fixture);
        }
        string memory json = vm.readFile(PRODUCTION_FIXTURE);
        try vm.keyExistsJson(json, ".pinnedVerifier") returns (bool hasPinned) {
            if (!hasPinned) revert("gas/production: fixture lacks .pinnedVerifier");
        } catch {
            emit log_string("gas/production: fixture unreadable, skipped");
            return (false, fixture);
        }
        return (true, _load(json, "", ".pinnedVerifier"));
    }

    /// @dev `proofPrefix` selects the object holding `solidityAbiProof`, `solidityAbiVerificationConfig`
    /// and `compactProof`; `idPrefix` the object holding `whirProtocolId` and `whirSessionId`.
    function _load(string memory json, string memory proofPrefix, string memory idPrefix)
        private
        pure
        returns (Fixture memory fixture)
    {
        fixture.proof = abi.decode(
            vm.parseJsonBytes(json, string.concat(proofPrefix, ".solidityAbiProof.bytes")), (MleVerifierV2.MleProof)
        );
        fixture.config = abi.decode(
            vm.parseJsonBytes(json, string.concat(proofPrefix, ".solidityAbiVerificationConfig.bytes")),
            (MleVerifierV2.VerificationConfig)
        );
        fixture.compact = vm.parseJsonBytes(json, string.concat(proofPrefix, ".compactProof.bytes"));

        bytes memory protocolId = vm.parseJsonBytes(json, string.concat(idPrefix, ".whirProtocolId"));
        require(protocolId.length == 64, "WHIR protocol identifier length");
        bytes32 first;
        bytes32 second;
        assembly ("memory-safe") {
            first := mload(add(protocolId, 0x20))
            second := mload(add(protocolId, 0x40))
        }
        fixture.whirProtocolId = [first, second];
        fixture.whirSessionId = vm.parseJsonBytes32(json, string.concat(idPrefix, ".whirSessionId"));
        require(fixture.proof.circuitDigest.length == 4, "circuit digest length");
        for (uint256 i = 0; i < 4; ++i) {
            fixture.circuitDigest[i] = uint64(fixture.proof.circuitDigest[i]);
        }
    }

    /// @dev Same deployment as V2ResourceEnvelope.t.sol so the figures are comparable.
    function _deploy(Fixture memory fixture) private returns (MleVerifierV2 core, PinnedMleVerifierV2 pinned) {
        core = new MleVerifierV2(
            block.chainid,
            fixture.proof.preprocessedRoot,
            fixture.whirProtocolId,
            fixture.whirSessionId,
            fixture.circuitDigest,
            fixture.config
        );
        pinned = new PinnedMleVerifierV2(core, fixture.config);
    }
}
