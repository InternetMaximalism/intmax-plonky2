// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

import {CircuitConfigV2} from "./CircuitConfigV2.sol";
import {CompactMleProofV2} from "./CompactMleProofV2.sol";
import {
    InvalidMleProof,
    InvalidMleVerifierChainId,
    InvalidMleVerifierConfiguration,
    MleProofEngineUnavailable
} from "./MleProofErrors.sol";
import {MleVerifierV2} from "./MleVerifierV2.sol";
import {Plonky2GateEvaluatorExt3} from "./Plonky2GateEvaluatorExt3.sol";
import {SpongefishWhirVerify} from "./spongefish/SpongefishWhirVerify.sol";
import {MLE_PROTOCOL_VERSION_CURRENT} from "./generated/MleWhirV2.sol";

/// @title PinnedMleVerifierV2
/// @notice Per-circuit adapter that owns the complete dynamic v2 verification configuration.
/// @dev `MleVerifierV2` pins configuration digests but accepts the corresponding dynamic values on
/// every call. This adapter removes those values from application calldata: its constructor checks
/// that one complete configuration matches one already-deployed core, writes its exact ABI encoding
/// into an immutable code-resident configuration store, and never exposes a mutator. Parent
/// protocols therefore pin only this adapter address per VK.
/// @dev The configuration is materialized from contract code (`EXTCODECOPY`) rather than from
/// storage: the 7.5 KB production profile spans roughly 170 storage slots, and reading them cold on
/// every verification cost about 360,000 gas of the 30,000,000-gas transaction envelope. Code is as
/// immutable as constructor-written storage with no mutator, so the trust boundary is unchanged.
contract PinnedMleVerifierV2 {
    uint8 private constant ENCODED_INVALID = 0;
    uint8 private constant ENCODED_VALID = 1;
    uint8 private constant ENCODED_UNEVALUABLE = 2;
    uint8 private constant ENCODED_STARVED = 3;
    uint8 private constant ENCODED_PI_MISMATCH = 4;

    error InvalidPinnedMleVerifierCore(address core);
    error ConfigurationStoreDeploymentFailed();

    event MleVerifierV2Pinned(
        address indexed core, uint256 indexed chainId, bytes32 circuitConfigDigest, bytes32 whirParametersDigest
    );

    MleVerifierV2 public immutable core;
    uint256 public immutable allowedChainId;

    /// @dev Contract whose runtime code is `0x00 || abi.encode(VerificationConfig)`. The leading
    /// `STOP` byte makes the data non-executable; the store has no constructor logic, no storage
    /// and no way to change. It is created once by this constructor and referenced only here.
    address private immutable _configStore;
    /// @dev Exact byte length of the ABI-encoded configuration, pinned so a store whose code was
    /// somehow shortened or extended can never decode as a different configuration.
    uint256 private immutable _configLength;

    constructor(MleVerifierV2 core_, MleVerifierV2.VerificationConfig memory config_) {
        if (address(core_) == address(0) || address(core_).code.length == 0) {
            revert InvalidPinnedMleVerifierCore(address(core_));
        }

        uint256 pinnedChainId = core_.allowedChainId();
        if (pinnedChainId == 0 || block.chainid != pinnedChainId) {
            revert InvalidMleVerifierChainId(pinnedChainId, block.chainid);
        }

        bytes32 computedWhirDigest = keccak256(abi.encode(config_.whir));
        if (computedWhirDigest != core_.whirParametersDigest()) revert InvalidMleVerifierConfiguration();

        uint256[] memory circuitDigest = new uint256[](4);
        circuitDigest[0] = core_.circuitDigest0();
        circuitDigest[1] = core_.circuitDigest1();
        circuitDigest[2] = core_.circuitDigest2();
        circuitDigest[3] = core_.circuitDigest3();
        bytes32 computedCircuitDigest = CircuitConfigV2.digest(
            config_.circuit,
            circuitDigest,
            config_.kIs,
            config_.subgroupGenPowers,
            config_.gates,
            config_.publicInputWireMap
        );
        if (computedCircuitDigest != core_.circuitConfigDigest()) revert InvalidMleVerifierConfiguration();

        // A canonical v2 core rejects all prover-derived point arrays in its constructor. Repeat
        // the invariant here because this contract deliberately stores only the trusted profile;
        // evaluation points are derived from the transcript inside the core on every verification.
        if (
            config_.whir.evaluationPoint.length != 0 || config_.whir.evaluationPoint2.length != 0
                || config_.whir.additionalEvaluationPoints.length != 0
        ) revert InvalidMleVerifierConfiguration();

        core = core_;
        allowedChainId = pinnedChainId;
        bytes memory encodedConfig = abi.encode(config_);
        _configLength = encodedConfig.length;
        _configStore = _deployConfigurationStore(encodedConfig);
        emit MleVerifierV2Pinned(address(core_), pinnedChainId, computedCircuitDigest, computedWhirDigest);
    }

    /// @notice Verify using only the constructor-pinned configuration.
    /// @dev The local guard runs before any storage-to-memory expansion. A contract moved to a
    /// different chain is unavailable, never an alternate execution environment for the proof.
    function verify(MleVerifierV2.MleProof calldata proof) external view returns (bool) {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        return core.verify(proof, _loadConfiguration());
    }

    /// @notice Verify the unique two-blob-capable `MLEWHIR3` DA encoding.
    /// @dev The compact decoder derives every array length from this adapter's
    /// constructor-pinned circuit. Applications should authenticate these exact
    /// bytes against proof DA and call this entry point; no caller-supplied ABI
    /// tuple or second representation is trusted.
    function verifyCompact(bytes calldata compactProof) external view returns (bool) {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decodeForCoreVerification(compactProof, config.circuit);
        return core.verify(proof, config);
    }

    /// @notice Verify canonical compact bytes and return their authenticated public inputs.
    /// @dev Parent protocols must bind application state to the public inputs of the exact proof
    /// bytes they verify. Returning the decoded vector only after the pinned core accepts avoids a
    /// second decoder and prevents callers from treating unauthenticated compact prefixes as proof
    /// outputs. The production core returns only `true`; any other successful return is a broken
    /// deployment/configuration condition, not proof-dependent fraud.
    function verifyCompactPublicInputs(bytes calldata compactProof)
        external
        view
        returns (uint256[] memory publicInputs)
    {
        if (block.chainid != allowedChainId) revert MleProofEngineUnavailable(block.chainid);
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decodeForCoreVerification(compactProof, config.circuit);
        if (!core.verify(proof, config)) revert InvalidMleVerifierConfiguration();
        publicInputs = proof.publicInputs;
    }

    /// @notice Classify authenticated compact DA bytes through the pinned core.
    /// @dev Only a successful strict decode followed by an exact `InvalidMleProof()`
    /// from the pinned core, or an exact decoder `InvalidMleProof()`, can convict.
    /// Resource exhaustion and all unknown failures remain non-convicting.
    function fraudVerdictCompact(bytes calldata compactProof, bytes32 expectedPiHash)
        external
        view
        returns (uint8)
    {
        if (block.chainid != allowedChainId) return ENCODED_UNEVALUABLE;

        // Keep untrusted decoding and core execution inside one catchable frame. Returning the
        // decoded maximum proof to this frame and ABI-encoding it a second time costs almost two
        // million gas and leaves the parent fraud transaction without a practical block-envelope
        // margin. The body below still preserves the exact same security boundary: only its strict
        // decoder or the pinned core may produce `InvalidMleProof()`.
        uint256 reserve = gasleft() / 64;
        uint256 budget = gasleft() - reserve;
        try this.compactFraudVerdictBody{gas: budget}(compactProof, expectedPiHash) returns (
            uint8 verdict
        ) {
            if (verdict <= ENCODED_PI_MISMATCH) return verdict;
            return ENCODED_UNEVALUABLE;
        } catch (bytes memory reason) {
            if (gasleft() < reserve + budget / 8) return ENCODED_STARVED;
            if (_isInvalidMleProof(reason)) return ENCODED_INVALID;
            return ENCODED_UNEVALUABLE;
        }
    }

    /// @notice Isolated implementation used by `fraudVerdictCompact`.
    /// @dev A direct caller receives ordinary reverts and MUST NOT use this as a fraud classifier;
    /// only the outer entry point reserves gas and maps exact proof-dependent failures. Keeping the
    /// decoded proof in this frame avoids a large ABI return/copy without weakening classification.
    function compactFraudVerdictBody(bytes calldata compactProof, bytes32 expectedPiHash)
        external
        view
        returns (uint8)
    {
        if (msg.sender != address(this)) revert InvalidMleVerifierConfiguration();
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        MleVerifierV2.MleProof memory proof = CompactMleProofV2.decode(compactProof, config.circuit);
        bool piMatches = _publicInputsMatch(proof.publicInputs, expectedPiHash);
        if (!core.verify(proof, config)) return ENCODED_UNEVALUABLE;
        return piMatches ? ENCODED_VALID : ENCODED_PI_MISMATCH;
    }

    /// @notice Decode compact bytes with this adapter's trusted circuit shape.
    /// @dev External only so the fraud classifier can catch malformed bytes and
    /// decoder resource exhaustion without conflating the two.
    function decodeCompactMleProof(bytes calldata compactProof)
        external
        view
        returns (MleVerifierV2.MleProof memory proof)
    {
        proof = CompactMleProofV2.decode(compactProof, _loadConfiguration().circuit);
    }

    /// @notice Classify authenticated canonical ABI bytes through the pinned core/config pair.
    /// @dev Decoding and classification live here so verification crosses only one EIP-150 boundary:
    /// this adapter calls `core.verify` exactly once. Only an exact `InvalidMleProof()` revert from
    /// that pinned core can produce INVALID after decoding. The chain guard precedes raw decoding.
    function fraudVerdictEncoded(bytes calldata rawProof, bytes32 expectedPiHash)
        external
        view
        returns (uint8)
    {
        if (block.chainid != allowedChainId) return ENCODED_UNEVALUABLE;

        MleVerifierV2.MleProof memory proof;
        bool canonical;
        {
            uint256 decodeReserve = gasleft() / 64;
            uint256 decodeBudget = gasleft() - decodeReserve;
            try this.decodeCanonicalMleProof{gas: decodeBudget}(rawProof) returns (
                MleVerifierV2.MleProof memory decoded, bool isCanonical
            ) {
                proof = decoded;
                canonical = isCanonical;
            } catch (bytes memory reason) {
                if (gasleft() < decodeReserve + decodeBudget / 8) return ENCODED_STARVED;
                if (reason.length == 0 || _isMemoryAllocationPanic(reason)) return ENCODED_INVALID;
                return ENCODED_UNEVALUABLE;
            }
        }

        if (!canonical || proof.protocolVersion != MLE_PROTOCOL_VERSION_CURRENT) return ENCODED_INVALID;
        bool piMatches = _publicInputsMatch(proof.publicInputs, expectedPiHash);

        // Materialize the trusted configuration before fixing the call budget. Storage expansion
        // and ABI construction are adapter availability costs, while the reserve below isolates
        // exhaustion inside the untrusted proof-dependent verification execution.
        MleVerifierV2.VerificationConfig memory config = _loadConfiguration();
        bytes memory callData = abi.encodeWithSelector(MleVerifierV2.verify.selector, proof, config);
        uint256 verifyReserve = gasleft() / 64;
        uint256 verifyBudget = gasleft() - verifyReserve;
        (bool ok, bytes memory result) = address(core).staticcall{gas: verifyBudget}(callData);
        if (ok) {
            if (result.length == 32) {
                uint256 returned;
                assembly ("memory-safe") {
                    returned := mload(add(result, 0x20))
                }
                if (returned == 1) return piMatches ? ENCODED_VALID : ENCODED_PI_MISMATCH;
            }
            return ENCODED_UNEVALUABLE;
        }
        if (_isInvalidMleProof(result)) return ENCODED_INVALID;
        if (gasleft() < verifyReserve + verifyBudget / 8) return ENCODED_STARVED;
        return ENCODED_UNEVALUABLE;
    }

    /// @notice Decode raw ABI proof bytes and report whether they have one unique encoding.
    /// @dev External only so malformed offsets and allocation panics can be caught by the classifier.
    function decodeCanonicalMleProof(bytes calldata rawProof)
        external
        pure
        returns (MleVerifierV2.MleProof memory proof, bool canonical)
    {
        proof = abi.decode(rawProof, (MleVerifierV2.MleProof));
        bytes memory encoded = abi.encode(proof);
        canonical = encoded.length == rawProof.length && keccak256(encoded) == keccak256(rawProof);
    }

    /// @dev Deploy the immutable configuration store. Init code is the standard eleven-byte
    /// "return everything after me" prologue (`PUSH1 0x0b CODESIZE DUP2 CODESIZE SUB DUP1 SWAP3
    /// MSIZE CODECOPY RETURN`) followed by a `STOP` guard byte and the encoded configuration.
    function _deployConfigurationStore(bytes memory encodedConfig) private returns (address store) {
        bytes memory initCode = abi.encodePacked(hex"600b5981380380925939f3", hex"00", encodedConfig);
        assembly ("memory-safe") {
            store := create(0, add(initCode, 0x20), mload(initCode))
        }
        if (store == address(0) || store.code.length != encodedConfig.length + 1) {
            revert ConfigurationStoreDeploymentFailed();
        }
    }

    function _loadConfiguration() private view returns (MleVerifierV2.VerificationConfig memory config) {
        address store = _configStore;
        uint256 length = _configLength;
        if (store.code.length != length + 1) revert InvalidMleVerifierConfiguration();
        bytes memory encodedConfig = new bytes(length);
        assembly ("memory-safe") {
            extcodecopy(store, add(encodedConfig, 0x20), 1, length)
        }
        config = abi.decode(encodedConfig, (MleVerifierV2.VerificationConfig));
    }

    function _publicInputsMatch(uint256[] memory publicInputs, bytes32 piHash) private pure returns (bool) {
        if (publicInputs.length != 8) return false;
        uint256 hash = uint256(piHash);
        for (uint256 i = 0; i < 8; ++i) {
            if (publicInputs[i] != ((hash >> (224 - i * 32)) & 0xffffffff)) return false;
        }
        return true;
    }

    function _isInvalidMleProof(bytes memory reason) private pure returns (bool yes) {
        if (reason.length != 4) return false;
        bytes4 selector;
        assembly ("memory-safe") {
            selector := mload(add(reason, 0x20))
        }
        return selector == InvalidMleProof.selector;
    }

    function _isMemoryAllocationPanic(bytes memory reason) private pure returns (bool yes) {
        assembly ("memory-safe") {
            yes := and(
                eq(mload(reason), 36),
                and(eq(mload(add(reason, 0x20)), shl(224, 0x4e487b71)), eq(mload(add(reason, 0x24)), 0x41))
            )
        }
    }
}
