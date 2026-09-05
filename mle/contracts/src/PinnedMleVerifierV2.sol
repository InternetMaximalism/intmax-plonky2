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
import {GoldilocksExt3} from "./spongefish/GoldilocksExt3.sol";
import {SpongefishWhirVerify} from "./spongefish/SpongefishWhirVerify.sol";
import {MLE_PROTOCOL_VERSION_CURRENT} from "./generated/MleWhirV2.sol";

/// @title PinnedMleVerifierV2
/// @notice Per-circuit adapter that owns the complete dynamic v2 verification configuration.
/// @dev `MleVerifierV2` pins configuration digests but accepts the corresponding dynamic values on
/// every call. This adapter removes those values from application calldata: its constructor checks
/// that one complete configuration matches one already-deployed core, deep-copies it to storage,
/// and never exposes a mutator. Parent protocols therefore pin only this adapter address per VK.
contract PinnedMleVerifierV2 {
    uint8 private constant ENCODED_INVALID = 0;
    uint8 private constant ENCODED_VALID = 1;
    uint8 private constant ENCODED_UNEVALUABLE = 2;
    uint8 private constant ENCODED_STARVED = 3;
    uint8 private constant ENCODED_PI_MISMATCH = 4;

    error InvalidPinnedMleVerifierCore(address core);

    event MleVerifierV2Pinned(
        address indexed core, uint256 indexed chainId, bytes32 circuitConfigDigest, bytes32 whirParametersDigest
    );

    MleVerifierV2 public immutable core;
    uint256 public immutable allowedChainId;

    CircuitConfigV2.Parameters private _circuit;
    /// @dev Packed `row_u16_le || routed_column_u8`, exactly three bytes per PI.
    /// Solidity's dynamic-bytes storage packs the 103-PI production map into ten slots.
    bytes private _publicInputWireMap;
    uint256[] private _kIs;
    uint256[] private _subgroupGenPowers;
    Plonky2GateEvaluatorExt3.GateInfoV2[] private _gates;
    SpongefishWhirVerify.WhirParams private _whir;

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
        _storeConfiguration(config_);
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
        CircuitConfigV2.Parameters memory circuit = _circuit;
        proof = CompactMleProofV2.decode(compactProof, circuit);
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

    function _storeConfiguration(MleVerifierV2.VerificationConfig memory source) private {
        _circuit = source.circuit;
        _publicInputWireMap = source.publicInputWireMap;
        for (uint256 i = 0; i < source.kIs.length; ++i) {
            _kIs.push(source.kIs[i]);
        }
        for (uint256 i = 0; i < source.subgroupGenPowers.length; ++i) {
            _subgroupGenPowers.push(source.subgroupGenPowers[i]);
        }
        for (uint256 i = 0; i < source.gates.length; ++i) {
            _gates.push(source.gates[i]);
        }

        SpongefishWhirVerify.WhirParams memory whir = source.whir;
        _whir.numVariables = whir.numVariables;
        _whir.foldingFactor = whir.foldingFactor;
        _whir.numVectors = whir.numVectors;
        _whir.numCommitments = whir.numCommitments;
        _whir.outDomainSamples = whir.outDomainSamples;
        _whir.inDomainSamples = whir.inDomainSamples;
        _whir.initialSumcheckRounds = whir.initialSumcheckRounds;
        _whir.numRounds = whir.numRounds;
        _whir.finalSumcheckRounds = whir.finalSumcheckRounds;
        _whir.finalSize = whir.finalSize;
        _whir.initialCodewordLength = whir.initialCodewordLength;
        _whir.initialMerkleDepth = whir.initialMerkleDepth;
        _whir.initialDomainGenerator = whir.initialDomainGenerator;
        _whir.initialInterleavingDepth = whir.initialInterleavingDepth;
        _whir.initialNumVariables = whir.initialNumVariables;
        _whir.initialCosetSize = whir.initialCosetSize;
        _whir.initialNumCosets = whir.initialNumCosets;
        _whir.initialSumcheckPowThreshold = whir.initialSumcheckPowThreshold;
        _whir.finalPowThreshold = whir.finalPowThreshold;
        _whir.finalSumcheckPowThreshold = whir.finalSumcheckPowThreshold;
        for (uint256 i = 0; i < whir.rounds.length; ++i) {
            _whir.rounds.push(whir.rounds[i]);
        }
    }

    function _loadConfiguration() private view returns (MleVerifierV2.VerificationConfig memory config) {
        config.circuit = _circuit;
        config.publicInputWireMap = _publicInputWireMap;
        config.kIs = _kIs;
        config.subgroupGenPowers = _subgroupGenPowers;
        config.gates = _gates;
        config.whir = _loadWhir();
    }

    function _loadWhir() private view returns (SpongefishWhirVerify.WhirParams memory whir) {
        whir.numVariables = _whir.numVariables;
        whir.foldingFactor = _whir.foldingFactor;
        whir.numVectors = _whir.numVectors;
        whir.numCommitments = _whir.numCommitments;
        whir.outDomainSamples = _whir.outDomainSamples;
        whir.inDomainSamples = _whir.inDomainSamples;
        whir.initialSumcheckRounds = _whir.initialSumcheckRounds;
        whir.numRounds = _whir.numRounds;
        whir.finalSumcheckRounds = _whir.finalSumcheckRounds;
        whir.finalSize = _whir.finalSize;
        whir.initialCodewordLength = _whir.initialCodewordLength;
        whir.initialMerkleDepth = _whir.initialMerkleDepth;
        whir.initialDomainGenerator = _whir.initialDomainGenerator;
        whir.initialInterleavingDepth = _whir.initialInterleavingDepth;
        whir.initialNumVariables = _whir.initialNumVariables;
        whir.initialCosetSize = _whir.initialCosetSize;
        whir.initialNumCosets = _whir.initialNumCosets;
        whir.initialSumcheckPowThreshold = _whir.initialSumcheckPowThreshold;
        whir.finalPowThreshold = _whir.finalPowThreshold;
        whir.finalSumcheckPowThreshold = _whir.finalSumcheckPowThreshold;
        whir.evaluationPoint = new GoldilocksExt3.Ext3[](0);
        whir.evaluationPoint2 = new GoldilocksExt3.Ext3[](0);
        whir.additionalEvaluationPoints = new GoldilocksExt3.Ext3[][](0);
        whir.rounds = _whir.rounds;
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
