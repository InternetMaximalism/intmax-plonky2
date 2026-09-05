// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

/// @dev A verifier reached a proof-dependent check and obtained a definitive negative result.
///      This selector is deliberately reserved for invalid proof data. Configuration drift,
///      unsupported gates, internal invariant failures and resource exhaustion must use another
///      error (or bubble their original revert) so a rollup cannot turn "unable to evaluate" into
///      a fraud conviction.
error InvalidMleProof();

/// @dev The immutable execution-chain pin must be non-zero and must match the
///      chain on which the verifier constructor is running. This error is a
///      deployment/configuration failure, never evidence of an invalid proof.
error InvalidMleVerifierChainId(uint256 configuredChainId, uint256 actualChainId);

/// @dev Stored verifier/VK data is unsupported, malformed, or has drifted
///      from the deployment-time digest. This is UNEVALUABLE and MUST NOT be
///      interpreted as evidence that attacker-supplied proof bytes are false.
error InvalidMleVerifierConfiguration();

/// @dev Packed protocol v1 commits every ordered constituent group before its
///      dependent challenges and authenticates the terminal-used constituent
///      evaluations. The complete MLE construction nevertheless still uses
///      individual Goldilocks challenges in its outer algebraic arguments and
///      does not have the required 128-bit end-to-end soundness bound. The
///      verifier therefore remains restricted to its immutable deployment-chain
///      pin; configuring that pin to a public chain is an explicit unsafe choice
///      until the complete construction and migration receive independent review.
///
///      This error MUST remain distinct from `InvalidMleProof`: inability to run
///      a verifier unavailable on the current chain is not evidence that an
///      authenticated proof is fraudulent. Fraud classifiers must treat it as
///      UNEVALUABLE.
error MleProofEngineUnavailable(uint256 chainId);
