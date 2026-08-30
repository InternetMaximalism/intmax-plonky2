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

/// @dev The current MLE proof engine commits only random-linear combinations of
///      constituent oracle columns.  Because those batching scalars are known
///      before the corresponding commitment roots, correlated terminal-evaluation
///      forgeries remain possible. The verifier is therefore restricted to its
///      immutable deployment-chain pin. Configuring that pin to a public chain
///      is an explicit unsafe choice until commitments bind every constituent
///      polynomial before batching challenges are sampled.
///
///      This error MUST remain distinct from `InvalidMleProof`: inability to run
///      a verifier unavailable on the current chain is not evidence that an
///      authenticated proof is fraudulent. Fraud classifiers must treat it as
///      UNEVALUABLE.
error MleProofEngineUnavailable(uint256 chainId);
