// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.25;

/// @dev A verifier reached a proof-dependent check and obtained a definitive negative result.
///      This selector is deliberately reserved for invalid proof data. Configuration drift,
///      unsupported gates, internal invariant failures and resource exhaustion must use another
///      error (or bubble their original revert) so a rollup cannot turn "unable to evaluate" into
///      a fraud conviction.
error InvalidMleProof();

/// @dev The current MLE proof engine commits only random-linear combinations of
///      constituent oracle columns.  Because those batching scalars are known
///      before the corresponding commitment roots, correlated terminal-evaluation
///      forgeries remain possible.  Public-chain verification is therefore
///      deliberately unavailable until the commitments bind every constituent
///      polynomial before batching challenges are sampled.
///
///      This error MUST remain distinct from `InvalidMleProof`: inability to run
///      an unreleased verifier is not evidence that an authenticated proof is
///      fraudulent.  Fraud classifiers must treat it as UNEVALUABLE.
error MleProofEngineUnavailable(uint256 chainId);
