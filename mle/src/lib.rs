//! MLE/WHIR wire-v3 proving and verification use [`prover_v2`] and [`verifier_v2`].
//!
//! The historical protocol-1 prover, verifier, and standalone WHIR verifier
//! require the non-default `legacy-conformance` feature. That feature exists
//! only to maintain frozen conformance evidence, not for production use.
#![cfg_attr(
    not(feature = "legacy-conformance"),
    doc = r#"
Default dependencies cannot import the historical proof entrypoints:

```compile_fail
use plonky2_mle::prover::{mle_setup, mle_prove, mle_prove_from_tables};
```

```compile_fail
use plonky2_mle::verifier::mle_verify;
```

The optional-evaluation standalone verifier is also unavailable by default:

```compile_fail
use plonky2_mle::commitment::whir_pcs::{WhirEvalProof, WhirPCS};
fn historical_verify(pcs: &WhirPCS, proof: &WhirEvalProof) {
    let _ = pcs.verify(4, proof, None, None);
}
```

```compile_fail
use plonky2_mle::commitment::whir_pcs::{WhirEvalProof, WhirPCS};
fn historical_session_verify(pcs: &WhirPCS, proof: &WhirEvalProof) {
    let _ = pcs.verify_with_session(4, proof, None, None, "legacy");
}
```
"#
)]

pub mod commitment;
pub mod compact_v2;
pub mod config;
pub mod constraint_eval;
pub mod dense_mle;
pub mod eq_poly;
pub mod fixture;
pub mod fixture_v2;
pub mod gate_ext3;
pub mod permutation;
pub mod proof;
pub mod proof_v2;
#[path = "generated/mle_whir_v1.rs"]
pub mod protocol_schema;
#[path = "generated/mle_whir_v2.rs"]
pub mod protocol_schema_v2;
#[cfg(feature = "legacy-conformance")]
pub mod prover;
pub mod prover_v2;
pub mod sumcheck;
pub mod transcript;
pub mod transcript_v2;
#[cfg(feature = "legacy-conformance")]
pub mod verifier;
pub mod verifier_v2;
pub mod vk_v2;
