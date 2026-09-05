# Plonky2 + WHIR

This fork repository was originally for [Plonky2 with FRI](https://github.com/0xPolygonZero/plonky2). In its mle/ directory, WHIR verification is available now. 
Periodic auditing and maintenance of this fork repository, including the MLE/WHIR proving system, is conducted by the Intmax team.

**WARNING: EXPERIMENTAL — PRODUCTION RELEASE REMAINS NO-GO.**

The current MLE implementation uses PCS wire v3 through the historical `V2`
Rust APIs and `MleVerifierV2` / `PinnedMleVerifierV2` Solidity contracts. Its
commitments bind the constituent tables before challenges and authenticate the
terminal claims and raw public inputs. Integrations must regenerate their
verification keys, configurations, and proofs together; old wire formats are
not accepted by the current entry points. The old Rust proving/verifying API
requires the non-default `legacy-conformance` feature, and the old Solidity
`MleVerifier` is abstract and retained for test conformance only.

See the [MLE implementation and migration guide](mle/README.md) for the exact
protocol, build commands, and remaining release gates. External cryptographic
review, the protocol-specific Fiat--Shamir/grinding analysis, and the complete
parent-system fixture and acceptance checks remain required. Keep deployment
containment in place. The [Lean audit archive](mle/audit/README.md) models the
July 2026 implementation; it does not certify PCS wire v3.

The [main repair integration record](mle/audit/main-pcs-repair-2026-09-05.md)
maps the reviewed gaps to the repair, records validation, and lists the
remaining release conditions.

## Documentation

For more details about the Plonky2 argument system, see this [writeup](plonky2/plonky2.pdf).

Polymer Labs has written up a helpful tutorial [here](https://polymerlabs.medium.com/a-tutorial-on-writing-zk-proofs-with-plonky2-part-i-be5812f6b798)!


## Examples

A good starting point for how to use Plonky2 for simple applications is the included examples:

* [`factorial`](plonky2/examples/factorial.rs): Proving knowledge of 100!
* [`fibonacci`](plonky2/examples/fibonacci.rs): Proving knowledge of the hundredth Fibonacci number
* [`range_check`](plonky2/examples/range_check.rs): Proving that a field element is in a given range
* [`square_root`](plonky2/examples/square_root.rs): Proving knowledge of the square root of a given field element

To run an example, use

```sh
cargo run --example <example_name>
```


## Building

The repository pins `nightly-2025-03-23` in `rust-toolchain` and commits
`Cargo.lock`. Install that toolchain and use the locked dependencies:

```sh
rustup toolchain install nightly-2025-03-23 --component rustfmt --component clippy
cargo build -p plonky2_mle --locked
```

Run these commands from the workspace root. Do not replace the pinned toolchain
with mutable `nightly`. The [MLE guide](mle/README.md#build-and-verification)
also describes offline checks once the pinned dependencies are cached.


## Running

To see recursion performance, one can run this bench, which generates a chain of three recursion proofs:

```sh
RUSTFLAGS=-Ctarget-cpu=native cargo run --release --example bench_recursion -- -vv
```

## Jemalloc

Plonky2 prefers the [Jemalloc](http://jemalloc.net) memory allocator due to its superior performance. To use it, include `jemallocator = "0.5.0"` in your `Cargo.toml` and add the following lines
to your `main.rs`:

```rust
use jemallocator::Jemalloc;

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;
```

Jemalloc is known to cause crashes when a binary compiled for x86 is run on an Apple silicon-based Mac under [Rosetta 2](https://support.apple.com/en-us/HT211861). If you are experiencing crashes on your Apple silicon Mac, run `rustc --print target-libdir`. The output should contain `aarch64-apple-darwin`. If the output contains `x86_64-apple-darwin`, then you are running the Rust toolchain for x86; we recommend switching to the native ARM version.

## Documentation

Generate documentation locally:

```sh
cargo doc --no-deps --open
```

## Contributing guidelines

See [CONTRIBUTING.md](./CONTRIBUTING.md).

## Licenses

All crates of this monorepo are licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.


## Security

This code has been audited prior to the `v1.0.0` release. The audits reports and findings are available in the [audits](./audits/) folder of this repository.
An audited codebase isn't necessarily free of bugs and security exploits, hence we recommend care when using `plonky2` in production settings.

If you find a security issue in the codebase, please refer to our [Security guidelines](./SECURITY.md) for private disclosure.

While Plonky2 is configurable, its defaults generally target 100 bits of security. The default FRI configuration targets 100 bits of *conjectured* security based on the conjecture in [ethSTARK](https://eprint.iacr.org/2021/582).

Plonky2's default hash function is Poseidon, configured with 8 full rounds, 22 partial rounds, a width of 12 field elements (each ~64 bits), and an S-box of `x^7`. [BBLP22](https://tosc.iacr.org/index.php/ToSC/article/view/9850) suggests that this configuration may have around 95 bits of security, falling a bit short of our 100 bit target.


## Links

- [Polygon Zero's zkEVM](https://github.com/0xPolygonZero/zk_evm), an efficient Type 1 zkEVM built on top of Starky and plonky2
- [System Zero](https://github.com/0xPolygonZero/system-zero), a zkVM built on top of Starky
- [Waksman](https://github.com/0xPolygonZero/plonky2-waksman), Plonky2 gadgets for permutation checking using Waksman networks
- [Insertion](https://github.com/0xPolygonZero/plonky2-insertion), Plonky2 gadgets for insertion into a list
- [u32](https://github.com/0xPolygonZero/plonky2-u32), Plonky2 gadgets for u32 arithmetic
- [ECDSA](https://github.com/0xPolygonZero/plonky2-ecdsa), Plonky2 gadgets for the ECDSA algorithm
