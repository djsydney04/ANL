# Contribute to APL

Start with the [architecture](docs/architecture/overview.md) and
[language requirements](docs/requirements.md). The repository currently contains
the scalar checker/interpreter, native C11 backend, file modules, core JSON
adapters, initialized mutable scalar locals and loops, a pure acyclic contract
verifier, and separate immutable/local-state Lean models. Verification-condition
proofs cover call-free terms and finite symbolic function-body expansion. Follow
[getting started](docs/getting-started.md) to build and run source programs; the
[proof inventory](formal/PROOFS.md) records finite model correspondence in both
directions and the remaining source, Rust, module, and backend proof boundaries.

## Build and check

From the repository root, use the pinned Rust 1.99.1 toolchain selected by rustup.
Native tests require a host C11 compiler. Verification tests require Z3 5.3.3;
install it using the [verification guide](docs/verification.md) and place `z3` on
`PATH`, or set `APL_TEST_SOLVER` to its executable path before running the suite.
A missing solver fails the semantic integration tests rather than skipping them.

```sh
cargo build --release --locked
cargo fmt --all --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked
cargo test --locked --release
python3 -m unittest discover -s benchmarks -p 'test_*.py'
```

Both test commands include the public API compile-fail doctests. `CC` can select
a host compiler executable. For formal changes, install the pinned Lean 4.36.0
tools as described in
[formal/README.md](formal/README.md), then run:

```sh
formal/check.sh
python3 formal/test.py --rust target/release/apl
python3 formal/test_local_state.py --rust target/release/apl
```

The proof check rebuilds the model, audits theorem dependencies, and replays
declarations through Lean's kernel. The comparison command executes the Rust and
Lean tools against specified outcomes; passing comparisons do not prove the Rust
implementation correct. The local-state model counts transitions, while Rust
counts expression entries and has a separate depth bound; resource-limited cases
are inconclusive comparisons. The proof inventory separates v0 theorems from the
new state machine and its forward finite-outcome embedding.

## Propose a language change

1. Identify the language capability or defect the change addresses.
2. Describe its behavior, competing alternatives, typing and evaluation rules.
3. Identify affected proof obligations, assumptions and compiler interfaces.
4. Define acceptance criteria and representative programs.
5. Obtain independent technical review of foundational changes.

## Validate an implementation

1. Implement a complete observable behavior.
2. Add positive and negative tests that detect plausible incorrect behavior.
3. Run affected component, integration and proof checks.
4. Update the specification, examples, proof coverage and known limitations.
5. Review the change and retain reproducible validation evidence.

Never disable a failing proof or test to obtain a passing build. Report checks
that could not run. Keep designed, implemented, tested and machine-checked
capabilities distinct.

## Continuous integration

The [current workflow](.github/workflows/ci.yml) configures Rust formatting, lint,
debug/release conformance and public API doctests on Linux and macOS, plus Lean
proof checks and evaluator comparisons on Linux. A configured job is not evidence
that it has passed on that platform; inspect the run for the revision under review.

The workflow includes native execution, module tests, arithmetic sanitizer
probes, and contract/verifier regressions with the pinned real solver and controlled
protocol-failure responders. At `f8ffb5f128aab5eaed4db3770ae500cd923cc61c`,
the Linux and macOS Rust jobs and the Lean proof/comparison job all passed
([run](https://github.com/djsydney04/ANL/actions/runs/44059286145)), including local
state and the 118-statement proof inventory. Later checks cover broader property
testing, fuzzing, security, installation, and release artifact integrity.

Use reproducible tool versions and lockfiles. Keep workflow permissions read-only
unless a specific operation requires more. Keep secrets out of logs and source
files. Release qualification requires the checks relevant to the capabilities
being published.
