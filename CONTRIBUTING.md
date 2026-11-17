# Contribute to APL

Start with the [architecture](docs/architecture/overview.md) and
[language requirements](docs/requirements.md). The repository currently contains
the scalar checker/interpreter, native C11 backend, file modules, core JSON
adapters, and a Lean model with expression and recursive-function proofs. Follow
[getting started](docs/getting-started.md) to build and run source programs; the
[proof inventory](formal/PROOFS.md) separates checked theorems from pending reverse
evaluator correspondence and implementation proofs.

## Build and check

From the repository root, use the pinned Rust 1.99.1 toolchain selected by rustup:

```sh
cargo build --release --locked
cargo fmt --all --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked
cargo test --locked --release
python3 -m unittest discover -s benchmarks -p 'test_*.py'
```

Both test commands include the public API compile-fail doctests. Native tests
require a host C11 compiler (`cc`, or an executable selected through `CC`). For formal
changes, install the pinned Lean 4.36.0 tools as described in
[formal/README.md](formal/README.md), then run:

```sh
formal/check.sh
python3 formal/test.py --rust target/release/apl
```

The proof check rebuilds the model, audits theorem dependencies, and replays
declarations through Lean's kernel. The comparison command executes the Rust and
Lean tools against specified outcomes; passing comparisons do not prove the Rust
implementation correct.

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

Native compilation will add binary execution and differential tests on supported
platforms. Later checks cover verifier regressions, property testing, fuzzing,
sanitizers, security analysis, performance, documentation examples, installation
and release artifact integrity.

Use reproducible tool versions and lockfiles. Keep workflow permissions read-only
unless a specific operation requires more. Keep secrets out of logs and source
files. Release qualification requires the checks relevant to the capabilities
being published.
