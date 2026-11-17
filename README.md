# APL

APL is a programming language under development for native systems software and
capability-controlled agent applications, with strong static types and integrated
formal verification.

The current implementation checks, interprets, and compiles a scalar language with
`i64`, `bool`, unit, immutable bindings, conditionals, named recursive functions,
and explicit file modules. `apl verify` checks arithmetic safety and contracts
for pure acyclic functions using Z3 5.3.3, with results labeled `smt-trusted`.
Ordinary compilation type-checks and erases contract annotations. The Rust CLI
also exports and independently validates typed core JSON. Lean proofs cover
expression and recursive-function typing,
safety, and finite evaluator correspondence with sufficient depth and fuel.
A separate call-free verification-condition model proves contract soundness from
logical obligations; it does not certify the production verifier or solver.
These proofs do not establish termination or Rust implementation correctness.
See the [proof inventory](formal/PROOFS.md) for exact scope and assumptions.

From this checkout, with Rust installed through rustup:

```sh
cargo build --release --locked
./target/release/apl check examples/factorial.apl
./target/release/apl eval examples/factorial.apl
```

Evaluation prints `3628800`. The checked-in toolchain selects Rust 1.99.1.
The [getting-started guide](docs/getting-started.md) covers examples, diagnostics,
resource limits, and core import/export. The CLI also supports native `build`,
`run`, and `emit-c` through a host C11 compiler; see
[native compilation](docs/native-compilation.md). There is no qualified
installable release yet. Ownership, mutable data, I/O, concurrency, recursive
verification, and the wider language remain roadmap work.

- [Getting started](docs/getting-started.md)
- [Native compilation](docs/native-compilation.md)
- [Programs with modules](docs/modules.md)
- [Verify function contracts](docs/verification.md)
- [Formal model and proof checks](formal/README.md)
- [Language charter](docs/charter.md)
- [Architecture](docs/architecture/overview.md)
- [Language requirements](docs/requirements.md)
- [Roadmap](docs/roadmap.md)
- [Contributing](CONTRIBUTING.md)

The repository is named ANL; the language is named APL. This project is unrelated
to the existing APL array-programming language.
