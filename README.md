# APL

APL is a programming language under development for native systems software and
capability-controlled agent applications, with strong static types and integrated
formal verification.

The current M1 implementation checks and interprets a scalar language with
`i64`, `bool`, unit, immutable bindings, conditionals, and named recursive
functions. The Rust CLI also exports and independently validates typed core JSON.
Lean proofs cover the scalar expression model; function-call safety and Rust
implementation correctness remain unproved. See the [proof inventory](formal/PROOFS.md)
for exact theorem scope and assumptions.

From this checkout, with Rust installed through rustup:

```sh
cargo build --release --locked
./target/release/apl check examples/factorial.apl
./target/release/apl eval examples/factorial.apl
```

Evaluation prints `3628800`. The checked-in toolchain selects Rust 1.99.1.
The [getting-started guide](docs/getting-started.md) covers examples, diagnostics,
resource limits, and core import/export. There is no native-code backend or
qualified installable release yet. Ownership, mutable data, I/O, concurrency,
contracts, and the wider language remain roadmap work.

- [Getting started](docs/getting-started.md)
- [Formal model and proof checks](formal/README.md)
- [Language charter](docs/charter.md)
- [Architecture](docs/architecture/overview.md)
- [Language requirements](docs/requirements.md)
- [Roadmap](docs/roadmap.md)
- [Contributing](CONTRIBUTING.md)

The repository is named ANL; the language is named APL. This project is unrelated
to the existing APL array-programming language.
