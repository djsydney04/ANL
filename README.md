# APL

APL is a programming language under development for native systems software and
capability-controlled agent applications, with strong static types and integrated
formal verification.

The current implementation checks, interprets, and compiles a scalar language with
`i64`, `bool`, unit, immutable and initialized mutable bindings, assignment,
structured while loops, conditionals, recursive functions, and file modules.
`apl verify` checks arithmetic safety and contracts for scalar code with mutable
locals, annotated while loops and acyclic calls, using Z3 5.3.3. Results are labeled
`smt-trusted`.
Ordinary compilation type-checks and erases function contracts and loop invariant
annotations; it does not prove or dynamically enforce them. Verification checks
invariant initialization and preservation separately. The Rust CLI
also exports and independently validates typed core JSON. Lean proofs cover
expression and recursive-function typing,
safety, and finite evaluator correspondence with sufficient depth and fuel.
A separate local-state model proves typing and finite machine safety for mutation
and loops. Verification-condition proofs cover call-free terms and finite symbolic
function-body expansion with ordered callee preconditions when generation succeeds,
including loop-free local-state updates. The invariant-loop model adds safety
at every machine budget and partial correctness of normal returns.
These proofs do not certify the production verifier or solver. None of these proofs
establishes production termination or Rust implementation correctness.
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
installable release yet. Aggregates, ownership, I/O, concurrency, recursive
verification, and the wider language remain roadmap work. `verify` rejects any
program containing an unannotated loop or recursive call graph before starting a
solver. See the [loop example](docs/verification.md#verify-a-loop).

- [Getting started](docs/getting-started.md)
- [Native compilation](docs/native-compilation.md)
- [Programs with modules](docs/modules.md)
- [Mutable locals and while loops](spec/control-flow.md)
- [Verify function contracts](docs/verification.md)
- [Formal model and proof checks](formal/README.md)
- [Language charter](docs/charter.md)
- [Architecture](docs/architecture/overview.md)
- [Language requirements](docs/requirements.md)
- [Roadmap](docs/roadmap.md)
- [Contributing](CONTRIBUTING.md)

The repository is named ANL; the language is named APL. This project is unrelated
to the existing APL array-programming language.
