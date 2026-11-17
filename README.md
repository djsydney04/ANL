# ANL

ANL is a programming language under development for native systems software and
capability-controlled agent applications, with strong static types and integrated
formal verification.

A complete operating system authored in ANL is a required product outcome,
including boot code, the kernel, drivers, services, agent infrastructure and GUI.
The [OS architecture](docs/architecture/operating-system.md) describes this planned
work and its language requirements. There is no bootable ANL OS yet; the current
compiler produces hosted executables.

The current implementation checks, interprets, and compiles `i64`, `bool`, unit,
flat tuples of 1–8 scalar fields, immutable and initialized mutable bindings, assignment,
structured while loops, conditionals, recursive functions, file modules, and scoped
`i64` buffers with read/edit call views. Buffer owners have fixed length and close
on normal scope exit; views cannot escape a call.
`anl verify` checks arithmetic safety and contracts for scalar and flat-tuple code
with mutable locals, annotated while loops and acyclic calls, using Z3 5.3.3. Results are labeled
`smt-trusted`.
Ordinary compilation type-checks and erases function contracts and loop invariant
annotations; it does not prove or dynamically enforce them. Verification checks
invariant initialization and preservation separately. The Rust CLI
also exports and independently validates typed core JSON. Existing Lean proofs cover
scalar expression and recursive-function typing,
safety, and finite evaluator correspondence with sufficient depth and fuel.
A separate local-state model proves typing and finite machine safety for mutation
and loops. A separate flat-tuple model proves inference equivalence, finite
machine type safety and run/transition correspondence, including state and
recursive calls. Successful decoding by its Lean v2 reader implies a typed
model input. At every execution budget, that input cannot produce an invalid
model outcome, and any returned value has the model input's result type. Executable
comparisons remain evidence for Rust agreement; resource-limited comparisons are
inconclusive. Verification-condition proofs
cover call-free terms and finite symbolic
function-body expansion with ordered callee preconditions when generation succeeds,
including loop-free local-state updates. The invariant-loop model adds safety
at every machine budget and partial correctness of normal returns. A separate
merged flat-tuple generator proves those properties under successful generation,
typing, representation and valid-check premises. Its contract theorems include
ordered precondition definedness, typed entry witnesses and exact query partition.
These proofs do not certify the production verifier or solver. None of these proofs
establishes production termination or Rust implementation correctness.
The separate `ANL.Memory` model adds checked buffer typing, finite heap and
capability safety, resource-accounted Core execution, and finite canonical
Core/MIR correspondence in both directions. Its independent pair checker links
those theorems to accepted Core/MIR artifacts. Heap-bearing `verify` reports
unsupported with exit 7; the model proofs do not prove user heap contracts or
Rust/native correctness. See the [proof inventory](formal/PROOFS.md) for exact
scope and assumptions.

From this checkout, with Rust installed through rustup:

```sh
cargo build --release --locked
./target/release/anl check examples/factorial.anl
./target/release/anl eval examples/factorial.anl
```

Evaluation prints `3628800`. The checked-in toolchain selects Rust 1.99.1.
The [getting-started guide](docs/getting-started.md) covers examples, diagnostics,
resource limits, and core import/export. The CLI also supports native `build`,
`run`, and `emit-c` through a host C11 compiler; see
[native compilation](docs/native-compilation.md). There is no qualified
installable release yet. Nested aggregates, records, general collections and
ownership transfers, I/O, concurrency, recursive
verification, and the wider language remain roadmap work. `verify` rejects any
program containing an unannotated loop or a recursive call graph before
starting a solver. Tuple contracts support construction, projection and same-shape
equality, including invariant clauses. See the [tuple contract examples](docs/verification.md#verify-tuple-contracts).

- [Getting started](docs/getting-started.md)
- [Native compilation](docs/native-compilation.md)
- [Programs with modules](docs/modules.md)
- [Mutable locals and while loops](spec/control-flow.md)
- [Flat tuples and multiple return values](spec/flat-products.md)
- [Scoped buffers and views](docs/book/owned-buffers.md)
- [Buffer language and runtime specification](spec/owned-buffers.md)
- [Verify function contracts](docs/verification.md)
- [Formal model and proof checks](formal/README.md)
- [Language charter](docs/charter.md)
- [Architecture](docs/architecture/overview.md)
- [ANL-authored operating system](docs/architecture/operating-system.md)
- [Language requirements](docs/requirements.md)
- [Roadmap](docs/roadmap.md)
- [Contributing](CONTRIBUTING.md)

The language and its current tools are named ANL. Historical `apl-*` wire schema
IDs and semantic revisions, generated C/SMT identifiers, and the internal Lean
namespace `APL` remain compatibility identifiers. They do not name a different
language or change the recorded proof and benchmark artifacts.
