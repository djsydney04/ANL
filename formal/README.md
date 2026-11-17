# APL formal core

This directory implements the `m1-2026-11-16` scalar expression model in Lean
4.36.0. It includes untyped syntax, declarative typing, an independently checked
inference function, a small-step evaluation machine, and proofs of type
uniqueness, preservation, progress, and finite evaluator correspondence.

The model covers bounded `i64`, `bool`, `unit`, lexical variables, immutable
lets, all scalar unary and binary operators, and conditionals. It is the first
mechanized slice of APL. It does not replace the complete-language roadmap.

## Build and check

Install the version named by `lean-toolchain` through an existing Lean/elan
installation, or put the corresponding official release's `bin` directory on
`PATH`. No third-party Lean packages are required.

From the repository root:

```sh
formal/check.sh
python3 formal/test.py
cargo build --locked
python3 formal/test.py --rust target/debug/apl
```

`check.sh` performs a clean build, rejects incomplete proof and custom axiom
syntax, checks every inventoried theorem's transitive axiom dependencies, and
replays the model declarations through `leanchecker`. Build warnings are errors.
The axiom audit fails on anything outside `propext`, `Classical.choice`, and
`Quot.sound`. The current proofs use only `propext` and `Quot.sound`.

The checked toolchain was the official
[Lean 4.36.0 release](https://github.com/leanprover/lean4/releases/tag/v4.36.0),
commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The macOS AArch64 release
archive's SHA-256 was verified as
`49acada8749ad1343eff1224a3d2510ac61ed53363d37b5e738e8c587e7deabd`.
The release is pinned; updating Lean requires repeating all checks.

An isolated installation at the repository's ignored
`.tools/lean-4.36.0-darwin_aarch64` can be used without changing global defaults:

```sh
PATH="$PWD/.tools/lean-4.36.0-darwin_aarch64/bin:$PATH" formal/check.sh
```

That local path is optional and platform-specific. The portable commands above
use the pinned version selected by the developer's toolchain manager.

## Executable reference

The built CLI accepts the shared [core format](../spec/core-format.md):

```sh
formal/.lake/build/bin/apl_formal spec/fixtures/core-expression.json
formal/.lake/build/bin/apl_formal spec/fixtures/core-program.json --fuel 100000
```

Both fixtures produce `{"outcome":"value","type":"i64","value":"42"}`.
The exit codes match the compiler's interchange CLI: 0 for a value, 1 for invalid
IR, 2 for an arithmetic trap, 3 for a resource limit, and 4 for an invocation or
file-access error. Output is one JSON outcome; file-access and invocation
messages go to stderr.

The reader rejects unknown/missing fields, duplicate object members, noncanonical
integer strings, decimal/exponent index representations, invalid UTF-8, unbound
locals, invalid function IDs, wrong arities, and inconsistent types. It checks
all functions and branches, including unused ones. Serialized `ty` annotations
are checked against inference. De Bruijn index zero denotes the newest local;
at function entry it denotes the final declared parameter.

Expression documents run `APL.run`, the evaluator covered by the expression
proofs. Each machine transition consumes one unit, and recognizing the terminal
state consumes one additional unit. A literal therefore needs two fuel units.
Fuel zero always yields `resource_limit`.

Program documents run `APL.Program.eval`, a separate executable evaluator that
supports named and mutually recursive calls. It charges one unit immediately
before evaluating each expression, with a global decreasing budget and a
256-expression nesting bound. Entry invocation is free; only evaluated arguments,
branches and operands consume fuel. Its correspondence to
`APL.Program.Step` is **not proved**. The expression theorems do not certify
recursive programs. Program execution is covered by conformance tests.

The CLI bounds files at 1,048,576 bytes, JSON nesting at 256, expression trees at
128, and indices at 4,294,967,295. These limits and exhausted fuel report
`resource_limit`, except an out-of-range index is invalid IR. Different tools can
hit different bounds. Resource-limited comparisons are inconclusive about
language behavior; they do not establish divergence or type safety.

## Model and evidence

- `APL/Core.lean` defines types, bounded values, untyped expressions, declarative
  typing, inference, checked arithmetic, and their basic theorems.
- `APL/Machine.lean` defines explicit environments, continuation frames, machine
  states, and typing judgments for intermediate configurations.
- `APL/Semantics.lean` defines the inductive, fuel-free `Step` relation and its
  finite closure. It proves preservation and progress and proves both directions
  of correspondence with the bounded executable machine.
- `APL/ProgramSemantics.lean` extends the mathematical small-step vocabulary with
  global functions and ordered arguments. Its relation has no fuel argument;
  infinite reduction represents divergence. Its safety and evaluator
  correspondence proofs remain FM-05 work.
- `APL/Program.lean`, `APL/Wire.lean`, and `Main.lean` implement program execution
  and strict interchange. These adapters and executable compilation remain
  trusted and tested components.
- `APL/Smoke.lean` contains kernel-reduced arithmetic, trap, short-circuit,
  scoping, and typing examples. `test.py` drives the actual executables against
  specified expected outcomes and a separate Python integer oracle, including
  deterministic generated terms and source-to-core recursive cases when Rust
  comparison is enabled.

The exact theorem statements, assumptions, and coverage are recorded in the
[proof inventory](PROOFS.md). These proofs concern the Lean model. They do not
prove the Rust parser, resolver, checker, exporter, interpreter, future native
backend, runtime, OS, or hardware correct. Executing a compiled Lean evaluator
also trusts Lean compilation and its runtime; a kernel proof is separate evidence.
