# Verify pure function contracts

`apl verify` checks arithmetic safety and function contracts for the current pure
scalar language. It uses Z3 5.3.3 and reports solver-trusted results. It supports
acyclic calls across source modules; recursive programs still compile and run,
but this verifier reports them as unsupported.

## Run a verification

Build the CLI with the pinned Rust toolchain and install the matching host archive
from the [Z3 5.3.3 release](https://github.com/Z3Prover/z3/releases/tag/z3-5.3.3).
The verifier's process driver supports macOS and Linux. Put `z3` on `PATH`, or
select its executable explicitly:

```sh
cargo build --release --locked
./target/release/apl verify examples/contracts/increment.apl --solver /path/to/z3
./target/release/apl verify examples/contracts/increment.apl --solver /path/to/z3 --json
```

The checked-in increment example verifies successfully. A solver installed in the
checkout's ignored `.tools/z3-5.3.3-arm64-osx-13.3/bin/z3` directory can be selected
with that relative path on macOS arm64. The tool does not download a solver or
change global configuration.

`--timeout-ms N` bounds the complete verification attempt after source checking,
including tool discovery and all solver queries. It defaults to 30000 and accepts
1 through 600000 milliseconds. A time or analysis limit produces `unknown`, never
verification success. `--solver` accepts one executable path, without shell
arguments or shell expansion.

## Write a contract

```text
fn increment(value: i64) -> i64
    requires value < 9223372036854775807;
    ensures (answer) answer == value + 1;
{
    value + 1
}
```

Preconditions follow the result type, then postconditions, then the body. Each
postcondition names its result explicitly. That name cannot shadow a parameter.
The compiler checks every clause's names and types, including clauses on unused
functions. `requires` and `ensures` remain ordinary identifiers elsewhere.

Specification integers are mathematical integers. A specification can use
`9223372036854775808`, even though executable `i64` arithmetic cannot produce that
value. The verifier separately checks every executed machine-arithmetic
intermediate. For example, `(value + 1) - 1` can overflow despite having a
mathematical result equal to `value`.

Clauses support parameter names, the postcondition result, scalar literals,
parentheses, and scalar operators. Calls, blocks, local bindings, and `if`
expressions inside clauses are not yet supported. Boolean short circuit can guard
partial specification arithmetic:

```text
fn quotient(value: i64) -> i64
    requires value != 0;
    requires 10 / value > 1;
    ensures (answer) answer == 10 / value;
{
    10 / value
}
```

Earlier true preconditions may guard later preconditions. A clause cannot assume
its own truth or a later clause to justify division. Preconditions must also be
satisfiable. Contradictory preconditions fail verification instead of making every
postcondition appear established. Postconditions cannot assume one another.

Division truncates toward zero in both executable and specification expressions.
The specification quotient of `-9223372036854775808 / -1` is mathematically valid;
that division and remainder are overflow traps in executable code.

## Understand the result

The verifier checks every loaded function, including private and unused functions.
A function with no explicit contracts still gets an arithmetic-safety check.
Any `let mut`, assignment, or `while` in any checked body makes the complete
attempt `unsupported`, including unused functions and unselected branches.
This preflight runs before compiler hashing, solver discovery, or query creation.
The diagnostic identifies the unsupported construct. A library does not need
`main`. An empty program reports that nothing was requested.

Calls check argument evaluation and callee preconditions, then analyze the actual
callee body. The verifier does not assume a callee's postconditions as axioms.
Branches, short-circuit operands, discarded expressions, and lexical scopes retain
their executable meaning.

| Exit | Result |
| ---: | --- |
| 0 | Every requested obligation verified and every precondition satisfiable |
| 1 | Invalid source or contract |
| 3 | Source loading or parsing resource limit |
| 4 | Invocation, solver protocol, tool, or I/O failure |
| 5 | Refuted property or unsatisfiable preconditions |
| 6 | Solver uncertainty, timeout, or verification analysis limit |
| 7 | Unsupported recursion, mutable state, loops, or an empty function graph |

A refuting solver model is labeled `replayed: false`. It is a candidate
counterexample, not an execution trace. A later error does not erase already
completed obligation results. Only the aggregate `verified` result returns zero.

The JSON report uses schema `apl-verify-v0`. It includes retained source hashes,
function identities, exact tool hashes and versions, limits, obligation locations,
SMT commands and hashes, outcomes, and candidate input assignments. Completed
query records include `get-value` when needed and `exit`; incomplete records are
marked `query_complete: false`. A source failure still produces one error report,
with unavailable bindings left null. `semantic_revision` is the checked
program's executable revision, including `local-state-2026-11-17` for rejected
stateful programs. It is null for source errors because no checked program
exists. Diagnostics also identify invalid source on stderr.

Preflight rejection or an empty function graph can also leave tool identities
null because discovery and hashing have not run. Null means unavailable or not
measured. Available source and function metadata remain recorded; successful
verification requires the complete compiler, solver, source, and query bindings.

Reports describe their exact source snapshot. They are not imported, cached as
proof input, or used to authorize a later build. Editing a source, contract, tool,
or option requires another verification attempt.

## Compilation and proof scope

Ordinary `check`, `eval`, `build`, and `run` type-check contracts and erase them.
They neither run a solver nor insert dynamic contract checks. `dump-core` exports
only the executable scalar program; importing it does not recover contracts.
`assert`, ghost code, mutable-state and loop verification, heap properties, and
recursive verification remain later work. Ordinary evaluation and native
compilation support the [local-state extension](../spec/control-flow.md).
Loop verification will require invariant obligations over mutable state;
finite unrolling cannot establish verification success.

The status `verified` establishes the requested arithmetic-safety and
partial-correctness obligations under the recorded SMT encoding and solver
assumptions. It does not establish native compiler correctness, a checked
termination proof, or a kernel-checked solver certificate. The
[formal proof inventory](../formal/PROOFS.md) separately records model theorems;
those do not prove this Rust generator or its SMT serialization correct.
The [verification specification](../spec/verification.md) defines exact rules,
resource bounds, protocol behavior, and the remaining FM-07 obligations.

For development checks, install the pinned solver before running the complete
suite. `APL_TEST_SOLVER` can select it for integration tests:

```sh
APL_TEST_SOLVER=/path/to/z3 cargo test --locked
APL_TEST_SOLVER=/path/to/z3 cargo test --release --locked
```

CI downloads the host's official archive, verifies its SHA-256, and runs real
solver tests alongside controlled protocol-failure tests. A missing real solver
does not silently skip semantic integration tests.
