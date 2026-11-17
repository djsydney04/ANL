# Verify scalar function contracts

`anl verify` checks arithmetic safety and function contracts for pure scalar
code, mutable scalar locals, and while loops with invariants. It uses Z3 5.3.3
and reports solver-trusted results. It supports acyclic calls across source
modules. Verification requires an invariant on every loaded loop and rejects
recursive call graphs. Ordinary compilation supports unannotated loops and recursion.
Flat tuples are executable but unsupported by verification. Any tuple in the loaded
graph, including an unused signature, causes pre-tool exit 7 with `apl-verify-v2`,
`trust: "not_established"` and no obligations. Scalar and invariant-loop proofs
do not establish tuple properties; see the [exact boundary](../spec/flat-products.md#verification-boundary).

## Run a verification

Build the CLI with the pinned Rust toolchain and install the matching host archive
from the [Z3 5.3.3 release](https://github.com/Z3Prover/z3/releases/tag/z3-5.3.3).
The verifier's process driver supports macOS and Linux. Put `z3` on `PATH`, or
select its executable explicitly:

```sh
cargo build --release --locked
./target/release/anl verify examples/contracts/increment.anl --solver /path/to/z3
./target/release/anl verify examples/contracts/increment.anl --solver /path/to/z3 --json
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

## Verify a loop

An invariant describes the state immediately before each condition evaluation.
The [counter example](../examples/contracts/count.anl) uses two independent clauses:

```text
fn count_to(n: i64) -> i64
    requires 0 <= n && n <= 1000;
    ensures (answer) answer == n;
{
    let mut i = 0;
    while (i < n)
        invariant 0 <= i;
        invariant i <= n;
    {
        i = i + 1;
    }
    i
}
```

Its `main` calls `count_to(42)`. With the pinned solver installed, run:

```sh
./target/release/anl verify examples/contracts/count.anl --solver /path/to/z3 --json
./target/release/anl eval examples/contracts/count.anl
./target/release/anl run examples/contracts/count.anl
```

Verification returns `verified`, exit 0, with `verification_revision:
"apl-loop-verify-v1"`. Interpretation and native execution both print `42`.
The verifier checks each invariant's definedness and truth on entry and after
each normal body return. A clause cannot assume its own or another clause's
conclusion at either point. Inside the loop, the established invariant and the
condition guard support arithmetic safety and the eventual postcondition.

Every visible mutable non-unit local gets a fresh arbitrary head value, even if
the loop never writes it. Retain a needed relation in an invariant, or use an
immutable binding for a value that should stay fixed. Conditions may change
locals; the final false condition's changes remain visible after the loop, and
the invariant need not hold after that condition.

Verification proves partial correctness: if the function returns normally, its
postconditions hold, and no finite execution prefix traps under the assumptions.
It does not prove a return will occur. A safe `while (true) invariant true; {}`
can verify even with a false postcondition. A trap before that loop still fails
verification; unreachable operations after it need not execute safely. Entry
preconditions must remain defined and satisfiable, independent of divergence.
No global satisfiability check is imposed on loop invariants.

## Understand the result

The verifier checks every loaded function, including private and unused functions.
A function with no explicit contracts still gets an arithmetic-safety check.
Any loop without an invariant or any recursive call graph makes the complete
attempt `unsupported`, including imported or unused functions, unselected
branches, loop conditions/bodies, and call arguments. This preflight runs before
compiler hashing, solver discovery, or query creation. The diagnostic identifies
the unsupported construct. A library does not need `main`. An empty program reports that nothing was requested.

Ordinary checking validates invariant names and Boolean types, then erases the
clauses; it proves neither truth nor definedness. `verify` separately checks their
initialization and preservation. The
[annotation specification](../spec/loop-verification.md#source-annotations-and-erasure)
describes the source syntax and invariant rule.

Calls check argument evaluation and callee preconditions, then analyze the actual
callee body. The verifier does not assume a callee's postconditions as axioms.
Branches, short-circuit operands, discarded expressions, and lexical scopes retain
their executable meaning. Mutable assignments pass updated state to later
operands, conditions, and arguments. Leaving a scope retains changes to outer
locals. A callee receives copied argument values and cannot mutate caller locals.
Postconditions refer to the original entry parameters, even when a body creates
mutable locals with the same names.

| Exit | Result |
| ---: | --- |
| 0 | Every requested obligation verified and every precondition satisfiable |
| 1 | Invalid source or contract |
| 3 | Source loading or parsing resource limit |
| 4 | Invocation, solver protocol, tool, or I/O failure |
| 5 | Refuted verification obligation or unsatisfiable preconditions |
| 6 | Solver uncertainty, timeout, or verification analysis limit |
| 7 | Unsupported recursion, missing loop invariants, or an empty function graph |

A refuting solver model is labeled `replayed: false`. It is a candidate
counterexample, not an execution trace. A later error does not erase already
completed obligation results. Only the aggregate `verified` result returns zero.

The complete checked program selects one route:

| Program | Schema | Verification revision |
| --- | --- | --- |
| Pure scalar code | `apl-verify-v0` | No separate field |
| Local state without loops | `apl-verify-v1` | `apl-state-verify-v1` |
| Any while loop | `apl-verify-v1` | `apl-loop-verify-v1` |

The route is selected even when preflight rejects the program. Reports include retained
source hashes,
function identities, exact tool hashes and versions, limits, obligation locations,
SMT commands and hashes, outcomes, and candidate input assignments. Completed
query records include `get-value` when needed and `exit`; incomplete records are
marked `query_complete: false`. A source failure still produces one error report,
with unavailable bindings left null. `semantic_revision` is the checked
program's executable revision, including `local-state-2026-11-17` for rejected
stateful programs. It is null for source errors because no checked program
exists; those errors retain the v0 error envelope. Malformed CLI options produce
stderr and exit 4 without a JSON report. Diagnostics also identify invalid source
on stderr.

Each v1 obligation records `model_symbols`, listing every non-unit entry parameter
in declaration order, including unused parameters. Counterexamples retain that
complete assignment; unit values require no solver symbol. Loop queries also
request exactly the head symbols on which their assertion depends. Reports map
these symbols to source bindings, loop occurrences and call expansions, and retain
the constituent guarded checks in each query.

Loop-head assignments are abstract states used to check the invariant. They can
be unreachable in a concrete execution; a failure may mean the invariant is too
weak. Integer head values are mathematical decimal strings with a
`within_machine_range` flag. An inactive guarded head may have an out-of-range
value without making the solver response malformed. Entry parameters still
require in-range `i64` values. Every model remains `replayed: false`.

`source_loop_metadata_complete` says the source loop/binding scan completed. It
does not say expansion or query generation completed. `expansions` and
`loop_occurrences` can be partial on a later failure; per-function source metadata
can be null when preflight stops early. The [loop report contract](../spec/loop-verification.md#invariant-loop-report-contract)
defines these fields and their provenance.

State analysis has attempt-wide ceilings of 1000000 symbolic work units and
100000 arena nodes, in addition to the existing expression, query, byte, and time
limits. Environment copies, state merges, formula operands, and arena insertions
consume this budget. Loop verification also limits fresh head allocations to
4096 per attempt, counting repeated call expansions separately. A limit returns
`unknown` and retains completed query evidence. These added limits do not change
the pure v0 path.

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
`assert`, ghost code, heap properties, and recursive
verification remain later work. Ordinary evaluation and native
compilation support the [local-state extension](../spec/control-flow.md).
Loop verification uses invariant obligations over arbitrary mutable head states;
it does not establish success by finite unrolling.

The status `verified` establishes the requested arithmetic-safety and
partial-correctness obligations under the recorded SMT encoding and solver
assumptions. It does not establish native compiler correctness, a checked
termination proof, or a kernel-checked solver certificate. The
[formal proof inventory](../formal/PROOFS.md) separately records model theorems;
those do not prove this Rust generator or its SMT serialization correct. The
formal continuation/path-split generators and production's merged-flow analysis
are separate implementations with an unproved correspondence. Exact mathematical
query-partition theorems do not certify production query metadata or SMT encoding.
The [verification specification](../spec/verification.md) defines exact rules,
resource bounds, protocol behavior, and the remaining FM-07 obligations. The
[state verification specification](../spec/loop-verification.md) defines the
implemented loop-free and invariant-loop report contracts.

For development checks, install the pinned solver before running the complete
suite. `ANL_TEST_SOLVER` can select it for integration tests; the legacy
`APL_TEST_SOLVER` remains a fallback when the preferred variable is absent:

```sh
ANL_TEST_SOLVER=/path/to/z3 cargo test --locked
ANL_TEST_SOLVER=/path/to/z3 cargo test --release --locked
```

CI downloads the host's official archive, verifies its SHA-256, and runs real
solver tests alongside controlled protocol-failure tests. A missing real solver
does not silently skip semantic integration tests.
