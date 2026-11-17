# Getting started with ANL

ANL provides a Rust command-line checker, reference interpreter, and native
compiler for a small, statically typed language. It supports checked `i64`
arithmetic, booleans, unit, flat tuples, immutable and initialized mutable bindings, assignment,
while loops, lexical blocks, conditionals, recursive functions, and file modules.
An optional verifier checks arithmetic safety and contracts for scalar and flat-tuple functions
with mutable locals, annotated while loops and acyclic calls. Collections,
ownership, source-level I/O, concurrency, and recursive verification remain in
the [roadmap](roadmap.md).

## Build and run

Install Rust through rustup, then run these commands from this checkout. The
checked-in toolchain file selects Rust 1.99.1, including rustfmt and Clippy.

```sh
cargo build --release --locked
./target/release/anl --version
./target/release/anl check examples/factorial.anl
./target/release/anl eval examples/factorial.anl
```

The evaluation prints `3628800` followed by a newline. Its process exit status is
zero; the numeric result is printed rather than truncated to an exit status.
The checker accepts a library without an entry point. Evaluation requires exactly
one `fn main() -> i64` with no parameters in the root file and checks every
function first, including unused imported functions.

A complete small program is:

```text
fn square(x: i64) -> i64 {
    x * x
}

fn main() -> i64 {
    let answer = square(6) + 6;
    answer
}
```

Save it as `answer.anl` and run `./target/release/anl eval answer.anl` to print `42`.
The final expression has no semicolon. A block with no final expression returns
`unit`, whose literal is `()`. Arithmetic and function arguments are statically
checked; there are no implicit type conversions.

## Build a native executable

Install a host C11 compiler providing `cc`, then run:

```sh
./target/release/anl build examples/factorial.anl -o /tmp/anl-factorial
/tmp/anl-factorial
./target/release/anl run examples/factorial.anl
```

Both executions print `3628800`. `build` publishes an executable at the requested
path; `run` builds and runs a temporary executable. `CC` may select a compiler
executable. See [native compilation](native-compilation.md) for output paths,
traps, tool failures, and emitted C. Native execution uses the host stack without
the interpreter's artificial fuel and nesting budgets.

## Update locals in a loop

Use `let mut` for an initialized value whose type stays fixed. Parameters and
ordinary `let` bindings remain immutable. A loop has a parenthesized Boolean
condition and a unit-valued body:

```text
fn main() -> i64 {
    let mut i = 0;
    let mut sum = 0;
    while (i < 100) {
        i = i + 1;
        sum = sum + i;
    }
    sum
}
```

Assignment requires a semicolon; a while statement ends at its closing brace.
The final expression `sum` returns `5050`. The checked-in examples run as follows:

```sh
./target/release/anl eval examples/control-flow/sum.anl
./target/release/anl run examples/control-flow/sum.anl
./target/release/anl eval examples/control-flow/gcd.anl
```

The first two commands print `5050`; the last prints `21`. Inner scopes preserve
updates to outer locals, and each loop iteration creates fresh body locals.
Calls capture argument values into a fresh frame, so callee-local updates cannot
change caller variables. This introduces no references or shared cells. See the
[local-state specification](../spec/control-flow.md) for exact evaluation order,
typing, and limits. `break`, `continue`, early `return`, and `for` are not supported.

You can attach typed, erased invariant annotations to a loop:

```text
fn main() -> i64 {
    let mut i = 0;
    while (i < 3)
        invariant 0 <= i && i <= 3;
    {
        i = i + 1;
    }
    i
}
```

Save this as `annotated-loop.anl`. With Z3 5.3.3 installed as described in the
[verification guide](verification.md), run:

```sh
./target/release/anl check annotated-loop.anl
./target/release/anl eval annotated-loop.anl
./target/release/anl verify annotated-loop.anl
```

Checking succeeds, evaluation prints `3`, and verification returns `verified`
with exit 0 and solver trust. Ordinary compilation checks each clause's names
and Boolean type but does not prove or execute it. Even false or undefined
well-typed clauses are erased; `verify` separately checks their definedness and
truth. Names refer to locals visible before the condition
runs; annotation arithmetic uses mathematical integers. See the
[annotation specification](../spec/loop-verification.md#source-annotations-and-erasure)
for scope and syntax. The [bounded counter](../examples/contracts/count.anl) also
checks that its returned value equals its original input. Loop verification
proves partial correctness and arithmetic safety, not termination.

## Return several values

Flat tuples contain 1–8 scalar fields and use fixed, ordered types. A function
can return `(i64, i64)`; callers select fields with `.0` and `.1`:

```sh
./target/release/anl eval examples/tuples/count-sum.anl
./target/release/anl run examples/tuples/snapshots.anl
```

These print `55` and `42`. The first example updates a whole `(count, sum)` tuple
inside a loop. The second shows that a saved tuple and an earlier argument keep
their values when a later argument replaces the original binding. Construction
and arguments evaluate left to right; projection evaluates the whole base.
`(7, 1 / 0).0` therefore traps.

`(value,)` is a singleton tuple, `(value)` is grouping, and `()` is unit. Tuple
types also require a comma: `(i64,)` is distinct from `i64`. Tuple equality
requires identical shapes. Nested tuples, destructuring and field assignment
are unavailable. See the [tuple specification](../spec/flat-products.md) for
syntax, value semantics, limits and the v2 interchange format.

Tuple contracts use the same construction, projection and equality syntax. The
[contract examples](verification.md#verify-tuple-contracts) verify captured tuple
arguments and a count-and-sum loop with invariants.

## Use several source files

```sh
./target/release/anl check examples/modules/main.anl
./target/release/anl eval examples/modules/main.anl
./target/release/anl run examples/modules/main.anl
```

The three-file example evaluates to `42` in both execution modes. `mod math;`
loads a sibling `math.anl`; `pub fn` exposes a function, and `math::double(21)`
calls it. The complete import graph is checked, including unused bodies. The
[module guide](modules.md) explains nested namespaces, visibility, and paths.

## Verify a function contract

Install Z3 5.3.3 and put `z3` on `PATH` using the
[verification guide](verification.md), then run:

```sh
./target/release/anl verify examples/contracts/increment.anl
./target/release/anl verify examples/contracts/increment.anl --json
```

The example returns `verified` with `trust=smt-trusted` and exit 0. `--solver PATH`
selects an executable explicitly. `--timeout-ms N` sets the whole attempt's budget
after source checking; its default is 30000 milliseconds. The verifier checks every
loaded function, including unused functions, for defined and satisfiable
preconditions, checked-arithmetic safety, and each postcondition. Calls must form
an acyclic graph, and every loop must have at least one invariant. Recursion or
a missing loop invariant anywhere in the loaded graph reports `unsupported`,
even in imported or unused functions, skipped branches, conditions and arguments.
These rejections happen before solver discovery and create no obligations.
`let mut`, assignment and annotated while loops are supported, including changes made while
evaluating operands, conditions, and call arguments. Ordinary interpretation and
native compilation also support loops and recursion.

A mutable implementation can use the same contract:

```text
fn increment(value: i64) -> i64
    requires value < 9223372036854775807;
    ensures (answer) answer == value + 1;
{
    let mut next = value;
    next = next + 1;
    next
}
```

Save it as `mutable-increment.anl` and run
`./target/release/anl verify mutable-increment.anl`. It returns `verified` with
`trust=smt-trusted`. Verification accepts this library without a `main` function.

`requires` and `ensures` clauses use mathematical integers. Runtime expressions
still use checked `i64`. Ordinary `check`, `eval`, `build`, and `run` type-check and
erase clauses without proving or dynamically enforcing them; core export
also erases them. Verification reports bind source, tools, and queries to their
exact hashes. Refuting models are candidate inputs labeled `replayed: false`,
not confirmed executions. Pure programs retain `apl-verify-v0` reports. Programs
containing scalar local-state constructs use `apl-verify-v1` with verification
revision `apl-state-verify-v1` or `apl-loop-verify-v1`. A tuple in executable
code or any clause selects `anl-verify-v3` with revision
`anl-flat-products-verify-v1`, also with solver trust. The guide explains
failed, unknown, and error outcomes.

## Examples

These examples have explicit expected results. The conformance suite covers
the scalar examples; the tuple commands above exercise the new examples.

| File | Demonstrates | Result |
| --- | --- | ---: |
| [factorial.anl](../examples/factorial.anl) | Recursive arithmetic | 3628800 |
| [gcd.anl](../examples/gcd.anl) | Euclid's algorithm and remainder | 21 |
| [sum-primes.anl](../examples/sum-primes.anl) | Boolean helpers, short-circuiting, recursive traversal | 328 |
| [scopes.anl](../examples/scopes.anl) | Inner shadowing, old-environment initializers, discarded unit results | 78 |
| [modules/main.anl](../examples/modules/main.anl) | File namespaces and public functions | 42 |
| [contracts/increment.anl](../examples/contracts/increment.anl) | Preconditions and a result postcondition | 42 |
| [control-flow/sum.anl](../examples/control-flow/sum.anl) | Mutable accumulation in a while loop | 5050 |
| [control-flow/gcd.anl](../examples/control-flow/gcd.anl) | Iterative Euclid's algorithm | 21 |
| [tuples/count-sum.anl](../examples/tuples/count-sum.anl) | Multiple results and whole-tuple loop updates | 55 |
| [tuples/snapshots.anl](../examples/tuples/snapshots.anl) | Saved values and ordered argument capture | 42 |
| [contracts/tuple-snapshots.anl](../examples/contracts/tuple-snapshots.anl) | Contracts over captured tuple arguments and results | 42 |
| [contracts/count-sum.anl](../examples/contracts/count-sum.anl) | Tuple postconditions and loop invariants | 55 |

All signed operations are checked. Division truncates toward zero, so `-7 / 3`
is `-2` and `-7 % 3` is `-1`. Overflow and division by zero are explicit traps.
The minimum value is written `-9223372036854775808`; the positive magnitude
`9223372036854775808` is outside the language's integer range.

## Diagnostics and limits

| Exit | Meaning |
| ---: | --- |
| 0 | Successful checking, compilation, or execution |
| 1 | Invalid source or rejected core artifact |
| 2 | `arithmetic_overflow` or `division_by_zero` |
| 3 | A tool resource limit was reached |
| 4 | Invalid CLI invocation, missing file, or infrastructure error |
| 5 | Verification found a refuted property or unsatisfiable preconditions |
| 6 | Verification is unknown or exceeded its analysis/time limit |
| 7 | Verification is unsupported or no functions were requested |

Source diagnostics include a filename, line, and column. Imported-file errors
and interpreter traps use the actual file's retained source snapshot. Runtime
traps retain canonical trap tags. For a deliberately trapping example, run
`./target/release/anl eval benchmarks/cases/overflow.apl`.

`anl eval FILE --fuel N` accepts `N` from `0` through `1000000000`; the default is
`100000`. The interpreter charges one unit before each core expression evaluation.
Skipped branches and short-circuited operands cost nothing. Calls charge their
arguments and bodies normally, and discarded statements lower to lets. Evaluation
nesting is independently limited to 256 active expressions. A while constructor
is charged once; each repeated condition and body uses its normal expression
fuel. Iterations do not accumulate interpreter nesting depth. Native loops have
no interpreter fuel budget.

Programs containing tuples also bound cumulative tuple allocation work at
1,048,576 scalar fields and active environment/argument slots at 65,536.
V2 JSON output is capped at 1 MiB and C output at 64 MiB, while producing it;
output-limit failure exits 3 before publication or compiler launch. These are
checked tool limits, not heap-byte guarantees. Native execution does not inherit
the interpreter's tuple counters. See the [exact accounting](../spec/flat-products.md#checked-resource-limits).

The Lean v1 and v2 models instead count machine transitions. Finite values and
trap kinds can be compared across tools, but exhausted budgets are inconclusive;
equal fuel numbers do not mean equal available work. The separate
[v2 adapter and comparison instructions](../formal/README.md#v2-interchange-adapter)
cover tuples. Successful decoding by the Lean v2 reader is proved to yield a typed
model input. JSON-text interpretation, compiled execution and agreement with Rust
remain separate tested boundaries.

Each source file and JSON input is limited to 1 MiB, source tokens per file to
100000, and core expression depth to 128. Parsing has a separate 128-level
recursion bound. A module graph is limited to 128 files, 32 active files in an
import chain, and 8 MiB of total source. Reaching a resource limit is neither a
language trap nor proof of divergence. Exact protocols are in
[core-format.md](../spec/core-format.md) and [modules.md](../spec/modules.md).

## Check this checkout

The complete suite requires a host C11 compiler and Z3 5.3.3. Put `z3` on `PATH`,
or set `ANL_TEST_SOLVER` to its executable path (`APL_TEST_SOLVER` remains a
fallback).

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --locked
cargo test --locked --release
python3 -m unittest discover -s benchmarks -p 'test_*.py'
```

The black-box suite runs the actual CLI and generated executables against
independent expected values and trap kinds. It
covers source and interchange rejection, whole-program checking, arithmetic,
sequencing, scopes, recursion, short-circuiting, module visibility, source
protection, local-state sequencing, and bounded resource failures. Revision
`f8ffb5f128aab5eaed4db3770ae500cd923cc61c` passed
[Linux/macOS Rust and Lean CI](https://github.com/djsydney04/ANL/actions/runs/44059286145),
including local-state execution, proof checks, and evaluator comparisons. These
checks are development evidence, not installation or release qualification.

`anl dump-core FILE` exports checked source into the versioned JSON format, and
`anl eval-core FILE [--fuel N]` independently validates a core artifact and emits
a JSON outcome. Programs using only immutable constructors still export the
unchanged `apl-core-v0` revision `m1-2026-11-16`. In scalar programs, any local-state constructor,
including one in an unused function, selects `apl-core-v1` revision
`local-state-2026-11-17`. Tuple use anywhere instead selects `apl-core-v2`,
revision `flat-products-2026-11-17`. Scalar-only v2 inputs normalize to v0/v1
behavior. Each importer checks its own schema and revision.
A modular program exports as one resolved function table;
file boundaries and visibility are checked before export. Rust library users
choose `anl::compile_file(path)` for imports or pure `anl::compile(source)` for
in-memory source without imports. These tools expose the model boundary for
comparison; they do not prove source-to-core translation or module resolution
correct. See the [formal methods scope](architecture/formal-methods.md)
for the distinction between checked theorems, tested behavior, and remaining proof
obligations.

The [baseline instructions](../benchmarks/README.md) describe reproducible release
CLI and native measurements. The original [native macOS arm64 report](../benchmarks/results/native-macos-arm64.md)
and the separate [local-state report](../benchmarks/results/local-state-macos-arm64.md)
record measured build/execution results and their limits. They do not establish
a cross-run speedup or cross-language performance claim.
