# Getting started with APL

APL provides a Rust command-line checker, reference interpreter, and native
compiler for a small, statically typed language. It supports checked `i64`
arithmetic, booleans, unit, immutable and initialized mutable bindings, assignment,
while loops, lexical blocks, conditionals, recursive functions, and file modules.
An optional verifier checks arithmetic safety and contracts for loop-free scalar
functions with mutable locals and acyclic calls. Collections, ownership, source-level
I/O, concurrency, and loop/recursive verification remain in the [roadmap](roadmap.md).

## Build and run

Install Rust through rustup, then run these commands from this checkout. The
checked-in toolchain file selects Rust 1.99.1, including rustfmt and Clippy.

```sh
cargo build --release --locked
./target/release/apl --version
./target/release/apl check examples/factorial.apl
./target/release/apl eval examples/factorial.apl
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

Save it as `answer.apl` and run `./target/release/apl eval answer.apl` to print `42`.
The final expression has no semicolon. A block with no final expression returns
`unit`, whose literal is `()`. Arithmetic and function arguments are statically
checked; there are no implicit type conversions.

## Build a native executable

Install a host C11 compiler providing `cc`, then run:

```sh
./target/release/apl build examples/factorial.apl -o /tmp/apl-factorial
/tmp/apl-factorial
./target/release/apl run examples/factorial.apl
```

Both executions print `3628800`. `build` publishes an executable at the requested
path; `run` builds and runs a temporary executable. `CC` may select a compiler
executable. See [native compilation](native-compilation.md) for output paths,
traps, tool failures, and emitted C. Native execution uses the host stack without
the interpreter's artificial fuel and nesting budgets.

## Update locals in a loop

Use `let mut` for an initialized scalar whose value may change. Parameters and
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
./target/release/apl eval examples/control-flow/sum.apl
./target/release/apl run examples/control-flow/sum.apl
./target/release/apl eval examples/control-flow/gcd.apl
```

The first two commands print `5050`; the last prints `21`. Inner scopes preserve
updates to outer locals, and each loop iteration creates fresh body locals.
Calls copy scalar arguments into a fresh frame, so callee-local updates cannot
change caller variables. This introduces no references or shared cells. See the
[local-state specification](../spec/control-flow.md) for exact evaluation order,
typing, and limits. `break`, `continue`, early `return`, and `for` are not supported.

## Use several source files

```sh
./target/release/apl check examples/modules/main.apl
./target/release/apl eval examples/modules/main.apl
./target/release/apl run examples/modules/main.apl
```

The three-file example evaluates to `42` in both execution modes. `mod math;`
loads a sibling `math.apl`; `pub fn` exposes a function, and `math::double(21)`
calls it. The complete import graph is checked, including unused bodies. The
[module guide](modules.md) explains nested namespaces, visibility, and paths.

## Verify a function contract

Install Z3 5.3.3 and put `z3` on `PATH` using the
[verification guide](verification.md), then run:

```sh
./target/release/apl verify examples/contracts/increment.apl
./target/release/apl verify examples/contracts/increment.apl --json
```

The example returns `verified` with `trust=smt-trusted` and exit 0. `--solver PATH`
selects an executable explicitly. `--timeout-ms N` sets the whole attempt's budget
after source checking; its default is 30000 milliseconds. The verifier checks every
loaded function, including unused functions, for defined and satisfiable
preconditions, checked-arithmetic safety, and each postcondition. Calls must form
an acyclic graph. Recursion or `while` anywhere in the
loaded graph report `unsupported`, even in unused functions or skipped branches.
This rejection happens before solver discovery and creates no obligations.
Loop-free `let mut` and assignment are supported, including changes made while
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

Save it as `mutable-increment.apl` and run
`./target/release/apl verify mutable-increment.apl`. It returns `verified` with
`trust=smt-trusted`. Verification accepts this library without a `main` function.

`requires` and `ensures` clauses use mathematical integers. Runtime expressions
still use checked `i64`. Ordinary `check`, `eval`, `build`, and `run` type-check and
erase clauses without proving or dynamically enforcing them; scalar core export
also erases them. Verification reports bind source, tools, and queries to their
exact hashes. Refuting models are candidate inputs labeled `replayed: false`,
not confirmed executions. Pure programs retain `apl-verify-v0` reports. Programs
containing local-state constructs use `apl-verify-v1` with verification revision
`apl-state-verify-v1`, including unsupported stateful programs. The guide explains
failed, unknown, and error outcomes.

## Examples

The conformance suite executes each of these files and checks its full result.

| File | Demonstrates | Result |
| --- | --- | ---: |
| [factorial.apl](../examples/factorial.apl) | Recursive arithmetic | 3628800 |
| [gcd.apl](../examples/gcd.apl) | Euclid's algorithm and remainder | 21 |
| [sum-primes.apl](../examples/sum-primes.apl) | Boolean helpers, short-circuiting, recursive traversal | 328 |
| [scopes.apl](../examples/scopes.apl) | Inner shadowing, old-environment initializers, discarded unit results | 78 |
| [modules/main.apl](../examples/modules/main.apl) | File namespaces and public functions | 42 |
| [contracts/increment.apl](../examples/contracts/increment.apl) | Preconditions and a result postcondition | 42 |
| [control-flow/sum.apl](../examples/control-flow/sum.apl) | Mutable accumulation in a while loop | 5050 |
| [control-flow/gcd.apl](../examples/control-flow/gcd.apl) | Iterative Euclid's algorithm | 21 |

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
`./target/release/apl eval benchmarks/cases/overflow.apl`.

`apl eval FILE --fuel N` accepts `N` from `0` through `1000000000`; the default is
`100000`. The interpreter charges one unit before each core expression evaluation.
Skipped branches and short-circuited operands cost nothing. Calls charge their
arguments and bodies normally, and discarded statements lower to lets. Evaluation
nesting is independently limited to 256 active expressions. A while constructor
is charged once; each repeated condition and body uses its normal expression
fuel. Iterations do not accumulate interpreter nesting depth. Native loops have
no interpreter fuel budget.

The Lean v1 model instead counts machine transitions. Finite values and trap kinds
can be compared across tools, but exhausted budgets are inconclusive; equal fuel
numbers do not mean equal available work.

Each source file and JSON input is limited to 1 MiB, source tokens per file to
100000, and core expression depth to 128. Parsing has a separate 128-level
recursion bound. A module graph is limited to 128 files, 32 active files in an
import chain, and 8 MiB of total source. Reaching a resource limit is neither a
language trap nor proof of divergence. Exact protocols are in
[core-format.md](../spec/core-format.md) and [modules.md](../spec/modules.md).

## Check this checkout

The complete suite requires a host C11 compiler and Z3 5.3.3. Put `z3` on `PATH`,
or set `APL_TEST_SOLVER` to its executable path.

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

`apl dump-core FILE` exports checked source into the versioned JSON format, and
`apl eval-core FILE [--fuel N]` independently validates a core artifact and emits
a JSON outcome. Programs using only immutable constructors still export the
unchanged `apl-core-v0` revision `m1-2026-11-16`. Any local-state constructor,
including one in an unused function, selects `apl-core-v1` revision
`local-state-2026-11-17`. Each importer checks its own schema and revision.
A modular program exports as one resolved scalar function table;
file boundaries and visibility are checked before export. Rust library users
choose `apl::compile_file(path)` for imports or pure `apl::compile(source)` for
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
