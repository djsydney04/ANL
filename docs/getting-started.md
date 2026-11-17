# Getting started with the scalar core

APL M1 provides a Rust command-line checker and reference interpreter for a small,
statically typed language. It supports checked `i64` arithmetic, booleans, unit,
immutable bindings, lexical blocks, conditionals, and named recursive functions.
It does not yet produce native executables or provide source-level I/O, mutable
state, collections, ownership, concurrency, or contracts. The complete language
remains tracked in the [roadmap](roadmap.md).

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
one `fn main() -> i64` with no parameters and checks every function first,
including unused functions.

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

## Examples

The conformance suite executes each of these files and checks its full result.

| File | Demonstrates | Result |
| --- | --- | ---: |
| [factorial.apl](../examples/factorial.apl) | Recursive arithmetic | 3628800 |
| [gcd.apl](../examples/gcd.apl) | Euclid's algorithm and remainder | 21 |
| [sum-primes.apl](../examples/sum-primes.apl) | Boolean helpers, short-circuiting, recursive traversal | 328 |
| [scopes.apl](../examples/scopes.apl) | Inner shadowing, old-environment initializers, discarded unit results | 78 |

All signed operations are checked. Division truncates toward zero, so `-7 / 3`
is `-2` and `-7 % 3` is `-1`. Overflow and division by zero are explicit traps.
The minimum value is written `-9223372036854775808`; the positive magnitude
`9223372036854775808` is outside the language's integer range.

## Diagnostics and limits

| Exit | Meaning |
| ---: | --- |
| 0 | Successful checking or evaluation |
| 1 | Invalid source or rejected core artifact |
| 2 | `arithmetic_overflow` or `division_by_zero` |
| 3 | A tool resource limit was reached |
| 4 | Invalid CLI invocation, missing file, or infrastructure error |

Source diagnostics include a filename, line, and column. Runtime traps retain
canonical trap tags. For a deliberately trapping example, run
`./target/release/apl eval benchmarks/cases/overflow.apl`.

`apl eval FILE --fuel N` accepts `N` from `0` through `1000000000`; the default is
`100000`. The interpreter charges one unit before each core expression evaluation.
Skipped branches and short-circuited operands cost nothing. Calls charge their
arguments and bodies normally, and discarded statements lower to lets. Evaluation
nesting is independently limited to 256 active expressions.

Source and JSON inputs are limited to 1 MiB, source tokens to 100000, and core
expression depth to 128. Parsing has a separate 128-level recursion bound.
Reaching a resource limit is neither a language trap nor proof of divergence.
The exact protocol is in [core-format.md](../spec/core-format.md).

## Check this checkout

```sh
cargo fmt --all --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
cargo test --locked --release --all-targets
python3 -m unittest discover -s benchmarks -p 'test_*.py'
```

The black-box suite runs the actual CLI and compares results with independent
expected values and trap kinds. It covers source and interchange rejection,
whole-program checking, arithmetic limits, sequencing, scopes, recursion,
short-circuiting, and bounded resource failures. CI defines Linux and macOS jobs;
a configured job alone does not establish a successful run on that platform.

`apl dump-core FILE` exports checked source into the versioned JSON format, and
`apl eval-core FILE [--fuel N]` independently validates a core artifact and emits
a JSON outcome. These tools expose the model boundary for comparison; they do not
prove source-to-core translation correct. See the [formal methods scope](architecture/formal-methods.md)
for the distinction between checked theorems, tested behavior, and remaining proof
obligations.

The [baseline instructions](../benchmarks/README.md) describe reproducible release
CLI measurements. They establish an initial measurement, without a speedup claim
or comparison with a native compiler.
