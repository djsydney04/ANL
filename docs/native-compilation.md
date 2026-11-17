# Native compilation

ANL can build scalar values and flat tuples into a host machine-code executable
through a C11 compiler. Initialized mutable locals, whole-value assignment, and
structured `while` statements are supported. Programs may use the
[file module system](modules.md); the checked graph lowers to one C11 translation unit. Separate-object compilation
and the remaining full-language requirements are pending. The backend and its
runtime helpers are tested, not formally verified.

Install a host C11 toolchain providing `cc`, then build the ANL CLI with the pinned
Rust toolchain. `CC` can select another compiler executable. Its value is one
executable name or path; embedded options and shell commands are not interpreted.

```sh
cargo build --release --locked
./target/release/anl build examples/factorial.anl -o /tmp/anl-factorial
/tmp/anl-factorial
./target/release/anl run examples/factorial.anl
./target/release/anl emit-c examples/factorial.anl > /tmp/anl-factorial.c
cc -std=c11 -O0 /tmp/anl-factorial.c -o /tmp/anl-factorial-debug
```

`build FILE [-o PATH]` checks the complete source and requires `main() -> i64`.
It invokes the host compiler at `-O2`. Without `-o`, the output is beside the
source with its final extension removed, or with `.out` appended when it has no
extension. The explicit output directory must already exist. A successful build
replaces an existing output file. The root and every transitive source input,
including Unix hard-link and symbolic-link aliases, are rejected as outputs.
Compilation takes place in a private staging directory beside the output; a
successful link is published by rename.
V2 C output is limited to 67,108,864 UTF-8 bytes. Checked output exhaustion
exits 3 before invoking the compiler or publishing an artifact. Missing tools,
compiler/linker failures, and publication failures exit 4. Failed
builds preserve existing output files and remove their staging directory.

`run FILE` builds in a temporary directory, executes the binary with inherited
standard streams, and removes the temporary files when the child exits. It
returns the child's status. A host signal termination is reported as an
infrastructure failure with status 4. Native recursion uses the host stack and
has no interpreter fuel or nesting limit. A `while` loop uses constant host
stack space with respect to its iteration count and has no native fuel limit.
Host resource failure is outside the scalar language semantics; it is not a language arithmetic trap or a proof of
divergence. Process termination or a machine crash can leave temporary files.

The native wrapper prints the complete signed `i64` result and a newline, then
exits 0. Arithmetic overflow and division by zero print `arithmetic_overflow` or
`division_by_zero` to stderr and exit 2. Output stream failures exit 4. The
wrapper's printing convention does not add a source-level I/O facility.

`emit-c FILE` writes a standalone C11 translation unit to stdout. This uses the
same checked lowering and output bound as `build`; it does not invoke a compiler
and publishes no stdout prefix on output-limit failure. It permits
inspection and compilation at other optimization levels or with sanitizers.
`check`, `eval`, `dump-core`, and `eval-core` retain their existing contracts.

## Lowering and validation

The typed core lowers to structured MIR before C emission. Each function has an
ordered parameter list, a declared result, and a table of uniquely identified,
typed temporaries. Each block sequences instructions and ends in one `Yield`
terminator. A branch instruction contains two blocks and assigns its destination
from the selected block's yield. `&&` and `||` become branches. Function calls
refer to a complete signature table, allowing forward and mutual recursion.
Mutable locals use separate typed slots. `MutableScope` initializes one slot,
executes its lexical body, and copies the result to a temporary. Each mutable
read emits `Load`; assignment evaluates its right-hand side before `Store`.
`While` contains a Boolean condition block and a unit body block. The condition
runs before every iteration, including the final false test.

The validator checks every function and both sides of every branch. Every use
must name an already-defined, visible temporary with the recorded type. Every
temporary has exactly one definition. Branch conditions are boolean, branch
results agree, calls match their parameter types and arity, function yields match
their result declarations, and the executable entry is nullary and returns
`i64`. A temporary defined inside a branch cannot escape except as its yield.
Residual short-circuit binary operations are rejected. Validation precedes C
emission, including for programs supplied through the Rust library API.

Every slot has one unique, in-range definition and a matching initializer type.
Loads and stores must use a visible slot with the recorded type. A slot is visible
only within its `MutableScope` body; no address or slot can be passed or yielded.
Condition and body temporaries and slots cannot escape their blocks or cross the
loop back edge. Each iteration initializes its body-local slots afresh.

Arithmetic instructions have checked semantics, including their named traps.
The MIR contains no unchecked partial signed arithmetic instruction. In emitted
C, portable helpers check their preconditions before addition, subtraction,
multiplication, negation, division, or remainder. Both `MIN / -1` and `MIN % -1`
trap, as do zero divisors. Helpers use no compiler-specific overflow builtins.

Instruction order becomes C statement order. Calls and binary operations receive
previously computed value temporaries, so C's argument evaluation order cannot
change ANL's first trap. Mutable reads are value snapshots, so later argument
mutations cannot change earlier argument values. A callee receives value copies
and cannot mutate caller slots. Mutable scopes emit lexical C blocks; loops emit
actual C loops with the condition computation inside the loop. Loads and stores
are separate sequenced statements. Branch bodies remain conditional. Discarded
expressions still produce instructions and execute their traps. Internal symbols use numeric
IDs; source identifiers and source text are never inserted into C identifiers or
shell commands. The internal scalar ABI uses `int64_t`, `bool`, and an
`unsigned char` zero value for unit. It is not a stable foreign-function ABI.

Flat tuples lower to one ordinary C struct typedef per used shape, emitted in
deterministic order before function prototypes. Construction evaluates all fields
into initialized temporaries, with unit fields set to zero; projection uses a named member of its completed
base. Equality evaluates both operands before comparing fields, including unit.
Copies use ordinary struct assignment, with no `memcmp`, packed layout or
uninitialized-padding dependency. Tuple operations add no generated heap
allocation and establish no stable foreign ABI. The interpreter's tuple-allocation
and slot budgets do not become native runtime limits. See the
[tuple rules](../spec/flat-products.md).

## Evidence and limits

`cargo test --test native` executes actual generated binaries at `-O0` and
`-O2`, comparing independently specified values and traps with the reference
evaluator. Cases include signed limits, arithmetic sign combinations, first-trap
ordering, discarded traps, branch selection, scopes, unit and bool calls,
forward calls, mutual recursion, lexical mutation, snapshot reads, ordered
argument effects, isolated callee state, fresh loop locals, effectful conditions,
short-circuit effects, nested loops, and a 300000-iteration loop. State cases also
round-trip through the strict v1 importer. Forged MIR tests reject invalid slot
initialization, types, scope, and loop-block yields. CLI tests check machine-code
file headers, full-width results, output preservation, missing tool diagnostics, source-path
protection, and temporary cleanup. The suite runs emitted arithmetic cases under
the undefined-behavior sanitizer when the installed toolchain supports it; an
unavailable sanitizer is reported explicitly.

The native and module checks passed on macOS AArch64 and Linux x86-64 at revision
`19d726c`; see the [CI run](https://github.com/djsydney04/ANL/actions/runs/44043755444).
Module tests exercise multi-file interpretation, native execution at `-O0` and
`-O2`, and protection of transitive source inputs. These checks do not qualify an
installable release or prove compiler correctness, memory safety for future heap
features, source-to-Lean
correspondence, or production performance. The C compiler, linker, scalar runtime,
host C library, and operating system remain trusted components. Source I/O, heap
allocation, ownership checking, concurrency, FFI, and ANL optimizer transforms
remain unimplemented.
