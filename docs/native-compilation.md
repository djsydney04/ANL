# Native scalar compilation

APL can build the checked scalar language into a host machine-code executable
through a C11 compiler. Programs may use the [file module system](modules.md);
the checked graph lowers to one C11 translation unit. Separate-object compilation
and the remaining full-language requirements are pending. The backend and its
runtime helpers are tested, not formally verified.

Install a host C11 toolchain providing `cc`, then build the APL CLI with the pinned
Rust toolchain. `CC` can select another compiler executable. Its value is one
executable name or path; embedded options and shell commands are not interpreted.

```sh
cargo build --release --locked
./target/release/apl build examples/factorial.apl -o /tmp/apl-factorial
/tmp/apl-factorial
./target/release/apl run examples/factorial.apl
./target/release/apl emit-c examples/factorial.apl > /tmp/apl-factorial.c
cc -std=c11 -O0 /tmp/apl-factorial.c -o /tmp/apl-factorial-debug
```

`build FILE [-o PATH]` checks the complete source and requires `main() -> i64`.
It invokes the host compiler at `-O2`. Without `-o`, the output is beside the
source with its final extension removed, or with `.out` appended when it has no
extension. The explicit output directory must already exist. A successful build
replaces an existing output file. The root and every transitive source input,
including Unix hard-link and symbolic-link aliases, are rejected as outputs.
Compilation takes place in a private staging directory beside the output; a
successful link is published by rename.
Missing tools, compiler/linker failures, and publication failures exit 4. Failed
builds preserve existing output files and remove their staging directory.

`run FILE` builds in a temporary directory, executes the binary with inherited
standard streams, and removes the temporary files when the child exits. It
returns the child's status. A host signal termination is reported as an
infrastructure failure with status 4. Native recursion uses the host stack and
has no interpreter fuel or nesting limit. Host resource failure is outside the
scalar language semantics; it is not a language arithmetic trap or a proof of
divergence. Process termination or a machine crash can leave temporary files.

The native wrapper prints the complete signed `i64` result and a newline, then
exits 0. Arithmetic overflow and division by zero print `arithmetic_overflow` or
`division_by_zero` to stderr and exit 2. Output stream failures exit 4. The
wrapper's printing convention does not add a source-level I/O facility.

`emit-c FILE` writes a standalone C11 translation unit to stdout. This uses the
same checked lowering as `build`; it does not invoke a compiler. It permits
inspection and compilation at other optimization levels or with sanitizers.
`check`, `eval`, `dump-core`, and `eval-core` retain their existing contracts.

## Lowering and validation

The typed core lowers to structured MIR before C emission. Each function has an
ordered parameter list, a declared result, and a table of uniquely identified,
typed temporaries. Each block sequences instructions and ends in one `Yield`
terminator. A branch instruction contains two blocks and assigns its destination
from the selected block's yield. `&&` and `||` become branches. Function calls
refer to a complete signature table, allowing forward and mutual recursion.

The validator checks every function and both sides of every branch. Every use
must name an already-defined, visible temporary with the recorded type. Every
temporary has exactly one definition. Branch conditions are boolean, branch
results agree, calls match their parameter types and arity, function yields match
their result declarations, and the executable entry is nullary and returns
`i64`. A temporary defined inside a branch cannot escape except as its yield.
Residual short-circuit binary operations are rejected. Validation precedes C
emission, including for programs supplied through the Rust library API.

Arithmetic instructions have checked semantics, including their named traps.
The MIR contains no unchecked partial signed arithmetic instruction. In emitted
C, portable helpers check their preconditions before addition, subtraction,
multiplication, negation, division, or remainder. Both `MIN / -1` and `MIN % -1`
trap, as do zero divisors. Helpers use no compiler-specific overflow builtins.

Instruction order becomes C statement order. Calls and binary operations receive
previously computed scalar temporaries, so C's argument evaluation order cannot
change APL's first trap. Branch bodies remain conditional. Discarded expressions
still produce instructions and execute their traps. Internal symbols use numeric
IDs; source identifiers and source text are never inserted into C identifiers or
shell commands. The internal scalar ABI uses `int64_t`, `bool`, and an
`unsigned char` zero value for unit. It is not a stable foreign-function ABI.

## Evidence and limits

`cargo test --test native` executes actual generated binaries at `-O0` and
`-O2`, comparing independently specified values and traps with the reference
evaluator. Cases include signed limits, arithmetic sign combinations, first-trap
ordering, discarded traps, branch selection, scopes, unit and bool calls,
forward calls, and mutual recursion. CLI tests check machine-code file headers,
full-width results, output preservation, missing tool diagnostics, source-path
protection, and temporary cleanup. The suite runs emitted arithmetic cases under
the undefined-behavior sanitizer when the installed toolchain supports it; an
unavailable sanitizer is reported explicitly.

The native CI build, run, trap, and linking checks passed on macOS AArch64 and
Linux x86-64 at revision `ab8d495`; see the
[native CI run](https://github.com/djsydney04/ANL/actions/runs/44040702654).
That run predates the module increment. Module tests additionally exercise
multi-file interpretation, native execution at `-O0` and `-O2`, and protection of
transitive source inputs. These checks do not qualify an installable release or
prove compiler correctness, memory safety for future heap features, source-to-Lean
correspondence, or production performance. The C compiler, linker, scalar runtime,
host C library, and operating system remain trusted components. Source I/O, heap
allocation, ownership checking, concurrency, FFI, and APL optimizer transforms
remain unimplemented.
