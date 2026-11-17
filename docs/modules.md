# Programs with modules

ANL source programs can span several files. Each file has its own namespace;
`pub` makes a function available to other files. The compiler checks the complete
import graph before interpreting or building the program.

## Run the example

From this checkout, build the CLI with the pinned Rust toolchain. Native commands
also require the host C11 compiler described in
[Native scalar compilation](native-compilation.md).

```sh
cargo build --release --locked
./target/release/anl check examples/modules/main.anl
./target/release/anl eval examples/modules/main.anl
./target/release/anl run examples/modules/main.anl
./target/release/anl build examples/modules/main.anl -o /tmp/anl-modules
/tmp/anl-modules
```

`check` succeeds without printing a result. `eval`, `run`, and the built binary
each print `42` followed by a newline and exit successfully.

The example has three sibling files:

| File | Contents |
| --- | --- |
| [main.anl](../examples/modules/main.anl) | Imports `math` and defines the executable entry |
| [math.anl](../examples/modules/math.anl) | Exposes `double` and the `constants` namespace; keeps `multiply` private |
| [constants.anl](../examples/modules/constants.anl) | Exposes `seed`, returning `21` |

The root file calls both a public function and a function in a public nested
namespace:

```text
mod math;

fn main() -> i64 {
    math::double(math::constants::seed())
}
```

`mod math;` loads `math.anl` beside the declaring file. In `math.anl`,
`pub mod constants;` loads its sibling `constants.anl` and permits callers to
continue through `math::constants`. Namespaces follow declarations; they do not
require matching directory trees. A declaration can appear before or after a
function that uses it.

## Choose an interface

Functions and module declarations are private by default. A file may call its
own private functions and access its own private module declarations.

```text
pub fn double(value: i64) -> i64 {
    multiply(value, 2)
}

fn multiply(left: i64, right: i64) -> i64 {
    left * right
}
```

Other files can call `math::double(21)`. Calling `math::multiply(21, 2)` is a
visibility error. If `math.anl` changes `pub mod constants;` to `mod constants;`,
`math::constants::seed()` becomes a visibility error as well; `math.anl` can
still use `constants::seed()` internally.

Function signatures are the interface: argument count, argument types, and result
types are checked across files. Imports do not bring functions into the local
namespace, so `double(21)` in the root requires a local `double` declaration.
Functions and modules cannot share a name in the same file. Two separate files
may declare functions with the same name.

Only the root file's nullary `fn main() -> i64` is the executable entry. An
imported function named `main` remains an ordinary function. `anl check` also
accepts a library with no root `main`. Unused imported functions are checked, so
an error in one still prevents execution or a native build.

`mod` and `pub` are contextual words. Existing identifiers such as `fn mod(pub:
i64) -> i64 { pub }` remain valid.

## Paths, failures, and limits

The root path as passed to `anl` or `compile_file` selects one extension family
before symlinks are resolved. An explicit `.apl` root retains legacy `.apl`
imports throughout its graph. A `.anl` root, or a root with another or no suffix,
uses `.anl` throughout. Both families can coexist: the loader selects only the
chosen suffix, with no fallback or mixed lookup. Renaming a root invocation from
`.apl` to `.anl` therefore requires migrating that graph's module filenames too.


Imports resolve from the canonical directory of the declaring source file. A
symbolic link therefore uses the target file's directory for its imports. Shared
dependencies reached through the same canonical path are loaded once. Different
canonical paths that are hard links to the same file are rejected as ambiguous:
the paths could give that file different relative dependencies.

An import cycle is rejected with a diagnostic identifying the cycle. Move shared
functions into a third module to remove the cycle. Missing files, duplicate
declarations, private access, and type errors also produce diagnostics. Static
errors and interpreter traps in imported files report that file's location;
related notes can point to a declaration in another file. Native arithmetic
traps retain the backend's trap-tag output.

Loading is bounded to 128 distinct source files, 32 active source files in an
import chain including the root, and 8 MiB of source across the graph. Each file
is limited to 1 MiB and 100000 tokens; qualified paths are limited to 32 segments,
including the final function name. Existing parser, expression, and
interpreter limits still apply. A resource-limit diagnostic is a tool failure,
not a language arithmetic trap.

Source, type, visibility, cycle, and ambiguous-identity errors exit 1. Resource
limits exit 3. Unreadable, missing, or nonregular source files are infrastructure
errors and exit 4.

Native `build` protects every loaded source file from being used as its output,
including transitive imports and their symbolic-link or Unix hard-link aliases.
The compiler performs no network requests or package search. Modules currently
provide no import aliases, glob imports, `super` or `crate` paths, cyclic imports,
or separate compilation interface.

## Library and core interfaces

Rust callers use `anl::compile_file(path)` to load a file and its imports.
`anl::compile(source)` remains a pure in-memory operation and reports an error
when the source declares a file import.

`dump-core` exports the checked graph as one function table. Tuple use in any
loaded signature or body selects the [v2 format](../spec/flat-products.md#version-selection-and-core-json);
scalar graphs retain v0/v1 selection.
Calls use numeric identities; generated names keep functions from different
files distinct. `emit-c` and native builds lower that resolved program to one
C11 translation unit. File boundaries and visibility are checked before these
steps. They are not represented in the scalar core JSON, and the existing
scalar model does not prove module resolution or source-to-core lowering.

The normative rules are in the [module specification](../spec/modules.md).
