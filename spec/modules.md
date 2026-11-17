# Source modules

This M2 source-language extension adds static file namespaces and visibility to
the [scalar grammar](grammar.ebnf). Scalar types, evaluation order, arithmetic,
and expression semantics are unchanged. The extension has no package registry,
dynamic loading, module initialization expressions, or runtime namespace values.

## Syntax

The following productions replace the scalar program and function productions,
and replace the identifier alternative in `primary`:

```ebnf
program         = { module | function } ;
module          = [ "pub" ], "mod", identifier, ";" ;
function        = [ "pub" ], "fn", identifier, "(", [ parameters ], ")",
                  "->", type, block ;
name_path       = identifier, { "::", identifier } ;
named_primary   = name_path, [ "(", [ arguments ], ")" ] ;
```

`mod` and `pub` are contextual words, recognized in declaration position. They
remain valid identifiers for functions, parameters, locals, and module names.
All other scalar lexical rules remain in effect. Modules are declared only at
file scope. There are no inline module bodies or explicit file-path strings.
Function paths used without a call are rejected because functions are not scalar
values. A namespace itself is not a value.

## Files and module identities

The explicitly supplied source file is the root module. In any file, `mod name;`
loads `name.apl` from the canonical parent directory of that declaring file. The
resolution rule does not depend on the process's working directory after the
root path is resolved. Import identifiers cannot express directory traversal.
Symlinks are resolved before determining a source file's dependency directory.

Each file is read and parsed independently. A module identity is assigned on its
first visit in deterministic declaration-order traversal. Later imports of the
same canonical file reuse the identity and its declarations, permitting shared
dependencies in an acyclic graph. Distinct canonical paths that identify the
same physical file through a Unix hard link are rejected as ambiguous module
identities. This avoids assigning different relative dependency directories to
one physical module.

An import that reaches an active ancestor is a cycle and is rejected with its
import chain. The loader never continues recursively around a cycle. Supporting
cycles later would require a specified interface-collection rule for strongly
connected components; this extension does not permit mutual recursion across
an import cycle. Local forward calls and mutual recursion remain supported.

No filesystem reads occur through `compile(&str)`. It accepts in-memory
declarations and expressions and rejects file imports with a diagnostic directing
the caller to `compile_file`. The latter explicitly loads the root and its graph.
The compiler does not search package paths or access the network.

## Names and visibility

Every module has one namespace for its function and module declarations.
Duplicate functions, duplicate module declarations, and a function and module
with the same name in one file are errors. Equal names in different files are
valid and designate different declarations.

An unqualified function call resolves only in the current file. Imports do not
implicitly add their functions to that namespace. Existing lexical rules apply
to local scalar bindings, including shadowing an unqualified function name and
rejecting a call to the resulting scalar.

For a qualified path `a::b::f` evaluated in module `M`:

1. Resolve `a` as a module declaration in `M`; it need not be public.
2. Resolve subsequent namespace components such as `b` in the preceding module.
   Each such module declaration must be public to continue through it.
3. Resolve `f` as a function in the final module. A function accessed from another
   file must be public.

A private function is callable from its own file. A private module declaration
is traversable from its declaring file. Visibility is checked at each boundary,
including an intermediate module in a longer path. `pub mod` exposes that
namespace edge; it does not make private functions or private nested modules
public. Qualified calls are resolved statically, without converting namespaces
or functions into first-class values.

The root module's `main` is the only candidate executable entry and must have
signature `fn main() -> i64`. Imported functions named `main` do not supply or
conflict with that entry. Library checking has no entry requirement. `pub` on
the root entry is optional.

## Checking and lowering

The compiler collects signatures throughout the complete loaded graph before
checking function bodies. Every body must type-check, including functions that
are private, unreachable, or never called. Calls must satisfy the scalar arity,
parameter, and result rules across file boundaries.

After namespace and visibility checking, calls refer to unique numeric function
identities. When the graph contains imports, generated ASCII names distinguish
all functions except the root entry, which retains `main`. The name mapping is
injective even when source identifiers resemble generated names. Names and
locations in source diagnostics refer to the original declarations.

The [core JSON format](core-format.md) and its scalar semantic revision are
unchanged. It contains the lowered function table and entry identity, with no
import paths, source snapshots, or visibility annotations. Importing such an
artifact validates scalar core invariants; it does not re-establish a source
module interface or prove namespace lowering correct. Native compilation lowers
the resolved graph to one C11 translation unit. This extension makes no separate
object-compilation or module-lowering proof claim.

## Diagnostics and resource bounds

Source spans contain a file identity and UTF-8 byte offsets within that file.
The checked program retains private source metadata for diagnostics and native
output protection. Static error locations, cross-file related notes, and
interpreter trap locations resolve through those source snapshots. Missing
metadata must not cause a diagnostic-rendering failure. Native trap output
continues to use the backend's canonical trap tags.

The loader returns the first diagnostic in deterministic traversal and checking
order. It reports unreadable files, invalid UTF-8, cycles, ambiguous identities,
duplicate declarations, unresolved paths, private access, and type errors.
Resource bounds limit work before host-stack or unbounded allocation failure:

| Resource | Limit |
| --- | ---: |
| Distinct loaded source files, including the root | 128 |
| Active source files in an import chain, including the root | 32 |
| Total source bytes across distinct loaded files | 8388608 |
| Source bytes per file | 1048576 |
| Tokens per file | 100000 |
| Qualified path segments, including the final function name | 32 |
| Parser nesting and expression depth | Existing scalar limit of 128 |
| Rendered diagnostic bytes | 8192, with a truncation marker when needed |

Source loading does not alter interpreter fuel or evaluation-depth accounting.
A resource-limit result is not a language trap or a proof of nontermination.
Syntax, type, visibility, cycle, and ambiguous-identity failures exit 1 through
the CLI; resource limits exit 3. Missing, unreadable, and nonregular source files
are infrastructure failures and exit 4.

Native output protection covers the root and every transitive source input. An
output path that identifies a source file, including a symbolic-link or Unix
hard-link alias, is rejected before publication. Rechecking after the external C
compiler returns preserves the existing publication contract.
