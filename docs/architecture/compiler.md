# Compiler architecture and integration contracts

Status: the Rust frontend, typed interpreter, file modules, strict core JSON
adapters, unsigned words, flat tuples, initialized local state and loops, validated structured MIR, C11 native
backend, scoped `i64` buffer owners/read-edit call views, and word-free scalar/flat-tuple
contract verification with loop invariants and acyclic calls are implemented.
General movable ownership, effects and language-server integration remain
planned. [Getting started](../getting-started.md) documents the working commands;
the [proof inventory](../../formal/PROOFS.md) covers the Lean expression and
recursive-function, local-state, flat-tuple and owned-buffer models. It does not
prove Rust implementation correctness.

## Pipeline

```mermaid
flowchart LR
    Source[ANL source] --> Parse[Lexer and parser]
    Parse --> AST[AST with source spans]
    AST --> Resolve[Names and modules]
    Resolve --> Core[Resolved typed core]
    Core --> Check[Ownership and effects]
    Core --> Ref[Reference evaluator]
    Core --> Formal[Lean model adapter]
    Check --> Verify[Contract verification]
    Check --> MIR[Explicit control flow and resources]
    MIR --> C[C11 native baseline]
    MIR --> LLVM[LLVM optimization backend]
    C --> Link[Object generation and linker]
    LLVM --> Link
    Link --> Native[Native executable]
```

M1 ends at typed core execution and formal comparison; the current M2 increment adds modules and native lowering. Scoped-buffer resource checks now enforce owner/read/edit modes and call lifetimes;
general moves, escaping borrows and effects remain extension points. Verifier results annotate obligations; ordinary compilation does not silently certify contracts. A strict verified build mode eventually requires a configured set of proved obligations.

The compiler is a Rust library called by the CLI, with language-server integration planned. The implementation toolchain is pinned to Rust 1.99.1. Each pass returns a result or structured diagnostics. No pass parses a preceding pass's displayed text.

## M1 caller contract

The initial program shape is `fn main() -> i64 { let x = 6 * 7; x }`. The parser accepts the [source grammar](../../spec/grammar.ebnf), [module declarations and paths](../../spec/modules.md), and typed [function contracts](../../spec/verification.md). The checker accepts `i64`, `u8`, `u16`, `u32`, `u64`, `bool`, unit, and flat tuples of 1–8 scalar fields, explicitly typed function parameters/results, immutable and initialized mutable lets with optional annotations, assignment, while statements, named recursive calls, conditionals, and scalar operators. The [local-state specification](../../spec/control-flow.md) defines permissions and state flow. The [flat-tuple specification](../../spec/flat-products.md) defines tuple behavior
and its contract-verification rules. Formal coverage follows the inventory
and does not automatically extend to a newly implemented form.

The CLI provides `anl check FILE` and `anl eval FILE` in M1. `check` resolves and checks every function, including unused functions, and accepts a typed library file without `main`. `eval` checks first, requires exactly one nullary `main` in the root file with result type `i64`, then displays its decimal result followed by a newline. The implemented `build`, `run`, and `emit-c` commands inherit that entry requirement. Internal expression evaluators may also return `bool`, unit and tuples; those are not executable entry types. Successful commands exit 0. Invalid source exits 1. Execution traps exit 2. Evaluation resource exhaustion exits 3 and is not reported as a language trap or divergence proof. CLI invocation or infrastructure errors exit 4.

An evaluation budget bounds interpreter work and call depth. The exact budget accounting is an implementation protocol recorded with tests, not language semantics. The implementation must fail with a diagnostic before exhausting the host stack. A native program is not required to reproduce the interpreter's artificial fuel budget.

## Representations and invariants

| Representation | Component and purpose | Required invariant | Validation |
| --- | --- | --- | --- |
| Tokens and AST | Frontend; preserve syntax and source locations | UTF-8 byte spans refer to the source file; tokens cannot reference outside it; malformed input cannot panic | Lexer/parser negative and recovery tests, fuzzing |
| Resolved core | Resolver; replace source names with function/local identities | Each reference is bound; functions have unique identities; parameter names are unique in their scope | Whole-program name validation |
| Typed core | Type checker; semantic input for evaluator and verifier | Every expression has a scalar or validated flat-tuple type; branch types agree; call arguments match; all operators meet operand rules | Independent core checker and rejection fixtures |
| MIR | Compiler; expose sequencing, branches, loops, typed value slots, guarded buffer operations, scoped owners and call views | Temporaries have single definitions; mutable slots are initialized, typed, and scope-local; loop condition/body yield bool/unit; one terminator per block; partial operations stay checked and sequenced | Structural validator, invalid-MIR tests, and evaluator/native comparison |
| Backend representation | Backend; implement MIR using C11 or LLVM | ABI/layout match target; no unchecked backend UB for safe core; source traps remain observable | Differential native execution and sanitizer tests |

No serialized representation is trusted merely because it declares itself typed. Imports revalidate tags, numeric ranges, binding indices, call signatures and inferred types. Stable IDs are internal compiler identities; source names remain available for diagnostics. Shared interfaces use owned data and IDs rather than cross-pass references whose lifetimes couple unrelated subsystems.

The current Rust boundaries are internal `syntax`, `modules`, `resolve`, and `mir`, plus `types`, `core`, `eval`, `diagnostic`, `codegen`, and `verify`. Checked Program contents are opaque to external mutation and construction; source compilation and core import establish their invariants. The verifier consumes retained typed contract metadata; core import does not recreate it.

Source loop annotations use separate head-local assertions and per-function
binding/loop metadata. Ordinary lowering erases these annotations. Verification
requires a clause on every loaded loop and checks initialization, preservation
and effectful exits using fresh abstract mutable heads.

`compile_file(path)` loads the bounded canonical file graph and checks all bodies.
`compile(source)` performs no filesystem reads and rejects file imports. Each file
has a private namespace with explicit public declarations; the [module rules](../../spec/modules.md)
define visibility, cycles, shared dependencies, and resource bounds. Spans identify
a source file and UTF-8 byte offsets. Private source snapshots retain imported-file
diagnostics and protect all source inputs from native output publication.

## Owned-buffer representation and evidence

The frontend adds contextual `heap`, `read` and `edit` syntax while preserving
ordinary value types. Checked memory nodes carry raw resource indices separately
from local indices. The program records `anl-owned-buffers-v1` and an explicit
allocation profile. Any memory form or view signature anywhere in the loaded graph
selects [Core v3](../../spec/owned-buffers.md#core-v3-interchange) unless the word
revision takes precedence, ahead of the
v0/v1/v2 routing rules. Import checks all functions, declarations, sites and entry.

The [memory MIR protocol](../../spec/memory-mir.md) exposes heap branches, index
guards, delayed write RHS blocks and already-captured call arguments. Static
resource IDs differ from Core stack indices. Its validator checks all instruction,
Temp, Slot and resource tables. The independent Lean pair checker validates both
artifacts and compares MIR with canonical lowering. The finite simulation proves
both completed directions under the same allocator responses and relates exact
world/capability state; it is not a proof of the Rust lowerer, source elaboration,
C backend or equal-budget exhaustion behavior.

Memory-bearing `verify` returns the explicit unsupported v4 report before solver
or C-tool discovery. Evidence tracing/replay is behind `memory-evidence`, with
bounded outputs and path protection; ordinary builds ignore those controls.
See the [evidence interface](../../spec/memory-evidence.md) for actual export,
pair-check and formal reference-runner commands.

## Cumulative word revision

The [word contract](../../spec/words.md) extends the existing Core/MIR pipeline.
Raw word literals carry a width and canonical unsigned payload; checking rejects
invalid combinations rather than silently reducing them. A dedicated conversion
node records checked/truncating mode, target and operand. Its input and output
may differ, and identity casts remain explicit through lowering and metering.

Revision, memory presence, profile metadata and active evidence are separate
properties. A whole loaded graph walk selects v4 for new types/nodes, including
unused/dead code; explicit v4 imports retain it. Every v4 graph has a profile,
but only memory-bearing graphs link the buffer runtime or activate evidence
controls. V4 selects the cumulative resource policy even with no memory forms.
Revision-specific decoder allowlists keep old schemas unchanged.

Specification conversion is fallible and rejects a referenced word-containing
runtime type before solver translation. Complete local/parameter arrays keep
original indices; word slots are not filtered out to construct a partial context.
After source checking, v4 routes to unsupported verification before all older
VCG paths and external tools. Rust source checking, generated C and native
execution remain separate from the [model proof scope](../../formal/PROOFS.md#unsigned-word-model).

## Rust host API compatibility

Flat products change `eval::Value` from `Copy` to `Clone`; `Value::ty(&self)`
borrows its receiver. `Type` remains `Copy`. The variants
`Type::Tuple(TupleShape)` and `Value::Tuple(TupleValue)` hold opaque validated
wrappers. Construct them with `TupleShape::new(&[ScalarType])` and
`TupleValue::new(&[ScalarValue])`, which return `Result<_, TupleError>` and
require 1–8 fields. The Rust `fields()` accessors expose immutable slices;
tuple-value clones may share immutable storage, and host callers can inspect
slice addresses. ANL source has no operation exposing pointer identity or
writable aliases.

Output functions now return typed errors:

```rust
core::export(&Program, usize) -> Result<serde_json::Value, bounded::OutputError>
codegen::emit_c(&Program, usize) -> Result<String, bounded::OutputError>
codegen::build(&Program, usize, &Path, &Path) -> Result<(), bounded::OutputError>
codegen::run(&Program, usize, &Path) -> Result<u8, bounded::OutputError>
```

These are API signatures, with the existing entry index and build path arguments.
Callers must handle `OutputError::ResourceLimit(&'static str)` separately from
`OutputError::Infrastructure(String)`. The CLI maps them to exits 3 and 4,
respectively, without classifying message text. `core::export` is now fallible;
callers must also replace implicit `Value` copies with deliberate clones or borrows.

## Core interchange with formal tools

Use versioned JSON: immutable programs retain `schema: "apl-core-v0"` with
`m1-2026-11-16`; any local-state constructor selects `apl-core-v1` with
`local-state-2026-11-17`. The separate expression formats follow the same v0/v1
split. Tuple use anywhere instead selects `apl-core-v2` or `apl-expr-v2` with
`flat-products-2026-11-17`. The [v2 contract](../../spec/flat-products.md#version-selection-and-core-json)
defines flat types, construction, projection and scalar-only v2 normalization.
Memory-bearing graphs instead select `anl-core-v3`/`anl-owned-buffers-v1` with
the profile, view and resource rules above; this highest-priority route has no
expression-only document.
V0 fields and semantics are unchanged. V1 adds `let_mut`, `assign`, and
`while`, and its importer checks target permissions, exact types, and loop-body
unit results. See the [state interchange rules](../../spec/control-flow.md#typed-core-and-interchange). Its semantic content is a function table and entry function ID. Each function contains its ID, printable name, ordered parameter types, result type, and body. Module graphs export as one function table with collision-free generated names; visibility and file boundaries are not represented in this interchange. Constructors have explicit tags: integer, boolean, unit, local, let, if, unary, binary, and call. The frozen member names, semantic revision `m1-2026-11-16`, expression fixture format, and fixtures are published in [core-format.md](../../spec/core-format.md). `anl dump-core FILE` exports checked source; `anl eval-core FILE` independently validates and evaluates the artifact.

Integer literals are decimal strings, avoiding host JSON precision loss. Local references use zero-based de Bruijn indices, with index 0 the most recently bound local. At function entry, the final declared parameter is index 0. A let initializer evaluates in the old environment, and its body evaluates with the new binding at index 0. Function IDs index the complete table, permitting forward and recursive calls. Spans and printable names are metadata and do not change semantics. Expression statements lower to discarded lets, with local indices adjusted to preserve binding and evaluation order. Expression-only proof fixtures use a separate expression fixture format; a program artifact's entry is always a function ID. New state in any checked scalar function, including an unused one, selects v1 for the whole export; tuple use takes precedence and selects v2 when the graph has no memory forms.

For the documented v0/v1 comparison, the Rust exporter and Lean importer are
trusted adapters until separately verified. The Lean side independently validates
those imported scalar programs. The separate `anl_formal_v2` executable validates
v2 artifacts and runs the flat-tuple model, with [independent executable
comparisons](../../formal/README.md#v2-interchange-adapter). The actual Lean v2
reader has a proved acceptance boundary: successful decoding yields a typed model
input, whose execution excludes invalid outcomes and preserves returned types
at every budget. JSON-text interpretation and compiled execution remain tested
trust boundaries. The runtime and reader proofs do not establish Rust/native
correspondence or tuple verification. Lean v2 uses transition budgets even for scalar-only v2 input;
resource limits are inconclusive rather than semantic disagreement. A malformed artifact returns `invalid_ir`, not a proved result. The comparison protocol records `value`, `trap`, or `resource_limit`; successful values include their type and canonical representation. Traps include `arithmetic_overflow` or `division_by_zero` and optional source metadata. A negative or exhausted budget is a tool condition.

This protocol does not prove that the parser faithfully represents source code. Source-level conformance fixtures and later refinement proofs cover that separate boundary. A proof about an expression subset must not be advertised as a proof about all imported function programs.

## Evaluation semantics that lowering preserves

Function arguments and non-short-circuit operands evaluate left to right. `&&` and `||` evaluate their second operand only when required. A conditional evaluates one branch. Lets evaluate once. Traps are observable, so constant folding cannot discard a trapping expression merely because its value is unused.

Signed `i64` arithmetic is checked in every build configuration. Overflow in addition, subtraction, multiplication, or unary negation traps. Division and remainder trap on zero and on `MIN / -1` or `MIN % -1`. Division truncates toward zero. No debug/release semantic switch exists. The type checker rejects arithmetic on booleans and mixed scalar equality. No implicit numeric conversion exists in M1.

The C11 backend emits one temporary per ordered subexpression as needed. It never relies on C argument evaluation order. Checked helpers test preconditions before performing signed operations. Builtins can be used only under an explicitly supported compiler contract; the portable helper path has its own tests. A trap calls a defined runtime handler before the invalid operation. Raw user identifiers never become unescaped C source or shell commands.

Mutable locals lower to initialized function-local slots, and reading a mutable
binding emits a load at that exact evaluation point. Scope exit preserves outer
slot updates and removes inner slots; slots never escape as arguments or yields.
A while lowers to a C11 loop that reexecutes its condition block before each test.
Each iteration creates fresh body slots. Separate statements preserve load/store,
argument, and trap order. The validator rejects uninitialized, mistyped, duplicate,
or out-of-scope slots before emission.

The planned LLVM backend must preserve the same checks and use overflow intrinsics or equivalent validated lowering. It cannot attach `nsw`, `nuw`, or other strengthening attributes without their preconditions. LLVM's [IR contracts](https://llvm.org/docs/LangRef.html) and [UB model](https://llvm.org/docs/UndefinedBehavior.html) are backend obligations, not ANL language semantics.

## Native interface and runtime boundary

Native and module build, execution, trap, and linking checks passed on macOS
AArch64 and Linux x86-64 at `19d726c` ([CI run](https://github.com/djsydney04/ANL/actions/runs/44043755444)).
Builds target the host; cross-compilation and qualified installation artifacts
remain pending.

Internal functions have fixed scalar or flat-tuple signatures. Unit has no meaningful payload. The native entry wrapper calls the required nullary ANL `main() -> i64`, prints its full decimal result followed by a newline, and returns status 0; it must not truncate the result into the operating system exit code. Arithmetic traps report their code on stderr and exit 2. M4 ordinary I/O programs use an explicitly specified entry ABI and do not inherit this evaluation-oriented display wrapper accidentally.

Foreign calls use an explicit C ABI declaration, target layout, and unsafe boundary until a safe wrapper establishes its preconditions. The compiler owns symbol mangling and ABI versioning. Heap resources and async tasks require a runtime ABI added with their language feature, not guessed from a C struct layout.

The linker driver receives structured arguments through a process API. It checks exit status, preserves diagnostics, and publishes an output artifact only after successful compilation and linking. Missing tools produce actionable diagnostics. Output paths cannot overwrite source inputs. M2 development builds may require a system C toolchain; the final end-user distribution must package or install the supported backend without requiring internal proof-development tools.

## Freestanding OS compilation (planned)

The current C11 output depends on the host C library for entry-wrapper output and
failure handling. It provides no freestanding entry or hardware intrinsics.
The [OS architecture](operating-system.md#hardware-operations-planned) requires
specified low-level types, layout, memory effects and target operations before
ANL OS code can use them. MIR validation and lowering must preserve privileged
effects, register clobbers, interrupt conventions and memory ordering; unsupported
target operations must be rejected explicitly.

A freestanding target must define its entry ABI, startup state, image sections,
linking and trap behavior without depending on hosted libc or an existing host
OS. Backend-generated instruction sequences may implement specified ANL
intrinsics, including interrupt entry/return. They must not embed handwritten OS
subsystems behind generated C or external helper calls. The
[authorship gate](../requirements.md#os-authorship-and-expressibility-gate)
applies to the full linked OS image, independently of the compiler's own
implementation language.

## Verification and optimization boundaries

`anl verify` consumes the complete checked source graph and its typed contracts.
For supported scalar and flat-tuple programs, it checks ordered precondition
definedness, satisfiability, runtime arithmetic
safety, callee preconditions, and postconditions. Calls inline the actual body;
recursive graphs are unsupported, and callee postconditions are never assumed.
Mutable locals and assignments pass symbolic state through operands, conditions,
scopes, and arguments. Annotated loops use invariant initialization/preservation
and a separate normal-return path. Missing invariants or recursion in any function
are rejected before tools, including unused bodies, skipped branches and arguments.
The [verification specification](../../spec/verification.md) defines the supported
fragment, bounds, and exact report schema.

Reports identify the checked program's executable revision. Scalar stateful programs
use schema `apl-verify-v1` and verification revision `apl-state-verify-v1` without
loops or `apl-loop-verify-v1` with loops, including preflight failures; pure
programs retain `apl-verify-v0`. Tuples in code or clauses select `anl-verify-v3`
with `anl-flat-products-verify-v1` and structured field metadata. A tuple used only
in a clause leaves the executable revision unchanged. Source-error
reports use null for the semantic revision when no checked program exists.
Reports bind retained source snapshots, compiler and solver identities, limits,
exact SMT commands, obligation locations, and per-obligation results. The driver
uses Z3 5.3.3 with a shared deadline and bounded protocol I/O. Only an aggregate
`verified` result succeeds, always labeled `smt-trusted`; candidate countermodels
are unreplayed. Reports are not imported or cached as proof input. Ordinary
compilation and core export erase contracts without dynamic checks or solver use.

Planned MIR transforms start with validated constant folding and dead-block removal; the current backend performs no ANL optimization passes. Each transform has a semantics statement and tests covering values, traps, and termination behavior within the tested scope. Later inlining, specialization, allocation elimination, loop transforms and layout optimization require explicit effect, alias and ownership conditions. A small transformation proof does not certify the backend.

Formal and native evaluators should not share arithmetic implementation code. Shared schemas are allowed; independent semantics are required to expose correlated mistakes. Differential testing compares terminating values and traps, and labels budget-limited cases inconclusive. Random testing supplements adversarial fixtures rather than replacing them.

## Executable milestone gates

M1 requires parser/checker rejection fixtures, ordinary and recursive execution, integer limits, left-to-right trap order, short-circuiting, shadowing and scope, malformed input diagnostics, and interpreter resource limits. Lean checks its declared theorems with no `sorry` or admitted project axioms. Coverage lists distinguish mechanized expression/function properties from tested source and backend correspondence. Documentation examples compile and execute.

Precedence fixtures reject `1 < 2 < 3` and `1 == 2 == false`, which repeat operators at the same non-associative grammar level. The mixed-precedence expression `1 < 2 == true` is accepted as `(1 < 2) == true`.

M2 additionally requires native binaries at optimization levels 0 and 2, matching results and traps against the interpreter and formal executable model where covered, multi-module linking, clean compiler-error handling, and sanitizer runs over emitted C and runtime helpers. Native success is demonstrated by execution of a machine-code binary, not generated text.

The production backend gate requires representative systems and numerical workloads, checked optimizer transformations, source debugging, target-matrix tests, reproducible build records, and measurements of time, memory, binary size and compile latency against pinned C/Rust baselines. No performance target is considered met by an external backend's reputation.
