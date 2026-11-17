# Owned i64 buffers

Semantic revision: `anl-owned-buffers-v1`. This revision adds initialized,
fixed-length `i64` storage and one call-scoped read or edit view. Ordinary scalar
and flat-tuple values remain copyable. It does not add resource-valued variables,
moves, resizing, subviews, raw pointers, explicit free, escaping references,
callbacks, globals, early return, recoverable exceptions, or heap contracts.

## Source syntax and permissions

```anl
fn seed(edit values: i64[], value: i64) -> unit {
    values[0] = value;
}
fn first(read values: i64[]) -> i64 {
    if values.length == 0 { 0 } else { values[0] }
}
fn main() -> i64 {
    heap values: i64[4] = 7 {
        seed(edit values, 42);
        first(read values)
    } else { -1 }
}
```

The optional view is the first and only resource parameter/argument. Ordinary
parameters and arguments follow it. `i64[]` is legal only in a view parameter;
it is not an ordinary value type. Owners and views cannot be returned, put in
tuples, copied into ordinary bindings, or assigned to mutable locals.

| Active resource | Length/read | Write | Lend read | Lend edit |
| --- | --- | --- | --- | --- |
| heap owner | yes | yes | yes | yes |
| read view | yes | no | yes | no |
| edit view | yes | yes | yes | yes |

A call's view spelling must match the callee's declared mode. A no-view callee
receives no caller resources. Functions may recurse; static checking does not
require an acyclic graph. All signatures are collected before every body is
checked, including unused functions and dead branches.

`heap` is contextual before `name : i64 [`. `read` and `edit` are contextual in
the first parameter/argument position. Ordinary functions and bindings may still
use those names where the view or heap form is absent. Parameter/argument lists
do not permit a trailing comma. Buffer indexing and `.length` require a bare
resource identifier, not a grouped expression, function result or module path.
They bind at postfix strength; `.length` is not general field selection.
Indexed writes are statements ending in `;` and produce unit internally. While
conditions still require parentheses, and a while block has no trailing `;`.
The complete productions are in [grammar.ebnf](grammar.ebnf).

Lookup uses the nearest binding in one source namespace. It never skips an
ordinary shadowing value to find an outer owner or function. Ordinary parameter
names and the view name must be distinct. An owner is introduced only around the
success block: length, initializer and failure see the incoming context. An outer
same-named binding remains visible there. Inner-block shadowing follows the
existing rules; a local in the success block may shadow the incoming owner name,
but cannot extend or cancel the owner's lifetime.

The executable entry has no ordinary parameters or view and returns `i64`.
`check` may check a library with no entry. Contracts and invariants can refer to
ordinary values, but cannot use resources, indexing, length, heaps or view calls.
Successful compilation erases ordinary contracts as before; it does not verify
them. Any checked memory-bearing graph is unsupported by `anl verify`, including
memory in an unused signature or dead expression. See [verification](../docs/verification.md).

## Heap evaluation and failure order

For `heap b: i64[length] = initial { success } else { failure }`:

1. Apply expression-entry depth/fuel checks and evaluate length once.
2. A negative result traps with `invalid_length`. Skip initializer, allocator and
   both branches.
3. Otherwise evaluate initializer once, including for zero or target-ineligible
   lengths. Preserve its completed effects. Its trap, resource stop or divergence
   takes precedence over allocation and either branch.
4. If the length exceeds the recorded profile's maximum, run failure without an
   owner, request, descriptor reservation or fill charge.
5. Zero length reserves one owner descriptor and enters success with a distinct
   empty identity. It requests no backing allocation or allocator response.
6. A positive eligible attempt checks the tool reservations described below,
   then consumes one allocator response. Refusal enters failure in the incoming
   context. Success provides exactly the requested number of initialized cells,
   all equal to the captured initializer, before entering the success block.
7. On normal success return, capture the ordinary result, close this owner, restore
   the incoming resource context, and return the result. Earlier effects on outer
   locals and other buffers remain. A failure branch has ordinary block cleanup.

Allocation refusal is an ordinary branch choice. It is distinct from a tool
limit, trace-recording failure, metadata allocation failure, process kill or other
host failure. Memory safety neither guarantees allocation success nor proves
trap freedom or termination.

## Access, argument capture and loans

`b.length` returns the captured nonnegative length. A read evaluates its index
once, checks `0 <= index < length`, and then loads. A write evaluates its index
once, performs the same signed guard, evaluates and captures the RHS, and then
stores. A failed guard traps with `index_out_of_bounds` and skips the RHS.
The target stays live and fixed-length throughout the RHS. A nested edit can
finish before the outer final store; a trapping RHS prevents that final store
without undoing earlier effects.

A call reserves its whole ordinary argument vector and pending view descriptor
before evaluating arguments. This reservation grants no permission. The selected
resource is resolved without effects; ordinary arguments are evaluated and
captured left to right; only then is the view granted and the caller suspended.
For example, `inspect(read b, { change(edit b); 7 })` permits the edit while
computing the argument, before the read loan starts. A failing argument never
grants the outer loan.

Only the executing frame can access its descriptors. Its input view and fresh
local owners denote distinct live resources. Suspended recursive callers can
retain descriptors for the same allocation. On normal return, revoke the callee
view before restoring caller access. A read loan prevents changes to its
allocation during that loan; it still permits allocating and editing a different
local owner.

Only normal completion promises lexical cleanup. Traps retain the mathematical
world and suspended state; native traps exit the process with status 2. There is
no unwind/free-on-trap or divergence cleanup promise. Interpreter host cleanup
does not invent semantic release events. A normally returning executable entry
has no live owners.

## Target profile and native ABI

The profile has exactly these fields; this is the common 64-bit host example:

```json
{"abi":"anl-buffer-c11-v1","char_bits":8,"i64_bytes":8,"i64_align":8,"size_bits":64,"ptrdiff_bits":64}
```

The ABI string, character width 8 and i64 size 8 are fixed. Alignment is one of
1, 2, 4, 8 or 16; size and pointer-difference widths are independently 32 or 64.
Using mathematical integers, the maximum cells are
`min(2^63-1, floor((2^size_bits-1)/8), floor((2^(ptrdiff_bits-1)-1)/8))`.
Alignment is an ABI constraint, not a different logical cell model.

Source evaluation/export selects the supported Rust host profile without invoking
a C tool. Imported v3 Core uses its recorded admissible profile. Native compilation
checks that profile against the selected C target using assertions in the generated
program and matching runtime header. Request/release symbols include ABI version 1
and key `c{char_bits}_i{i64_bytes}_a{i64_align}_s{size_bits}_d{ptrdiff_bits}`.
Signed checks precede narrowing, multiplication and pointer formation.

Buffer programs compile the generated program and hosted allocation runtime as
separate C11 objects at `-O2 -fno-lto`, followed by a separate link. The opaque
request/release boundary has no allocator, purity, non-null or `restrict`
attributes. Manual LTO/whole-program rebuilding is outside this guarantee. The
guarantee concerns ordered logical requests/releases, not exact physical malloc
counts or resident memory. This libc-backed bootstrap adapter is not an
ANL-authored OS memory manager or a freestanding runtime.

## Reference-tool resource policy

The abstract language has no numeric tool budget. Rust and the bounded formal
reference tool apply these resource checks before their semantic transitions:

| Limit | Policy |
| --- | --- |
| Expression/fill fuel | default 100000, accepted range 0–1000000000 |
| Expression depth | at most 256 active expression levels; checked before entry fuel |
| Active slots | at most 65536 logical value/argument/owner/view slots |
| Live buffer cells | at most 1048576, including pending reservations |
| Tuple fields | at most 1048576 cumulative constructed scalar fields |

Every entered expression consumes one unit. Skipped branches do not. Call entry
fuel is charged before a possible argument-vector reservation failure; the
entire vector and optional pending view slot are reserved before its first
argument. Let storage is reserved after its initializer, before the body. Unit
values and zero-length owner/view descriptors count as slots. Reserved arguments
are not charged again when passed to the callee.

After a positive eligible initializer, atomically check live cells, the owner
slot, and `n` fill fuel, in that order, before calling the abstract/backing
allocator or constructing cells. Refusal refunds cells and descriptor, but keeps
the attempted fill charge. Zero uses a descriptor but no fill; target rejection
uses neither. Normal releases reduce live cells/slots. Tuple construction charges
fields after its field expressions complete. Logical counts are not a bound on
every host allocation or continuation byte. Host bookkeeping unwind must not add
semantic closes to a stopped trace.

The formal reference runner also takes an independent administrative transition
budget. Its zero-budget cutoff retains the state without invoking allocation;
an administrative cutoff is incomplete evidence, not expression-fuel exhaustion.
Different Core/MIR machines need not take the same number of steps. The finite
simulation does not equate resource cutoffs or equal budgets.

## Core v3 interchange

The root has exactly `schema`, `semantic_revision`, `allocation_profile`,
`functions`, `entry`: schema `anl-core-v3`, revision `anl-owned-buffers-v1`.
Each function has `id`, `name`, `view`, `params`, `result`, `body`; view is null,
`"read"` or `"edit"`, and params contains only ordinary types. IDs equal table
positions; names are unique ASCII identifiers beginning with a letter or underscore,
followed by letters/digits/underscores, excluding the nine reserved words
`fn`, `let`, `if`, `else`, `true`, `false`, `i64`, `bool`, `unit`. All annotations and bodies are
checked independently. V2 ordinary type/term encodings remain available.

| Term tag | Additional fields beyond `tag`, `ty` |
| --- | --- |
| heap | site, length, initial, success, failure |
| buffer_length | resource |
| buffer_read | resource, index |
| buffer_write | resource, index, value |
| call_view | function, resource, mode, arguments |

Ordinary and resource indices are independent, newest-first stacks. Pushing one
does not shift the other. Heap sites are validated preorder numbers starting at
zero in each function, visiting the heap before length/initial/success/failure.
Trace identity is `(function ID, heap site)` plus a fresh execution ordinal; site
numbers are stable for this program, not across source edits. The owner exists
only in success. Mode, arity, visibility, declared annotations and entry are
checked across the entire table, including recursion and unused bodies.

Memory anywhere in the checked graph takes precedence over product/state/scalar
wire selection. Memory-free ordinary exports retain their earlier schemas. An
explicit memory-free v3 envelope is admitted under its declared memory revision,
but re-export can normalize it to an older schema. No memory expression-only
artifact schema is added.

Core bytes are capped at 1048576 and logical expression depth at 128. The formal
reader separately allows at most 1024 nested JSON containers. Rust `eval-core`
retains pinned serde_json's recursion budget of 128: it admits at most 127 nested
objects/arrays and rejects the 128th before logical checking. These are different
bounds; not every logically admissible/exported boundary shape round-trips through
that Rust parser. Capacity failures are resource outcomes, not invalid-typing
proofs. Both readers reject duplicate fields, including escaped equivalents,
extra/missing keys, malformed tags, invalid numeric representations and forged
annotations. See [MIR](memory-mir.md), [evidence protocols](memory-evidence.md),
and the [proof inventory](../formal/PROOFS.md#owned-buffers-and-coremir-correspondence).
