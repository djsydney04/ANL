# Scoped buffers and call-scoped views

A buffer stores a fixed number of `i64` cells. Its owner lives inside a `heap`
success block. A helper can read or edit that buffer during a call, but cannot
keep it or return it.

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
    } else {
        -1
    }
}
```

This is [the complete example](../../examples/buffers/basic.anl). With successful
allocation, evaluation prints `42`:

```sh
./target/release/anl check examples/buffers/basic.anl
./target/release/anl eval examples/buffers/basic.anl
./target/release/anl run examples/buffers/basic.anl
```

`heap values: i64[4] = 7` requests four cells and initializes every cell to `7`.
The success block owns `values`. `seed` takes an `edit` view and replaces its
first cell. `first` takes a `read` view and reads it. The success block returns an
ordinary integer; the buffer closes before that integer becomes the heap
expression's result. If a representable positive allocation is refused, the
`else` block returns `-1`.

A function may have one view, in its first parameter position. The call spells
the same mode: `seed(edit values, 42)` or `first(read values)`. An owner or edit
view may lend either mode; a read view may lend only another read view. All
ordinary arguments are evaluated before the view is granted. The caller's
capabilities are suspended during the call and restored after revocation.

`values` is a resource binding, not an ordinary value. You cannot put it in a
tuple, return it, assign it to another binding or save it for a later call.
`values.length` and `values[index]` use the resource's bare name. An indexed
write is a statement and needs its semicolon.

An index must be nonnegative and below the length. A failed write check traps
before evaluating the right-hand side. A negative heap length traps before its
initializer; a nonnegative length evaluates its initializer before target-size
rejection. Zero length still opens a scoped owner, but makes no allocator
request. A trap retains the execution trace prefix rather than pretending that
normal scope cleanup happened.

The interpreter bounds expression fuel, nesting, live slots/cells and cumulative
tuple fields. These tool limits are distinct from allocation refusal and native
memory availability. Native code uses a separate hosted C allocator runtime.
The ANL OS allocator and hardware operations remain future language/runtime work.

Use `check` for types and scope, `eval` for the reference behavior, and `run` for
hosted native execution. Heap-bearing `verify` currently exits 7 as unsupported;
it does not prove buffer contracts. The separate Lean model establishes the
scoped memory and canonical Core/MIR properties described in the
[proof inventory](../../formal/PROOFS.md#owned-buffers-and-coremir-correspondence).
The [buffer specification](../../spec/owned-buffers.md) gives the exact rules.
