# Unsigned words and explicit conversions

Use `u8`, `u16`, `u32` or `u64` when a value needs an exact unsigned width.
Write that width on a literal: `42u8`. Ordinary arithmetic checks the range;
wrapping arithmetic spells its choice explicitly: `255u8 +% 1u8` gives `0u8`,
while `255u8 + 1u8` traps with `arithmetic_overflow`.

## Pack two four-bit fields

```anl
fn pack(high: u8, low: u8) -> u8 {
    ((high & 15u8) << 4) | (low & 15u8)
}

fn split(value: u8) -> (u8, u8) {
    (value >> 4, value & 15u8)
}

fn main() -> i64 {
    let fields = split(42u8);
    cast i64(pack(fields.0, fields.1))
}
```

The [complete example](../../examples/words/packed-fields.anl) prints `42`:

```sh
./target/release/anl check examples/words/packed-fields.anl
./target/release/anl eval examples/words/packed-fields.anl
./target/release/anl run examples/words/packed-fields.anl
```

The mask `15u8` keeps four bits. Shift counts have type `i64`, so `<< 4` is
correct and `<< 4u8` is rejected. Shifts require a count from zero through seven
for `u8`; `<< 8` traps with `invalid_shift`. The tuple keeps its two exact word
field types. `cast i64(...)` converts the final value to the executable entry's
required return type. Packing an ordinary word does not create a byte buffer or
specify its layout in memory.

## Cross an i64 buffer boundary

[The counter example](../../examples/words/buffer-counter.anl) reads an `i64`
cell through a call-scoped view, checks that it fits `u8`, wraps its increment,
and converts it back before storing:

```anl
fn advance(read counters: i64[], amount: u8) -> u8 {
    cast u8(counters[0]) +% amount
}

fn main() -> i64 {
    heap counters: i64[1] = 255 {
        let next = advance(read counters, 43u8);
        counters[0] = cast i64(next);
        counters[0]
    } else {
        -1
    }
}
```

```sh
./target/release/anl check examples/words/buffer-counter.anl
./target/release/anl eval examples/words/buffer-counter.anl
./target/release/anl run examples/words/buffer-counter.anl
```

With successful allocation it prints `42`: `(255 + 43) mod 256 = 42`. Refusal
returns `-1`. Buffers still contain `i64`, and their lengths and indices remain
`i64`. The view lasts only for `advance`; the caller can write after the call
returns. A failing write index would trap before evaluating its conversion RHS.

Use `cast` to require that a mathematical integer fits. Use `truncate` to keep
its low bits: `truncate u8(-1)` produces `255u8`, whereas `cast u8(-1)` traps.
No conversion is implicit; `1u8 + 1` and `1u8 + 1u16` are type errors.

`check` establishes types and scope. `eval` runs the bounded interpreter; `run`
uses the hosted C backend. `verify` on either example returns unsupported with
exit 7 before starting external tools. Word-dependent contracts are not supported,
although ordinary word-free clauses may be checked and erased beside words.
The [word specification](../../spec/words.md) gives the complete operator and
failure rules; the [formal inventory](../../formal/PROOFS.md#unsigned-word-model)
records the separate proof and acceptance boundaries.
