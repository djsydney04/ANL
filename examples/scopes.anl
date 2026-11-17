// Nested bindings, discarded unit results, and restored scope. Expected: 78.
fn ignore(value: i64) -> unit {
    value;
}

fn main() -> i64 {
    let x = 7;
    let y = {
        let x = x + 1;
        ignore(x);
        x
    };
    ignore(y);
    x * 10 + y
}
