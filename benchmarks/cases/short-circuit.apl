// A skipped recursive call must do no work. Expected result: 42.
fn forever() -> bool { forever() }
fn main() -> i64 {
    if true || forever() { 42 } else { 0 }
}
