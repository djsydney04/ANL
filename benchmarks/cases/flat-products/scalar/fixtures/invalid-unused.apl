// Whole-program checking must reject even this unused function.
fn broken() -> i64 { true }
fn main() -> i64 { 42 }
