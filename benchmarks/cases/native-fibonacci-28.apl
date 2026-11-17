// Branching recursion. Fibonacci(28) = 317811.
fn fibonacci(n: i64) -> i64 {
    if n < 2 { n } else { fibonacci(n - 1) + fibonacci(n - 2) }
}
fn main() -> i64 { fibonacci(28) }
