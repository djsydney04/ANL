fn divide(n: i64, d: i64) -> (i64, i64) { (n / d, n % d) }
fn main() -> i64 {
    let result = divide(85, 2);
    result.0 + result.1
}
