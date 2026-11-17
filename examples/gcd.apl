// Euclid's algorithm. Expected result: 21.
fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn main() -> i64 {
    gcd(1071, 462)
}
