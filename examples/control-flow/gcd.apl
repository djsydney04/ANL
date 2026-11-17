fn gcd(a: i64, b: i64) -> i64 {
    let mut a = a;
    let mut b = b;
    while (b != 0) {
        let remainder = a % b;
        a = b;
        b = remainder;
    }
    a
}

fn main() -> i64 { gcd(1071, 462) }
