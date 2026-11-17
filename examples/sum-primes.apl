// Sum the primes from 2 through 49. Expected result: 328.
fn has_divisor(n: i64, divisor: i64) -> bool {
    if divisor * divisor > n {
        false
    } else {
        n % divisor == 0 || has_divisor(n, divisor + 1)
    }
}

fn is_prime(n: i64) -> bool {
    n >= 2 && !has_divisor(n, 2)
}

fn sum_primes(n: i64) -> i64 {
    if n < 2 {
        0
    } else {
        let contribution = if is_prime(n) { n } else { 0 };
        contribution + sum_primes(n - 1)
    }
}

fn main() -> i64 {
    sum_primes(49)
}
