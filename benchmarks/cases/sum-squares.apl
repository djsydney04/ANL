// Arithmetic and linear recursive calls. Sum of squares 1..40 = 22140.
fn sum_squares(n: i64) -> i64 {
    if n == 0 { 0 } else { n * n + sum_squares(n - 1) }
}
fn main() -> i64 { sum_squares(40) }
