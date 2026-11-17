// One million Park-Miller updates. pow(48271, 1000000, 2147483647) = 1263606197.
fn park_miller(steps: i64) -> i64 {
    let mut x = 1;
    let mut i = 0;
    while (i < steps) {
        x = (x * 48271) % 2147483647;
        i = i + 1;
    }
    x
}

fn main() -> i64 { park_miller(1000000) }
