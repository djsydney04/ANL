fn count_to(n: i64) -> i64
    requires 0 <= n && n <= 1000;
    ensures (answer) answer == n;
{
    let mut i = 0;
    while (i < n)
        invariant 0 <= i;
        invariant i <= n;
    {
        i = i + 1;
    }
    i
}

fn main() -> i64 {
    count_to(42)
}
