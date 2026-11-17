fn increment(value: i64) -> i64
    requires value < 9223372036854775807;
    ensures (answer) answer == value + 1;
{
    value + 1
}

fn main() -> i64
    ensures (answer) answer == 42;
{
    increment(41)
}
