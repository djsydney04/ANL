fn count_sum(limit: i64) -> (i64, i64) {
    let mut totals = (0, 0);
    while (totals.0 < limit) {
        let next = totals.0 + 1;
        totals = (next, totals.1 + next);
    }
    totals
}

fn main() -> i64 {
    let result = count_sum(10);
    if result.0 == 10 { result.1 } else { 0 }
}
