fn advance(p: (i64, bool, unit, i64, bool, unit, i64, i64))
    -> (i64, bool, unit, i64, bool, unit, i64, i64) {
    (p.0 + 1, !p.1, (), p.3 + 2, !p.4, (), p.6 + 3, p.7 + 4)
}
fn main() -> i64 {
    let mut p = (0, true, (), 1, false, (), 2, 3);
    let mut i = 0;
    let mut correct_snapshots = 0;
    while (i < 100000) {
        let old = p;
        p = advance(p);
        if old.0 + 1 == p.0 && old.1 != p.1 && old.6 + 3 == p.6 {
            correct_snapshots = correct_snapshots + 1;
        } else {
            correct_snapshots = -1000000000000;
        };
        i = i + 1;
    }
    if p.1 && !p.4 && p.2 == () && p.5 == () {
        p.0 + p.3 + p.6 + p.7 + correct_snapshots
    } else { 0 }
}
