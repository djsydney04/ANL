fn advance(p: (i64, i64)) -> (i64, i64) {
    (p.0 + 1, p.1 + 2)
}
fn identity(p: (i64, i64)) -> (i64, i64) { p }
fn main() -> i64 {
    let mut p = (0, 1);
    let mut i = 0;
    let mut checksum = 0;
    while (i < 200000) {
        let old = p;
        let mirror = identity(old);
        p = advance(p);
        if mirror == old && old.0 + 1 == p.0 {
            checksum = checksum + old.0;
        } else {
            checksum = -1000000000000;
        };
        i = i + 1;
    }
    p.0 + p.1 + checksum
}
