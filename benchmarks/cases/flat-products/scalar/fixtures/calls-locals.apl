// 10,000 calls, each with 16 parameters and 16 immutable locals.
// Sum alternating signed i for 0..9999 is -5000; fixed contribution is 256/call.
fn combine(a0: i64, a1: i64, a2: i64, a3: i64, a4: i64, a5: i64, a6: i64, a7: i64, a8: i64, a9: i64, a10: i64, a11: i64, a12: i64, a13: i64, a14: i64, a15: i64) -> i64 {
    let v0 = a0 + 1;
    let v1 = a1 + 2;
    let v2 = a2 + 3;
    let v3 = a3 + 4;
    let v4 = a4 + 5;
    let v5 = a5 + 6;
    let v6 = a6 + 7;
    let v7 = a7 + 8;
    let v8 = a8 + 9;
    let v9 = a9 + 10;
    let v10 = a10 + 11;
    let v11 = a11 + 12;
    let v12 = a12 + 13;
    let v13 = a13 + 14;
    let v14 = a14 + 15;
    let v15 = a15 + 16;
    v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12 + v13 + v14 + v15
}
fn main() -> i64 {
    let mut i = 0;
    let mut total = 0;
    while (i < 10000) {
        let base = if i % 2 == 0 { i } else { 0 - i };
        total = total + combine(base, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
        i = i + 1;
    }
    total
}
