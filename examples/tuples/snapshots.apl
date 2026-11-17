fn encode(first: (i64, bool), second: (i64, bool)) -> i64 {
    if first.1 && second.1 { first.0 * 10 + second.0 } else { 0 }
}

fn main() -> i64 {
    let mut pair = (4, true);
    let saved = pair;
    let answer = encode(pair, { pair = (2, true); pair });
    if saved == (4, true) { answer } else { 0 }
}
