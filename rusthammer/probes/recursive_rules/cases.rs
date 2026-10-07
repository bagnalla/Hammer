//! Emit a deterministic corpus for comparison with the C packrat interpreter.
use rusthammer_recursive_rules_probe::{parse, Answer, ParseContext};
fn main() {
    for mode in 0..8 {
        for length in 0..7 {
            for mask in 0..(1usize << length) {
                let input: Vec<u8> = (0..length)
                    .map(|bit| if mask & (1 << bit) == 0 { b'a' } else { b'x' })
                    .collect();
                let answer = parse(mode, &input, ParseContext::FINAL, 256, 100_000);
                let (success, consumed, count) = match answer {
                    Answer::Success(cursor, count) => {
                        (1, cursor.byte * 8 + usize::from(cursor.bit), count)
                    }
                    Answer::Error(_) => (0, 0, 0),
                    other => panic!("unexpected final outcome: {other:?}"),
                };
                println!("{mode} {length} {mask} {success} {consumed} {count}");
            }
        }
    }
}
