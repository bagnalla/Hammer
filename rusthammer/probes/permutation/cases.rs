//! Complete-input cases for the optional C Hammer compatibility check.
use rusthammer::{optional, permutation, required, BytePattern, Cursor, Parser};

trait Present {
    fn present(self, expected: &[u8]) -> bool;
}

impl Present for &[u8] {
    fn present(self, expected: &[u8]) -> bool {
        assert_eq!(self, expected);
        true
    }
}

impl Present for Option<&[u8]> {
    fn present(self, expected: &[u8]) -> bool {
        self.is_some_and(|value| value.present(expected))
    }
}

fn run<A: Present, B: Present, C: Present>(
    result: Result<(Cursor, (A, B, C)), rusthammer::ParseError>,
    patterns: [&[u8]; 3],
) -> (u8, usize, u8) {
    match result {
        Ok((next, (a, b, c))) => (
            1,
            next.byte * 8 + usize::from(next.bit),
            u8::from(a.present(patterns[0]))
                | u8::from(b.present(patterns[1])) << 1
                | u8::from(c.present(patterns[2])) << 2,
        ),
        Err(_) => (0, 0, 0),
    }
}

fn main() {
    let patterns: [&[u8]; 6] = [b"", b"a", b"b", b"aa", b"ab", b"ba"];
    for a in 0..6 {
        for b in 0..6 {
            for c in 0..6 {
                let expected = [patterns[a], patterns[b], patterns[c]];
                let p = BytePattern::new(expected[0]);
                let q = BytePattern::new(expected[1]);
                let r = BytePattern::new(expected[2]);
                for optional_mask in 0..8 {
                    for len in 0..=5 {
                        for mask in 0..(1 << len) {
                            for offset in [0usize, 3] {
                                let mut input = vec![0u8; (offset + len * 8).div_ceil(8)];
                                for i in 0..len {
                                    let byte = if mask & (1 << i) == 0 { b'a' } else { b'b' };
                                    for bit in 0..8 {
                                        let position = offset + i * 8 + bit;
                                        input[position / 8] |=
                                            ((byte >> (7 - bit)) & 1) << (7 - position % 8);
                                    }
                                }
                                let cursor = Cursor {
                                    byte: 0,
                                    bit: offset as u8,
                                };
                                macro_rules! check {
                                    ($a:expr, $b:expr, $c:expr) => {
                                        run(
                                            permutation(($a, $b, $c)).parse(&input, cursor),
                                            expected,
                                        )
                                    };
                                }
                                let result = match optional_mask {
                                    0 => check!(required(p), required(q), required(r)),
                                    1 => check!(optional(p), required(q), required(r)),
                                    2 => check!(required(p), optional(q), required(r)),
                                    3 => check!(optional(p), optional(q), required(r)),
                                    4 => check!(required(p), required(q), optional(r)),
                                    5 => check!(optional(p), required(q), optional(r)),
                                    6 => check!(required(p), optional(q), optional(r)),
                                    _ => check!(optional(p), optional(q), optional(r)),
                                };
                                println!(
                                    "{a} {b} {c} {optional_mask} {len} {mask} {offset} {} {} {}",
                                    result.0, result.1, result.2
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}
