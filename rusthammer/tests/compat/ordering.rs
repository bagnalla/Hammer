// Exercise the actual library using the same corpus and protocol as the scope probe.
#![allow(dead_code)]

#[allow(unused_imports)] // Crate-root re-exports are only partially used by this driver.
#[path = "../../src/lib.rs"]
mod rusthammer;
use rusthammer::*;
fn main() {
    use std::io::{self, BufRead, Write};
    fn order(flags: u8) -> ByteOrder {
        assert_ne!(flags & 2, 0, "v1 supports high-first bit traversal only");
        if flags & 1 != 0 {
            ByteOrder::Big
        } else {
            ByteOrder::Little
        }
    }
    fn failure<T>(outcome: Result<(Cursor, T), ParseError>) -> String {
        match outcome {
            Err(ParseError::UnexpectedEnd) => "E".into(),
            _ => panic!("unexpected differential-test outcome"),
        }
    }
    let mut out = io::BufWriter::new(io::stdout().lock());
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let words: Vec<_> = line.split_whitespace().collect();
        let input: Vec<u8> = if words[1] == "-" {
            Vec::new()
        } else {
            words[1]
                .as_bytes()
                .chunks_exact(2)
                .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
                .collect()
        };
        let args: Vec<usize> = words[2..].iter().map(|p| p.parse().unwrap()).collect();
        let result = match words[0] {
            "R" => {
                let cursor = Cursor {
                    byte: args[0],
                    bit: args[1] as u8,
                };
                let ctx = order(args[2] as u8);
                match Bits::new(args[3] as u8)
                    .unwrap()
                    .parse_with(&input, cursor, ctx)
                {
                    Ok((c, value)) => format!("1 {} {} {value}", c.byte, c.bit),
                    other => failure(other),
                }
            }
            "N" => {
                let ctx = order(args[0] as u8);
                let widths = [
                    args[3] as u8,
                    args[4] as u8,
                    args[5] as u8,
                    args[6] as u8,
                    args[7] as u8,
                ];
                match nested(
                    &input,
                    widths,
                    order(args[1] as u8),
                    order(args[2] as u8),
                    ctx,
                )
                .unwrap()
                {
                    Ok((end, (a, (b, (c, d)), e))) => {
                        let rank = 8 * end.byte + end.bit as usize;
                        format!("1 {rank} {a} {b} {c} {d} {e}")
                    }
                    other => failure(other),
                }
            }
            _ => panic!("unknown request"),
        };
        writeln!(out, "{result}").unwrap();
    }
}

fn field(width: u8) -> Bits {
    Bits::new(width).unwrap()
}
const START: Cursor = Cursor::start();
fn seq<P, Q>(first: P, second: Q) -> Seq<P, Q> {
    Seq { first, second }
}
fn nested(
    input: &[u8],
    widths: [u8; 5],
    outer: ByteOrder,
    inner: ByteOrder,
    context: ByteOrder,
) -> Option<Result<(Cursor, (u64, (u64, (u64, u64)), u64)), ParseError>> {
    let [a, b, c, d, e] = widths.map(field);
    let parser = seq(
        a,
        seq(
            WithByteOrder {
                byte_order: outer,
                parser: seq(
                    b,
                    seq(
                        WithByteOrder {
                            byte_order: inner,
                            parser: c,
                        },
                        d,
                    ),
                ),
            },
            e,
        ),
    );
    Some(match parser.parse_with(input, START, context) {
        Ok((next, (a, (middle, e)))) => Ok((next, (a, middle, e))),
        Err(error) => Err(error),
    })
}
