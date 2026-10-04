// Standalone driver for tools/compare_primitives.py; not part of the library API.
#[allow(dead_code)]
#[path = "../../src/lib.rs"]
mod rusthammer;

use rusthammer::{
    BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Byte, BytePattern, Cursor, ParseError, Parser,
    SignedBits, I8,
};
use std::io::{self, BufRead};

fn unhex(text: &str) -> Vec<u8> {
    if text == "-" {
        return Vec::new();
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
        .collect()
}

fn widened<'input, P>(
    parser: P,
    input: &'input [u8],
    cursor: Cursor,
) -> Result<(Cursor, i128), ParseError>
where
    P: Parser<'input>,
    P::Output: Into<i128>,
{
    parser
        .parse(input, cursor)
        .map(|(next, value)| (next, value.into()))
}

fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let fields: Vec<_> = line.split_whitespace().collect();
        let bit = fields[1].parse().unwrap();
        let input = unhex(fields[3]);
        let cursor = Cursor { byte: 0, bit };
        let result = if fields[0] == "byte" {
            widened(Byte, &input, cursor)
        } else if fields[0] == "signed" {
            widened(
                SignedBits::new(fields[2].parse().unwrap()).unwrap(),
                &input,
                cursor,
            )
        } else if fields[0] == "uint" || fields[0] == "int" {
            match (fields[0], fields[2]) {
                ("uint", "8") => widened(Byte, &input, cursor),
                ("int", "8") => widened(I8, &input, cursor),
                ("uint", "16") => widened(BeU16, &input, cursor),
                ("int", "16") => widened(BeI16, &input, cursor),
                ("uint", "32") => widened(BeU32, &input, cursor),
                ("int", "32") => widened(BeI32, &input, cursor),
                ("uint", "64") => widened(BeU64, &input, cursor),
                ("int", "64") => widened(BeI64, &input, cursor),
                _ => panic!("unsupported integer reader"),
            }
        } else {
            let pattern = unhex(fields[2]);
            BytePattern::new(&pattern)
                .parse(&input, cursor)
                .map(|(next, matched)| {
                    assert!(core::ptr::eq(matched, &pattern[..]));
                    (next, 0)
                })
        };
        match result {
            Ok((next, value)) => println!("{} {value}", 8 * next.byte + usize::from(next.bit)),
            Err(_) => println!("error"),
        }
    }
}
