// Standalone driver for tools/compare_primitives.py; not part of the library API.
#[allow(dead_code)]
#[path = "../../src/lib.rs"]
mod rusthammer;

use rusthammer::{
    BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Byte, ByteIn, ByteNotIn, BytePattern, Cursor,
    IntRange, ParseError, Parser, SignedBits, SkipBits, Tell, I8,
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
        let offset: usize = fields[1].parse().unwrap();
        let input = unhex(fields[3]);
        let cursor = Cursor {
            byte: offset / 8,
            bit: (offset % 8) as u8,
        };
        let result = if fields[0] == "skip" {
            SkipBits::new(fields[2].parse().unwrap())
                .parse(&input, cursor)
                .map(|(next, ())| (next, 0))
        } else if fields[0] == "tell" {
            Tell.parse(&input, cursor)
                .map(|(next, at)| (next, (at.byte * 8 + usize::from(at.bit)) as i128))
        } else if fields[0] == "byte" {
            widened(Byte, &input, cursor)
        } else if fields[0] == "in" || fields[0] == "not_in" {
            let bytes = unhex(fields[2]);
            if fields[0] == "in" {
                widened(ByteIn::new(&bytes), &input, cursor)
            } else {
                widened(ByteNotIn::new(&bytes), &input, cursor)
            }
        } else if fields[0] == "signed" {
            widened(
                SignedBits::new(fields[2].parse().unwrap()).unwrap(),
                &input,
                cursor,
            )
        } else if fields[0].starts_with("range_") {
            let setting: Vec<_> = fields[2].split(':').collect();
            macro_rules! range {
                ($parser:expr, $ty:ty) => {
                    widened(
                        IntRange::new(
                            $parser,
                            setting[1].parse::<$ty>().unwrap(),
                            setting[2].parse::<$ty>().unwrap(),
                        )
                        .unwrap(),
                        &input,
                        cursor,
                    )
                };
            }
            match (fields[0], setting[0]) {
                ("range_ch" | "range_uint", "8") => range!(Byte, u8),
                ("range_int", "8") => range!(I8, i8),
                ("range_uint", "16") => range!(BeU16, u16),
                ("range_int", "16") => range!(BeI16, i16),
                ("range_uint", "32") => range!(BeU32, u32),
                ("range_int", "32") => range!(BeI32, i32),
                ("range_uint", "64") => range!(BeU64, u64),
                ("range_int", "64") => range!(BeI64, i64),
                _ => panic!("unsupported range reader"),
            }
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
