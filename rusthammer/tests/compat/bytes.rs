// Standalone driver for tools/compare_bytes.py; not part of the library API.
#[allow(dead_code)]
#[path = "../../src/lib.rs"]
mod rusthammer;

use rusthammer::{Byte, BytePattern, Cursor, Parser};
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

fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let fields: Vec<_> = line.split_whitespace().collect();
        let bit = fields[1].parse().unwrap();
        let pattern = unhex(fields[2]);
        let input = unhex(fields[3]);
        let cursor = Cursor { byte: 0, bit };
        let result = if fields[0] == "byte" {
            Byte.parse(&input, cursor)
                .map(|(next, value)| (next, u32::from(value)))
        } else {
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
