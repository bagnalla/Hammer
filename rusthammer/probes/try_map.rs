//! Exercise a captured, fallible callback through the actual library source.
#![no_std]

// Retain a same-crate comparison. The cross_crate fixture separately checks
// the library as an ordinary Cargo dependency at the later MIR stage.
#[allow(dead_code, unused_attributes)]
#[path = "../src/lib.rs"]
mod rusthammer;

use rusthammer::{Bit, Cursor, ParseContext, ParseOutcome, Parser, TryMap};

pub struct Flag {
    pub value: bool,
}

pub fn checked_flag(input: &[u8], expected: bool, context: ParseContext) -> ParseOutcome<Flag> {
    let parser = TryMap {
        parser: Bit,
        map: |value| {
            if value == expected {
                Ok(Flag { value })
            } else {
                Err(())
            }
        },
    };
    parser.parse_with(input, Cursor::start(), context)
}
