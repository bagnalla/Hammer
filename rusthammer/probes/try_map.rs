//! Exercise a captured, fallible callback through the actual library source.
#![no_std]

// Compile the library in this crate so Charon gets the same MIR stage as it
// does for the library's normal verification, rather than dependency MIR.
#[allow(dead_code, unused_attributes)]
#[path = "../src/lib.rs"]
mod rusthammer;

use rusthammer::{Bit, Cursor, InputStatus, ParseOutcome, Parser, TryMap};

pub struct Flag {
    pub value: bool,
}

pub fn checked_flag(input: &[u8], expected: bool, status: InputStatus) -> ParseOutcome<Flag> {
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
    parser.parse_with(input, Cursor::start(), status)
}
