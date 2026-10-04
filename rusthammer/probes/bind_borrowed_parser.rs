//! Regression probe: a factory returns a parser containing a captured reference.
#![no_std]

#[path = "../src/lib.rs"]
mod rusthammer;
use rusthammer::{
    Bind, Bits, Cursor, InputStatus, ParseOutcome, Parser, Repeat, TakeAligned, TryMap,
};
extern crate alloc;

pub fn blocks(input: &[u8], status: InputStatus) -> ParseOutcome<alloc::vec::Vec<&[u8]>> {
    let element = TakeAligned { count: 1 };
    Bind {
        parser: TryMap {
            parser: Bits::new(8).unwrap(),
            map: |count| {
                if count <= 255 {
                    Ok(count as usize)
                } else {
                    Err(())
                }
            },
        },
        then: |count| Repeat::exact(&element, count),
    }
    .parse_with(input, Cursor::start(), status)
}
