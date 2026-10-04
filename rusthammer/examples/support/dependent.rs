//! Small count-prefixed formats, shared by examples, native tests, and extraction.
#[cfg(rusthammer_verify)]
use crate as rusthammer;
use rusthammer::{Bind, Bits, Cursor, InputStatus, ParseOutcome, Parser, TakeAligned, TryMap};

#[cfg(feature = "alloc")]
extern crate alloc;

// `unwrap()` carries a Debug bound whose extracted formatting model adds
// assumptions even when construction succeeds. The explicit panic branch keeps
// that model out of the proofs; both call sites prove their constant width valid.
fn fixed_bits(width: u8) -> Bits {
    match Bits::new(width) {
        Ok(parser) => parser,
        Err(_) => panic!("invalid fixed example field width"),
    }
}

/// One unsigned byte containing an element count, limited to 64 by these formats.
#[derive(Clone, Copy)]
pub struct CountPrefix;

impl<'input> Parser<'input> for CountPrefix {
    type Output = usize;
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<usize> {
        TryMap {
            parser: fixed_bits(8),
            // The format limit also establishes representability on Rust targets.
            map: |count| {
                if count <= 64 {
                    Ok(count as usize)
                } else {
                    Err(())
                }
            },
        }
        .parse_with(input, cursor, status)
    }
}

/// Read the count, then return exactly that many aligned bytes, borrowing the input.
/// This parses a prefix; compose with `End` when the format forbids trailing bytes.
pub fn payload(input: &[u8], cursor: Cursor, status: InputStatus) -> ParseOutcome<&[u8]> {
    Bind {
        parser: CountPrefix,
        then: |count| TakeAligned { count },
    }
    .parse_with(input, cursor, status)
}

/// Read the count, then collect that many four-bit numbers in order.
#[cfg(feature = "alloc")]
pub fn fields(
    input: &[u8],
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<alloc::vec::Vec<u64>> {
    let element = fixed_bits(4);
    Bind {
        parser: CountPrefix,
        then: |count| rusthammer::Repeat::exact(element, count),
    }
    .parse_with(input, cursor, status)
}
