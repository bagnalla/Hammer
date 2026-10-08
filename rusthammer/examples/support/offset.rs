//! A relative byte pointer followed by a borrowed two-byte field.
#[cfg(rusthammer_verify)]
use crate as rusthammer;
use rusthammer::{
    bind, Byte, Cursor, ParseContext, ParseOutcome, Parser, Right, Seek, TakeAligned,
};

/// The first byte is a displacement from the end of that byte to a two-byte
/// payload. This is a prefix parser; skipped bytes and trailing bytes are allowed.
/// Borrowed output refers to the original input, including after a partial retry.
pub fn payload(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<&[u8]> {
    bind(Byte, |distance| Right {
        // A byte fits in isize; multiplying by eight is safe on every Rust target.
        first: Seek::relative(distance as isize * 8),
        second: TakeAligned { count: 2 },
    })
    .parse_with(input, cursor, context)
}
