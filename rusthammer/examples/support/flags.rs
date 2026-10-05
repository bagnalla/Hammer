//! Example flags format, shared by runnable examples, native tests, and extraction.
#[cfg(rusthammer_verify)]
use crate as rusthammer;
use rusthammer::{Bit, Cursor, Map, ParseError, Parser, Seq};

/// A toy three-bit header used to exercise typed parser composition.
#[derive(Debug, PartialEq, Eq)]
pub struct Flags {
    pub urgent: bool,
    pub encrypted: bool,
    pub compressed: bool,
}

/// Parse a header prefix, preserving every unconsumed bit.
pub fn parse_flags(input: &[u8], cursor: Cursor) -> Result<(Cursor, Flags), ParseError> {
    let parser = Map {
        parser: Seq {
            first: Bit,
            second: Seq {
                first: Bit,
                second: Bit,
            },
        },
        map: |(urgent, (encrypted, compressed))| Flags {
            urgent,
            encrypted,
            compressed,
        },
    };
    parser.parse(input, cursor)
}
