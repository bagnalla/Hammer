//! Example record format, shared by runnable examples, native tests, and extraction.
#[cfg(rusthammer_verify)]
use crate as rusthammer;
use rusthammer::{
    Bits, ConfigError, Cursor, End, InputStatus, ParseError, ParseOutcome, Parser, Seq,
    TakeAligned, Verify,
};

/// Maximum payload length in the example record format, in bytes.
pub const MAX_RECORD_PAYLOAD: u64 = 1024;

/// A decoded record. The payload borrows the original input buffer.
#[derive(Debug, PartialEq, Eq)]
pub struct Record<'input> {
    pub version: u64,
    pub flags: u64,
    pub payload: &'input [u8],
}

/// A byte-aligned, complete record: 3-bit version, 5-bit flags, 16-bit length,
/// then exactly that many payload bytes. All fields are MSB-first.
///
/// Version must be 1; all five flag bits are available. Lengths above
/// `MAX_RECORD_PAYLOAD` are rejected with `Mismatch`. The complete three-byte
/// header is read before these constraints are checked. Trailing input is rejected.
/// Partial input waits for the remaining bytes or confirmation of EOF; call
/// `parse_with` again with the accumulated buffer and the original cursor.
#[derive(Clone, Copy)]
pub struct RecordParser {
    version: Bits,
    flags: Bits,
    length: Bits,
}

impl RecordParser {
    /// Validate the fixed field widths once, before any input is supplied.
    pub fn new() -> Result<Self, ConfigError> {
        let version = match Bits::new(3) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        let flags = match Bits::new(5) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        let length = match Bits::new(16) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        Ok(Self {
            version,
            flags,
            length,
        })
    }
}

impl<'input> Parser<'input> for RecordParser {
    type Output = Record<'input>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        // An empty aligned read validates the cursor and alignment without advancing.
        match (TakeAligned { count: 0 }).parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => return ParseOutcome::Error(error),
            ParseOutcome::Success(_, _) => {}
        }
        let header = Verify {
            parser: Seq {
                first: self.version,
                second: Seq {
                    first: self.flags,
                    second: self.length,
                },
            },
            predicate: |fields: &(u64, (u64, u64))| {
                fields.0 == 1 && fields.1 .1 <= MAX_RECORD_PAYLOAD
            },
        };
        match header.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::Success(next, (version, (flags, length))) => {
                // The verified bound fits usize on every supported Rust target.
                parse_record_body(input, next, version, flags, length as usize, status)
            }
        }
    }
}

fn parse_record_body(
    input: &[u8],
    cursor: Cursor,
    version: u64,
    flags: u64,
    count: usize,
    status: InputStatus,
) -> ParseOutcome<Record<'_>> {
    let body = Seq {
        first: TakeAligned { count },
        second: End,
    };
    match body.parse_with(input, cursor, status) {
        ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::Success(end, (payload, ())) => ParseOutcome::Success(
            end,
            Record {
                version,
                flags,
                payload,
            },
        ),
    }
}

/// Parse using an already constructed record grammar.
pub fn parse_record<'input>(
    input: &'input [u8],
    cursor: Cursor,
    parser: &RecordParser,
) -> Result<(Cursor, Record<'input>), ParseError> {
    parser.parse(input, cursor)
}
