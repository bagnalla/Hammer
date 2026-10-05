//! Diagnostic reproducer: returning the pattern borrow through a matching loop.
#![no_std]

#[path = "../src/lib.rs"]
mod rusthammer;
use rusthammer::{Byte, Cursor, ParseContext, ParseError, ParseOutcome, Parser};

pub fn match_pattern<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<&'pattern [u8]> {
    let mut next = cursor;
    let mut index = 0;
    while index < pattern.len() {
        match Byte.parse_with(input, next, context) {
            ParseOutcome::Success(after, value) => {
                if value != pattern[index] {
                    return ParseOutcome::Error(ParseError::Mismatch);
                }
                next = after;
                index += 1;
            }
            ParseOutcome::Error(error) => return ParseOutcome::Error(error),
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
        }
    }
    ParseOutcome::Success(next, pattern)
}
