#![no_std]

use rusthammer::{
    bind, seq, BitSpan, ButNot, Byte, Cursor, Eval, FoldRepeat, Grammar, ParseContext,
    ParseOutcome, Parser, Right, TakeAligned, Tell, WithSpan,
};
use rusthammer_seek_probe::{Seek, SeekConfigError};

pub fn absolute(
    target: Cursor,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> Result<ParseOutcome<Cursor>, SeekConfigError> {
    let seek = Seek::to(target)?;
    Ok(seek.parse_with(input, cursor, context))
}

pub fn relative(
    offset: isize,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<Cursor> {
    Seek::relative(offset).parse_with(input, cursor, context)
}

pub fn end_relative(
    offset: isize,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<Cursor> {
    Seek::from_end(offset).parse_with(input, cursor, context)
}

// The displacement is relative to the end of the pointer field. A byte field
// bounds the multiplication independently of pointer width.
pub fn packet(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<&[u8]> {
    bind(Byte, |offset| Right {
        // u8 -> isize is lossless on every Rust target. An explicit cast uses
        // the existing scalar model; the From<u8> method is opaque in the pins.
        first: Seek::relative(offset as isize * 8),
        second: TakeAligned { count: 2 },
    })
    .parse_with(input, cursor, context)
}

pub fn spanned(
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<(u8, BitSpan<'_>)> {
    WithSpan {
        parser: Right {
            first: Seek::relative(8),
            second: Byte,
        },
    }
    .parse_with(input, cursor, context)
}

pub fn repeated(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<u8> {
    FoldRepeat::exact(Seek::relative(-1), 2, || 0u8, |n, _| n + 1)
        .parse_with(input, cursor, context)
}

pub fn compared(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<Cursor> {
    ButNot {
        first: Seek::relative(-1),
        second: Seek::relative(-2),
    }
    .parse_with(input, cursor, context)
}

// This parser demonstrates that a seek does not erase the selected backend.
pub struct CountedByte;

impl<'input> Grammar<'input> for CountedByte {
    type Output = u8;
}

impl<'input> Eval<'input, u8> for CountedByte {
    fn eval(
        &self,
        backend: &mut u8,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        *backend = 1;
        Byte.eval(backend, input, cursor, context)
    }
}

pub fn backend(
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> (u8, ParseOutcome<(Cursor, u8)>) {
    let mut state = 0u8;
    let parser = seq(Seek::relative(-8), CountedByte);
    let result = parser.eval(&mut state, input, cursor, context);
    (state, result)
}

pub fn saved_position(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<Cursor> {
    // Construct the parser in TryMap so invalid configuration is input rejection.
    // Tell always returns a normalized cursor, but no unwrap is needed.
    let target = rusthammer::try_map(Tell, |position| Seek::to(position));
    bind(target, |seek| Right {
        first: Byte,
        second: seek,
    })
    .parse_with(input, cursor, context)
}

// Retain the native-valid function-item spelling as a separate extraction
// diagnostic. It is not among the supported consumer roots.
pub fn saved_position_function_item(
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<Cursor> {
    let target = rusthammer::try_map(Tell, Seek::to);
    bind(target, |seek| Right {
        first: Byte,
        second: seek,
    })
    .parse_with(input, cursor, context)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrowed_packet_and_saved_position() {
        let input = [1, 99, 12, 34];
        assert_eq!(
            packet(&input, Cursor::start(), ParseContext::FINAL),
            ParseOutcome::Success(Cursor { byte: 4, bit: 0 }, &input[2..])
        );
        assert_eq!(
            saved_position(&input, Cursor::start(), ParseContext::FINAL),
            ParseOutcome::Success(Cursor::start(), Cursor::start())
        );
        assert_eq!(
            saved_position_function_item(&input, Cursor::start(), ParseContext::FINAL),
            ParseOutcome::Success(Cursor::start(), Cursor::start())
        );
    }

    #[test]
    fn state_and_backward_endpoint() {
        assert_eq!(
            backend(&[42], Cursor { byte: 1, bit: 0 }, ParseContext::FINAL),
            (
                1,
                ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, (Cursor::start(), 42))
            )
        );
        assert_eq!(
            compared(&[0], Cursor { byte: 0, bit: 7 }, ParseContext::FINAL),
            ParseOutcome::Success(Cursor { byte: 0, bit: 6 }, Cursor { byte: 0, bit: 6 })
        );
    }
}
