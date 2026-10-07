//! Consume constructor bodies through normal dependency MIR.
#![no_std]

use rusthammer::{
    Byte, BytePattern, Cursor, Eval, ParseContext, ParseOutcome, Parser, TakeAligned,
};
use rusthammer_constructor_probe::{
    bind, identity_bytes, map, mapped_header, opaque_header, opaque_payload, seq, verify,
    CountByte, Counter,
};

pub fn header(input: &[u8], cursor: Cursor, context: ParseContext, bias: u16) -> ParseOutcome<u32> {
    opaque_header(bias).parse_with(input, cursor, context)
}

pub fn borrows<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<(&'pattern [u8], &'input [u8])> {
    seq(BytePattern::new(pattern), opaque_payload(count)).parse_with(input, cursor, context)
}

pub fn callback<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<&'input [u8]> {
    map(TakeAligned { count }, |bytes| bytes).parse_with(input, cursor, context)
}

pub fn named_callback<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<&'input [u8]> {
    map(TakeAligned { count }, identity_bytes).parse_with(input, cursor, context)
}

pub fn backend<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> (u64, ParseOutcome<&'input [u8]>) {
    let length = map(verify(CountByte, |n| *n <= 16), |n| n as usize);
    let parser = bind(&length, |count| TakeAligned { count });
    let mut counter = Counter { visits: 0 };
    let result = parser.eval(&mut counter, input, cursor, context);
    (counter.visits, result)
}

pub fn generic_backend<Backend>(
    backend: &mut Backend,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
    bias: u16,
) -> ParseOutcome<u32> {
    mapped_header(bias).eval(backend, input, cursor, context)
}

pub fn owned(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<Value> {
    map(Byte, |value| Value(value as u16)).parse_with(input, cursor, context)
}

// Parsed outputs acquire neither Copy nor Clone from the construction API.
#[derive(Debug, PartialEq, Eq)]
pub struct Value(pub u16);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downstream_builders_keep_owned_and_borrowed_outputs() {
        assert_eq!(
            owned(&[7], Cursor::start(), ParseContext::FINAL),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, Value(7))
        );
        let input = *b"\x03abc!";
        assert_eq!(
            backend(&input, Cursor::start(), ParseContext::FINAL),
            (
                1,
                ParseOutcome::Success(Cursor { byte: 4, bit: 0 }, &input[1..4])
            )
        );
        assert_eq!(
            callback(&input, Cursor::start(), ParseContext::FINAL, 2),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &input[..2])
        );
        assert_eq!(
            named_callback(&input, Cursor::start(), ParseContext::FINAL, 2),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &input[..2])
        );
        assert_eq!(
            borrows(&input[..1], &input, Cursor::start(), ParseContext::FINAL, 3),
            ParseOutcome::Success(Cursor { byte: 4, bit: 0 }, (&input[..1], &input[1..4]))
        );
    }
}
