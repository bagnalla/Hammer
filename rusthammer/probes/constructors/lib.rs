//! Experimental construction API: no additions to RustHammer's public API.
#![no_std]

use rusthammer::{
    BeU16, Bind, Byte, BytePattern, Choice, Cursor, Eval, Grammar, Map, Optional, ParseContext,
    ParseOutcome, Parser, Seq, TakeAligned, TryMap, Verify,
};

pub fn baseline(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<u8> {
    Byte.parse_with(input, cursor, context)
}

pub const fn seq<P, Q>(first: P, second: Q) -> Seq<P, Q> {
    Seq { first, second }
}

pub fn map<'input, P, F, O>(parser: P, map: F) -> Map<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> O,
{
    Map { parser, map }
}

pub fn try_map<'input, P, F, O, E>(parser: P, map: F) -> TryMap<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> Result<O, E>,
{
    TryMap { parser, map }
}

pub fn verify<'input, P, F>(parser: P, predicate: F) -> Verify<P, F>
where
    P: Grammar<'input>,
    F: Fn(&P::Output) -> bool,
{
    Verify { parser, predicate }
}

pub fn choice<'input, P, Q>(first: P, second: Q) -> Choice<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input, Output = P::Output>,
{
    Choice { first, second }
}

pub fn bind<'input, P, F, Q>(parser: P, then: F) -> Bind<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> Q,
    Q: Grammar<'input>,
{
    Bind { parser, then }
}

pub const fn optional<P>(parser: P) -> Optional<P> {
    Optional { parser }
}

// Hide only the callback, retaining the grammar node and its backend capabilities.
pub fn mapped_header(bias: u16) -> Map<Seq<Byte, BeU16>, impl Fn((u8, u16)) -> u32 + Copy> {
    map(seq(Byte, BeU16), move |(tag, length)| {
        tag as u32 + length as u32 + bias as u32
    })
}

pub fn concrete_header(
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
    bias: u16,
) -> ParseOutcome<u32> {
    mapped_header(bias).parse_with(input, cursor, context)
}

pub fn checked_choice(
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
    limit: u8,
) -> ParseOutcome<Option<u16>> {
    let checked = try_map(Byte, move |value| {
        if value < limit {
            Ok(value as u16)
        } else {
            Err(())
        }
    });
    let fallback = map(verify(Byte, |value| *value == 255), |_| 256u16);
    optional(choice(checked, fallback)).parse_with(input, cursor, context)
}

pub fn dependent_payload<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<&'input [u8]> {
    bind(Byte, |count| TakeAligned {
        count: count as usize,
    })
    .parse_with(input, cursor, context)
}

pub fn borrowed_sources<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<(&'pattern [u8], &'input [u8])> {
    seq(BytePattern::new(pattern), TakeAligned { count }).parse_with(input, cursor, context)
}

// Exercise the lifetime-specific callback bound, including a borrowed result.
pub fn borrowed_callback<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<&'input [u8]> {
    map(TakeAligned { count }, |bytes| bytes).parse_with(input, cursor, context)
}

// Control: the same lifetime-specific closure without a construction helper.
pub fn direct_borrowed_callback<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<&'input [u8]> {
    Map {
        parser: TakeAligned { count },
        map: |bytes: &'input [u8]| bytes,
    }
    .parse_with(input, cursor, context)
}

pub fn identity_bytes(bytes: &[u8]) -> &[u8] {
    bytes
}

pub fn named_borrowed_callback<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<&'input [u8]> {
    map(TakeAligned { count }, identity_bytes).parse_with(input, cursor, context)
}

pub struct Counter {
    pub visits: u64,
}

pub struct CountByte;

impl<'input> Grammar<'input> for CountByte {
    type Output = u8;
}

// Deliberately no Eval<Direct>: the constructors must not require Parser bounds.
impl<'input> Eval<'input, Counter> for CountByte {
    fn eval(
        &self,
        backend: &mut Counter,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        backend.visits += 1;
        Byte.eval(backend, input, cursor, context)
    }
}

pub fn backend_only<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> (u64, ParseOutcome<&'input [u8]>) {
    let mut counter = Counter { visits: 0 };
    let length = map(verify(CountByte, |n| *n <= 16), |n| n as usize);
    let parser = bind(&length, |count| TakeAligned { count });
    let result = parser.eval(&mut counter, input, cursor, context);
    (counter.visits, result)
}

pub fn opaque_header(bias: u16) -> impl for<'input> Parser<'input, Output = u32> + Copy {
    mapped_header(bias)
}

pub fn run_opaque_header(
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
    bias: u16,
) -> ParseOutcome<u32> {
    opaque_header(bias).parse_with(input, cursor, context)
}

pub fn opaque_payload(count: usize) -> impl for<'input> Parser<'input, Output = &'input [u8]> {
    TakeAligned { count }
}

pub fn run_opaque_payload<'input>(
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    count: usize,
) -> ParseOutcome<&'input [u8]> {
    opaque_payload(count).parse_with(input, cursor, context)
}

// The callback is constructed outside this backend-generic function, avoiding
// the separately documented backend_closure.rs limitation.
pub fn callback_backend<Backend>(
    backend: &mut Backend,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
    bias: u16,
) -> ParseOutcome<u32> {
    mapped_header(bias).eval(backend, input, cursor, context)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rusthammer::{Direct, ParseError};

    #[test]
    fn concrete_and_opaque_headers_preserve_results_and_input_status() {
        for context in [ParseContext::FINAL, ParseContext::PARTIAL] {
            let expected = ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, 9);
            assert_eq!(
                concrete_header(&[1, 0, 3], Cursor::start(), context, 5),
                expected
            );
            assert_eq!(
                run_opaque_header(&[1, 0, 3], Cursor::start(), context, 5),
                expected
            );
            assert_eq!(
                callback_backend(&mut Direct, &[1, 0, 3], Cursor::start(), context, 5),
                expected
            );
        }
        assert_eq!(
            run_opaque_header(&[1], Cursor::start(), ParseContext::PARTIAL, 0),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            concrete_header(&[1], Cursor::start(), ParseContext::FINAL, 0),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
    }

    #[test]
    fn checked_constructors_preserve_retry_and_optionality() {
        assert_eq!(
            checked_choice(&[3], Cursor::start(), ParseContext::FINAL, 8),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, Some(3))
        );
        assert_eq!(
            checked_choice(&[255], Cursor::start(), ParseContext::FINAL, 8),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, Some(256))
        );
        assert_eq!(
            checked_choice(&[20], Cursor::start(), ParseContext::FINAL, 8),
            ParseOutcome::Success(Cursor::start(), None)
        );
        assert_eq!(
            checked_choice(&[], Cursor::start(), ParseContext::PARTIAL, 8),
            ParseOutcome::NeedMore
        );
    }

    #[test]
    fn borrowed_results_outlive_local_grammars_and_backend_state() {
        let input = *b"\x03abc!";
        let expected = ParseOutcome::Success(Cursor { byte: 4, bit: 0 }, &input[1..4]);
        assert_eq!(
            dependent_payload(&input, Cursor::start(), ParseContext::FINAL),
            expected
        );
        assert_eq!(
            backend_only(&input, Cursor::start(), ParseContext::FINAL),
            (1, expected)
        );
        assert_eq!(
            borrowed_callback(&input, Cursor::start(), ParseContext::FINAL, 2),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &input[..2])
        );
        assert_eq!(
            direct_borrowed_callback(&input, Cursor::start(), ParseContext::FINAL, 2),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &input[..2])
        );
        assert_eq!(
            named_borrowed_callback(&input, Cursor::start(), ParseContext::FINAL, 2),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &input[..2])
        );
        assert_eq!(
            run_opaque_payload(&input, Cursor::start(), ParseContext::FINAL, 2),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &input[..2])
        );
    }

    #[test]
    fn configuration_and_input_borrows_remain_distinct() {
        let pattern = *b"ab";
        let input = *b"abcd";
        match borrowed_sources(&pattern, &input, Cursor::start(), ParseContext::FINAL, 2) {
            ParseOutcome::Success(_, (matched, payload)) => {
                assert!(core::ptr::eq(matched.as_ptr(), pattern.as_ptr()));
                assert!(core::ptr::eq(payload.as_ptr(), input[2..].as_ptr()));
            }
            _ => panic!("expected borrowed outputs"),
        }
    }

    #[test]
    fn bounded_constructor_infers_callback_and_keeps_copy() {
        let parser = map(Byte, |n| n.wrapping_add(1));
        let copied = parser;
        assert_eq!(
            copied.parse(&[255], Cursor::start()),
            parser.parse(&[255], Cursor::start())
        );
        let header = opaque_header(0);
        let copy = header;
        assert_eq!(
            header.parse(&[1, 0, 2], Cursor::start()),
            copy.parse(&[1, 0, 2], Cursor::start())
        );
    }
}
