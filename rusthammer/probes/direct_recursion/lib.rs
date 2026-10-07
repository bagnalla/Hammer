//! Private direct-recursion compatibility evidence, not a production API.
#![no_std]
#![forbid(unsafe_code)]

pub mod candidates;

use rusthammer::{
    seq, BytePattern, Direct, End, Eval, Grammar, Literal, ParseError, Recognize, WithSpan,
};
pub use rusthammer::{BitSpan, Cursor, ParseContext, ParseOutcome};

#[cfg(test)]
mod tests;

// The grammar configuration is retained independently of the input. This named
// adapter is finite and does not call its own Eval dictionary from its body.
#[derive(Clone, Copy)]
pub struct Pairs<'pattern> {
    pattern: BytePattern<'pattern>,
}

impl<'pattern> Pairs<'pattern> {
    pub const fn new(pattern: &'pattern [u8]) -> Self {
        Self {
            pattern: BytePattern::new(pattern),
        }
    }
}

// Intentionally neither Clone nor Copy. These results are moved through the
// recursive calls and the existing outer combinators, never memoized or replayed.
#[derive(Debug, PartialEq, Eq)]
pub struct Parsed<'pattern> {
    pub pattern: &'pattern [u8],
    pub depth: usize,
}
struct Inner<'pattern> {
    parsed: Parsed<'pattern>,
}

impl<'input, 'pattern> Grammar<'input> for Pairs<'pattern> {
    type Output = Parsed<'pattern>;
}
impl<'input, 'pattern> Eval<'input, Direct> for Pairs<'pattern> {
    fn eval(
        &self,
        backend: &mut Direct,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Parsed<'pattern>> {
        round(&self.pattern, backend, input, cursor, context)
    }
}

fn literal(byte: u8) -> Literal {
    Literal::new(8, u64::from(byte)).unwrap()
}

// A <- '(' B ')' / configured_pattern
// B <- '[' A ']'
// These functions implement choice/sequence around the recursive calls using
// ordinary Rust control flow. This limitation is deliberate evidence: the full
// body cannot yet be passed to existing generic Eval combinators without the
// dictionary cycle retained in candidates.rs. No general lowering is claimed.
fn round<'input, 'pattern>(
    pattern: &BytePattern<'pattern>,
    backend: &mut Direct,
    input: &'input [u8],
    start: Cursor,
    context: ParseContext,
) -> ParseOutcome<Parsed<'pattern>> {
    let attempt = round_delimited(pattern, backend, input, start, context);
    match attempt {
        ParseOutcome::Error(error) if error.is_recoverable() => {
            match pattern.eval(backend, input, start, context) {
                ParseOutcome::Success(next, pattern) => {
                    ParseOutcome::Success(next, Parsed { pattern, depth: 0 })
                }
                ParseOutcome::Error(error) => ParseOutcome::Error(error),
                ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            }
        }
        other => other,
    }
}

fn round_delimited<'input, 'pattern>(
    pattern: &BytePattern<'pattern>,
    backend: &mut Direct,
    input: &'input [u8],
    start: Cursor,
    context: ParseContext,
) -> ParseOutcome<Parsed<'pattern>> {
    match literal(b'(').eval(backend, input, start, context) {
        ParseOutcome::Success(next, _) => match square(pattern, backend, input, next, context) {
            ParseOutcome::Success(after, inner) => {
                match literal(b')').eval(backend, input, after, context) {
                    ParseOutcome::Success(end, _) => match inner.parsed.depth.checked_add(1) {
                        Some(depth) => ParseOutcome::Success(
                            end,
                            Parsed {
                                pattern: inner.parsed.pattern,
                                depth,
                            },
                        ),
                        None => ParseOutcome::Error(ParseError::CountOverflow),
                    },
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                }
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        },
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

fn square<'input, 'pattern>(
    pattern: &BytePattern<'pattern>,
    backend: &mut Direct,
    input: &'input [u8],
    start: Cursor,
    context: ParseContext,
) -> ParseOutcome<Inner<'pattern>> {
    match literal(b'[').eval(backend, input, start, context) {
        ParseOutcome::Success(next, _) => match round(pattern, backend, input, next, context) {
            ParseOutcome::Success(after, parsed) => {
                match literal(b']').eval(backend, input, after, context) {
                    ParseOutcome::Success(end, _) => ParseOutcome::Success(end, Inner { parsed }),
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                }
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        },
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

pub fn configured<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    context: ParseContext,
) -> ParseOutcome<Parsed<'pattern>> {
    Pairs::new(pattern).eval(&mut Direct, input, Cursor::start(), context)
}

pub fn spanned<'input, 'pattern>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<(Parsed<'pattern>, BitSpan<'input>)> {
    WithSpan {
        parser: Pairs::new(pattern),
    }
    .eval(&mut Direct, input, cursor, context)
}

pub fn recognized<'input>(
    pattern: &[u8],
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<BitSpan<'input>> {
    Recognize {
        parser: Pairs::new(pattern),
    }
    .eval(&mut Direct, input, cursor, context)
}

pub fn complete<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    context: ParseContext,
) -> ParseOutcome<(Parsed<'pattern>, ())> {
    seq(Pairs::new(pattern), End).eval(&mut Direct, input, Cursor::start(), context)
}

pub fn twice<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    context: ParseContext,
) -> ParseOutcome<(Parsed<'pattern>, Parsed<'pattern>)> {
    let parser = Pairs::new(pattern);
    seq(parser, parser).eval(&mut Direct, input, Cursor::start(), context)
}

// A second fixture isolates ordinary self recursion from the heterogeneous
// mutual calls above. All recursive calls follow a successful one-byte read.
pub fn count(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<usize> {
    match literal(b'a').eval(&mut Direct, input, cursor, context) {
        ParseOutcome::Success(next, _) => match count(input, next, context) {
            ParseOutcome::Success(end, n) => match n.checked_add(1) {
                Some(total) => ParseOutcome::Success(end, total),
                None => ParseOutcome::Error(ParseError::CountOverflow),
            },
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        },
        ParseOutcome::Error(error) if error.is_recoverable() => ParseOutcome::Success(cursor, 0),
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}
