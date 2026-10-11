use super::super::{ByteOrder, Cursor, ParseError, Parser};

/// Run two parsers in order, returning their typed outputs as a pair.
/// Errors propagate unchanged. No caller-owned cursor is mutated.
#[derive(Clone, Copy)]
pub struct Seq<P, Q> {
    pub first: P,
    pub second: Q,
}

/// Construct a [`Seq`], retaining both children.
/// Construction has no trait bounds; parsing requires both children to implement
/// `Parser`. Shared child references are accepted.
///
/// ```
/// use rusthammer::{seq, BeU16, Byte, Cursor, Parser, Seq};
/// const HEADER: Seq<Byte, BeU16> = seq(Byte, BeU16);
/// assert_eq!(HEADER.parse(&[7, 0, 3], Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, (7, 3))));
/// ```
pub const fn seq<P, Q>(first: P, second: Q) -> Seq<P, Q> {
    Seq { first, second }
}

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Seq<P, Q> {
    type Output = (P::Output, Q::Output);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        match self.first.parse_with(input, cursor, byte_order) {
            Err(error) => Err(error),
            Ok(parsed) => {
                let (next, first) = parsed;
                match self.second.parse_with(input, next, byte_order) {
                    Err(error) => Err(error),
                    Ok(parsed) => {
                        let (end, second) = parsed;
                        Ok((end, (first, second)))
                    }
                }
            }
        }
    }
}

/// Use a parsed value to construct the next parser, returning that parser's output.
///
/// `then` takes ownership of the first output and runs exactly once after success.
/// Its parser runs at that success cursor with the same input and byte order. Errors from
/// either stage propagate unchanged; a first-stage failure
/// skips the factory. Outputs and the constructed parser need neither `Copy` nor
/// `Clone`. Copying this combinator depends only on its stored parser and factory.
///
/// For each input lifetime, the factory returns one concrete parser type. Parsed
/// values can change that parser's configuration. Use a typed parser enum for
/// branches with different implementations. `TryMap` can check input-derived
/// counts or construct a checked parser before `Bind` executes it.
///
/// The combinator allocates no memory and retains no state between calls.
/// Verification requires contracts for the first parser, factory, and constructed
/// parsers. Retrying or backtracking can rerun the factory; its effects are not
/// rolled back. `Fn` alone does not imply purity, termination, or panic freedom.
///
/// ```
/// use rusthammer::{Bind, Bits, Cursor, Parser, TakeAligned, TryMap};
/// let payload = Bind {
///     parser: TryMap {
///         parser: Bits::new(8).unwrap(),
///         map: |length| usize::try_from(length),
///     },
///     then: |count| TakeAligned { count },
/// };
/// assert_eq!(payload.parse(b"\x03abc!", Cursor::start()),
///     Ok((Cursor { byte: 4, bit: 0 }, &b"abc"[..])));
/// ```
#[derive(Clone, Copy)]
pub struct Bind<P, F> {
    pub parser: P,
    pub then: F,
}

/// Construct a [`Bind`], inferring the factory argument from the child's output.
/// The factory is stored without being called. Both parser types implement `Parser`.
///
/// ```
/// use rusthammer::{bind, Byte, Cursor, Parser, TakeAligned};
/// let payload = bind(Byte, |count| TakeAligned { count: usize::from(count) });
/// assert_eq!(payload.parse(b"\x03abc!", Cursor::start()),
///     Ok((Cursor { byte: 4, bit: 0 }, &b"abc"[..])));
/// ```
pub fn bind<'input, P, F, Q>(parser: P, then: F) -> Bind<P, F>
where
    P: Parser<'input>,
    F: Fn(P::Output) -> Q,
    Q: Parser<'input>,
{
    Bind { parser, then }
}

impl<'input, P, F, Q> Parser<'input> for Bind<P, F>
where
    P: Parser<'input>,
    F: Fn(P::Output) -> Q,
    Q: Parser<'input>,
{
    type Output = Q::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        match self.parser.parse_with(input, cursor, byte_order) {
            Ok(parsed) => {
                let (next, value) = parsed;
                (self.then)(value).parse_with(input, next, byte_order)
            }
            Err(error) => Err(error),
        }
    }
}

/// Run both parsers in order, keeping the first value and the final cursor.
/// Both children must succeed; errors propagate as in `Seq`.
/// Outputs are moved or discarded and need neither `Copy` nor `Clone`.
#[derive(Clone, Copy)]
pub struct Left<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Left<P, Q> {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.parse_with(input, cursor, byte_order) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see probes/direct_v1/README.md.
            Ok(parsed) => {
                let (next, values) = parsed;
                let (first, _) = values;
                Ok((next, first))
            }
            Err(error) => Err(error),
        }
    }
}

/// Run both parsers in order, keeping the second value and the final cursor.
/// Both children must succeed; errors propagate as in `Seq`.
/// Outputs are moved or discarded and need neither `Copy` nor `Clone`.
#[derive(Clone, Copy)]
pub struct Right<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Right<P, Q> {
    type Output = Q::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.parse_with(input, cursor, byte_order) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see probes/direct_v1/README.md.
            Ok(parsed) => {
                let (next, values) = parsed;
                let (_, second) = values;
                Ok((next, second))
            }
            Err(error) => Err(error),
        }
    }
}

/// Run `left`, `parser`, and `right` in order, keeping the middle value and the
/// final cursor. All three must succeed, including the discarded delimiters.
/// Errors propagate as in `Seq`; outputs need no `Copy` or `Clone`.
#[derive(Clone, Copy)]
pub struct Middle<L, P, R> {
    pub left: L,
    pub parser: P,
    pub right: R,
}

impl<'input, L: Parser<'input>, P: Parser<'input>, R: Parser<'input>> Parser<'input>
    for Middle<L, P, R>
{
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let sequence = Seq {
            first: &self.left,
            second: Seq {
                first: &self.parser,
                second: &self.right,
            },
        };
        match sequence.parse_with(input, cursor, byte_order) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see probes/direct_v1/README.md.
            Ok(parsed) => {
                let (next, values) = parsed;
                let (_, (middle, _)) = values;
                Ok((next, middle))
            }
            Err(error) => Err(error),
        }
    }
}

/// Run a parser, consuming its match and replacing its successful output with `()`.
/// Child errors propagate unchanged. The child still constructs
/// its output before it is discarded, including any allocations or callback effects.
#[derive(Clone, Copy)]
pub struct Ignore<P> {
    pub parser: P,
}

impl<'input, P: Parser<'input>> Parser<'input> for Ignore<P> {
    type Output = ();

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, ()), ParseError> {
        match self.parser.parse_with(input, cursor, byte_order) {
            Ok(parsed) => {
                let (next, _) = parsed;
                Ok((next, ()))
            }
            Err(error) => Err(error),
        }
    }
}
