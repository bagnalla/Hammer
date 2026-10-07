use super::super::{Cursor, Eval, Grammar, ParseContext, ParseOutcome};

/// Run two parsers in order, returning their typed outputs as a pair.
/// Errors and `NeedMore` propagate unchanged. No caller-owned cursor is mutated.
#[derive(Clone, Copy)]
pub struct Seq<P, Q> {
    pub first: P,
    pub second: Q,
}

/// Construct a [`Seq`], retaining both children and their backend capabilities.
/// Construction has no grammar bounds; evaluation requires both children to
/// support the chosen backend. Shared child references are accepted.
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

impl<'input, P: Grammar<'input>, Q: Grammar<'input>> Grammar<'input> for Seq<P, Q> {
    type Output = (P::Output, Q::Output);
}

impl<'input, Backend, P: Eval<'input, Backend>, Q: Eval<'input, Backend>> Eval<'input, Backend>
    for Seq<P, Q>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.first.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::Success(next, first) => {
                match self.second.eval(backend, input, next, context) {
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::Success(end, second) => {
                        ParseOutcome::Success(end, (first, second))
                    }
                }
            }
        }
    }
}

/// Use a parsed value to construct the next parser, returning that parser's output.
///
/// `then` takes ownership of the first output and runs exactly once after success.
/// Its parser runs at that success cursor with the same input and context. Errors
/// and `NeedMore` from either stage propagate unchanged; a first-stage failure
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
/// The factory is stored without being called. Both grammar types can support
/// any backend; construction does not require `Eval<Direct>`.
///
/// ```
/// use rusthammer::{bind, Byte, Cursor, Parser, TakeAligned};
/// let payload = bind(Byte, |count| TakeAligned { count: usize::from(count) });
/// assert_eq!(payload.parse(b"\x03abc!", Cursor::start()),
///     Ok((Cursor { byte: 4, bit: 0 }, &b"abc"[..])));
/// ```
pub fn bind<'input, P, F, Q>(parser: P, then: F) -> Bind<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> Q,
    Q: Grammar<'input>,
{
    Bind { parser, then }
}

impl<'input, P, F, Q> Grammar<'input> for Bind<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> Q,
    Q: Grammar<'input>,
{
    type Output = Q::Output;
}

impl<'input, Backend, P, F, Q> Eval<'input, Backend> for Bind<P, F>
where
    P: Eval<'input, Backend>,
    F: Fn(P::Output) -> Q,
    Q: Eval<'input, Backend>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => {
                (self.then)(value).eval(backend, input, next, context)
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Run both parsers in order, keeping the first value and the final cursor.
/// Both children must succeed; errors and `NeedMore` propagate as in `Seq`.
/// Outputs are moved or discarded and need neither `Copy` nor `Clone`.
#[derive(Clone, Copy)]
pub struct Left<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P: Grammar<'input>, Q: Grammar<'input>> Grammar<'input> for Left<P, Q> {
    type Output = P::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>, Q: Eval<'input, Backend>> Eval<'input, Backend>
    for Left<P, Q>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.eval(backend, input, cursor, context) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, values) => {
                let (first, _) = values;
                ParseOutcome::Success(next, first)
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Run both parsers in order, keeping the second value and the final cursor.
/// Both children must succeed; errors and `NeedMore` propagate as in `Seq`.
/// Outputs are moved or discarded and need neither `Copy` nor `Clone`.
#[derive(Clone, Copy)]
pub struct Right<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P: Grammar<'input>, Q: Grammar<'input>> Grammar<'input> for Right<P, Q> {
    type Output = Q::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>, Q: Eval<'input, Backend>> Eval<'input, Backend>
    for Right<P, Q>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.eval(backend, input, cursor, context) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, values) => {
                let (_, second) = values;
                ParseOutcome::Success(next, second)
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Run `left`, `parser`, and `right` in order, keeping the middle value and the
/// final cursor. All three must succeed, including the discarded delimiters.
/// Errors and `NeedMore` propagate as in `Seq`; outputs need no `Copy` or `Clone`.
#[derive(Clone, Copy)]
pub struct Middle<L, P, R> {
    pub left: L,
    pub parser: P,
    pub right: R,
}

impl<'input, L: Grammar<'input>, P: Grammar<'input>, R: Grammar<'input>> Grammar<'input>
    for Middle<L, P, R>
{
    type Output = P::Output;
}

impl<
        'input,
        Backend,
        L: Eval<'input, Backend>,
        P: Eval<'input, Backend>,
        R: Eval<'input, Backend>,
    > Eval<'input, Backend> for Middle<L, P, R>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.left,
            second: Seq {
                first: &self.parser,
                second: &self.right,
            },
        };
        match sequence.eval(backend, input, cursor, context) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, values) => {
                let (_, (middle, _)) = values;
                ParseOutcome::Success(next, middle)
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Run a parser, consuming its match and replacing its successful output with `()`.
/// Child errors and `NeedMore` propagate unchanged. The child still constructs
/// its output before it is discarded, including any allocations or callback effects.
#[derive(Clone, Copy)]
pub struct Ignore<P> {
    pub parser: P,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for Ignore<P> {
    type Output = ();
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Ignore<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, _) => ParseOutcome::Success(next, ()),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}
