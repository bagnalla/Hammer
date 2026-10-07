use super::super::{Cursor, Eval, Grammar, ParseContext, ParseError, ParseOutcome};

use core::marker::PhantomData;

/// Succeed with `()` without reading input or validating the supplied cursor.
/// Unlike `End`, this accepts at any position, including on partial input.
/// Unbounded repetition rejects this parser's empty success with `NonProgress`.
#[derive(Clone, Copy)]
pub struct Epsilon;

impl<'input> Grammar<'input> for Epsilon {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for Epsilon {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        cursor: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<()> {
        ParseOutcome::Success(cursor, ())
    }
}

/// Always reject with recoverable `Mismatch`, without inspecting input or cursor.
/// `T` selects the output type for composition; no value of `T` is stored or made.
/// This zero-sized parser implements `Copy` and `Clone` for every output type.
pub struct Fail<T> {
    output: PhantomData<T>,
}

impl<T> Fail<T> {
    /// Construct a failing parser. There is no configuration to validate.
    pub const fn new() -> Self {
        Self {
            output: PhantomData,
        }
    }
}

impl<T> Default for Fail<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Copy for Fail<T> {}

impl<T> Clone for Fail<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'input, T> Grammar<'input> for Fail<T> {
    type Output = T;
}

impl<'input, Backend, T> Eval<'input, Backend> for Fail<T> {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<T> {
        ParseOutcome::Error(ParseError::Mismatch)
    }
}

/// Ordered choice between parsers with the same output type.
///
/// The first success wins. After a recoverable failure, the second parser starts
/// at the original cursor and its result is returned unchanged. Other errors
/// propagate immediately. A later failure outside this choice does not revisit it.
/// `NeedMore` propagates immediately, preserving priority of the first alternative.
/// Cursor backtracking does not undo effects in custom parsers with interior state.
#[derive(Clone, Copy)]
pub struct Choice<P, Q> {
    pub first: P,
    pub second: Q,
}

/// Construct a [`Choice`], checking that both grammars have the same output type.
/// Each child retains its backend capabilities; no parser runs during construction.
///
/// ```
/// use rusthammer::{choice, map, BeU16, Byte, Cursor, Parser};
/// let number = choice(BeU16, map(Byte, u16::from));
/// assert_eq!(number.parse(&[7], Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, 7)));
/// ```
///
/// Different output types are rejected at construction:
///
/// ```compile_fail
/// use rusthammer::{choice, Bit, Byte};
/// let _ = choice(Bit, Byte);
/// ```
pub fn choice<'input, P, Q>(first: P, second: Q) -> Choice<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input, Output = P::Output>,
{
    Choice { first, second }
}

impl<'input, P, Q> Grammar<'input> for Choice<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input, Output = P::Output>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for Choice<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend, Output = P::Output>,
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
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, value),
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    self.second.eval(backend, input, cursor, context)
                } else {
                    ParseOutcome::Error(error)
                }
            }
        }
    }
}

// Both matches start at the same cursor. Ordering their normalized endpoints
// compares consumed bits without an absolute bit count or subtraction.
fn match_length_allows(first: Cursor, second: Cursor, allow_equal: bool) -> bool {
    first.byte > second.byte
        || (first.byte == second.byte
            && (first.bit > second.bit || (allow_equal && first.bit == second.bit)))
}

fn restrict_match<'input, Backend, P, Q>(
    backend: &mut Backend,
    first: &P,
    second: &Q,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    allow_equal: bool,
) -> ParseOutcome<P::Output>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend>,
{
    match first.eval(backend, input, cursor, context) {
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::Success(next, value) => match second.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    ParseOutcome::Success(next, value)
                } else {
                    ParseOutcome::Error(error)
                }
            }
            ParseOutcome::Success(other, _other_value) => {
                if match_length_allows(next, other, allow_equal) {
                    ParseOutcome::Success(next, value)
                } else {
                    ParseOutcome::Error(ParseError::Mismatch)
                }
            }
        },
    }
}

/// Keep the first match if the second rejects or matches strictly fewer bits.
///
/// Corresponds to Hammer's `h_butnot`. Run `first`, then on success run `second`
/// from the original cursor. Recoverable second-child rejection accepts the
/// first value and cursor; two successes accept only when the first is longer.
/// Otherwise return `Mismatch`. Every attempted child's fatal error or
/// `NeedMore` propagates. The second output is discarded and may have any type.
///
/// Cursor validation is delegated to children, as with `Choice`. Endpoints are
/// ordered by byte index, then bit offset; normalized forward matches therefore
/// compare exact consumed bit lengths, without overflowing a bit count. Custom
/// parsers must respect that cursor convention. Speculative effects are not undone.
///
/// ```
/// use rusthammer::{ButNot, ByteIn, BytePattern, Cursor, Parser};
/// let digit_except_six = ButNot {
///     first: ByteIn::new(b"0123456789"),
///     second: BytePattern::new(b"6"),
/// };
/// assert_eq!(digit_except_six.parse(b"7", Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, b'7')));
/// assert!(digit_except_six.parse(b"6", Cursor::start()).is_err());
/// ```
#[derive(Clone, Copy)]
pub struct ButNot<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P, Q> Grammar<'input> for ButNot<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for ButNot<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        restrict_match(
            backend,
            &self.first,
            &self.second,
            input,
            cursor,
            context,
            false,
        )
    }
}

/// Keep the first match if the second rejects or matches no more bits.
///
/// Corresponds to Hammer's `h_difference`. This has `ButNot`'s evaluation order,
/// output, cursor, error, and incompleteness rules, but also accepts equal-length
/// successes. Both children run from the original cursor. Their outputs may have
/// different types. This operation is not ordinary language-set subtraction.
#[derive(Clone, Copy)]
pub struct Difference<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P, Q> Grammar<'input> for Difference<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for Difference<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        restrict_match(
            backend,
            &self.first,
            &self.second,
            input,
            cursor,
            context,
            true,
        )
    }
}

/// Accept exactly one of two matches, returning that child's value and cursor.
///
/// Corresponds to Hammer's `h_xor`. Run `first`; on success or recoverable
/// rejection, run `second` from the original cursor. Two successes return
/// `Mismatch`, regardless of their lengths. Two recoverable rejections return
/// the second error. Fatal errors and `NeedMore` from attempted children
/// propagate immediately. Cursor validation is delegated to children, and
/// speculative effects are not undone.
///
/// Both children must produce the same type. Use `Map` to put different kinds
/// of values into an application enum, as with `Choice`. Outputs need neither
/// `Copy` nor `Clone`; copying this parser requires only copyable children.
///
/// ```compile_fail
/// use rusthammer::{BeU16, Byte, Cursor, Parser, Xor};
/// let parser = Xor { first: Byte, second: BeU16 };
/// let _ = parser.parse(&[0, 1], Cursor::start());
/// ```
#[derive(Clone, Copy)]
pub struct Xor<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P, Q> Grammar<'input> for Xor<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input, Output = P::Output>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for Xor<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend, Output = P::Output>,
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
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    self.second.eval(backend, input, cursor, context)
                } else {
                    ParseOutcome::Error(error)
                }
            }
            ParseOutcome::Success(next, value) => {
                match self.second.eval(backend, input, cursor, context) {
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                    ParseOutcome::Success(_other_cursor, _other_value) => {
                        ParseOutcome::Error(ParseError::Mismatch)
                    }
                    ParseOutcome::Error(error) => {
                        if error.is_recoverable() {
                            ParseOutcome::Success(next, value)
                        } else {
                            ParseOutcome::Error(error)
                        }
                    }
                }
            }
        }
    }
}

/// Parse an optional value, preserving `NeedMore` on partial input.
///
/// Success preserves the child's cursor and wraps its output in `Some`.
/// Recoverable rejection returns `None` at the original cursor, even if the child
/// consumed a prefix before failing. Cursor and alignment errors propagate.
/// The child runs once; restoring the cursor does not undo custom parser effects.
#[derive(Clone, Copy)]
pub struct Optional<P> {
    pub parser: P,
}

/// Construct an [`Optional`] node without evaluating or constraining its child.
/// Evaluation preserves `NeedMore` and treats recoverable rejection as absence.
///
/// ```
/// use rusthammer::{optional, Byte, Cursor, Optional, Parser};
/// const MAYBE_BYTE: Optional<Byte> = optional(Byte);
/// assert_eq!(MAYBE_BYTE.parse(&[], Cursor::start()), Ok((Cursor::start(), None)));
/// ```
pub const fn optional<P>(parser: P) -> Optional<P> {
    Optional { parser }
}

impl<'input, P: Grammar<'input>> Grammar<'input> for Optional<P> {
    type Output = Option<P::Output>;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Optional<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, Some(value)),
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    ParseOutcome::Success(cursor, None)
                } else {
                    ParseOutcome::Error(error)
                }
            }
        }
    }
}

/// Positive lookahead, corresponding to Hammer's `h_and`.
///
/// Run the child once. Success returns `()` at the original cursor, discarding
/// the child's output. Every child error and `NeedMore` propagates unchanged. Lookahead restores
/// only the cursor; it does not undo effects in custom parsers with interior state.
#[derive(Clone, Copy)]
pub struct And<P> {
    pub parser: P,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for And<P> {
    type Output = ();
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for And<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(_, _) => ParseOutcome::Success(cursor, ()),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
        }
    }
}

/// Negative lookahead, preserving `NeedMore` on partial input and corresponding to Hammer's `h_not`.
///
/// Run the child once. Child success returns `Mismatch`; recoverable rejection
/// returns `()` at the original cursor. Cursor and alignment errors propagate.
/// The child's value is discarded, and custom parser effects are not undone.
#[derive(Clone, Copy)]
pub struct Not<P> {
    pub parser: P,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for Not<P> {
    type Output = ();
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Not<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(_, _) => ParseOutcome::Error(ParseError::Mismatch),
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    ParseOutcome::Success(cursor, ())
                } else {
                    ParseOutcome::Error(error)
                }
            }
        }
    }
}
