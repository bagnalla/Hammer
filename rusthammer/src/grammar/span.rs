use super::super::{BitSpan, Cursor, Eval, Grammar, ParseContext, ParseError, ParseOutcome};

use super::super::span_types::span_cursor_valid;

/// Retain a child's decoded value together with its matched input span.
///
/// The output is `(P::Output, BitSpan<'input>)`. This wrapper annotates only its
/// own result; nested values acquire spans only where explicitly wrapped.
/// The starting cursor is validated before the child runs. On success, the
/// ending cursor is validated and backward movement rejected with `NonProgress`.
/// Empty matches are allowed. Child errors and `NeedMore` propagate unchanged.
/// Backend state and context follow the child, including on a rejected exit.
///
/// Custom children must obey the ordering scope rules: endpoint checks cannot
/// establish which bits an arbitrary parser inspected. Lookahead contributes
/// no consumed input, and therefore has an empty span when wrapped.
/// Seeking measures the interval between this wrapper's entry and final exit:
/// it can include skipped bytes and omit bytes read during a seek-and-return
/// excursion. Wrap the field parser after a seek to capture that field's span.
///
/// ```
/// use rusthammer::{BeU16, Cursor, Parser, WithSpan};
/// let input = [0x12, 0x34];
/// let (_, (value, span)) = WithSpan { parser: BeU16 }
///     .parse(&input, Cursor::start()).unwrap();
/// assert_eq!(value, 0x1234);
/// assert_eq!(span.as_bytes(), Some(input.as_slice()));
/// ```
#[derive(Clone, Copy)]
pub struct WithSpan<P> {
    pub parser: P,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for WithSpan<P> {
    type Output = (P::Output, BitSpan<'input>);
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for WithSpan<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        if !span_cursor_valid(input.len(), cursor) {
            return ParseOutcome::Error(ParseError::InvalidCursor);
        }
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => {
                let span = match BitSpan::new(input, cursor, next, context.order.bit) {
                    Ok(span) => span,
                    Err(error) => return ParseOutcome::Error(error),
                };
                ParseOutcome::Success(next, (value, span))
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Return the matched input span, discarding the child's decoded value.
///
/// Uses the same validation and consumption rules as [`WithSpan`]. The child
/// still runs and constructs its output, including allocations and callback
/// effects; that value is then dropped. Grammar nodes remain backend-generic.
///
/// ```
/// use rusthammer::{BeU16, Cursor, Parser, Recognize};
/// let input = [0x12, 0x34];
/// let (_, span) = Recognize { parser: BeU16 }
///     .parse(&input, Cursor::start()).unwrap();
/// assert_eq!(span.as_bytes(), Some(input.as_slice()));
/// ```
#[derive(Clone, Copy)]
pub struct Recognize<P> {
    pub parser: P,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for Recognize<P> {
    type Output = BitSpan<'input>;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Recognize<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let spanned = WithSpan {
            parser: &self.parser,
        };
        match spanned.eval(backend, input, cursor, context) {
            // Move the complete tuple before destructuring for dependency MIR;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, output) => {
                let (_, span) = output;
                ParseOutcome::Success(next, span)
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}
