use super::{Cursor, ParseContext, ParseError, ParseOutcome};

/// A typed grammar, independent of the backend used to execute it.
///
/// The output can borrow from the input or from the grammar's configuration.
/// Implementing this trait alone does not provide an execution capability.
pub trait Grammar<'input> {
    type Output;
}

/// Execute a grammar with a selected backend and its invocation-local state.
///
/// Every child invocation must use `eval` with the same backend, including
/// lookahead, retries, and parsers constructed by `Bind`. Calling `parse` or
/// `parse_with` inside an evaluator would start a separate direct execution.
/// Backtracking restores the cursor, not backend bookkeeping.
///
/// Input and immutable ordering/finality context are separate from mutable
/// execution state so returned values can borrow the input independently.
/// Implementations propagate `NeedMore` before trying alternatives or deciding
/// absence; on final input they return success or an error, never `NeedMore`.
/// A stateful backend must bind its state to the input and grammar it describes.
pub trait Eval<'input, Backend>: Grammar<'input> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output>;
}

/// Direct recursive interpretation, with no retained execution state.
#[derive(Clone, Copy, Debug, Default)]
pub struct Direct;

/// Convenience entry points for grammars that support direct interpretation.
///
/// This trait is implemented automatically from `Eval<Direct>`. Custom parsers
/// implement `Grammar` and `Eval`, rather than overriding these entry points.
pub trait Parser<'input>: Eval<'input, Direct> {
    /// Start direct execution with explicit ordering and input finality.
    ///
    /// A partial parse can succeed without reaching EOF. To retry `NeedMore`,
    /// supply the accumulated input and original cursor. Parsers retain no buffer
    /// or continuation. Retrying can rerun callbacks; effects are not rolled back.
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        self.eval(&mut Direct, input, cursor, context)
    }

    /// Parse a complete buffer with high-first bits and big byte order.
    /// A custom evaluator's unexpected `NeedMore` becomes `UnexpectedEnd`.
    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parse_with(input, cursor, ParseContext::FINAL)
            .into_complete()
    }
}

impl<'input, P: Eval<'input, Direct>> Parser<'input> for P {}

/// Reuse a parser by shared reference, preserving both entry points and its output
/// type. The parser reference's lifetime is independent of the input lifetime.
impl<'input, P: Grammar<'input>> Grammar<'input> for &P {
    type Output = P::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for &P {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        P::eval(*self, backend, input, cursor, context)
    }
}
