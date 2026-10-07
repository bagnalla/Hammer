use super::super::{Cursor, Eval, Grammar, Order, ParseContext, ParseError, ParseOutcome};

/// Override a child's bit and byte order, preserving input finality.
///
/// A change of bit direction requires a valid, byte-aligned starting cursor
/// and successful ending cursor. Invalid bounds take precedence over `Unaligned`.
/// Entry rejection skips the child; exit rejection discards its output. Child
/// errors and `NeedMore` propagate unchanged. No padding is inserted.
/// A scope that keeps bit direction delegates without extra cursor checks,
/// so byte-order-only changes can start and finish within a byte.
///
/// ```
/// use rusthammer::{BeU16, BitOrder, Bits, ByteOrder, Cursor, Order, Parser, Seq, WithOrder};
/// let parser = Seq {
///     first: WithOrder {
///         order: Order { bit: BitOrder::LowFirst, byte: ByteOrder::Little },
///         parser: Seq { first: Bits::new(3).unwrap(), second: Bits::new(5).unwrap() },
///     },
///     second: BeU16,
/// };
/// assert_eq!(parser.parse(&[0x96, 0x12, 0x34], Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, ((6, 18), 0x1234))));
/// ```
#[derive(Clone, Copy)]
pub struct WithOrder<P> {
    pub parser: P,
    pub order: Order,
}

fn scope_boundary_error(length: usize, cursor: Cursor) -> Option<ParseError> {
    if cursor.bit >= 8 || cursor.byte > length || (cursor.byte == length && cursor.bit != 0) {
        Some(ParseError::InvalidCursor)
    } else if cursor.bit != 0 {
        Some(ParseError::Unaligned)
    } else {
        None
    }
}

fn finish_order_scope<T>(length: usize, changed: bool, result: ParseOutcome<T>) -> ParseOutcome<T> {
    if !changed {
        return result;
    }
    match result {
        ParseOutcome::Success(next, value) => match scope_boundary_error(length, next) {
            Some(error) => ParseOutcome::Error(error),
            None => ParseOutcome::Success(next, value),
        },
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

impl<'input, P: Grammar<'input>> Grammar<'input> for WithOrder<P> {
    type Output = P::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for WithOrder<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let changed = self.order.bit != context.order.bit;
        if changed {
            if let Some(error) = scope_boundary_error(input.len(), cursor) {
                return ParseOutcome::Error(error);
            }
        }
        let result = self.parser.eval(
            backend,
            input,
            cursor,
            ParseContext {
                order: self.order,
                status: context.status,
            },
        );
        finish_order_scope(input.len(), changed, result)
    }
}
