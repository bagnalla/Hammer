use super::{ByteOrder, Cursor, ParseError};

/// Execute a typed parser directly on a complete, immutable input buffer.
///
/// Outputs may borrow the input or independently borrowed configuration; they
/// need neither `Copy` nor `Clone`. Bits are traversed high first. Byte order
/// controls the significance of successive physical-byte fragments in a field.
///
/// From a valid entry cursor, supported parsers must return a valid cursor at
/// or after that entry on success. Choice and lookahead may restore cursors
/// internally. Unbounded repetition additionally requires strict advancement.
/// These are implementation contracts, not properties enforced by this trait:
/// proofs of custom parsers and callbacks must establish their own contracts,
/// including termination and freedom from panics. Callbacks may have effects;
/// restoring a cursor does not undo them.
pub trait Parser<'input> {
    type Output;

    /// Parse with explicit byte order. Exhaustion returns `UnexpectedEnd`.
    /// Children receive the same order unless wrapped in `WithByteOrder`.
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError>;

    /// Parse with big byte order. Use `End` to require consuming the whole buffer.
    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parse_with(input, cursor, ByteOrder::Big)
    }
}

/// Reuse a parser by reference, with a lifetime independent of the input.
impl<'input, P: Parser<'input>> Parser<'input> for &P {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        P::parse_with(*self, input, cursor, byte_order)
    }
}
