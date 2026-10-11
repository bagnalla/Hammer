use super::super::{ByteOrder, Cursor, ParseError, Parser};

/// Run a child with the configured byte order, without implicit alignment.
/// The enclosing parser's order is unchanged for subsequent children.
#[derive(Clone, Copy)]
pub struct WithByteOrder<P> {
    pub parser: P,
    pub byte_order: ByteOrder,
}

impl<'input, P: Parser<'input>> Parser<'input> for WithByteOrder<P> {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        _: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parser.parse_with(input, cursor, self.byte_order)
    }
}
