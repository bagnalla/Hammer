use super::super::{BitSpan, ByteOrder, Cursor, ParseError, Parser};

use super::super::span_types::span_cursor_valid;

/// Retain a child's decoded value together with its matched input span.
///
/// The output is `(P::Output, BitSpan<'input>)`. This wrapper annotates only its
/// own result; nested values acquire spans only where explicitly wrapped.
/// The starting cursor is validated before the child runs. On success, the
/// ending cursor is validated and backward movement rejected with `NonProgress`.
/// Empty matches are allowed. Child errors propagate unchanged.
///
/// Custom children must obey the parser contract: endpoint checks cannot
/// establish which bits an arbitrary parser inspected. Lookahead contributes
/// no consumed input, and therefore has an empty span when wrapped.
/// Skipped bits are included; speculative lookahead beyond the endpoint is not.
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

impl<'input, P: Parser<'input>> Parser<'input> for WithSpan<P> {
    type Output = (P::Output, BitSpan<'input>);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        if !span_cursor_valid(input.len(), cursor) {
            return Err(ParseError::InvalidCursor);
        }
        match self.parser.parse_with(input, cursor, byte_order) {
            Ok(parsed) => {
                let (next, value) = parsed;
                let span = match BitSpan::new(input, cursor, next) {
                    Ok(span) => span,
                    Err(error) => return Err(error),
                };
                Ok((next, (value, span)))
            }
            Err(error) => Err(error),
        }
    }
}

/// Return the matched input span, discarding the child's decoded value.
///
/// Uses the same validation and consumption rules as [`WithSpan`]. The child
/// still runs and constructs its output, including allocations and callback
/// effects; that value is then dropped.
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

impl<'input, P: Parser<'input>> Parser<'input> for Recognize<P> {
    type Output = BitSpan<'input>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let spanned = WithSpan {
            parser: &self.parser,
        };
        match spanned.parse_with(input, cursor, byte_order) {
            // Move the complete tuple before destructuring for dependency MIR;
            // see probes/direct_v1/README.md.
            Ok(parsed) => {
                let (next, output) = parsed;
                let (_, span) = output;
                Ok((next, span))
            }
            Err(error) => Err(error),
        }
    }
}
