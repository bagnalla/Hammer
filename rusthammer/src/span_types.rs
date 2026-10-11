use super::{Cursor, ParseError};

/// A validated region of the original input, including partial boundary bytes.
///
/// Positions count high-first bits. Byte order does not affect the source region.
/// Both endpoints are normalized, within `input`, and in forward order; equal
/// endpoints describe an empty span. Fields are private to preserve those bounds.
/// Use [`Self::as_bytes`] for a borrowed view when both endpoints are aligned.
/// Partial-byte spans expose their input and positions. No absolute machine-sized
/// bit count is needed. The interval includes skipped input; it does not record
/// speculative reads performed by lookahead or rejected alternatives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitSpan<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
}

pub(crate) fn span_cursor_valid(length: usize, cursor: Cursor) -> bool {
    cursor.bit < 8 && (cursor.byte < length || (cursor.byte == length && cursor.bit == 0))
}

impl<'input> BitSpan<'input> {
    /// Validate a region. Invalid endpoints yield `InvalidCursor` before checking
    /// for a backward span (`NonProgress`). Empty and unaligned spans are valid.
    pub fn new(input: &'input [u8], start: Cursor, end: Cursor) -> Result<Self, ParseError> {
        if !span_cursor_valid(input.len(), start) || !span_cursor_valid(input.len(), end) {
            return Err(ParseError::InvalidCursor);
        }
        if end.byte < start.byte || (end.byte == start.byte && end.bit < start.bit) {
            return Err(ParseError::NonProgress);
        }
        Ok(Self { input, start, end })
    }

    /// The complete input buffer from which this region was selected.
    pub const fn input(&self) -> &'input [u8] {
        self.input
    }

    pub const fn start(&self) -> Cursor {
        self.start
    }

    pub const fn end(&self) -> Cursor {
        self.end
    }

    pub fn is_empty(&self) -> bool {
        self.start.byte == self.end.byte && self.start.bit == self.end.bit
    }

    /// Original source bytes, without reordering or copying, if both endpoints
    /// are aligned. An aligned empty span returns `Some(&[])`; an unaligned
    /// empty span returns `None`. The borrow lasts as long as the original input.
    pub fn as_bytes(&self) -> Option<&'input [u8]> {
        if self.start.bit != 0 || self.end.bit != 0 {
            return None;
        }
        Some(&self.input[self.start.byte..self.end.byte])
    }
}
