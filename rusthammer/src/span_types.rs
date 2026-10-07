use super::{BitOrder, Cursor, ParseError};

/// A validated region of the original input, including partial boundary bytes.
///
/// Positions count bits consumed from the end of each byte selected by
/// `bit_order`. The span retains that direction after parsing returns. It
/// identifies source bits, not the field grouping or internal ordering scopes
/// used to decode them. Byte order does not affect the source region.
///
/// Both endpoints are normalized, within `input`, and in forward order; equal
/// endpoints describe an empty span. Fields are private to preserve those bounds.
/// Use [`Self::as_bytes`] for a borrowed byte view when both endpoints are aligned.
/// Partial-byte spans expose their input, positions, and direction instead.
/// No absolute machine-sized bit count is needed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitSpan<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
    bit_order: BitOrder,
}

pub(crate) fn span_cursor_valid(length: usize, cursor: Cursor) -> bool {
    cursor.bit < 8 && (cursor.byte < length || (cursor.byte == length && cursor.bit == 0))
}

impl<'input> BitSpan<'input> {
    /// Validate a region. Invalid endpoints yield `InvalidCursor` before checking
    /// for a backward span (`NonProgress`). Empty and unaligned spans are valid.
    pub fn new(
        input: &'input [u8],
        start: Cursor,
        end: Cursor,
        bit_order: BitOrder,
    ) -> Result<Self, ParseError> {
        if !span_cursor_valid(input.len(), start) || !span_cursor_valid(input.len(), end) {
            return Err(ParseError::InvalidCursor);
        }
        if end.byte < start.byte || (end.byte == start.byte && end.bit < start.bit) {
            return Err(ParseError::NonProgress);
        }
        Ok(Self {
            input,
            start,
            end,
            bit_order,
        })
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

    /// Direction used to identify the selected bits in partial boundary bytes.
    pub const fn bit_order(&self) -> BitOrder {
        self.bit_order
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
