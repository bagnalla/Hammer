use super::super::{Cursor, Eval, Grammar, InputStatus, ParseContext, ParseError, ParseOutcome};

// Advance using the input length alone: skipping never reads the input bytes.
// Split the count before adding so neither an absolute bit position nor
// `bits + cursor.bit` has to fit in usize. Check the remaining byte count before
// adding to the cursor; the final bit offset must also fit at end-of-input.
fn advance_cursor(length: usize, cursor: Cursor, bits: usize) -> Result<Cursor, ParseError> {
    if cursor.bit >= 8 || cursor.byte > length || (cursor.byte == length && cursor.bit != 0) {
        return Err(ParseError::InvalidCursor);
    }
    let tail = cursor.bit + (bits % 8) as u8;
    let bytes = bits / 8 + (tail / 8) as usize;
    let bit = tail % 8;
    if bytes > length - cursor.byte {
        return Err(ParseError::UnexpectedEnd);
    }
    let byte = cursor.byte + bytes;
    if byte == length && bit != 0 {
        return Err(ParseError::UnexpectedEnd);
    }
    Ok(Cursor { byte, bit })
}

#[cfg(test)]
mod position_boundary_tests {
    use super::{advance_cursor, Cursor, ParseError};

    #[test]
    fn virtual_lengths_cover_machine_limits_without_allocating_input() {
        let max = usize::MAX;
        let points = [0, 1, 7, 8, max / 8 - 1, max / 8, max / 8 + 1, max - 1, max];
        for length in points {
            for byte in points.into_iter().chain([length.saturating_sub(1), length]) {
                for bit in (0..=9).chain([u8::MAX]) {
                    let cursor = Cursor { byte, bit };
                    for bits in points.into_iter().chain([2, 6, 9, 63, 64, 65]) {
                        let start = byte as u128 * 8 + u128::from(bit);
                        let end = length as u128 * 8;
                        let target = start + bits as u128;
                        let expected = if bit >= 8 || start > end {
                            Err(ParseError::InvalidCursor)
                        } else if target > end {
                            Err(ParseError::UnexpectedEnd)
                        } else {
                            Ok(Cursor {
                                byte: (target / 8) as usize,
                                bit: (target % 8) as u8,
                            })
                        };
                        assert_eq!(
                            advance_cursor(length, cursor, bits),
                            expected,
                            "length={length} cursor={cursor:?} bits={bits}"
                        );
                    }
                }
            }
        }
    }
}

/// Discard exactly the configured number of bits, returning `()`.
///
/// Corresponds to Hammer's `h_skip`. Starts may be unaligned; no padding is
/// inserted, and counts are not limited to 64. Advancement takes constant time
/// without reading input bytes or allocating. Every `usize` count is valid.
/// Parsing validates the cursor even when skipping zero bits. Insufficient
/// input returns `NeedMore` on partial input or `UnexpectedEnd` on final input.
///
/// ```
/// use rusthammer::{Cursor, Parser, SkipBits};
/// const RESERVED: SkipBits = SkipBits::new(11);
/// assert_eq!(RESERVED.parse(&[0; 2], Cursor { byte: 0, bit: 3 }),
///     Ok((Cursor { byte: 1, bit: 6 }, ())));
/// ```
///
/// ```compile_fail,E0451
/// let parser = rusthammer::SkipBits { bits: 8 };
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SkipBits {
    bits: usize,
}

impl SkipBits {
    /// Construct a skip parser. Every count is valid, including zero.
    pub const fn new(bits: usize) -> Self {
        Self { bits }
    }

    /// The number of bits to discard on success.
    pub const fn bits(&self) -> usize {
        self.bits
    }
}

impl<'input> Grammar<'input> for SkipBits {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for SkipBits {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        let result = match advance_cursor(input.len(), cursor, self.bits) {
            Ok(next) => Ok((next, ())),
            Err(error) => Err(error),
        };
        context.status.classify(result)
    }
}

/// Report the current validated cursor without consuming input.
///
/// Corresponds to Hammer's `h_tell`, with a byte-and-bit `Cursor` output instead
/// of an absolute bit count. This avoids overflowing a byte-to-bit conversion.
/// Returns `InvalidCursor` for invalid positions; every valid position succeeds
/// immediately on both partial and final input, including canonical end-of-input.
///
/// ```
/// use rusthammer::{Cursor, Parser, Tell};
/// let cursor = Cursor { byte: 0, bit: 3 };
/// assert_eq!(Tell.parse(&[0], cursor), Ok((cursor, cursor)));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tell;

impl<'input> Grammar<'input> for Tell {
    type Output = Cursor;
}

impl<'input, Backend> Eval<'input, Backend> for Tell {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        _context: ParseContext,
    ) -> ParseOutcome<Cursor> {
        match advance_cursor(input.len(), cursor, 0) {
            Ok(next) => ParseOutcome::Success(next, next),
            Err(error) => ParseOutcome::Error(error),
        }
    }
}

/// Require canonical end-of-input, consuming nothing. Remaining bits, including
/// zero padding, produce `TrailingInput`; malformed cursors produce `InvalidCursor`.
/// At the boundary of partial input, return `NeedMore` until finality is known.
#[derive(Clone, Copy)]
pub struct End;

impl<'input> Grammar<'input> for End {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for End {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        if cursor.bit >= 8
            || cursor.byte > input.len()
            || (cursor.byte == input.len() && cursor.bit != 0)
        {
            return ParseOutcome::Error(ParseError::InvalidCursor);
        }
        if cursor.byte == input.len() {
            match context.status {
                InputStatus::Final => ParseOutcome::Success(cursor, ()),
                InputStatus::Partial => ParseOutcome::NeedMore,
            }
        } else {
            ParseOutcome::Error(ParseError::TrailingInput)
        }
    }
}
