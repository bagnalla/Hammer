use super::super::{
    ConfigError, Cursor, Eval, Grammar, InputStatus, ParseContext, ParseError, ParseOutcome,
};

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SeekTarget {
    Absolute(Cursor),
    Relative(isize),
    End(isize),
}

/// Reposition within the current input, returning the destination [`Cursor`].
///
/// Corresponds to Hammer's `h_seek`. Absolute targets use byte-and-bit cursors;
/// relative offsets are signed bit counts. Seeking reads no input bytes and does
/// not allocate or modify backend state. Every invocation validates its entry
/// cursor, including absolute seeks and zero offsets. A destination before the
/// start yields recoverable `Mismatch`; a destination beyond available input
/// yields `NeedMore` on partial input or `UnexpectedEnd` on final input.
/// End-relative seeks wait for finality before calculating their destination.
///
/// Coordinates are relative to the supplied input slice and interpreted in the
/// active bit direction. Seeking preserves the ordering context; a saved cursor
/// does not restore another input buffer or an earlier bit direction.
///
/// Bounded repetition may move backward. Unbounded repetition requires each
/// complete iteration to advance. `WithSpan` and `Recognize` describe only the
/// interval between their endpoints and reject a net backward result. Skipped
/// bytes may lie inside a span; bytes inspected during an excursion may lie outside.
///
/// ```
/// use rusthammer::{Cursor, Parser, Right, Seek, Byte};
/// let field = Right { first: Seek::from_end(-8), second: Byte };
/// assert_eq!(field.parse(b"abc", Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, b'c')));
/// ```
///
/// ```compile_fail,E0616
/// let parser = rusthammer::Seek::relative(1);
/// let _ = parser.target;
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Seek {
    target: SeekTarget,
}

impl Seek {
    /// Construct an absolute destination. Only `bit < 8` is required here;
    /// bounds against the actual input are checked when parsing.
    /// An invalid bit offset returns `ConfigError::InvalidBitOffset`.
    pub const fn to(target: Cursor) -> Result<Self, ConfigError> {
        if target.bit >= 8 {
            Err(ConfigError::InvalidBitOffset)
        } else {
            Ok(Self {
                target: SeekTarget::Absolute(target),
            })
        }
    }

    /// Move by a signed number of bits from the invocation's entry cursor.
    /// Every `isize` offset is valid configuration, including `isize::MIN`.
    pub const fn relative(offset_bits: isize) -> Self {
        Self {
            target: SeekTarget::Relative(offset_bits),
        }
    }

    /// Move by a signed number of bits from the final input boundary.
    /// Partial input returns `NeedMore`, even for zero or positive offsets.
    pub const fn from_end(offset_bits: isize) -> Self {
        Self {
            target: SeekTarget::End(offset_bits),
        }
    }
}

// Backward counterpart of advance_cursor. Both are total on raw cursors and
// arbitrary usize counts; no absolute machine bit position is formed.
fn retreat_cursor(length: usize, cursor: Cursor, bits: usize) -> Result<Cursor, ParseError> {
    let cursor = advance_cursor(length, cursor, 0)?;
    let whole = bits / 8;
    let tail = (bits % 8) as u8;
    let (bytes, bit) = if tail > cursor.bit {
        (whole + 1, cursor.bit + 8 - tail)
    } else {
        (whole, cursor.bit - tail)
    };
    if bytes > cursor.byte {
        return Err(ParseError::Mismatch);
    }
    Ok(Cursor {
        byte: cursor.byte - bytes,
        bit,
    })
}

fn offset_cursor(length: usize, cursor: Cursor, offset: isize) -> Result<Cursor, ParseError> {
    if offset < 0 {
        // Negating the offset itself would overflow at isize::MIN.
        let magnitude = (-(offset + 1)) as usize + 1;
        retreat_cursor(length, cursor, magnitude)
    } else {
        advance_cursor(length, cursor, offset as usize)
    }
}

fn seek_position(
    parser: Seek,
    length: usize,
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<Cursor> {
    if let Err(error) = advance_cursor(length, cursor, 0) {
        return ParseOutcome::Error(error);
    }
    let result = match parser.target {
        SeekTarget::Absolute(target) => match advance_cursor(length, target, 0) {
            Ok(next) => Ok(next),
            Err(_) => Err(ParseError::UnexpectedEnd),
        },
        SeekTarget::Relative(offset) => offset_cursor(length, cursor, offset),
        SeekTarget::End(offset) => match status {
            InputStatus::Partial => return ParseOutcome::NeedMore,
            InputStatus::Final => offset_cursor(
                length,
                Cursor {
                    byte: length,
                    bit: 0,
                },
                offset,
            ),
        },
    };
    let result = match result {
        Ok(next) => Ok((next, next)),
        Err(error) => Err(error),
    };
    status.classify(result)
}

#[cfg(test)]
#[path = "position_seek_tests.rs"]
mod seek_boundary_tests;

impl<'input> Grammar<'input> for Seek {
    type Output = Cursor;
}

impl<'input, Backend> Eval<'input, Backend> for Seek {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Cursor> {
        seek_position(*self, input.len(), cursor, context.status)
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
