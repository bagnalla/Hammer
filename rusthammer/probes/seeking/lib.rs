//! Private seeking candidate using the real RustHammer traits and combinators.
#![no_std]

use rusthammer::{Cursor, Eval, Grammar, InputStatus, ParseContext, ParseError, ParseOutcome};

// This probe-local error would be ConfigError::InvalidBitOffset in the library.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeekConfigError {
    InvalidBitOffset,
}

#[derive(Clone, Copy)]
enum Target {
    Absolute(Cursor),
    Relative(isize),
    End(isize),
}

#[derive(Clone, Copy)]
pub struct Seek {
    target: Target,
}

impl Seek {
    pub const fn to(target: Cursor) -> Result<Self, SeekConfigError> {
        if target.bit >= 8 {
            Err(SeekConfigError::InvalidBitOffset)
        } else {
            Ok(Self {
                target: Target::Absolute(target),
            })
        }
    }

    pub const fn relative(offset_bits: isize) -> Self {
        Self {
            target: Target::Relative(offset_bits),
        }
    }

    pub const fn from_end(offset_bits: isize) -> Self {
        Self {
            target: Target::End(offset_bits),
        }
    }
}

fn valid(length: usize, cursor: Cursor) -> bool {
    cursor.bit < 8 && (cursor.byte < length || (cursor.byte == length && cursor.bit == 0))
}

// Accepts only a validated base. The signed minimum is handled without negating it.
fn shift(length: usize, base: Cursor, offset: isize) -> Result<Cursor, ParseError> {
    if offset < 0 {
        let magnitude = (-(offset + 1)) as usize + 1;
        let whole = magnitude / 8;
        let tail = (magnitude % 8) as u8;
        let (bytes, bit) = if tail > base.bit {
            (whole + 1, base.bit + 8 - tail)
        } else {
            (whole, base.bit - tail)
        };
        if bytes > base.byte {
            return Err(ParseError::Mismatch);
        }
        Ok(Cursor {
            byte: base.byte - bytes,
            bit,
        })
    } else {
        let magnitude = offset as usize;
        let tail = base.bit + (magnitude % 8) as u8;
        let bytes = magnitude / 8 + (tail / 8) as usize;
        let bit = tail % 8;
        if bytes > length - base.byte {
            return Err(ParseError::UnexpectedEnd);
        }
        let byte = base.byte + bytes;
        if byte == length && bit != 0 {
            return Err(ParseError::UnexpectedEnd);
        }
        Ok(Cursor { byte, bit })
    }
}

// Length-only entry permits machine-limit tests without allocating huge buffers.
pub fn seek_position(
    parser: Seek,
    length: usize,
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<Cursor> {
    if !valid(length, cursor) {
        return ParseOutcome::Error(ParseError::InvalidCursor);
    }
    let result = match parser.target {
        Target::Absolute(target) => {
            if valid(length, target) {
                Ok(target)
            } else {
                Err(ParseError::UnexpectedEnd)
            }
        }
        Target::Relative(offset) => shift(length, cursor, offset),
        Target::End(offset) => match status {
            InputStatus::Partial => return ParseOutcome::NeedMore,
            InputStatus::Final => shift(
                length,
                Cursor {
                    byte: length,
                    bit: 0,
                },
                offset,
            ),
        },
    };
    match result {
        Ok(next) => ParseOutcome::Success(next, next),
        Err(ParseError::UnexpectedEnd) => match status {
            InputStatus::Partial => ParseOutcome::NeedMore,
            InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
        },
        Err(error) => ParseOutcome::Error(error),
    }
}

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

pub fn run(
    parser: Seek,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<Cursor> {
    use rusthammer::Parser;
    parser.parse_with(input, cursor, context)
}
