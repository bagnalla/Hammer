//! Extraction regression fixture using RustHammer as an ordinary Cargo dependency.
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

use rusthammer::{
    BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Bind, Bit, Bits, ButNot, Byte, ByteIn, ByteNotIn,
    BytePattern, ConfigError, Cursor, Difference, End, FoldRepeat, Ignore, InputStatus, IntRange,
    Left, Literal, Map, Middle, ParseError, ParseOutcome, Parser, Right, Seq, SignedBits, SkipBits,
    TakeAligned, Tell, TryMap, Xor, I8,
};

pub fn restricted_payload(
    input: &[u8],
    count: usize,
    width: u8,
    status: InputStatus,
) -> Result<ParseOutcome<&[u8]>, ConfigError> {
    let parser = ButNot {
        first: TakeAligned { count },
        second: Bits::new(width)?,
    };
    Ok(parser.clone().parse_with(input, Cursor::start(), status))
}

pub fn difference_pattern<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    status: InputStatus,
) -> ParseOutcome<&'pattern [u8]> {
    let first = BytePattern::new(pattern);
    Difference {
        first: &first,
        second: Byte,
    }
    .clone()
    .parse_with(input, Cursor::start(), status)
}

pub fn exclusive_patterns<'pattern>(
    first: &'pattern [u8],
    second: &'pattern [u8],
    input: &[u8],
    status: InputStatus,
) -> ParseOutcome<&'pattern [u8]> {
    Xor {
        first: BytePattern::new(first),
        second: BytePattern::new(second),
    }
    .clone()
    .parse_with(input, Cursor::start(), status)
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExclusiveValue {
    Digit(u8),
    Word(u16),
}

/// Different child values explicitly mapped into an owned, non-Clone enum.
pub fn exclusive_value(input: &[u8], status: InputStatus) -> ParseOutcome<ExclusiveValue> {
    Xor {
        first: Map {
            parser: ByteIn::new(b"0123456789"),
            map: |digit| ExclusiveValue::Digit(digit),
        },
        second: Map {
            parser: Right {
                first: BytePattern::new(b"#"),
                second: BeU16,
            },
            map: |word| ExclusiveValue::Word(word),
        },
    }
    .parse_with(input, Cursor::start(), status)
}

pub fn complete_matches(input: &[u8]) -> [Result<(Cursor, u8), ParseError>; 3] {
    let first = ByteIn::new(b"ab");
    let second = ByteIn::new(b"b");
    [
        ButNot {
            first: &first,
            second: &second,
        }
        .parse(input, Cursor::start()),
        Difference {
            first: &first,
            second: &second,
        }
        .parse(input, Cursor::start()),
        Xor {
            first: &first,
            second: &second,
        }
        .parse(input, Cursor::start()),
    ]
}

pub fn skipped_position(
    input: &[u8],
    cursor: Cursor,
    bits: usize,
    status: InputStatus,
) -> ParseOutcome<Cursor> {
    let skip = SkipBits::new(bits);
    Right {
        first: &skip,
        second: Tell,
    }
    .parse_with(input, cursor, status)
}

pub fn reported_position(
    input: &[u8],
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<Cursor> {
    Tell.parse_with(input, cursor, status)
}

pub fn complete_skip(
    parser: &SkipBits,
    input: &[u8],
    cursor: Cursor,
) -> Result<(Cursor, ()), ParseError> {
    parser.parse(input, cursor)
}

pub fn skip_configuration(bits: usize) -> usize {
    SkipBits::new(bits).clone().bits()
}

pub fn byte_in(
    bytes: &[u8],
    input: &[u8],
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<u8> {
    ByteIn::new(bytes).parse_with(input, cursor, status)
}

pub fn byte_not_in(
    bytes: &[u8],
    input: &[u8],
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<u8> {
    ByteNotIn::new(bytes).parse_with(input, cursor, status)
}

/// Independently constructed bitmaps compose through a reference and a clone.
pub fn byte_set_pair(
    allowed: &[u8],
    excluded: &[u8],
    input: &[u8],
    status: InputStatus,
) -> ParseOutcome<(u8, u8)> {
    let first = ByteIn::new(allowed);
    let second = ByteNotIn::new(excluded);
    Seq {
        first: &first,
        second: second.clone(),
    }
    .parse_with(input, Cursor::start(), status)
}

pub fn complete_byte_set(
    parser: &ByteNotIn,
    input: &[u8],
    cursor: Cursor,
) -> Result<(Cursor, u8), ParseError> {
    parser.parse(input, cursor)
}

/// The returned parser owns its set and can outlive the construction slice.
pub fn owned_byte_set(bytes: &[u8]) -> ByteIn {
    ByteIn::new(bytes)
}

pub fn byte_set_accepts(allowed: &[u8], excluded: &[u8], byte: u8) -> (bool, bool) {
    (
        ByteIn::new(allowed).accepts(byte),
        ByteNotIn::new(excluded).accepts(byte),
    )
}

pub fn ranged_u64(
    input: &[u8],
    lower: u64,
    upper: u64,
    status: InputStatus,
) -> Result<ParseOutcome<u64>, ConfigError> {
    let range = IntRange::new(BeU64, lower, upper)?;
    Ok(range.parse_with(input, Cursor::start(), status))
}

/// A borrowed child, typed signed bounds, and a byte range compose as usual.
pub fn ranged_pair(
    input: &[u8],
    lower: i16,
    upper: i16,
    status: InputStatus,
) -> Result<ParseOutcome<(i16, u8)>, ConfigError> {
    let signed = BeI16;
    let parser = Seq {
        first: IntRange::new(&signed, lower, upper)?,
        second: IntRange::new(Byte, b'0', b'9')?,
    };
    Ok(parser.parse_with(input, Cursor::start(), status))
}

/// An integer newtype deliberately implementing neither Copy nor Clone.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Count {
    pub value: u16,
}

pub fn ranged_count(
    input: &[u8],
    lower: u16,
    upper: u16,
    status: InputStatus,
) -> Result<ParseOutcome<Count>, ConfigError> {
    let child = Map {
        parser: BeU16,
        map: |value| Count { value },
    };
    let range = IntRange::new(child, Count { value: lower }, Count { value: upper })?;
    Ok(range.parse_with(input, Cursor::start(), status))
}

pub fn complete_range(
    input: &[u8],
    cursor: Cursor,
    range: &IntRange<BeU16, u16>,
) -> Result<(Cursor, u16), ParseError> {
    range.parse(input, cursor)
}

/// The fixed-width output types survive sequencing and a shared parser reference.
pub fn integers16(input: &[u8], cursor: Cursor, status: InputStatus) -> ParseOutcome<(u16, i16)> {
    let unsigned = BeU16;
    Seq {
        first: &unsigned,
        second: BeI16,
    }
    .parse_with(input, cursor, status)
}

pub fn integers32(input: &[u8], cursor: Cursor, status: InputStatus) -> ParseOutcome<(u32, i32)> {
    Seq {
        first: BeU32,
        second: BeI32,
    }
    .parse_with(input, cursor, status)
}

pub fn integers64(input: &[u8], cursor: Cursor, status: InputStatus) -> ParseOutcome<(u64, i64)> {
    Seq {
        first: BeU64,
        second: BeI64,
    }
    .parse_with(input, cursor, status)
}

/// Exercise the default complete-input method with the signed byte output.
pub fn complete_i8(input: &[u8], cursor: Cursor) -> Result<(Cursor, i8), ParseError> {
    I8.parse(input, cursor)
}

/// Dynamic construction preserves configuration errors separately from parsing.
pub fn signed_field(
    input: &[u8],
    cursor: Cursor,
    width: u8,
    status: InputStatus,
) -> Result<ParseOutcome<i64>, ConfigError> {
    let parser = SignedBits::new(width)?;
    Ok(parser.parse_with(input, cursor, status))
}

/// A validated signed parser composes with an unsigned byte through a reference.
pub fn signed_and_unsigned(
    input: &[u8],
    cursor: Cursor,
    signed: &SignedBits,
    status: InputStatus,
) -> ParseOutcome<(i64, u8)> {
    Seq {
        first: signed,
        second: Byte,
    }
    .parse_with(input, cursor, status)
}

/// Input, pattern, and parser references have independent lifetimes.
pub fn matched_pattern<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<&'pattern [u8]> {
    let parser = BytePattern::new(pattern);
    let borrowed = &parser;
    borrowed.parse_with(input, cursor, status)
}

/// Both borrowing sources remain distinct through typed sequencing.
pub fn pattern_and_input<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    status: InputStatus,
) -> ParseOutcome<((&'pattern [u8], u8), &'input [u8])> {
    Seq {
        first: Seq {
            first: BytePattern::new(pattern),
            second: Byte,
        },
        second: TakeAligned { count: 1 },
    }
    .parse_with(input, Cursor::start(), status)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Flag {
    pub value: bool,
}

/// A captured fallible callback constructs an owned, non-Clone output.
pub fn checked_flag(input: &[u8], expected: bool, status: InputStatus) -> ParseOutcome<Flag> {
    let parser = TryMap {
        parser: Bit,
        map: |value| {
            if value == expected {
                Ok(Flag { value })
            } else {
                Err(())
            }
        },
    };
    parser.parse_with(input, Cursor::start(), status)
}

/// One flag bit, seven ignored bits, then a bracketed two-byte borrowed payload.
pub fn packet(input: &[u8], status: InputStatus) -> ParseOutcome<(bool, &[u8])> {
    let parser = Left {
        first: Seq {
            first: Bit,
            second: Right {
                first: Ignore {
                    parser: Bits::new(7).unwrap(),
                },
                second: Middle {
                    left: Literal::new(8, u64::from(b'[')).unwrap(),
                    parser: TakeAligned { count: 2 },
                    right: Literal::new(8, u64::from(b']')).unwrap(),
                },
            },
        },
        second: End,
    };
    parser.parse_with(input, Cursor::start(), status)
}

/// Also exercise the default complete-input trait method across the crate boundary.
pub fn complete_bit(input: &[u8]) -> Result<(Cursor, bool), ParseError> {
    Bit.parse(input, Cursor::start())
}

/// A checked input value configures a parser returning a borrowed slice.
pub fn bound_payload(input: &[u8], limit: u64, status: InputStatus) -> ParseOutcome<&[u8]> {
    Bind {
        parser: TryMap {
            parser: Bits::new(8).unwrap(),
            map: |length| {
                if length <= limit && length <= 255 {
                    Ok(length as usize)
                } else {
                    Err(())
                }
            },
        },
        then: |count| TakeAligned { count },
    }
    .parse_with(input, Cursor::start(), status)
}

/// The factory reads a borrowed first output to construct an owned parser.
pub fn bound_literal(input: &[u8], status: InputStatus) -> ParseOutcome<u64> {
    Bind {
        parser: TakeAligned { count: 1 },
        then: |byte: &[u8]| Literal::new(8, u64::from(byte[0])).unwrap(),
    }
    .parse_with(input, Cursor::start(), status)
}

/// A constructed repetition owns a copy of its captured child parser.
#[cfg(feature = "alloc")]
pub fn bound_blocks(input: &[u8], status: InputStatus) -> ParseOutcome<alloc::vec::Vec<&[u8]>> {
    let element = TakeAligned { count: 1 };
    Bind {
        parser: TryMap {
            parser: Bits::new(8).unwrap(),
            map: |count| {
                if count <= 255 {
                    Ok(count as usize)
                } else {
                    Err(())
                }
            },
        },
        then: |count| rusthammer::Repeat::exact(element, count),
    }
    .parse_with(input, Cursor::start(), status)
}

/// A factory may also return an existing parser by shared reference.
pub fn bound_reference(input: &[u8], status: InputStatus) -> ParseOutcome<&[u8]> {
    let body = TakeAligned { count: 1 };
    Bind {
        parser: Bits::new(8).unwrap(),
        then: |_| &body,
    }
    .parse_with(input, Cursor::start(), status)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Checksum {
    pub value: u64,
}

/// Captured initialization, borrowed child outputs, and an owned non-Clone accumulator.
pub fn folded_checksum(
    input: &[u8],
    count: usize,
    seed: u64,
    status: InputStatus,
) -> ParseOutcome<Checksum> {
    FoldRepeat::exact(
        TakeAligned { count: 1 },
        count,
        || Checksum { value: seed },
        |sum: Checksum, byte: &[u8]| Checksum {
            value: sum.value ^ u64::from(byte[0]),
        },
    )
    .parse_with(input, Cursor::start(), status)
}

pub fn leading_ones_count(input: &[u8], status: InputStatus) -> ParseOutcome<usize> {
    FoldRepeat::at_least(
        Literal::new(1, 1).unwrap(),
        0,
        || 0usize,
        |count, _| count + 1,
    )
    .parse_with(input, Cursor::start(), status)
}

/// Both item and discarded separator outputs borrow the input.
#[cfg(feature = "alloc")]
pub fn separated_blocks(
    input: &[u8],
    count: usize,
    status: InputStatus,
) -> ParseOutcome<alloc::vec::Vec<&[u8]>> {
    rusthammer::SepBy::exact(TakeAligned { count: 1 }, TakeAligned { count: 1 }, count).parse_with(
        input,
        Cursor::start(),
        status,
    )
}

pub struct Separator;

/// A non-Clone separator output is discarded; borrowed items enter an owned fold.
pub fn separated_checksum(input: &[u8], seed: u64, status: InputStatus) -> ParseOutcome<Checksum> {
    let separator = rusthammer::Map {
        parser: Literal::new(8, 44).unwrap(),
        map: |_| Separator,
    };
    rusthammer::FoldSepBy::at_least(
        TakeAligned { count: 1 },
        separator,
        1,
        || Checksum { value: seed },
        |sum: Checksum, byte: &[u8]| Checksum {
            value: sum.value ^ u64::from(byte[0]),
        },
    )
    .parse_with(input, Cursor::start(), status)
}

#[cfg(feature = "alloc")]
pub fn blocks(
    input: &[u8],
    count: usize,
    status: InputStatus,
) -> ParseOutcome<alloc::vec::Vec<&[u8]>> {
    rusthammer::Repeat::exact(TakeAligned { count: 1 }, count).parse_with(
        input,
        Cursor::start(),
        status,
    )
}

#[cfg(feature = "alloc")]
pub fn leading_ones(input: &[u8], status: InputStatus) -> ParseOutcome<alloc::vec::Vec<u64>> {
    rusthammer::Repeat::at_least(Literal::new(1, 1).unwrap(), 0).parse_with(
        input,
        Cursor::start(),
        status,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_keep_borrows_types_lengths_and_finality_across_crates() {
        let input = [1, 2];
        let ParseOutcome::Success(next, payload) =
            restricted_payload(&input, 2, 8, InputStatus::Final).unwrap()
        else {
            panic!("expected payload");
        };
        assert_eq!(next, Cursor { byte: 2, bit: 0 });
        assert!(core::ptr::eq(payload, &input[..]));
        assert_eq!(
            restricted_payload(&input, 1, 8, InputStatus::Final),
            Ok(ParseOutcome::Error(ParseError::Mismatch))
        );
        assert_eq!(
            restricted_payload(&input, 1, 24, InputStatus::Partial),
            Ok(ParseOutcome::NeedMore)
        );
        assert_eq!(
            restricted_payload(&input, 1, 65, InputStatus::Final),
            Err(ConfigError::InvalidWidth)
        );
        let pattern = *b"a";
        let parsed = {
            let input = *b"a";
            difference_pattern(&pattern, &input, InputStatus::Final)
        };
        let ParseOutcome::Success(_, matched) = parsed else {
            panic!("expected pattern");
        };
        assert!(core::ptr::eq(matched, &pattern[..]));
        assert_eq!(
            exclusive_patterns(b"a", b"ab", b"a", InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            exclusive_patterns(b"a", b"ab", b"a", InputStatus::Final),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, &b"a"[..])
        );
        assert_eq!(
            exclusive_patterns(b"a", b"ab", b"ab", InputStatus::Final),
            ParseOutcome::Error(ParseError::Mismatch)
        );
        assert_eq!(
            exclusive_value(b"5", InputStatus::Final),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, ExclusiveValue::Digit(b'5'))
        );
        assert_eq!(
            exclusive_value(b"#\x12\x34", InputStatus::Final),
            ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, ExclusiveValue::Word(0x1234))
        );
        assert_eq!(
            exclusive_value(b"#\x12", InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            complete_matches(b"b"),
            [
                Err(ParseError::Mismatch),
                Ok((Cursor { byte: 1, bit: 0 }, b'b')),
                Err(ParseError::Mismatch)
            ]
        );
    }

    #[test]
    fn positions_and_dynamic_skips_cross_crate_boundaries() {
        let cursor = Cursor { byte: 0, bit: 7 };
        let end = Cursor { byte: 11, bit: 0 };
        assert_eq!(skip_configuration(usize::MAX), usize::MAX);
        assert_eq!(
            skipped_position(&[0; 11], cursor, 81, InputStatus::Partial),
            ParseOutcome::Success(end, end)
        );
        assert_eq!(
            skipped_position(&[0; 10], cursor, 81, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            skipped_position(&[0; 10], cursor, 81, InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            complete_skip(&SkipBits::new(81), &[0; 11], cursor),
            Ok((end, ()))
        );
        assert_eq!(
            complete_skip(&SkipBits::new(usize::MAX), &[0], cursor),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            reported_position(&[], Cursor::start(), InputStatus::Partial),
            ParseOutcome::Success(Cursor::start(), Cursor::start())
        );
        assert_eq!(
            reported_position(&[0], cursor, InputStatus::Final),
            ParseOutcome::Success(cursor, cursor)
        );
        let invalid = Cursor {
            byte: usize::MAX,
            bit: 0,
        };
        assert_eq!(
            reported_position(&[], invalid, InputStatus::Partial),
            ParseOutcome::Error(ParseError::InvalidCursor)
        );
        assert_eq!(
            skipped_position(&[], invalid, 0, InputStatus::Final),
            ParseOutcome::Error(ParseError::InvalidCursor)
        );
    }

    #[test]
    fn byte_sets_keep_membership_and_finality_across_crates() {
        let cursor = Cursor { byte: 0, bit: 1 };
        assert_eq!(
            byte_in(&[0x80, 0, 0x80], &[0x40, 0], cursor, InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 1, bit: 1 }, 0x80)
        );
        assert_eq!(
            byte_not_in(&[0x80], &[0x40, 0], cursor, InputStatus::Final),
            ParseOutcome::Error(ParseError::Mismatch)
        );
        for bytes in [&[][..], &[0x80][..]] {
            assert_eq!(
                byte_in(bytes, &[0x40], cursor, InputStatus::Partial),
                ParseOutcome::NeedMore
            );
            assert_eq!(
                byte_not_in(bytes, &[0x40], cursor, InputStatus::Final),
                ParseOutcome::Error(ParseError::UnexpectedEnd)
            );
        }
        assert_eq!(
            byte_in(&[], &[], Cursor { byte: 0, bit: 1 }, InputStatus::Partial),
            ParseOutcome::Error(ParseError::InvalidCursor)
        );
    }

    #[test]
    fn byte_set_outputs_outlive_the_input_sets_and_parser() {
        let owned = {
            let mut bytes = [0, 128, 255];
            let parser = owned_byte_set(&bytes);
            bytes.fill(1);
            parser
        };
        for byte in 0..=255 {
            assert_eq!(owned.accepts(byte), byte == 0 || byte == 128 || byte == 255);
            assert_eq!(
                byte_set_accepts(&[0, 128, 255], &[0, 128, 255], byte),
                (owned.accepts(byte), !owned.accepts(byte))
            );
        }
        let output = {
            let allowed = [0, 255, 0];
            let excluded = [b'\r', b'\n'];
            let input = [255, b'x'];
            byte_set_pair(&allowed, &excluded, &input, InputStatus::Final)
        };
        assert_eq!(
            output,
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, (255, b'x'))
        );
        let parser = ByteNotIn::new(b"\r\n");
        assert_eq!(
            complete_byte_set(&parser, b"x", Cursor::start()),
            Ok((Cursor { byte: 1, bit: 0 }, b'x'))
        );
    }

    #[test]
    fn typed_ranges_keep_bounds_finality_and_rejection_across_crates() {
        assert_eq!(
            ranged_u64(&[], 2, 1, InputStatus::Partial),
            Err(ConfigError::InvalidBounds)
        );
        assert_eq!(
            ranged_u64(&[0xff; 8], 1 << 63, u64::MAX, InputStatus::Partial),
            Ok(ParseOutcome::Success(Cursor { byte: 8, bit: 0 }, u64::MAX))
        );
        assert_eq!(
            ranged_u64(&[0xff; 7], 0, 100, InputStatus::Partial),
            Ok(ParseOutcome::NeedMore)
        );
        assert_eq!(
            ranged_u64(&[0xff; 7], 0, 100, InputStatus::Final),
            Ok(ParseOutcome::Error(ParseError::UnexpectedEnd))
        );
        assert_eq!(
            ranged_pair(&[0xff, 0xfd, b'7'], -100, 100, InputStatus::Partial),
            Ok(ParseOutcome::Success(
                Cursor { byte: 3, bit: 0 },
                (-3, b'7')
            ))
        );
        assert_eq!(
            ranged_pair(&[0xff, 0xfd, b'x'], -100, 100, InputStatus::Final),
            Ok(ParseOutcome::Error(ParseError::Mismatch))
        );
        let range = IntRange::new(BeU16, 1, 4096).unwrap();
        assert_eq!(
            complete_range(&[0x01, 0], Cursor::start(), &range),
            Ok((Cursor { byte: 2, bit: 0 }, 256))
        );
    }

    #[test]
    fn ordered_newtype_bounds_and_outputs_need_no_copy_or_clone() {
        assert_eq!(
            ranged_count(&[0x01, 0], 1, 4096, InputStatus::Partial),
            Ok(ParseOutcome::Success(
                Cursor { byte: 2, bit: 0 },
                Count { value: 256 }
            ))
        );
        assert_eq!(
            ranged_count(&[0x01, 0], 1, 100, InputStatus::Final),
            Ok(ParseOutcome::Error(ParseError::Mismatch))
        );
        assert_eq!(
            ranged_count(&[], 2, 1, InputStatus::Final),
            Err(ConfigError::InvalidBounds)
        );
    }

    #[test]
    fn fixed_width_types_sequence_across_the_crate_boundary() {
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                integers16(&[0x12, 0x34, 0xff, 0xfd], Cursor::start(), status),
                ParseOutcome::Success(Cursor { byte: 4, bit: 0 }, (0x1234u16, -3i16))
            );
            assert_eq!(
                integers32(
                    &[0xff, 0xff, 0xff, 0xff, 0x80, 0, 0, 0],
                    Cursor::start(),
                    status
                ),
                ParseOutcome::Success(Cursor { byte: 8, bit: 0 }, (u32::MAX, i32::MIN))
            );
            assert_eq!(
                integers64(
                    &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0, 0, 0, 0, 0, 0, 0],
                    Cursor::start(),
                    status
                ),
                ParseOutcome::Success(Cursor { byte: 16, bit: 0 }, (u64::MAX, i64::MIN))
            );
        }
        assert_eq!(
            integers16(&[0, 0, 0], Cursor::start(), InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            integers32(&[0; 7], Cursor::start(), InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            integers64(&[0; 17], Cursor { byte: 0, bit: 1 }, InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 16, bit: 1 }, (0, 0))
        );
    }

    #[test]
    fn signed_byte_complete_method_keeps_its_native_type() {
        assert_eq!(
            complete_i8(&[0x80], Cursor::start()),
            Ok((Cursor { byte: 1, bit: 0 }, i8::MIN))
        );
        assert_eq!(
            complete_i8(&[0x7f], Cursor::start()),
            Ok((Cursor { byte: 1, bit: 0 }, i8::MAX))
        );
        assert_eq!(
            complete_i8(&[], Cursor::start()),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            complete_i8(&[], Cursor { byte: 0, bit: 1 }),
            Err(ParseError::InvalidCursor)
        );
    }

    #[test]
    fn signed_construction_and_extremes_cross_the_crate_boundary() {
        assert_eq!(
            signed_field(&[], Cursor::start(), 65, InputStatus::Final),
            Err(ConfigError::InvalidWidth)
        );
        assert_eq!(
            signed_field(&[], Cursor::start(), 0, InputStatus::Partial),
            Ok(ParseOutcome::Success(Cursor::start(), 0))
        );
        for value in [i64::MIN, -1, 0, i64::MAX] {
            assert_eq!(
                signed_field(
                    &value.to_be_bytes(),
                    Cursor::start(),
                    64,
                    InputStatus::Final
                ),
                Ok(ParseOutcome::Success(Cursor { byte: 8, bit: 0 }, value))
            );
        }
        assert_eq!(
            signed_field(&[0xff], Cursor::start(), 9, InputStatus::Partial),
            Ok(ParseOutcome::NeedMore)
        );
        assert_eq!(
            signed_field(&[0xff], Cursor::start(), 9, InputStatus::Final),
            Ok(ParseOutcome::Error(ParseError::UnexpectedEnd))
        );
    }

    #[test]
    fn signed_parser_references_sequence_with_an_unsigned_byte() {
        let signed = SignedBits::new(5).unwrap();
        // Skip three prefix bits; the signed field is 11101 (-3), then A5.
        let cursor = Cursor { byte: 0, bit: 3 };
        assert_eq!(
            signed_and_unsigned(&[0x1d, 0xa5], cursor, &signed, InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, (-3, 0xa5))
        );
    }

    #[test]
    fn pattern_output_outlives_input_and_parser() {
        let pattern = [0xab, 0xcd];
        let result = {
            let input = [0x55, 0xe6, 0x80];
            matched_pattern(
                &pattern,
                &input,
                Cursor { byte: 0, bit: 1 },
                InputStatus::Partial,
            )
        };
        assert_eq!(
            result,
            ParseOutcome::Success(Cursor { byte: 2, bit: 1 }, &pattern[..])
        );
        let ParseOutcome::Success(_, matched) = result else {
            panic!("expected match")
        };
        assert!(core::ptr::eq(matched, &pattern[..]));
    }

    #[test]
    fn sequence_retains_distinct_pattern_and_input_borrows() {
        let pattern = *b"ab";
        let input = *b"abcd";
        let result = pattern_and_input(&pattern, &input, InputStatus::Final);
        assert_eq!(
            result,
            ParseOutcome::Success(
                Cursor { byte: 4, bit: 0 },
                ((&pattern[..], b'c'), &input[3..])
            )
        );
        let ParseOutcome::Success(_, ((matched, _), payload)) = result else {
            panic!("expected match")
        };
        assert!(core::ptr::eq(matched, &pattern[..]));
        assert!(core::ptr::eq(payload, &input[3..]));
    }

    #[test]
    fn dependent_factories_preserve_borrowing_finality_and_checked_counts() {
        assert_eq!(
            bound_payload(b"\x02ab!", 2, InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, &b"ab"[..])
        );
        assert_eq!(
            bound_payload(b"\x02a", 2, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            bound_payload(b"\x02a", 1, InputStatus::Partial),
            ParseOutcome::Error(ParseError::Mismatch)
        );
        assert_eq!(
            bound_payload(b"\x02a", 2, InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            bound_literal(b"aa", InputStatus::Final),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, 97)
        );
        assert_eq!(
            bound_literal(b"ab", InputStatus::Final),
            ParseOutcome::Error(ParseError::Mismatch)
        );
        assert_eq!(
            bound_reference(b"ab", InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &b"b"[..])
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn dependent_collection_owns_its_captured_child() {
        assert_eq!(
            bound_blocks(b"\x02ab!", InputStatus::Partial),
            ParseOutcome::Success(
                Cursor { byte: 3, bit: 0 },
                alloc::vec![&b"a"[..], &b"b"[..]]
            )
        );
        assert_eq!(
            bound_blocks(b"\x02a", InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            bound_blocks(b"\x00", InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, alloc::vec![])
        );
    }

    #[test]
    fn captured_conversion_and_complete_entry_point() {
        assert_eq!(
            checked_flag(&[0x80], true, InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 0, bit: 1 }, Flag { value: true })
        );
        assert_eq!(
            checked_flag(&[0x80], false, InputStatus::Final),
            ParseOutcome::Error(ParseError::Mismatch)
        );
        assert_eq!(
            checked_flag(&[], true, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(complete_bit(&[]), Err(ParseError::UnexpectedEnd));
        assert_eq!(
            complete_bit(&[0x80]),
            Ok((Cursor { byte: 0, bit: 1 }, true))
        );
    }

    #[test]
    fn borrowed_packet_values_and_finality() {
        let input = [0x80, b'[', b'h', b'i', b']'];
        assert_eq!(
            packet(&input, InputStatus::Final),
            ParseOutcome::Success(Cursor { byte: 5, bit: 0 }, (true, &input[2..4]))
        );
        assert_eq!(packet(&input, InputStatus::Partial), ParseOutcome::NeedMore);
        assert_eq!(
            packet(&input[..4], InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            packet(&[0, b'[', b'h', b'i', b'!'], InputStatus::Final),
            ParseOutcome::Error(ParseError::Mismatch)
        );
    }

    #[test]
    fn folding_with_captured_initialization_and_borrowed_child_values() {
        assert_eq!(
            folded_checksum(b"abc", 3, 0x80, InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, Checksum { value: 0xe0 })
        );
        assert_eq!(
            folded_checksum(b"ab", 3, 0, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            folded_checksum(b"ab", 3, 0, InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            folded_checksum(b"", 0, 7, InputStatus::Final),
            ParseOutcome::Success(Cursor::start(), Checksum { value: 7 })
        );
        assert_eq!(
            leading_ones_count(&[0xc0], InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 0, bit: 2 }, 2)
        );
        assert_eq!(
            leading_ones_count(&[0xff], InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            leading_ones_count(&[0xff], InputStatus::Final),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, 8)
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn separated_borrowed_outputs_and_exact_caps() {
        let input = *b"a,b,";
        assert_eq!(
            separated_blocks(&input, 2, InputStatus::Partial),
            ParseOutcome::Success(
                Cursor { byte: 3, bit: 0 },
                alloc::vec![&input[..1], &input[2..3]]
            )
        );
        assert_eq!(
            separated_blocks(&input, 3, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            separated_blocks(&input, 3, InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
    }

    #[test]
    fn separated_folding_discards_separator_outputs_and_rolls_back_trailing_comma() {
        for input in [b"a,b,".as_slice(), b"a,b!"] {
            assert_eq!(
                separated_checksum(input, 0x80, InputStatus::Final),
                ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, Checksum { value: 0x83 })
            );
        }
        assert_eq!(
            separated_checksum(b"a,b,", 0, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            separated_checksum(b"", 0, InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn collected_outputs_and_unbounded_stopping() {
        let input = *b"abc";
        assert_eq!(
            blocks(&input, 2, InputStatus::Partial),
            ParseOutcome::Success(
                Cursor { byte: 2, bit: 0 },
                alloc::vec![&input[..1], &input[1..2]]
            )
        );
        assert_eq!(
            blocks(&input, 4, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            leading_ones(&[0xc0], InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 0, bit: 2 }, alloc::vec![1, 1])
        );
        assert_eq!(
            leading_ones(&[0xff], InputStatus::Partial),
            ParseOutcome::NeedMore
        );
    }
}
