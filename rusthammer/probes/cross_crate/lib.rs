//! Extraction regression fixture using RustHammer as an ordinary Cargo dependency.
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

use rusthammer::{
    BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Bind, Bit, Bits, Byte, BytePattern, ConfigError,
    Cursor, End, FoldRepeat, Ignore, InputStatus, Left, Literal, Middle, ParseError, ParseOutcome,
    Parser, Right, Seq, SignedBits, TakeAligned, TryMap, I8,
};

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
