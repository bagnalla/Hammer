//! Extraction regression fixture using RustHammer as an ordinary Cargo dependency.
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

use rusthammer::grammar::{
    BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Bind, Bit, Bits, ButNot, Byte, ByteIn, ByteNotIn,
    BytePattern, Difference, End, FoldRepeat, Ignore, IntRange, Left, Literal, Map, Middle, Right,
    Seq, SignedBits, SkipBits, TakeAligned, Tell, TryMap, WithByteOrder, Xor, I8,
};
use rusthammer::{ByteOrder, ConfigError, Cursor, ParseError, Parser};

#[path = "../../examples/support/constructors.rs"]
mod constructor_example;

/// Concrete nodes with opaque callbacks support direct execution.
pub fn constructor_header(
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, constructor_example::Header), ParseError> {
    constructor_example::header().parse_with(input, Cursor::start(), byte_order)
}

pub fn constructor_choice(
    input: &[u8],
    byte_order: ByteOrder,
    limit: u8,
) -> Result<(Cursor, Option<u16>), ParseError> {
    use rusthammer::{choice, map, optional, try_map, verify, ByteOrder, ParseError, Parser};
    let checked = try_map(Byte, move |value| {
        if value < limit {
            Ok(value as u16)
        } else {
            Err(())
        }
    });
    let fallback = map(verify(Byte, |value| *value == 255), |_| 256u16);
    optional(choice(checked, fallback)).parse_with(input, Cursor::start(), byte_order)
}

/// Input and configuration lifetimes escape the parser independently.
pub fn constructor_payload<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, (&'pattern [u8], &'input [u8])), ParseError> {
    use rusthammer::{bind, map, seq, verify, ByteOrder, ParseError, Parser};
    let length = map(verify(Byte, |count| *count <= 16), |count| count as usize);
    let parser = seq(
        BytePattern::new(pattern),
        bind(&length, |count| TakeAligned { count }),
    );
    let outcome = parser.parse_with(input, Cursor::start(), byte_order);
    outcome
}

pub fn spanned_pattern<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, (&'pattern [u8], rusthammer::BitSpan<'input>)), ParseError> {
    rusthammer::WithSpan {
        parser: BytePattern::new(pattern),
    }
    .parse_with(input, Cursor::start(), byte_order)
}

pub fn recognized_payload(
    input: &[u8],
    count: usize,
) -> Result<(Cursor, rusthammer::BitSpan<'_>), ParseError> {
    rusthammer::Recognize {
        parser: TakeAligned { count },
    }
    .parse(input, Cursor::start())
}

pub fn scoped_span(
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, ((u64, rusthammer::BitSpan<'_>), ())), ParseError> {
    WithByteOrder {
        byte_order: ByteOrder::Little,
        parser: Seq {
            first: rusthammer::WithSpan {
                parser: Bits::new(3).unwrap(),
            },
            second: SkipBits::new(5),
        },
    }
    .parse_with(input, Cursor::start(), byte_order)
}

pub fn span_views(
    input: &[u8],
    start: Cursor,
    end: Cursor,
) -> Result<(&[u8], Cursor, Cursor, bool, Option<&[u8]>), ParseError> {
    let span = rusthammer::BitSpan::new(input, start, end)?;
    let copied = span;
    Ok((
        copied.input(),
        copied.start(),
        copied.end(),
        copied.is_empty(),
        copied.as_bytes(),
    ))
}

pub fn ordered_fields(
    input: &[u8],
    width: u8,
    byte_order: ByteOrder,
) -> Result<Result<(Cursor, (u64, (i64, (u16, i8)))), ParseError>, ConfigError> {
    let parser = Seq {
        first: Bits::new(width)?,
        second: Seq {
            first: SignedBits::new(width)?,
            second: Seq {
                first: BeU16,
                second: I8,
            },
        },
    };
    Ok(parser.parse_with(input, Cursor::start(), byte_order))
}

pub fn scoped_payload(
    input: &[u8],
    count: usize,
    order: ByteOrder,
    byte_order: ByteOrder,
) -> Result<(Cursor, (&[u8], u16)), ParseError> {
    let region = WithByteOrder {
        byte_order: order,
        parser: Left {
            first: TakeAligned { count },
            second: Seq {
                first: Bits::new(3).unwrap(),
                second: Bits::new(5).unwrap(),
            },
        },
    };
    let parser = Seq {
        first: &region,
        second: BeU16,
    };
    parser
        .clone()
        .parse_with(input, Cursor::start(), byte_order)
}

pub fn scoped_pattern<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    order: ByteOrder,
    byte_order: ByteOrder,
) -> Result<(Cursor, &'pattern [u8]), ParseError> {
    WithByteOrder {
        byte_order: order,
        parser: BytePattern::new(pattern),
    }
    .parse_with(input, Cursor::start(), byte_order)
}

pub fn restricted_payload(
    input: &[u8],
    count: usize,
    width: u8,
    byte_order: ByteOrder,
) -> Result<Result<(Cursor, &[u8]), ParseError>, ConfigError> {
    let parser = ButNot {
        first: TakeAligned { count },
        second: Bits::new(width)?,
    };
    Ok(parser
        .clone()
        .parse_with(input, Cursor::start(), byte_order))
}

pub fn difference_pattern<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, &'pattern [u8]), ParseError> {
    let first = BytePattern::new(pattern);
    Difference {
        first: &first,
        second: Byte,
    }
    .clone()
    .parse_with(input, Cursor::start(), byte_order)
}

pub fn exclusive_patterns<'pattern>(
    first: &'pattern [u8],
    second: &'pattern [u8],
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, &'pattern [u8]), ParseError> {
    Xor {
        first: BytePattern::new(first),
        second: BytePattern::new(second),
    }
    .clone()
    .parse_with(input, Cursor::start(), byte_order)
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExclusiveValue {
    Digit(u8),
    Word(u16),
}

/// Different child values explicitly mapped into an owned, non-Clone enum.
pub fn exclusive_value(
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, ExclusiveValue), ParseError> {
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
    .parse_with(input, Cursor::start(), byte_order)
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
    byte_order: ByteOrder,
) -> Result<(Cursor, Cursor), ParseError> {
    let skip = SkipBits::new(bits);
    Right {
        first: &skip,
        second: Tell,
    }
    .parse_with(input, cursor, byte_order)
}

pub fn reported_position(
    input: &[u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, Cursor), ParseError> {
    Tell.parse_with(input, cursor, byte_order)
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
    byte_order: ByteOrder,
) -> Result<(Cursor, u8), ParseError> {
    ByteIn::new(bytes).parse_with(input, cursor, byte_order)
}

pub fn byte_not_in(
    bytes: &[u8],
    input: &[u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, u8), ParseError> {
    ByteNotIn::new(bytes).parse_with(input, cursor, byte_order)
}

/// Independently constructed bitmaps compose through a reference and a clone.
pub fn byte_set_pair(
    allowed: &[u8],
    excluded: &[u8],
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, (u8, u8)), ParseError> {
    let first = ByteIn::new(allowed);
    let second = ByteNotIn::new(excluded);
    Seq {
        first: &first,
        second: second.clone(),
    }
    .parse_with(input, Cursor::start(), byte_order)
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
    byte_order: ByteOrder,
) -> Result<Result<(Cursor, u64), ParseError>, ConfigError> {
    let range = IntRange::new(BeU64, lower, upper)?;
    Ok(range.parse_with(input, Cursor::start(), byte_order))
}

/// A borrowed child, typed signed bounds, and a byte range compose as usual.
pub fn ranged_pair(
    input: &[u8],
    lower: i16,
    upper: i16,
    byte_order: ByteOrder,
) -> Result<Result<(Cursor, (i16, u8)), ParseError>, ConfigError> {
    let signed = BeI16;
    let parser = Seq {
        first: IntRange::new(&signed, lower, upper)?,
        second: IntRange::new(Byte, b'0', b'9')?,
    };
    Ok(parser.parse_with(input, Cursor::start(), byte_order))
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
    byte_order: ByteOrder,
) -> Result<Result<(Cursor, Count), ParseError>, ConfigError> {
    let child = Map {
        parser: BeU16,
        map: |value| Count { value },
    };
    let range = IntRange::new(child, Count { value: lower }, Count { value: upper })?;
    Ok(range.parse_with(input, Cursor::start(), byte_order))
}

pub fn complete_range(
    input: &[u8],
    cursor: Cursor,
    range: &IntRange<BeU16, u16>,
) -> Result<(Cursor, u16), ParseError> {
    range.parse(input, cursor)
}

/// The fixed-width output types survive sequencing and a shared parser reference.
pub fn integers16(
    input: &[u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, (u16, i16)), ParseError> {
    let unsigned = BeU16;
    Seq {
        first: &unsigned,
        second: BeI16,
    }
    .parse_with(input, cursor, byte_order)
}

pub fn integers32(
    input: &[u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, (u32, i32)), ParseError> {
    Seq {
        first: BeU32,
        second: BeI32,
    }
    .parse_with(input, cursor, byte_order)
}

pub fn integers64(
    input: &[u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, (u64, i64)), ParseError> {
    Seq {
        first: BeU64,
        second: BeI64,
    }
    .parse_with(input, cursor, byte_order)
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
    byte_order: ByteOrder,
) -> Result<Result<(Cursor, i64), ParseError>, ConfigError> {
    let parser = SignedBits::new(width)?;
    Ok(parser.parse_with(input, cursor, byte_order))
}

/// A validated signed parser composes with an unsigned byte through a reference.
pub fn signed_and_unsigned(
    input: &[u8],
    cursor: Cursor,
    signed: &SignedBits,
    byte_order: ByteOrder,
) -> Result<(Cursor, (i64, u8)), ParseError> {
    Seq {
        first: signed,
        second: Byte,
    }
    .parse_with(input, cursor, byte_order)
}

/// Input, pattern, and parser references have independent lifetimes.
pub fn matched_pattern<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, &'pattern [u8]), ParseError> {
    let parser = BytePattern::new(pattern);
    let borrowed = &parser;
    borrowed.parse_with(input, cursor, byte_order)
}

/// Both borrowing sources remain distinct through typed sequencing.
pub fn pattern_and_input<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, ((&'pattern [u8], u8), &'input [u8])), ParseError> {
    Seq {
        first: Seq {
            first: BytePattern::new(pattern),
            second: Byte,
        },
        second: TakeAligned { count: 1 },
    }
    .parse_with(input, Cursor::start(), byte_order)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Flag {
    pub value: bool,
}

/// A captured fallible callback constructs an owned, non-Clone output.
pub fn checked_flag(
    input: &[u8],
    expected: bool,
    byte_order: ByteOrder,
) -> Result<(Cursor, Flag), ParseError> {
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
    parser.parse_with(input, Cursor::start(), byte_order)
}

/// One flag bit, seven ignored bits, then a bracketed two-byte borrowed payload.
pub fn packet(input: &[u8], byte_order: ByteOrder) -> Result<(Cursor, (bool, &[u8])), ParseError> {
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
    parser.parse_with(input, Cursor::start(), byte_order)
}

/// Also exercise the default complete-input trait method across the crate boundary.
pub fn complete_bit(input: &[u8]) -> Result<(Cursor, bool), ParseError> {
    Bit.parse(input, Cursor::start())
}

/// A checked input value configures a parser returning a borrowed slice.
pub fn bound_payload(
    input: &[u8],
    limit: u64,
    byte_order: ByteOrder,
) -> Result<(Cursor, &[u8]), ParseError> {
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
    .parse_with(input, Cursor::start(), byte_order)
}

/// The factory reads a borrowed first output to construct an owned parser.
pub fn bound_literal(input: &[u8], byte_order: ByteOrder) -> Result<(Cursor, u64), ParseError> {
    Bind {
        parser: TakeAligned { count: 1 },
        then: |byte: &[u8]| Literal::new(8, u64::from(byte[0])).unwrap(),
    }
    .parse_with(input, Cursor::start(), byte_order)
}

/// A constructed repetition owns a copy of its captured child parser.
#[cfg(feature = "alloc")]
pub fn bound_blocks(
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, alloc::vec::Vec<&[u8]>), ParseError> {
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
        then: |count| rusthammer::grammar::Repeat::exact(element, count),
    }
    .parse_with(input, Cursor::start(), byte_order)
}

/// A factory may also return an existing parser by shared reference.
pub fn bound_reference(input: &[u8], byte_order: ByteOrder) -> Result<(Cursor, &[u8]), ParseError> {
    let body = TakeAligned { count: 1 };
    Bind {
        parser: Bits::new(8).unwrap(),
        then: |_| &body,
    }
    .parse_with(input, Cursor::start(), byte_order)
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
    byte_order: ByteOrder,
) -> Result<(Cursor, Checksum), ParseError> {
    FoldRepeat::exact(
        TakeAligned { count: 1 },
        count,
        || Checksum { value: seed },
        |sum: Checksum, byte: &[u8]| Checksum {
            value: sum.value ^ u64::from(byte[0]),
        },
    )
    .parse_with(input, Cursor::start(), byte_order)
}

pub fn leading_ones_count(
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, usize), ParseError> {
    FoldRepeat::at_least(
        Literal::new(1, 1).unwrap(),
        0,
        || 0usize,
        |count, _| count + 1,
    )
    .parse_with(input, Cursor::start(), byte_order)
}

/// Both item and discarded separator outputs borrow the input.
#[cfg(feature = "alloc")]
pub fn separated_blocks(
    input: &[u8],
    count: usize,
    byte_order: ByteOrder,
) -> Result<(Cursor, alloc::vec::Vec<&[u8]>), ParseError> {
    rusthammer::grammar::SepBy::exact(TakeAligned { count: 1 }, TakeAligned { count: 1 }, count)
        .parse_with(input, Cursor::start(), byte_order)
}

pub struct Separator;

/// A non-Clone separator output is discarded; borrowed items enter an owned fold.
pub fn separated_checksum(
    input: &[u8],
    seed: u64,
    byte_order: ByteOrder,
) -> Result<(Cursor, Checksum), ParseError> {
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
    .parse_with(input, Cursor::start(), byte_order)
}

#[cfg(feature = "alloc")]
pub fn blocks(
    input: &[u8],
    count: usize,
    byte_order: ByteOrder,
) -> Result<(Cursor, alloc::vec::Vec<&[u8]>), ParseError> {
    rusthammer::grammar::Repeat::exact(TakeAligned { count: 1 }, count).parse_with(
        input,
        Cursor::start(),
        byte_order,
    )
}

#[cfg(feature = "alloc")]
pub fn leading_ones(
    input: &[u8],
    byte_order: ByteOrder,
) -> Result<(Cursor, alloc::vec::Vec<u64>), ParseError> {
    rusthammer::grammar::Repeat::at_least(Literal::new(1, 1).unwrap(), 0).parse_with(
        input,
        Cursor::start(),
        byte_order,
    )
}

#[allow(dead_code)]
#[path = "../../examples/support/mavlink.rs"]
mod mavlink_example;

pub fn mavlink_packet(input: &[u8]) -> Result<(Cursor, mavlink_example::Packet<'_>), ParseError> {
    mavlink_example::mavlink_v2(|id| mavlink_example::heartbeat_crc_extra(id))
        .parse(input, Cursor::start())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn input_and_configuration_borrows_escape_the_parser() {
        let input = *b"ab\x02cd";
        let pattern = *b"ab";
        let (_, (configuration, payload)) =
            constructor_payload(&pattern, &input, ByteOrder::Big).unwrap();
        assert!(core::ptr::eq(configuration, &pattern[..]));
        assert!(core::ptr::eq(payload, &input[3..]));
    }
    #[test]
    fn mavlink_packet_borrows_payload_and_validates_crc() {
        let input = mavlink_example::HEARTBEAT_FRAME;
        let (next, packet) = mavlink_packet(&input).unwrap();
        assert_eq!(next.byte, input.len());
        assert!(core::ptr::eq(packet.payload, &input[10..19]));
        let mut corrupt = input;
        corrupt[10] ^= 1;
        assert_eq!(mavlink_packet(&corrupt), Err(ParseError::Mismatch));
    }
}

#[cfg(test)]
mod retained_tests {

    #[test]
    fn constructor_callbacks_infer_types_and_preserve_alternative_priority() {
        use super::*;
        let next = Cursor { byte: 1, bit: 0 };
        for byte_order in [ByteOrder::Big] {
            assert_eq!(
                constructor_choice(&[3], byte_order, 10),
                Ok((next, Some(3)))
            );
            assert_eq!(
                constructor_choice(&[255], byte_order, 10),
                Ok((next, Some(256)))
            );
            assert_eq!(
                constructor_choice(&[10], byte_order, 10),
                Ok((Cursor::start(), None))
            );
        }

        assert_eq!(
            constructor_choice(&[], ByteOrder::Big, 10),
            Ok((Cursor::start(), None))
        );
    }

    #[test]
    fn spans_escape_parsers_and_byte_order_scopes() {
        use super::*;
        use rusthammer::BitSpan;
        let input = [0x96, 0x53];
        let end = Cursor { byte: 1, bit: 0 };
        let expected = BitSpan::new(&input, Cursor::start(), end).unwrap();
        let pattern = [0x96];
        assert_eq!(
            spanned_pattern(&pattern, &input, ByteOrder::Big),
            Ok((end, (pattern.as_slice(), expected)))
        );
        assert_eq!(recognized_payload(&input, 1), Ok((end, expected)));
        let Ok((_, ((value, partial), ()))) = scoped_span(&input, ByteOrder::Big) else {
            panic!()
        };
        assert_eq!(value, 4);

        assert_eq!(partial.end(), Cursor { byte: 0, bit: 3 });
        assert_eq!(
            span_views(&input, Cursor::start(), end),
            Ok((
                input.as_slice(),
                Cursor::start(),
                end,
                false,
                Some(&input[..1])
            ))
        );
    }

    use super::*;

    #[test]
    fn scoped_ordering_keeps_borrows_truncation_and_named_byte_order() {
        use rusthammer::{ByteOrder, ParseError, Parser};
        let low = ByteOrder::Little;
        let byte_order = low;
        assert_eq!(
            ordered_fields(&[0xd6, 0x12, 0x34, 0x56], 4, byte_order),
            Ok(Ok((Cursor { byte: 4, bit: 0 }, (13, (6, (0x1234, 0x56))))))
        );
        let data = [b'a', b'b', 0xd6, 0x12, 0x34];
        let Ok((next, (payload, number))) = scoped_payload(&data, 2, low, ByteOrder::Big) else {
            panic!("expected payload")
        };
        assert_eq!((next, number), (Cursor { byte: 5, bit: 0 }, 0x1234));
        assert!(core::ptr::eq(payload, &data[..2]));

        let pattern = [0x12, 0x34];
        let Ok((_, matched)) = scoped_pattern(&pattern, &data[3..], low, ByteOrder::Big) else {
            panic!("expected pattern")
        };
        assert!(core::ptr::eq(matched, &pattern[..]));
    }

    #[test]
    fn matches_keep_borrows_types_lengths_and_truncation_across_crates() {
        let input = [1, 2];
        let Ok((next, payload)) = restricted_payload(&input, 2, 8, ByteOrder::Big).unwrap() else {
            panic!("expected payload");
        };
        assert_eq!(next, Cursor { byte: 2, bit: 0 });
        assert!(core::ptr::eq(payload, &input[..]));
        assert_eq!(
            restricted_payload(&input, 1, 8, ByteOrder::Big),
            Ok(Err(ParseError::Mismatch))
        );

        assert_eq!(
            restricted_payload(&input, 1, 65, ByteOrder::Big),
            Err(ConfigError::InvalidWidth)
        );
        let pattern = *b"a";
        let parsed = {
            let input = *b"a";
            difference_pattern(&pattern, &input, ByteOrder::Big)
        };
        let Ok((_, matched)) = parsed else {
            panic!("expected pattern");
        };
        assert!(core::ptr::eq(matched, &pattern[..]));

        assert_eq!(
            exclusive_patterns(b"a", b"ab", b"a", ByteOrder::Big),
            Ok((Cursor { byte: 1, bit: 0 }, &b"a"[..]))
        );
        assert_eq!(
            exclusive_patterns(b"a", b"ab", b"ab", ByteOrder::Big),
            Err(ParseError::Mismatch)
        );
        assert_eq!(
            exclusive_value(b"5", ByteOrder::Big),
            Ok((Cursor { byte: 1, bit: 0 }, ExclusiveValue::Digit(b'5')))
        );
        assert_eq!(
            exclusive_value(b"#\x12\x34", ByteOrder::Big),
            Ok((Cursor { byte: 3, bit: 0 }, ExclusiveValue::Word(0x1234)))
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
            skipped_position(&[0; 11], cursor, 81, ByteOrder::Big),
            Ok((end, end))
        );

        assert_eq!(
            skipped_position(&[0; 10], cursor, 81, ByteOrder::Big),
            Err(ParseError::UnexpectedEnd)
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
            reported_position(&[], Cursor::start(), ByteOrder::Big),
            Ok((Cursor::start(), Cursor::start()))
        );
        assert_eq!(
            reported_position(&[0], cursor, ByteOrder::Big),
            Ok((cursor, cursor))
        );
        let invalid = Cursor {
            byte: usize::MAX,
            bit: 0,
        };
        assert_eq!(
            reported_position(&[], invalid, ByteOrder::Big),
            Err(ParseError::InvalidCursor)
        );
        assert_eq!(
            skipped_position(&[], invalid, 0, ByteOrder::Big),
            Err(ParseError::InvalidCursor)
        );
    }

    #[test]
    fn byte_sets_keep_membership_and_truncation_across_crates() {
        let cursor = Cursor { byte: 0, bit: 1 };
        assert_eq!(
            byte_in(&[0x80, 0, 0x80], &[0x40, 0], cursor, ByteOrder::Big),
            Ok((Cursor { byte: 1, bit: 1 }, 0x80))
        );
        assert_eq!(
            byte_not_in(&[0x80], &[0x40, 0], cursor, ByteOrder::Big),
            Err(ParseError::Mismatch)
        );
        for bytes in [&[][..], &[0x80][..]] {
            assert_eq!(
                byte_not_in(bytes, &[0x40], cursor, ByteOrder::Big),
                Err(ParseError::UnexpectedEnd)
            );
        }
        assert_eq!(
            byte_in(&[], &[], Cursor { byte: 0, bit: 1 }, ByteOrder::Big),
            Err(ParseError::InvalidCursor)
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
            byte_set_pair(&allowed, &excluded, &input, ByteOrder::Big)
        };
        assert_eq!(output, Ok((Cursor { byte: 2, bit: 0 }, (255, b'x'))));
        let parser = ByteNotIn::new(b"\r\n");
        assert_eq!(
            complete_byte_set(&parser, b"x", Cursor::start()),
            Ok((Cursor { byte: 1, bit: 0 }, b'x'))
        );
    }

    #[test]
    fn typed_ranges_keep_bounds_truncation_and_rejection_across_crates() {
        assert_eq!(
            ranged_u64(&[], 2, 1, ByteOrder::Big),
            Err(ConfigError::InvalidBounds)
        );
        assert_eq!(
            ranged_u64(&[0xff; 8], 1 << 63, u64::MAX, ByteOrder::Big),
            Ok(Ok((Cursor { byte: 8, bit: 0 }, u64::MAX)))
        );

        assert_eq!(
            ranged_u64(&[0xff; 7], 0, 100, ByteOrder::Big),
            Ok(Err(ParseError::UnexpectedEnd))
        );
        assert_eq!(
            ranged_pair(&[0xff, 0xfd, b'7'], -100, 100, ByteOrder::Big),
            Ok(Ok((Cursor { byte: 3, bit: 0 }, (-3, b'7'))))
        );
        assert_eq!(
            ranged_pair(&[0xff, 0xfd, b'x'], -100, 100, ByteOrder::Big),
            Ok(Err(ParseError::Mismatch))
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
            ranged_count(&[0x01, 0], 1, 4096, ByteOrder::Big),
            Ok(Ok((Cursor { byte: 2, bit: 0 }, Count { value: 256 })))
        );
        assert_eq!(
            ranged_count(&[0x01, 0], 1, 100, ByteOrder::Big),
            Ok(Err(ParseError::Mismatch))
        );
        assert_eq!(
            ranged_count(&[], 2, 1, ByteOrder::Big),
            Err(ConfigError::InvalidBounds)
        );
    }

    #[test]
    fn fixed_width_types_sequence_across_the_crate_boundary() {
        for byte_order in [ByteOrder::Big] {
            assert_eq!(
                integers16(&[0x12, 0x34, 0xff, 0xfd], Cursor::start(), byte_order),
                Ok((Cursor { byte: 4, bit: 0 }, (0x1234u16, -3i16)))
            );
            assert_eq!(
                integers32(
                    &[0xff, 0xff, 0xff, 0xff, 0x80, 0, 0, 0],
                    Cursor::start(),
                    byte_order
                ),
                Ok((Cursor { byte: 8, bit: 0 }, (u32::MAX, i32::MIN)))
            );
            assert_eq!(
                integers64(
                    &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0, 0, 0, 0, 0, 0, 0],
                    Cursor::start(),
                    byte_order
                ),
                Ok((Cursor { byte: 16, bit: 0 }, (u64::MAX, i64::MIN)))
            );
        }

        assert_eq!(
            integers32(&[0; 7], Cursor::start(), ByteOrder::Big),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            integers64(&[0; 17], Cursor { byte: 0, bit: 1 }, ByteOrder::Big),
            Ok((Cursor { byte: 16, bit: 1 }, (0, 0)))
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
            signed_field(&[], Cursor::start(), 65, ByteOrder::Big),
            Err(ConfigError::InvalidWidth)
        );
        assert_eq!(
            signed_field(&[], Cursor::start(), 0, ByteOrder::Big),
            Ok(Ok((Cursor::start(), 0)))
        );
        for value in [i64::MIN, -1, 0, i64::MAX] {
            assert_eq!(
                signed_field(&value.to_be_bytes(), Cursor::start(), 64, ByteOrder::Big),
                Ok(Ok((Cursor { byte: 8, bit: 0 }, value)))
            );
        }

        assert_eq!(
            signed_field(&[0xff], Cursor::start(), 9, ByteOrder::Big),
            Ok(Err(ParseError::UnexpectedEnd))
        );
    }

    #[test]
    fn signed_parser_references_sequence_with_an_unsigned_byte() {
        let signed = SignedBits::new(5).unwrap();
        // Skip three prefix bits; the signed field is 11101 (-3), then A5.
        let cursor = Cursor { byte: 0, bit: 3 };
        assert_eq!(
            signed_and_unsigned(&[0x1d, 0xa5], cursor, &signed, ByteOrder::Big),
            Ok((Cursor { byte: 2, bit: 0 }, (-3, 0xa5)))
        );
    }

    #[test]
    fn pattern_output_outlives_input_and_parser() {
        let pattern = [0xab, 0xcd];
        let result = {
            let input = [0x55, 0xe6, 0x80];
            matched_pattern(&pattern, &input, Cursor { byte: 0, bit: 1 }, ByteOrder::Big)
        };
        assert_eq!(result, Ok((Cursor { byte: 2, bit: 1 }, &pattern[..])));
        let Ok((_, matched)) = result else {
            panic!("expected match")
        };
        assert!(core::ptr::eq(matched, &pattern[..]));
    }

    #[test]
    fn sequence_retains_distinct_pattern_and_input_borrows() {
        let pattern = *b"ab";
        let input = *b"abcd";
        let result = pattern_and_input(&pattern, &input, ByteOrder::Big);
        assert_eq!(
            result,
            Ok((
                Cursor { byte: 4, bit: 0 },
                ((&pattern[..], b'c'), &input[3..])
            ))
        );
        let Ok((_, ((matched, _), payload))) = result else {
            panic!("expected match")
        };
        assert!(core::ptr::eq(matched, &pattern[..]));
        assert!(core::ptr::eq(payload, &input[3..]));
    }

    #[test]
    fn dependent_factories_preserve_borrowing_truncation_and_checked_counts() {
        assert_eq!(
            bound_payload(b"\x02ab!", 2, ByteOrder::Big),
            Ok((Cursor { byte: 3, bit: 0 }, &b"ab"[..]))
        );

        assert_eq!(
            bound_payload(b"\x02a", 1, ByteOrder::Big),
            Err(ParseError::Mismatch)
        );
        assert_eq!(
            bound_payload(b"\x02a", 2, ByteOrder::Big),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            bound_literal(b"aa", ByteOrder::Big),
            Ok((Cursor { byte: 2, bit: 0 }, 97))
        );
        assert_eq!(
            bound_literal(b"ab", ByteOrder::Big),
            Err(ParseError::Mismatch)
        );
        assert_eq!(
            bound_reference(b"ab", ByteOrder::Big),
            Ok((Cursor { byte: 2, bit: 0 }, &b"b"[..]))
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn dependent_collection_owns_its_captured_child() {
        assert_eq!(
            bound_blocks(b"\x02ab!", ByteOrder::Big),
            Ok((
                Cursor { byte: 3, bit: 0 },
                alloc::vec![&b"a"[..], &b"b"[..]]
            ))
        );

        assert_eq!(
            bound_blocks(b"\x00", ByteOrder::Big),
            Ok((Cursor { byte: 1, bit: 0 }, alloc::vec![]))
        );
    }

    #[test]
    fn captured_conversion_and_complete_entry_point() {
        assert_eq!(
            checked_flag(&[0x80], true, ByteOrder::Big),
            Ok((Cursor { byte: 0, bit: 1 }, Flag { value: true }))
        );
        assert_eq!(
            checked_flag(&[0x80], false, ByteOrder::Big),
            Err(ParseError::Mismatch)
        );

        assert_eq!(complete_bit(&[]), Err(ParseError::UnexpectedEnd));
        assert_eq!(
            complete_bit(&[0x80]),
            Ok((Cursor { byte: 0, bit: 1 }, true))
        );
    }

    #[test]
    fn borrowed_packet_values_and_truncation() {
        let input = [0x80, b'[', b'h', b'i', b']'];
        assert_eq!(
            packet(&input, ByteOrder::Big),
            Ok((Cursor { byte: 5, bit: 0 }, (true, &input[2..4])))
        );

        assert_eq!(
            packet(&input[..4], ByteOrder::Big),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            packet(&[0, b'[', b'h', b'i', b'!'], ByteOrder::Big),
            Err(ParseError::Mismatch)
        );
    }

    #[test]
    fn folding_with_captured_initialization_and_borrowed_child_values() {
        assert_eq!(
            folded_checksum(b"abc", 3, 0x80, ByteOrder::Big),
            Ok((Cursor { byte: 3, bit: 0 }, Checksum { value: 0xe0 }))
        );

        assert_eq!(
            folded_checksum(b"ab", 3, 0, ByteOrder::Big),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            folded_checksum(b"", 0, 7, ByteOrder::Big),
            Ok((Cursor::start(), Checksum { value: 7 }))
        );
        assert_eq!(
            leading_ones_count(&[0xc0], ByteOrder::Big),
            Ok((Cursor { byte: 0, bit: 2 }, 2))
        );

        assert_eq!(
            leading_ones_count(&[0xff], ByteOrder::Big),
            Ok((Cursor { byte: 1, bit: 0 }, 8))
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn separated_borrowed_outputs_and_exact_caps() {
        let input = *b"a,b,";
        assert_eq!(
            separated_blocks(&input, 2, ByteOrder::Big),
            Ok((
                Cursor { byte: 3, bit: 0 },
                alloc::vec![&input[..1], &input[2..3]]
            ))
        );

        assert_eq!(
            separated_blocks(&input, 3, ByteOrder::Big),
            Err(ParseError::UnexpectedEnd)
        );
    }

    #[test]
    fn separated_folding_discards_separator_outputs_and_rolls_back_trailing_comma() {
        for input in [b"a,b,".as_slice(), b"a,b!"] {
            assert_eq!(
                separated_checksum(input, 0x80, ByteOrder::Big),
                Ok((Cursor { byte: 3, bit: 0 }, Checksum { value: 0x83 }))
            );
        }

        assert_eq!(
            separated_checksum(b"", 0, ByteOrder::Big),
            Err(ParseError::UnexpectedEnd)
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn collected_outputs_and_unbounded_stopping() {
        let input = *b"abc";
        assert_eq!(
            blocks(&input, 2, ByteOrder::Big),
            Ok((
                Cursor { byte: 2, bit: 0 },
                alloc::vec![&input[..1], &input[1..2]]
            ))
        );

        assert_eq!(
            leading_ones(&[0xc0], ByteOrder::Big),
            Ok((Cursor { byte: 0, bit: 2 }, alloc::vec![1, 1]))
        );
    }
}
