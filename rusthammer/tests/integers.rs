use core::fmt::Debug;
use rusthammer::{
    BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Byte, Choice, Cursor, InputStatus, Optional,
    ParseError, ParseOutcome, Parser, Seq, Verify, I8,
};

// Decode a binary string with i128 arithmetic, independently of Bits and
// SignedBits. The wider oracle can represent 2^64 and every unsigned output.
fn oracle(
    input: &[u8],
    cursor: Cursor,
    width: usize,
    signed: bool,
    status: InputStatus,
) -> ParseOutcome<i128> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return ParseOutcome::Error(ParseError::InvalidCursor);
    }
    let text: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    let start = cursor.byte * 8 + usize::from(cursor.bit);
    let end = start + width;
    let Some(field) = text.get(start..end) else {
        return match status {
            InputStatus::Partial => ParseOutcome::NeedMore,
            InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
        };
    };
    let unsigned = i128::from_str_radix(field, 2).unwrap();
    let value = if signed && field.starts_with('1') {
        unsigned - (1i128 << width)
    } else {
        unsigned
    };
    ParseOutcome::Success(
        Cursor {
            byte: end / 8,
            bit: (end % 8) as u8,
        },
        value,
    )
}

fn widen<T: Into<i128>>(result: ParseOutcome<T>) -> ParseOutcome<i128> {
    match result {
        ParseOutcome::Success(next, value) => ParseOutcome::Success(next, value.into()),
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

fn check_cursors<P, T>(parser: P, width: usize, signed: bool)
where
    P: for<'input> Parser<'input, Output = T>,
    T: Into<i128> + Debug + PartialEq,
{
    for input in [
        [0; 11],
        [255; 11],
        [
            0x80, 0x01, 0x55, 0xaa, 0x7f, 0x81, 0xfe, 0x42, 0x99, 0, 0x13,
        ],
    ] {
        for length in 0..=input.len() {
            let input = &input[..length];
            for byte in (0..=input.len() + 1).chain([usize::MAX]) {
                for bit in (0..=8).chain([u8::MAX]) {
                    let cursor = Cursor { byte, bit };
                    for status in [InputStatus::Partial, InputStatus::Final] {
                        assert_eq!(
                            widen(parser.parse_with(input, cursor, status)),
                            oracle(input, cursor, width, signed, status),
                            "input={input:?}, cursor={cursor:?}, status={status:?}"
                        );
                    }
                    let expected = match oracle(input, cursor, width, signed, InputStatus::Final) {
                        ParseOutcome::Success(next, value) => Ok((next, value)),
                        ParseOutcome::Error(error) => Err(error),
                        ParseOutcome::NeedMore => unreachable!(),
                    };
                    assert_eq!(
                        parser
                            .parse(input, cursor)
                            .map(|(next, value)| (next, value.into())),
                        expected
                    );
                }
            }
        }
    }
}

#[test]
fn every_reader_matches_the_oracle_for_truncation_finality_and_raw_cursors() {
    check_cursors(Byte, 8, false);
    check_cursors(I8, 8, true);
    check_cursors(BeU16, 16, false);
    check_cursors(BeI16, 16, true);
    check_cursors(BeU32, 32, false);
    check_cursors(BeI32, 32, true);
    check_cursors(BeU64, 64, false);
    check_cursors(BeI64, 64, true);
}

#[test]
fn small_integer_types_exhaust_their_bit_patterns() {
    for byte in 0..=u8::MAX {
        let typed: Result<(Cursor, i8), ParseError> = I8.parse(&[byte], Cursor::start());
        assert_eq!(
            typed,
            Ok((Cursor { byte: 1, bit: 0 }, i8::from_be_bytes([byte])))
        );
    }
    for word in 0..=u16::MAX {
        let input = word.to_be_bytes();
        let unsigned: (Cursor, u16) = BeU16.parse(&input, Cursor::start()).unwrap();
        let signed: (Cursor, i16) = BeI16.parse(&input, Cursor::start()).unwrap();
        assert_eq!(
            unsigned,
            (Cursor { byte: 2, bit: 0 }, u16::from_be_bytes(input))
        );
        assert_eq!(
            signed,
            (Cursor { byte: 2, bit: 0 }, i16::from_be_bytes(input))
        );
    }
}

// Encode complete byte fields with a nonzero byte position and arbitrary bit
// offset. Native from_be_bytes supplies the expected value, including extremes.
fn check_offsets<P, T, const N: usize>(parser: P, fields: &[[u8; N]], decode: fn([u8; N]) -> T)
where
    P: Copy + for<'input> Parser<'input, Output = T>,
    T: Copy + Debug + PartialEq,
{
    assert_eq!(core::mem::size_of::<P>(), 0);
    let copied = parser;
    for field in fields {
        for bit in 0..8 {
            let mut text = String::from("10010110");
            text.push_str(&"1010101"[..usize::from(bit)]);
            for byte in field {
                text.push_str(&format!("{byte:08b}"));
            }
            text.push_str("01100101");
            text.push_str(&"0".repeat((8 - text.len() % 8) % 8));
            let input: Vec<_> = text
                .as_bytes()
                .chunks_exact(8)
                .map(|chunk| u8::from_str_radix(core::str::from_utf8(chunk).unwrap(), 2).unwrap())
                .collect();
            let cursor = Cursor { byte: 1, bit };
            let next = Cursor { byte: N + 1, bit };
            for status in [InputStatus::Partial, InputStatus::Final] {
                assert_eq!(
                    copied.parse_with(&input, cursor, status),
                    ParseOutcome::Success(next, decode(*field))
                );
            }
            assert_eq!(parser.parse(&input, cursor), Ok((next, decode(*field))));
        }
    }
}

#[test]
fn sign_boundaries_and_native_integer_extremes_work_at_every_bit_offset() {
    // Include both ends of each signed range, -1, zero, one, and asymmetric bytes
    // so reversing byte or bit order cannot pass these cases.
    let fields8 = [0, 1, 0x7f, 0x80, 0x81, 0xfe, 0xff, 0xa5].map(|x| [x]);
    check_offsets(Byte, &fields8, u8::from_be_bytes);
    check_offsets(I8, &fields8, i8::from_be_bytes);
    let fields16 = [0u16, 1, 0x7fff, 0x8000, 0x8001, 0xfffe, 0xffff, 0x1234].map(u16::to_be_bytes);
    check_offsets(BeU16, &fields16, u16::from_be_bytes);
    check_offsets(BeI16, &fields16, i16::from_be_bytes);
    let fields32 = [
        0u32,
        1,
        0x7fff_ffff,
        0x8000_0000,
        0x8000_0001,
        u32::MAX - 1,
        u32::MAX,
        0x1234_5678,
    ]
    .map(u32::to_be_bytes);
    check_offsets(BeU32, &fields32, u32::from_be_bytes);
    check_offsets(BeI32, &fields32, i32::from_be_bytes);
    let fields64 = [
        0u64,
        1,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0001,
        u64::MAX - 1,
        u64::MAX,
        0x1234_5678_9abc_def0,
    ]
    .map(u64::to_be_bytes);
    check_offsets(BeU64, &fields64, u64::from_be_bytes);
    check_offsets(BeI64, &fields64, i64::from_be_bytes);
}

#[test]
fn typed_sequence_retries_from_its_original_cursor() {
    let unsigned = BeU16;
    let parser = Seq {
        first: &unsigned,
        second: BeI16,
    };
    let input = [0x12, 0x34, 0xff, 0xfd];
    for length in 0..input.len() {
        assert_eq!(
            parser.parse_with(&input[..length], Cursor::start(), InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            parser.parse(&input[..length], Cursor::start()),
            Err(ParseError::UnexpectedEnd)
        );
    }
    let typed: (Cursor, (u16, i16)) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(typed, (Cursor { byte: 4, bit: 0 }, (0x1234, -3)));
    assert_eq!(
        parser.parse_with(&input, Cursor::start(), InputStatus::Partial),
        ParseOutcome::Success(typed.0, typed.1)
    );
}

#[test]
fn typed_predicates_and_recovery_keep_existing_control_semantics() {
    let parser = Choice {
        first: Verify {
            parser: BeI16,
            predicate: |value: &i16| *value >= 0,
        },
        second: BeI16,
    };
    assert_eq!(
        parser.parse(&[0xff, 0xfd], Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, -3i16))
    );
    let optional = Optional { parser: BeU32 };
    assert_eq!(
        optional.parse(&[1, 2], Cursor::start()),
        Ok((Cursor::start(), None))
    );
    assert_eq!(
        optional.parse_with(&[1, 2], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        optional.parse(&[], Cursor { byte: 0, bit: 1 }),
        Err(ParseError::InvalidCursor)
    );
}
