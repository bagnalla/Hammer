use rusthammer::{
    And, BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Bits, Byte, Choice, ConfigError, Cursor,
    IntRange, Map, Not, Optional, ParseContext, ParseError, ParseOutcome, Parser, Seq, SignedBits,
    I8,
};
use rusthammer::{Eval, Grammar};
use std::cell::Cell;
use std::rc::Rc;

#[test]
fn constructors_validate_all_byte_bounds_and_expose_immutable_endpoints() {
    for lower in 0..=u8::MAX {
        for upper in 0..=u8::MAX {
            let range = IntRange::new(Byte, lower, upper);
            if lower <= upper {
                let range = range.unwrap();
                let copied = range;
                assert_eq!((*range.lower(), *copied.upper()), (lower, upper));
            } else {
                assert!(matches!(range, Err(ConfigError::InvalidBounds)));
            }
            let lower = i8::from_ne_bytes([lower]);
            let upper = i8::from_ne_bytes([upper]);
            match IntRange::new(I8, lower, upper) {
                Ok(range) => {
                    assert!(lower <= upper);
                    assert_eq!((*range.lower(), *range.upper()), (lower, upper));
                }
                Err(error) => {
                    assert!(lower > upper);
                    assert_eq!(error, ConfigError::InvalidBounds);
                }
            }
        }
    }
}

// Mathematical binary decoding and signed interpretation in i128, independent
// of the library's numeric readers, comparisons, and cursor arithmetic.
fn oracle(
    input: &[u8],
    cursor: Cursor,
    width: usize,
    signed: bool,
    lower: i128,
    upper: i128,
    context: ParseContext,
) -> ParseOutcome<i128> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return ParseOutcome::Error(ParseError::InvalidCursor);
    }
    let bits: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    let start = 8 * cursor.byte + usize::from(cursor.bit);
    let end = start + width;
    let Some(field) = bits.get(start..end) else {
        return match context.status {
            rusthammer::InputStatus::Partial => ParseOutcome::NeedMore,
            rusthammer::InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
        };
    };
    let raw = if field.is_empty() {
        0
    } else {
        i128::from_str_radix(field, 2).unwrap()
    };
    let value = if signed && field.starts_with('1') {
        raw - (1i128 << width)
    } else {
        raw
    };
    if !(lower..=upper).contains(&value) {
        return ParseOutcome::Error(ParseError::Mismatch);
    }
    ParseOutcome::Success(
        Cursor {
            byte: end / 8,
            bit: (end % 8) as u8,
        },
        value,
    )
}

fn widen<T: Into<i128>>(outcome: ParseOutcome<T>) -> ParseOutcome<i128> {
    match outcome {
        ParseOutcome::Success(next, value) => ParseOutcome::Success(next, value.into()),
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

fn check<P, T>(parser: P, width: usize, signed: bool, bounds: &[(T, T)])
where
    P: Copy + for<'input> Parser<'input, Output = T>,
    T: Copy + Ord + Into<i128>,
{
    for &(lower, upper) in bounds {
        let range = IntRange::new(parser, lower, upper).unwrap();
        for input in [
            [0; 10],
            [255; 10],
            [0x80, 0x01, 0x55, 0xaa, 0x7f, 0x81, 0xfe, 0x42, 0x99, 0],
        ] {
            for byte in (0..=input.len() + 1).chain([usize::MAX]) {
                for bit in (0..=8).chain([u8::MAX]) {
                    let cursor = Cursor { byte, bit };
                    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                        assert_eq!(
                            widen(range.parse_with(&input, cursor, context)),
                            oracle(
                                &input,
                                cursor,
                                width,
                                signed,
                                lower.into(),
                                upper.into(),
                                context
                            )
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn native_and_variable_width_fields_match_an_independent_oracle() {
    check(
        Byte,
        8,
        false,
        &[(0, u8::MAX), (0, 0), (255, 255), (b'0', b'9')],
    );
    check(I8, 8, true, &[(i8::MIN, i8::MAX), (i8::MIN, -1), (0, 0)]);
    check(
        BeU16,
        16,
        false,
        &[(0, u16::MAX), (1, 4096), (u16::MAX, u16::MAX)],
    );
    check(
        BeI16,
        16,
        true,
        &[(i16::MIN, i16::MAX), (-100, 100), (-1, -1)],
    );
    check(
        BeU32,
        32,
        false,
        &[(0, u32::MAX), (u32::MAX, u32::MAX), (123, 456)],
    );
    check(
        BeI32,
        32,
        true,
        &[(i32::MIN, i32::MAX), (i32::MIN, 0), (1, i32::MAX)],
    );
    check(
        BeU64,
        64,
        false,
        &[(0, u64::MAX), (1 << 63, u64::MAX), (u64::MAX, u64::MAX)],
    );
    check(
        BeI64,
        64,
        true,
        &[(i64::MIN, i64::MAX), (i64::MIN, i64::MIN), (-1, 0)],
    );
    check(
        Bits::new(13).unwrap(),
        13,
        false,
        &[(0, 8191), (10, 20), (8192, 9000)],
    );
    check(
        SignedBits::new(13).unwrap(),
        13,
        true,
        &[(-4096, 4095), (-100, 100)],
    );
    check(Bits::new(0).unwrap(), 0, false, &[(0, 0), (1, 2)]);
}

fn encode_byte(value: u8, bit: u8) -> [u8; 2] {
    ((u16::from(value) << (8 - bit)) | 1).to_be_bytes()
}

#[test]
fn every_byte_is_filtered_inclusively_at_every_bit_offset() {
    for (lower, upper) in [(0, 0), (0, 255), (255, 255), (b'0', b'9'), (127, 128)] {
        let range = IntRange::new(Byte, lower, upper).unwrap();
        for value in 0..=u8::MAX {
            for bit in 0..8 {
                let input = encode_byte(value, bit);
                let expected = if (lower..=upper).contains(&value) {
                    Ok((Cursor { byte: 1, bit }, value))
                } else {
                    Err(ParseError::Mismatch)
                };
                assert_eq!(range.parse(&input, Cursor { byte: 0, bit }), expected);
            }
        }
    }
}

#[test]
fn full_integer_extremes_are_accepted_without_bound_conversions() {
    for value in [0, (1u64 << 63) - 1, 1u64 << 63, u64::MAX] {
        let range = IntRange::new(BeU64, value, value).unwrap();
        assert_eq!(
            range.parse(&value.to_be_bytes(), Cursor::start()),
            Ok((Cursor { byte: 8, bit: 0 }, value))
        );
    }
    for value in [i64::MIN, i64::MIN + 1, -1, 0, i64::MAX] {
        let range = IntRange::new(BeI64, value, value).unwrap();
        assert_eq!(
            range.parse(&value.to_be_bytes(), Cursor::start()),
            Ok((Cursor { byte: 8, bit: 0 }, value))
        );
    }
}

#[test]
fn short_input_remains_incomplete_even_when_the_prefix_is_out_of_range() {
    let range = IntRange::new(BeU16, 0, 100).unwrap();
    assert_eq!(
        range.parse_with(&[0xff], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        range.parse(&[0xff], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        range.parse(&[0xff, 0], Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        range.parse(&[0, 100], Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, 100))
    );
}

#[test]
fn choice_optionality_and_lookahead_keep_existing_recovery_rules() {
    let digit = IntRange::new(Byte, b'0', b'9').unwrap();
    let choice = Choice {
        first: digit,
        second: Byte,
    };
    assert_eq!(
        choice.parse(b"x", Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, b'x'))
    );
    assert_eq!(
        Optional { parser: digit }.parse(b"x", Cursor::start()),
        Ok((Cursor::start(), None))
    );
    assert_eq!(
        Optional { parser: digit }.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        And { parser: digit }.parse(b"7", Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    assert_eq!(
        Not { parser: digit }.parse(b"x", Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    let sequence = Seq {
        first: &digit,
        second: digit,
    };
    assert_eq!(
        sequence.parse(b"42", Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, (b'4', b'2')))
    );
}

struct Stub<'a> {
    outcome: ParseOutcome<u16>,
    calls: &'a Cell<usize>,
}
impl<'input> Grammar<'input> for Stub<'_> {
    type Output = u16;
}

impl<'input, Backend> Eval<'input, Backend> for Stub<'_> {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<u16> {
        self.calls.set(self.calls.get() + 1);
        match &self.outcome {
            ParseOutcome::Success(next, value) => ParseOutcome::Success(*next, *value),
            ParseOutcome::Error(error) => ParseOutcome::Error(*error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn construction_never_parses_and_child_errors_propagate_once() {
    let calls = Cell::new(0);
    assert!(matches!(
        IntRange::new(
            Stub {
                outcome: ParseOutcome::NeedMore,
                calls: &calls
            },
            2,
            1
        ),
        Err(ConfigError::InvalidBounds)
    ));
    assert_eq!(calls.get(), 0);
    for error in [
        ParseError::Mismatch,
        ParseError::UnexpectedEnd,
        ParseError::TrailingInput,
        ParseError::InvalidCursor,
        ParseError::Unaligned,
        ParseError::NonProgress,
        ParseError::CountOverflow,
    ] {
        let range = IntRange::new(
            Stub {
                outcome: ParseOutcome::Error(error),
                calls: &calls,
            },
            0,
            100,
        )
        .unwrap();
        assert_eq!(calls.get(), 0);
        assert_eq!(
            range.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
            ParseOutcome::Error(error)
        );
        assert_eq!(calls.replace(0), 1);
    }
    let raw = Cursor {
        byte: usize::MAX,
        bit: u8::MAX,
    };
    let range = IntRange::new(
        Stub {
            outcome: ParseOutcome::Success(raw, 7),
            calls: &calls,
        },
        7,
        7,
    )
    .unwrap();
    assert_eq!(range.parse(&[], raw), Ok((raw, 7)));
    assert_eq!(calls.get(), 1);
}

#[derive(Debug)]
struct Owned {
    value: u8,
    drops: Rc<Cell<usize>>,
}
impl PartialEq for Owned {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl Eq for Owned {}
impl PartialOrd for Owned {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Owned {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}
impl Drop for Owned {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

#[test]
fn owned_bounds_and_outputs_need_no_copy_or_clone_and_drop_once() {
    let drops = Rc::new(Cell::new(0));
    let owned = |value| Owned {
        value,
        drops: drops.clone(),
    };
    {
        let range = IntRange::new(
            Map {
                parser: Byte,
                map: &owned,
            },
            owned(10),
            owned(20),
        )
        .unwrap();
        let (_, value) = range.parse(&[15], Cursor::start()).unwrap();
        assert_eq!(value.value, 15);
        assert_eq!(drops.get(), 0);
        drop(value);
        assert_eq!(drops.get(), 1);
        assert_eq!(
            range.parse(&[30], Cursor::start()),
            Err(ParseError::Mismatch)
        );
        assert_eq!(drops.get(), 2);
        assert_eq!((range.lower().value, range.upper().value), (10, 20));
    }
    assert_eq!(drops.get(), 4); // Two parsed outputs and two stored bounds.
    assert!(matches!(
        IntRange::new(
            Map {
                parser: Byte,
                map: &owned
            },
            owned(20),
            owned(10)
        ),
        Err(ConfigError::InvalidBounds)
    ));
    assert_eq!(drops.get(), 6);
}
