use rusthammer::{
    Bits, Choice, ConfigError, Cursor, Optional, ParseContext, ParseError, ParseOutcome, Parser,
    Seq, SignedBits, Verify,
};

// A binary-string/i128 oracle independent of the implementation's u64 arithmetic.
fn oracle(input: &[u8], cursor: Cursor, width: u8, context: ParseContext) -> ParseOutcome<i64> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return ParseOutcome::Error(ParseError::InvalidCursor);
    }
    let text: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    let start = 8 * cursor.byte + usize::from(cursor.bit);
    let end = start + usize::from(width);
    let Some(field) = text.get(start..end) else {
        return match context.status {
            rusthammer::InputStatus::Partial => ParseOutcome::NeedMore,
            rusthammer::InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
        };
    };
    let value = if field.is_empty() {
        0
    } else {
        let unsigned = i128::from_str_radix(field, 2).unwrap();
        if field.starts_with('1') {
            unsigned - (1i128 << width)
        } else {
            unsigned
        }
    };
    ParseOutcome::Success(
        Cursor {
            byte: end / 8,
            bit: (end % 8) as u8,
        },
        i64::try_from(value).unwrap(),
    )
}

fn encode(value: u64, width: u8, offset: u8) -> Vec<u8> {
    let mut bits = "1010101"[..usize::from(offset)].to_owned();
    if width != 0 {
        bits.push_str(&format!("{value:0width$b}", width = usize::from(width)));
    }
    bits.push_str("01100101");
    bits.push_str(&"0".repeat((8 - bits.len() % 8) % 8));
    bits.as_bytes()
        .chunks_exact(8)
        .map(|chunk| u8::from_str_radix(core::str::from_utf8(chunk).unwrap(), 2).unwrap())
        .collect()
}

#[test]
fn constructor_accepts_exactly_zero_through_sixty_four() {
    for width in 0..=u8::MAX {
        match SignedBits::new(width) {
            Ok(parser) => {
                assert!(width <= 64);
                assert_eq!(parser.width(), width);
            }
            Err(error) => {
                assert!(width > 64);
                assert_eq!(error, ConfigError::InvalidWidth);
            }
        }
    }
    const FIVE: SignedBits = match SignedBits::new(5) {
        Ok(parser) => parser,
        Err(_) => panic!("invalid fixed width"),
    };
    fn copyable<T: Copy>(_: T) {}
    copyable(FIVE);
    assert_eq!(
        FIVE.parse(&[0xe8], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 5 }, -3))
    );
}

#[test]
fn signed_byte_exhausts_every_two_byte_input_and_offset() {
    let parser = SignedBits::new(8).unwrap();
    for word in 0..=u16::MAX {
        for bit in 0..8 {
            let byte = ((word >> (8 - bit)) & 255) as u8;
            let expected = i64::from(i8::from_ne_bytes([byte]));
            let cursor = Cursor { byte: 0, bit };
            assert_eq!(
                parser.parse(&word.to_be_bytes(), cursor),
                Ok((Cursor { byte: 1, bit }, expected))
            );
        }
    }
}

#[test]
fn all_widths_and_cursors_match_the_independent_oracle() {
    for input in [
        [0; 10],
        [255; 10],
        [0x80, 0x01, 0x55, 0xaa, 0x7f, 0x81, 0xfe, 0x42, 0x99, 0],
    ] {
        for byte in 0..=input.len() + 1 {
            for bit in 0..=8 {
                let cursor = Cursor { byte, bit };
                for width in 0..=64 {
                    let parser = SignedBits::new(width).unwrap();
                    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                        assert_eq!(
                            parser.parse_with(&input, cursor, context),
                            oracle(&input, cursor, width, context),
                            "input={input:?}, cursor={cursor:?}, width={width}, context={context:?}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn sign_boundaries_at_every_width_and_offset_include_the_full_i64_range() {
    for width in 1..=64 {
        let sign = 1u64 << (width - 1);
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        for value in [0, 1, sign - 1, sign, sign | 1, mask - 1, mask] {
            let value = value & mask;
            for bit in 0..8 {
                let input = encode(value, width, bit);
                let cursor = Cursor { byte: 0, bit };
                let parser = SignedBits::new(width).unwrap();
                for len in 0..=input.len() {
                    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                        assert_eq!(
                            parser.parse_with(&input[..len], cursor, context),
                            oracle(&input[..len], cursor, width, context),
                            "value={value}, width={width}, bit={bit}, len={len}, context={context:?}"
                        );
                    }
                }
            }
        }
    }
    let parser = SignedBits::new(64).unwrap();
    for expected in [i64::MIN, i64::MIN + 1, -1, 0, 1, i64::MAX] {
        assert_eq!(
            parser.parse(&expected.to_be_bytes(), Cursor::start()),
            Ok((Cursor { byte: 8, bit: 0 }, expected))
        );
    }
}

#[test]
fn zero_width_validates_cursor_and_returns_zero_without_reading() {
    let parser = SignedBits::new(0).unwrap();
    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
        assert_eq!(
            parser.parse_with(&[], Cursor::start(), context),
            ParseOutcome::Success(Cursor::start(), 0)
        );
        for cursor in [Cursor { byte: 0, bit: 7 }, Cursor { byte: 1, bit: 0 }] {
            assert_eq!(
                parser.parse_with(&[0xff], cursor, context),
                ParseOutcome::Success(cursor, 0)
            );
        }
    }
}

#[test]
fn invalid_raw_cursors_are_fatal_even_for_empty_fields() {
    for width in 0..=64 {
        let parser = SignedBits::new(width).unwrap();
        for cursor in [
            Cursor { byte: 0, bit: 8 },
            Cursor { byte: 1, bit: 1 },
            Cursor { byte: 2, bit: 0 },
            Cursor {
                byte: usize::MAX,
                bit: u8::MAX,
            },
        ] {
            for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                assert_eq!(
                    parser.parse_with(&[0], cursor, context),
                    ParseOutcome::Error(ParseError::InvalidCursor)
                );
            }
        }
    }
}

#[test]
fn partial_retry_and_final_input_have_distinct_outcomes() {
    let parser = SignedBits::new(13).unwrap();
    let input = encode(0x1ffb, 13, 5); // -5, spanning three input bytes.
    let start = Cursor { byte: 0, bit: 5 };
    for length in 1..3 {
        assert_eq!(
            parser.parse_with(&input[..length], start, ParseContext::PARTIAL),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            parser.parse(&input[..length], start),
            Err(ParseError::UnexpectedEnd)
        );
    }
    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
        assert_eq!(
            parser.parse_with(&input, start, context),
            ParseOutcome::Success(Cursor { byte: 2, bit: 2 }, -5)
        );
    }
}

#[test]
fn signed_and_unsigned_values_sequence_with_their_own_types() {
    let signed = SignedBits::new(5).unwrap();
    let parser = Seq {
        first: &signed,
        second: Bits::new(3).unwrap(),
    };
    let typed: (Cursor, (i64, u64)) = parser.parse(&[0xed], Cursor::start()).unwrap();
    assert_eq!(typed, (Cursor { byte: 1, bit: 0 }, (-3, 5)));
    assert_eq!(
        Optional { parser: signed }.parse(&[], Cursor::start()),
        Ok((Cursor::start(), None))
    );
    assert_eq!(
        Optional { parser: signed }.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}

#[test]
fn signed_predicates_and_choice_preserve_rejection_and_rollback() {
    let parser = Choice {
        first: Verify {
            parser: SignedBits::new(8).unwrap(),
            predicate: |value: &i64| *value >= 0,
        },
        second: SignedBits::new(4).unwrap(),
    };
    assert_eq!(
        parser.parse(&[0xf1], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 4 }, -1))
    );
    assert_eq!(
        parser.parse(&[0x71], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, 113))
    );
    assert_eq!(
        parser.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}
