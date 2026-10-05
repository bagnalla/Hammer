#[path = "../examples/support/flags.rs"]
mod flags_example;

use flags_example::{parse_flags, Flags};
use rusthammer::{read_bit, take_aligned, Bit, Bits, ConfigError, Cursor, ParseError, Parser, Seq};

fn read_bits(input: &[u8], cursor: Cursor, width: u8) -> Result<(Cursor, u64), ParseError> {
    let parser = Bits::new(width).unwrap();
    rusthammer::read_bits(input, cursor, &parser)
}

#[test]
fn numeric_field_construction_accepts_exactly_the_supported_widths() {
    for width in 0..=u8::MAX {
        if width <= 64 {
            assert_eq!(Bits::new(width).unwrap().width(), width);
        } else {
            assert_eq!(Bits::new(width), Err(ConfigError::InvalidWidth));
        }
    }
}

#[test]
fn every_byte_reads_in_most_significant_bit_order() {
    for byte in 0..=u8::MAX {
        let input = [byte];
        let text = format!("{byte:08b}");
        let mut cursor = Cursor::start();
        for expected in text.bytes() {
            let (next, actual) = read_bit(&input, cursor).unwrap();
            assert_eq!(actual, expected == b'1');
            cursor = next;
        }
        assert_eq!(cursor, Cursor { byte: 1, bit: 0 });
        assert_eq!(read_bit(&input, cursor), Err(ParseError::UnexpectedEnd));
    }
}

#[test]
fn sequence_crosses_a_byte_boundary_without_alignment() {
    let parser = Seq {
        first: Bit,
        second: Bit,
    };
    assert_eq!(
        parser.parse(&[0x01, 0x80], Cursor { byte: 0, bit: 7 }),
        Ok((Cursor { byte: 1, bit: 1 }, (true, true)))
    );
}

#[test]
fn typed_header_preserves_the_remaining_bits() {
    assert_eq!(
        parse_flags(&[0xa0], Cursor::start()),
        Ok((
            Cursor { byte: 0, bit: 3 },
            Flags {
                urgent: true,
                encrypted: false,
                compressed: true,
            }
        ))
    );
    assert_eq!(
        parse_flags(&[0x01, 0x80], Cursor { byte: 0, bit: 7 }),
        Ok((
            Cursor { byte: 1, bit: 2 },
            Flags {
                urgent: true,
                encrypted: true,
                compressed: false,
            }
        ))
    );
}

#[test]
fn failed_sequence_leaves_the_callers_cursor_available() {
    let cursor = Cursor { byte: 0, bit: 7 };
    assert_eq!(parse_flags(&[0x01], cursor), Err(ParseError::UnexpectedEnd));
    assert_eq!(
        Bit.parse(&[0x01], cursor),
        Ok((Cursor { byte: 1, bit: 0 }, true))
    );
}

#[test]
fn invalid_cursors_and_truncation_are_distinct() {
    let input = [0];
    for cursor in [
        Cursor { byte: 0, bit: 8 },
        Cursor { byte: 1, bit: 1 },
        Cursor { byte: 2, bit: 0 },
        Cursor {
            byte: usize::MAX,
            bit: u8::MAX,
        },
    ] {
        assert_eq!(read_bit(&input, cursor), Err(ParseError::InvalidCursor));
        assert_eq!(
            take_aligned(&input, cursor, 0),
            Err(ParseError::InvalidCursor)
        );
    }
    assert_eq!(
        read_bit(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        read_bit(&input, Cursor { byte: 1, bit: 0 }),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn payload_is_a_borrowed_view_of_the_input() {
    let input = [10, 20, 30, 40];
    let (next, payload) = take_aligned(&input, Cursor { byte: 1, bit: 0 }, 2).unwrap();
    assert_eq!(next, Cursor { byte: 3, bit: 0 });
    assert_eq!(payload, &[20, 30]);
    assert_eq!(payload.as_ptr(), input[1..].as_ptr());
}

#[test]
fn aligned_payload_handles_empty_truncated_and_huge_lengths() {
    assert_eq!(
        take_aligned(&[], Cursor::start(), 0),
        Ok((Cursor::start(), &[][..]))
    );
    assert_eq!(
        take_aligned(&[0], Cursor::start(), usize::MAX),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        take_aligned(&[0], Cursor { byte: 0, bit: 1 }, 0),
        Err(ParseError::Unaligned)
    );
    assert_eq!(
        take_aligned(&[0], Cursor { byte: 1, bit: 0 }, 1),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn unaligned_bytes_match_every_two_byte_value() {
    for word in 0..=u16::MAX {
        let input = word.to_be_bytes();
        for offset in 0..8 {
            assert_eq!(
                read_bits(
                    &input,
                    Cursor {
                        byte: 0,
                        bit: offset
                    },
                    8
                ),
                Ok((
                    Cursor {
                        byte: 1,
                        bit: offset
                    },
                    u64::from((word >> (8 - offset)) & 0xff),
                )),
            );
        }
    }
}

#[test]
fn every_width_and_offset_matches_a_binary_string_oracle() {
    for input in [
        [0; 9],
        [0xff; 9],
        [0x80, 0x01, 0x55, 0xaa, 0x7f, 0x81, 0xfe, 0x42, 0x99],
    ] {
        let text: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
        for start in 0..=text.len() {
            let cursor = Cursor {
                byte: start / 8,
                bit: (start % 8) as u8,
            };
            for width in 0..=64 {
                let end = start + usize::from(width);
                let expected = if end > text.len() {
                    Err(ParseError::UnexpectedEnd)
                } else {
                    let value = if width == 0 {
                        0
                    } else {
                        u64::from_str_radix(&text[start..end], 2).unwrap()
                    };
                    Ok((
                        Cursor {
                            byte: end / 8,
                            bit: (end % 8) as u8,
                        },
                        value,
                    ))
                };
                assert_eq!(read_bits(&input, cursor, width), expected);
            }
        }
    }
}

#[test]
fn numeric_fields_validate_cursors_including_empty_fields() {
    let invalid = Cursor {
        byte: usize::MAX,
        bit: u8::MAX,
    };
    for cursor in [
        invalid,
        Cursor { byte: 0, bit: 8 },
        Cursor { byte: 1, bit: 1 },
        Cursor { byte: 2, bit: 0 },
    ] {
        for width in 0..=64 {
            assert_eq!(
                read_bits(&[0], cursor, width),
                Err(ParseError::InvalidCursor)
            );
        }
    }
    assert_eq!(read_bits(&[], Cursor::start(), 0), Ok((Cursor::start(), 0)));
    assert_eq!(
        read_bits(&[], Cursor::start(), 1),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn numeric_fields_compose_with_typed_bits_and_borrowed_payloads() {
    let parser = Seq {
        first: Bit,
        second: Seq {
            first: Bits::new(7).unwrap(),
            second: rusthammer::TakeAligned { count: 2 },
        },
    };
    let input = [0xd5, 0x12, 0x34];
    let (next, (flag, (number, payload))) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 3, bit: 0 });
    assert!(flag);
    assert_eq!(number, 0x55u64);
    assert_eq!(payload, &input[1..]);
    assert_eq!(payload.as_ptr(), input[1..].as_ptr());
    assert_eq!(
        parser.parse(&input[..2], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
}
