use rusthammer::{
    And, Byte, BytePattern, Choice, Cursor, InputStatus, Not, Optional, ParseError, ParseOutcome,
    Parser, Seq,
};

fn binary(input: &[u8]) -> String {
    input.iter().map(|byte| format!("{byte:08b}")).collect()
}

// Independent binary-string oracle, including ordered byte comparison and finality.
fn pattern_oracle<'p>(
    pattern: &'p [u8],
    input: &[u8],
    cursor: Cursor,
    status: InputStatus,
) -> ParseOutcome<&'p [u8]> {
    if pattern.is_empty() {
        return ParseOutcome::Success(cursor, pattern);
    }
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return ParseOutcome::Error(ParseError::InvalidCursor);
    }
    let bits = binary(input);
    let mut position = cursor.byte * 8 + usize::from(cursor.bit);
    for expected in pattern {
        let Some(field) = bits.get(position..position + 8) else {
            return match status {
                InputStatus::Partial => ParseOutcome::NeedMore,
                InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
            };
        };
        if field != format!("{expected:08b}") {
            return ParseOutcome::Error(ParseError::Mismatch);
        }
        position += 8;
    }
    ParseOutcome::Success(
        Cursor {
            byte: position / 8,
            bit: (position % 8) as u8,
        },
        pattern,
    )
}

#[test]
fn byte_exhausts_two_byte_inputs_at_every_offset() {
    for word in 0..=u16::MAX {
        let input = word.to_be_bytes();
        for bit in 0..8 {
            let expected = ((word >> (8 - bit)) & 255) as u8;
            let cursor = Cursor { byte: 0, bit };
            let next = Cursor { byte: 1, bit };
            assert_eq!(Byte.parse(&input, cursor), Ok((next, expected)));
            assert_eq!(
                Byte.parse_with(&input, cursor, InputStatus::Partial),
                ParseOutcome::Success(next, expected)
            );
        }
    }
}

#[test]
fn byte_checks_cursor_before_input_exhaustion() {
    for status in [InputStatus::Partial, InputStatus::Final] {
        for cursor in [
            Cursor { byte: 0, bit: 8 },
            Cursor { byte: 1, bit: 1 },
            Cursor { byte: 2, bit: 0 },
            Cursor {
                byte: usize::MAX,
                bit: u8::MAX,
            },
        ] {
            assert_eq!(
                Byte.parse_with(&[0], cursor, status),
                ParseOutcome::Error(ParseError::InvalidCursor)
            );
        }
        for bit in 1..8 {
            let expected = match status {
                InputStatus::Partial => ParseOutcome::NeedMore,
                InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
            };
            assert_eq!(
                Byte.parse_with(&[0], Cursor { byte: 0, bit }, status),
                expected
            );
        }
    }
    assert_eq!(
        Byte.parse(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        Byte.parse_with(&[0], Cursor { byte: 1, bit: 0 }, InputStatus::Partial),
        ParseOutcome::NeedMore
    );
}

#[test]
fn patterns_match_binary_string_oracle_at_every_cursor() {
    let input = [
        0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xff, 0, 0x80,
    ];
    let bits = binary(&input);
    for byte in 0..=input.len() + 1 {
        for bit in 0..=8 {
            let cursor = Cursor { byte, bit };
            let start = byte * 8 + usize::from(bit);
            let decoded: Vec<_> = bits
                .get(start..)
                .unwrap_or("")
                .as_bytes()
                .chunks_exact(8)
                .map(|chunk| u8::from_str_radix(core::str::from_utf8(chunk).unwrap(), 2).unwrap())
                .collect();
            for len in 0..=12 {
                let mut pattern: Vec<_> = decoded
                    .iter()
                    .copied()
                    .chain([0, 255].into_iter().cycle())
                    .take(len)
                    .collect();
                for mutation in 0..=len {
                    if mutation < len {
                        pattern[mutation] ^= 0x80;
                    }
                    for status in [InputStatus::Partial, InputStatus::Final] {
                        assert_eq!(
                            BytePattern::new(&pattern).parse_with(&input, cursor, status),
                            pattern_oracle(&pattern, &input, cursor, status),
                            "pattern={pattern:?}, cursor={cursor:?}, status={status:?}"
                        );
                    }
                    if mutation < len {
                        pattern[mutation] ^= 0x80;
                    }
                }
            }
        }
    }
}

#[test]
fn output_borrows_pattern_independently_of_input_and_parser() {
    let pattern = [0xab, 0xcd];
    let matched = {
        let input = [0x55, 0xe6, 0x80];
        let parser = BytePattern::new(&pattern);
        assert!(core::ptr::eq(parser.pattern(), &pattern[..]));
        let (next, value) = (&parser).parse(&input, Cursor { byte: 0, bit: 1 }).unwrap();
        assert_eq!(next, Cursor { byte: 2, bit: 1 });
        assert!(core::ptr::eq(value, &pattern[..]));
        value
    };
    assert!(core::ptr::eq(matched, &pattern[..]));
    fn copyable<T: Copy>(_: T) {}
    copyable(Byte);
    copyable(BytePattern::new(&pattern));
}

#[test]
fn empty_pattern_is_empty_success_even_at_invalid_cursors() {
    let parser = BytePattern::new(&[]);
    for cursor in [
        Cursor::start(),
        Cursor {
            byte: usize::MAX,
            bit: u8::MAX,
        },
    ] {
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                parser.parse_with(&[], cursor, status),
                ParseOutcome::Success(cursor, &[][..])
            );
        }
    }
}

#[test]
fn long_patterns_and_embedded_zeros_are_supported() {
    // C Hammer's token regression includes the formerly unsupported length 256.
    let pattern: Vec<u8> = (0..=255).collect();
    let parser = BytePattern::new(&pattern);
    assert_eq!(
        parser.parse(&pattern, Cursor::start()),
        Ok((Cursor { byte: 256, bit: 0 }, &pattern[..]))
    );
    assert_eq!(
        parser.parse(&pattern[..255], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    let mut input = pattern.clone();
    input[255] = 0;
    assert_eq!(
        parser.parse(&input, Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        BytePattern::new(&[0]).parse(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn partial_patterns_distinguish_mismatch_from_incomplete_bytes() {
    let parser = BytePattern::new(b"ab");
    assert_eq!(
        parser.parse_with(b"x", Cursor::start(), InputStatus::Partial),
        ParseOutcome::Error(ParseError::Mismatch)
    );
    assert_eq!(
        parser.parse_with(b"a", Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse(b"a", Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    // Incomplete individual bytes are not compared bit by bit.
    assert_eq!(
        parser.parse_with(&[0xff], Cursor { byte: 0, bit: 1 }, InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    let pattern = [0xab, 0xcd];
    let input = [0x55, 0xe6, 0x80];
    let parser = BytePattern::new(&pattern);
    let cursor = Cursor { byte: 0, bit: 1 };
    for len in 1..3 {
        assert_eq!(
            parser.parse_with(&input[..len], cursor, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
    }
    assert_eq!(
        parser.parse_with(&input, cursor, InputStatus::Partial),
        ParseOutcome::Success(Cursor { byte: 2, bit: 1 }, &pattern[..])
    );
}

#[test]
fn pattern_choice_lookahead_and_typed_sequence_preserve_semantics() {
    let long = BytePattern::new(b"ab");
    let short = BytePattern::new(b"a");
    let choice = Choice {
        first: long,
        second: short,
    };
    assert_eq!(
        choice.parse_with(b"a", Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        choice.parse(b"a", Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, &b"a"[..]))
    );
    assert_eq!(
        choice.parse(b"ax", Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, &b"a"[..]))
    );
    assert_eq!(
        Optional { parser: long }.parse_with(b"a", Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        And { parser: long }.parse(b"ab", Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    assert_eq!(
        Not { parser: long }.parse(b"ax", Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    let parser = Seq {
        first: long,
        second: Byte,
    };
    assert_eq!(
        parser.parse(b"abc", Cursor::start()),
        Ok((Cursor { byte: 3, bit: 0 }, (&b"ab"[..], b'c')))
    );
}

#[test]
fn original_hammer_token_examples() {
    assert_eq!(
        BytePattern::new(b"foobar").parse(b"foobar", Cursor::start()),
        Ok((Cursor { byte: 6, bit: 0 }, &b"foobar"[..]))
    );
    let parser = Seq {
        first: Seq {
            first: BytePattern::new(b"f"),
            second: BytePattern::new(b"ooba"),
        },
        second: BytePattern::new(b"r"),
    };
    assert_eq!(
        parser.parse(b"foobar", Cursor::start()),
        Ok((
            Cursor { byte: 6, bit: 0 },
            ((&b"f"[..], &b"ooba"[..]), &b"r"[..])
        ))
    );
}
