use rusthammer::{
    And, ByteIn, ByteNotIn, Choice, Cursor, FoldRepeat, Not, Optional, ParseContext, ParseError,
    ParseOutcome, Parser, Seq,
};
use std::collections::BTreeSet;

// Independent oracle: decode via a binary string, then use a mathematical set.
fn oracle(
    set: &BTreeSet<u8>,
    excluded: bool,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<u8> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return ParseOutcome::Error(ParseError::InvalidCursor);
    }
    let bits: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    let position = cursor.byte * 8 + usize::from(cursor.bit);
    let Some(field) = bits.get(position..position + 8) else {
        return match context.status {
            rusthammer::InputStatus::Partial => ParseOutcome::NeedMore,
            rusthammer::InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
        };
    };
    let value = u8::from_str_radix(field, 2).unwrap();
    if set.contains(&value) == excluded {
        ParseOutcome::Error(ParseError::Mismatch)
    } else {
        ParseOutcome::Success(
            Cursor {
                byte: cursor.byte + 1,
                bit: cursor.bit,
            },
            value,
        )
    }
}

fn encoded(value: u8, offset: u8) -> Vec<u8> {
    let mut bits = format!("{}{value:08b}01100101", &"1010101"[..usize::from(offset)]);
    bits.push_str(&"0".repeat((8 - bits.len() % 8) % 8));
    bits.as_bytes()
        .chunks_exact(8)
        .map(|chunk| u8::from_str_radix(core::str::from_utf8(chunk).unwrap(), 2).unwrap())
        .collect()
}

#[test]
fn every_byte_and_offset_matches_set_oracle_with_truncation_and_both_statuses() {
    let sets = [
        vec![],
        vec![0],
        vec![255],
        vec![255, 0, 128, 0, 255],
        b"0-9".to_vec(),
        b"0123456789".to_vec(),
        b"\r\n".to_vec(),
        (0..=255).collect(),
        (0..=255).rev().collect(),
        (0..=255).step_by(2).collect(),
        // More entries than the byte domain; duplicates remain harmless.
        [0, 128, 255].repeat(100),
    ];
    for bytes in &sets {
        let set: BTreeSet<_> = bytes.iter().copied().collect();
        let include = ByteIn::new(bytes);
        let exclude = ByteNotIn::new(bytes);
        for value in 0..=255 {
            assert_eq!(include.accepts(value), set.contains(&value));
            assert_eq!(exclude.accepts(value), !set.contains(&value));
            for bit in 0..8 {
                let input = encoded(value, bit);
                let cursor = Cursor { byte: 0, bit };
                for length in 0..=input.len() {
                    let prefix = &input[..length];
                    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                        assert_eq!(
                            include.parse_with(prefix, cursor, context),
                            oracle(&set, false, prefix, cursor, context),
                            "include {bytes:?}, value={value}, bit={bit}, length={length}, {context:?}"
                        );
                        assert_eq!(
                            exclude.parse_with(prefix, cursor, context),
                            oracle(&set, true, prefix, cursor, context),
                            "exclude {bytes:?}, value={value}, bit={bit}, length={length}, {context:?}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn every_singleton_distinguishes_every_byte() {
    for member in 0..=255 {
        let bytes = [member];
        let include = ByteIn::new(&bytes);
        let exclude = ByteNotIn::new(&bytes);
        for value in 0..=255 {
            let success = Ok((Cursor { byte: 1, bit: 0 }, value));
            let mismatch = Err(ParseError::Mismatch);
            assert_eq!(
                include.parse(&[value], Cursor::start()),
                if value == member { success } else { mismatch }
            );
            assert_eq!(
                exclude.parse(&[value], Cursor::start()),
                if value == member { mismatch } else { success }
            );
        }
    }
}

#[test]
fn arbitrary_cursors_preserve_validation_and_short_input_precedence() {
    let input = [0, 0x80, 0xff, b'9'];
    for bytes in [&[][..], &[0, 128, 255][..]] {
        let set = bytes.iter().copied().collect();
        let cursors = (0..=input.len() + 1)
            .flat_map(|byte| (0..=8).map(move |bit| Cursor { byte, bit }))
            .chain([
                Cursor {
                    byte: usize::MAX,
                    bit: 0,
                },
                Cursor {
                    byte: 0,
                    bit: u8::MAX,
                },
            ]);
        for cursor in cursors {
            for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                assert_eq!(
                    ByteIn::new(bytes).parse_with(&input, cursor, context),
                    oracle(&set, false, &input, cursor, context)
                );
                assert_eq!(
                    ByteNotIn::new(bytes).parse_with(&input, cursor, context),
                    oracle(&set, true, &input, cursor, context)
                );
            }
        }
    }
    // Even an empty inclusion set waits for a byte before testing membership.
    assert_eq!(
        ByteIn::new(b"").parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        ByteIn::new(b"").parse(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        ByteIn::new(b"").parse(b"x", Cursor::start()),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn construction_is_const_and_owns_a_fixed_bitmap() {
    const INCLUDE: ByteIn = ByteIn::new(b";,;");
    const EXCLUDE: ByteNotIn = ByteNotIn::new(b"\r\n");
    const ALLOWED: bool = INCLUDE.accepts(b';');
    const EXCLUDED: bool = EXCLUDE.accepts(b'\n');
    assert!(ALLOWED);
    assert!(!EXCLUDED);
    assert_eq!(core::mem::size_of::<ByteIn>(), 32);
    assert_eq!(core::mem::size_of::<ByteNotIn>(), 32);
    fn copyable<T: Copy>(_: T) {}
    copyable(INCLUDE);
    copyable(EXCLUDE);

    let (include, exclude) = {
        let mut allowed = vec![0x80, 0, 0x80];
        let mut excluded = vec![255, 255];
        let include = ByteIn::new(&allowed);
        let exclude = ByteNotIn::new(&excluded);
        // Construction must own the set, not retain either input slice.
        allowed.fill(255);
        excluded.fill(0);
        (include, exclude)
    };
    let output = {
        let input = vec![0x80, 0];
        let copied = include;
        let cloned = Clone::clone(&exclude);
        for value in 0..=255 {
            assert_eq!(copied.accepts(value), value == 0 || value == 0x80);
            assert_eq!(cloned.accepts(value), value != 255);
        }
        Seq {
            first: &copied,
            second: &cloned,
        }
        .parse(&input, Cursor::start())
        .unwrap()
    };
    assert_eq!(output, (Cursor { byte: 2, bit: 0 }, (0x80, 0)));
}

#[test]
fn composition_preserves_backtracking_lookahead_and_incompleteness() {
    let digit = ByteIn::new(b"0123456789");
    let other = ByteNotIn::new(b"0123456789");
    let choice = Choice {
        first: &digit,
        second: &other,
    };
    for value in 0..=255 {
        assert_eq!(
            choice.parse(&[value], Cursor::start()),
            Ok((Cursor { byte: 1, bit: 0 }, value))
        );
    }
    assert_eq!(
        Optional { parser: &digit }.parse(b"x", Cursor::start()),
        Ok((Cursor::start(), None))
    );
    assert_eq!(
        And { parser: &digit }.parse(b"7", Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    assert_eq!(
        Not { parser: &digit }.parse(b"x", Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    assert_eq!(
        choice.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        Not { parser: &digit }.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    let leading = FoldRepeat::at_least(&digit, 0, || 0usize, |count, _| count + 1);
    assert_eq!(
        leading.parse(b"12x", Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, 2))
    );
    assert_eq!(
        leading.parse_with(b"12", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}

#[test]
fn literal_sets_have_no_regular_expression_syntax() {
    let parser = ByteIn::new(b"0-9");
    for byte in [b'0', b'-', b'9'] {
        assert_eq!(
            parser.parse(&[byte], Cursor::start()),
            Ok((Cursor { byte: 1, bit: 0 }, byte))
        );
    }
    assert_eq!(
        parser.parse(b"5", Cursor::start()),
        Err(ParseError::Mismatch)
    );
}
