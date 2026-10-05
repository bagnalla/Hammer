#[path = "../examples/support/marker.rs"]
mod marker_example;

use marker_example::{parse_marker, Marker};
use rusthammer::{
    Bits, Choice, ConfigError, Cursor, End, InputStatus, Literal, ParseError, ParseOutcome, Parser,
    Seq, TakeAligned,
};

struct MustNotRun;

impl<'input> Parser<'input> for MustNotRun {
    type Output = u64;

    fn parse_with(&self, _: &'input [u8], _: Cursor, _: InputStatus) -> ParseOutcome<u64> {
        panic!("ordered choice evaluated an unreachable branch");
    }
}

#[test]
fn literals_match_every_byte_value() {
    for expected in 0..=u8::MAX {
        let parser = Literal::new(8, u64::from(expected)).unwrap();
        for actual in 0..=u8::MAX {
            let result = if actual == expected {
                Ok((Cursor { byte: 1, bit: 0 }, u64::from(expected)))
            } else {
                Err(ParseError::Mismatch)
            };
            assert_eq!(parser.parse(&[actual], Cursor::start()), result);
        }
    }
}

#[test]
fn literal_construction_checks_width_and_value_before_any_input() {
    for width in 65..=u8::MAX {
        for value in [0, u64::MAX] {
            assert_eq!(Literal::new(width, value), Err(ConfigError::InvalidWidth));
        }
    }
    for width in 0..=64 {
        let max = ((1u128 << width) - 1) as u64;
        for value in [0, max] {
            let parser = Literal::new(width, value).unwrap();
            assert_eq!(parser.width(), width);
            assert_eq!(parser.value(), value);
        }
        if width < 64 {
            assert_eq!(
                Literal::new(width, max + 1),
                Err(ConfigError::InvalidLiteral)
            );
        }
    }
}

#[test]
fn literal_input_boundaries_are_explicit() {
    let invalid = Cursor {
        byte: usize::MAX,
        bit: u8::MAX,
    };
    assert_eq!(
        Literal::new(0, 0).unwrap().parse(&[], Cursor::start()),
        Ok((Cursor::start(), 0))
    );
    assert_eq!(
        Literal::new(0, 0).unwrap().parse(&[], invalid),
        Err(ParseError::InvalidCursor)
    );
    assert_eq!(
        Literal::new(64, u64::MAX)
            .unwrap()
            .parse(&[0xff; 8], Cursor::start()),
        Ok((Cursor { byte: 8, bit: 0 }, u64::MAX))
    );
    assert_eq!(
        Literal::new(64, u64::MAX)
            .unwrap()
            .parse(&[0xff; 7], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        Literal::new(8, 0x80)
            .unwrap()
            .parse(&[1, 0], Cursor { byte: 0, bit: 7 }),
        Ok((Cursor { byte: 1, bit: 7 }, 0x80))
    );
}

#[test]
fn end_requires_the_exact_cursor_without_skipping_padding() {
    assert_eq!(End.parse(&[], Cursor::start()), Ok((Cursor::start(), ())));
    assert_eq!(
        End.parse(&[0], Cursor { byte: 1, bit: 0 }),
        Ok((Cursor { byte: 1, bit: 0 }, ()))
    );
    for bit in 0..8 {
        assert_eq!(
            End.parse(&[0], Cursor { byte: 0, bit }),
            Err(ParseError::TrailingInput)
        );
    }
    for cursor in [
        Cursor { byte: 0, bit: 8 },
        Cursor { byte: 1, bit: 1 },
        Cursor { byte: 2, bit: 0 },
        Cursor {
            byte: usize::MAX,
            bit: u8::MAX,
        },
    ] {
        assert_eq!(End.parse(&[0], cursor), Err(ParseError::InvalidCursor));
    }
}

#[test]
fn choice_restarts_after_partial_consumption_and_truncation() {
    let parser = Choice {
        first: Seq {
            first: Literal::new(8, 0xca).unwrap(),
            second: Literal::new(8, 0xff).unwrap(),
        },
        second: Seq {
            first: Bits::new(8).unwrap(),
            second: Bits::new(8).unwrap(),
        },
    };
    assert_eq!(
        parser.parse(&[0xca, 0xfe], Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, (0xca, 0xfe)))
    );

    let borrowed = Choice {
        first: TakeAligned { count: 2 },
        second: TakeAligned { count: 1 },
    };
    let input = [0xca];
    let (next, payload) = borrowed.parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 1, bit: 0 });
    assert_eq!(payload.as_ptr(), input.as_ptr());
    assert_eq!(payload, &input);
}

#[test]
fn choice_keeps_the_first_success_without_evaluating_the_second() {
    let parser = Choice {
        first: Bits::new(1).unwrap(),
        second: MustNotRun,
    };
    assert_eq!(
        parser.parse(&[0x80], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 1 }, 1))
    );
    let empty = Choice {
        first: Bits::new(0).unwrap(),
        second: MustNotRun,
    };
    assert_eq!(empty.parse(&[], Cursor::start()), Ok((Cursor::start(), 0)));
}

#[test]
fn choice_propagates_cursor_and_alignment_errors() {
    let cursor = Choice {
        first: Bits::new(0).unwrap(),
        second: MustNotRun,
    };
    assert_eq!(
        cursor.parse(&[], Cursor { byte: 0, bit: 1 }),
        Err(ParseError::InvalidCursor)
    );
    let unaligned = Choice {
        first: TakeAligned { count: 0 },
        second: TakeAligned { count: 0 },
    };
    assert_eq!(
        unaligned.parse(&[0], Cursor { byte: 0, bit: 1 }),
        Err(ParseError::Unaligned)
    );
}

#[test]
fn choice_recovers_from_trailing_input_and_returns_the_second_error() {
    let parser = Choice {
        first: Seq {
            first: Bits::new(1).unwrap(),
            second: End,
        },
        second: Seq {
            first: Bits::new(8).unwrap(),
            second: End,
        },
    };
    assert_eq!(
        parser.parse(&[0xca], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, (0xca, ())))
    );
    let rejected = Choice {
        first: Literal::new(8, 0xff).unwrap(),
        second: Bits::new(16).unwrap(),
    };
    assert_eq!(
        rejected.parse(&[0], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn grammar_construction_rejects_an_invalid_fallback() {
    fn grammar(width: u8) -> Result<Choice<Literal, Bits>, ConfigError> {
        Ok(Choice {
            first: Literal::new(8, 0xff)?,
            second: Bits::new(width)?,
        })
    }
    assert!(matches!(grammar(65), Err(ConfigError::InvalidWidth)));
    let parser = grammar(16).unwrap();
    assert_eq!(
        parser.parse(&[0xff], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, 0xff))
    );
}

#[test]
fn outer_failure_does_not_revisit_an_earlier_choice() {
    let parser = Seq {
        first: Choice {
            first: Bits::new(1).unwrap(),
            second: Bits::new(8).unwrap(),
        },
        second: End,
    };
    assert_eq!(
        parser.parse(&[0], Cursor::start()),
        Err(ParseError::TrailingInput)
    );
}

#[test]
fn complete_marker_accepts_only_its_two_alternatives() {
    let parser = Marker::new().unwrap();
    assert_eq!(
        parse_marker(&[0xca, 0xfe], Cursor::start(), &parser),
        Ok((Cursor { byte: 2, bit: 0 }, 0xcafe))
    );
    assert_eq!(
        parse_marker(&[0xca], Cursor::start(), &parser),
        Ok((Cursor { byte: 1, bit: 0 }, 0xca))
    );
    assert_eq!(
        parse_marker(&[], Cursor::start(), &parser),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        parse_marker(&[0], Cursor::start(), &parser),
        Err(ParseError::Mismatch)
    );
    for input in [&[0xca, 0xfd][..], &[0xca, 0xfe, 0][..]] {
        assert_eq!(
            parse_marker(input, Cursor::start(), &parser),
            Err(ParseError::TrailingInput)
        );
    }
}
