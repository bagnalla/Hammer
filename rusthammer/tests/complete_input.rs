#[path = "../examples/support/marker.rs"]
#[allow(dead_code)] // Complete-entry helpers are exercised in other tests.
mod marker_example;
#[path = "../examples/support/record.rs"]
#[allow(dead_code)] // Complete-entry helpers are exercised in other tests.
mod record_example;

use marker_example::Marker;
use record_example::RecordParser;
use std::cell::Cell;

use rusthammer::{
    And, Bit, Bits, ByteOrder, Choice, Cursor, End, Literal, Map, Not, Optional, ParseError,
    Parser, Seq, TakeAligned, Verify,
};

struct MustNotRun;

impl<'input> Parser<'input> for MustNotRun {
    type Output = u64;

    fn parse_with(
        &self,
        _: &'input [u8],
        _: Cursor,
        _: ByteOrder,
    ) -> Result<(Cursor, u64), ParseError> {
        panic!("this child must not run");
    }
}

#[test]
fn primitives_report_truncation_and_accept_sufficient_input() {
    let start = Cursor::start();

    assert_eq!(
        Bit.parse_with(&[], start, ByteOrder::Big),
        Err(ParseError::UnexpectedEnd)
    );
    let bits = Bits::new(8).unwrap();
    let cursor = Cursor { byte: 0, bit: 7 };

    assert_eq!(
        bits.parse_with(&[1], cursor, ByteOrder::Big),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        bits.parse_with(&[1, 0], cursor, ByteOrder::Big),
        Ok((Cursor { byte: 1, bit: 7 }, 0x80))
    );

    assert_eq!(
        TakeAligned { count: usize::MAX }.parse_with(&[1], start, ByteOrder::Big),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn invalid_cursors_and_alignment_are_fatal() {
    for byte_order in [ByteOrder::Big, ByteOrder::Little] {
        for cursor in [
            Cursor { byte: 0, bit: 8 },
            Cursor { byte: 1, bit: 1 },
            Cursor {
                byte: usize::MAX,
                bit: 0,
            },
        ] {
            assert_eq!(
                Bit.parse_with(&[0], cursor, byte_order),
                Err(ParseError::InvalidCursor)
            );
            assert_eq!(
                Bits::new(0).unwrap().parse_with(&[0], cursor, byte_order),
                Err(ParseError::InvalidCursor)
            );
            assert_eq!(
                End.parse_with(&[0], cursor, byte_order),
                Err(ParseError::InvalidCursor)
            );
        }
        let cursor = Cursor { byte: 0, bit: 1 };
        assert_eq!(
            Optional {
                parser: TakeAligned { count: 0 }
            }
            .parse_with(&[0], cursor, byte_order),
            Err(ParseError::Unaligned)
        );
        assert_eq!(
            Not {
                parser: TakeAligned { count: 0 }
            }
            .parse_with(&[0], cursor, byte_order),
            Err(ParseError::Unaligned)
        );
    }
}

#[test]
fn choice_retries_a_shorter_alternative_after_truncation() {
    let parser = Choice {
        first: Literal::new(16, 0x6162).unwrap(),
        second: Literal::new(8, 0x61).unwrap(),
    };
    let start = Cursor::start();

    assert_eq!(
        parser.parse_with(b"a", start, ByteOrder::Big),
        Ok((Cursor { byte: 1, bit: 0 }, 0x61))
    );
    assert_eq!(
        parser.parse_with(b"ab", start, ByteOrder::Big),
        Ok((Cursor { byte: 2, bit: 0 }, 0x6162))
    );
    assert_eq!(
        parser.parse_with(b"ac", start, ByteOrder::Big),
        Ok((Cursor { byte: 1, bit: 0 }, 0x61))
    );
    let guarded = Choice {
        first: Bits::new(16).unwrap(),
        second: MustNotRun,
    };
    assert_eq!(
        guarded.parse(b"ab", start),
        Ok((Cursor { byte: 2, bit: 0 }, 0x6162))
    );
}

#[test]
fn optionality_and_lookahead_handle_truncation() {
    let ab = Literal::new(16, 0x6162).unwrap();
    let start = Cursor::start();

    assert_eq!(
        Optional { parser: ab }.parse_with(b"a", start, ByteOrder::Big),
        Ok((start, None))
    );
    assert_eq!(
        And { parser: ab }.parse_with(b"a", start, ByteOrder::Big),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        Not { parser: ab }.parse_with(b"a", start, ByteOrder::Big),
        Ok((start, ()))
    );
    assert_eq!(
        Optional { parser: ab }.parse_with(b"ab", start, ByteOrder::Big),
        Ok((Cursor { byte: 2, bit: 0 }, Some(0x6162)))
    );
    assert_eq!(
        And { parser: ab }.parse_with(b"ab", start, ByteOrder::Big),
        Ok((start, ()))
    );
    assert_eq!(
        Not { parser: ab }.parse_with(b"ab", start, ByteOrder::Big),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        Optional { parser: ab }.parse_with(b"ac", start, ByteOrder::Big),
        Ok((start, None))
    );
    assert_eq!(
        Not { parser: ab }.parse_with(b"ac", start, ByteOrder::Big),
        Ok((start, ()))
    );
}

#[test]
fn sequence_and_callbacks_stop_on_errors() {
    let start = Cursor::start();

    let calls = Cell::new(0);
    let mapped = Map {
        parser: Bits::new(16).unwrap(),
        map: |value| {
            calls.set(calls.get() + 1);
            value
        },
    };
    let verified = Verify {
        parser: Bits::new(16).unwrap(),
        predicate: |_: &u64| {
            calls.set(calls.get() + 1);
            true
        },
    };

    assert_eq!(
        Seq {
            first: Bits::new(16).unwrap(),
            second: MustNotRun
        }
        .parse(b"a", start),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(mapped.parse(b"a", start), Err(ParseError::UnexpectedEnd));
    assert_eq!(verified.parse(b"a", start), Err(ParseError::UnexpectedEnd));
    assert_eq!(calls.get(), 0);
    assert!(matches!(
        mapped.parse_with(b"ab", start, ByteOrder::Big),
        Ok((_, 0x6162))
    ));
    assert!(matches!(
        verified.parse_with(b"ab", start, ByteOrder::Big),
        Ok((_, 0x6162))
    ));
    assert_eq!(calls.get(), 2);
}

#[test]
fn end_checks_consumption_and_empty_parsers_can_succeed() {
    let start = Cursor::start();

    assert_eq!(End.parse_with(&[], start, ByteOrder::Big), Ok((start, ())));
    assert_eq!(
        End.parse_with(&[0], start, ByteOrder::Big),
        Err(ParseError::TrailingInput)
    );

    assert_eq!(
        Bits::new(0).unwrap().parse_with(&[], start, ByteOrder::Big),
        Ok((start, 0))
    );
    assert_eq!(
        Optional {
            parser: Bits::new(0).unwrap()
        }
        .parse_with(&[], start, ByteOrder::Big),
        Ok((start, Some(0)))
    );
    assert_eq!(
        Not {
            parser: Bits::new(0).unwrap()
        }
        .parse_with(&[], start, ByteOrder::Big),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn prefix_success_borrows_the_original_input() {
    let input = [0, 0xca, 0xfe, 1];
    let parser = Optional {
        parser: TakeAligned { count: 2 },
    };
    let Ok((next, Some(payload))) =
        parser.parse_with(&input, Cursor { byte: 1, bit: 0 }, ByteOrder::Big)
    else {
        panic!("expected prefix success")
    };
    assert_eq!(next, Cursor { byte: 3, bit: 0 });
    assert_eq!(payload, &input[1..3]);
    assert_eq!(payload.as_ptr(), input[1..].as_ptr());
}

#[test]
fn marker_selects_an_alternative_and_requires_end_of_input() {
    let parser = Marker::new().unwrap();
    assert_eq!(
        parser.parse(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        parser.parse_with(&[0xca], Cursor::start(), ByteOrder::Big),
        Ok((Cursor { byte: 1, bit: 0 }, 0xca))
    );
    assert_eq!(
        parser.parse_with(&[0xca, 0xfe], Cursor::start(), ByteOrder::Big),
        Ok((Cursor { byte: 2, bit: 0 }, 0xcafe))
    );
    assert_eq!(
        parser.parse_with(&[0xca, 0xfe, 0], Cursor::start(), ByteOrder::Big),
        Err(ParseError::TrailingInput)
    );
}

#[test]
fn records_reject_every_truncated_prefix() {
    let parser = RecordParser::new().unwrap();
    for count in [0usize, 1, 7, 1024] {
        let mut input = vec![0xff, 0x25, (count >> 8) as u8, count as u8];
        input.extend((0..count).map(|i| i as u8));
        let start = Cursor { byte: 1, bit: 0 };
        for available in 1..=input.len() {
            if available < input.len() {
                assert_eq!(
                    parser.parse_with(&input[..available], start, ByteOrder::Big),
                    Err(ParseError::UnexpectedEnd)
                );
            }
        }
        let Ok((next, record)) = parser.parse_with(&input, start, ByteOrder::Big) else {
            panic!("expected complete record")
        };
        assert_eq!(
            next,
            Cursor {
                byte: input.len(),
                bit: 0
            }
        );
        assert_eq!(record.version, 1);
        assert_eq!(record.flags, 5);
        assert_eq!(record.payload, &input[4..]);
        assert_eq!(record.payload.as_ptr(), input[4..].as_ptr());
    }
    assert_eq!(
        parser.parse_with(&[0, 0, 0], Cursor::start(), ByteOrder::Big),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        parser.parse_with(&[0x20, 4, 1], Cursor::start(), ByteOrder::Big),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        parser.parse_with(&[0x20, 0, 0, 1], Cursor::start(), ByteOrder::Big),
        Err(ParseError::TrailingInput)
    );
}
