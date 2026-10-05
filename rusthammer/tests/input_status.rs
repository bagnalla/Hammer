use rusthammer::{Eval, Grammar};
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
    And, Bit, Bits, Choice, Cursor, End, Literal, Map, Not, Optional, ParseContext, ParseError,
    ParseOutcome, Parser, Seq, TakeAligned, Verify,
};

use ParseOutcome::{Error, NeedMore, Success};

struct MustNotRun;
impl<'input> Grammar<'input> for MustNotRun {
    type Output = u64;
}

impl<'input, Backend> Eval<'input, Backend> for MustNotRun {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<u64> {
        panic!("incompleteness must stop this branch");
    }
}

#[test]
fn primitives_distinguish_nonfinal_exhaustion_from_final_truncation() {
    let start = Cursor::start();
    assert_eq!(Bit.parse_with(&[], start, ParseContext::PARTIAL), NeedMore);
    assert_eq!(
        Bit.parse_with(&[], start, ParseContext::FINAL),
        Error(ParseError::UnexpectedEnd)
    );
    let bits = Bits::new(8).unwrap();
    let cursor = Cursor { byte: 0, bit: 7 };
    assert_eq!(
        bits.parse_with(&[1], cursor, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        bits.parse_with(&[1], cursor, ParseContext::FINAL),
        Error(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        bits.parse_with(&[1, 0], cursor, ParseContext::PARTIAL),
        Success(Cursor { byte: 1, bit: 7 }, 0x80)
    );
    assert_eq!(
        TakeAligned { count: usize::MAX }.parse_with(&[1], start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        TakeAligned { count: usize::MAX }.parse_with(&[1], start, ParseContext::FINAL),
        Error(ParseError::UnexpectedEnd)
    );
}

#[test]
fn invalid_cursors_and_alignment_remain_errors_on_partial_input() {
    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
        for cursor in [
            Cursor { byte: 0, bit: 8 },
            Cursor { byte: 1, bit: 1 },
            Cursor {
                byte: usize::MAX,
                bit: 0,
            },
        ] {
            assert_eq!(
                Bit.parse_with(&[0], cursor, context),
                Error(ParseError::InvalidCursor)
            );
            assert_eq!(
                Bits::new(0).unwrap().parse_with(&[0], cursor, context),
                Error(ParseError::InvalidCursor)
            );
            assert_eq!(
                End.parse_with(&[0], cursor, context),
                Error(ParseError::InvalidCursor)
            );
        }
        let cursor = Cursor { byte: 0, bit: 1 };
        assert_eq!(
            Optional {
                parser: TakeAligned { count: 0 }
            }
            .parse_with(&[0], cursor, context),
            Error(ParseError::Unaligned)
        );
        assert_eq!(
            Not {
                parser: TakeAligned { count: 0 }
            }
            .parse_with(&[0], cursor, context),
            Error(ParseError::Unaligned)
        );
    }
}

#[test]
fn choice_waits_before_selecting_a_shorter_alternative() {
    let parser = Choice {
        first: Literal::new(16, 0x6162).unwrap(),
        second: Literal::new(8, 0x61).unwrap(),
    };
    let start = Cursor::start();
    assert_eq!(
        parser.parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        parser.parse_with(b"a", start, ParseContext::FINAL),
        Success(Cursor { byte: 1, bit: 0 }, 0x61)
    );
    assert_eq!(
        parser.parse_with(b"ab", start, ParseContext::PARTIAL),
        Success(Cursor { byte: 2, bit: 0 }, 0x6162)
    );
    assert_eq!(
        parser.parse_with(b"ac", start, ParseContext::PARTIAL),
        Success(Cursor { byte: 1, bit: 0 }, 0x61)
    );
    let guarded = Choice {
        first: Bits::new(16).unwrap(),
        second: MustNotRun,
    };
    assert_eq!(
        guarded.parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
}

#[test]
fn optionality_and_lookahead_preserve_incompleteness() {
    let ab = Literal::new(16, 0x6162).unwrap();
    let start = Cursor::start();
    assert_eq!(
        Optional { parser: ab }.parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        And { parser: ab }.parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        Not { parser: ab }.parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        Optional { parser: ab }.parse_with(b"a", start, ParseContext::FINAL),
        Success(start, None)
    );
    assert_eq!(
        And { parser: ab }.parse_with(b"a", start, ParseContext::FINAL),
        Error(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        Not { parser: ab }.parse_with(b"a", start, ParseContext::FINAL),
        Success(start, ())
    );
    assert_eq!(
        Optional { parser: ab }.parse_with(b"ab", start, ParseContext::PARTIAL),
        Success(Cursor { byte: 2, bit: 0 }, Some(0x6162))
    );
    assert_eq!(
        And { parser: ab }.parse_with(b"ab", start, ParseContext::PARTIAL),
        Success(start, ())
    );
    assert_eq!(
        Not { parser: ab }.parse_with(b"ab", start, ParseContext::PARTIAL),
        Error(ParseError::Mismatch)
    );
    assert_eq!(
        Optional { parser: ab }.parse_with(b"ac", start, ParseContext::PARTIAL),
        Success(start, None)
    );
    assert_eq!(
        Not { parser: ab }.parse_with(b"ac", start, ParseContext::PARTIAL),
        Success(start, ())
    );
}

#[test]
fn sequence_and_callbacks_stop_on_need_more() {
    let start = Cursor::start();
    assert_eq!(
        Seq {
            first: Bits::new(8).unwrap(),
            second: MustNotRun
        }
        .parse_with(&[], start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        Seq {
            first: Bits::new(8).unwrap(),
            second: Bits::new(8).unwrap()
        }
        .parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
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
        mapped.parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        verified.parse_with(b"a", start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(calls.get(), 0);
    assert!(matches!(
        mapped.parse_with(b"ab", start, ParseContext::PARTIAL),
        Success(_, 0x6162)
    ));
    assert!(matches!(
        verified.parse_with(b"ab", start, ParseContext::PARTIAL),
        Success(_, 0x6162)
    ));
    assert_eq!(calls.get(), 2);
}

#[test]
fn end_requires_finality_but_empty_parsers_can_finish_early() {
    let start = Cursor::start();
    assert_eq!(End.parse_with(&[], start, ParseContext::PARTIAL), NeedMore);
    assert_eq!(
        End.parse_with(&[], start, ParseContext::FINAL),
        Success(start, ())
    );
    assert_eq!(
        End.parse_with(&[0], start, ParseContext::PARTIAL),
        Error(ParseError::TrailingInput)
    );
    assert_eq!(
        Not { parser: End }.parse_with(&[], start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        Optional { parser: End }.parse_with(&[], start, ParseContext::PARTIAL),
        NeedMore
    );
    assert_eq!(
        Bits::new(0)
            .unwrap()
            .parse_with(&[], start, ParseContext::PARTIAL),
        Success(start, 0)
    );
    assert_eq!(
        Optional {
            parser: Bits::new(0).unwrap()
        }
        .parse_with(&[], start, ParseContext::PARTIAL),
        Success(start, Some(0))
    );
    assert_eq!(
        Not {
            parser: Bits::new(0).unwrap()
        }
        .parse_with(&[], start, ParseContext::PARTIAL),
        Error(ParseError::Mismatch)
    );
}

#[test]
fn partial_success_can_borrow_a_finished_prefix() {
    let input = [0, 0xca, 0xfe, 1];
    let parser = Optional {
        parser: TakeAligned { count: 2 },
    };
    let Success(next, Some(payload)) =
        parser.parse_with(&input, Cursor { byte: 1, bit: 0 }, ParseContext::PARTIAL)
    else {
        panic!("expected prefix success")
    };
    assert_eq!(next, Cursor { byte: 3, bit: 0 });
    assert_eq!(payload, &input[1..3]);
    assert_eq!(payload.as_ptr(), input[1..].as_ptr());
}

#[test]
fn marker_waits_for_both_alternative_resolution_and_end_of_input() {
    let parser = Marker::new().unwrap();
    for input in [&[][..], &[0xca][..], &[0xca, 0xfe][..]] {
        assert_eq!(
            parser.parse_with(input, Cursor::start(), ParseContext::PARTIAL),
            NeedMore
        );
    }
    assert_eq!(
        parser.parse_with(&[0xca], Cursor::start(), ParseContext::FINAL),
        Success(Cursor { byte: 1, bit: 0 }, 0xca)
    );
    assert_eq!(
        parser.parse_with(&[0xca, 0xfe], Cursor::start(), ParseContext::FINAL),
        Success(Cursor { byte: 2, bit: 0 }, 0xcafe)
    );
    assert_eq!(
        parser.parse_with(&[0xca, 0xfe, 0], Cursor::start(), ParseContext::PARTIAL),
        Error(ParseError::TrailingInput)
    );
}

#[test]
fn records_can_be_retried_at_every_chunk_boundary() {
    let parser = RecordParser::new().unwrap();
    for count in [0usize, 1, 7, 1024] {
        let mut input = vec![0xff, 0x25, (count >> 8) as u8, count as u8];
        input.extend((0..count).map(|i| i as u8));
        let start = Cursor { byte: 1, bit: 0 };
        for available in 1..=input.len() {
            assert_eq!(
                parser.parse_with(&input[..available], start, ParseContext::PARTIAL),
                NeedMore
            );
            if available < input.len() {
                assert_eq!(
                    parser.parse_with(&input[..available], start, ParseContext::FINAL),
                    Error(ParseError::UnexpectedEnd)
                );
            }
        }
        let Success(next, record) = parser.parse_with(&input, start, ParseContext::FINAL) else {
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
        parser.parse_with(&[0, 0, 0], Cursor::start(), ParseContext::PARTIAL),
        Error(ParseError::Mismatch)
    );
    assert_eq!(
        parser.parse_with(&[0x20, 4, 1], Cursor::start(), ParseContext::PARTIAL),
        Error(ParseError::Mismatch)
    );
    assert_eq!(
        parser.parse_with(&[0x20, 0, 0, 1], Cursor::start(), ParseContext::PARTIAL),
        Error(ParseError::TrailingInput)
    );
}
