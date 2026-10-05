use std::cell::{Cell, RefCell};
use std::rc::Rc;

use rusthammer::{
    And, BeU16, ButNot, Byte, ByteIn, BytePattern, Choice, Cursor, Difference, Epsilon, Fail, Map,
    Not, ParseContext, ParseError, ParseOutcome, Parser, Right, Seq, SkipBits, TakeAligned, Xor,
};

#[derive(Clone, Copy, Debug)]
enum Case {
    Success(Cursor),
    Error(ParseError),
    More,
}

#[derive(Debug, PartialEq, Eq)]
enum Expected {
    Success(Cursor, u8),
    Error(ParseError),
    More,
}

fn recoverable(error: ParseError) -> bool {
    matches!(
        error,
        ParseError::Mismatch | ParseError::UnexpectedEnd | ParseError::TrailingInput
    )
}

fn position(cursor: Cursor) -> u128 {
    cursor.byte as u128 * 8 + u128::from(cursor.bit)
}

// Truth-table oracle compares unbounded-for-this-target absolute positions.
fn oracle(kind: u8, first: Case, second: Case) -> (Expected, bool) {
    if matches!(first, Case::More) {
        return (Expected::More, false);
    }
    if let Case::Error(error) = first {
        if kind != 2 || !recoverable(error) {
            return (Expected::Error(error), false);
        }
    }
    let result = match (first, second) {
        (_, Case::More) => Expected::More,
        (Case::Error(_), Case::Error(error)) => Expected::Error(error),
        (Case::Error(_), Case::Success(next)) => Expected::Success(next, 1),
        (Case::Success(next), Case::Error(error)) if recoverable(error) => {
            Expected::Success(next, 0)
        }
        (Case::Success(_), Case::Error(error)) => Expected::Error(error),
        (Case::Success(next), Case::Success(other)) => {
            let accepted = match kind {
                0 => position(next) > position(other),
                1 => position(next) >= position(other),
                _ => false,
            };
            if accepted {
                Expected::Success(next, 0)
            } else {
                Expected::Error(ParseError::Mismatch)
            }
        }
        _ => unreachable!(),
    };
    (result, true)
}

// Deliberately neither Copy nor Clone. Every speculative output must be dropped
// exactly once; the accepted one must survive until its caller drops it.
struct Token {
    id: u8,
    drops: Rc<Cell<usize>>,
}

impl Drop for Token {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

struct Probe<'a> {
    id: u8,
    outcome: Case,
    calls: &'a RefCell<Vec<(u8, Cursor, ParseContext)>>,
    drops: Rc<Cell<usize>>,
}

impl<'input> Parser<'input> for Probe<'_> {
    type Output = Token;
    fn parse_with(
        &self,
        _: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Token> {
        self.calls.borrow_mut().push((self.id, cursor, context));
        match self.outcome {
            Case::Success(next) => ParseOutcome::Success(
                next,
                Token {
                    id: self.id,
                    drops: self.drops.clone(),
                },
            ),
            Case::Error(error) => ParseOutcome::Error(error),
            Case::More => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn all_outcomes_preserve_order_short_circuiting_and_ownership() {
    let cases = [
        Case::Success(Cursor::start()),
        Case::Success(Cursor { byte: 0, bit: 7 }),
        Case::Success(Cursor { byte: 1, bit: 0 }),
        Case::Success(Cursor {
            byte: usize::MAX / 8,
            bit: 7,
        }),
        Case::Success(Cursor {
            byte: usize::MAX,
            bit: 0,
        }),
        Case::Success(Cursor {
            byte: usize::MAX,
            bit: 7,
        }),
        Case::Error(ParseError::Mismatch),
        Case::Error(ParseError::UnexpectedEnd),
        Case::Error(ParseError::TrailingInput),
        Case::Error(ParseError::InvalidCursor),
        Case::Error(ParseError::Unaligned),
        Case::Error(ParseError::NonProgress),
        Case::Error(ParseError::CountOverflow),
        Case::More,
    ];
    for kind in 0..3 {
        for first_case in cases {
            for second_case in cases {
                for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                    let cursor = Cursor::start();
                    let calls = RefCell::new(Vec::new());
                    let drops = [Rc::new(Cell::new(0)), Rc::new(Cell::new(0))];
                    let first = Probe {
                        id: 0,
                        outcome: first_case,
                        calls: &calls,
                        drops: drops[0].clone(),
                    };
                    let second = Probe {
                        id: 1,
                        outcome: second_case,
                        calls: &calls,
                        drops: drops[1].clone(),
                    };
                    let (expected, second_called) = oracle(kind, first_case, second_case);
                    let result = match kind {
                        0 => ButNot {
                            first: &first,
                            second: &second,
                        }
                        .parse_with(&[], cursor, context),
                        1 => Difference {
                            first: &first,
                            second: &second,
                        }
                        .parse_with(&[], cursor, context),
                        _ => Xor {
                            first: &first,
                            second: &second,
                        }
                        .parse_with(&[], cursor, context),
                    };
                    let actual = match &result {
                        ParseOutcome::Success(next, value) => Expected::Success(*next, value.id),
                        ParseOutcome::Error(error) => Expected::Error(*error),
                        ParseOutcome::NeedMore => Expected::More,
                    };
                    assert_eq!(
                        actual, expected,
                        "{kind}: {first_case:?}, {second_case:?}, {context:?}"
                    );
                    let mut expected_calls = vec![(0, cursor, context)];
                    if second_called {
                        expected_calls.push((1, cursor, context));
                    }
                    assert_eq!(*calls.borrow(), expected_calls);
                    for (id, case) in [first_case, second_case].into_iter().enumerate() {
                        let created =
                            (id == 0 || second_called) && matches!(case, Case::Success(_));
                        let retained = matches!(actual, Expected::Success(_, selected) if usize::from(selected) == id);
                        assert_eq!(drops[id].get(), usize::from(created && !retained));
                    }
                    drop(result);
                    assert_eq!(
                        drops[0].get(),
                        usize::from(matches!(first_case, Case::Success(_)))
                    );
                    assert_eq!(
                        drops[1].get(),
                        usize::from(second_called && matches!(second_case, Case::Success(_)))
                    );
                }
            }
        }
    }
}

#[test]
fn compare_consumption_in_bits_including_discarded_input_and_lookahead() {
    for offset in 0..8 {
        for left in 0..=17 {
            for right in 0..=17 {
                let start = Cursor {
                    byte: 0,
                    bit: offset,
                };
                let first = Right {
                    first: SkipBits::new(left),
                    second: Epsilon,
                };
                let second = SkipBits::new(right);
                let next = Cursor {
                    byte: (usize::from(offset) + left) / 8,
                    bit: ((usize::from(offset) + left) % 8) as u8,
                };
                let strict = ButNot { first, second }.parse(&[0; 4], start);
                let inclusive = Difference { first, second }.parse(&[0; 4], start);
                assert_eq!(
                    strict,
                    if left > right {
                        Ok((next, ()))
                    } else {
                        Err(ParseError::Mismatch)
                    }
                );
                assert_eq!(
                    inclusive,
                    if left >= right {
                        Ok((next, ()))
                    } else {
                        Err(ParseError::Mismatch)
                    }
                );
            }
        }
    }
    assert_eq!(
        ButNot {
            first: Byte,
            second: And { parser: BeU16 }
        }
        .parse(&[0; 2], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, 0))
    );
    assert_eq!(
        Difference {
            first: Epsilon,
            second: And { parser: Byte }
        }
        .parse(&[0], Cursor::start()),
        Ok((Cursor::start(), ()))
    );
}

#[test]
fn partial_input_waits_for_the_second_match_before_accepting() {
    let first = BytePattern::new(b"a");
    let second = BytePattern::new(b"ab");
    let restricted = ButNot { first, second };
    for outcome in [
        restricted.parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
        Difference { first, second }.parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
        Xor { first, second }.parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
        Choice {
            first: restricted,
            second: first,
        }
        .parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
    ] {
        assert_eq!(outcome, ParseOutcome::NeedMore);
    }
    assert_eq!(
        restricted.parse(b"a", Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, &b"a"[..]))
    );
    assert_eq!(
        restricted.parse(b"ab", Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        restricted.parse_with(b"ac", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, &b"a"[..])
    );
    assert_eq!(
        Not { parser: restricted }.parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    let rejected_prefix = Right {
        first: BytePattern::new(b"a"),
        second: BytePattern::new(b"x"),
    };
    assert_eq!(
        Xor {
            first: rejected_prefix,
            second
        }
        .parse(b"ab", Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, &b"ab"[..]))
    );
}

#[test]
fn different_outputs_and_borrows_need_no_copy_or_clone_bounds() {
    fn copyable<T: Copy>(_: T) {}
    let input = [7, 8];
    let parser = ButNot {
        first: TakeAligned { count: 2 },
        second: Byte,
    };
    copyable(parser);
    let clone = Clone::clone(&parser);
    let (next, payload) = (&clone).parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 2, bit: 0 });
    assert!(core::ptr::eq(payload, &input[..]));
    let parser = Difference {
        first: TakeAligned { count: 1 },
        second: Byte,
    };
    copyable(parser);
    assert!(core::ptr::eq(
        parser.parse(&input, Cursor::start()).unwrap().1,
        &input[..1]
    ));

    #[derive(Debug, PartialEq, Eq)]
    enum Value {
        Digit(u8),
        Word(u16),
    }
    let first = Map {
        parser: ByteIn::new(b"0123456789"),
        map: Value::Digit,
    };
    let second = Map {
        parser: Right {
            first: BytePattern::new(b"#"),
            second: BeU16,
        },
        map: Value::Word,
    };
    let parser = Xor { first, second };
    copyable(parser);
    let clone = Clone::clone(&parser);
    assert_eq!(
        clone.parse(b"7", Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, Value::Digit(b'7')))
    );
    assert_eq!(
        parser.parse(b"#\x12\x34", Cursor::start()),
        Ok((Cursor { byte: 3, bit: 0 }, Value::Word(0x1234)))
    );
}

#[test]
fn empty_children_delegate_cursor_validation() {
    let raw = Cursor {
        byte: usize::MAX,
        bit: u8::MAX,
    };
    assert_eq!(
        ButNot {
            first: Epsilon,
            second: Fail::<u8>::new()
        }
        .parse(&[], raw),
        Ok((raw, ()))
    );
    assert_eq!(
        Difference {
            first: Epsilon,
            second: Epsilon
        }
        .parse(&[], raw),
        Ok((raw, ()))
    );
    assert_eq!(
        ButNot {
            first: Epsilon,
            second: Epsilon
        }
        .parse(&[], raw),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        Xor {
            first: Epsilon,
            second: Fail::new()
        }
        .parse(&[], raw),
        Ok((raw, ()))
    );
    assert_eq!(
        Xor {
            first: Epsilon,
            second: Epsilon
        }
        .parse(&[], raw),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        ButNot {
            first: Epsilon,
            second: Byte
        }
        .parse(&[], raw),
        Err(ParseError::InvalidCursor)
    );
    assert_eq!(
        Seq {
            first: Difference {
                first: Epsilon,
                second: Epsilon
            },
            second: Byte
        }
        .parse(&[], raw),
        Err(ParseError::InvalidCursor)
    );
}
