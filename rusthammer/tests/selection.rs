use std::cell::{Cell, RefCell};

use rusthammer::{
    Bits, Choice, Cursor, End, Ignore, Left, Literal, Middle, ParseContext, ParseError,
    ParseOutcome, Parser, Right, Seq, TakeAligned,
};

fn literal(byte: u8) -> Literal {
    Literal::new(8, u64::from(byte)).unwrap()
}

fn complete<'input, P: Parser<'input>>(
    parser: P,
    input: &'input [u8],
) -> Result<(Cursor, P::Output), ParseError> {
    parser.parse(input, Cursor::start())
}

#[test]
fn references_forward_both_methods_including_complete_overrides() {
    struct Custom(Cell<usize>);
    impl<'input> Parser<'input> for Custom {
        type Output = &'input [u8];
        fn parse_with(
            &self,
            _: &'input [u8],
            _: Cursor,
            context: ParseContext,
        ) -> ParseOutcome<Self::Output> {
            self.0.set(self.0.get() + 1);
            match context.status {
                rusthammer::InputStatus::Partial => ParseOutcome::NeedMore,
                rusthammer::InputStatus::Final => ParseOutcome::Error(ParseError::Mismatch),
            }
        }
        fn parse(
            &self,
            input: &'input [u8],
            cursor: Cursor,
        ) -> Result<(Cursor, Self::Output), ParseError> {
            self.0.set(self.0.get() + 10);
            Ok((cursor, input))
        }
    }
    let parser = Custom(Cell::new(0));
    let reference = &parser;
    assert_eq!(
        complete(reference, b"abc"),
        Ok((Cursor::start(), &b"abc"[..]))
    );
    assert_eq!(
        complete(&reference, b"xy"),
        Ok((Cursor::start(), &b"xy"[..]))
    );
    assert_eq!(parser.0.get(), 20);
    // Generic combinators use parse_with, even when the child overrides parse.
    let ignore = Ignore { parser: &reference };
    assert_eq!(
        ignore.parse_with(b"abc", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(complete(&ignore, b"abc"), Err(ParseError::Mismatch));
    assert_eq!(parser.0.get(), 22);
}

#[test]
fn one_nonclone_parser_can_be_reused_in_multiple_grammars() {
    // The wrapper deliberately implements neither Clone nor Copy.
    struct Byte(Bits);
    impl<'input> Parser<'input> for Byte {
        type Output = u64;
        fn parse_with(
            &self,
            input: &'input [u8],
            cursor: Cursor,
            context: ParseContext,
        ) -> ParseOutcome<u64> {
            self.0.parse_with(input, cursor, context)
        }
    }
    let byte = Byte(Bits::new(8).unwrap());
    let pair = Seq {
        first: &byte,
        second: &byte,
    };
    let first = Left {
        first: &byte,
        second: &byte,
    };
    assert_eq!(
        complete(&pair, &[7, 9]),
        Ok((Cursor { byte: 2, bit: 0 }, (7, 9)))
    );
    assert_eq!(
        complete(&first, &[3, 4]),
        Ok((Cursor { byte: 2, bit: 0 }, 3))
    );
    assert_eq!(complete(&byte, &[5]), Ok((Cursor { byte: 1, bit: 0 }, 5)));
}

#[test]
fn hammer_output_selection_regressions() {
    // Port test_left, test_right, test_middle, and test_ignore from t_parser.c.
    let a = literal(b'a');
    let space = literal(b' ');
    let left = Left {
        first: &a,
        second: &space,
    };
    let right = Right {
        first: &space,
        second: &a,
    };
    let middle = Middle {
        left: &space,
        parser: &a,
        right: &space,
    };
    assert_eq!(complete(&left, b"a "), Ok((Cursor { byte: 2, bit: 0 }, 97)));
    assert_eq!(
        complete(&right, b" a"),
        Ok((Cursor { byte: 2, bit: 0 }, 97))
    );
    assert_eq!(
        complete(&middle, b" a "),
        Ok((Cursor { byte: 3, bit: 0 }, 97))
    );
    for input in [b"a".as_slice(), b" ", b"ab"] {
        assert!(complete(&left, input).is_err());
    }
    for input in [b"a".as_slice(), b" ", b"ba"] {
        assert!(complete(&right, input).is_err());
    }
    for input in [b"a".as_slice(), b" ", b" a", b"a ", b" b ", b"ba ", b" ab"] {
        assert!(complete(&middle, input).is_err());
    }
    let ignored = Seq {
        first: a,
        second: Seq {
            first: Ignore {
                parser: literal(b'b'),
            },
            second: literal(b'c'),
        },
    };
    // Rust retains the explicit unit in the tuple instead of deleting an AST entry.
    assert_eq!(
        complete(&ignored, b"abc"),
        Ok((Cursor { byte: 3, bit: 0 }, (97, ((), 99))))
    );
    assert_eq!(complete(&ignored, b"ac"), Err(ParseError::Mismatch));
}

#[test]
fn selection_matches_a_bit_string_oracle_including_empty_fields() {
    let input = [0xac, 0x53];
    let bits: String = input.iter().map(|b| format!("{b:08b}")).collect();
    let value = |start: usize, width: usize| {
        if width == 0 {
            0
        } else {
            u64::from_str_radix(&bits[start..start + width], 2).unwrap()
        }
    };
    for start in 0..=bits.len() {
        let cursor = Cursor {
            byte: start / 8,
            bit: (start % 8) as u8,
        };
        for first_width in 0..=5u8 {
            for second_width in 0..=5u8 {
                let first = Bits::new(first_width).unwrap();
                let second = Bits::new(second_width).unwrap();
                let left = Left {
                    first: &first,
                    second: &second,
                };
                let right = Right {
                    first: &first,
                    second: &second,
                };
                let end = start + usize::from(first_width) + usize::from(second_width);
                for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                    let actual = (
                        left.parse_with(&input, cursor, context),
                        right.parse_with(&input, cursor, context),
                    );
                    if end <= bits.len() {
                        let next = Cursor {
                            byte: end / 8,
                            bit: (end % 8) as u8,
                        };
                        assert_eq!(
                            actual,
                            (
                                ParseOutcome::Success(next, value(start, usize::from(first_width))),
                                ParseOutcome::Success(
                                    next,
                                    value(
                                        start + usize::from(first_width),
                                        usize::from(second_width)
                                    )
                                ),
                            )
                        );
                    } else if context == ParseContext::PARTIAL {
                        assert_eq!(actual, (ParseOutcome::NeedMore, ParseOutcome::NeedMore));
                    } else {
                        assert_eq!(
                            actual,
                            (
                                ParseOutcome::Error(ParseError::UnexpectedEnd),
                                ParseOutcome::Error(ParseError::UnexpectedEnd),
                            )
                        );
                    }
                }
            }
        }
        let middle = Middle {
            left: Bits::new(2).unwrap(),
            parser: Bits::new(3).unwrap(),
            right: Bits::new(4).unwrap(),
        };
        let expected = if start + 9 <= bits.len() {
            Ok((
                Cursor {
                    byte: (start + 9) / 8,
                    bit: ((start + 9) % 8) as u8,
                },
                value(start + 2, 3),
            ))
        } else {
            Err(ParseError::UnexpectedEnd)
        };
        assert_eq!(middle.parse(&input, cursor), expected);
    }
}

#[derive(Debug, PartialEq)]
struct Borrowed<'input>(&'input [u8]);

struct BorrowedParser;
impl<'input> Parser<'input> for BorrowedParser {
    type Output = Borrowed<'input>;
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match (TakeAligned { count: 3 }).parse_with(input, cursor, context) {
            ParseOutcome::Success(next, bytes) => ParseOutcome::Success(next, Borrowed(bytes)),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn borrowed_noncopy_outputs_outlive_local_parser_references() {
    let input = *b"[abc]";
    let selected = {
        let body = BorrowedParser;
        let open = literal(b'[');
        let close = literal(b']');
        let middle = Middle {
            left: &open,
            parser: &body,
            right: &close,
        };
        let parser = Left {
            first: &middle,
            second: End,
        };
        complete(&parser, &input).unwrap()
    };
    assert_eq!(selected.0, Cursor { byte: 5, bit: 0 });
    assert_eq!(selected.1 .0, b"abc");
    assert_eq!(selected.1 .0.as_ptr(), input[1..].as_ptr());
    let body = BorrowedParser;
    let left = Left {
        first: &body,
        second: literal(b']'),
    };
    let right = Right {
        first: literal(b'['),
        second: &body,
    };
    assert_eq!(
        left.parse(&input[1..], Cursor::start())
            .unwrap()
            .1
             .0
            .as_ptr(),
        input[1..].as_ptr()
    );
    assert_eq!(
        right
            .parse(&input[..4], Cursor::start())
            .unwrap()
            .1
             .0
            .as_ptr(),
        input[1..].as_ptr()
    );
}

#[test]
fn delimiters_and_end_preserve_partial_input_semantics() {
    let middle = Middle {
        left: literal(b'['),
        parser: BorrowedParser,
        right: literal(b']'),
    };
    let complete_parser = Left {
        first: &middle,
        second: End,
    };
    for end in 0..5 {
        let input = &b"[abc]"[..end];
        assert_eq!(
            middle.parse_with(input, Cursor::start(), ParseContext::PARTIAL),
            ParseOutcome::NeedMore
        );
        assert_eq!(complete(&middle, input), Err(ParseError::UnexpectedEnd));
    }
    assert_eq!(
        middle.parse_with(b"[abc]", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 5, bit: 0 }, Borrowed(b"abc"))
    );
    assert_eq!(
        complete_parser.parse_with(b"[abc]", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        complete(&complete_parser, b"[abc]"),
        Ok((Cursor { byte: 5, bit: 0 }, Borrowed(b"abc")))
    );
    assert_eq!(
        complete_parser.parse_with(b"[abc]!", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Error(ParseError::TrailingInput)
    );
    assert_eq!(
        middle.parse_with(b"[abc!", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Error(ParseError::Mismatch)
    );
}

#[derive(Clone, Copy, Debug)]
enum Action {
    Success,
    Error(ParseError),
    NeedMore,
}

#[derive(Debug)]
struct Ticket<'a> {
    id: usize,
    drops: &'a RefCell<Vec<usize>>,
}
impl Drop for Ticket<'_> {
    fn drop(&mut self) {
        self.drops.borrow_mut().push(self.id);
    }
}

struct Stage<'a> {
    id: usize,
    action: Action,
    visits: &'a RefCell<Vec<(usize, Cursor, ParseContext)>>,
    drops: &'a RefCell<Vec<usize>>,
}
impl<'input, 'a> Parser<'input> for Stage<'a> {
    type Output = Ticket<'a>;
    fn parse_with(
        &self,
        _: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        self.visits.borrow_mut().push((self.id, cursor, context));
        match self.action {
            Action::Success => ParseOutcome::Success(
                Cursor {
                    byte: cursor.byte + 1,
                    bit: cursor.bit,
                },
                Ticket {
                    id: self.id,
                    drops: self.drops,
                },
            ),
            Action::Error(error) => ParseOutcome::Error(error),
            Action::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn selection_short_circuits_and_drops_each_noncopy_output_once() {
    let mut cases = vec![(3, Action::Success)];
    for stop in 0..3 {
        cases.push((stop, Action::NeedMore));
        for error in [
            ParseError::Mismatch,
            ParseError::UnexpectedEnd,
            ParseError::TrailingInput,
            ParseError::InvalidCursor,
            ParseError::Unaligned,
            ParseError::NonProgress,
            ParseError::CountOverflow,
        ] {
            cases.push((stop, Action::Error(error)));
        }
    }
    for (stop, action) in cases {
        for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
            for selection in 0..3 {
                let visits = RefCell::new(Vec::new());
                let drops = RefCell::new(Vec::new());
                let stage = |id| Stage {
                    id,
                    action: if id == stop { action } else { Action::Success },
                    visits: &visits,
                    drops: &drops,
                };
                let first = stage(0);
                let second = stage(1);
                let third = stage(2);
                let result = match selection {
                    0 => Left {
                        first: &first,
                        second: &second,
                    }
                    .parse_with(b"abc", Cursor::start(), context),
                    1 => Right {
                        first: &first,
                        second: &second,
                    }
                    .parse_with(b"abc", Cursor::start(), context),
                    _ => Middle {
                        left: &first,
                        parser: &second,
                        right: &third,
                    }
                    .parse_with(b"abc", Cursor::start(), context),
                };
                let count = if selection == 2 { 3 } else { 2 };
                let succeeded = stop >= count;
                if succeeded {
                    let selected = if selection == 0 { 0 } else { 1 };
                    match result {
                        ParseOutcome::Success(next, ticket) => {
                            assert_eq!(
                                next,
                                Cursor {
                                    byte: count,
                                    bit: 0
                                }
                            );
                            assert_eq!(ticket.id, selected);
                            let mut discarded = drops.borrow().clone();
                            discarded.sort();
                            assert_eq!(
                                discarded,
                                (0..count).filter(|id| *id != selected).collect::<Vec<_>>()
                            );
                            drop(ticket);
                        }
                        _ => panic!("expected success, got {result:?}"),
                    }
                } else {
                    match (action, result) {
                        (Action::Error(expected), ParseOutcome::Error(actual)) => {
                            assert_eq!(actual, expected)
                        }
                        (Action::NeedMore, ParseOutcome::NeedMore) => (),
                        (_, actual) => panic!("expected {action:?}, got {actual:?}"),
                    }
                }
                assert_eq!(
                    *visits.borrow(),
                    (0..count.min(stop + 1))
                        .map(|id| (id, Cursor { byte: id, bit: 0 }, context))
                        .collect::<Vec<_>>()
                );
                drops.borrow_mut().sort();
                assert_eq!(*drops.borrow(), (0..count.min(stop)).collect::<Vec<_>>());
            }
        }
    }
}

#[test]
fn ignore_consumes_and_drops_but_never_suppresses_errors_or_incompleteness() {
    let mut actions = vec![Action::Success, Action::NeedMore];
    for error in [
        ParseError::Mismatch,
        ParseError::UnexpectedEnd,
        ParseError::TrailingInput,
        ParseError::InvalidCursor,
        ParseError::Unaligned,
        ParseError::NonProgress,
        ParseError::CountOverflow,
    ] {
        actions.push(Action::Error(error));
    }
    for action in actions {
        for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
            let visits = RefCell::new(Vec::new());
            let drops = RefCell::new(Vec::new());
            let parser = Ignore {
                parser: Stage {
                    id: 0,
                    action,
                    visits: &visits,
                    drops: &drops,
                },
            };
            let expected = match action {
                Action::Success => ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, ()),
                Action::Error(error) => ParseOutcome::Error(error),
                Action::NeedMore => ParseOutcome::NeedMore,
            };
            assert_eq!(parser.parse_with(b"a", Cursor::start(), context), expected);
            assert_eq!(*visits.borrow(), [(0, Cursor::start(), context)]);
            assert_eq!(
                *drops.borrow(),
                if matches!(action, Action::Success) {
                    vec![0]
                } else {
                    vec![]
                }
            );
        }
    }
}

#[test]
fn selection_failure_allows_choice_to_retry_at_the_original_bit_cursor() {
    let selected = Left {
        first: literal(b'a'),
        second: literal(b'b'),
    };
    let parser = Choice {
        first: &selected,
        second: Bits::new(8).unwrap(),
    };
    let input = [0x30, 0xb1, 0]; // At bit 1: 'a', then 'b'.
    let start = Cursor { byte: 0, bit: 1 };
    let mut rejected = input;
    rejected[1] ^= 1; // second byte decodes to '`', making the discarded child reject.
    assert_eq!(
        parser.parse(&rejected, start),
        Ok((Cursor { byte: 1, bit: 1 }, 97))
    );
    assert_eq!(
        parser.parse_with(&input[..2], start, ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse(&input[..2], start),
        Ok((Cursor { byte: 1, bit: 1 }, 97))
    );
}

#[test]
fn empty_successes_and_invalid_cursors_follow_child_semantics() {
    let empty = Bits::new(0).unwrap();
    let left = Left {
        first: &empty,
        second: &empty,
    };
    let right = Right {
        first: &empty,
        second: &empty,
    };
    let middle = Middle {
        left: &empty,
        parser: &empty,
        right: &empty,
    };
    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
        for cursor in [
            Cursor::start(),
            Cursor { byte: 1, bit: 0 },
            Cursor { byte: 0, bit: 8 },
        ] {
            let expected = if cursor == Cursor::start() {
                ParseOutcome::Success(cursor, 0)
            } else {
                ParseOutcome::Error(ParseError::InvalidCursor)
            };
            assert_eq!(left.parse_with(&[], cursor, context), expected);
            assert_eq!(right.parse_with(&[], cursor, context), expected);
            assert_eq!(middle.parse_with(&[], cursor, context), expected);
        }
    }
    assert_eq!(
        Ignore { parser: End }.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        Ignore { parser: End }.parse(&[], Cursor::start()),
        Ok((Cursor::start(), ()))
    );
}
