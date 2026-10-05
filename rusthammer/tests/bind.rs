use rusthammer::{Eval, Grammar};
#[path = "../examples/support/dependent.rs"]
mod formats;

use rusthammer::{
    Bind, Bit, Bits, Choice, Cursor, Epsilon, Literal, Map, Optional, ParseContext, ParseError,
    ParseOutcome, Parser, TakeAligned, TryMap,
};
use std::cell::Cell;
use std::rc::Rc;

fn at(bit: usize) -> Cursor {
    Cursor {
        byte: bit / 8,
        bit: (bit % 8) as u8,
    }
}

#[test]
fn length_prefixed_examples_match_independent_bit_string_and_slice_oracles() {
    for length in 0..=255u8 {
        let mut input = vec![length];
        input.extend((0..=65u8).map(|n| n.wrapping_mul(37)));
        let bit_string: String = input.iter().map(|b| format!("{b:08b}")).collect();
        for available in 0..=input.len() {
            let input = &input[..available];
            for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                let short = if context == ParseContext::PARTIAL {
                    ParseOutcome::NeedMore
                } else {
                    ParseOutcome::Error(ParseError::UnexpectedEnd)
                };
                let expected = if available == 0 {
                    short
                } else if length > 64 {
                    ParseOutcome::Error(ParseError::Mismatch)
                } else if usize::from(length) + 1 > available {
                    short
                } else {
                    ParseOutcome::Success(
                        at((usize::from(length) + 1) * 8),
                        &input[1..=usize::from(length)],
                    )
                };
                let actual = formats::payload(input, Cursor::start(), context);
                assert_eq!(
                    actual, expected,
                    "length={length} available={available} context={context:?}"
                );
                if let ParseOutcome::Success(_, bytes) = actual {
                    assert!(core::ptr::eq(bytes.as_ptr(), input[1..].as_ptr()));
                }
                #[cfg(feature = "alloc")]
                {
                    let expected = if available == 0
                        || (length <= 64 && 8 + usize::from(length) * 4 > available * 8)
                    {
                        if context == ParseContext::PARTIAL {
                            ParseOutcome::NeedMore
                        } else {
                            ParseOutcome::Error(ParseError::UnexpectedEnd)
                        }
                    } else if length > 64 {
                        ParseOutcome::Error(ParseError::Mismatch)
                    } else {
                        let values = (0..usize::from(length))
                            .map(|i| {
                                u64::from_str_radix(&bit_string[8 + i * 4..12 + i * 4], 2).unwrap()
                            })
                            .collect();
                        ParseOutcome::Success(at(8 + usize::from(length) * 4), values)
                    };
                    assert_eq!(formats::fields(input, Cursor::start(), context), expected);
                }
            }
        }
        // The owned bit-string oracle is used only by the allocating format.
        #[cfg(not(feature = "alloc"))]
        let _ = bit_string;
    }
}

#[test]
fn prefix_errors_have_defined_precedence_at_every_raw_cursor() {
    let input = [0u8; 4];
    for byte in [0, 1, 3, 4, 5, usize::MAX] {
        for bit in [0, 1, 7, 8, 255] {
            let cursor = Cursor { byte, bit };
            for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                let expected =
                    if bit >= 8 || byte > input.len() || (byte == input.len() && bit != 0) {
                        ParseOutcome::Error(ParseError::InvalidCursor)
                    } else if byte == input.len() || (byte == 3 && bit > 0) {
                        if context == ParseContext::PARTIAL {
                            ParseOutcome::NeedMore
                        } else {
                            ParseOutcome::Error(ParseError::UnexpectedEnd)
                        }
                    } else if bit != 0 {
                        ParseOutcome::Error(ParseError::Unaligned)
                    } else {
                        ParseOutcome::Success(
                            Cursor {
                                byte: byte + 1,
                                bit: 0,
                            },
                            &input[byte + 1..byte + 1],
                        )
                    };
                assert_eq!(formats::payload(&input, cursor, context), expected);
            }
        }
    }
    // Count validation precedes payload alignment, including on partial input.
    assert_eq!(
        formats::payload(&[0xff, 0xff], at(1), ParseContext::PARTIAL),
        ParseOutcome::Error(ParseError::Mismatch)
    );
}

struct Fixed(ParseOutcome<()>);
impl<'input> Grammar<'input> for Fixed {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for Fixed {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<()> {
        match self.0 {
            ParseOutcome::Success(cursor, ()) => ParseOutcome::Success(cursor, ()),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn first_errors_and_incompleteness_skip_the_factory() {
    for error in [
        None,
        Some(ParseError::Mismatch),
        Some(ParseError::UnexpectedEnd),
        Some(ParseError::TrailingInput),
        Some(ParseError::InvalidCursor),
        Some(ParseError::Unaligned),
        Some(ParseError::NonProgress),
        Some(ParseError::CountOverflow),
    ] {
        let expected = match error {
            Some(error) => ParseOutcome::Error(error),
            None => ParseOutcome::NeedMore,
        };
        let parser = Bind {
            parser: Fixed(expected),
            then: |()| -> Epsilon { panic!("factory must not run") },
        };
        for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
            let expected = match error {
                Some(error) => ParseOutcome::Error(error),
                None => ParseOutcome::NeedMore,
            };
            assert_eq!(parser.parse_with(&[], Cursor::start(), context), expected);
        }
    }
}

struct Observed<'a> {
    expected: Cursor,
    context: ParseContext,
    calls: &'a Cell<usize>,
    error: Option<ParseError>,
}
impl<'input> Grammar<'input> for Observed<'_> {
    type Output = bool;
}

impl<'input, Backend> Eval<'input, Backend> for Observed<'_> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<bool> {
        assert_eq!(
            (input, cursor, context),
            (&b"x"[..], self.expected, self.context)
        );
        self.calls.set(self.calls.get() + 1);
        match self.error {
            Some(error) => ParseOutcome::Error(error),
            None => Bit.eval(backend, input, cursor, context),
        }
    }
}

#[test]
fn second_stage_gets_the_exact_input_cursor_and_status_and_propagates_its_outcome() {
    for cursor in [at(3), at(8)] {
        for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
            for error in [
                None,
                Some(ParseError::Mismatch),
                Some(ParseError::InvalidCursor),
                Some(ParseError::CountOverflow),
            ] {
                let factories = Cell::new(0);
                let children = Cell::new(0);
                let parser = Bind {
                    parser: Fixed(ParseOutcome::Success(cursor, ())),
                    then: |()| {
                        factories.set(factories.get() + 1);
                        Observed {
                            expected: cursor,
                            context,
                            calls: &children,
                            error,
                        }
                    },
                };
                let expected = match error {
                    Some(error) => ParseOutcome::Error(error),
                    None => Bit.parse_with(b"x", cursor, context),
                };
                assert_eq!(parser.parse_with(b"x", Cursor::start(), context), expected);
                assert_eq!((factories.get(), children.get()), (1, 1));
            }
        }
    }
}

#[test]
fn backtracking_restores_input_and_retry_constructs_a_fresh_parser() {
    let calls = Cell::new(0);
    let dependent = Bind {
        parser: Bits::new(8).unwrap(),
        then: |byte| {
            calls.set(calls.get() + 1);
            Literal::new(8, byte).unwrap()
        },
    };
    assert_eq!(
        dependent.parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(dependent.parse(b"aa", Cursor::start()), Ok((at(16), 97)));
    assert_eq!(calls.get(), 2);
    let alternative = Choice {
        first: &dependent,
        second: Bits::new(8).unwrap(),
    };
    assert_eq!(alternative.parse(b"ab", Cursor::start()), Ok((at(8), 97)));
    assert_eq!(
        Optional { parser: &dependent }.parse(b"ab", Cursor::start()),
        Ok((Cursor::start(), None))
    );
    assert_eq!(
        alternative.parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(calls.get(), 5);
}

#[test]
fn checked_parser_construction_rejects_before_bind_invokes_its_factory() {
    let calls = Cell::new(0);
    let parser = Bind {
        parser: TryMap {
            parser: Bits::new(8).unwrap(),
            map: |width| Bits::new(width as u8),
        },
        then: |parser| {
            calls.set(calls.get() + 1);
            parser
        },
    };
    assert_eq!(
        parser.parse(&[65], Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(calls.get(), 0);
    assert_eq!(parser.parse(&[4, 0xa0], Cursor::start()), Ok((at(12), 10)));
    assert_eq!(calls.get(), 1);
}

#[test]
fn borrowed_first_values_and_parser_references_work_without_cloning() {
    let borrowed = Bind {
        parser: TakeAligned { count: 1 },
        then: |byte: &[u8]| Literal::new(8, u64::from(byte[0])).unwrap(),
    };
    assert_eq!(borrowed.parse(b"aa", Cursor::start()), Ok((at(16), 97)));
    let body = TakeAligned { count: 2 };
    let parser = Bind {
        parser: Epsilon,
        then: |()| &body,
    };
    assert_eq!(
        parser.parse(b"ab!", Cursor::start()),
        Ok((at(16), &b"ab"[..]))
    );
    #[cfg(feature = "alloc")]
    {
        // Native Rust supports this shape even though the pinned Aeneas rejects
        // a factory constructing a parser containing a captured reference.
        let parser = Bind {
            parser: formats::CountPrefix,
            then: |count| rusthammer::Repeat::exact(&body, count),
        };
        assert_eq!(
            parser.parse(b"\x02abcd", Cursor::start()),
            Ok((at(40), vec![&b"ab"[..], &b"cd"[..]]))
        );
    }
}

struct Token(Rc<Cell<usize>>);
impl Drop for Token {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}
struct OwnedParser {
    input_value: Token,
    parser_drops: Rc<Cell<usize>>,
    output_drops: Rc<Cell<usize>>,
}
impl Drop for OwnedParser {
    fn drop(&mut self) {
        self.parser_drops.set(self.parser_drops.get() + 1);
    }
}
impl<'input> Grammar<'input> for OwnedParser {
    type Output = Token;
}

impl<'input, Backend> Eval<'input, Backend> for OwnedParser {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Token> {
        assert_eq!(self.input_value.0.get(), 0);
        match Literal::new(8, 97)
            .unwrap()
            .eval(backend, input, cursor, context)
        {
            ParseOutcome::Success(next, _) => {
                ParseOutcome::Success(next, Token(Rc::clone(&self.output_drops)))
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn first_values_constructed_parsers_and_second_values_have_independent_ownership() {
    for (input, context) in [
        (b"a".as_slice(), ParseContext::FINAL),
        (b"b", ParseContext::FINAL),
        (b"", ParseContext::PARTIAL),
        (b"", ParseContext::FINAL),
    ] {
        let first_drops = Rc::new(Cell::new(0));
        let parser_drops = Rc::new(Cell::new(0));
        let output_drops = Rc::new(Cell::new(0));
        let parser = Bind {
            parser: Map {
                parser: Epsilon,
                map: |()| Token(Rc::clone(&first_drops)),
            },
            then: |input_value| OwnedParser {
                input_value,
                parser_drops: Rc::clone(&parser_drops),
                output_drops: Rc::clone(&output_drops),
            },
        };
        let result = parser.parse_with(input, Cursor::start(), context);
        assert_eq!(
            (first_drops.get(), parser_drops.get(), output_drops.get()),
            (1, 1, 0)
        );
        assert_eq!(matches!(result, ParseOutcome::Success(_, _)), input == b"a");
        drop(result);
        assert_eq!(output_drops.get(), usize::from(input == b"a"));
    }
}

#[test]
fn copy_bounds_do_not_extend_to_outputs_or_constructed_parsers() {
    struct Owned(bool);
    struct Body(Owned);
    impl<'input> Grammar<'input> for Body {
        type Output = Owned;
    }

    impl<'input, Backend> Eval<'input, Backend> for Body {
        fn eval(
            &self,
            _: &mut Backend,
            _: &'input [u8],
            cursor: Cursor,
            _: ParseContext,
        ) -> ParseOutcome<Owned> {
            ParseOutcome::Success(cursor, Owned(self.0 .0))
        }
    }
    let parser = Bind {
        parser: Map {
            parser: Bit,
            map: Owned,
        },
        then: Body,
    };
    let copied = parser;
    for parser in [parser, copied] {
        match parser.parse(&[0x80], Cursor::start()) {
            Ok((cursor, Owned(value))) => {
                assert_eq!(cursor, at(1));
                assert!(value);
            }
            _ => panic!("expected success"),
        }
    }
}
