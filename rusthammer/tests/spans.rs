use std::cell::Cell;

use rusthammer::{
    And, BeU16, BitOrder, BitSpan, Bits, ByteOrder, BytePattern, Cursor, Epsilon, Eval, Grammar,
    Order, ParseContext, ParseError, ParseOutcome, Parser, Recognize, Seq, SkipBits, TakeAligned,
    WithOrder, WithSpan,
};

fn pos(bit: usize) -> Cursor {
    Cursor {
        byte: bit / 8,
        bit: (bit % 8) as u8,
    }
}

#[test]
fn constructor_checks_all_small_bounds_and_preserves_original_views() {
    let input = [0x96, 0x53, 0xe1];
    let cursors: Vec<_> = (0..=4)
        .flat_map(|byte| (0..=9).map(move |bit| Cursor { byte, bit }))
        .chain([Cursor {
            byte: usize::MAX,
            bit: u8::MAX,
        }])
        .collect();
    for start in &cursors {
        for end in &cursors {
            for order in [BitOrder::HighFirst, BitOrder::LowFirst] {
                let valid = |c: &Cursor| {
                    c.bit < 8 && (c.byte < input.len() || (c.byte == input.len() && c.bit == 0))
                };
                let result = BitSpan::new(&input, *start, *end, order);
                if !valid(start) || !valid(end) {
                    assert_eq!(result, Err(ParseError::InvalidCursor));
                } else if (end.byte, end.bit) < (start.byte, start.bit) {
                    assert_eq!(result, Err(ParseError::NonProgress));
                } else {
                    let span = result.unwrap();
                    assert_eq!(span.start(), *start);
                    assert_eq!(span.end(), *end);
                    assert_eq!(span.bit_order(), order);
                    assert!(std::ptr::eq(span.input(), input.as_slice()));
                    assert_eq!(span.is_empty(), start == end);
                    if start.bit == 0 && end.bit == 0 {
                        let bytes = span.as_bytes().unwrap();
                        assert!(std::ptr::eq(bytes, &input[start.byte..end.byte]));
                    } else {
                        assert_eq!(span.as_bytes(), None);
                    }
                }
            }
        }
    }
    let empty = BitSpan::new(&[], Cursor::start(), Cursor::start(), BitOrder::LowFirst).unwrap();
    assert!(empty.is_empty());
    assert_eq!(empty.as_bytes(), Some([].as_slice()));
}

#[test]
fn wrappers_agree_on_region_for_every_bit_range_order_and_finality() {
    let input = [0x96, 0x53, 0xe1];
    for start in 0..=24 {
        for end in start..=24 {
            for bit in [BitOrder::HighFirst, BitOrder::LowFirst] {
                for byte in [ByteOrder::Big, ByteOrder::Little] {
                    for status in [
                        rusthammer::InputStatus::Partial,
                        rusthammer::InputStatus::Final,
                    ] {
                        let ctx = ParseContext {
                            order: Order { bit, byte },
                            status,
                        };
                        let parser = Bits::new((end - start) as u8).unwrap();
                        let span = BitSpan::new(&input, pos(start), pos(end), bit).unwrap();
                        let ParseOutcome::Success(next, value) =
                            parser.parse_with(&input, pos(start), ctx)
                        else {
                            panic!("valid field rejected");
                        };
                        assert_eq!(next, pos(end));
                        assert_eq!(
                            WithSpan { parser }.parse_with(&input, pos(start), ctx),
                            ParseOutcome::Success(next, (value, span))
                        );
                        assert_eq!(
                            Recognize { parser }.parse_with(&input, pos(start), ctx),
                            ParseOutcome::Success(next, span)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn byte_view_outlives_parser_and_span_and_keeps_original_order() {
    let input = [0x12, 0x34, 0x56];
    let bytes = {
        let parser = WithSpan { parser: BeU16 };
        let (_, (value, span)) = parser.parse(&input, Cursor::start()).unwrap();
        assert_eq!(value, 0x1234);
        span.as_bytes().unwrap()
    };
    assert!(std::ptr::eq(bytes, &input[..2]));
    let ctx = ParseContext {
        order: Order {
            bit: BitOrder::LowFirst,
            byte: ByteOrder::Little,
        },
        ..ParseContext::FINAL
    };
    let ParseOutcome::Success(_, span) = (Recognize {
        parser: Bits::new(16).unwrap(),
    })
    .parse_with(&input, Cursor::start(), ctx) else {
        panic!()
    };
    assert!(std::ptr::eq(span.as_bytes().unwrap(), &input[..2]));
}

#[test]
fn escaped_partial_span_remembers_inner_direction_and_nested_scopes() {
    let input = [0x96, 0x53, 0xe1];
    let parser = WithSpan {
        parser: Seq {
            first: WithOrder {
                order: Order {
                    bit: BitOrder::LowFirst,
                    byte: ByteOrder::Little,
                },
                parser: Seq {
                    first: WithSpan {
                        parser: Bits::new(3).unwrap(),
                    },
                    second: SkipBits::new(5),
                },
            },
            second: WithSpan {
                parser: Bits::new(3).unwrap(),
            },
        },
    };
    let (_, ((((value, inner), ()), (following, tail)), outer)) =
        parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(value, 6);
    assert_eq!(inner.bit_order(), BitOrder::LowFirst);
    assert_eq!((inner.start(), inner.end()), (pos(0), pos(3)));
    assert_eq!(following, 2);
    assert_eq!(tail.bit_order(), BitOrder::HighFirst);
    assert_eq!((tail.start(), tail.end()), (pos(8), pos(11)));
    assert_eq!(outer.bit_order(), BitOrder::HighFirst);
    assert_eq!((outer.start(), outer.end()), (pos(0), pos(11)));
    assert_eq!(outer.as_bytes(), None);
}

#[test]
fn configuration_and_input_borrows_are_independent() {
    let input = *b"abc";
    let retained = {
        let pattern = *b"ab";
        let parser = WithSpan {
            parser: BytePattern::new(&pattern),
        };
        let (_, (matched_pattern, span)) = parser.parse(&input, Cursor::start()).unwrap();
        assert!(std::ptr::eq(matched_pattern, pattern.as_slice()));
        span
    };
    assert!(std::ptr::eq(retained.as_bytes().unwrap(), &input[..2]));
    let (_, (borrowed, span)) = (WithSpan {
        parser: TakeAligned { count: 2 },
    })
    .parse(&input, Cursor::start())
    .unwrap();
    assert!(std::ptr::eq(borrowed, span.as_bytes().unwrap()));
}

#[test]
fn lookahead_and_empty_children_report_consumption_not_inspection() {
    let input = [0x96];
    for cursor in [pos(0), pos(3), pos(8)] {
        for ctx in [ParseContext::PARTIAL, ParseContext::FINAL] {
            let expected = BitSpan::new(&input, cursor, cursor, ctx.order.bit).unwrap();
            assert_eq!(
                (Recognize { parser: Epsilon }).parse_with(&input, cursor, ctx),
                ParseOutcome::Success(cursor, expected)
            );
        }
    }
    let (_, span) = (Recognize {
        parser: And { parser: BeU16 },
    })
    .parse(&[0x12, 0x34], pos(0))
    .unwrap();
    assert!(span.is_empty());
}

#[test]
fn incomplete_retry_returns_a_span_of_the_new_buffer() {
    let parser = WithSpan { parser: BeU16 };
    assert_eq!(
        parser.parse_with(&[0x12], pos(0), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse(&[0x12], pos(0)),
        Err(ParseError::UnexpectedEnd)
    );
    let accumulated = [0x12, 0x34];
    let ParseOutcome::Success(_, (value, span)) =
        parser.parse_with(&accumulated, pos(0), ParseContext::PARTIAL)
    else {
        panic!()
    };
    assert_eq!(value, 0x1234);
    assert!(std::ptr::eq(span.input(), accumulated.as_slice()));
}

#[derive(Default)]
struct Trace(Vec<(Cursor, ParseContext)>);

struct Dropped<'a>(&'a Cell<usize>);

impl Drop for Dropped<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

// Only supports this stateful backend. Its output is neither Clone nor Copy.
#[derive(Clone, Copy)]
struct Script<'a> {
    outcome: &'a ParseOutcome<()>,
    drops: &'a Cell<usize>,
}

impl<'input, 'a> Grammar<'input> for Script<'a> {
    type Output = Dropped<'a>;
}

impl<'input> Eval<'input, Trace> for Script<'_> {
    fn eval(
        &self,
        backend: &mut Trace,
        _: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        backend.0.push((cursor, context));
        match *self.outcome {
            ParseOutcome::Success(next, ()) => ParseOutcome::Success(next, Dropped(self.drops)),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn validation_propagation_backend_effects_and_output_drop() {
    let input = [0x96];
    let ctx = ParseContext {
        order: Order {
            bit: BitOrder::LowFirst,
            byte: ByteOrder::Little,
        },
        ..ParseContext::PARTIAL
    };
    let outcomes = [
        ParseOutcome::Success(pos(4), ()),
        ParseOutcome::Success(pos(3), ()),
        ParseOutcome::Success(pos(2), ()),
        ParseOutcome::Success(pos(9), ()),
        ParseOutcome::Success(Cursor { byte: 0, bit: 8 }, ()),
        ParseOutcome::NeedMore,
        ParseOutcome::Error(ParseError::Mismatch),
        ParseOutcome::Error(ParseError::UnexpectedEnd),
        ParseOutcome::Error(ParseError::Unaligned),
        ParseOutcome::Error(ParseError::NonProgress),
        ParseOutcome::Error(ParseError::InvalidCursor),
        ParseOutcome::Error(ParseError::TrailingInput),
        ParseOutcome::Error(ParseError::CountOverflow),
    ];
    for outcome in &outcomes {
        for start in [
            pos(3),
            pos(9),
            Cursor {
                byte: usize::MAX,
                bit: 0,
            },
        ] {
            let drops = Cell::new(0);
            let parser = Script {
                outcome,
                drops: &drops,
            };
            let mut trace = Trace::default();
            let copied = WithSpan { parser };
            let _copy = copied;
            let result = copied.eval(&mut trace, &input, start, ctx);
            let expected = if start != pos(3) {
                assert!(trace.0.is_empty());
                ParseOutcome::Error(ParseError::InvalidCursor)
            } else {
                assert_eq!(trace.0, [(start, ctx)]);
                match *outcome {
                    ParseOutcome::Success(end, ()) => {
                        match BitSpan::new(&input, start, end, ctx.order.bit) {
                            Ok(span) => ParseOutcome::Success(end, span),
                            Err(error) => ParseOutcome::Error(error),
                        }
                    }
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                }
            };
            let projected = match result {
                ParseOutcome::Success(end, (value, span)) => {
                    assert_eq!(drops.get(), 0);
                    drop(value);
                    ParseOutcome::Success(end, span)
                }
                ParseOutcome::Error(error) => ParseOutcome::Error(error),
                ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            };
            assert_eq!(projected, expected);
            let produced =
                usize::from(start == pos(3) && matches!(outcome, ParseOutcome::Success(..)));
            assert_eq!(drops.get(), produced);
            drops.set(0);
            let mut second_trace = Trace::default();
            let recognized = Recognize { parser };
            let _copy = recognized;
            assert_eq!(
                recognized.eval(&mut second_trace, &input, start, ctx),
                expected
            );
            assert_eq!(second_trace.0, trace.0);
            assert_eq!(drops.get(), produced);
        }
    }
}
