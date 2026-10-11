use std::cell::Cell;

use rusthammer::{
    And, BeU16, BitSpan, Bits, ByteOrder, BytePattern, Cursor, Epsilon, ParseError, Parser,
    Recognize, Seq, SkipBits, TakeAligned, WithByteOrder, WithSpan,
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
            let valid = |c: &Cursor| {
                c.bit < 8 && (c.byte < input.len() || (c.byte == input.len() && c.bit == 0))
            };
            let result = BitSpan::new(&input, *start, *end);
            if !valid(start) || !valid(end) {
                assert_eq!(result, Err(ParseError::InvalidCursor));
            } else if (end.byte, end.bit) < (start.byte, start.bit) {
                assert_eq!(result, Err(ParseError::NonProgress));
            } else {
                let span = result.unwrap();
                assert_eq!(span.start(), *start);
                assert_eq!(span.end(), *end);

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
    let empty = BitSpan::new(&[], Cursor::start(), Cursor::start()).unwrap();
    assert!(empty.is_empty());
    assert_eq!(empty.as_bytes(), Some([].as_slice()));
}

#[test]
fn wrappers_agree_on_region_for_every_bit_range_and_byte_order() {
    let input = [0x96, 0x53, 0xe1];
    for start in 0..=24 {
        for end in start..=24 {
            for byte in [ByteOrder::Big, ByteOrder::Little] {
                let ctx = byte;
                let parser = Bits::new((end - start) as u8).unwrap();
                let span = BitSpan::new(&input, pos(start), pos(end)).unwrap();
                let Ok((next, value)) = parser.parse_with(&input, pos(start), ctx) else {
                    panic!("valid field rejected");
                };
                assert_eq!(next, pos(end));
                assert_eq!(
                    WithSpan { parser }.parse_with(&input, pos(start), ctx),
                    Ok((next, (value, span)))
                );
                assert_eq!(
                    Recognize { parser }.parse_with(&input, pos(start), ctx),
                    Ok((next, span))
                );
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
    let ctx = ByteOrder::Little;
    let Ok((_, span)) = (Recognize {
        parser: Bits::new(16).unwrap(),
    })
    .parse_with(&input, Cursor::start(), ctx) else {
        panic!()
    };
    assert!(std::ptr::eq(span.as_bytes().unwrap(), &input[..2]));
}

#[test]
fn partial_byte_spans_preserve_endpoints_across_nested_byte_order_scopes() {
    let input = [0x96, 0x53, 0xe1];
    let parser = WithSpan {
        parser: Seq {
            first: WithByteOrder {
                byte_order: ByteOrder::Little,
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
    assert_eq!(value, 4);

    assert_eq!((inner.start(), inner.end()), (pos(0), pos(3)));
    assert_eq!(following, 2);

    assert_eq!((tail.start(), tail.end()), (pos(8), pos(11)));

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
        for ctx in [ByteOrder::Big] {
            let expected = BitSpan::new(&input, cursor, cursor).unwrap();
            assert_eq!(
                (Recognize { parser: Epsilon }).parse_with(&input, cursor, ctx),
                Ok((cursor, expected))
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
fn truncated_input_retry_returns_a_span_of_the_new_buffer() {
    let parser = WithSpan { parser: BeU16 };

    assert_eq!(
        parser.parse(&[0x12], pos(0)),
        Err(ParseError::UnexpectedEnd)
    );
    let accumulated = [0x12, 0x34];
    let Ok((_, (value, span))) = parser.parse_with(&accumulated, pos(0), ByteOrder::Big) else {
        panic!()
    };
    assert_eq!(value, 0x1234);
    assert!(std::ptr::eq(span.input(), accumulated.as_slice()));
}

#[derive(Default)]
struct Trace(std::cell::RefCell<Vec<(Cursor, ByteOrder)>>);

struct Dropped<'a>(&'a Cell<usize>);

impl Drop for Dropped<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

// Records calls inside the custom child. Its output is neither Clone nor Copy.
#[derive(Clone, Copy)]
struct Script<'a> {
    trace: &'a Trace,
    outcome: &'a Result<(Cursor, ()), ParseError>,
    drops: &'a Cell<usize>,
}

impl<'input, 'a> Parser<'input> for Script<'a> {
    type Output = Dropped<'a>;

    fn parse_with(
        &self,
        _: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.trace.0.borrow_mut().push((cursor, byte_order));
        match *self.outcome {
            Ok(parsed) => {
                let (next, ()) = parsed;
                Ok((next, Dropped(self.drops)))
            }
            Err(error) => Err(error),
        }
    }
}

#[test]
fn validation_propagation_child_effects_and_output_drop() {
    let input = [0x96];
    let ctx = ByteOrder::Little;
    let outcomes = [
        Ok((pos(4), ())),
        Ok((pos(3), ())),
        Ok((pos(2), ())),
        Ok((pos(9), ())),
        Ok((Cursor { byte: 0, bit: 8 }, ())),
        Err(ParseError::Mismatch),
        Err(ParseError::UnexpectedEnd),
        Err(ParseError::Unaligned),
        Err(ParseError::NonProgress),
        Err(ParseError::InvalidCursor),
        Err(ParseError::TrailingInput),
        Err(ParseError::CountOverflow),
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
            let trace = Trace::default();
            let parser = Script {
                trace: &trace,
                outcome,
                drops: &drops,
            };
            let copied = WithSpan { parser };
            let _copy = copied;
            let result = copied.parse_with(&input, start, ctx);
            let expected = if start != pos(3) {
                assert!(trace.0.borrow().is_empty());
                Err(ParseError::InvalidCursor)
            } else {
                assert_eq!(*trace.0.borrow(), [(start, ctx)]);
                match *outcome {
                    Ok(parsed) => {
                        let (end, ()) = parsed;
                        match BitSpan::new(&input, start, end) {
                            Ok(span) => Ok((end, span)),
                            Err(error) => Err(error),
                        }
                    }
                    Err(error) => Err(error),
                }
            };
            let projected = match result {
                Ok(parsed) => {
                    let (end, (value, span)) = parsed;
                    assert_eq!(drops.get(), 0);
                    drop(value);
                    Ok((end, span))
                }
                Err(error) => Err(error),
            };
            assert_eq!(projected, expected);
            let produced = usize::from(start == pos(3) && matches!(outcome, Ok((..))));
            assert_eq!(drops.get(), produced);
            drops.set(0);
            trace.0.borrow_mut().clear();
            let recognized = Recognize { parser };
            let _copy = recognized;
            assert_eq!(recognized.parse_with(&input, start, ctx), expected);
            assert_eq!(trace.0.borrow().len(), usize::from(start == pos(3)));
            assert_eq!(drops.get(), produced);
        }
    }
}
