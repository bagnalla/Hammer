use super::*;
use std::cell::Cell;

fn order(flags: u8) -> Order {
    Order {
        bit: if flags & 2 != 0 {
            BitOrder::HighFirst
        } else {
            BitOrder::LowFirst
        },
        byte: if flags & 1 != 0 {
            ByteOrder::Big
        } else {
            ByteOrder::Little
        },
    }
}

fn ctx(flags: u8, status: InputStatus) -> ParseContext {
    ParseContext {
        order: order(flags),
        status,
    }
}

fn field(width: u8) -> Field {
    Field::new(width).unwrap()
}
const START: Cursor = Cursor { byte: 0, bit: 0 };

// Independent numeric oracle: select physical bit positions, then concatenate
// boolean fragments in significance order. No shift/mask decoder is reused.
fn oracle(input: &[u8], cursor: Cursor, width: u8, context: ParseContext) -> Outcome<u64> {
    let position = 8 * cursor.byte as u128 + cursor.bit as u128;
    if cursor.bit >= 8 || position > 8 * input.len() as u128 {
        return Outcome::Error(ParseError::InvalidCursor);
    }
    if position + width as u128 > 8 * input.len() as u128 {
        return match context.status {
            InputStatus::Partial => Outcome::NeedMore,
            InputStatus::Final => Outcome::Error(ParseError::UnexpectedEnd),
        };
    }
    let mut fragments = Vec::new();
    let mut offset = position as usize;
    let finish = offset + width as usize;
    while offset < finish {
        let end = finish.min((offset / 8 + 1) * 8);
        let mut positions: Vec<usize> = (offset..end)
            .map(|p| match context.order.bit {
                BitOrder::HighFirst => 7 - p % 8,
                BitOrder::LowFirst => p % 8,
            })
            .collect();
        positions.sort_by(|a, b| b.cmp(a));
        fragments.push(
            positions
                .into_iter()
                .map(|b| input[offset / 8] & (1 << b) != 0)
                .collect::<Vec<_>>(),
        );
        offset = end;
    }
    if context.order.byte == ByteOrder::Little {
        fragments.reverse();
    }
    let value = fragments
        .into_iter()
        .flatten()
        .fold(0, |n, b| n * 2 + u64::from(b));
    Outcome::Success(
        Cursor {
            byte: finish / 8,
            bit: (finish % 8) as u8,
        },
        value,
    )
}

#[test]
fn field_values_widths_and_both_finalities() {
    let data = [0xd6, 0xab, 0x61, 0x82, 0x17, 0xff, 0x00, 0x5b, 0xc9];
    for length in 0..=data.len() {
        for byte in [0, 1, length, usize::MAX] {
            for bit in 0..=8 {
                let cursor = Cursor { byte, bit };
                for width in 0..=64 {
                    for flags in 0..4 {
                        for status in [InputStatus::Final, InputStatus::Partial] {
                            let context = ctx(flags, status);
                            assert_eq!(
                                field(width).parse_with(&data[..length], cursor, context),
                                oracle(&data[..length], cursor, width, context)
                            );
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Answer {
    Success(Cursor),
    Error(ParseError),
    NeedMore,
}

struct Scripted<'a> {
    calls: &'a Cell<usize>,
    expected_context: ParseContext,
    answer: Answer,
}

impl<'input> Parser<'input> for Scripted<'_> {
    type Output = u64;
    fn parse_with(&self, _: &'input [u8], _: Cursor, context: ParseContext) -> Outcome<u64> {
        self.calls.set(self.calls.get() + 1);
        assert_eq!(context, self.expected_context);
        match self.answer {
            Answer::Success(next) => Outcome::Success(next, 42),
            Answer::Error(error) => Outcome::Error(error),
            Answer::NeedMore => Outcome::NeedMore,
        }
    }
}

#[test]
fn entry_errors_do_not_call_the_child() {
    let cases = [
        (Cursor { byte: 0, bit: 1 }, ParseError::Unaligned),
        (Cursor { byte: 0, bit: 7 }, ParseError::Unaligned),
        (Cursor { byte: 0, bit: 8 }, ParseError::InvalidCursor),
        (Cursor { byte: 1, bit: 1 }, ParseError::InvalidCursor),
        (Cursor { byte: 2, bit: 0 }, ParseError::InvalidCursor),
        (
            Cursor {
                byte: usize::MAX,
                bit: 255,
            },
            ParseError::InvalidCursor,
        ),
    ];
    for ambient in 0..4 {
        for selected in 0..4 {
            if order(ambient).bit == order(selected).bit {
                continue;
            }
            for status in [InputStatus::Partial, InputStatus::Final] {
                for (cursor, error) in cases {
                    for answer in [
                        Answer::Success(START),
                        Answer::Error(ParseError::Mismatch),
                        Answer::NeedMore,
                    ] {
                        let calls = Cell::new(0);
                        let parser = WithOrder {
                            order: order(selected),
                            child: Scripted {
                                calls: &calls,
                                expected_context: ctx(selected, status),
                                answer,
                            },
                        };
                        assert_eq!(
                            parser.parse_with(&[0], cursor, ctx(ambient, status)),
                            Outcome::Error(error)
                        );
                        assert_eq!(calls.get(), 0);
                    }
                }
            }
        }
    }
}

#[test]
fn exit_guards_and_error_propagation() {
    let cases = [
        (Answer::Success(START), Outcome::Success(START, 42)),
        (
            Answer::Success(Cursor { byte: 1, bit: 0 }),
            Outcome::Success(Cursor { byte: 1, bit: 0 }, 42),
        ),
        (
            Answer::Success(Cursor { byte: 0, bit: 3 }),
            Outcome::Error(ParseError::Unaligned),
        ),
        (
            Answer::Success(Cursor { byte: 0, bit: 8 }),
            Outcome::Error(ParseError::InvalidCursor),
        ),
        (
            Answer::Success(Cursor { byte: 1, bit: 1 }),
            Outcome::Error(ParseError::InvalidCursor),
        ),
        (
            Answer::Success(Cursor { byte: 2, bit: 0 }),
            Outcome::Error(ParseError::InvalidCursor),
        ),
        (Answer::NeedMore, Outcome::NeedMore),
        (
            Answer::Error(ParseError::UnexpectedEnd),
            Outcome::Error(ParseError::UnexpectedEnd),
        ),
        (
            Answer::Error(ParseError::Mismatch),
            Outcome::Error(ParseError::Mismatch),
        ),
        (
            Answer::Error(ParseError::TrailingInput),
            Outcome::Error(ParseError::TrailingInput),
        ),
        (
            Answer::Error(ParseError::InvalidCursor),
            Outcome::Error(ParseError::InvalidCursor),
        ),
        (
            Answer::Error(ParseError::Unaligned),
            Outcome::Error(ParseError::Unaligned),
        ),
        (
            Answer::Error(ParseError::NonProgress),
            Outcome::Error(ParseError::NonProgress),
        ),
        (
            Answer::Error(ParseError::CountOverflow),
            Outcome::Error(ParseError::CountOverflow),
        ),
    ];
    for status in [InputStatus::Partial, InputStatus::Final] {
        for (answer, expected) in &cases {
            let calls = Cell::new(0);
            let parser = WithOrder {
                order: order(0),
                child: Scripted {
                    calls: &calls,
                    expected_context: ctx(0, status),
                    answer: *answer,
                },
            };
            assert_eq!(&parser.parse_with(&[0], START, ctx(3, status)), expected);
            assert_eq!(calls.get(), 1);
        }
    }
}

#[test]
fn same_direction_is_transparent_even_for_custom_cursors() {
    for ambient in 0..4 {
        let selected = ambient ^ 1; // Byte order only.
        for status in [InputStatus::Partial, InputStatus::Final] {
            for start in [
                START,
                Cursor { byte: 0, bit: 3 },
                Cursor {
                    byte: usize::MAX,
                    bit: 255,
                },
            ] {
                let calls = Cell::new(0);
                let end = Cursor {
                    byte: usize::MAX,
                    bit: 255,
                };
                let parser = WithOrder {
                    order: order(selected),
                    child: Scripted {
                        calls: &calls,
                        expected_context: ctx(selected, status),
                        answer: Answer::Success(end),
                    },
                };
                assert_eq!(
                    parser.parse_with(&[0], start, ctx(ambient, status)),
                    Outcome::Success(end, 42)
                );
                assert_eq!(calls.get(), 1);
            }
        }
    }
}

#[test]
fn same_direction_nested_fields_and_unaligned_byte_order_changes() {
    let parser = WithOrder {
        order: order(0),
        child: Seq(
            field(3),
            WithOrder {
                order: order(0),
                child: field(5),
            },
        ),
    };
    assert_eq!(
        parser.parse_with(&[0xd6], START, ctx(3, InputStatus::Final)),
        Outcome::Success(Cursor { byte: 1, bit: 0 }, (6, 26))
    );
    for ambient in 0..4 {
        for bit in 0..8 {
            let cursor = Cursor { byte: 0, bit };
            let parser = WithOrder {
                order: order(ambient ^ 1),
                child: field(10),
            };
            let input = [0xd6, 0xab, 0x61];
            assert_eq!(
                parser.parse_with(&input, cursor, ctx(ambient, InputStatus::Final)),
                oracle(&input, cursor, 10, ctx(ambient ^ 1, InputStatus::Final))
            );
        }
    }
}

#[test]
fn nested_scopes_restore_order_and_finality() {
    let data = [0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x11, 0x22];
    let result = nested(
        &data,
        [16; 5],
        order(0),
        order(3),
        ctx(3, InputStatus::Final),
    );
    assert_eq!(
        result,
        Some(Outcome::Success(
            Cursor { byte: 10, bit: 0 },
            (0x1234, (0x7856, (0x9abc, 0xf0de)), 0x1122)
        ))
    );
    for length in 0..data.len() {
        assert_eq!(
            nested(
                &data[..length],
                [16; 5],
                order(0),
                order(3),
                ctx(3, InputStatus::Partial)
            ),
            Some(Outcome::NeedMore)
        );
        assert_eq!(
            nested(
                &data[..length],
                [16; 5],
                order(0),
                order(3),
                ctx(3, InputStatus::Final)
            ),
            Some(Outcome::Error(ParseError::UnexpectedEnd))
        );
    }
    // A successful 3-bit child is a scope violation even on partial input.
    for status in [InputStatus::Final, InputStatus::Partial] {
        assert_eq!(
            WithOrder {
                order: order(0),
                child: field(3)
            }
            .parse_with(&[0xff], START, ctx(3, status)),
            Outcome::Error(ParseError::Unaligned)
        );
    }
}

#[test]
fn lookahead_obeys_scope_boundaries_and_shortage_rules() {
    let low = order(1);
    for status in [InputStatus::Final, InputStatus::Partial] {
        let context = ctx(3, status);
        assert_eq!(
            WithOrder {
                order: low,
                child: And(field(3))
            }
            .parse_with(&[0xff], START, context),
            Outcome::Success(START, ())
        );
        assert_eq!(
            And(WithOrder {
                order: low,
                child: field(3)
            })
            .parse_with(&[0xff], START, context),
            Outcome::Error(ParseError::Unaligned)
        );
        assert_eq!(
            Not(WithOrder {
                order: low,
                child: field(3)
            })
            .parse_with(&[0xff], START, context),
            Outcome::Error(ParseError::Unaligned)
        );
        assert_eq!(
            WithOrder {
                order: low,
                child: Not(field(3))
            }
            .parse_with(&[0xff], START, context),
            Outcome::Error(ParseError::Mismatch)
        );
        assert_eq!(
            lookahead(&[0xff], context),
            Outcome::Error(ParseError::Unaligned)
        );
    }
    assert_eq!(
        lookahead(&[], ctx(3, InputStatus::Partial)),
        Outcome::NeedMore
    );
    assert_eq!(
        lookahead(&[], ctx(3, InputStatus::Final)),
        Outcome::Error(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        WithOrder {
            order: low,
            child: Not(field(3))
        }
        .parse_with(&[], START, ctx(3, InputStatus::Final)),
        Outcome::Success(START, ())
    );
    assert_eq!(
        WithOrder {
            order: low,
            child: field(0)
        }
        .parse_with(&[], START, ctx(3, InputStatus::Final)),
        Outcome::Success(START, 0)
    );
    assert_eq!(
        WithOrder {
            order: low,
            child: field(0)
        }
        .parse_with(&[0], Cursor { byte: 0, bit: 1 }, ctx(3, InputStatus::Final)),
        Outcome::Error(ParseError::Unaligned)
    );
}

#[test]
fn escaped_span_keeps_input_identity_and_its_boundary_direction() {
    let input = [0x96];
    let parsed = escaped_span(&input, ctx(3, InputStatus::Final));
    match parsed {
        Outcome::Success(next, ((value, span), rest)) => {
            assert_eq!(next, Cursor { byte: 1, bit: 0 });
            assert_eq!((value, rest), (6, 18));
            assert!(core::ptr::eq(span.input.as_ptr(), input.as_ptr()));
            assert_eq!(span.start, START);
            assert_eq!(span.end, Cursor { byte: 0, bit: 3 });
            assert_eq!(span.bit_order, BitOrder::LowFirst);
            // The same positions in the enclosing high-first context select 4.
            assert_eq!(input[0] & 7, value as u8);
            assert_eq!(input[0] >> 5, 4);
        }
        other => panic!("unexpected {other:?}"),
    }
    assert_eq!(
        escaped_span(&[], ctx(3, InputStatus::Partial)),
        Outcome::NeedMore
    );
}

#[test]
fn scope_discards_owned_outputs_exactly_once_on_exit_errors() {
    struct Owned<'a>(&'a Cell<usize>);
    impl Drop for Owned<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    struct Produce<'a> {
        drops: &'a Cell<usize>,
        next: Cursor,
    }
    impl<'input, 'a> Parser<'input> for Produce<'a> {
        type Output = Owned<'a>;
        fn parse_with(&self, _: &'input [u8], _: Cursor, _: ParseContext) -> Outcome<Owned<'a>> {
            Outcome::Success(self.next, Owned(self.drops))
        }
    }
    for next in [Cursor { byte: 0, bit: 3 }, Cursor { byte: 2, bit: 0 }] {
        let drops = Cell::new(0);
        let parser = WithOrder {
            order: order(0),
            child: Produce {
                drops: &drops,
                next,
            },
        };
        assert!(matches!(
            parser.parse_with(&[0], START, ctx(3, InputStatus::Final)),
            Outcome::Error(_)
        ));
        assert_eq!(drops.get(), 1);
    }
    let drops = Cell::new(0);
    let parser = WithOrder {
        order: order(0),
        child: Produce {
            drops: &drops,
            next: START,
        },
    };
    let result = parser.parse_with(&[0], START, ctx(3, InputStatus::Final));
    assert_eq!(drops.get(), 0);
    drop(result);
    assert_eq!(drops.get(), 1);
}

#[test]
fn validation_at_machine_boundaries_and_span_rejections() {
    assert_eq!(
        boundary_error(
            usize::MAX,
            Cursor {
                byte: usize::MAX,
                bit: 0
            }
        ),
        None
    );
    assert_eq!(
        boundary_error(
            usize::MAX,
            Cursor {
                byte: usize::MAX,
                bit: 1
            }
        ),
        Some(ParseError::InvalidCursor)
    );
    assert_eq!(
        boundary_error(
            usize::MAX,
            Cursor {
                byte: usize::MAX - 1,
                bit: 7
            }
        ),
        Some(ParseError::Unaligned)
    );
    for width in 0..=255 {
        assert_eq!(Field::new(width).is_some(), width <= 64);
    }
    for (end, expected) in [
        (START, ParseError::NonProgress),
        (Cursor { byte: 1, bit: 1 }, ParseError::InvalidCursor),
    ] {
        let calls = Cell::new(0);
        let context = ctx(0, InputStatus::Final);
        let parser = WithSpan(Scripted {
            calls: &calls,
            expected_context: context,
            answer: Answer::Success(end),
        });
        assert_eq!(
            parser.parse_with(&[0], Cursor { byte: 0, bit: 3 }, context),
            Outcome::Error(expected)
        );
    }
    let parser = WithSpan(field(0));
    assert!(matches!(
        parser.parse_with(&[0], Cursor { byte: 0, bit: 3 }, ctx(0, InputStatus::Final)),
        Outcome::Success(_, _)
    ));
}
