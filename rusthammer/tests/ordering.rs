use rusthammer::*;
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

fn field(width: u8) -> Bits {
    Bits::new(width).unwrap()
}
const START: Cursor = Cursor { byte: 0, bit: 0 };

// Independent numeric oracle: select physical bit positions, then concatenate
// boolean fragments in significance order. No shift/mask decoder is reused.
fn oracle(input: &[u8], cursor: Cursor, width: u8, context: ParseContext) -> ParseOutcome<u64> {
    let position = 8 * cursor.byte as u128 + cursor.bit as u128;
    if cursor.bit >= 8 || position > 8 * input.len() as u128 {
        return ParseOutcome::Error(ParseError::InvalidCursor);
    }
    if position + width as u128 > 8 * input.len() as u128 {
        return match context.status {
            InputStatus::Partial => ParseOutcome::NeedMore,
            InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
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
    ParseOutcome::Success(
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

fn converted<T>(value: ParseOutcome<u64>, f: impl FnOnce(u64) -> T) -> ParseOutcome<T> {
    match value {
        ParseOutcome::Success(next, value) => ParseOutcome::Success(next, f(value)),
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

fn signed(value: u64, width: u8) -> i64 {
    if width == 0 {
        0
    } else if value & (1 << (width - 1)) == 0 {
        value as i64
    } else {
        (i128::from(value) - (1i128 << width)) as i64
    }
}

#[test]
fn typed_readers_literals_sets_and_patterns_use_the_documented_order() {
    let input = [0xd6, 0x92, 0x81, 0xff, 0x00, 0x17, 0xa4, 0x53, 0xbc];
    for flags in 0..4 {
        for status in [InputStatus::Final, InputStatus::Partial] {
            let context = ctx(flags, status);
            let big = ParseContext {
                order: Order {
                    byte: ByteOrder::Big,
                    ..context.order
                },
                ..context
            };
            for bit in 0..8 {
                let start = Cursor { byte: 0, bit };
                for length in 0..=input.len() {
                    let data = &input[..length];
                    for width in 0..=64 {
                        let expected = oracle(data, start, width, context);
                        assert_eq!(
                            SignedBits::new(width)
                                .unwrap()
                                .parse_with(data, start, context),
                            converted(expected, |v| signed(v, width))
                        );
                    }
                    macro_rules! unsigned_reader {
                        ($parser:expr, $width:expr, $ty:ty, $context:expr) => {
                            assert_eq!(
                                $parser.parse_with(data, start, context),
                                converted(oracle(data, start, $width, $context), |v| v as $ty)
                            );
                        };
                    }
                    macro_rules! signed_reader {
                        ($parser:expr, $width:expr, $ty:ty, $context:expr) => {
                            assert_eq!(
                                $parser.parse_with(data, start, context),
                                converted(oracle(data, start, $width, $context), |v| signed(
                                    v, $width
                                ) as $ty)
                            );
                        };
                    }
                    unsigned_reader!(Byte, 8, u8, context);
                    unsigned_reader!(BeU16, 16, u16, big);
                    unsigned_reader!(BeU32, 32, u32, big);
                    unsigned_reader!(BeU64, 64, u64, big);
                    signed_reader!(I8, 8, i8, context);
                    signed_reader!(BeI16, 16, i16, big);
                    signed_reader!(BeI32, 32, i32, big);
                    signed_reader!(BeI64, 64, i64, big);
                    assert_eq!(
                        Bit.parse_with(data, start, context),
                        converted(oracle(data, start, 1, context), |v| v != 0)
                    );
                }
                let ParseOutcome::Success(next, value) = oracle(&input, start, 8, context) else {
                    unreachable!()
                };
                let value = value as u8;
                assert_eq!(
                    Literal::new(8, u64::from(value))
                        .unwrap()
                        .parse_with(&input, start, context),
                    ParseOutcome::Success(next, u64::from(value))
                );
                assert_eq!(
                    Literal::new(8, u64::from(value ^ 1))
                        .unwrap()
                        .parse_with(&input, start, context),
                    ParseOutcome::Error(ParseError::Mismatch)
                );
                assert_eq!(
                    ByteIn::new(&[value]).parse_with(&input, start, context),
                    ParseOutcome::Success(next, value)
                );
                assert_eq!(
                    ByteNotIn::new(&[value]).parse_with(&input, start, context),
                    ParseOutcome::Error(ParseError::Mismatch)
                );
                let ParseOutcome::Success(end, second) = oracle(&input, next, 8, context) else {
                    unreachable!()
                };
                let pattern = [value, second as u8];
                let ParseOutcome::Success(actual_end, matched) =
                    BytePattern::new(&pattern).parse_with(&input, start, context)
                else {
                    panic!("contextual pattern did not match")
                };
                assert_eq!(actual_end, end);
                assert!(core::ptr::eq(matched, &pattern[..]));
                assert_eq!(
                    SkipBits::new(8).parse_with(&input, start, context),
                    ParseOutcome::Success(next, ())
                );
                assert_eq!(
                    Tell.parse_with(&input, start, context),
                    ParseOutcome::Success(start, start)
                );
            }
        }
    }
}

#[test]
fn scopes_compose_with_borrowing_repetition_and_selection() {
    let data = [0x96, 0x12, 0x34, 0x56];
    let low = order(0);
    let parser = Seq {
        first: WithOrder {
            order: low,
            parser: Seq {
                first: field(3),
                second: field(5),
            },
        },
        second: Seq {
            first: TakeAligned { count: 1 },
            second: BeU16,
        },
    };
    let copied = parser;
    for grammar in [&parser, &copied] {
        let (_, ((first, second), (payload, number))) = grammar.parse(&data, START).unwrap();
        assert_eq!((first, second, number), (6, 18, 0x3456));
        assert!(core::ptr::eq(payload, &data[1..2]));
    }
    let folded = WithOrder {
        order: low,
        parser: FoldRepeat::exact(field(4), 2, || 0, |sum, nibble| sum + nibble),
    };
    assert_eq!(
        folded.parse(&data, START),
        Ok((Cursor { byte: 1, bit: 0 }, 15))
    );
    let invalid = WithOrder {
        order: low,
        parser: field(3),
    };
    assert_eq!(
        Choice {
            first: invalid,
            second: field(8)
        }
        .parse(&data, START),
        Err(ParseError::Unaligned)
    );
    assert_eq!(
        Optional { parser: invalid }.parse(&data, START),
        Err(ParseError::Unaligned)
    );
    let bits = WithOrder {
        order: low,
        parser: Left {
            first: field(3),
            second: SkipBits::new(5),
        },
    };
    assert_eq!(
        bits.parse(&data, START),
        Ok((Cursor { byte: 1, bit: 0 }, 6))
    );
    #[cfg(feature = "alloc")]
    {
        let repeated = WithOrder {
            order: low,
            parser: Repeat::exact(field(4), 2),
        };
        assert_eq!(
            repeated.parse(&data, START),
            Ok((Cursor { byte: 1, bit: 0 }, vec![6, 9]))
        );
        assert_eq!(
            Repeat::exact(invalid, 2).parse(&data, START),
            Err(ParseError::Unaligned)
        );
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
    fn parse_with(&self, _: &'input [u8], _: Cursor, context: ParseContext) -> ParseOutcome<u64> {
        self.calls.set(self.calls.get() + 1);
        assert_eq!(context, self.expected_context);
        match self.answer {
            Answer::Success(next) => ParseOutcome::Success(next, 42),
            Answer::Error(error) => ParseOutcome::Error(error),
            Answer::NeedMore => ParseOutcome::NeedMore,
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
                            parser: Scripted {
                                calls: &calls,
                                expected_context: ctx(selected, status),
                                answer,
                            },
                        };
                        assert_eq!(
                            parser.parse_with(&[0], cursor, ctx(ambient, status)),
                            ParseOutcome::Error(error)
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
        (Answer::Success(START), ParseOutcome::Success(START, 42)),
        (
            Answer::Success(Cursor { byte: 1, bit: 0 }),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, 42),
        ),
        (
            Answer::Success(Cursor { byte: 0, bit: 3 }),
            ParseOutcome::Error(ParseError::Unaligned),
        ),
        (
            Answer::Success(Cursor { byte: 0, bit: 8 }),
            ParseOutcome::Error(ParseError::InvalidCursor),
        ),
        (
            Answer::Success(Cursor { byte: 1, bit: 1 }),
            ParseOutcome::Error(ParseError::InvalidCursor),
        ),
        (
            Answer::Success(Cursor { byte: 2, bit: 0 }),
            ParseOutcome::Error(ParseError::InvalidCursor),
        ),
        (Answer::NeedMore, ParseOutcome::NeedMore),
        (
            Answer::Error(ParseError::UnexpectedEnd),
            ParseOutcome::Error(ParseError::UnexpectedEnd),
        ),
        (
            Answer::Error(ParseError::Mismatch),
            ParseOutcome::Error(ParseError::Mismatch),
        ),
        (
            Answer::Error(ParseError::TrailingInput),
            ParseOutcome::Error(ParseError::TrailingInput),
        ),
        (
            Answer::Error(ParseError::InvalidCursor),
            ParseOutcome::Error(ParseError::InvalidCursor),
        ),
        (
            Answer::Error(ParseError::Unaligned),
            ParseOutcome::Error(ParseError::Unaligned),
        ),
        (
            Answer::Error(ParseError::NonProgress),
            ParseOutcome::Error(ParseError::NonProgress),
        ),
        (
            Answer::Error(ParseError::CountOverflow),
            ParseOutcome::Error(ParseError::CountOverflow),
        ),
    ];
    for status in [InputStatus::Partial, InputStatus::Final] {
        for (answer, expected) in &cases {
            let calls = Cell::new(0);
            let parser = WithOrder {
                order: order(0),
                parser: Scripted {
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
                    parser: Scripted {
                        calls: &calls,
                        expected_context: ctx(selected, status),
                        answer: Answer::Success(end),
                    },
                };
                assert_eq!(
                    parser.parse_with(&[0], start, ctx(ambient, status)),
                    ParseOutcome::Success(end, 42)
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
        parser: seq(
            field(3),
            WithOrder {
                order: order(0),
                parser: field(5),
            },
        ),
    };
    assert_eq!(
        parser.parse_with(&[0xd6], START, ctx(3, InputStatus::Final)),
        ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, (6, 26))
    );
    for ambient in 0..4 {
        for bit in 0..8 {
            let cursor = Cursor { byte: 0, bit };
            let parser = WithOrder {
                order: order(ambient ^ 1),
                parser: field(10),
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
        Some(ParseOutcome::Success(
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
            Some(ParseOutcome::NeedMore)
        );
        assert_eq!(
            nested(
                &data[..length],
                [16; 5],
                order(0),
                order(3),
                ctx(3, InputStatus::Final)
            ),
            Some(ParseOutcome::Error(ParseError::UnexpectedEnd))
        );
    }
    // A successful 3-bit child is a scope violation even on partial input.
    for status in [InputStatus::Final, InputStatus::Partial] {
        assert_eq!(
            WithOrder {
                order: order(0),
                parser: field(3)
            }
            .parse_with(&[0xff], START, ctx(3, status)),
            ParseOutcome::Error(ParseError::Unaligned)
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
                parser: and(field(3))
            }
            .parse_with(&[0xff], START, context),
            ParseOutcome::Success(START, ())
        );
        assert_eq!(
            and(WithOrder {
                order: low,
                parser: field(3)
            })
            .parse_with(&[0xff], START, context),
            ParseOutcome::Error(ParseError::Unaligned)
        );
        assert_eq!(
            not(WithOrder {
                order: low,
                parser: field(3)
            })
            .parse_with(&[0xff], START, context),
            ParseOutcome::Error(ParseError::Unaligned)
        );
        assert_eq!(
            WithOrder {
                order: low,
                parser: not(field(3))
            }
            .parse_with(&[0xff], START, context),
            ParseOutcome::Error(ParseError::Mismatch)
        );
        assert_eq!(
            lookahead(&[0xff], context),
            ParseOutcome::Error(ParseError::Unaligned)
        );
    }
    assert_eq!(
        lookahead(&[], ctx(3, InputStatus::Partial)),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        lookahead(&[], ctx(3, InputStatus::Final)),
        ParseOutcome::Error(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        WithOrder {
            order: low,
            parser: not(field(3))
        }
        .parse_with(&[], START, ctx(3, InputStatus::Final)),
        ParseOutcome::Success(START, ())
    );
    assert_eq!(
        WithOrder {
            order: low,
            parser: field(0)
        }
        .parse_with(&[], START, ctx(3, InputStatus::Final)),
        ParseOutcome::Success(START, 0)
    );
    assert_eq!(
        WithOrder {
            order: low,
            parser: field(0)
        }
        .parse_with(&[0], Cursor { byte: 0, bit: 1 }, ctx(3, InputStatus::Final)),
        ParseOutcome::Error(ParseError::Unaligned)
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
        fn parse_with(
            &self,
            _: &'input [u8],
            _: Cursor,
            _: ParseContext,
        ) -> ParseOutcome<Owned<'a>> {
            ParseOutcome::Success(self.next, Owned(self.drops))
        }
    }
    for next in [Cursor { byte: 0, bit: 3 }, Cursor { byte: 2, bit: 0 }] {
        let drops = Cell::new(0);
        let parser = WithOrder {
            order: order(0),
            parser: Produce {
                drops: &drops,
                next,
            },
        };
        assert!(matches!(
            parser.parse_with(&[0], START, ctx(3, InputStatus::Final)),
            ParseOutcome::Error(_)
        ));
        assert_eq!(drops.get(), 1);
    }
    let drops = Cell::new(0);
    let parser = WithOrder {
        order: order(0),
        parser: Produce {
            drops: &drops,
            next: START,
        },
    };
    let result = parser.parse_with(&[0], START, ctx(3, InputStatus::Final));
    assert_eq!(drops.get(), 0);
    drop(result);
    assert_eq!(drops.get(), 1);
}

fn seq<P, Q>(first: P, second: Q) -> Seq<P, Q> {
    Seq { first, second }
}
fn and<P>(parser: P) -> And<P> {
    And { parser }
}
fn not<P>(parser: P) -> Not<P> {
    Not { parser }
}

fn nested(
    input: &[u8],
    widths: [u8; 5],
    outer: Order,
    inner: Order,
    context: ParseContext,
) -> Option<ParseOutcome<(u64, (u64, (u64, u64)), u64)>> {
    let [a, b, c, d, e] = widths.map(field);
    let parser = seq(
        a,
        seq(
            WithOrder {
                order: outer,
                parser: seq(
                    b,
                    seq(
                        WithOrder {
                            order: inner,
                            parser: c,
                        },
                        d,
                    ),
                ),
            },
            e,
        ),
    );
    Some(match parser.parse_with(input, START, context) {
        ParseOutcome::Success(next, (a, (middle, e))) => {
            ParseOutcome::Success(next, (a, middle, e))
        }
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    })
}

fn lookahead(input: &[u8], context: ParseContext) -> ParseOutcome<((), ())> {
    let order = order(1);
    seq(
        WithOrder {
            order,
            parser: and(field(3)),
        },
        not(WithOrder {
            order,
            parser: field(3),
        }),
    )
    .parse_with(input, START, context)
}
