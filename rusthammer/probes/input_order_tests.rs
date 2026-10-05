use super::*;

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

fn context(flags: u8, status: InputStatus) -> Context {
    Context {
        order: order(flags),
        status,
    }
}

// Independent value oracle: collect the actual bit positions of each physical
// fragment and fold individual booleans, rather than shifting/masking bytes.
fn oracle(input: &[u8], mut cursor: Cursor, width: u8, ctx: Context) -> Outcome<u64> {
    if !cursor.valid(input.len()) {
        return Outcome::Error(Error::InvalidCursor);
    }
    let mut fragments = std::vec::Vec::new();
    let mut left = width;
    while left != 0 {
        if cursor.byte == input.len() {
            return shortage(ctx.status);
        }
        let positions: std::vec::Vec<u8> = (cursor.low..8 - cursor.high).collect();
        let count = (left as usize).min(positions.len());
        let selected = match ctx.order.bit {
            BitOrder::HighFirst => &positions[positions.len() - count..],
            BitOrder::LowFirst => &positions[..count],
        };
        let bits: std::vec::Vec<bool> = selected
            .iter()
            .rev()
            .map(|bit| input[cursor.byte] & (1 << bit) != 0)
            .collect();
        fragments.push(bits);
        if count == positions.len() {
            cursor = Cursor {
                byte: cursor.byte + 1,
                high: 0,
                low: 0,
            };
        } else {
            match ctx.order.bit {
                BitOrder::HighFirst => cursor.high += count as u8,
                BitOrder::LowFirst => cursor.low += count as u8,
            }
        }
        left -= count as u8;
    }
    if ctx.order.byte == ByteOrder::Little {
        fragments.reverse();
    }
    let value = fragments
        .into_iter()
        .flatten()
        .fold(0, |value, bit| value * 2 + u64::from(bit));
    Outcome::Success(cursor, value)
}

#[test]
fn all_single_byte_values_and_geometries() {
    for value in 0..=255 {
        for high in 0..8 {
            for low in 0..8 - high {
                let cursor = Cursor::new(0, high, low).unwrap();
                for width in 0..=9 {
                    for flags in 0..4 {
                        for status in [InputStatus::Final, InputStatus::Partial] {
                            let ctx = context(flags, status);
                            assert_eq!(
                                Field::new(width).unwrap().parse_with(&[value], cursor, ctx),
                                oracle(&[value], cursor, width, ctx)
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn all_widths_and_truncations() {
    let input = [0xd6, 0xab, 0x61, 0x82, 0x17, 0xff, 0x00, 0x5b, 0xc9];
    for length in 0..=input.len() {
        for byte in 0..=length {
            for high in 0..8 {
                for low in 0..8 - high {
                    let cursor = Cursor::new(byte, high, low).unwrap();
                    for width in 0..=64 {
                        for flags in 0..4 {
                            for status in [InputStatus::Final, InputStatus::Partial] {
                                let ctx = context(flags, status);
                                let expected = oracle(&input[..length], cursor, width, ctx);
                                let skipped = match &expected {
                                    Outcome::Success(end, _) => Outcome::Success(*end, ()),
                                    Outcome::Error(Error::InvalidCursor) => {
                                        Outcome::Error(Error::InvalidCursor)
                                    }
                                    Outcome::Error(Error::UnexpectedEnd) => {
                                        Outcome::Error(Error::UnexpectedEnd)
                                    }
                                    Outcome::NeedMore => Outcome::NeedMore,
                                    _ => unreachable!(),
                                };
                                assert_eq!(
                                    Field::new(width).unwrap().parse_with(
                                        &input[..length],
                                        cursor,
                                        ctx
                                    ),
                                    expected
                                );
                                assert_eq!(
                                    skip_bits(&input[..length], cursor, width as usize, ctx),
                                    skipped
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn constructors_and_machine_boundaries() {
    for high in 0..=255u8 {
        for low in 0..=255u8 {
            assert_eq!(
                Cursor::new(usize::MAX, high, low).is_some(),
                (high as u16) + (low as u16) < 8
            );
        }
    }
    for width in 0..=255u8 {
        assert_eq!(Field::new(width).is_some(), width <= 64);
    }
    for flags in 0..4 {
        let ctx = context(flags, InputStatus::Final);
        assert_eq!(
            skip_bits(&[0], Cursor::new(0, 3, 2).unwrap(), usize::MAX, ctx),
            Outcome::Error(Error::UnexpectedEnd)
        );
        let last = Cursor::new(usize::MAX - 1, 3, 2).unwrap();
        let end = advance_segment(last, 3, ctx.order.bit);
        assert_eq!(end.parts(), (usize::MAX, 0, 0));
        assert!(end.valid(usize::MAX));
        assert_eq!(
            Field::new(0)
                .unwrap()
                .parse_with(&[], Cursor::new(usize::MAX, 0, 0).unwrap(), ctx),
            Outcome::Error(Error::InvalidCursor)
        );
    }
}

#[test]
fn nested_scopes_restore_both_axes_and_borrow_the_input() {
    let input = [0xd6, 0xab];
    let result = nested(
        &input,
        [3, 2, 3, 4, 4],
        order(1),
        order(3),
        context(3, InputStatus::Final),
    );
    match result.unwrap() {
        Outcome::Success(end, ((a, (b, (c, d)), e), span)) => {
            assert_eq!((a, b, c, d, e), (6, 2, 5, 11, 10));
            assert_eq!(end.parts(), (2, 0, 0));
            assert_eq!(span.start.parts(), (0, 0, 0));
            assert_eq!(span.end, end);
            assert!(core::ptr::eq(span.input.as_ptr(), input.as_ptr()));
        }
        other => panic!("unexpected {other:?}"),
    }
    for status in [InputStatus::Final, InputStatus::Partial] {
        assert_eq!(
            nested(
                &input[..1],
                [3, 2, 3, 4, 4],
                order(1),
                order(3),
                context(3, status)
            ),
            Some(shortage(status))
        );
    }
    let bytes = [0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x11, 0x22];
    match nested(
        &bytes,
        [16; 5],
        order(2),
        order(3),
        context(3, InputStatus::Final),
    )
    .unwrap()
    {
        Outcome::Success(end, ((a, (b, (c, d)), e), _)) => {
            assert_eq!((a, b, c, d, e), (0x1234, 0x7856, 0x9abc, 0xf0de, 0x1122));
            assert_eq!(end.parts(), (10, 0, 0));
        }
        other => panic!("unexpected {other:?}"),
    }
}

#[test]
fn fragment_significance_is_not_bit_reversal() {
    let cursor = Cursor::new(0, 0, 0).unwrap();
    for flags in 0..4 {
        let ctx = context(flags, InputStatus::Final);
        assert_eq!(
            Field::new(8).unwrap().parse_with(&[0x61], cursor, ctx),
            Outcome::Success(Cursor::new(1, 0, 0).unwrap(), 0x61)
        );
    }
    let parsed = Seq(Field::new(5).unwrap(), Field::new(3).unwrap()).parse_with(
        &[0x61],
        cursor,
        context(1, InputStatus::Final),
    );
    assert_eq!(
        parsed,
        Outcome::Success(Cursor::new(1, 0, 0).unwrap(), (1, 3))
    );
}

#[test]
fn spans_reject_reintroduced_bits_and_allow_empty_matches() {
    struct Jump(Cursor);
    impl<'a> Parser<'a> for Jump {
        type Output = ();
        fn parse_with(&self, _: &'a [u8], _: Cursor, _: Context) -> Outcome<()> {
            Outcome::Success(self.0, ())
        }
    }
    let start = Cursor::new(0, 3, 0).unwrap();
    let other = Cursor::new(0, 0, 4).unwrap(); // Larger rank, but reintroduces high bits.
    let ctx = context(3, InputStatus::Final);
    assert!(!forward(start, other));
    assert_eq!(
        WithSpan(Jump(other)).parse_with(&[0], start, ctx),
        Outcome::Error(Error::NonForward)
    );
    assert!(matches!(
        WithSpan(Jump(start)).parse_with(&[0], start, ctx),
        Outcome::Success(_, _)
    ));
    assert_eq!(
        WithSpan(Jump(Cursor::new(1, 1, 0).unwrap())).parse_with(&[0], start, ctx),
        Outcome::Error(Error::InvalidCursor)
    );
}
