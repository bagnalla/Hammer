use rusthammer::*;

fn ctx(flags: u8) -> ByteOrder {
    if flags & 1 != 0 {
        ByteOrder::Big
    } else {
        ByteOrder::Little
    }
}
fn field(width: u8) -> Bits {
    Bits::new(width).unwrap()
}

// Independent numeric oracle: select physical bit positions, then concatenate
// boolean fragments in significance order. No shift/mask decoder is reused.
fn oracle(
    input: &[u8],
    cursor: Cursor,
    width: u8,
    byte_order: ByteOrder,
) -> Result<(Cursor, u64), ParseError> {
    let position = 8 * cursor.byte as u128 + cursor.bit as u128;
    if cursor.bit >= 8 || position > 8 * input.len() as u128 {
        return Err(ParseError::InvalidCursor);
    }
    if position + width as u128 > 8 * input.len() as u128 {
        return Err(ParseError::UnexpectedEnd);
    }
    let mut fragments = Vec::new();
    let mut offset = position as usize;
    let finish = offset + width as usize;
    while offset < finish {
        let end = finish.min((offset / 8 + 1) * 8);
        let mut positions: Vec<usize> = (offset..end).map(|p| 7 - p % 8).collect();
        positions.sort_by(|a, b| b.cmp(a));
        fragments.push(
            positions
                .into_iter()
                .map(|b| input[offset / 8] & (1 << b) != 0)
                .collect::<Vec<_>>(),
        );
        offset = end;
    }
    if byte_order == ByteOrder::Little {
        fragments.reverse();
    }
    let value = fragments
        .into_iter()
        .flatten()
        .fold(0, |n, b| n * 2 + u64::from(b));
    Ok((
        Cursor {
            byte: finish / 8,
            bit: (finish % 8) as u8,
        },
        value,
    ))
}

#[test]
fn field_values_widths_and_both_finalities() {
    let data = [0xd6, 0xab, 0x61, 0x82, 0x17, 0xff, 0x00, 0x5b, 0xc9];
    for length in 0..=data.len() {
        for byte in [0, 1, length, usize::MAX] {
            for bit in 0..=8 {
                let cursor = Cursor { byte, bit };
                for width in 0..=64 {
                    for flags in 2..4 {
                        {
                            let byte_order = ctx(flags);
                            assert_eq!(
                                field(width).parse_with(&data[..length], cursor, byte_order),
                                oracle(&data[..length], cursor, width, byte_order)
                            );
                        }
                    }
                }
            }
        }
    }
}

fn converted<T>(
    value: Result<(Cursor, u64), ParseError>,
    f: impl FnOnce(u64) -> T,
) -> Result<(Cursor, T), ParseError> {
    match value {
        Ok(parsed) => {
            let (next, value) = parsed;
            Ok((next, f(value)))
        }
        Err(error) => Err(error),
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
    for flags in 2..4 {
        {
            let byte_order = ctx(flags);
            let big = ByteOrder::Big;
            for bit in 0..8 {
                let start = Cursor { byte: 0, bit };
                for length in 0..=input.len() {
                    let data = &input[..length];
                    for width in 0..=64 {
                        let expected = oracle(data, start, width, byte_order);
                        assert_eq!(
                            SignedBits::new(width)
                                .unwrap()
                                .parse_with(data, start, byte_order),
                            converted(expected, |v| signed(v, width))
                        );
                    }
                    macro_rules! unsigned_reader {
                        ($parser:expr, $width:expr, $ty:ty, $byte_order:expr) => {
                            assert_eq!(
                                $parser.parse_with(data, start, byte_order),
                                converted(oracle(data, start, $width, $byte_order), |v| v as $ty)
                            );
                        };
                    }
                    macro_rules! signed_reader {
                        ($parser:expr, $width:expr, $ty:ty, $byte_order:expr) => {
                            assert_eq!(
                                $parser.parse_with(data, start, byte_order),
                                converted(oracle(data, start, $width, $byte_order), |v| signed(
                                    v, $width
                                )
                                    as $ty)
                            );
                        };
                    }
                    unsigned_reader!(Byte, 8, u8, byte_order);
                    unsigned_reader!(BeU16, 16, u16, big);
                    unsigned_reader!(BeU32, 32, u32, big);
                    unsigned_reader!(BeU64, 64, u64, big);
                    signed_reader!(I8, 8, i8, byte_order);
                    signed_reader!(BeI16, 16, i16, big);
                    signed_reader!(BeI32, 32, i32, big);
                    signed_reader!(BeI64, 64, i64, big);
                    assert_eq!(
                        Bit.parse_with(data, start, byte_order),
                        converted(oracle(data, start, 1, byte_order), |v| v != 0)
                    );
                }
                let Ok((next, value)) = oracle(&input, start, 8, byte_order) else {
                    unreachable!()
                };
                let value = value as u8;
                assert_eq!(
                    Literal::new(8, u64::from(value))
                        .unwrap()
                        .parse_with(&input, start, byte_order),
                    Ok((next, u64::from(value)))
                );
                assert_eq!(
                    Literal::new(8, u64::from(value ^ 1))
                        .unwrap()
                        .parse_with(&input, start, byte_order),
                    Err(ParseError::Mismatch)
                );
                assert_eq!(
                    ByteIn::new(&[value]).parse_with(&input, start, byte_order),
                    Ok((next, value))
                );
                assert_eq!(
                    ByteNotIn::new(&[value]).parse_with(&input, start, byte_order),
                    Err(ParseError::Mismatch)
                );
                let Ok((end, second)) = oracle(&input, next, 8, byte_order) else {
                    unreachable!()
                };
                let pattern = [value, second as u8];
                let Ok((actual_end, matched)) =
                    BytePattern::new(&pattern).parse_with(&input, start, byte_order)
                else {
                    panic!("contextual pattern did not match")
                };
                assert_eq!(actual_end, end);
                assert!(core::ptr::eq(matched, &pattern[..]));
                assert_eq!(
                    SkipBits::new(8).parse_with(&input, start, byte_order),
                    Ok((next, ()))
                );
                assert_eq!(
                    Tell.parse_with(&input, start, byte_order),
                    Ok((start, start))
                );
            }
        }
    }
}

#[test]
fn byte_order_scopes_allow_unaligned_fields_and_restore_the_enclosing_order() {
    use rusthammer::{seq, WithByteOrder};
    let input = [0xd6, 0xab, 0x61, 0x82];
    for byte in [ByteOrder::Big, ByteOrder::Little] {
        for bit in 0..8 {
            let start = Cursor { byte: 0, bit };
            let parser = seq(
                WithByteOrder {
                    parser: field(10),
                    byte_order: byte,
                },
                field(8),
            );
            let (middle, first) = oracle(&input, start, 10, byte).unwrap();
            let (end, second) = oracle(&input, middle, 8, ByteOrder::Big).unwrap();
            assert_eq!(parser.parse(&input, start), Ok((end, (first, second))));
        }
    }
}

#[test]
fn byte_order_scope_delegates_validation_and_preserves_custom_errors() {
    use rusthammer::WithByteOrder;
    struct Child(Result<(Cursor, u8), ParseError>);
    impl<'input> Parser<'input> for Child {
        type Output = u8;
        fn parse_with(
            &self,
            _: &'input [u8],
            _: Cursor,
            byte_order: ByteOrder,
        ) -> Result<(Cursor, u8), ParseError> {
            assert_eq!(byte_order, ByteOrder::Little);
            self.0
        }
    }
    let invalid = Cursor {
        byte: usize::MAX,
        bit: 255,
    };
    // Deliberately invalid custom output: the scope adds no validation of its own.
    for outcome in [
        Ok((invalid, 42)),
        Err(ParseError::Mismatch),
        Err(ParseError::InvalidCursor),
        Err(ParseError::UnexpectedEnd),
    ] {
        assert_eq!(
            WithByteOrder {
                parser: Child(outcome),
                byte_order: ByteOrder::Little
            }
            .parse(&[], invalid),
            outcome
        );
    }
}
