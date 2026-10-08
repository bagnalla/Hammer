use rusthammer::{
    permutation, required, And, BitOrder, ButNot, Byte, ByteOrder, Choice, Cursor, Difference,
    FoldRepeat, FoldSepBy, InputStatus, Literal, Not, Optional, Order, ParseContext, ParseError,
    ParseOutcome, Parser, Recognize, Right, Seq, SkipBits, WithOrder, WithSpan,
};
use rusthammer_seek_probe::{seek_position, Seek, SeekConfigError};

fn cursor(bits: usize) -> Cursor {
    Cursor {
        byte: bits / 8,
        bit: (bits % 8) as u8,
    }
}

fn absolute(bits: usize) -> Seek {
    Seek::to(cursor(bits)).unwrap()
}

fn oracle(
    length: usize,
    start: Cursor,
    target: i128,
    status: InputStatus,
    end: bool,
) -> ParseOutcome<Cursor> {
    let limit = length as i128 * 8;
    if start.bit >= 8 || start.byte as i128 * 8 + i128::from(start.bit) > limit {
        ParseOutcome::Error(ParseError::InvalidCursor)
    } else if end && status == InputStatus::Partial {
        ParseOutcome::NeedMore
    } else if target < 0 {
        ParseOutcome::Error(ParseError::Mismatch)
    } else if target > limit {
        match status {
            InputStatus::Partial => ParseOutcome::NeedMore,
            InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
        }
    } else {
        let next = Cursor {
            byte: (target / 8) as usize,
            bit: (target % 8) as u8,
        };
        ParseOutcome::Success(next, next)
    }
}

#[test]
fn exhaustive_small_positions_and_offsets() {
    for length in 0..=8 {
        for byte in 0..=length + 1 {
            for bit in 0..=9 {
                let start = Cursor { byte, bit };
                for status in [InputStatus::Partial, InputStatus::Final] {
                    for offset in -80..=80 {
                        for end in [false, true] {
                            let parser = if end {
                                Seek::from_end(offset)
                            } else {
                                Seek::relative(offset)
                            };
                            let base = if end {
                                length as i128 * 8
                            } else {
                                byte as i128 * 8 + i128::from(bit)
                            };
                            assert_eq!(
                                seek_position(parser, length, start, status),
                                oracle(length, start, base + offset as i128, status, end)
                            );
                        }
                    }
                    for target in 0..=8 * length + 9 {
                        assert_eq!(
                            seek_position(absolute(target), length, start, status),
                            oracle(length, start, target as i128, status, false)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn machine_boundaries_use_virtual_lengths() {
    assert!(
        usize::BITS <= 64,
        "the independent i128 oracle assumes at most 64-bit usize"
    );
    let max = usize::MAX;
    let points = [0, 1, max / 8, max / 8 + 1, max / 2, max - 1, max];
    for length in points {
        for byte in points {
            for bit in [0, 1, 7, 8, u8::MAX] {
                let start = Cursor { byte, bit };
                for status in [InputStatus::Partial, InputStatus::Final] {
                    for offset in [
                        isize::MIN,
                        isize::MIN + 1,
                        -9,
                        -8,
                        -1,
                        0,
                        1,
                        7,
                        8,
                        isize::MAX,
                    ] {
                        for end in [false, true] {
                            let parser = if end {
                                Seek::from_end(offset)
                            } else {
                                Seek::relative(offset)
                            };
                            let base = if end {
                                length as i128 * 8
                            } else {
                                byte as i128 * 8 + i128::from(bit)
                            };
                            assert_eq!(
                                seek_position(parser, length, start, status),
                                oracle(length, start, base + offset as i128, status, end)
                            );
                        }
                    }
                    for target_byte in points {
                        for target_bit in [0, 1, 7] {
                            let target = Cursor {
                                byte: target_byte,
                                bit: target_bit,
                            };
                            assert_eq!(
                                seek_position(Seek::to(target).unwrap(), length, start, status),
                                oracle(
                                    length,
                                    start,
                                    target_byte as i128 * 8 + i128::from(target_bit),
                                    status,
                                    false
                                )
                            );
                        }
                    }
                }
            }
        }
    }
    for bit in 8..=u8::MAX {
        assert!(matches!(
            Seek::to(Cursor { byte: 0, bit }),
            Err(SeekConfigError::InvalidBitOffset)
        ));
    }
}

#[test]
fn backtracking_and_lookahead_restore_entry_cursors() {
    let input = [b'a', b'b', b'c'];
    let fail_after_seek = Right {
        first: absolute(16),
        second: Literal::new(8, b'x' as u64).unwrap(),
    };
    let fallback = Literal::new(8, b'a' as u64).unwrap();
    assert_eq!(
        Choice {
            first: fail_after_seek,
            second: fallback
        }
        .parse(&input, cursor(0)),
        Ok((cursor(8), b'a' as u64))
    );
    assert_eq!(
        Optional {
            parser: fail_after_seek
        }
        .parse(&input, cursor(0)),
        Ok((cursor(0), None))
    );
    assert_eq!(
        And {
            parser: absolute(0)
        }
        .parse(&input, cursor(16)),
        Ok((cursor(16), ()))
    );
    assert_eq!(
        Not {
            parser: absolute(32)
        }
        .parse(&input, cursor(8)),
        Ok((cursor(8), ()))
    );
    assert_eq!(
        Optional {
            parser: Seek::relative(-9)
        }
        .parse(&input, cursor(8)),
        Ok((cursor(8), None))
    );
    assert_eq!(
        Optional {
            parser: absolute(32)
        }
        .parse_with(&input, cursor(8), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}

#[test]
fn spans_measure_endpoints_including_skips_but_not_excursions() {
    let input = [10, 20, 30, 40];
    let skip_read = WithSpan {
        parser: Right {
            first: absolute(16),
            second: Byte,
        },
    };
    let (next, (value, span)) = skip_read.parse(&input, cursor(0)).unwrap();
    assert_eq!(
        (next, value, span.as_bytes()),
        (cursor(24), 30, Some(&input[..3]))
    );
    let excursion = WithSpan {
        parser: Seq {
            first: Right {
                first: absolute(24),
                second: Byte,
            },
            second: absolute(8),
        },
    };
    let (next, ((value, _), span)) = excursion.parse(&input, cursor(0)).unwrap();
    assert_eq!(
        (next, value, span.as_bytes()),
        (cursor(8), 40, Some(&input[..1]))
    );
    let round_trip = Recognize {
        parser: Seq {
            first: absolute(24),
            second: absolute(8),
        },
    };
    assert!(round_trip.parse(&input, cursor(8)).unwrap().1.is_empty());
    assert_eq!(
        Recognize {
            parser: absolute(0)
        }
        .parse(&input, cursor(8)),
        Err(ParseError::NonProgress)
    );
}

#[test]
fn repetition_checks_net_progress_and_finite_repetition_can_move_backward() {
    let input = [1, 2, 3];
    let bounded = FoldRepeat::exact(Seek::relative(-8), 2, || 0, |n, _| n + 1);
    assert_eq!(bounded.parse(&input, cursor(24)), Ok((cursor(8), 2)));
    let unbounded = FoldRepeat::at_least(Seek::relative(-8), 0, || 0, |n, _| n + 1);
    assert_eq!(
        unbounded.parse(&input, cursor(24)),
        Err(ParseError::NonProgress)
    );
    let zero = FoldRepeat::at_least(Seek::relative(0), 0, || 0, |n, _| n + 1);
    assert_eq!(zero.parse(&input, cursor(0)), Err(ParseError::NonProgress));
    let advance = Seq {
        first: Seek::relative(-8),
        second: SkipBits::new(16),
    };
    let looped = FoldRepeat::at_least(advance, 0, || 0, |n, _| n + 1);
    assert_eq!(looped.parse(&input, cursor(8)), Ok((cursor(24), 2)));
    assert_eq!(
        looped.parse_with(&input, cursor(8), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    let separated =
        FoldSepBy::at_least(SkipBits::new(16), Seek::relative(-8), 0, || 0, |n, _| n + 1);
    assert_eq!(separated.parse(&input, cursor(0)), Ok((cursor(24), 2)));
}

#[test]
fn restrictions_compare_destinations_even_when_both_are_backward() {
    let input = [0, 0];
    assert_eq!(
        ButNot {
            first: absolute(8),
            second: absolute(0)
        }
        .parse(&input, cursor(16)),
        Ok((cursor(8), cursor(8)))
    );
    assert_eq!(
        Difference {
            first: absolute(0),
            second: absolute(8)
        }
        .parse(&input, cursor(16)),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        Difference {
            first: absolute(0),
            second: absolute(0)
        }
        .parse(&input, cursor(16)),
        Ok((cursor(0), cursor(0)))
    );
}

#[test]
fn finite_permutation_does_not_require_input_progress() {
    let parser = permutation((required(absolute(0)), required(Byte)));
    assert_eq!(
        parser.parse(&[42], cursor(8)),
        Ok((cursor(8), (cursor(0), 42)))
    );
}

#[test]
fn seeks_preserve_order_and_changed_direction_scope_guards() {
    for bit in [BitOrder::HighFirst, BitOrder::LowFirst] {
        for byte in [ByteOrder::Big, ByteOrder::Little] {
            for status in [InputStatus::Partial, InputStatus::Final] {
                let context = ParseContext {
                    order: Order { bit, byte },
                    status,
                };
                assert_eq!(
                    absolute(3).parse_with(&[0x96, 0x52], cursor(8), context),
                    ParseOutcome::Success(cursor(3), cursor(3))
                );
                let seek_read = Right {
                    first: absolute(3),
                    second: Byte,
                };
                assert_eq!(
                    seek_read.parse_with(&[0x96, 0x52], cursor(8), context),
                    Byte.parse_with(&[0x96, 0x52], cursor(3), context)
                );
            }
        }
    }
    let low = Order {
        bit: BitOrder::LowFirst,
        byte: ByteOrder::Big,
    };
    assert_eq!(
        WithOrder {
            order: low,
            parser: absolute(3)
        }
        .parse(&[0], cursor(0)),
        Err(ParseError::Unaligned)
    );
    assert_eq!(
        WithOrder {
            order: low,
            parser: absolute(0)
        }
        .parse(&[0], cursor(8)),
        Ok((cursor(0), cursor(0)))
    );
}

#[test]
fn retries_keep_absolute_targets_and_end_seeks_wait_for_finality() {
    for length in 0..4 {
        let input = [0; 4];
        assert_eq!(
            absolute(24).parse_with(&input[..length], cursor(0), ParseContext::PARTIAL),
            if length < 3 {
                ParseOutcome::NeedMore
            } else {
                ParseOutcome::Success(cursor(24), cursor(24))
            }
        );
        for offset in [isize::MIN, -8, 0, 1, isize::MAX] {
            assert_eq!(
                Seek::from_end(offset).parse_with(
                    &input[..length],
                    cursor(0),
                    ParseContext::PARTIAL
                ),
                ParseOutcome::NeedMore
            );
        }
    }
    assert_eq!(
        Seek::from_end(-8).parse(&[1, 2, 3], cursor(0)),
        Ok((cursor(16), cursor(16)))
    );
    assert_eq!(
        Seek::relative(1).parse(&[], cursor(0)),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        Seek::from_end(0).parse_with(&[], Cursor { byte: 0, bit: 1 }, ParseContext::PARTIAL),
        ParseOutcome::Error(ParseError::InvalidCursor)
    );
}
