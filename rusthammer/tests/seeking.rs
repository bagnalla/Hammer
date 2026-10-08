use rusthammer::{
    permutation, required, And, BitOrder, ButNot, Byte, ByteOrder, Choice, Cursor, Difference,
    FoldRepeat, FoldSepBy, InputStatus, Literal, Not, Optional, Order, ParseContext, ParseError,
    ParseOutcome, Parser, Recognize, Right, Seek, Seq, SkipBits, WithOrder, WithSpan,
};

fn cursor(bits: usize) -> Cursor {
    Cursor {
        byte: bits / 8,
        bit: (bits % 8) as u8,
    }
}

fn absolute(bits: usize) -> Seek {
    Seek::to(cursor(bits)).unwrap()
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

#[path = "../examples/support/offset.rs"]
mod offset;

#[test]
fn offset_example_matches_independent_byte_format_and_partial_retries() {
    for distance in 0..=255 {
        let mut input = vec![0; distance + 4];
        input[0] = distance as u8;
        input[distance + 1] = 0x12;
        input[distance + 2] = 0x34;
        for size in 0..=input.len() {
            let final_result = offset::payload(&input[..size], cursor(0), ParseContext::FINAL);
            let partial_result = offset::payload(&input[..size], cursor(0), ParseContext::PARTIAL);
            if size < distance + 3 {
                assert_eq!(final_result, ParseOutcome::Error(ParseError::UnexpectedEnd));
                assert_eq!(partial_result, ParseOutcome::NeedMore);
            } else {
                assert_eq!(
                    final_result,
                    ParseOutcome::Success(
                        cursor((distance + 3) * 8),
                        &input[distance + 1..distance + 3]
                    )
                );
                assert_eq!(partial_result, final_result);
                let ParseOutcome::Success(_, payload) = final_result else {
                    panic!("the complete offset field and payload must succeed")
                };
                assert!(core::ptr::eq(
                    payload.as_ptr(),
                    input[distance + 1..].as_ptr()
                ));
            }
        }
    }
}

#[cfg(feature = "alloc")]
#[test]
fn collected_backward_seeks_obey_finite_and_unbounded_progress_rules() {
    use rusthammer::Repeat;
    let seek = Seek::relative(-1);
    assert_eq!(
        Repeat::exact(&seek, 2).parse(&[0], cursor(8)),
        Ok((cursor(6), vec![cursor(7), cursor(6)]))
    );
    assert_eq!(
        Repeat::at_least(&seek, 0).parse(&[0], cursor(8)),
        Err(ParseError::NonProgress)
    );
}

#[test]
fn constructor_configuration_and_state_are_preserved() {
    use rusthammer::{ConfigError, Eval};
    assert_eq!(
        Seek::to(Cursor { byte: 0, bit: 8 }),
        Err(ConfigError::InvalidBitOffset)
    );
    let original = Seek::to(Cursor {
        byte: usize::MAX,
        bit: 7,
    })
    .unwrap();
    let copied = original;
    assert_eq!(copied, original.clone());
    let mut state = 42;
    assert_eq!(
        copied.eval(&mut state, &[0], cursor(0), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(state, 42);
    assert_eq!(
        Seek::relative(-1).eval(&mut state, &[0], cursor(0), ParseContext::FINAL),
        ParseOutcome::Error(ParseError::Mismatch)
    );
    assert_eq!(state, 42);
    assert_eq!(
        Seek::from_end(0).eval(&mut state, &[0], cursor(0), ParseContext::FINAL),
        ParseOutcome::Success(cursor(8), cursor(8))
    );
    assert_eq!(state, 42);
}
