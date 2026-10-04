#![cfg(feature = "alloc")]

use rusthammer::{
    And, Bits, Choice, ConfigError, Cursor, End, InputStatus, Literal, Map, Not, Optional,
    ParseError, ParseOutcome, Parser, Repeat, Seq, TakeAligned,
};
use std::cell::Cell;

struct MustNotRun;

impl<'input> Parser<'input> for MustNotRun {
    type Output = ();

    fn parse_with(&self, _: &'input [u8], _: Cursor, _: InputStatus) -> ParseOutcome<()> {
        panic!("zero repetitions must not invoke the child")
    }
}

#[test]
fn constructors_validate_inclusive_bounds_without_running_the_child() {
    for min in [0, 1, 2, usize::MAX - 1, usize::MAX] {
        let exact = Repeat::exact(MustNotRun, min);
        assert_eq!((exact.min(), exact.max()), (min, Some(min)));
        let unbounded = Repeat::at_least(MustNotRun, min);
        assert_eq!((unbounded.min(), unbounded.max()), (min, None));
        for max in [0, 1, 2, usize::MAX - 1, usize::MAX] {
            match Repeat::new(MustNotRun, min, max) {
                Ok(parser) => {
                    assert!(min <= max);
                    assert_eq!((parser.min(), parser.max()), (min, Some(max)));
                }
                Err(error) => {
                    assert!(min > max);
                    assert_eq!(error, ConfigError::InvalidBounds);
                }
            }
        }
    }
}

#[test]
fn bounded_numeric_repetition_matches_an_independent_bit_string_oracle() {
    let input = [0xa5, 0x13, 0xff];
    let bit_string: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    for start_bit in 0..=bit_string.len() {
        let start = Cursor {
            byte: start_bit / 8,
            bit: (start_bit % 8) as u8,
        };
        for width in 0..=13u8 {
            for min in 0..=4 {
                for max in min..=5 {
                    let parser = Repeat::new(Bits::new(width).unwrap(), min, max).unwrap();
                    let available = if width == 0 {
                        max
                    } else {
                        (bit_string.len() - start_bit) / usize::from(width)
                    };
                    let count = available.min(max);
                    let values: Vec<u64> = (0..count)
                        .map(|i| {
                            let lo = start_bit + i * usize::from(width);
                            if width == 0 {
                                0
                            } else {
                                u64::from_str_radix(&bit_string[lo..lo + usize::from(width)], 2)
                                    .unwrap()
                            }
                        })
                        .collect();
                    let end_bit = start_bit + usize::from(width) * count;
                    let next = Cursor {
                        byte: end_bit / 8,
                        bit: (end_bit % 8) as u8,
                    };
                    let final_result = if count < min {
                        Err(ParseError::UnexpectedEnd)
                    } else {
                        Ok((next, values.clone()))
                    };
                    assert_eq!(parser.parse(&input, start), final_result);
                    let partial = if count == max {
                        ParseOutcome::Success(next, values)
                    } else {
                        ParseOutcome::NeedMore
                    };
                    assert_eq!(
                        parser.parse_with(&input, start, InputStatus::Partial),
                        partial
                    );
                }
            }
        }
    }
}

#[test]
fn a_rejected_attempt_restores_its_starting_bit_cursor() {
    // At bit 1: 101, 100, then padding. The second child consumes its first
    // two bits before rejecting the last bit of that attempted three-bit group.
    let input = [0b0101_1000];
    let start = Cursor { byte: 0, bit: 1 };
    for min in [1, 2] {
        let parser = Repeat::new(
            Seq {
                first: Literal::new(2, 2).unwrap(),
                second: Literal::new(1, 1).unwrap(),
            },
            min,
            3,
        )
        .unwrap();
        for status in [InputStatus::Partial, InputStatus::Final] {
            let expected = if min == 1 {
                ParseOutcome::Success(Cursor { byte: 0, bit: 4 }, vec![(2, 1)])
            } else {
                ParseOutcome::Error(ParseError::Mismatch)
            };
            assert_eq!(parser.parse_with(&input, start, status), expected);
        }
    }
}

#[test]
fn reaching_the_maximum_does_not_attempt_another_child() {
    let calls = Cell::new(0);
    let parser = Repeat::new(
        Map {
            parser: Bits::new(0).unwrap(),
            map: |_| {
                calls.set(calls.get() + 1);
                assert!(calls.get() <= 2);
            },
        },
        0,
        2,
    )
    .unwrap();
    for status in [InputStatus::Partial, InputStatus::Final] {
        calls.set(0);
        assert_eq!(
            parser.parse_with(&[], Cursor::start(), status),
            ParseOutcome::Success(Cursor::start(), vec![(); 2])
        );
        assert_eq!(calls.get(), 2);
    }
}

#[test]
fn stopping_distinguishes_rejection_fatal_errors_and_incompleteness() {
    struct StopAfterTwo<'a> {
        calls: &'a Cell<usize>,
        error: Option<ParseError>,
    }
    impl<'input> Parser<'input> for StopAfterTwo<'_> {
        type Output = ();
        fn parse_with(&self, _: &'input [u8], cursor: Cursor, _: InputStatus) -> ParseOutcome<()> {
            self.calls.set(self.calls.get() + 1);
            match self.calls.get() {
                1 | 2 => ParseOutcome::Success(cursor, ()),
                3 => match self.error {
                    Some(error) => ParseOutcome::Error(error),
                    None => ParseOutcome::NeedMore,
                },
                _ => panic!("repetition must stop at the first non-success"),
            }
        }
    }
    for error in [
        Some(ParseError::Mismatch),
        Some(ParseError::UnexpectedEnd),
        Some(ParseError::TrailingInput),
        Some(ParseError::InvalidCursor),
        Some(ParseError::Unaligned),
        Some(ParseError::NonProgress),
        Some(ParseError::CountOverflow),
        None,
    ] {
        for min in [0, 2, 3] {
            let calls = Cell::new(0);
            let parser = Repeat::new(
                StopAfterTwo {
                    calls: &calls,
                    error,
                },
                min,
                4,
            )
            .unwrap();
            let expected = match error {
                Some(
                    ParseError::Mismatch | ParseError::UnexpectedEnd | ParseError::TrailingInput,
                ) if min <= 2 => ParseOutcome::Success(Cursor::start(), vec![(); 2]),
                Some(error) => ParseOutcome::Error(error),
                None => ParseOutcome::NeedMore,
            };
            assert_eq!(
                parser.parse_with(&[], Cursor::start(), InputStatus::Partial),
                expected
            );
            assert_eq!(calls.get(), 3);
        }
    }
}

#[test]
fn bounded_borrowed_outputs_are_kept_on_recoverable_stopping() {
    let input = [0xff, 1, 2, 3, 4, 5];
    let parser = Repeat::new(TakeAligned { count: 2 }, 1, 4).unwrap();
    let start = Cursor { byte: 1, bit: 0 };
    let (next, values) = parser.parse(&input, start).unwrap();
    assert_eq!(next, Cursor { byte: 5, bit: 0 });
    assert_eq!(values, [&input[1..3], &input[3..5]]);
    assert_eq!(values[0].as_ptr(), input[1..].as_ptr());
    assert_eq!(values[1].as_ptr(), input[3..].as_ptr());
    assert_eq!(
        parser.parse_with(&input, start, InputStatus::Partial),
        ParseOutcome::NeedMore
    );
}

#[test]
fn bounded_owned_values_survive_success_and_are_dropped_on_incompleteness() {
    struct Value<'a>(&'a Cell<usize>);
    impl Drop for Value<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Cell::new(0);
    let parser = Repeat::new(
        Map {
            parser: Bits::new(8).unwrap(),
            map: |_| Value(&drops),
        },
        1,
        4,
    )
    .unwrap();
    let (_, values) = parser.parse(&[1, 2], Cursor::start()).unwrap();
    assert_eq!(values.len(), 2);
    assert_eq!(drops.get(), 0);
    drop(values);
    assert_eq!(drops.get(), 2);
    assert!(matches!(
        parser.parse_with(&[1, 2], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    ));
    assert_eq!(drops.get(), 4);
}

#[test]
fn hammer_capped_repetition_regression_cases() {
    // tests/t_parser.c:test_many_cap and test_many1_cap, with typed values.
    for min in [0, 1] {
        for max in min..=2 {
            let parser = Repeat::new(
                Choice {
                    first: Literal::new(8, u64::from(b'a')).unwrap(),
                    second: Literal::new(8, u64::from(b'b')).unwrap(),
                },
                min,
                max,
            )
            .unwrap();
            for input in [b"".as_slice(), b"a", b"ab", b"aab", b"ac", b"c"] {
                let accepted = input
                    .iter()
                    .take_while(|&&b| b == b'a' || b == b'b')
                    .count();
                let count = accepted.min(max);
                let expected = if count >= min {
                    Ok((
                        Cursor {
                            byte: count,
                            bit: 0,
                        },
                        input[..count].iter().map(|&b| u64::from(b)).collect(),
                    ))
                } else if accepted == input.len() {
                    Err(ParseError::UnexpectedEnd)
                } else {
                    Err(ParseError::Mismatch)
                };
                assert_eq!(parser.parse(input, Cursor::start()), expected);
            }
        }
    }
}

#[test]
fn zero_repetitions_do_not_call_the_child_or_validate_the_cursor() {
    let parser = Repeat::exact(MustNotRun, 0);
    for cursor in [
        Cursor::start(),
        Cursor {
            byte: usize::MAX,
            bit: 255,
        },
    ] {
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                parser.parse_with(&[], cursor, status),
                ParseOutcome::Success(cursor, vec![])
            );
        }
        assert_eq!(parser.parse(&[], cursor), Ok((cursor, vec![])));
    }
}

#[test]
fn numeric_repetition_matches_an_independent_bit_string_oracle() {
    let input = [0xa5, 0x13, 0xff, 0x00, 0xe7];
    let bit_string: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    for start_bit in 0..=bit_string.len() {
        let start = Cursor {
            byte: start_bit / 8,
            bit: (start_bit % 8) as u8,
        };
        for width in 0..=13u8 {
            for count in 0..=7 {
                let parser = Repeat::exact(Bits::new(width).unwrap(), count);
                let end_bit = start_bit + usize::from(width) * count;
                if end_bit <= bit_string.len() {
                    let values: Vec<u64> = (0..count)
                        .map(|i| {
                            let lo = start_bit + i * usize::from(width);
                            if width == 0 {
                                0
                            } else {
                                u64::from_str_radix(&bit_string[lo..lo + usize::from(width)], 2)
                                    .unwrap()
                            }
                        })
                        .collect();
                    let next = Cursor {
                        byte: end_bit / 8,
                        bit: (end_bit % 8) as u8,
                    };
                    assert_eq!(parser.parse(&input, start), Ok((next, values.clone())));
                    assert_eq!(
                        parser.parse_with(&input, start, InputStatus::Partial),
                        ParseOutcome::Success(next, values)
                    );
                } else {
                    assert_eq!(parser.parse(&input, start), Err(ParseError::UnexpectedEnd));
                    assert_eq!(
                        parser.parse_with(&input, start, InputStatus::Partial),
                        ParseOutcome::NeedMore
                    );
                }
            }
        }
    }
}

#[test]
fn borrowed_values_preserve_order_boundaries_and_identity() {
    let input = [0xff, 1, 2, 3, 4, 5, 6, 0xee];
    let start = Cursor { byte: 1, bit: 0 };
    let parser = Repeat::exact(TakeAligned { count: 2 }, 3);
    let ParseOutcome::Success(next, values) =
        parser.parse_with(&input, start, InputStatus::Partial)
    else {
        panic!("expected borrowed prefix")
    };
    assert_eq!(next, Cursor { byte: 7, bit: 0 });
    assert_eq!(values.len(), 3);
    for (i, value) in values.iter().enumerate() {
        let expected = &input[1 + 2 * i..3 + 2 * i];
        assert_eq!(*value, expected);
        assert_eq!(value.as_ptr(), expected.as_ptr());
    }
}

#[test]
fn owned_values_are_moved_and_dropped_on_early_exit() {
    #[derive(Debug)]
    struct Value<'a> {
        value: u64,
        drops: &'a Cell<usize>,
    }
    impl Drop for Value<'_> {
        fn drop(&mut self) {
            self.drops.set(self.drops.get() + 1);
        }
    }
    let calls = Cell::new(0);
    let drops = Cell::new(0);
    let parser = Repeat::exact(
        Map {
            parser: Bits::new(8).unwrap(),
            map: |value| {
                calls.set(calls.get() + 1);
                Value {
                    value,
                    drops: &drops,
                }
            },
        },
        3,
    );
    for status in [InputStatus::Partial, InputStatus::Final] {
        let outcome = parser.parse_with(&[1, 2], Cursor::start(), status);
        match status {
            InputStatus::Partial => assert!(matches!(outcome, ParseOutcome::NeedMore)),
            InputStatus::Final => assert!(matches!(
                outcome,
                ParseOutcome::Error(ParseError::UnexpectedEnd)
            )),
        }
        assert_eq!(drops.get(), calls.get());
    }
    let (_, values) = parser.parse(&[1, 2, 3, 4], Cursor::start()).unwrap();
    assert_eq!(
        values.iter().map(|v| v.value).collect::<Vec<_>>(),
        [1, 2, 3]
    );
    assert_eq!(calls.get(), 7);
    assert_eq!(drops.get(), 4);
    drop(values);
    assert_eq!(drops.get(), 7);
}

#[test]
fn every_child_error_stops_repetition_and_is_preserved() {
    struct FailAfterTwo<'a> {
        calls: &'a Cell<usize>,
        error: ParseError,
    }
    impl<'input> Parser<'input> for FailAfterTwo<'_> {
        type Output = ();
        fn parse_with(&self, _: &'input [u8], cursor: Cursor, _: InputStatus) -> ParseOutcome<()> {
            self.calls.set(self.calls.get() + 1);
            match self.calls.get() {
                1 | 2 => ParseOutcome::Success(cursor, ()),
                3 => ParseOutcome::Error(self.error),
                _ => panic!("must stop at the first error"),
            }
        }
    }
    for error in [
        ParseError::Mismatch,
        ParseError::UnexpectedEnd,
        ParseError::TrailingInput,
        ParseError::InvalidCursor,
        ParseError::Unaligned,
        ParseError::NonProgress,
        ParseError::CountOverflow,
    ] {
        for status in [InputStatus::Partial, InputStatus::Final] {
            let calls = Cell::new(0);
            let parser = Repeat::exact(
                FailAfterTwo {
                    calls: &calls,
                    error,
                },
                5,
            );
            assert_eq!(
                parser.parse_with(&[], Cursor::start(), status),
                ParseOutcome::Error(error)
            );
            assert_eq!(calls.get(), 3);
        }
    }
}

#[test]
fn huge_counts_can_reject_before_allocating_for_the_count() {
    let parser = Repeat::exact(Bits::new(8).unwrap(), usize::MAX);
    for input in [&[][..], &[1][..]] {
        assert_eq!(
            parser.parse(input, Cursor::start()),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            parser.parse_with(input, Cursor::start(), InputStatus::Partial),
            ParseOutcome::NeedMore
        );
    }
}

#[test]
fn empty_success_is_bounded_and_preserves_every_output() {
    let calls = Cell::new(0);
    let parser = Repeat::exact(
        Map {
            parser: Bits::new(0).unwrap(),
            map: |_| {
                let value = calls.get();
                calls.set(value + 1);
                value
            },
        },
        17,
    );
    assert_eq!(
        parser.parse(&[], Cursor::start()),
        Ok((Cursor::start(), (0..17).collect()))
    );
    assert_eq!(calls.get(), 17);
    // Unit-valued children are retained too; C Hammer omits absent AST entries.
    let units = Repeat::exact(
        And {
            parser: Bits::new(0).unwrap(),
        },
        3,
    );
    assert_eq!(
        units.parse(&[], Cursor::start()),
        Ok((Cursor::start(), vec![(); 3]))
    );
}

#[test]
fn choice_and_optionality_retry_at_the_original_bit_cursor() {
    let first = Repeat::exact(Literal::new(3, 5).unwrap(), 2);
    let fallback = Repeat::exact(Bits::new(3).unwrap(), 1);
    let parser = Choice {
        first,
        second: fallback,
    };
    let input = [0b0001_0100, 0];
    let start = Cursor { byte: 0, bit: 3 };
    assert_eq!(
        parser.parse(&input, start),
        Ok((Cursor { byte: 0, bit: 6 }, vec![5]))
    );
    assert_eq!(
        parser.parse_with(&input[..1], start, InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse(&input[..1], start),
        Ok((Cursor { byte: 0, bit: 6 }, vec![5]))
    );
    let optional = Optional {
        parser: Repeat::exact(Literal::new(3, 5).unwrap(), 2),
    };
    assert_eq!(optional.parse(&input, start), Ok((start, None)));
    assert_eq!(
        optional.parse_with(&input[..1], start, InputStatus::Partial),
        ParseOutcome::NeedMore
    );
}

#[test]
fn repeated_end_and_lookahead_honor_finality() {
    let parser = Repeat::exact(End, 3);
    assert_eq!(
        parser.parse(&[], Cursor::start()),
        Ok((Cursor::start(), vec![(); 3]))
    );
    assert_eq!(
        parser.parse_with(&[], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    let negative = Not { parser };
    assert_eq!(
        negative.parse_with(&[], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        negative.parse(&[], Cursor::start()),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn completed_count_does_not_require_final_input_but_end_does() {
    let parser = Seq {
        first: Repeat::exact(Bits::new(8).unwrap(), 2),
        second: End,
    };
    assert_eq!(
        parser.parse_with(&[1, 2], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse(&[1, 2], Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, (vec![1, 2], ())))
    );
    assert_eq!(
        parser.parse(&[1, 2, 3], Cursor::start()),
        Err(ParseError::TrailingInput)
    );
}

#[test]
fn hammer_exact_count_regression_cases() {
    // Port tests/t_parser.c:test_repeat_n: repeat choice("a", "b") twice.
    let letters = Repeat::exact(
        Choice {
            first: Literal::new(8, u64::from(b'a')).unwrap(),
            second: Literal::new(8, u64::from(b'b')).unwrap(),
        },
        2,
    );
    assert_eq!(
        letters.parse(b"adef", Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        letters.parse(b"abdef", Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, vec![97, 98]))
    );
    assert_eq!(
        letters.parse(b"dabdef", Cursor::start()),
        Err(ParseError::Mismatch)
    );
    let parser = Repeat::exact(Literal::new(8, u64::from(b'a')).unwrap(), 3);
    assert_eq!(
        parser.parse(b"aaab", Cursor::start()),
        Ok((Cursor { byte: 3, bit: 0 }, vec![97; 3]))
    );
    assert_eq!(
        parser.parse(b"aab", Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        parser.parse(b"aa", Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    let large = Repeat::exact(Literal::new(8, u64::from(b'a')).unwrap(), 2000);
    assert_eq!(
        large.parse(&vec![b'a'; 2000], Cursor::start()),
        Ok((Cursor { byte: 2000, bit: 0 }, vec![97; 2000]))
    );
}

#[test]
fn unbounded_numeric_repetition_matches_a_bit_string_oracle() {
    let input = [0xa5, 0x13, 0xff];
    let bits: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    for start_bit in 0..=bits.len() {
        let start = Cursor {
            byte: start_bit / 8,
            bit: (start_bit % 8) as u8,
        };
        for width in 1..=13u8 {
            let count = (bits.len() - start_bit) / usize::from(width);
            let values: Vec<u64> = (0..count)
                .map(|i| {
                    let lo = start_bit + i * usize::from(width);
                    u64::from_str_radix(&bits[lo..lo + usize::from(width)], 2).unwrap()
                })
                .collect();
            let end_bit = start_bit + count * usize::from(width);
            let next = Cursor {
                byte: end_bit / 8,
                bit: (end_bit % 8) as u8,
            };
            for min in [0, 1, 3, usize::MAX] {
                let parser = Repeat::at_least(Bits::new(width).unwrap(), min);
                let expected = if count >= min {
                    Ok((next, values.clone()))
                } else {
                    Err(ParseError::UnexpectedEnd)
                };
                assert_eq!(parser.parse(&input, start), expected);
                assert_eq!(
                    parser.parse_with(&input, start, InputStatus::Partial),
                    ParseOutcome::NeedMore
                );
            }
        }
    }
}

#[test]
fn hammer_many_and_many1_cases_including_partial_stopping() {
    for min in [0, 1] {
        let parser = Repeat::at_least(
            Choice {
                first: Literal::new(8, u64::from(b'a')).unwrap(),
                second: Literal::new(8, u64::from(b'b')).unwrap(),
            },
            min,
        );
        for input in [b"".as_slice(), b"a", b"ab", b"abdef", b"d", b"aabbba!"] {
            let count = input
                .iter()
                .take_while(|&&b| b == b'a' || b == b'b')
                .count();
            let final_result = if count >= min {
                Ok((
                    Cursor {
                        byte: count,
                        bit: 0,
                    },
                    input[..count].iter().map(|&b| u64::from(b)).collect(),
                ))
            } else if input.is_empty() {
                Err(ParseError::UnexpectedEnd)
            } else {
                Err(ParseError::Mismatch)
            };
            assert_eq!(parser.parse(input, Cursor::start()), final_result);
            let partial = if count == input.len() {
                ParseOutcome::NeedMore
            } else {
                match final_result {
                    Ok((next, values)) => ParseOutcome::Success(next, values),
                    Err(error) => ParseOutcome::Error(error),
                }
            };
            assert_eq!(
                parser.parse_with(input, Cursor::start(), InputStatus::Partial),
                partial
            );
        }
    }
}

#[test]
fn unbounded_rejection_restores_the_start_of_the_attempt() {
    let input = [0b0101_1000];
    let start = Cursor { byte: 0, bit: 1 };
    for min in [1, 2] {
        let parser = Repeat::at_least(
            Seq {
                first: Literal::new(2, 2).unwrap(),
                second: Literal::new(1, 1).unwrap(),
            },
            min,
        );
        for status in [InputStatus::Partial, InputStatus::Final] {
            let expected = if min == 1 {
                ParseOutcome::Success(Cursor { byte: 0, bit: 4 }, vec![(2, 1)])
            } else {
                ParseOutcome::Error(ParseError::Mismatch)
            };
            assert_eq!(parser.parse_with(&input, start, status), expected);
        }
    }
}

#[test]
fn unbounded_empty_success_is_fatal_even_after_the_minimum() {
    for min in [0, 1, 3] {
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                Repeat::at_least(Bits::new(0).unwrap(), min).parse_with(
                    &[],
                    Cursor::start(),
                    status
                ),
                ParseOutcome::Error(ParseError::NonProgress)
            );
        }
    }
    let optional = Repeat::at_least(
        Optional {
            parser: Literal::new(8, u64::from(b'a')).unwrap(),
        },
        1,
    );
    assert_eq!(
        optional.parse(b"ab", Cursor::start()),
        Err(ParseError::NonProgress)
    );
    let nested = Repeat::at_least(Repeat::new(Bits::new(8).unwrap(), 0, 2).unwrap(), 0);
    assert_eq!(
        nested.parse(b"ab", Cursor::start()),
        Err(ParseError::NonProgress)
    );
    let end = Repeat::at_least(End, 0);
    assert_eq!(
        end.parse(&[], Cursor::start()),
        Err(ParseError::NonProgress)
    );
    assert_eq!(
        end.parse_with(&[], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
}

#[test]
fn unbounded_invalid_initial_cursors_skip_the_child() {
    let parser = Repeat::at_least(MustNotRun, 0);
    for cursor in [
        Cursor { byte: 0, bit: 8 },
        Cursor { byte: 1, bit: 1 },
        Cursor { byte: 2, bit: 0 },
        Cursor {
            byte: usize::MAX,
            bit: 255,
        },
    ] {
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                parser.parse_with(&[0], cursor, status),
                ParseOutcome::Error(ParseError::InvalidCursor)
            );
        }
    }
}

#[test]
fn unbounded_success_cursors_must_be_valid_and_strictly_forward() {
    struct Jump(Cursor);
    impl<'input> Parser<'input> for Jump {
        type Output = ();
        fn parse_with(&self, _: &'input [u8], _: Cursor, _: InputStatus) -> ParseOutcome<()> {
            ParseOutcome::Success(self.0, ())
        }
    }
    let start = Cursor { byte: 1, bit: 3 };
    for (after, error) in [
        (start, ParseError::NonProgress),
        (Cursor { byte: 0, bit: 7 }, ParseError::NonProgress),
        (Cursor { byte: 1, bit: 2 }, ParseError::NonProgress),
        (Cursor { byte: 0, bit: 8 }, ParseError::InvalidCursor),
        (Cursor { byte: 2, bit: 1 }, ParseError::InvalidCursor),
        (
            Cursor {
                byte: usize::MAX,
                bit: 0,
            },
            ParseError::InvalidCursor,
        ),
    ] {
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                Repeat::at_least(Jump(after), 0).parse_with(&[0, 0], start, status),
                ParseOutcome::Error(error)
            );
        }
        // Finite repetition still delegates cursor validation to the child.
        assert_eq!(
            Repeat::exact(Jump(after), 1).parse(&[0, 0], start),
            Ok((after, vec![()]))
        );
    }
}

#[test]
fn repetition_progress_and_count_errors_are_fatal_in_control_combinators() {
    struct Fail(ParseError);
    impl<'input> Parser<'input> for Fail {
        type Output = ();
        fn parse_with(&self, _: &'input [u8], _: Cursor, _: InputStatus) -> ParseOutcome<()> {
            ParseOutcome::Error(self.0)
        }
    }
    for error in [ParseError::NonProgress, ParseError::CountOverflow] {
        assert!(!error.is_recoverable());
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                Choice {
                    first: Fail(error),
                    second: MustNotRun
                }
                .parse_with(&[], Cursor::start(), status),
                ParseOutcome::Error(error)
            );
            assert_eq!(
                Optional {
                    parser: Fail(error)
                }
                .parse_with(&[], Cursor::start(), status),
                ParseOutcome::Error(error)
            );
            assert_eq!(
                And {
                    parser: Fail(error)
                }
                .parse_with(&[], Cursor::start(), status),
                ParseOutcome::Error(error)
            );
            assert_eq!(
                Not {
                    parser: Fail(error)
                }
                .parse_with(&[], Cursor::start(), status),
                ParseOutcome::Error(error)
            );
            assert_eq!(
                Repeat::at_least(Fail(error), 0).parse_with(&[], Cursor::start(), status),
                ParseOutcome::Error(error)
            );
        }
    }
}

#[test]
fn unbounded_borrowed_values_preserve_identity_and_finality() {
    let input = [1, 2, 3, 4, 5];
    let parser = Repeat::at_least(TakeAligned { count: 2 }, 1);
    let (next, values) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 4, bit: 0 });
    assert_eq!(values, [&input[..2], &input[2..4]]);
    assert_eq!(values[0].as_ptr(), input.as_ptr());
    assert_eq!(values[1].as_ptr(), input[2..].as_ptr());
    assert_eq!(
        parser.parse_with(&input, Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
}

#[test]
fn nonprogress_discards_the_last_value_and_all_collected_values() {
    struct Value<'a>(&'a Cell<usize>);
    impl Drop for Value<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Cell::new(0);
    let parser = Repeat::at_least(
        Map {
            parser: Optional {
                parser: Literal::new(8, u64::from(b'a')).unwrap(),
            },
            map: |_| Value(&drops),
        },
        1,
    );
    assert!(matches!(
        parser.parse(b"ab", Cursor::start()),
        Err(ParseError::NonProgress)
    ));
    assert_eq!(drops.get(), 2);
}
