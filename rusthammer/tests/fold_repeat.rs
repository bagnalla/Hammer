use rusthammer::{
    Bit, Bits, ConfigError, Cursor, Epsilon, FoldRepeat, Literal, Map, ParseContext, ParseError,
    ParseOutcome, Parser, Seq, TakeAligned,
};
use rusthammer::{Eval, Grammar};
use std::cell::Cell;

struct MustNotRun;
impl<'input> Grammar<'input> for MustNotRun {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for MustNotRun {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<()> {
        panic!("child must not run")
    }
}
fn no_init() {
    panic!("initializer must not run")
}
fn no_step(_: (), _: ()) {
    panic!("fold step must not run")
}

#[test]
fn constructors_validate_bounds_without_running_any_callbacks() {
    for min in [0, 1, usize::MAX - 1, usize::MAX] {
        let exact = FoldRepeat::exact(MustNotRun, min, no_init, no_step);
        assert_eq!((exact.min(), exact.max()), (min, Some(min)));
        let unbounded = FoldRepeat::at_least(MustNotRun, min, no_init, no_step);
        assert_eq!((unbounded.min(), unbounded.max()), (min, None));
        for max in [0, 1, usize::MAX - 1, usize::MAX] {
            match FoldRepeat::new(MustNotRun, min, max, no_init, no_step) {
                Ok(p) => {
                    assert!(min <= max);
                    assert_eq!((p.min(), p.max()), (min, Some(max)));
                }
                Err(e) => {
                    assert!(min > max);
                    assert_eq!(e, ConfigError::InvalidBounds);
                }
            }
        }
    }
}

#[test]
fn numeric_folding_matches_an_independent_bit_string_oracle() {
    let input = [0xa5, 0x13, 0xff];
    let bits: String = input.iter().map(|byte| format!("{byte:08b}")).collect();
    for start in 0..=bits.len() {
        let cursor = Cursor {
            byte: start / 8,
            bit: (start % 8) as u8,
        };
        for width in 0..=9u8 {
            for min in 0..=3 {
                for max in min..=4 {
                    let fold = |acc: u64, value| acc.rotate_left(4) ^ value;
                    let parser =
                        FoldRepeat::new(Bits::new(width).unwrap(), min, max, || 7u64, fold)
                            .unwrap();
                    let available = if width == 0 {
                        max
                    } else {
                        (bits.len() - start) / usize::from(width)
                    };
                    let count = available.min(max);
                    let expected = (0..count).fold(7u64, |acc, i| {
                        let pos = start + i * usize::from(width);
                        let value = if width == 0 {
                            0
                        } else {
                            u64::from_str_radix(&bits[pos..pos + usize::from(width)], 2).unwrap()
                        };
                        fold(acc, value)
                    });
                    let end = start + count * usize::from(width);
                    let next = Cursor {
                        byte: end / 8,
                        bit: (end % 8) as u8,
                    };
                    let complete = if count < min {
                        Err(ParseError::UnexpectedEnd)
                    } else {
                        Ok((next, expected))
                    };
                    assert_eq!(parser.parse(&input, cursor), complete);
                    let partial = if count == max {
                        ParseOutcome::Success(next, expected)
                    } else {
                        ParseOutcome::NeedMore
                    };
                    assert_eq!(
                        parser.parse_with(&input, cursor, ParseContext::PARTIAL),
                        partial
                    );
                }
            }
        }
    }
}

#[test]
fn zero_maximum_initializes_once_and_preserves_even_an_invalid_cursor() {
    let calls = Cell::new(0);
    let parser = FoldRepeat::exact(
        MustNotRun,
        0,
        || {
            calls.set(calls.get() + 1);
        },
        no_step,
    );
    let cursor = Cursor {
        byte: usize::MAX,
        bit: 255,
    };
    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
        assert_eq!(
            parser.parse_with(&[], cursor, context),
            ParseOutcome::Success(cursor, ())
        );
    }
    assert_eq!(calls.get(), 2);
    let invalid = FoldRepeat::at_least(MustNotRun, 0, no_init, no_step);
    assert_eq!(invalid.parse(&[], cursor), Err(ParseError::InvalidCursor));
}

#[test]
fn finite_empty_successes_fold_in_order_and_each_parse_starts_fresh() {
    let init_calls = Cell::new(0);
    let step_calls = Cell::new(0);
    let parser = FoldRepeat::exact(
        Epsilon,
        3,
        || {
            init_calls.set(init_calls.get() + 1);
            0u32
        },
        |acc, ()| {
            step_calls.set(step_calls.get() + 1);
            acc * 10 + 1
        },
    );
    for _ in 0..2 {
        assert_eq!(
            parser.parse(&[], Cursor::start()),
            Ok((Cursor::start(), 111))
        );
    }
    assert_eq!((init_calls.get(), step_calls.get()), (2, 6));
}

#[test]
fn rejected_composite_attempt_rolls_back_without_folding_its_partial_output() {
    let steps = Cell::new(0);
    let child = Seq {
        first: Bits::new(8).unwrap(),
        second: Literal::new(8, 0xff).unwrap(),
    };
    let parser = FoldRepeat::new(
        child,
        1,
        3,
        || 0u64,
        |acc, (byte, _)| {
            steps.set(steps.get() + 1);
            acc ^ byte
        },
    )
    .unwrap();
    assert_eq!(
        parser.parse(&[5, 0xff, 6, 0], Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, 5))
    );
    assert_eq!(steps.get(), 1);
    assert_eq!(
        parser.parse_with(&[5, 0xff, 6], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(steps.get(), 2);
}

#[derive(Clone, Copy)]
struct FirstThen {
    error: Option<ParseError>,
}
impl<'input> Grammar<'input> for FirstThen {
    type Output = bool;
}

impl<'input, Backend> Eval<'input, Backend> for FirstThen {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        cursor: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<bool> {
        if cursor == Cursor::start() {
            ParseOutcome::Success(Cursor { byte: 0, bit: 1 }, true)
        } else {
            match self.error {
                Some(error) => ParseOutcome::Error(error),
                None => ParseOutcome::NeedMore,
            }
        }
    }
}

#[test]
fn minimum_fatal_errors_and_incompleteness_share_the_collection_rules() {
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
        for min in [0, 1, 2] {
            for unbounded in [false, true] {
                let calls = Cell::new(0);
                let fold = |acc, _| {
                    calls.set(calls.get() + 1);
                    acc + 1
                };
                let child = FirstThen { error };
                let init = || 0usize;
                let parser = if unbounded {
                    FoldRepeat::at_least(child, min, init, fold)
                } else {
                    FoldRepeat::new(child, min, 2, init, fold).unwrap()
                };
                let expected = match error {
                    None => ParseOutcome::NeedMore,
                    Some(e) if e.is_recoverable() && min <= 1 => {
                        ParseOutcome::Success(Cursor { byte: 0, bit: 1 }, 1)
                    }
                    Some(e) => ParseOutcome::Error(e),
                };
                for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                    assert_eq!(parser.parse_with(&[0], Cursor::start(), context), expected);
                }
                assert_eq!(calls.get(), 2);
            }
        }
    }
}

#[test]
fn unbounded_folding_stops_at_rejection_but_propagates_partial_exhaustion() {
    let parser = FoldRepeat::at_least(Literal::new(1, 1).unwrap(), 0, || 0usize, |n, _| n + 1);
    assert_eq!(
        parser.parse_with(&[0xc0], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 0, bit: 2 }, 2)
    );
    assert_eq!(
        parser.parse_with(&[0xff], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse(&[0xff], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, 8))
    );
    assert_eq!(
        parser.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(parser.parse(&[], Cursor::start()), Ok((Cursor::start(), 0)));
}

struct Jump(Cursor);
impl<'input> Grammar<'input> for Jump {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for Jump {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<()> {
        ParseOutcome::Success(self.0, ())
    }
}

#[test]
fn progress_and_cursor_errors_precede_the_fold_step() {
    let start = Cursor { byte: 0, bit: 2 };
    for (after, error) in [
        (start, ParseError::NonProgress),
        (Cursor { byte: 0, bit: 1 }, ParseError::NonProgress),
        (Cursor { byte: 0, bit: 8 }, ParseError::InvalidCursor),
        (Cursor { byte: 2, bit: 0 }, ParseError::InvalidCursor),
        (Cursor { byte: 1, bit: 1 }, ParseError::InvalidCursor),
    ] {
        let parser = FoldRepeat::at_least(Jump(after), 0, || (), no_step);
        assert_eq!(parser.parse(&[0], start), Err(error));
        // Finite repetition delegates successful-cursor validation to its child.
        let finite = FoldRepeat::exact(Jump(after), 1, || 0, |n, ()| n + 1);
        assert_eq!(finite.parse(&[0], start), Ok((after, 1)));
    }
}

#[derive(Debug)]
struct Owned<'a> {
    total: usize,
    drops: &'a Cell<usize>,
}
impl Drop for Owned<'_> {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}
struct Borrowed<'a, 'b> {
    bytes: &'a [u8],
    drops: &'b Cell<usize>,
}
impl Drop for Borrowed<'_, '_> {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

fn sum_owned<'a>(mut state: Owned<'a>, value: Borrowed<'_, '_>) -> Owned<'a> {
    state.total += usize::from(value.bytes[0]);
    state
}

#[test]
fn non_clone_outputs_and_accumulators_are_moved_and_dropped_on_every_outcome() {
    for (count, context) in [
        (2, ParseContext::FINAL),
        (3, ParseContext::FINAL),
        (3, ParseContext::PARTIAL),
    ] {
        let output_drops = Cell::new(0);
        let state_drops = Cell::new(0);
        let child = Map {
            parser: TakeAligned { count: 1 },
            map: |bytes| Borrowed {
                bytes,
                drops: &output_drops,
            },
        };
        let parser = FoldRepeat::exact(
            child,
            count,
            || Owned {
                total: 0,
                drops: &state_drops,
            },
            sum_owned,
        );
        let outcome = parser.parse_with(&[2, 3], Cursor::start(), context);
        assert_eq!(output_drops.get(), 2);
        match outcome {
            ParseOutcome::Success(next, state) => {
                assert_eq!(count, 2);
                assert_eq!(next, Cursor { byte: 2, bit: 0 });
                assert_eq!(state.total, 5);
                assert_eq!(state_drops.get(), 0);
                drop(state);
            }
            ParseOutcome::Error(error) => {
                assert_eq!(count, 3);
                assert_eq!(error, ParseError::UnexpectedEnd);
            }
            ParseOutcome::NeedMore => {
                assert_eq!((count, context), (3, ParseContext::PARTIAL));
            }
        }
        assert_eq!(state_drops.get(), 1);
    }
}

#[test]
fn borrowed_accumulator_points_into_the_original_input() {
    let input = *b"abc";
    let parser = FoldRepeat::exact(TakeAligned { count: 1 }, 2, || &[][..], |_, byte| byte);
    let (next, last) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 2, bit: 0 });
    assert_eq!(last, b"b");
    assert_eq!(last.as_ptr(), input[1..].as_ptr());
}

#[test]
fn parser_copy_depends_on_stored_components_not_the_accumulator() {
    #[derive(Debug, PartialEq)]
    struct Total(usize);
    let fold = FoldRepeat::exact(
        Bit,
        2,
        || Total(0),
        |n: Total, bit| Total(n.0 + usize::from(bit)),
    );
    fn assert_copy<T: Copy>(_: &T) {}
    assert_copy(&fold);
    let seq = Seq {
        first: fold,
        second: fold,
    };
    assert_eq!(
        seq.parse(&[0xb0], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 4 }, (Total(1), Total(2))))
    );
}
