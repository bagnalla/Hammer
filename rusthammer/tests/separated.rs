#[cfg(feature = "alloc")]
use rusthammer::SepBy;
use rusthammer::{
    Bits, Choice, ConfigError, Cursor, End, Epsilon, FoldSepBy, Ignore, Left, Literal, Map,
    Optional, ParseContext, ParseError, ParseOutcome, Parser, Seq, TakeAligned,
};
use std::cell::Cell;
use std::rc::Rc;

fn byte_cursor(byte: usize) -> Cursor {
    Cursor { byte, bit: 0 }
}

fn literal(byte: u8) -> Literal {
    Literal::new(8, u64::from(byte)).unwrap()
}

struct MustNotRun;
impl<'input> Parser<'input> for MustNotRun {
    type Output = ();
    fn parse_with(&self, _: &'input [u8], _: Cursor, _: ParseContext) -> ParseOutcome<()> {
        panic!("parser must not run")
    }
}

#[test]
fn constructors_validate_item_bounds_without_running_parsers_or_callbacks() {
    let init = || panic!("initializer must not run");
    let fold = |_: (), _: ()| panic!("fold must not run");
    for min in [0, 1, usize::MAX - 1, usize::MAX] {
        let exact = FoldSepBy::exact(MustNotRun, MustNotRun, min, init, fold);
        assert_eq!((exact.min(), exact.max()), (min, Some(min)));
        let unbounded = FoldSepBy::at_least(MustNotRun, MustNotRun, min, init, fold);
        assert_eq!((unbounded.min(), unbounded.max()), (min, None));
        #[cfg(feature = "alloc")]
        {
            let exact = SepBy::exact(MustNotRun, MustNotRun, min);
            assert_eq!((exact.min(), exact.max()), (min, Some(min)));
            let unbounded = SepBy::at_least(MustNotRun, MustNotRun, min);
            assert_eq!((unbounded.min(), unbounded.max()), (min, None));
        }
        for max in [0, 1, usize::MAX - 1, usize::MAX] {
            let result = FoldSepBy::new(MustNotRun, MustNotRun, min, max, init, fold);
            if min <= max {
                let parser = result.unwrap();
                assert_eq!((parser.min(), parser.max()), (min, Some(max)));
            } else {
                assert!(matches!(result, Err(ConfigError::InvalidBounds)));
            }
            #[cfg(feature = "alloc")]
            match SepBy::new(MustNotRun, MustNotRun, min, max) {
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

// An independent language oracle: the longest prefix shared with "a,a,a,..."
// determines the item count and whether a boundary or a conflicting byte stopped it.
fn expected_letters(
    input: &[u8],
    min: usize,
    max: Option<usize>,
    context: ParseContext,
) -> ParseOutcome<usize> {
    let matched = input
        .iter()
        .copied()
        .zip([b'a', b','].into_iter().cycle())
        .take_while(|(actual, expected)| actual == expected)
        .count();
    let count = matched.div_ceil(2).min(max.unwrap_or(usize::MAX));
    let next = byte_cursor(if count == 0 { 0 } else { 2 * count - 1 });
    if max == Some(count) {
        ParseOutcome::Success(next, count)
    } else if matched == input.len() && context == ParseContext::PARTIAL {
        ParseOutcome::NeedMore
    } else if count < min {
        ParseOutcome::Error(if matched == input.len() {
            ParseError::UnexpectedEnd
        } else {
            ParseError::Mismatch
        })
    } else {
        ParseOutcome::Success(next, count)
    }
}

#[test]
fn exhaustive_small_languages_match_for_all_bound_modes_and_input_finalities() {
    for len in 0..=6u32 {
        for mut encoded in 0..3usize.pow(len) {
            let input: Vec<_> = (0..len)
                .map(|_| {
                    let byte = [b'a', b',', b'b'][encoded % 3];
                    encoded /= 3;
                    byte
                })
                .collect();
            for min in 0..=3 {
                for max in (min..=4).map(Some).chain([None]) {
                    let init = || 0usize;
                    let fold = |n, _| n + 1;
                    let parser = match max {
                        Some(max) => {
                            FoldSepBy::new(literal(b'a'), literal(b','), min, max, init, fold)
                                .unwrap()
                        }
                        None => FoldSepBy::at_least(literal(b'a'), literal(b','), min, init, fold),
                    };
                    for context in [ParseContext::FINAL, ParseContext::PARTIAL] {
                        let expected = expected_letters(&input, min, max, context);
                        assert_eq!(
                            parser.parse_with(&input, Cursor::start(), context),
                            expected,
                            "input={input:?} min={min} max={max:?} context={context:?}"
                        );
                        #[cfg(feature = "alloc")]
                        {
                            let collecting = match max {
                                Some(max) => {
                                    SepBy::new(literal(b'a'), literal(b','), min, max).unwrap()
                                }
                                None => SepBy::at_least(literal(b'a'), literal(b','), min),
                            };
                            let expected = match expected {
                                ParseOutcome::Success(next, count) => {
                                    ParseOutcome::Success(next, vec![97; count])
                                }
                                ParseOutcome::Error(error) => ParseOutcome::Error(error),
                                ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                            };
                            assert_eq!(
                                collecting.parse_with(&input, Cursor::start(), context),
                                expected
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn zero_cap_and_invalid_unbounded_start_skip_the_right_operations() {
    let calls = Cell::new(0);
    let parser = FoldSepBy::exact(
        MustNotRun,
        MustNotRun,
        0,
        || {
            calls.set(calls.get() + 1);
            7
        },
        |_, ()| panic!("step must not run"),
    );
    let cursor = Cursor {
        byte: usize::MAX,
        bit: 255,
    };
    for context in [ParseContext::FINAL, ParseContext::PARTIAL] {
        assert_eq!(
            parser.parse_with(&[], cursor, context),
            ParseOutcome::Success(cursor, 7)
        );
        #[cfg(feature = "alloc")]
        assert_eq!(
            SepBy::exact(MustNotRun, MustNotRun, 0).parse_with(&[], cursor, context),
            ParseOutcome::Success(cursor, vec![])
        );
    }
    assert_eq!(calls.get(), 2);
    let parser = FoldSepBy::at_least(
        MustNotRun,
        MustNotRun,
        0,
        || panic!("init must not run"),
        |_: (), ()| panic!("step must not run"),
    );
    assert_eq!(parser.parse(&[], cursor), Err(ParseError::InvalidCursor));
    #[cfg(feature = "alloc")]
    assert_eq!(
        SepBy::at_least(MustNotRun, MustNotRun, 0).parse(&[], cursor),
        Err(ParseError::InvalidCursor)
    );
}

#[test]
fn exact_one_never_calls_a_separator_and_unit_items_are_counted() {
    let item = Ignore {
        parser: literal(b'a'),
    };
    let parser = FoldSepBy::exact(item, MustNotRun, 1, || 0, |n, ()| n + 1);
    assert_eq!(
        parser.parse_with(b"a,", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(byte_cursor(1), 1)
    );
    #[cfg(feature = "alloc")]
    assert_eq!(
        SepBy::exact(item, MustNotRun, 1).parse(b"a,", Cursor::start()),
        Ok((byte_cursor(1), vec![()]))
    );
}

#[test]
fn trailing_separator_is_rolled_back_and_retry_uses_a_fresh_accumulator() {
    let init_calls = Cell::new(0);
    let step_calls = Cell::new(0);
    let parser = FoldSepBy::at_least(
        literal(b'a'),
        literal(b','),
        1,
        || {
            init_calls.set(init_calls.get() + 1);
            0usize
        },
        |n, _| {
            step_calls.set(step_calls.get() + 1);
            n + 1
        },
    );
    assert_eq!(
        parser.parse_with(b"a,", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse_with(b"a,a!", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(byte_cursor(3), 2)
    );
    assert_eq!((init_calls.get(), step_calls.get()), (2, 3));
    assert_eq!(
        parser.parse(b"a,", Cursor::start()),
        Ok((byte_cursor(1), 1))
    );
    assert_eq!(
        Left {
            first: &parser,
            second: End
        }
        .parse(b"a,", Cursor::start()),
        Err(ParseError::TrailingInput)
    );
}

#[test]
fn both_separator_prefixes_and_item_prefixes_roll_back_as_one_attempt() {
    let separator = Seq {
        first: literal(b','),
        second: literal(b':'),
    };
    let parser = FoldSepBy::at_least(literal(b'a'), separator, 1, || 0, |n, _| n + 1);
    assert_eq!(
        parser.parse(b"a,!", Cursor::start()),
        Ok((byte_cursor(1), 1))
    );
    assert_eq!(
        parser.parse_with(b"a,", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    let item = Seq {
        first: literal(b'a'),
        second: literal(b'b'),
    };
    let parser = FoldSepBy::at_least(item, literal(b','), 1, || 0, |n, _| n + 1);
    assert_eq!(
        parser.parse(b"ab,ac", Cursor::start()),
        Ok((byte_cursor(2), 1))
    );
    assert_eq!(
        parser.parse_with(b"ab,a", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    #[cfg(feature = "alloc")]
    {
        assert_eq!(
            SepBy::at_least(literal(b'a'), separator, 1).parse(b"a,!", Cursor::start()),
            Ok((byte_cursor(1), vec![97]))
        );
        assert_eq!(
            SepBy::at_least(item, literal(b','), 1).parse(b"ab,ac", Cursor::start()),
            Ok((byte_cursor(2), vec![(97, 98)]))
        );
    }
}

struct Controlled<'a> {
    first_item: bool,
    stop: bool,
    error: Option<ParseError>,
    calls: &'a Cell<usize>,
}
impl<'input> Parser<'input> for Controlled<'_> {
    type Output = ();
    fn parse_with(&self, _: &'input [u8], cursor: Cursor, _: ParseContext) -> ParseOutcome<()> {
        self.calls.set(self.calls.get() + 1);
        if self.first_item && cursor == Cursor::start() {
            ParseOutcome::Success(byte_cursor(1), ())
        } else if !self.stop {
            ParseOutcome::Success(cursor, ())
        } else {
            match self.error {
                Some(error) => ParseOutcome::Error(error),
                None => ParseOutcome::NeedMore,
            }
        }
    }
}

#[test]
fn errors_and_need_more_from_either_stage_respect_minimum_and_short_circuit() {
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
        for fail_separator in [false, true] {
            for min in [0, 1, 2] {
                for max in [Some(3), None] {
                    let items = Cell::new(0);
                    let separators = Cell::new(0);
                    let steps = Cell::new(0);
                    let item = Controlled {
                        first_item: true,
                        stop: true,
                        error,
                        calls: &items,
                    };
                    let separator = Controlled {
                        first_item: false,
                        stop: fail_separator,
                        error,
                        calls: &separators,
                    };
                    let fold = |n, ()| {
                        steps.set(steps.get() + 1);
                        n + 1
                    };
                    let init = || 0usize;
                    let parser = match max {
                        Some(max) => {
                            FoldSepBy::new(&item, &separator, min, max, init, fold).unwrap()
                        }
                        None => FoldSepBy::at_least(&item, &separator, min, init, fold),
                    };
                    let expected = match error {
                        None => ParseOutcome::NeedMore,
                        Some(e) if e.is_recoverable() && min <= 1 => {
                            ParseOutcome::Success(byte_cursor(1), 1)
                        }
                        Some(e) => ParseOutcome::Error(e),
                    };
                    assert_eq!(
                        parser.parse_with(b"x", Cursor::start(), ParseContext::PARTIAL),
                        expected
                    );
                    assert_eq!(
                        (items.get(), separators.get(), steps.get()),
                        (if fail_separator { 1 } else { 2 }, 1, 1)
                    );
                    #[cfg(feature = "alloc")]
                    {
                        let parser = match max {
                            Some(max) => SepBy::new(&item, &separator, min, max).unwrap(),
                            None => SepBy::at_least(&item, &separator, min),
                        };
                        let expected = match expected {
                            ParseOutcome::Success(next, _) => ParseOutcome::Success(next, vec![()]),
                            ParseOutcome::Error(error) => ParseOutcome::Error(error),
                            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                        };
                        assert_eq!(
                            parser.parse_with(b"x", Cursor::start(), ParseContext::PARTIAL),
                            expected
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn unbounded_progress_belongs_to_the_first_item_then_to_whole_pairs() {
    let empty_first =
        FoldSepBy::at_least(Epsilon, literal(b','), 0, || (), |(), ()| panic!("no step"));
    assert_eq!(
        empty_first.parse(b",", Cursor::start()),
        Err(ParseError::NonProgress)
    );
    let optional = Optional {
        parser: literal(b'a'),
    };
    let parser = FoldSepBy::at_least(optional, literal(b','), 1, || 0, |n, _| n + 1);
    assert_eq!(
        parser.parse(b"a,,!", Cursor::start()),
        Ok((byte_cursor(3), 3))
    );
    let parser = FoldSepBy::at_least(literal(b'a'), Epsilon, 1, || 0, |n, _| n + 1);
    assert_eq!(
        parser.parse(b"aaa!", Cursor::start()),
        Ok((byte_cursor(3), 3))
    );
    let steps = Cell::new(0);
    let stuck = FoldSepBy::at_least(
        optional,
        Epsilon,
        1,
        || (),
        |(), _| steps.set(steps.get() + 1),
    );
    assert_eq!(
        stuck.parse(b"a!", Cursor::start()),
        Err(ParseError::NonProgress)
    );
    assert_eq!(steps.get(), 1);
    #[cfg(feature = "alloc")]
    {
        assert_eq!(
            SepBy::at_least(Epsilon, literal(b','), 0).parse(b",", Cursor::start()),
            Err(ParseError::NonProgress)
        );
        assert_eq!(
            SepBy::at_least(optional, literal(b','), 1).parse(b"a,,!", Cursor::start()),
            Ok((byte_cursor(3), vec![Some(97), None, None]))
        );
        assert_eq!(
            SepBy::at_least(literal(b'a'), Epsilon, 1).parse(b"aaa!", Cursor::start()),
            Ok((byte_cursor(3), vec![97; 3]))
        );
        assert_eq!(
            SepBy::at_least(optional, Epsilon, 1).parse(b"a!", Cursor::start()),
            Err(ParseError::NonProgress)
        );
    }
}

#[test]
fn finite_empty_items_still_call_separators_and_fold_each_item() {
    let separators = Cell::new(0);
    let separator = Map {
        parser: Epsilon,
        map: |()| separators.set(separators.get() + 1),
    };
    let parser = FoldSepBy::exact(Epsilon, &separator, 3, || 0, |n, ()| n * 10 + 1);
    assert_eq!(
        parser.parse(&[], Cursor::start()),
        Ok((Cursor::start(), 111))
    );
    assert_eq!(separators.get(), 2);
    #[cfg(feature = "alloc")]
    {
        assert_eq!(
            SepBy::exact(Epsilon, separator, 3).parse(&[], Cursor::start()),
            Ok((Cursor::start(), vec![(); 3]))
        );
        assert_eq!(separators.get(), 4);
    }
}

#[test]
fn bit_items_and_separators_cross_byte_boundaries() {
    // 101 11 010 11 111: three 3-bit items separated by two 2-bit literals.
    let input = [0xba, 0xf8];
    let item = Bits::new(3).unwrap();
    let separator = Literal::new(2, 3).unwrap();
    let parser = FoldSepBy::exact(item, separator, 3, || 0u64, |n, bits| n * 8 + bits);
    assert_eq!(
        parser.parse_with(&input, Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 1, bit: 5 }, 0o527)
    );
    #[cfg(feature = "alloc")]
    assert_eq!(
        SepBy::exact(item, separator, 3).parse(&input, Cursor::start()),
        Ok((Cursor { byte: 1, bit: 5 }, vec![5, 2, 7]))
    );
}

#[test]
fn existing_hammer_sep_by_and_sep_by1_examples_keep_item_order() {
    // Ported from tests/t_parser.c:test_sepBy and test_sepBy1.
    let item = Choice {
        first: literal(b'1'),
        second: Choice {
            first: literal(b'2'),
            second: literal(b'3'),
        },
    };
    for min in [0, 1] {
        let parser = FoldSepBy::at_least(
            item,
            literal(b','),
            min,
            || 0u64,
            |n, digit| n * 10 + digit - 48,
        );
        for (input, expected) in [
            (b"1,2,3".as_slice(), 123),
            (b"1,3,2", 132),
            (b"1,3", 13),
            (b"3", 3),
        ] {
            assert_eq!(
                parser.parse(input, Cursor::start()),
                Ok((byte_cursor(input.len()), expected))
            );
            #[cfg(feature = "alloc")]
            assert_eq!(
                SepBy::at_least(item, literal(b','), min).parse(input, Cursor::start()),
                Ok((
                    byte_cursor(input.len()),
                    input.iter().step_by(2).map(|&b| u64::from(b)).collect()
                ))
            );
        }
        assert_eq!(
            parser.parse(b"", Cursor::start()),
            if min == 0 {
                Ok((Cursor::start(), 0))
            } else {
                Err(ParseError::UnexpectedEnd)
            }
        );
    }
}

#[derive(Debug)]
struct Token<T> {
    value: T,
    drops: Rc<Cell<usize>>,
}
impl<T> Drop for Token<T> {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}
struct Tracked<P> {
    parser: P,
    drops: Rc<Cell<usize>>,
}
impl<'input, P: Parser<'input>> Parser<'input> for Tracked<P> {
    type Output = Token<P::Output>;
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.parse_with(input, cursor, context) {
            ParseOutcome::Success(next, value) => ParseOutcome::Success(
                next,
                Token {
                    value,
                    drops: Rc::clone(&self.drops),
                },
            ),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn owned_items_separators_and_accumulators_are_dropped_on_each_exit_path() {
    for (min, max, context, success) in [
        (1, None, ParseContext::FINAL, true),
        (1, None, ParseContext::PARTIAL, false),
        (3, None, ParseContext::FINAL, false),
        (2, Some(2), ParseContext::PARTIAL, true),
    ] {
        let item_drops = Rc::new(Cell::new(0));
        let separator_drops = Rc::new(Cell::new(0));
        let state_drops = Rc::new(Cell::new(0));
        let item = Tracked {
            parser: TakeAligned { count: 1 },
            drops: Rc::clone(&item_drops),
        };
        let separator = Tracked {
            parser: literal(b','),
            drops: Rc::clone(&separator_drops),
        };
        let init = || Token {
            value: 0u64,
            drops: Rc::clone(&state_drops),
        };
        let fold = |mut state: Token<u64>, item: Token<&[u8]>| {
            state.value ^= u64::from(item.value[0]);
            state
        };
        let parser = match max {
            Some(max) => FoldSepBy::new(&item, &separator, min, max, init, fold).unwrap(),
            None => FoldSepBy::at_least(&item, &separator, min, init, fold),
        };
        let result = parser.parse_with(b"a,b,", Cursor::start(), context);
        match &result {
            ParseOutcome::Success(next, state) => {
                assert!(success);
                assert_eq!((*next, state.value), (byte_cursor(3), 3));
            }
            ParseOutcome::NeedMore => assert_eq!(context, ParseContext::PARTIAL),
            ParseOutcome::Error(error) => assert_eq!(*error, ParseError::UnexpectedEnd),
        }
        assert_eq!(
            (item_drops.get(), separator_drops.get(), state_drops.get()),
            (2, if max.is_some() { 1 } else { 2 }, usize::from(!success))
        );
        drop(result);
        assert_eq!(state_drops.get(), 1);
        #[cfg(feature = "alloc")]
        {
            item_drops.set(0);
            separator_drops.set(0);
            let parser = match max {
                Some(max) => SepBy::new(&item, &separator, min, max).unwrap(),
                None => SepBy::at_least(&item, &separator, min),
            };
            let input = *b"a,b,";
            let result = parser.parse_with(&input, Cursor::start(), context);
            if let ParseOutcome::Success(next, values) = &result {
                assert!(success);
                assert_eq!(*next, byte_cursor(3));
                assert_eq!(
                    (values[0].value, values[1].value),
                    (&input[..1], &input[2..3])
                );
                assert!(core::ptr::eq(values[0].value.as_ptr(), input.as_ptr()));
                assert!(core::ptr::eq(values[1].value.as_ptr(), input[2..].as_ptr()));
            } else {
                assert!(!success);
            }
            assert_eq!(
                (item_drops.get(), separator_drops.get()),
                (
                    if success { 0 } else { 2 },
                    if max.is_some() { 1 } else { 2 }
                )
            );
            drop(result);
            assert_eq!(item_drops.get(), 2);
        }
    }
}

#[test]
fn copying_parsers_does_not_require_copyable_outputs_or_accumulators() {
    #[derive(Debug, PartialEq)]
    struct Owned(u64);
    let item = Map {
        parser: literal(b'a'),
        map: Owned,
    };
    let separator = Map {
        parser: literal(b','),
        map: Owned,
    };
    let parser = FoldSepBy::exact(
        item,
        separator,
        2,
        || Owned(0),
        |sum: Owned, item: Owned| Owned(sum.0 ^ item.0),
    );
    let copied = parser;
    let input = b"a,a";
    assert_eq!(
        parser.parse(input, Cursor::start()),
        copied.parse(input, Cursor::start())
    );
    #[cfg(feature = "alloc")]
    {
        let parser = SepBy::exact(item, separator, 2);
        let copied = parser;
        assert_eq!(
            parser.parse(input, Cursor::start()),
            copied.parse(input, Cursor::start())
        );
    }
}
