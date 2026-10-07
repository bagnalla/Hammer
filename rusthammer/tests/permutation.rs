use rusthammer::{
    optional, BitOrder, Byte, ByteOrder, BytePattern, Cursor, Epsilon, Eval, Fail, Grammar,
    Literal, Order, ParseContext, ParseError, ParseOutcome, Parser, TakeAligned, WithSpan,
};
use rusthammer::{permutation, required};
use std::{cell::Cell, rc::Rc};

fn at(bit: usize) -> Cursor {
    Cursor {
        byte: bit / 8,
        bit: (bit % 8) as u8,
    }
}
fn lit(byte: u8) -> Literal {
    Literal::new(8, u64::from(byte)).unwrap()
}

#[test]
fn all_orders_and_optional_positions_return_declaration_order() {
    for input in [b"abc", b"acb", b"bac", b"bca", b"cab", b"cba"] {
        assert_eq!(
            permutation((
                required(lit(b'a')),
                required(lit(b'b')),
                required(lit(b'c'))
            ))
            .parse(input, at(0)),
            Ok((at(24), (97, 98, 99)))
        );
        assert_eq!(
            permutation((
                optional(lit(b'a')),
                required(lit(b'b')),
                optional(lit(b'c'))
            ))
            .parse(input, at(0)),
            Ok((at(24), (Some(97), 98, Some(99))))
        );
    }
    let parser = permutation((
        optional(lit(b'a')),
        required(lit(b'b')),
        optional(lit(b'c')),
    ));
    assert_eq!(parser.parse(b"b", at(0)), Ok((at(8), (None, 98, None))));
    assert_eq!(
        parser.parse(b"bc", at(0)),
        Ok((at(16), (None, 98, Some(99))))
    );
    assert_eq!(
        parser.parse(b"ab", at(0)),
        Ok((at(16), (Some(97), 98, None)))
    );
    assert_eq!(parser.parse(b"ac", at(0)), Err(ParseError::Mismatch));
}

#[test]
fn retries_a_successful_prefix_when_the_remaining_items_fail() {
    let parser = permutation((
        required(BytePattern::new(b"a")),
        required(BytePattern::new(b"ab")),
    ));
    assert_eq!(
        parser.parse(b"aba", at(0)),
        Ok((at(24), (&b"a"[..], &b"ab"[..])))
    );
    assert_eq!(
        parser.parse(b"aab", at(0)),
        Ok((at(24), (&b"a"[..], &b"ab"[..])))
    );
    assert_eq!(parser.parse(b"abb", at(0)), Err(ParseError::Mismatch));
    // Each child still chooses only its own first successful alternative.
    let child = rusthammer::choice(BytePattern::new(b"a"), BytePattern::new(b"ab"));
    let parser = permutation((required(child), required(BytePattern::new(b"c"))));
    assert_eq!(parser.parse(b"abc", at(0)), Err(ParseError::Mismatch));
}

#[test]
fn argument_order_breaks_ties_and_optional_matches_precede_absence() {
    assert_eq!(
        permutation((required(Byte), required(Byte))).parse(b"ab", at(0)),
        Ok((at(16), (97, 98)))
    );
    assert_eq!(
        permutation((optional(lit(b'a')), optional(lit(b'a')))).parse(b"a", at(0)),
        Ok((at(8), (Some(97), None)))
    );
    assert_eq!(
        permutation((optional(lit(b'a')), optional(lit(b'a')))).parse(b"", at(0)),
        Ok((at(0), (None, None)))
    );
}

#[test]
fn empty_successes_are_distinct_from_absent_optional_items() {
    let parser = permutation((
        required(Epsilon),
        optional(Epsilon),
        required(optional(Fail::<u8>::new())),
    ));
    assert_eq!(parser.parse(b"", at(0)), Ok((at(0), ((), Some(()), None))));
    assert_eq!(
        permutation((optional(Fail::<u8>::new()),)).parse(b"", at(0)),
        Ok((at(0), (None,)))
    );
    assert_eq!(
        permutation((required(Fail::<u8>::new()),)).parse(b"", at(0)),
        Err(ParseError::Mismatch)
    );
    let invalid = Cursor {
        byte: usize::MAX,
        bit: 255,
    };
    assert_eq!(permutation(()).parse(b"", invalid), Ok((invalid, ())));
    assert_eq!(
        permutation((required(Epsilon),)).parse(b"", invalid),
        Ok((invalid, ((),)))
    );
    assert_eq!(
        permutation((optional(Byte),)).parse(b"", invalid),
        Err(ParseError::InvalidCursor)
    );
}

struct Logged<P> {
    parser: P,
    id: u8,
}
impl<'i, P: Grammar<'i>> Grammar<'i> for Logged<P> {
    type Output = P::Output;
}
impl<'i, P: Eval<'i, Vec<(u8, Cursor)>>> Eval<'i, Vec<(u8, Cursor)>> for Logged<P> {
    fn eval(
        &self,
        backend: &mut Vec<(u8, Cursor)>,
        input: &'i [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        backend.push((self.id, cursor));
        self.parser.eval(backend, input, cursor, context)
    }
}

#[test]
fn cursor_rollback_retains_backend_history_and_fatal_or_partial_stops_search() {
    let mut trace = Vec::new();
    let parser = permutation((
        required(Logged {
            parser: BytePattern::new(b"a"),
            id: 0,
        }),
        required(Logged {
            parser: BytePattern::new(b"ab"),
            id: 1,
        }),
    ));
    assert!(matches!(
        parser.eval(&mut trace, b"aba", at(0), ParseContext::FINAL),
        ParseOutcome::Success(_, _)
    ));
    assert_eq!(trace, [(0, at(0)), (1, at(8)), (1, at(0)), (0, at(16))]);
    trace.clear();
    assert_eq!(
        parser.eval(&mut trace, b"a", at(0), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(trace, [(0, at(0)), (1, at(8))]);
    trace.clear();
    let fatal = permutation((
        optional(Logged {
            parser: TakeAligned { count: 1 },
            id: 0,
        }),
        required(Logged {
            parser: Epsilon,
            id: 1,
        }),
    ));
    assert_eq!(
        fatal.eval(&mut trace, b"ab", at(1), ParseContext::FINAL),
        ParseOutcome::Error(ParseError::Unaligned)
    );
    assert_eq!(trace, [(0, at(1))]);
}

#[test]
fn partial_input_never_establishes_absence_or_tries_a_lower_priority_order() {
    let parser = permutation((
        optional(BytePattern::new(b"ab")),
        required(BytePattern::new(b"a")),
    ));
    assert_eq!(
        parser.parse_with(b"a", at(0), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(parser.parse(b"a", at(0)), Ok((at(8), (None, &b"a"[..]))));
    assert_eq!(
        permutation((required(lit(b'a')),)).parse_with(b"a", at(0), ParseContext::PARTIAL),
        ParseOutcome::Success(at(8), (97,))
    );
    assert_eq!(
        permutation((required(lit(b'a')), optional(lit(b'b')))).parse_with(
            b"a",
            at(0),
            ParseContext::PARTIAL
        ),
        ParseOutcome::NeedMore
    );
}

#[test]
fn outputs_borrow_input_and_configuration_after_the_parser_is_dropped() {
    let pattern = Vec::from(&b"ab"[..]);
    let input = Vec::from(&b"zab"[..]);
    let result = {
        let parser = WithSpan {
            parser: permutation((
                required(BytePattern::new(&pattern)),
                required(TakeAligned { count: 1 }),
            )),
        };
        parser.parse(&input, at(0)).unwrap()
    };
    let (next, ((configured, borrowed), span)) = result;
    assert_eq!(next, at(24));
    assert!(std::ptr::eq(configured.as_ptr(), pattern.as_ptr()));
    assert!(std::ptr::eq(borrowed.as_ptr(), input.as_ptr()));
    assert_eq!(borrowed, b"z");
    assert_eq!(span.as_bytes(), Some(input.as_slice()));
}

struct Tracked {
    byte: u8,
    drops: Rc<Cell<usize>>,
}
impl Drop for Tracked {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}
struct TrackByte(Rc<Cell<usize>>);
impl Grammar<'_> for TrackByte {
    type Output = Tracked;
}
impl<'i, B> Eval<'i, B> for TrackByte {
    fn eval(
        &self,
        backend: &mut B,
        input: &'i [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Tracked> {
        match Byte.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, byte) => ParseOutcome::Success(
                next,
                Tracked {
                    byte,
                    drops: self.0.clone(),
                },
            ),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

#[test]
fn backtracking_moves_and_drops_non_clone_values_without_leaking_them() {
    let drops = Rc::new(Cell::new(0));
    let first = TrackByte(drops.clone());
    let parser = permutation((required(&first), required(lit(b'a'))));
    let (next, (value, literal)) = parser.parse(b"ab", at(0)).unwrap();
    assert_eq!((next, value.byte, literal), (at(16), b'b', 97));
    assert_eq!(drops.get(), 1);
    drop(value);
    assert_eq!(drops.get(), 2);
    assert!(parser.parse(b"xx", at(0)).is_err());
    assert_eq!(drops.get(), 3);
}

#[test]
fn all_orders_and_unaligned_bit_positions_use_the_same_context() {
    for bit in [BitOrder::HighFirst, BitOrder::LowFirst] {
        for byte in [ByteOrder::Big, ByteOrder::Little] {
            for start in 0..8 {
                for first_one in [false, true] {
                    let mut input = [0u8; 2];
                    let one_at = start + usize::from(!first_one);
                    let shift = match bit {
                        BitOrder::HighFirst => 7 - one_at % 8,
                        BitOrder::LowFirst => one_at % 8,
                    };
                    input[one_at / 8] |= 1 << shift;
                    let parser = permutation((
                        required(Literal::new(1, 0).unwrap()),
                        required(Literal::new(1, 1).unwrap()),
                    ));
                    for status in [
                        rusthammer::InputStatus::Final,
                        rusthammer::InputStatus::Partial,
                    ] {
                        assert_eq!(
                            parser.parse_with(
                                &input,
                                at(start),
                                ParseContext {
                                    status,
                                    order: Order { bit, byte }
                                }
                            ),
                            ParseOutcome::Success(at(start + 2), (0, 1))
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn all_supported_tuple_arities_keep_the_declared_shape() {
    macro_rules! check { ($($n:literal),+) => {{
        let parser = permutation(($(required(lit($n)),)+));
        let mut input = vec![$($n),+];
        input.reverse();
        assert_eq!(parser.parse(&input, at(0)), Ok((at(input.len() * 8), ($(u64::from($n as u8),)+))));
    }}; }
    assert_eq!(permutation(()).parse(b"", at(0)), Ok((at(0), ())));
    check!(0);
    check!(0, 1);
    check!(0, 1, 2);
    check!(0, 1, 2, 3);
    check!(0, 1, 2, 3, 4);
    check!(0, 1, 2, 3, 4, 5);
    check!(0, 1, 2, 3, 4, 5, 6);
    check!(0, 1, 2, 3, 4, 5, 6, 7);
    check!(0, 1, 2, 3, 4, 5, 6, 7, 8);
    check!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
    check!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
    check!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
}

#[test]
fn exhaustive_small_required_grammars_match_concatenation_of_permuted_patterns() {
    let patterns: &[&[u8]] = &[b"", b"a", b"b", b"aa", b"ab", b"ba"];
    let orders = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    for &a in patterns {
        for &b in patterns {
            for &c in patterns {
                let children = [a, b, c];
                let parser = permutation((
                    required(BytePattern::new(a)),
                    required(BytePattern::new(b)),
                    required(BytePattern::new(c)),
                ));
                for length in 0..=5 {
                    for bits in 0..(1 << length) {
                        let input: Vec<u8> = (0..length)
                            .map(|i| if bits & (1 << i) == 0 { b'a' } else { b'b' })
                            .collect();
                        let expected = orders.iter().any(|order| {
                            let joined: Vec<u8> = order
                                .iter()
                                .flat_map(|&i| children[i].iter().copied())
                                .collect();
                            input.starts_with(&joined)
                        });
                        let result = parser.parse(&input, at(0));
                        assert_eq!(
                            result.is_ok(),
                            expected,
                            "patterns={children:?}, input={input:?}"
                        );
                        if let Ok((next, values)) = result {
                            assert_eq!(next, at((a.len() + b.len() + c.len()) * 8));
                            assert_eq!(values, (a, b, c));
                        }
                    }
                }
            }
        }
    }
}
