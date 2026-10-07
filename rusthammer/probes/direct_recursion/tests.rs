extern crate std;
use self::std::vec::Vec;
use super::*;
use rusthammer::{choice, BitOrder, ByteOrder, Epsilon, Ignore, InputStatus, Order};

fn input_at_depth(atom: &[u8], depth: usize) -> Vec<u8> {
    let mut input = Vec::new();
    for _ in 0..depth {
        input.extend_from_slice(b"([");
    }
    input.extend_from_slice(atom);
    for _ in 0..depth {
        input.extend_from_slice(b"])");
    }
    input
}

#[test]
fn nested_mutual_grammar_and_consumption() {
    for depth in 0..12 {
        let mut input = input_at_depth(b"ab", depth);
        let end = input.len();
        input.push(b'!');
        assert_eq!(
            configured(b"ab", &input, ParseContext::FINAL),
            ParseOutcome::Success(
                Cursor { byte: end, bit: 0 },
                Parsed {
                    pattern: b"ab",
                    depth
                }
            )
        );
        assert_eq!(
            complete(b"ab", &input, ParseContext::FINAL),
            ParseOutcome::Error(ParseError::TrailingInput)
        );
    }
}

#[test]
fn all_contexts_and_partial_input() {
    for bit in [BitOrder::HighFirst, BitOrder::LowFirst] {
        for byte in [ByteOrder::Big, ByteOrder::Little] {
            for status in [InputStatus::Final, InputStatus::Partial] {
                let context = ParseContext {
                    order: Order { bit, byte },
                    status,
                };
                assert_eq!(
                    configured(b"ab", b"([ab])", context),
                    ParseOutcome::Success(
                        Cursor { byte: 6, bit: 0 },
                        Parsed {
                            pattern: b"ab",
                            depth: 1
                        }
                    )
                );
                assert_eq!(
                    count(b"aaax", Cursor::start(), context),
                    ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, 3)
                );
            }
        }
    }
    assert_eq!(
        count(b"aaa", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        complete(b"ab", b"([ab])", ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}

#[test]
fn truncation_and_malformed_delimiters() {
    let input = input_at_depth(b"ab", 3);
    for end in 0..input.len() {
        assert_eq!(
            configured(b"ab", &input[..end], ParseContext::PARTIAL),
            ParseOutcome::NeedMore
        );
        assert!(matches!(
            configured(b"ab", &input[..end], ParseContext::FINAL),
            ParseOutcome::Error(_)
        ));
    }
    for input in [b"(ab)".as_slice(), b"[ab]", b"([ab)]", b"([x])"] {
        assert!(matches!(
            complete(b"ab", input, ParseContext::FINAL),
            ParseOutcome::Error(_)
        ));
    }
}

#[test]
fn backtracking_and_incomplete_priority() {
    // The delimited branch consumes '(' before it rejects. The configured
    // alternative must be retried at the original cursor.
    assert_eq!(
        configured(b"(", b"(", ParseContext::FINAL),
        ParseOutcome::Success(
            Cursor { byte: 1, bit: 0 },
            Parsed {
                pattern: b"(",
                depth: 0
            }
        )
    );
    assert_eq!(
        configured(b"(", b"(", ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}

#[test]
fn nullable_terminal_does_not_make_recursive_cycle_nullable() {
    assert_eq!(
        configured(b"", b"([])", ParseContext::FINAL),
        ParseOutcome::Success(
            Cursor { byte: 4, bit: 0 },
            Parsed {
                pattern: b"",
                depth: 1
            }
        )
    );
    assert_eq!(
        configured(b"", b"", ParseContext::FINAL),
        ParseOutcome::Success(
            Cursor::start(),
            Parsed {
                pattern: b"",
                depth: 0
            }
        )
    );
    assert_eq!(
        configured(b"", b"", ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}

#[test]
fn independent_borrows_escape_local_parsers_and_sources() {
    let pattern = *b"ab";
    let parsed = {
        let input = *b"([ab])";
        configured(&pattern, &input, ParseContext::FINAL)
    };
    match parsed {
        ParseOutcome::Success(_, value) => assert_eq!(value.pattern.as_ptr(), pattern.as_ptr()),
        _ => panic!("expected configured borrow"),
    }
    let input = *b"([ab])!";
    let recognized = {
        let temporary_pattern = *b"ab";
        super::recognized(
            &temporary_pattern,
            &input,
            Cursor::start(),
            ParseContext::FINAL,
        )
    };
    match recognized {
        ParseOutcome::Success(end, span) => {
            assert_eq!(end, Cursor { byte: 6, bit: 0 });
            assert_eq!(span.as_bytes(), Some(b"([ab])".as_slice()));
            assert_eq!(span.input().as_ptr(), input.as_ptr());
        }
        _ => panic!("expected input borrow"),
    }
    match spanned(&pattern, &input, Cursor::start(), ParseContext::FINAL) {
        ParseOutcome::Success(_, (value, span)) => {
            assert_eq!(value.pattern.as_ptr(), pattern.as_ptr());
            assert_eq!(span.input().as_ptr(), input.as_ptr());
        }
        _ => panic!("expected independent borrows"),
    }
}

#[test]
fn configuration_identity_and_non_clone_results_compose() {
    let first_pattern = *b"a";
    let second_pattern = *b"b";
    let parser = choice(Pairs::new(&first_pattern), Pairs::new(&second_pattern));
    match parser.eval(&mut Direct, b"([b])", Cursor::start(), ParseContext::FINAL) {
        ParseOutcome::Success(_, value) => {
            assert_eq!(value.pattern.as_ptr(), second_pattern.as_ptr())
        }
        _ => panic!("expected second configured parser"),
    }
    assert_eq!(
        twice(b"a", b"([a])a", ParseContext::FINAL),
        ParseOutcome::Success(
            Cursor { byte: 6, bit: 0 },
            (
                Parsed {
                    pattern: b"a",
                    depth: 1
                },
                Parsed {
                    pattern: b"a",
                    depth: 0
                }
            )
        )
    );
}

#[test]
fn unaligned_recursive_span() {
    let payload = b"([a])";
    let mut input = [0u8; 6];
    for offset in 0..40 {
        let bit = (payload[offset / 8] >> (7 - offset % 8)) & 1;
        let at = offset + 3;
        input[at / 8] |= bit << (7 - at % 8);
    }
    match spanned(
        b"a",
        &input,
        Cursor { byte: 0, bit: 3 },
        ParseContext::FINAL,
    ) {
        ParseOutcome::Success(end, (value, span)) => {
            assert_eq!(value.depth, 1);
            assert_eq!(end, Cursor { byte: 5, bit: 3 });
            assert_eq!(span.start(), Cursor { byte: 0, bit: 3 });
            assert_eq!(span.end(), end);
            assert_eq!(span.as_bytes(), None);
        }
        _ => panic!("expected unaligned recursive span"),
    }
}

#[test]
fn fatal_errors_are_not_recovered_by_outer_combinators() {
    let parser = choice(
        Ignore {
            parser: Pairs::new(b""),
        },
        Epsilon,
    );
    for cursor in [Cursor { byte: 1, bit: 0 }, Cursor { byte: 0, bit: 8 }] {
        assert_eq!(
            parser.eval(&mut Direct, b"", cursor, ParseContext::FINAL),
            ParseOutcome::Error(ParseError::InvalidCursor)
        );
    }
}
