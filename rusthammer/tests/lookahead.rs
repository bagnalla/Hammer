use rusthammer::{
    And, Bits, Choice, Cursor, End, Literal, Map, Not, Optional, ParseError, Parser, Seq,
    TakeAligned,
};
use std::cell::Cell;

#[test]
fn optional_preserves_borrowed_and_non_copy_outputs() {
    let input = [0xca, 0xfe, 0x42];
    let (next, output) = Optional {
        parser: TakeAligned { count: 2 },
    }
    .parse(&input, Cursor::start())
    .unwrap();
    let payload = output.unwrap();
    assert_eq!(next, Cursor { byte: 2, bit: 0 });
    assert_eq!(payload, &input[..2]);
    assert_eq!(payload.as_ptr(), input.as_ptr());

    #[derive(Debug, PartialEq, Eq)]
    struct Value(u64);
    let parser = Optional {
        parser: Map {
            parser: Bits::new(8).unwrap(),
            map: Value,
        },
    };
    assert_eq!(
        parser.parse(&input, Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, Some(Value(0xca))))
    );
}

fn cross_byte_child() -> Seq<Literal, Literal> {
    Seq {
        first: Literal::new(3, 5).unwrap(),
        second: Literal::new(8, 0xff).unwrap(),
    }
}

#[test]
fn optional_restores_the_bit_cursor_after_partial_rejection() {
    let parser = Seq {
        first: Optional {
            parser: cross_byte_child(),
        },
        second: Bits::new(3).unwrap(),
    };
    let start = Cursor { byte: 0, bit: 5 };
    // The first three bits match; the next byte mismatches or is truncated.
    for input in [&[0x05, 0xfe][..], &[0x05][..]] {
        assert_eq!(
            parser.parse(input, start),
            Ok((Cursor { byte: 1, bit: 0 }, (None, 5)))
        );
    }
    assert_eq!(
        parser.parse(&[0x05, 0xff, 0xa0], start),
        Ok((Cursor { byte: 2, bit: 3 }, (Some((5, 0xff)), 5)))
    );
}

#[test]
fn positive_lookahead_discards_consumption_and_preserves_errors() {
    let parser = Seq {
        first: And {
            parser: cross_byte_child(),
        },
        second: Bits::new(3).unwrap(),
    };
    let start = Cursor { byte: 0, bit: 5 };
    assert_eq!(
        parser.parse(&[0x05, 0xff], start),
        Ok((Cursor { byte: 1, bit: 0 }, ((), 5)))
    );
    assert_eq!(
        parser.parse(&[0x05, 0xfe], start),
        Err(ParseError::Mismatch)
    );
    assert_eq!(parser.parse(&[0x05], start), Err(ParseError::UnexpectedEnd));
}

#[test]
fn negative_lookahead_restores_the_bit_cursor_after_partial_rejection() {
    let parser = Seq {
        first: Not {
            parser: cross_byte_child(),
        },
        second: Bits::new(3).unwrap(),
    };
    let start = Cursor { byte: 0, bit: 5 };
    for input in [&[0x05, 0xfe][..], &[0x05][..]] {
        assert_eq!(
            parser.parse(input, start),
            Ok((Cursor { byte: 1, bit: 0 }, ((), 5)))
        );
    }
    assert_eq!(
        parser.parse(&[0x05, 0xff], start),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn complete_input_truncation_and_trailing_input_are_recoverable() {
    fn child() -> Seq<Bits, End> {
        Seq {
            first: Bits::new(8).unwrap(),
            second: End,
        }
    }
    for (input, error) in [
        (&[][..], ParseError::UnexpectedEnd),
        (&[0xca, 0xfe][..], ParseError::TrailingInput),
    ] {
        assert_eq!(
            Optional { parser: child() }.parse(input, Cursor::start()),
            Ok((Cursor::start(), None))
        );
        assert_eq!(
            And { parser: child() }.parse(input, Cursor::start()),
            Err(error)
        );
        assert_eq!(
            Not { parser: child() }.parse(input, Cursor::start()),
            Ok((Cursor::start(), ()))
        );
    }
}

#[test]
fn cursor_and_alignment_errors_cannot_be_hidden_by_assertions_or_optionality() {
    for cursor in [
        Cursor { byte: 0, bit: 8 },
        Cursor { byte: 1, bit: 1 },
        Cursor { byte: 2, bit: 0 },
        Cursor {
            byte: usize::MAX,
            bit: u8::MAX,
        },
    ] {
        assert_eq!(
            Optional {
                parser: Bits::new(0).unwrap()
            }
            .parse(&[0], cursor),
            Err(ParseError::InvalidCursor)
        );
        assert_eq!(
            And {
                parser: Bits::new(0).unwrap()
            }
            .parse(&[0], cursor),
            Err(ParseError::InvalidCursor)
        );
        assert_eq!(
            Not {
                parser: Bits::new(0).unwrap()
            }
            .parse(&[0], cursor),
            Err(ParseError::InvalidCursor)
        );
    }
    // The error is fatal even after a valid child prefix has advanced the cursor.
    fn child() -> Seq<Bits, TakeAligned> {
        Seq {
            first: Bits::new(1).unwrap(),
            second: TakeAligned { count: 0 },
        }
    }
    assert_eq!(
        Optional { parser: child() }.parse(&[0], Cursor::start()),
        Err(ParseError::Unaligned)
    );
    assert_eq!(
        And { parser: child() }.parse(&[0], Cursor::start()),
        Err(ParseError::Unaligned)
    );
    assert_eq!(
        Not { parser: child() }.parse(&[0], Cursor::start()),
        Err(ParseError::Unaligned)
    );
}

#[test]
fn empty_success_is_distinct_from_absence_even_at_end_of_input() {
    let start = Cursor::start();
    assert_eq!(
        Optional {
            parser: Bits::new(0).unwrap()
        }
        .parse(&[], start),
        Ok((start, Some(0)))
    );
    assert_eq!(
        Optional {
            parser: Bits::new(1).unwrap()
        }
        .parse(&[], start),
        Ok((start, None))
    );
    assert_eq!(
        And {
            parser: Bits::new(0).unwrap()
        }
        .parse(&[], start),
        Ok((start, ()))
    );
    assert_eq!(
        Not {
            parser: Bits::new(0).unwrap()
        }
        .parse(&[], start),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        Not { parser: End }.parse(&[], start),
        Err(ParseError::Mismatch)
    );
    assert_eq!(Not { parser: End }.parse(&[0], start), Ok((start, ())));
}

#[test]
fn lookahead_runs_the_child_once_and_accepts_non_copy_outputs() {
    #[derive(Debug)]
    struct Value;
    let calls = Cell::new(0);
    let and = And {
        parser: Map {
            parser: Bits::new(8).unwrap(),
            map: |_| {
                calls.set(calls.get() + 1);
                Value
            },
        },
    };
    assert_eq!(and.parse(&[0], Cursor::start()), Ok((Cursor::start(), ())));
    assert_eq!(calls.get(), 1);
    let not = Not {
        parser: Map {
            parser: Bits::new(8).unwrap(),
            map: |_| {
                calls.set(calls.get() + 1);
                Value
            },
        },
    };
    assert_eq!(not.parse(&[0], Cursor::start()), Err(ParseError::Mismatch));
    assert_eq!(calls.get(), 2);
    // Cursor rollback deliberately does not undo the callback's observable effect.
}

#[test]
fn negative_lookahead_disambiguates_ordered_alternatives() {
    // Hammer's documented example: the single '+' branch must not steal '++'.
    let operator = Choice {
        first: Seq {
            first: Literal::new(8, u64::from(b'+')).unwrap(),
            second: Not {
                parser: Literal::new(8, u64::from(b'+')).unwrap(),
            },
        },
        second: Seq {
            first: Literal::new(16, 0x2b2b).unwrap(),
            second: And {
                parser: Literal::new(8, u64::from(b'b')).unwrap(),
            },
        },
    };
    let parser = Seq {
        first: Literal::new(8, u64::from(b'a')).unwrap(),
        second: Seq {
            first: operator,
            second: Seq {
                first: Literal::new(8, u64::from(b'b')).unwrap(),
                second: End,
            },
        },
    };
    for (input, expected) in [(&b"a+b"[..], 0x2b), (&b"a++b"[..], 0x2b2b)] {
        assert_eq!(
            parser.parse(input, Cursor::start()),
            Ok((
                Cursor {
                    byte: input.len(),
                    bit: 0
                },
                (u64::from(b'a'), ((expected, ()), (u64::from(b'b'), ())))
            ))
        );
    }
    for input in [&b"a+++b"[..], &b"a+b!"[..], &b"a++"[..]] {
        assert!(parser.parse(input, Cursor::start()).is_err());
    }
}

#[test]
fn optional_matches_hammers_optional_choice_grammar() {
    // Port the a[bc]?d cases from Hammer's test_optional.
    let parser = Seq {
        first: Literal::new(8, u64::from(b'a')).unwrap(),
        second: Seq {
            first: Optional {
                parser: Choice {
                    first: Literal::new(8, u64::from(b'b')).unwrap(),
                    second: Literal::new(8, u64::from(b'c')).unwrap(),
                },
            },
            second: Literal::new(8, u64::from(b'd')).unwrap(),
        },
    };
    for (input, value) in [
        (&b"abd"[..], Some(u64::from(b'b'))),
        (&b"acd"[..], Some(u64::from(b'c'))),
        (&b"ad"[..], None),
    ] {
        assert_eq!(
            parser.parse(input, Cursor::start()),
            Ok((
                Cursor {
                    byte: input.len(),
                    bit: 0
                },
                (u64::from(b'a'), (value, u64::from(b'd')))
            ))
        );
    }
    for input in [&b"aed"[..], &b"ab"[..], &b"ac"[..]] {
        assert!(parser.parse(input, Cursor::start()).is_err());
    }
}
