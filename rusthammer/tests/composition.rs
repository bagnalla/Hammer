use std::cell::Cell;

use rusthammer::{
    Bit, Bits, Choice, Cursor, End, Epsilon, Fail, InputStatus, Map, Not, Optional, ParseError,
    ParseOutcome, Parser, Seq, TakeAligned, TryMap,
};

#[test]
fn epsilon_preserves_any_raw_cursor_in_both_modes() {
    for input in [&[][..], &[0x80][..]] {
        for cursor in [
            Cursor::start(),
            Cursor { byte: 0, bit: 5 },
            Cursor { byte: 1, bit: 0 },
            Cursor {
                byte: usize::MAX,
                bit: u8::MAX,
            },
        ] {
            for status in [InputStatus::Partial, InputStatus::Final] {
                assert_eq!(
                    Epsilon.parse_with(input, cursor, status),
                    ParseOutcome::Success(cursor, ())
                );
            }
            assert_eq!(Epsilon.parse(input, cursor), Ok((cursor, ())));
        }
    }
    // Empty success does not wait for end-of-input confirmation.
    assert_eq!(
        End.parse_with(&[], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
}

#[test]
fn fail_is_copyable_without_output_bounds_and_always_rejects() {
    struct NeverMade;
    const REJECT: Fail<NeverMade> = Fail::new();
    fn clone_parser<T>(parser: &Fail<T>) -> Fail<T> {
        parser.clone()
    }
    let parser = clone_parser(&REJECT);
    let copied = parser;
    let default: Fail<NeverMade> = Fail::default();
    for input in [&[][..], &[0x80][..]] {
        for cursor in [
            Cursor::start(),
            Cursor {
                byte: usize::MAX,
                bit: u8::MAX,
            },
        ] {
            for status in [InputStatus::Partial, InputStatus::Final] {
                for grammar in [&parser, &copied, &default] {
                    assert!(matches!(
                        grammar.parse_with(input, cursor, status),
                        ParseOutcome::Error(ParseError::Mismatch)
                    ));
                    assert!(matches!(
                        grammar.parse(input, cursor),
                        Err(ParseError::Mismatch)
                    ));
                }
            }
        }
    }
}

#[test]
fn empty_and_failing_grammars_compose_with_control_flow() {
    let skipped = Map {
        parser: Epsilon,
        map: |_| panic!("unused alternative ran"),
    };
    assert_eq!(
        Choice {
            first: Epsilon,
            second: skipped
        }
        .parse(&[], Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    assert_eq!(
        Choice {
            first: Fail::new(),
            second: Bit
        }
        .parse(&[0x80], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 1 }, true))
    );
    assert_eq!(
        Optional {
            parser: Fail::<bool>::new()
        }
        .parse_with(&[], Cursor::start(), InputStatus::Partial),
        ParseOutcome::Success(Cursor::start(), None)
    );
    assert_eq!(
        Not { parser: Epsilon }.parse(&[], Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        Not {
            parser: Fail::<bool>::new()
        }
        .parse(&[], Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    assert_eq!(
        Seq {
            first: Epsilon,
            second: Bit
        }
        .parse(&[0x80], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 1 }, ((), true)))
    );
}

#[cfg(feature = "alloc")]
#[test]
fn repetition_handles_empty_success_and_definite_rejection() {
    use rusthammer::Repeat;

    for status in [InputStatus::Partial, InputStatus::Final] {
        assert_eq!(
            Repeat::exact(Epsilon, 3).parse_with(&[], Cursor::start(), status),
            ParseOutcome::Success(Cursor::start(), vec![(); 3])
        );
        assert_eq!(
            Repeat::at_least(Epsilon, 0).parse_with(&[], Cursor::start(), status),
            ParseOutcome::Error(ParseError::NonProgress)
        );
        assert_eq!(
            Repeat::at_least(Fail::<bool>::new(), 0).parse_with(&[], Cursor::start(), status),
            ParseOutcome::Success(Cursor::start(), vec![])
        );
        assert_eq!(
            Repeat::at_least(Fail::<bool>::new(), 1).parse_with(&[], Cursor::start(), status),
            ParseOutcome::Error(ParseError::Mismatch)
        );
    }
}

#[test]
fn checked_integer_conversion_preserves_consumption_and_rejects_overflow() {
    let parser = TryMap {
        parser: Bits::new(9).unwrap(),
        map: u8::try_from,
    };
    for status in [InputStatus::Partial, InputStatus::Final] {
        assert_eq!(
            parser.parse_with(&[0x7f, 0x80], Cursor::start(), status),
            ParseOutcome::Success(Cursor { byte: 1, bit: 1 }, 255)
        );
        assert_eq!(
            parser.parse_with(&[0x80, 0x00], Cursor::start(), status),
            ParseOutcome::Error(ParseError::Mismatch)
        );
    }
    assert_eq!(
        parser.parse(&[0x7f, 0x80], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 1 }, 255))
    );
    assert_eq!(
        parser.parse(&[0x80, 0x00], Cursor::start()),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn checked_mapping_skips_callbacks_after_every_child_error_and_need_more() {
    struct Reject(ParseError);
    impl<'input> Parser<'input> for Reject {
        type Output = bool;
        fn parse_with(&self, _: &'input [u8], _: Cursor, _: InputStatus) -> ParseOutcome<bool> {
            ParseOutcome::Error(self.0)
        }
    }
    fn unused(_: bool) -> Result<(), ()> {
        panic!("callback ran without child success")
    }
    for error in [
        ParseError::InvalidCursor,
        ParseError::UnexpectedEnd,
        ParseError::Unaligned,
        ParseError::Mismatch,
        ParseError::TrailingInput,
        ParseError::NonProgress,
        ParseError::CountOverflow,
    ] {
        let parser = TryMap {
            parser: Reject(error),
            map: unused,
        };
        for status in [InputStatus::Partial, InputStatus::Final] {
            assert_eq!(
                parser.parse_with(&[], Cursor::start(), status),
                ParseOutcome::Error(error)
            );
        }
        assert_eq!(parser.parse(&[], Cursor::start()), Err(error));
    }
    let parser = TryMap {
        parser: Bit,
        map: unused,
    };
    assert_eq!(
        parser.parse_with(&[], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn checked_mapping_calls_once_and_is_copyable_with_nonclone_outputs_and_errors() {
    #[derive(Debug, PartialEq)]
    struct Flag(bool);
    struct Rejected;
    let calls = Cell::new(0);
    let parser = TryMap {
        parser: Bit,
        map: |bit| {
            calls.set(calls.get() + 1);
            if bit {
                Ok(Flag(bit))
            } else {
                Err(Rejected)
            }
        },
    };
    let copied = parser;
    assert_eq!(
        copied.parse(&[0x80], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 1 }, Flag(true)))
    );
    assert_eq!(calls.get(), 1);
    assert_eq!(
        parser.parse(&[0x00], Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(calls.get(), 2);
    assert_eq!(
        parser.parse_with(&[], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
    assert_eq!(calls.get(), 2);
}

#[test]
fn conversion_rejection_allows_choice_to_retry_at_the_original_cursor() {
    let parser = Choice {
        first: TryMap {
            parser: Bits::new(3).unwrap(),
            // Conversion error payloads are discarded, even if they look fatal.
            map: |_| Err::<bool, _>(ParseError::InvalidCursor),
        },
        second: Bit,
    };
    for status in [InputStatus::Partial, InputStatus::Final] {
        assert_eq!(
            parser.parse_with(&[0x50], Cursor { byte: 0, bit: 1 }, status),
            ParseOutcome::Success(Cursor { byte: 0, bit: 2 }, true)
        );
    }
    let wait = Choice {
        first: TryMap {
            parser: Bits::new(9).unwrap(),
            map: |_| Err::<(), _>(()),
        },
        second: Map {
            parser: Epsilon,
            map: |_| panic!("fallback ran after NeedMore"),
        },
    };
    assert_eq!(
        wait.parse_with(&[0x80], Cursor::start(), InputStatus::Partial),
        ParseOutcome::NeedMore
    );
}

#[test]
fn checked_mapping_can_return_borrowed_output() {
    fn checked_payload(bytes: &[u8]) -> Result<&[u8], ()> {
        if bytes[0] == b':' {
            Ok(&bytes[1..])
        } else {
            Err(())
        }
    }
    let parser = TryMap {
        parser: TakeAligned { count: 3 },
        map: checked_payload,
    };
    let input = *b":hi!";
    let (next, payload) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 3, bit: 0 });
    assert_eq!(payload, b"hi");
    assert_eq!(payload.as_ptr(), input[1..].as_ptr());
    assert_eq!(
        parser.parse(b"!hi", Cursor::start()),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn checked_mapping_moves_values_and_drops_conversion_errors_once() {
    struct Tracked<'a>(&'a Cell<usize>);
    impl Drop for Tracked<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Cell::new(0);
    let child = Map {
        parser: Epsilon,
        map: |_| Tracked(&drops),
    };
    let accept = TryMap {
        parser: child,
        map: Ok::<Tracked<'_>, Tracked<'_>>,
    };
    let outcome = accept.parse(&[], Cursor::start()).unwrap();
    assert_eq!(drops.get(), 0);
    drop(outcome);
    assert_eq!(drops.get(), 1);
    let reject = TryMap {
        parser: child,
        map: Err::<Tracked<'_>, Tracked<'_>>,
    };
    assert!(matches!(
        reject.parse(&[], Cursor::start()),
        Err(ParseError::Mismatch)
    ));
    assert_eq!(drops.get(), 2);
}
