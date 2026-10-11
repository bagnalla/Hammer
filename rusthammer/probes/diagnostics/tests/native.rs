use rusthammer::*;
use rusthammer_diagnostic_probe::*;

fn label(name: &str) -> Label<'_> {
    Label { name, source: None }
}

fn check<'meta, 'input, P>(
    parser: P,
    input: &'input [u8],
    context: ParseContext,
) -> (ParseOutcome<P::Output>, Report<'meta>, u32)
where
    P: Eval<'input, Session<u32, Collect<'meta>>> + Eval<'input, Session<u32, Silent>>,
    P::Output: core::fmt::Debug + PartialEq,
{
    let mut collecting = Session {
        backend: 0,
        observer: Collect {
            report: Report::empty(),
        },
    };
    let mut silent = Session {
        backend: 0,
        observer: Silent,
    };
    let result = parser.eval(&mut collecting, input, Cursor::start(), context);
    assert_eq!(
        result,
        parser.eval(&mut silent, input, Cursor::start(), context)
    );
    assert_eq!(collecting.backend, silent.backend);
    (result, collecting.observer.report, collecting.backend)
}

struct Tick<P>(P);
impl<'input, P: Grammar<'input>> Grammar<'input> for Tick<P> {
    type Output = P::Output;
}
impl<'input, O, P: Eval<'input, Session<u32, O>>> Eval<'input, Session<u32, O>> for Tick<P> {
    fn eval(
        &self,
        session: &mut Session<u32, O>,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        session.backend = session.backend.saturating_add(1);
        self.0.eval(session, input, cursor, context)
    }
}

#[test]
fn labelled_reader_agrees_with_production_in_all_orders_and_cursor_classes() {
    for bit in [BitOrder::HighFirst, BitOrder::LowFirst] {
        for byte in [ByteOrder::Big, ByteOrder::Little] {
            for status in [InputStatus::Final, InputStatus::Partial] {
                let context = ParseContext {
                    order: Order { bit, byte },
                    status,
                };
                for length in 0..=2 {
                    for value in 0..=255 {
                        let data = [value, !value];
                        for start in 0..=3 {
                            for offset in 0..=8 {
                                let cursor = Cursor {
                                    byte: start,
                                    bit: offset,
                                };
                                let (result, _) = run(label("A"), &data[..length], cursor, context);
                                assert_eq!(
                                    result,
                                    ByteIn::new(b"A").parse_with(&data[..length], cursor, context)
                                );
                                assert_eq!(
                                    result,
                                    quiet(label("A"), &data[..length], cursor, context)
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn labels_are_occurrences_and_keep_source_locations() {
    let child = ByteEq(b'A');
    let source = Source {
        file: "format.rs",
        line: 12,
        column: 3,
    };
    let parser = labelled(
        Seq {
            first: labelled(&child, label("first")),
            second: labelled(
                &child,
                Label {
                    name: "second",
                    source: Some(source),
                },
            ),
        },
        label("packet"),
    );
    let (_, report, _) = check(parser, b"AX", ParseContext::FINAL);
    let failure = report.first.unwrap();
    assert_eq!(failure.at, Cursor { byte: 1, bit: 0 });
    assert_eq!(failure.inner.unwrap().name, "second");
    assert_eq!(failure.inner.unwrap().source, Some(source));
    assert_eq!(failure.outer.unwrap().name, "packet");
}

#[test]
fn successful_choice_discards_speculation_but_keeps_backend_effects() {
    let parser = scoped(Right {
        first: scoped(Choice {
            first: Tick(ByteEq(b'B')),
            second: Tick(ByteEq(b'A')),
        }),
        second: Tick(ByteEq(b'Z')),
    });
    let (_, report, calls) = check(parser, b"AX", ParseContext::FINAL);
    assert_eq!(calls, 3);
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'Z'));
    assert!(report.second.is_none());
}

#[test]
fn alternatives_merge_ties_and_mark_capacity_loss() {
    let parser = scoped(Choice {
        first: labelled(ByteEq(b'A'), label("left")),
        second: scoped(Choice {
            first: ByteEq(b'B'),
            second: ByteEq(b'C'),
        }),
    });
    let (_, report, _) = check(parser, b"X", ParseContext::FINAL);
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'A'));
    assert_eq!(report.second.unwrap().expected, Expected::Byte(b'B'));
    assert!(report.alternatives_truncated);
    let parser = labelled(
        labelled(labelled(ByteEq(b'A'), label("one")), label("two")),
        label("three"),
    );
    let (_, report, _) = check(parser, b"X", ParseContext::FINAL);
    assert!(report.first.unwrap().labels_truncated);
}

#[test]
fn choice_uses_failing_positions_not_visited_positions() {
    let parser = scoped(Choice {
        first: scoped(Right {
            first: Seek::relative(16),
            second: ByteEq(b'A'),
        }),
        second: scoped(Right {
            first: Seek::relative(24),
            second: Right {
                first: Seek::relative(-24),
                second: ByteEq(b'B'),
            },
        }),
    });
    let (_, report, _) = check(parser, b"XXXX", ParseContext::FINAL);
    assert_eq!(report.first.unwrap().at, Cursor { byte: 2, bit: 0 });
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'A'));
}

#[test]
fn need_more_short_circuits_and_final_input_can_try_an_alternative() {
    let grammar = || {
        scoped(Choice {
            first: Tick(scoped(Right {
                first: ByteEq(b'A'),
                second: ByteEq(b'B'),
            })),
            second: Tick(ByteEq(b'A')),
        })
    };
    let (result, report, calls) = check(grammar(), b"A", ParseContext::PARTIAL);
    assert_eq!(result, ParseOutcome::NeedMore);
    assert_eq!(report.first.unwrap().issue, Issue::Incomplete);
    assert_eq!(report.first.unwrap().at, Cursor { byte: 1, bit: 0 });
    assert_eq!(calls, 1);
    let (result, report, calls) = check(grammar(), b"A", ParseContext::FINAL);
    assert_eq!(
        result,
        ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, b'A')
    );
    assert!(report.first.is_none());
    assert_eq!(calls, 2);
    let parser = scoped(Choice {
        first: scoped(Right {
            first: Seek::relative(16),
            second: ByteEq(b'A'),
        }),
        second: scoped(Right {
            first: Seek::from_end(-8),
            second: ByteEq(b'B'),
        }),
    });
    let (result, report, _) = check(parser, b"XXX", ParseContext::PARTIAL);
    assert_eq!(result, ParseOutcome::NeedMore);
    assert_eq!(report.first.unwrap().issue, Issue::Incomplete);
    assert_eq!(report.first.unwrap().at, Cursor::start());
}

struct Fatal;
impl<'input> Grammar<'input> for Fatal {
    type Output = u8;
}
impl<'input, Backend> Eval<'input, Backend> for Fatal {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<u8> {
        ParseOutcome::Error(ParseError::NonProgress)
    }
}

#[test]
fn fatal_failure_displaces_a_farther_recoverable_failure() {
    let parser = scoped(Choice {
        first: scoped(Right {
            first: Seek::relative(16),
            second: ByteEq(b'A'),
        }),
        second: scoped(Fatal),
    });
    let (result, report, _) = check(parser, b"XXX", ParseContext::FINAL);
    assert_eq!(result, ParseOutcome::Error(ParseError::NonProgress));
    let failure = report.first.unwrap();
    assert_eq!(failure.issue, Issue::Rejected(ParseError::NonProgress));
    assert_eq!(failure.at, Cursor::start());
    assert!(!failure.exact);
}

#[test]
fn optional_and_negative_lookahead_suppress_caught_rejections() {
    let parser = scoped(Right {
        first: scoped(Optional {
            parser: ByteEq(b'B'),
        }),
        second: ByteEq(b'C'),
    });
    let (_, report, _) = check(parser, b"A", ParseContext::FINAL);
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'C'));
    assert!(report.second.is_none());
    let parser = scoped(Right {
        first: scoped(Not {
            parser: ByteEq(b'B'),
        }),
        second: ByteEq(b'C'),
    });
    let (_, report, _) = check(parser, b"A", ParseContext::FINAL);
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'C'));
    assert!(report.second.is_none());
    let (result, report, _) = check(
        scoped(Not {
            parser: ByteEq(b'A'),
        }),
        b"A",
        ParseContext::FINAL,
    );
    assert_eq!(result, ParseOutcome::Error(ParseError::Mismatch));
    assert_eq!(report.first.unwrap().expected, Expected::Unspecified);
}

#[test]
fn positive_lookahead_retains_failure_and_discards_success() {
    let (_, report, _) = check(
        scoped(And {
            parser: ByteEq(b'A'),
        }),
        b"X",
        ParseContext::FINAL,
    );
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'A'));
    let (result, report, _) = check(
        scoped(And {
            parser: ByteEq(b'A'),
        }),
        b"A",
        ParseContext::FINAL,
    );
    assert_eq!(result, ParseOutcome::Success(Cursor::start(), ()));
    assert!(report.first.is_none());
}

#[test]
fn opaque_child_boundary_is_never_claimed_as_an_exact_failure() {
    let parser = labelled(
        Right {
            first: Byte,
            second: Fail::<u8>::new(),
        },
        label("opaque"),
    );
    let (_, report, _) = check(parser, b"A", ParseContext::FINAL);
    assert!(!report.first.unwrap().exact);
    assert_eq!(report.first.unwrap().at, Cursor::start());
}

#[test]
fn root_only_instrumentation_is_insufficient() {
    // Deliberately missing inner scope: demonstrates why hooks must be inside
    // each choice/optional/repetition, not just on the public root wrapper.
    let parser = scoped(Right {
        first: Choice {
            first: ByteEq(b'B'),
            second: ByteEq(b'A'),
        },
        second: ByteEq(b'C'),
    });
    let (_, report, _) = check(parser, b"X", ParseContext::FINAL);
    assert!(report.second.is_some());
    let parser = scoped(Right {
        first: Optional {
            parser: Right {
                first: Seek::relative(8),
                second: ByteEq(b'B'),
            },
        },
        second: ByteEq(b'C'),
    });
    let (_, report, _) = check(parser, b"XX", ParseContext::FINAL);
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'B'));
    // This is the misleading suppressed failure the proposed internal hooks avoid.
    let parser = scoped(Right {
        first: scoped(Optional {
            parser: Right {
                first: Seek::relative(8),
                second: ByteEq(b'B'),
            },
        }),
        second: ByteEq(b'C'),
    });
    let (_, report, _) = check(parser, b"XX", ParseContext::FINAL);
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'C'));
    assert_eq!(report.first.unwrap().at, Cursor::start());
}

#[test]
fn no_clone_outputs_are_moved_once_and_hooks_do_not_reinvoke_callbacks() {
    use std::cell::Cell;
    struct Owned<'a>(&'a Cell<u32>);
    impl Drop for Owned<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Cell::new(0);
    let calls = Cell::new(0);
    let parser = scoped(Map {
        parser: Byte,
        map: |_| {
            calls.set(calls.get() + 1);
            Owned(&drops)
        },
    });
    let mut session = Session {
        backend: (),
        observer: Collect {
            report: Report::empty(),
        },
    };
    let result = parser.eval(&mut session, b"A", Cursor::start(), ParseContext::FINAL);
    assert_eq!(calls.get(), 1);
    assert_eq!(drops.get(), 0);
    drop(result);
    assert_eq!(drops.get(), 1);
}

#[cfg(feature = "alloc")]
#[test]
fn repetition_stopping_is_not_a_failure_but_incompleteness_is() {
    let parser = scoped(Right {
        first: scoped(Repeat::at_least(ByteEq(b'A'), 0)),
        second: ByteEq(b'B'),
    });
    let (_, report, _) = check(parser, b"AAC", ParseContext::FINAL);
    assert_eq!(report.first.unwrap().expected, Expected::Byte(b'B'));
    assert!(report.second.is_none());
    let (result, report, _) = check(
        scoped(Repeat::at_least(ByteEq(b'A'), 0)),
        b"AA",
        ParseContext::PARTIAL,
    );
    assert_eq!(result, ParseOutcome::NeedMore);
    assert_eq!(report.first.unwrap().issue, Issue::Incomplete);
}
