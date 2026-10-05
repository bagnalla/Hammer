use rusthammer::{
    And, Bind, BitOrder, Bits, ButNot, Byte, ByteOrder, Choice, Cursor, Difference, Eval,
    FoldRepeat, FoldSepBy, Grammar, Ignore, IntRange, Left, Literal, Map, Middle, Not, Optional,
    Order, ParseContext, ParseOutcome, Right, Seq, TryMap, Verify, WithOrder, Xor,
};

#[derive(Default)]
struct Trace(Vec<(u8, Cursor, ParseContext)>);

// No Eval<Direct> implementation: accidental calls through Parser cannot compile.
struct Observe<P>(u8, P);

impl<'input, P: Grammar<'input>> Grammar<'input> for Observe<P> {
    type Output = P::Output;
}

impl<'input, P: Eval<'input, Trace>> Eval<'input, Trace> for Observe<P> {
    fn eval(
        &self,
        backend: &mut Trace,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        backend.0.push((self.0, cursor, context));
        self.1.eval(backend, input, cursor, context)
    }
}

fn run<'input, P: Eval<'input, Trace>>(parser: P, input: &'input [u8], ids: &[u8]) {
    let mut trace = Trace::default();
    let _ = parser.eval(&mut trace, input, Cursor::start(), ParseContext::FINAL);
    assert_eq!(trace.0.iter().map(|entry| entry.0).collect::<Vec<_>>(), ids);
}

#[test]
fn sequence_selection_references_and_callbacks_keep_the_backend() {
    let a = Observe(1, Byte);
    let b = Observe(2, Byte);
    run(
        Seq {
            first: &a,
            second: &b,
        },
        b"ab",
        &[1, 2],
    );
    run(
        Left {
            first: &a,
            second: &b,
        },
        b"ab",
        &[1, 2],
    );
    run(
        Right {
            first: &a,
            second: &b,
        },
        b"ab",
        &[1, 2],
    );
    run(
        Middle {
            left: &a,
            parser: &b,
            right: &a,
        },
        b"abc",
        &[1, 2, 1],
    );
    run(Ignore { parser: &a }, b"a", &[1]);
    // The output intentionally implements neither Clone nor Copy.
    struct Owned(u8);
    let parser = Map {
        parser: &a,
        map: Owned,
    };
    let mut trace = Trace::default();
    match parser.eval(&mut trace, b"a", Cursor::start(), ParseContext::FINAL) {
        ParseOutcome::Success(_, value) => assert_eq!(value.0, b'a'),
        _ => panic!("expected success"),
    }
    assert_eq!(trace.0.len(), 1);
    run(
        TryMap {
            parser: &a,
            map: |v| Ok::<_, ()>(Owned(v)),
        },
        b"a",
        &[1],
    );
    run(
        Verify {
            parser: &a,
            predicate: |_: &u8| true,
        },
        b"a",
        &[1],
    );
    run(IntRange::new(&a, b'a', b'z').unwrap(), b"a", &[1]);
    run(
        Bind {
            parser: &a,
            then: |_| &b,
        },
        b"ab",
        &[1, 2],
    );
}

#[test]
fn backtracking_keeps_bookkeeping_but_restores_the_cursor() {
    let a = Observe(1, Literal::new(8, b'a'.into()).unwrap());
    let b = Observe(2, Byte);
    run(
        Choice {
            first: &a,
            second: &Observe(3, Literal::new(8, b'b'.into()).unwrap()),
        },
        b"b",
        &[1, 3],
    );
    run(Optional { parser: &a }, b"b", &[1]);
    run(And { parser: &a }, b"a", &[1]);
    run(Not { parser: &a }, b"b", &[1]);
    run(
        ButNot {
            first: &a,
            second: &b,
        },
        b"a",
        &[1, 2],
    );
    run(
        Difference {
            first: &a,
            second: &b,
        },
        b"a",
        &[1, 2],
    );
    run(
        Xor {
            first: &a,
            second: &a,
        },
        b"a",
        &[1, 1],
    );
    let parser = Seq {
        first: Not { parser: &a },
        second: &b,
    };
    let mut trace = Trace::default();
    assert_eq!(
        parser.eval(&mut trace, b"b", Cursor::start(), ParseContext::FINAL),
        ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, ((), b'b'))
    );
    assert_eq!(
        trace.0,
        vec![
            (1, Cursor::start(), ParseContext::FINAL),
            (2, Cursor::start(), ParseContext::FINAL)
        ]
    );
}

#[test]
fn scopes_change_context_while_retaining_execution_state() {
    let parser = Seq {
        first: WithOrder {
            parser: Observe(1, Bits::new(8).unwrap()),
            order: Order {
                bit: BitOrder::LowFirst,
                byte: ByteOrder::Little,
            },
        },
        second: Observe(2, Byte),
    };
    let mut trace = Trace::default();
    let result = parser.eval(&mut trace, &[1, 2], Cursor::start(), ParseContext::PARTIAL);
    assert!(matches!(result, ParseOutcome::Success(_, _)));
    assert_eq!(trace.0[0].2.order, parser.first.order);
    assert_eq!(trace.0[0].2.status, ParseContext::PARTIAL.status);
    assert_eq!(
        trace.0[1],
        (2, Cursor { byte: 1, bit: 0 }, ParseContext::PARTIAL)
    );
}

#[test]
fn repetition_and_separator_helpers_keep_the_backend() {
    let a = Observe(1, Literal::new(8, b'a'.into()).unwrap());
    let comma = Observe(2, Literal::new(8, b','.into()).unwrap());
    run(
        FoldRepeat::at_least(&a, 0, || 0usize, |n, _| n + 1),
        b"aa!",
        &[1, 1, 1],
    );
    run(
        FoldSepBy::at_least(&a, &comma, 0, || 0usize, |n, _| n + 1),
        b"a,a!",
        &[1, 2, 1, 2],
    );
    #[cfg(feature = "alloc")]
    {
        run(rusthammer::Repeat::exact(&a, 2), b"aa", &[1, 1]);
        run(rusthammer::SepBy::exact(&a, &comma, 2), b"a,a", &[1, 2, 1]);
    }
}
