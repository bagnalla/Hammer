use rusthammer::{
    And, Bind, Bits, ButNot, Byte, ByteOrder, Choice, Cursor, Difference, FoldRepeat, FoldSepBy,
    Ignore, IntRange, Left, Literal, Map, Middle, Not, Optional, ParseError, Parser, Right, Seq,
    TryMap, Verify, WithByteOrder, Xor,
};

thread_local! {
    static TRACE: std::cell::RefCell<Vec<(u8, Cursor, ByteOrder)>> = const { std::cell::RefCell::new(Vec::new()) };
}
fn trace() -> Vec<(u8, Cursor, ByteOrder)> {
    TRACE.with(|trace| trace.borrow().clone())
}
fn clear_trace() {
    TRACE.with(|trace| trace.borrow_mut().clear());
}

// A custom parser records child execution without a library execution-state parameter.
struct Observe<P>(u8, P);

impl<'input, P: Parser<'input>> Parser<'input> for Observe<P> {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        TRACE.with(|trace| trace.borrow_mut().push((self.0, cursor, byte_order)));
        self.1.parse_with(input, cursor, byte_order)
    }
}

fn run<'input, P: Parser<'input>>(parser: P, input: &'input [u8], ids: &[u8]) {
    clear_trace();
    let _ = parser.parse_with(input, Cursor::start(), ByteOrder::Big);
    assert_eq!(trace().iter().map(|entry| entry.0).collect::<Vec<_>>(), ids);
}

#[test]
fn sequence_selection_references_and_callbacks_preserve_call_order() {
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
    clear_trace();
    match parser.parse_with(b"a", Cursor::start(), ByteOrder::Big) {
        Ok(parsed) => {
            let (_, value) = parsed;
            assert_eq!(value.0, b'a')
        }
        _ => panic!("expected success"),
    }
    assert_eq!(trace().len(), 1);
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
    clear_trace();
    assert_eq!(
        parser.parse_with(b"b", Cursor::start(), ByteOrder::Big),
        Ok((Cursor { byte: 1, bit: 0 }, ((), b'b')))
    );
    assert_eq!(
        trace(),
        vec![
            (1, Cursor::start(), ByteOrder::Big),
            (2, Cursor::start(), ByteOrder::Big)
        ]
    );
}

#[test]
fn scopes_change_byte_order_while_retaining_execution_state() {
    let parser = Seq {
        first: WithByteOrder {
            parser: Observe(1, Bits::new(8).unwrap()),
            byte_order: ByteOrder::Little,
        },
        second: Observe(2, Byte),
    };
    clear_trace();
    let result = parser.parse_with(&[1, 2], Cursor::start(), ByteOrder::Big);
    assert!(matches!(result, Ok((_, _))));
    assert_eq!(trace()[0].2, parser.first.byte_order);
    assert_eq!(trace()[1], (2, Cursor { byte: 1, bit: 0 }, ByteOrder::Big));
}

#[test]
fn repetition_and_separator_helpers_preserve_call_order() {
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
