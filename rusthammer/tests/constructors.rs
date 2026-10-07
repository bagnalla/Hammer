use std::cell::Cell;

use rusthammer::{
    bind, choice, map, optional, seq, try_map, verify, Cursor, Eval, Grammar, ParseContext,
    ParseOutcome, Parser, TakeAligned,
};

#[path = "../examples/support/constructors.rs"]
mod support;

// Constructing a grammar must not require any interpreter implementation.
struct Declaration;

impl<'input> Grammar<'input> for Declaration {
    type Output = u8;
}

#[test]
fn construction_checks_output_relationships_without_interpreting_or_calling_callbacks() {
    let calls = Cell::new(0);
    let mapped = map(Declaration, |value| {
        calls.set(calls.get() + 1);
        value
    });
    let converted = try_map(mapped, |value| {
        calls.set(calls.get() + 1);
        Ok::<_, ()>(value)
    });
    let checked = verify(converted, |value| {
        calls.set(calls.get() + 1);
        *value <= 3
    });
    let dependent = bind(&checked, |_value| {
        calls.set(calls.get() + 1);
        Declaration
    });
    let grammar = seq(choice(dependent, Declaration), optional(Declaration));
    fn check_output<'input>(_: &impl Grammar<'input, Output = (u8, Option<u8>)>) {}
    check_output(&grammar);
    assert_eq!(calls.get(), 0);
}

#[test]
fn opaque_callback_keeps_generic_backends_and_copy_without_copying_outputs() {
    // The factory returns a concrete Map node, so arbitrary backends still work.
    struct Backend;
    let header = support::header();
    let copied = header;
    let grammar = seq(&header, copied);
    assert_eq!(
        grammar.eval(
            &mut Backend,
            &[1, 0, 3, 2, 0, 4],
            Cursor::start(),
            ParseContext::FINAL
        ),
        ParseOutcome::Success(
            Cursor { byte: 6, bit: 0 },
            (
                support::Header { tag: 1, length: 3 },
                support::Header { tag: 2, length: 4 }
            )
        )
    );
}

#[test]
fn callbacks_may_return_input_borrows_without_a_static_or_higher_ranked_bound() {
    fn borrowed(input: &[u8]) -> &[u8] {
        let parser = try_map(
            verify(map(TakeAligned { count: 2 }, |bytes| bytes), |bytes| {
                bytes.len() == 2
            }),
            |bytes| Ok::<_, ()>(bytes),
        );
        parser.parse(input, Cursor::start()).unwrap().1
    }
    let input = vec![0x12, 0x34, 0x56];
    assert!(std::ptr::eq(borrowed(&input), &input[..2]));
}
