use rusthammer::{Eval, Grammar};
use std::cell::Cell;

use rusthammer::{
    Bit, Bits, Choice, Cursor, Map, ParseContext, ParseError, ParseOutcome, Parser, TakeAligned,
    Verify,
};

struct Reject(ParseError);

impl<'input> Grammar<'input> for Reject {
    type Output = bool;
}

impl<'input, Backend> Eval<'input, Backend> for Reject {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<bool> {
        ParseOutcome::Error(self.0)
    }
}

#[test]
fn mapping_calls_a_captured_callback_once_after_success() {
    let calls = Cell::new(0);
    let parser = Map {
        parser: Bit,
        map: |bit| {
            calls.set(calls.get() + 1);
            if bit { "set" } else { "clear" }.to_owned()
        },
    };
    let copied = parser;
    assert_eq!(
        copied.parse(&[0x80], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 1 }, "set".to_owned()))
    );
    assert_eq!(calls.get(), 1);
    assert_eq!(
        parser.parse(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(calls.get(), 1);
}

#[test]
fn mapping_preserves_every_child_error_without_calling_the_callback() {
    for error in [
        ParseError::InvalidCursor,
        ParseError::UnexpectedEnd,
        ParseError::Unaligned,
        ParseError::Mismatch,
        ParseError::TrailingInput,
    ] {
        let parser = Map {
            parser: Reject(error),
            map: |_| -> () { panic!("callback ran after a child error") },
        };
        assert_eq!(parser.parse(&[], Cursor::start()), Err(error));
    }
}

#[test]
fn mapping_can_preserve_borrowed_outputs() {
    let input = [0x12, 0x34];
    let parser = Map {
        parser: TakeAligned { count: 2 },
        map: |payload| (7u8, payload),
    };
    let (next, (tag, payload)) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 2, bit: 0 });
    assert_eq!(tag, 7);
    assert_eq!(payload, &input);
    assert_eq!(payload.as_ptr(), input.as_ptr());
}

#[test]
fn predicate_borrows_a_non_copy_output_and_runs_once() {
    let calls = Cell::new(0);
    let parser = Verify {
        parser: Map {
            parser: Bit,
            map: |bit| if bit { "yes" } else { "no" }.to_owned(),
        },
        predicate: |value: &String| {
            calls.set(calls.get() + 1);
            value == "yes"
        },
    };
    assert_eq!(
        parser.parse(&[0x80], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 1 }, "yes".to_owned()))
    );
    assert_eq!(calls.get(), 1);
    assert_eq!(
        parser.parse(&[0], Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(calls.get(), 2);
    assert_eq!(
        parser.parse(&[], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(calls.get(), 2);
}

#[test]
fn predicate_rejection_allows_choice_to_restart() {
    let parser = Choice {
        first: Verify {
            parser: Bits::new(8).unwrap(),
            predicate: |value: &u64| *value == 0xff,
        },
        second: Bits::new(1).unwrap(),
    };
    assert_eq!(
        parser.parse(&[0x80], Cursor::start()),
        Ok((Cursor { byte: 0, bit: 1 }, 1))
    );
}

#[test]
fn verification_preserves_borrowed_outputs_and_every_child_error() {
    let input = [0xca];
    let parser = Verify {
        parser: TakeAligned { count: 1 },
        predicate: |payload: &&[u8]| *payload == [0xca],
    };
    let (next, payload) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 1, bit: 0 });
    assert_eq!(payload.as_ptr(), input.as_ptr());

    for error in [
        ParseError::InvalidCursor,
        ParseError::UnexpectedEnd,
        ParseError::Unaligned,
        ParseError::Mismatch,
        ParseError::TrailingInput,
    ] {
        let parser = Verify {
            parser: Reject(error),
            predicate: |_: &bool| -> bool { panic!("predicate ran after a child error") },
        };
        assert_eq!(parser.parse(&[], Cursor::start()), Err(error));
    }
}
