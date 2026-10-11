//! Ordinary downstream extraction roots with independent metadata/input borrows.
#![no_std]

use rusthammer::{
    Choice, Cursor, Eval, Grammar, Map, ParseContext, ParseOutcome, Right, Seek, TakeAligned,
};
use rusthammer_diagnostic_probe::{
    labelled, scoped, ByteEq, Collect, Label, Report, Session, Source,
};

pub struct Owned(pub u8);

pub mod negative;

pub fn owned<'meta>(
    label: Label<'meta>,
    input: &[u8],
    context: ParseContext,
) -> (ParseOutcome<Owned>, Report<'meta>) {
    let parser = labelled(
        Map {
            parser: ByteEq(b'A'),
            map: |byte| Owned(byte),
        },
        label,
    );
    let mut session = Session {
        backend: (),
        observer: Collect {
            report: Report::empty(),
        },
    };
    let result = parser.eval(&mut session, input, Cursor::start(), context);
    (result, session.observer.report)
}

pub fn located(input: &[u8], context: ParseContext) -> (ParseOutcome<Owned>, Report<'static>) {
    owned(
        Label {
            name: "tag",
            source: Some(Source {
                file: file!(),
                line: line!(),
                column: column!(),
            }),
        },
        input,
        context,
    )
}

pub struct Counted<P>(pub P);
impl<'input, P: Grammar<'input>> Grammar<'input> for Counted<P> {
    type Output = P::Output;
}
impl<'input, O, P: Eval<'input, Session<u32, O>>> Eval<'input, Session<u32, O>> for Counted<P> {
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

pub fn effects<'meta>(
    label: Label<'meta>,
    input: &[u8],
    context: ParseContext,
) -> (ParseOutcome<u8>, u32, Report<'meta>) {
    let parser = labelled(
        Choice {
            first: Counted(ByteEq(b'A')),
            second: Counted(ByteEq(b'B')),
        },
        label,
    );
    let mut session = Session {
        backend: 0,
        observer: Collect {
            report: Report::empty(),
        },
    };
    let result = parser.eval(&mut session, input, Cursor::start(), context);
    (result, session.backend, session.observer.report)
}

pub fn alternatives<'meta>(
    label: Label<'meta>,
    input: &[u8],
    context: ParseContext,
) -> (ParseOutcome<u8>, Report<'meta>) {
    let parser = labelled(
        Choice {
            first: ByteEq(b'A'),
            second: ByteEq(b'B'),
        },
        label,
    );
    let mut session = Session {
        backend: (),
        observer: Collect {
            report: Report::empty(),
        },
    };
    let result = parser.eval(&mut session, input, Cursor::start(), context);
    (result, session.observer.report)
}

pub fn borrowed<'meta, 'input>(
    label: Label<'meta>,
    input: &'input [u8],
    context: ParseContext,
) -> (ParseOutcome<&'input [u8]>, Report<'meta>) {
    let parser = scoped(Right {
        first: labelled(ByteEq(b'A'), label),
        second: labelled(TakeAligned { count: 1 }, label),
    });
    let mut session = Session {
        backend: (),
        observer: Collect {
            report: Report::empty(),
        },
    };
    let result = parser.eval(&mut session, input, Cursor::start(), context);
    (result, session.observer.report)
}

pub fn backwards<'meta>(
    label: Label<'meta>,
    input: &[u8],
    context: ParseContext,
) -> (ParseOutcome<u8>, Report<'meta>) {
    let parser = labelled(
        Right {
            first: Seek::relative(-8),
            second: ByteEq(b'A'),
        },
        label,
    );
    let mut session = Session {
        backend: (),
        observer: Collect {
            report: Report::empty(),
        },
    };
    let result = parser.eval(&mut session, input, Cursor { byte: 1, bit: 0 }, context);
    (result, session.observer.report)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn owned_outputs_locations_and_backend_effects() {
        let (result, report) = located(b"A", ParseContext::FINAL);
        assert!(matches!(result, ParseOutcome::Success(_, Owned(b'A'))));
        assert!(report.first.is_none());
        let (_, report) = located(b"X", ParseContext::FINAL);
        let source = report.first.unwrap().inner.unwrap().source.unwrap();
        assert_eq!(source.file, file!());
        assert!(source.line > 0 && source.column > 0);
        let (_, calls, report) = effects(
            Label {
                name: "counted",
                source: None,
            },
            b"B",
            ParseContext::FINAL,
        );
        assert_eq!(calls, 2);
        assert!(report.first.is_none());
        let (result, _) = negative::located(b"A", ParseContext::FINAL);
        assert!(matches!(result, ParseOutcome::Success(_, Owned(b'A'))));
        let (_, calls, report) = negative::effects(b"B", ParseContext::FINAL);
        assert_eq!(calls, 2);
        assert!(report.first.is_none());
    }

    #[test]
    fn metadata_and_input_can_escape_independently() {
        let name = "borrowed";
        let label = Label { name, source: None };
        let report = {
            let input = [b'X'];
            alternatives(label, &input, ParseContext::FINAL).1
        };
        assert_eq!(report.first.unwrap().inner.unwrap().name, name);
        let input = [b'A', b'Z'];
        let outcome = {
            let local_name = [b'p', b'a', b'y'];
            let name = core::str::from_utf8(&local_name).unwrap();
            borrowed(Label { name, source: None }, &input, ParseContext::FINAL).0
        };
        assert_eq!(
            outcome,
            ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, &input[1..])
        );
        if let ParseOutcome::Success(_, bytes) = outcome {
            assert_eq!(bytes.as_ptr(), input[1..].as_ptr());
        }
    }

    #[test]
    fn seeking_reports_the_failed_read_not_the_entry() {
        let label = Label {
            name: "backwards",
            source: None,
        };
        let (result, report) = backwards(label, b"XX", ParseContext::FINAL);
        assert_eq!(
            result,
            ParseOutcome::Error(rusthammer::ParseError::Mismatch)
        );
        let failure = report.first.unwrap();
        assert_eq!(failure.at, Cursor::start());
        assert!(failure.exact);
    }
}
