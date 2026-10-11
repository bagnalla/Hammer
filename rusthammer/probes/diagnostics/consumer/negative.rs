// Original source forms retained to isolate extraction limitations.
use super::*;

pub fn located(input: &[u8], context: ParseContext) -> (ParseOutcome<Owned>, Report<'static>) {
    let parser = labelled(
        Map {
            parser: ByteEq(b'A'),
            map: |byte| Owned(byte),
        },
        Label {
            name: "tag",
            source: Some(Source {
                file: file!(),
                line: line!(),
                column: column!(),
            }),
        },
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

pub fn effects(input: &[u8], context: ParseContext) -> (ParseOutcome<u8>, u32, Report<'static>) {
    let parser = scoped(Choice {
        first: Counted(ByteEq(b'A')),
        second: Counted(ByteEq(b'B')),
    });
    let mut session = Session {
        backend: 0,
        observer: Collect {
            report: Report::empty(),
        },
    };
    let result = parser.eval(&mut session, input, Cursor::start(), context);
    (result, session.backend, session.observer.report)
}
