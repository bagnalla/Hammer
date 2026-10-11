//! Private diagnostic instrumentation experiment, not a production API.
#![no_std]

use rusthammer::{Byte, Cursor, Eval, Grammar, ParseContext, ParseError, ParseOutcome};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Source<'meta> {
    pub file: &'meta str,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Label<'meta> {
    pub name: &'meta str,
    pub source: Option<Source<'meta>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Issue {
    Rejected(ParseError),
    Incomplete,
}

// Classification takes precedence over input distance. In particular, a fatal
// error or NeedMore in the second arm must displace an earlier recoverable error.
pub fn priority(issue: Issue) -> u8 {
    match issue {
        Issue::Incomplete => 1,
        Issue::Rejected(error) => {
            if error.is_recoverable() {
                0
            } else {
                2
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expected {
    Byte(u8),
    Unspecified,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Failure<'meta> {
    pub at: Cursor,
    // False means this is an opaque parser's invocation boundary, NOT a known
    // failure position. A generic wrapper cannot infer a child's internal cursor.
    pub exact: bool,
    pub issue: Issue,
    pub expected: Expected,
    pub inner: Option<Label<'meta>>,
    pub outer: Option<Label<'meta>>,
    pub labels_truncated: bool,
}

impl<'meta> Failure<'meta> {
    pub fn new(at: Cursor, exact: bool, issue: Issue, expected: Expected) -> Self {
        Self {
            at,
            exact,
            issue,
            expected,
            inner: None,
            outer: None,
            labels_truncated: false,
        }
    }

    fn annotate(&mut self, label: Label<'meta>) {
        if self.inner.is_none() {
            self.inner = Some(label);
        } else if self.outer.is_none() {
            self.outer = Some(label);
        } else {
            self.labels_truncated = true;
        }
    }
}

// Two alternatives and two labels are deliberately small probe capacities.
// Truncation is observable and never changes a ParseOutcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Report<'meta> {
    pub first: Option<Failure<'meta>>,
    pub second: Option<Failure<'meta>>,
    pub alternatives_truncated: bool,
}

impl<'meta> Report<'meta> {
    pub const fn empty() -> Self {
        Self {
            first: None,
            second: None,
            alternatives_truncated: false,
        }
    }

    pub fn insert(&mut self, failure: Failure<'meta>) {
        if let Some(current) = self.first {
            let old = priority(current.issue);
            let new = priority(failure.issue);
            let farther = failure.at.byte > current.at.byte
                || (failure.at.byte == current.at.byte && failure.at.bit > current.at.bit);
            if new > old || (new == old && farther) {
                self.first = Some(failure);
                self.second = None;
                self.alternatives_truncated = false;
            } else if new == old
                && failure.at.byte == current.at.byte
                && failure.at.bit == current.at.bit
            {
                if self.second.is_none() {
                    self.second = Some(failure);
                } else {
                    self.alternatives_truncated = true;
                }
            }
        } else {
            self.first = Some(failure);
        }
    }

    pub fn merge(&mut self, other: Self) {
        // Preserve the overflow flag only when the other report contributes to
        // the selected position/class; overflow at a discarded position is irrelevant.
        if let Some(first) = other.first {
            self.insert(first);
            if let Some(second) = other.second {
                self.insert(second);
            }
            if let Some(selected) = self.first {
                if priority(first.issue) == priority(selected.issue)
                    && first.at.byte == selected.at.byte
                    && first.at.bit == selected.at.bit
                {
                    self.alternatives_truncated |= other.alternatives_truncated;
                }
            }
        }
    }

    pub fn annotate(&mut self, label: Label<'meta>) {
        // Explicit reconstruction avoids borrowing through an Option payload.
        if let Some(mut first) = self.first {
            first.annotate(label);
            self.first = Some(first);
        }
        if let Some(mut second) = self.second {
            second.annotate(label);
            self.second = Some(second);
        }
    }
}

// Candidate hook shape. The associated mark is kept in the Rust call frame,
// allowing a zero-sized silent observer without a heap-allocated frame stack.
pub trait Observe<'meta> {
    type Mark;
    fn begin(&mut self) -> Self::Mark;
    fn finish(&mut self, mark: Self::Mark, keep: bool);
    fn record(&mut self, failure: Failure<'meta>);
    fn fallback(&mut self, at: Cursor, issue: Issue);
    fn annotate(&mut self, label: Label<'meta>);
}

#[derive(Clone, Copy)]
pub struct Silent;

impl<'meta> Observe<'meta> for Silent {
    // A unit-valued mark makes the pinned Aeneas emit an ill-typed dictionary.
    // Keep the no-op state zero-sized; the ignored Boolean mark passes both MIR
    // stages. See unit_mark.rs for the independent negative reproduction.
    type Mark = bool;
    fn begin(&mut self) -> bool {
        false
    }
    fn finish(&mut self, _: bool, _: bool) {}
    fn record(&mut self, _: Failure<'meta>) {}
    fn fallback(&mut self, _: Cursor, _: Issue) {}
    fn annotate(&mut self, _: Label<'meta>) {}
}

pub struct Collect<'meta> {
    pub report: Report<'meta>,
}

impl<'meta> Observe<'meta> for Collect<'meta> {
    type Mark = Report<'meta>;
    fn begin(&mut self) -> Self::Mark {
        let saved = self.report;
        self.report = Report::empty();
        saved
    }
    fn finish(&mut self, mut saved: Self::Mark, keep: bool) {
        if keep {
            saved.merge(self.report);
        }
        self.report = saved;
    }
    fn record(&mut self, failure: Failure<'meta>) {
        self.report.insert(failure);
    }
    fn fallback(&mut self, at: Cursor, issue: Issue) {
        let needed = match self.report.first {
            None => true,
            Some(current) => priority(current.issue) < priority(issue),
        };
        if needed {
            self.report
                .insert(Failure::new(at, false, issue, Expected::Unspecified));
        }
    }
    fn annotate(&mut self, label: Label<'meta>) {
        self.report.annotate(label);
    }
}

pub struct Session<B, O> {
    pub backend: B,
    pub observer: O,
}

// These operations touch only the observer. Hooks never get the user's backend
// state, output, callbacks, or input. Child calls still use the SAME Session.
pub fn close<'meta, B, O: Observe<'meta>, T>(
    session: &mut Session<B, O>,
    mark: O::Mark,
    result: ParseOutcome<T>,
) -> ParseOutcome<T> {
    let keep = match &result {
        ParseOutcome::Success(_, _) => false,
        _ => true,
    };
    session.observer.finish(mark, keep);
    result
}

pub fn decorate<'meta, B, O: Observe<'meta>, T>(
    session: &mut Session<B, O>,
    at: Cursor,
    label: Option<Label<'meta>>,
    result: ParseOutcome<T>,
) -> ParseOutcome<T> {
    let issue = match &result {
        ParseOutcome::Success(_, _) => None,
        ParseOutcome::Error(error) => Some(Issue::Rejected(*error)),
        ParseOutcome::NeedMore => Some(Issue::Incomplete),
    };
    if let Some(issue) = issue {
        session.observer.fallback(at, issue);
        if let Some(label) = label {
            session.observer.annotate(label);
        }
    }
    result
}

// Private stand-in for hooks that would live INSIDE production combinators.
// Wrapping only the root cannot suppress internal successful speculation.
pub struct Scoped<'meta, P> {
    pub parser: P,
    pub label: Option<Label<'meta>>,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for Scoped<'_, P> {
    type Output = P::Output;
}

impl<'meta, 'input, B, O: Observe<'meta>, P: Eval<'input, Session<B, O>>>
    Eval<'input, Session<B, O>> for Scoped<'meta, P>
{
    fn eval(
        &self,
        session: &mut Session<B, O>,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let mark = session.observer.begin();
        let result = self.parser.eval(session, input, cursor, context);
        let result = decorate(session, cursor, self.label, result);
        close(session, mark, result)
    }
}

pub fn scoped<'meta, P>(parser: P) -> Scoped<'meta, P> {
    Scoped {
        parser,
        label: None,
    }
}

pub fn labelled<'meta, P>(parser: P, label: Label<'meta>) -> Scoped<'meta, P> {
    Scoped {
        parser,
        label: Some(label),
    }
}

// A precisely instrumented leaf. Byte itself is the real production reader;
// the probe adds literal comparison and records the known failure location.
#[derive(Clone, Copy)]
pub struct ByteEq(pub u8);

impl<'input> Grammar<'input> for ByteEq {
    type Output = u8;
}

impl<'meta, 'input, B, O: Observe<'meta>> Eval<'input, Session<B, O>> for ByteEq {
    fn eval(
        &self,
        session: &mut Session<B, O>,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        let result = Byte.eval(session, input, cursor, context);
        observe_byte(session, cursor, input.len(), self.0, result)
    }
}

pub fn observe_byte<'meta, B, O: Observe<'meta>>(
    session: &mut Session<B, O>,
    cursor: Cursor,
    length: usize,
    expected: u8,
    result: ParseOutcome<u8>,
) -> ParseOutcome<u8> {
    let (at, issue, outcome) = match result {
        ParseOutcome::Success(next, byte) => {
            if byte == expected {
                return ParseOutcome::Success(next, byte);
            }
            (
                cursor,
                Issue::Rejected(ParseError::Mismatch),
                ParseOutcome::Error(ParseError::Mismatch),
            )
        }
        ParseOutcome::Error(error) => {
            let at = match error {
                ParseError::UnexpectedEnd => Cursor {
                    byte: length,
                    bit: 0,
                },
                _ => cursor,
            };
            (at, Issue::Rejected(error), ParseOutcome::Error(error))
        }
        ParseOutcome::NeedMore => (
            Cursor {
                byte: length,
                bit: 0,
            },
            Issue::Incomplete,
            ParseOutcome::NeedMore,
        ),
    };
    session
        .observer
        .record(Failure::new(at, true, issue, Expected::Byte(expected)));
    outcome
}

pub fn sample<'meta, 'input, O: Observe<'meta>>(
    observer: O,
    label: Label<'meta>,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> (ParseOutcome<u8>, Session<(), O>) {
    let mut session = Session {
        backend: (),
        observer,
    };
    let result = labelled(ByteEq(b'A'), label).eval(&mut session, input, cursor, context);
    (result, session)
}

pub fn run<'meta>(
    label: Label<'meta>,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> (ParseOutcome<u8>, Report<'meta>) {
    let (result, session) = sample(
        Collect {
            report: Report::empty(),
        },
        label,
        input,
        cursor,
        context,
    );
    (result, session.observer.report)
}

pub fn quiet(
    label: Label<'_>,
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<u8> {
    sample(Silent, label, input, cursor, context).0
}
