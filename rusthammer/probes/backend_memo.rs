//! Private backend/typed-cache feasibility probe; no public library API.
#![no_std]

extern crate alloc;
use alloc::vec::Vec;

#[allow(dead_code, unused_attributes)]
#[path = "../src/lib.rs"]
mod rusthammer;
use rusthammer::{Byte, BytePattern, Parser, TakeAligned};
pub use rusthammer::{Cursor, ParseContext, ParseError, ParseOutcome};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Key {
    pub cursor: Cursor,
    pub context: ParseContext,
}

pub struct Entry<T> {
    key: Key,
    // None denotes an active invocation, not a failed parse.
    outcome: Option<ParseOutcome<T>>,
}

pub fn copy_outcome<T: Clone>(outcome: &ParseOutcome<T>) -> ParseOutcome<T> {
    match outcome {
        ParseOutcome::Success(next, value) => ParseOutcome::Success(*next, value.clone()),
        ParseOutcome::Error(error) => ParseOutcome::Error(*error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

pub fn lookup<T: Clone>(table: &Vec<Entry<T>>, key: Key) -> Option<ParseOutcome<T>> {
    let mut index = 0;
    while index < table.len() {
        if table[index].key == key {
            return Some(match &table[index].outcome {
                Some(outcome) => copy_outcome(outcome),
                // A fatal diagnostic in this probe, never a recoverable seed.
                // The final backend needs a distinct recursion error and LR design.
                None => ParseOutcome::Error(ParseError::NonProgress),
            });
        }
        index += 1;
    }
    None
}

pub struct Direct;

pub struct Packrat<'input> {
    bytes: Vec<Entry<u8>>,
    payloads: Vec<Entry<&'input [u8]>>,
    counts: Vec<Entry<usize>>,
}

impl<'input> Packrat<'input> {
    fn new() -> Self {
        Self {
            bytes: Vec::new(),
            payloads: Vec::new(),
            counts: Vec::new(),
        }
    }
}

// The output is a property of the grammar, independent of its interpreter.
pub trait Grammar<'input> {
    type Output;
}

pub trait Eval<'input, Backend>: Grammar<'input> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output>;
}

pub struct ByteRule;
pub struct PayloadRule;
pub struct CountRule;
pub struct Seq<P, Q>(pub P, pub Q);
pub struct Choice<P, Q>(pub P, pub Q);
pub struct Tag(pub u8);
pub struct Map<P, F>(pub P, pub F);

// Intentionally neither Clone nor Copy.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
pub struct OwnedByte {
    pub value: u8,
}

impl<'input> Grammar<'input> for ByteRule {
    type Output = u8;
}
impl<'input> Grammar<'input> for PayloadRule {
    type Output = &'input [u8];
}
impl<'input> Grammar<'input> for CountRule {
    type Output = usize;
}
impl<'input> Grammar<'input> for Tag {
    type Output = u8;
}

impl<'input, P: Grammar<'input>, Q: Grammar<'input>> Grammar<'input> for Seq<P, Q> {
    type Output = (P::Output, Q::Output);
}

impl<'input, P: Grammar<'input>, Q: Grammar<'input, Output = P::Output>> Grammar<'input>
    for Choice<P, Q>
{
    type Output = P::Output;
}

impl<'input, P, F, T> Grammar<'input> for Map<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> T,
{
    type Output = T;
}

impl<'input, B, P, F, T> Eval<'input, B> for Map<P, F>
where
    P: Eval<'input, B>,
    F: Fn(P::Output) -> T,
{
    fn eval(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<T> {
        match self.0.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, (self.1)(value)),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

impl<'input> Eval<'input, Direct> for ByteRule {
    fn eval(
        &self,
        _: &mut Direct,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        Byte.parse_with(input, cursor, context)
    }
}

impl<'input> Eval<'input, Packrat<'input>> for ByteRule {
    fn eval(
        &self,
        backend: &mut Packrat<'input>,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        let key = Key { cursor, context };
        if let Some(outcome) = lookup(&backend.bytes, key) {
            return outcome;
        }
        let outcome = Byte.parse_with(input, cursor, context);
        backend.bytes.push(Entry {
            key,
            outcome: Some(copy_outcome(&outcome)),
        });
        outcome
    }
}

impl<'input> Eval<'input, Direct> for PayloadRule {
    fn eval(
        &self,
        _: &mut Direct,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<&'input [u8]> {
        TakeAligned { count: 2 }.parse_with(input, cursor, context)
    }
}

impl<'input> Eval<'input, Packrat<'input>> for PayloadRule {
    fn eval(
        &self,
        backend: &mut Packrat<'input>,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<&'input [u8]> {
        let key = Key { cursor, context };
        if let Some(outcome) = lookup(&backend.payloads, key) {
            return outcome;
        }
        let outcome = TakeAligned { count: 2 }.parse_with(input, cursor, context);
        backend.payloads.push(Entry {
            key,
            outcome: Some(copy_outcome(&outcome)),
        });
        outcome
    }
}

impl<'input, B> Eval<'input, B> for Tag
where
    ByteRule: Eval<'input, B, Output = u8>,
{
    fn eval(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        match ByteRule.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => {
                if value == self.0 {
                    ParseOutcome::Success(next, value)
                } else {
                    ParseOutcome::Error(ParseError::Mismatch)
                }
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

impl<'input, B, P: Eval<'input, B>, Q: Eval<'input, B>> Eval<'input, B> for Seq<P, Q> {
    fn eval(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.0.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, first) => {
                match self.1.eval(backend, input, next, context) {
                    ParseOutcome::Success(end, second) => {
                        ParseOutcome::Success(end, (first, second))
                    }
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                }
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

impl<'input, B, P: Eval<'input, B>, Q: Eval<'input, B, Output = P::Output>> Eval<'input, B>
    for Choice<P, Q>
{
    fn eval(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.0.eval(backend, input, cursor, context) {
            ParseOutcome::Error(
                ParseError::Mismatch | ParseError::UnexpectedEnd | ParseError::TrailingInput,
            ) => self.1.eval(backend, input, cursor, context),
            outcome => outcome,
        }
    }
}

// Construct this once, then interpret the same tree using either backend.
fn grammar() -> Choice<Seq<PayloadRule, Tag>, Seq<PayloadRule, Tag>> {
    Choice(Seq(PayloadRule, Tag(b'X')), Seq(PayloadRule, Tag(b'Y')))
}

pub fn direct(input: &[u8], context: ParseContext) -> ParseOutcome<(&[u8], u8)> {
    grammar().eval(&mut Direct, input, Cursor::start(), context)
}

pub fn packrat(input: &[u8], context: ParseContext) -> ParseOutcome<(&[u8], u8)> {
    grammar().eval(&mut Packrat::new(), input, Cursor::start(), context)
}

pub fn owned_output(input: &[u8], context: ParseContext) -> ParseOutcome<OwnedByte> {
    Map(ByteRule, |value| OwnedByte { value }).eval(
        &mut Packrat::new(),
        input,
        Cursor::start(),
        context,
    )
}

// Separate tables can retain independent input and grammar borrows. Each helper
// is private to this invocation, so its input and configured pattern stay fixed.
fn cached_payload<'input>(
    table: &mut Vec<Entry<&'input [u8]>>,
    input: &'input [u8],
    key: Key,
) -> ParseOutcome<&'input [u8]> {
    if let Some(outcome) = lookup(table, key) {
        return outcome;
    }
    let outcome = TakeAligned { count: 2 }.parse_with(input, key.cursor, key.context);
    table.push(Entry {
        key,
        outcome: Some(copy_outcome(&outcome)),
    });
    outcome
}

fn cached_pattern<'pattern>(
    table: &mut Vec<Entry<&'pattern [u8]>>,
    pattern: &'pattern [u8],
    input: &[u8],
    key: Key,
) -> ParseOutcome<&'pattern [u8]> {
    if let Some(outcome) = lookup(table, key) {
        return outcome;
    }
    let outcome = BytePattern::new(pattern).parse_with(input, key.cursor, key.context);
    table.push(Entry {
        key,
        outcome: Some(copy_outcome(&outcome)),
    });
    outcome
}

pub fn distinct_borrows<'input, 'pattern>(
    input: &'input [u8],
    pattern: &'pattern [u8],
    context: ParseContext,
) -> ParseOutcome<(&'input [u8], &'pattern [u8])> {
    let mut tables = (Vec::new(), Vec::new());
    let key = Key {
        cursor: Cursor::start(),
        context,
    };
    // Populate each table, then return values obtained by replaying both entries.
    let _ = cached_payload(&mut tables.0, input, key);
    let _ = cached_pattern(&mut tables.1, pattern, input, key);
    match cached_payload(&mut tables.0, input, key) {
        ParseOutcome::Success(_, payload) => {
            match cached_pattern(&mut tables.1, pattern, input, key) {
                ParseOutcome::Success(next, matched) => {
                    ParseOutcome::Success(next, (payload, matched))
                }
                ParseOutcome::Error(error) => ParseOutcome::Error(error),
                ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            }
        }
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

// Keep recursive calls in an ordinary function. The cache-policy dictionaries
// contain only table operations and do not depend on the recursive evaluator.
// See backend_recursive_trait.rs for the unsupported dictionary cycle.
pub trait CountMemo {
    fn recall(&self, key: Key) -> Option<ParseOutcome<usize>>;
    fn begin(&mut self, key: Key) -> Option<usize>;
    fn finish(&mut self, token: Option<usize>, outcome: &ParseOutcome<usize>);
}

impl CountMemo for Direct {
    fn recall(&self, _: Key) -> Option<ParseOutcome<usize>> {
        None
    }
    fn begin(&mut self, _: Key) -> Option<usize> {
        None
    }
    fn finish(&mut self, _: Option<usize>, _: &ParseOutcome<usize>) {}
}

impl CountMemo for Packrat<'_> {
    fn recall(&self, key: Key) -> Option<ParseOutcome<usize>> {
        lookup(&self.counts, key)
    }
    fn begin(&mut self, key: Key) -> Option<usize> {
        let index = self.counts.len();
        self.counts.push(Entry { key, outcome: None });
        Some(index)
    }
    fn finish(&mut self, token: Option<usize>, outcome: &ParseOutcome<usize>) {
        if let Some(index) = token {
            self.counts[index].outcome = Some(copy_outcome(outcome));
        }
    }
}

fn count_rule<'input, B: CountMemo>(
    backend: &mut B,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<usize>
where
    ByteRule: Eval<'input, B, Output = u8>,
{
    let key = Key { cursor, context };
    if let Some(outcome) = backend.recall(key) {
        return outcome;
    }
    let token = backend.begin(key);
    let outcome = match ByteRule.eval(backend, input, cursor, context) {
        ParseOutcome::Success(next, value) => {
            if value != b'a' {
                ParseOutcome::Success(cursor, 0)
            } else {
                match count_rule(backend, input, next, context) {
                    ParseOutcome::Success(end, count) => match count.checked_add(1) {
                        Some(total) => ParseOutcome::Success(end, total),
                        None => ParseOutcome::Error(ParseError::CountOverflow),
                    },
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                }
            }
        }
        ParseOutcome::Error(ParseError::UnexpectedEnd) => ParseOutcome::Success(cursor, 0),
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    };
    backend.finish(token, &outcome);
    outcome
}

impl<'input> Eval<'input, Direct> for CountRule {
    fn eval(
        &self,
        backend: &mut Direct,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<usize> {
        count_rule(backend, input, cursor, context)
    }
}

impl<'input> Eval<'input, Packrat<'input>> for CountRule {
    fn eval(
        &self,
        backend: &mut Packrat<'input>,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<usize> {
        count_rule(backend, input, cursor, context)
    }
}

pub fn recursive_direct(input: &[u8], context: ParseContext) -> ParseOutcome<usize> {
    CountRule.eval(&mut Direct, input, Cursor::start(), context)
}

pub fn recursive_packrat(input: &[u8], context: ParseContext) -> ParseOutcome<usize> {
    CountRule.eval(&mut Packrat::new(), input, Cursor::start(), context)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rusthammer::{BitOrder, ByteOrder, InputStatus, Order};

    fn contexts() -> [ParseContext; 8] {
        core::array::from_fn(|i| ParseContext {
            order: Order {
                bit: if i & 1 == 0 {
                    BitOrder::HighFirst
                } else {
                    BitOrder::LowFirst
                },
                byte: if i & 2 == 0 {
                    ByteOrder::Big
                } else {
                    ByteOrder::Little
                },
            },
            status: if i & 4 == 0 {
                InputStatus::Final
            } else {
                InputStatus::Partial
            },
        })
    }

    #[test]
    fn same_grammar_two_engines_and_shared_borrowed_result() {
        for context in contexts() {
            for input in [&b""[..], b"a", b"ab", b"abX", b"abY", b"abZ", b"abYtail"] {
                assert_eq!(direct(input, context), packrat(input, context));
            }
        }
        let input = *b"abY";
        let mut memo = Packrat::new();
        let result = grammar().eval(&mut memo, &input, Cursor::start(), ParseContext::FINAL);
        let ParseOutcome::Success(next, (payload, tag)) = result else {
            panic!()
        };
        assert_eq!(next, Cursor { byte: 3, bit: 0 });
        assert_eq!(tag, b'Y');
        assert_eq!(payload.as_ptr(), input.as_ptr());
        // The failed X arm and successful Y arm share both rule results.
        assert_eq!(memo.payloads.len(), 1);
        assert_eq!(memo.bytes.len(), 1);
    }

    #[test]
    fn context_and_cursor_are_part_of_the_key() {
        let input = [0xd6, 0x39, 0x81];
        let mut memo = Packrat::new();
        for bit in 0..8 {
            let cursor = Cursor { byte: 0, bit };
            for context in contexts() {
                let expected = ByteRule.eval(&mut Direct, &input, cursor, context);
                assert_eq!(ByteRule.eval(&mut memo, &input, cursor, context), expected);
                assert_eq!(ByteRule.eval(&mut memo, &input, cursor, context), expected);
            }
        }
        assert_eq!(memo.bytes.len(), 64);
    }

    #[test]
    fn failures_and_need_more_are_cached_and_retries_get_fresh_tables() {
        let mut memo = Packrat::new();
        let start = Cursor::start();
        for context in contexts() {
            let expected = ByteRule.eval(&mut Direct, &[], start, context);
            assert_eq!(ByteRule.eval(&mut memo, &[], start, context), expected);
            assert_eq!(ByteRule.eval(&mut memo, &[], start, context), expected);
        }
        assert_eq!(memo.bytes.len(), 8);
        let invalid = Cursor {
            byte: usize::MAX,
            bit: 9,
        };
        assert_eq!(
            ByteRule.eval(&mut memo, &[], invalid, ParseContext::PARTIAL),
            ParseOutcome::Error(ParseError::InvalidCursor)
        );
        assert_eq!(
            ByteRule.eval(&mut memo, &[], invalid, ParseContext::PARTIAL),
            ParseOutcome::Error(ParseError::InvalidCursor)
        );
        assert_eq!(memo.bytes.len(), 9);
        assert_eq!(
            packrat(b"ab", ParseContext::PARTIAL),
            ParseOutcome::NeedMore
        );
        assert!(matches!(
            packrat(b"abY", ParseContext::PARTIAL),
            ParseOutcome::Success(_, _)
        ));
    }

    #[test]
    fn output_need_not_be_clone() {
        assert_eq!(
            owned_output(b"x", ParseContext::FINAL),
            ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, OwnedByte { value: b'x' })
        );
    }

    #[test]
    fn cache_replay_preserves_independent_input_and_pattern_borrows() {
        let input = alloc::vec![b'a', b'b'];
        let pattern = alloc::vec![b'a', b'b'];
        let ParseOutcome::Success(_, (payload, matched)) =
            distinct_borrows(&input, &pattern, ParseContext::FINAL)
        else {
            panic!()
        };
        assert_eq!(payload.as_ptr(), input.as_ptr());
        assert_eq!(matched.as_ptr(), pattern.as_ptr());
        assert_ne!(payload.as_ptr(), matched.as_ptr());
    }

    #[test]
    fn recursive_calls_use_the_same_backend() {
        for context in contexts() {
            for input in [&b""[..], b"a", b"aa", b"aaa", b"aaa!", b"!aaa"] {
                assert_eq!(
                    recursive_direct(input, context),
                    recursive_packrat(input, context)
                );
            }
        }
        let mut memo = Packrat::new();
        let input = b"aaa!";
        let result = CountRule.eval(&mut memo, input, Cursor::start(), ParseContext::FINAL);
        assert_eq!(result, ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, 3));
        assert_eq!(memo.counts.len(), 4);
        assert_eq!(
            CountRule.eval(
                &mut memo,
                input,
                Cursor { byte: 1, bit: 0 },
                ParseContext::FINAL
            ),
            ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, 2)
        );
        assert_eq!(memo.counts.len(), 4);
    }

    #[test]
    fn an_active_entry_is_fatal_in_this_probe() {
        let mut memo = Packrat::new();
        memo.counts.push(Entry {
            key: Key {
                cursor: Cursor::start(),
                context: ParseContext::FINAL,
            },
            outcome: None,
        });
        assert_eq!(
            CountRule.eval(&mut memo, b"a", Cursor::start(), ParseContext::FINAL),
            ParseOutcome::Error(ParseError::NonProgress)
        );
    }
}
