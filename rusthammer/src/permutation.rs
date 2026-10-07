use crate::{Cursor, Eval, Grammar, Optional, ParseContext, ParseError, ParseOutcome};

/// Mark a parser as a required entry in a permutation.
///
/// Every success fills this entry, including an empty success or an `Option::None`
/// value. Outside a permutation this wrapper delegates to its child unchanged.
#[derive(Clone, Copy)]
pub struct Required<P> {
    pub parser: P,
}

/// Construct a required permutation entry without executing the child.
pub const fn required<P>(parser: P) -> Required<P> {
    Required { parser }
}

impl<'input, P: Grammar<'input>> Grammar<'input> for Required<P> {
    type Output = P::Output;
}

impl<'input, B, P: Eval<'input, B>> Eval<'input, B> for Required<P> {
    fn eval(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<P::Output> {
        self.parser.eval(backend, input, cursor, context)
    }
}

/// Parse a tuple of required and optional entries in any input order.
///
/// Return values in tuple/declaration order. At each position, try unmatched
/// entries in that order; backtrack to another entry if a successful match leaves
/// no matching ordering of the remaining entries. Child parsers retain their own
/// choice semantics: permutation retries entries, not the alternatives inside a
/// successful child.
///
/// Use `required(p)` for required entries and `optional(p)` for optional entries.
/// Optional absence is considered only when every remaining entry rejects
/// recoverably and is optional. An empty actual success still fills its entry.
/// `NeedMore` and fatal errors propagate immediately. Exhausting the possible
/// orderings returns recoverable `Mismatch`.
///
/// Tuples of zero through twelve entries are supported. No heap allocation or
/// output cloning is required. An empty tuple succeeds without validating the
/// cursor. The finite search terminates if each attempted child terminates;
/// ambiguous grammars can require factorial work. The implementation uses the
/// call stack. Backtracking drops speculative outputs and restores the cursor,
/// while preserving backend state and callback effects.
///
/// ```
/// use rusthammer::{permutation, required, BytePattern, Cursor, Parser};
/// let parser = permutation((
///     required(BytePattern::new(b"a")),
///     required(BytePattern::new(b"ab")),
/// ));
/// // Matching "a" first would leave "ba", so the search retries "ab" first.
/// assert_eq!(parser.parse(b"aba", Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, (&b"a"[..], &b"ab"[..]))));
/// ```
///
/// Entries must state whether they are required or optional:
///
/// ```compile_fail
/// use rusthammer::{permutation, Byte, Cursor, Parser};
/// let _ = permutation((Byte, Byte)).parse(b"ab", Cursor::start());
/// ```
#[derive(Clone, Copy)]
pub struct Permutation<T> {
    pub items: T,
}

/// Construct a permutation from a tuple of `required(p)` and `optional(p)` entries.
/// Neither child evaluation nor callbacks run during construction.
pub const fn permutation<T>(items: T) -> Permutation<T> {
    Permutation { items }
}

pub struct Slot<T> {
    matched: bool,
    value: Option<T>,
}

fn empty_slot<T>() -> Slot<T> {
    Slot {
        matched: false,
        value: None,
    }
}

fn slot_value<T>(slot: Slot<T>) -> Result<T, ParseError> {
    match slot.value {
        Some(value) => Ok(value),
        None => Err(ParseError::Mismatch),
    }
}

pub enum Attempt {
    Matched(Cursor),
    Absent,
    Error(ParseError),
    NeedMore,
}

fn required_slot<T>(result: ParseOutcome<T>) -> (Attempt, Slot<T>) {
    match result {
        ParseOutcome::Success(next, value) => (
            Attempt::Matched(next),
            Slot {
                matched: true,
                value: Some(value),
            },
        ),
        ParseOutcome::NeedMore => (Attempt::NeedMore, empty_slot()),
        ParseOutcome::Error(error) => (Attempt::Error(error), empty_slot()),
    }
}

fn optional_slot<T>(result: ParseOutcome<T>) -> (Attempt, Slot<Option<T>>) {
    match result {
        ParseOutcome::Success(next, value) => (
            Attempt::Matched(next),
            Slot {
                matched: true,
                value: Some(Some(value)),
            },
        ),
        ParseOutcome::NeedMore => (Attempt::NeedMore, empty_slot()),
        ParseOutcome::Error(error) => {
            if error.is_recoverable() {
                (
                    Attempt::Absent,
                    Slot {
                        matched: false,
                        value: Some(None),
                    },
                )
            } else {
                (Attempt::Error(error), empty_slot())
            }
        }
    }
}

pub trait ItemEval<'input, B>: Grammar<'input> {
    fn eval_slot(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> (Attempt, Slot<Self::Output>);
}

impl<'input, B, P: Eval<'input, B>> ItemEval<'input, B> for Required<P> {
    fn eval_slot(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> (Attempt, Slot<P::Output>) {
        required_slot(self.parser.eval(backend, input, cursor, context))
    }
}

impl<'input, B, P: Eval<'input, B>> ItemEval<'input, B> for Optional<P> {
    fn eval_slot(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> (Attempt, Slot<Option<P::Output>>) {
        optional_slot(self.parser.eval(backend, input, cursor, context))
    }
}

pub trait Layout<'input> {
    type State;
    type Output;
    fn count(&self) -> usize;
    fn empty(&self) -> Self::State;
    fn matched(&self, state: &Self::State, index: usize) -> bool;
    fn clear(&self, state: Self::State, index: usize) -> Self::State;
    fn finish(&self, state: Self::State) -> Result<Self::Output, ParseError>;
}

pub trait Items<'input, B>: Layout<'input> {
    fn attempt(
        &self,
        state: Self::State,
        index: usize,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> (Attempt, Self::State);
}

impl Layout<'_> for () {
    type State = ();
    type Output = ();
    fn count(&self) -> usize {
        0
    }
    fn empty(&self) {}
    fn matched(&self, _: &(), _: usize) -> bool {
        false
    }
    fn clear(&self, _: (), _: usize) {}
    fn finish(&self, _: ()) -> Result<(), ParseError> {
        Ok(())
    }
}

impl<B> Items<'_, B> for () {
    fn attempt(
        &self,
        state: (),
        _: usize,
        _: &mut B,
        _: &[u8],
        _: Cursor,
        _: ParseContext,
    ) -> (Attempt, ()) {
        (Attempt::Error(ParseError::Mismatch), state)
    }
}

macro_rules! tuple_items {
    ($count:literal; $($index:tt : $P:ident : $value:ident),+) => {
        impl<'input, $($P: Grammar<'input>),+> Layout<'input> for ($($P,)+) {
            type State = ($(Slot<$P::Output>,)+);
            type Output = ($($P::Output,)+);
            fn count(&self) -> usize { $count }
            fn empty(&self) -> Self::State { ($(empty_slot::<$P::Output>(),)+) }
            fn matched(&self, state: &Self::State, index: usize) -> bool {
                match index { $($index => state.$index.matched,)+ _ => false }
            }
            fn clear(&self, mut state: Self::State, index: usize) -> Self::State {
                match index { $($index => state.$index = empty_slot(),)+ _ => () }
                state
            }
            fn finish(&self, state: Self::State) -> Result<Self::Output, ParseError> {
                let ($($value,)+) = state;
                $(let $value = match slot_value($value) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };)+
                Ok(($($value,)+))
            }
        }
        impl<'input, B, $($P: ItemEval<'input, B>),+> Items<'input, B> for ($($P,)+) {
            fn attempt(&self, mut state: Self::State, index: usize, backend: &mut B,
                input: &'input [u8], cursor: Cursor, context: ParseContext) -> (Attempt, Self::State) {
                let result = match index {
                    $($index => {
                        let (result, slot) = self.$index.eval_slot(backend, input, cursor, context);
                        state.$index = slot;
                        result
                    },)+
                    _ => Attempt::Error(ParseError::Mismatch),
                };
                (result, state)
            }
        }
    };
}

tuple_items!(1; 0:P:p);
tuple_items!(2; 0:P:p, 1:Q:q);
tuple_items!(3; 0:P:p, 1:Q:q, 2:R:r);
tuple_items!(4; 0:P:p, 1:Q:q, 2:R:r, 3:S:s);
tuple_items!(5; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t);
tuple_items!(6; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t, 5:U:u);
tuple_items!(7; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t, 5:U:u, 6:V:v);
tuple_items!(8; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t, 5:U:u, 6:V:v, 7:W:w);
tuple_items!(9; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t, 5:U:u, 6:V:v, 7:W:w, 8:X:x);
tuple_items!(10; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t, 5:U:u, 6:V:v, 7:W:w, 8:X:x, 9:Y:y);
tuple_items!(11; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t, 5:U:u, 6:V:v, 7:W:w, 8:X:x, 9:Y:y, 10:Z:z);
tuple_items!(12; 0:P:p, 1:Q:q, 2:R:r, 3:S:s, 4:T:t, 5:U:u, 6:V:v, 7:W:w, 8:X:x, 9:Y:y, 10:Z:z, 11:A:a);

fn search<'input, B, L: Items<'input, B>>(
    items: &L,
    state: L::State,
    remaining: usize,
    backend: &mut B,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    index: usize,
    all_absent: bool,
) -> (ParseOutcome<()>, L::State) {
    if remaining == 0 {
        return (ParseOutcome::Success(cursor, ()), state);
    }
    if index >= items.count() {
        return if all_absent {
            (ParseOutcome::Success(cursor, ()), state)
        } else {
            (ParseOutcome::Error(ParseError::Mismatch), state)
        };
    }
    if items.matched(&state, index) {
        return search(
            items,
            state,
            remaining,
            backend,
            input,
            cursor,
            context,
            index + 1,
            all_absent,
        );
    }
    let (attempt, state) = items.attempt(state, index, backend, input, cursor, context);
    match attempt {
        Attempt::NeedMore => (ParseOutcome::NeedMore, state),
        Attempt::Error(error) => {
            if error.is_recoverable() {
                search(
                    items,
                    state,
                    remaining,
                    backend,
                    input,
                    cursor,
                    context,
                    index + 1,
                    false,
                )
            } else {
                (ParseOutcome::Error(error), state)
            }
        }
        Attempt::Absent => search(
            items,
            state,
            remaining,
            backend,
            input,
            cursor,
            context,
            index + 1,
            all_absent,
        ),
        Attempt::Matched(next) => {
            let (result, state) = search(
                items,
                state,
                remaining - 1,
                backend,
                input,
                next,
                context,
                0,
                true,
            );
            match result {
                ParseOutcome::Error(error) => {
                    if error.is_recoverable() {
                        let state = items.clear(state, index);
                        search(
                            items,
                            state,
                            remaining,
                            backend,
                            input,
                            cursor,
                            context,
                            index + 1,
                            false,
                        )
                    } else {
                        (ParseOutcome::Error(error), state)
                    }
                }
                _ => (result, state),
            }
        }
    }
}

impl<'input, T: Layout<'input>> Grammar<'input> for Permutation<T> {
    type Output = T::Output;
}

impl<'input, B, T: Items<'input, B>> Eval<'input, B> for Permutation<T> {
    fn eval(
        &self,
        backend: &mut B,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<T::Output> {
        let (result, state) = search(
            &self.items,
            self.items.empty(),
            self.items.count(),
            backend,
            input,
            cursor,
            context,
            0,
            true,
        );
        match result {
            ParseOutcome::Success(next, ()) => match self.items.finish(state) {
                Ok(value) => ParseOutcome::Success(next, value),
                Err(error) => ParseOutcome::Error(error),
            },
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}
