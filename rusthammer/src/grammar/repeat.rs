use super::super::{
    ConfigError, Cursor, Eval, Grammar, ParseContext, ParseError, ParseOutcome, Right,
};

#[cfg(feature = "alloc")]
use super::super::alloc::vec::Vec;

/// Run a parser between inclusive count bounds, collecting typed outputs in order.
/// Available with the `alloc` feature; the application supplies the allocator.
///
/// Recoverable rejection stops successfully once the minimum is met, restoring
/// the cursor to before that attempt. Otherwise the error propagates. Fatal errors
/// and `NeedMore` always propagate, discarding previously collected values.
/// Reaching a finite maximum succeeds without attempting another child. Finite
/// repetition permits empty successes. Unbounded repetition validates its starting
/// and successful child cursors and requires strict forward progress, returning
/// `InvalidCursor` or `NonProgress` on violations. Another valid advancing success after
/// `usize::MAX` retained values returns `CountOverflow` before increment or push.
/// Outputs need neither `Copy` nor `Clone`; unit values are retained.
///
/// A zero maximum succeeds with an empty vector and the original cursor without
/// calling the child or validating the cursor. Otherwise cursor validation belongs
/// to the child for finite repetition, as in `Seq`. Storage grows only after successful iterations;
/// no capacity is reserved from the configured maximum.
/// Allocation failure follows `Vec` behavior and is not a parse error.
/// Cloning or copying this parser depends only on its child parser, not its
/// `Vec` output. Each parse constructs a new output vector.
///
/// ```
/// use rusthammer::{Bit, Cursor, Parser, Repeat, Seq};
///
/// let bits = Repeat::exact(Bit, 2);
/// let pairs = Seq { first: bits, second: bits };
/// assert_eq!(pairs.parse(&[0xb0], Cursor::start()),
///     Ok((Cursor { byte: 0, bit: 4 }, (vec![true, false], vec![true, true]))));
/// ```
///
/// ```compile_fail,E0451
/// let parser = rusthammer::Repeat {
///     parser: rusthammer::End, ..rusthammer::Repeat::exact(rusthammer::End, 1)
/// };
/// ```
///
/// ```compile_fail,E0616
/// let mut parser = rusthammer::Repeat::exact(rusthammer::End, 1);
/// parser.bounds.min = 2;
/// ```
#[cfg(feature = "alloc")]
#[derive(Clone, Copy)]
pub struct Repeat<P> {
    parser: P,
    bounds: RepeatBounds,
}

#[cfg(feature = "alloc")]
impl<P> Repeat<P> {
    /// Construct inclusive finite bounds, rejecting `min > max` with `InvalidBounds`.
    pub fn new(parser: P, min: usize, max: usize) -> Result<Self, ConfigError> {
        let bounds = RepeatBounds::new(min, max)?;
        Ok(Self { parser, bounds })
    }

    /// Require exactly `count` successes. Every `usize` count is valid.
    pub fn exact(parser: P, count: usize) -> Self {
        Self {
            parser,
            bounds: RepeatBounds::exact(count),
        }
    }

    /// Require at least `min` successes, with no configured maximum.
    /// Every successful child must advance within the input, even after `min`
    /// is met. Recoverable rejection stops repetition; `NeedMore` still propagates.
    pub fn at_least(parser: P, min: usize) -> Self {
        Self {
            parser,
            bounds: RepeatBounds::at_least(min),
        }
    }

    /// Return the inclusive minimum count.
    pub const fn min(&self) -> usize {
        self.bounds.min
    }

    /// Return the inclusive maximum, or `None` for an unbounded repetition.
    pub const fn max(&self) -> Option<usize> {
        self.bounds.max
    }
}

/// Repeat a parser, folding its outputs into one value without allocating storage.
///
/// The count bounds and stopping rules are the same as for `Repeat`: finite
/// repetition permits empty successes, while unbounded repetition requires valid,
/// strictly advancing cursors. Recoverable rejection stops after the minimum;
/// fatal errors and `NeedMore` always propagate. The cursor rolls back to before
/// the rejected attempt. Reaching the maximum makes no further child call.
///
/// `init` creates a fresh accumulator once per parse, including a zero maximum.
/// An invalid unbounded starting cursor is rejected before calling it. `fold`
/// takes ownership of the accumulator and each accepted output in order, after
/// progress and count checks. Neither type needs `Copy` or `Clone`. On error or
/// `NeedMore`, the accumulator is discarded. Retrying a parse initializes again;
/// this combinator does not retain partial state between calls.
///
/// The driver uses no allocation; callbacks and child parsers may allocate.
/// Verification requires contracts for both callbacks: `Fn` alone does not imply
/// purity, termination, or freedom from panics. Backtracking does not undo callback
/// side effects. Copying this parser depends only on its stored child and callbacks.
///
/// ```
/// use rusthammer::{Bits, Cursor, FoldRepeat, Parser};
///
/// let checksum = FoldRepeat::exact(Bits::new(8).unwrap(), 3,
///     || 0u64, |sum, byte| sum ^ byte);
/// assert_eq!(checksum.parse(b"abc", Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, 0x60)));
/// ```
///
/// ```compile_fail,E0616
/// let mut parser = rusthammer::FoldRepeat::exact(rusthammer::Bit, 1,
///     || 0u8, |count: u8, _: bool| count + 1);
/// parser.bounds.min = 2;
/// ```
#[derive(Clone, Copy)]
pub struct FoldRepeat<P, I, F> {
    parser: P,
    bounds: RepeatBounds,
    init: I,
    fold: F,
}

impl<P, I, F> FoldRepeat<P, I, F> {
    /// Construct inclusive finite bounds, rejecting `min > max` with `InvalidBounds`.
    pub fn new(parser: P, min: usize, max: usize, init: I, fold: F) -> Result<Self, ConfigError> {
        let bounds = RepeatBounds::new(min, max)?;
        Ok(Self {
            parser,
            bounds,
            init,
            fold,
        })
    }

    /// Fold exactly `count` successes. Every `usize` count is valid.
    pub fn exact(parser: P, count: usize, init: I, fold: F) -> Self {
        Self {
            parser,
            bounds: RepeatBounds::exact(count),
            init,
            fold,
        }
    }

    /// Fold at least `min` successes, requiring progress, with no configured maximum.
    pub fn at_least(parser: P, min: usize, init: I, fold: F) -> Self {
        Self {
            parser,
            bounds: RepeatBounds::at_least(min),
            init,
            fold,
        }
    }

    /// Return the inclusive minimum count.
    pub const fn min(&self) -> usize {
        self.bounds.min
    }

    /// Return the inclusive maximum, or `None` for an unbounded repetition.
    pub const fn max(&self) -> Option<usize> {
        self.bounds.max
    }
}

/// Parse items separated by another parser, collecting only item outputs.
/// Available with `alloc`; separator outputs are discarded without requiring
/// either output type to implement `Copy` or `Clone`.
///
/// The first attempt parses only an item. Each later attempt parses a separator
/// and an item together. Recoverable rejection after the minimum rolls back the
/// whole attempt, leaving a trailing separator unconsumed. Fatal errors and
/// `NeedMore` always propagate. Reaching the maximum makes no separator call.
///
/// Counts refer to items. Finite repetition permits empty successes. Unbounded
/// repetition requires the first item and each complete separator/item pair to
/// advance to a valid cursor; the separator and following item need not each
/// advance individually. Progress and count checks match `Repeat`.
/// A zero maximum returns an empty vector without calling either parser or
/// validating the cursor. Storage and allocation behavior also match `Repeat`.
///
/// ```
/// use rusthammer::{Cursor, Literal, Parser, SepBy};
/// let letters = SepBy::at_least(Literal::new(8, 97).unwrap(),
///     Literal::new(8, 44).unwrap(), 1);
/// assert_eq!(letters.parse(b"a,a,", Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, vec![97, 97])));
/// ```
///
/// ```compile_fail,E0616
/// let mut parser = rusthammer::SepBy::exact(rusthammer::Bit, rusthammer::Bit, 1);
/// parser.bounds.min = 2;
/// ```
#[cfg(feature = "alloc")]
#[derive(Clone, Copy)]
pub struct SepBy<P, S> {
    parser: P,
    separator: S,
    bounds: RepeatBounds,
}

#[cfg(feature = "alloc")]
impl<P, S> SepBy<P, S> {
    /// Construct inclusive item-count bounds; `min > max` returns `InvalidBounds`.
    pub fn new(parser: P, separator: S, min: usize, max: usize) -> Result<Self, ConfigError> {
        let bounds = RepeatBounds::new(min, max)?;
        Ok(Self {
            parser,
            separator,
            bounds,
        })
    }

    /// Require exactly `count` items. Every `usize` count is valid.
    pub fn exact(parser: P, separator: S, count: usize) -> Self {
        Self {
            parser,
            separator,
            bounds: RepeatBounds::exact(count),
        }
    }

    /// Require at least `min` items, checking progress, without a finite maximum.
    /// Minima zero and one correspond to Hammer's `h_sepBy` and `h_sepBy1`.
    pub fn at_least(parser: P, separator: S, min: usize) -> Self {
        Self {
            parser,
            separator,
            bounds: RepeatBounds::at_least(min),
        }
    }

    /// Return the inclusive minimum item count.
    pub const fn min(&self) -> usize {
        self.bounds.min
    }

    /// Return the inclusive maximum item count, or `None` if unbounded.
    pub const fn max(&self) -> Option<usize> {
        self.bounds.max
    }
}

/// Parse separated items, folding their outputs without allocating storage.
///
/// The count, separator, rollback, and progress rules are the same as for `SepBy`.
/// Only item outputs enter the fold; separator outputs are discarded. `init`
/// creates a fresh accumulator once per parse, including a zero maximum, after
/// any unbounded starting-cursor check. `fold` consumes it and each retained item
/// after the progress/count checks. Outputs and accumulators need neither
/// `Copy` nor `Clone`. Parser copying depends only on the stored components.
///
/// Errors and `NeedMore` discard the accumulator. Retrying initializes again;
/// cursor rollback does not undo callback effects. Like `FoldRepeat`, the driver
/// allocates no storage, but children and callbacks may allocate. Verification
/// requires child and callback contracts, including termination and panic freedom.
///
/// ```
/// use rusthammer::{Cursor, FoldSepBy, Literal, Parser};
/// let count = FoldSepBy::at_least(Literal::new(8, 97).unwrap(),
///     Literal::new(8, 44).unwrap(), 0, || 0usize, |n, _| n + 1);
/// assert_eq!(count.parse(b"a,a!", Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, 2)));
/// ```
///
/// ```compile_fail,E0616
/// let mut parser = rusthammer::FoldSepBy::exact(rusthammer::Bit, rusthammer::Bit, 1,
///     || 0u8, |n: u8, _: bool| n + 1);
/// parser.bounds.min = 2;
/// ```
#[derive(Clone, Copy)]
pub struct FoldSepBy<P, S, I, F> {
    parser: P,
    separator: S,
    bounds: RepeatBounds,
    init: I,
    fold: F,
}

impl<P, S, I, F> FoldSepBy<P, S, I, F> {
    /// Construct inclusive item-count bounds; `min > max` returns `InvalidBounds`.
    pub fn new(
        parser: P,
        separator: S,
        min: usize,
        max: usize,
        init: I,
        fold: F,
    ) -> Result<Self, ConfigError> {
        let bounds = RepeatBounds::new(min, max)?;
        Ok(Self {
            parser,
            separator,
            bounds,
            init,
            fold,
        })
    }

    /// Fold exactly `count` items. Every `usize` count is valid.
    pub fn exact(parser: P, separator: S, count: usize, init: I, fold: F) -> Self {
        Self {
            parser,
            separator,
            bounds: RepeatBounds::exact(count),
            init,
            fold,
        }
    }

    /// Fold at least `min` items, checking progress, without a finite maximum.
    pub fn at_least(parser: P, separator: S, min: usize, init: I, fold: F) -> Self {
        Self {
            parser,
            separator,
            bounds: RepeatBounds::at_least(min),
            init,
            fold,
        }
    }

    /// Return the inclusive minimum item count.
    pub const fn min(&self) -> usize {
        self.bounds.min
    }

    /// Return the inclusive maximum item count, or `None` if unbounded.
    pub const fn max(&self) -> Option<usize> {
        self.bounds.max
    }
}

// All repetition combinators construct bounds through the same validation.
#[derive(Clone, Copy)]
struct RepeatBounds {
    min: usize,
    max: Option<usize>,
}

impl RepeatBounds {
    fn new(min: usize, max: usize) -> Result<Self, ConfigError> {
        if min > max {
            Err(ConfigError::InvalidBounds)
        } else {
            Ok(Self {
                min,
                max: Some(max),
            })
        }
    }

    fn exact(count: usize) -> Self {
        Self {
            min: count,
            max: Some(count),
        }
    }

    fn at_least(min: usize) -> Self {
        Self { min, max: None }
    }
}

// An internal storage policy: the driver alone decides which successes to retain.
trait RepeatAccumulator<A> {
    type Output;
    fn init(&self) -> Self::Output;
    fn step(&self, accumulated: Self::Output, value: A) -> Self::Output;
}

#[cfg(feature = "alloc")]
struct Collect;

#[cfg(feature = "alloc")]
impl<A> RepeatAccumulator<A> for Collect {
    type Output = Vec<A>;
    fn init(&self) -> Vec<A> {
        Vec::new()
    }
    fn step(&self, mut accumulated: Vec<A>, value: A) -> Vec<A> {
        accumulated.push(value);
        accumulated
    }
}

impl<P, I, F, A, R> RepeatAccumulator<A> for FoldRepeat<P, I, F>
where
    I: Fn() -> R,
    F: Fn(R, A) -> R,
{
    type Output = R;
    fn init(&self) -> R {
        (self.init)()
    }
    fn step(&self, accumulated: R, value: A) -> R {
        (self.fold)(accumulated, value)
    }
}

impl<P, S, I, F, A, R> RepeatAccumulator<A> for FoldSepBy<P, S, I, F>
where
    I: Fn() -> R,
    F: Fn(R, A) -> R,
{
    type Output = R;
    fn init(&self) -> R {
        (self.init)()
    }
    fn step(&self, accumulated: R, value: A) -> R {
        (self.fold)(accumulated, value)
    }
}

// Compare normalized cursors without computing a potentially overflowing bit index.
fn repeat_cursor_valid(input: &[u8], cursor: Cursor) -> bool {
    cursor.bit < 8 && (cursor.byte < input.len() || (cursor.byte == input.len() && cursor.bit == 0))
}

fn repeat_start(input: &[u8], cursor: Cursor, unbounded: bool) -> Result<(), ParseError> {
    if unbounded && !repeat_cursor_valid(input, cursor) {
        Err(ParseError::InvalidCursor)
    } else {
        Ok(())
    }
}

fn repeat_below_max(count: usize, max: Option<usize>) -> bool {
    match max {
        Some(max) => count < max,
        None => true,
    }
}

fn repeat_progress(input: &[u8], before: Cursor, after: Cursor) -> Result<(), ParseError> {
    if !repeat_cursor_valid(input, after) {
        return Err(ParseError::InvalidCursor);
    }
    if after.byte < before.byte || (after.byte == before.byte && after.bit <= before.bit) {
        return Err(ParseError::NonProgress);
    }
    Ok(())
}

fn repeat_next_count(count: usize) -> Result<usize, ParseError> {
    if count == usize::MAX {
        Err(ParseError::CountOverflow)
    } else {
        Ok(count + 1)
    }
}

#[cfg(feature = "alloc")]
impl<'input, P: Grammar<'input>> Grammar<'input> for Repeat<P> {
    type Output = Vec<P::Output>;
}

#[cfg(feature = "alloc")]
impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Repeat<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        repeat_run(
            backend,
            &self.parser,
            self.bounds,
            &Collect,
            input,
            cursor,
            context,
        )
    }
}

impl<'input, P, I, F, R> Grammar<'input> for FoldRepeat<P, I, F>
where
    P: Grammar<'input>,
    I: Fn() -> R,
    F: Fn(R, P::Output) -> R,
{
    type Output = R;
}

impl<'input, Backend, P, I, F, R> Eval<'input, Backend> for FoldRepeat<P, I, F>
where
    P: Eval<'input, Backend>,
    I: Fn() -> R,
    F: Fn(R, P::Output) -> R,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<R> {
        repeat_run(
            backend,
            &self.parser,
            self.bounds,
            self,
            input,
            cursor,
            context,
        )
    }
}

fn repeat_run<'input, Backend, P, A>(
    backend: &mut Backend,
    parser: &P,
    bounds: RepeatBounds,
    accumulator: &A,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<A::Output>
where
    P: Eval<'input, Backend>,
    A: RepeatAccumulator<P::Output>,
{
    repeat_run_with(
        backend,
        parser,
        parser,
        bounds,
        accumulator,
        input,
        cursor,
        context,
    )
}

#[cfg(feature = "alloc")]
impl<'input, P: Grammar<'input>, S: Grammar<'input>> Grammar<'input> for SepBy<P, S> {
    type Output = Vec<P::Output>;
}

#[cfg(feature = "alloc")]
impl<'input, Backend, P: Eval<'input, Backend>, S: Eval<'input, Backend>> Eval<'input, Backend>
    for SepBy<P, S>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let following = Right {
            first: &self.separator,
            second: &self.parser,
        };
        repeat_run_with(
            backend,
            &self.parser,
            &following,
            self.bounds,
            &Collect,
            input,
            cursor,
            context,
        )
    }
}

impl<'input, P, S, I, F, R> Grammar<'input> for FoldSepBy<P, S, I, F>
where
    P: Grammar<'input>,
    S: Grammar<'input>,
    I: Fn() -> R,
    F: Fn(R, P::Output) -> R,
{
    type Output = R;
}

impl<'input, Backend, P, S, I, F, R> Eval<'input, Backend> for FoldSepBy<P, S, I, F>
where
    P: Eval<'input, Backend>,
    S: Eval<'input, Backend>,
    I: Fn() -> R,
    F: Fn(R, P::Output) -> R,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<R> {
        let following = Right {
            first: &self.separator,
            second: &self.parser,
        };
        repeat_run_with(
            backend,
            &self.parser,
            &following,
            self.bounds,
            self,
            input,
            cursor,
            context,
        )
    }
}

// Choose by retained item count, not cursor position: finite empty items are valid.
fn repeat_parse<'input, Backend, P, Q>(
    backend: &mut Backend,
    parser: &P,
    following: &Q,
    count: usize,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<P::Output>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend, Output = P::Output>,
{
    if count == 0 {
        parser.eval(backend, input, cursor, context)
    } else {
        following.eval(backend, input, cursor, context)
    }
}

// The first item and all following attempts share one count/progress/storage loop.
// A separator/item pair is a single `Right` parser, so rejected pairs naturally
// leave `next` at the cursor before the separator.
fn repeat_run_with<'input, Backend, P, Q, A>(
    backend: &mut Backend,
    parser: &P,
    following: &Q,
    bounds: RepeatBounds,
    accumulator: &A,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<A::Output>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend, Output = P::Output>,
    A: RepeatAccumulator<P::Output>,
{
    let unbounded = bounds.max.is_none();
    if let Err(error) = repeat_start(input, cursor, unbounded) {
        return ParseOutcome::Error(error);
    }
    let mut values = accumulator.init();
    let mut next = cursor;
    let mut count = 0;
    // Keep the helper call inside `loop`: the pinned Aeneas prepass rejects
    // this call in a `while` condition combined with early returns.
    loop {
        if !repeat_below_max(count, bounds.max) {
            return ParseOutcome::Success(next, values);
        }
        match repeat_parse(backend, parser, following, count, input, next, context) {
            ParseOutcome::Success(after, value) => {
                if unbounded {
                    if let Err(error) = repeat_progress(input, next, after) {
                        return ParseOutcome::Error(error);
                    }
                }
                count = match repeat_next_count(count) {
                    Ok(count) => count,
                    Err(error) => return ParseOutcome::Error(error),
                };
                values = accumulator.step(values, value);
                next = after;
            }
            ParseOutcome::Error(error) => {
                if count >= bounds.min && error.is_recoverable() {
                    return ParseOutcome::Success(next, values);
                }
                return ParseOutcome::Error(error);
            }
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
        }
    }
}

#[cfg(test)]
mod repetition_count_tests {
    use super::{repeat_next_count, ParseError};

    #[test]
    fn last_representable_count_succeeds_then_reports_overflow() {
        assert_eq!(repeat_next_count(0), Ok(1));
        assert_eq!(repeat_next_count(usize::MAX - 1), Ok(usize::MAX));
        assert_eq!(
            repeat_next_count(usize::MAX),
            Err(ParseError::CountOverflow)
        );
    }
}
