//! Small, experimental parsing core for translation and verification with Aeneas.
//!
//! This prototype reads bits most-significant first. It does not yet implement
//! Hammer's configurable bit order, chunk buffering, recursion, or compiled backends.
//!
//! Parser values implement `Clone` and `Copy` when their stored children and
//! callbacks do. Parsed outputs need neither trait. For example, a copied grammar
//! can produce values that implement neither `Clone` nor `Copy`:
//!
//! ```
//! use rusthammer::{Bit, Cursor, Map, Parser, Seq};
//!
//! #[derive(Debug, PartialEq)]
//! struct Flag(bool);
//!
//! let flag = Map { parser: Bit, map: |bit| Flag(bit) };
//! let pair = Seq { first: flag, second: flag };
//! let copied = pair;
//! assert_eq!(copied.parse(&[0x80], Cursor::start()),
//!     Ok((Cursor { byte: 0, bit: 2 }, (Flag(true), Flag(false)))));
//! assert_eq!(pair.parse(&[0x80], Cursor::start()),
//!     copied.parse(&[0x80], Cursor::start()));
//! ```
//!
//! Copies duplicate the stored configuration; their cost grows with its size.
//! `clone()` delegates to each field's `Clone` implementation and may allocate
//! when a child or callback owns data. Shared parser references are another way
//! to reuse a grammar, including when its components implement neither trait.

#![no_std]
#![forbid(unsafe_code)]

use core::marker::PhantomData;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// A byte index and a bit offset measured from the most-significant bit.
///
/// Input-reading primitives validate cursors against their input. The canonical
/// end cursor is `(input.len(), 0)`; other positions beyond the input are invalid.
/// Empty grammars such as `Epsilon` do not inspect or validate the cursor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cursor {
    pub byte: usize,
    pub bit: u8,
}

impl Cursor {
    pub const fn start() -> Self {
        Self { byte: 0, bit: 0 }
    }
}

/// Invalid parameters supplied while constructing a parser, before parsing input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConfigError {
    /// The requested unsigned field width exceeds 64 bits.
    InvalidWidth,
    /// The expected literal value cannot be represented in its field width.
    InvalidLiteral,
    /// A repetition minimum exceeds its maximum.
    InvalidBounds,
}

/// Input rejection, invalid parser execution, or a repetition representation limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseError {
    InvalidCursor,
    UnexpectedEnd,
    Unaligned,
    Mismatch,
    TrailingInput,
    /// An unbounded repetition's successful child did not strictly advance the cursor.
    NonProgress,
    /// Another successful repetition would exceed the largest representable count.
    CountOverflow,
}

impl ParseError {
    /// Whether choice, optionality, and negative lookahead may recover from this
    /// rejection. Partial-input exhaustion uses `NeedMore` instead of an error.
    /// Cursor, alignment, progress, and count-limit errors always propagate.
    pub const fn is_recoverable(self) -> bool {
        match self {
            Self::Mismatch | Self::UnexpectedEnd | Self::TrailingInput => true,
            Self::InvalidCursor | Self::Unaligned | Self::NonProgress | Self::CountOverflow => {
                false
            }
        }
    }
}

/// Whether the supplied buffer contains all remaining input for this parse.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InputStatus {
    /// The buffer may be extended; its boundary is not end-of-input.
    Partial,
    /// No more input will be supplied for this parse.
    Final,
}

/// Parsing can finish, reject input, or await more input (or an end-of-input signal).
/// `NeedMore` has no committed cursor or output: retry with the accumulated buffer
/// at the original cursor. No input is retained by the parser.
#[derive(Debug, PartialEq, Eq)]
pub enum ParseOutcome<T> {
    Success(Cursor, T),
    Error(ParseError),
    NeedMore,
}

impl InputStatus {
    // Used only at primitive boundaries. Applying this to an entire complete
    // grammar would lose incomplete results already caught by its combinators.
    fn classify<T>(self, result: Result<(Cursor, T), ParseError>) -> ParseOutcome<T> {
        match result {
            Ok((next, value)) => ParseOutcome::Success(next, value),
            Err(ParseError::UnexpectedEnd) => match self {
                Self::Partial => ParseOutcome::NeedMore,
                Self::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
            },
            Err(error) => ParseOutcome::Error(error),
        }
    }
}

impl<T> ParseOutcome<T> {
    fn into_complete(self) -> Result<(Cursor, T), ParseError> {
        match self {
            Self::Success(next, value) => Ok((next, value)),
            Self::Error(error) => Err(error),
            // Built-in parsers never return NeedMore on final input. Keep the
            // complete API total even for custom parsers that violate that rule.
            Self::NeedMore => Err(ParseError::UnexpectedEnd),
        }
    }
}

/// A parser with an output type determined by its implementation.
///
/// Input and cursor are separate so outputs may borrow from the input without
/// also returning a borrowed input object through the generic interface.
pub trait Parser<'input> {
    type Output;

    /// Parse with explicit input finality. Implementations must propagate
    /// `NeedMore` before trying alternatives or deciding absence. On final input,
    /// they must return success or a parse error, never `NeedMore`.
    ///
    /// A partial parse can succeed without reaching EOF. To retry `NeedMore`,
    /// supply the accumulated input and the original cursor, not just the new
    /// chunk. Parsers retain no buffer or continuation. Retrying can rerun
    /// callbacks from successful prefixes; their effects are not rolled back.
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output>;

    /// Parse a complete buffer. Built-in combinators use this default unchanged;
    /// parser references forward any override from their underlying parser.
    /// A custom implementation's unexpected `NeedMore` becomes `UnexpectedEnd`.
    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parse_with(input, cursor, InputStatus::Final)
            .into_complete()
    }
}

/// Reuse a parser by shared reference, preserving both entry points and its output
/// type. The parser reference's lifetime is independent of the input lifetime.
impl<'input, P: Parser<'input>> Parser<'input> for &P {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        P::parse_with(*self, input, cursor, status)
    }

    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        P::parse(*self, input, cursor)
    }
}

/// Read one bit, advancing into the next byte after its least-significant bit.
/// All cursor values are checked; malformed input is an ordinary error.
pub fn read_bit(input: &[u8], cursor: Cursor) -> Result<(Cursor, bool), ParseError> {
    if cursor.bit >= 8 {
        return Err(ParseError::InvalidCursor);
    }
    if cursor.byte >= input.len() {
        return if cursor.byte == input.len() && cursor.bit == 0 {
            Err(ParseError::UnexpectedEnd)
        } else {
            Err(ParseError::InvalidCursor)
        };
    }

    let value = ((input[cursor.byte] >> (7 - cursor.bit)) & 1) != 0;
    let next = if cursor.bit == 7 {
        Cursor {
            byte: cursor.byte + 1,
            bit: 0,
        }
    } else {
        Cursor {
            byte: cursor.byte,
            bit: cursor.bit + 1,
        }
    };
    Ok((next, value))
}

#[derive(Clone, Copy)]
pub struct Bit;

impl<'input> Parser<'input> for Bit {
    type Output = bool;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<bool> {
        status.classify(read_bit(input, cursor))
    }
}

/// Read an unsigned, most-significant-first field of 0 through 64 bits.
///
/// Fields may start inside a byte and cross byte boundaries. Zero-width fields
/// return zero without consuming input, including at canonical end-of-input.
/// Construction validates the width; parsing validates the cursor even for an
/// empty field. The private width cannot be changed after construction.
///
/// ```compile_fail,E0451
/// let parser = rusthammer::Bits { width: 65 };
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bits {
    width: u8,
}

impl Bits {
    /// Construct a numeric field, rejecting widths above 64 with `InvalidWidth`.
    pub const fn new(width: u8) -> Result<Self, ConfigError> {
        if width > 64 {
            Err(ConfigError::InvalidWidth)
        } else {
            Ok(Self { width })
        }
    }

    /// Return the validated field width.
    pub const fn width(&self) -> u8 {
        self.width
    }
}

impl<'input> Parser<'input> for Bits {
    type Output = u64;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<u64> {
        status.classify(read_bits(input, cursor, self))
    }
}

/// Parse using an already validated numeric field, without implicit alignment.
pub fn read_bits(input: &[u8], cursor: Cursor, parser: &Bits) -> Result<(Cursor, u64), ParseError> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return Err(ParseError::InvalidCursor);
    }
    let mut next = cursor;
    let mut remaining = parser.width;
    let mut value = 0u64;
    while remaining != 0 {
        match read_bit(input, next) {
            Err(error) => return Err(error),
            Ok((after, bit)) => {
                // Before the final bit, the accumulator has at most 63 bits.
                value = value * 2 + if bit { 1 } else { 0 };
                next = after;
                remaining -= 1;
            }
        }
    }
    Ok((next, value))
}

/// Match an MSB-first numeric field against an expected value.
///
/// Construction checks that width is at most 64 and value fits that width.
/// The only valid zero-width literal is zero. Parsing does not recheck these
/// configuration constraints. It reads the whole field before comparing, so a
/// short partial prefix returns `NeedMore` even if its available bits differ.
///
/// ```compile_fail,E0616
/// let mut parser = rusthammer::Literal::new(3, 7).unwrap();
/// parser.value = 8;
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Literal {
    bits: Bits,
    value: u64,
}

impl Literal {
    /// Reject an unsupported width with `InvalidWidth`, then an unrepresentable
    /// expected value with `InvalidLiteral`.
    pub const fn new(width: u8, value: u64) -> Result<Self, ConfigError> {
        let bits = match Bits::new(width) {
            Ok(bits) => bits,
            Err(error) => return Err(error),
        };
        if width < 64 && value >= (1u64 << width) {
            Err(ConfigError::InvalidLiteral)
        } else {
            Ok(Self { bits, value })
        }
    }

    /// Return the validated field width.
    pub const fn width(&self) -> u8 {
        self.bits.width()
    }

    /// Return the expected value, which fits in the field width.
    pub const fn value(&self) -> u64 {
        self.value
    }
}

impl<'input> Parser<'input> for Literal {
    type Output = u64;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<u64> {
        status.classify(read_literal(input, cursor, self))
    }
}

fn read_literal(
    input: &[u8],
    cursor: Cursor,
    parser: &Literal,
) -> Result<(Cursor, u64), ParseError> {
    match read_bits(input, cursor, &parser.bits) {
        Err(error) => Err(error),
        Ok((next, value)) => {
            if value == parser.value {
                Ok((next, value))
            } else {
                Err(ParseError::Mismatch)
            }
        }
    }
}

/// Require canonical end-of-input, consuming nothing. Remaining bits, including
/// zero padding, produce `TrailingInput`; malformed cursors produce `InvalidCursor`.
/// At the boundary of partial input, return `NeedMore` until finality is known.
#[derive(Clone, Copy)]
pub struct End;

impl<'input> Parser<'input> for End {
    type Output = ();

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<()> {
        if cursor.bit >= 8
            || cursor.byte > input.len()
            || (cursor.byte == input.len() && cursor.bit != 0)
        {
            return ParseOutcome::Error(ParseError::InvalidCursor);
        }
        if cursor.byte == input.len() {
            match status {
                InputStatus::Final => ParseOutcome::Success(cursor, ()),
                InputStatus::Partial => ParseOutcome::NeedMore,
            }
        } else {
            ParseOutcome::Error(ParseError::TrailingInput)
        }
    }
}

/// Succeed with `()` without reading input or validating the supplied cursor.
/// Unlike `End`, this accepts at any position, including on partial input.
/// Unbounded repetition rejects this parser's empty success with `NonProgress`.
#[derive(Clone, Copy)]
pub struct Epsilon;

impl<'input> Parser<'input> for Epsilon {
    type Output = ();

    fn parse_with(&self, _: &'input [u8], cursor: Cursor, _: InputStatus) -> ParseOutcome<()> {
        ParseOutcome::Success(cursor, ())
    }
}

/// Always reject with recoverable `Mismatch`, without inspecting input or cursor.
/// `T` selects the output type for composition; no value of `T` is stored or made.
/// This zero-sized parser implements `Copy` and `Clone` for every output type.
pub struct Fail<T> {
    output: PhantomData<T>,
}

impl<T> Fail<T> {
    /// Construct a failing parser. There is no configuration to validate.
    pub const fn new() -> Self {
        Self {
            output: PhantomData,
        }
    }
}

impl<T> Default for Fail<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Copy for Fail<T> {}

impl<T> Clone for Fail<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'input, T> Parser<'input> for Fail<T> {
    type Output = T;

    fn parse_with(&self, _: &'input [u8], _: Cursor, _: InputStatus) -> ParseOutcome<T> {
        ParseOutcome::Error(ParseError::Mismatch)
    }
}

/// Run two parsers in order, returning their typed outputs as a pair.
/// Errors and `NeedMore` propagate unchanged. No caller-owned cursor is mutated.
#[derive(Clone, Copy)]
pub struct Seq<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Seq<P, Q> {
    type Output = (P::Output, Q::Output);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        match self.first.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::Success(next, first) => match self.second.parse_with(input, next, status)
            {
                ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                ParseOutcome::Error(error) => ParseOutcome::Error(error),
                ParseOutcome::Success(end, second) => ParseOutcome::Success(end, (first, second)),
            },
        }
    }
}

/// Run both parsers in order, keeping the first value and the final cursor.
/// Both children must succeed; errors and `NeedMore` propagate as in `Seq`.
/// Outputs are moved or discarded and need neither `Copy` nor `Clone`.
#[derive(Clone, Copy)]
pub struct Left<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Left<P, Q> {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.parse_with(input, cursor, status) {
            ParseOutcome::Success(next, (first, _)) => ParseOutcome::Success(next, first),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Run both parsers in order, keeping the second value and the final cursor.
/// Both children must succeed; errors and `NeedMore` propagate as in `Seq`.
/// Outputs are moved or discarded and need neither `Copy` nor `Clone`.
#[derive(Clone, Copy)]
pub struct Right<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Right<P, Q> {
    type Output = Q::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.parse_with(input, cursor, status) {
            ParseOutcome::Success(next, (_, second)) => ParseOutcome::Success(next, second),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Run `left`, `parser`, and `right` in order, keeping the middle value and the
/// final cursor. All three must succeed, including the discarded delimiters.
/// Errors and `NeedMore` propagate as in `Seq`; outputs need no `Copy` or `Clone`.
#[derive(Clone, Copy)]
pub struct Middle<L, P, R> {
    pub left: L,
    pub parser: P,
    pub right: R,
}

impl<'input, L: Parser<'input>, P: Parser<'input>, R: Parser<'input>> Parser<'input>
    for Middle<L, P, R>
{
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.left,
            second: Seq {
                first: &self.parser,
                second: &self.right,
            },
        };
        match sequence.parse_with(input, cursor, status) {
            ParseOutcome::Success(next, (_, (middle, _))) => ParseOutcome::Success(next, middle),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Run a parser, consuming its match and replacing its successful output with `()`.
/// Child errors and `NeedMore` propagate unchanged. The child still constructs
/// its output before it is discarded, including any allocations or callback effects.
#[derive(Clone, Copy)]
pub struct Ignore<P> {
    pub parser: P,
}

impl<'input, P: Parser<'input>> Parser<'input> for Ignore<P> {
    type Output = ();

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<()> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::Success(next, _) => ParseOutcome::Success(next, ()),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

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
/// let parser = rusthammer::Repeat { parser: rusthammer::End, min: 2, max: Some(1) };
/// ```
///
/// ```compile_fail,E0616
/// let mut parser = rusthammer::Repeat::exact(rusthammer::End, 1);
/// parser.min = 2;
/// ```
#[cfg(feature = "alloc")]
#[derive(Clone, Copy)]
pub struct Repeat<P> {
    parser: P,
    min: usize,
    max: Option<usize>,
}

#[cfg(feature = "alloc")]
impl<P> Repeat<P> {
    /// Construct inclusive finite bounds, rejecting `min > max` with `InvalidBounds`.
    pub fn new(parser: P, min: usize, max: usize) -> Result<Self, ConfigError> {
        if min > max {
            Err(ConfigError::InvalidBounds)
        } else {
            Ok(Self {
                parser,
                min,
                max: Some(max),
            })
        }
    }

    /// Require exactly `count` successes. Every `usize` count is valid.
    pub fn exact(parser: P, count: usize) -> Self {
        Self {
            parser,
            min: count,
            max: Some(count),
        }
    }

    /// Require at least `min` successes, with no configured maximum.
    /// Every successful child must advance within the input, even after `min`
    /// is met. Recoverable rejection stops repetition; `NeedMore` still propagates.
    pub fn at_least(parser: P, min: usize) -> Self {
        Self {
            parser,
            min,
            max: None,
        }
    }

    /// Return the inclusive minimum count.
    pub const fn min(&self) -> usize {
        self.min
    }

    /// Return the inclusive maximum, or `None` for an unbounded repetition.
    pub const fn max(&self) -> Option<usize> {
        self.max
    }
}

// Compare normalized cursors without computing a potentially overflowing bit index.
#[cfg(feature = "alloc")]
fn repeat_cursor_valid(input: &[u8], cursor: Cursor) -> bool {
    cursor.bit < 8 && (cursor.byte < input.len() || (cursor.byte == input.len() && cursor.bit == 0))
}

#[cfg(feature = "alloc")]
fn repeat_start(input: &[u8], cursor: Cursor, unbounded: bool) -> Result<(), ParseError> {
    if unbounded && !repeat_cursor_valid(input, cursor) {
        Err(ParseError::InvalidCursor)
    } else {
        Ok(())
    }
}

#[cfg(feature = "alloc")]
fn repeat_below_max(count: usize, max: Option<usize>) -> bool {
    match max {
        Some(max) => count < max,
        None => true,
    }
}

#[cfg(feature = "alloc")]
fn repeat_progress(input: &[u8], before: Cursor, after: Cursor) -> Result<(), ParseError> {
    if !repeat_cursor_valid(input, after) {
        return Err(ParseError::InvalidCursor);
    }
    if after.byte < before.byte || (after.byte == before.byte && after.bit <= before.bit) {
        return Err(ParseError::NonProgress);
    }
    Ok(())
}

#[cfg(feature = "alloc")]
fn repeat_next_count(count: usize) -> Result<usize, ParseError> {
    if count == usize::MAX {
        Err(ParseError::CountOverflow)
    } else {
        Ok(count + 1)
    }
}

#[cfg(feature = "alloc")]
impl<'input, P: Parser<'input>> Parser<'input> for Repeat<P> {
    type Output = Vec<P::Output>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        let unbounded = self.max.is_none();
        if let Err(error) = repeat_start(input, cursor, unbounded) {
            return ParseOutcome::Error(error);
        }
        let mut values = Vec::new();
        let mut next = cursor;
        let mut count = 0;
        // Keep the helper call inside `loop`: the pinned Aeneas prepass rejects
        // this call in a `while` condition combined with early returns.
        loop {
            if !repeat_below_max(count, self.max) {
                return ParseOutcome::Success(next, values);
            }
            match self.parser.parse_with(input, next, status) {
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
                    values.push(value);
                    next = after;
                }
                ParseOutcome::Error(error) => {
                    if count >= self.min && error.is_recoverable() {
                        return ParseOutcome::Success(next, values);
                    }
                    return ParseOutcome::Error(error);
                }
                ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
            }
        }
    }
}

/// Transform a successful output, preserving its cursor and all child errors.
///
/// The callback runs exactly once after success and never after a child error
/// or `NeedMore`.
/// Verification requires a contract for the callback; `Fn` alone does not imply
/// purity, termination, or freedom from panics.
#[derive(Clone, Copy)]
pub struct Map<P, F> {
    pub parser: P,
    pub map: F,
}

impl<'input, P, F, O> Parser<'input> for Map<P, F>
where
    P: Parser<'input>,
    F: Fn(P::Output) -> O,
{
    type Output = O;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, (self.map)(value)),
        }
    }
}

/// Transform a successful output with a checked conversion.
///
/// The callback consumes the child's value and runs exactly once after success.
/// `Ok(value)` preserves the child's cursor; `Err(_)` discards the conversion
/// error and returns recoverable `Mismatch`. Even a conversion error of type
/// `ParseError` is mapped to `Mismatch`, not propagated as a parser error.
/// Child errors and `NeedMore` propagate unchanged without calling the callback.
/// As with `Map`, verification requires a contract for the callback; callback
/// effects are not rolled back when conversion fails or a parse is retried.
#[derive(Clone, Copy)]
pub struct TryMap<P, F> {
    pub parser: P,
    pub map: F,
}

impl<'input, P, F, O, E> Parser<'input> for TryMap<P, F>
where
    P: Parser<'input>,
    F: Fn(P::Output) -> Result<O, E>,
{
    type Output = O;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::Success(next, value) => match (self.map)(value) {
                Ok(mapped) => ParseOutcome::Success(next, mapped),
                Err(_) => ParseOutcome::Error(ParseError::Mismatch),
            },
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Keep a successful output only when a predicate accepts it.
///
/// Rejection returns `Mismatch`; acceptance preserves the value and cursor.
/// Child errors and `NeedMore` propagate without calling the predicate. It borrows
/// the output, so non-`Copy` and borrowed outputs are supported. As with `Map`,
/// verification requires a contract for the callback.
#[derive(Clone, Copy)]
pub struct Verify<P, F> {
    pub parser: P,
    pub predicate: F,
}

impl<'input, P, F> Parser<'input> for Verify<P, F>
where
    P: Parser<'input>,
    F: Fn(&P::Output) -> bool,
{
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::Success(next, value) => {
                if (self.predicate)(&value) {
                    ParseOutcome::Success(next, value)
                } else {
                    ParseOutcome::Error(ParseError::Mismatch)
                }
            }
        }
    }
}

/// Ordered choice between parsers with the same output type.
///
/// The first success wins. After a recoverable failure, the second parser starts
/// at the original cursor and its result is returned unchanged. Other errors
/// propagate immediately. A later failure outside this choice does not revisit it.
/// `NeedMore` propagates immediately, preserving priority of the first alternative.
/// Cursor backtracking does not undo effects in custom parsers with interior state.
#[derive(Clone, Copy)]
pub struct Choice<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P, Q> Parser<'input> for Choice<P, Q>
where
    P: Parser<'input>,
    Q: Parser<'input, Output = P::Output>,
{
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        match self.first.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, value),
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    self.second.parse_with(input, cursor, status)
                } else {
                    ParseOutcome::Error(error)
                }
            }
        }
    }
}

/// Parse an optional value, preserving `NeedMore` on partial input.
///
/// Success preserves the child's cursor and wraps its output in `Some`.
/// Recoverable rejection returns `None` at the original cursor, even if the child
/// consumed a prefix before failing. Cursor and alignment errors propagate.
/// The child runs once; restoring the cursor does not undo custom parser effects.
#[derive(Clone, Copy)]
pub struct Optional<P> {
    pub parser: P,
}

impl<'input, P: Parser<'input>> Parser<'input> for Optional<P> {
    type Output = Option<P::Output>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, Some(value)),
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    ParseOutcome::Success(cursor, None)
                } else {
                    ParseOutcome::Error(error)
                }
            }
        }
    }
}

/// Positive lookahead, corresponding to Hammer's `h_and`.
///
/// Run the child once. Success returns `()` at the original cursor, discarding
/// the child's output. Every child error and `NeedMore` propagates unchanged. Lookahead restores
/// only the cursor; it does not undo effects in custom parsers with interior state.
#[derive(Clone, Copy)]
pub struct And<P> {
    pub parser: P,
}

impl<'input, P: Parser<'input>> Parser<'input> for And<P> {
    type Output = ();

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<()> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(_, _) => ParseOutcome::Success(cursor, ()),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
        }
    }
}

/// Negative lookahead, preserving `NeedMore` on partial input and corresponding to Hammer's `h_not`.
///
/// Run the child once. Child success returns `Mismatch`; recoverable rejection
/// returns `()` at the original cursor. Cursor and alignment errors propagate.
/// The child's value is discarded, and custom parser effects are not undone.
#[derive(Clone, Copy)]
pub struct Not<P> {
    pub parser: P,
}

impl<'input, P: Parser<'input>> Parser<'input> for Not<P> {
    type Output = ();

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<()> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(_, _) => ParseOutcome::Error(ParseError::Mismatch),
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    ParseOutcome::Success(cursor, ())
                } else {
                    ParseOutcome::Error(error)
                }
            }
        }
    }
}

/// Borrow an explicitly byte-aligned payload without copying.
///
/// This is not a replacement for Hammer's unaligned `h_bytes` primitive.
/// Every `usize` count is valid configuration; available input is checked per parse.
#[derive(Clone, Copy)]
pub struct TakeAligned {
    pub count: usize,
}

impl<'input> Parser<'input> for TakeAligned {
    type Output = &'input [u8];

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        status.classify(take_aligned(input, cursor, self.count))
    }
}

/// A toy three-bit header used to exercise typed parser composition.
#[derive(Debug, PartialEq, Eq)]
pub struct Flags {
    pub urgent: bool,
    pub encrypted: bool,
    pub compressed: bool,
}

/// Parse a header prefix, preserving every unconsumed bit.
pub fn parse_flags(input: &[u8], cursor: Cursor) -> Result<(Cursor, Flags), ParseError> {
    let parser = Map {
        parser: Seq {
            first: Bit,
            second: Seq {
                first: Bit,
                second: Bit,
            },
        },
        map: |(urgent, (encrypted, compressed))| Flags {
            urgent,
            encrypted,
            compressed,
        },
    };
    parser.parse(input, cursor)
}

/// Parse a byte-aligned payload with a borrowed output.
pub fn take_aligned(
    input: &[u8],
    cursor: Cursor,
    count: usize,
) -> Result<(Cursor, &[u8]), ParseError> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return Err(ParseError::InvalidCursor);
    }
    if cursor.bit != 0 {
        return Err(ParseError::Unaligned);
    }
    if count > input.len() - cursor.byte {
        return Err(ParseError::UnexpectedEnd);
    }
    let end = cursor.byte + count;
    Ok((Cursor { byte: end, bit: 0 }, &input[cursor.byte..end]))
}

/// A complete marker is either the two bytes `CA FE` or the single byte `CA`.
/// Build the grammar once, then reuse it. Partial input waits for confirmation of EOF.
#[derive(Clone, Copy)]
pub struct Marker {
    parser: Seq<Choice<Literal, Literal>, End>,
}

impl Marker {
    /// Construct both validated alternatives before parsing any input.
    /// The fixed constants are valid; the fallible return composes their constructors.
    pub fn new() -> Result<Self, ConfigError> {
        let first = match Literal::new(16, 0xcafe) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        let second = match Literal::new(8, 0xca) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        Ok(Self {
            parser: Seq {
                first: Choice { first, second },
                second: End,
            },
        })
    }
}

impl<'input> Parser<'input> for Marker {
    type Output = u64;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<u64> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::Success(next, (value, ())) => ParseOutcome::Success(next, value),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Parse using the already constructed marker grammar.
pub fn parse_marker(
    input: &[u8],
    cursor: Cursor,
    parser: &Marker,
) -> Result<(Cursor, u64), ParseError> {
    parser.parse(input, cursor)
}

/// Maximum payload length in the example record format, in bytes.
pub const MAX_RECORD_PAYLOAD: u64 = 1024;

/// A decoded record. The payload borrows the original input buffer.
#[derive(Debug, PartialEq, Eq)]
pub struct Record<'input> {
    pub version: u64,
    pub flags: u64,
    pub payload: &'input [u8],
}

/// A byte-aligned, complete record: 3-bit version, 5-bit flags, 16-bit length,
/// then exactly that many payload bytes. All fields are MSB-first.
///
/// Version must be 1; all five flag bits are available. Lengths above
/// `MAX_RECORD_PAYLOAD` are rejected with `Mismatch`. The complete three-byte
/// header is read before these constraints are checked. Trailing input is rejected.
/// Partial input waits for the remaining bytes or confirmation of EOF; call
/// `parse_with` again with the accumulated buffer and the original cursor.
#[derive(Clone, Copy)]
pub struct RecordParser {
    version: Bits,
    flags: Bits,
    length: Bits,
}

impl RecordParser {
    /// Validate the fixed field widths once, before any input is supplied.
    pub fn new() -> Result<Self, ConfigError> {
        let version = match Bits::new(3) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        let flags = match Bits::new(5) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        let length = match Bits::new(16) {
            Ok(parser) => parser,
            Err(error) => return Err(error),
        };
        Ok(Self {
            version,
            flags,
            length,
        })
    }
}

impl<'input> Parser<'input> for RecordParser {
    type Output = Record<'input>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        // An empty aligned read validates the cursor and alignment without advancing.
        match (TakeAligned { count: 0 }).parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => return ParseOutcome::Error(error),
            ParseOutcome::Success(_, _) => {}
        }
        let header = Verify {
            parser: Seq {
                first: self.version,
                second: Seq {
                    first: self.flags,
                    second: self.length,
                },
            },
            predicate: |fields: &(u64, (u64, u64))| {
                fields.0 == 1 && fields.1 .1 <= MAX_RECORD_PAYLOAD
            },
        };
        match header.parse_with(input, cursor, status) {
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::Success(next, (version, (flags, length))) => {
                // The verified bound fits usize on every supported Rust target.
                parse_record_body(input, next, version, flags, length as usize, status)
            }
        }
    }
}

fn parse_record_body(
    input: &[u8],
    cursor: Cursor,
    version: u64,
    flags: u64,
    count: usize,
    status: InputStatus,
) -> ParseOutcome<Record<'_>> {
    let body = Seq {
        first: TakeAligned { count },
        second: End,
    };
    match body.parse_with(input, cursor, status) {
        ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::Success(end, (payload, ())) => ParseOutcome::Success(
            end,
            Record {
                version,
                flags,
                payload,
            },
        ),
    }
}

/// Parse using an already constructed record grammar.
pub fn parse_record<'input>(
    input: &'input [u8],
    cursor: Cursor,
    parser: &RecordParser,
) -> Result<(Cursor, Record<'input>), ParseError> {
    parser.parse(input, cursor)
}

#[cfg(all(test, feature = "alloc"))]
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
