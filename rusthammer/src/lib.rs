//! Small, experimental parsing core for translation and verification with Aeneas.
//!
//! Bit and byte ordering are configurable. Changes of bit direction require
//! byte-aligned scope boundaries. Chunk buffering, recursion, and compiled
//! backends are not implemented.
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

// Extract the same application code used by the examples and tests without
// adding example formats to the library API or ordinary builds.
#[cfg(rusthammer_verify)]
#[allow(dead_code)] // Entry points are reached by Charon, not by Rust library calls.
#[path = "../examples/support/dependent.rs"]
mod dependent_examples;

#[cfg(rusthammer_verify)]
#[allow(dead_code)]
#[path = "../examples/support/flags.rs"]
mod flags_example;

#[cfg(rusthammer_verify)]
#[allow(dead_code)]
#[path = "../examples/support/marker.rs"]
mod marker_example;

#[cfg(rusthammer_verify)]
#[allow(dead_code)]
#[path = "../examples/support/record.rs"]
mod record_example;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// A byte index and the number of bits consumed in that byte.
/// The active bit direction determines which end those bits were consumed from.
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

// Advance using the input length alone: skipping never reads the input bytes.
// Split the count before adding so neither an absolute bit position nor
// `bits + cursor.bit` has to fit in usize. Check the remaining byte count before
// adding to the cursor; the final bit offset must also fit at end-of-input.
fn advance_cursor(length: usize, cursor: Cursor, bits: usize) -> Result<Cursor, ParseError> {
    if cursor.bit >= 8 || cursor.byte > length || (cursor.byte == length && cursor.bit != 0) {
        return Err(ParseError::InvalidCursor);
    }
    let tail = cursor.bit + (bits % 8) as u8;
    let bytes = bits / 8 + (tail / 8) as usize;
    let bit = tail % 8;
    if bytes > length - cursor.byte {
        return Err(ParseError::UnexpectedEnd);
    }
    let byte = cursor.byte + bytes;
    if byte == length && bit != 0 {
        return Err(ParseError::UnexpectedEnd);
    }
    Ok(Cursor { byte, bit })
}

#[cfg(test)]
mod position_boundary_tests {
    use super::{advance_cursor, Cursor, ParseError};

    #[test]
    fn virtual_lengths_cover_machine_limits_without_allocating_input() {
        let max = usize::MAX;
        let points = [0, 1, 7, 8, max / 8 - 1, max / 8, max / 8 + 1, max - 1, max];
        for length in points {
            for byte in points.into_iter().chain([length.saturating_sub(1), length]) {
                for bit in (0..=9).chain([u8::MAX]) {
                    let cursor = Cursor { byte, bit };
                    for bits in points.into_iter().chain([2, 6, 9, 63, 64, 65]) {
                        let start = byte as u128 * 8 + u128::from(bit);
                        let end = length as u128 * 8;
                        let target = start + bits as u128;
                        let expected = if bit >= 8 || start > end {
                            Err(ParseError::InvalidCursor)
                        } else if target > end {
                            Err(ParseError::UnexpectedEnd)
                        } else {
                            Ok(Cursor {
                                byte: (target / 8) as usize,
                                bit: (target % 8) as u8,
                            })
                        };
                        assert_eq!(
                            advance_cursor(length, cursor, bits),
                            expected,
                            "length={length} cursor={cursor:?} bits={bits}"
                        );
                    }
                }
            }
        }
    }
}

/// Discard exactly the configured number of bits, returning `()`.
///
/// Corresponds to Hammer's `h_skip`. Starts may be unaligned; no padding is
/// inserted, and counts are not limited to 64. Advancement takes constant time
/// without reading input bytes or allocating. Every `usize` count is valid.
/// Parsing validates the cursor even when skipping zero bits. Insufficient
/// input returns `NeedMore` on partial input or `UnexpectedEnd` on final input.
///
/// ```
/// use rusthammer::{Cursor, Parser, SkipBits};
/// const RESERVED: SkipBits = SkipBits::new(11);
/// assert_eq!(RESERVED.parse(&[0; 2], Cursor { byte: 0, bit: 3 }),
///     Ok((Cursor { byte: 1, bit: 6 }, ())));
/// ```
///
/// ```compile_fail,E0451
/// let parser = rusthammer::SkipBits { bits: 8 };
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SkipBits {
    bits: usize,
}

impl SkipBits {
    /// Construct a skip parser. Every count is valid, including zero.
    pub const fn new(bits: usize) -> Self {
        Self { bits }
    }

    /// The number of bits to discard on success.
    pub const fn bits(&self) -> usize {
        self.bits
    }
}

impl<'input> Grammar<'input> for SkipBits {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for SkipBits {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        let result = match advance_cursor(input.len(), cursor, self.bits) {
            Ok(next) => Ok((next, ())),
            Err(error) => Err(error),
        };
        context.status.classify(result)
    }
}

/// Report the current validated cursor without consuming input.
///
/// Corresponds to Hammer's `h_tell`, with a byte-and-bit `Cursor` output instead
/// of an absolute bit count. This avoids overflowing a byte-to-bit conversion.
/// Returns `InvalidCursor` for invalid positions; every valid position succeeds
/// immediately on both partial and final input, including canonical end-of-input.
///
/// ```
/// use rusthammer::{Cursor, Parser, Tell};
/// let cursor = Cursor { byte: 0, bit: 3 };
/// assert_eq!(Tell.parse(&[0], cursor), Ok((cursor, cursor)));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tell;

impl<'input> Grammar<'input> for Tell {
    type Output = Cursor;
}

impl<'input, Backend> Eval<'input, Backend> for Tell {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        _context: ParseContext,
    ) -> ParseOutcome<Cursor> {
        match advance_cursor(input.len(), cursor, 0) {
            Ok(next) => ParseOutcome::Success(next, next),
            Err(error) => ParseOutcome::Error(error),
        }
    }
}

/// Invalid parameters supplied while constructing a parser, before parsing input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConfigError {
    /// The requested integer field width exceeds 64 bits.
    InvalidWidth,
    /// The expected literal value cannot be represented in its field width.
    InvalidLiteral,
    /// A lower range bound or repetition minimum exceeds its upper bound or maximum.
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
    /// An unbounded repetition did not strictly advance, or a span's end precedes its start.
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

/// Which end of each physical byte is consumed first. Fragment bits retain
/// their ordinary numeric significance; `LowFirst` does not reverse them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitOrder {
    HighFirst,
    LowFirst,
}

/// The significance of successive physical-byte fragments of a numeric field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteOrder {
    Big,
    Little,
}

/// Independent bit direction and byte-fragment significance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Order {
    pub bit: BitOrder,
    pub byte: ByteOrder,
}

impl Order {
    pub const DEFAULT: Self = Self {
        bit: BitOrder::HighFirst,
        byte: ByteOrder::Big,
    };
}

/// Immutable interpretation settings passed to every child parser.
///
/// A partial-byte cursor must be resumed with its original bit direction.
/// To retry `NeedMore`, keep the order and original cursor, supply accumulated
/// input, and update finality if the input is now complete.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseContext {
    pub order: Order,
    pub status: InputStatus,
}

impl ParseContext {
    /// Complete input, with high-first bits and big byte order.
    pub const FINAL: Self = Self {
        order: Order::DEFAULT,
        status: InputStatus::Final,
    };
    /// Extendable input, with high-first bits and big byte order.
    pub const PARTIAL: Self = Self {
        order: Order::DEFAULT,
        status: InputStatus::Partial,
    };
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
            // Aeneas workaround: move the tuple before destructuring it. Nested
            // Ok((next, value)) generates cleanup reads of a partly moved enum
            // in dependency MIR, which the pinned Aeneas interpreter rejects.
            // See probes/cross_crate/README.md for the reproducer and tool versions.
            Ok(parsed) => {
                let (next, value) = parsed;
                ParseOutcome::Success(next, value)
            }
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

/// A typed grammar, independent of the backend used to execute it.
///
/// The output can borrow from the input or from the grammar's configuration.
/// Implementing this trait alone does not provide an execution capability.
pub trait Grammar<'input> {
    type Output;
}

/// Execute a grammar with a selected backend and its invocation-local state.
///
/// Every child invocation must use `eval` with the same backend, including
/// lookahead, retries, and parsers constructed by `Bind`. Calling `parse` or
/// `parse_with` inside an evaluator would start a separate direct execution.
/// Backtracking restores the cursor, not backend bookkeeping.
///
/// Input and immutable ordering/finality context are separate from mutable
/// execution state so returned values can borrow the input independently.
/// Implementations propagate `NeedMore` before trying alternatives or deciding
/// absence; on final input they return success or an error, never `NeedMore`.
/// A stateful backend must bind its state to the input and grammar it describes.
pub trait Eval<'input, Backend>: Grammar<'input> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output>;
}

/// Direct recursive interpretation, with no retained execution state.
#[derive(Clone, Copy, Debug, Default)]
pub struct Direct;

/// Convenience entry points for grammars that support direct interpretation.
///
/// This trait is implemented automatically from `Eval<Direct>`. Custom parsers
/// implement `Grammar` and `Eval`, rather than overriding these entry points.
pub trait Parser<'input>: Eval<'input, Direct> {
    /// Start direct execution with explicit ordering and input finality.
    ///
    /// A partial parse can succeed without reaching EOF. To retry `NeedMore`,
    /// supply the accumulated input and original cursor. Parsers retain no buffer
    /// or continuation. Retrying can rerun callbacks; effects are not rolled back.
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        self.eval(&mut Direct, input, cursor, context)
    }

    /// Parse a complete buffer with high-first bits and big byte order.
    /// A custom evaluator's unexpected `NeedMore` becomes `UnexpectedEnd`.
    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parse_with(input, cursor, ParseContext::FINAL)
            .into_complete()
    }
}

impl<'input, P: Eval<'input, Direct>> Parser<'input> for P {}

/// Reuse a parser by shared reference, preserving both entry points and its output
/// type. The parser reference's lifetime is independent of the input lifetime.
impl<'input, P: Grammar<'input>> Grammar<'input> for &P {
    type Output = P::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for &P {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        P::eval(*self, backend, input, cursor, context)
    }
}

/// Read one bit, advancing into the next byte after its least-significant bit.
/// All cursor values are checked; malformed input is an ordinary error.
pub fn read_bit(input: &[u8], cursor: Cursor) -> Result<(Cursor, bool), ParseError> {
    read_bit_ordered(input, cursor, BitOrder::HighFirst)
}

fn read_bit_ordered(
    input: &[u8],
    cursor: Cursor,
    order: BitOrder,
) -> Result<(Cursor, bool), ParseError> {
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

    let shift = match order {
        BitOrder::HighFirst => 7 - cursor.bit,
        BitOrder::LowFirst => cursor.bit,
    };
    let value = ((input[cursor.byte] >> shift) & 1) != 0;
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

impl<'input> Grammar<'input> for Bit {
    type Output = bool;
}

impl<'input, Backend> Eval<'input, Backend> for Bit {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<bool> {
        context
            .status
            .classify(read_bit_ordered(input, cursor, context.order.bit))
    }
}

/// Read an unsigned field of 0 through 64 bits using the active ordering.
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

impl<'input> Grammar<'input> for Bits {
    type Output = u64;
}

impl<'input, Backend> Eval<'input, Backend> for Bits {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u64> {
        context
            .status
            .classify(read_ordered_bits(input, cursor, self, context.order))
    }
}

/// Read a validated field with high-first bits and big byte order, without
/// implicit alignment. Use `Bits::parse_with` for explicit ordering/finality.
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

// The public read_bits helper retains its explicit default-order semantics.
// Reuse it for physical fragments so the contiguous-bit decoder and its bounds
// proof are shared. The default order can decode the whole field directly.
fn read_ordered_bits(
    input: &[u8],
    cursor: Cursor,
    parser: &Bits,
    order: Order,
) -> Result<(Cursor, u64), ParseError> {
    if let Order {
        bit: BitOrder::HighFirst,
        byte: ByteOrder::Big,
    } = order
    {
        return read_bits(input, cursor, parser);
    }
    read_fragments(input, cursor, parser.width, order)
}

fn fragment_offset(bit: u8, take: u8, order: BitOrder) -> u8 {
    match order {
        BitOrder::HighFirst => bit,
        BitOrder::LowFirst => 8 - bit - take,
    }
}

fn append_fragment(value: u64, fragment: u64, done: u8, take: u8, order: ByteOrder) -> u64 {
    match order {
        ByteOrder::Big => value * (1u64 << take) + fragment,
        ByteOrder::Little => value + fragment * (1u64 << done),
    }
}

fn advance_fragment(cursor: Cursor, take: u8) -> Cursor {
    let bit = cursor.bit + take;
    if bit == 8 {
        Cursor {
            byte: cursor.byte + 1,
            bit: 0,
        }
    } else {
        Cursor {
            byte: cursor.byte,
            bit,
        }
    }
}

fn read_fragments(
    input: &[u8],
    cursor: Cursor,
    width: u8,
    order: Order,
) -> Result<(Cursor, u64), ParseError> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return Err(ParseError::InvalidCursor);
    }
    let mut next = cursor;
    let mut remaining = width;
    let mut value = 0;
    while remaining != 0 {
        if next.byte == input.len() {
            return Err(ParseError::UnexpectedEnd);
        }
        let available = 8 - next.bit;
        let take = if remaining < available {
            remaining
        } else {
            available
        };
        let bit = fragment_offset(next.bit, take, order.bit);
        let fragment = match read_bits(
            input,
            Cursor {
                byte: next.byte,
                bit,
            },
            &Bits { width: take },
        ) {
            Ok((_, fragment)) => fragment,
            Err(error) => return Err(error),
        };
        value = append_fragment(value, fragment, width - remaining, take, order.byte);
        next = advance_fragment(next, take);
        remaining -= take;
    }
    Ok((next, value))
}

/// Override a child's bit and byte order, preserving input finality.
///
/// A change of bit direction requires a valid, byte-aligned starting cursor
/// and successful ending cursor. Invalid bounds take precedence over `Unaligned`.
/// Entry rejection skips the child; exit rejection discards its output. Child
/// errors and `NeedMore` propagate unchanged. No padding is inserted.
/// A scope that keeps bit direction delegates without extra cursor checks,
/// so byte-order-only changes can start and finish within a byte.
///
/// ```
/// use rusthammer::{BeU16, BitOrder, Bits, ByteOrder, Cursor, Order, Parser, Seq, WithOrder};
/// let parser = Seq {
///     first: WithOrder {
///         order: Order { bit: BitOrder::LowFirst, byte: ByteOrder::Little },
///         parser: Seq { first: Bits::new(3).unwrap(), second: Bits::new(5).unwrap() },
///     },
///     second: BeU16,
/// };
/// assert_eq!(parser.parse(&[0x96, 0x12, 0x34], Cursor::start()),
///     Ok((Cursor { byte: 3, bit: 0 }, ((6, 18), 0x1234))));
/// ```
#[derive(Clone, Copy)]
pub struct WithOrder<P> {
    pub parser: P,
    pub order: Order,
}

fn scope_boundary_error(length: usize, cursor: Cursor) -> Option<ParseError> {
    if cursor.bit >= 8 || cursor.byte > length || (cursor.byte == length && cursor.bit != 0) {
        Some(ParseError::InvalidCursor)
    } else if cursor.bit != 0 {
        Some(ParseError::Unaligned)
    } else {
        None
    }
}

fn finish_order_scope<T>(length: usize, changed: bool, result: ParseOutcome<T>) -> ParseOutcome<T> {
    if !changed {
        return result;
    }
    match result {
        ParseOutcome::Success(next, value) => match scope_boundary_error(length, next) {
            Some(error) => ParseOutcome::Error(error),
            None => ParseOutcome::Success(next, value),
        },
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
    }
}

impl<'input, P: Grammar<'input>> Grammar<'input> for WithOrder<P> {
    type Output = P::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for WithOrder<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let changed = self.order.bit != context.order.bit;
        if changed {
            if let Some(error) = scope_boundary_error(input.len(), cursor) {
                return ParseOutcome::Error(error);
            }
        }
        let result = self.parser.eval(
            backend,
            input,
            cursor,
            ParseContext {
                order: self.order,
                status: context.status,
            },
        );
        finish_order_scope(input.len(), changed, result)
    }
}

/// Read a two's-complement field of 0 through 64 bits using the active ordering.
///
/// Fields may start inside a byte and cross byte boundaries. Width zero returns
/// zero without consuming input, but still validates the cursor, just like `Bits`.
/// Construction rejects widths above 64 before any input is supplied.
///
/// ```
/// use rusthammer::{Cursor, Parser, SignedBits};
/// let field = SignedBits::new(5).unwrap();
/// assert_eq!(field.parse(&[0b1110_1000], Cursor::start()),
///     Ok((Cursor { byte: 0, bit: 5 }, -3i64)));
/// ```
///
/// ```compile_fail,E0451
/// let parser = rusthammer::SignedBits { bits: rusthammer::Bits::new(5).unwrap() };
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedBits {
    bits: Bits,
}

impl SignedBits {
    /// Construct a signed field, rejecting widths above 64 with `InvalidWidth`.
    pub const fn new(width: u8) -> Result<Self, ConfigError> {
        let bits = match Bits::new(width) {
            Ok(bits) => bits,
            Err(error) => return Err(error),
        };
        Ok(Self { bits })
    }

    /// Return the validated field width.
    pub const fn width(&self) -> u8 {
        self.bits.width()
    }
}

impl<'input> Grammar<'input> for SignedBits {
    type Output = i64;
}

impl<'input, Backend> Eval<'input, Backend> for SignedBits {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<i64> {
        match self.bits.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => {
                ParseOutcome::Success(next, sign_extend(value, self.bits.width))
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

// The caller supplies a width <= 64 and a value that fits in that width.
fn sign_extend(value: u64, width: u8) -> i64 {
    if width == 0 {
        return 0;
    }
    let sign = 1u64 << (width - 1);
    if value < sign {
        value as i64
    } else {
        // Compute value - 2^width as -1 - (2^width - 1 - value).
        // Splitting around the sign bit avoids constructing 2^64, out-of-range
        // signed casts, and negating i64::MIN. Both casts preserve their values.
        let complement = (sign - 1) - (value - sign);
        -1 - complement as i64
    }
}

/// Read an eight-bit field as a `u8` using the active ordering, even unaligned.
#[derive(Clone, Copy)]
pub struct Byte;

impl<'input> Grammar<'input> for Byte {
    type Output = u8;
}

impl<'input, Backend> Eval<'input, Backend> for Byte {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        match (Bits { width: 8 }).eval(backend, input, cursor, context) {
            // An eight-bit field is always representable as a byte.
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, value as u8),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

// These fixed widths always satisfy the private field invariants. Decoding
// establishes that each value fits its output type, so every cast is lossless.
// A private macro keeps the outcome propagation identical for all readers.
macro_rules! fixed_integer {
    ($(#[$doc:meta])* $name:ident, $output:ty, $field:expr, $pin_big:literal) => {
        $(#[$doc])*
        #[derive(Clone, Copy)]
        pub struct $name;

        impl<'input> Grammar<'input> for $name {
            type Output = $output;
        }

        impl<'input, Backend> Eval<'input, Backend> for $name {
            fn eval(
                &self,
                backend: &mut Backend,
                input: &'input [u8],
                cursor: Cursor,
                context: ParseContext,
            ) -> ParseOutcome<$output> {
                let context = if $pin_big {
                    ParseContext { order: Order { bit: context.order.bit, byte: ByteOrder::Big }, status: context.status }
                } else { context };
                match ($field).eval(backend, input, cursor, context) {
                    ParseOutcome::Success(next, value) => ParseOutcome::Success(next, value as $output),
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                }
            }
        }
    };
}

fixed_integer!(
    /// Read a big-endian 16-bit unsigned integer as `u16`.
    ///
    /// Pins big byte order and inherits bit direction, without implicit alignment.
    /// This zero-sized parser has no configuration to validate.
    ///
    /// ```
    /// use rusthammer::{BeI16, BeU16, Cursor, Parser, Seq};
    /// let parser = Seq { first: BeU16, second: BeI16 };
    /// let (next, values): (Cursor, (u16, i16)) =
    ///     parser.parse(&[0x12, 0x34, 0xff, 0xfd], Cursor::start()).unwrap();
    /// assert_eq!(values, (0x1234, -3));
    /// assert_eq!(next, Cursor { byte: 4, bit: 0 });
    /// ```
    BeU16,
    u16,
    Bits { width: 16 },
    true
);

fixed_integer!(
    /// Read a big-endian 32-bit unsigned integer as `u32`.
    ///
    /// Pins big byte order and inherits bit direction, without implicit alignment.
    /// This zero-sized parser has no configuration to validate.
    BeU32,
    u32,
    Bits { width: 32 },
    true
);

fixed_integer!(
    /// Read a big-endian 64-bit unsigned integer as `u64`.
    ///
    /// Pins big byte order and inherits bit direction, without implicit alignment.
    /// This zero-sized parser has no configuration to validate.
    BeU64,
    u64,
    Bits { width: 64 },
    true
);

fixed_integer!(
    /// Read an eight-bit field as a two's-complement `i8` using the active ordering.
    ///
    /// Reads from the supplied cursor, without implicit alignment.
    /// This zero-sized parser has no configuration to validate.
    I8,
    i8,
    SignedBits {
        bits: Bits { width: 8 }
    },
    false
);

fixed_integer!(
    /// Read a big-endian 16-bit two's-complement integer as `i16`.
    ///
    /// Pins big byte order and inherits bit direction, without implicit alignment.
    /// This zero-sized parser has no configuration to validate.
    BeI16,
    i16,
    SignedBits {
        bits: Bits { width: 16 }
    },
    true
);

fixed_integer!(
    /// Read a big-endian 32-bit two's-complement integer as `i32`.
    ///
    /// Pins big byte order and inherits bit direction, without implicit alignment.
    /// This zero-sized parser has no configuration to validate.
    BeI32,
    i32,
    SignedBits {
        bits: Bits { width: 32 }
    },
    true
);

fixed_integer!(
    /// Read a big-endian 64-bit two's-complement integer as `i64`.
    ///
    /// Pins big byte order and inherits bit direction, without implicit alignment.
    /// This zero-sized parser has no configuration to validate.
    BeI64,
    i64,
    SignedBits {
        bits: Bits { width: 64 }
    },
    true
);

/// Fixed bitmap over the byte domain, shared by inclusion and exclusion.
#[derive(Clone, Copy)]
struct ByteSet {
    words: [u64; 4],
}

impl ByteSet {
    const fn new(bytes: &[u8]) -> Self {
        let mut words = [0u64; 4];
        let mut index = 0;
        while index < bytes.len() {
            let byte = bytes[index];
            words[(byte / 64) as usize] |= 1u64 << (byte % 64);
            index += 1;
        }
        Self { words }
    }

    const fn contains(&self, byte: u8) -> bool {
        self.words[(byte / 64) as usize] & (1u64 << (byte % 64)) != 0
    }
}

/// Read one byte belonging to a set of literal byte values.
///
/// Corresponds to Hammer's `h_in`. The set is a byte slice, not a regular
/// expression: order and duplicates do not affect membership. Construction is
/// infallible, including for empty sets and embedded zeros, and allocates nothing.
/// Construction scans the slice once into an owned 32-byte bitmap; membership
/// takes constant time. The parser does not borrow the slice or preserve its
/// order and duplicates. Copying a parser copies its bitmap.
///
/// Parsing delegates to `Verify` over `Byte`, returning the decoded `u8` and
/// consuming eight bits on success, even from an unaligned cursor. A decoded
/// nonmember returns `Mismatch`. Invalid cursors and short input follow `Byte`'s
/// rules, including `NeedMore` on partial input, even when the set is empty.
/// The output does not borrow the set, input, or parser.
///
/// ```
/// use rusthammer::{ByteIn, Cursor, Parser};
/// const SEPARATOR: ByteIn = ByteIn::new(b",;:");
/// assert!(SEPARATOR.accepts(b';'));
/// assert_eq!(SEPARATOR.parse(b";", Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, b';')));
/// ```
///
/// ```compile_fail,E0616
/// let hidden = rusthammer::ByteIn::new(b"abc").set;
/// ```
#[derive(Clone, Copy)]
pub struct ByteIn {
    set: ByteSet,
}

impl ByteIn {
    /// Build an owned bitmap of allowed values. Every slice is a valid set.
    pub const fn new(bytes: &[u8]) -> Self {
        Self {
            set: ByteSet::new(bytes),
        }
    }

    /// Test whether a decoded byte would be accepted, without reading input.
    pub const fn accepts(&self, byte: u8) -> bool {
        self.set.contains(byte)
    }
}

impl<'input> Grammar<'input> for ByteIn {
    type Output = u8;
}

impl<'input, Backend> Eval<'input, Backend> for ByteIn {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        Verify {
            parser: Byte,
            predicate: |value: &u8| self.accepts(*value),
        }
        .eval(backend, input, cursor, context)
    }
}

/// Read one byte outside a set of literal byte values.
///
/// Corresponds to Hammer's `h_not_in`. Like `ByteIn`, construction is infallible
/// and allocation-free, and parsing uses `Verify` over `Byte`. A decoded member
/// returns `Mismatch`; success returns the decoded `u8` and consumes eight bits
/// without implicit alignment. An empty exclusion set accepts any decoded byte.
/// Short input still returns `NeedMore` on partial input or `UnexpectedEnd` on
/// final input. The output does not borrow the set, input, or parser.
/// Construction scans the slice once into an owned 32-byte bitmap; membership
/// takes constant time. The parser does not borrow the slice or preserve its
/// order and duplicates. Copying a parser copies its bitmap.
///
/// ```
/// use rusthammer::{ByteNotIn, Cursor, ParseError, Parser};
/// let content = ByteNotIn::new(b"\r\n");
/// assert_eq!(content.parse(b"x", Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, b'x')));
/// assert_eq!(content.parse(b"\n", Cursor::start()), Err(ParseError::Mismatch));
/// ```
///
/// ```compile_fail,E0616
/// let hidden = rusthammer::ByteNotIn::new(b"abc").set;
/// ```
#[derive(Clone, Copy)]
pub struct ByteNotIn {
    set: ByteSet,
}

impl ByteNotIn {
    /// Build an owned bitmap of excluded values. Every slice is a valid set.
    pub const fn new(bytes: &[u8]) -> Self {
        Self {
            set: ByteSet::new(bytes),
        }
    }

    /// Test whether a decoded byte would be accepted, without reading input.
    /// Returns true precisely for bytes outside the configured exclusion set.
    pub const fn accepts(&self, byte: u8) -> bool {
        !self.set.contains(byte)
    }
}

impl<'input> Grammar<'input> for ByteNotIn {
    type Output = u8;
}

impl<'input, Backend> Eval<'input, Backend> for ByteNotIn {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        Verify {
            parser: Byte,
            predicate: |value: &u8| self.accepts(*value),
        }
        .eval(backend, input, cursor, context)
    }
}

/// Match a borrowed byte pattern, including from an unaligned bit cursor.
///
/// Success returns the configured pattern slice, whose lifetime is independent
/// of the input and of the parser value. This requires no allocation even when
/// the matched bits cross byte boundaries. Use `TakeAligned` to borrow input.
/// An empty pattern succeeds without reading input or validating the cursor.
///
/// Bytes are compared in order: a complete differing byte rejects immediately.
/// A missing or incomplete byte returns `NeedMore` on partial input and
/// `UnexpectedEnd` on final input, even if its available bits already differ.
///
/// ```
/// use rusthammer::{BytePattern, Cursor, Parser};
/// let pattern = [0xab, 0xcd];
/// let matched = {
///     let input = [0x55, 0xe6, 0x80];
///     BytePattern::new(&pattern).parse(&input, Cursor { byte: 0, bit: 1 }).unwrap().1
/// };
/// assert!(core::ptr::eq(matched, &pattern[..]));
/// ```
#[derive(Clone, Copy)]
pub struct BytePattern<'pattern> {
    pattern: &'pattern [u8],
}

impl<'pattern> BytePattern<'pattern> {
    /// Every slice is a valid pattern, including empty slices and embedded zeros.
    pub const fn new(pattern: &'pattern [u8]) -> Self {
        Self { pattern }
    }

    /// Return the configured pattern, which is also the successful parse output.
    pub const fn pattern(&self) -> &'pattern [u8] {
        self.pattern
    }
}

impl<'input, 'pattern> Grammar<'input> for BytePattern<'pattern> {
    type Output = &'pattern [u8];
}

impl<'input, 'pattern, Backend> Eval<'input, Backend> for BytePattern<'pattern> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        // Keep the returned pattern borrow outside the matching loop. The pinned
        // Aeneas cannot join the loop's borrow contexts when it returns the slice.
        // See probes/pattern_loop_borrow.rs and the accompanying probe notes.
        match match_byte_pattern(backend, self.pattern, input, cursor, context) {
            ParseOutcome::Success(next, ()) => ParseOutcome::Success(next, self.pattern),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

fn match_byte_pattern<Backend>(
    backend: &mut Backend,
    pattern: &[u8],
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<()> {
    let mut next = cursor;
    let mut index = 0;
    while index < pattern.len() {
        match Byte.eval(backend, input, next, context) {
            ParseOutcome::Success(after, value) => {
                if value != pattern[index] {
                    return ParseOutcome::Error(ParseError::Mismatch);
                }
                next = after;
                index += 1;
            }
            ParseOutcome::Error(error) => return ParseOutcome::Error(error),
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
        }
    }
    ParseOutcome::Success(next, ())
}

/// Match a numeric field in the active order against an expected value.
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

impl<'input> Grammar<'input> for Literal {
    type Output = u64;
}

impl<'input, Backend> Eval<'input, Backend> for Literal {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u64> {
        context
            .status
            .classify(read_literal(input, cursor, self, context.order))
    }
}

fn read_literal(
    input: &[u8],
    cursor: Cursor,
    parser: &Literal,
    order: Order,
) -> Result<(Cursor, u64), ParseError> {
    match read_ordered_bits(input, cursor, &parser.bits, order) {
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

impl<'input> Grammar<'input> for End {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for End {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        if cursor.bit >= 8
            || cursor.byte > input.len()
            || (cursor.byte == input.len() && cursor.bit != 0)
        {
            return ParseOutcome::Error(ParseError::InvalidCursor);
        }
        if cursor.byte == input.len() {
            match context.status {
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

impl<'input> Grammar<'input> for Epsilon {
    type Output = ();
}

impl<'input, Backend> Eval<'input, Backend> for Epsilon {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        cursor: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<()> {
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

impl<'input, T> Grammar<'input> for Fail<T> {
    type Output = T;
}

impl<'input, Backend, T> Eval<'input, Backend> for Fail<T> {
    fn eval(
        &self,
        _: &mut Backend,
        _: &'input [u8],
        _: Cursor,
        _: ParseContext,
    ) -> ParseOutcome<T> {
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

impl<'input, P: Grammar<'input>, Q: Grammar<'input>> Grammar<'input> for Seq<P, Q> {
    type Output = (P::Output, Q::Output);
}

impl<'input, Backend, P: Eval<'input, Backend>, Q: Eval<'input, Backend>> Eval<'input, Backend>
    for Seq<P, Q>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.first.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::Success(next, first) => {
                match self.second.eval(backend, input, next, context) {
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                    ParseOutcome::Error(error) => ParseOutcome::Error(error),
                    ParseOutcome::Success(end, second) => {
                        ParseOutcome::Success(end, (first, second))
                    }
                }
            }
        }
    }
}

/// Use a parsed value to construct the next parser, returning that parser's output.
///
/// `then` takes ownership of the first output and runs exactly once after success.
/// Its parser runs at that success cursor with the same input and context. Errors
/// and `NeedMore` from either stage propagate unchanged; a first-stage failure
/// skips the factory. Outputs and the constructed parser need neither `Copy` nor
/// `Clone`. Copying this combinator depends only on its stored parser and factory.
///
/// For each input lifetime, the factory returns one concrete parser type. Parsed
/// values can change that parser's configuration. Use a typed parser enum for
/// branches with different implementations. `TryMap` can check input-derived
/// counts or construct a checked parser before `Bind` executes it.
///
/// The combinator allocates no memory and retains no state between calls.
/// Verification requires contracts for the first parser, factory, and constructed
/// parsers. Retrying or backtracking can rerun the factory; its effects are not
/// rolled back. `Fn` alone does not imply purity, termination, or panic freedom.
///
/// ```
/// use rusthammer::{Bind, Bits, Cursor, Parser, TakeAligned, TryMap};
/// let payload = Bind {
///     parser: TryMap {
///         parser: Bits::new(8).unwrap(),
///         map: |length| usize::try_from(length),
///     },
///     then: |count| TakeAligned { count },
/// };
/// assert_eq!(payload.parse(b"\x03abc!", Cursor::start()),
///     Ok((Cursor { byte: 4, bit: 0 }, &b"abc"[..])));
/// ```
#[derive(Clone, Copy)]
pub struct Bind<P, F> {
    pub parser: P,
    pub then: F,
}

impl<'input, P, F, Q> Grammar<'input> for Bind<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> Q,
    Q: Grammar<'input>,
{
    type Output = Q::Output;
}

impl<'input, Backend, P, F, Q> Eval<'input, Backend> for Bind<P, F>
where
    P: Eval<'input, Backend>,
    F: Fn(P::Output) -> Q,
    Q: Eval<'input, Backend>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => {
                (self.then)(value).eval(backend, input, next, context)
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
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

impl<'input, P: Grammar<'input>, Q: Grammar<'input>> Grammar<'input> for Left<P, Q> {
    type Output = P::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>, Q: Eval<'input, Backend>> Eval<'input, Backend>
    for Left<P, Q>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.eval(backend, input, cursor, context) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, values) => {
                let (first, _) = values;
                ParseOutcome::Success(next, first)
            }
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

impl<'input, P: Grammar<'input>, Q: Grammar<'input>> Grammar<'input> for Right<P, Q> {
    type Output = Q::Output;
}

impl<'input, Backend, P: Eval<'input, Backend>, Q: Eval<'input, Backend>> Eval<'input, Backend>
    for Right<P, Q>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.first,
            second: &self.second,
        };
        match sequence.eval(backend, input, cursor, context) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, values) => {
                let (_, second) = values;
                ParseOutcome::Success(next, second)
            }
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

impl<'input, L: Grammar<'input>, P: Grammar<'input>, R: Grammar<'input>> Grammar<'input>
    for Middle<L, P, R>
{
    type Output = P::Output;
}

impl<
        'input,
        Backend,
        L: Eval<'input, Backend>,
        P: Eval<'input, Backend>,
        R: Eval<'input, Backend>,
    > Eval<'input, Backend> for Middle<L, P, R>
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let sequence = Seq {
            first: &self.left,
            second: Seq {
                first: &self.parser,
                second: &self.right,
            },
        };
        match sequence.eval(backend, input, cursor, context) {
            // Keep tuple destructuring separate for Aeneas dependency extraction;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, values) => {
                let (_, (middle, _)) = values;
                ParseOutcome::Success(next, middle)
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// A validated region of the original input, including partial boundary bytes.
///
/// Positions count bits consumed from the end of each byte selected by
/// `bit_order`. The span retains that direction after parsing returns. It
/// identifies source bits, not the field grouping or internal ordering scopes
/// used to decode them. Byte order does not affect the source region.
///
/// Both endpoints are normalized, within `input`, and in forward order; equal
/// endpoints describe an empty span. Fields are private to preserve those bounds.
/// Use [`Self::as_bytes`] for a borrowed byte view when both endpoints are aligned.
/// Partial-byte spans expose their input, positions, and direction instead.
/// No absolute machine-sized bit count is needed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitSpan<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
    bit_order: BitOrder,
}

fn span_cursor_valid(length: usize, cursor: Cursor) -> bool {
    cursor.bit < 8 && (cursor.byte < length || (cursor.byte == length && cursor.bit == 0))
}

impl<'input> BitSpan<'input> {
    /// Validate a region. Invalid endpoints yield `InvalidCursor` before checking
    /// for a backward span (`NonProgress`). Empty and unaligned spans are valid.
    pub fn new(
        input: &'input [u8],
        start: Cursor,
        end: Cursor,
        bit_order: BitOrder,
    ) -> Result<Self, ParseError> {
        if !span_cursor_valid(input.len(), start) || !span_cursor_valid(input.len(), end) {
            return Err(ParseError::InvalidCursor);
        }
        if end.byte < start.byte || (end.byte == start.byte && end.bit < start.bit) {
            return Err(ParseError::NonProgress);
        }
        Ok(Self {
            input,
            start,
            end,
            bit_order,
        })
    }

    /// The complete input buffer from which this region was selected.
    pub const fn input(&self) -> &'input [u8] {
        self.input
    }

    pub const fn start(&self) -> Cursor {
        self.start
    }

    pub const fn end(&self) -> Cursor {
        self.end
    }

    /// Direction used to identify the selected bits in partial boundary bytes.
    pub const fn bit_order(&self) -> BitOrder {
        self.bit_order
    }

    pub fn is_empty(&self) -> bool {
        self.start.byte == self.end.byte && self.start.bit == self.end.bit
    }

    /// Original source bytes, without reordering or copying, if both endpoints
    /// are aligned. An aligned empty span returns `Some(&[])`; an unaligned
    /// empty span returns `None`. The borrow lasts as long as the original input.
    pub fn as_bytes(&self) -> Option<&'input [u8]> {
        if self.start.bit != 0 || self.end.bit != 0 {
            return None;
        }
        Some(&self.input[self.start.byte..self.end.byte])
    }
}

/// Retain a child's decoded value together with its matched input span.
///
/// The output is `(P::Output, BitSpan<'input>)`. This wrapper annotates only its
/// own result; nested values acquire spans only where explicitly wrapped.
/// The starting cursor is validated before the child runs. On success, the
/// ending cursor is validated and backward movement rejected with `NonProgress`.
/// Empty matches are allowed. Child errors and `NeedMore` propagate unchanged.
/// Backend state and context follow the child, including on a rejected exit.
///
/// Custom children must obey the ordering scope rules: endpoint checks cannot
/// establish which bits an arbitrary parser inspected. Lookahead contributes
/// no consumed input, and therefore has an empty span when wrapped.
///
/// ```
/// use rusthammer::{BeU16, Cursor, Parser, WithSpan};
/// let input = [0x12, 0x34];
/// let (_, (value, span)) = WithSpan { parser: BeU16 }
///     .parse(&input, Cursor::start()).unwrap();
/// assert_eq!(value, 0x1234);
/// assert_eq!(span.as_bytes(), Some(input.as_slice()));
/// ```
#[derive(Clone, Copy)]
pub struct WithSpan<P> {
    pub parser: P,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for WithSpan<P> {
    type Output = (P::Output, BitSpan<'input>);
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for WithSpan<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        if !span_cursor_valid(input.len(), cursor) {
            return ParseOutcome::Error(ParseError::InvalidCursor);
        }
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => {
                let span = match BitSpan::new(input, cursor, next, context.order.bit) {
                    Ok(span) => span,
                    Err(error) => return ParseOutcome::Error(error),
                };
                ParseOutcome::Success(next, (value, span))
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

/// Return the matched input span, discarding the child's decoded value.
///
/// Uses the same validation and consumption rules as [`WithSpan`]. The child
/// still runs and constructs its output, including allocations and callback
/// effects; that value is then dropped. Grammar nodes remain backend-generic.
///
/// ```
/// use rusthammer::{BeU16, Cursor, Parser, Recognize};
/// let input = [0x12, 0x34];
/// let (_, span) = Recognize { parser: BeU16 }
///     .parse(&input, Cursor::start()).unwrap();
/// assert_eq!(span.as_bytes(), Some(input.as_slice()));
/// ```
#[derive(Clone, Copy)]
pub struct Recognize<P> {
    pub parser: P,
}

impl<'input, P: Grammar<'input>> Grammar<'input> for Recognize<P> {
    type Output = BitSpan<'input>;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Recognize<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let spanned = WithSpan {
            parser: &self.parser,
        };
        match spanned.eval(backend, input, cursor, context) {
            // Move the complete tuple before destructuring for dependency MIR;
            // see InputStatus::classify and probes/cross_crate/README.md.
            ParseOutcome::Success(next, output) => {
                let (_, span) = output;
                ParseOutcome::Success(next, span)
            }
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

impl<'input, P: Grammar<'input>> Grammar<'input> for Ignore<P> {
    type Output = ();
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Ignore<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        match self.parser.eval(backend, input, cursor, context) {
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

impl<'input, P, F, O> Grammar<'input> for Map<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> O,
{
    type Output = O;
}

impl<'input, Backend, P, F, O> Eval<'input, Backend> for Map<P, F>
where
    P: Eval<'input, Backend>,
    F: Fn(P::Output) -> O,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
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

impl<'input, P, F, O, E> Grammar<'input> for TryMap<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> Result<O, E>,
{
    type Output = O;
}

impl<'input, Backend, P, F, O, E> Eval<'input, Backend> for TryMap<P, F>
where
    P: Eval<'input, Backend>,
    F: Fn(P::Output) -> Result<O, E>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, value) => match (self.map)(value) {
                Ok(mapped) => ParseOutcome::Success(next, mapped),
                // Keep `_error`: unlike `_`, it moves the payload out of Result.
                // This avoids cleanup reads of a partly moved enum in dependency MIR;
                // see probes/cross_crate/README.md.
                Err(_error) => ParseOutcome::Error(ParseError::Mismatch),
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

impl<'input, P, F> Grammar<'input> for Verify<P, F>
where
    P: Grammar<'input>,
    F: Fn(&P::Output) -> bool,
{
    type Output = P::Output;
}

impl<'input, Backend, P, F> Eval<'input, Backend> for Verify<P, F>
where
    P: Eval<'input, Backend>,
    F: Fn(&P::Output) -> bool,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
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

/// Keep a parsed integer only when it lies between inclusive, typed bounds.
///
/// Bounds have the child's output type and use its `Ord` implementation, so
/// integer newtypes also work. The child and bounds need not be `Copy` or `Clone`;
/// the range implements those traits when its stored fields do. Floating-point
/// types lack `Ord`; use `Verify` with an explicit predicate for those instead.
///
/// Construction rejects reversed bounds with `ConfigError::InvalidBounds`.
/// Parsing delegates to `Verify`: acceptance preserves the child's value and
/// cursor, rejection returns recoverable `Mismatch`, and child errors and
/// `NeedMore` propagate unchanged. No input is read during construction.
///
/// ```
/// use rusthammer::{BeU16, Byte, Cursor, IntRange, Parser};
/// let length = IntRange::new(BeU16, 1u16, 4096u16).unwrap();
/// assert_eq!(length.parse(&[0x01, 0x00], Cursor::start()),
///     Ok((Cursor { byte: 2, bit: 0 }, 256u16)));
/// let digit = IntRange::new(Byte, b'0', b'9').unwrap();
/// assert_eq!(digit.parse(b"7", Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, b'7')));
/// ```
///
/// ```compile_fail,E0451
/// use rusthammer::{Byte, IntRange};
/// let invalid = IntRange { parser: Byte, lower: 9u8, upper: 0u8 };
/// ```
///
/// ```compile_fail,E0308
/// use rusthammer::{BeU16, IntRange};
/// let wrong_type = IntRange::new(BeU16, 0i16, 100i16);
/// ```
#[derive(Clone, Copy)]
pub struct IntRange<P, T> {
    parser: P,
    lower: T,
    upper: T,
}

impl<P, T> IntRange<P, T> {
    /// Construct an inclusive range, rejecting `lower > upper` before parsing.
    pub fn new<'input>(parser: P, lower: T, upper: T) -> Result<Self, ConfigError>
    where
        P: Grammar<'input, Output = T>,
        T: Ord,
    {
        if lower > upper {
            Err(ConfigError::InvalidBounds)
        } else {
            Ok(Self {
                parser,
                lower,
                upper,
            })
        }
    }

    /// Borrow the inclusive lower bound.
    pub const fn lower(&self) -> &T {
        &self.lower
    }

    /// Borrow the inclusive upper bound.
    pub const fn upper(&self) -> &T {
        &self.upper
    }
}

impl<'input, P, T> Grammar<'input> for IntRange<P, T>
where
    P: Grammar<'input, Output = T>,
    T: Ord,
{
    type Output = T;
}

impl<'input, Backend, P, T> Eval<'input, Backend> for IntRange<P, T>
where
    P: Eval<'input, Backend, Output = T>,
    T: Ord,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<T> {
        Verify {
            parser: &self.parser,
            predicate: |value: &T| self.lower <= *value && *value <= self.upper,
        }
        .eval(backend, input, cursor, context)
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

impl<'input, P, Q> Grammar<'input> for Choice<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input, Output = P::Output>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for Choice<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend, Output = P::Output>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.first.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, value),
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    self.second.eval(backend, input, cursor, context)
                } else {
                    ParseOutcome::Error(error)
                }
            }
        }
    }
}

// Both matches start at the same cursor. Ordering their normalized endpoints
// compares consumed bits without an absolute bit count or subtraction.
fn match_length_allows(first: Cursor, second: Cursor, allow_equal: bool) -> bool {
    first.byte > second.byte
        || (first.byte == second.byte
            && (first.bit > second.bit || (allow_equal && first.bit == second.bit)))
}

fn restrict_match<'input, Backend, P, Q>(
    backend: &mut Backend,
    first: &P,
    second: &Q,
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
    allow_equal: bool,
) -> ParseOutcome<P::Output>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend>,
{
    match first.eval(backend, input, cursor, context) {
        ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        ParseOutcome::Error(error) => ParseOutcome::Error(error),
        ParseOutcome::Success(next, value) => match second.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    ParseOutcome::Success(next, value)
                } else {
                    ParseOutcome::Error(error)
                }
            }
            ParseOutcome::Success(other, _other_value) => {
                if match_length_allows(next, other, allow_equal) {
                    ParseOutcome::Success(next, value)
                } else {
                    ParseOutcome::Error(ParseError::Mismatch)
                }
            }
        },
    }
}

/// Keep the first match if the second rejects or matches strictly fewer bits.
///
/// Corresponds to Hammer's `h_butnot`. Run `first`, then on success run `second`
/// from the original cursor. Recoverable second-child rejection accepts the
/// first value and cursor; two successes accept only when the first is longer.
/// Otherwise return `Mismatch`. Every attempted child's fatal error or
/// `NeedMore` propagates. The second output is discarded and may have any type.
///
/// Cursor validation is delegated to children, as with `Choice`. Endpoints are
/// ordered by byte index, then bit offset; normalized forward matches therefore
/// compare exact consumed bit lengths, without overflowing a bit count. Custom
/// parsers must respect that cursor convention. Speculative effects are not undone.
///
/// ```
/// use rusthammer::{ButNot, ByteIn, BytePattern, Cursor, Parser};
/// let digit_except_six = ButNot {
///     first: ByteIn::new(b"0123456789"),
///     second: BytePattern::new(b"6"),
/// };
/// assert_eq!(digit_except_six.parse(b"7", Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, b'7')));
/// assert!(digit_except_six.parse(b"6", Cursor::start()).is_err());
/// ```
#[derive(Clone, Copy)]
pub struct ButNot<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P, Q> Grammar<'input> for ButNot<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for ButNot<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        restrict_match(
            backend,
            &self.first,
            &self.second,
            input,
            cursor,
            context,
            false,
        )
    }
}

/// Keep the first match if the second rejects or matches no more bits.
///
/// Corresponds to Hammer's `h_difference`. This has `ButNot`'s evaluation order,
/// output, cursor, error, and incompleteness rules, but also accepts equal-length
/// successes. Both children run from the original cursor. Their outputs may have
/// different types. This operation is not ordinary language-set subtraction.
#[derive(Clone, Copy)]
pub struct Difference<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P, Q> Grammar<'input> for Difference<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for Difference<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        restrict_match(
            backend,
            &self.first,
            &self.second,
            input,
            cursor,
            context,
            true,
        )
    }
}

/// Accept exactly one of two matches, returning that child's value and cursor.
///
/// Corresponds to Hammer's `h_xor`. Run `first`; on success or recoverable
/// rejection, run `second` from the original cursor. Two successes return
/// `Mismatch`, regardless of their lengths. Two recoverable rejections return
/// the second error. Fatal errors and `NeedMore` from attempted children
/// propagate immediately. Cursor validation is delegated to children, and
/// speculative effects are not undone.
///
/// Both children must produce the same type. Use `Map` to put different kinds
/// of values into an application enum, as with `Choice`. Outputs need neither
/// `Copy` nor `Clone`; copying this parser requires only copyable children.
///
/// ```compile_fail
/// use rusthammer::{BeU16, Byte, Cursor, Parser, Xor};
/// let parser = Xor { first: Byte, second: BeU16 };
/// let _ = parser.parse(&[0, 1], Cursor::start());
/// ```
#[derive(Clone, Copy)]
pub struct Xor<P, Q> {
    pub first: P,
    pub second: Q,
}

impl<'input, P, Q> Grammar<'input> for Xor<P, Q>
where
    P: Grammar<'input>,
    Q: Grammar<'input, Output = P::Output>,
{
    type Output = P::Output;
}

impl<'input, Backend, P, Q> Eval<'input, Backend> for Xor<P, Q>
where
    P: Eval<'input, Backend>,
    Q: Eval<'input, Backend, Output = P::Output>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.first.eval(backend, input, cursor, context) {
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
            ParseOutcome::Error(error) => {
                if error.is_recoverable() {
                    self.second.eval(backend, input, cursor, context)
                } else {
                    ParseOutcome::Error(error)
                }
            }
            ParseOutcome::Success(next, value) => {
                match self.second.eval(backend, input, cursor, context) {
                    ParseOutcome::NeedMore => ParseOutcome::NeedMore,
                    ParseOutcome::Success(_other_cursor, _other_value) => {
                        ParseOutcome::Error(ParseError::Mismatch)
                    }
                    ParseOutcome::Error(error) => {
                        if error.is_recoverable() {
                            ParseOutcome::Success(next, value)
                        } else {
                            ParseOutcome::Error(error)
                        }
                    }
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

impl<'input, P: Grammar<'input>> Grammar<'input> for Optional<P> {
    type Output = Option<P::Output>;
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Optional<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
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

impl<'input, P: Grammar<'input>> Grammar<'input> for And<P> {
    type Output = ();
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for And<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        match self.parser.eval(backend, input, cursor, context) {
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

impl<'input, P: Grammar<'input>> Grammar<'input> for Not<P> {
    type Output = ();
}

impl<'input, Backend, P: Eval<'input, Backend>> Eval<'input, Backend> for Not<P> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<()> {
        match self.parser.eval(backend, input, cursor, context) {
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

impl<'input> Grammar<'input> for TakeAligned {
    type Output = &'input [u8];
}

impl<'input, Backend> Eval<'input, Backend> for TakeAligned {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        context
            .status
            .classify(take_aligned(input, cursor, self.count))
    }
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
