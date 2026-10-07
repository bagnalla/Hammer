use super::super::{ConfigError, Cursor, Eval, Grammar, ParseContext, ParseError, ParseOutcome};

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

/// Construct a [`Map`], inferring the callback argument from the child's output.
/// The callback is stored without being called. The concrete node preserves
/// backend support and conditional `Copy`/`Clone`, without requiring either
/// trait on its output.
///
/// ```
/// use rusthammer::{map, Byte, Cursor, Parser};
/// let doubled = map(Byte, |value| u16::from(value) * 2);
/// assert_eq!(doubled.parse(&[200], Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, 400)));
/// ```
pub fn map<'input, P, F, O>(parser: P, map: F) -> Map<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> O,
{
    Map { parser, map }
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

/// Construct a [`TryMap`], inferring the checked conversion's argument type.
/// Construction stores the callback; during parsing, conversion rejection
/// becomes `Mismatch` under the existing `TryMap` rules.
///
/// ```
/// use rusthammer::{try_map, BeU16, Cursor, ParseError, Parser};
/// let small = try_map(BeU16, u8::try_from);
/// assert_eq!(small.parse(&[1, 0], Cursor::start()), Err(ParseError::Mismatch));
/// ```
pub fn try_map<'input, P, F, O, E>(parser: P, map: F) -> TryMap<P, F>
where
    P: Grammar<'input>,
    F: Fn(P::Output) -> Result<O, E>,
{
    TryMap { parser, map }
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

/// Construct a [`Verify`], inferring the predicate's borrowed argument type.
/// The predicate is stored without being called and the output type is preserved.
///
/// ```
/// use rusthammer::{verify, Byte, Cursor, ParseError, Parser};
/// let version = verify(Byte, |value| *value <= 3);
/// assert_eq!(version.parse(&[4], Cursor::start()), Err(ParseError::Mismatch));
/// ```
pub fn verify<'input, P, F>(parser: P, predicate: F) -> Verify<P, F>
where
    P: Grammar<'input>,
    F: Fn(&P::Output) -> bool,
{
    Verify { parser, predicate }
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
