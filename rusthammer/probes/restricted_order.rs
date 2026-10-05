//! Private probe of byte-boundary bit-order scopes; not a library API.
#![cfg_attr(not(any(test, restricted_order_driver)), no_std)]

#[derive(Clone, Copy)]
#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
pub struct Cursor {
    pub byte: usize,
    pub bit: u8,
}

impl Cursor {
    pub fn valid(self, length: usize) -> bool {
        self.bit < 8 && (self.byte < length || (self.byte == length && self.bit == 0))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(any(test, restricted_order_driver), derive(Debug))]
pub enum BitOrder {
    HighFirst,
    LowFirst,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
pub enum ByteOrder {
    Big,
    Little,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
pub struct Order {
    pub bit: BitOrder,
    pub byte: ByteOrder,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
pub enum InputStatus {
    Final,
    Partial,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
pub struct ParseContext {
    pub order: Order,
    pub status: InputStatus,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
pub enum ParseError {
    InvalidCursor,
    UnexpectedEnd,
    Unaligned,
    Mismatch,
    TrailingInput,
    NonProgress,
    CountOverflow,
}

impl ParseError {
    fn is_recoverable(self) -> bool {
        matches!(
            self,
            Self::Mismatch | Self::UnexpectedEnd | Self::TrailingInput
        )
    }
}

#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
pub enum Outcome<T> {
    Success(Cursor, T),
    Error(ParseError),
    NeedMore,
}

pub trait Parser<'input> {
    type Output;
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        ctx: ParseContext,
    ) -> Outcome<Self::Output>;
}

/// Bounds take precedence over alignment, on both scope boundaries.
pub fn boundary_error(length: usize, cursor: Cursor) -> Option<ParseError> {
    if !cursor.valid(length) {
        Some(ParseError::InvalidCursor)
    } else if cursor.bit != 0 {
        Some(ParseError::Unaligned)
    } else {
        None
    }
}

pub fn finish_scope<T>(length: usize, changed: bool, result: Outcome<T>) -> Outcome<T> {
    if !changed {
        return result;
    }
    match result {
        Outcome::Success(next, value) => match boundary_error(length, next) {
            Some(error) => Outcome::Error(error),
            None => Outcome::Success(next, value),
        },
        Outcome::Error(error) => Outcome::Error(error),
        Outcome::NeedMore => Outcome::NeedMore,
    }
}

pub struct WithOrder<P> {
    pub order: Order,
    pub child: P,
}

impl<'input, P: Parser<'input>> Parser<'input> for WithOrder<P> {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        ctx: ParseContext,
    ) -> Outcome<Self::Output> {
        let changed = self.order.bit != ctx.order.bit;
        if changed {
            if let Some(error) = boundary_error(input.len(), cursor) {
                return Outcome::Error(error);
            }
        }
        let result = self.child.parse_with(
            input,
            cursor,
            ParseContext {
                order: self.order,
                status: ctx.status,
            },
        );
        finish_scope(input.len(), changed, result)
    }
}

pub struct Field {
    width: u8,
}

impl Field {
    pub fn new(width: u8) -> Option<Self> {
        if width <= 64 {
            Some(Self { width })
        } else {
            None
        }
    }
}

impl<'input> Parser<'input> for Field {
    type Output = u64;

    fn parse_with(&self, input: &'input [u8], cursor: Cursor, ctx: ParseContext) -> Outcome<u64> {
        if !cursor.valid(input.len()) {
            return Outcome::Error(ParseError::InvalidCursor);
        }
        let mut cursor = cursor;
        let mut done = 0;
        let mut value = 0;
        loop {
            if done == self.width {
                return Outcome::Success(cursor, value);
            }
            if cursor.byte == input.len() {
                return match ctx.status {
                    InputStatus::Partial => Outcome::NeedMore,
                    InputStatus::Final => Outcome::Error(ParseError::UnexpectedEnd),
                };
            }
            let available = 8 - cursor.bit;
            let needed = self.width - done;
            let take = if needed < available {
                needed
            } else {
                available
            };
            let shift = match ctx.order.bit {
                BitOrder::HighFirst => 8 - cursor.bit - take,
                BitOrder::LowFirst => cursor.bit,
            };
            // Bit direction selects a fragment; it does not reverse its bits.
            let fragment = ((input[cursor.byte] as u64) >> shift) & ((1u64 << take) - 1);
            value = match ctx.order.byte {
                ByteOrder::Big => (value << take) | fragment,
                ByteOrder::Little => value | (fragment << done),
            };
            cursor.bit += take;
            if cursor.bit == 8 {
                cursor.byte += 1;
                cursor.bit = 0;
            }
            done += take;
        }
    }
}

pub struct Seq<P, Q>(pub P, pub Q);

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Seq<P, Q> {
    type Output = (P::Output, Q::Output);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        ctx: ParseContext,
    ) -> Outcome<Self::Output> {
        match self.0.parse_with(input, cursor, ctx) {
            Outcome::Success(next, first) => match self.1.parse_with(input, next, ctx) {
                Outcome::Success(end, second) => Outcome::Success(end, (first, second)),
                Outcome::Error(error) => Outcome::Error(error),
                Outcome::NeedMore => Outcome::NeedMore,
            },
            Outcome::Error(error) => Outcome::Error(error),
            Outcome::NeedMore => Outcome::NeedMore,
        }
    }
}

pub struct And<P>(pub P);
pub struct Not<P>(pub P);

impl<'input, P: Parser<'input>> Parser<'input> for And<P> {
    type Output = ();

    fn parse_with(&self, input: &'input [u8], cursor: Cursor, ctx: ParseContext) -> Outcome<()> {
        match self.0.parse_with(input, cursor, ctx) {
            Outcome::Success(_, _) => Outcome::Success(cursor, ()),
            Outcome::Error(error) => Outcome::Error(error),
            Outcome::NeedMore => Outcome::NeedMore,
        }
    }
}

impl<'input, P: Parser<'input>> Parser<'input> for Not<P> {
    type Output = ();

    fn parse_with(&self, input: &'input [u8], cursor: Cursor, ctx: ParseContext) -> Outcome<()> {
        match self.0.parse_with(input, cursor, ctx) {
            Outcome::Success(_, _) => Outcome::Error(ParseError::Mismatch),
            Outcome::Error(error) => {
                if error.is_recoverable() {
                    Outcome::Success(cursor, ())
                } else {
                    Outcome::Error(error)
                }
            }
            Outcome::NeedMore => Outcome::NeedMore,
        }
    }
}

#[cfg_attr(any(test, restricted_order_driver), derive(Debug, PartialEq, Eq))]
// Construction is extracted; native tests inspect the escaped partial span.
#[allow(dead_code)]
pub struct Span<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
    bit_order: BitOrder,
}

pub struct WithSpan<P>(pub P);

impl<'input, P: Parser<'input>> Parser<'input> for WithSpan<P> {
    type Output = (P::Output, Span<'input>);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        ctx: ParseContext,
    ) -> Outcome<Self::Output> {
        if !cursor.valid(input.len()) {
            return Outcome::Error(ParseError::InvalidCursor);
        }
        match self.0.parse_with(input, cursor, ctx) {
            Outcome::Success(end, value) => {
                if !end.valid(input.len()) {
                    return Outcome::Error(ParseError::InvalidCursor);
                }
                if end.byte < cursor.byte || (end.byte == cursor.byte && end.bit < cursor.bit) {
                    return Outcome::Error(ParseError::NonProgress);
                }
                // Early validation returns retain the source shape that passed
                // optimized extraction in the earlier input-order probe.
                Outcome::Success(
                    end,
                    (
                        value,
                        Span {
                            input,
                            start: cursor,
                            end,
                            bit_order: ctx.order.bit,
                        },
                    ),
                )
            }
            Outcome::Error(error) => Outcome::Error(error),
            Outcome::NeedMore => Outcome::NeedMore,
        }
    }
}

/// Same five-field shape as the historical C comparison adapter.
pub fn nested(
    input: &[u8],
    widths: [u8; 5],
    outer: Order,
    inner: Order,
    ctx: ParseContext,
) -> Option<Outcome<(u64, (u64, (u64, u64)), u64)>> {
    let a = match Field::new(widths[0]) {
        Some(p) => p,
        None => return None,
    };
    let b = match Field::new(widths[1]) {
        Some(p) => p,
        None => return None,
    };
    let c = match Field::new(widths[2]) {
        Some(p) => p,
        None => return None,
    };
    let d = match Field::new(widths[3]) {
        Some(p) => p,
        None => return None,
    };
    let e = match Field::new(widths[4]) {
        Some(p) => p,
        None => return None,
    };
    let parser = Seq(
        a,
        Seq(
            WithOrder {
                order: outer,
                child: Seq(
                    b,
                    Seq(
                        WithOrder {
                            order: inner,
                            child: c,
                        },
                        d,
                    ),
                ),
            },
            e,
        ),
    );
    Some(
        match parser.parse_with(input, Cursor { byte: 0, bit: 0 }, ctx) {
            Outcome::Success(end, payload) => {
                let (a, (middle, e)) = payload;
                Outcome::Success(end, (a, middle, e))
            }
            Outcome::Error(error) => Outcome::Error(error),
            Outcome::NeedMore => Outcome::NeedMore,
        },
    )
}

/// The low-first span leaves its scope as output after the scope reaches alignment.
pub fn escaped_span(input: &[u8], ctx: ParseContext) -> Outcome<((u64, Span<'_>), u64)> {
    WithOrder {
        order: Order {
            bit: BitOrder::LowFirst,
            byte: ByteOrder::Big,
        },
        child: Seq(WithSpan(Field { width: 3 }), Field { width: 5 }),
    }
    .parse_with(input, Cursor { byte: 0, bit: 0 }, ctx)
}

/// Extract concrete lookahead compositions as well as their generic bodies.
pub fn lookahead(input: &[u8], ctx: ParseContext) -> Outcome<((), ())> {
    let order = Order {
        bit: BitOrder::LowFirst,
        byte: ByteOrder::Big,
    };
    Seq(
        WithOrder {
            order,
            child: And(Field { width: 3 }),
        },
        Not(WithOrder {
            order,
            child: Field { width: 3 },
        }),
    )
    .parse_with(input, Cursor { byte: 0, bit: 0 }, ctx)
}

#[cfg(test)]
#[path = "restricted_order_tests.rs"]
mod tests;

#[cfg(restricted_order_driver)]
include!("restricted_order_driver.rs");
