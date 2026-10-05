//! Historical unrestricted-order probe, not imported by the RustHammer library.
//! Superseded by plans/rusthammer-input.md's byte-boundary scope restriction.
#![cfg_attr(not(any(test, input_order_driver)), no_std)]

#[derive(Clone, Copy)]
#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub struct Cursor {
    byte: usize,
    high: u8,
    low: u8,
}

impl Cursor {
    pub fn new(byte: usize, high: u8, low: u8) -> Option<Self> {
        if high >= 8 || low >= 8 || high + low >= 8 {
            None
        } else {
            Some(Self { byte, high, low })
        }
    }

    pub fn parts(self) -> (usize, u8, u8) {
        (self.byte, self.high, self.low)
    }

    pub fn valid(self, length: usize) -> bool {
        self.high < 8
            && self.low < 8
            && self.high + self.low < 8
            && (self.byte < length || (self.byte == length && self.high == 0 && self.low == 0))
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub enum BitOrder {
    HighFirst,
    LowFirst,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub enum ByteOrder {
    Big,
    Little,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub struct Order {
    pub bit: BitOrder,
    pub byte: ByteOrder,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub enum InputStatus {
    Final,
    Partial,
}

#[derive(Clone, Copy)]
#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub struct Context {
    pub order: Order,
    pub status: InputStatus,
}

#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub enum Error {
    InvalidCursor,
    UnexpectedEnd,
    NonForward,
}

#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
pub enum Outcome<T> {
    Success(Cursor, T),
    Error(Error),
    NeedMore,
}

fn shortage<T>(status: InputStatus) -> Outcome<T> {
    match status {
        InputStatus::Final => Outcome::Error(Error::UnexpectedEnd),
        InputStatus::Partial => Outcome::NeedMore,
    }
}

/// Core transition proved in input_order_proofs.lean. The caller establishes
/// high + low < 8, take <= 8 - high - low, and byte < the input length.
pub fn advance_segment(cursor: Cursor, take: u8, order: BitOrder) -> Cursor {
    if cursor.high + cursor.low + take == 8 {
        Cursor {
            byte: cursor.byte + 1,
            high: 0,
            low: 0,
        }
    } else {
        match order {
            BitOrder::HighFirst => Cursor {
                byte: cursor.byte,
                high: cursor.high + take,
                low: cursor.low,
            },
            BitOrder::LowFirst => Cursor {
                byte: cursor.byte,
                high: cursor.high,
                low: cursor.low + take,
            },
        }
    }
}

pub trait Parser<'input> {
    type Output;
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        context: Context,
    ) -> Outcome<Self::Output>;
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

    fn parse_with(&self, input: &'input [u8], cursor: Cursor, ctx: Context) -> Outcome<u64> {
        if !cursor.valid(input.len()) {
            return Outcome::Error(Error::InvalidCursor);
        }
        let mut cursor = cursor;
        let mut done = 0;
        let mut value = 0;
        loop {
            if done == self.width {
                return Outcome::Success(cursor, value);
            }
            if cursor.byte == input.len() {
                return shortage(ctx.status);
            }
            let available = 8 - cursor.high - cursor.low;
            let needed = self.width - done;
            let take = if needed < available {
                needed
            } else {
                available
            };
            let shift = match ctx.order.bit {
                BitOrder::HighFirst => 8 - cursor.high - take,
                BitOrder::LowFirst => cursor.low,
            };
            // A physical-byte fragment keeps its ordinary binary significance.
            // In particular, LowFirst does not reverse the fragment's bits.
            let fragment = ((input[cursor.byte] as u64) >> shift) & ((1u64 << take) - 1);
            value = match ctx.order.byte {
                ByteOrder::Big => (value << take) | fragment,
                ByteOrder::Little => value | (fragment << done),
            };
            cursor = advance_segment(cursor, take, ctx.order.bit);
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
        ctx: Context,
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
        ctx: Context,
    ) -> Outcome<Self::Output> {
        self.child.parse_with(
            input,
            cursor,
            Context {
                order: self.order,
                status: ctx.status,
            },
        )
    }
}

/// Only meaningful for normalized, input-valid cursors. It allows an empty span.
pub fn forward(start: Cursor, end: Cursor) -> bool {
    end.byte > start.byte
        || (end.byte == start.byte && end.high >= start.high && end.low >= start.low)
}

#[cfg_attr(any(test, input_order_driver), derive(Debug, PartialEq, Eq))]
// Native tests inspect these fields; extraction currently probes construction.
#[allow(dead_code)]
pub struct Span<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
}

pub struct WithSpan<P>(pub P);

impl<'input, P: Parser<'input>> Parser<'input> for WithSpan<P> {
    type Output = (P::Output, Span<'input>);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        ctx: Context,
    ) -> Outcome<Self::Output> {
        if !cursor.valid(input.len()) {
            return Outcome::Error(Error::InvalidCursor);
        }
        match self.0.parse_with(input, cursor, ctx) {
            Outcome::Success(end, value) => {
                if !end.valid(input.len()) {
                    return Outcome::Error(Error::InvalidCursor);
                }
                if !forward(cursor, end) {
                    return Outcome::Error(Error::NonForward);
                }
                // Attach the borrow after returning validation errors. Putting
                // this success inside the final `else` instead failed optimized
                // extraction in the pinned Aeneas (InterpJoin context mismatch).
                Outcome::Success(
                    end,
                    (
                        value,
                        Span {
                            input,
                            start: cursor,
                            end,
                        },
                    ),
                )
            }
            Outcome::Error(error) => Outcome::Error(error),
            Outcome::NeedMore => Outcome::NeedMore,
        }
    }
}

/// O(1) skip; the count and byte index never become absolute machine bit counts.
pub fn skip_bits(input: &[u8], cursor: Cursor, bits: usize, ctx: Context) -> Outcome<()> {
    if !cursor.valid(input.len()) {
        return Outcome::Error(Error::InvalidCursor);
    }
    if bits == 0 {
        return Outcome::Success(cursor, ());
    }
    if cursor.byte == input.len() {
        return shortage(ctx.status);
    }
    let available = 8 - cursor.high - cursor.low;
    if bits < available as usize {
        return Outcome::Success(advance_segment(cursor, bits as u8, ctx.order.bit), ());
    }
    let next = cursor.byte + 1;
    let left = bits - available as usize;
    let whole = left / 8;
    let tail = (left % 8) as u8;
    if whole > input.len() - next {
        return shortage(ctx.status);
    }
    let byte = next + whole;
    if byte == input.len() && tail != 0 {
        return shortage(ctx.status);
    }
    let end = match ctx.order.bit {
        BitOrder::HighFirst => Cursor {
            byte,
            high: tail,
            low: 0,
        },
        BitOrder::LowFirst => Cursor {
            byte,
            high: 0,
            low: tail,
        },
    };
    Outcome::Success(end, ())
}

/// Concrete nested scopes plus a borrowed result, for both MIR stages.
pub fn nested<'input>(
    input: &'input [u8],
    widths: [u8; 5],
    outer: Order,
    inner: Order,
    ctx: Context,
) -> Option<Outcome<((u64, (u64, (u64, u64)), u64), Span<'input>)>> {
    // Deliberately use validated constructors; malformed configurations are not
    // parsing failures. These matches keep the probe free of formatter models.
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
    let parser = WithSpan(Seq(
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
    ));
    let start = Cursor {
        byte: 0,
        high: 0,
        low: 0,
    };
    Some(match parser.parse_with(input, start, ctx) {
        Outcome::Success(end, payload) => {
            let ((a, (middle, e)), span) = payload;
            Outcome::Success(end, ((a, middle, e), span))
        }
        Outcome::Error(error) => Outcome::Error(error),
        Outcome::NeedMore => Outcome::NeedMore,
    })
}

#[cfg(test)]
#[path = "input_order_tests.rs"]
mod tests;

#[cfg(input_order_driver)]
include!("input_order_driver.rs");
