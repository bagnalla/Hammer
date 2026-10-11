//! Private extraction experiment, not the production implementation or a proved library.
#![no_std]

pub mod candidates;
pub mod mavlink;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteOrder {
    Big,
    Little,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseError {
    InvalidCursor,
    UnexpectedEnd,
    Unaligned,
    Mismatch,
    NonProgress,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConfigError {
    InvalidWidth,
}

pub trait Parser<'input> {
    type Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError>;

    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parse_with(input, cursor, ByteOrder::Big)
    }
}

impl<'input, P: Parser<'input>> Parser<'input> for &P {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        (*self).parse_with(input, cursor, byte_order)
    }
}

fn valid(input: &[u8], cursor: Cursor) -> bool {
    cursor.bit < 8 && (cursor.byte < input.len() || (cursor.byte == input.len() && cursor.bit == 0))
}

#[derive(Clone, Copy)]
pub struct Bits {
    width: u8,
}

impl Bits {
    pub const fn new(width: u8) -> Result<Self, ConfigError> {
        if width <= 64 {
            Ok(Self { width })
        } else {
            Err(ConfigError::InvalidWidth)
        }
    }
}

impl<'input> Parser<'input> for Bits {
    type Output = u64;

    fn parse_with(
        &self,
        input: &'input [u8],
        mut cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, u64), ParseError> {
        if !valid(input, cursor) {
            return Err(ParseError::InvalidCursor);
        }
        let mut used = 0;
        let mut value = 0;
        while used < self.width {
            if cursor.byte == input.len() {
                return Err(ParseError::UnexpectedEnd);
            }
            let available = 8 - cursor.bit;
            let remaining = self.width - used;
            let count = if remaining < available {
                remaining
            } else {
                available
            };
            let shift = available - count;
            let fragment = ((input[cursor.byte] >> shift) as u64) & ((1u64 << count) - 1);
            value = match byte_order {
                ByteOrder::Big => (value << count) | fragment,
                ByteOrder::Little => value | (fragment << used),
            };
            used += count;
            cursor.bit += count;
            if cursor.bit == 8 {
                cursor.byte += 1;
                cursor.bit = 0;
            }
        }
        Ok((cursor, value))
    }
}

#[derive(Clone, Copy)]
pub struct Byte;

impl<'input> Parser<'input> for Byte {
    type Output = u8;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, u8), ParseError> {
        let parsed = Bits { width: 8 }.parse_with(input, cursor, byte_order)?;
        let (next, value) = parsed;
        Ok((next, value as u8))
    }
}

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
        _byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        if !valid(input, cursor) {
            return Err(ParseError::InvalidCursor);
        }
        if cursor.bit != 0 {
            return Err(ParseError::Unaligned);
        }
        if self.count > input.len() - cursor.byte {
            return Err(ParseError::UnexpectedEnd);
        }
        let end = cursor.byte + self.count;
        Ok((Cursor { byte: end, bit: 0 }, &input[cursor.byte..end]))
    }
}

#[derive(Clone, Copy)]
pub struct WithByteOrder<P> {
    pub parser: P,
    pub byte_order: ByteOrder,
}

impl<'input, P: Parser<'input>> Parser<'input> for WithByteOrder<P> {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        _byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parser.parse_with(input, cursor, self.byte_order)
    }
}

#[derive(Clone, Copy)]
pub struct Seq<P, Q> {
    pub first: P,
    pub second: Q,
}

pub const fn seq<P, Q>(first: P, second: Q) -> Seq<P, Q> {
    Seq { first, second }
}

impl<'input, P: Parser<'input>, Q: Parser<'input>> Parser<'input> for Seq<P, Q> {
    type Output = (P::Output, Q::Output);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        // Move each whole Result payload before destructuring its tuple. The
        // separate partial_enum_move control checks why this spelling matters.
        let first = self.first.parse_with(input, cursor, byte_order)?;
        let (middle, first) = first;
        let second = self.second.parse_with(input, middle, byte_order)?;
        let (end, second) = second;
        Ok((end, (first, second)))
    }
}

#[derive(Clone, Copy)]
pub struct Map<P, F> {
    pub parser: P,
    pub map: F,
}

pub fn map<'input, P: Parser<'input>, F: Fn(P::Output) -> O, O>(parser: P, map: F) -> Map<P, F> {
    Map { parser, map }
}

impl<'input, P: Parser<'input>, F: Fn(P::Output) -> O, O> Parser<'input> for Map<P, F> {
    type Output = O;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, O), ParseError> {
        let parsed = self.parser.parse_with(input, cursor, byte_order)?;
        let (next, value) = parsed;
        Ok((next, (self.map)(value)))
    }
}

#[derive(Clone, Copy)]
pub struct TryMap<P, F> {
    pub parser: P,
    pub map: F,
}

pub fn try_map<'input, P: Parser<'input>, F: Fn(P::Output) -> Result<O, E>, O, E>(
    parser: P,
    map: F,
) -> TryMap<P, F> {
    TryMap { parser, map }
}

impl<'input, P: Parser<'input>, F: Fn(P::Output) -> Result<O, E>, O, E> Parser<'input>
    for TryMap<P, F>
{
    type Output = O;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, O), ParseError> {
        let parsed = self.parser.parse_with(input, cursor, byte_order)?;
        let (next, value) = parsed;
        match (self.map)(value) {
            Ok(output) => Ok((next, output)),
            Err(_error) => Err(ParseError::Mismatch),
        }
    }
}

#[derive(Clone, Copy)]
pub struct Verify<P, F> {
    pub parser: P,
    pub predicate: F,
}

pub fn verify<'input, P: Parser<'input>, F: Fn(&P::Output) -> bool>(
    parser: P,
    predicate: F,
) -> Verify<P, F> {
    Verify { parser, predicate }
}

impl<'input, P: Parser<'input>, F: Fn(&P::Output) -> bool> Parser<'input> for Verify<P, F> {
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let parsed = self.parser.parse_with(input, cursor, byte_order)?;
        let (next, value) = parsed;
        if (self.predicate)(&value) {
            Ok((next, value))
        } else {
            Err(ParseError::Mismatch)
        }
    }
}

#[derive(Clone, Copy)]
pub struct Bind<P, F> {
    pub parser: P,
    pub then: F,
}

pub fn bind<'input, P: Parser<'input>, F: Fn(P::Output) -> Q, Q: Parser<'input>>(
    parser: P,
    then: F,
) -> Bind<P, F> {
    Bind { parser, then }
}

impl<'input, P: Parser<'input>, F: Fn(P::Output) -> Q, Q: Parser<'input>> Parser<'input>
    for Bind<P, F>
{
    type Output = Q::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let parsed = self.parser.parse_with(input, cursor, byte_order)?;
        let (next, value) = parsed;
        (self.then)(value).parse_with(input, next, byte_order)
    }
}

#[derive(Clone, Copy)]
pub struct Choice<P, Q> {
    pub first: P,
    pub second: Q,
}

pub fn choice<'input, P: Parser<'input>, Q: Parser<'input, Output = P::Output>>(
    first: P,
    second: Q,
) -> Choice<P, Q> {
    Choice { first, second }
}

impl<'input, P: Parser<'input>, Q: Parser<'input, Output = P::Output>> Parser<'input>
    for Choice<P, Q>
{
    type Output = P::Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        match self.first.parse_with(input, cursor, byte_order) {
            Err(ParseError::Mismatch | ParseError::UnexpectedEnd) => {
                self.second.parse_with(input, cursor, byte_order)
            }
            result => result,
        }
    }
}

#[derive(Clone, Copy)]
pub struct Optional<P> {
    pub parser: P,
}

pub const fn optional<P>(parser: P) -> Optional<P> {
    Optional { parser }
}

impl<'input, P: Parser<'input>> Parser<'input> for Optional<P> {
    type Output = Option<P::Output>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        match self.parser.parse_with(input, cursor, byte_order) {
            Ok(parsed) => {
                let (next, value) = parsed;
                Ok((next, Some(value)))
            }
            Err(ParseError::Mismatch | ParseError::UnexpectedEnd) => Ok((cursor, None)),
            Err(error) => Err(error),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitSpan<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
}

impl<'input> BitSpan<'input> {
    pub fn as_bytes(&self) -> Option<&'input [u8]> {
        if self.start.bit == 0 && self.end.bit == 0 {
            Some(&self.input[self.start.byte..self.end.byte])
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
pub struct WithSpan<P> {
    pub parser: P,
}

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
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let parsed = seq(&self.first, &self.second).parse_with(input, cursor, byte_order)?;
        let (next, values) = parsed;
        let (_first, second) = values;
        Ok((next, second))
    }
}

impl<'input, P: Parser<'input>> Parser<'input> for WithSpan<P> {
    type Output = (P::Output, BitSpan<'input>);

    fn parse_with(
        &self,
        input: &'input [u8],
        start: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        if !valid(input, start) {
            return Err(ParseError::InvalidCursor);
        }
        let parsed = self.parser.parse_with(input, start, byte_order)?;
        let (end, value) = parsed;
        if !valid(input, end) {
            return Err(ParseError::InvalidCursor);
        }
        if end.byte < start.byte || (end.byte == start.byte && end.bit < start.bit) {
            return Err(ParseError::NonProgress);
        }
        Ok((end, (value, BitSpan { input, start, end })))
    }
}

#[derive(Clone, Copy)]
pub struct Pattern<'pattern> {
    pub bytes: &'pattern [u8],
}

// Keep the loop outside the Result-derived borrow's scope. See the isolated
// candidates::pattern_loop reproduction of the extractor's context-join error.
fn equal_bytes(first: &[u8], second: &[u8]) -> bool {
    if first.len() != second.len() {
        return false;
    }
    let mut index = 0;
    while index < first.len() {
        if first[index] != second[index] {
            return false;
        }
        index += 1;
    }
    true
}

impl<'input, 'pattern> Parser<'input> for Pattern<'pattern> {
    type Output = &'pattern [u8];

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let parsed = TakeAligned {
            count: self.bytes.len(),
        }
        .parse_with(input, cursor, byte_order)?;
        let (next, bytes) = parsed;
        if !equal_bytes(bytes, self.bytes) {
            return Err(ParseError::Mismatch);
        }
        Ok((next, self.bytes))
    }
}

// These closures are deliberately constructed inside lifetime-generic methods.
pub struct LocalCallbacks;

impl<'input> Parser<'input> for LocalCallbacks {
    type Output = &'input [u8];

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let length = map(Byte, |value| value as usize);
        bind(&length, |count| TakeAligned { count }).parse_with(input, cursor, byte_order)
    }
}

pub fn local_callbacks(input: &[u8], cursor: Cursor) -> Result<(Cursor, &[u8]), ParseError> {
    LocalCallbacks.parse(input, cursor)
}

pub fn opaque_payload(
    count: usize,
) -> impl for<'input> Parser<'input, Output = &'input [u8]> + Copy {
    TakeAligned { count }
}

pub fn opaque_number() -> impl for<'input> Parser<'input, Output = u64> + Copy {
    Bits { width: 16 }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Value(pub u16);

pub fn mapped_number(bias: u16) -> Map<Byte, impl Fn(u8) -> Value + Copy> {
    map(Byte, move |value| Value(value as u16 + bias))
}

pub fn owned(input: &[u8], cursor: Cursor) -> Result<(Cursor, (Value, u8)), ParseError> {
    let parser = mapped_number(1);
    seq(&parser, Byte).parse(input, cursor)
}

pub fn checked(
    input: &[u8],
    cursor: Cursor,
    limit: u8,
) -> Result<(Cursor, Option<u16>), ParseError> {
    let first = try_map(Byte, move |value| {
        if value < limit {
            Ok(value as u16)
        } else {
            Err(())
        }
    });
    let second = map(verify(Byte, |value| *value == 255), |_| 256u16);
    optional(choice(first, second)).parse(input, cursor)
}

pub fn independent<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    count: usize,
) -> Result<(Cursor, (&'pattern [u8], &'input [u8])), ParseError> {
    let parser = Pattern { bytes: pattern };
    seq(&parser, opaque_payload(count)).parse(input, Cursor::start())
}

pub fn ordered(input: &[u8], cursor: Cursor) -> Result<(Cursor, (u64, u64)), ParseError> {
    seq(
        WithByteOrder {
            parser: opaque_number(),
            byte_order: ByteOrder::Little,
        },
        opaque_number(),
    )
    .parse(input, cursor)
}

pub fn run_parser<'input, P: Parser<'input>>(
    parser: &P,
    input: &'input [u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, P::Output), ParseError> {
    parser.parse_with(input, cursor, byte_order)
}

#[cfg(test)]
mod tests;
