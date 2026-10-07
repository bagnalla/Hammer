use super::super::{
    BitOrder, ByteOrder, ConfigError, Cursor, Eval, Grammar, Order, ParseContext, ParseError,
    ParseOutcome,
};

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
