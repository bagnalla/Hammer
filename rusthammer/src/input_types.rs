/// A byte index and the number of bits consumed in that byte.
/// Bits are consumed from the most-significant end of each byte.
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
    /// rejection, including exhaustion of the complete input.
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

/// The significance of successive physical-byte fragments of a numeric field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteOrder {
    Big,
    Little,
}
