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
    pub(crate) fn classify<T>(self, result: Result<(Cursor, T), ParseError>) -> ParseOutcome<T> {
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
    pub(crate) fn into_complete(self) -> Result<(Cursor, T), ParseError> {
        match self {
            Self::Success(next, value) => Ok((next, value)),
            Self::Error(error) => Err(error),
            // Built-in parsers never return NeedMore on final input. Keep the
            // complete API total even for custom parsers that violate that rule.
            Self::NeedMore => Err(ParseError::UnexpectedEnd),
        }
    }
}
