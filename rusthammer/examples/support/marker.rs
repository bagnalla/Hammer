//! Example marker format, shared by runnable examples, native tests, and extraction.
#[cfg(rusthammer_verify)]
use crate as rusthammer;
use rusthammer::{
    Choice, ConfigError, Cursor, End, Eval, Grammar, Literal, ParseContext, ParseError,
    ParseOutcome, Parser, Seq,
};

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

impl<'input> Grammar<'input> for Marker {
    type Output = u64;
}

impl<'input, Backend> Eval<'input, Backend> for Marker {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u64> {
        match self.parser.eval(backend, input, cursor, context) {
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
