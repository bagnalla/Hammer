//! Minimal extraction probe for finality, three outcomes, and borrowed outputs.
#![no_std]

pub enum InputStatus {
    Partial,
    Final,
}

pub enum ParseError {
    UnexpectedEnd,
}

pub enum ParseOutcome<T> {
    Success(usize, T),
    Error(ParseError),
    NeedMore,
}

pub trait Parser<'input> {
    type Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: usize,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output>;

    fn parse(
        &self,
        input: &'input [u8],
        cursor: usize,
    ) -> Result<(usize, Self::Output), ParseError> {
        match self.parse_with(input, cursor, InputStatus::Final) {
            ParseOutcome::Success(next, value) => Ok((next, value)),
            ParseOutcome::Error(error) => Err(error),
            ParseOutcome::NeedMore => Err(ParseError::UnexpectedEnd),
        }
    }
}

pub struct Byte;

impl<'input> Parser<'input> for Byte {
    type Output = &'input [u8];

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: usize,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        if cursor >= input.len() {
            match status {
                InputStatus::Partial => ParseOutcome::NeedMore,
                InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
            }
        } else {
            ParseOutcome::Success(cursor + 1, &input[cursor..cursor + 1])
        }
    }
}

pub struct Optional<P> {
    pub parser: P,
}

impl<'input, P: Parser<'input>> Parser<'input> for Optional<P> {
    type Output = Option<P::Output>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: usize,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.parse_with(input, cursor, status) {
            ParseOutcome::Success(next, value) => ParseOutcome::Success(next, Some(value)),
            ParseOutcome::Error(_) => ParseOutcome::Success(cursor, None),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

pub fn complete(input: &[u8]) -> Result<(usize, Option<&[u8]>), ParseError> {
    Optional { parser: Byte }.parse(input, 0)
}

pub fn partial(input: &[u8]) -> ParseOutcome<Option<&[u8]>> {
    Optional { parser: Byte }.parse_with(input, 0, InputStatus::Partial)
}
