//! Extraction probe for collecting generic, borrowed, and non-Copy parser outputs.
#![no_std]

extern crate alloc;
use alloc::vec::Vec;

pub enum Outcome<T> {
    Success(usize, T),
    Error,
    NeedMore,
}

pub trait Parser<'input> {
    type Output;
    fn parse(&self, input: &'input [u8], cursor: usize, final_input: bool)
        -> Outcome<Self::Output>;
}

pub fn repeat<'input, P: Parser<'input>>(
    parser: &P,
    input: &'input [u8],
    cursor: usize,
    count: usize,
    final_input: bool,
) -> Outcome<Vec<P::Output>> {
    let mut values = Vec::new();
    let mut next = cursor;
    let mut remaining = count;
    while remaining != 0 {
        match parser.parse(input, next, final_input) {
            Outcome::Success(after, value) => {
                values.push(value);
                next = after;
                remaining -= 1;
            }
            Outcome::Error => return Outcome::Error,
            Outcome::NeedMore => return Outcome::NeedMore,
        }
    }
    Outcome::Success(next, values)
}

pub struct Borrowed<'input> {
    pub bytes: &'input [u8],
}

pub struct Byte;

impl<'input> Parser<'input> for Byte {
    type Output = Borrowed<'input>;

    fn parse(
        &self,
        input: &'input [u8],
        cursor: usize,
        final_input: bool,
    ) -> Outcome<Self::Output> {
        if cursor >= input.len() {
            if final_input {
                Outcome::Error
            } else {
                Outcome::NeedMore
            }
        } else {
            Outcome::Success(
                cursor + 1,
                Borrowed {
                    bytes: &input[cursor..cursor + 1],
                },
            )
        }
    }
}

pub fn borrowed(input: &[u8], count: usize, final_input: bool) -> Outcome<Vec<Borrowed<'_>>> {
    repeat(&Byte, input, 0, count, final_input)
}
