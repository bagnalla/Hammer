//! Check the proposed interpreter and typed tables through a Cargo dependency.
#![no_std]

use rusthammer_backend_probe::{self as probe, OwnedByte, ParseContext, ParseOutcome};

pub fn borrowed(input: &[u8], context: ParseContext) -> ParseOutcome<(&[u8], u8)> {
    probe::packrat(input, context)
}

pub fn owned(input: &[u8], context: ParseContext) -> ParseOutcome<OwnedByte> {
    probe::owned_output(input, context)
}

pub fn recursive(input: &[u8], context: ParseContext) -> ParseOutcome<usize> {
    probe::recursive_packrat(input, context)
}

pub fn independent_borrows<'input, 'pattern>(
    input: &'input [u8],
    pattern: &'pattern [u8],
    context: ParseContext,
) -> ParseOutcome<(&'input [u8], &'pattern [u8])> {
    probe::distinct_borrows(input, pattern, context)
}
