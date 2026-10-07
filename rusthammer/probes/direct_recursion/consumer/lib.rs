#![no_std]
use rusthammer_direct_recursion_probe::{
    self as probe, BitSpan, Cursor, ParseContext, ParseOutcome, Parsed,
};

pub fn configured<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    context: ParseContext,
) -> ParseOutcome<Parsed<'pattern>> {
    probe::configured(pattern, input, context)
}
pub fn spanned<'input, 'pattern>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<(Parsed<'pattern>, BitSpan<'input>)> {
    probe::spanned(pattern, input, cursor, context)
}
pub fn recognized<'input>(
    pattern: &[u8],
    input: &'input [u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<BitSpan<'input>> {
    probe::recognized(pattern, input, cursor, context)
}
pub fn complete<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    context: ParseContext,
) -> ParseOutcome<(Parsed<'pattern>, ())> {
    probe::complete(pattern, input, context)
}
pub fn twice<'pattern>(
    pattern: &'pattern [u8],
    input: &[u8],
    context: ParseContext,
) -> ParseOutcome<(Parsed<'pattern>, Parsed<'pattern>)> {
    probe::twice(pattern, input, context)
}
pub fn count(input: &[u8], cursor: Cursor, context: ParseContext) -> ParseOutcome<usize> {
    probe::count(input, cursor, context)
}
