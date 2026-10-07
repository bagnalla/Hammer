#![no_std]
use rusthammer_recursive_rules_probe::{self as probe, Answer, Owned, ParseContext};

pub fn recursive(mode: u8, input: &[u8], context: ParseContext) -> Answer<usize> {
    probe::parse(mode, input, context, 256, 100_000)
}
pub fn borrowed(input: &[u8], context: ParseContext) -> Answer<&[u8]> {
    probe::borrowed(input, context)
}
pub fn pattern<'p>(pattern: &'p [u8], input: &[u8], context: ParseContext) -> Answer<&'p [u8]> {
    probe::pattern(pattern, input, context)
}
pub fn owned(input: &[u8]) -> Answer<Owned> {
    probe::owned(input)
}

pub fn lowered(input: &[u8], context: ParseContext) -> Answer<&[u8]> {
    probe::lowered(input, context)
}

pub fn bit_span(input: &[u8], context: ParseContext) -> Answer<probe::Span<'_>> {
    probe::bit_span(input, context)
}
