//! Regression probe for the deferred borrowed callback limitation.
#![no_std]

#[path = "../src/lib.rs"]
mod rusthammer;
use rusthammer::{Cursor, FoldRepeat, InputStatus, ParseOutcome, Parser, TakeAligned};

/// Borrowed accumulators also need no cloning or allocation.
pub fn last_block(input: &[u8], count: usize, status: InputStatus) -> ParseOutcome<&[u8]> {
    let empty = &input[..0];
    FoldRepeat::exact(TakeAligned { count: 1 }, count, || empty, |_previous, byte| byte).parse_with(
        input,
        Cursor::start(),
        status,
    )
}
