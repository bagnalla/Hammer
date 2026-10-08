#[path = "support/offset.rs"]
mod offset;

use rusthammer::{Cursor, ParseContext};

fn main() {
    let input = [2, 0xaa, 0xbb, 0x12, 0x34, 0xff];
    println!(
        "{:?}",
        offset::payload(&input, Cursor::start(), ParseContext::FINAL)
    );
}
