#[path = "support/flags.rs"]
mod flags_example;

use flags_example::parse_flags;
use rusthammer::Cursor;

fn main() {
    let (next, flags) = parse_flags(&[0b1010_0000], Cursor::start()).unwrap();
    println!("{flags:?}; next cursor: {next:?}");
}
