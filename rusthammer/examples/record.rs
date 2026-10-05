#[path = "support/record.rs"]
mod record_example;

use record_example::{parse_record, RecordParser};
use rusthammer::{ConfigError, Cursor};

fn main() -> Result<(), ConfigError> {
    let parser = RecordParser::new()?;
    // Version 1, flags 5, length 3, followed by the borrowed payload.
    let input = [0x25, 0, 3, 0xca, 0xfe, 0x01];
    let (next, record) = parse_record(&input, Cursor::start(), &parser).unwrap();
    println!("{record:?}; next cursor: {next:?}");
    Ok(())
}
