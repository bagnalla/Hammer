use rusthammer::{Bits, ConfigError, Cursor, Parser, Seq};

fn main() -> Result<(), ConfigError> {
    let parser = Seq {
        first: Bits::new(3)?,
        second: Bits::new(13)?,
    };
    let (next, (version, length)) = parser.parse(&[0xa1, 0x34], Cursor::start()).unwrap();
    println!("version: {version}; length: {length}; next cursor: {next:?}");
    Ok(())
}
