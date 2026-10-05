use rusthammer::{ByteIn, ByteNotIn, Cursor, FoldRepeat, Left, ParseError, Parser};

fn main() -> Result<(), ParseError> {
    // Count a nonempty field and consume its comma/semicolon delimiter.
    let field = Left {
        first: FoldRepeat::at_least(ByteNotIn::new(b",;"), 1, || 0usize, |count, _| count + 1),
        second: ByteIn::new(b",;"),
    };
    let (next, count) = field.parse(b"hello;rest", Cursor::start())?;
    assert_eq!(count, 5);
    assert_eq!(next, Cursor { byte: 6, bit: 0 });
    println!("field length: {count}; next cursor: {next:?}");
    Ok(())
}
