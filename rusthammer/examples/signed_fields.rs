use rusthammer::{Bits, ConfigError, Cursor, Parser, Seq, SignedBits};

fn main() -> Result<(), ConfigError> {
    let parser = Seq {
        first: SignedBits::new(5)?,
        second: Bits::new(3)?,
    };
    // Three prefix bits, then 11101 (-3) and 101 (5), followed by padding.
    let (next, (adjustment, flags)) = parser
        .parse(&[0x1d, 0xa0], Cursor { byte: 0, bit: 3 })
        .unwrap();
    assert_eq!((adjustment, flags), (-3i64, 5u64));
    assert_eq!(next, Cursor { byte: 1, bit: 3 });
    println!("adjustment: {adjustment}; flags: {flags}; next: {next:?}");
    Ok(())
}
