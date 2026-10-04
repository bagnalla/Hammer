use rusthammer::{BeI16, BeU16, Byte, ConfigError, Cursor, IntRange, Parser, Seq};

fn main() -> Result<(), ConfigError> {
    let parser = Seq {
        first: IntRange::new(BeU16, 1u16, 4096u16)?,
        second: Seq {
            first: IntRange::new(BeI16, -100i16, 100i16)?,
            second: IntRange::new(Byte, b'0', b'9')?,
        },
    };
    let (next, (length, (adjustment, digit))) = parser
        .parse(&[0x01, 0x00, 0xff, 0xfd, b'7'], Cursor::start())
        .unwrap();
    assert_eq!((length, adjustment, digit), (256u16, -3i16, b'7'));
    assert_eq!(next, Cursor { byte: 5, bit: 0 });
    println!(
        "length: {length}, adjustment: {adjustment}, digit: {}; next cursor: {next:?}",
        char::from(digit)
    );
    Ok(())
}
