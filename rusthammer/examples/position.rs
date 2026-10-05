use rusthammer::{Bind, Byte, Cursor, Parser, Right, Seq, SkipBits, Tell};

fn main() {
    let parser = Right {
        first: Bind {
            parser: Byte,
            then: |bits| SkipBits::new(usize::from(bits)),
        },
        second: Seq {
            first: Tell,
            second: Byte,
        },
    };
    let (next, (field_start, value)) = parser
        .parse(&[3, 0b0001_0100, 0b1100_0000], Cursor::start())
        .unwrap();
    assert_eq!(field_start, Cursor { byte: 1, bit: 3 });
    assert_eq!(value, 0xa6);
    println!("field at {field_start:?}: {value:#x}; next cursor: {next:?}");
}
