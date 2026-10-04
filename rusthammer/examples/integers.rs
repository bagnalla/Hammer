use rusthammer::{BeI16, BeU16, Cursor, Parser, Seq};

fn main() {
    let parser = Seq {
        first: BeU16,
        second: BeI16,
    };
    let (next, (count, adjustment)): (Cursor, (u16, i16)) = parser
        .parse(&[0x12, 0x34, 0xff, 0xfd], Cursor::start())
        .unwrap();
    assert_eq!((count, adjustment), (0x1234, -3));
    assert_eq!(next, Cursor { byte: 4, bit: 0 });
    println!("count: {count}, adjustment: {adjustment}; next cursor: {next:?}");
}
