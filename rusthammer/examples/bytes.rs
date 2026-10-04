use rusthammer::{Byte, BytePattern, Cursor, Parser, Seq};

fn main() {
    let pattern = [0xab, 0xcd];
    let parser = Seq {
        first: BytePattern::new(&pattern),
        second: Byte,
    };
    let (next, (matched, value)) = {
        // One leading bit, AB CD 42, then seven trailing padding bits.
        let input = [0x55, 0xe6, 0xa1, 0x00];
        parser.parse(&input, Cursor { byte: 0, bit: 1 }).unwrap()
    };
    assert!(core::ptr::eq(matched, &pattern[..]));
    assert_eq!(value, 0x42);
    assert_eq!(next, Cursor { byte: 3, bit: 1 });
    println!("pattern: {matched:02x?}; byte: {value:02x}; next: {next:?}");
}
