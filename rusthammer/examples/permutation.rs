use rusthammer::{
    optional, permutation, required, BeU16, Byte, BytePattern, Cursor, Parser, Right,
};

fn main() {
    let parser = permutation((
        required(Right {
            first: BytePattern::new(b"v"),
            second: Byte,
        }),
        required(Right {
            first: BytePattern::new(b"n"),
            second: BeU16,
        }),
        optional(BytePattern::new(b"!")),
    ));
    // The input supplies length before version. Output follows the tuple order.
    let (next, (version, length, marker)) =
        parser.parse(b"n\x00\x03v\x01!", Cursor::start()).unwrap();
    assert_eq!((version, length, marker), (1, 3, Some(&b"!"[..])));
    println!("version: {version}; length: {length}; marker: {marker:?}; next: {next:?}");
}
