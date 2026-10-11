#[path = "support/dependent.rs"]
mod formats;

use rusthammer::{ByteOrder, Cursor, ParseError};

fn main() {
    let input = b"\x03abc!";
    let outcome = formats::payload(input, Cursor::start(), ByteOrder::Big);
    assert_eq!(outcome, Ok((Cursor { byte: 4, bit: 0 }, &b"abc"[..])));
    println!("payload: {outcome:?}");

    assert_eq!(
        formats::payload(&input[..3], Cursor::start(), ByteOrder::Big),
        Err(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        formats::payload(b"\x41", Cursor::start(), ByteOrder::Big),
        Err(ParseError::Mismatch)
    );

    #[cfg(feature = "alloc")]
    {
        // The prefix counts four-bit elements, not bytes.
        let outcome = formats::fields(&[3, 0xab, 0xc0], Cursor::start(), ByteOrder::Big);
        assert_eq!(outcome, Ok((Cursor { byte: 2, bit: 4 }, vec![10, 11, 12])));
        println!("fields: {outcome:?}");
    }
}
