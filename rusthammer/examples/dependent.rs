#[path = "support/dependent.rs"]
mod formats;

use rusthammer::{Cursor, ParseContext, ParseError, ParseOutcome};

fn main() {
    let input = b"\x03abc!";
    let outcome = formats::payload(input, Cursor::start(), ParseContext::PARTIAL);
    assert_eq!(
        outcome,
        ParseOutcome::Success(Cursor { byte: 4, bit: 0 }, &b"abc"[..])
    );
    println!("payload: {outcome:?}");
    assert_eq!(
        formats::payload(&input[..3], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        formats::payload(&input[..3], Cursor::start(), ParseContext::FINAL),
        ParseOutcome::Error(ParseError::UnexpectedEnd)
    );
    assert_eq!(
        formats::payload(b"\x41", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Error(ParseError::Mismatch)
    );

    #[cfg(feature = "alloc")]
    {
        // The prefix counts four-bit elements, not bytes.
        let outcome = formats::fields(&[3, 0xab, 0xc0], Cursor::start(), ParseContext::PARTIAL);
        assert_eq!(
            outcome,
            ParseOutcome::Success(Cursor { byte: 2, bit: 4 }, vec![10, 11, 12])
        );
        println!("fields: {outcome:?}");
    }
}
