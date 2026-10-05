use rusthammer::{
    Bits, ConfigError, Cursor, End, Ignore, Left, Literal, Middle, ParseContext, ParseOutcome,
    Parser, Right, TakeAligned,
};

fn main() -> Result<(), ConfigError> {
    let payload = TakeAligned { count: 3 };
    let bracketed = Middle {
        left: Literal::new(8, u64::from(b'['))?,
        parser: &payload,
        right: Literal::new(8, u64::from(b']'))?,
    };
    let complete = Left {
        first: &bracketed,
        second: End,
    };
    let (next, bytes) = complete.parse(b"[abc]", Cursor::start()).unwrap();
    assert_eq!(bytes, b"abc");
    assert_eq!(next, Cursor { byte: 5, bit: 0 });
    println!("payload: {bytes:?}; next: {next:?}");

    // The same parser can be reused by reference in several grammars.
    let prefixed = Right {
        first: Literal::new(8, u64::from(b':'))?,
        second: &payload,
    };
    assert_eq!(
        prefixed.parse(b":xyz!", Cursor::start()),
        Ok((Cursor { byte: 4, bit: 0 }, &b"xyz"[..]))
    );

    // The closing delimiter is required even though its value is discarded.
    assert_eq!(
        bracketed.parse_with(b"[abc", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        bracketed.parse_with(b"[abc]", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 5, bit: 0 }, &b"abc"[..])
    );
    assert_eq!(
        complete.parse_with(b"[abc]", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );

    // Ignore consumes the field and produces unit, including across a byte boundary.
    let reserved = Ignore {
        parser: Bits::new(5)?,
    };
    assert_eq!(
        reserved.parse(&[0xff, 0xff], Cursor { byte: 0, bit: 6 }),
        Ok((Cursor { byte: 1, bit: 3 }, ()))
    );
    Ok(())
}
