use rusthammer::{
    Choice, ConfigError, Cursor, End, InputStatus, Literal, ParseOutcome, Parser, Seq,
};

fn main() -> Result<(), ConfigError> {
    let parser = Seq {
        first: Choice {
            first: Literal::new(16, 0x6162)?, // "ab"
            second: Literal::new(8, 0x61)?,   // "a"
        },
        second: End,
    };
    let start = Cursor::start();
    let mut buffer = Vec::new();

    // Buffering belongs to the caller. Retry with all bytes and the original cursor.
    for chunk in [b'a', b'b'] {
        buffer.push(chunk);
        let outcome = parser.parse_with(&buffer, start, InputStatus::Partial);
        assert_eq!(outcome, ParseOutcome::NeedMore);
        println!("partial {buffer:?}: {outcome:?}");
    }

    // The input source has finished. The same buffer can now establish EOF.
    let outcome = parser.parse_with(&buffer, start, InputStatus::Final);
    assert_eq!(
        outcome,
        ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, (0x6162, ()))
    );
    println!("final {buffer:?}: {outcome:?}");

    // If the source ends after just "a", final truncation permits the shorter arm.
    assert_eq!(
        parser.parse(b"a", start),
        Ok((Cursor { byte: 1, bit: 0 }, (0x61, ())))
    );
    Ok(())
}
