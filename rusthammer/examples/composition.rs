use rusthammer::{
    Bits, ConfigError, Cursor, Epsilon, Fail, ParseContext, ParseError, ParseOutcome, Parser,
    TryMap,
};

#[derive(Debug, PartialEq)]
enum Mode {
    Read,
    Write,
}

// A checked conversion constructs a typed value only for supported encodings.
fn decode_mode(input: &[u8], context: ParseContext) -> ParseOutcome<Mode> {
    let mode = TryMap {
        parser: Bits::new(8).unwrap(),
        map: |value| match value {
            1 => Ok(Mode::Read),
            2 => Ok(Mode::Write),
            _ => Err(()),
        },
    };
    mode.parse_with(input, Cursor::start(), context)
}

fn main() -> Result<(), ConfigError> {
    assert_eq!(
        decode_mode(&[1], ParseContext::FINAL),
        ParseOutcome::Success(Cursor { byte: 1, bit: 0 }, Mode::Read)
    );
    assert_eq!(
        decode_mode(&[3], ParseContext::FINAL),
        ParseOutcome::Error(ParseError::Mismatch)
    );
    assert_eq!(
        decode_mode(&[], ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    println!("mode: {:?}", decode_mode(&[2], ParseContext::FINAL));

    // Narrow a nine-bit wire field with a standard checked integer conversion.
    let byte = TryMap {
        parser: Bits::new(9)?,
        map: u8::try_from,
    };
    assert_eq!(
        byte.parse(&[0x7f, 0x80], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 1 }, 255))
    );
    assert_eq!(
        byte.parse(&[0x80, 0x00], Cursor::start()),
        Err(ParseError::Mismatch)
    );

    // These grammars never read input, even on a partial buffer.
    assert_eq!(
        Epsilon.parse_with(&[], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor::start(), ())
    );
    assert_eq!(
        Fail::<Mode>::new().parse(&[], Cursor::start()),
        Err(ParseError::Mismatch)
    );
    Ok(())
}
