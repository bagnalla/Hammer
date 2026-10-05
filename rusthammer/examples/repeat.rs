use rusthammer::{
    Bits, ConfigError, Cursor, End, Literal, ParseContext, ParseOutcome, Parser, Repeat, Seq,
};

fn main() -> Result<(), ConfigError> {
    // Three five-bit fields span two bytes, followed by one padding bit.
    let fields = Repeat::exact(Bits::new(5)?, 3);
    let input = [0b00001_111, 0b11_00101_0];
    let (next, values) = fields.parse(&input, Cursor::start()).unwrap();
    assert_eq!(values, [1, 31, 5]);
    assert_eq!(next, Cursor { byte: 1, bit: 7 });
    println!("fields: {values:?}; next: {next:?}");

    println!(
        "partial first byte: {:?}",
        fields.parse_with(&input[..1], Cursor::start(), ParseContext::PARTIAL)
    );

    // The same combinator accepts a runtime count read from the input.
    let counted_input = [3, 0, 10, 0, 20, 0, 30];
    let (body_start, count) = Bits::new(8)?
        .parse(&counted_input, Cursor::start())
        .unwrap();
    // An eight-bit count fits usize on all supported targets.
    let body = Seq {
        first: Repeat::exact(Bits::new(16)?, count as usize),
        second: End,
    };
    let (end, (values, ())) = body.parse(&counted_input, body_start).unwrap();
    assert_eq!(values, [10, 20, 30]);
    println!("counted values: {values:?}; end: {end:?}");

    // One through three 'a' bytes; a rejected attempt leaves the '!' untouched.
    let bounded = Repeat::new(Literal::new(8, u64::from(b'a'))?, 1, 3)?;
    let (next, values) = bounded.parse(b"aa!", Cursor::start()).unwrap();
    assert_eq!(values, [97, 97]);
    assert_eq!(next, Cursor { byte: 2, bit: 0 });
    println!("bounded values: {values:?}; next: {next:?}");

    // Meeting the minimum does not establish where a partial list stops.
    assert_eq!(
        bounded.parse_with(b"aa", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    // Reaching the maximum does: no fourth child is attempted.
    assert_eq!(
        bounded.parse_with(b"aaa", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, vec![97; 3])
    );

    let unbounded = Repeat::at_least(Literal::new(8, u64::from(b'a'))?, 1);
    let (next, values) = unbounded.parse(b"aaaa!", Cursor::start()).unwrap();
    assert_eq!(next, Cursor { byte: 4, bit: 0 });
    assert_eq!(values, vec![97; 4]);
    assert_eq!(unbounded.max(), None);
    println!("unbounded values: {values:?}; next: {next:?}");
    assert_eq!(
        unbounded.parse_with(b"aaaa", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    Ok(())
}
