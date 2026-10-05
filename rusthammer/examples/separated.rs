use rusthammer::{
    ConfigError, Cursor, End, FoldSepBy, Left, Literal, ParseContext, ParseError, ParseOutcome,
    Parser,
};

fn main() -> Result<(), ConfigError> {
    let item = Literal::new(8, u64::from(b'a'))?;
    let separator = Literal::new(8, u64::from(b','))?;
    let count = FoldSepBy::at_least(item, separator, 1, || 0usize, |n, _| n + 1);
    let (next, items) = count.parse(b"a,a,a!", Cursor::start()).unwrap();
    assert_eq!((next, items), (Cursor { byte: 5, bit: 0 }, 3));
    println!("items: {items}; next: {next:?}");

    // On partial input the next item might still arrive. Retry from the original
    // cursor with the accumulated buffer; each call initializes its own count.
    assert_eq!(
        count.parse_with(b"a,", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        count.parse(b"a,", Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, 1))
    );
    // A trailing separator remains unconsumed, so a complete grammar rejects it.
    assert_eq!(
        Left {
            first: &count,
            second: End
        }
        .parse(b"a,", Cursor::start()),
        Err(ParseError::TrailingInput)
    );

    // Exact counts finish without probing a further separator, even on partial input.
    let pair = FoldSepBy::exact(item, separator, 2, || 0usize, |n, _| n + 1);
    assert_eq!(
        pair.parse_with(b"a,a,", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, 2)
    );

    #[cfg(feature = "alloc")]
    {
        let list = rusthammer::SepBy::at_least(item, separator, 1);
        let (next, values) = list.parse(b"a,a,a!", Cursor::start()).unwrap();
        assert_eq!(values, vec![97, 97, 97]);
        println!("values: {values:?}; next: {next:?}");
    }
    Ok(())
}
