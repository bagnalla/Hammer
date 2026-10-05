use rusthammer::{
    Bits, ConfigError, Cursor, FoldRepeat, Literal, ParseContext, ParseOutcome, Parser,
};

fn main() -> Result<(), ConfigError> {
    // Count matching bytes without constructing a vector. The repetition driver
    // checks its count before calling this step, so this matching count fits usize.
    let letters = FoldRepeat::at_least(
        Literal::new(8, u64::from(b'a'))?,
        1,
        || 0usize,
        |count, _| count + 1,
    );
    let (next, count) = letters.parse(b"aaaa!", Cursor::start()).unwrap();
    assert_eq!((next, count), (Cursor { byte: 4, bit: 0 }, 4));
    println!("letters: {count}; next: {next:?}");
    assert_eq!(
        letters.parse_with(b"aaaa", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );

    // Exact repetition can finish on partial input. XOR cannot overflow and the
    // captured initializer creates a fresh checksum every time the parser runs.
    let seed = 0x80u64;
    let checksum = FoldRepeat::exact(Bits::new(8)?, 3, || seed, |sum, byte| sum ^ byte);
    assert_eq!(
        checksum.parse_with(b"abc", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 3, bit: 0 }, 0xe0)
    );
    assert_eq!(
        checksum.parse_with(b"ab", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    let (end, sum) = checksum.parse(b"abc", Cursor::start()).unwrap();
    println!("checksum: {sum:#x}; end: {end:?}");
    Ok(())
}
