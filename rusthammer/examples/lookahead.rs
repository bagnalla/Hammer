use rusthammer::{And, ConfigError, Cursor, Literal, Not, Optional, Parser, Seq};

fn main() -> Result<(), ConfigError> {
    let a = Literal::new(8, u64::from(b'a'))?;
    let b = Literal::new(8, u64::from(b'b'))?;
    let ab = Literal::new(16, 0x6162)?;

    // Require "ab", then consume only its first byte.
    let positive = Seq {
        first: And { parser: ab },
        second: a,
    };
    println!(
        "a starting ab: {:?}",
        positive.parse(b"abc", Cursor::start())
    );

    // Consume "a" only if the next byte is not "b".
    let negative = Seq {
        first: a,
        second: Not { parser: b },
    };
    for input in [&b"ac"[..], &b"ab"[..], &b"a"[..]] {
        println!(
            "a not followed by b, {input:?}: {:?}",
            negative.parse(input, Cursor::start())
        );
    }

    // A truncated optional "ab" restores the original cursor and yields None.
    let optional = Optional { parser: ab };
    for input in [&b"ab"[..], &b"a"[..]] {
        println!(
            "optional ab, {input:?}: {:?}",
            optional.parse(input, Cursor::start())
        );
    }
    Ok(())
}
