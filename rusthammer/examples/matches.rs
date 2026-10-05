use rusthammer::{
    BeU16, ButNot, ByteIn, BytePattern, Cursor, Difference, Map, ParseContext, ParseOutcome,
    Parser, Right, Xor,
};

#[derive(Debug, PartialEq, Eq)]
enum Value {
    Digit(u8),
    Word(u16),
}

fn main() {
    let except_six = ButNot {
        first: ByteIn::new(b"0123456789"),
        second: BytePattern::new(b"6"),
    };
    assert_eq!(except_six.parse(b"7", Cursor::start()).unwrap().1, b'7');
    assert!(except_six.parse(b"6", Cursor::start()).is_err());

    // Difference also accepts equal-length matches, following C Hammer.
    let equal_allowed = Difference {
        first: except_six.first,
        second: except_six.second,
    };
    assert_eq!(equal_allowed.parse(b"6", Cursor::start()).unwrap().1, b'6');

    // The application chooses one output type for exclusive alternatives.
    let value = Xor {
        first: Map {
            parser: ByteIn::new(b"0123456789"),
            map: |digit| Value::Digit(digit),
        },
        second: Map {
            parser: Right {
                first: BytePattern::new(b"#"),
                second: BeU16,
            },
            map: |word| Value::Word(word),
        },
    };
    assert_eq!(
        value.parse(b"5", Cursor::start()).unwrap().1,
        Value::Digit(b'5')
    );
    assert_eq!(
        value.parse(b"#\x12\x34", Cursor::start()).unwrap().1,
        Value::Word(0x1234)
    );

    // A partial second match cannot yet be counted as a rejection.
    let prefix = ButNot {
        first: BytePattern::new(b"a"),
        second: BytePattern::new(b"ab"),
    };
    assert_eq!(
        prefix.parse_with(b"a", Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(prefix.parse(b"a", Cursor::start()).unwrap().1, b"a");
}
