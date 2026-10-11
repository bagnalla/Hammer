use rusthammer::{
    BeU16, Bits, ByteOrder, Cursor, Parser, Recognize, Seq, SkipBits, WithByteOrder, WithSpan,
};

fn main() {
    let input = [0x12, 0x34];
    let (_, (value, span)) = WithSpan { parser: BeU16 }
        .parse(&input, Cursor::start())
        .unwrap();
    assert_eq!(value, 0x1234);
    assert_eq!(span.as_bytes(), Some(input.as_slice()));
    println!(
        "WithSpan: decoded {value:#06x}, original bytes {:?}",
        span.as_bytes().unwrap()
    );

    let (_, span) = Recognize { parser: BeU16 }
        .parse(&input, Cursor::start())
        .unwrap();
    println!("Recognize: original bytes {:?}", span.as_bytes().unwrap());

    let input = [0x96];
    let parser = WithByteOrder {
        byte_order: ByteOrder::Little,
        parser: Seq {
            first: WithSpan {
                parser: Bits::new(3).unwrap(),
            },
            second: SkipBits::new(5),
        },
    };
    let (_, ((value, span), ())) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!(value, 4);
    assert_eq!(span.as_bytes(), None);

    println!(
        "Partial-byte span: value {value}, {:?} to {:?}",
        span.start(),
        span.end()
    );
}
