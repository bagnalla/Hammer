use rusthammer::{
    BeU16, BitOrder, Bits, ByteOrder, Cursor, Order, ParseContext, ParseOutcome, Parser, Seq,
    WithOrder,
};

fn main() {
    let parser = Seq {
        first: WithOrder {
            order: Order {
                bit: BitOrder::LowFirst,
                byte: ByteOrder::Little,
            },
            parser: Seq {
                first: Bits::new(3).unwrap(),
                second: Bits::new(5).unwrap(),
            },
        },
        second: BeU16,
    };
    let input = [0x96, 0x12, 0x34];
    assert_eq!(
        parser.parse_with(&input[..2], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    // Retry the whole grammar with the accumulated input and original context.
    let (next, ((kind, flags), length)) = parser.parse(&input, Cursor::start()).unwrap();
    assert_eq!((kind, flags, length), (6, 18, 0x1234));
    assert_eq!(next, Cursor { byte: 3, bit: 0 });
    println!("kind: {kind}; flags: {flags}; length: {length:#x}; next cursor: {next:?}");
}
