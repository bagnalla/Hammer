#[path = "support/constructors.rs"]
mod support;

use rusthammer::{
    bind, choice, map, optional, seq, try_map, verify, Byte, Cursor, Parser, TakeAligned,
};

fn main() {
    let packet = bind(
        verify(support::header(), |header| header.tag == 1),
        |header| TakeAligned {
            count: usize::from(header.length),
        },
    );
    let (_, payload) = packet.parse(b"\x01\x00\x03abc!", Cursor::start()).unwrap();
    assert_eq!(payload, b"abc");
    println!("Payload: {payload:?}");

    let digit = try_map(Byte, |byte| {
        if byte.is_ascii_digit() {
            Ok(byte - b'0')
        } else {
            Err(())
        }
    });
    let special = map(verify(Byte, |byte| *byte == b'?'), |_| 10);
    let parser = seq(optional(choice(digit, special)), Byte);
    let (_, values) = parser.parse(b"?!", Cursor::start()).unwrap();
    assert_eq!(values, (Some(10), b'!'));
    println!("Optional value and following byte: {values:?}");
}
