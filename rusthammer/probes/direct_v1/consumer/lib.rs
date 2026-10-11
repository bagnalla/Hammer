//! Ordinary dependency use: all probe library bodies arrive as optimized MIR.
#![no_std]
use rusthammer_direct_v1_probe::mavlink::{mavlink_v2, Packet};
use rusthammer_direct_v1_probe::{
    bind, map, opaque_number, opaque_payload, seq, Byte, ByteOrder, Cursor, LocalCallbacks,
    ParseError, Parser, Pattern, TakeAligned, Value, WithByteOrder,
};

pub fn local(input: &[u8], cursor: Cursor) -> Result<(Cursor, &[u8]), ParseError> {
    LocalCallbacks.parse(input, cursor)
}

pub fn owned(input: &[u8], cursor: Cursor) -> Result<(Cursor, (Value, u8)), ParseError> {
    let parser = map(Byte, |value| Value(value as u16));
    seq(&parser, Byte).parse(input, cursor)
}

pub fn borrowed<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
    count: usize,
) -> Result<(Cursor, (&'pattern [u8], &'input [u8])), ParseError> {
    let parser = Pattern { bytes: pattern };
    seq(&parser, opaque_payload(count)).parse(input, Cursor::start())
}

pub fn ordered(input: &[u8], cursor: Cursor) -> Result<(Cursor, u64), ParseError> {
    WithByteOrder {
        parser: opaque_number(),
        byte_order: ByteOrder::Little,
    }
    .parse(input, cursor)
}

pub fn dependent(input: &[u8], cursor: Cursor) -> Result<(Cursor, &[u8]), ParseError> {
    bind(Byte, |count| TakeAligned {
        count: count as usize,
    })
    .parse(input, cursor)
}

// A consumer-defined parser implements only the new trait.
pub struct Local;
impl<'input> Parser<'input> for Local {
    type Output = u16;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        order: ByteOrder,
    ) -> Result<(Cursor, u16), ParseError> {
        map(Byte, |value| value as u16).parse_with(input, cursor, order)
    }
}

pub fn custom(input: &[u8], cursor: Cursor) -> Result<(Cursor, (u16, u8)), ParseError> {
    seq(&Local, Byte).parse(input, cursor)
}

pub fn frame(
    input: &[u8],
    cursor: Cursor,
    id: u32,
    extra: u8,
) -> Result<(Cursor, Packet<'_>), ParseError> {
    mavlink_v2(move |message_id| if message_id == id { Some(extra) } else { None })
        .parse(input, cursor)
}

pub fn borrowed_identity(input: &[u8], count: usize) -> Result<(Cursor, &[u8]), ParseError> {
    map(TakeAligned { count }, |bytes| bytes).parse(input, Cursor::start())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rusthammer_direct_v1_probe::mavlink::HEARTBEAT_FRAME;

    #[test]
    fn dependency_bodies_keep_owned_borrowed_and_custom_outputs() {
        assert_eq!(
            owned(&[3, 7], Cursor::start()),
            Ok((Cursor { byte: 2, bit: 0 }, (Value(3), 7)))
        );
        assert_eq!(
            custom(&[3, 7], Cursor::start()),
            Ok((Cursor { byte: 2, bit: 0 }, (3, 7)))
        );
        assert_eq!(
            ordered(&[3, 7], Cursor::start()),
            Ok((Cursor { byte: 2, bit: 0 }, 0x0703))
        );
        let input = *b"\x02ab!";
        assert_eq!(
            dependent(&input, Cursor::start()),
            Ok((Cursor { byte: 3, bit: 0 }, &input[1..3]))
        );
        assert_eq!(
            local(&input, Cursor::start()),
            dependent(&input, Cursor::start())
        );
        assert_eq!(
            borrowed(&input[..1], &input, 2),
            Ok((Cursor { byte: 3, bit: 0 }, (&input[..1], &input[1..3])))
        );
        assert_eq!(
            borrowed_identity(&input, 2),
            Ok((Cursor { byte: 2, bit: 0 }, &input[..2]))
        );
    }

    #[test]
    fn caller_lookup_and_borrow_survive_the_dependency_boundary() {
        let (end, packet) = frame(&HEARTBEAT_FRAME, Cursor::start(), 0, 50).unwrap();
        assert_eq!(end, Cursor { byte: 21, bit: 0 });
        assert_eq!(packet.payload, &HEARTBEAT_FRAME[10..19]);
        assert_eq!(
            frame(&HEARTBEAT_FRAME, Cursor::start(), 1, 50),
            Err(ParseError::Mismatch)
        );
        assert_eq!(
            frame(&HEARTBEAT_FRAME, Cursor::start(), 0, 49),
            Err(ParseError::Mismatch)
        );
    }
}
