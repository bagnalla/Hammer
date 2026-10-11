//! Adapted from examples/support/mavlink.rs to exercise the proposed interface.
//! This private copy has no migrated correctness proof and is not a library API.
use crate::{
    bind, map, seq, verify, BitSpan, Bits, Byte, ByteOrder, Cursor, Map, ParseError, Parser, Right,
    TakeAligned, WithByteOrder, WithSpan,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    pub payload_length: u8,
    pub incompat_flags: u8,
    pub compat_flags: u8,
    pub sequence: u8,
    pub system_id: u8,
    pub component_id: u8,
    pub message_id: u32,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Packet<'input> {
    pub header: Header,
    pub payload: &'input [u8],
    pub checksum: u16,
}

fn fixed_bits(width: u8) -> Bits {
    match Bits::new(width) {
        Ok(parser) => parser,
        Err(_) => panic!("invalid fixed MAVLink field width"),
    }
}

// Isolated negative control: nested predicate closures generate Lean record
// updates without enough type information. It is not a supported root.
pub fn predicate_header<'input>() -> impl Parser<'input, Output = Header> {
    let length_and_flags = seq(Byte, seq(verify(Byte, |value| *value == 0), Byte));
    let sender = seq(
        Byte,
        seq(
            verify(Byte, |value| *value != 0),
            verify(Byte, |value| *value != 0),
        ),
    );
    map(
        seq(length_and_flags, seq(sender, fixed_bits(24))),
        |(
            (payload_length, (incompat_flags, compat_flags)),
            ((sequence, (system_id, component_id)), message_id),
        )| Header {
            payload_length,
            incompat_flags,
            compat_flags,
            sequence,
            system_id,
            component_id,
            message_id: message_id as u32,
        },
    )
}

// A small concrete byte-validation node stands in for the production byte sets.
// Keeping validation out of nested closure fields avoids the control above.
#[derive(Clone, Copy)]
struct CheckedByte {
    expected: u8,
    different: bool,
}

impl<'input> Parser<'input> for CheckedByte {
    type Output = u8;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, u8), ParseError> {
        let parsed = Byte.parse_with(input, cursor, byte_order)?;
        let (next, value) = parsed;
        if (value != self.expected) == self.different {
            Ok((next, value))
        } else {
            Err(ParseError::Mismatch)
        }
    }
}

// This closure is still constructed inside a lifetime-generic function.
fn header<'input>() -> impl Parser<'input, Output = Header> {
    let length_and_flags = seq(
        Byte,
        seq(
            CheckedByte {
                expected: 0,
                different: false,
            },
            Byte,
        ),
    );
    let nonzero = CheckedByte {
        expected: 0,
        different: true,
    };
    let sender = seq(Byte, seq(nonzero, nonzero));
    map(
        seq(length_and_flags, seq(sender, fixed_bits(24))),
        |(
            (payload_length, (incompat_flags, compat_flags)),
            ((sequence, (system_id, component_id)), message_id),
        )| Header {
            payload_length,
            incompat_flags,
            compat_flags,
            sequence,
            system_id,
            component_id,
            message_id: message_id as u32,
        },
    )
}

#[derive(Clone, Copy)]
pub struct MavlinkV2<F> {
    crc_extra: F,
}

pub fn mavlink_v2<F: Fn(u32) -> Option<u8>>(crc_extra: F) -> MavlinkV2<F> {
    MavlinkV2 { crc_extra }
}

impl<'input, F: Fn(u32) -> Option<u8>> Parser<'input> for MavlinkV2<F> {
    type Output = Packet<'input>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        frame_grammar(&self.crc_extra).parse_with(input, cursor, byte_order)
    }
}

pub fn frame_grammar<'input>(
    crc_extra: impl Fn(u32) -> Option<u8>,
) -> impl Parser<'input, Output = Packet<'input>> {
    let body = bind(header(), payload_factory());
    let checked = verify(
        seq(WithSpan { parser: body }, checksum_reader()),
        checksum_predicate(crc_extra),
    );
    WithByteOrder {
        byte_order: ByteOrder::Little,
        parser: Right {
            first: seq(
                TakeAligned { count: 0 },
                CheckedByte {
                    expected: 0xfd,
                    different: false,
                },
            ),
            second: PacketFields { parser: checked },
        },
    }
}

fn payload_factory() -> impl Fn(Header) -> Payload {
    |header| Payload { header }
}

fn checksum_reader() -> Map<Bits, impl Fn(u64) -> u16> {
    map(fixed_bits(16), |value| value as u16)
}

type CheckedFields<'input> = (((Header, &'input [u8]), BitSpan<'input>), u16);

fn checksum_predicate(
    crc_extra: impl Fn(u32) -> Option<u8>,
) -> impl Fn(&CheckedFields<'_>) -> bool {
    move |(((header, _payload), span), checksum)| match (
        crc_extra(header.message_id),
        span.as_bytes(),
    ) {
        (Some(extra), Some(bytes)) => crc_mcrf4xx(bytes, extra) == *checksum,
        _ => false,
    }
}

// Keep the named borrowed-output adapters until the separate callback controls pass.
struct Payload {
    header: Header,
}

impl<'input> Parser<'input> for Payload {
    type Output = (Header, &'input [u8]);

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let parsed = TakeAligned {
            count: self.header.payload_length as usize,
        }
        .parse_with(input, cursor, byte_order)?;
        let (next, payload) = parsed;
        Ok((next, (self.header, payload)))
    }
}

struct PacketFields<P> {
    parser: P,
}

impl<'input, P: Parser<'input, Output = CheckedFields<'input>>> Parser<'input> for PacketFields<P> {
    type Output = Packet<'input>;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        let parsed = self.parser.parse_with(input, cursor, byte_order)?;
        let (next, fields) = parsed;
        let (((header, payload), _span), checksum) = fields;
        Ok((
            next,
            Packet {
                header,
                payload,
                checksum,
            },
        ))
    }
}

pub fn parse_frame<F: Fn(u32) -> Option<u8>>(
    input: &[u8],
    cursor: Cursor,
    crc_extra: F,
) -> Result<(Cursor, Packet<'_>), ParseError> {
    mavlink_v2(crc_extra).parse(input, cursor)
}

pub fn heartbeat(input: &[u8], cursor: Cursor) -> Result<(Cursor, Packet<'_>), ParseError> {
    // Keep an ordinary call inside a closure instead of passing a function item
    // through a generic factory that returns a value borrowing the input.
    parse_frame(input, cursor, |id| heartbeat_crc_extra(id))
}

fn crc_mcrf4xx(bytes: &[u8], extra: u8) -> u16 {
    let mut crc = 0xffff_u16;
    let mut index = 0;
    while index < bytes.len() {
        crc = crc_accumulate(crc, bytes[index]);
        index += 1;
    }
    crc_accumulate(crc, extra)
}

fn crc_accumulate(mut crc: u16, byte: u8) -> u16 {
    crc ^= u16::from(byte);
    let mut bit = 0_u8;
    while bit < 8 {
        crc = if crc & 1 != 0 {
            (crc >> 1) ^ 0x8408
        } else {
            crc >> 1
        };
        bit += 1;
    }
    crc
}

pub fn heartbeat_crc_extra(message_id: u32) -> Option<u8> {
    match message_id {
        0 => Some(50),
        _ => None,
    }
}

// Same independently checked fixture as the existing shared example.
pub const HEARTBEAT_FRAME: [u8; 21] = [
    0xfd, 9, 0, 0, 42, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0x51, 4, 3, 0x13, 0x11,
];
