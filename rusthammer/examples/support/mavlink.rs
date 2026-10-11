//! An unsigned MAVLink 2 frame grammar using the existing RustHammer API.
//!
//! Wire format: https://mavlink.io/en/guide/serialization.html
//! Native tests and Lean extraction share this source; see lean/RustHammer/MavlinkProofs.lean.

#[cfg(rusthammer_verify)]
use crate as rusthammer;
use rusthammer::{
    bind, map, seq, verify, BitOrder, BitSpan, Bits, Byte, ByteIn, ByteNotIn, ByteOrder, Cursor,
    Eval, Grammar, Map, Order, ParseContext, ParseOutcome, Right, Seq, TakeAligned, WithOrder,
    WithSpan,
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
    /// The transmitted bytes, borrowing the input. Message decoding is separate:
    /// MAVLink 2 may omit trailing zero bytes from a message's payload.
    pub payload: &'input [u8],
    pub checksum: u16,
}

fn fixed_bits(width: u8) -> Bits {
    match Bits::new(width) {
        Ok(parser) => parser,
        Err(_) => panic!("invalid fixed MAVLink field width"),
    }
}

type HeaderFields =
    Seq<Seq<Byte, Seq<ByteIn, Byte>>, Seq<Seq<Byte, Seq<ByteNotIn, ByteNotIn>>, Bits>>;
type HeaderValues = ((u8, (u8, u8)), ((u8, (u8, u8)), u64));

// Define callbacks outside backend-generic functions: the pinned extractor
// cannot infer an unused Backend parameter on generated closure implementations.
fn header() -> Map<HeaderFields, impl Fn(HeaderValues) -> Header> {
    let length_and_flags = seq(Byte, seq(ByteIn::new(&[0]), Byte));
    let sender = seq(Byte, seq(ByteNotIn::new(&[0]), ByteNotIn::new(&[0])));
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

/// Parse one unsigned MAVLink 2 frame, with no allocation or payload copying.
///
/// `crc_extra` must supply the dialect's CRC_EXTRA for the message ID. Unknown
/// messages, bad checksums, zero sender IDs, and nonzero incompatibility flags
/// yield `Mismatch`. In particular, signed frames are rejected: this example
/// does not implement signature authentication or replay protection.
/// Compatibility flags are retained without imposing restrictions.
///
/// The returned cursor points just past the checksum. Use `Left { first: parser,
/// second: End }` for a buffer that must contain exactly one frame. For partial
/// input, retry `NeedMore` with the accumulated buffer and the original cursor.
/// The CRC lookup should be pure, since retries can call it again.
pub fn mavlink_v2<F: Fn(u32) -> Option<u8>>(crc_extra: F) -> MavlinkV2<F> {
    MavlinkV2 { crc_extra }
}

// A concrete wrapper keeps the parser reusable across unrelated input lifetimes.
// The composed grammar below is rebuilt cheaply for each invocation.
#[derive(Clone, Copy)]
pub struct MavlinkV2<F> {
    crc_extra: F,
}

impl<'input, F> Grammar<'input> for MavlinkV2<F> {
    type Output = Packet<'input>;
}

impl<'a, Backend, F: Fn(u32) -> Option<u8>> Eval<'a, Backend> for MavlinkV2<F> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'a [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        frame_grammar::<Backend>(&self.crc_extra).eval(backend, input, cursor, context)
    }
}

fn frame_grammar<'a, Backend>(
    crc_extra: impl Fn(u32) -> Option<u8>,
) -> impl Eval<'a, Backend, Output = Packet<'a>> {
    // Bind makes the payload's length depend on the decoded header.
    let body = bind(header(), payload_factory());

    let checked = verify(
        seq(WithSpan { parser: body }, checksum_reader()),
        checksum_predicate(crc_extra),
    );
    let packet = PacketFields { parser: checked };

    WithOrder {
        order: Order {
            bit: BitOrder::HighFirst,
            byte: ByteOrder::Little,
        },
        parser: Right {
            // The empty read checks alignment; the magic byte is outside the CRC span.
            first: seq(TakeAligned { count: 0 }, ByteIn::new(&[0xfd])),
            second: packet,
        },
    }
}

fn payload_factory() -> impl Fn(Header) -> Payload {
    |header| Payload { header }
}

fn checksum_reader() -> Map<Bits, impl Fn(u64) -> u16> {
    map(fixed_bits(16), |n| n as u16)
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

// Named adapters preserve input borrows without the borrowed-output closures
// that the pinned Aeneas cannot translate. Both execute with the same backend.
struct Payload {
    header: Header,
}

impl<'input> Grammar<'input> for Payload {
    type Output = (Header, &'input [u8]);
}

impl<'input, Backend> Eval<'input, Backend> for Payload {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        let parser = TakeAligned {
            count: usize::from(self.header.payload_length),
        };
        match parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, payload) => {
                ParseOutcome::Success(next, (self.header, payload))
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

struct PacketFields<P> {
    parser: P,
}

impl<'input, P> Grammar<'input> for PacketFields<P> {
    type Output = Packet<'input>;
}

impl<'input, Backend, P> Eval<'input, Backend> for PacketFields<P>
where
    P: Eval<'input, Backend, Output = (((Header, &'input [u8]), BitSpan<'input>), u16)>,
{
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        match self.parser.eval(backend, input, cursor, context) {
            ParseOutcome::Success(next, fields) => {
                let (((header, payload), _span), checksum) = fields;
                ParseOutcome::Success(
                    next,
                    Packet {
                        header,
                        payload,
                        checksum,
                    },
                )
            }
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

// CRC-16/MCRF4XX: reflected polynomial 0x8408, initial 0xffff, no final XOR.
// Feed the header (excluding magic), the transmitted payload, then CRC_EXTRA.
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

/// A deliberately small dialect lookup. Extend it from your generated dialect table.
/// HEARTBEAT (ID 0) has CRC_EXTRA 50:
/// https://github.com/mavlink/c_library_v2/blob/master/minimal/mavlink_msg_heartbeat.h
pub fn heartbeat_crc_extra(message_id: u32) -> Option<u8> {
    match message_id {
        0 => Some(50),
        _ => None,
    }
}

/// HEARTBEAT from system/component 1, sequence 42. The checksum was independently
/// checked with https://github.com/mavlink/c_library_v2/blob/master/checksum.h.
pub const HEARTBEAT_FRAME: [u8; 21] = [
    0xfd, 9, 0, 0, 42, 1, 1, 0, 0, 0, // MAVLink 2 header
    0, 0, 0, 0, 2, 3, 0x51, 4, 3, // HEARTBEAT payload in wire order
    0x13, 0x11, // little-endian CRC 0x1113, including CRC_EXTRA 50
];
