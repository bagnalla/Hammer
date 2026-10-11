#[path = "../examples/support/mavlink.rs"]
mod mavlink;

use mavlink::{heartbeat_crc_extra, mavlink_v2, Header, HEARTBEAT_FRAME};
use rusthammer::{
    BitOrder, ByteOrder, Cursor, End, Left, Order, ParseContext, ParseError, ParseOutcome, Parser,
};

#[test]
fn heartbeat_matches_reference_crc_and_borrows_payload() {
    let input = HEARTBEAT_FRAME;
    let (next, packet) = mavlink_v2(heartbeat_crc_extra)
        .parse(&input, Cursor::start())
        .unwrap();
    assert_eq!(next, Cursor { byte: 21, bit: 0 });
    assert_eq!(
        packet.header,
        Header {
            payload_length: 9,
            incompat_flags: 0,
            compat_flags: 0,
            sequence: 42,
            system_id: 1,
            component_id: 1,
            message_id: 0,
        }
    );
    assert_eq!(packet.payload, &[0, 0, 0, 0, 2, 3, 0x51, 4, 3]);
    assert_eq!(packet.payload.as_ptr(), input[10..].as_ptr());
    assert_eq!(packet.checksum, 0x1113);
}

#[test]
fn every_truncated_prefix_waits_only_when_input_is_partial() {
    let parser = mavlink_v2(heartbeat_crc_extra);
    for end in 0..HEARTBEAT_FRAME.len() {
        let input = &HEARTBEAT_FRAME[..end];
        assert_eq!(
            parser.parse_with(input, Cursor::start(), ParseContext::PARTIAL),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            parser.parse(input, Cursor::start()),
            Err(ParseError::UnexpectedEnd)
        );
    }
    assert!(matches!(
        parser.parse_with(&HEARTBEAT_FRAME, Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 21, bit: 0 }, _)
    ));
}

#[test]
fn corruption_unknown_messages_and_unsupported_flags_are_rejected() {
    let parser = mavlink_v2(heartbeat_crc_extra);
    // Header, payload, and checksum bytes all participate in validation.
    for index in 0..HEARTBEAT_FRAME.len() {
        let mut bad = HEARTBEAT_FRAME;
        bad[index] ^= 0x80;
        let expected = if index == 1 {
            ParseError::UnexpectedEnd // Corrupting length promises a larger frame.
        } else {
            ParseError::Mismatch
        };
        assert_eq!(parser.parse(&bad, Cursor::start()), Err(expected));
    }
    assert_eq!(
        mavlink_v2(|_| None).parse(&HEARTBEAT_FRAME, Cursor::start()),
        Err(ParseError::Mismatch)
    );
    assert_eq!(
        mavlink_v2(|_| Some(51)).parse(&HEARTBEAT_FRAME, Cursor::start()),
        Err(ParseError::Mismatch)
    );

    // Reject at the unsupported flag/source itself, before reading a payload or CRC.
    for flag in [1, 2, 0x80, 0xff] {
        let input = [0xfd, 9, flag];
        assert_eq!(
            parser.parse_with(&input, Cursor::start(), ParseContext::PARTIAL),
            ParseOutcome::Error(ParseError::Mismatch)
        );
    }
    for index in [5, 6] {
        let mut bad = HEARTBEAT_FRAME;
        bad[index] = 0;
        assert_eq!(
            parser.parse_with(&bad[..=index], Cursor::start(), ParseContext::PARTIAL),
            ParseOutcome::Error(ParseError::Mismatch)
        );
    }
}

#[test]
fn frame_boundaries_allow_streams_or_an_explicit_end_check() {
    let mut stream = vec![0xaa];
    stream.extend(HEARTBEAT_FRAME);
    stream.extend(HEARTBEAT_FRAME);
    let parser = mavlink_v2(heartbeat_crc_extra);
    let (next, packet) = parser.parse(&stream, Cursor { byte: 1, bit: 0 }).unwrap();
    assert_eq!(next, Cursor { byte: 22, bit: 0 });
    assert_eq!(packet.payload.as_ptr(), stream[11..].as_ptr());
    assert_eq!(
        parser.parse(&stream, next).unwrap().0,
        Cursor { byte: 43, bit: 0 }
    );

    let complete = Left {
        first: parser,
        second: End,
    };
    assert_eq!(
        complete.parse(&stream, Cursor { byte: 1, bit: 0 }),
        Err(ParseError::TrailingInput)
    );
    assert!(complete.parse(&HEARTBEAT_FRAME, Cursor::start()).is_ok());
}

#[test]
fn alignment_is_checked_and_wire_order_is_independent_of_the_caller() {
    let parser = mavlink_v2(heartbeat_crc_extra);
    assert_eq!(
        parser.parse(&HEARTBEAT_FRAME, Cursor { byte: 0, bit: 1 }),
        Err(ParseError::Unaligned)
    );
    assert_eq!(
        parser.parse(&HEARTBEAT_FRAME, Cursor { byte: 22, bit: 0 }),
        Err(ParseError::InvalidCursor)
    );
    let expected = parser.parse_with(&HEARTBEAT_FRAME, Cursor::start(), ParseContext::FINAL);
    for bit in [BitOrder::HighFirst, BitOrder::LowFirst] {
        for byte in [ByteOrder::Big, ByteOrder::Little] {
            assert_eq!(
                parser.parse_with(
                    &HEARTBEAT_FRAME,
                    Cursor::start(),
                    ParseContext {
                        order: Order { bit, byte },
                        ..ParseContext::FINAL
                    },
                ),
                expected
            );
        }
    }
}

#[test]
fn custom_dialect_uses_all_message_id_bytes_and_accepts_compat_flags() {
    // Synthetic dialect: message 0x010203, CRC_EXTRA 0x42. Reference checksums
    // below were computed with mavlink/c_library_v2/checksum.h, not our CRC code.
    let parser = mavlink_v2(|id| (id == 0x010203).then_some(0x42));
    let frame = [
        0xfd, 3, 0, 0x80, 255, 7, 8, 3, 2, 1, 0xaa, 0, 0xbb, 0x2f, 0x22,
    ];
    let (next, packet) = parser.parse(&frame, Cursor::start()).unwrap();
    assert_eq!(next.byte, frame.len());
    assert_eq!(packet.header.message_id, 0x010203);
    assert_eq!(packet.header.compat_flags, 0x80);
    assert_eq!(packet.payload, &[0xaa, 0, 0xbb]);

    // Framing also permits zero and maximum-size payloads. Message-specific
    // payload length/field checks belong in a separate message decoder.
    let empty = [0xfd, 0, 0, 0, 0, 1, 1, 3, 2, 1, 0x53, 0x7b];
    assert!(parser
        .parse(&empty, Cursor::start())
        .unwrap()
        .1
        .payload
        .is_empty());
    let mut full = vec![0xfd, 255, 0, 0, 0, 1, 1, 3, 2, 1];
    full.extend(0..255_u8);
    full.extend([0x07, 0xd9]);
    let (next, packet) = parser.parse(&full, Cursor::start()).unwrap();
    assert_eq!(next.byte, 267);
    assert_eq!(packet.payload, &full[10..265]);
}
