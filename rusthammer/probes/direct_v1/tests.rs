use super::*;

#[test]
fn local_callbacks_borrow_past_local_parser_and_reject_truncation() {
    let input = *b"\x03abc!";
    let (end, payload) = local_callbacks(&input, Cursor::start()).unwrap();
    assert_eq!(end, Cursor { byte: 4, bit: 0 });
    assert!(core::ptr::eq(payload.as_ptr(), input[1..].as_ptr()));
    assert_eq!(payload, b"abc");
    assert_eq!(
        local_callbacks(&input[..3], Cursor::start()),
        Err(ParseError::UnexpectedEnd)
    );
}

#[test]
fn byte_order_scopes_restore_the_enclosing_order_without_alignment_guards() {
    assert_eq!(
        ordered(&[1, 2, 3, 4], Cursor::start()),
        Ok((Cursor { byte: 4, bit: 0 }, (0x0201, 0x0304)))
    );
    let bits = Bits::new(8).unwrap();
    let input = [0x12, 0x34];
    let start = Cursor { byte: 0, bit: 4 };
    assert_eq!(
        bits.parse(&input, start),
        Ok((Cursor { byte: 1, bit: 4 }, 0x23))
    );
    assert_eq!(
        WithByteOrder {
            parser: bits,
            byte_order: ByteOrder::Little
        }
        .parse(&input, start),
        Ok((Cursor { byte: 1, bit: 4 }, 0x32))
    );
    assert_eq!(
        TakeAligned { count: 0 }.parse(&input, start),
        Err(ParseError::Unaligned)
    );
}

#[test]
fn input_and_configuration_borrows_are_independent() {
    let pattern = *b"ab";
    let input = *b"abcde";
    let (end, (matched, payload)) = independent(&pattern, &input, 2).unwrap();
    assert_eq!(end, Cursor { byte: 4, bit: 0 });
    assert!(core::ptr::eq(matched.as_ptr(), pattern.as_ptr()));
    assert!(core::ptr::eq(payload.as_ptr(), input[2..].as_ptr()));
}

#[test]
fn owned_outputs_need_no_copy_or_clone_and_errors_propagate() {
    assert_eq!(
        owned(&[7, 8], Cursor::start()),
        Ok((Cursor { byte: 2, bit: 0 }, (Value(8), 8)))
    );
    assert_eq!(owned(&[7], Cursor::start()), Err(ParseError::UnexpectedEnd));
}

#[test]
fn constructor_inference_and_complete_input_choice_rules() {
    assert_eq!(
        checked(&[3], Cursor::start(), 10),
        Ok((Cursor { byte: 1, bit: 0 }, Some(3)))
    );
    assert_eq!(
        checked(&[255], Cursor::start(), 10),
        Ok((Cursor { byte: 1, bit: 0 }, Some(256)))
    );
    assert_eq!(
        checked(&[20], Cursor::start(), 10),
        Ok((Cursor::start(), None))
    );
    assert_eq!(
        checked(&[], Cursor::start(), 10),
        Ok((Cursor::start(), None))
    );
    assert_eq!(
        checked(&[], Cursor { byte: 1, bit: 0 }, 10),
        Err(ParseError::InvalidCursor)
    );
    let fallback = choice(Bits::new(16).unwrap(), map(Byte, |value| value as u64));
    assert_eq!(
        fallback.parse(&[5], Cursor::start()),
        Ok((Cursor { byte: 1, bit: 0 }, 5))
    );
}

#[test]
fn borrowed_callback_controls_are_valid_rust() {
    let input = *b"abc";
    let expected = Ok((Cursor { byte: 2, bit: 0 }, &input[..2]));
    assert_eq!(candidates::borrowed_identity(&input, 2), expected);
    assert_eq!(candidates::named_identity(&input, 2), expected);
    assert_eq!(
        candidates::pattern_loop(b"ab", &input),
        Ok((Cursor { byte: 2, bit: 0 }, &b"ab"[..]))
    );
    assert_eq!(
        candidates::function_item_lookup(&mavlink::HEARTBEAT_FRAME, Cursor::start()),
        mavlink::heartbeat(&mavlink::HEARTBEAT_FRAME, Cursor::start())
    );
}

#[test]
fn mavlink_frame_preserves_payload_crc_and_prefix_consumption() {
    let mut input = [0; 22];
    input[..21].copy_from_slice(&mavlink::HEARTBEAT_FRAME);
    let (end, packet) = mavlink::heartbeat(&input, Cursor::start()).unwrap();
    assert_eq!(end, Cursor { byte: 21, bit: 0 });
    assert_eq!(packet.header.message_id, 0);
    assert_eq!(packet.header.sequence, 42);
    assert_eq!(packet.checksum, 0x1113);
    assert!(core::ptr::eq(packet.payload.as_ptr(), input[10..].as_ptr()));
    assert_eq!(packet.payload, &input[10..19]);
    let (header_end, header) = mavlink::predicate_header()
        .parse_with(&input, Cursor { byte: 1, bit: 0 }, ByteOrder::Little)
        .unwrap();
    assert_eq!(header_end, Cursor { byte: 10, bit: 0 });
    assert_eq!(header, packet.header);
}

#[test]
fn mavlink_rejects_each_truncation_corruption_and_unknown_message() {
    let input = mavlink::HEARTBEAT_FRAME;
    for end in 0..input.len() {
        assert_eq!(
            mavlink::heartbeat(&input[..end], Cursor::start()),
            Err(ParseError::UnexpectedEnd)
        );
    }
    for index in 0..input.len() {
        let mut corrupt = input;
        corrupt[index] ^= 1;
        assert!(mavlink::heartbeat(&corrupt, Cursor::start()).is_err());
    }
    assert_eq!(
        mavlink::parse_frame(&input, Cursor::start(), |_| None),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn mavlink_preserves_all_message_id_bytes_and_caller_crc_extra() {
    // Independent byte-wise CRC calculation, checked against the original fixture.
    fn checksum(bytes: &[u8], extra: u8) -> u16 {
        let mut crc = 0xffff_u16;
        for byte in bytes.iter().copied().chain(core::iter::once(extra)) {
            let mut tmp = byte ^ crc as u8;
            tmp ^= tmp << 4;
            crc = (crc >> 8) ^ ((tmp as u16) << 8) ^ ((tmp as u16) << 3) ^ ((tmp as u16) >> 4);
        }
        crc
    }
    let mut input = mavlink::HEARTBEAT_FRAME;
    assert_eq!(checksum(&input[1..19], 50), 0x1113);
    input[7..10].copy_from_slice(&[0x56, 0x34, 0x12]);
    let crc = checksum(&input[1..19], 173);
    input[19..21].copy_from_slice(&crc.to_le_bytes());
    let (end, packet) = mavlink::parse_frame(&input, Cursor::start(), |id| {
        if id == 0x123456 {
            Some(173)
        } else {
            None
        }
    })
    .unwrap();
    assert_eq!(end, Cursor { byte: 21, bit: 0 });
    assert_eq!(packet.header.message_id, 0x123456);
    assert_eq!(packet.checksum, crc);
}
