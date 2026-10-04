use rusthammer::{parse_record, Cursor, ParseError, Record, RecordParser, MAX_RECORD_PAYLOAD};

#[test]
fn records_decode_all_header_values_and_borrow_the_exact_payload() {
    let parser = RecordParser::new().unwrap();
    for flags in 0..32 {
        for length in 0..=MAX_RECORD_PAYLOAD as usize {
            let mut input = vec![0x20 | flags, (length >> 8) as u8, length as u8];
            input.extend((0..length).map(|i| (i % 251) as u8));
            let (next, record) = parse_record(&input, Cursor::start(), &parser).unwrap();
            assert_eq!(
                next,
                Cursor {
                    byte: input.len(),
                    bit: 0
                }
            );
            assert_eq!(
                record,
                Record {
                    version: 1,
                    flags: flags as u64,
                    payload: &input[3..]
                }
            );
            assert_eq!(record.payload.as_ptr(), input[3..].as_ptr());
        }
    }
}

#[test]
fn record_constraints_are_input_rejection_not_configuration_errors() {
    let parser = RecordParser::new().unwrap();
    for version in [0, 2, 3, 4, 5, 6, 7] {
        assert_eq!(
            parse_record(&[version << 5, 0, 0], Cursor::start(), &parser),
            Err(ParseError::Mismatch)
        );
    }
    for length in 1025..=u16::MAX {
        let [high, low] = length.to_be_bytes();
        // A complete header is enough to reject the length, even with no payload.
        assert_eq!(
            parse_record(&[0x20, high, low], Cursor::start(), &parser),
            Err(ParseError::Mismatch)
        );
    }
}

#[test]
fn record_errors_have_specified_precedence() {
    let parser = RecordParser::new().unwrap();
    for input in [&[][..], &[0][..], &[0, 0][..]] {
        // Header truncation precedes checking the unsupported version.
        assert_eq!(
            parse_record(input, Cursor::start(), &parser),
            Err(ParseError::UnexpectedEnd)
        );
    }
    let complete = [0x25, 0, 3, 0xca, 0xfe, 1];
    for end in 0..complete.len() {
        assert_eq!(
            parse_record(&complete[..end], Cursor::start(), &parser),
            Err(ParseError::UnexpectedEnd)
        );
    }
    assert_eq!(
        parse_record(&[0x20, 0, 0, 0], Cursor::start(), &parser),
        Err(ParseError::TrailingInput)
    );
    assert_eq!(
        parse_record(&[0x40, 0, 3], Cursor::start(), &parser),
        Err(ParseError::Mismatch)
    );
}

#[test]
fn record_checks_alignment_and_supports_a_byte_offset() {
    let parser = RecordParser::new().unwrap();
    let input = [0xff, 0x25, 0, 1, 0xca];
    let (next, record) = parse_record(&input, Cursor { byte: 1, bit: 0 }, &parser).unwrap();
    assert_eq!(next, Cursor { byte: 5, bit: 0 });
    assert_eq!(
        record,
        Record {
            version: 1,
            flags: 5,
            payload: &input[4..]
        }
    );
    assert_eq!(record.payload.as_ptr(), input[4..].as_ptr());
    for bit in 1..8 {
        assert_eq!(
            parse_record(&input, Cursor { byte: 0, bit }, &parser),
            Err(ParseError::Unaligned)
        );
    }
    for cursor in [
        Cursor { byte: 0, bit: 8 },
        Cursor {
            byte: input.len(),
            bit: 1,
        },
        Cursor {
            byte: input.len() + 1,
            bit: 0,
        },
        Cursor {
            byte: usize::MAX,
            bit: u8::MAX,
        },
    ] {
        assert_eq!(
            parse_record(&input, cursor, &parser),
            Err(ParseError::InvalidCursor)
        );
    }
}
