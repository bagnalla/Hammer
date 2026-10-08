use super::{seek_position, Seek};
use crate::{ConfigError, Cursor, InputStatus, ParseError, ParseOutcome};

fn cursor(bits: usize) -> Cursor {
    Cursor {
        byte: bits / 8,
        bit: (bits % 8) as u8,
    }
}

fn absolute(bits: usize) -> Seek {
    Seek::to(cursor(bits)).unwrap()
}

fn oracle(
    length: usize,
    start: Cursor,
    target: i128,
    status: InputStatus,
    end: bool,
) -> ParseOutcome<Cursor> {
    let limit = length as i128 * 8;
    if start.bit >= 8 || start.byte as i128 * 8 + i128::from(start.bit) > limit {
        ParseOutcome::Error(ParseError::InvalidCursor)
    } else if end && status == InputStatus::Partial {
        ParseOutcome::NeedMore
    } else if target < 0 {
        ParseOutcome::Error(ParseError::Mismatch)
    } else if target > limit {
        match status {
            InputStatus::Partial => ParseOutcome::NeedMore,
            InputStatus::Final => ParseOutcome::Error(ParseError::UnexpectedEnd),
        }
    } else {
        let next = Cursor {
            byte: (target / 8) as usize,
            bit: (target % 8) as u8,
        };
        ParseOutcome::Success(next, next)
    }
}

#[test]
fn exhaustive_small_positions_and_offsets() {
    for length in 0..=8 {
        for byte in 0..=length + 1 {
            for bit in 0..=9 {
                let start = Cursor { byte, bit };
                for status in [InputStatus::Partial, InputStatus::Final] {
                    for offset in -80..=80 {
                        for end in [false, true] {
                            let parser = if end {
                                Seek::from_end(offset)
                            } else {
                                Seek::relative(offset)
                            };
                            let base = if end {
                                length as i128 * 8
                            } else {
                                byte as i128 * 8 + i128::from(bit)
                            };
                            assert_eq!(
                                seek_position(parser, length, start, status),
                                oracle(length, start, base + offset as i128, status, end)
                            );
                        }
                    }
                    for target in 0..=8 * length + 9 {
                        assert_eq!(
                            seek_position(absolute(target), length, start, status),
                            oracle(length, start, target as i128, status, false)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn machine_boundaries_use_virtual_lengths() {
    assert!(
        usize::BITS <= 64,
        "the independent i128 oracle assumes at most 64-bit usize"
    );
    let max = usize::MAX;
    let points = [0, 1, max / 8, max / 8 + 1, max / 2, max - 1, max];
    for length in points {
        for byte in points {
            for bit in [0, 1, 7, 8, u8::MAX] {
                let start = Cursor { byte, bit };
                for status in [InputStatus::Partial, InputStatus::Final] {
                    for offset in [
                        isize::MIN,
                        isize::MIN + 1,
                        -9,
                        -8,
                        -1,
                        0,
                        1,
                        7,
                        8,
                        isize::MAX,
                    ] {
                        for end in [false, true] {
                            let parser = if end {
                                Seek::from_end(offset)
                            } else {
                                Seek::relative(offset)
                            };
                            let base = if end {
                                length as i128 * 8
                            } else {
                                byte as i128 * 8 + i128::from(bit)
                            };
                            assert_eq!(
                                seek_position(parser, length, start, status),
                                oracle(length, start, base + offset as i128, status, end)
                            );
                        }
                    }
                    for target_byte in points {
                        for target_bit in [0, 1, 7] {
                            let target = Cursor {
                                byte: target_byte,
                                bit: target_bit,
                            };
                            assert_eq!(
                                seek_position(Seek::to(target).unwrap(), length, start, status),
                                oracle(
                                    length,
                                    start,
                                    target_byte as i128 * 8 + i128::from(target_bit),
                                    status,
                                    false
                                )
                            );
                        }
                    }
                }
            }
        }
    }
    for bit in 8..=u8::MAX {
        assert!(matches!(
            Seek::to(Cursor { byte: 0, bit }),
            Err(ConfigError::InvalidBitOffset)
        ));
    }
}
