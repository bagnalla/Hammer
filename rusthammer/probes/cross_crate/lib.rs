//! Extraction regression fixture using RustHammer as an ordinary Cargo dependency.
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

use rusthammer::{
    Bit, Bits, Cursor, End, Ignore, InputStatus, Left, Literal, Middle, ParseError, ParseOutcome,
    Parser, Right, Seq, TakeAligned, TryMap,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Flag {
    pub value: bool,
}

/// A captured fallible callback constructs an owned, non-Clone output.
pub fn checked_flag(input: &[u8], expected: bool, status: InputStatus) -> ParseOutcome<Flag> {
    let parser = TryMap {
        parser: Bit,
        map: |value| {
            if value == expected {
                Ok(Flag { value })
            } else {
                Err(())
            }
        },
    };
    parser.parse_with(input, Cursor::start(), status)
}

/// One flag bit, seven ignored bits, then a bracketed two-byte borrowed payload.
pub fn packet(input: &[u8], status: InputStatus) -> ParseOutcome<(bool, &[u8])> {
    let parser = Left {
        first: Seq {
            first: Bit,
            second: Right {
                first: Ignore {
                    parser: Bits::new(7).unwrap(),
                },
                second: Middle {
                    left: Literal::new(8, u64::from(b'[')).unwrap(),
                    parser: TakeAligned { count: 2 },
                    right: Literal::new(8, u64::from(b']')).unwrap(),
                },
            },
        },
        second: End,
    };
    parser.parse_with(input, Cursor::start(), status)
}

/// Also exercise the default complete-input trait method across the crate boundary.
pub fn complete_bit(input: &[u8]) -> Result<(Cursor, bool), ParseError> {
    Bit.parse(input, Cursor::start())
}

#[cfg(feature = "alloc")]
pub fn blocks(
    input: &[u8],
    count: usize,
    status: InputStatus,
) -> ParseOutcome<alloc::vec::Vec<&[u8]>> {
    rusthammer::Repeat::exact(TakeAligned { count: 1 }, count).parse_with(
        input,
        Cursor::start(),
        status,
    )
}

#[cfg(feature = "alloc")]
pub fn leading_ones(input: &[u8], status: InputStatus) -> ParseOutcome<alloc::vec::Vec<u64>> {
    rusthammer::Repeat::at_least(Literal::new(1, 1).unwrap(), 0).parse_with(
        input,
        Cursor::start(),
        status,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn captured_conversion_and_complete_entry_point() {
        assert_eq!(
            checked_flag(&[0x80], true, InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 0, bit: 1 }, Flag { value: true })
        );
        assert_eq!(
            checked_flag(&[0x80], false, InputStatus::Final),
            ParseOutcome::Error(ParseError::Mismatch)
        );
        assert_eq!(
            checked_flag(&[], true, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(complete_bit(&[]), Err(ParseError::UnexpectedEnd));
        assert_eq!(
            complete_bit(&[0x80]),
            Ok((Cursor { byte: 0, bit: 1 }, true))
        );
    }

    #[test]
    fn borrowed_packet_values_and_finality() {
        let input = [0x80, b'[', b'h', b'i', b']'];
        assert_eq!(
            packet(&input, InputStatus::Final),
            ParseOutcome::Success(Cursor { byte: 5, bit: 0 }, (true, &input[2..4]))
        );
        assert_eq!(packet(&input, InputStatus::Partial), ParseOutcome::NeedMore);
        assert_eq!(
            packet(&input[..4], InputStatus::Final),
            ParseOutcome::Error(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            packet(&[0, b'[', b'h', b'i', b'!'], InputStatus::Final),
            ParseOutcome::Error(ParseError::Mismatch)
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn collected_outputs_and_unbounded_stopping() {
        let input = *b"abc";
        assert_eq!(
            blocks(&input, 2, InputStatus::Partial),
            ParseOutcome::Success(
                Cursor { byte: 2, bit: 0 },
                alloc::vec![&input[..1], &input[1..2]]
            )
        );
        assert_eq!(
            blocks(&input, 4, InputStatus::Partial),
            ParseOutcome::NeedMore
        );
        assert_eq!(
            leading_ones(&[0xc0], InputStatus::Partial),
            ParseOutcome::Success(Cursor { byte: 0, bit: 2 }, alloc::vec![1, 1])
        );
        assert_eq!(
            leading_ones(&[0xff], InputStatus::Partial),
            ParseOutcome::NeedMore
        );
    }
}
