#![no_std]

use rusthammer::{Cursor, ParseError};

pub fn encoding(bits: u16) -> u32 {
    rusthammer_float_probe::half_bits(bits)
}

pub fn packet(input: &[u8], cursor: Cursor) -> Result<(Cursor, f32), ParseError> {
    rusthammer_float_probe::mapped_field(input, cursor)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn downstream_encoding() {
        assert_eq!(encoding(0x3e00), 0x3fc0_0000);
        assert_eq!(encoding(0x8000), 0x8000_0000);
        assert_eq!(encoding(1), 0x3380_0000);
    }

    #[test]
    fn downstream_packet() {
        assert_eq!(
            packet(&[0x3f, 0xc0, 0, 0], Cursor::start()),
            Ok((Cursor { byte: 4, bit: 0 }, 1.5))
        );
        assert_eq!(
            packet(&[0x3f, 0xc0], Cursor::start()),
            Err(ParseError::UnexpectedEnd)
        );
    }
}
