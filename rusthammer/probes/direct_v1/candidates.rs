//! Isolated Rust-valid borrowed callback controls; not passing extraction roots.
use crate::{map, Cursor, ParseError, Parser, TakeAligned};

pub fn borrowed_identity<'input>(
    input: &'input [u8],
    count: usize,
) -> Result<(Cursor, &'input [u8]), ParseError> {
    map(TakeAligned { count }, |bytes| bytes).parse(input, Cursor::start())
}

pub fn identity_bytes(bytes: &[u8]) -> &[u8] {
    bytes
}

pub fn named_identity(input: &[u8], count: usize) -> Result<(Cursor, &[u8]), ParseError> {
    map(TakeAligned { count }, identity_bytes).parse(input, Cursor::start())
}

pub fn function_item_lookup(
    input: &[u8],
    cursor: Cursor,
) -> Result<(Cursor, crate::mavlink::Packet<'_>), ParseError> {
    crate::mavlink::parse_frame(input, cursor, crate::mavlink::heartbeat_crc_extra)
}

pub fn pattern_loop<'pattern, 'input>(
    pattern: &'pattern [u8],
    input: &'input [u8],
) -> Result<(Cursor, &'pattern [u8]), ParseError> {
    let parsed = TakeAligned {
        count: pattern.len(),
    }
    .parse(input, Cursor::start())?;
    let (next, bytes) = parsed;
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != pattern[index] {
            return Err(ParseError::Mismatch);
        }
        index += 1;
    }
    Ok((next, pattern))
}
