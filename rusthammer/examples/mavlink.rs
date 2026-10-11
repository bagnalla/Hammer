#[path = "support/mavlink.rs"]
mod mavlink;

use mavlink::{heartbeat_crc_extra, mavlink_v2, HEARTBEAT_FRAME};
use rusthammer::{Cursor, ParseContext, ParseError, ParseOutcome, Parser};

fn main() -> Result<(), ParseError> {
    let parser = mavlink_v2(heartbeat_crc_extra);
    let (next, packet) = parser.parse(&HEARTBEAT_FRAME, Cursor::start())?;
    println!("header: {:?}", packet.header);
    println!("payload: {:02x?}", packet.payload);
    println!("checksum: {:#06x}; next cursor: {next:?}", packet.checksum);

    assert_eq!(
        parser.parse_with(
            &HEARTBEAT_FRAME[..15],
            Cursor::start(),
            ParseContext::PARTIAL
        ),
        ParseOutcome::NeedMore
    );
    Ok(())
}
