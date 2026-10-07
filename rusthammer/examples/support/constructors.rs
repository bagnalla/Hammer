//! A grammar factory shared by the runnable example, tests, and Cargo consumer.
use rusthammer::{map, seq, BeU16, Byte, Map, Seq};

// The output deliberately implements neither Clone nor Copy.
#[derive(Debug, PartialEq, Eq)]
pub struct Header {
    pub tag: u8,
    pub length: u16,
}

/// Hide the closure type while preserving the node's backend implementations.
pub fn header() -> Map<Seq<Byte, BeU16>, impl Fn((u8, u16)) -> Header + Copy> {
    map(seq(Byte, BeU16), |(tag, length)| Header { tag, length })
}
