//! Private extraction probes, not proposed production parser APIs.
#![no_std]

use rusthammer::{BeU32, Cursor, Map, ParseError, Parser};

pub fn identity32(value: f32) -> f32 {
    value
}

pub fn identity64(value: f64) -> f64 {
    value
}

pub fn decode32(bits: u32) -> f32 {
    f32::from_bits(bits)
}

pub fn decode64(bits: u64) -> f64 {
    f64::from_bits(bits)
}

pub fn encode32(value: f32) -> u32 {
    value.to_bits()
}

pub fn encode64(value: f64) -> u64 {
    value.to_bits()
}

pub fn range32(value: f32, lower: f32, upper: f32) -> bool {
    lower <= value && value <= upper
}

pub fn range64(value: f64, lower: f64, upper: f64) -> bool {
    lower <= value && value <= upper
}

/// C Hammer widens a binary32 value before comparing its binary64 bounds.
pub fn range32_double_bounds(value: f32, lower: f64, upper: f64) -> bool {
    let value = value as f64;
    lower <= value && value <= upper
}

pub fn equal32(left: f32, right: f32) -> bool {
    left == right
}

pub fn nan32(value: f32) -> bool {
    value.is_nan()
}

pub fn widen(value: f32) -> f64 {
    value as f64
}

pub fn literal() -> f32 {
    1.0
}

/// A passing integer-only control using the actual RustHammer reader.
pub fn raw_field(input: &[u8], cursor: Cursor) -> Result<(Cursor, u32), ParseError> {
    BeU32.parse(input, cursor)
}

/// Separate integer decoding from the conversion needed for native float output.
pub fn float_field(input: &[u8], cursor: Cursor) -> Result<(Cursor, f32), ParseError> {
    let (next, bits) = BeU32.parse(input, cursor)?;
    Ok((next, f32::from_bits(bits)))
}

pub fn mapped_field(input: &[u8], cursor: Cursor) -> Result<(Cursor, f32), ParseError> {
    Map {
        parser: BeU32,
        map: decode32,
    }
    .parse(input, cursor)
}

/// Classify binary32 encodings using only integer operations.
pub fn nan_bits32(bits: u32) -> bool {
    bits & 0x7f80_0000 == 0x7f80_0000 && bits & 0x007f_ffff != 0
}

/// Binary16-to-binary32 encoding conversion, without constructing a Rust float.
/// Finite values widen exactly; NaN sign and payload bits are carried across.
pub fn half_bits(bits: u16) -> u32 {
    let sign = u32::from(bits & 0x8000) << 16;
    let exponent = u32::from((bits >> 10) & 0x1f);
    let mut fraction = u32::from(bits & 0x03ff);
    if exponent == 0 {
        if fraction == 0 {
            sign
        } else {
            let mut adjusted = 113u32;
            while fraction & 0x0400 == 0 {
                fraction <<= 1;
                adjusted -= 1;
            }
            sign | (adjusted << 23) | ((fraction & 0x03ff) << 13)
        }
    } else if exponent == 0x1f {
        sign | 0x7f80_0000 | (fraction << 13)
    } else {
        sign | ((exponent + 112) << 23) | (fraction << 13)
    }
}

pub fn decode16(bits: u16) -> f32 {
    f32::from_bits(half_bits(bits))
}
