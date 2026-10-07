use rusthammer::{Cursor, ParseError};
use rusthammer_float_probe::*;

const BINARY32_CASES: &[u32] = &[
    0,
    0x8000_0000,
    1,
    0x007f_ffff,
    0x0080_0000,
    0x3f80_0000,
    0xbf80_0000,
    0x7f7f_ffff,
    0xff7f_ffff,
    0x7f80_0000,
    0xff80_0000,
    0x7f80_0001,
    0x7fc0_0000,
    0xffc1_2345,
];

const BINARY64_CASES: &[u64] = &[
    0,
    0x8000_0000_0000_0000,
    1,
    0x000f_ffff_ffff_ffff,
    0x0010_0000_0000_0000,
    0x3ff0_0000_0000_0000,
    0xbff0_0000_0000_0000,
    0x7fef_ffff_ffff_ffff,
    0xffef_ffff_ffff_ffff,
    0x7ff0_0000_0000_0000,
    0xfff0_0000_0000_0000,
    0x7ff0_0000_0000_0001,
    0x7ff8_0000_0000_0000,
    0xfff8_1234_5678_9abc,
];

#[test]
fn binary32_preserves_encodings() {
    for &bits in BINARY32_CASES {
        assert_eq!(encode32(identity32(decode32(bits))), bits);
    }
    assert_eq!(decode32(0x3fc0_0000), 1.5);
    assert_eq!(encode32(literal()), 0x3f80_0000);
}

#[test]
fn binary64_preserves_encodings() {
    for &bits in BINARY64_CASES {
        assert_eq!(encode64(identity64(decode64(bits))), bits);
    }
    assert_eq!(decode64(0x3ff8_0000_0000_0000), 1.5);
}

#[test]
fn half_conversion_matches_value_spec_exhaustively() {
    for bits in 0..=u16::MAX {
        let negative = bits & 0x8000 != 0;
        let exponent = (bits >> 10) & 0x1f;
        let fraction = bits & 0x03ff;
        let actual = decode16(bits);
        assert_eq!(actual.is_sign_negative(), negative, "{bits:04x}");
        if exponent == 31 {
            if fraction == 0 {
                assert!(actual.is_infinite(), "{bits:04x}");
            } else {
                assert!(actual.is_nan(), "{bits:04x}");
                assert_eq!(actual.to_bits() & 0x007f_ffff, u32::from(fraction) << 13);
            }
        } else {
            // Independent numerical specification: m * 2^e, exactly representable
            // in f64 and f32. No IEEE encoding manipulation is used here.
            let (significand, power) = if exponent == 0 {
                (fraction, -24)
            } else {
                (1024 + fraction, i32::from(exponent) - 25)
            };
            let mut expected = f64::from(significand);
            for _ in 0..power.unsigned_abs() {
                expected = if power < 0 {
                    expected / 2.0
                } else {
                    expected * 2.0
                };
            }
            if negative {
                expected = -expected;
            }
            assert_eq!(f64::from(actual), expected, "{bits:04x}");
        }
    }
}

#[test]
fn inclusive_ranges_reject_nans_and_reversed_bounds() {
    assert!(range32(1.0, 1.0, 2.0));
    assert!(range32(2.0, 1.0, 2.0));
    assert!(!range32(0.5, 1.0, 2.0));
    assert!(!range32(1.5, 2.0, 1.0));
    assert!(!range32(f32::NAN, 1.0, 2.0));
    assert!(!range32(1.0, f32::NAN, 2.0));
    assert!(!range32(1.0, 0.0, f32::NAN));
    assert!(range32(-0.0, 0.0, 0.0));
    assert!(range32(f32::INFINITY, f32::NEG_INFINITY, f32::INFINITY));
    assert!(range64(-0.0, 0.0, 0.0));
    assert!(!range64(f64::NAN, f64::NEG_INFINITY, f64::INFINITY));
    assert!(!range64(1.0, f64::NAN, 2.0));
    assert!(!range64(1.0, 0.0, f64::NAN));
    assert!(range64(f64::NEG_INFINITY, f64::NEG_INFINITY, f64::INFINITY));
}

#[test]
fn float_equality_is_not_encoding_equality() {
    assert!(equal32(0.0, -0.0));
    assert!(!equal32(f32::NAN, f32::NAN));
}

#[test]
fn widening_preserves_finite_values_and_double_bounds() {
    for &bits in BINARY32_CASES {
        let value = decode32(bits);
        if !value.is_nan() {
            assert_eq!((widen(value) as f32).to_bits(), bits);
        }
    }
    assert!(!range32_double_bounds(1.0, 1.00000001, 2.0));
    assert!(range32_double_bounds(1.0, 1.0, 2.0));
}

#[test]
fn integer_classification_matches_native_float_classification() {
    for &bits in BINARY32_CASES {
        assert_eq!(nan_bits32(bits), nan32(decode32(bits)));
    }
}

#[test]
fn float_fields_reuse_rusthammer_cursor_and_error_behavior() {
    for &bits in BINARY32_CASES {
        let bytes = bits.to_be_bytes();
        for parse in [float_field, mapped_field] {
            let (next, value) = parse(&bytes, Cursor::start()).unwrap();
            assert_eq!(next, Cursor { byte: 4, bit: 0 });
            assert_eq!(value.to_bits(), bits);
            assert_eq!(
                parse(&bytes[..3], Cursor::start()),
                Err(ParseError::UnexpectedEnd)
            );
            assert_eq!(
                parse(&bytes, Cursor { byte: 0, bit: 8 }),
                Err(ParseError::InvalidCursor)
            );
        }
        assert_eq!(raw_field(&bytes, Cursor::start()).unwrap().1, bits);
        let shifted = (u64::from(bits) << 7).to_be_bytes();
        let (next, value) = float_field(&shifted[3..], Cursor { byte: 0, bit: 1 }).unwrap();
        assert_eq!(next, Cursor { byte: 4, bit: 1 });
        assert_eq!(value.to_bits(), bits);
    }
}
