use rusthammer::{
    And, Bind, Byte, Choice, Cursor, End, Epsilon, FoldRepeat, Left, Not, Optional, ParseContext,
    ParseError, ParseOutcome, Parser, Right, Seq, SkipBits, Tell,
};

// Independent oracle uses absolute positions in a wider integer type. The
// implementation instead advances byte/bit components using usize arithmetic.
fn advance(length: usize, cursor: Cursor, bits: usize) -> Result<Cursor, ParseError> {
    let start = cursor.byte as u128 * 8 + u128::from(cursor.bit);
    let end = length as u128 * 8;
    if cursor.bit >= 8 || start > end {
        return Err(ParseError::InvalidCursor);
    }
    let next = start + bits as u128;
    if next > end {
        Err(ParseError::UnexpectedEnd)
    } else {
        Ok(Cursor {
            byte: (next / 8) as usize,
            bit: (next % 8) as u8,
        })
    }
}

fn expected<T>(result: Result<(Cursor, T), ParseError>, context: ParseContext) -> ParseOutcome<T> {
    match result {
        Ok((next, value)) => ParseOutcome::Success(next, value),
        Err(ParseError::UnexpectedEnd) if context == ParseContext::PARTIAL => {
            ParseOutcome::NeedMore
        }
        Err(error) => ParseOutcome::Error(error),
    }
}

#[test]
fn every_offset_and_truncation_agree_with_wide_arithmetic() {
    for length in (0..=17).chain([31, 32, 33]) {
        for fill in [0, 255] {
            let input = vec![fill; length];
            for byte in (0..=length + 1).chain([usize::MAX / 8, usize::MAX]) {
                for bit in (0..=9).chain([u8::MAX]) {
                    let cursor = Cursor { byte, bit };
                    let tell = advance(length, cursor, 0).map(|next| (next, next));
                    assert_eq!(Tell.parse(&input, cursor), tell);
                    for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                        assert_eq!(
                            Tell.parse_with(&input, cursor, context),
                            expected(tell, context)
                        );
                    }
                    for bits in (0..=145).chain([256, usize::MAX / 8, usize::MAX - 1, usize::MAX]) {
                        let parser = SkipBits::new(bits);
                        let result = advance(length, cursor, bits).map(|next| (next, ()));
                        assert_eq!(
                            parser.parse(&input, cursor),
                            result,
                            "{length} {cursor:?} {bits}"
                        );
                        for context in [ParseContext::PARTIAL, ParseContext::FINAL] {
                            assert_eq!(
                                parser.parse_with(&input, cursor, context),
                                expected(result, context)
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn constructors_are_const_and_parsers_and_outputs_are_copyable() {
    const SKIP: SkipBits = SkipBits::new(usize::MAX);
    const COUNT: usize = SKIP.bits();
    fn copyable<T: Copy>(_: T) {}
    copyable(SKIP);
    copyable(Tell);
    assert_eq!(COUNT, usize::MAX);
    assert_eq!(Clone::clone(&SKIP).bits(), COUNT);
    assert_eq!(core::mem::size_of::<Tell>(), 0);
    let output = {
        let input = [0; 11];
        let parser = SkipBits::new(80);
        Seq {
            first: &parser,
            second: &Clone::clone(&Tell),
        }
        .parse(&input, Cursor { byte: 0, bit: 7 })
        .unwrap()
    };
    let cursor = Cursor { byte: 10, bit: 7 };
    assert_eq!(output, (cursor, ((), cursor)));
}

#[test]
fn partial_skips_retry_and_preserve_backtracking_and_lookahead() {
    let start = Cursor { byte: 0, bit: 7 };
    let parser = Right {
        first: SkipBits::new(9),
        second: Tell,
    };
    assert_eq!(
        parser.parse_with(&[0], start, ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        parser.parse_with(&[0, 0], start, ParseContext::PARTIAL),
        ParseOutcome::Success(Cursor { byte: 2, bit: 0 }, Cursor { byte: 2, bit: 0 })
    );
    assert_eq!(
        Left {
            first: &parser,
            second: End
        }
        .parse(&[0, 0], start),
        Ok((Cursor { byte: 2, bit: 0 }, Cursor { byte: 2, bit: 0 }))
    );

    let skip = SkipBits::new(9);
    let choice = Choice {
        first: &skip,
        second: Epsilon,
    };
    assert_eq!(
        choice.parse(&[0], Cursor::start()),
        Ok((Cursor::start(), ()))
    );
    assert_eq!(
        choice.parse_with(&[0], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        Optional { parser: &skip }.parse(&[0], Cursor::start()),
        Ok((Cursor::start(), None))
    );
    assert_eq!(And { parser: &skip }.parse(&[0, 0], start), Ok((start, ())));
    assert_eq!(Not { parser: &skip }.parse(&[0], start), Ok((start, ())));
    assert_eq!(
        Not { parser: &skip }.parse_with(&[0], start, ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
    assert_eq!(
        choice.parse(&[], Cursor { byte: 0, bit: 1 }),
        Err(ParseError::InvalidCursor)
    );
}

#[test]
fn zero_consumption_is_visible_to_repetition() {
    let tells = FoldRepeat::exact(Tell, 3, || 0, |count, _| count + 1);
    assert_eq!(tells.parse(&[], Cursor::start()), Ok((Cursor::start(), 3)));
    let unbounded = FoldRepeat::at_least(Tell, 0, || (), |(), _| ());
    assert_eq!(
        unbounded.parse(&[], Cursor::start()),
        Err(ParseError::NonProgress)
    );
    let zero_skips = FoldRepeat::at_least(SkipBits::new(0), 0, || (), |(), ()| ());
    assert_eq!(
        zero_skips.parse(&[], Cursor::start()),
        Err(ParseError::NonProgress)
    );
    let bytes = FoldRepeat::at_least(SkipBits::new(8), 0, || 0, |count, ()| count + 1);
    assert_eq!(
        bytes.parse(&[0; 4], Cursor::start()),
        Ok((Cursor { byte: 4, bit: 0 }, 4))
    );
    assert_eq!(
        bytes.parse_with(&[0; 4], Cursor::start(), ParseContext::PARTIAL),
        ParseOutcome::NeedMore
    );
}

#[test]
fn parsed_counts_configure_skips_and_tell_records_positions() {
    let parser = Seq {
        first: Tell,
        second: Right {
            first: Bind {
                parser: Byte,
                then: |bits| SkipBits::new(usize::from(bits)),
            },
            second: Seq {
                first: Tell,
                second: Byte,
            },
        },
    };
    // Header says to skip three bits, then the unaligned byte is 0b10100110.
    assert_eq!(
        parser.parse(&[3, 0b0001_0100, 0b1100_0000], Cursor::start()),
        Ok((
            Cursor { byte: 2, bit: 3 },
            (Cursor::start(), (Cursor { byte: 1, bit: 3 }, 0xa6))
        ))
    );
}
