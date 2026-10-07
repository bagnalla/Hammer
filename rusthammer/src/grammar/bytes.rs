use super::super::{Byte, Cursor, Eval, Grammar, ParseContext, ParseError, ParseOutcome, Verify};

/// Fixed bitmap over the byte domain, shared by inclusion and exclusion.
#[derive(Clone, Copy)]
struct ByteSet {
    words: [u64; 4],
}

impl ByteSet {
    const fn new(bytes: &[u8]) -> Self {
        let mut words = [0u64; 4];
        let mut index = 0;
        while index < bytes.len() {
            let byte = bytes[index];
            words[(byte / 64) as usize] |= 1u64 << (byte % 64);
            index += 1;
        }
        Self { words }
    }

    const fn contains(&self, byte: u8) -> bool {
        self.words[(byte / 64) as usize] & (1u64 << (byte % 64)) != 0
    }
}

/// Read one byte belonging to a set of literal byte values.
///
/// Corresponds to Hammer's `h_in`. The set is a byte slice, not a regular
/// expression: order and duplicates do not affect membership. Construction is
/// infallible, including for empty sets and embedded zeros, and allocates nothing.
/// Construction scans the slice once into an owned 32-byte bitmap; membership
/// takes constant time. The parser does not borrow the slice or preserve its
/// order and duplicates. Copying a parser copies its bitmap.
///
/// Parsing delegates to `Verify` over `Byte`, returning the decoded `u8` and
/// consuming eight bits on success, even from an unaligned cursor. A decoded
/// nonmember returns `Mismatch`. Invalid cursors and short input follow `Byte`'s
/// rules, including `NeedMore` on partial input, even when the set is empty.
/// The output does not borrow the set, input, or parser.
///
/// ```
/// use rusthammer::{ByteIn, Cursor, Parser};
/// const SEPARATOR: ByteIn = ByteIn::new(b",;:");
/// assert!(SEPARATOR.accepts(b';'));
/// assert_eq!(SEPARATOR.parse(b";", Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, b';')));
/// ```
///
/// ```compile_fail,E0616
/// let hidden = rusthammer::ByteIn::new(b"abc").set;
/// ```
#[derive(Clone, Copy)]
pub struct ByteIn {
    set: ByteSet,
}

impl ByteIn {
    /// Build an owned bitmap of allowed values. Every slice is a valid set.
    pub const fn new(bytes: &[u8]) -> Self {
        Self {
            set: ByteSet::new(bytes),
        }
    }

    /// Test whether a decoded byte would be accepted, without reading input.
    pub const fn accepts(&self, byte: u8) -> bool {
        self.set.contains(byte)
    }
}

impl<'input> Grammar<'input> for ByteIn {
    type Output = u8;
}

impl<'input, Backend> Eval<'input, Backend> for ByteIn {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        Verify {
            parser: Byte,
            predicate: |value: &u8| self.accepts(*value),
        }
        .eval(backend, input, cursor, context)
    }
}

/// Read one byte outside a set of literal byte values.
///
/// Corresponds to Hammer's `h_not_in`. Like `ByteIn`, construction is infallible
/// and allocation-free, and parsing uses `Verify` over `Byte`. A decoded member
/// returns `Mismatch`; success returns the decoded `u8` and consumes eight bits
/// without implicit alignment. An empty exclusion set accepts any decoded byte.
/// Short input still returns `NeedMore` on partial input or `UnexpectedEnd` on
/// final input. The output does not borrow the set, input, or parser.
/// Construction scans the slice once into an owned 32-byte bitmap; membership
/// takes constant time. The parser does not borrow the slice or preserve its
/// order and duplicates. Copying a parser copies its bitmap.
///
/// ```
/// use rusthammer::{ByteNotIn, Cursor, ParseError, Parser};
/// let content = ByteNotIn::new(b"\r\n");
/// assert_eq!(content.parse(b"x", Cursor::start()),
///     Ok((Cursor { byte: 1, bit: 0 }, b'x')));
/// assert_eq!(content.parse(b"\n", Cursor::start()), Err(ParseError::Mismatch));
/// ```
///
/// ```compile_fail,E0616
/// let hidden = rusthammer::ByteNotIn::new(b"abc").set;
/// ```
#[derive(Clone, Copy)]
pub struct ByteNotIn {
    set: ByteSet,
}

impl ByteNotIn {
    /// Build an owned bitmap of excluded values. Every slice is a valid set.
    pub const fn new(bytes: &[u8]) -> Self {
        Self {
            set: ByteSet::new(bytes),
        }
    }

    /// Test whether a decoded byte would be accepted, without reading input.
    /// Returns true precisely for bytes outside the configured exclusion set.
    pub const fn accepts(&self, byte: u8) -> bool {
        !self.set.contains(byte)
    }
}

impl<'input> Grammar<'input> for ByteNotIn {
    type Output = u8;
}

impl<'input, Backend> Eval<'input, Backend> for ByteNotIn {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<u8> {
        Verify {
            parser: Byte,
            predicate: |value: &u8| self.accepts(*value),
        }
        .eval(backend, input, cursor, context)
    }
}

/// Match a borrowed byte pattern, including from an unaligned bit cursor.
///
/// Success returns the configured pattern slice, whose lifetime is independent
/// of the input and of the parser value. This requires no allocation even when
/// the matched bits cross byte boundaries. Use `TakeAligned` to borrow input.
/// An empty pattern succeeds without reading input or validating the cursor.
///
/// Bytes are compared in order: a complete differing byte rejects immediately.
/// A missing or incomplete byte returns `NeedMore` on partial input and
/// `UnexpectedEnd` on final input, even if its available bits already differ.
///
/// ```
/// use rusthammer::{BytePattern, Cursor, Parser};
/// let pattern = [0xab, 0xcd];
/// let matched = {
///     let input = [0x55, 0xe6, 0x80];
///     BytePattern::new(&pattern).parse(&input, Cursor { byte: 0, bit: 1 }).unwrap().1
/// };
/// assert!(core::ptr::eq(matched, &pattern[..]));
/// ```
#[derive(Clone, Copy)]
pub struct BytePattern<'pattern> {
    pattern: &'pattern [u8],
}

impl<'pattern> BytePattern<'pattern> {
    /// Every slice is a valid pattern, including empty slices and embedded zeros.
    pub const fn new(pattern: &'pattern [u8]) -> Self {
        Self { pattern }
    }

    /// Return the configured pattern, which is also the successful parse output.
    pub const fn pattern(&self) -> &'pattern [u8] {
        self.pattern
    }
}

impl<'input, 'pattern> Grammar<'input> for BytePattern<'pattern> {
    type Output = &'pattern [u8];
}

impl<'input, 'pattern, Backend> Eval<'input, Backend> for BytePattern<'pattern> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        // Keep the returned pattern borrow outside the matching loop. The pinned
        // Aeneas cannot join the loop's borrow contexts when it returns the slice.
        // See probes/pattern_loop_borrow.rs and the accompanying probe notes.
        match match_byte_pattern(backend, self.pattern, input, cursor, context) {
            ParseOutcome::Success(next, ()) => ParseOutcome::Success(next, self.pattern),
            ParseOutcome::Error(error) => ParseOutcome::Error(error),
            ParseOutcome::NeedMore => ParseOutcome::NeedMore,
        }
    }
}

fn match_byte_pattern<Backend>(
    backend: &mut Backend,
    pattern: &[u8],
    input: &[u8],
    cursor: Cursor,
    context: ParseContext,
) -> ParseOutcome<()> {
    let mut next = cursor;
    let mut index = 0;
    while index < pattern.len() {
        match Byte.eval(backend, input, next, context) {
            ParseOutcome::Success(after, value) => {
                if value != pattern[index] {
                    return ParseOutcome::Error(ParseError::Mismatch);
                }
                next = after;
                index += 1;
            }
            ParseOutcome::Error(error) => return ParseOutcome::Error(error),
            ParseOutcome::NeedMore => return ParseOutcome::NeedMore,
        }
    }
    ParseOutcome::Success(next, ())
}

/// Borrow an explicitly byte-aligned payload without copying.
///
/// This is not a replacement for Hammer's unaligned `h_bytes` primitive.
/// Every `usize` count is valid configuration; available input is checked per parse.
#[derive(Clone, Copy)]
pub struct TakeAligned {
    pub count: usize,
}

impl<'input> Grammar<'input> for TakeAligned {
    type Output = &'input [u8];
}

impl<'input, Backend> Eval<'input, Backend> for TakeAligned {
    fn eval(
        &self,
        _: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output> {
        context
            .status
            .classify(take_aligned(input, cursor, self.count))
    }
}

/// Parse a byte-aligned payload with a borrowed output.
pub fn take_aligned(
    input: &[u8],
    cursor: Cursor,
    count: usize,
) -> Result<(Cursor, &[u8]), ParseError> {
    if cursor.bit >= 8
        || cursor.byte > input.len()
        || (cursor.byte == input.len() && cursor.bit != 0)
    {
        return Err(ParseError::InvalidCursor);
    }
    if cursor.bit != 0 {
        return Err(ParseError::Unaligned);
    }
    if count > input.len() - cursor.byte {
        return Err(ParseError::UnexpectedEnd);
    }
    let end = cursor.byte + count;
    Ok((Cursor { byte: end, bit: 0 }, &input[cursor.byte..end]))
}
