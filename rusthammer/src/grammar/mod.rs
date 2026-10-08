//! Primitives and combinators for constructing typed grammars.
//!
//! Constructors store their children and configuration. Parsing starts through
//! [`crate::Parser`] or [`crate::Eval`]. Family modules are private; their public
//! grammar types and constructors are available directly in this namespace.
//!
//! ```
//! use rusthammer::grammar::{seq, BeU16, Byte};
//! use rusthammer::{Cursor, Parser};
//!
//! let header = seq(Byte, BeU16);
//! assert_eq!(header.parse(&[7, 0, 3, 99], Cursor::start()),
//!     Ok((Cursor { byte: 3, bit: 0 }, (7, 3))));
//! ```

mod bytes;
mod control;
mod numeric;
mod order;
mod permutation;
mod position;
mod repeat;
mod sequence;
mod span;
mod transform;

pub use bytes::{take_aligned, ByteIn, ByteNotIn, BytePattern, TakeAligned};
pub use control::{
    choice, optional, And, ButNot, Choice, Difference, Epsilon, Fail, Not, Optional, Xor,
};
pub use numeric::{
    read_bit, read_bits, BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Bit, Bits, Byte, Literal,
    SignedBits, I8,
};
pub use order::WithOrder;
pub use permutation::{permutation, required, Permutation, Required};
pub use position::{End, Seek, SkipBits, Tell};
pub use repeat::{FoldRepeat, FoldSepBy};
#[cfg(feature = "alloc")]
pub use repeat::{Repeat, SepBy};
pub use sequence::{bind, seq, Bind, Ignore, Left, Middle, Right, Seq};
pub use span::{Recognize, WithSpan};
pub use transform::{map, try_map, verify, IntRange, Map, TryMap, Verify};
