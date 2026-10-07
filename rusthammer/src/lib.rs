//! Small, experimental parsing core for translation and verification with Aeneas.
//!
//! Bit and byte ordering are configurable. Changes of bit direction require
//! byte-aligned scope boundaries; see [`WithOrder`] for details. Chunk buffering,
//! recursion, and compiled backends are not implemented.
//!
//! Build concrete grammar nodes with [`seq`], [`choice`], [`optional`], [`map`],
//! [`try_map`], [`verify`], and [`bind`]. These functions store their arguments;
//! parsing and callbacks run only when the grammar is evaluated. Construction
//! does not select a backend or require direct parsing support.
//! All grammar primitives and combinators are grouped in [`grammar`]; their
//! crate-root exports are also available for convenient imports.
//!
//! Parser values implement `Clone` and `Copy` when their stored children and
//! callbacks do. Parsed outputs need neither trait. For example, a copied grammar
//! can produce values that implement neither `Clone` nor `Copy`:
//!
//! ```
//! use rusthammer::{Bit, Cursor, Map, Parser, Seq};
//!
//! #[derive(Debug, PartialEq)]
//! struct Flag(bool);
//!
//! let flag = Map { parser: Bit, map: |bit| Flag(bit) };
//! let pair = Seq { first: flag, second: flag };
//! let copied = pair;
//! assert_eq!(copied.parse(&[0x80], Cursor::start()),
//!     Ok((Cursor { byte: 0, bit: 2 }, (Flag(true), Flag(false)))));
//! assert_eq!(pair.parse(&[0x80], Cursor::start()),
//!     copied.parse(&[0x80], Cursor::start()));
//! ```
//!
//! Copies duplicate the stored configuration; their cost grows with its size.
//! `clone()` delegates to each field's `Clone` implementation and may allocate
//! when a child or callback owns data. Shared parser references are another way
//! to reuse a grammar, including when its components implement neither trait.

#![no_std]
#![forbid(unsafe_code)]

/// Typed grammar primitives and combinators.
pub mod grammar;
// Specific private names avoid clashes with input/parser/span locals in Lean.
mod input_types;
mod parser_traits;
mod span_types;

pub use input_types::{
    BitOrder, ByteOrder, ConfigError, Cursor, InputStatus, Order, ParseContext, ParseError,
    ParseOutcome,
};
pub use parser_traits::{Direct, Eval, Grammar, Parser};
pub use span_types::BitSpan;

// Keep crate-root imports available alongside the grammar namespace.
pub use grammar::{
    bind, choice, map, optional, permutation, read_bit, read_bits, required, seq, take_aligned,
    try_map, verify, And, BeI16, BeI32, BeI64, BeU16, BeU32, BeU64, Bind, Bit, Bits, ButNot, Byte,
    ByteIn, ByteNotIn, BytePattern, Choice, Difference, End, Epsilon, Fail, FoldRepeat, FoldSepBy,
    Ignore, IntRange, Left, Literal, Map, Middle, Not, Optional, Permutation, Recognize, Required,
    Right, Seq, SignedBits, SkipBits, TakeAligned, Tell, TryMap, Verify, WithOrder, WithSpan, Xor,
    I8,
};
#[cfg(feature = "alloc")]
pub use grammar::{Repeat, SepBy};

// Extract the same application code used by the examples and tests without
// adding example formats to the library API or ordinary builds.
#[cfg(rusthammer_verify)]
#[allow(dead_code)] // Entry points are reached by Charon, not by Rust library calls.
#[path = "../examples/support/dependent.rs"]
mod dependent_examples;

#[cfg(rusthammer_verify)]
#[allow(dead_code)]
#[path = "../examples/support/flags.rs"]
mod flags_example;

#[cfg(rusthammer_verify)]
#[allow(dead_code)]
#[path = "../examples/support/marker.rs"]
mod marker_example;

#[cfg(rusthammer_verify)]
#[allow(dead_code)]
#[path = "../examples/support/record.rs"]
mod record_example;

#[cfg(feature = "alloc")]
extern crate alloc;
