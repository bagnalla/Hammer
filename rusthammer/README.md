# RustHammer prototype

This implements the early checkpoints from the
[RustHammer plan](../plans/rusthammer.md): a dependency-free Rust parsing core,
its generated Aeneas translation, and Lean-checked specifications and proofs.
The public API is experimental. The
[combinator API plan](../plans/rusthammer-combinators.md) records the intended final
families and their implementation order; public additions must have a durable
role beyond an implementation or proof milestone. The features below describe
what is implemented today.

The prototype supports:

- A cursor with a byte index and a bit offset, passed separately from the input.
- Reading bits from either end of each byte and independent big/little byte order.
- `WithOrder` scopes, with aligned entry and successful exit when bit direction changes.
- Unsigned numeric fields of 0 through 64 bits, producing `u64` values and
  supporting unaligned starts and byte-boundary crossing.
- Signed two's-complement fields of 0 through 64 bits, producing `i64` with
  the same cursor and input-finality rules.
- Fixed-width `BeU16`, `BeU32`, `BeU64`, `I8`, `BeI16`, `BeI32`, and `BeI64`
  readers returning their corresponding native Rust integer types.
- `IntRange<P, T>` for inclusive ranges with typed, validated bounds.
- `Byte` producing `u8` and `BytePattern` matching arbitrary borrowed patterns,
  both supporting unaligned starts without allocation.
- `ByteIn` and `ByteNotIn` accepting or excluding literal byte sets and returning `u8`.
- `SkipBits` discarding arbitrary bit counts and `Tell` reporting a validated cursor.
- Private numeric and literal configuration, validated by fallible constructors.
- `Parser<'input>` with an associated `Output` type and explicit ordering/finality context.
- Separate `Success`, `Error`, and `NeedMore` outcomes, with a complete-buffer convenience API.
- `Seq<P, Q>`, which returns a typed pair and propagates child errors.
- `Bind<P, F>`, whose factory uses a parsed value to configure the next parser.
- Shared parser references and `Left`, `Right`, `Middle`, and `Ignore` for selecting outputs.
- `Clone` and `Copy` for parser values when their stored children and callbacks support them.
- `Map<P, F>` for typed output transformations, `TryMap<P, F>` for checked conversions,
  and `Verify<P, F>` for predicates.
- `Epsilon` for empty success and `Fail<T>` for definite rejection with a chosen output type.
- `Choice<P, Q>`, which tries ordered alternatives with the same output type.
- `ButNot<P, Q>` and `Difference<P, Q>` for match-length restrictions, and `Xor<P, Q>` for exclusive alternatives.
- `Optional<P>` for optional typed values, and `And<P>` / `Not<P>` for lookahead.
- Exact, bounded, and unbounded `Repeat<P>` collecting typed outputs, with optional `alloc`.
- `FoldRepeat<P, I, F>` folding those same repetitions into an owned accumulator without library allocation.
- `SepBy<P, S>` and `FoldSepBy<P, S, I, F>` for separated lists, collecting or folding only item outputs.
- Numeric literal matching and an exact end-of-input check.
- An explicitly aligned payload parser returning a borrowed `&'input [u8]`.

Verified application examples live in [`examples/support/`](examples/support/):
a three-bit `Flags` header, a complete `CA FE` / `CA` marker grammar, a bounded
record with a borrowed payload, and count-prefixed formats built with `Bind`.
Their types, parsing helpers, and format limits belong to those examples and
are absent from the public library API. Runnable examples, native tests, and
Lean extraction share each format's source.

The library uses `no_std` and forbids unsafe Rust. Default features are empty;
without `alloc`, the built-in core allocates no memory. The optional `alloc` feature
enables `Repeat` and `SepBy`, using `alloc::vec::Vec` and an application-provided allocator.
It does not enable `std`. Successful parsing reports the next cursor and preserves
remaining bits; composing with
`End` requires complete consumption. `TakeAligned` deliberately requires byte
alignment and is not the planned implementation of Hammer's unaligned `h_bytes`.

## Run the prototype

From this directory:

```sh
cargo test --no-default-features
cargo test --features alloc
cargo run --example flags
cargo run --example fields
cargo run --example ordering
cargo run --example signed_fields
cargo run --example integers
cargo run --example ranges
cargo run --example byte_sets
cargo run --example position
cargo run --example bytes
cargo run --example marker
cargo run --example matches
cargo run --example record
cargo run --example lookahead
cargo run --example input_status
cargo run --example selection
cargo run --example composition
cargo run --features alloc --example repeat
cargo run --no-default-features --example fold_repeat
cargo run --no-default-features --example separated
cargo run --features alloc --example separated
cargo run --no-default-features --example dependent
cargo run --features alloc --example dependent
```

The `flags` example parses `101` from the start of `0b1010_0000` and returns:

```text
Flags { urgent: true, encrypted: false, compressed: true }; next cursor: Cursor { byte: 0, bit: 3 }
```

The `fields` example sequences a 3-bit version and a 13-bit length from `[0xa1,
0x34]`, returning `(5u64, 308u64)` and cursor `{ byte: 2, bit: 0 }`.

`Bits::new(width)` constructs an unsigned reader using the active order, returning
`Result<Bits, ConfigError>`. Widths above 64 produce `ConfigError::InvalidWidth`
before any input is supplied. The resulting parser can be reused through
`parser.parse(input, cursor)` or `read_bits(input, cursor, &parser)`.
A zero-width field returns zero without consuming input, including at end-of-input;
an invalid cursor is still rejected. `Byte` reads the same eight bits as
`Bits::new(8)` and returns `u8`. `SignedBits::new(width)` reads those bits as a
signed `i64`. `parse()` and `read_bits()` use high-first bits and big byte order;
`parse_with()` takes explicit settings, as described below.

For example, a grammar builder can propagate construction errors with `?`:

```rust
use rusthammer::{Bits, ConfigError, Literal, Seq};

fn grammar(width: u8) -> Result<Seq<Literal, Bits>, ConfigError> {
    Ok(Seq {
        first: Literal::new(8, 0xca)?,
        second: Bits::new(width)?,
    })
}
```

The configuration fields of `Bits` and `Literal` are private. Read-only `width()`
and `value()` accessors expose their settings; there are no setters or unchecked
constructors. Parsing relies on the validated configuration and continues to
check cursors, alignment, and available input. `Seq` and `Choice` can still be
assembled directly from their children. `TakeAligned` accepts every `usize` count,
so its available-input check belongs in parsing and needs no fallible constructor.
For a future parser whose configuration comes from an input field, the application
must decide how a construction failure maps to its format's rejection semantics.

The tests cover every byte's bit values and order, byte-boundary crossing, typed
composition, truncation, invalid cursors, and borrowed payload bounds and identity.
Numeric tests exhaust every two-byte input at every starting bit offset for an
8-bit field, and check all widths through 64 against a binary-string oracle at
every cursor in several longer inputs, including truncation and the maximum
`u64` value. Constructor tests cover every `u8` width and literal representability
boundaries at all supported widths. Compile-fail doctests check that callers
cannot directly construct or mutate the private configuration.

## Signed fields

`SignedBits::new(width)` corresponds to C Hammer's `h_bits(width, true)`.
It returns `Result<SignedBits, ConfigError>`, accepting widths 0 through 64 and
rejecting larger widths with `InvalidWidth`. The configuration is private,
`width()` exposes it, and parser values implement `Copy` and `Clone`.

```rust
use rusthammer::{Cursor, Parser, SignedBits};

let field = SignedBits::new(5).unwrap();
assert_eq!(field.parse(&[0b1110_1000], Cursor::start()),
    Ok((Cursor { byte: 0, bit: 5 }, -3i64)));
```

For a nonempty field of width `w`, its unsigned binary value `u` is interpreted
as `u` when the top bit is zero, or mathematically `u - 2^w` when it is one.
The range is `-2^(w-1)` through `2^(w-1)-1`; width 64 covers all of `i64`.
Width zero returns zero without consuming input, while still validating the
cursor. Reads may start inside a byte and never implicitly align. Short input
returns `NeedMore` in partial mode or `UnexpectedEnd` in final mode.

The implementation reuses `Bits` and a private sign-extension helper. The
negative branch computes `-1 - (2^w - 1 - u)` using bounded intermediate values;
it never constructs `2^64`, negates `i64::MIN`, or casts an unrepresentable value
to `i64`. Lean proves every intermediate fits and both casts preserve values.
No allocation, callbacks, or additional Aeneas workaround is required.

The [signed-fields example](examples/signed_fields.rs) sequences an unaligned
signed field and unsigned flags, retaining `i64` and `u64` as distinct output
types. Tests cover all constructor widths, an independent binary-string/`i128`
oracle, signed boundaries at every width and bit offset, retries, invalid raw
cursors, and composition. Separate-crate extraction exercises dynamic
construction, signed extremes, and sequencing through a parser reference.
The optional C comparison below includes 27,724 signed-field cases in addition
to the byte-pattern and fixed-width integer cases.

## Fixed-width integers

The integer readers return native Rust values and correspond to C Hammer's
named integer primitives under its default ordering:

| RustHammer | Output | C Hammer |
| --- | --- | --- |
| `Byte` | `u8` | `h_uint8()` |
| `I8` | `i8` | `h_int8()` |
| `BeU16`, `BeI16` | `u16`, `i16` | `h_uint16()`, `h_int16()` |
| `BeU32`, `BeI32` | `u32`, `i32` | `h_uint32()`, `h_int32()` |
| `BeU64`, `BeI64` | `u64`, `i64` | `h_uint64()`, `h_int64()` |

These are zero-sized, `Copy` and `Clone` parser values. Use them directly; their
widths are always valid, so they have no fallible constructor or configuration.
`Be` explicitly pins big byte order and inherits the active bit direction.
Readers start at the supplied cursor, including unaligned fields, and never insert alignment padding.
They consume exactly their output type's bit width and use two's-complement
interpretation for signed outputs. Invalid cursors return `InvalidCursor`; short
input returns `NeedMore` in partial mode or `UnexpectedEnd` in final mode.

```rust
use rusthammer::{BeI16, BeU16, Cursor, Parser, Seq};

let parser = Seq { first: BeU16, second: BeI16 };
let (next, values): (Cursor, (u16, i16)) =
    parser.parse(&[0x12, 0x34, 0xff, 0xfd], Cursor::start()).unwrap();
assert_eq!(values, (0x1234, -3));
assert_eq!(next, Cursor { byte: 4, bit: 0 });
```

The [integers example](examples/integers.rs) runs this typed sequence. The readers
reuse `Bits` or `SignedBits`; a private macro shares outcome propagation. Lean
proves that narrowing casts preserve the decoded value, including each signed
minimum. The 64-bit readers preserve the general decoders' values directly.
No callbacks or allocation are needed. Native tests use an independent
binary-string/`i128` oracle, exhaust every 8- and 16-bit pattern, and compare
native `from_be_bytes` decoding at every starting bit offset. Tests also cover
raw invalid cursors, truncation, partial retries, references, and typed composition.
The optional C check adds 134,896 cases against the named integer primitives.

## Inclusive integer ranges

`IntRange::new(parser, lower, upper)` corresponds to `h_int_range`; using `Byte`
as its child also supplies `h_ch_range`. Both endpoints are inclusive and have
the child's output type. Construction returns `Result<IntRange<P, T>, ConfigError>`
and rejects `lower > upper` with `InvalidBounds` before any parsing. Equal
bounds accept precisely one value. Fields are private, and `lower()` / `upper()`
borrow the endpoints without exposing mutation.

```rust
use rusthammer::{BeI16, BeU16, Byte, IntRange};

let length = IntRange::new(BeU16, 1u16, 4096u16).unwrap();
let adjustment = IntRange::new(BeI16, -100i16, 100i16).unwrap();
let digit = IntRange::new(Byte, b'0', b'9').unwrap();
```

The [ranges example](examples/ranges.rs) combines these parsers and propagates
configuration errors with `?`. Bounds remain in their native type, including
the full `u64` range and signed minima. The generic implementation uses `Ord`,
so integer newtypes and other ordered outputs also work. Neither the child,
bounds, nor outputs need `Copy` or `Clone`; the range has those traits when its
stored fields do. Floating-point values lack `Ord` and need an explicit `Verify`
predicate with the desired NaN policy. The generic constructor is not `const`.

Parsing delegates to `Verify`. It runs the child once, preserves an accepted
value and cursor, maps an out-of-range value to recoverable `Mismatch`, and
propagates child errors and `NeedMore` unchanged. It adds no cursor validation
or implicit alignment. Bounds need not overlap the child's possible outputs;
for example, a three-bit reader restricted to 10 through 20 is a valid parser
that rejects every completed field. Range rejection waits for child success:
a two-byte reader given only `FF` in partial mode still returns `NeedMore`, even
if that prefix cannot fit the configured range. This retains the child's
established finality and error precedence.

Native tests cover every 8-bit bound pair, all native reader types, variable
widths (including zero), an independent string/`i128` oracle, all bit offsets,
raw cursors, inclusive endpoints, recovery, and owned-value cleanup. The ordinary
Cargo consumer checks dynamic bounds, signed/unsigned composition, references,
the complete API, and a non-`Copy`, non-`Clone` integer newtype. Both MIR modes
translate without a new workaround. The optional C check adds 138,240 cases
against `h_int_range` and `h_ch_range` using valid ordered bounds; Rust rejects
reversed configuration during construction rather than constructing C's empty
range parser.

## Byte sets

`ByteIn::new(bytes)` and `ByteNotIn::new(bytes)` correspond to C Hammer's `h_in`
and `h_not_in`. Each reads one byte and returns its `u8` value, accepting it when
it belongs to the configured set or lies outside it, respectively. Both reuse
`Verify` over `Byte`, consuming a contextual eight-bit field without implicit alignment.

```rust
use rusthammer::{ByteIn, ByteNotIn, Cursor, Parser};

const SEPARATOR: ByteIn = ByteIn::new(b",;:");
let content = ByteNotIn::new(b"\r\n");
assert!(SEPARATOR.accepts(b';'));
assert!(!content.accepts(b'\n'));
assert_eq!(SEPARATOR.parse(b";", Cursor::start()),
    Ok((Cursor { byte: 1, bit: 0 }, b';')));
assert_eq!(content.parse(b"x", Cursor::start()),
    Ok((Cursor { byte: 1, bit: 0 }, b'x')));
```

These are literal byte sets, with no regular-expression syntax: `b"0-9"` denotes
the three bytes `0`, `-`, and `9`. Use `b"0123456789"` or `IntRange` over `Byte`
for ASCII digits. Order and duplicates do not affect membership; embedded zeros,
all 256 byte values, and slices longer than 256 entries are valid.

Both parsers own a private 32-byte bitmap stored as `[u64; 4]`. Construction
scans the supplied slice once, setting the bit for each value; lookups use one
word and one bit mask, taking O(1) time independent of the slice length. No heap
allocation is needed. Constructors remain infallible `const fn`, so constant
grammars can build their bitmaps at compile time.

`accepts(byte)` is a `const` query for whether a decoded byte would pass the
parser's filter; for `ByteNotIn` it returns true for values outside the exclusion
set. Construction discards the original order and duplicates.
Neither parser has a lifetime parameter, and both can outlive or be
reused after changes to their construction slice. Both implement `Copy`/`Clone`;
copying a parser copies 32 bytes. Parse outputs remain owned `u8` values.

Decoding precedes membership testing. A decoded rejection is recoverable
`Mismatch`; invalid cursors and insufficient input keep `Byte`'s outcomes.
Even an empty inclusion set returns `NeedMore` for short partial input and
`UnexpectedEnd` for short final input. After decoding, empty inclusion rejects
every byte and empty exclusion accepts every byte.

The [byte-sets example](examples/byte_sets.rs) counts a delimited field without
library allocation. Native tests cover every singleton/value pair, independent
binary-string/set oracles at every bit offset and truncation, both input statuses,
raw cursors, bitmap size/ownership, acceptance queries, and composition. Lean
proves that construction sets exactly the listed bytes, lookup agrees with bit
membership, and all indexing, shifts, and loop arithmetic are in bounds. It also
proves queries, cloning, both parsing APIs, and exact consumption/output
properties. Both MIR modes and the separate Cargo consumer pass without a new
Aeneas workaround. The optional C check adds 147,456 cases
against `h_in` and `h_not_in`, including empty, full, duplicate, and long sets.

## Skipping and position

`SkipBits::new(bits)` corresponds to `h_skip`: it discards exactly that many bits
and returns `()`, with no implicit alignment or 64-bit field-width restriction.
Every `usize` count is valid, so its private configuration has an infallible
`const` constructor and a `const bits()` accessor. It reads no input bytes,
allocates nothing, and advances in constant time. Parsing validates the cursor
even for a zero count. Insufficient input returns `NeedMore` on partial input
and `UnexpectedEnd` on final input, with the usual retry/backtracking rules.

`Tell` corresponds to `h_tell` and returns the current `Cursor` without consuming
input. It succeeds immediately at every valid position in either input mode,
including the end of a partial buffer, and rejects invalid cursors with
`InvalidCursor`. `End` remains the operation that requires finality. Both new
parsers implement `Copy`/`Clone`; `Tell` is zero-sized and both outputs are owned.
Unbounded repetition rejects successful `Tell` or zero-bit skips with `NonProgress`.

```rust
use rusthammer::{Cursor, Parser, Right, SkipBits, Tell};

let parser = Right { first: SkipBits::new(81), second: Tell };
let end = Cursor { byte: 11, bit: 0 };
assert_eq!(parser.parse(&[0; 11], Cursor { byte: 0, bit: 7 }), Ok((end, end)));
```

Position reporting preserves byte-and-bit coordinates instead of forming an
absolute `usize` bit count; the [known C overflow issue](../plans/rusthammer.md#known-c-issue-absolute-bit-position-overflow)
records why this matters. A private advancement helper splits the count into
whole bytes and a bounded remainder, handles a bit carry, and checks the
remaining input before adding to the byte index. Its Lean contract uses
unbounded natural-number positions and covers every `usize` input length and
count without assuming that the absolute bit position fits in `usize`.

The [position example](examples/position.rs) parses a bit count, skips that many
bits, records the next field's cursor, and decodes an unaligned byte. Native
tests compare against independent `u128` position arithmetic, including virtual
lengths near `usize::MAX` without allocating input. They also cover both statuses,
all bit offsets, truncation, invalid cursors, zero counts, parser references,
dependent counts, lookahead, backtracking, and repetition. Both MIR modes and
the separate Cargo consumer translate and Lean type-check. The C comparison
adds 118,188 cases for `h_skip` and `h_tell` at
representable positions, including canonical end-of-input and large skip counts.

## Bytes and byte patterns

`Byte` corresponds to `h_uint8()`: it consumes an eight-bit field in the active order and returns
`u8`, including from an unaligned cursor. `BytePattern::new(pattern)` corresponds
to `h_token` / `h_literal` matching arbitrary byte sequences, including embedded
zeros and patterns longer than 64 bits. Every slice is a valid configuration, so
construction is infallible. Its field is private; `pattern()` exposes the slice.

```rust
use rusthammer::{Byte, BytePattern, Cursor, Parser, Seq};

let pattern = [0xab, 0xcd];
let parser = Seq { first: BytePattern::new(&pattern), second: Byte };
let (next, (matched, value)) = parser
    .parse(&[0x55, 0xe6, 0xa1, 0], Cursor { byte: 0, bit: 1 }).unwrap();
assert!(core::ptr::eq(matched, &pattern[..]));
assert_eq!(value, 0x42);
assert_eq!(next, Cursor { byte: 3, bit: 1 });
```

The output of `BytePattern<'pattern>` is `&'pattern [u8]`: it borrows the
configured pattern and can outlive both the input and the parser value.
An unaligned match cannot be represented by a borrowed input byte slice.
C Hammer copies the configured pattern; RustHammer borrows it without allocation.
Use `TakeAligned` when the output should borrow aligned input bytes. The
[bytes example](examples/bytes.rs) demonstrates these output lifetimes.
With `alloc`, `Repeat::exact(Byte, count)` collects decoded bytes as `Vec<u8>`
for `h_bytes`-style unaligned reads.

An empty pattern succeeds at the original cursor without reading or validating
it, like `Epsilon`. Nonempty patterns validate the cursor through `Byte`. Bytes
are compared in order: `BytePattern::new(b"ab")` rejects partial `b"x"` with
`Mismatch`, while partial `b"a"` yields `NeedMore`. Final `b"a"` yields
`UnexpectedEnd`. An incomplete *individual byte* is read before comparison,
so available conflicting bits can still yield `NeedMore`. The deferred
[eager bit-prefix rejection task](../plans/rusthammer.md#deferred-eager-literal-rejection)
also covers that case; numeric `Literal` behavior is unchanged.

Lean proofs cover both modes and the complete API, all raw cursors, empty
patterns, ordered comparison, exact consumption and bit contents, safe narrowing
to `u8`, and loop termination. Native tests check pattern slice identity, which
is not represented by Lean's value-based slice model. Independent pattern/input
lifetimes also pass the separate Cargo consumer extraction check. The private
matching helper avoids a documented [Aeneas loop-borrow limitation](probes/README.md#pattern-borrows-and-loops).

The optional direct-backend differential check compares acceptance, consumption,
and normalized outputs with C `h_uint8` and `h_token` over 10,561 cases. It includes
all bit offsets, truncations, mismatches, empty patterns, zeros, and 256-byte
patterns. With a C shared library built using `scons --no-tests` at the repository
root, run from `rusthammer/`:

```sh
python3 tools/compare_primitives.py --hammer-library ../build/opt/src/libhammer.so
```

This check needs GCC and compares complete input at valid starting cursors.
It does not assert equivalence of streaming interfaces or other C backends.
The tool also checks signed bit fields and all named fixed-width integer readers.
It also checks integer and byte ranges, byte sets, and skipping/position, for
577,065 cases in total:
10,561 byte/pattern, 27,724 signed-field, 134,896 fixed-width, 138,240 range,
147,456 byte-set, and 118,188 skip/position cases.
Unsigned results retain their full range, including `u64::MAX`, when normalized
for comparison. C `h_int_range` accepts `int64_t` endpoints even for unsigned
children and then casts them to `uint64_t` for comparison. The adapter encodes
unsigned endpoints modulo `2^64` to preserve that interpretation; Rust keeps
native typed endpoints throughout.

## Bit and byte order

`Order` has two independent settings: `BitOrder::{HighFirst, LowFirst}` controls
which end of each byte is consumed, and `ByteOrder::{Big, Little}` controls the
numeric significance of successive byte fragments. `Order::DEFAULT` is high
first and big. Each fragment keeps its ordinary numeric bit significance:
reading all eight bits of `0x96` yields `0x96` in every order. Reading three bits
first yields `4` in high-first order or `6` in low-first order.

Fields are split at physical byte boundaries. Big byte order puts earlier
fragments above later ones; little byte order puts them below. This also applies
to unaligned fields and widths that are not multiples of eight. `Bits`,
`SignedBits`, `Literal`, `Byte`, `I8`, byte patterns, and byte sets use the active
order. The named `Be*` readers pin big byte order while retaining bit direction.
`SkipBits`, `Tell`, `TakeAligned`, and `End` keep their position-based behavior.

`WithOrder { parser, order }` overrides order for its child and preserves
finality. A **change of bit direction requires aligned entry and successful
exit**. An unaligned boundary returns fatal `Unaligned`; an invalid cursor takes
precedence. No padding is inserted. Child errors and `NeedMore` propagate
unchanged. Byte-order-only changes and nested same-direction scopes can start
and finish within a byte without extra validation.

For example, finish the low-first byte before returning to the enclosing order:

```rust
use rusthammer::{BeU16, BitOrder, Bits, ByteOrder, Cursor, Order, Parser, Seq, WithOrder};

let parser = Seq {
    first: WithOrder {
        order: Order { bit: BitOrder::LowFirst, byte: ByteOrder::Little },
        parser: Seq { first: Bits::new(3).unwrap(), second: Bits::new(5).unwrap() },
    },
    second: BeU16,
};
assert_eq!(parser.parse(&[0x96, 0x12, 0x34], Cursor::start()),
    Ok((Cursor { byte: 3, bit: 0 }, ((6, 18), 0x1234))));
```

The [ordering example](examples/ordering.rs) also retries this grammar after
partial input. `parse()` and the public `read_bit()` / `read_bits()` helpers use
default order. For explicit order, use `parse_with(input, cursor, context)`.
`Cursor.bit` counts consumed bits; a saved partial-byte cursor must be resumed
with its original bit direction. The bare cursor does not store that direction.

The [ordering specification](lean/RustHammer/OrderSpec.lean) defines values by
physical fragments using unbounded arithmetic. Its
[mathematical lemmas](lean/RustHammer/OrderMath.lean) connect default order to the
previous binary-value specification. The [reader proofs](lean/RustHammer/OrderProofs.lean)
cover values, exact consumption, truncation, invalid cursors, termination, and
arithmetic bounds. [Parser contracts](lean/RustHammer/OrderParserProofs.lean)
cover all orders and finalities, and [scope contracts](lean/RustHammer/OrderScopeProofs.lean)
require child behavior only when the entry guard permits a call. Generic
composition, repetition, folding, and match contracts now accept the full
context; existing default-order application proofs still pass. The verification
command audits 25 ordering theorems for only standard Lean axioms.

Native tests use an independent physical-bit oracle and cover nested scopes,
lookahead, borrowing, and exactly-once cleanup of discarded outputs. Both MIR
stages and the separate Cargo consumer pass without a new extraction workaround.
To compare the library against C Hammer's direct backend, run:

```sh
python3 tools/compare_ordering.py --hammer-lib ../build/opt/src/libhammer.so
```

There are 107,364 agreements (101,060 fields and 6,304 nested grammars), plus
2,848 expected scope rejections, including 2,064 cases C accepts. Those rejections
are the intentional restriction on direction changes, documented in the
[input plan](../plans/rusthammer-input.md). The comparison uses complete input;
native tests and Lean contracts also cover partial input.

## Partial input and finality

`parser.parse(input, cursor)` retains the complete-buffer API and returns
`Result<(Cursor, Output), ParseError>`. Use `parser.parse_with(input, cursor, context)`
when more bytes might arrive:

```rust
pub enum InputStatus { Partial, Final }
pub struct ParseContext { pub order: Order, pub status: InputStatus }
pub enum ParseOutcome<T> {
    Success(Cursor, T),
    Error(ParseError),
    NeedMore,
}
```

`ParseContext::PARTIAL` and `ParseContext::FINAL` use the default numeric order.
For another order, construct `ParseContext { order, status }`.
`InputStatus::Partial` says the buffer may grow; `InputStatus::Final` says no more
bytes will be supplied for this parse. A parser can succeed on partial input as soon as its grammar is
satisfied. For example, a byte reader can return its byte while more bytes may
still arrive. `End` needs finality as well as an empty remaining buffer.

| Situation | Partial input | Final input |
| --- | --- | --- |
| A primitive needs unavailable bytes | `NeedMore` | `Error(UnexpectedEnd)` |
| `Choice("ab", "a")` on `"a"` | `NeedMore`; preserve the first branch's priority | Success on `"a"` |
| `Optional("ab")` on `"a"` | `NeedMore` | `None` at the original cursor |
| `Not("b")` on empty input | `NeedMore` | Success at the original cursor |
| `End` at the buffer boundary | `NeedMore` | Success |
| Invalid cursor or alignment | Error | Error |

Combinators pass the context to their children; `WithOrder` overrides order while
preserving finality. `NeedMore` propagates without
selecting alternatives, deciding absence, inverting lookahead, or invoking the
callback for that child. Final-input contracts prove that built-in compositions
return success or error, assuming their child and callback contracts.

This increment supplies the semantics needed for future streaming. Parsers do
not retain chunks or save execution state. On `NeedMore`, accumulate bytes in the
caller and retry with the **whole accumulated buffer and original cursor**. If
the source ends, retry with final status and the same order, even if no new bytes arrived. See the runnable
[input-status example](examples/input_status.rs).

A retry reparses the prefix and can rerun callbacks from previously successful
stages. Keep such callbacks pure or account for repeated effects. Successful
borrowed outputs refer to the buffer supplied to that call; Rust's borrowing
rules govern when that buffer can be changed. Saved continuations, efficient
chunk buffering, and output ownership across chunks remain future work.

`NeedMore` means the parser has not decided yet; it does not promise that some
extension will succeed, nor report a minimum byte count. Numeric literals read
the entire field before comparing, so even a conflicting short prefix can need
more input. The record similarly checks its constraints after reading the full
three-byte header.

Custom parser implementations now implement `parse_with` and must honor the
finality contract. The default `parse` calls it with `ParseContext::FINAL`; defensively, an
unexpected `NeedMore` from a custom parser becomes `UnexpectedEnd`. The built-in
proofs rule out that case rather than relying on this conversion. The free
`read_bit`, `read_bits`, and `take_aligned` library helpers remain complete-input
functions; use the corresponding parser's `parse_with` for partial input. The
`parse_flags`, `parse_marker`, and `parse_record` helpers are complete-input
functions in the shared example source.

## Grammar and execution

`Grammar<'input>` supplies the associated `Output` type. `Eval<'input, Backend>`
executes that grammar with `&mut Backend`, an input slice, cursor, and immutable
`ParseContext`. `Direct` is an empty backend; the library currently implements
only direct interpretation. Built-in combinators share one execution implementation
and pass the same backend through every child call, including lookahead,
repetition, and the parser produced by `Bind`.

`Parser<'input>` is a convenience trait implemented automatically for every
`Eval<'input, Direct>`. Existing `parser.parse(...)` and `parser.parse_with(...)`
calls keep their signatures and behavior. Custom implementations migrate from
`impl Parser` to separate `Grammar` and `Eval` implementations; custom overrides
of `parse` are no longer supported. An evaluator must call child `eval` methods,
since a convenience entry point creates a fresh direct execution.

A custom parser may implement `Eval<Direct>` only, or provide a generic evaluator
with explicit backend capabilities. A grammar is executable with a backend only
when its children support it. No fallback silently runs a child through `Direct`.
Construction needs only the grammar/output constraints, as in `IntRange::new`.
Outputs retain their own lifetimes and require neither `Clone` nor `Copy`.

Cursor rollback does not roll back backend bookkeeping. A future caching backend
must bind its state to an input and grammar session; passing backend state alone
does not supply memoization, rule identity, or left recursion. Compilation to
other parsing engines remains a separate capability over the structured grammar.

## Parser reuse and output selection

`&P` forwards `Grammar` and `Eval<Backend>` to the underlying parser. A grammar
can therefore borrow a parser or use it in several positions while retaining the
selected backend. The reference lifetime is independent of the input lifetime;
outputs can borrow the input after local grammar objects have gone out of scope.
The `Parser` convenience methods are supplied automatically for `Eval<Direct>`.

The primitive parsers (`Bit`, `Bits`, `Literal`, `End`, and `TakeAligned`) and the
example `Marker` and `RecordParser` implement `Clone` and `Copy`. Every combinator
derives these traits conditionally on its stored fields: `Seq<P, Q>` is `Copy`
when both children are `Copy`, and `Map<P, F>` also requires a `Copy` callback.
`Clone` works with children and callbacks that are clonable without being `Copy`.
The `Parser` trait itself requires neither trait, and parsed outputs remain
unrestricted. `Repeat<Bit>` is `Copy` even though its output is `Vec<bool>`;
copying its configuration does not create a vector.

For small grammars, this makes reuse by value convenient:

```rust
use rusthammer::{Bits, Cursor, Parser, Seq};

let field = Seq { first: Bits::new(3).unwrap(), second: Bits::new(5).unwrap() };
let pair = Seq { first: field, second: field };
assert_eq!(pair.parse(&[0x25, 0x67], Cursor::start()),
    Ok((Cursor { byte: 2, bit: 0 }, ((1, 5), (3, 7)))));
```

A copy duplicates the stored grammar configuration, so its cost grows with that
configuration's size. Explicit cloning calls the fields' `Clone` implementations
and can allocate when children or callbacks own data. References remain useful
for large grammars and non-clonable parsers. Copying a captured reference preserves
its shared target; it does not create independent state behind that reference.

| Combinator | Successful output | Consumption |
| --- | --- | --- |
| `Left { first, second }` | The first child's value. | Both children, in order. |
| `Right { first, second }` | The second child's value. | Both children, in order. |
| `Middle { left, parser, right }` | The middle child's value. | All three children, in order. |
| `Ignore { parser }` | `()` | The child's entire match. |

All attempted children must succeed, including those whose values are discarded.
An error or `NeedMore` stops the sequence immediately and propagates unchanged;
later children are skipped. Success reports the last child's cursor. Output
selection does not restore the cursor, and it delegates cursor validation to the
children, just as `Seq` does. Empty successes remain valid.

For example, parse a delimited borrowed payload and require exact end-of-input:

```rust
use rusthammer::{Cursor, End, Left, Literal, Middle, Parser, TakeAligned};

let payload = TakeAligned { count: 3 };
let delimited = Middle {
    left: Literal::new(8, u64::from(b'[')).unwrap(),
    parser: &payload,
    right: Literal::new(8, u64::from(b']')).unwrap(),
};
let complete = Left { first: &delimited, second: End };
assert_eq!(complete.parse(b"[abc]", Cursor::start()),
    Ok((Cursor { byte: 5, bit: 0 }, &b"abc"[..])));
```

On partial `"[abc"`, the missing closing delimiter causes `NeedMore`. On partial
`"[abc]"`, `delimited` succeeds, but `complete` waits for EOF confirmation. The
[selection example](examples/selection.rs) also demonstrates `Right`, `Ignore`,
and reusing the payload parser.

These helpers allocate no storage themselves and require no `Copy` or `Clone`
bound on parsers or outputs. `Left`, `Right`, and `Middle` reuse `Seq` through
shared references and project its tuple with pattern matching. `Ignore` replaces
the successful value with unit. No callbacks are needed for these projections.
The child still constructs its output: ignoring a `Repeat` still builds its
vector, and ignoring a `Map` still runs its callback. Use
`FoldRepeat::at_least(parser, 0, || (), |(), _| ())` to discard repeated outputs
without constructing a vector.

The counterparts are C Hammer's `h_left`, `h_right`, `h_middle`, and `h_ignore`.
Rust keeps `()` as an ordinary value in surrounding tuples; it does not remove a
tuple member as C removes an absent AST entry. Tests port the C selection examples
and cover unaligned consumption against a bit-string oracle, borrowed slice
identity, non-`Copy` outputs, cleanup on failure, exact call order and status,
short-circuiting at every child, and choice rollback after a discarded child fails.

## Matching and ordered choice

`Literal::new(width, value)` validates width first, then whether the expected value
fits that width. Impossible literals produce `ConfigError::InvalidLiteral`,
including any nonzero value at width zero. Width 64 supports every `u64` value.
The resulting parser returns the matching numeric value as `u64`, or
`ParseError::Mismatch` when a complete field differs.

`End` returns `()` at the exact end of **final** input without advancing the cursor.
At the boundary of partial input it returns `NeedMore`, awaiting EOF confirmation.
Remaining bits, including zero padding, produce `TrailingInput`. Invalid cursors
remain errors even for an empty input.

`Choice<P, Q>` requires both children to have the same output type. It returns
the first success, including an empty success. On a recoverable error, it runs
the second child with the original input and cursor and returns that child's
result unchanged. If both fail, the second error is returned; diagnostics are
not aggregated yet.

| Error category | Variants | Choice behavior |
| --- | --- | --- |
| Input rejection | `Mismatch`, `UnexpectedEnd`, `TrailingInput` | Try the second branch at the original cursor. |
| Cursor or alignment error | `InvalidCursor`, `Unaligned` | Propagate immediately. |
| Repetition execution error | `NonProgress`, `CountOverflow` | Propagate immediately. |

On final input, `UnexpectedEnd` can select another alternative. On partial input,
exhaustion is `NeedMore`, which propagates without trying the second branch.
Configuration errors use the separate `ConfigError` type and are handled during grammar construction.
Both children must be constructed successfully before assembling a `Choice`;
an unused parsing branch is still skipped when the first succeeds.
A later failure outside a successful choice does not revisit that choice.
The built-in parsers have no mutable semantic state; cursor backtracking does
not undo effects in custom parsers that use interior mutability.

The [marker example](examples/marker.rs) imports its grammar from
[`support/marker.rs`](examples/support/marker.rs), calls `Marker::new()` once, then passes
`&parser` to `parse_marker(input, cursor, &parser)` for each input buffer. The grammar
tries the 16-bit literal `0xcafe`, then the 8-bit literal `0xca`, followed by `End`.
Thus `[0xca]` succeeds after the
longer branch is truncated, `[0xca, 0xfe]` succeeds immediately, and extra input
is rejected. Tests also cover partial-consumption rollback, borrowed alternative
outputs, branch short-circuiting, error propagation, and every pair of expected
and actual byte values for literal matching.

## Match restrictions and exclusive alternatives

`ButNot`, `Difference`, and `Xor` correspond to C Hammer's `h_butnot`,
`h_difference`, and `h_xor`. All have public `first` and `second` children, run
attempted children from the same original cursor, and require no allocation.

| Operation | Success condition | Returned output and cursor |
| --- | --- | --- |
| `ButNot` | First succeeds; second rejects recoverably or consumes strictly fewer bits. | First child's. |
| `Difference` | First succeeds; second rejects recoverably or consumes no more bits. | First child's. |
| `Xor` | One child succeeds and the other rejects recoverably. | Successful child's. |

Equal-length successes therefore reject with `ButNot`, accept with `Difference`,
and reject with `Xor`. `Difference` follows Hammer's length comparison, not
ordinary language-set subtraction. The restriction parsers cannot be replaced
by `Not` followed by a sequence: they can accept when both children succeed.

```rust
use rusthammer::{ButNot, ByteIn, BytePattern, Cursor, Parser};

let digit_except_six = ButNot {
    first: ByteIn::new(b"0123456789"),
    second: BytePattern::new(b"6"),
};
assert_eq!(digit_except_six.parse(b"7", Cursor::start()),
    Ok((Cursor { byte: 1, bit: 0 }, b'7')));
assert!(digit_except_six.parse(b"6", Cursor::start()).is_err());
```

`ButNot` and `Difference` allow unrelated child output types; the second output
is discarded. `Xor` requires a common output type, as `Choice` does. The
[matches example](examples/matches.rs) uses `Map` to put a digit and a tagged
16-bit word into an application enum. Outputs need neither `Copy` nor `Clone`.
Each combinator implements those traits when its stored children do, and can
also be reused through a shared reference. Input and pattern borrows are preserved.

First-child rejection short-circuits `ButNot` and `Difference`. `Xor` runs the
second child after a first success or recoverable rejection; two recoverable
rejections return the second error, and two successes return `Mismatch`
regardless of their lengths. Any attempted child's fatal error or `NeedMore`
propagates immediately. In particular, `ButNot` or `Xor` of patterns `a` and `ab`
returns `NeedMore` on partial `a`, but accepts `a` on final input. Incompleteness
is not evidence that the other grammar rejects.

The two length restrictions share a private implementation. It orders byte and
bit endpoints directly, avoiding an absolute machine bit count or subtraction.
For normalized forward matches from a common start, Lean proves this is exactly
consumed-bit ordering. Discarded input still counts; lookahead consumes zero.
Cursor validation is delegated to children, as with `Choice`; custom parsers
must respect the cursor convention for that consumed-length interpretation.
Speculative effects in custom parsers or callbacks are not rolled back.

Native tests cover every combination of success, all error variants, and
`NeedMore`, including call order, original cursors, ownership/drop counts,
borrowing, bit-level lengths, empty matches, and machine-limit endpoints.
Both MIR stages and the separate Cargo consumer pass without a new workaround.
The optional C comparison checks 1,879,635 complete-input cases, including
literal/skip/lookahead children, discarded prefixes/suffixes, all bit offsets,
nonzero byte starts, truncation, and equal/unequal match lengths:

```sh
python3 tools/compare_matches.py --hammer-library ../build/opt/src/libhammer.so
```

It requires a built C shared library and GCC, like the primitive comparison.
Acceptance, consumption, and selected outputs agree on this corpus; it does
not establish streaming or backend equivalence. Rust-specific error categories,
incompleteness, and output types are checked separately by tests and proofs.

## Optionality and lookahead

These combinators each run their child once on the original input and cursor:

| Combinator | Child succeeds | Child rejects the input |
| --- | --- | --- |
| `Optional { parser }` | Return `Some(value)` at the child's next cursor. | Return `None` at the original cursor. |
| `And { parser }` | Return `()` at the original cursor. | Propagate the child's error. |
| `Not { parser }` | Return `Mismatch`. | Return `()` at the original cursor. |

Here input rejection means `Mismatch`, `UnexpectedEnd`, or `TrailingInput`.
All three propagate `InvalidCursor`, `Unaligned`, `NonProgress`, and `CountOverflow`,
including errors after the child has consumed a prefix. Optional absence and
successful lookahead restore the exact byte and bit cursor; they do not round to
a byte boundary.

`Optional<P>` produces `Option<P::Output>` without requiring the output to be
`Copy` or `Clone`. A child that succeeds without consuming input produces `Some`,
not `None`. `And` and `Not` discard the child value and produce `()` on success.
`And` takes a single parser; sequencing two parsers remains `Seq`.

The [lookahead example](examples/lookahead.rs) demonstrates these grammars:

- `Seq(And("ab"), "a")` accepts `"abc"` and leaves `"bc"`.
- `Seq("a", Not("b"))` accepts `"ac"` and leaves `"c"`, rejects `"ab"`, and
  accepts `"a"` at end-of-input.
- `Optional("ab")` returns `Some` after `"ab"`; on `"a"`, it returns `None`
  without consuming that prefix.

These examples use the complete-buffer `parse` API. With `parse_with(..., Partial)`,
a truncated prefix produces `NeedMore` in all three combinators, so it cannot
establish optional absence or negative lookahead.
Restoring a cursor also does not undo callback effects or interior mutation in
custom parsers. The verified core's child contracts must account for any such state.

The C counterparts are [`h_optional`](../src/parsers/optional.c),
[`h_and`](../src/parsers/and.c), and [`h_not`](../src/parsers/not.c). Rust uses
`None` for C's absent optional token and `()` for lookahead's absent AST. Native
regression tests port Hammer's optional-choice grammar and its `a+b` / `a++b`
disambiguation example. They also check partial rejection, unaligned bit cursors,
empty matches, borrowed and non-`Copy` values, and fatal-error propagation.
This is focused semantic coverage, not a complete backend differential suite.

## Collecting repetition (optional `alloc`)

`Repeat::exact(parser, count)`, `Repeat::new(parser, min, max)`, and
`Repeat::at_least(parser, min)` share one implementation. The experimental
`RepeatN` type has been removed. An unbounded minimum of zero corresponds to
Hammer's `h_many`; a minimum of one corresponds to `h_many1`.

Enable `features = ["alloc"]` on the RustHammer dependency, or pass
`--features alloc` to Cargo when working in this crate. `Repeat` produces
`Vec<P::Output>`, without requiring outputs to implement `Copy` or `Clone`:

```rust
use rusthammer::{Bits, Cursor, Parser, Repeat};

let fields = Repeat::exact(Bits::new(5).unwrap(), 3);
let (next, values) = fields.parse(&[0x0f, 0xca], Cursor::start()).unwrap();
assert_eq!(values, [1, 31, 5]);
assert_eq!(next, Cursor { byte: 1, bit: 7 });
```

The bounded constructor returns `Result<Repeat<P>, ConfigError>` and rejects
`min > max` with `InvalidBounds`. Both limits are inclusive and private. Exact
and unbounded construction are infallible because every `usize` count is valid.
Accessors expose `min() -> usize` and `max() -> Option<usize>`: `Some(limit)` for
finite repetition and `None` for unbounded repetition. `usize::MAX` remains a
valid finite count.

```rust
use rusthammer::{Cursor, Literal, Parser, Repeat};

let letters = Repeat::new(Literal::new(8, u64::from(b'a')).unwrap(), 1, 3).unwrap();
assert_eq!(letters.parse(b"aa!", Cursor::start()),
    Ok((Cursor { byte: 2, bit: 0 }, vec![97, 97])));

let many_letters = Repeat::at_least(Literal::new(8, u64::from(b'a')).unwrap(), 1);
assert_eq!(many_letters.max(), None);
assert_eq!(many_letters.parse(b"aaaa!", Cursor::start()),
    Ok((Cursor { byte: 4, bit: 0 }, vec![97, 97, 97, 97])));
```

| Child outcome or limit | Repetition behavior |
| --- | --- |
| Success below any finite maximum | Check progress if unbounded, check the count, retain the value, and continue. |
| Finite maximum reached | Succeed immediately, without attempting another child. |
| Recoverable rejection, minimum met | Succeed with the collected values and the cursor before the rejected attempt. |
| Recoverable rejection below the minimum | Propagate the error and discard the collected prefix. |
| Fatal error or `NeedMore` | Propagate it and discard the prefix, even if the minimum has been met. |

Thus `letters` above needs more input on partial `"aa"`, but can succeed on
partial `"aaa"` because the maximum has been reached. `End` can be added when the
grammar also requires confirmed EOF. Exact repetition has equal bounds, so every
attempted child error propagates, as before.

Unbounded repetition has no maximum at which to stop: it keeps trying until a
child rejects. For example, partial `"aaaa"` needs more input, while partial
`"aaaa!"` can succeed because `!` establishes the end of this repetition.

Finite repetition permits empty successes because the count bounds the calls.
A maximum of zero returns an empty vector at the original cursor without calling
the child or validating that cursor. Otherwise finite repetition leaves cursor
validation to the child, as before.

Unbounded repetition validates its initial cursor before calling the child. On
each child success, it applies these checks in order:

1. The returned cursor must be valid for the supplied input, or return fatal
   `InvalidCursor`.
2. It must strictly advance, or return fatal `NonProgress`. Both empty and backward
   successes are errors, even after the minimum has been met. Thus repeating an
   `Optional` parser indefinitely fails when that parser succeeds with absence.
3. Another retained value must fit in the `usize` count, or return fatal
   `CountOverflow` before incrementing or pushing. At `usize::MAX`, a rejected
   next attempt can still stop successfully; `NeedMore` still propagates.

Progress compares byte and bit offsets directly; Rust never forms a potentially
overflowing absolute bit index. The Lean proof uses mathematical bit positions.
Every retained success contributes one output, including `()`; C Hammer's absent
AST entries have no direct equivalent in this typed collection. Restoring a cursor
does not roll back callback effects.

Storage grows after successful iterations, with no reservation based on the
requested count. Thus even `usize::MAX` can promptly return an early child error
or `NeedMore`. Large successful counts still require corresponding work and
storage. `CountOverflow` checks the number of outputs; allocation follows `Vec`
behavior and allocation failure is not a `ParseError`. See the proof-model limits
below. The count alone does not impose a resource budget on children or their outputs.

The [repeat example](examples/repeat.rs) demonstrates crossing byte boundaries,
bounded and unbounded stopping, partial input, and a runtime count read from an
eight-bit field. That example uses explicit Rust control flow for the dependent
count; the [dependent example](examples/dependent.rs) uses the reusable `Bind`.
Tests cover bit values against a binary-string oracle, borrowed slice identity,
non-`Copy` values and drop behavior, private validated bounds, zero/huge counts,
empty/non-advancing successes, invalid returned cursors, count overflow, error and
`NeedMore` propagation, rollback, and EOF. They also port Hammer's exact-count
choice example, capped and unbounded zero-or-more and one-or-more examples, and
its 2,000-element repetition case. This is focused compatibility
coverage, not a full differential harness.

## Folding repetition (no `alloc` required)

`FoldRepeat<P, I, F>` uses the same private bounds and iteration driver as `Repeat`,
returning one accumulator instead of a vector. Its constructors are:

```rust,ignore
FoldRepeat::exact(parser, count, init, fold)
FoldRepeat::new(parser, min, max, init, fold) // Result<_, ConfigError>
FoldRepeat::at_least(parser, min, init, fold)
```

Bounds are private and validated, with the same `min()` and `max()` accessors.
`init: Fn() -> R` makes a fresh accumulator; `fold: Fn(R, P::Output) -> R` consumes
it and each accepted child output in order. No `Clone` or `Copy` bounds apply to
outputs or accumulators. Parser `Clone`/`Copy` depends only on its stored components.

```rust
use rusthammer::{Bits, Cursor, FoldRepeat, Parser};

let checksum = FoldRepeat::exact(Bits::new(8).unwrap(), 3,
    || 0u64, |sum, byte| sum ^ byte);
assert_eq!(checksum.parse(b"abc", Cursor::start()),
    Ok((Cursor { byte: 3, bit: 0 }, 0x60)));
```

Initialization runs once per parse, including a zero maximum, but after the
starting-cursor check for unbounded repetition. Each fold step runs only after
child success and the progress/count checks. Recoverable stopping returns the
accumulator and the cursor before the rejected attempt; fatal errors and
`NeedMore` discard it. Retrying initializes again and reparses the prefix.
Callbacks may have side effects that cursor rollback cannot undo. The driver
allocates no storage; child parsers and callbacks may still allocate or panic.
Their correctness and termination require separate contracts.

The [folding example](examples/fold_repeat.rs) counts matching bytes and computes
an XOR checksum with default features disabled. Native tests also cover empty
successes, invalid cursors, partial input, non-`Clone` outputs and accumulators,
destructors, and borrowed accumulator identity.

Generic folding, captured initialization, and borrowed child outputs folded into
an owned non-`Clone` accumulator translate through an ordinary Cargo dependency.
The [borrowed-accumulator probe](probes/README.md#folding-and-borrowed-accumulators)
records a callback that returns a borrowed slice and fails with Aeneas's
non-endable-abstraction error. That pattern works in native Rust; concrete
callback extraction still needs checking separately from the generic fold proof.

## Separated lists

`SepBy<P, S>` collects item outputs with `alloc`; `FoldSepBy<P, S, I, F>` folds
them without library allocation. Separator outputs are discarded. Both use
private validated bounds and the same `min()` / `max()` accessors as `Repeat`:

```rust,ignore
SepBy::exact(item, separator, count)
SepBy::new(item, separator, min, max) // Result<_, ConfigError>
SepBy::at_least(item, separator, min)
FoldSepBy::exact(item, separator, count, init, fold)
FoldSepBy::new(item, separator, min, max, init, fold) // Result<_, ConfigError>
FoldSepBy::at_least(item, separator, min, init, fold)
```

`SepBy::at_least(p, s, 0)` corresponds to Hammer's `h_sepBy(p, s)`, and minimum
one corresponds to `h_sepBy1`. Counts refer to items, including unit values.
The first attempt parses only an item. Later attempts parse a separator and an
item together; after the minimum, recoverable rejection at either stage restores
the cursor to before that whole attempt. A trailing separator remains unconsumed,
so composing with `End` rejects it. For example, parsing `"a,a,"` on final input
retains two items and stops before the final comma; on partial input it returns
`NeedMore`. Fatal errors and incompleteness always propagate.

A finite maximum stops without probing another separator. Zero invokes neither
parser; folding still initializes once. Finite empty successes are allowed.
Unbounded lists require the first item and each whole subsequent pair to advance
to a valid cursor. An empty first item is `NonProgress`; a later empty item is
allowed if its separator advances. Empty separators also work if items advance.
The same count-overflow and accumulator rules apply as for ordinary repetition.
No output or accumulator needs `Copy` or `Clone`.

All four repetition types share one private loop. Separated forms supply an item
parser for the first attempt and `Right(separator, item)` for following attempts,
using shared references. This reuses sequencing and output-selection semantics.
The [separated example](examples/separated.rs) runs with and without `alloc`.
Tests exhaust short strings over item, separator, and conflicting bytes against
an independent language oracle, port C Hammer's list examples, and cover bit
boundaries, rollback, callback counts, partial input, empty matches, borrowed
identity, and cleanup of owned items, separators, and accumulators.

## Value-dependent sequencing

`Bind { parser, then }` corresponds to Hammer's `h_bind`. The first parser
produces a value `A`; `then: Fn(A) -> Q` consumes it and constructs a parser `Q`.
That parser runs at the first parser's success cursor with the same input and
finality, and its output is the output of `Bind`. Both stages propagate errors
and `NeedMore` unchanged. The factory runs once after first-stage success and is
skipped on error or incompleteness.

```rust
use rusthammer::{Bind, Bits, Cursor, Parser, TakeAligned, TryMap};

let payload = Bind {
    parser: TryMap {
        parser: Bits::new(8).unwrap(),
        map: |length| usize::try_from(length),
    },
    then: |count| TakeAligned { count },
};
assert_eq!(payload.parse(b"\x03abc!", Cursor::start()),
    Ok((Cursor { byte: 4, bit: 0 }, &b"abc"[..])));
```

For a given input lifetime the factory returns one concrete parser type; values
change its configuration. Heterogeneous branches need a typed parser enum or
another explicit representation. Input-derived validation belongs in `TryMap`;
the checked result may be a count or an already constructed parser that `Bind`
then executes. Neither output nor the constructed parser needs `Clone` or `Copy`.
The combinator itself supports these traits when its stored components do.
It allocates no storage and saves no state between calls. Retrying can rerun the
factory, and cursor rollback does not undo callback effects.

The [dependent formats](examples/support/dependent.rs) check an eight-bit count
against a format limit of 64, then parse either borrowed aligned bytes or that
many four-bit elements. Both parse prefixes, so callers can retain trailing input;
zero counts finish immediately after the header, even on partial input. The byte
format checks alignment after count validation; the element format also supports
unaligned starts. The runnable example works without `alloc` for borrowed bytes;
element collection requires `alloc`.

Generic extraction and the separate Cargo consumer cover scalar factories,
borrowed first outputs used to construct owned parsers, copied children inside
constructed repetitions, and returning an existing parser by reference.
A factory returning a *new parser containing a captured reference*, such as
`|count| Repeat::exact(&element, count)`, hits the recorded Aeneas
non-endable-abstraction error. Copying the child into the returned parser passes
when that child is `Copy`. Native Rust supports both forms; no restriction was
added to `Bind`'s Rust API. The [regression probe](probes/README.md#bind-factories-containing-borrowed-parsers)
records this distinction; the callback investigation remains deferred.

## Empty and failing grammars

`Epsilon` succeeds with `()` at the supplied cursor. It neither reads input nor
validates the cursor, and succeeds on partial input, including an empty buffer.
Unlike `End`, it does not require end-of-input. A finite `Repeat` can retain its
unit values; an unbounded repetition returns `NonProgress` on its empty success.

`Fail::<T>::new()` always returns recoverable `Mismatch`, even on partial input or
with an invalid cursor. The output type is inferred from composition or supplied
explicitly; no value of `T` is constructed. `Fail<T>` is zero-sized, has an
infallible `const` constructor and `Default`, and implements `Copy` and `Clone`
without requiring either trait on `T`. Its private `PhantomData<T>` marker follows
`T`'s auto-trait restrictions (for example, `Send` and `Sync`).

These correspond to Hammer's `h_epsilon_p` and `h_nothing_p`. They have no
configuration invariants. Like other recoverable failures, `Fail` permits choice
to try the next alternative and optionality to return absence at the original cursor.

## Mapping and predicates

`Map { parser, map }` applies a statically dispatched `Fn(P::Output) -> O` after
the child succeeds. Its output type is `O`; consumption is unchanged. The `Flags`
example now uses `Map` to turn the sequence's nested tuple into a struct.

`TryMap { parser, map }` uses `Fn(P::Output) -> Result<O, E>` for a checked
conversion. `Ok(value)` retains the child's successful cursor; `Err(_)` discards
the conversion error and produces recoverable `Mismatch`. This applies even when
`E` is `ParseError`: a conversion error is a rejected value, not a child parser
error. An enclosing `Choice` can retry at its original cursor. For example:

```rust
use rusthammer::{Bits, Cursor, ParseError, Parser, TryMap};

let byte = TryMap { parser: Bits::new(9).unwrap(), map: u8::try_from };
assert_eq!(byte.parse(&[0x7f, 0x80], Cursor::start()),
    Ok((Cursor { byte: 1, bit: 1 }, 255)));
assert_eq!(byte.parse(&[0x80, 0x00], Cursor::start()), Err(ParseError::Mismatch));
```

`Verify { parser, predicate }` uses `Fn(&P::Output) -> bool`. Acceptance preserves
the child's value and next cursor. Rejection returns `Mismatch`, so an enclosing
`Choice` can retry at its original cursor. The callback borrows its argument;
the output need not be `Copy`. All three combinators invoke their callback once
after child success and propagate every child error and `NeedMore` without
invoking it. `Map` and `TryMap` move the child's value into the callback; inputs,
outputs, and conversion errors need neither `Copy` nor `Clone`. Callback effects
are not rolled back on rejection or retry.

The generic Lean theorems require callback contracts only for values that the
child can successfully return. `Fn` itself does not guarantee purity, termination,
or freedom from panics. Concrete callbacks must translate and satisfy those
contracts. Native tests also cover captured callbacks, non-`Copy` outputs,
borrowed outputs, and callback invocation behavior.

The [composition example](examples/composition.rs) demonstrates a checked enum
decoder, integer narrowing, and empty/failing grammars. A separate
[captured-callback probe](probes/try_map.rs) exercises the actual library source
through a fallible closure returning an owned, non-`Copy` record. It translates
and Lean type-checks with the pinned tools; the older borrowed-record callback
limitation remains separate and deferred.

## Bounded record example

The [record example](examples/record.rs) uses the grammar and format limit defined
in [`support/record.rs`](examples/support/record.rs). It constructs a reusable
`RecordParser` with `RecordParser::new()`, then calls
`parse_record(input, cursor, &parser)`.
The format is:

```text
3-bit version | 5-bit flags | 16-bit payload length | payload bytes
```

Fields are MSB-first and the record starts on a byte boundary. Version must be 1;
all five flag bits are allowed. The length is at most 1,024 bytes, including zero.
The parser returns `Record { version, flags, payload }`, where the numeric fields
are `u64` and the payload is a borrowed slice. It requires exact end-of-input after
the payload. A byte offset may select a record following an earlier prefix.

For `[0x25, 0, 3, 0xca, 0xfe, 0x01]`, the output has version 1, flags 5, the last
three bytes as its payload, and the next cursor at byte 6.

With final input, rejections occur in this order:

1. Invalid cursor: `InvalidCursor`.
2. Valid cursor inside a byte: `Unaligned`, without skipping padding.
3. Fewer than three header bytes: `UnexpectedEnd`.
4. Unsupported version or excessive declared length: `Mismatch`.
5. Fewer than the declared payload bytes: `UnexpectedEnd`.
6. Bytes remaining after the declared payload: `TrailingInput`.

With partial input, incomplete headers or payloads produce `NeedMore`. A full
valid record also returns `NeedMore` until the caller declares the buffer final.
Invalid cursors, unaligned starts, rejected full headers, and trailing input remain
errors. Tests retry valid records at every byte boundary, including empty and
maximum-length payloads and a nonzero starting offset.

The input's version and length are format constraints, so violations are parse
errors. The constructor validates the fixed field widths and returns `ConfigError`
only for configuration failure; its proof establishes that these constants succeed.
The payload length is checked before conversion to `usize` and before taking a slice.
The tests cover every valid length and flag combination, every oversized 16-bit
length, unsupported versions, truncation, alignment, trailing input, offsets,
and borrowed-payload identity.

The record uses `Verify` for header constraints and `Seq` for its fields and
payload/end check. Its final borrowed struct is constructed directly. A capturing
closure performing that construction hit an Aeneas extraction limitation; the
small [reproduction](probes/README.md) is retained for toolchain upgrades. This
does not establish that all callbacks returning borrowed values are unsupported.

## Check Rust and Lean together

With the matching Aeneas and Charon binaries built in `~/source/aeneas/`, run:

```sh
python3 tools/verify.py
```

For another checkout location:

```sh
python3 tools/verify.py --aeneas-dir /path/to/aeneas
```

This checks the extractor revisions, checks Rust formatting, runs Rust tests with
allocation disabled and enabled, regenerates Lean with `alloc` enabled, rejects admitted or opaque project
declarations, and runs `lake build`. The checked-in generated file is replaced
during verification; edit the Rust source rather than that file.
Extraction includes derived `Clone` methods and the standard library's
`Option::clone` implementation used by repetition bounds.

The library extraction also sets the private `rusthammer_verify` configuration
to include the shared [flags](examples/support/flags.rs),
[marker](examples/support/marker.rs), [record](examples/support/record.rs), and
[dependent-format](examples/support/dependent.rs) sources as private modules.
Examples and native tests compile those same sources against the ordinary
library. The formats are absent from normal library builds and add no public
API or Cargo feature. Their extraction roots include the constructors, parsing
helpers, and derived marker/record clone methods. Both MIR stages use these
roots, preserving application proof coverage alongside the core definitions.
The Lean application theorems retain their names and contracts; generated
application definitions live under their example-module namespaces.

The command also extracts the same library roots at the optimized MIR stage
available for dependency bodies and checks a
[separate Cargo consumer](probes/cross_crate/README.md). The consumer has native
tests in both allocation configurations; its extraction includes RustHammer's
implementation with `alloc` enabled. Both extra translations are checked for
admitted/opaque declarations and Lean type-checked. They stay under `target/`.
All 44 consumer entry points pass, including an evaluator that uses a local
mutable backend while returning a borrowed input slice.

The cross-crate investigation found that cleanup code can recheck an enum's tag
after a payload move, which the pinned Aeneas rejects. Five internal pattern
matches now move whole payloads before unpacking or discarding them to avoid
that code. This preserves the API and existing proofs. The
[minimal reproductions and explanation](probes/cross_crate/README.md#cause-of-the-original-failure)
record the constraint for future changes; the borrowed-record callback issue
remains separate and deferred.

Two example evaluators construct their zero-capture callbacks in nongeneric
helpers. This avoids a Lean type-inference failure in closures defined inside
lifetime/backend-generic methods. The [minimal probe and workaround](probes/README.md#closures-inside-lifetime-generic-evaluators)
record both forms at both MIR stages; this does not change their parser semantics.

The first Lean build downloads the pinned Aeneas proof library, its dependencies,
and available cached build artifacts. Subsequent builds reuse `lean/.lake/`.
The extraction tools use the local Aeneas checkout; the Lean dependency uses the
same pinned revision through Lake. The existing C build is independent.

| Tool | Pinned version |
| --- | --- |
| Rust | `nightly-2026-09-17` |
| Aeneas | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| Charon | `c8f15d7d658c86a95658f71ad99cddd4be002e04` |
| Lean | `v4.31.0` |

Cargo and Lake lockfiles record the dependency state. To check the current Lean
files without regenerating them, run `lake build` from `lean/`.

## Specifications and proof coverage

[Spec.lean](lean/RustHammer/Spec.lean) specifies bit values using natural-number
`testBit`, cursor advancement using natural arithmetic, and grammar composition
using relations on parse results. Payload contents are specified by list
`drop` and `take`; bounds use natural arithmetic so oversized requests are covered
without assuming their end position fits in `usize`.
[Proofs.lean](lean/RustHammer/Proofs.lean) proves the primitive readers;
[CompleteProofs.lean](lean/RustHammer/CompleteProofs.lean) preserves the complete
combinator contracts, and [FlagsProofs.lean](lean/RustHammer/FlagsProofs.lean) proves
the typed flag example. These relate the specifications to the
[generated implementation](lean/RustHammer/Rusthammer.lean).

The [direct views](lean/RustHammer/DirectState.lean) specialize extracted `Eval`
implementations to `Direct` and discard its empty state. Their
[equations](lean/RustHammer/DirectEquations.lean) are proved against the generated
code, and the convenience entry points are definitionally equal to these views.
The existing grammar contracts therefore still verify the actual Rust execution.
[Backend composition proofs](lean/RustHammer/BackendProofs.lean) also establish
state propagation through sequencing and choice for arbitrary backend types,
assuming the child evaluators satisfy their state-transition contracts. They
include retaining state from a rejected alternative while restoring its cursor.
The verification command audits these results and the direct adapters alongside
the ordering theorems; no project axioms or admitted obligations are introduced.

[BitsSpec.lean](lean/RustHammer/BitsSpec.lean) specifies numeric fields using
positional binary notation with unbounded natural numbers. Its
[proofs](lean/RustHammer/BitsProofs.lean) establish a decreasing loop measure,
an accumulator bound, exact consumption, and the complete input-error contract
for validated numeric parsers. Constructor proofs cover every configuration value.

[SignedBitsSpec.lean](lean/RustHammer/SignedBitsSpec.lean) defines two's-complement
values with unbounded mathematical integers. Its
[proofs](lean/RustHammer/SignedBitsProofs.lean) establish constructor validity,
safe sign extension, the exact signed range for each nonzero width, and total
parsing contracts for both statuses and the complete API. The decoder proof
reuses unsigned decoding's contents, consumption, and termination guarantees.
The new theorems' axiom audit lists only `propext`, `Classical.choice`, and
`Quot.sound`.

[IntegerSpec.lean](lean/RustHammer/IntegerSpec.lean) specifies fixed-width integer
values and exact consumption using the output type's bit width.
[IntegerProofs.lean](lean/RustHammer/IntegerProofs.lean) reuses the general field
proofs, proves each narrowing cast is lossless, and establishes total contracts
for both statuses and the complete API. The fixed settings need no caller-supplied
configuration invariant. The existing `Byte` reader also satisfies this unsigned
integer contract. Axiom audits of all new reader theorems list only `propext`,
`Classical.choice`, and `Quot.sound`.

[IntRangeSpec.lean](lean/RustHammer/IntRangeSpec.lean) defines inclusive membership
and constructor validity using an ordering relation. Its
[proofs](lean/RustHammer/IntRangeProofs.lean) connect construction, bound access,
cloning, and both parsing APIs to that contract, reusing `Verify`'s proofs. Generic
theorems take contracts for the child and the `Ord` comparison methods; native
comparison lemmas discharge those obligations for all eight primitive output
types. Specialized native-reader theorems cover arbitrary cursors, values,
endpoints, and input statuses. The axiom audit lists only `propext`,
`Classical.choice`, and `Quot.sound`.

[ByteSpec.lean](lean/RustHammer/ByteSpec.lean) specifies byte decoding and ordered
pattern matching over mathematical lists. Its [proofs](lean/RustHammer/ByteProofs.lean)
establish lossless narrowing, total parsing, exact consumption and bit contents,
termination by remaining pattern length, and exclusion of `NeedMore` on final
input. The constructor and accessor preserve the configured slice. An axiom
audit of the new parser theorems lists only `propext`, `Classical.choice`, and
`Quot.sound`; physical pointer identity is covered by native tests.

[ByteSetSpec.lean](lean/RustHammer/ByteSetSpec.lean) defines mathematical bitmap
membership and relates it to literal lists, with exclusion negating membership.
[ByteSetBitmapProofs.lean](lean/RustHammer/ByteSetBitmapProofs.lean) proves that
one update adds exactly one member and construction represents precisely the
processed prefix. The loop terminates by remaining slice length. Lookup proves
the word index below four and the shift below 64, then connects a one-bit mask
to mathematical membership.

[ByteSetProofs.lean](lean/RustHammer/ByteSetProofs.lean) proves the public
constructors, `accepts` queries, and cloning. It reuses `Byte` and `Verify` for
total parsing of every bitmap in both statuses and the complete API. The
constructor's `bitmapRepresents` relation connects those contracts to the
caller's literal list; it is a representation-correctness statement, not a
validity restriction on bitmaps. Success preserves the decoded value, consumes
exactly eight bits, and satisfies membership/exclusion. Lists with equal
membership have equivalent contracts regardless of order or duplicates.
The axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`.

[PositionSpec.lean](lean/RustHammer/PositionSpec.lean) specifies advancement using
mathematical bit positions and bounds, and position reporting as cursor identity
after validation. Its [proofs](lean/RustHammer/PositionProofs.lean) establish safe
arithmetic and casts for every input length, raw cursor, and count; constructor,
accessor, and clone contracts; both parsing interfaces; exact advancement; and
zero-count behavior. `Tell` never returns `NeedMore`, even on partial input.
An audit of all 14 public position theorems finds only `propext`,
`Classical.choice`, and `Quot.sound`.

[ControlSpec.lean](lean/RustHammer/ControlSpec.lean) defines literal matching,
ordered choice, optionality, lookahead, end-of-input, and the marker grammar. Its
[proofs](lean/RustHammer/ControlProofs.lean) reuse the numeric and sequencing
contracts. Generic optionality and lookahead theorems require only the child's
contract, for arbitrary output types; they cover every success and error case.
Additional lemmas establish unchanged cursors for absent optional values and
successful lookahead.

[MatchSpec.lean](lean/RustHammer/MatchSpec.lean) specifies the three match
operations using child-outcome relations and mathematical endpoint ordering.
[MatchProofs.lean](lean/RustHammer/MatchProofs.lean) proves generic contracts for
both input statuses, final-input exclusion of `NeedMore` under complete child
contracts, and the default complete API. Success properties identify the retained
child value and cursor. Short-circuit laws require no contract or termination
assumption for an uncalled second child. Endpoint ordering agrees with unbounded
consumed-bit lengths for normalized forward matches, without a machine-position
bound. All 22 public theorems were axiom-audited; they depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Native tests cover physical borrow identity
and destructors, which are outside these value-based contracts.

[SelectionSpec.lean](lean/RustHammer/SelectionSpec.lean) defines output selection
by composing the existing sequencing and mapping relations with tuple projections.
Its [proofs](lean/RustHammer/SelectionProofs.lean) establish reference forwarding
for both entry points and selection contracts for both input statuses, final input,
and the complete API. They reuse the generic sequencing proofs and require no
callback contract. Success lemmas expose every child's successful cursor and
value, including discarded delimiters, and show that `Ignore` preserves consumption.
Rust tests check ownership and destructor behavior; arbitrary user destructors are
outside the Lean model.

[CompositionSpec.lean](lean/RustHammer/CompositionSpec.lean) specifies empty and
failing grammars and checked conversion. Its
[proofs](lean/RustHammer/CompositionProofs.lean) cover both input statuses,
final-input exclusion of `NeedMore`, and the complete API. Empty and failing
grammars work for every raw cursor without validity assumptions. `TryMap` requires
a callback contract only for successful child outputs, preserves their cursor on
conversion success, and maps every conversion rejection to `Mismatch`. Separate
short-circuit lemmas need no assumptions about skipped callbacks.

[RecordSpec.lean](lean/RustHammer/RecordSpec.lean) specifies the record format
using natural-number field values, byte bounds, and list subsequences. Its
[proofs](lean/RustHammer/RecordProofs.lean) compose the numeric, sequencing,
predicate, payload, and end-of-input contracts. They also establish that the
bounded length converts to `usize` without truncation.

[PartialSpec.lean](lean/RustHammer/PartialSpec.lean) specifies the three outcomes,
primitive exhaustion, finality, and each combinator's control flow. Its
[proofs](lean/RustHammer/PartialProofs.lean) cover both input statuses and establish
short-circuiting on `NeedMore`. Final-input contracts use `Spec.completed`, which
excludes `NeedMore`; `complete_spec` connects them to the unchanged complete API.
[PartialRecordSpec.lean](lean/RustHammer/PartialRecordSpec.lean) and its
[proofs](lean/RustHammer/PartialRecordProofs.lean) cover the marker grammar and the
record's independent partial-input format contract. In particular, a valid record
awaits EOF confirmation, while definite format errors remain errors.

[RepeatSpec.lean](lean/RustHammer/RepeatSpec.lean) specifies an ordered chain of
child successes within inclusive bounds, with an optional maximum. Success before
a finite maximum requires a recoverably rejected next attempt; errors below the minimum, fatal errors, and
incompleteness propagate. The [finite proofs](lean/RustHammer/RepeatProofs.lean) establish
constructor validity, output bounds/order, cursor chaining, stopping/rollback,
and termination under child contracts. Termination uses remaining permitted
calls and needs no input-progress assumption. Equal bounds are proved equivalent
to the original exact-count specification, making its parsing theorem a
specialization of the bounded theorem. A zero-maximum theorem needs no child
contract at all. Complete-input specialization rules out `NeedMore`; numeric
and borrowed-payload specializations reuse the corresponding primitive proofs.

[RepeatSupport.lean](lean/RustHammer/RepeatSupport.lean) proves the private cursor,
progress, and count checks. [UnboundedRepeatProofs.lean](lean/RustHammer/UnboundedRepeatProofs.lean)
proves the unbounded contract, including runtime rejection of invalid or
non-advancing child cursors and count overflow. Its termination measure is the
number of remaining input bits, using natural numbers rather than machine
arithmetic. A child contract must establish termination of each attempt; it need
not assume valid or advancing successes, since the driver enforces those checks.
Each retained item consumes at least one bit. Initial cursor rejection needs no
child contract at all. Final-input, numeric, and borrowed-payload specializations
are also proved.

[IterationProofs.lean](lean/RustHammer/IterationProofs.lean) proves the shared
iteration driver with a storage invariant relating the accumulator to a logical
list of retained outputs. Attempt contracts may depend on the number of retained
items, allowing distinct first-item and separator/item behavior.
[RepeatDriverProofs.lean](lean/RustHammer/RepeatDriverProofs.lean) specializes it
to a constant child contract and proves equivalence with the existing repetition
specifications. `Repeat` specializes the storage invariant to vector contents;
[FoldRepeatProofs.lean](lean/RustHammer/FoldRepeatProofs.lean) specializes it to
an initializer and left-fold recurrence, defined in
[FoldRepeatSpec.lean](lean/RustHammer/FoldRepeatSpec.lean). Both use the same
list-based stopping and rollback specifications and termination arguments.
Fold step contracts are required only for reachable prefixes and child successes
that pass the count/progress checks. Fold constructor, accessor, exact-count,
zero-count, invalid-start, and complete-input contracts are included. The zero
case needs only the initializer contract; an invalid unbounded start needs no
callback or child contracts. `folds_function` identifies deterministic callback
contracts with mathematical `List.foldl`.

[SepBySpec.lean](lean/RustHammer/SepBySpec.lean) independently describes the
first item and subsequent separator/item pairs, including failures at either
stage. [SepByProofs.lean](lean/RustHammer/SepByProofs.lean) connects these contracts
to `Right` and the common driver for both collection and folding. The theorems
cover constructors, accessors, finite and unbounded parsing, both finalities,
and the complete API. [SepByProperties.lean](lean/RustHammer/SepByProperties.lean)
proves zero-cap and invalid-start short-circuiting, exact item counts, and the
consumption bound for advancing attempts. Fold contracts concern retained items
only; separator values never enter the recurrence.

[BindSpec.lean](lean/RustHammer/BindSpec.lean) specifies value-dependent sequencing.
[BindProofs.lean](lean/RustHammer/BindProofs.lean) proves both input modes, the
complete API, and first-stage short-circuiting without assumptions about skipped
callbacks or constructed parsers. Factory and second-parser contracts apply only
to reachable first-stage successes. [DependentSpec.lean](lean/RustHammer/DependentSpec.lean)
specifies the example count field by its positional binary value and format bound,
and the bodies by slice contents or ordered numeric fields.
[DependentProofs.lean](lean/RustHammer/DependentProofs.lean) proves the extracted
examples against those contracts for all inputs, raw cursors, and finalities,
including the checked cast. Success theorems establish exact payload contents
and length, element counts, and byte/bit consumption. Native tests check borrowed
identity and ownership cleanup, which are outside these functional specifications.

These are per-invocation proofs. A future buffering/resumption implementation
will need its own cross-chunk correctness and ownership arguments.

Rust field privacy does not make extracted Lean records intrinsically valid.
The specifications therefore state `validBits`, `validSignedBits`, `validLiteral`, `validRepeat`, `validFoldRepeat`,
`validSepBy`, `validFoldSepBy`,
`validMarker`, and `validRecordParser`
explicitly. Constructor theorems establish these invariants on success; parsing
theorems take them as hypotheses. This separates configuration validation from
per-input checks without assuming that an arbitrary Lean record came from a
Rust constructor. The marker constructor also proves the exact fixed grammar,
so its application contract is connected to construction.

`validIntRange` similarly records the constructor's ordered-bound invariant.
The range filtering proof does not need that assumption: membership uses only
comparisons, so it also specifies filtering for raw Lean records with reversed
bounds. The public Rust constructor still rejects those configurations.

The following original contracts use final input for parser methods; their
`*_with_spec` counterparts cover both statuses. Raw reader functions remain
complete-input operations.

| Theorem | Guarantee |
| --- | --- |
| `read_bit_success` | Every readable cursor returns the specified bit and next cursor, without a modeled execution failure. |
| `read_bit_failure` | Every cursor without a readable bit returns the specified invalid-cursor or end-of-input error. |
| `bit_spec` | Combines those cases into a total specification of the `Bit` parser for all inputs and raw cursors. |
| `byte_with_spec`, `byte_spec` | Eight-bit decoding as `u8`, including lossless narrowing, invalid cursors, and exhaustion in both modes. |
| `byte_set_new_spec`, `byte_in_new_spec`, `byte_not_in_new_spec` | Infallible construction terminates and creates a bitmap representing exactly the supplied literal set, including empty/duplicate sets. |
| `byte_set_contains_spec`, `byte_in_accepts_spec`, `byte_not_in_accepts_spec` | Bounded bitmap lookup and acceptance queries agree with mathematical membership/exclusion. |
| `byte_in_bitmap_with_spec`, `byte_not_in_bitmap_with_spec`, `byte_in_spec`, `byte_not_in_spec` | Total parsing for every bitmap preserves byte decoding and finality; `*_final_spec` excludes `NeedMore` on final input. |
| `byte_in_with_spec`, `byte_not_in_with_spec`, `byte_in_set_spec`, `byte_not_in_set_spec` | Construction's representation relation recovers the original literal-set contract in both APIs. |
| `byte_set_success`, `byte_set_membership_ext` | Success consumes exactly eight bits with the decoded member/nonmember value; lists with equal membership have equivalent contracts. |
| `advance_cursor_spec`, `advance_cursor_zero_spec` | Cursor arithmetic is total and agrees with unbounded positions for every machine length/count; zero counts validate and preserve the cursor. |
| `skip_bits_new_spec`, `skip_bits_bits_spec`, `skip_bits_clone_spec`, `tell_clone_spec` | Construction, access, and cloning preserve configuration without extra validity assumptions. |
| `skip_bits_with_spec`, `skip_bits_final_spec`, `skip_bits_spec`, `skip_bits_success` | Skips consume exactly the requested bits, with cursor-validation precedence and correct partial/final exhaustion. |
| `skip_bits_zero_with_spec`, `tell_with_spec`, `tell_spec`, `tell_never_need_more` | Zero skips and position reporting validate the cursor and succeed without consuming input at every valid position, regardless of finality. |
| `signed_bits_new_spec`, `signed_bits_new_valid`, `signed_bits_width_spec` | Construction rejects precisely widths above 64, establishes the private invariant, and preserves the width. |
| `sign_extend_spec`, `signed_value_bounds` | Sign extension equals mathematical two's-complement interpretation, all arithmetic/casts are in bounds, and nonempty fields have their specified signed range. |
| `signed_bits_with_spec`, `signed_bits_final_spec`, `signed_bits_spec` | Total signed decoding for every input/cursor and validated width, including zero width, truncation, and finality. |
| `be_u16_with_spec`, `be_u32_with_spec`, `be_u64_with_spec`, `byte_integer_with_spec` | Fixed-width unsigned decoding preserves values in native outputs and consumes exactly the output type's bit width, for every cursor and both statuses. |
| `i8_with_spec`, `be_i16_with_spec`, `be_i32_with_spec`, `be_i64_with_spec` | Fixed-width signed decoding and lossless narrowing, including signed minima, invalid cursors, and exhaustion. |
| `be_u16_spec`, `be_u32_spec`, `be_u64_spec`, `i8_spec`, `be_i16_spec`, `be_i32_spec`, `be_i64_spec` | Complete-input contracts; corresponding `*_final_spec` theorems exclude `NeedMore` on final input. |
| `int_range_new_spec`, `int_range_new_valid`, `int_range_lower_spec`, `int_range_upper_spec` | Construction validates ordered typed bounds without parsing and preserves immutable endpoint access. |
| `int_range_with_spec`, `int_range_final_spec`, `int_range_spec`, `int_range_success` | Inclusive filtering preserves the child's accepted value and cursor, returns `Mismatch` on rejected values, and propagates child errors and incompleteness. |
| `int_range_u64_comparisons`, `int_range_i64_comparisons` (and the narrower variants) | Native comparison models match mathematical ordering, including unsigned maxima and signed minima. |
| `byte_pattern_with_spec`, `byte_pattern_final_spec`, `byte_pattern_spec` | Total ordered pattern matching, empty-pattern identity, byte-wise error precedence, and final-input exclusion of `NeedMore`. |
| `byte_pattern_success` | Output equals the configured pattern; each byte matches eight input bits and total consumption is exactly eight times the pattern length. |
| `seq_spec` | Sequencing preserves arbitrary supplied child specifications, including error propagation. |
| `parser_ref_with_spec`, `parser_ref_spec` | Shared references forward evaluation and preserve the underlying parser's contracts for both direct convenience methods. |
| `left_with_spec`, `right_with_spec`, `middle_with_spec`, `ignore_with_spec` | Output selection preserves sequencing or child behavior for both input statuses and arbitrary output types. |
| `left_final_spec`, `right_final_spec`, `middle_final_spec`, `ignore_final_spec` | Final-input child contracts exclude `NeedMore` and give the complete selection relation. |
| `left_spec`, `right_spec`, `middle_spec`, `ignore_spec` | The default complete API satisfies the corresponding selection contract. |
| `left_success_children`, `right_success_children`, `middle_success_children`, `ignore_success_cursor` | Success requires all children, keeps the selected value, and preserves full consumption. |
| `map_spec`, `verify_spec` | Mapping and predicates preserve child contracts under callback contracts for successful child outputs. |
| `map_child_error`, `verify_child_error` | Child errors propagate without any correctness or termination assumption about the callback. |
| `epsilon_with_spec`, `epsilon_final_spec`, `epsilon_spec` | Empty success preserves every raw cursor in both modes and the complete API. |
| `fail_new_spec`, `fail_default_spec`, `fail_clone_spec` | Construction and cloning terminate for arbitrary output types without additional bounds. |
| `fail_with_spec`, `fail_final_spec`, `fail_spec` | The failing grammar always returns `Mismatch`, regardless of input, cursor, or finality. |
| `try_map_with_spec`, `try_map_final_spec`, `try_map_spec` | Checked mapping preserves child and callback contracts, returning `Mismatch` for conversion errors. |
| `try_map_child_error`, `try_map_need_more`, `try_map_success_child` | Errors and incompleteness skip the callback; success preserves the child's exact cursor. |
| `flags_spec` | The typed example implements the specified three-bit grammar for every input and cursor, including its error paths. |
| `take_aligned_success` | An aligned, in-bounds payload is exactly the requested subsequence, with the correct next cursor. |
| `take_aligned_invalid_cursor` | Invalid cursors produce `InvalidCursor` for every requested length. |
| `take_aligned_unaligned` | Valid positions inside a byte produce `Unaligned`, even for zero-length requests. |
| `take_aligned_truncated` | Aligned requests beyond the available input produce `UnexpectedEnd`, including lengths that would overflow an unchecked end calculation. |
| `take_aligned_spec`, `take_aligned_parser_spec` | The payload function and parser satisfy the total contract for every input, raw cursor, and count, without a modeled execution failure. |
| `bits_new_spec`, `literal_new_spec` | Construction preserves valid settings and returns the specified configuration error for every unsupported width or unrepresentable literal. |
| `bits_new_valid`, `literal_new_valid` | Successful constructor calls establish the invariants required by parsing proofs. |
| `bits_width_spec`, `literal_width_spec`, `literal_value_spec` | Read-only accessors return the stored settings. |
| `unsignedBits_lt_pow` | The mathematical value of an unsigned field fits in its specified number of bits. |
| `bits_loop_spec` | The numeric loop terminates, preserves cursor validity, computes the specified value, and safely rejects truncation without overflowing its accumulator. |
| `bits_spec`, `read_bits_spec` | Given valid configuration, the numeric parser and function satisfy their total contract for every input and raw cursor, including truncation and invalid cursors. |
| `read_bits_success` | Every valid field with sufficient input returns its binary value and consumes exactly the requested width. |
| `recoverable_spec` | The executable error classifier matches the specified set of recoverable errors. |
| `literal_spec` | Given valid configuration, literal matching satisfies its total contract, including input errors and mismatches. |
| `end_spec` | End-of-input accepts exactly the valid end cursor and consumes nothing. |
| `choice_spec` | Ordered choice preserves child specifications and retries only recoverable failures at the original cursor. |
| `choice_first_success`, `choice_first_fatal` | Success and fatal errors propagate without any termination or correctness assumption about the second child. |
| `but_not_with_spec`, `difference_with_spec`, `xor_with_spec` | Generic match restrictions and exclusive alternatives preserve child contracts, errors, and incompleteness in both statuses. |
| `but_not_final_spec`, `difference_final_spec`, `xor_final_spec` | Complete child contracts exclude `NeedMore` and establish the final-input relation. |
| `but_not_spec`, `difference_spec`, `xor_spec` | The default complete API satisfies the corresponding match contract. |
| `match_endpoint_order_bits`, `match_endpoint_order_consumption` | Endpoint ordering equals mathematical bit-position and consumed-length ordering for normalized forward matches. |
| `match_restriction_success`, `xor_success` | Success preserves the selected child value/cursor and has the specified other-child rejection or length relation. |
| `restrict_match_first_error`, `restrict_match_first_more`, `xor_first_fatal`, `xor_first_more` | Short-circuit paths make no assumptions about the uncalled second child. |
| `optional_spec`, `and_spec`, `not_spec` | Optionality and lookahead preserve arbitrary child contracts, with the specified outputs, consumption, and error categories. |
| `optional_absent_cursor`, `and_success_cursor`, `not_success_cursor` | Optional absence and successful lookahead preserve the exact starting cursor. |
| `marker_new_spec`, `marker_new_valid` | Marker construction always succeeds and establishes the exact intended grammar. |
| `marker_spec`, `marker_parser_spec` | Given that grammar invariant, the complete marker parser implements its specified ordered grammar for every input and raw cursor, including errors. |
| `record_new_spec`, `record_new_valid` | Construction always succeeds and establishes the record's fixed field widths. |
| `record_fields_decode`, `record_header_fields_spec` | Sequenced numeric fields implement the three-byte header and its positional values, including truncation. |
| `record_predicate_spec` | The executable predicate accepts exactly version 1 and lengths through 1,024 bytes. |
| `record_body_spec` | The payload helper returns the declared suffix with the original header values, or the specified truncation/trailing-input error. |
| `record_spec`, `record_parser_spec` | Given valid construction, the whole record satisfies its independent format and error contract for every input and raw cursor. |
| `record_success` | Every aligned record with the supported version, bounded declared length, and exact input length is accepted. |
| `classify_spec`, `bit_with_spec`, `bits_with_spec`, `literal_with_spec`, `take_aligned_with_spec`, `end_with_spec` | Primitive behavior for both input statuses, including incomplete fields and EOF confirmation. |
| `seq_with_spec`, `choice_with_spec`, `optional_with_spec`, `and_with_spec`, `not_with_spec`, `map_with_spec`, `verify_with_spec` | Compositional three-outcome semantics, with `NeedMore` propagation. |
| `choice_first_need_more`, `seq_first_need_more`, `map_need_more`, `verify_need_more` | Incompleteness skips the unused branch or callback without assumptions about it. |
| `marker_with_spec`, `record_header_with_spec`, `record_body_partial_spec`, `record_partial_spec` | Application contracts for partial input, with exact record errors and waiting for EOF. |
| `repeat_new_spec`, `repeat_new_valid`, `repeat_exact_spec`, `repeat_at_least_spec` | Constructors reject exactly inverted finite bounds and establish the private invariant; every exact count or unbounded minimum is valid. |
| `repeat_min_spec`, `repeat_max_spec` | Read-only accessors expose the validated limits. |
| `repeat_with_spec`, `repeat_final_spec`, `repeat_spec` | Bounded repetition satisfies its child-dependent contract in both modes, including recoverable stopping and the complete-input API. |
| `bounded_repeat_exact`, `repeat_exact_with_spec`, `repeat_exact_final_spec`, `repeat_exact_complete_spec` | Equal bounds give precisely the original exact-count specification and its parsing contracts. |
| `repeat_zero`, `repeat_first_error`, `repeat_first_need_more` | Zero maximum skips the child; a first propagated error or incomplete outcome needs no assumptions about later calls. |
| `repeat_success_bounds`, `repeat_exact_success_length`, `repetitions_advance` | Output lengths obey inclusive bounds (exactly the count when equal); fixed-width consumption adds across iterations. |
| `repeat_bits_with_spec`, `repeat_payloads_with_spec` | Numeric fields and borrowed payloads instantiate the generic repetition contract. |
| `repeat_cursor_valid_spec`, `repeat_start_spec`, `repeat_progress_spec` | Cursor validity and strict progress checks agree with mathematical bit positions, including invalid and backward cursors. |
| `repeat_next_count_success`, `repeat_next_count_overflow` | Increment succeeds exactly below `usize::MAX`; another retained output at the limit returns `CountOverflow`. |
| `repeat_unbounded_with_spec`, `repeat_unbounded_final_spec`, `repeat_unbounded_spec` | Unbounded repetition satisfies its contract and terminates under child contracts, covering both input statuses and the complete API. |
| `repeat_unbounded_invalid_cursor` | Invalid initial cursors skip the child entirely. |
| `advancing_repetitions_consumption`, `repeat_unbounded_success_properties` | Successful unbounded repetition meets its minimum and consumes at least one bit per retained value. |
| `repeat_unbounded_bits_with_spec`, `repeat_unbounded_payloads_with_spec` | Numeric and borrowed-payload contracts instantiate unbounded repetition. |
| `record_success_properties` | Successful format outcomes have version 1, flags below 32, a payload exactly as long as declared and at most 1,024 bytes, and a canonical end cursor. |

The payload contract gives cursor validity precedence over alignment, then input
bounds. An empty request at canonical end-of-input succeeds; a nonempty request
there produces `UnexpectedEnd`. The trait-level theorem can supply the payload
child's contract to `seq_spec`.

The proofs contain no admitted obligations or project-defined axioms. They use
the pinned Aeneas execution and standard-library models and Lean's proof checker;
they do not establish the correctness of the Rust compiler or translation tools,
or guarantees about physical resource exhaustion.

The pinned Aeneas `Vec` model abstracts allocation and represents contents as
a bounded list. The repetition proof discharges its element-count bound and the
loop's arithmetic obligations. It does not cover allocator failure, Rust's byte
capacity limits, or arbitrary user-defined destructor behavior. Native tests
exercise cleanup of collected values on early exit. Resource-failure handling
remains a separate future capability.

Aeneas models borrowed slices by their contents; pointer identity is checked by
the Rust tests. The full core has not been compared against C Hammer by a
differential test harness. The record is an example format, not a claim of
compatibility with an existing protocol or full C Hammer coverage. Its dependent
payload step still uses explicit Rust control flow. New dependent examples use
the verified `Bind` combinator.

## Next increments

Follow the [combinator API plan](../plans/rusthammer-combinators.md):

Basic composition is implemented and proved, including parser references,
output selection, empty/failing grammars, and checked mapping.

Collection and folding now support both ordinary and separated repetition with
shared count, stopping, and progress rules and proofs.

`Bind` and representative count-prefixed formats are also implemented and proved.
Named length/count convenience wrappers remain proposals; their core composition
is now available.

Fixed-width typed integer readers, inclusive ranges, byte sets, `SkipBits`,
`Tell`, `ButNot`, `Difference`, and `Xor` are implemented and proved, with
semantic and differential checks. Scoped ordering and its context interface are
also implemented and proved; see the [input plan](../plans/rusthammer-input.md).
The [backend execution boundary](../plans/rusthammer-backends.md) separates
`Grammar` output types from `Eval<Backend>`, with `Parser` providing direct parsing
entry points. Continue with `BitSpan`, `Recognize`, and `WithSpan` and their
physical-boundary and borrowed-view contracts. Memoization, cached-output ownership,
rule identities, and recursive grammar construction remain later work, guided by
representative protocol benchmarks. The private cache probe remains design evidence.
Design permutation separately.

Keep future application grammars in shared example/proof-support source. The
original `Flags`, `Marker`, and `Record` fixtures have been migrated out of the
public library while preserving their tests and proofs.

Before implementing streaming buffering and resumption, revisit the
[deferred eager literal rejection](../plans/rusthammer.md#deferred-eager-literal-rejection)
work, including its error precedence and proof updates.

After each production increment, run `python3 tools/verify.py`. Packrat and its
recursion support follow the backend plan above. Keep chunk buffering and
resumption, seeking, deferred effects, and other engines as separately specified
additions.

CI integration and further investigation of the recorded borrowed-callback
extraction limitation are deferred. Continue running verification locally.
