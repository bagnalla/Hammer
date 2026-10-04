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
- Reading one bit in most-significant-first order, including crossing into the
  next byte without implicit alignment.
- Unsigned numeric fields of 0 through 64 bits, producing `u64` values and
  supporting unaligned starts and byte-boundary crossing.
- `Byte` producing `u8` and `BytePattern` matching arbitrary borrowed patterns,
  both supporting unaligned starts without allocation.
- Private numeric and literal configuration, validated by fallible constructors.
- `Parser<'input>` with an associated `Output` type and explicit input finality.
- Separate `Success`, `Error`, and `NeedMore` outcomes, with a complete-buffer convenience API.
- `Seq<P, Q>`, which returns a typed pair and propagates child errors.
- `Bind<P, F>`, whose factory uses a parsed value to configure the next parser.
- Shared parser references and `Left`, `Right`, `Middle`, and `Ignore` for selecting outputs.
- `Clone` and `Copy` for parser values when their stored children and callbacks support them.
- `Map<P, F>` for typed output transformations, `TryMap<P, F>` for checked conversions,
  and `Verify<P, F>` for predicates.
- `Epsilon` for empty success and `Fail<T>` for definite rejection with a chosen output type.
- `Choice<P, Q>`, which tries ordered alternatives with the same output type.
- `Optional<P>` for optional typed values, and `And<P>` / `Not<P>` for lookahead.
- Exact, bounded, and unbounded `Repeat<P>` collecting typed outputs, with optional `alloc`.
- `FoldRepeat<P, I, F>` folding those same repetitions into an owned accumulator without library allocation.
- `SepBy<P, S>` and `FoldSepBy<P, S, I, F>` for separated lists, collecting or folding only item outputs.
- Numeric literal matching and an exact end-of-input check.
- A toy three-bit header parser returning a `Flags` struct.
- An explicitly aligned payload parser returning a borrowed `&'input [u8]`.
- A complete marker grammar accepting `CA FE` or `CA`, with no trailing input.
- A complete record with a constrained header and a bounded, borrowed payload
  whose length comes from the input.

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
cargo run --example bytes
cargo run --example marker
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

`Bits::new(width)` constructs an MSB-first unsigned reader, returning
`Result<Bits, ConfigError>`. Widths above 64 produce `ConfigError::InvalidWidth`
before any input is supplied. The resulting parser can be reused through
`parser.parse(input, cursor)` or `read_bits(input, cursor, &parser)`.
A zero-width field returns zero without consuming input, including at end-of-input;
an invalid cursor is still rejected. `Byte` reads the same eight bits as
`Bits::new(8)` and returns `u8`. Signed fields and configurable
byte or bit order remain future work.

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

## Bytes and byte patterns

`Byte` corresponds to `h_uint8()`: it consumes eight MSB-first bits and returns
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
python3 tools/compare_bytes.py --hammer-library ../build/opt/src/libhammer.so
```

This check needs GCC and compares complete input at valid starting cursors.
It does not assert equivalence of streaming interfaces or other C backends.

## Partial input and finality

`parser.parse(input, cursor)` retains the complete-buffer API and returns
`Result<(Cursor, Output), ParseError>`. Use `parser.parse_with(input, cursor, status)`
when more bytes might arrive:

```rust
pub enum InputStatus { Partial, Final }
pub enum ParseOutcome<T> {
    Success(Cursor, T),
    Error(ParseError),
    NeedMore,
}
```

`Partial` says the buffer may grow; `Final` says no more bytes will be supplied for
this parse. A parser can succeed on partial input as soon as its grammar is
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

All combinators pass the status to their children. `NeedMore` propagates without
selecting alternatives, deciding absence, inverting lookahead, or invoking the
callback for that child. Final-input contracts prove that built-in compositions
return success or error, assuming their child and callback contracts.

This increment supplies the semantics needed for future streaming. Parsers do
not retain chunks or save execution state. On `NeedMore`, accumulate bytes in the
caller and retry with the **whole accumulated buffer and original cursor**. If
the source ends, retry with `Final`, even if no new bytes arrived. See the runnable
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
finality contract. The default `parse` calls it with `Final`; defensively, an
unexpected `NeedMore` from a custom parser becomes `UnexpectedEnd`. The built-in
proofs rule out that case rather than relying on this conversion. The free
`read_bit`, `read_bits`, `take_aligned`, and `parse_*` helpers remain complete-input
functions; use the corresponding parser's `parse_with` for partial input.

## Parser reuse and output selection

`&P` implements `Parser<'input>` when `P` does, so a grammar can borrow an existing
parser or use the same parser in several positions. Both `parse_with` and `parse`
forward to the underlying parser, including a custom override of `parse`.
Combinators continue to call their children's `parse_with` method. The parser
reference's lifetime is independent of the input lifetime; selected outputs can
borrow the input after local grammar objects have gone out of scope.

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

The [marker example](examples/marker.rs) calls `Marker::new()` once, then passes
`&parser` to `parse_marker(input, cursor, &parser)` for each input buffer. The grammar
tries the 16-bit literal `0xcafe`, then the 8-bit literal `0xca`, followed by `End`.
Thus `[0xca]` succeeds after the
longer branch is truncated, `[0xca, 0xfe]` succeeds immediately, and extra input
is rejected. Tests also cover partial-consumption rollback, borrowed alternative
outputs, branch short-circuiting, error propagation, and every pair of expected
and actual byte values for literal matching.

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

The [record example](examples/record.rs) constructs a reusable `RecordParser` with
`RecordParser::new()`, then calls `parse_record(input, cursor, &parser)`.
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
to include [the dependent-format source](examples/support/dependent.rs) as a
private module. Examples and native tests compile that same source against the
ordinary library. These formats are absent from normal library builds and add
no public API or Cargo feature. This gives application proofs access to the same
generated core definitions without maintaining a second implementation.

The command also extracts the same library roots at the optimized MIR stage
available for dependency bodies and checks a
[separate Cargo consumer](probes/cross_crate/README.md). The consumer has native
tests in both allocation configurations; its extraction includes RustHammer's
implementation with `alloc` enabled. Both extra translations are checked for
admitted/opaque declarations and Lean type-checked. They stay under `target/`.

The cross-crate investigation found that cleanup code can recheck an enum's tag
after a payload move, which the pinned Aeneas rejects. Five internal pattern
matches now move whole payloads before unpacking or discarding them to avoid
that code. This preserves the API and existing proofs. The
[minimal reproductions and explanation](probes/cross_crate/README.md#cause-of-the-original-failure)
record the constraint for future changes; the borrowed-record callback issue
remains separate and deferred.

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

[BitsSpec.lean](lean/RustHammer/BitsSpec.lean) specifies numeric fields using
positional binary notation with unbounded natural numbers. Its
[proofs](lean/RustHammer/BitsProofs.lean) establish a decreasing loop measure,
an accumulator bound, exact consumption, and the complete input-error contract
for validated numeric parsers. Constructor proofs cover every configuration value.

[ByteSpec.lean](lean/RustHammer/ByteSpec.lean) specifies byte decoding and ordered
pattern matching over mathematical lists. Its [proofs](lean/RustHammer/ByteProofs.lean)
establish lossless narrowing, total parsing, exact consumption and bit contents,
termination by remaining pattern length, and exclusion of `NeedMore` on final
input. The constructor and accessor preserve the configured slice. An axiom
audit of the new parser theorems lists only `propext`, `Classical.choice`, and
`Quot.sound`; physical pointer identity is covered by native tests.

[ControlSpec.lean](lean/RustHammer/ControlSpec.lean) defines literal matching,
ordered choice, optionality, lookahead, end-of-input, and the marker grammar. Its
[proofs](lean/RustHammer/ControlProofs.lean) reuse the numeric and sequencing
contracts. Generic optionality and lookahead theorems require only the child's
contract, for arbitrary output types; they cover every success and error case.
Additional lemmas establish unchanged cursors for absent optional values and
successful lookahead.

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
The specifications therefore state `validBits`, `validLiteral`, `validRepeat`, `validFoldRepeat`,
`validSepBy`, `validFoldSepBy`,
`validMarker`, and `validRecordParser`
explicitly. Constructor theorems establish these invariants on success; parsing
theorems take them as hypotheses. This separates configuration validation from
per-input checks without assuming that an arbitrary Lean record came from a
Rust constructor. The marker constructor also proves the exact fixed grammar,
so its application contract is connected to construction.

The following original contracts use final input for parser methods; their
`*_with_spec` counterparts cover both statuses. Raw reader functions remain
complete-input operations.

| Theorem | Guarantee |
| --- | --- |
| `read_bit_success` | Every readable cursor returns the specified bit and next cursor, without a modeled execution failure. |
| `read_bit_failure` | Every cursor without a readable bit returns the specified invalid-cursor or end-of-input error. |
| `bit_spec` | Combines those cases into a total specification of the `Bit` parser for all inputs and raw cursors. |
| `byte_with_spec`, `byte_spec` | Eight-bit decoding as `u8`, including lossless narrowing, invalid cursors, and exhaustion in both modes. |
| `byte_pattern_with_spec`, `byte_pattern_final_spec`, `byte_pattern_spec` | Total ordered pattern matching, empty-pattern identity, byte-wise error precedence, and final-input exclusion of `NeedMore`. |
| `byte_pattern_success` | Output equals the configured pattern; each byte matches eight input bits and total consumption is exactly eight times the pattern length. |
| `seq_spec` | Sequencing preserves arbitrary supplied child specifications, including error propagation. |
| `parser_ref_with_spec`, `parser_ref_spec` | Shared references preserve the underlying parser's contracts for both methods, including custom complete-method overrides. |
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

Expand binary primitives and match restrictions, with semantic and differential
checks. Settle cursor/span and bit-order semantics before their affected APIs.

Keep application grammars in examples or proof fixtures as the API is organized;
the current exported demo types are also recorded for migration in the plan.

Before implementing streaming buffering and resumption, revisit the
[deferred eager literal rejection](../plans/rusthammer.md#deferred-eager-literal-rejection)
work, including its error precedence and proof updates.

After each increment, run `python3 tools/verify.py`. Keep recursion, chunk buffering and resumption,
seeking, deferred effects, memoization, and additional backends as separately
specified additions.

CI integration and further investigation of the recorded borrowed-callback
extraction limitation are deferred. Continue running verification locally.
