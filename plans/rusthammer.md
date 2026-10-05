# RustHammer design and verification plan

Status: verified prototype with typed ranges, native integer readers, signed fields, byte patterns, `Bind`, ordinary/separated collection and folding, parser references, and output selection, 2026-10-04.

RustHammer will be a Rust rewrite of Hammer whose parsers can be translated
through Charon and Aeneas and proved correct in Lean. It should preserve Hammer's
essential parsing capabilities while using appropriate Rust representations.
Ordinary parsers will produce typed Rust values.

The first application milestone is a small, fully specified and verified binary
parser built from reusable combinators. The bounded record prototype now meets
that goal. CI is deferred at the user's request. The
[combinator API plan](rusthammer-combinators.md) inventories the intended families,
their Hammer counterparts, and implementation order. Detailed compatibility work
and additional core combinators remain unfinished; the prototype is not a complete
replacement for C Hammer. Public features must have an intended role in the final
API, independent of implementation or proof milestones.

## Prototype checkpoint

An initial implementation now lives in [rusthammer/](../rusthammer/README.md).
It includes most-significant-first bit readers, unsigned and signed numeric fields, typed
sequencing, a three-bit header example, and an explicitly aligned borrowed-payload
parser. The verification command checks Rust tests, regenerates the Aeneas
translation, and checks Lean proofs with pinned tools.

The bit reader and header example have specifications covering all input and
cursor values, including error paths. Sequencing has a reusable compositional
theorem. Aligned payloads now have a total specification and proofs covering
contents, consumption, invalid cursors, unaligned positions, and insufficient
input for every requested length, including zero and lengths that would overflow
an unchecked end calculation. The payload theorem is available for both the
function and the parser trait implementation.

`Bits::new(width)` constructs a `u64` reader for widths from 0 through 64,
including unaligned and cross-byte fields. Unsupported widths are rejected during
construction. Given valid configuration, its total Lean parsing contract covers
positional binary values, normalized cursors, exact consumption, invalid cursors,
and truncation. The loop proof establishes termination and accumulator bounds.
Zero-width reads return zero without advancing a valid cursor. An 8-bit field
provides unaligned byte decoding as a numeric value. Native tests include
exhaustive two-byte inputs for 8-bit fields
at every bit offset and an independent binary-string oracle for all supported
widths on representative longer inputs.

`SignedBits::new(width)` now provides `i64` decoding for widths 0 through 64,
corresponding to C's `h_bits(width, true)`. It shares the unsigned reader's
validated width, unaligned decoding, cursor/error rules, and input-finality
handling. Zero width returns zero after validating the cursor. Private
configuration and a read-only accessor preserve the constructor invariant.

The Lean specification interprets nonempty fields as mathematical two's-complement
integers, and the proof establishes the exact signed range. The private
sign-extension helper uses bounded arithmetic even for the 64-bit minimum:
it avoids constructing `2^64`, negating `i64::MIN`, or relying on out-of-range
casts. Constructor, accessor, helper, and both parsing APIs are proved. Library
extraction at both MIR stages and the ordinary Cargo consumer pass without a new
tool workaround. Native tests use an independent string/`i128` oracle and cover
all widths and offsets, signed boundaries, raw cursor errors, and partial retries.
Direct-backend C comparisons add 27,724 signed-field cases. General signed bit
fields remain a permanent API alongside fixed-width typed readers.

`BeU16`, `BeU32`, `BeU64`, `I8`, `BeI16`, `BeI32`, and `BeI64` now return their
corresponding native Rust integer types; existing `Byte` supplies `u8`. They
correspond to C's `h_uint*` and `h_int*` under default ordering. The `Be` prefix
explicitly fixes big-endian interpretation. All read MSB-first at the supplied
cursor without implicit alignment. They are zero-sized `Copy`/`Clone` values
with fixed valid widths, so no fallible constructors are needed.

The readers reuse `Bits` and `SignedBits`, with a private macro sharing outcome
propagation. Lean proves exact native values, consumption, lossless narrowing,
and the full cursor/finality contract for both parsing APIs without a caller
configuration assumption. Native tests exhaust 8- and 16-bit patterns, check
larger boundaries against `from_be_bytes` at all bit offsets, and use an
independent string/`i128` oracle for cursors, truncation, and finality. Both MIR
stages and cross-crate extraction pass. C comparisons add 134,896 cases against
the named integer readers. No new Aeneas workaround is needed.

`IntRange::new(parser, lower, upper)` now supplies inclusive numeric restrictions
corresponding to `h_int_range` and, over `Byte`, `h_ch_range`. Bounds have the
child's output type; reversed bounds return `ConfigError::InvalidBounds` during
construction. Fields are private with immutable endpoint accessors. Parsing
delegates to `Verify`, preserving accepted values/cursors and child errors or
`NeedMore`, while rejected values produce recoverable `Mismatch`.

The implementation uses `Ord`, supports integer newtypes, and requires no copying
or cloning of child values or endpoints. Lean proves construction, accessors,
cloning under field contracts, and inclusive filtering in both APIs under child
and comparison contracts. Native scalar comparison lemmas and reader
specializations discharge the ordering obligations for all primitive outputs.
The ordered-bound invariant is explicit; the filtering proof also works for
raw Lean records without that invariant because it performs only comparisons.
Native tests cover constructor bounds, exact endpoints, signed/unsigned extremes,
all offsets, finality, composition, and cleanup. Both MIR stages and the normal
Cargo consumer pass, including a non-`Copy`, non-`Clone` newtype. C comparisons
add 138,240 valid-configuration range cases. The adapter preserves unsigned
endpoints despite C's signed bound parameters. No new Aeneas workaround is needed.

`ByteIn::new(bytes)` and `ByteNotIn::new(bytes)` now implement `h_in` / `h_not_in`
through `Verify` over `Byte`. They return `u8` and own private `[u64; 4]` bitmaps,
using 32 bytes per parser with no lifetime parameter. Infallible `const`
constructors scan a literal byte slice once; `const accepts(byte)` queries and
parse-time membership take O(1) time.
Every slice is valid, including empty, duplicate, full, and long sets, and parser
values are `Copy`/`Clone`. No allocation or regular-expression interpretation is
involved. The original slice is not retained, and order/duplicates are discarded.
Copying a parser copies its 32-byte bitmap.
Decoding precedes filtering, retaining cursor validation and `NeedMore`/end-of-input
precedence even for empty sets.

Lean proves construction by a processed-prefix invariant and lookup by bounded
word indexing and bit masking. It connects the bitmap to mathematical list
membership and proves acceptance queries, cloning, both parsing APIs, exact
consumption, decoded outputs, and equivalence for lists denoting the same set. Native tests
cover every singleton/value pair, independent set/binary-string oracles at all
bit offsets and truncations, both statuses, raw cursors, bitmap ownership after
the construction slice changes or is dropped, and composition.
Both MIR stages and all 35 consumer entry points pass without a new workaround.
C comparisons add 147,456 byte-set cases.

`SkipBits::new(bits)` and `Tell` are implemented and proved. Skips discard any
`usize` bit count in constant time without reading input bytes or allocating;
`Tell` returns the current byte-and-bit `Cursor` without consuming. Both validate
raw cursors, including zero-length skips; valid `Tell` and zero skips succeed in
either status, including canonical end-of-input. Nonempty exhaustion returns
`NeedMore` on partial input or `UnexpectedEnd` on final input. Skip configuration
is private, with infallible `const` construction and a `const bits()` accessor.
Both parsers are `Copy`/`Clone`, and their outputs have no borrows.

The private length-based advancement helper has a total Lean contract over all
`usize` lengths/counts, using unbounded mathematical bit positions. It proves
all additions, subtractions, divisions, and casts safe, including positions
whose absolute bit count would exceed `usize`. Native `u128` oracles exercise
virtual lengths near `usize::MAX` without allocating input. Tests also cover
truncation, raw cursors, both statuses, dependent counts, parser references,
lookahead, backtracking, and zero-consumption repetition. Both MIR stages and
all 35 consumer entries pass without a new workaround. C comparisons add
118,188 skip/position cases; the total primitive corpus is 577,065. The
[known C absolute-position overflow](#known-c-issue-absolute-bit-position-overflow)
remains a separate issue; differential checks use representable C positions.

`Byte` now reads eight bits as `u8`, with a proof that narrowing the numeric
result is lossless. `BytePattern::new(pattern)` matches arbitrary borrowed byte
sequences at aligned or unaligned positions and returns the configured pattern
slice. Input, pattern, and parser-reference lifetimes are independent. Every
slice is valid, so construction is infallible; the field is private with a
read-only accessor. Empty patterns succeed without cursor validation. Nonempty
patterns compare each fully decoded byte immediately and classify incomplete
bytes according to finality. Neither primitive needs allocation.

The byte-pattern loop terminates by the remaining pattern length. Total Lean
contracts cover all cursors and both statuses, error precedence, exact bit
consumption and contents, and the complete API. Rust tests check pointer identity
and output lifetimes, which the Lean slice model erases. Library extraction at
both MIR stages and the ordinary Cargo consumer pass. Returning the pattern
borrow through the loop itself exposed an Aeneas loop-context limitation; a
private matching helper returning unit keeps the returned borrow outside the
loop. The [probe notes](../rusthammer/probes/README.md#pattern-borrows-and-loops)
record the failing shape and supported implementation.

An optional [C/Rust differential check](../rusthammer/tools/compare_primitives.py)
passes 10,561 complete-input cases against direct-backend `h_uint8` and `h_token`,
normalizing ownership and typed output differences. It covers every bit offset,
truncation, mismatches, empty patterns, embedded zeros, and 256-byte patterns.
This is focused compatibility evidence, not an audit of all C backends.

Numeric `Literal`, ordered `Choice<P, Q>`, and exact `End` checks now have Lean
contracts and proofs. Choice requires matching child output types, retries input
rejection at the original cursor, and propagates fatal errors. It returns
the second result unchanged after a retry. Separate theorems cover first-branch
success and fatal errors without assumptions about the unused second branch.
The complete `CA FE` / `CA` marker example has a compositional grammar theorem.

`Bits` and `Literal` now have private configuration fields, read-only accessors,
and fallible constructors returning a separate `ConfigError`. `Literal::new`
validates the width before checking that the expected value fits. Lean proofs
establish explicit validity invariants on successful construction and use those
invariants in the parsing contracts. The reusable marker parser is constructed
once with `Marker::new()`; its constructor is proved to produce the intended grammar.

`Map<P, F>` and `Verify<P, F>` now have generic Lean contracts parameterized by
callback contracts on successful child outputs. Mapping preserves consumption;
predicate rejection returns recoverable `Mismatch`. Child errors skip the
callback entirely. The `Flags` example uses `Map` for its typed output.

`&P` now implements `Parser` by forwarding both `parse_with` and `parse`, including
custom overrides of the complete method. Shared parser references can be reused
throughout a grammar without cloning the parser, and their lifetimes are independent
of input borrowing. `Left`, `Right`, and `Middle` compose `Seq` over these references
and select the desired tuple component. `Ignore` replaces a successful output with
unit while preserving consumption. All children must succeed, including discarded
delimiters; errors and `NeedMore` skip later children and propagate unchanged.
No output needs `Copy` or `Clone`, and the helpers add no allocation or callback
requirements. Generic Lean contracts reuse sequencing for both input statuses and
the complete API; success lemmas preserve full consumption. Native tests cover
borrowed outputs outliving local grammar objects, exact-once drops, bit-cursor
rollback, and C's selection examples. The runnable
[selection example](../rusthammer/examples/selection.rs) parses a delimited payload
and uses `Left` with `End` to require complete consumption.

All parser structs now derive `Clone` and `Copy` when their stored fields support
those traits. `Bits` and `Literal` already supported them; the remaining primitives,
combinators, and fixed example parsers now do too. Parsed output types impose no
cloning or copying requirement, including for vector-producing repetition. Copies
duplicate configuration, and clones use each child's or callback's own `Clone`
implementation. Reference reuse remains supported for non-clonable parsers and
large grammars. Runnable documentation covers copied grammars returning non-clonable
values and copied repetition producing fresh vectors.

`Optional<P>`, `And<P>`, and `Not<P>` now have generic Lean contracts and proofs.
Optionality preserves successful outputs in `Some` and turns recoverable rejection
into `None` at the original cursor. Positive lookahead asserts child success;
negative lookahead asserts recoverable child rejection. Both produce `()` on
success without consuming input. Fatal errors always propagate.
Proofs and tests cover empty-success children and exact bit-cursor restoration;
native regression cases also port Hammer's optional-choice and lookahead examples.

The core now distinguishes incomplete input from rejection. `InputStatus::Partial`
marks a buffer that may grow; `Final` marks the end of input. `parse_with` returns
`Success`, `Error`, or `NeedMore`, while `parse` retains the complete-buffer
`Result` API. Every combinator propagates incompleteness before making a choice,
deciding optional absence, or inverting lookahead. `End` requires finality even
at an empty buffer boundary. Generic Lean proofs cover both modes; the existing
complete contracts and the record's partial-input format contract are proved.
Chunk buffering, saved continuations, and cross-chunk output ownership are still
deferred. Callers can accumulate bytes and retry from the original cursor.

`Repeat<P>` now collects typed outputs in `Vec<P::Output>`, behind opt-in `alloc`,
using one implementation for `Repeat::exact(parser, count)`,
`Repeat::new(parser, min, max)`, and `Repeat::at_least(parser, min)`. The experimental
`RepeatN` type has been removed. Exact and unbounded construction are infallible;
bounded construction rejects `min > max` with `ConfigError::InvalidBounds`.
Private fields preserve this invariant. Read-only
`min()` and `max()` accessors expose the limits; `max()` returns `Some(limit)` for
finite repetition and `None` for unbounded repetition. `usize::MAX` remains a
valid finite bound. Unbounded minima zero and one correspond to `h_many` and `h_many1`.
Default features remain empty and the library remains `no_std`.

Repetition stops at a finite maximum without probing again. Recoverable rejection
after meeting the minimum succeeds with the preceding values and cursor; earlier
rejection, fatal errors, and `NeedMore` propagate after discarding the prefix.
A zero maximum invokes no child and preserves the supplied cursor without
validation. Finite repetition supports empty-success children because the maximum
bounds the calls. Unbounded repetition validates its initial cursor before calling
the child. It rejects invalid returned cursors with `InvalidCursor`, then empty or
backward successes with `NonProgress`, then another retained value at `usize::MAX`
with `CountOverflow`. All three errors are fatal. Progress uses direct byte/bit
comparisons without computing a machine-sized absolute bit index. Outputs need
neither `Copy` nor `Clone`, and unit values are retained. The
[repetition design](rusthammer-combinators.md#one-repetition-design) records these
rules shared by folding and separated lists too.

Aeneas extraction and Lean checking cover constructors, accessors, and the shared
collection loop. Generic theorems prove count bounds, ordered values, cursor
chaining, stopping/rollback, failure propagation, and termination. The finite
measure is remaining permitted calls; the unbounded measure is remaining input
bits in mathematical natural numbers. Runtime progress checks are proved, so the
unbounded theorem needs no assumption that successful children advance or return
valid cursors. Each child attempt must still satisfy its termination contract.
Equal bounds are proved equivalent to the original exact-count contract, and exact parsing is
a specialization. Native tests cover both feature configurations, independent bit
oracles, borrowed/non-`Copy` values, cleanup, invalid/non-advancing cursors, count
overflow, and C exact/capped/unbounded repetition cases.
The minimized exact-count collection probe remains as compatibility evidence.
Allocation grows with successes, not the configured count. Proofs use Aeneas's
`Vec` model, which abstracts allocation and byte capacity; allocation failure and
resource budgets remain outside this increment.

`FoldRepeat<P, I, F>` now offers `exact(parser, count, init, fold)`,
`new(parser, min, max, init, fold)`, and `at_least(parser, min, init, fold)` in the
allocation-free core. `I: Fn() -> R` initializes each parse; `F: Fn(R, A) -> R`
moves the accumulator and each accepted output, requiring neither to be cloned.
The repetition combinators share private validated bounds, the iteration driver,
and a list-based Lean stopping specification. Generic driver proofs carry a
storage invariant; collection instantiates vector contents and folding instantiates
an initializer/left-fold recurrence. Constructor, accessor, both input modes,
complete-input, exact-count, and callback short-circuit contracts are proved.
Initialization follows the unbounded initial-cursor check and still runs for a
zero maximum. The step follows successful-child progress/count checks. Failure or
`NeedMore` discards the accumulator; retrying initializes and parses again.

The driver extracts at promoted and optimized MIR. A Cargo consumer checks
captured initializers, borrowed child values, and owned non-`Clone` accumulators;
these examples translate and Lean type-check. A callback returning a borrowed
accumulator reproduces the deferred non-endable-abstraction failure, now recorded
in `rusthammer/probes/fold_borrowed_accumulator.rs`. Native Rust supports that
pattern. No tool patch or extra public policy type was needed. A counting/checksum
example runs with default features disabled.

`SepBy<P, S>` and `FoldSepBy<P, S, I, F>` now add separated lists with the same
`exact`, fallible `new`, and `at_least` count policy. `SepBy` needs `alloc`;
`FoldSepBy` does not. Minima zero and one correspond to C's `h_sepBy` and
`h_sepBy1`. The first attempt parses only an item; later attempts use
`Right(separator, item)` over shared references. The shared driver rolls back
the whole rejected pair, leaving a trailing separator unconsumed, and propagates
fatal errors and `NeedMore`. Finite caps probe no further separator. Unbounded
progress applies to the first item and then each whole pair; a later empty item
is permitted if the separator advances. Only item values are collected or folded.

The generalized loop has an indexed attempt contract and one storage invariant;
ordinary repetition is proved equivalent to its existing constant-child
specification. Separated-list proofs cover constructors, bounds, both input modes,
finite/unbounded stopping, rollback, exact counts, zero caps, invalid starts,
and termination. Native tests include an independent exhaustive short-string
oracle, C list examples, bit boundaries, empty matches, and ownership cleanup.
Both MIR modes and the Cargo consumer translate and Lean type-check, including
borrowed item/separator values and owned folding. No new tool limitation appeared;
the previously recorded borrowed-callback investigation remains deferred.

The first application parser is a byte-aligned record with a 3-bit version, 5-bit
flags, 16-bit payload length, and a borrowed payload. It accepts version 1, all
five flag bits, and lengths through 1,024 bytes, then requires exact end-of-input.
Its constructor establishes fixed field widths. An independent Lean format
specification and compositional proofs cover decoded values, payload contents,
exact consumption, the bounded integer conversion, and every input/cursor error.
Its dependent payload step still uses explicit Rust control flow. The core now
also provides a verified `Bind` combinator for reusable value-dependent sequencing.

`Bind { parser, then }` moves a first-stage output into an `Fn(A) -> Q` factory,
then runs the returned parser at the success cursor with the same finality.
The returned parser's output becomes the result. First-stage errors and
`NeedMore` skip the factory; second-stage outcomes propagate. Generic proofs
cover both input modes and the complete API, with contracts required only for
reachable callbacks and constructed parsers. No cloning or allocation is required.

New application fixtures decode an eight-bit count capped at 64 and use `Bind`
to read borrowed bytes or collect four-bit elements. Their source lives under
`examples/support/`, shared by native tests, runnable examples, and a private
`rusthammer_verify` extraction module. These formats add no public API or Cargo
feature. Independent format specifications and Lean proofs cover every input,
raw cursor, and finality, plus exact payload contents/length, element count, and
byte/bit consumption. Native tests use independent bit-string and slice oracles
and cover callback skipping, retries, borrowed identity, and ownership cleanup.

The generic combinator, factories constructing owned parsers from borrowed
values, copied children inside constructed parsers, and factories returning an
existing parser by reference all extract. A factory returning a new parser
containing a captured reference reproduces the recorded non-endable-abstraction
error. `Repeat::exact(element, count)` passes for a `Copy` element where
`Repeat::exact(&element, count)` fails extraction. Both work in native Rust;
the [probe notes](../rusthammer/probes/README.md#bind-factories-containing-borrowed-parsers)
record this boundary. The callback investigation remains deferred.

A capturing closure constructing the borrowed record failed extraction in the
pinned Aeneas revision. Direct struct construction extracts and is proved.
A minimized [compatibility probe](../rusthammer/probes/README.md) preserves the
failing shape for toolchain upgrades; this is not a finding that all callbacks
returning borrowed values are unsupported.

The initial combinator inventory and proposed contracts are in the companion API
plan. Empty/failing parsers, checked mapping, folding, separated lists, and `Bind`
are implemented and proved, including representative dependent grammars. `Byte`
and `BytePattern` expand the binary primitives, and signed fields are implemented
and proved, including fixed-width readers with native Rust integer outputs.
Inclusive typed ranges, byte sets, skipping, and position reporting are also
implemented and proved. Next add match restrictions from the API plan, with further
semantic/differential checks.
CI integration and the
recorded Aeneas callback investigation are deferred. Configurable byte and bit
order remains unimplemented.

## Requirements and working decisions

The established requirements are:

- Preserve Hammer's essential design principles and distinguish them from its C
  implementation mechanisms.
- Support correctness proofs of RustHammer parsers using Aeneas and Lean.
- Produce typed Rust values from ordinary parsers.
- Keep the core `no_std`, with opt-in `alloc` support for collected repetition outputs.
- Validate constrained parser configuration through fallible constructors and
  protect its invariants with private fields.
- Give every public feature an intended place in the final API. Implementation
  and proof stages must not introduce temporary public combinators.
- Use the local Hammer, Aeneas, and nom checkouts to inform the design.

The following are proposed choices to validate during implementation:

- Use static dispatch and concrete combinator types for ordinary Rust grammars.
- Keep grammar structure available for analysis and compilation where supported.
- Use ordered choice with explicit finality and a distinct incomplete-input outcome.
- Preserve complete-buffer parsing while deferring buffering and saved continuations.
- Pass the input slice separately from a cursor that contains no references.
- Keep the core semantically pure, with explicit input and semantic state.
- Prove primitives and combinators compositionally against independent Lean
  specifications.
- Stage implementation and proofs within the intended API; keep experiments and
  application-specific proof fixtures outside the general-purpose public API.

Exact Rust API syntax, crate organization, release scope, and compatibility
guarantees remain open. Source compatibility with the C API and preservation of
every historical behavior are not established requirements.

## What to preserve and what to replace

| Aspect | Design direction |
| --- | --- |
| Declarative, compositional grammars | Preserve reusable grammar construction through primitives and combinators. |
| Bit-oriented parsing | Preserve fields crossing byte boundaries and byte parsers operating at unaligned positions. Specify byte order and bit order independently. |
| Sequence, choice, lookahead, repetition, and restrictions | Preserve expressive power and document exact success, failure, value, and consumption semantics. |
| Data-dependent parsing | Preserve length-dependent parsing, predicates, mapping, and sequencing based on earlier values. Prefer explicit values over hidden mutable environments. |
| Recursive grammars | Preserve as a capability. Distinguish ordinary recursion, runtime grammar graphs, and left-recursive parsing. |
| Multiple parsing backends | Preserve the architectural possibility, with explicit supported grammar classes and semantic conditions. |
| Parse-local state and reentrancy | Preserve through ownership, immutable parser descriptions, and explicit per-parse state. |
| Vtables, function-pointer environments, and variadic APIs | Replace with generic structs, traits, typed fields, tuples, and enums where appropriate. |
| Uniform dynamically tagged AST | Make optional. Use tuples, enums, structs, options, collections, and borrowed views for ordinary outputs. |
| Arenas, memoization, and runtime graphs | Evaluate individually. These solve real allocation, performance, and grammar-representation problems and are not inherently C-specific. |
| Manual graph ownership and cleanup | Replace with Rust ownership where possible; choose an explicit ownership scheme for shared or recursive graphs. |
| Streaming, seeking, diagnostics, and floating-point fields | Record as capabilities with explicit scope and milestones; do not discard them as C implementation details. |

Hammer's [parser vtable](../src/internal.h) includes grammar classification,
desugaring, and compilation as well as parsing. Replacing only the parsing
operation would lose part of the current architecture. The
[public API](../src/hammer.h), [parser implementations](../src/parsers/), and
[tests](../tests/) are the starting points for a semantic inventory.

For each public primitive and combinator, that inventory should record:

- Accepted and rejected inputs, including empty and truncated inputs.
- Decoded values, consumed bits, and remaining input.
- Backtracking, lookahead, and semantic-state behavior.
- Behavior on complete buffers and nonfinal input chunks.
- Backend restrictions and differences.
- Proposed Rust representation and proof obligations.
- Whether a difference is intentional, unresolved, or a defect to investigate.

C tests provide examples and differential checks. They do not automatically
resolve discrepancies between implementation behavior and intended semantics.

## Parsing interface

The current experimental interface is:

```rust
pub trait Parser<'input> {
    type Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        status: InputStatus,
    ) -> ParseOutcome<Self::Output>;

    // The default implementation invokes parse_with with InputStatus::Final.
    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError>;
}
```

This summarizes the experimental interface; the implementation supplies the
default `parse` body. `Cursor` contains byte and bit offsets, `ParseError` describes
rejection, and `ParseOutcome` separately represents incomplete input. The full
bit-cursor interface now extracts and its implementations have Lean proofs.

### Output type and input lifetime

An associated `Output` expresses that a concrete parser type, for a given input
lifetime, determines its output type. It keeps composition direct:

| Combinator | Output |
| --- | --- |
| `Seq<P, Q>` | `(P::Output, Q::Output)` |
| `Bind<P, F>` | The output of the parser constructed from `P::Output` |
| `Repeat<P>` | `Vec<P::Output>` with the optional `alloc` feature |
| `FoldRepeat<P, I, F>` | The accumulator type, without requiring allocation |
| `SepBy<P, S>` | `Vec<P::Output>` with `alloc`; separator outputs are discarded |
| `FoldSepBy<P, S, I, F>` | An accumulator over item outputs, without library allocation |
| `Optional<P>` | `Option<P::Output>` |
| `Map<P, F>` | The result type of the mapping function |
| `Choice<P, Q>` | A common output type, or an explicit enum distinguishing branches |

The lifetime permits outputs that borrow from the input. It does not imply that
every output contains a reference. For example, with parsing methods omitted:

```rust
impl<'input> Parser<'input> for BeU16 {
    type Output = u16;
}

impl<'input> Parser<'input> for TakeBytes {
    type Output = &'input [u8];
}
```

`BeU16` always produces `u16`, which can outlive the input buffer. `TakeBytes`
produces a slice whose lifetime is tied to the input reference. The trait
parameter describes a borrow relationship for a parse invocation; it does not
require the parser object to own or retain that input.

An output type parameter would instead permit the same parser type to implement
several output interpretations. That may be useful for a future interpretation
or AST-building interface, but is not the proposed default. Both designs support
static dispatch.

### Parser configuration

Use private fields and fallible constructors for configuration with validity
constraints. The prototype's `Bits::new(width)` accepts widths through 64;
`Literal::new(width, value)` additionally requires the value to fit in that width.
They return `ConfigError`, separate from `ParseError`. Read-only accessors expose
configuration without allowing callers to invalidate it. Parsing can then rely
on these invariants while checking input-dependent conditions on each call.

In Lean, prove that successful construction establishes a named validity predicate,
then state the parsing theorem under that predicate. Aeneas translates the fields
as ordinary Lean records, so Rust privacy alone does not discharge this proof
obligation. Any future operation that constructs or changes configuration must
establish or preserve the same invariant.

`Seq`, `Choice`, `Optional`, `And`, and `Not` currently need no additional validity
constraint beyond their children's contracts and Rust output-type requirements.
`TakeAligned` accepts
every `usize` count; insufficient input is a parse error. These types can still
be assembled directly. Input-derived configurations require an explicit decision
about how construction failure becomes rejection of the enclosing format.

### Input and cursor

The input is an immutable byte slice. The cursor describes where and how parsing
continues without borrowing the slice itself. Cursor construction and operations
must establish bounds and avoid overflowing position arithmetic.

Bit semantics need an independent specification before choosing cursor fields.
Hammer's [endianness wrapper](../src/parsers/endianness.c) and
[bit reader](../src/bitreader.c) can track consumption from opposite ends of a
partially consumed byte when bit order changes. A single monotonically increasing
bit offset should not be assumed sufficient to preserve this behavior.

Specify field width, sign extension, byte order, bit order, alignment, padding,
and end-of-input behavior. Preserve unaligned byte parsing deliberately. Aligned
payloads can use borrowed slices; unaligned payloads may need a bit view, a span,
or decoded values.

### Known C issue: absolute bit position overflow

Open C Hammer issue, observed on 2026-10-04 in checkout `a8dc507`. The
[`h_input_stream_pos` helper](../src/internal.h) converts a byte position to an
absolute bit count using `size_t` arithmetic:

```c
(state->pos + state->index) * 8 + state->bit_offset + state->margin
```

Its addition and multiplication bounds are enforced only by ordinary `assert`
checks. With assertions enabled, an oversized position aborts the process; with
`NDEBUG`, the checks disappear and unsigned arithmetic can wrap. The
[`h_tell` implementation](../src/parsers/seek.c) stores this result in a `uint64_t`
token, but that widening happens after the `size_t` calculation and cannot repair
overflow on a 32-bit target.

Multiplication first overflows at byte position `SIZE_MAX / 8 + 1`: 512 MiB with
32-bit `size_t`, or 2 EiB with 64-bit `size_t`. The current position assertion is
slightly stricter: it requires `pos + index < SIZE_MAX / 8`, rejecting the byte
immediately before that overflow boundary as well.

A minimal helper-level reproducer is:

```c
#include <sys/types.h>
#include "internal.h"
#include <stdio.h>

int main(void) {
    HInputStream stream = {.pos = SIZE_MAX / 8 + 1};
    printf("%zu\n", h_input_stream_pos(&stream));
    return 0;
}
```

Compile from the repository root with `cc -std=gnu99 -O2 -Isrc`, once with
`-DNDEBUG` and once without. On the tested 64-bit host, the former prints `0` and
the latter fails the assertion in `h_input_stream_pos`. This uses a synthetic
stream state and does not allocate or parse a 2 EiB input. Assertion behavior
depends on `NDEBUG`, not optimization alone; the current SCons `opt` variant
adds `-O3` without defining `NDEBUG`.

The C follow-up is checked position/length arithmetic with a defined failure
path and boundary tests with and without assertions. Audit
`h_input_stream_length` in the same header, the base-position conversions used
by `h_seek` (its offset checks happen after those conversions), result-length
calculation in [packrat parsing](../src/backends/packrat.c), and the separate
`s->pos * 8 + s->bit_offset` calculation in
[`h_parse_finish`](../src/hammer.c). The helper reproducer does not constitute a
full audit of those paths. No C fix has been made as part of RustHammer.

RustHammer should retain byte-and-bit cursors for position reporting and prove
cursor advancement safe without requiring an absolute bit count to fit in
`usize`. C differential checks must stay within C's representable range; larger
positions need independent specifications and boundary checks.

## Grammar structure and execution

Use concrete structures such as `Seq<P, Q>`, `Choice<P, Q>`, `Repeat<P>`,
`Map<P, F>`, and `Bind<P, F>`. Their fields retain structure while trait
implementations provide execution through static dispatch.

Separate the ability to execute a parser from the ability to analyze or lower its
grammar. A custom parser function can be an extension point without automatically
being eligible for compilation. An unrestricted value-dependent `Bind` cannot
generally be lowered to a context-free grammar; C Hammer already marks
[bind](../src/parsers/bind.c) as unsuitable for its regular and context-free
compilation paths.

Initially, these can be module boundaries rather than separate crates:

| Component | Responsibility |
| --- | --- |
| Input and primitives | Cursor invariants, bit operations, literals, numeric decoding, bounds, and spans. |
| Combinators | Typed composition with explicitly specified control flow and results. |
| Grammar analysis and lowering | Supported grammar representations, capability checks, and compilation. |
| Execution engines | Direct parsing initially; memoized or compiled execution as later implementations. |
| Lean specifications and proofs | Independent semantics, primitive proofs, combinator theorems, and application proofs. |

The Rust parsing implementation used by applications should be the implementation
translated for verification. Any later optimized implementation needs its own
correctness or refinement argument.

### Choice and backend semantics

The initial core uses ordered choice. For example:

```text
sequence(choice("a", "ab"), "c", end)
```

On `"abc"`, the first choice arm succeeds on `"a"`; the later failure on `"c"`
does not revisit that choice. A context-free interpretation of the alternatives
can accept `"ab" + "c"`. Hammer describes the ordered behavior in the comments
for `h_not` in its [public API](../src/hammer.h).

Additional backends must either preserve the selected semantics on a supported
subset or expose a separately specified interpretation. Structural compilability
alone is insufficient to establish equivalence. Ambiguous grammars also need an
explicit result and disambiguation policy.

The prototype's `Choice<P, Q>` requires a common output type. It retries only
`Mismatch`, `UnexpectedEnd`, and `TrailingInput`, restarting at the original
cursor, and returns the second result unchanged. The first success wins, even if
it consumes no input. Unused branches are not parsed, but both children must have
been constructed before assembling the choice. `InvalidWidth`, `InvalidLiteral`, and `InvalidBounds`
are construction errors in the separate `ConfigError` type. During parsing,
`InvalidCursor`, `Unaligned`, `NonProgress`, and `CountOverflow` propagate immediately.
Partial-input exhaustion returns `NeedMore` and does not select another arm. Final-input truncation remains
recoverable `UnexpectedEnd`. `End` accepts only a canonical end cursor on final
input, waits at a partial buffer boundary, and rejects leftover bits, including
zero padding.

### Optionality and lookahead

The core now includes these counterparts of C Hammer's direct combinators:

| C combinator | Rust combinator | Success and consumption |
| --- | --- | --- |
| `h_optional(p)` | `Optional<P>` | Preserve child success as `Some(value)`; recoverable rejection yields `None` at the starting cursor. |
| `h_and(p)` | `And<P>` | Require child success, discard its value, and return `()` at the starting cursor. |
| `h_not(p)` | `Not<P>` | Child success becomes `Mismatch`; recoverable rejection yields `()` at the starting cursor. |

All three run the child once and propagate fatal errors. They use the
same recoverable categories as `Choice`. Zero-length success remains success:
optionality returns `Some`, positive lookahead succeeds, and negative lookahead
rejects. No progress requirement is needed because none of these combinators loops.

The Rust representations replace C's absent optional token with `None` and absent
lookahead AST with `()`. The complete-buffer contract treats truncation as
recoverable rejection; the partial-input contract propagates `NeedMore` unchanged
through all three combinators. Actual streaming suspension remains outside this
subset and requires a separate implementation and proof. Cursor
restoration does not undo custom parser effects; hidden mutable semantic state
does not acquire rollback guarantees from these combinators.

`ControlSpec.lean` gives relational contracts; `ControlProofs.lean` proves the three
generic implementations and the cursor-restoration properties. Tests port the
existing C optional-choice grammar and negative-lookahead disambiguation case,
and exercise partial consumption, truncation, borrowed values, non-`Copy` outputs,
empty matches, and fatal errors. These examples are an incremental semantic
inventory, not an exhaustive comparison across C backends.

### State, actions, and effects

Prefer explicit values and typed environments for dependencies between fields.
Avoid hidden mutable callback state in the verified core. Backtracking and
lookahead must have defined rollback behavior for every semantic state component,
not only the cursor.

Mapping and predicates require contracts for their computations. `Fn` is a useful
interface but does not itself guarantee purity, termination, or freedom from
panics. Ordinary local mutation and allocation are acceptable when their behavior
is translated and proved.

The implemented `Map` and `Verify` use generic `Fn` callbacks and shared parser
access. Their proofs require callback contracts only on values admitted by the
child's success contract. `Verify` borrows the decoded value, preserving non-`Copy`
outputs on acceptance. Its `Mismatch` result participates in the existing
ordered-choice semantics. Final borrowed-record assembly currently uses direct
Rust construction because of the recorded closure extraction limitation.

Observable application effects should normally happen after successful parsing.
If deferred actions are supported, specify their ordering, commit point, and
behavior on failed or speculative branches. C Hammer's immediate and deferred
action APIs should be inventoried separately rather than mechanically translated.

### Recursion, progress, and resources

Named parser types or functions can express recursion without infinitely nested
combinator types. Runtime grammars may use a finite graph of rule IDs and explicit
node variants. Such a graph needs a design for output typing, ownership, and rule
validation; a generic internal parse tree may be appropriate there.

Left recursion requires a suitable algorithm and proof. Hammer already exercises
it in [its core parser tests](../tests/t_parser.c), so its omission from an early
subset must be explicit. Guarded recursion and left recursion should have separate
milestones.

Unbounded repetition now enforces valid, strictly advancing success cursors,
reporting `InvalidCursor` or `NonProgress` on violations. Empty-success parsers
remain useful in finite, explicitly bounded repetition, as implemented by `Repeat`.
The [target repetition family](rusthammer-combinators.md#one-repetition-design)
specifies shared stopping, incompleteness, and progress rules. Finite and unbounded
forms have generic Lean contracts, including count-overflow handling. Arbitrary
seeking and recursive cycles need termination measures beyond simple input consumption.

Handle invalid parser configuration during construction. During parsing,
distinguish grammar mismatch, committed failure if supported, incomplete input,
and resource exhaustion. Choice and repetition must propagate the appropriate
categories rather than treating every error as a recoverable mismatch.
Exhausting a budget does not prove that the input is outside
the language. The prototype's concrete recoverable and fatal categories are
specified above, including the distinct `NeedMore` outcome; committed failures
and resource-limit errors remain future additions.

Memoization must respect every dependency of a result: rule identity, input and
cursor state, parser parameters, and relevant semantic context. A `(rule,
position)` key is sufficient only under conditions that make those dependencies
implicit or irrelevant. Budget-dependent failures require special treatment.

### Streaming and seeking

Explicit finality and incomplete-input semantics are implemented before adding
buffering. `parse_with(input, cursor, InputStatus::Partial)` may return
`NeedMore` for missing bytes or an unconfirmed EOF. A final invocation never
returns `NeedMore` for built-in parsers under their child/callback contracts.
`parse(input, cursor)` is the complete-buffer convenience method and preserves
its previous values, consumption, and error ordering.

Prefix parsing may succeed on partial input as soon as the grammar is satisfied;
whole-input parsing includes `End`, which waits for finality and rejects all
remaining bits, including padding. `NeedMore` has no committed cursor or partial
value. The caller may accumulate bytes and retry from the original cursor; it
must supply the accumulated buffer, not only the newest chunk. Confirmation of
EOF can resolve `NeedMore` without adding bytes.

Primitives classify exhaustion before enclosing combinators can recover from it.
Converting only the final result of a complete parser would be incorrect: choice,
optionality, or negative lookahead might already have consumed the rejection.
Numeric literals conservatively read their whole field before comparing;
`NeedMore` does not guarantee that some extension will succeed or provide a
minimum required size.

The new API, generic combinator contracts, final-input compatibility, marker
composition, and the record's exact partial-input behavior are Lean-checked.
Native tests cover both finality modes and retry records at every byte boundary.
The small `probes/input_status.rs` experiment also records successful translation
and Lean type-checking of default trait methods and borrowed three-outcome values.

Streaming machinery remains a later capability. Specify buffering, resumption,
consistency across growing buffers, and output lifetime/ownership across chunks.
Retries currently reparse prefixes and can rerun callbacks; speculative effects
are not rolled back. Input-borrowing outputs refer to the input of their invocation;
`BytePattern` outputs instead borrow its configured pattern.

Seeking needs explicit bounds, position units, and interaction with backtracking,
memoization, spans, and termination. It should not silently inherit the invariants
of a forward-only core.

### Deferred: eager literal rejection

Deferred by agreement on 2026-10-04. Revisit before implementing streaming
buffering and resumption; repetition work can proceed first.

`Literal` currently reads its entire numeric field before comparing. For example,
`Literal::new(16, 0x6162)` (the bits of `"ab"`) given partial input `"x"` returns
`NeedMore` even though the available prefix already conflicts. This is conservative and permitted by the
current contract, but delays rejection and selection of later `Choice` branches.

The follow-up is to compare available bits with the expected literal prefix and
return `Mismatch` as soon as a difference is known. A matching incomplete prefix
would still yield `NeedMore` on partial input or `UnexpectedEnd` on final input.
Applying eager rejection in both modes would intentionally change the error for
truncated, conflicting final input from `UnexpectedEnd` to `Mismatch`, without
changing which complete inputs match.

Update the literal specification, Lean proofs, affected application proofs, and
tests together. Cover matching and conflicting truncated prefixes, unaligned
fields, and interactions with choice and lookahead. The parser interface and
generic combinators need no redesign.

`BytePattern` already compares each complete decoded byte, so `b"ab"` against
partial `b"x"` returns `Mismatch`. Its incomplete final byte remains conservative:
at an unaligned position, conflicting available bits still yield `NeedMore` until
that byte is complete. Include this case in the future eager bit-prefix work;
adding byte patterns did not change numeric `Literal` semantics.

## Verification approach

Define independent Lean specifications for bit decoding and the selected parser
semantics. Relate the translated Rust implementation to these specifications.
Merely restating the extracted implementation is insufficient to establish that
it recognizes the intended format.

For well-formed parsers and inputs within stated assumptions, establish:

- **Soundness:** successful results are permitted by the specification.
- **Completeness:** inputs accepted by the specified parsing semantics succeed
  when the required resources are available.
- **Value and cursor correctness:** decoded values and consumed input are exact.
- **Safe rejection:** malformed input produces a specified parsing outcome rather
  than a panic, invalid access, or arithmetic failure.
- **Termination:** parsing finishes under the grammar and resource assumptions.

Specify ordered choice, predicates, and lookahead as part of those semantics;
completeness is not completeness for an unrelated context-free interpretation.

Prove each combinator assuming contracts for its child parsers. Mapping and bind
also require contracts for their functions or parser families. Application-parser
proofs should reuse these theorems and add format-specific constraints. Arbitrary
Rust implementations of the `Parser` trait do not acquire correctness proofs
merely by implementing the interface.

Rust `ParseOutcome::Error` and `NeedMore`, or `Result::Err` from the complete
entry point, represent intended parser outcomes. Aeneas's
execution model separately represents failures such as panics and divergence.
The proofs must distinguish them. Physical resource and platform assumptions,
external models, and the trusted translation/toolchain boundary must be recorded.

Keep generated Lean separate from handwritten specifications and proofs. Check
for admitted proof obligations, unsupported translated bodies, and new opaque
parser operations. Do not replace the parser being verified with an assumed
correct axiom to obtain a passing proof build.

## Aeneas compatibility evidence

The initial investigation used these local revisions:

| Project | Revision |
| --- | --- |
| Hammer | `c0d6b23f739292ffc6e6fb46e989e0a498b26409` |
| Aeneas | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| Charon, matching Aeneas's pin | `c8f15d7d658c86a95658f71ad99cddd4be002e04` |
| nom, version 8.0.0 | `51c3c4e44fa78a8a09b413419372b97b2cc2a787` |

The Aeneas checkout specifies Lean `v4.31.0`; its matching Charon checkout uses
Rust `nightly-2026-09-17`. These describe the investigation baseline, not a promise
to follow unpinned latest versions.

Small scratch experiments on 2026-10-03 produced the following results:

| Interface or feature exercised | Observed result |
| --- | --- |
| Generic sequence, choice, repetition, `Fn` mapping, and value-dependent bind with separate input and position arguments | Charon and Aeneas generated Lean successfully. |
| Associated outputs containing borrowed slices, with input and position separate | Charon and Aeneas generated Lean successfully. |
| Passing and returning a borrowed input object through the tested generic combinators | Charon succeeded; Aeneas reported abstraction-ending and value-translation errors. |

The successful probes used a byte cursor and simplified errors. They did not
establish the full bit interface, recursive grammar support, production error
semantics, or parser correctness. **Generated Lean was not type-checked and no
correctness proof was completed during this investigation.** The failing shape
does not establish that all borrowed input objects are unsupported.

Temporary artifacts were created under
`/tmp/rusthammer-design-probe-6f19so4g/`, outside this repository. They are not a
durable regression suite. The first implementation phase should preserve minimized
probes and commands in the RustHammer project. The successful borrowed-output
probe used:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
    --dest-file borrowed.llbc -- --crate-type lib --edition 2021 borrowed.rs
~/source/aeneas/bin/aeneas -backend lean -dest lean-borrowed \
    -abort-on-error -warnings-as-errors -no-progress-bar borrowed.llbc
```

The generated trait represents the associated output as a Lean type parameter:

```lean
structure Parser (Self : Type) (Self_Output : Type) where
  -- translated parse operation
```

Thus, the proposed associated type is a Rust API choice, not an assumption that
Lean requires that particular source syntax.

Subsequent prototype work has now type-checked and proved the generic `Map` and
`Verify` implementations, the concrete `Flags` mapping callback, the record header
predicate, and the complete borrowed record parser. This provides stronger
evidence than the initial extraction-only experiments. The finality interface and
default trait method now also translate and type-check, with primitive,
combinator, and application proofs for both input statuses. The separate capturing
callback failure is retained under `rusthammer/probes/`; the normal verification
command checks the supported record implementation rather than expecting that
probe to succeed.

The inspected Aeneas revision supports trait and closure examples, but documents
limitations involving particular generic mutable-reference patterns, nested-loop
control flow, unsafe code, and concurrency. Validate exact Rust patterns instead
of assuming that all safe Rust translates or that all closures are unsupported.
See the pinned [Aeneas README](https://github.com/AeneasVerif/aeneas/blob/557eff83ecef5083b98a52a94ca7fae63d6c1dab/README.md)
and [closure tests](https://github.com/AeneasVerif/aeneas/blob/557eff83ecef5083b98a52a94ca7fae63d6c1dab/tests/src/closures.rs).

The collection loop now translates and is proved for exact, finite bounded, and
unbounded repetition, with constructor/accessor contracts, runtime progress
checks, count-overflow handling, and exact-count specialization. A helper call in
a `while` condition triggered Aeneas's early-return prepass error for this loop;
an equivalent `loop` with the stop check inside translates and is proved. The
[compatibility notes](../rusthammer/probes/README.md#repetition-loop-control-flow)
record this source-shape constraint separately from the deferred callback issue.
The durable `probes/repeat_n.rs` preserves the initial borrowed, non-`Copy`
collection experiment. The verification command tests both feature configurations
and extracts with `alloc` enabled, including the repetition constructors.

Shared parser references and output-selection wrappers now extract and are proved
in the actual library. References preserve both trait methods; tuple projections
need no callback. Their generic proofs cover arbitrary output types, and native
tests check borrowed slices, non-`Copy` records, and destructor behavior. The older
borrowed-record callback issue remains deferred.

The verification command also extracts derived `Clone` methods. Repetition's
optional maximum uses `Option::clone`; its Rust standard-library body is explicitly
included in extraction, avoiding an opaque external declaration in the generated
Lean code. Parser proof coverage and the no-admitted-obligations check remain in place.

`Epsilon`, `Fail<T>`, and `TryMap` now extract and have reusable contracts for both
input statuses and the complete API. `TryMap` maps conversion rejection to
`Mismatch` and preserves child errors and `NeedMore`. Its captured fallible
callback probe returns an owned, non-`Copy` record through the actual library
source and passes translation and Lean checking. `Fail<T>` uses `PhantomData<T>`:
the pinned Aeneas rejects a function-type marker such as `PhantomData<fn() -> T>`.
Manual `Copy`/`Clone` implementations avoid bounds on its output type. The
[cross-crate investigation](../rusthammer/probes/cross_crate/README.md) diagnosed
the separate dependency-extraction failure: later MIR inserts cleanup discriminant
reads on partially moved enums, which the pinned interpreter rejects. Five
internal matches now move complete payloads before unpacking or discarding them.
The API and existing proofs are unchanged. Local verification now also extracts
all library verification roots at optimized MIR and a separate Cargo consumer,
including borrowed outputs and repetition, then Lean type-checks both results.
Minimal failing and passing patterns are retained for toolchain upgrades. These
checks establish compatibility for the exercised code; consumer application
correctness still requires its own specification and proofs.

Pin Aeneas, Charon, Rust extraction tooling, Lean, and proof dependencies together.
The local verification command runs extraction and Lean checking; CI integration
is deferred at the user's request. Upgrades must rerun compatibility probes and
the proof suite. Further investigation of the borrowed-callback limitation is
also deferred; the existing reproduction remains available.

## Lessons to take from nom

Use nom as a reference for typed composition, borrowed outputs, explicit error
categories, and repetition progress checks. Its complete-versus-streaming distinction informs the explicit finality contract;
RustHammer keeps its own smaller interface and bit-cursor semantics.

Do not assume its input semantics match Hammer's. In particular, nom's
[bit-to-byte adapter](https://docs.rs/nom/8.0.0/nom/bits/fn.bytes.html) skips a
remaining partial byte; Hammer's `h_bytes` can parse bytes at unaligned positions.
The proposed core should retain Hammer's bit semantics deliberately.

Avoid adopting nom's full generic input, mutable-parser, and output-mode machinery
before the smaller RustHammer interface is proved useful and tractable. This is a
scope choice, not a finding that those mechanisms cannot be verified.

## Implementation and proof stages

These stages organize work, not temporary public APIs. The
[combinator API plan](rusthammer-combinators.md#implementation-order-and-migration)
specifies the intended families and the next implementation steps. Complete a
subset of that API at each stage without exporting unsupported cases or stand-in
types that are intended to be discarded.

| Stage | Work | Completion evidence |
| --- | --- | --- |
| 1. Semantic inventory and compatibility foundation | Inventory the public API and backend behavior; select the first supported subset; preserve minimized Rust probes; pin tools; establish local verification (CI deferred). | Written contracts for the initial subset and Lean-checked translations of the proposed trait, borrowed outputs, and representative combinators. |
| 2. Verified input and primitives | Specify the bit cursor, ordering, alignment, widths, sign extension, bounds, and basic literal/numeric operations. | Lean proofs of decoding, cursor invariants, termination, and safe failure; boundary tests against agreed Hammer behavior. |
| 3. Compositional core | Implement sequence, ordered choice, optionality, lookahead, bounded repetition, mapping, predicates, and the data dependencies needed by the first format. Add unbounded repetition only with progress semantics. | Reusable combinator theorems, checked callback assumptions, and tests for backtracking, empty success, truncation, and error propagation. |
| 4. First verified application parser | Parse a small binary record with bit fields, a constrained header, a bounded length-prefixed payload, and explicit end-of-input behavior. | An independent format specification and a Lean-checked application theorem covering values, consumption, valid-input acceptance, safe rejection, and termination under documented bounds. |
| 5. Capability expansion | Add guarded recursion, then separately plan left recursion, runtime grammars, seeking, streaming, deferred effects, additional field types, and richer diagnostics. | A contract, compatibility probe, tests, and proof obligations for each added capability; no implicit claim of full Hammer coverage. |
| 6. Additional engines and optimization | Add memoization or compiled backends where justified; optimize measured bottlenecks. | Correctness or refinement proofs on explicit supported subsets, documented complexity assumptions, differential tests, and benchmarks. |

Use native Rust tests, focused property tests, and differential tests with C Hammer
to catch integration and specification mistakes. Compare acceptance, decoded
values, and consumption after normalizing intentional output-representation
differences. Resolve disagreements against the specification. Testing supplements
the proofs and helps identify missing assumptions.

The first application should be small enough to prove completely. An NTP-style
header can supply representative bit fields, but a complete NTP or DNS parser is
not required for this milestone.

## Open decisions

- Which C semantics are compatibility requirements, particularly mixed bit-order
  scopes, unusual combinators, immediate/deferred actions, and seeking?
- Which capabilities are required for the first RustHammer release, and when must
  it support left recursion or grammars built at runtime?
- Should context-free alternatives have a distinct API, or should lowering accept
  only grammars for which ordered-choice equivalence can be established?
- What cursor representation, bit-span representation, and whole-input padding
  rules best preserve the chosen semantics?
- Which resource limits, error categories, and diagnostics belong in the initial
  core, and which require a separate execution context?
- The core provides allocation-free folding alongside opt-in collected
  outputs. Are additional collection policies or explicit allocation-failure
  results needed? Which platforms and Rust versions should be supported
  independently of the extraction toolchain?
- What is the ownership model for streaming output and runtime recursive grammars?
- Which handwritten parser extensions and callback patterns will be supported by
  the reusable verification contracts?
- Where will the Rust crate and Lean project live, and are C or other language
  bindings needed later?

Resolve interface questions using small Lean-checked examples before expanding
the implementation. The prototype now provides a verified record parser and
reusable primitive, sequencing, choice, mapping, predicate, optionality, lookahead,
finite/unbounded repetition, parser-reference, output-selection, empty/failing
grammar, checked-mapping, folding, separated-list, and `Bind` contracts, plus
verified dependent-format examples. Next expand the binary primitives and other
durable families in the companion API plan.
Continue focused semantic and differential checks. CI and the Aeneas callback
investigation remain deferred.
