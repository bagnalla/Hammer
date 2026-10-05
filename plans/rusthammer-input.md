# RustHammer input, ordering, and spans

Status: restricted ordering implemented and proved, 2026-10-05; spans remain planned.
This document extends the
[main plan](rusthammer.md) and [combinator plan](rusthammer-combinators.md).
The production library implements the context and scope contract below, with
numeric-reader and compositional proofs. The
[restricted probe](#restricted-probe-and-evidence) records the preceding design
check. The earlier unrestricted-order probe is retained as historical evidence.

**RustHammer allows bit-direction changes only at byte boundaries.** Keep
big/little byte order, both fixed bit directions, and fields crossing byte
boundaries. Exclude arbitrary switches between the high and low ends of one
partially consumed byte. This is an intentional API restriction, not a
milestone limitation awaiting removal. Reconsider it only if a concrete use
case justifies its implementation and proof cost.

This decision replaces the earlier proposal for a `(byte, high, low)` cursor.
Keep typed outputs, static dispatch, immutable input, `no_std`, and the existing
configuration-error, parse-error, and `NeedMore` distinctions.

## Compatibility and motivation

C Hammer's direct parser supports more general order changes. Its
[`HInputStream`](../src/internal.h),
[`bit reader`](../src/bitreader.c), and
[`endianness wrapper`](../src/parsers/endianness.c) track consumption at both
ends of a byte. RustHammer deliberately supports a smaller ordering contract.
Compare values and consumption with C within that supported subset; unsupported
scope transitions should be tested as intentional rejections.

The historical evidence supports ordinary ordering control more strongly than
arbitrary within-byte direction changes:

- [Issue #77](https://github.com/UpstandingHackers/hammer/issues/77) motivated
  the combinator with TIFF's header-selected byte order.
- [Issue #118](https://github.com/UpstandingHackers/hammer/issues/118) reported
  problems with unaligned 4-bit and 10-bit fields. The
  [retained reproducer](../tests/t_regression.c) uses big bit order and little
  byte order for those fields. It does not require alternating the bit direction.
- The bundled DNS, NTP, and TFTP examples do not use ordering overrides. The
  examples and historical reports inspected did not identify an application
  requiring consumption from opposite ends of one byte. This is limited
  evidence, not a claim that no such applications exist.

The C audit was conducted at Hammer commit `b651dfe`. Additional sources are
[`h_bits` and fixed-width aliases](../src/parsers/bits.c),
[`h_token`](../src/parsers/token.c), [`h_tell`](../src/parsers/seek.c), and the
[ordering tests](../tests/t_parser.c). Seeking, live streaming, left recursion,
and equivalence across all compiled backends need separate work.

## Numeric ordering

There are two independent axes:

| Axis | Big / high first | Little / low first |
| --- | --- | --- |
| Bit direction | Consume the current byte from its high end. | Consume it from its low end. |
| Byte order | Earlier physical-byte fragments have greater numeric significance. | Earlier fragments have less numeric significance. |

Both default to big/high first. Bits within each fragment keep their ordinary
numeric significance. Little bit order does not reverse a fragment's bits. An
aligned 8-bit read of `0x61` yields `0x61` in all four combinations. A 5-bit read
from that byte yields `12` in high-first order and `1` in low-first order.

Partition each field at physical byte boundaries. Take the requested portion
from the active end, interpret that fragment as an unsigned bit pattern, and
assemble fragments according to byte order. Big byte order appends each
fragment below the accumulated value; little byte order places it above the
fragments already read. Thus byte order still matters for unaligned fields and
widths that are not multiples of eight. Field boundaries remain part of numeric
semantics: a low-first 8-bit field is not eight 1-bit fields folded MSB-first.

A parser can read any supported width, including across byte boundaries, while
using one bit direction. Byte-order changes themselves require no alignment.
The restriction concerns changing bit direction, including restoration when a
scope exits.

## Cursor and context

Retain the existing `Cursor { byte, bit }` representation. `bit` counts how many
bits of the current byte have been consumed, with `bit < 8`. Exhausting the byte
increments `byte` and resets `bit` to zero. Input-relative validity remains:
`byte < input.len()`, or exactly `(input.len(), 0)` at the end.

There is no need to introduce a second consumed-end count or new cursor
construction rules for ordering. Existing raw-cursor validation and parser
configuration constructors retain their roles.

Pass interpretation settings separately, by value:

```rust,ignore
pub enum BitOrder { HighFirst, LowFirst }
pub enum ByteOrder { Big, Little }
pub struct Order { pub bit: BitOrder, pub byte: ByteOrder }
pub struct ParseContext { pub status: InputStatus, pub order: Order }

pub trait Grammar<'input> { type Output; }
pub trait Eval<'input, Backend>: Grammar<'input> {
    fn eval(
        &self, backend: &mut Backend, input: &'input [u8], cursor: Cursor, context: ParseContext,
    ) -> ParseOutcome<Self::Output>;
    // Parser supplies direct parse / parse_with entry points separately.
}
```

For a partial byte, the cursor's physical meaning depends on the active bit
order. In LSB-numbered physical indices, the unread interval is:

- High first: `[0, 8 - cursor.bit)`.
- Low first: `[cursor.bit, 8)`.

A cursor is a position within a known parsing context, not a standalone physical
snapshot. `Tell` continues to return the cursor. Resuming from a saved partial
cursor requires its original bit direction; callers must not reinterpret a
cursor obtained inside a low-first scope using the default high-first entry
point. A bare cursor contains no provenance with which to detect that misuse.
A span that escapes its context stores the necessary direction explicitly.

`parse` and existing complete-input primitive helpers supply final input and
the current both-big default. Explicit partial parsing supplies a context;
retry after `NeedMore` uses the original cursor and order with the accumulated
input. Finality may change from partial to final. The associated output type
and input lifetimes are unchanged. `parse_with` now accepts `ParseContext` in
place of `InputStatus`; there are no temporary public adapters. `Order::DEFAULT`
and `ParseContext::{FINAL, PARTIAL}` supply the default order explicitly.

### Position and progress

The existing mathematical position remains:

```text
position(cursor) = 8 * cursor.byte + cursor.bit
```

Use unbounded naturals in Lean and lexicographic `(byte, bit)` comparisons in
Rust. No absolute machine bit count or machine subtraction is needed. Position
still uniquely identifies a normalized cursor value. For parsers running in
the same enclosing context, the scope rules below also preserve the physical
interpretation of partial-byte endpoints.

Existing match-length comparison, strict forward-progress checks, and the
termination measure `8 * input.len() - position(cursor)` can therefore retain
their arithmetic structure. Their generic contracts now carry the full context;
the existing application theorems retain default order. Arbitrary custom parser
behavior still needs its own contract.

## Ordering scopes

`WithOrder<P>` overrides both axes for its child and preserves input finality.
Sequencing supplies its original context to the following child. A scope whose
bit direction differs from its caller enforces alignment at both boundaries:

1. Validate the input cursor. An invalid cursor returns fatal `InvalidCursor`.
2. Require `cursor.bit == 0` before calling the child; otherwise return fatal
   `Unaligned` without calling it.
3. Call the child with the selected order and original finality.
4. Propagate an error or `NeedMore` unchanged; neither commits a cursor/output.
5. On success, validate the returned cursor, then require `next.bit == 0` before
   returning to the enclosing direction. Invalid bounds produce `InvalidCursor`;
   an unaligned success becomes fatal `Unaligned` and its value is discarded.

The successful-exit check is essential. Allowing a low-first scope to return
halfway through a byte would let the enclosing high-first parser reinterpret
that partial byte. Do not silently discard bits, insert padding, or restart
from its other end.

If the bit direction is unchanged, the wrapper simply delegates with the new
context. It adds no alignment or validation checks beyond the child. In
particular, byte-order-only scopes can start and finish unaligned. Nested scopes
using the current bit direction also remain unrestricted. All four order
configurations are valid; alignment failures depend on execution position and
belong to parsing, not fallible parser construction.

Examples below use pseudocode, starting in high-first mode at a byte boundary:

| Grammar | Result of the scope rule |
| --- | --- |
| `with_low_bits(seq(bits(3), bits(5)))` | Allowed: the changed-direction region consumes a whole byte. |
| `with_low_bits(seq(bits(3), with_low_bits(bits(5))))` | Allowed: the inner scope keeps the active direction. |
| `seq(bits(3), with_low_bits(bits(5)))` | `Unaligned` on entry to the changed-direction scope. |
| `with_low_bits(bits(3))` | `Unaligned` on successful exit. More input does not repair this grammar. |
| A byte-order-only wrapper around an unaligned 10-bit field | Allowed. |

The guard is a rule for entering/exiting a scope, even when its child would
consume zero bits. For example, entering a different-direction empty scope at
an unaligned cursor is rejected. Wrap a complete low-first region, including
any explicit padding, rather than individually scoping fields that leave the
byte unfinished.

Lookahead follows the same rule: from an aligned cursor,
`with_low_bits(and(bits(3)))` can succeed because the child lookahead restores
its cursor before leaving the scope. `and(with_low_bits(bits(3)))` encounters
the inner scope's unaligned-exit error. No special exemption hides a scope
violation. Existing fatal-error propagation through choice/lookahead applies.

## Primitive and combinator policy

| Family | Proposed behavior |
| --- | --- |
| `Bit`, `Bits`, `SignedBits`, `Literal` | Use the active bit direction and byte-fragment order. Sign extension follows unsigned field assembly. |
| `Byte`, `I8`, byte sets and ranges over them | Decode an 8-bit field in the active order, including at unaligned starts. |
| `BytePattern` | Match successive contextual 8-bit fields, like C `h_token`. Preserve the configured pattern slice's independent lifetime. |
| `BeU16/32/64`, `BeI16/32/64` | Pin big byte order and inherit bit direction. Future `Le` readers do the symmetric operation. |
| `TakeAligned` | Require `bit == 0`; borrow raw bytes without decoding or implicit alignment. |
| `SkipBits` | Keep the existing O(1) cursor arithmetic. Consumed count is independent of direction; the active context determines which physical bits it skips. Validate even a zero count. |
| `Tell`, `End` | Report the validated cursor; require `(input.len(), 0)` and finality for end-of-input. |
| `Seq`, selection, mapping, predicates, `Bind` | Pass context through ordinary child calls. Existing output types and callback obligations remain. |
| `Choice`, `Optional`, `And`, `Not` | Restore the original cursor/context for retries and lookahead. Preserve existing outcome rules, including propagation of fatal `Unaligned`. |
| `ButNot`, `Difference`, `Xor` | Preserve existing selection/outcome rules and byte-and-bit length comparison. Both alternatives receive the same enclosing context. |
| Repetition and folding | Retain current count, progress, and overflow rules. Successful children obey the enclosing context's bit direction at partial endpoints. |

C's contextual `h_uint16` behavior corresponds to `Bits::new(16)` plus a typed
conversion when needed. Explicit `Be` readers keep their named byte order even
inside an opposite byte-order scope. Preserve existing zero-width behavior,
configuration validation, and shortage classification outside the new scope
guards. The input buffer still contains whole bytes with no implicit padding.
The known [C absolute-position overflow issue](rusthammer.md#known-c-issue-absolute-bit-position-overflow)
remains excluded from compatibility.

## Matched-input spans

Retain endpoint positions and record the enclosing bit direction:

```rust,ignore
pub struct BitSpan<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
    bit_order: BitOrder,
}
```

Require valid endpoints and `start <= end` in normalized position order. Permit
empty spans. A span-producing wrapper validates endpoints even if a custom
child does not: bad bounds yield `InvalidCursor`, backward movement yields
fatal `NonProgress`. Child contracts must establish the scope discipline.
Endpoint checks alone cannot verify how arbitrary custom parsers used the input.

For a span within one byte, its physical bits form one interval:

- High first: `[8 - end.bit, 8 - start.bit)`.
- Low first: `[start.bit, end.bit)`.

For a span crossing bytes, take the unread portion of the starting byte, all
intervening bytes, and the consumed portion of the ending byte, interpreting
both partial boundaries in `bit_order`. Legal inner direction changes start
and finish at whole-byte boundaries, so they do not create a second disjoint
portion in either boundary byte. The consumed-bit count remains the position
difference.

The stored direction matters even after parsing returns: `(byte, bit)` endpoints
alone do not distinguish a partial high-first match from a partial low-first
match. Byte order is unnecessary for identifying source bits. Endpoints and the
boundary direction still do not record internal whole-byte ordering scopes or
field grouping, so a span does not promise to replay decoding.

A raw `as_bytes()` view requires both endpoints to be byte-aligned and returns
original source bytes. If an iterator is exposed, specify canonical physical
order: increasing byte index and highest selected bit first within each byte.
Avoid an unchecked scalar `usize` bit length; retain positions or use a checked
conversion.

`Recognize<P>` would discard the child's value and return the span;
`WithSpan<P>` would return `(P::Output, BitSpan<'input>)`. Restricted ordering and
the backend boundary are established; this family is the next increment.
Constructor/accessor signatures and wrapper validation precedence still need to
be specified before implementation. Build the wrappers through `Grammar` and
backend-generic `Eval`, retaining the child's backend state and context rules.

## Production implementation and evidence

The library now implements `BitOrder`, `ByteOrder`, `Order`, `ParseContext`, and
`WithOrder`, with the retained `(byte, bit)` cursor. All built-in composition,
selection, repetition, folding, lookahead, and match combinators forward the
full context. `Bits`, signed fields, literals, bytes, patterns, and byte sets
decode using it. Named `Be*` readers pin big byte order while inheriting bit
direction; positional primitives keep their previous behavior. The public
complete-input helpers retain default order.

The fragment reader reuses the existing contiguous high-first decoder for
each selected physical fragment, then combines fragments according to byte
order. High-first/big fields keep the existing whole-field path. Private helpers
factor fragment selection, cursor advancement, and bounded accumulation; no new
extraction workaround is needed.

The [specification](../rusthammer/lean/RustHammer/OrderSpec.lean) expresses numeric
values with unbounded arithmetic over physical fragments.
[Reader proofs](../rusthammer/lean/RustHammer/OrderProofs.lean) establish decoded
values, exact consumption, invalid-cursor and exhaustion behavior, termination,
and arithmetic safety. [Parser proofs](../rusthammer/lean/RustHammer/OrderParserProofs.lean)
cover every order and finality, including signed/native narrowing, literals,
patterns, and byte sets. [Scope proofs](../rusthammer/lean/RustHammer/OrderScopeProofs.lean)
cover both guards, context propagation, and same-direction transparency without
assuming a child contract when entry is rejected. Generic combinator theorems
accept arbitrary contexts; all existing default-order format proofs are retained.
The verification runner audits 25 ordering theorems for only `propext`,
`Classical.choice`, and `Quot.sound`.

Ten dedicated native tests cover widths 0 through 64, all four orders and both
finalities, independent physical-bit and signed-value oracles, all reader
families, nested scopes, lookahead placement, borrowed outputs, entry call
counts, and exactly-once destruction after exit rejection. All previous native
tests pass with and without allocation. Promoted and optimized library MIR and
all 43 separate Cargo-consumer entries translate and Lean type-check. Three new
consumer entries exercise ordered typed fields, a borrowed payload crossing a
scope boundary, and a configured pattern borrow.

Run the full verification and optional C comparison from `rusthammer/`:

```sh
python3 tools/verify.py
python3 tools/compare_ordering.py --hammer-lib /absolute/path/to/libhammer.so
```

The actual library matches the probe's differential results: **107,364 C
agreements** and **2,848 expected scope rejections**, including 2,064 that C
accepts. The comparison uses the same independent event/bit-count model and
corpus classification. See the [runnable example](../rusthammer/examples/ordering.rs)
for scoped fields and a partial-input retry. Span geometry and recognition APIs
remain planned after the [backend foundation](rusthammer-backends.md); no public
span type is introduced by this work.

## Restricted probe and evidence

[`restricted_order.rs`](../rusthammer/probes/restricted_order.rs) exercises
the retained `(byte, bit)` cursor, immutable `ParseContext`, guarded `WithOrder`,
fragment decoding, typed sequencing, positive/negative lookahead, and borrowed
spans storing their boundary direction. It is an isolated probe, not a library
module or public milestone API.

Run from `rusthammer/`, with the pinned extraction tools and Lean dependencies:

```sh
python3 tools/check_restricted_order.py
# Optional comparison with a locally built C Hammer library:
python3 tools/check_restricted_order.py --hammer-lib /absolute/path/to/libhammer.so
```

The runner checks tool pins, Rust formatting/native tests, both promoted and
optimized MIR, generated Lean modules, and the same handwritten proofs against
both translations. It rejects admitted/opaque project declarations and checks
the printed axiom lists for all nine theorems. Build and proof artifacts go
under ignored `target/restricted-order/`. These probe checks are separate from
the production verification and Cargo-consumer checks above.

Evidence:

- Ten native tests pass. They cover field widths 0 through 64, all four orders,
  truncation, both finalities, raw invalid cursors, machine-boundary validation,
  nested restoration, same-direction unaligned scopes, lookahead, empty scopes,
  span bounds/direction, and input pointer identity. Call counters establish
  that entry rejections skip the child. Non-`Clone` output/drop tests check
  exactly-once cleanup when exit validation discards a successful value.
- Both MIR stages translate and Lean type-check, including a concrete nested
  grammar, lookahead compositions, and a partial low-first span that escapes
  its scope after the enclosing region reaches alignment. No additional
  extraction workaround was needed; span construction retains the earlier
  early-validation-return spelling.
- The [Lean contracts](../rusthammer/probes/restricted_order_proofs.lean) prove
  total cursor/boundary validation, the bit-order comparison, exit filtering,
  and generic scope behavior. The child contract is required only when the
  entry guard permits a call. Error precedence, finality/context propagation,
  same-direction transparency, and preservation of accepted values/cursors
  are explicit. Successful direction-changing scopes have valid, aligned
  entry and exit. The nine axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **107,364 differential cases agree with C:** 101,060 field reads and 6,304
  nested grammar cases. An independent event/bit-count model checks scope
  transitions and shortage precedence. **2,848 scope violations are rejected**,
  including 2,064 that C accepts. These deliberate compatibility differences
  are asserted separately, not counted as C agreement. The checks use final
  input and representable C positions; native tests cover partial input.

The proof coverage is deliberately focused. The probe's numeric reader,
physical span geometry, and concrete application grammars do not yet have
full correctness theorems. Rust lifetime checking and native pointer/drop
tests supply evidence outside the functional scope contracts. The production
integration above supplies its own reader/combinator proofs and preserves the
existing default application theorems; physical span proofs remain future work.

## Earlier unrestricted probe

The isolated [`input_order.rs`](../rusthammer/probes/input_order.rs) and
[runner](../rusthammer/tools/check_input_order.py) preserve the superseded
experiment with a `(byte, high, low)` cursor. They support arbitrary within-byte
direction changes and do not check the new scope alignment rule. They are not
part of the library, a Cargo feature, or the intended public API.

Historical checks passed: six native tests, both promoted and optimized MIR,
Lean type-checking, focused proofs of fragment cursor advancement and order
scope delegation, and 313,784 C comparisons. Those proofs do not establish full
reader, skip, span, or application correctness, and these results are not
verification of the revised design. See the [probe notes](../rusthammer/probes/README.md#earlier-unrestricted-input-ordering-probe)
for reproducible commands and the resolved optimized-MIR span-construction issue.

Retain this evidence for reference; its richer cursor is no longer scheduled
for production migration. Do not fold its unrestricted corpus into the revised
verification as though all of those cases should still be accepted.

## Implementation order

1. **Restricted scope probe complete.** The probe and evidence above cover entry
   and successful-exit guards, nested same-direction scopes, unaligned byte-order
   changes, lookahead, errors/`NeedMore`, and escaped span direction. Both MIR
   stages and the generic scope proofs pass.
2. **Production ordering complete.** Context and guarded `WithOrder` are integrated
   with numeric-reader and compositional proofs, default-format theorems,
   examples, and tests. Both MIR stages and the separate Cargo consumer pass;
   differential checks distinguish agreements from intentional rejections.
3. **Backend execution boundary complete.** Direct execution and its proofs use
   [Grammar / Eval / Parser](rusthammer-backends.md). Memoization and recursive
   rule construction are deferred; they do not block the span API.
4. Add the intended span/recognition APIs with bounds, physical-interval,
   borrowing, consumed-length, and raw-byte-view proofs. Expose only durable,
   implemented operations.

This removes the two-ended cursor invariant, its non-injective position mapping,
and the need for a separate physical-progress relation. Context plumbing,
fragment decoding, and scope integration are now implemented and proved in the
production library. Span operations will build on this restricted model.

Permutation, recursion, live streaming, seeking, memoization, and additional
backends remain separate designs. CI and the older callback investigation remain
deferred. Revisit eager literal rejection before streaming buffering/resumption.
