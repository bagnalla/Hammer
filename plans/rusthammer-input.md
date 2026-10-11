# RustHammer input, byte ordering, and spans

Status: v1 input, byte-order, and span implementation and proofs migrated.
The [MAVLink 2 target](rusthammer.md#target-application-mavlink-2-packet-parsing)
uses complete inputs, high-first bit traversal, and little-endian numeric fields.
High-first-only traversal and forward successful consumption are adopted v1
constraints. This plan supersedes the baseline's configurable bit direction and
changed-direction scope guards. Historical proof/probe evidence remains below.
Retired probe runners and their recorded commands are preserved at `c5c2643`;
see the [checkout instructions](../rusthammer/probes/README.md#historical-probes-and-reproduction).

## Compatibility and motivation

Retain `(byte, bit)` cursors, typed outputs, static dispatch, independently
borrowed immutable input, `no_std`, and separate configuration and parse errors.
V1 still supports unaligned and cross-byte bit fields; it is not restricted to
byte-only grammars. Complete input means the supplied bytes are all the input for
this invocation. Prefix parsing remains valid; `End` explicitly requires EOF.

Transport buffering precedes parsing. MAVLink's intentional trailing-zero payload
omission does not make its fully received frame a partial input; its transmitted
header specifies the payload length. Message-specific reconstruction is separate.

C Hammer's [bit reader](../src/bitreader.c) and
[endianness wrapper](../src/parsers/endianness.c) support more general bit order.
V1's Lean contracts specify the high-first subset. Historical C comparisons
helped establish these semantics; their infrastructure is now retired. Any
promised compatibility belongs in the contracts. Low-first behavior is excluded.
The earlier two-ended cursor proposal and baseline direction-change guards
remain historical designs, not implementation prerequisites.

## Numeric ordering

Bit traversal is fixed: consume the high, then lower bits of each physical byte.
`ByteOrder::{Big, Little}` determines the significance of successive physical-byte
fragments of a numeric field. Big remains the default. Preserve the existing
high-first behavior for both byte orders, including arbitrary supported field
widths and unaligned starts.

Partition a field at physical byte boundaries. Take its requested high-first
fragments and interpret each with ordinary numeric bit significance. Big byte
order appends later fragments below the accumulated value; little byte order
places them above earlier fragments. Byte order still matters for unaligned
fields and widths that are not multiples of eight. Changing byte order never
changes which physical bits the cursor denotes.

An aligned 8-bit read of `0x61` yields `0x61` in both byte orders. The first
high-first 5-bit field from that byte is `12`. MAVLink's aligned 24-bit ID and
16-bit checksum use little byte order; its CRC's internal shifts do not require
another parser bit direction.

Remove `BitOrder` entirely rather than leaving an enum with one variant or an
always-high argument. Replace combined `Order`/`ParseContext` with `ByteOrder`
and replace `WithOrder` with `WithByteOrder`.

## Cursor and context

Keep `Cursor { byte, bit }`, with `bit < 8` counting consumed high bits.
Exhausting a byte increments `byte` and resets `bit` to zero. A cursor is valid
when `bit < 8` and either `byte < input.len()` or it is exactly
`(input.len(), 0)`. The canonical EOF cursor remains byte-aligned.

The unread physical interval within a byte, in LSB-numbered indices, is always
`[0, 8 - cursor.bit)`. No bit-direction context is needed to interpret a saved
cursor. It remains relative to its input slice; the type does not track input
identity or bounds.

The target interpretation parameter is:

```rust,ignore
pub enum ByteOrder { Big, Little }
// Parser::parse_with(input, cursor, byte_order) -> Result<(Cursor, Output), ParseError>
// Parser::parse(input, cursor) supplies ByteOrder::Big.
```

The [single parser trait](rusthammer.md#parsing-interface) takes input and cursor
separately, with no finality, mutable backend, or reporting state. Remove
`InputStatus`, `ParseOutcome`, `NeedMore`, and complete-outcome conversions.
Exhaustion is recoverable `UnexpectedEnd`, following the old final-input rules.
Preserve invalid-cursor/error precedence and existing zero-width/empty behavior.

### Position and progress

Use unbounded positions in Lean:

```text
position(cursor) = 8 * cursor.byte + cursor.bit
```

Rust compares `(byte, bit)` lexicographically and advances with checked byte/bit
arithmetic, avoiding a machine-sized absolute bit count. From a valid entry, a
supported successful parser returns a valid cursor at or after that entry.
Document this law for custom parsers and `Bind` results, and use it as an explicit
premise when proving generic combinators. The Rust trait alone cannot establish
it for arbitrary implementations.

Choice can retry its entry cursor, and lookahead can restore it; neither returns
before its own invocation entry. Finite repetition may accept empty success.
Unbounded repetition additionally enforces strict progress for each whole
successful iteration. Retain current invalid-cursor and `NonProgress` checks;
no universal entry validation is introduced for empty grammars.

`Seek` is excluded, including forward and end-relative variants. `SkipBits`
remains the advancing/discarding operation and `Tell` the validated position
reader. Match restrictions compare endpoints from a shared start, corresponding
to nonnegative consumed lengths under the supported parser contract.

## Ordering scopes

The target wrapper is `WithByteOrder { parser, byte_order }`. It calls its child
with the selected `ByteOrder` and returns that child's result. Sequencing still
passes its enclosing byte order to the next child. Nested scopes can override it
again. Parser copying remains conditional on the stored child.

Byte-order changes impose no alignment or cursor checks beyond the child. Remove
all changed-bit-direction entry/exit guards and their helpers. Unaligned fields
remain supported inside byte-order scopes. `TakeAligned` still enforces its own
alignment requirement; removing scope guards does not add implicit padding.

The scope proof becomes delegation plus restoration of the enclosing argument,
with no direction-change cases. The [direct-v1 probe](../rusthammer/probes/direct_v1/README.md)
checks `ByteOrder`/`WithByteOrder`, unaligned scopes, and borrowed spans through
both MIR stages and ordinary dependency use. The production semantics and proofs now use the same interface, without old
wrapper aliases or hidden bit-order parameters.

## Primitive and combinator policy

| Family | V1 behavior |
| --- | --- |
| `Bit`, `Bits`, `SignedBits`, `Literal` | Read high-first bits with the active byte-fragment order. Sign extension follows unsigned assembly. |
| `Byte`, `I8`, byte sets/ranges | Decode a contextual 8-bit field, including unaligned starts. |
| `BytePattern` | Match contextual 8-bit fields; retain the pattern's independent lifetime. |
| `BeU16/32/64`, `BeI16/32/64` | Pin big byte order; high-first traversal is universal. Little-endian reads remain available through byte-order scopes. |
| `TakeAligned` | Require `bit == 0` and borrow raw bytes without decoding or implicit alignment. |
| `SkipBits`, `Tell`, `End` | Retain validated forward arithmetic, position reporting, and exact EOF behavior, including zero-count validation where already required. |
| `Seq`, selection, maps, predicates, `Bind` | Pass byte order to children and preserve success-only callback and ownership rules. |
| `Choice`, `Optional`, `And`, `Not` | Retain final-input rollback/rejection rules and fatal-error propagation. |
| `ButNot`, `Difference`, `Xor` | Retain output/selection rules and endpoint comparison under forward child contracts. |
| Repetition and folding | Retain count, progress, overflow, and separator rollback rules. |

## Matched-input spans

With one physical bit direction, spans need only input and endpoints:

```rust,ignore
pub struct BitSpan<'input> {
    input: &'input [u8],
    start: Cursor,
    end: Cursor,
}
```

The target constructor is
`BitSpan::new(input, start, end) -> Result<BitSpan, ParseError>`.
Require valid endpoints and `start <= end`; allow empty spans. Preserve private
fields and `input()`, `start()`, `end()`, `is_empty()`, and `as_bytes()` accessors.
Remove the bit-order argument, stored field, and accessor. Byte order does not
affect which source bits a span denotes and need not be stored either.

Within one byte, the selected physical interval is
`[8 - end.bit, 8 - start.bit)`. Across bytes, select the unconsumed low portion of
the first byte, all interior bytes, and the consumed high portion of the final
byte. Reuse the baseline's high-first geometry, injectivity, and length proofs.
Remove low-first branches and mixed-direction obligations from the active model.

`as_bytes()` requires aligned endpoints and borrows the original bytes for the
input lifetime. Empty aligned spans yield `Some(&[])`; unaligned spans yield
`None`. Keep bounds, geometry, and borrow-content proofs. No scalar machine bit
length or iterator is added by this migration.

`Recognize<P>` returns the span after fully running and discarding the child
output; `WithSpan<P>` returns `(P::Output, BitSpan<'input>)`. Both use direct
`parse_with` under the enclosing byte order. Entry validation precedes the child,
and exit validation applies to success. Keep defensive `InvalidCursor` and
backward-exit `NonProgress` errors, even though verified supported children obey
the forward-consumption law. Bounds errors retain precedence over backward exits.

Spans describe the interval between endpoints, not a trace of inspected bytes.
Lookahead can inspect beyond its returned cursor, and `SkipBits` can consume
without reading. CRC validation can inspect a span's byte view without moving
the parser cursor; no seeking capability is needed.

## Current implementation and evidence

The production core uses `Result`, `ByteOrder`, and direct `Parser` execution.
`WithByteOrder` delegates without guards; spans store only input and endpoints.
High-first decoding and geometry, both byte orders, unaligned fields, raw-cursor
errors, forward consumption, and retained application contracts are proved.
The [main verification record](rusthammer.md#verification-and-proof-maintenance)
tracks the migrated roots, retired claims, and current checks.
Arbitrary-byte-order parser proofs now live in their numeric, byte, and position
family modules; default-order proofs specialize them. For example, the
[integer proofs](../rusthammer/lean/RustHammer/IntegerProofs.lean) share one pair
of narrowing helpers for signed and unsigned values.

## Historical pre-v1 implementation and evidence

This section records the pre-v1 ordering increment. References to finality,
backend support, low-first fields, direction-change guards, and then-planned
spans are historical, not v1 requirements.
The implementation and proof migration is tracked at the end of this document.

The baseline library implements `BitOrder`, `ByteOrder`, `Order`, `ParseContext`, and
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
and arithmetic safety. At that point, `OrderParserProofs` covered every order and
finality, including signed/native narrowing, literals, patterns, and byte sets.
[Scope proofs](../rusthammer/lean/RustHammer/OrderScopeProofs.lean)
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

Reproduce these baseline results from `rusthammer/` in a checkout of `c5c2643`:

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

Historical probe results follow; reproduce old API-dependent fixtures against
`c5c2643`. Their runners have been removed from the current tree.

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
existing default application theorems; production spans now have separate
physical-geometry and parser contracts as described above.

## Earlier unrestricted probe

The isolated [`input_order.rs`](../rusthammer/probes/input_order.rs) and its
runner (`tools/check_input_order.py` at `c5c2643`) preserve the superseded
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

The [main migration sequence](rusthammer.md#first-version-scope-and-next-steps)
implements the following input, ordering, and span changes:

1. Retain `Cursor`, `ByteOrder`, and `BitSpan`. Remove finality/outcome wrappers,
   `BitOrder`, combined `Order`, and direction stored in spans. Use `Result` and
   a direct `ByteOrder` argument; preserve the default high-first/big behavior.
2. Simplify numeric readers to the high-first path, retaining both byte orders,
   unaligned/cross-byte fields, invalid-cursor and exhaustion precedence, and
   zero-width validation. Replace `WithOrder` with `WithByteOrder` delegation.
3. Remove `Seek` and direction-change guards. Preserve shared forward cursor
   arithmetic for `SkipBits`, `Tell`, readers, and repetition. Keep defensive
   span endpoint checks and simplify construction/accessors and physical geometry.
4. Port high-first mathematical models and extracted-code contracts. Prove the
   supported forward-consumption law compositionally under child contracts.
   Retire low-first, changed-direction, seeking, and offset-application roots;
   preserve their baseline evidence at `c5c2643` rather than adding v1 adapters.
5. Migrate retained tests, examples, and downstream fixtures. Check both byte
   orders and high-first boundary cases, payload borrowing, all MAVLink truncation
   boundaries, exact frame consumption, and CRC validation. Scope guards and
   low-first tests no longer describe supported behavior.

The earlier ordering probes are historical evidence. The new direct-v1 probe
checks representative source forms through both MIR stages and ordinary
dependency extraction, with strict Lean checking. The production verifier now regenerates the migrated core, builds its retained
proofs, and audits the selected theorem roots. Reproduce the earlier probes
against `c5c2643` when they import retired interfaces.
