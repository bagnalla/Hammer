# RustHammer seeking design and verification

Status: implemented and proved on 2026-10-07. Public `Seek` uses the existing
`Grammar`/`Eval` interface and ordinary combinators. Production arithmetic,
evaluation, and an offset-based application have Lean correctness proofs. Native
tests, both library MIR stages, and the ordinary Cargo consumer exercise the
production implementation. The original private probe remains investigation
evidence, including the C characterization and unsupported callback spelling.

## Implementation decision

`Seek` is a backend-generic primitive alongside `SkipBits` and `Tell`.
The current execution interface already supports returning an earlier cursor;
seeking does not require a new interpreter, mutable input stream, or grammar
representation. The existing repetition, span, and ordering checks are preserved.
Span and match-comparison documentation now explains their endpoint semantics
when children seek backward. Seeking is included in the first-version API.

The [private probe](../rusthammer/probes/seeking/README.md) tests this design with
the actual library. It is investigation evidence, not an alternative production
parser or a temporary public API. No Aeneas/Charon changes or pin updates were
needed.

## C Hammer behavior

[`h_seek`](../src/hammer.h) accepts a signed **bit** offset and one of `SEEK_SET`,
`SEEK_CUR`, or `SEEK_END`. It changes the input position and returns that absolute
bit position as `TT_UINT`. The documented bounds are zero through end-of-input,
inclusive. Seeking does not read or validate the intervening bytes.

[`parse_seek`](../src/parsers/seek.c) waits for a final chunk before interpreting
an end-relative offset. Its offset arithmetic handles the signed minimum without
negating it. Its current/end bases still depend on C's machine-sized absolute
bit-position helpers and their assertion limits; Rust should continue using
`(byte, bit)` cursors instead of inheriting those representation limits.

The C characterization found two details that should not define Rust semantics.
The [C implementation issue log](../docs/c-implementation-issues.md) records
their causes, public-API reproducers, and C follow-up work:

- [C-002](../docs/c-implementation-issues.md#c-002-seeking-just-past-eof-can-succeed):
  `h_seek_bits` handles a target in the current byte before
  checking bounds. When already at EOF, it therefore accepts targets one through
  seven bits past EOF. For example, seeking to bit 1 of an empty final input
  succeeds. The probe reproduced 189 cases of this specific discrepancy.
- [C-003](../docs/c-implementation-issues.md#c-003-backward-seeks-produce-wrapped-child-lengths):
  the packrat backend computes a child's
  `bit_length` by unsigned endpoint subtraction. Seeking backward by eight bits
  gives that child `SIZE_MAX - 7` as its length. An action in the probe observes
  this value before a parent can replace it with the parent's net length.
  Backward match lengths are consequently unsuitable as a compatibility oracle.

Across 145,233 small complete-input cases, C agreed with the mathematical target
and bounds contract in 145,044 cases; the other 189 were the EOF cases above.
This comparison uses default ordering and valid starting cursors. It does not
claim compatibility with C's arbitrary mixed-direction scopes or streaming
buffer management. No C implementation changes were made.

## Public API

```rust,ignore
impl Seek {
    pub const fn to(target: Cursor) -> Result<Self, ConfigError>;
    pub const fn relative(offset_bits: isize) -> Self;
    pub const fn from_end(offset_bits: isize) -> Self;
}

impl<'input> Grammar<'input> for Seek {
    type Output = Cursor;
}
impl<'input, Backend> Eval<'input, Backend> for Seek { /* ... */ }
```

`Seek` is a `Copy`/`Clone` node with private configuration. `to` checks
`target.bit < 8`, returning `ConfigError::InvalidBitOffset` for a malformed bit
offset. Whether the target lies within a particular input is
checked during parsing. Every `isize` relative offset is valid configuration.

An absolute `Cursor` can address every normalized position in a `usize`-length
input, without converting the position to a machine bit count. It also accepts
the result of `Tell`. Relative offsets have the explicit `isize` range; larger
relocations can use an absolute cursor. The three constructors express the
useful C operations without integer origin tags. A negative start-relative
position is not a constructible absolute cursor.

Coordinates are relative to the supplied input slice. Its index zero is the
absolute origin, including when the caller deliberately supplies a subslice.
`Cursor.bit` is interpreted in the active bit direction. Seeking preserves
ordering and finality; restoring a saved cursor does not restore an earlier
ordering context or identify a different input buffer.

Success is `Success(target, target)`: the destination is both the continuation
cursor and the output. As with `Tell`, there is no allocation. The input bytes
are not accessed, and backend state is unchanged. The node supports arbitrary
backends through `Eval`, with no call to `parse` inside its evaluator.

Use the existing `Bind`/`TryMap` machinery for offsets decoded from input. The
consumer probe parses a byte displacement, seeks relative to the end of that
field, then returns a borrowed two-byte payload. Another example saves `Tell`'s
cursor, parses a byte, and seeks back, without an unchecked `unwrap` in parsing.

## Outcome and arithmetic contract

First validate the **entry** cursor, for every constructor and offset, including
zero. Invalid entries yield fatal `InvalidCursor`; an absolute seek does not
repair an invalid invocation. All following rules assume a valid entry:

| Condition | Result |
| --- | --- |
| End-relative seek on partial input | `NeedMore`, before calculating the target. |
| Mathematical target below zero | Recoverable `Mismatch`. |
| Target after the available buffer, partial input | `NeedMore`. |
| Target after the available buffer, final input | Recoverable `UnexpectedEnd`. |
| Target in bounds, including exactly EOF | `Success(target, target)`. |

The entry check has priority over end-relative incompleteness. For an
end-relative seek, waiting for finality applies to positive and zero offsets
as well as negative offsets. This follows C's evaluation order and the existing
conservative meaning of `NeedMore`; it does not promise a successful extension.

Out-of-range destinations are ordinary input rejection or incompleteness,
distinct from a malformed entry cursor. A relative underflow can therefore be
handled by `Choice`, `Optional`, or `Not`; extending the input cannot repair it.
An absolute target with `bit < 8` beyond the current buffer can become valid
after extension, including `(input.len(), nonzero_bit)`.

For the specification, use mathematical integers:

```text
position(c) = 8 * c.byte + c.bit
limit       = 8 * input_length
target      = position(configured_cursor)        [absolute]
            | position(entry) + signed_offset   [relative]
            | limit + signed_offset             [from end, final only]
valid(c)    = c.bit < 8 and position(c) <= limit
```

On success the destination is the unique normalized cursor at `target`, with
`0 <= target <= limit`. No assumption requires `limit` or `position(entry)` to
fit in `usize` or `isize`.

The implementation splits offset magnitude into whole bytes and a bit
remainder. It handles negative offsets with `(-(offset + 1)) as usize + 1`;
that expression is defined even for `isize::MIN`. Backward movement checks the
byte subtraction before performing it. Forward movement checks available space
before adding to the byte index. It never computes an absolute machine bit
position, signed position sum, or overflowing final byte index. These checks
are constant-time and independent of the distance moved.

## Composition audit

| Existing component | Consequence of seeking |
| --- | --- |
| `Grammar`, `Eval`, `Parser`, parser references | Their interfaces do not impose monotonic cursor movement. The primitive fits unchanged. |
| Sequence, output selection, `Bind`, transforms | Continue from the returned cursor, even when it is earlier. Child contracts carry the meaning of that movement. |
| `Choice`, `Optional`, `Xor` | Retry from their original cursor under the existing recoverable-error rules. Backend effects of attempted children remain; seeking adds no effects. |
| `And`, `Not` | Keep their original cursor after the child. `NeedMore` and fatal errors retain their current behavior. |
| Finite repetition and folds | Termination uses remaining permitted calls. Children may move backward, provided each child invocation terminates. |
| Unbounded repetition and folds | Every successful complete iteration must end strictly after its start. A child may seek backward internally and then finish ahead. Net empty/backward success still yields fatal `NonProgress`. |
| Separated repetition | The first item, then each whole separator/item pair, must advance when unbounded. A backward separator is permitted if its complete pair advances. |
| Permutation | The search's decreasing entry/candidate counts do not depend on cursor progress. No algorithm change is needed. |
| `WithSpan`, `Recognize` | Validate entry and exit, then require final position at or after entry. Preserve fatal `NonProgress` for a backward final cursor; allow an empty round trip. |
| `ButNot`, `Difference` | Keep comparing final cursors from a common start. Specify this as signed net displacement when seeking is involved. The ordinary consumed-length interpretation remains valid for forward matches. |
| `WithOrder` | Changed bit direction still requires aligned entry and successful exit. Seeking does not bypass either guard. |

A span describes the **interval between the wrapper's endpoints**, in its
enclosing bit direction. It is not a log of reads or seeks. For example, a parser
starting at byte 0 can seek to byte 3, read that byte, and seek back to byte 1.
Wrapping it produces `[0, 1)`, although its decoded value came from byte 3.
Conversely, seeking forward and reading a byte gives a span including the skipped
bytes. This extends the existing distinction between lookahead inspection and
net consumption. Callers needing the pointed-to field's span should wrap that
field parser after the seek.

For two normalized endpoints from a common entry, comparing their positions is
equivalent to comparing their **signed** differences from the entry. Thus
`ButNot(seek(-1), seek(-2))` can succeed at a sufficiently late entry, whereas
`ButNot(seek(-1), seek(0))` rejects. Do not interpret backward displacement using
natural-number subtraction or C's wrapped unsigned lengths. No additional
runtime validation or changed comparison algorithm is needed.

Future memoization must retain the actual returned cursor, including a backward
one, and bind cached results to the same input snapshot and relevant context.
A forward byte count is insufficient. Future live-streaming buffer reclamation
must also respect possible backward reads. Neither feature is needed for
seeking within the current immutable input snapshot. Recursive grammar support
remains deferred; seeking does not remove its termination obligations.

## Extraction evidence

The production verification runner includes all three constructors, the generic
evaluator, cloning, and the shared [offset example](../rusthammer/examples/support/offset.rs)
at both library MIR stages. Nine new ordinary Cargo-consumer roots cover absolute,
relative, and end-relative movement; the borrowed payload; spans; finite backward
folding; endpoint comparison; a custom backend; and saving/restoring `Tell`.
There are now 66 consumer roots. No extraction-tool changes were needed.

The following records the earlier private investigation, whose negative source
case is retained separately from the production verifier:

The two probe roots and nine ordinary Cargo-consumer roots pass Charon, Aeneas,
and strict Lean checking at promoted and optimized MIR. The checks reject
generated axioms, opaque declarations, and admits, and disable Lean's automatic
implicit variables. Native testing passes nine probe tests and two consumer
tests. Two source spellings needed adjustment in the consumer:

- `try_map(Tell, Seek::to)` encounters Aeneas's `Arrow types are not supported
  yet` diagnostic. `try_map(Tell, |position| Seek::to(position))` passes. The
  original form remains a separate negative root whose expected failure is
  checked at both MIR stages; it works in native Rust.
- `isize::from(offset)` for a `u8` initially introduced the unproved generated
  declaration `axiom Isize.Insts.CoreConvertFromU8.from`. The example uses the
  lossless `offset as isize` cast, which translates with the existing scalar
  model. The production application proof establishes the byte bound and the
  safety of multiplying that displacement by eight.

Neither adjustment changes the seek API or requires a tool patch.
These results do not establish support for every possible callback spelling.

## Lean proofs and integration

The existing generic specifications support the composition decisions above:
[`RepeatSpec`](../rusthammer/lean/RustHammer/RepeatSpec.lean) separates finite
chains from checked advancing iterations;
[`SpanSpec`](../rusthammer/lean/RustHammer/SpanSpec.lean) checks endpoints;
[`PermutationSpec`](../rusthammer/lean/RustHammer/PermutationSpec.lean) decreases
entry/candidate counts. The general endpoint-order theorem in
[`MatchProofs`](../rusthammer/lean/RustHammer/MatchProofs.lean) already needs only
normalized endpoints; its separate consumption corollary explicitly assumes
forward matches. No existing general theorem needs an unspoken global
forward-motion premise.

The production proof and implementation files are:

- [`position.rs`](../rusthammer/src/grammar/position.rs): private configuration,
  checked absolute construction, total movement, and backend-generic evaluation.
  Forward movement reuses `advance_cursor` with `SkipBits` and `Tell`.
- [`SeekSpec`](../rusthammer/lean/RustHammer/SeekSpec.lean): the independent
  mathematical destination/outcome relations above.
- [`SeekArithmetic`](../rusthammer/lean/RustHammer/SeekArithmetic.lean): total
  backward and signed movement for every machine length, raw cursor, and offset,
  including the signed minimum; all operations and casts are proved safe.
- [`SeekProofs`](../rusthammer/lean/RustHammer/SeekProofs.lean): constructor
  invariants, cloning, outcome classification, state-preserving generic
  evaluation, and the public direct entry point for every ordering context.
- [`SeekProperties`](../rusthammer/lean/RustHammer/SeekProperties.lean): exact
  successful destinations/output, final-input exclusion of `NeedMore`, the
  complete API, and successful absolute/current-relative contract stability
  under extension. Seeking itself depends only on length, not byte contents.
- [`OffsetSpec`](../rusthammer/lean/RustHammer/OffsetSpec.lean) and
  [`OffsetProofs`](../rusthammer/lean/RustHammer/OffsetProofs.lean): the shared
  displacement-field application, including lossless conversion/multiplication,
  total composition, payload contents, alignment, and the exact final cursor
  under default ordering, for both input statuses.
  Lean slices model contents; native tests additionally check borrow identity.
- [`MatchProofs`](../rusthammer/lean/RustHammer/MatchProofs.lean): endpoint ordering
  equals signed net-displacement ordering, including backward results.

Production tests include exhaustive small positions and offsets, virtual machine
limits without huge allocations, and composition with lookahead, backtracking,
spans, repetition/folds, permutation, ordering scopes, and custom backends. The
application tests cover all 256 displacement bytes and every truncation boundary.
Both allocation configurations run in `tools/verify.py`. That command also
regenerates Lean, checks downstream extraction, and audits the new 22 theorem
roots; the combined selected-root audit now contains 178 theorems.
