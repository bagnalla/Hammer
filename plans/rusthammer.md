# RustHammer version 1: design and verification plan

Status: v1 core migration implemented on `rusthammer-v1-simplify`, branched
from `rusthammer-dev` at `c5c2643` (`Before simplification`). Plans were committed
at `3052099`; the extraction probe was committed at `8c08046`. The retained Rust
implementation, examples, Cargo consumer, generated Lean, and proofs now use the
single direct parser interface, complete inputs, and high-first traversal.

RustHammer is a typed Rust parser-combinator library whose implementation is
translated through Charon and Aeneas and verified in Lean. Version 1 supports
**direct execution of nonrecursive grammars over complete immutable inputs**.
**MAVLink 2 packet parsing is the target application for version 1.** Use its
requirements to choose the initial library scope and demonstrate verification
on a real format. RustHammer remains a reusable combinator library; MAVLink
grammar and dialect data stay in application/example code.
The user's scope decision supersedes earlier requirements to retain a generic
backend boundary, partial-input support, low-first bit traversal, permutation,
seeking, or first-version diagnostic annotations. Preserve the verified behavior
of retained capabilities and simplify their execution and proof interfaces.

The [previous main plan](rusthammer-pre-v1.md) preserves the earlier designs,
implementation history, and verification evidence. Historical probe results are
not evidence that the new interface has already been extracted or proved.

## Resume here

The simplified core and retained proofs are migrated. The
[README](../rusthammer/README.md) and [overview](../rusthammer/OVERVIEW.md) describe
the current implementation. The [direct-v1 probe](../rusthammer/probes/direct_v1/README.md)
remains the record of supported source forms and remaining extraction failures.

Next is the v1 application/release scope review: select dialect/message metadata,
decide whether unsigned framing is sufficient for the first release, and review
packaging and supported environments. Typed payloads or signature-field parsing
would be separate verified increments; cryptographic authentication remains an
application responsibility. No deferred backend, streaming, diagnostic,
permutation, seeking, float, or recursion work gates this review.

| Document | Role in v1 |
| --- | --- |
| [Combinator plan](rusthammer-combinators.md) | Retained families, construction policy, complete-input control flow, and migration inventory. |
| [Input plan](rusthammer-input.md) | Complete buffers, high-first bits, byte order, forward consumption, and matched spans. |
| [Seeking plan](rusthammer-seeking.md) | Deferred capability, baseline evidence, and removal from the v1 build/proof surface. |
| [Diagnostics investigation](rusthammer-diagnostics.md) | Deferred reporting research; no production hooks or reporting state in v1. |
| [Backend research](rusthammer-backends.md) | Historical boundary and deferred packrat research; no v1 compatibility requirement. |
| [Recursion research](rusthammer-recursive-rules.md) | Deferred construction and extraction investigations, outside v1. |
| [Prototype README](../rusthammer/README.md) and [overview](../rusthammer/OVERVIEW.md) | Document the current direct-only implementation and proof coverage. |
| [Compatibility probes](../rusthammer/probes/README.md) | Reproductions and known limits of the pinned tools. |
| [Direct-v1 probe](../rusthammer/probes/direct_v1/README.md) | Completed interface/extraction check; supported forms and remaining failures, without new correctness proofs. |

## Target application: MAVLink 2 packet parsing

The starting point is the shared [MAVLink grammar](../rusthammer/examples/support/mavlink.rs),
its [native tests](../rusthammer/tests/mavlink.rs), and the extracted framing/CRC
proofs. The current example parses unsigned frames, borrows the transmitted
payload, validates the checksum using a caller-supplied dialect `CRC_EXTRA`
lookup, and returns the cursor after the frame. HEARTBEAT is a reference fixture,
not a requirement to support only message ID zero; preserve the full 24-bit ID
and the ability to supply other dialect lookups.

The [MAVLink serialization specification](https://mavlink.io/en/guide/serialization.html)
describes byte-aligned fields and little-endian multibyte values. Payload field
order is fixed by the message definition's serialization rules. Its reordering
from XML declaration order is not an arbitrary-order parsing problem. Low-first
bit traversal is unnecessary. Protocol-defined trailing-zero payload omission
is valid serialization, distinct from an incomplete frame on the transport.

For the initial verified framing milestone, preserve:

- Header decoding, declared payload length, full message ID, compatibility flags,
  and the existing checks on supported incompatibility flags and sender IDs.
- Borrowed payload contents and exact successful consumption. Prefix parsing
  supports consecutive frames in an already buffered input; `End` remains the
  explicit requirement for a buffer containing exactly one frame.
- CRC validation over the actual transmitted header/payload bytes, excluding the
  magic byte and including the dialect's extra byte. Keep the independent CRC
  specification and the lookup contract; do not silently skip unknown IDs or
  weaken checksum validation to simplify extraction.
- Rejection of truncated frames, corruption, and unsupported
  configurations, with Rust tests and proofs for the actual shared parser source.
- Allocation-free execution and payload borrowing. Keep the parser's necessary
  length-dependent composition, byte reads, little-endian numeric reads, spans,
  and predicates as ordinary reusable library capabilities.

The current example is not a complete MAVLink implementation: it rejects signed
frames and does not decode message-specific payload fields. Select the supported
dialect/messages and any expansion into payload or signature-field decoding
explicitly before describing v1's protocol coverage. The application target
alone does not make these unimplemented capabilities part of the existing proof
claim.

Three boundaries matter when deciding the application scope:

- **Transport:** a caller or separate adapter must assemble enough bytes before
  invoking the complete-input parser. A transport read is not necessarily a
  complete packet. Buffering, resynchronization, and live reception are separate
  from the parser's success/error interface.
- **Payload decoding:** preserve transmitted bytes during framing. A later
  typed decoder must handle dialect layouts and omitted trailing zeros. Native
  float support can remain deferred for framing, but selected message decoders
  may require floats or an explicitly specified raw-bit representation; MAVLink
  message definitions include [floating-point fields](https://mavlink.io/en/guide/define_xml_element.html).
- **Signing and authentication:** cryptographic signing/verification, key
  management, and replay protection belong to application code, outside the v1
  combinator library. The current unsigned example continues to reject signed
  frames. Any later signature-field parser must distinguish parsing those bytes
  from establishing the [authentication contract](https://mavlink.io/en/guide/message_signing.html).
  Application validation can run after parsing or through a callback with its
  own contract; core proofs do not establish arbitrary callback correctness.
  C Hammer provides the analogous generic [predicate hook](../src/hammer.h),
  while its [NTP example](../examples/ntp/ntp.c) merely parses authentication fields.

### Adopted simplifications

These are v1 scope decisions, not optional migration candidates. The excluded
features remain documented as baseline or deferred research; do not port them
into the simplified production library or add placeholder extension points.

| Decision | Fit for the target and consequence |
| --- | --- |
| Defer diagnostic annotations | Ordinary parse errors support framing/CRC validation. Exclude reporting state, scope hooks, labels, and diagnostic metadata extraction from v1. |
| Defer permutation | Fixed header and schema-defined payload order need no search over permutations. Remove the node, entry wrappers, search machinery, and v1 proof/extraction roots. |
| Fix bit traversal to high-first | Keep little-endian reads for the 24-bit ID and 16-bit checksum. Remove `BitOrder`, changed-direction scopes/guards, and direction stored in spans. CRC arithmetic remains unchanged. |
| Defer seeking; require nondecreasing successful cursors | Parse frames in order and validate CRC from a borrowed region. Retain internal rollback for choice/lookahead and specify the forward-consumption law for custom parsers. |
| Document supported extraction forms | Retain typed borrowed outputs and `Bind`. Check the callback/adapter forms used by the target; do not promise extraction of every valid Rust callback. |
| Keep authentication in application code | No built-in cryptographic signing, verification, key store, or replay state. Parsing signature fields and validating a CRC do not establish sender authentication. |

Direct-only execution and complete-input results remain confirmed. Recursion,
packrat, and native floats are unnecessary for the current framing grammar.
Native float decoding remains outside v1; a later expansion into typed payloads
must specify its numeric representation separately.

## Version 1 scope

Retain:

- Typed outputs, static dispatch, independently borrowed input/configuration,
  and outputs that need neither `Copy` nor `Clone`.
- Concrete grammar nodes and construction helpers; construction runs no parser
  or callback. Conditional parser `Copy`/`Clone` and shared references remain.
- `no_std`, safe Rust, optional `alloc` for collected outputs, and allocation-free
  folding and MAVLink framing.
- High-first bit parsing, including unaligned/cross-byte fields, and big/little
  byte order. Signed fields, literals, byte patterns/sets, typed ranges, validated
  configuration, and aligned borrowed byte reads remain.
- Sequence and output selection, ordered choice, optionality, lookahead,
  transformations/predicates, `Bind`, and match restrictions.
- Exact/bounded/unbounded repetition, collection, folding, and separated lists,
  with existing count, progress, ownership, and error rules.
- Byte-order scopes, spans/recognition, `SkipBits`, `Tell`, and explicit `End`.
  Successful parsing from a valid entry preserves cursor validity and never
  returns before that entry; empty success remains allowed where specified.
- Retained shared application examples and proofs, particularly unsigned MAVLink
  2 framing, length-dependent borrowed payloads, and CRC validation.

Remove from the v1 design and implementation:

- Backend selection, `Eval<'input, Backend>`, `Direct`, mutable generic backend
  plumbing, backend-specific implementations, and backend-only tests.
- The separate output-only `Grammar` trait in favor of one parser trait. The
  focused extraction/inference probe supports this shape.
- `InputStatus`, `ParseOutcome`, `NeedMore`, retry/finality classification, and
  complete-outcome conversion wrappers. Use `Result` throughout parsing.
- `ParseContext`, combined `Order`, `BitOrder`, and `WithOrder`. Pass `ByteOrder`
  directly and replace the scope with `WithByteOrder`; retain the existing
  high-first/big default. Remove bit-direction fields/accessors from `BitSpan`.
- `Permutation`, `Required`, `permutation`, `required`, and their dedicated
  tuple/search machinery. Keep `Optional` for ordinary optional parsing.
- `Seek`, its exclusive configuration/error machinery, and the offset-seeking
  example from the v1 API, examples, extraction roots, and active proof build.
  Preserve arithmetic still used by `SkipBits`, `Tell`, and readers.
- Diagnostic annotations, observer/reporting hooks, and reporting state. These
  have no production implementation to migrate; retain the investigation only.
- Partial-input/state-erasure proof adapters and obligations specific to the
  excluded features. Preserve retained complete-input claims in the new layers.

No compatibility aliases, disabled production features, dummy state, or
always-high bit-order parameters are required. This is an experimental API on a
new branch. Deferred features may require a later design and API migration.

Recursion, packrat, other engines, streaming, native floats, diagnostics,
permutation, and seeking are outside v1. Cryptography and authentication policy
remain application responsibilities. CI and the broader borrowed-callback
investigation remain deferred. Deferred actions and dedicated dispatch remain
omitted; named parse-local application-value storage remains outside v1.
Small length/count/whitespace conveniences are separate scope choices after
migration, not prerequisites for the target framing parser.

## Parsing interface

The target interface checked by the focused probe is:

```rust,ignore
pub trait Parser<'input> {
    type Output;

    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError>;

    fn parse(
        &self,
        input: &'input [u8],
        cursor: Cursor,
    ) -> Result<(Cursor, Self::Output), ParseError> {
        self.parse_with(input, cursor, ByteOrder::Big)
    }
}
```

This is the implemented public interface, checked by the probe and production verifier.
`parse_with` is the execution operation implemented by primitives, combinators, custom
parsers, and reference forwarding. Every child call uses it with the active
byte order; `parse` supplies big byte order. Bit traversal is always high-first.
`WithByteOrder { parser, byte_order }` overrides byte order for its child without
alignment guards. This retains the useful byte-order scope and removes the
combined context; per-reader-only byte order is not part of this migration.
Construction helpers continue to return concrete nodes. Use `Parser` bounds
where output relationships or callback inference require them, without adding
bounds to constructors that
only store fields. The probe checks all seven generic construction helpers and
their representative uses without retaining `Grammar`.

Keep the input slice separate from the cursor and parser reference so outputs
can borrow input independently. A factory may return a concrete node with an
opaque callback, or `impl Parser<'input, Output = T>` when that is its intended
contract. There is no backend capability to preserve through that return type.
Unlisted `Copy`/`Clone` bounds and lifetime relationships still matter.

V1 parsing has no mutable execution-context parameter. Local values, explicit
outputs, and callbacks provide the required composition. Add no observer, label
storage, crypto state, or empty state wrapper for deferred capabilities.

The supported extraction contract covers the retained generic combinators and
checked concrete applications with the pinned tools. Keep named adapters for
borrowed-output callback forms that still fail. Record which callback shapes
pass both MIR stages and downstream use; a Rust-valid callback is not guaranteed
to translate or to satisfy the child/callback contracts needed by the proofs.

## Complete-input semantics

Complete input means the supplied slice is all the input for this invocation.
It does **not** require every successful parser to consume the entire slice.
Keep returning the next cursor; compose `Left { first: parser, second: End }`
when a grammar requires EOF. Truncated packets are ordinary rejection, and
callers do not receive a suspension result or continuation.

The migration's semantic reference is the baseline's **final-input, high-first**
behavior for retained parsers under the same byte order, cursor, configuration,
and callback contracts. Preserve decoded values, successful cursors, error
precedence, child/callback order, and cleanup within the selected scope. Removing
unsupported modes is not an opportunity to change unrelated parsing policy.

| Case | V1 behavior |
| --- | --- |
| A primitive needs unavailable bits/bytes | Recoverable `Err(UnexpectedEnd)`. |
| `End` at a valid `(input.len(), 0)` | Success; otherwise retain `TrailingInput` or invalid-cursor rejection as appropriate. |
| `Choice` first arm rejects recoverably, including `UnexpectedEnd` | Try the second arm from the original cursor and order. |
| `Optional` child rejects recoverably | Succeed with `None` at the original cursor. |
| Repetition rejects recoverably | Finish if its minimum is met; otherwise propagate the error. A rejected separator/item pair leaves its separator unconsumed. |
| `And` / `Not` | Retain current final-input assertion and cursor-restoration rules. |
| Fatal cursor, alignment, progress, or count error | Propagate through choice, lookahead, optionality, and repetition. |

Retain existing zero-consumption contracts: some empty grammars do not validate
an unused cursor; input-reading primitives and validated positional operations
do. Removing partial input does not mean removing unaligned bit parsing.
Byte-order scopes do not change physical bit traversal and impose no alignment
guards. `TakeAligned` still requires byte alignment. A span remains an endpoint
interval, not an execution trace.

Backtracking restores cursor/order, not arbitrary effects performed by custom
parsers or callbacks. `Fn` does not guarantee purity or termination. Proofs must
continue to state the contracts needed for those calls. Unbounded repetition
must strictly advance after each successful whole iteration; finite repetition
can terminate by its count even with empty successes.

### Forward-consumption contract

For a valid entry cursor, a supported parser's successful result has a valid
cursor at or after the entry. Compare `(byte, bit)` lexicographically; use
unbounded positions only in specifications. This law covers custom parsers and
parsers constructed by `Bind`, and must appear in their verification contracts.
It is not enforced by the Rust trait alone. Preserve current defensive cursor
and progress checks rather than assuming arbitrary implementations are proved.

Choice retries from its own entry, and lookahead returns to its entry; both obey
the law. Empty success is nondecreasing. Unbounded repetition separately requires
strict progress for each whole successful iteration. Existing zero-count and
empty-parser behavior on invalid entries is not silently changed by this law,
whose premise is a valid entry. CRC callbacks can reread a borrowed input region
without changing the parser cursor or requiring `Seek`.

## First-version scope and next steps

1. **Plan revision — complete.** Direct-only/complete-input semantics, the MAVLink
   target, retained capabilities, exclusions, proof obligations, and deferred
   research are recorded in this plan and its supporting documents.
2. **Extraction probe — complete.** The [probe report](../rusthammer/probes/direct_v1/README.md#results)
   records single-trait inference, `Result`, reference forwarding, opaque returns,
   method-local callbacks, owned/borrowed outputs, `Bind`, byte-order scopes, and
   adapted MAVLink framing/CRC through both MIR stages and a Cargo consumer.
   Controls retain the distinct borrowed-callback and cleanup failures.
3. **Rust and callers — migrated.** All retained families, shared examples, native
   tests, extraction roots, and consumer entries use direct `Parser` calls and
   ordinary results. Excluded APIs and their dedicated fixtures are removed.
   The tests retain complete-input/high-first behavior, callback and drop timing,
   borrow identity, error precedence, and empty/raw-cursor boundaries.
4. **Specifications and proofs — migrated.** Generated code is regenerated from
   Rust. Retained decoding, ordering, span geometry, repetition/fold, constructor,
   match, record, and MAVLink proofs build. Backend state projections and result
   finality conversions are gone. `ParserSpec`/`ParserProofs` hold direct contracts;
   `Spec.satisfies` is an ordinary result-witness relation, with no input status or
   outcome conversion. `ForwardProofs` establishes cursor preservation under
   explicit child/factory contracts and for the MAVLink frame relation. CRC model
   and implementation proofs remain unchanged.
5. **Verification and documentation — complete.** The production verifier covers both
   allocation configurations and MIR stages, ordinary downstream extraction,
   strict Lean compilation, and selected theorem axiom checks. C comparisons
   cover retained primitive/match semantics and high-first ordering. Current
   results are recorded below; no retired feature is counted as verified v1 code.
6. **Application/release scope review — next.** Select supported MAVLink metadata
   and review whether more application coverage is needed, then public API,
   callback support, resource assumptions, packaging, and supported environments.
   New capabilities require their own specification and verification increment.

A temporary baseline checkout may help compare native behavior; it must not
become a second implementation shipped in the crate. Retained research probes
that import removed APIs need either a direct-only port (when still useful to
v1), or an explicit instruction to reproduce against `c5c2643`. Do not keep the
old interface in production just to keep deferred research runners working.

## Verification and proof maintenance

The baseline includes verified flags, marker, record, dependent-count, offset,
and MAVLink examples. Recorded baseline checks cover 246 tests without `alloc`,
281 with `alloc`, 66 downstream entry points, and 200 selected theorem axiom
audits. These are baseline results, not claims about a migrated implementation.
Test and theorem counts may shrink when excluded capabilities are removed;
acceptance depends on retained semantic coverage, not matching those counts.

The migrated implementation passed the production verifier on 2026-10-10 with
the pinned tools below:

- Native tests: 213 without `alloc` and 247 with `alloc`, including 35 and 40
  doctests respectively; downstream consumer tests: 22 and 25 respectively.
- Library extraction through promoted and optimized MIR, and 51 ordinary Cargo
  consumer extraction roots, including shared MAVLink framing and CRC validation.
- Full Lean proof build and additional generated-code checks with warnings as
  errors and `autoImplicit=false`; 131 selected theorem axiom audits passed using
  only standard Lean axioms, with no project admissions or opaque stand-ins.
- C comparisons: 577,065 primitive cases, 1,879,635 match cases, 50,530 high-first
  ordered-field cases, and 1,144 nested byte-order scope cases, all passing.

These results cover the retained v1 implementation. The independent MAVLink CRC
specification and implementation proof files are unchanged by the migration.

| Existing proof area | Migration obligation |
| --- | --- |
| `DirectState`, `Direct`, `DirectEquations`, `BackendProofs` | Replace state projection and generic-backend contracts with direct parser equations/contracts. Retain child order and recoverable rollback claims. |
| `PartialSpec`, `PartialProofs`, `CompleteProofs`, partial record specifications/proofs | Port useful final-input semantics to result-based relations; remove incompleteness, finality conversion, and impossible-`NeedMore` lemmas. |
| Primitive, byte-order, span, match, constructor proofs | Preserve high-first value/cursor/error claims and validation precedence. Simplify byte scopes and span geometry; prove forward consumption under child contracts. |
| Repetition, folds, separated lists | Preserve termination, progress/count arithmetic, ownership, rollback, and short-circuiting under complete-input child contracts. |
| Permutation/tuple, seek/offset, and low-first/scope-guard proofs | Retire from the v1 build and theorem audit with their excluded source. Retain baseline research/history; preserve shared arithmetic and retained high-first claims. |
| Shared applications | Reprove retained extracted parsers, including truncated frames, borrowed payload contents, and exact consumption. Retire the offset-seeking example rather than adding a substitute seek API. |
| MAVLink CRC | Retain the independent CRC model and implementation proof; port framing composition and success/error properties without weakening checksum validation. |

The proof retirement inventory is explicit:

- Delete `DirectState`, `Direct`, and `DirectEquations`; generated parser methods
  now execute directly. `BackendProofs.seq_eval_spec` and `choice_eval_spec` are
  replaced by direct `ParserProofs` contracts. Constructor sequencing is now
  `Constructors.seq_parse_spec`.
- Rename `PartialSpec`/`PartialProofs` to `ParserSpec`/`ParserProofs`; retain their
  complete-input combinator claims. Retire `classify_*`, incomplete propagation,
  and impossible-`NeedMore` lemmas. Result-witness lemmas replace finality adapters.
- Retire `PartialRecordSpec`/`PartialRecordProofs`. Their complete-input header,
  marker, and record claims remain in `RecordProofs` and `ControlProofs`; their
  partial-input/EOF-waiting claims are outside v1.
- Delete `PermutationSpec`, `PermutationProofs`, `PermutationTupleProofs`,
  `SeekSpec`, `SeekArithmetic`, `SeekProofs`, `SeekProperties`, `OffsetSpec`, and
  `OffsetProofs`. Preserve shared forward arithmetic and the general match
  endpoint/displacement theorem and audit.
- Remove `BitSpan.bit_order`, low-first span geometry, `fragment_offset_spec`,
  ordered-bit direction cases, and scope guard/state theorems. High-first bit
  proofs remain in `Proofs`/`CompleteProofs`; byte-order decoding remains in
  `Order*`; transparent scoping is `Ordering.with_byte_order_spec`.
- Preserve all substantive MAVLink framing, payload, checksum, constructor, and
  success/truncation contracts. Only status/guard helper lemmas and impossible
  incomplete outcomes are retired. The two CRC files are unchanged.

The exclusions intentionally remove tests and theorem roots for permutation,
seeking/offset applications, low-first order, and input/backend modes. Document
those removals; they are scope changes, not passing verification results for the
retired features. Keep the proof/extraction checkers strict for everything left.

Do not mechanically delete a file merely because its name contains `Partial`:
several contain the general semantics on which complete parsing currently
rests. Prefer a direct result-based proof layer over a permanent encoding of
`Result` back into the removed outcome type. Generated code comes from Rust;
never hand-edit `lean/RustHammer/Rusthammer.lean` or replace unsupported bodies
with axioms, admissions, or opaque stand-ins.

For a completed production increment, from `rusthammer/`:

```sh
python3 tools/verify.py --aeneas-dir /path/to/pinned/aeneas
```

The available matching checkout in this workspace is
`/home/alex/source/rosette/aeneas`. If using the existing local Lake package
override, append `--lean-packages target/mavlink/lean-packages.json`; that ignored
file is machine-local, not a prerequisite for a fresh checkout. `lake build`
from `rusthammer/lean/` checks proofs without regenerating Rust extraction.

The verifier must continue to check formatting, Rust tests with and without
`alloc`, promoted/optimized extraction, downstream extraction and strict Lean
checking, the complete proof build, and admitted/opaque declarations and theorem
axioms. Maintain an explicit audit list for the retained contracts; do not obtain
a passing run by silently removing failing retained theorem roots.

## Aeneas compatibility evidence

Keep the pinned tools during this migration:

| Tool | Revision |
| --- | --- |
| Rust | `nightly-2026-09-17` |
| Lean | `v4.31.0` |
| Aeneas | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| Charon | `c8f15d7d658c86a95658f71ad99cddd4be002e04` |

The implementation now has fewer trait dictionaries, no generic backend
argument or unit-state projection, no incomplete-input branches or finality
conversions, one physical bit direction, and fewer production parser/proof
families. There are no diagnostic metadata gates in the v1 completion path.
The new probe confirms the tested single-trait forms and method-local callbacks
translate; it does not show that every Aeneas limitation disappears. Its 11
native tests, 16 passing translations, and 16 expected failure checks support
the interface choice without establishing new semantic theorems.

Borrowed callbacks and locally returned static diagnostic metadata have failures
in parser/backend-free reproductions. `Result` still has enum payloads, so the
optimized-MIR partial-move/cleanup issue must also remain covered; its name does
not refer to partial input. Recursive trait dictionaries and native floats
remain separate tool/model problems. Keep comments explaining workarounds until
a focused check shows the actual source form works without them.

## Known C issue: absolute bit position overflow

Retain `(byte, bit)` cursors and mathematical bit positions in Lean. Do not
compute `8 * byte` in machine arithmetic merely to implement comparison or
forward advancement. The [C issue log](../docs/c-implementation-issues.md) records
overflow, seeking beyond EOF, and wrapped backward lengths; these do not define
v1 semantics.

## Deferred: eager literal rejection

Keep current final-input error precedence during simplification. A truncated
numeric literal can return `UnexpectedEnd` before comparing an available
conflicting prefix; changing that to `Mismatch` is a separate semantic change.
The [historical proposal](rusthammer-pre-v1.md#deferred-eager-literal-rejection)
retains the investigation. Streaming is outside v1, so that proposal is no
longer a scheduled prerequisite for this release.

## Remaining decisions

The additional feature cuts and application/core authentication boundary are
settled. Select the supported dialect/message metadata and any expansion beyond
the initial unsigned framing example into typed payload or signature-field
parsing. Cryptographic verification and replay state remain application concerns.
The focused probe settles the tested single-trait inference/extraction forms,
byte-order-only interface, and adapted MAVLink callback shapes. The production
migration carries those supported forms into the library and consumer. Named
borrowed-output adapters, whole-payload moves, and closure
forwarding remain where required by the pinned tools.

Collection does not promise recoverable allocation failure, and logical
termination does not prove physical stack or memory bounds. Keep those limits
explicit for retained operations. Deferred diagnostic, permutation, and seeking
work is not an open v1 completion requirement.

Broader release packaging, supported native toolchains/platforms, and the final
set of convenience operations remain to be selected. None justifies retaining
backend or partial-input abstractions in the simplified implementation.
