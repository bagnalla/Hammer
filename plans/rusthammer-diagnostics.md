# RustHammer diagnostic annotations: deferred investigation

Status: deferred beyond v1 by the 2026-10-10 scope decision. No production
reporting API has been added. Keep the [probe report](../rusthammer/probes/diagnostics/README.md)
and design evidence for later work; metadata extraction, collector storage, and
observer integration are not v1 completion gates.

## Version 1 decision

The [MAVLink 2 target](rusthammer.md#target-application-mavlink-2-packet-parsing)
uses ordinary parse errors for framing and CRC acceptance/rejection. V1 adds no
labels, source-location metadata, observer hooks, report storage, or mutable
reporting context. The simplified parser has input, cursor, and byte-order
arguments only. Do not reserve an empty observer or generic backend capability
for a deferred reporting API.

The research below describes scoped reporting and its preservation obligations.
It includes cases involving the baseline's seeking, permutation, and both bit
directions; these are also outside v1. Their presence in this research is not a
requirement to keep or reintroduce them. API-dependent probes can be reproduced
against `c5c2643` until a reporting increment is explicitly resumed.

## Direction for later work

If resumed, use invocation-local, scoped collection with bounded reports usable
without `alloc`, and recheck the design against the then-current parser API.
An annotation supplies a label and optional location; primitive/combinator hooks
select which failures survive. Reports must preserve success/rejection, callback
order, output ownership, and backtracking behavior.

A root wrapper alone cannot recover failure cursors discarded by child parsers
or see all caught errors. Scoped instrumentation and an explicit concrete
reporting context remain candidates. The old `Observe` trait and `Scoped`
wrappers are evidence, not a required future public API. Do not rerun parsing to
reconstruct reports or convert a full diagnostic buffer into a parse error.
Formatting, full traces, and unlimited storage remain separate capabilities.

## Information and position semantics

A production failure descriptor should retain:

- The originating parse-error kind. In this complete-input design, unavailable
  input is `UnexpectedEnd`; there is no incomplete-input outcome or report
  waiting for another chunk.
- An exact failure `Cursor` when known, plus the active order for unaligned
  positions. A custom parser may supply only a qualified invocation boundary.
- A parser-occurrence label path, inner to outer, with optional source file,
  line, and column. Borrow metadata independently of input and parser values;
  static metadata is a common case.
- Structured expectations when known, initially byte values/sets and EOF, with
  room for fields and predicates. Lack of an expectation is explicit.
- Omitted-alternative and label-path truncation flags. Rendering can receive the
  input later; the report need not own or retain it.

For a literal mismatch, identify the compared field's starting cursor. For
unavailable input, identify the supplied buffer's end. A semantic predicate or
range failure originates after child success; retain its entry and successful
endpoint when reporting the checked region. Seeking can make these endpoints
run backward, so do not present their difference as an unsigned length. An
invalid-cursor error can identify the supplied cursor without claiming it is
inside the input.

Compare `(byte, bit)` lexicographically, without multiplying a machine byte index
by eight. Among eligible recoverable failures, select the greatest failure
position and retain ties in evaluation order. This is a reporting policy, not
an inference about the furthest position visited. A branch that seeks to byte 3,
returns to byte 0, and fails there loses to an eligible failure at byte 2.
Opposite bit directions at the same logical cursor can identify different
physical bits; retain their order/expectations separately.

The returned error still follows the combinator's ordinary contract. `Choice`
returns its second recoverable error even if the report explains a farther
failure in its first arm. Expose that distinction without changing parsing.
Opaque invocation boundaries remain explicitly qualified evidence and must not
be presented as exact inner failure locations.

## Selection and scope rules

These are the intended complete-input rules if reporting is integrated:

| Operation/outcome | Diagnostic rule |
| --- | --- |
| Successful parser scope | Discard caught internal failures and restore its incoming summary. |
| Sequence, selection, `Bind` | Preserve the failing required child. Successful prefixes leave no speculative diagnostic behind. |
| Choice: all attempted arms reject recoverably | Merge eligible failures by position; retain ties within capacity. |
| Choice: an arm succeeds | Discard earlier rejected arms in this choice. |
| Fatal error | Report the causative fatal failure, even if an earlier recoverable failure was farther. Do not try more arms. |
| `UnexpectedEnd` | Follow the ordinary recoverable-error rule of the enclosing combinator; there is no suspension or special incomplete classification. |
| Optional absence | Discard the recoverable failure used to choose absence; propagate fatal errors. |
| Repetition | Discard the stopping rejection when the minimum is met. Otherwise retain the required failure. Fatal errors, invalid progress, and count overflow retain their cause. |
| Separated repetition | Scope the separator/item attempt as a unit when it is rolled back. |
| Positive lookahead | Retain failure explanations; on success discard internal speculation and restore the cursor. |
| Negative lookahead | Caught recoverable failure is successful assertion evidence. Child success emits a new assertion failure; fatal errors propagate. |
| `Verify`, `TryMap`, ranges | Preserve child failures; after child success, predicate/conversion rejection emits the node's own cause. |
| `ButNot`, `Difference`, `Xor` | Suppress failures used as evidence for success. Emit the restriction's cause when competing successes reject; preserve fatal failures. |
| Permutation | Scope tentative paths; discard failed paths after a successful assignment. Merge exhausted required paths, excluding optional-absence checks that succeeded. |
| Seeking | Successful movement emits no failure. Rejected movement reports the seek's cause; later reads report their own positions. |
| Nested annotations | Add the outer occurrence to surviving inner candidates without replacing the origin or error kind. |

The old probe exercised representative cases, not all these contracts.
Separated repetition, permutation, match restrictions, and node-owned causes
still need production integration and compositional selection proofs.

## Scoped hooks under direct execution

The historical private `Observe` trait tests five operations: begin an isolated
scope and return a mark; finish by discarding or merging evidence; record a known
failure; provide a qualified fallback for an opaque child; and attach a label.
Its no-op/recording implementations and explicit wrappers tested the protocol
under the old backend interface. They do not establish the best representation
for the simplified library.

Begin saves the incoming summary and starts an empty local one. Successful
finish restores the saved summary. Failing finish merges eligible local evidence,
with fatal classification taking precedence over distance. This rollback affects
only diagnostic data; arbitrary effects in callbacks/custom parsers are not
undone. Hooks must not inspect or modify decoded outputs or invoke callbacks.

Before production integration:

1. Select bounded storage and measure per-frame costs. The probe copies a tiny
   fixed report into a local mark; that does not justify copying a large report
   at every node. Caller-provided storage with marks is another option.
2. Specify a concrete execution context, lifetimes, entry points, and no-report
   behavior. Keep input borrowing independent of mutable reporting state.
   Recheck the resulting shape with the pinned tools before changing `Parser`.
3. Ensure every child call uses the same reporting invocation, including loops,
   lookahead, references, and parsers returned by `Bind`. A default entry point
   must not silently start a new report inside a combinator. State an explicit
   participation contract for custom parsers and qualify opaque boundaries.
4. Instrument primitive failure sites, node-owned rejections, and scopes that
   catch errors. A label wrapper cannot reconstruct a discarded failure cursor.
5. Expose report access alongside the ordinary result. Fresh parses start fresh
   reports. This complete-input design has no partial/final report lifecycle or
   input-extension protocol.

Hooks must terminate, affect only diagnostic data, and leave parsing control
unchanged. Generic preservation arguments require child/hook contracts, while
a concrete collector's operations need their own proofs. Merely naming a type
an observer does not establish noninterference.

## Extraction evidence and remaining gates

The [2026-10-08 probe](../rusthammer/probes/diagnostics/README.md#findings) passed
both MIR stages, ordinary downstream borrowed-metadata examples, and preservation
proofs for the historical interface. Returning locally constructed static string
metadata failed even in a parser-free label constructor. Removing backends or
partial input does not resolve that independent failure. Settle the intended
static-metadata API before claiming production annotation support.

A separate unit-valued checkpoint translation defect had a passing Boolean-mark
form. Recheck it against the chosen concrete context; do not assume removing the
old `Direct` state fixes every unit-return issue. Keep old API-dependent probes
reproducible against `c5c2643` until explicitly ported.

Enriching ordinary errors would spread metadata/storage through every parser and
proof but would still require scope selection. Global state loses invocation
isolation; reparsing can duplicate effects. These considerations favor explicit
scoped collection, without settling a public hook trait or storage type now.

## C reference and deliberate differences

The earlier investigation inspected [`hammer.h`](../src/hammer.h),
[`trace.c`](../src/trace.c), [`choice.c`](../src/parsers/choice.c),
[`many.c`](../src/parsers/many.c), [`not.c`](../src/parsers/not.c), and
[`test_trace.c`](../tests/backends/test_trace.c).

C's `h_with_context` labels occurrences; its debug parser can retain a full trace
and structured expectations. Choice hooks save/clear/restore diagnostic state.
Tests cover discarding failures after success, nested/reused occurrences, source
provenance, and error-kind preservation. Rust need not copy C's ownership,
formatting, trace tree, or backend reconstruction. Typed values, explicit fatal
errors, bit ordering, and bounded seeking retain their own contracts. No C/Rust
diagnostic equivalence or new differential corpus is claimed here.

## Completion gates for a production increment

If diagnostics are explicitly resumed beyond v1, settle metadata extraction,
report fields, storage budgets, context propagation, and custom-parser behavior.
Prove selection correctness and preservation of ordinary results and callback
behavior; the old preservation probe does not establish useful reporting for
every grammar. Include complete-input truncation, independent metadata/input
borrows, report overflow, cleanup, and lookahead/backtracking cases. Include
seeking only if it has separately returned to scope. Regenerate and audit the
production proofs with `tools/verify.py`.

Do not promote the probe's two-slot report, Boolean mark, or explicit `Scoped`
wrappers merely because they passed extraction. Their role is evidence for a
durable design, not a required compatibility interface.
