# RustHammer diagnostic annotations: investigation

Status: design and private extraction investigation, 2026-10-08. No production
API or interpreter change. Diagnostic annotations remain an intended capability;
their first-version inclusion is a scope decision, not an implication of these
probes. Reproduction and checked proof coverage are recorded in the
[probe report](../rusthammer/probes/diagnostics/README.md).

## Recommendation

Use invocation-local, scoped diagnostic collection with a no-op observer for
ordinary execution. Keep `ParseOutcome`, typed outputs, and the existing error
control flow. An annotation supplies a label and optional construction location;
primitive and combinator hooks supply the actual cause and select which failures
survive. Treat a report as an explanation alongside the returned outcome, never
as a replacement error that controls backtracking.

A root-only wrapper is insufficient. `Eval<Backend>` passes state but does not
intercept calls, and `ParseOutcome::Error` contains no failure cursor. Production
integration must instrument the relevant nodes and supply an explicit observer
capability at the backend boundary. The private probe uses the real `Grammar`,
`Eval`, byte reader, choice, sequencing, lookahead, optionality, repetition, and
seeking. Its explicit `Scoped` wrappers model hook placement; users should not
have to remember such wrappers around every built-in combinator.

The recommended report is structured and bounded, usable without `alloc`.
Preserve diagnostic truncation as data. Do not turn a full diagnostic buffer into
a parse error, rerun callbacks to reconstruct failures, or clone parser outputs.
A full execution trace, formatting, an alternative tree, and unlimited storage
are separate capabilities, not prerequisites for useful annotations.

The borrowing/hook design passes for caller-supplied metadata. The pinned
extractor still fails on locally constructed static metadata returned to the
caller, minimized to a string-only label constructor. A separate unit-valued
checkpoint defect has a passing Boolean-checkpoint form. See the
[extraction evidence](../rusthammer/probes/diagnostics/README.md#findings): the
static-metadata use case must be settled before claiming the intended annotation
API is ready for production verification.

## Information and position semantics

A production failure descriptor should retain:

- The originating error kind or an explicit incomplete-input classification.
- An exact failure `Cursor` when the originating parser knows it, plus the active
  ordering needed to interpret an unaligned position. An opaque custom parser
  may provide only an explicitly marked invocation boundary.
- The parser-occurrence label path, from inner to outer, with optional source
  file, line, and column. Borrow metadata independently of input and parser
  values; static metadata is a common special case.
- Structured expectations when known, initially byte values/sets and EOF, with
  room for numeric fields and predicates. Lack of an expectation is explicit.
- Flags for omitted alternatives and label-path truncation. Reports need not
  retain the input itself; rendering can accept the input later.

For a literal mismatch, identify the compared field's starting cursor. For
unavailable input, identify the buffer boundary, while retaining whether the
outcome is `NeedMore` or final `UnexpectedEnd`. A semantic predicate or range
failure originates at its own node after a successful child; retain its entry
and successful endpoint if reporting the checked region. These endpoints may
run backward after seeking and must not be presented as an unsigned length.
An invalid-cursor error can identify the invalid supplied cursor without
claiming it is an address inside the input.

Compare `(byte, bit)` lexicographically, without multiplying a machine byte index
by eight. Among eligible recoverable failures, select the greatest failure
position, retaining alternatives tied there in evaluation order. This is a
reporting policy, not an inference about the parser's last cursor or the furthest
position it visited. For example, a branch can seek to byte 3, seek back to byte
0, and fail there; a competing failure at byte 2 takes precedence. Two opposite
bit directions can identify different physical bits at the same logical cursor;
retain their ordering and expectation separately instead of merging them as an
identical physical observation.

The actual returned error remains the existing combinator result. For example,
`Choice` still returns its second recoverable error even when the selected report
explains a farther failure in its first arm. Expose that distinction in the report
API rather than changing `Choice`'s semantics.

Opaque boundaries must never be labelled exact. In a mixed report they remain
qualified evidence, not proof that a precise inner failure occurred there. The
probe orders them by their recorded boundary but marks the uncertainty; production
should preserve the distinction in both structured data and formatting.

## Selection and scope rules

| Operation/outcome | Diagnostic rule |
| --- | --- |
| Successful parser scope | Discard failures caught inside that scope and restore its incoming diagnostic summary. |
| Sequence, selection, `Bind` | Preserve the failing/incomplete required child. Successful prefixes leave no speculative diagnostic behind. Do not restore backend effects. |
| Choice: all attempted arms reject recoverably | Merge eligible arm failures by failure position; retain ties up to the configured capacity. |
| Choice: an arm succeeds | Discard failures from all earlier rejected arms in this choice. |
| Fatal error | Report the causative fatal failure, regardless of an earlier recoverable failure's greater position. Do not try more arms. |
| `NeedMore` | Retain the incomplete required attempt and suspend the choice/repetition according to existing rules. Earlier rejected alternatives do not displace it. |
| Optional absence | Discard the recoverable failure used to choose absence. Fatal errors and incompleteness propagate. |
| Repetition stopping after its minimum | Discard the rejected stopping attempt. If the minimum is unmet, retain the required failure. Fatal errors, `NeedMore`, invalid progress, and count overflow retain their own cause. |
| Separated repetition | Scope the separator-plus-element attempt as a unit when existing semantics roll it back; report a required trailing-element failure when the selected list policy makes it mandatory. |
| Positive lookahead | On failure/incompleteness retain the child's explanation. On success discard internal speculation and restore the cursor as today. |
| Negative lookahead | A caught recoverable child failure is successful assertion evidence, not a reportable error. Child success causes a new assertion failure at the assertion node; propagate fatal/incomplete children. |
| `Verify`, `TryMap`, ranges | Preserve child failures; if the child succeeds and the predicate/conversion rejects, emit the node's own cause. |
| `ButNot`, `Difference`, `Xor` | Suppress failures used as evidence for success. When successful competing matches cause rejection, emit the restriction's own cause. Preserve fatal/incomplete required evaluations. |
| Permutation | Scope each tentative path; discard failed paths after a successful assignment. Merge failures of exhausted required paths, not optional-absence checks that ultimately succeeded. Preserve fatal/incomplete short-circuiting. |
| Seeking | A successful movement emits no failure. A rejected seek reports its cause at the seek operation; later reads report their own positions, including after backward seeks. |
| Nested annotations | Add the outer occurrence to each surviving inner candidate; do not replace the inner origin or error classification. |

These are intended production contracts. The probe exercises representative
cases, not every operation in this table. In particular, separated repetition,
permutation, match restrictions, and all node-owned causes still need integration
and compositional selection proofs.

## Hook and backend design

The private `Observe` trait tests five operations: begin an isolated scope and
return a saved mark; finish by discarding or merging its evidence; record a known
failure; supply a qualified fallback for an opaque child; and attach a label.
Its associated mark type permits different storage strategies. The no-op observer
has zero-sized state. A recording observer holds only diagnostic state, separate
from the user's mutable backend state. Neither hooks nor reports receive decoded
outputs or application callbacks.

On entry, begin saves the incoming summary and starts an empty local one. On
success, finish restores the saved summary. On rejection/incompleteness, it
merges the local summary into the saved one with control classification taking
precedence over distance. Diagnostic rollback affects only the observer;
ordinary backend mutations persist exactly as required by `Eval`.

Required production work at the boundary is explicit:

1. Choose the durable hook trait and bounded storage. The probe copies a tiny
   fixed report into a call-local mark; it does not establish an acceptable byte
   cost per frame for large reports or deep grammars. Measure the intended design
   before adopting it. Caller-provided storage with marks is another option.
2. Make `Direct` implement no-op hooks and define how custom backends implement
   or carry an observer. Existing unconstrained `impl<Backend> Eval<Backend>`
   bodies cannot call methods on arbitrary `Backend`; new bounds or an explicit
   execution-context migration are required. A blanket no-op implementation for
   every backend would prevent a specialized recording implementation.
3. Keep every child invocation on the same backend, including references,
   lookahead, loops, and `Bind` results. A wrapper must not quietly call `parse`
   on an inner parser to bypass missing capabilities. Backend-specific custom
   evaluators need an explicit participation/migration policy.
4. Instrument primitive failure sites, node-owned rejection sites, and the
   scopes that catch child errors. A wrapper cannot reconstruct a discarded
   cursor from `ParseError`. The probe's precise leaf uses the real `Byte`
   evaluator and knows the compared field's start and short-input boundary.
5. Return outcomes and report access through a deliberate entry point. Keep
   ordinary `Parser::parse_with` behavior and represent partial reports distinctly
   from final rejection. Retrying a partial parse starts a fresh report for the
   new input snapshot, alongside the current retry-from-start parsing semantics.

The observer protocol must be noninterfering: hooks terminate, affect only
diagnostic state, and never influence parser control decisions. Arbitrary custom
Rust implementations could violate this contract. Generic preservation theorems
therefore require contracts for hooks and children; naming a type `Observer`
does not prove the contract.

## Why the alternatives are less suitable

Enriching `ParseOutcome::Error` directly would spread metadata lifetimes/storage
and new payloads throughout ordinary parsing and every existing proof. It also
does not by itself specify which caught failures to retain. A global/thread-local
trace loses invocation isolation and complicates `no_std`, nesting, and proofs.
Reparsing after an error can duplicate callback/backend effects and need not
reproduce the original execution. A bare label wrapper supplies context but not
an internal failure position or the scope decisions needed for correct selection.

These comparisons favor explicit observer hooks, while leaving their final
signature and storage representation to the production design review.

## C reference and deliberate differences

The reference was inspected in [`hammer.h`](../src/hammer.h),
[`trace.c`](../src/trace.c), [`choice.c`](../src/parsers/choice.c),
[`many.c`](../src/parsers/many.c), [`not.c`](../src/parsers/not.c), and
[`test_trace.c`](../tests/backends/test_trace.c).

`h_with_context` annotates an occurrence without modifying its child. C copies
the metadata and owns the diagnostic separately. `h_parse_debug` can retain a
complete execution trace; structured byte-range and EOF expectations accompany
the selected failure. C's choice hooks save/clear/restore diagnostic state and
retain alternative information, and tests specifically cover discarding choice
failures after success, nested/reused occurrences, source provenance, and
preservation of error kinds. `trace_failure_progress` distinguishes syntax
failure positions from endpoints of value-check failures.

Rust need not reproduce C's ownership, formatting priorities, trace tree, or
backend reconstruction algorithms. It has typed values, explicit fatal errors,
partial `NeedMore`, bit ordering, and bounded seeking contracts that need their
own specification. The C read-through informs this proposal; this investigation
does not claim a new C differential corpus or C/Rust diagnostic equivalence.

## Completion gates for a production increment

First settle the static-metadata extraction gate for the intended API. Select
the first-version report fields and storage budgets, settle the backend
migration, and instrument the intended core paths. Prove both diagnostic
selection correctness and preservation of ordinary outcomes/backend transitions;
the probe's preservation proof alone does not establish useful or complete
reporting for every grammar. Include ordinary downstream grammars, metadata/input
borrow separation, both input statuses, report truncation, callbacks and cleanup,
and seeking/lookahead/backtracking cases. Regenerate and audit the production
proofs with `tools/verify.py` after that integration.

Do not promote the probe's two-slot report or explicit `Scoped` wrappers merely
because they pass extraction. Their role here is to test the semantics, trait
shape, lifetimes, and proof method before choosing durable production machinery.
