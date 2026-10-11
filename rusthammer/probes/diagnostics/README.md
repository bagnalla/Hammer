# Diagnostic annotation investigation

Investigated on 2026-10-08 with the repository's pinned Rust, Charon, Aeneas, and
Lean versions. This is private feasibility evidence, not a production API.
The [design report](../../../plans/rusthammer-diagnostics.md) specifies selection
rules, compares collection mechanisms, reviews C's annotations/tracing, and lists
the remaining production decisions.

## Findings

Scoped collection can preserve parsing behavior while recording exact leaf
failures, borrowed occurrence labels, optional source locations, and bounded
alternative/label information. Successful speculation must be discarded at
the combinator that handles it. Fatal errors and `NeedMore` must supersede
earlier recoverable alternatives, irrespective of their input positions.
The `root_only_instrumentation_is_insufficient` test retains a counterexample:
a rejected optional attempt at byte 1 can incorrectly mask the real failure at
byte 0 if the optional node has no scope hook.

Two extraction boundaries were identified:

1. A no-op observer with an associated `Mark = ()` translates to an ill-typed
   Lean trait implementation. Aeneas emits a method of type
   `Silent → Result Silent` where the dictionary requires
   `Silent → Result (Unit × Silent)`. Charon and Aeneas exit successfully;
   strict Lean checking catches the error. [`unit_mark.rs`](unit_mark.rs) is a
   standalone reproduction. An ignored Boolean mark passes without changing
   the zero-sized observer state or the extraction tools.
2. Returning locally constructed static string metadata is not generally
   supported by the pinned extractor. [`static_metadata.rs`](static_metadata.rs)
   reduces the failure to `Label { name: "tag" }` returned as `Label<'static>`,
   with no parser, callback, or mutable state. Aeneas reports
   `There should be no bottoms in the value`. Returning a store through a helper
   has the same failure; a store borrowing a caller-supplied string passes.
   The ordinary consumer retains both inline/helper static-location examples and
   a static-report backend example (the latter reports `InterpProjectors.ml:109`).
   All are valid native Rust. Caller-supplied `Label<'meta>` forms pass extraction,
   including non-`Clone` outputs and independent metadata/input lifetimes.

The second finding is an application-extraction gate for a convenient static
annotation API, not evidence that strings or borrowed reports are wholly
unsupported. It is also independent of the older borrowed mapping-callback
investigation: the minimized failure has no callback. No tool patch or dummy
lifetime parameter is proposed here. Before production, choose a durable report
representation/API whose intended static-metadata use extracts, or explicitly
schedule the required extraction-tool work. Generic borrowed-metadata examples
alone do not establish that stronger compatibility claim.

## Probe and native evidence

`lib.rs` defines a private observer protocol with an associated saved mark,
separate observer/backend state, and a report retaining up to two tied failures
and two labels per failure. Capacity loss is flagged; it never changes parsing.
`ByteEq` calls the actual production `Byte` evaluator. `Scoped` calls its child
with the same session and then processes its outcome without borrowing, cloning,
or inspecting decoded values. These explicit wrappers stand in for hooks that
would have to live inside production nodes.

Native tests pass in both allocation configurations:

- 12 probe tests without `alloc`, 13 with it. The extra test covers collected
  repetition stopping and incomplete input.
- 3 ordinary Cargo-consumer tests in each configuration, including native
  executions of the source forms retained as negative extraction cases.
- Within one probe test, 221,184 cases compare the diagnostic reader with the
  existing `ByteIn::new(b"A")` parser and with its silent-observer form: all four
  orderings, both input statuses, short inputs, and valid/invalid cursor classes.
- Targeted cases cover nested/reused occurrences, source metadata, bounded ties
  and truncation, successful alternatives, seeking backward, fatal priority,
  optionality, positive/negative lookahead, retry classification, opaque failure
  boundaries, backend effects, non-`Clone` outputs, and destructor/callback counts.
- Returned input slices and report metadata can escape independently; native
  tests also check input pointer identity.

The probe report omits production fields such as the active ordering at each
failure and richer expectations. Its two-slot capacities are experimental, not
selected library defaults. No storage/stack cost in bytes has been established.

## Extraction and proof evidence

The runner checks both promoted and optimized MIR for the probe and an ordinary
Cargo consumer, scans emitted code for unproved/opaque declarations, and runs Lean
with warnings as errors and implicit variables disabled.

| Case | Roots per MIR stage | Result |
| --- | --- | --- |
| Probe | `run`, `quiet`, `sample`, `close`, `decorate`, `observe_byte` | Extraction, strict Lean, and preservation proofs pass. |
| Consumer | `alternatives`, `borrowed`, `backwards`, `owned`, `effects` | Extraction and strict Lean pass. |
| Standalone metadata control | `borrowed` | Extraction and strict Lean pass. |
| Consumer static metadata | `located`, `negative::located`, `negative::effects`, separately | Three expected Aeneas failures at each stage. |
| Standalone static metadata | `literal_label`, `literal_store`, separately | Two expected Aeneas failures at each stage. |
| Unit mark | `run` | Expected generated-Lean type error at each stage. |

Thus six successful translations and twelve expected failing translations are
checked. A successful runner exit means the positive cases passed and each
specific negative behavior was reproduced; it does not mean every source form
in this directory is extractable.

[`Preservation.lean`](Preservation.lean) is appended to the **freshly generated**
probe implementation at each MIR stage. It proves:

- Totality of every concrete collector hook for all report values, including
  full/truncated reports; the silent hooks are also total.
- `close` and `decorate` preserve arbitrary typed outcomes and the user's backend
  state under total hook contracts.
- `scoped_preserves` transports an observer-independent child contract, preserving
  its entire outcome, successful value/cursor, and backend transition. It does
  not assume all custom parsers obey that contract.
- `observe_byte_preserves` connects the instrumented literal check to its pure
  outcome operation while preserving backend state.
- `run_erases` establishes that enabling the concrete collector and discarding
  the report gives exactly the silent labelled byte parser. This is an equality
  of the extracted Aeneas computations for all inputs, cursors, and contexts;
  both use the same extracted production byte reader. It includes parse errors
  and `NeedMore` and does not assume successful reading.

Six selected theorem roots are axiom-audited at each stage. Their dependencies
contain only `propext`, `Classical.choice`, and `Quot.sound`; there are no project
axioms or admitted proof obligations. Successful extraction is separate evidence
from these semantic proofs. Checking preservation separately at two stages is
not a proof of equivalence between compiler stages.

Selection correctness for the whole report, every core combinator's hook
placement, arbitrary callback/destructor effects, physical stack limits, and
production backend migration remain outside these proofs. Production integration
still needs selection and per-combinator preservation contracts together with
the backend migration. Native callback/destructor tests do not remove the usual
functional-model limits or establish a stack bound.

## Reproduction

From `rusthammer/`, with the pinned extraction checkout and Lean dependencies:

```sh
python3 tools/check_diagnostics.py --aeneas-dir /path/to/aeneas
```

The default Lean environment is `rusthammer/lean/`. A prepared Aeneas backend
project at the same revision can provide the environment without building all
RustHammer proofs. The investigation used:

```sh
python3 tools/check_diagnostics.py \
  --aeneas-dir /home/alex/source/rosette/aeneas \
  --lean-dir /home/alex/source/rosette/aeneas/backends/lean
```

`--native-only` runs the native checks without extraction/Lean. Artifacts and
per-stage logs are written under ignored `target/diagnostics/`; `results.json`
records each positive/negative result. A failed run exits nonzero; a partial
results file is not evidence that the remaining cases passed.

Pins: Rust `nightly-2026-09-17`, Lean `v4.31.0`, Aeneas
`557eff83ecef5083b98a52a94ca7fae63d6c1dab`, and Charon
`c8f15d7d658c86a95658f71ad99cddd4be002e04`. The runner checks extraction checkout
and binary revisions. Generated Lean stays under `target/` and is never edited
to make a failing translation pass.
