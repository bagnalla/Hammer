# Direct-only version 1 extraction probe

This private, dependency-free `no_std` package checks the interface selected in
the [v1 plan](../../../plans/rusthammer.md#parsing-interface). It is not imported
by the production library or its proof build. Its implementations are extraction
fixtures, not a second library or a completed migration.

The experiment uses one `Parser<'input>` trait with its own associated `Output`
and `parse_with(input, cursor, ByteOrder) -> Result<(Cursor, Output), ParseError>`.
`parse` supplies big byte order. There is no `Grammar`, `Eval`, backend parameter,
input finality, partial outcome, bit-direction parameter, or reporting state.

## Results

Checked on 2026-10-10 with Rust `nightly-2026-09-17`, Lean `v4.31.0`, Aeneas
`557eff83ecef5083b98a52a94ca7fae63d6c1dab`, and Charon
`c8f15d7d658c86a95658f71ad99cddd4be002e04`.

All 11 native tests pass (nine probe tests and two consumer tests). The full
runner exits successfully with **16 passing translations and 16 specifically
matched expected failures**. Those negative cases remain unsupported source
forms; they are not passing translations.

| Case | Promoted MIR | Optimized MIR |
| --- | --- | --- |
| Core: 16 generic/concrete roots | Pass | Pass |
| Adapted MAVLink: 3 roots | Pass | Pass |
| Cargo consumer: 6 core roots | Pass | Pass |
| Cargo consumer: captured MAVLink lookup | Pass | Pass |
| Backend-free method-local callbacks (within core/consumer) | Pass | Pass |
| Old backend-generic closure | Lean: cannot infer `Backend` | Same |
| Old external closure factory | Pass | Pass |
| Borrowed closure identity, local and consumer | Aeneas: non-endable abstraction | Same |
| Borrowed function-item identity | Aeneas: higher-ranked/free lifetime constraint | Same |
| Function-item CRC lookup | Aeneas: unsupported arrow type | Same |
| Loop over a borrowed parse result | Aeneas: cannot match contexts | Same |
| Header built with nested predicate closures | Lean: insufficient record-update type information | Same |
| Partial tuple/error moves (two controls) | Pass | Aeneas: bottom value in cleanup discriminant read |
| Whole tuple/error moves (two controls) | Pass | Pass |

The evidence supports the planned single trait and removal of the output-only
`Grammar` trait. Constructor inference and the tested opaque returns do not need
the old split. The tested callbacks inside lifetime-generic parser methods no
longer need external factories merely to avoid an unused backend type argument.
This is not a claim about closures under every other generic parameter.

Keep named borrowed-output adapters and whole-payload `Result` moves. The old
borrowed-identity and cleanup failures reproduce without any backend, finality,
or `NeedMore` type. The supported MAVLink form also retains concrete byte
validation and uses a closure to call the named CRC lookup. Source refactoring
still needs extraction checks; the runner preserves the failing alternatives.

## Coverage

- All seven constructor helpers are generic extraction roots. They infer child
  outputs through `Parser`; `seq` and `optional` need no constructor bounds.
- Shared `&P` forwarding, consumer-defined parsers, local parser lifetimes,
  independently borrowed input/configuration, and owned non-`Clone` outputs.
- Whole-parser `impl Parser` returns, including higher-ranked borrowed outputs,
  and concrete `Map` returns with opaque callbacks and conditional `Copy`.
- `LocalCallbacks` constructs mapping and `Bind` closures inside a method
  generic over the input lifetime, with no backend parameter or external factory.
- High-first numeric fields, little/big byte order, unaligned byte-order scopes,
  restoration of enclosing order, and direction-free spans with borrowed views.
- An [adapted MAVLink grammar](mavlink.rs) exercises the real application's
  header, length-dependent borrowed payload, span-based CRC predicate, borrowed
  caller lookup, opaque frame grammar, and named borrowed-output adapters.
  It keeps the existing unsigned framing and CRC algorithm. A concrete byte
  equality/exclusion node stands in for production byte sets; the small `Pattern`
  fixture is aligned-only. These are source-shape checks, not full library parity.
- The [consumer](consumer/lib.rs) depends on this package through ordinary Cargo
  dependency MIR. It builds its own compositions and captured dialect lookup.

Native checks cover prefix consumption, payload pointer identity, every truncated
HEARTBEAT prefix, byte corruption, unknown IDs, full 24-bit message IDs with a
caller-supplied extra byte, callback inference, complete-input choice behavior,
byte-order restoration, and owned/borrowed consumer outputs. The custom-ID test
uses an independent byte-wise CRC calculation checked against the HEARTBEAT fixture.

## Controls and extraction boundaries

The runner separates passing cases from specific expected failures. A negative
case must fail in the expected phase with its recorded diagnostic; an unrelated
tool error does not count as a successful reproduction.

- [Backend closure control](../backend_closure.rs): the original backend-generic
  evaluator and its external-factory workaround are checked alongside the new
  method-local callbacks. This distinguishes removal of that type-argument
  problem from more general callback support.
- [Borrowed callback controls](candidates.rs): closure identity and function-item
  identity remain separate from ordinary borrowed parser outputs and named
  parser adapters. The consumer also constructs the closure identity itself.
- The function-item CRC lookup and a loop over a `TakeAligned` result have
  isolated candidate roots. The supported forms use a closure that calls the
  lookup function and a separate byte-comparison helper, respectively.
- `mavlink::predicate_header` retains a Rust-valid alternative using nested
  `Verify` closures. The passing header uses concrete byte-validation nodes,
  avoiding insufficiently typed record updates in generated Lean.
- [Partial enum moves](../partial_enum_move.rs): nested tuple matching and
  discarding a generic error are compared with whole-payload moves. Returning
  `Result` does not itself remove the optimized-MIR cleanup limitation.

The MAVLink wrapper borrows its lookup callback. As in the production extraction,
the runner includes `core::ops::function::impls::_` so `&F` forwarding has actual
translated bodies. It rejects generated axioms rather than accepting opaque
callback forwarding.

## Reproduction

From `rusthammer/`, with the extraction tools pinned by `tools/verify.py`:

```sh
python3 tools/check_direct_v1.py --native-only
python3 tools/check_direct_v1.py --aeneas-dir /path/to/pinned/aeneas
```

The existing `lean/` project's Aeneas dependencies must be available. An optional
`--lean-packages /path/to/packages.json` selects existing local Lake checkouts;
it is not required on a normally configured checkout. In this workspace, the
matching tools are at `/home/alex/source/rosette/aeneas` and the existing package
override is `target/mavlink/lean-packages.json`.

The runner checks formatting and both packages' native tests, verifies extraction
tool revisions, then checks every selected case at promoted and optimized MIR.
Dependencies expose optimized MIR in either consumer mode. It audits every
requested root and rejects generated admissions, axioms, and opaque declarations.
Lean runs with `warningAsError=true` and `autoImplicit=false`.

Use repeated `--case NAME` options for a focused reproduction. Logs, LLBC,
generated Lean, and `results.json` stay under ignored `target/direct-v1/`. The
results file describes the selected cases in the latest invocation.

These checks establish translation and Lean type-checking compatibility, not
semantic correctness, cursor laws, CRC correctness, or compiler-stage equivalence.
The production migration must regenerate and port the retained proofs against
the actual library source.
