# Cross-crate extraction regression

This package consumes the direct-only RustHammer v1 API through a normal Cargo
path dependency. Its 51 extraction roots cover all retained families, constructor
inference and opaque returns, shared references, independent input/configuration
borrows, owned non-`Clone` outputs, checked callbacks, and borrowed accumulators.
Both allocation configurations have native tests; extraction includes `alloc`.

Ordering entries cover high-first traversal and both byte orders, including
unaligned scopes and fixed `Be*` readers. Span entries cover construction,
accessors, original byte views, and captured borrowed outputs. Position entries
retain `SkipBits` and `Tell`. Dependent parsing and repetition cover borrowed
payloads, owned fields, shared parser factories, exact/bounded/unbounded counts,
separator rollback, and folding. The shared MAVLink example validates the CRC and
borrows its payload; a closure forwards the HEARTBEAT lookup.

The consumer has no backend, finality, seek, permutation, or low-first entries.
Complete-input/high-first cases from the old mixed tests remain, along with
ownership and borrow-identity checks. Reproduce those excluded APIs at `c5c2643`.

Run `python3 tools/verify.py --aeneas-dir /path/to/aeneas` from `rusthammer/`.
It tests both consumer allocation configurations, extracts its dependency bodies,
requires all 51 roots in the result, and compiles the generated Lean with warnings
as errors and implicit parameters disabled. Borrowed callback forwarding includes
`core::ops::function::impls::_`, so reference calls have actual translated bodies.

The verifier also translates the library at promoted and optimized MIR stages.
Extra translations stay under `target/`. The handwritten correctness proofs use
the promoted translation; compatibility checks do not prove equivalence of
compiler stages. The library README describes model/resource limitations.

## Cause of the original failure

Investigated with Aeneas `557eff83ecef5083b98a52a94ca7fae63d6c1dab`,
Charon `c8f15d7d658c86a95658f71ad99cddd4be002e04`,
Rust `nightly-2026-09-17`, and Lean `v4.31.0`.

The original `composition` example failed inside Aeneas when extracted as a
separate crate. Charon normally reads promoted MIR for the crate being verified,
but dependency function bodies are available only as optimized MIR. Charon
disables the optimizations it can; the relevant difference here is that the
later stage includes compiler-generated cleanup code after drop elaboration.
Selecting `--mir promoted` for the consumer cannot change its dependencies' stage.

For certain patterns, that cleanup code checks an enum's variant after moving a
payload field out of it. The variant is still available, but Aeneas's
`InterpStatements.eval_switch_raw` handles `SwitchDiscriminant` by calling
`access_rplace_reorganize_and_read`. That reaches `InterpExpressions.read_place_check`,
which rejects a bottom value anywhere inside the enum. A moved payload is
represented by such a bottom value. The resulting message is:

```text
There should be no bottoms in the value
```

This can be reproduced in one crate, without parsers, traits, or closures. It is
not inherently a crate-boundary problem. The boundary exposes it by selecting
the later MIR stage. Both elaborated and optimized MIR reproduce it; promoted
MIR does not for these examples. Charon's `--resugar-drops` did not fix the
generic error-discarding example.

## Minimal reproductions

[`partial_enum_move.rs`](../partial_enum_move.rs) contains two failing patterns
and corresponding alternatives:

| Function | Promoted MIR | Elaborated MIR | Optimized MIR |
| --- | --- | --- | --- |
| `partial_error` | Translates | Discriminant-read failure | Discriminant-read failure |
| `whole_error` | Translates | Translates | Translates |
| `partial_pair` | Translates | Discriminant-read failure | Discriminant-read failure |
| `whole_pair` | Translates | Translates | Translates |

All twelve cases were checked with the pinned tools. From `rusthammer/`, this
reproduces the first failure:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --mir optimized --start-from partial_enum_move::partial_error --print-llbc \
  --dest-file target/partial_enum_move.llbc -- \
  --crate-type lib --edition 2021 probes/partial_enum_move.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/partial-enum-move \
  -abort-on-error -warnings-as-errors -no-progress-bar target/partial_enum_move.llbc
```

Change the entry point to another table row and the MIR stage to reproduce the
other cases. The intentionally failing functions are separate diagnostic probes,
not library exports or expected failures in the normal verification command.

## Library changes

In result-handling combinators, move the entire tuple
payload out of the enum before unpacking or selecting its fields. For example:

```rust,ignore
// The nested pattern partially moves the enum's tuple payload.
Ok((next, value)) => Ok((next, value)),

// Moving the tuple first avoids the problematic cleanup discriminant read.
Ok(parsed) => {
    let (next, value) = parsed;
    Ok((next, value))
}
```

In `TryMap`, bind the rejected conversion error as `Err(_error)` instead of
`Err(_)`. The wildcard leaves that payload in the enum for cleanup; the binding
moves it out, so both variants' payloads are consumed and the redundant enum
check disappears. The error is still dropped and the result is still `Mismatch`.

These source-shape changes preserve input consumption, error rules, and
support for borrowed and non-`Copy` outputs. Native ownership/destructor tests and
all existing Lean proofs pass. No tool patch, additional trait bound, or disabled
interpreter check is required. The original separate-crate example and this
ordinary Cargo consumer now translate and Lean type-check.

A general tool-side solution would need to support inspecting an enum tag
without reading moved payload fields, or eliminate the redundant cleanup checks.
The source forms above are the supported approach for the pinned toolchain.
They do not resolve the separately recorded borrowed-record callback limitation
or establish compatibility for arbitrary downstream Rust code.
