# Cross-crate extraction regression

This Cargo package consumes RustHammer through a normal path dependency. It
checks a captured fallible callback returning an owned, non-`Clone` value,
sequencing and output selection returning a borrowed payload, the default
complete-input method, exact/unbounded collection with `alloc`, and allocation-free
folding with captured initialization, borrowed child values, and an owned non-`Clone`
accumulator. Both finite and unbounded folding are exercised. Separated-list
entries check exact collection with borrowed item and separator outputs, and
unbounded folding with an owned non-`Clone` separator output that is discarded.

Run `python3 tools/verify.py` from `rusthammer/`. Alongside the library tests and
proofs, that command:

1. Extracts the library's complete set of verification roots from optimized MIR,
   the compiler stage available for dependencies, and Lean type-checks it.
2. Tests this consumer with allocation disabled and enabled.
3. Extracts the consumer with RustHammer's dependency bodies included and `alloc`
   enabled, checks that all nine entry points were translated, and Lean
   type-checks the result.
4. Rejects admitted or opaque project declarations in both extra translations.

Extra translations and Cargo outputs stay under `rusthammer/target/`. Existing
library correctness proofs still use the ordinary promoted-MIR translation.
The additional checks establish extraction and Lean type-checking compatibility;
they do not constitute new application correctness theorems or a proof that the
compiler stages are equivalent. Standard-library model and destructor limitations
remain as documented in the crate README.

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

In `InputStatus::classify`, `Left`, `Right`, and `Middle`, move the entire tuple
payload out of the enum before unpacking or selecting its fields. For example:

```rust,ignore
// The nested pattern partially moves the enum's tuple payload.
Ok((next, value)) => ParseOutcome::Success(next, value),

// Moving the tuple first avoids the problematic cleanup discriminant read.
Ok(parsed) => {
    let (next, value) = parsed;
    ParseOutcome::Success(next, value)
}
```

In `TryMap`, bind the rejected conversion error as `Err(_error)` instead of
`Err(_)`. The wildcard leaves that payload in the enum for cleanup; the binding
moves it out, so both variants' payloads are consumed and the redundant enum
check disappears. The error is still dropped and the result is still `Mismatch`.

These changes preserve the public API, input consumption, outcome rules, and
support for borrowed and non-`Copy` outputs. Native ownership/destructor tests and
all existing Lean proofs pass. No tool patch, additional trait bound, or disabled
interpreter check is required. The original separate-crate example and this
ordinary Cargo consumer now translate and Lean type-check.

A general tool-side solution would need to support inspecting an enum tag
without reading moved payload fields, or eliminate the redundant cleanup checks.
The source forms above are the supported approach for the pinned toolchain.
They do not resolve the separately recorded borrowed-record callback limitation
or establish compatibility for arbitrary downstream Rust code.
