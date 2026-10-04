# Aeneas compatibility probes

These small programs record extraction behavior separately from the main proof
suite. They are not imported into the crate or its Lean proofs. The checked
mapping probe includes the actual library source to exercise a concrete callback.
The `cross_crate` fixture instead uses a normal Cargo dependency and is checked
by the local verification command.

## Capturing callback with a borrowed record output

[`borrowed_record_map.rs`](borrowed_record_map.rs) passes a capturing `Fn` to a
generic function. The callback constructs a record containing the borrowed slice
it receives. This is valid Rust, and Charon extracts it, but the pinned Aeneas
revision fails with `Can't end abstraction ... as it is set as non-endable` in
`interp/InterpBorrows.ml`.

From `rusthammer/`, reproduce with the pinned tools:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --dest-file target/borrowed_record_map.llbc -- \
  --crate-type lib --edition 2021 probes/borrowed_record_map.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/borrowed-record-probe \
  -abort-on-error -warnings-as-errors -no-progress-bar target/borrowed_record_map.llbc
```

The second command is expected to fail at Aeneas revision
`557eff83ecef5083b98a52a94ca7fae63d6c1dab`, with Charon revision
`c8f15d7d658c86a95658f71ad99cddd4be002e04`. Recheck it when upgrading the tools;
it does not establish that all callbacks returning borrowed values are unsupported.

The record parser constructs its final borrowed `Record` directly after parsing
the payload. That implementation extracts and is included in the normal
verification command. Generic `Map` and `Verify` have callback-dependent Lean
contracts; each concrete callback must still translate and satisfy its contract.

## Input finality, default methods, and borrowed outcomes

[`input_status.rs`](input_status.rs) exercises `InputStatus`, a three-variant
`ParseOutcome`, a default complete-input trait method, a borrowed output, and an
optional combinator. Charon/Aeneas translation **and Lean type-checking succeed**
with the pinned toolchain. The supported library's proofs cover the full bit
cursor, cursor validation, and all current combinators; this tiny probe is only
an interface compatibility check.

From `rusthammer/`, after setting up the Lean dependencies:

```sh
mkdir -p target/input-status-probe
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --dest-file target/input_status.llbc -- \
  --crate-type lib --edition 2021 probes/input_status.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/input-status-probe \
  -abort-on-error -warnings-as-errors -no-progress-bar target/input_status.llbc
cd lean
lake env lean ../target/input-status-probe/InputStatus.lean
```

The normal verification command regenerates and proves the actual implementation,
including this interface shape. These probe commands are available separately for
toolchain investigations; the older borrowed-record callback issue stays deferred.

## Exact-count collection with borrowed outputs

[`repeat_n.rs`](repeat_n.rs) collects generic parser outputs in a `Vec`, stops on
error or `NeedMore`, and instantiates the loop with a non-`Copy` struct containing
a borrowed slice. Charon extraction, Aeneas translation, and Lean type-checking
succeed with the pinned tools. It uses `no_std` plus `alloc`; a standalone library
probe does not supply an allocator because the final application supplies one.

From `rusthammer/`:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --dest-file target/repeat_n.llbc -- \
  --crate-type lib --edition 2021 probes/repeat_n.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/repeat-n-probe \
  -abort-on-error -warnings-as-errors -no-progress-bar target/repeat_n.llbc
cd lean
lake env lean ../target/repeat-n-probe/RepeatN.lean
```

The library's generalized `Repeat` is extracted and proved by `tools/verify.py`
with `alloc` enabled; exact repetition is now `Repeat::exact`. This minimized
probe retains its original exact-count name and records collection compatibility;
allocation/resource guarantees remain
limited by Aeneas's standard-library model as documented in the crate README.

## Repetition loop control flow

While adding unbounded repetition, the shared library loop initially used
`while repeat_below_max(count, self.max) { ... }`, with early returns for child
errors and incomplete input. Charon succeeded, but the pinned Aeneas revision's
`PrePasses.ml` reported `Early returns inside of loops are not supported yet`.
For this shape, moving the same check inside the loop succeeds:

```rust,ignore
loop {
    if !repeat_below_max(count, self.max) {
        return ParseOutcome::Success(next, values);
    }
    // Parse the child, check progress/count, and accumulate or return its outcome.
}
```

This preserves the public API and stopping semantics. The actual `Repeat`
implementation is extracted and proved by `tools/verify.py`; it is the regression
case for the accepted shape. This observation concerns this particular combination
of a condition helper and loop exits, not a general prohibition on `while` or
early returns. Revisit the alternate spelling when upgrading Aeneas if useful;
the borrowed-record callback investigation remains deferred.

## Checked mapping and phantom output types

[`try_map.rs`](try_map.rs) runs the library's `TryMap` with a captured `Fn` that
returns `Result<Flag, ()>`. `Flag` is an owned record with neither `Copy` nor
`Clone`. Charon extraction, Aeneas translation, and Lean type-checking succeed
with the pinned tools. This checks a concrete fallible callback; the library's
generic contracts separately require each callback's termination and semantic
contract. It does not resolve the earlier borrowed-record callback limitation.

From `rusthammer/`:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --start-from try_map::checked_flag --dest-file target/try_map.llbc -- \
  --crate-type lib --edition 2021 probes/try_map.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/try-map-probe \
  -abort-on-error -warnings-as-errors -no-progress-bar target/try_map.llbc
cd lean
lake env lean -DwarningAsError=true ../target/try-map-probe/TryMap.lean
```

The probe includes `src/lib.rs` as a module and remains useful as a same-crate
comparison. The original separate-crate `composition` example failed on cleanup
discriminant reads after partial enum moves. That issue is now understood and
avoided in the library. The original example translates and Lean type-checks;
the normal verification command also checks a separate Cargo consumer. See the
[investigation and regression fixture](cross_crate/README.md).

To recheck the original example from `rusthammer/`:

```sh
~/source/aeneas/charon/bin/charon cargo --preset=aeneas --sysroot default \
  --start-from-if-exists composition::decode_mode --include 'rusthammer::_' \
  --dest target/composition-example -- --example composition --locked
~/source/aeneas/bin/aeneas -backend lean -dest target/composition-example-lean \
  -abort-on-error -warnings-as-errors -no-progress-bar \
  target/composition-example/composition.llbc
cd lean
lake env lean -DwarningAsError=true ../target/composition-example-lean/Composition.lean
```

The failing parser also exposed a smaller representation constraint:
`PhantomData<fn() -> T>` is valid Rust but Aeneas reports `Arrow types are not
supported yet`. The supported `Fail<T>` uses plain `PhantomData<T>`, with manual
`Copy`/`Clone` implementations that require no bounds on `T`. Unlike a function-type
marker, it inherits `T`'s auto-trait restrictions. It stores no output at runtime,
and its constructor, clone, and parsing methods are translated and proved by the
normal verification command.
