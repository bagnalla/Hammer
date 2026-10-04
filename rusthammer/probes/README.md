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

## Folding and borrowed accumulators

The library's shared repetition driver uses a private accumulator trait, with
collection and fold implementations. The driver and both implementations
translate at promoted and optimized MIR and have shared Lean contracts. The
normal Cargo consumer exercises a captured initializer, borrowed child slices
folded into an owned non-`Clone` checksum, and unbounded counting. Translation
and Lean type-checking succeed with the pinned tools. These consumer checks
establish extraction compatibility, not application correctness theorems.

[`fold_borrowed_accumulator.rs`](fold_borrowed_accumulator.rs) instead returns a
borrowed slice from both callbacks. It initializes with an empty slice of the
input and retains the last parsed one-byte slice. Native Rust supports this
pattern and a native test checks that the accumulator still points into the input.
Both callbacks fail Aeneas translation with `Can't end abstraction ... as it is
set as non-endable` in `InterpBorrows.ml`. This was reproduced through a normal
Cargo dependency and with the library included as a module; it is separate from
the resolved partially moved enum problem. The error matches the older borrowed
record callback failure; a common underlying cause has not been established.

Reproduce from `rusthammer/` with the pinned tools:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --start-from fold_borrowed_accumulator::last_block \
  --dest-file target/fold_borrowed_accumulator.llbc -- \
  --crate-type lib --edition 2021 probes/fold_borrowed_accumulator.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/fold-borrowed-probe \
  -abort-on-error -warnings-as-errors -no-progress-bar target/fold_borrowed_accumulator.llbc
```

The second command is expected to fail. This diagnostic probe stays outside the
normal verification command. The generic fold proof requires callback contracts;
it does not assert that every concrete callback translates. Further investigation
remains deferred alongside the borrowed-record callback probe.

## Separated repetition through the shared driver

`SepBy` and `FoldSepBy` use the item parser for the first attempt and
`Right(separator, item)` over shared parser references for subsequent attempts.
The private loop selects by retained item count, so finite empty successes still
invoke separators after the first item. Collection, folding, progress, rollback,
and count checks remain in one driver.

The library and all four repetition families translate at promoted and optimized
MIR with the pinned tools. The normal [Cargo consumer](cross_crate/README.md)
also translates and Lean type-checks separated collection with borrowed item and
separator outputs, and folding with a non-`Clone` separator output and an owned
accumulator. `tools/verify.py` checks these actual library paths; no separate
minimized probe or new tool workaround was needed. Generic Lean proofs establish
the separated-list contracts, while the consumer remains an extraction regression.
The borrowed-accumulator callback limitation above is unchanged and deferred.

## Bind factories containing borrowed parsers

The generic `Bind` implementation translates at promoted and optimized MIR.
The normal Cargo consumer passes with four concrete factory shapes: a checked
scalar count constructing `TakeAligned`, a borrowed first output constructing
an owned `Literal`, a captured `Copy` child placed in `Repeat::exact`, and a
factory returning an existing parser by shared reference. These concrete
translations Lean type-check, and their native tests run in both feature modes.

[`bind_borrowed_parser.rs`](bind_borrowed_parser.rs) instead constructs
`Repeat::exact(&element, count)` inside the factory. The returned parser contains
a reference captured by the closure. Native Rust supports it, but the pinned
Aeneas fails with `Can't end abstraction ... as it is set as non-endable` in
`InterpBorrows.ml`. This reproduces both through a Cargo dependency and with the
library included as a module. Using `Repeat::exact(element, count)` with the
`Copy` child passes. Returning `&element` directly also passes: this is a specific
borrowed aggregate construction boundary, not a blanket ban on factory references.
The error matches the previously recorded callback failures; a shared underlying
cause has not been established.

Reproduce from `rusthammer/` with the pinned tools:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --start-from bind_borrowed_parser::blocks \
  --dest-file target/bind_borrowed_parser.llbc -- \
  --crate-type lib --edition 2021 --cfg 'feature="alloc"' probes/bind_borrowed_parser.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/bind-borrowed-probe \
  -abort-on-error -warnings-as-errors -no-progress-bar target/bind_borrowed_parser.llbc
```

The second command is expected to fail. The probe stays outside the normal
verification command, while that command checks the supported library and
consumer shapes. The Rust API remains unrestricted, and the extraction tools are unchanged.
Further investigation remains deferred.

## Fixed constructors in application proofs

The dependent-format fixture originally used `Bits::new(8).unwrap()` and
`Bits::new(4).unwrap()`. Its correctness proofs checked, but a `#print axioms`
audit also listed Aeneas's abstract formatter type and generated formatting
assumptions through the `Debug` argument to `Result::unwrap`, even though the
constructors always succeeded.

The fixture's private `fixed_bits` helper instead matches the constructor result
and has an explicit panic branch. Its proof establishes successful construction
at both constant widths, so that branch is unreachable. This removes the
formatting dependencies from the application theorems without altering parsing
behavior or the public library. The source includes a comment explaining this
proof-motivated spelling. It is separate from the borrowed-factory extraction
failure above.

## Pattern borrows and loops

`BytePattern<'pattern>` implements `Parser<'input>` with independent lifetimes
and returns the configured pattern slice. The supported library translates at
promoted and optimized MIR. The normal Cargo consumer also translates and Lean
type-checks both direct matching and sequencing with separate pattern and input
borrows in the output. Native tests confirm pointer identity and that the output
can outlive the input and the parser value.

Putting the matching loop directly inside `parse_with`, returning the pattern
slice afterward, failed in the pinned Aeneas with an internal error in
`InterpMatchCtxs.ml`. Copying `self.pattern` to a local before the loop did not
resolve it. The smaller [pattern_loop_borrow.rs](pattern_loop_borrow.rs) reproduces
a loop-context matching failure (`Could not match the contexts`, `InterpJoin.ml`)
at both MIR stages. These observations concern the tested loop and returned
borrow shape; they do not establish a general limitation on independent lifetimes.

The library instead uses a private `match_byte_pattern` helper returning a cursor
and `()`. The parser attaches the configured slice after the helper succeeds.
Both functions translate and have total Lean proofs; no tool patch, extra lifetime
bound, allocation, or API restriction is needed. The source comment explains the
split. Reproduce the failing shape from `rusthammer/`:

```sh
~/source/aeneas/charon/bin/charon rustc --preset=aeneas --sysroot default \
  --mir promoted --start-from pattern_loop_borrow::match_pattern \
  --dest-file target/pattern_loop_borrow.llbc -- \
  --crate-type lib --edition 2021 probes/pattern_loop_borrow.rs
~/source/aeneas/bin/aeneas -backend lean -dest target/pattern-loop-probe \
  -abort-on-error -warnings-as-errors -no-progress-bar target/pattern_loop_borrow.llbc
```

Use `--mir optimized` to check the other stage. The second command is expected
to fail at the pinned revisions above. This diagnostic probe stays outside
`tools/verify.py`, which checks the supported implementation. Investigating the
tool's loop-context matching further remains deferred.

## Signed numeric fields

`SignedBits` reuses `Bits` and a private `sign_extend` helper. Both library MIR
stages translate, including the helper's unsigned-to-signed casts and signed
subtraction. The ordinary Cargo consumer also translates and Lean type-checks
runtime construction returning a separate configuration error, and signed/unsigned
sequencing through a shared parser reference. No new extraction limitation was
encountered, and the actual library paths are checked by `tools/verify.py`.

For a negative `w`-bit value `u`, the helper computes `u - 2^w` as
`-1 - (2^w - 1 - u)`, splitting the inner difference around the sign bit so no
operation constructs `2^64`. All intermediates fit their types even at width 64
and `i64::MIN`; both casts to `i64` preserve their values. The source comment
explains this arithmetic. The helper's Lean contract requires `w <= 64` and
`u < 2^w`, established by validated construction and the unsigned decoder's
proof. This is ordinary bounded arithmetic, not a tool workaround or a reliance
on signed overflow.
