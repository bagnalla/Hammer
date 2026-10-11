# RustHammer v1 core

RustHammer is an experimental, dependency-free Rust parser-combinator library
with an Aeneas translation and Lean proofs. Version 1 executes parsers directly
on complete immutable input slices. **MAVLink 2 packet parsing is the initial
application target.** The current example parses unsigned frames and validates
their CRC with a caller-supplied dialect lookup.

```rust
use rusthammer::grammar::{seq, BeU16, Byte};
use rusthammer::{Cursor, Parser};

let header = seq(Byte, BeU16);
assert_eq!(header.parse(&[7, 0, 3, 99], Cursor::start()),
    Ok((Cursor { byte: 3, bit: 0 }, (7, 3))));
```

The remaining byte is intentional: complete input permits prefix parsing.
Compose `Left { first: parser, second: End }` to require consuming the entire
slice. Transport buffering belongs to the application.

The library is `no_std`, forbids unsafe Rust, and has no default features.
`alloc` enables collecting repetition with `Vec`; folding needs no library
allocation. The public API is experimental. See the [v1 plan](../plans/rusthammer.md)
and [design overview](OVERVIEW.md) for scope, verification, and remaining decisions.

## Execution interface

```rust,ignore
pub trait Parser<'input> {
    type Output;
    fn parse_with(
        &self,
        input: &'input [u8],
        cursor: Cursor,
        byte_order: ByteOrder,
    ) -> Result<(Cursor, Self::Output), ParseError>;
    // The provided parse(input, cursor) method supplies ByteOrder::Big.
}
```

Outputs may borrow the input or independently borrowed parser configuration.
They need neither `Clone` nor `Copy`. `&P` forwards `parse_with` to `P`; its
provided `parse` entry point uses big byte order. Parser nodes can be cloned or
copied when their stored children and callbacks support those operations.

`Cursor { byte, bit }` counts consumed high bits in a byte. Valid cursors have
`bit < 8` and refer to an input byte or exactly `(input.len(), 0)`. Input-reading
primitives validate cursors. Empty grammars such as `Epsilon`, empty patterns,
and repetitions capped at zero preserve the raw entry cursor without adding a
universal validation step.

From a **valid entry**, a supported successful parser returns a valid cursor at
or after that entry. Custom parsers and parsers produced by `Bind` must satisfy
this contract; Rust's trait system does not enforce it. Unbounded repetition
also checks strict progress and rejects invalid or nonadvancing child results.
Choice and lookahead can restore cursors internally. Restoring a cursor does
not undo callback effects.

## Ordering, errors, and borrowing

Bits always traverse each physical byte from high to low. `ByteOrder::{Big,
Little}` controls the significance of successive physical-byte fragments in a
numeric field, including unaligned fields. Big order appends later fragments
below earlier ones; little order places later fragments above earlier ones.
This is observable even for some eight-bit reads starting inside a byte.

```rust
use rusthammer::{Bits, ByteOrder, Cursor, Parser, WithByteOrder};

let message_id = WithByteOrder {
    parser: Bits::new(24).unwrap(),
    byte_order: ByteOrder::Little,
};
assert_eq!(message_id.parse(&[0x12, 0x34, 0x56], Cursor::start()),
    Ok((Cursor { byte: 3, bit: 0 }, 0x563412)));
```

`WithByteOrder` delegates to its child with the selected order. It imposes no
alignment checks. The enclosing order still applies to later siblings.
`BeU16/32/64` and `BeI16/32/64` explicitly pin big order. `TakeAligned` borrows raw
bytes and requires alignment; it never inserts padding or decodes byte order.

`UnexpectedEnd`, `Mismatch`, and `TrailingInput` are recoverable rejections.
`Choice` retries its second child at the original cursor after these errors;
`Optional` returns `None`; negative lookahead succeeds without consuming input.
`InvalidCursor`, `Unaligned`, `NonProgress`, and `CountOverflow` propagate.
A truncated literal reports `UnexpectedEnd` before comparing a conflicting
available prefix, preserving the established error precedence.

`ConfigError` reports invalid widths, unrepresentable literal values, or inverted
bounds during construction. Numeric widths are 0–64. Width zero returns zero
and still validates its cursor. Signed fields use two's complement. Repetition
bounds and integer ranges are inclusive.

`WithSpan<P>` returns `(P::Output, BitSpan)`; `Recognize<P>` returns the span alone.
A span retains the original input and validated start/end cursors, with no bit
order field. Its end cannot precede its start. `as_bytes()` returns the exact
borrowed byte interval when both endpoints are aligned; partial-byte spans expose
the original input and endpoints. Span wrappers validate entry before invoking
the child and validate successful endpoints afterwards.

## Grammar families

Grammar types and constructors are available under `rusthammer::grammar` and
are re-exported at the crate root. Implementation family modules are private.

| Family | Available parsers |
| --- | --- |
| Bits and integers | `Bit`, `Bits`, `SignedBits`, `Literal`, `Byte`, `I8`, `BeU16/32/64`, `BeI16/32/64` |
| Bytes and position | `BytePattern`, `ByteIn`, `ByteNotIn`, `TakeAligned`, `SkipBits`, `Tell`, `End` |
| Composition | `Seq`, `Bind`, `Left`, `Right`, `Middle`, `Ignore` |
| Transformations | `Map`, `TryMap`, `Verify`, `IntRange` |
| Control | `Choice`, `Optional`, `And`, `Not`, `Epsilon`, `Fail<T>` |
| Match restrictions | `ButNot`, `Difference`, `Xor` |
| Order and capture | `WithByteOrder`, `WithSpan`, `Recognize` |
| Repetition | `FoldRepeat`, `FoldSepBy`; `Repeat` and `SepBy` with `alloc` |

The free `seq`, `choice`, `optional`, `map`, `try_map`, `verify`, and `bind`
constructors return their concrete node types. They store children/callbacks;
construction does not parse or invoke callbacks. Callback-taking constructors
use `Parser` and `Fn` bounds for output inference. Their callbacks run only after
the relevant child succeeds. `TryMap` maps callback rejection to `Mismatch`.
`Bind` passes the first value to a factory and parses its returned node at the
first child's end cursor.

`BytePattern` borrows its configuration independently of the input and returns
the configured pattern. `ByteIn` and `ByteNotIn` copy membership into a bitmap.
`ButNot` accepts its first result if the second rejects recoverably or consumes
strictly fewer bits than the first; `Difference` also permits equal lengths.
`Xor` accepts exactly one successful alternative, with recoverable rejection of
the other. Match endpoints are compared without computing machine-sized absolute
bit positions.

Repetition supports exact counts, inclusive finite bounds, and unbounded minima.
A recoverable rejection stops only after the minimum is satisfied. The rejected
attempt's cursor is discarded. Unbounded repetitions check each complete
iteration for valid strict progress and count overflow before retaining/folding
its value. Separated repetition treats separator-plus-item as one later attempt,
rolls back a rejected whole attempt, and retains only item outputs. Fold callbacks
receive owned accumulators, including non-`Clone` values.

## MAVLink and other examples

```sh
cargo run --example mavlink
cargo run --example flags
cargo run --example fields
cargo run --example ordering
cargo run --example spans
cargo run --example constructors
cargo run --example record
cargo run --example matches
cargo run --example dependent
cargo run --features alloc --example repeat
cargo run --example fold_repeat
cargo run --features alloc --example separated
```

The [shared MAVLink grammar](examples/support/mavlink.rs) uses `Bind` for the
payload length, `WithByteOrder` for little-endian fields, and `WithSpan` plus
`Verify` for checksum coverage. It handles the full 24-bit message ID, borrows the
transmitted payload, and accepts arbitrary dialect lookup callbacks with the
specified contract. The runnable sample lookup supports HEARTBEAT. Signed
frames, unsupported incompatibility flags, unknown CRC metadata, and invalid
checksums are rejected. Typed payload decoding and cryptographic authentication
are outside this example; CRC validation does not authenticate a sender.

The [parser proof](lean/RustHammer/MavlinkProofs.lean) covers arbitrary input
buffers, cursors, and ambient byte orders, assuming the dialect callback
terminates and implements its lookup. The [frame properties](lean/RustHammer/MavlinkProperties.lean)
prove aligned success, exact consumption of `12 + payload_length` bytes, the
payload's precise source interval, sender/flag constraints, and CRC coverage from
the length byte through the transmitted payload. A truncated aligned payload
returns `UnexpectedEnd`. The independent [CRC model and proof](lean/RustHammer/MavlinkCrcProofs.lean)
cover arbitrary byte slices and `CRC_EXTRA` and are unchanged by the v1 migration.

Flags, marker, record, and count-prefixed examples also share source between
runnable programs, native tests, and extraction. Application-specific types stay
outside the public library API.

## Verification

Use the pinned toolchain from this directory:

```sh
cargo test --locked --no-default-features
cargo test --locked --features alloc
python3 tools/verify.py --aeneas-dir /path/to/aeneas
```

The verifier checks formatting, both allocation configurations, promoted and
optimized MIR extraction, the normal Cargo [consumer](probes/cross_crate/lib.rs),
strict Lean compilation, and an automatic axiom audit of every production Lean
declaration. Optional local Lake package overrides can be supplied with
`--lean-packages path/to/packages.json`.
Tool revisions are pinned in the repository; Aeneas and Charon binaries must
match those revisions. The generated [Rusthammer.lean](lean/RustHammer/Rusthammer.lean)
is regenerated from Rust, never maintained by hand.

The [Lean auditor](lean/ProofAudit.lean) discovers all modules under
`lean/RustHammer/` plus `lean/RustHammer.lean`, including private and generated
declarations. It uses Lean's axiom-dependency API directly and accepts only
`propext`, `Classical.choice`, and `Quot.sound`. No theorem-name list or printed
diagnostic parsing is needed. To check existing extracted code, run from `lean/`:

```sh
lake build
lake exe proof-audit
```

The full verifier also runs isolated audit regression tests, including deliberate
axioms and admissions confined to temporary fixtures outside the development.

With a locally built C Hammer library, the compatibility subsets can also be checked:

```sh
python3 tools/compare_primitives.py --hammer-lib ../build/opt/src/libhammer.so
python3 tools/compare_matches.py --hammer-lib ../build/opt/src/libhammer.so
python3 tools/compare_ordering.py --hammer-lib ../build/opt/src/libhammer.so
```

These compare acceptance, consumption, and values on complete inputs. Ordering
comparison covers high-first bits and both byte orders, including unaligned fields
and nested scopes. They do not claim full C Hammer API equivalence.

Aeneas still constrains source forms. Match an entire successful `Result` payload
before destructuring it to avoid optimized-MIR cleanup partial moves. Borrowed
callbacks and loop-local borrows may need named adapters or helper functions.
The MAVLink checksum lookup uses closure forwarding in the consumer because a
generic function-item form fails translation. Keep the [direct-v1 probe](probes/direct_v1/README.md)
as evidence for supported shapes and remaining failures.

Proofs establish the stated contracts in the pinned Aeneas models, under child,
factory, callback, and custom comparison contracts. They use only standard Lean
axioms and contain no admitted obligations. They do not verify the compiler or
translator, physical stack/memory limits, allocator failure, or arbitrary
user-defined destructors. Lean models slice contents; native tests check pointer
identity and ownership/drop behavior. The [forward-consumption proofs](lean/RustHammer/ForwardProofs.lean)
make the custom-parser premises explicit.

## Scope and history

V1 excludes alternate backends, partial/streaming inputs, low-first bit traversal,
seeking, permutation, diagnostics, recursion, and native floating-point readers.
There are no compatibility aliases for the removed APIs. Authentication, keys,
and replay state belong to applications. Signature-field parsing or typed MAVLink
payload support would require a separately specified and verified increment.

The [plan](../plans/rusthammer.md#first-version-scope-and-next-steps) records the
remaining MAVLink scope and release review. The [archived plan](../plans/rusthammer-pre-v1.md)
and commit `c5c2643` preserve pre-v1 API, test, and proof evidence. Historical
probes that import retired APIs must be reproduced at that baseline; their
results do not describe the current production API.
