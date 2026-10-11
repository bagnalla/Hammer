# RustHammer design and verification overview

RustHammer v1 is a typed parser-combinator core for direct execution on complete
immutable byte slices. MAVLink 2 framing is the initial target. The current
application example accepts unsigned frames with a borrowed payload and a
validated dialect-dependent CRC. The [README](README.md) describes the public
API; the [plan](../plans/rusthammer.md) records scope and remaining decisions.

## Grammar representation and execution

A grammar is an ordinary Rust value whose type records its children and callbacks.
`Seq<P, Q>` stores two parsers; `Map<P, F>` stores a parser and transformation;
`Bind<P, F>` stores a parser and a factory for the following parser. There is no
runtime grammar graph, generic backend, interpreter state, or engine selection.

One `Parser<'input>` trait declares the associated `Output` and execution method:

```rust,ignore
fn parse_with(
    &self,
    input: &'input [u8],
    cursor: Cursor,
    byte_order: ByteOrder,
) -> Result<(Cursor, Self::Output), ParseError>;
```

The provided `parse` method supplies big byte order. Outputs can be owned or
borrowed, including an input borrow and an independently borrowed configuration
in one result. Outputs need neither `Clone` nor `Copy`. `&P` forwards execution;
node cloning/copying depends only on stored configuration. Constructors store
children and callbacks without invoking them. The seven free construction helpers
return concrete nodes and preserve normal Rust type inference.

Complete input is a property of an invocation, not a demand to consume every byte.
Prefix parsers return a cursor; `End` adds exact consumption. Exhaustion returns
`UnexpectedEnd`. Transport buffering and retries with a new complete buffer are
application responsibilities.

## Input and parser contracts

`Cursor { byte, bit }` tracks a byte index and the number of consumed high bits.
Its canonical end position is `(input.len(), 0)`. Lean uses the unbounded
mathematical position `8 * byte + bit`. Rust advances or compares byte/bit
coordinates directly to avoid absolute-position overflow.

High-first traversal is fixed. Big/little byte order determines how successive
physical-byte fragments contribute to a numeric value. `WithByteOrder` passes an
order to its child without checking alignment; later siblings receive their
enclosing order. Fixed `Be*` readers pin big order. Raw payload slicing does not
interpret byte order.

Input-reading primitives validate cursors. Existing empty grammar behavior is
preserved: for example, `Epsilon`, an empty pattern, or a zero-cap repetition may
return an invalid raw entry cursor unchanged. The supported cursor law therefore
starts from a **valid** entry: successful execution returns a valid position at
or after that entry. It is a semantic obligation for custom implementations and
factory-produced parsers. The trait itself cannot enforce it.

`Mismatch`, `UnexpectedEnd`, and `TrailingInput` permit recovery. Choice retries
at the original cursor; lookahead restores it. Fatal cursor, alignment, progress,
and count errors propagate. Callbacks execute only on the relevant successes;
rolling back a cursor does not undo their effects. Generic proofs require explicit
termination and semantic contracts for children and callbacks.

`WithSpan` validates entry and the child's successful endpoint before constructing
a borrowed interval. `Recognize` discards the child value. Span geometry needs no
direction parameter. Aligned spans expose their exact original bytes.

Repetition uses one shared driver with accumulator operations. Collecting modes
use `Vec` behind `alloc`; folds can operate without allocation. Finite repetitions
permit empty success. Unbounded iterations must strictly advance within the
input, including each whole separator/item attempt, before retaining its output.
Bounds, count overflow, recoverable stopping, and callback order are explicit in
the specification.

## Source organization

| Location | Purpose |
| --- | --- |
| [src/parser_traits.rs](src/parser_traits.rs) | Direct parser trait and shared-reference forwarding |
| [src/input_types.rs](src/input_types.rs) | Cursor, byte order, configuration and parse errors |
| [src/span_types.rs](src/span_types.rs) | Validated borrowed span |
| [src/grammar/](src/grammar/) | Public grammar namespace, with private implementation family files |
| [examples/support/](examples/support/) | Shared application grammars used by examples, tests, and extraction |
| [tests/](tests/) | Oracles, boundary cases, callbacks, ownership/drop and borrow identity tests |
| [probes/cross_crate/](probes/cross_crate/) | Normal Cargo consumer exercising supported public forms |
| [lean/RustHammer/](lean/RustHammer/) | Generated code, independent specifications, and proofs |
| [tools/verify.py](tools/verify.py) | Native, extraction, Lean, and axiom verification gates |
| [lean/ProofAudit.lean](lean/ProofAudit.lean) | Automatic axiom audit of all production Lean declarations |

The core is `no_std`, has no dependencies, and forbids unsafe Rust. Application
formats are not library API. Research probes are separate from production source.

## From Rust to Lean

The pinned Rust toolchain produces MIR; Charon translates selected roots to LLBC;
Aeneas generates [Rusthammer.lean](lean/RustHammer/Rusthammer.lean). The generated
module contains the actual implementations, trait dictionaries, callback code,
and loop bodies. Handwritten proofs refer to those definitions. Regeneration is
part of the verifier, and generated files must not be patched to make proofs pass.

Aeneas's outer `Result` models execution, including panics/failure or divergence.
Inside it, Rust's `core.result.Result (Cursor × Output) ParseError` distinguishes
successful parsing from an ordinary parser error. A totality theorem for the
outer computation can therefore establish both successful and rejecting parsing
without claiming that every input is accepted.

A specification is a relation between input, entry cursor, and a Rust result.
Combinator relations compose arbitrary child relations; proofs relate extracted
execution to those relations under child/callback contracts. Application proofs
instantiate them with numeric decoding, borrowed slices, format constraints, and
checksum specifications.

The build checks both promoted and optimized MIR and separately extracts a Cargo
consumer through its normal path dependency. This catches source patterns that
work in local extraction but fail once the parser is used downstream. Remaining
restrictions and their controls are recorded in the [direct-v1 probe](probes/direct_v1/README.md).

## Proof organization and coverage

| Area | Specifications and proofs |
| --- | --- |
| Cursor, bit and payload primitives | `Spec`, `Proofs`, `BitsSpec`, `BitsProofs`, `CompleteProofs` |
| Direct composition and callbacks | `Spec`, `CompleteProofs`, `ParserProofs`, `Control*`, `Selection*`, `Composition*`, `Bind*` |
| Numeric interpretation | `Order*`, `SignedBits*`, `Integer*`, `IntRange*` |
| Bytes and positions | `Byte*`, `ByteSet*`, `Position*`, `Match*` |
| Borrowed spans | `SpanSpec`, `SpanProofs` |
| Repetition and folds | `Repeat*`, `UnboundedRepeatProofs`, `Iteration*`, `FoldRepeat*`, `SepBy*` |
| Constructors and cursor preservation | `ConstructorProofs`, `ForwardProofs` |
| Applications | `FlagsProofs`, `Record*`, `Dependent*`, marker proofs in `ControlProofs` |
| MAVLink | `MavlinkSpec`, `MavlinkProofs`, `MavlinkProperties`, `MavlinkCrcSpec`, `MavlinkCrcProofs` |

Contracts cover arbitrary raw cursors and complete buffers, including error
precedence, zero-width/count behavior, exact decoded values, unaligned fields,
shared-reference reuse, callback short-circuiting, and borrowed source contents.
Repetition proofs establish loop termination and arithmetic bounds. The forward
cursor laws compose under explicit child contracts and apply directly to the
MAVLink frame relation.

The CRC implementation is compared to an independent bit-vector recurrence for
arbitrary input bytes and `CRC_EXTRA`. MAVLink parsing proofs establish total
execution under a dialect callback contract. Success establishes exact framing
consumption, aligned endpoints, header constraints, the original payload interval,
and the checksum over precisely the transmitted header/payload interval.

Combinators have one relational specification in `Spec`; execution proofs apply
it directly to the Rust result. There are no identity result witnesses or separate
complete-input specifications. Implementation proofs accept arbitrary byte-order
contexts, with default-order theorems as specializations. Numeric family modules
contain both versions together. `RepeatSpec` defines one indexed repetition
relation; ordinary repetition ignores the index, while separated lists use it to
distinguish the first item from later separator/item attempts. Bounded and
unbounded stopping conditions remain distinct, as do their termination arguments.

The migration removes backend projection/state equations, input-finality
conversion, incomplete-input lemmas, seek/offset proofs, permutation proofs,
low-first geometry, and changed-direction scope guards. Retained complete-input,
high-first behavior is proved against regenerated code. The [migration record](../plans/rusthammer.md#verification-and-proof-maintenance)
maps the removed and retained proof areas. The earlier evidence remains at
`c5c2643` and in the archived plan.

## Verification workflow and limits

From `rusthammer/`, run `python3 tools/verify.py --aeneas-dir /path/to/aeneas`.
It checks formatting, tests with and without `alloc`, both MIR stages, consumer
roots, full Lean compilation, absence of admissions/opaque project declarations,
and standard-only axioms for every production Lean declaration. `lake build` in
`lean/` builds the root and all source modules recursively without regenerating
Rust extraction. `lake exe proof-audit` then discovers those modules and audits
their compiled declarations using `Lean.collectAxioms`. Module ownership selects
the declarations, including private helpers and generated definitions; dependency
axioms are checked transitively. The three standard axioms are the only explicit
allowlist. Local package overrides are supported for existing Aeneas/Lean
dependency checkouts.

The verifier also exercises the auditor with temporary fixtures: permitted
axioms, unused private axioms in newly discovered modules, admitted proofs,
transitive dependency axioms, and missing or empty developments. These fixtures
are outside the production proof modules.

The trust boundary includes the pinned Rust compiler, Charon, Aeneas, its
standard-library models, and Lean's kernel. Proofs do not establish physical
resource bounds or recoverable allocation failure. The Aeneas vector model
abstracts allocation and stores a bounded list; loop count obligations are proved.
Arbitrary user destructors are outside that model. Native tests check ownership,
drop behavior, and pointer identity because Lean's slice model retains contents.

C differential tests compare explicit retained subsets, not the whole C API.
High-first ordering, primitive decoding, and match restrictions retain C behavior
on complete inputs. There are no claims about retired bit directions or engines.

Authentication, signing keys, and replay protection remain application concerns.
CRC acceptance is not authentication. The current frame proof does not decode
message payloads, accept signed frames, or prove conformance to every dialect.
Those extensions require explicit scope and their own contracts.
