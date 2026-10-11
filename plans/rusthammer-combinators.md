# RustHammer combinator API plan

Status: v1 API plan revised 2026-10-10; implementation migration pending.
The implemented families below are verified at the pre-migration checkpoint
`c5c2643`; additional conveniences remain proposals. V1 keeps complete-input
behavior for retained high-first parsers while replacing backend/finality
plumbing with the [single direct parser interface](rusthammer.md#parsing-interface).
Permutation, seeking, low-first bit traversal, and diagnostic annotations are
excluded from v1; their implementation/research evidence remains labelled below.
Claims about existing proof files and extraction counts describe that baseline,
not a completed migration.

The first version targets nonrecursive grammars over complete inputs. Recursion,
packrat, streaming, and native floats remain outside v1. The
[backend research](rusthammer-backends.md) and [recursion writeup](rusthammer-recursive-rules.md)
preserve evidence without imposing extension points on the simplified API.

MAVLink 2 packet parsing is the v1 target application. The
[application contract](rusthammer.md#target-application-mavlink-2-packet-parsing)
prioritizes sequential framing, little-endian fields, length-dependent borrowed
payloads, and CRC validation. The additional feature cuts are adopted decisions.
V1 retains high-first unaligned bit parsing and big/little byte order, with a
forward-consumption contract for supported custom parsers and `Bind` results.
Authentication, key management, and replay policy belong to application code.

## Agreed API scope

The 2026-10-10 simplification updates the earlier parity review and
floating-point investigation with the following scope. RustHammer does not
require a counterpart for every C combinator.

| Capability | Decision |
| --- | --- |
| Execution and input | Direct execution on complete slices only. Remove backend capabilities, input finality, and `NeedMore`; retain prefix parsing and explicit `End`. |
| Permutation | Deferred beyond v1. Remove `Permutation`, `Required`, `permutation`, `required`, search/tuple machinery, and their active proof/extraction roots. Keep the ordinary `Optional` combinator. |
| Floating-point fields/ranges | Exclude from the first version due to the pinned Aeneas limitations. Retain as a later capability; the [probe report](../rusthammer/probes/floating_point/README.md) preserves the evidence and required tool/model work. |
| Seeking and diagnostic annotations | Deferred beyond v1. Remove `Seek` and its exclusive helpers/example/proof roots; keep `SkipBits` and `Tell`. Add no diagnostic annotations, observer hooks, or reporting state. Preserve [seeking](rusthammer-seeking.md) and [diagnostics](rusthammer-diagnostics.md) evidence for later work. |
| Bit direction and byte order | High-first traversal only. Keep big/little byte order through `ByteOrder` and `WithByteOrder`; remove combined order context, bit-direction guards, and direction stored in spans. |
| Signing/authentication | Application responsibility. Keep generic validation callbacks, but add no cryptographic primitives, key store, or replay state to the v1 core. |
| Deferred actions (`h_action_stash`, `h_action_apply`) | Omit from the intended API. Ordinary transformations through `Map`, `TryMap`, and predicates remain supported; application effects can follow successful parsing. |
| Dedicated dispatch (`h_dispatch`) | Omit from the intended API. Express tagged formats through `Choice` or `Bind`, using explicit typed parser alternatives where needed. |
| Named parse-local value storage (`h_put_value`, `h_get_value`, `h_free_value`) | Exclude from the first version; its longer-term role is undecided. Use explicit typed values and `Bind` for field dependencies. Revisit only when a concrete grammar motivates shared storage, considering an explicit typed environment before a string-keyed store. |

The storage decision concerns values shared by application grammar components.
V1 removes the generic backend boundary; field dependencies continue to use
explicit outputs and `Bind`.
The detailed inventory below records the retained capabilities and marks
excluded families as deferred. Diagnostic annotations, recursive construction,
and their extraction investigations do not gate the v1 migration.

## API policy

Production APIs and implementations must have an intended place in the finished
library. Do not add public types, internal algorithms, or representations merely
because they are convenient implementation or proof milestones and are intended
to be replaced. Implement and prove retained parts of the intended design
incrementally; keep compatibility experiments in `probes/` and application-specific
grammars in examples or proof fixtures. Do not export unsupported modes or
placeholder implementations, or hide disposable implementations behind private
helpers or feature flags.

This does not require freezing every signature now. Resolve a feature's output,
failure, consumption, ownership, and verification requirements before exporting
it. Changes supported by new evidence remain possible while the API is experimental.

Convenience operations are useful permanent API when they express common grammar
intent. They should compose existing operations or share their implementation.
Different names do not require different parsing algorithms or independent proofs.

## Construction functions and return types

Retain concrete grammar nodes and an associated output type for each input
lifetime. The target places that type directly on `Parser<'input>` and removes
`Grammar` and `Eval`. The [direct-v1 probe](../rusthammer/probes/direct_v1/README.md)
checks all seven generic helpers and representative uses at both MIR stages and
through a Cargo consumer; no separate output-only trait is needed for those cases.

Free `seq`, `choice`, `optional`, `map`, `try_map`, `verify`, and `bind` helpers
continue to return nodes such as `Seq<P, Q>` or `Map<P, F>`. Construction only
stores configuration and never invokes a parser or callback. Keep unconstrained
constructors where possible; use `Parser` bounds when output relationships or
callback parameter inference need them. Validated constructors keep their
configuration checks. There is no interpreter selection at construction time.

A factory can hide its callback as `Map<P, impl Fn(...) -> ...>` or expose a
whole parser as `impl Parser<'input, Output = T>`. Both are reasonable when they
express the intended contract. Concrete core constructor returns still aid
composition and preserve visible structure and conditional `Copy`/`Clone`.
Opaque returns must expose any required extra bounds and preserve input/output
lifetime relationships; they no longer need to preserve multiple backends.

The [constructor probes](../rusthammer/probes/constructors/README.md) and
[constructor proofs](../rusthammer/lean/RustHammer/ConstructorProofs.lean)
record the old boundary's compatibility and construction equations. The new
probe rechecks the single-trait shape for owned/borrowed results, references,
non-`Clone` outputs, opaque returns, and ordinary downstream use. Remove
backend-only fixtures after retaining useful construction and ownership coverage.
Port the equations and
contract-transport proof to the actual new constructors.

The tested backend-free method-local callbacks pass, while the old unused-backend
type-argument failure still reproduces. External factories are no longer required
solely for that parameter in the tested shapes. Borrowed identity mapping still
fails; borrowed accumulators remain a separate limitation. Keep named adapters
and whole-payload `Result` moves, and check each migrated source form. The new
probe also records function-item, borrowed-loop, and nested-predicate limitations;
it does not establish unrestricted callback extraction.

## Core combinator families

`A` and `B` below denote child output types for the input lifetime. All operations
use static dispatch and retain typed outputs, including borrowed and non-`Copy`
values. Only collecting operations require the optional `alloc` feature.

| Family | Intended API and output | Implementation and Hammer correspondence |
| --- | --- | --- |
| Sequencing | `Seq<P, Q>` produces `(A, B)`. | Already implemented. Run children in order, passing the successful cursor onward. Corresponds to `h_sequence`. Retain binary sequencing; any later tuple syntax should compose it or share its semantics and implementation. |
| Ordered alternatives | `Choice<P, Q>` produces their common output type. | Already implemented. Retry recoverable rejection at the original cursor. Map alternatives into an enum when their natural outputs differ. Corresponds to `h_choice`. |
| Optionality | `Optional<P>` produces `Option<A>`. | Already implemented; corresponds to `h_optional`. Empty success is `Some`, not absence. |
| Output transformation | `Map<P, F>` produces `B`; `Verify<P, F>` preserves `A` when its predicate holds. | Already implemented. Typed counterparts of transforming `h_action` callbacks and `h_attr_bool`. These do not supply deferred-effect semantics. |
| Checked transformation | `TryMap<P, F>` produces `B` from a callback returning `Result<B, E>`. | Implemented and proved. Run the callback once after child success; conversion rejection becomes recoverable `Mismatch`. Useful for checked integer conversions and validated data construction without panicking or computing the conversion twice. |
| Lookahead | `And<P>` and `Not<P>` produce `()`. | Already implemented; correspond to `h_and` and `h_not`. Restore the original cursor on success. |
| Selecting sequence outputs | `Left<P, Q>`, `Right<P, Q>`, `Middle<L, P, R>`, and `Ignore<P>` return `A`, `B`, the middle output, or `()`, respectively. | Implemented and proved; correspond to `h_left`, `h_right`, `h_middle`, and `h_ignore`. Derived from sequencing and output projection. Arbitrary `h_drop_from` becomes typed tuple projection. |
| Empty and failing grammars | `Epsilon` produces `()`; `Fail<T>` always rejects with `Mismatch`. | Implemented and proved; correspond to `h_epsilon_p` and `h_nothing_p`. Neither reads input; `Epsilon` preserves the supplied cursor without validation. `Fail::new()` is infallible and needs an inferred or explicit output type so it composes with typed alternatives. |
| Repetition | `Repeat<P>` produces `Vec<A>` with `alloc`. | Exact, finite bounded, and unbounded forms are implemented and proved, replacing `RepeatN` and covering `h_repeat_n`, `h_many_cap`, `h_many1_cap`, `h_many`, and `h_many1`. |
| Folding repetition | `FoldRepeat<P, I, F>` produces an accumulator `R`. | Implemented and proved. Same count and stopping rules as `Repeat`; initialize a fresh accumulator and update it with each output. Supports allocation-free counting, discarding, checksums, and application accumulators. No C wrapper is required to justify this separate output policy. |
| Separated repetition | `SepBy<P, S>` produces `Vec<A>` with `alloc`; `FoldSepBy<P, S, I, F>` produces an accumulator without library allocation. | Implemented and proved. One count policy covers `h_sepBy` and `h_sepBy1`, as well as finite limits. Parse the first item, then separator/item pairs; discard separator outputs. |
| Value-dependent sequencing | `Bind<P, F>` produces the output of the parser selected or constructed from `A`. | Implemented and proved. Corresponds to `h_bind`. Run the first child, move its value into the factory, then run the resulting parser at the next cursor. |
| Match restrictions | `ButNot<P, Q>` and `Difference<P, Q>` preserve `A`; `Xor<P, Q>` requires a common output type. | Implemented and proved; correspond to `h_butnot`, `h_difference`, and `h_xor`. Compare matches starting at the same cursor; see below. |

Output selection moves retained values and drops the others without requiring
`Copy` or `Clone`. The implemented helpers use `Seq` over shared references and
tuple pattern matching, preserving sequencing behavior without callback requirements.
Their public fields are `first`/`second`, `left`/`parser`/`right`, and `parser`,
respectively. All children must succeed, and the final cursor includes discarded
children's matches. Errors propagate before later children run.
`Ignore(Repeat(...))` would still build a vector: use a unit accumulator to discard
repeated outputs without allocating. Units are ordinary typed values; sequencing
and collection do not automatically erase them as C's null AST handling does.

For a parse that must consume the entire input, compose `Left(parser, End)`.
Every input is complete in v1, but prefix success remains valid without `End`.
Forward `Parser` through `&P` to reuse immutable parsers without cloning them.
Combinators call `parse_with` with the active `ByteOrder`; `parse` supplies big
byte order. Bit traversal is always high-first. Input borrowing remains
independent of the parser reference's lifetime.
The actual Rust syntax is `Left { first: parser, second: End }`.

Parser structs derive `Clone` and `Copy` conditionally on their stored children
and callbacks. Primitive settings and fixed example grammars support both traits.
These bounds do not constrain parsed output types or the `Parser` trait itself;
for example, `Repeat<Bit>` can be copied while returning a fresh `Vec<bool>` on
each parse. Larger grammar copies duplicate their stored configuration, and
cloning delegates to the fields' implementations, which may allocate. References
remain available when copying is costly or children implement neither trait.

## One repetition design

The collecting interface is:

```rust,ignore
Repeat::exact(parser, count)       // Implemented: Repeat<P>; infallible
Repeat::new(parser, min, max)       // Implemented: Result<Repeat<P>, ConfigError>
Repeat::at_least(parser, min)       // Implemented: Repeat<P>; infallible, no finite maximum
```

Counts are runtime `usize` values; finite bounds are inclusive. Keep the bounds
private, validate `min <= max` during construction, and provide read-only
accessors. `min()` returns `usize`; `max()` returns `Option<usize>`, with `Some`
for finite constructors and `None` for `at_least`. The absent maximum is explicit
internally too; `usize::MAX` is a valid finite count. Exact construction sets
both bounds to `count` and cannot fail. The folding and separated forms reuse
this count policy and corresponding constructors. Folding is implemented as
`FoldRepeat::exact(parser, count, init, fold)`,
`FoldRepeat::new(parser, min, max, init, fold)`, and
`FoldRepeat::at_least(parser, min, init, fold)` with the same bounds accessors.
Separated forms are implemented as `SepBy::exact(parser, separator, count)`,
`SepBy::new(parser, separator, min, max)`, and
`SepBy::at_least(parser, separator, min)`; `FoldSepBy` has the same constructors
with `init, fold` appended. All four families share private validated bounds.

| Hammer expression | Rust form |
| --- | --- |
| `h_repeat_n(p, n)` | `Repeat::exact(p, n)` |
| `h_many_cap(p, n)` | `Repeat::new(p, 0, n)` |
| `h_many1_cap(p, n)` | `Repeat::new(p, 1, n)`; `n == 0` is a configuration error |
| `h_many(p)` | `Repeat::at_least(p, 0)` |
| `h_many1(p)` | `Repeat::at_least(p, 1)` |
| `h_sepBy(p, s)` | `SepBy::at_least(p, s, 0)` |
| `h_sepBy1(p, s)` | `SepBy::at_least(p, s, 1)` |

All variants follow these rules:

1. Stop successfully at the finite maximum without attempting another child.
   A maximum of zero invokes no child and preserves the supplied cursor without
   validating it, matching the existing exact-zero contract.
2. On recoverable rejection, succeed with the accumulated result if the minimum
   has been met; otherwise propagate that rejection. A rejected attempt consumes
   nothing in the returned success, even if the child parsed a prefix internally.
3. Propagate fatal errors, including after the minimum is met. Exhaustion is
   recoverable `UnexpectedEnd`, so it follows rule 2. Previously collected
   outputs are discarded on an unsuccessful overall result.
4. Finite repetition permits empty successes: the iteration count ensures
   termination. This deliberately differs from nom's `many_m_n` progress check.
5. Unbounded repetition validates the initial cursor before invoking the child.
   Each successful iteration must return a valid cursor and strictly advance.
   An invalid cursor returns fatal `InvalidCursor`; an empty or backward success
   returns fatal `NonProgress`, even after the minimum. Compare byte/bit offsets
   directly, avoiding a machine-sized absolute bit index.
6. After these progress checks, retaining another value at `usize::MAX` returns
   fatal `CountOverflow` before increment or vector push. Reaching that count
   alone does not stop unbounded repetition: a recoverably rejected next attempt
   can still finish it, and a fatal child error still propagates.
   Finite repetition stops at its explicit maximum, so its count cannot overflow.

For separated lists, a repeated attempt consists of the separator and following
item together. If either rejects recoverably after the minimum, restore the cursor
to before the separator. Thus a trailing separator remains unconsumed; enclosing
`End` will reject it. Fatal errors still propagate. Reaching the
maximum consumes no following separator. For unbounded lists, check progress of
the first item and then each whole separator/item iteration, as Hammer's direct
implementation does; finite lists allow empty successes.
Thus an empty first item is rejected for an unbounded list; later empty items
are allowed when their separators advance, and empty separators are allowed when
their following items advance. Count and progress checks precede retention or folding.

Collection and folding, with or without separators, share private validated
`RepeatBounds`, one `repeat_run_with` iteration driver, a private accumulator
trait, and a list-based Lean specification. The driver uses the item parser
for the first attempt and a supplied parser for subsequent attempts. Ordinary
repetition supplies the same child twice; separated repetition supplies
`Right(separator, item)` over shared references. The logical attempt contract is
indexed by retained item count; the constant-contract specialization preserves
the existing repetition specifications and proofs. A fold uses
an initializer `Fn() -> R` and a step `Fn(R, A) -> R`, so the accumulator is passed
explicitly and outputs need not be cloned. Initialization runs once, after the
unbounded starting-cursor check, including for a zero maximum. Steps run after
successful-child progress/count checks. An overall error discards the
accumulator; a fresh invocation initializes again. A recoverable stopping attempt
after the minimum returns the accumulated value. Callback effects are not rolled
back.
The driver translates at promoted and optimized MIR. A separate Cargo consumer
checks captured initialization and borrowed child outputs with owned accumulators.
A borrowed accumulator returned by callbacks reproduces the deferred Aeneas
non-endable-abstraction error; see the [probe notes](../rusthammer/probes/README.md#folding-and-borrowed-accumulators).

`FoldRepeat` has a lasting purpose because it changes storage and output behavior.
Another exact-count type returning the same vector does not. A future parser
returning `[A; N]` would likewise be a distinct output capability, but it is not
needed in the initial API and should not be added merely to retain `RepeatN`.

Keep the existing allocation assumptions explicit: using `Vec` does not establish
recoverable allocation failure or a resource budget. Collection should grow with
successful iterations rather than reserve an input-derived count in advance.

## Dependent parsing and reusable helpers

The implemented `Bind { parser, then }` factory has the shape `Fn(A) -> Q`, where
`Q` implements `Parser<'input>`. For a given input lifetime, it returns one
concrete parser type;
input values may change that parser's configuration. Choosing heterogeneous
branches requires a typed parser enum or another explicitly represented choice.
Static dispatch does not make a Rust return type depend on a runtime value.

The factory is called once after first-child success and never after its error.
Its parser consumes from that success cursor. `Fn` permits repeated
use of a grammar; neither purity nor termination follows from that trait bound.
Generic proofs require factory and child-parser family contracts only for
reachable first-stage successes. Retain the proved final-input behavior:
first-stage errors skip the factory without assumptions about it.
Neither parsed outputs nor constructed parsers need copying or cloning.

Promoted/optimized MIR and a normal Cargo consumer pass for scalar factories,
borrowed first values used to build owned parsers, copied children inside new
parsers, and returning an existing parser by reference. Returning a new parser
containing a captured reference, such as `Repeat::exact(&element, count)`, fails
with the recorded non-endable-abstraction error. Copying a `Copy` child into the
returned parser passes; native Rust supports both. The focused
[probe](../rusthammer/probes/README.md#bind-factories-containing-borrowed-parsers)
records this boundary without changing the Rust API. Further callback investigation
remains deferred.

The verified [dependent examples](../rusthammer/examples/support/dependent.rs)
decode an eight-bit count limited to 64, then read borrowed aligned bytes or
collect four-bit elements. Lean proves their independent format contracts and
exact contents/counts/consumption. Examples and native tests share the same source;
a private extraction-only module supplies the application proof fixtures without
adding public demo types or a Cargo feature. Named convenience wrappers below
remain proposals; their compositions now work through `Bind`.

Build these permanent conveniences from the core, rather than separate engines:

| Helper | Composition and intended meaning |
| --- | --- |
| Length-counted elements | Decode and check a count, then `Repeat::exact(element, count)`. This is Hammer's `h_length_value`; prefer the unambiguous name `LengthCount`. |
| Length-prefixed aligned bytes | Decode and check a byte length, then construct `TakeAligned`. Preserve the length in the typed output if the application needs it. |
| Numeric ranges | Implemented and proved: `IntRange::new(parser, lower, upper)` returns `Result<IntRange<P, T>, ConfigError>` and delegates to `Verify`. Inclusive bounds have the output type; private fields and a fallible constructor reject reversed bounds with `InvalidBounds`. Immutable accessors borrow both endpoints. Corresponds to `h_int_range`, and to `h_ch_range` when the child is `Byte`. |
| Byte sets | Implemented and proved: `ByteIn::new(bytes)` (`h_in`) and `ByteNotIn::new(bytes)` (`h_not_in`) use `Verify` over `Byte` and return `u8`. Own private 32-byte bitmaps with O(1) membership, infallible `const` constructors, `const accepts(byte)` queries, and `Copy`/`Clone`. Empty sets and duplicates are valid; decoding always precedes membership testing. |
| Leading whitespace | Skip repeated ASCII whitespace, then return the following parser's output, corresponding to `h_whitespace`. Specify the ASCII set explicitly instead of importing locale-dependent `isspace` behavior. |

Tagged formats remain expressible through `Choice` or `Bind`; the
[scope decision](#agreed-api-scope) excludes a dedicated `h_dispatch` counterpart.
Applications can represent heterogeneous parser branches explicitly with a typed
enum and retain the tag in their output when needed. This remains ordinary
composition, with the existing extraction limits on callback forms.

`TryMap` is useful when decoding counts: overflow during conversion to `usize`,
an application length limit, or invalid input-derived parser configuration is
input rejection. A programmer's invalid fixed configuration remains a constructor
error. Do not use `unwrap` inside the parser to bridge that distinction. A factory
that can fail can first produce a checked parser value with `TryMap`, then use
`Bind` to execute it.

Do not confuse element counts with byte windows. nom's `length_count` matches
Hammer's `h_length_value`; nom's `length_value` limits a child to a byte region.
A future bounded-region combinator needs a separate contract for the
inner complete slice, full consumption versus permitted leftovers, and cursor
translation to the outer input. Do not introduce a count-only public stand-in for that operation.

## Match restrictions and permutation

The implemented and proved Rust operations preserve these distinctions from the
[C implementations](../src/parsers/):

| Operation | Success condition |
| --- | --- |
| `ButNot(p, q)` | `p` succeeds and `q` rejects, or both succeed and `p` matches strictly more input. |
| `Difference(p, q)` | `p` succeeds and `q` rejects, or both succeed and `p` matches at least as much input. |
| `Xor(p, q)` | Exactly one child succeeds. Return that child's value and cursor. |

Run children from the same original cursor. A first-child rejection short-circuits
`ButNot` and `Difference`; otherwise run the second child. These two return the
first child's value and cursor on acceptance. `Xor` must check the second child
after a first success or recoverable rejection. Propagate fatal errors from
attempted children; when both `Xor` children reject, return the second
rejection, and when both succeed return `Mismatch`.

The two length restrictions share one private driver, differing only on equal
lengths. Their children may have unrelated outputs; the second output is discarded.
`Xor` has `Choice`'s common-output constraint. Applications can use `Map` to
construct their own enums; no automatic sum-output variant is introduced.
Parser values are `Copy`/`Clone` when their children are, without output bounds.

For the forward cursor model, compare consumed bit spans, not output sizes or
rounded byte counts. C's `token_length` returns `HParseResult.bit_length`.
Rust orders byte-and-bit endpoints directly, without absolute machine bit counts
or subtraction. Lean proves equivalence to mathematical consumed lengths for
normalized forward matches. As with `Choice`, children retain responsibility for
cursor validation; speculative effects in custom parsers are not rolled back.
The optional C comparison agrees on 1,879,635 complete-input cases, including
lookahead, discarded prefixes/suffixes, zero/equal/unequal lengths, all bit
offsets, nonzero byte starts, and truncation. Native tests and compositional
proofs at that checkpoint also covered partial input and fatal errors. Retain
the final-input cases and fatal-error coverage in v1. Both MIR stages and all
40 consumer entries pass, including enum-mapped alternatives and borrowed outputs.
The revised [input plan](rusthammer-input.md) retains this `(byte, bit)`
comparison with high-first traversal and nondecreasing successful cursors.
V1 parser contracts carry `ByteOrder` and the forward-consumption law; there is
no input-status parameter or supported backward-seeking child. The baseline's
signed-displacement extension remains recorded in the
[deferred seeking design](rusthammer-seeking.md#composition-audit). Port the
forward-consumption theorem; signed-displacement support is not a v1 obligation.
In particular, `ButNot` and `Difference` cannot be replaced by sequencing with
`Not(q)`: they may accept when both children succeed.

### Deferred permutation: baseline contract

Permutation is excluded from v1. The rest of this section records the baseline
implementation and proof evidence, not production work to migrate. Reproduce it
at `c5c2643` until the feature is deliberately resumed. It does not constrain the
new parser trait or forward-consumption contract.

The baseline implements `permutation((required(a), optional(b), ...))`,
returning the concrete `Permutation<T>` node. `required` constructs `Required<P>`;
optional entries use the existing `Optional<P>`. Entry wrappers are explicit,
because arbitrary typed values do not carry C's dynamic `TT_NONE` tag. Outside
permutation, `Required<P>` delegates to its child unchanged. Both new constructors
are unconstrained `const fn`s and execute no parser or callback.

The supported tuple arities are zero through twelve, with heterogeneous outputs
in declaration order. The search tries unmatched entries in that same priority
order and retries another ordering when a successful prefix leaves a recoverably
rejected suffix. It does not revisit alternatives inside an already successful
child. Optional absence is accepted only when every remaining entry is optional
and rejects at the current cursor. An actual empty success fills its slot;
`required(optional(p))` remains a required slot, even when its value is `None`.
Fatal errors stop immediately; recoverable exhaustion can trigger backtracking.
Exhausted orderings return `Mismatch`. The empty tuple succeeds without cursor
validation.

One search handles all arities without allocation or output cloning. Separate
slot presence and match flags allow speculative values to be dropped and accepted
values to be moved, including independent input/configuration borrows. Backtracking
restores the cursor without rolling back callback effects, consistently with
`Choice`. The baseline also preserves backend state; both backend plumbing and
permutation are outside v1. Termination uses the pair of remaining entries and
remaining candidates, so empty matches are permitted.
Ambiguity can require factorial work;
the current implementation uses the call stack. Candidate scanning is recursive
too, giving an inspected conservative bound of `n² + 1` active search calls
(145 at twelve entries), excluding child calls. The termination proof does not
bound stack consumption in bytes or establish freedom from stack overflow.
Large inline outputs, nested permutations, and small stacks remain concerns.
If permutation is resumed, evaluate stack usage and extraction-compatible
iterative search with bounded explicit backtracking storage before settling the
resource guarantees. This work does not gate v1.

The [search proofs](../rusthammer/lean/RustHammer/PermutationProofs.lean) establish
agreement with a total natural-number model under child and storage contracts,
including backend transitions, partial/fatal propagation, and safe counters in
the baseline. Retire these search/tuple contracts from the v1 proof roots;
retain them as evidence for a later permutation design.
[Tuple equations](../rusthammer/lean/RustHammer/PermutationTupleProofs.lean) cover
initialization, selected-slot access/clearing, typed output assembly, and child
dispatch for every supported nonempty arity; the empty case has a separate theorem.
All 82 new theorems are axiom-audited. Native tests cover ownership, ordering,
nullable/optional entries, ambiguous prefixes, and a 13,608-case independent
required-pattern oracle. Both MIR stages and the expanded 57-entry Cargo consumer
pass extraction and Lean checking. The optional
[C comparison](../rusthammer/probes/permutation/README.md) adds 217,728 agreements
on acceptance, consumption, presence, and declaration-order values. No extraction
tool changes were needed; the probe notes record the supported source shapes.

## Primitive support and later capabilities

The combinators above also need a deliberate primitive and extension inventory:

| Capability | Direction |
| --- | --- |
| Bits, unsigned numbers, numeric literals, exact EOF | Retain `Bit`, `Bits`, `Literal`, and `End`. Implemented and proved: `Byte`, `BeU16`, `BeU32`, and `BeU64` correspond to `h_uint*` under default ordering, with native unsigned Rust outputs. Fixed-width readers are zero-sized `Copy`/`Clone` values with no configuration or fallible constructor. |
| Signed numbers | Implemented and proved: `SignedBits::new(width)` corresponds to `h_bits(width, true)` and returns `i64` for widths 0 through 64. Zero width returns zero after validating the cursor. Nonempty fields use specified two's-complement interpretation; every arithmetic intermediate and cast is proved in bounds. `I8`, `BeI16`, `BeI32`, and `BeI64` now correspond to `h_int*` under default ordering, with native signed outputs and proved lossless narrowing. |
| Byte/token parsing | Implemented and proved: `Byte` (`h_uint8`) returns `u8`; `BytePattern::new(&pattern)` (`h_token` / `h_literal`) borrows an arbitrary byte pattern and returns that configured slice on success. Input and pattern lifetimes are independent. Both support unaligned starts without allocation. Empty patterns succeed without cursor validation; nonempty patterns compare complete bytes in order. `h_ch` can be a later literal-reader convenience. |
| Byte sequences | Keep `TakeAligned` for borrowed slices. `Repeat::exact(Byte, count)` now supplies `h_bytes`-style decoded `Vec<u8>` with `alloc`; a named convenience can be added if useful. Never silently align unaligned input. |
| Skipping and position | Implemented and proved: `SkipBits::new(bits)` discards any `usize` bit count and returns `()`; `Tell` reports the validated `Cursor` without consuming. Both validate even at zero consumption and preserve `h_skip` and `h_tell` capabilities. Skips advance in constant time, return `UnexpectedEnd` on exhaustion, and have an infallible `const` constructor and `bits()` accessor. Position reporting avoids an absolute machine bit count; see the [known C overflow issue](rusthammer.md#known-c-issue-absolute-bit-position-overflow). |
| Recognizing matched input | Retain `BitSpan`, `Recognize`, and `WithSpan`, with validated input/endpoints and high-first geometry. Remove stored bit direction and its constructor argument/accessor. Borrowed byte views still require aligned endpoints; see the [input plan](rusthammer-input.md#matched-input-spans). |
| Floating-point fields/ranges | Deferred beyond the first version due to the pinned Aeneas limitations. Retain counterparts of `h_float16`, `h_float32`, `h_float64`, and `h_float_range` as later capabilities. Settle bit decoding, NaNs, infinities, signed zero, range-bound precision, and the required Aeneas models/translation support before exporting readers or range helpers. |
| Bit and byte order | High-first traversal with configurable `ByteOrder`; `WithByteOrder` delegates without alignment guards. Keep unaligned/cross-byte fields and both byte orders, with `Be*` pinning big order. Remove `BitOrder`, combined `Order`/`WithOrder`, low-first paths, and changed-direction guards; see the [input plan](rusthammer-input.md#ordering-scopes). |
| Recursion | Outside v1, including the related extraction-tool work. The [writeup](rusthammer-recursive-rules.md) preserves the fixed-point construction proposal, extraction failures, and soundness/termination gates. Reassess that design and any packrat lowering when resumed; neither constrains the v1 interface. C uses `h_indirect`/`h_bind_indirect` for two-step fixed-point construction. |
| Named parse-local value storage | Outside the first version; longer-term support is undecided. Express ordinary dependencies with typed values and `Bind`. A concrete shared-environment use case must motivate reconsideration, with explicit value types, ownership, scope, backtracking, and eventual memoization semantics. |
| Deferred actions | Intentionally omitted under the [scope decision](#agreed-api-scope); ordinary mapping and predicates retain their current contracts. |
| Diagnostics | Deferred beyond v1. Keep ordinary `ParseError` outcomes; add no labels, source-location metadata, observer hooks, or reporting state. The [investigation](rusthammer-diagnostics.md) preserves later scope/selection and extraction obligations. |
| Packrat and other execution engines | Outside v1. The [historical backend plan](rusthammer-backends.md) preserves research; remove the generic execution boundary. Later engines need a new design and their own correctness/refinement proofs. |
| Seeking | Deferred beyond v1. Remove `Seek` and the offset-field application from production, extraction, and proofs. Keep shared forward-advancement arithmetic, `SkipBits`, and `Tell`. Preserve the [baseline design](rusthammer-seeking.md) for later work. |
| Streaming | Retain buffering/resumption as a separate later capability, with explicit ownership, state, termination, and semantic-equivalence contracts. |

C allocator variants, variadic/array calling variants, dynamic AST extraction,
and vtable plumbing do not need one-for-one public replacements. Permanent Rust
helpers should represent grammar operations or output needs.

The [2026-10-07 floating-point probe](../rusthammer/probes/floating_point/README.md)
records the current extraction gate: integer encodings translate, but native
float outputs and range comparisons do not meet the pinned toolchain's Lean
requirements. It also records C's binary16-to-binary32 widening and its use of
double-precision bounds even for binary32 values. Those range-precision and
special-value contracts must be settled along with tool/model support before
exporting float readers or range helpers. Native floats and their tool/model work
are deferred at the user's request; the probe remains evidence for later work.

## Implementation order and migration

Follow the [main plan](rusthammer.md#first-version-scope-and-next-steps). The cuts
are settled: port the retained families and retire excluded source/proof roots
in one coherent migration. No dummy implementation or compatibility feature is
needed for later backends, diagnostics, permutation, seeking, or low-first order.

| Area | Required migration and retained coverage |
| --- | --- |
| Traits and constructors | One direct `Parser`, reference forwarding, concrete nodes, output inference, conditional parser copying, independent borrows, and explicit supported callback forms. |
| Primitives, byte ordering, spans | `Result` and `ByteOrder`; retain high-first decoding/cursors, complete-input errors, unaligned reads, and aligned byte views. Simplify scopes and erase span direction. |
| Sequence, selection, mapping, predicates, `Bind` | Direct child calls, success-only callbacks, checked rejection, move/drop behavior, and forward-consumption preservation under child/factory contracts. |
| Choice, optionality, lookahead, match restrictions | Recoverable `UnexpectedEnd` follows final-input rules. Retain internal rollback, short-circuiting, fatal propagation, and nondecreasing successful endpoints. |
| Repeat/fold/separated families | Remove incomplete branches; retain minima/maxima, strict unbounded progress, count safety, separator rollback, and owned/borrowed outputs. |
| Permutation and seeking | Remove dedicated nodes/helpers/exports, fixtures, roots, and audits. Preserve shared `Optional`, forward cursor arithmetic, and baseline evidence for excluded features. |
| Diagnostics and authentication | No diagnostic or crypto state/API in the core. Generic application predicates retain their own proof obligations. |
| Applications and consumers | Port retained shared examples and high-first complete-input consumer tests/proofs, especially MAVLink CRC, borrowed payloads, full message IDs, and truncation. Retire offset-seeking and excluded ordering/permutation fixtures. |

Keep application source in `examples/support/`, extracted through private
verification modules. `read_bit`, `read_bits`, and `take_aligned` remain
complete-input conveniences. Constructor helpers share existing retained nodes
and algorithms. Unsupported borrowed callback shapes can use named adapters;
record actual extraction support without imposing `Copy`/`Clone` on all outputs.

The [historical main plan](rusthammer-pre-v1.md) records completed increments and
then-current counts. Remove excluded tests/theorem roots explicitly, preserving
high-first complete-input, callback, borrowing, and ownership coverage for
retained families. General contracts in `Partial*` files still need migration;
feature exclusion does not justify deleting claims used by retained parsers.

After migration, small length/count/ASCII-whitespace conveniences can be selected
independently. Diagnostics, permutation, seeking, recursion, floats, packrat, and
streaming remain outside v1; their research is not a release-completion gate.

Before exposing any later family, specify its independent semantics, check the
Aeneas shape, implement the library path, prove its contract, and test meaningful
boundary/interoperation cases. Keep configuration invariants, error precedence,
cursor behavior, and termination assumptions explicit.

Retain both MIR stages and downstream extraction: the
[partial-enum-move issue](../rusthammer/probes/cross_crate/README.md) concerns
ownership cleanup, not partial input, and `Result` also has enum payloads. Run
`tools/verify.py` for the completed increment, including the full retained proof
and axiom audit. CI and the broader borrowed-callback investigation remain deferred.

## Sources checked

This inventory uses the local [public C API](../src/hammer.h), especially
[repetition](../src/parsers/many.c), [sequence selection](../src/parsers/ignoreseq.c),
[bind](../src/parsers/bind.c), [match exclusion](../src/parsers/butnot.c),
[difference](../src/parsers/difference.c), [exclusive choice](../src/parsers/xor.c),
and [permutation](../src/parsers/permutation.c). It concerns direct parsing;
backend equivalence is outside v1 and would require a separate audit.

The local nom checkout's `src/multi/mod.rs`, `src/sequence/mod.rs`, and
`src/combinator/mod.rs` inform folding, typed selection, and checked mapping.
Revision identifiers and current Aeneas evidence are recorded in the
[main plan](rusthammer.md#aeneas-compatibility-evidence). Only features explicitly
marked implemented have completed extraction and Lean verification.
