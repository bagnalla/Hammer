# RustHammer combinator API plan

Status: target API and implementation order, with permutation, spans, scoped ordering, signed fields, byte patterns, `Bind`, ordinary/separated collection and folding, parser references, and output selection verified,
2026-10-07. Unimplemented features remain proposals. See the
[main plan](rusthammer.md) and [prototype README](../rusthammer/README.md) for
current implementation and proof coverage.

The [backend execution boundary](rusthammer-backends.md) is implemented and
verified, as are span and recognition combinators. The private
memoization probes remain design evidence outside the public API.
The seven constructor helpers are implemented and proved, following the private
compatibility check. Larger capabilities remain separate increments below.
The first version targets nonrecursive grammars using `Direct`. Recursive grammar
support and the associated extraction-tool investigation are deferred at the
user's request. The [recursion writeup](rusthammer-recursive-rules.md) retains the
construction proposal, private direct/packrat evidence, tool failures, and
unproved translation-soundness obligations. These are future design gates,
not requirements for finishing the first version.

## Agreed API scope

The parity review and subsequent floating-point investigation on 2026-10-07
selected the following scope. RustHammer does not require a counterpart for
every C combinator.

| Capability | Decision |
| --- | --- |
| Permutation | Implemented and proved as a retained nonrecursive capability; see the contract below. |
| Floating-point fields/ranges | Exclude from the first version due to the pinned Aeneas limitations. Retain as a later capability; the [probe report](../rusthammer/probes/floating_point/README.md) preserves the evidence and required tool/model work. |
| Seeking and diagnostic annotations | Retain as intended capabilities. Their contracts, implementation order, and inclusion in the first version remain to be selected. |
| Deferred actions (`h_action_stash`, `h_action_apply`) | Omit from the intended API. Ordinary transformations through `Map`, `TryMap`, and predicates remain supported; application effects can follow successful parsing. |
| Dedicated dispatch (`h_dispatch`) | Omit from the intended API. Express tagged formats through `Choice` or `Bind`, using explicit typed parser alternatives where needed. |
| Named parse-local value storage (`h_put_value`, `h_get_value`, `h_free_value`) | Exclude from the first version; its longer-term role is undecided. Use explicit typed values and `Bind` for field dependencies. Revisit only when a concrete grammar motivates shared storage, considering an explicit typed environment before a string-keyed store. |

The storage decision concerns values shared by application grammar components;
it does not remove interpreter bookkeeping or the existing backend boundary.
Diagnostic annotations identify a parser occurrence with a label and an optional
grammar construction location. They enrich failure reporting while preserving
the underlying parsing behavior. The detailed inventory below records the design
obligations for the retained capabilities. Recursion and its extraction-tool work
remain deferred under the separate writeup.

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

Retain `Grammar<'input>::Output`, concrete grammar nodes, and the separate
`Eval<'input, Backend>` capability. The associated type records the output fixed
by a grammar type for an input lifetime; it does not require an output type to
uniquely identify a grammar. Generic construction functions fit this design and
preserve the separation of grammar construction from interpretation.

Implemented: free construction functions `seq`, `choice`, `optional`, `map`,
`try_map`, `verify`, and `bind`. Each returns the existing concrete node, such as
`Seq<P, Q>` or `Map<P, F>`. `seq` and `optional` are unconstrained `const fn`s;
the remaining helpers use `Grammar` bounds to establish output relationships
or infer callback parameters. Construction requires neither `Parser` nor
`Eval<Direct>` and never invokes a child or callback. Existing validated
constructors retain their configuration checks. These helpers add syntax and
inference support, with no new parsing algorithm or runtime grammar representation.

Use opaque returns selectively. A grammar factory may hide an unnameable
callback as `Map<P, impl Fn(...) -> ...>` while retaining the node's generic
backend implementations. A whole-grammar `impl Parser<...>` return is suitable
when its exposed capabilities are the intended caller contract; it hides other
backend implementations and unlisted `Copy`/`Clone` capabilities. Do not make
it the default return type of the core construction helpers. Expose additional
bounds when they are part of the intended contract, and require borrowed-output
factories to preserve the appropriate input-lifetime relationships.

The [constructor probes](../rusthammer/probes/constructors/README.md), checked on
2026-10-06 with the pinned tools, establish compatibility for the generic
helpers, backend-only children, independent borrows, partially opaque callbacks,
and whole-parser opaque returns with owned or borrowed outputs. Both MIR stages
and downstream Cargo use pass extraction and Lean checking for these shapes.
This is compatibility evidence, not production implementation or correctness
proofs. Borrowed identity mapping callbacks fail with both the helper and direct
`Map` construction; a named callback also fails with a distinct lifetime
diagnostic. Keep those negative probes and the callback investigation separate
from the constructor work.

The production increment is complete. The
[constructor proofs](../rusthammer/lean/RustHammer/ConstructorProofs.lean) give
seven exact construction equations and a generic theorem transporting existing
node contracts through construction, demonstrated with stateful sequencing.
All nine theorems are axiom-audited. Native tests check construction without any
interpreter, deferred callbacks, input borrows, and retained backend/Copy
capabilities. The [example](../rusthammer/examples/constructors.rs) shares its
opaque-callback factory with the ordinary Cargo consumer. Both library MIR stages
extract the generic helpers themselves; all 52 consumer entries passed at that
checkpoint (57 after permutation). The older
negative probes remain isolated. Apply this return-type and backend-bound policy
to new APIs; no revision of the associated-output design is planned.

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
| Permutation | `Permutation<T>` produces a tuple in declaration order. | Implemented and proved; corresponds to `h_permutation`. Tuples of zero through twelve `required(p)` / `optional(p)` entries share a backtracking search. |

Output selection moves retained values and drops the others without requiring
`Copy` or `Clone`. The implemented helpers use `Seq` over shared references and
tuple pattern matching, preserving sequencing behavior without callback requirements.
Their public fields are `first`/`second`, `left`/`parser`/`right`, and `parser`,
respectively. All children must succeed, and the final cursor includes discarded
children's matches. Errors and `NeedMore` propagate before later children run.
`Ignore(Repeat(...))` would still build a vector: use a unit accumulator to discard
repeated outputs without allocating. Units are ordinary typed values; sequencing
and collection do not automatically erase them as C's null AST handling does.

For a complete parse, compose `Left(parser, End)`. Convenience syntax for this
can be added if useful; it does not need another parsing algorithm. Forwarding
`Grammar` and `Eval` through `&P` is implemented and proved for reusing immutable
parsers without cloning them. Combinators call `eval` with the selected backend;
`Parser` supplies direct convenience methods automatically. Input borrowing is independent of the lifetime
of the parser reference. The actual Rust syntax is `Left { first: parser, second: End }`.

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
3. Propagate fatal errors and `NeedMore`, including after the minimum is met.
   Partial input does not establish that repetition has finished. Previously
   collected outputs are discarded on an unsuccessful overall result.
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
   can still finish it, and `NeedMore` or a fatal child error still propagates.
   Finite repetition stops at its explicit maximum, so its count cannot overflow.

For separated lists, a repeated attempt consists of the separator and following
item together. If either rejects recoverably after the minimum, restore the cursor
to before the separator. Thus a trailing separator remains unconsumed; enclosing
`End` will reject it. Fatal errors and `NeedMore` still propagate. Reaching the
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
successful-child progress/count checks. Errors and `NeedMore` discard the state;
retries initialize again, and callback side effects are not rolled back.
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
`Q` implements `Eval<'input, Backend>` for the selected backend. For a given input lifetime, it returns one concrete parser type;
input values may change that parser's configuration. Choosing heterogeneous
branches requires a typed parser enum or another explicitly represented choice.
Static dispatch does not make a Rust return type depend on a runtime value.

The factory is called once after first-child success and never after its error
or `NeedMore`. Its parser consumes from that success cursor. `Fn` permits repeated
use of a grammar; neither purity nor termination follows from that trait bound.
Generic proofs require factory and child-parser family contracts only for
reachable first-stage successes. Both finalities and the complete API are proved;
first-stage errors and `NeedMore` skip the factory without assumptions about it.
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
A future bounded-region combinator needs a separate contract for inner finality,
full consumption versus permitted leftovers, and translation of cursors to the
outer input. Do not introduce a count-only public stand-in for that operation.

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
after a first success or recoverable rejection. Propagate `NeedMore` and fatal
errors from attempted children; when both `Xor` children reject, return the second
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
proofs separately cover partial input and fatal errors. Both MIR stages and all
40 consumer entries pass, including enum-mapped alternatives and borrowed outputs.
The revised [input plan](rusthammer-input.md) retains this `(byte, bit)`
comparison by restricting bit-direction changes to aligned scope boundaries.
Its generic parser contracts now carry the full ordering/finality context.
Arbitrary seeking still needs a separate treatment.
In particular, `ButNot` and `Difference` cannot be replaced by sequencing with
`Not(q)`: they may accept when both children succeed.

Permutation is implemented as `permutation((required(a), optional(b), ...))`,
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
`NeedMore` and fatal errors stop immediately. Exhausted orderings return
`Mismatch`. The empty tuple succeeds without cursor validation.

One search handles all arities without allocation or output cloning. Separate
slot presence and match flags allow speculative values to be dropped and accepted
values to be moved, including independent input/configuration borrows. Backtracking
restores the cursor and retains backend state and callback effects, consistently
with `Choice`. Termination uses the pair of remaining entries and remaining
candidates, so empty matches are permitted. Ambiguity can require factorial work;
the current implementation uses the call stack. Candidate scanning is recursive
too, giving an inspected conservative bound of `n² + 1` active search calls
(145 at twelve entries), excluding child calls. The termination proof does not
bound stack consumption in bytes or establish freedom from stack overflow.
Large inline outputs, nested permutations, and small stacks remain concerns.
Evaluate stack usage and extraction-compatible iterative search with bounded
explicit backtracking storage before settling the resource guarantees; the
public permutation API can be preserved.

The [search proofs](../rusthammer/lean/RustHammer/PermutationProofs.lean) establish
agreement with a total natural-number model under child and storage contracts,
including backend transitions, partial/fatal propagation, and safe counters.
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
| Skipping and position | Implemented and proved: `SkipBits::new(bits)` discards any `usize` bit count and returns `()`; `Tell` reports the validated `Cursor` without consuming. Both validate even at zero consumption and preserve `h_skip` and `h_tell` capabilities. Skips advance in constant time, classify exhaustion by input finality, and have an infallible `const` constructor and `bits()` accessor. Position reporting avoids an absolute machine bit count; see the [known C overflow issue](rusthammer.md#known-c-issue-absolute-bit-position-overflow). |
| Recognizing matched input | Implemented and proved: `BitSpan`, `Recognize`, and `WithSpan`, retaining validated `(byte, bit)` endpoints and the enclosing bit direction. `WithSpan` returns the decoded value with its span; `Recognize` runs the child and discards its value. Partial-bit matches need not be byte slices; `as_bytes()` requires both endpoints aligned. No direct C combinator counterparts; these provide optional source retention. See the [input plan](rusthammer-input.md#matched-input-spans). |
| Floating-point fields/ranges | Deferred beyond the first version due to the pinned Aeneas limitations. Retain counterparts of `h_float16`, `h_float32`, `h_float64`, and `h_float_range` as later capabilities. Settle bit decoding, NaNs, infinities, signed zero, range-bound precision, and the required Aeneas models/translation support before exporting readers or range helpers. |
| Bit and byte order | Implemented and proved with the [input plan's restriction](rusthammer-input.md#ordering-scopes): a changed bit direction requires aligned entry and successful exit, otherwise fatal `Unaligned`. Unaligned fields and unrestricted byte-order changes remain supported. Retain `(byte, bit)` with immutable `ParseContext`. Numeric-reader, contextual primitive, and generic scope/combinator proofs pass; `Be*` pins big byte order while inheriting bit direction. |
| Recursion | Deferred beyond the first nonrecursive version, including the related extraction-tool work. Retain `recursive(|self_ref| body)` as a proposal using ordinary combinator bodies; see the [writeup](rusthammer-recursive-rules.md) for representation, translation soundness, ownership, and termination gates. Keep construction usable by a later packrat compiler, whose intended production algorithm includes left recursion. C uses `h_indirect`/`h_bind_indirect` for two-step fixed-point construction; a declaration DSL is not required. |
| Named parse-local value storage | Outside the first version; longer-term support is undecided. Express ordinary dependencies with typed values and `Bind`. A concrete shared-environment use case must motivate reconsideration, with explicit value types, ownership, scope, backtracking, and eventual memoization semantics. |
| Deferred actions | Intentionally omitted under the [scope decision](#agreed-api-scope); ordinary mapping and predicates retain their current contracts. |
| Diagnostics | Retain annotations corresponding to `h_with_context` and parser labels as an intended capability. Attach a label and optional grammar construction location to a parser occurrence. Specify propagation and selection through nesting, alternatives, lookahead, and partial input; prove the underlying parsing behavior is preserved. |
| Packrat and other execution engines | The [backend plan](rusthammer-backends.md) separates grammar outputs and evaluation. Memoization, rule identities, and the cached-output policy remain future work guided by protocol benchmarks. Left recursion needs its own algorithm and proofs. Other compiled engines remain separately specified. |
| Seeking | Retain a counterpart of `h_seek` as an intended capability. Specify bounds, position units, backward movement, and interaction with spans, repetition, backtracking, and memoization. First-version inclusion remains open. |
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

1. **Consolidate repetition (complete).** Exact, finite bounded, and unbounded
   forms are implemented and proved through one `Repeat` type and loop.
   `RepeatN` has been removed; its exact-count contract is a specialization of
   the bounded theorem. Constructor invariants, zero-count, borrowed output,
   non-`Copy`, cleanup, rollback, and both input statuses are covered. Unbounded
   repetition enforces cursor validity and progress and checks count overflow;
   its Lean termination measure is the mathematical number of remaining bits.
2. **Finish basic composition (complete).** Parser references and output-selection
   helpers are implemented and proved by reusing the sequencing contracts.
   Borrowed/non-`Copy` outputs, cleanup, exact consumption, short-circuiting,
   and both input statuses are covered. `Epsilon`, `Fail<T>`, and `TryMap` are
   implemented with contracts for both modes and the complete API. Checked
   conversion errors become recoverable rejection; child failures/incompleteness
   skip the callback. A captured fallible callback returning an owned record
   translates and Lean type-checks through the actual library source.
3. **Complete repetition outputs and lists (complete).** `FoldRepeat`
   supports exact, bounded, and unbounded counts without library allocation.
   `SepBy` and `FoldSepBy` add separated lists with the same constructors.
   The shared driver and recurrence are proved for all four families, including
   separator/item rollback, progress of whole pairs, error propagation, and
   final-input specialization. Native tests cover empty successes, ownership,
   bit boundaries, independent short-input oracles, and C list examples. Both
   MIR modes and the ordinary Cargo consumer translate and Lean type-check.
4. **Generalize data dependencies (core and formats complete).** `Bind` and
   count-prefixed element/byte examples are implemented and proved. Tests cover
   both input modes, checked counts, factory invocation, cursor rollback, borrowed
   identity, and owned output/parser cleanup. Application proofs cover the actual
   shared example source. Named length/count helpers remain planned conveniences.
5. **Expand binary vocabulary and restrictions (initial set complete).** `Byte` and
   `BytePattern` are implemented and proved, including arbitrary patterns,
   unaligned starts, both input modes, empty patterns, and independent output
   lifetimes. Both MIR stages and the normal Cargo consumer pass; optional
   direct-backend C comparisons cover 10,561 complete-input cases. A private
   matching helper avoids the documented Aeneas loop-borrow limitation.
   `SignedBits` now adds verified signed fields of width 0 through 64, with total
   parsing and safe sign-extension proofs. It passes both MIR stages and the
   Cargo consumer; 27,724 signed-field C comparisons cover boundaries, truncation,
   and every bit offset. Fixed-width typed integer readers are also implemented
   and proved, with zero-sized configuration-free values, native output types,
   and lossless conversions. Both MIR stages and the Cargo consumer pass;
   134,896 additional C comparisons exercise the named integer primitives.
   `IntRange` now adds inclusive typed restrictions by delegating to `Verify`,
   with constructor, ordering, native-reader, and generic compositional proofs.
   Bounds use `Ord`; integer newtypes need neither `Copy` nor `Clone`. Both MIR
   stages and the Cargo consumer pass, and 138,240 additional C cases
   cover `h_int_range` and `h_ch_range` at every bit offset, including truncation
   and endpoint/extreme values. Native tests separately verify construction-time
   rejection of reversed bounds. `ByteIn` and `ByteNotIn` now add literal byte
   membership/exclusion through `Verify`, with total parsing and set-membership
   proofs. Owned 32-byte bitmaps accept all construction slices, with infallible
   `const` construction and O(1) membership. They have no lifetime parameter;
   `accepts(byte)` queries the filter. Constructor and bounded-lookup proofs
   connect the bitmap to the original literal set without a bitmap validity
   invariant. Both MIR stages and all 40 consumer entry
   points pass; 147,456 additional C cases cover every byte and bit offset,
   truncation, empty/full sets, duplicates, and sets longer than 256 entries.
   `SkipBits` and `Tell` now add constant-time skipping and cursor reporting,
   with total cursor-advancement proofs over all machine lengths/counts and
   both input statuses. Native virtual-length tests cover machine boundaries
   without allocating input; 118,188 C comparisons cover representable positions.
   Both MIR stages and all 40 consumer entries pass without a new workaround.
   `ButNot`, `Difference`, and `Xor` now implement the match contracts above.
   Generic Lean proofs cover both statuses, the complete API, selected outputs
   and cursors, short-circuiting, and overflow-free length comparison. All 22
   public match theorems were axiom-audited. Native tests cover every outcome
   combination, ownership, borrowing, and independent bit-length oracles;
   1,879,635 additional C cases agree. Both MIR stages and all 40 consumer entries
   pass without a new workaround.
   The revised [input plan](rusthammer-input.md) limits bit-direction changes
   to aligned scope boundaries and retains existing cursor arithmetic. The
   production implementation and proofs now pass both MIR stages, all 43
   Cargo-consumer entries, native tests, and 25 ordering theorem axiom audits.
   C comparisons add 107,364 agreements and 2,848 expected scope rejections.
   The subsequent backend migration is complete, with all existing proofs,
   stateful backend tests, 44 consumer entries, and 31 ordering/backend theorem
   axiom audits passing. `BitSpan`, `Recognize`, and `WithSpan` are now implemented
   and proved, with safe raw byte views, physical-bit geometry, backend-generic
   validation and propagation, native tests, and 49 consumer entries passing.
   The isolated probes remain design evidence.
   Plan larger capabilities separately; permutation is completed in step 7.
6. **Construction conveniences (complete).** The seven
   [construction helpers](#construction-functions-and-return-types) return concrete
   nodes with bounds independent of the evaluator. Generic extraction roots,
   ordinary Cargo-consumer coverage, a shared opaque-callback example, and exact
   construction proofs are integrated into the normal verification command.
   Existing node contracts govern parsing. The nine new theorem audits bring
   the total to 74; all 52 consumer entries pass. Existing grammars need no
   migration. Negative callback probes remain in the separate diagnostic runner,
   whose default run intentionally reports failures.
7. **Typed permutation (complete).** Explicit required/optional tuple entries,
   full backtracking over orderings, and one allocation-free evaluator support
   borrowed and non-`Clone` outputs. Native tests, generic search and tuple proofs,
   both MIR stages, 57 consumer entries, and 217,728 C comparisons pass. The new
   proofs bring the axiom-audit total to 156. See the contract above.
8. **Select and finish the first-version nonrecursive API.** Review the retained
   capabilities in the [scope decision](#agreed-api-scope):
   seeking and diagnostics. Consider the remaining
   [dependent helpers](#dependent-parsing-and-reusable-helpers), including
   length/count wrappers and ASCII whitespace, alongside those substantive gaps.
   Select the operations needed for the first version and their implementation
   order, specify their contracts, and reuse the existing primitives, `Bind`,
   and repetition where appropriate.
   Keep ordinary downstream examples, extraction checks, and compositional proofs
   with each chosen increment. The full future feature inventory is not an
   implicit first-release requirement.

**Native floating-point support is deferred.** The
[investigation](../rusthammer/probes/floating_point/README.md) and reproductions
remain available. Float readers, range helpers, and the required Aeneas work
are outside the first version; no placeholder float API is planned.

**Recursive construction and direct execution are deferred.** The
[writeup](rusthammer-recursive-rules.md) preserves the proposed constructor,
passing ordinary-function probes, failing recursive combinator bodies, and
separate later packrat direction. Aeneas dictionary lowering requires a scoped
soundness argument before general implementation; the handwritten Lean model
does not supply that argument. Resume this investigation when reprioritized,
without introducing a placeholder recursion API in the first version.

**Application fixture migration is complete.** `Flags`, `Marker`, `Record`,
`RecordParser`, their parsing helpers, and the example payload limit now live in
[`examples/support/`](../rusthammer/examples/support/). Each runnable example and
its existing native tests compile the same shared source against the ordinary
library. Private modules enabled only by `rusthammer_verify` supply extraction
and Lean proofs, following the dependent-format pattern. The moved fixtures
are absent from normal library builds and the public API; no feature or public
compatibility alias exposes them. Generated application names acquire module
prefixes, while the existing Lean theorems and contracts are preserved.
Explicit extraction roots retain the moved parsers' derived clone methods in
both MIR stages. The normal Cargo consumer continues to use only core exports.

`read_bit`, `read_bits`, and `take_aligned` remain documented complete-input
primitive convenience functions; use the parser interface for partial input.
Keep future application fixtures outside the general-purpose public API.
Internal proof convenience alone is not a reason to export any additional helper.

Before exposing a new family: write its independent semantics, check the relevant
Aeneas shape, implement the actual library path, prove its compositional contract,
and test meaningful boundary/interoperation cases. Proofs should cover constructor
invariants, both input statuses, consumption, error precedence, and termination
under child/callback contracts. Differential tests should normalize typed output
differences and identify intentional differences from C. Implementation steps may
be small; each production addition, including internal machinery, must have a
durable role in this plan.

The local verification command also checks every library verification root at
the MIR stage used for dependencies and translates a separate Cargo consumer.
Retain those checks when adding combinators: the promoted-MIR proof path alone
missed the [partial-enum-move issue](../rusthammer/probes/cross_crate/README.md).

CI and the recorded borrowed-callback investigation remain deferred. The
[eager literal rejection task](rusthammer.md#deferred-eager-literal-rejection)
remains scheduled before streaming buffering/resumption. Repetition work
does not start those deferred investigations.

## Sources checked

This inventory uses the local [public C API](../src/hammer.h), especially
[repetition](../src/parsers/many.c), [sequence selection](../src/parsers/ignoreseq.c),
[bind](../src/parsers/bind.c), [match exclusion](../src/parsers/butnot.c),
[difference](../src/parsers/difference.c), [exclusive choice](../src/parsers/xor.c),
and [permutation](../src/parsers/permutation.c). It concerns direct parsing;
backend equivalence still needs the separate audit in the main plan.

The local nom checkout's `src/multi/mod.rs`, `src/sequence/mod.rs`, and
`src/combinator/mod.rs` inform folding, typed selection, and checked mapping.
Revision identifiers and current Aeneas evidence are recorded in the
[main plan](rusthammer.md#aeneas-compatibility-evidence). Only features explicitly
marked implemented have completed extraction and Lean verification.
