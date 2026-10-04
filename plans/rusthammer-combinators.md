# RustHammer combinator API plan

Status: target API and implementation order, with repetition, parser references, and output selection verified,
2026-10-04. Unimplemented features remain proposals. See the
[main plan](rusthammer.md) and [prototype README](../rusthammer/README.md) for
current implementation and proof coverage.

## API policy

Public features must have an intended place in the finished library. Do not add
a public type merely because it is a convenient implementation or proof milestone.
Implement and prove the intended abstraction incrementally; keep compatibility
experiments in `probes/` and application-specific grammars in examples or proof
fixtures. Do not export unsupported modes or placeholder implementations.

This does not require freezing every signature now. Resolve a feature's output,
failure, consumption, ownership, and verification requirements before exporting
it. Changes supported by new evidence remain possible while the API is experimental.

Convenience operations are useful permanent API when they express common grammar
intent. They should compose existing operations or share their implementation.
Different names do not require different parsing algorithms or independent proofs.

## Core combinator families

`A` and `B` below denote child output types for the input lifetime. All operations
use static dispatch and retain typed outputs, including borrowed and non-`Copy`
values. Only collecting operations require the optional `alloc` feature.

| Family | Intended API and output | Implementation and Hammer correspondence |
| --- | --- | --- |
| Sequencing | `Seq<P, Q>` produces `(A, B)`. | Already implemented. Run children in order, passing the successful cursor onward. Corresponds to `h_sequence`. Nest pairs initially; any later tuple syntax should expand to the same semantics. |
| Ordered alternatives | `Choice<P, Q>` produces their common output type. | Already implemented. Retry recoverable rejection at the original cursor. Map alternatives into an enum when their natural outputs differ. Corresponds to `h_choice`. |
| Optionality | `Optional<P>` produces `Option<A>`. | Already implemented; corresponds to `h_optional`. Empty success is `Some`, not absence. |
| Output transformation | `Map<P, F>` produces `B`; `Verify<P, F>` preserves `A` when its predicate holds. | Already implemented. Typed counterparts of transforming `h_action` callbacks and `h_attr_bool`. These do not supply deferred-effect semantics. |
| Checked transformation | `TryMap<P, F>` produces `B` from a callback returning `Result<B, E>`. | Implemented and proved. Run the callback once after child success; conversion rejection becomes recoverable `Mismatch`. Useful for checked integer conversions and validated data construction without panicking or computing the conversion twice. |
| Lookahead | `And<P>` and `Not<P>` produce `()`. | Already implemented; correspond to `h_and` and `h_not`. Restore the original cursor on success. |
| Selecting sequence outputs | `Left<P, Q>`, `Right<P, Q>`, `Middle<L, P, R>`, and `Ignore<P>` return `A`, `B`, the middle output, or `()`, respectively. | Implemented and proved; correspond to `h_left`, `h_right`, `h_middle`, and `h_ignore`. Derived from sequencing and output projection. Arbitrary `h_drop_from` becomes typed tuple projection. |
| Empty and failing grammars | `Epsilon` produces `()`; `Fail<T>` always rejects with `Mismatch`. | Implemented and proved; correspond to `h_epsilon_p` and `h_nothing_p`. Neither reads input; `Epsilon` preserves the supplied cursor without validation. `Fail::new()` is infallible and needs an inferred or explicit output type so it composes with typed alternatives. |
| Repetition | `Repeat<P>` produces `Vec<A>` with `alloc`. | Exact, finite bounded, and unbounded forms are implemented and proved, replacing `RepeatN` and covering `h_repeat_n`, `h_many_cap`, `h_many1_cap`, `h_many`, and `h_many1`. |
| Folding repetition | `FoldRepeat<P, I, F>` produces an accumulator `R`. | Same count and stopping rules as `Repeat`; initialize a fresh accumulator and update it with each output. Supports allocation-free counting, discarding, checksums, and application accumulators. No C wrapper is required to justify this separate output policy. |
| Separated repetition | `SepBy<P, S>` produces `Vec<A>` with `alloc`; `FoldSepBy<P, S, I, F>` produces an accumulator without library allocation. | One count policy covers `h_sepBy` and `h_sepBy1`, as well as finite limits. Parse the first item, then separator/item pairs; discard separator outputs. |
| Value-dependent sequencing | `Bind<P, F>` produces the output of the parser selected or constructed from `A`. | Corresponds to `h_bind`. Run the first child, move its value into the factory, then run the resulting parser at the next cursor. |
| Match restrictions | `ButNot<P, Q>` and `Difference<P, Q>` preserve `A`; `Xor<P, Q>` requires a common output type. | Separate semantics from ordered choice and lookahead. Compare matches starting at the same cursor; see below. |

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
`Parser` through `&P` is implemented and proved for reusing immutable parsers
without cloning them. Both methods forward, preserving a custom `parse` override;
combinators still call `parse_with`. Input borrowing is independent of the lifetime
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
this count policy and corresponding constructors.

| Hammer expression | Rust form |
| --- | --- |
| `h_repeat_n(p, n)` | `Repeat::exact(p, n)` |
| `h_many_cap(p, n)` | `Repeat::new(p, 0, n)` |
| `h_many1_cap(p, n)` | `Repeat::new(p, 1, n)`; `n == 0` is a configuration error |
| `h_many(p)` | `Repeat::at_least(p, 0)` |
| `h_many1(p)` | `Repeat::at_least(p, 1)` |

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

Share validated bounds, the iteration driver, and its specification between
collection and folding; keep implementation policy traits private. A fold uses
an initializer `Fn() -> R` and a step `Fn(R, A) -> R`, so the accumulator is passed
explicitly and outputs need not be cloned. Probe the private driver with Aeneas
before committing to its representation. If extraction requires a different
internal structure, preserve the public semantics and prove the implementations
against the same recurrence.

`FoldRepeat` has a lasting purpose because it changes storage and output behavior.
Another exact-count type returning the same vector does not. A future parser
returning `[A; N]` would likewise be a distinct output capability, but it is not
needed in the initial API and should not be added merely to retain `RepeatN`.

Keep the existing allocation assumptions explicit: using `Vec` does not establish
recoverable allocation failure or a resource budget. Collection should grow with
successful iterations rather than reserve an input-derived count in advance.

## Dependent parsing and reusable helpers

The target `Bind` factory has the shape `Fn(A) -> Q`, where `Q` implements
`Parser<'input>`. For a given input lifetime, it returns one concrete parser type;
input values may change that parser's configuration. Choosing heterogeneous
branches requires a typed parser enum or another explicitly represented choice.
Static dispatch does not make a Rust return type depend on a runtime value.

The factory is called once after first-child success and never after its error
or `NeedMore`. Its parser consumes from that success cursor. `Fn` permits repeated
use of a grammar; neither purity nor termination follows from that trait bound.
Prove a factory contract and child-parser family contract. Probe factories using
borrowed values and parser references before exporting the generic implementation.
Keep the previously deferred borrowed-record callback investigation separate.

Build these permanent conveniences from the core, rather than separate engines:

| Helper | Composition and intended meaning |
| --- | --- |
| Length-counted elements | Decode and check a count, then `Repeat::exact(element, count)`. This is Hammer's `h_length_value`; prefer the unambiguous name `LengthCount`. |
| Length-prefixed aligned bytes | Decode and check a byte length, then construct `TakeAligned`. Preserve the length in the typed output if the application needs it. |
| Discriminator-based parsing | Decode a tag and select a typed parser branch. This supplies the capability of `h_dispatch`, including an explicit default/rejection branch; retain tag and payload when needed. |
| Numeric ranges and byte sets | `Verify` over numeric or byte readers implements `h_int_range`, `h_ch_range`, `h_in`, and `h_not_in`. Validated range helpers may share that implementation. |
| Leading whitespace | Skip repeated ASCII whitespace, then return the following parser's output, corresponding to `h_whitespace`. Specify the ASCII set explicitly instead of importing locale-dependent `isspace` behavior. |

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

The [C implementations](../src/parsers/) make these distinctions:

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

For the forward cursor model, compare consumed bit spans, not output sizes or
rounded byte counts. Audit correspondence with C's `token_length` in differential
tests. Arbitrary seeking and mixed bit-order scopes need a separate treatment.
In particular, `ButNot` and `Difference` cannot be replaced by sequencing with
`Not(q)`: they may accept when both children succeed.

Preserve `h_permutation` as a planned capability, after the smaller core. It tries
parser orderings in argument priority order, backtracking when the remaining
parsers cannot match, and returns outputs in declaration order. A Rust version
needs a typed tuple of outputs and an explicit set of remaining parsers. C's
special treatment of absent optional tokens must become an explicit optional-item
policy; generic Rust values cannot be inspected for a dynamic `TT_NONE` tag.
Specify that policy and termination before exporting a permutation combinator.

## Primitive support and later capabilities

The combinators above also need a deliberate primitive and extension inventory:

| Capability | Direction |
| --- | --- |
| Bits, unsigned numbers, numeric literals, exact EOF | Retain `Bit`, `Bits`, `Literal`, and `End`. Fixed-width readers with narrower Rust outputs can be permanent conveniences over common decoding operations. |
| Signed numbers | Add specified sign extension and typed readers for `h_bits(..., true)` and `h_int*`; do not approximate signed fields with an undocumented cast. |
| Byte/token parsing | Add a `u8` reader and byte-pattern matching, including unaligned starts. `h_ch` can be a literal-reader convenience; patterns should not be restricted to the numeric literal's 64 bits. Choose pattern output and ownership before exporting its API. |
| Byte sequences | Keep `TakeAligned` for borrowed slices. Supply `h_bytes` through exact repetition of decoded bytes with `alloc`, with a convenience operation if useful. Never silently align unaligned input. |
| Skipping and position | `SkipBits` discards a specified number of bits; `Tell` reports the cursor without consuming. Preserve `h_skip` and `h_tell` capabilities, with explicit Rust position units and checked arithmetic. |
| Recognizing matched input | A bit-span view and `Recognize`/value-with-span operations are useful additions. Settle span invariants and bit-order interaction before promising a borrowed slice for arbitrary bit matches. |
| Floating-point fields/ranges | Preserve as a later capability; specify bit decoding, NaNs, infinities, rounding where applicable, and available Aeneas models before exporting readers or range helpers. |
| Bit and byte order | Preserve the capability of `h_with_endianness`. Mixed order within a partially consumed byte needs the cursor design work recorded in the main plan. No nominal wrapper around MSB-only parsing. |
| Recursion | Start with named typed parsers and guarded recursion. Design runtime rule graphs and left-recursive execution separately; `h_indirect`/`h_bind_indirect` are C's construction mechanism, not the required Rust interface. |
| Parse-local state and actions | Express ordinary dependencies with typed values and `Bind`. Preserve `h_put_value`/`h_get_value`/`h_free_value` and deferred `h_action_stash`/`h_action_apply` capabilities in a separately specified environment/effect design, including rollback and commit. |
| Diagnostics | Plan context labels corresponding to `h_with_context` and parser labels as a separate diagnostic layer; keep their effect on errors explicit. |
| Seeking, streaming, memoization, compiled engines | Retain as separately specified capabilities. They need ownership, termination, state, and semantic-equivalence work, not placeholder combinators. |

C allocator variants, variadic/array calling variants, dynamic AST extraction,
and vtable plumbing do not need one-for-one public replacements. Permanent Rust
helpers should represent grammar operations or output needs.

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
3. **Complete repetition outputs and lists.** Add the shared fold path and
   separator handling, including their unbounded forms under the progress rule.
   Verify collection and folding use the same stopping and rollback semantics.
4. **Generalize data dependencies.** Validate and implement `Bind`, then use it
   in count-prefixed elements and length-prefixed bytes. Prove a representative
   format against an independent format specification.
5. **Expand binary vocabulary and restrictions.** Add byte patterns, signed
   readers, ranges, skipping/position, and match comparisons as specified above.
   Resolve cursor/span/order questions before implementing their affected APIs.
   Plan permutation, recursion, and the other larger capabilities separately.

Audit existing exports alongside this work: `Flags`, `Marker`, `Record`, their
parsers/functions, and the example payload limit are application fixtures, not
general-purpose final library features. Move them to an example/proof-support
target while preserving their extraction and proofs. Retain `read_bit`,
`read_bits`, and `take_aligned` as documented complete-input primitive convenience
functions; use the parser interface when partial-input semantics are needed.
Internal proof convenience alone is not a reason to export any additional helper.
These are planned migrations, not changes already made.

Before exposing a new family: write its independent semantics, check the relevant
Aeneas shape, implement the actual library path, prove its compositional contract,
and test meaningful boundary/interoperation cases. Proofs should cover constructor
invariants, both input statuses, consumption, error precedence, and termination
under child/callback contracts. Differential tests should normalize typed output
differences and identify intentional differences from C. Implementation steps may
be small; each public addition must have a durable role in this plan.

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
