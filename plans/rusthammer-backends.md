# RustHammer backends and packrat parsing

Status: direct execution boundary implemented and verified, 2026-10-05.
Production has the public `Grammar` / `Eval` boundary
and the `Direct` interpreter. Memoization remains a later optimization, with a
private feasibility probe to inform its design. This document extends the
[main plan](rusthammer.md); it does not claim a production or verified packrat
implementation.

## Requirements and recommendation

Preserve a grammar as structured data that can be constructed independently of
execution. Keep typed outputs, static dispatch, borrowed input, `no_std`, the
ordering/finality context, and compositional Lean specifications. Support direct
execution and a packrat backend over an explicit supported grammar class.

The chosen boundary and later backend work are:

1. Keep concrete grammar nodes such as `Seq<P, Q>` and `Choice<P, Q>`.
2. Separate a grammar's output type from its interpreter implementation. Thread
   the selected backend's execution state through all child invocations.
3. Give named rules stable identities within an immutable grammar, and use
   typed memo tables whose result types are known for those rules.
4. Require reproducible values at memoized boundaries. One proposed
   policy is `Clone` for the values stored there, without adding that bound to
   ordinary parsers, combinators, or final outputs. This ownership policy needs
   review before it becomes public API; alternatives are compared below.
5. Make left recursion an explicit part of the Hammer compatibility target.
   Ordinary memoization and left-recursion growth need separate correctness
   arguments. Do not describe the first as an implementation of the second.

Establish and validate the execution boundary now, before spans and more
combinators increase the migration cost. Memoization, its output ownership
policy, rule identity, and recursion are deferred; choosing them is not a
prerequisite for finishing this refactor or continuing combinator work. Measure
representative grammars to guide their priority. No temporary public `Memo`,
prototype backend, or grammar-builder API is added for the experiments below.

## What C Hammer actually separates

[`HParser`](../src/hammer.h) retains grammar configuration and backend data.
[`HParserVtable`](../src/internal.h) supplies node-specific parsing, regular/CF
eligibility, RVM compilation, and desugaring operations.
[`h_do_parse`](../src/backends/packrat.c) is the common invocation path: it looks
up cached results and dispatches to a node's parsing operation. Combinators
such as [sequence](../src/parsers/sequence.c) call their children through that
path. Packrat is the default backend. Nonprimitive nodes are memoized; the C
backend also implements Warth-style left recursion.

Thus the architecture preserves grammar structure and separate interpretations,
but the nodes are not devoid of executable behavior. Rust trait implementations
can provide those operations without retaining C vtables. RustHammer now keeps
the chosen execution state active throughout a grammar. Rule identity and the
representation of memoized results remain future work.

## Grammar and interpreter boundary

Previously, `Parser::parse_with` combined the associated output type and one
execution method. Children called `parse_with` directly, so a wrapper around the
outer parser could not retain its chosen engine throughout the grammar.

The production interface now separates these concerns:

```rust,ignore
pub trait Grammar<'input> {
    type Output;
}

pub trait Eval<'input, Backend>: Grammar<'input> {
    fn eval(
        &self,
        backend: &mut Backend,
        input: &'input [u8],
        cursor: Cursor,
        context: ParseContext,
    ) -> ParseOutcome<Self::Output>;
}
```

The output is independent of the backend. Structural combinators have one
generic implementation over the children's interpreter capabilities. Their
recursive calls retain the same backend state. Primitives can reuse the current
verified decoding operations. `Direct` has empty execution state; a future
packrat engine would have parse-local tables and recursion metadata.

Keep `ParseContext` immutable and concerned with input interpretation. It should
not become the owner of memo tables, grammar definitions, or borrowed outputs.
Keep the input slice separate from mutable execution state in evaluator calls;
a public session or entry point must bind that state to one input and grammar.

The ordinary `Parser::parse` / `parse_with` convenience entry points select
`Direct`. `Parser` extends `Eval<'input, Direct>` and is implemented automatically
for every direct evaluator. A custom parser implements `Grammar` and `Eval`,
with no separate override of those convenience methods. `Eval::eval` is the
explicit execution entry point; every child call, including calls in loops and
application parsers, receives the same mutable backend. `&P` delegates to `P`'s
evaluator. Sequence, choice, lookahead, and repetition retain one implementation
of their control flow.

Custom parsers may implement `Eval` generically over the capabilities their
children need, or for a specific backend. There is no fallback from a missing
backend capability to direct execution. An arbitrary custom evaluator supplies
an execution operation, not inspectable syntax. Analysis and compilation remain
separate capabilities.

Threading state does not itself intercept every node or memoize a grammar.
Built-in primitives ignore the backend; structural nodes pass it to children.
Later named rules or a lowered representation must define where memoization
occurs, with stable identities and typed storage. That design may need additional
capabilities, but does not require a second copy of ordinary combinator semantics.
No production output acquires a `Clone` or `Copy` bound from this refactor.

Backtracking restores the input cursor, not mutable backend state. A backend
must decide which bookkeeping persists across failed branches and lookahead.
This is necessary for caches to retain useful work; it is also explicit in the
state-tracing regression tests. `ParseContext` ordering and finality still follow
their existing scope rules.

## Production evidence

`python3 tools/verify.py` passes native tests with and without `alloc`, the full
Lean proof build, promoted and optimized library MIR extraction, and the normal
Cargo consumer. All 44 consumer entry points translate and Lean type-check;
the consumer passes 19 tests without `alloc` and 22 with it. Generated project
declarations contain no admissions or opaque replacements.

The [backend tests](../rusthammer/tests/backend.rs) use children that implement
only their tracing backend's evaluator. They exercise sequencing, output
selection, references, callbacks, dependent parsing, alternatives, lookahead,
match restrictions, ordering scopes, collection, and folding. Accidental direct
fallbacks cannot satisfy these children's trait bounds. The separate consumer
also checks that borrowed output escapes a local mutable backend after nested
lookahead and dependent calls.

The [Lean direct views](../rusthammer/lean/RustHammer/DirectState.lean) specialize
the actual extracted evaluators and project away `Direct`'s unit state. Proven
equations preserve the existing specifications and application theorems without
introducing a second interpreter. [Generic backend proofs](../rusthammer/lean/RustHammer/BackendProofs.lean)
add state-transition contracts for sequencing and ordered choice, including
retaining state across recoverable rejection. The verification command audits
31 ordering/backend theorems using only standard Lean axioms. These results do
not establish correctness of a future memoization implementation.

Two application evaluators needed a small source workaround: construct their
zero-capture callbacks in nongeneric helpers. With this lifetime/backend-generic
method shape, Aeneas emits closure calls whose unused `Backend` argument Lean
cannot infer. The [minimal reproduction](../rusthammer/probes/backend_closure.rs)
fails at Lean type-checking for both MIR stages, while the helper-based form
passes both. Comments in `CountPrefix` and `RecordParser` retain the reason.
This is separate from the earlier borrowed-record callback limitation.

## Typed memoization and ownership

C can return the same arena-owned result pointer repeatedly. Our interface
returns a Rust value by ownership. Once a cached value has been moved to a caller,
it cannot also remain available for another caller without some replay policy.
Memoizing only success/failure and the end cursor does not solve this: a caller
also needs the typed value, and `Verify`, `TryMap`, and `Bind` may use it to
determine acceptance or later parsing.

| Policy | Benefits | Cost or restriction |
| --- | --- | --- |
| Clone typed results at memoized rule boundaries | Direct model; works for integers, tuples, borrowed slices, and ordinary cloneable application values. No type erasure. | A cached owned value must implement a value-preserving clone. Deep clones may be expensive. |
| Cache shared values or typed arena handles | Constant-size replay can preserve large result structures efficiently. | Requires an ownership/lifetime design for stored objects and escaped results; does not automatically retain today's move-based output interface. |
| Cache a derivation and reconstruct values | Can produce fresh non-`Clone` outputs while sharing parsing decisions. | Replays semantic work; data-dependent parsing and predicates require more than a cursor trace. Reconstruction cost and callback semantics need their own proofs. |
| Cache failures only | Can help some searches without storing successes. | Does not provide general packrat bounds or replay successful values. |

Typed result caching is a candidate for the later durable policy. Impose `Clone` only
where a result is actually retained for replay, not on every `Grammar::Output`.
For example, memoize a rule returning `(&[u8], u16)` and then use `Map` outside
that rule to build an owned non-`Clone` application object. Moving that map inside
the memoized rule changes its eligibility. This is a real capability restriction,
not something to hide as a temporary implementation detail.

`Clone` is a mechanism, not a proof of semantic equality or constant cost.
Verification requires a value-preserving clone contract. Large trees may be
better represented by immutable handles with later application construction;
do not claim those handles, `Rc`, or an arbitrary reconstruction scheme have
already been checked with Aeneas.

Use one typed table per declared rule or another statically checked schema.
For a fixed grammar, a product of tables can store `u8`, borrowed slices, and
other unrelated types. Future lowering can generate this schema. A universal
`HashMap<RuleId, Box<dyn Any>>` is a poor default: borrowed values and Aeneas
compatibility are central requirements, and runtime downcasts add no benefit
when the rule/result relation is already known.

The probe manually defines a small schema. A reusable grammar declaration and
lowering mechanism is still required; do not mistake its three tables for a
general grammar-registration API.

## Identity, cache keys, and sessions

A cache entry belongs to one immutable input snapshot and one immutable grammar
instance. Within that session, its logical key includes:

- A stable rule or expression identity, implicit in a dedicated typed table.
- The complete `Cursor { byte, bit }`.
- Both ordering axes and input finality from `ParseContext`.
- Any additional parameters or semantic state on which that rule depends.

Do not use the address of a Rust parser value as grammar identity: zero-sized
nodes, moves, copies, and separate values of the same type make that unsuitable.
Type identity alone is also insufficient: `Bits::new(3)` and `Bits::new(5)` have
the same type. Assign identities during grammar assembly/lowering, with explicit
rule references preserving sharing. Copies of a rule handle refer to that rule;
unrelated configured nodes must not collide.

Each top-level parse invocation starts with a fresh cache. Partial-input retries
and finality changes do not reuse a previous invocation's entries. Keep `NeedMore`
distinct from recoverable rejection and cache it only within the same snapshot.
A future incremental cache must account for successes and failures that depend
on the old end of input; invalidating only `NeedMore` entries is insufficient.

Do not hold a mutable table-element borrow across recursive evaluation. Mark
the entry active, retain a stable slot/index, release the borrow, evaluate its
body, and then complete the entry. Recursive calls may grow the tables.

## Callbacks and dependent parsing

Memoization changes how often semantic callbacks, constructors, clones, and
destructors run. `Fn` and `Clone` do not guarantee purity. The equivalence target
is specified values, consumed positions, errors, and incompleteness for pure,
deterministic grammars with terminating callback/clone contracts. Arbitrary
externally observable side effects do not inherit direct-backend equivalence.
Applications should perform committed effects after parsing; an effect-aware
action system would need a separate specification.

`Map` can construct a non-`Clone` result outside a memoized boundary. `TryMap`
and `Verify` must retain their acceptance effects in any lowering; they cannot
simply be postponed until after recognition. `Bind` is not automatically ruled
out of memoized execution, but its constructed parsers and input-derived
configuration make identity and cost explicit design obligations. Never cache
different configurations under the same rule/type identifier. Initially, allow
only forms with a justified rule identity/parameter scheme and reject unsupported
lowering, rather than inventing an unsound generic cache key.

This differs from regular/CF compilation: C itself marks unrestricted
[`h_bind`](../src/parsers/bind.c) ineligible for those compilation paths.

## Recursion and complexity

Named rule references must have finite Rust types and explicit identities.
Consuming recursion is an initial correctness case. Encountering an active entry
at the same key is a recursion cycle; it must not silently become `Mismatch`.

For C-compatible left recursion, design the seed/growth algorithm explicitly:
an initial internal seed, recursion heads and involved rules, reevaluation, and
strictly increasing accepted end positions. Direct, indirect, mutual, nullable,
and mixed left/right recursion require tests and stated supported semantics.
Growth compares `(byte, bit)` positions in the same enclosing context and must
preserve the ordering-scope discipline. Partial input and ambiguous same-length
semantic results need an explicit policy. These are not solved by adding a
`Busy` flag to an ordinary cache.

The [Warth, Douglass, and Millstein paper](https://web.cs.ucla.edu/~todd/research/pub.php?id=pepm08)
provides C Hammer's algorithmic starting point. It also explicitly notes that
some left-recursive grammars can take superlinear time. Preserve this capability
as a planned part of packrat support, while proving the ordinary memoization
case separately. A backend lacking the growth algorithm must report unsupported
recursion explicitly; the probe uses a fatal diagnostic and implements no growth.

Do not advertise unconditional linear time. The classical
[packrat result](https://pdos.csail.mit.edu/~baford/packrat/icfp02/)
depends on a fixed grammar and bounded work per memoized state. For RustHammer:

- Constant-time table access is needed. The probe's linear table search is only
  a feasibility device, not the proposed production data structure.
- Memoization must cover the appropriate recursive expression/suffix states.
  Caching a named rule that scans a long `Repeat` from every position can still
  be quadratic; normalization or equivalent sharing is needed.
- Callback time, dynamic `Bind` configurations, cloned output size, allocation,
  and left-recursion growth contribute additional cost.
- Counting entries does not bound memory by input length if each entry owns a
  result whose size grows with that input. Constant-size shared results/handles
  are needed for the corresponding storage bound.

For the initial fixed-rule design, investigate dense typed tables indexed by
byte, bit, and the finite context, with checked allocation/index arithmetic.
Retain `(byte, bit)`; do not reintroduce unchecked absolute machine bit counts.
Sparse storage is a separately justified alternative. Failure to allocate a
table or exhaustion of a configured budget must be fatal execution failure,
never recoverable grammar mismatch.

Cache indexability is not itself a new parser validation rule. For example,
`Epsilon` currently accepts a raw cursor without inspecting it. A direct/packrat
equivalence claim must either preserve that behavior (such as by evaluating
uncacheable positions without the table) or explicitly constrain the theorem's
input domain. Do not accidentally change grammar semantics in a cache lookup.

## Feasibility evidence and a tool limitation

[`backend_memo.rs`](../rusthammer/probes/backend_memo.rs) is an isolated `no_std`
probe using `alloc` and the actual library's primitives. It has independent
grammar/output and interpreter traits, common sequence/choice/map implementations,
typed tables for numeric and borrowed results, a non-`Clone` final output, and a
recursive rule with separate cache-policy operations.

Run from `rusthammer/`:

```sh
python3 tools/check_backend_memo.py
```

Checked with the existing pinned Rust/Charon/Aeneas/Lean tools: seven focused native
tests, plus two included library boundary tests, pass. They cover alternative
reuse, borrowed pointer identity, every context, cursor separation, cached errors
and incompleteness, fresh retries, a non-`Clone` output, recursive use of the same
backend, an active-entry diagnostic, and independent input/pattern lifetimes.
Both promoted and optimized MIR and a [normal Cargo consumer](../rusthammer/probes/backend_memo/consumer/lib.rs)
translate. All three resulting Lean modules type-check without admitted/opaque
project declarations; the runner checks every expected entry point. This is extraction and semantic-test evidence, not a
backend correctness, termination, left-recursion, or complexity proof.

The straightforward recursive trait design did fail. A generic rule body that
requires that rule's own `Eval<B>` implementation creates a dependency cycle:
the implementation calls the body with its own interpreter dictionary, and the
body recursively calls that dictionary. The small
[`backend_recursive_trait.rs`](../rusthammer/probes/backend_recursive_trait.rs)
reproduces an Aeneas extraction error, `Could not find: trait_impl_id`, without
memo tables or borrowed outputs. The full original probe failed at both MIR
stages; the minimized reproducer also fails at both stages and is retained independently.

The passing form puts recursive calls in an ordinary recursive function and
gives it cache-policy dictionaries containing only lookup/start/finish operations.
Those implementations do not call the recursive evaluator, so the dictionary
dependency cycle is absent. This validates one recursive driver arrangement.
It does **not** establish that arbitrary recursive combinator descriptions can
be lowered automatically. A general rule representation/lowering must preserve
that separation, or the tool limitation must be fixed and verified separately.

## Work sequence and proof obligations

1. **Direct execution boundary complete.** One implementation of ordinary
   combinator control flow, migrated examples and Lean proofs, a stateful test
   backend, and normal Cargo consumers pass the checks described above.
2. **Continue the planned API and measure representative grammars.** Spans can
   follow this boundary; memoization is not a prerequisite. Use measurements to
   select worthwhile cache boundaries and assess storage and replay costs.
3. **Choose the memoized-output policy and validate rule lowering privately.**
   Choose its durable capability contract before imposing public bounds. Keep
   unrestricted direct outputs. The basic independent-borrow
   and Cargo dependency checks pass. Next exercise reusable configurable rule
   identity, mutual recursion, and lowering of recursive combinator descriptions
   without the trait cycle. Choose the declaration/compiled representation based on that
   evidence. Set the left-recursion and fatal-resource-error contracts.
4. **Implement typed packrat storage and ordinary recursion.** Use the selected
   table representation, stable identities, fresh sessions, and explicit cycle
   handling. Prove lookup/completion invariants and refinement of direct parsing
   for the supported pure, terminating subset. Validate all current primitives
   and ordering scopes through that interpreter.
5. **Implement and prove left-recursion growth.** Specify its semantics separately
   from the direct interpreter, which may diverge on the same grammar. Compare
   the admitted cases with C; add direct/indirect/nullable regression grammars.
6. **State measured and proved cost bounds.** Include normalization, table access,
   semantic-value ownership, callbacks, and memory limits. Keep all assertions
   specific to their supported grammar class.

The central invariant is that each completed memo entry agrees with the rule's
specification at its session, cursor, context, and parameters. A cache hit must
return an equivalent typed result and end cursor; a miss must establish that
invariant before publishing the entry. Termination and safe table growth need
separate arguments. The established independent Lean grammar contracts remain
the reference for the non-left-recursive subset; a second backend does not
inherit their implementation proofs automatically.

Span APIs remain planned after the execution boundary. CI, the older borrowed-callback
investigation, live streaming, seeking, and unrelated compiled engines retain
their separate scope.
