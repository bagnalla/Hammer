# RustHammer recursion: deferred design and investigation

Status: deferred at the user's request, 2026-10-06. The first version of
RustHammer will support nonrecursive grammars. Recursive grammar construction,
its direct interpreter support, and the associated extraction-tool investigation
are set aside. This document preserves the proposed direction, evidence, and
unresolved obligations for later work; it is not the next implementation task.
No production `recursive`, rule, compiler, workspace, or packrat API has been
added, and no extraction-tool pin has been changed.

## First-version scope

Continue developing nonrecursive grammars through the existing concrete nodes,
`Grammar` / `Eval` boundary, and `Direct` interpreter. Existing repetition and
data-dependent parsing with `Bind` remain useful within this scope: iterating a
child parser or selecting its configuration does not require a recursive grammar
reference. The first version does not depend on a recursive constructor, a
dictionary-translation change in Aeneas, or the private packrat model.

Keep the probes and their reproduction commands as evidence. Do not promote the
handwritten recursive-parser fallback or the diagnostic tool patch to production
to fill this gap. Resume this work when it is reprioritized, beginning with the
soundness and representation questions below. The future packrat design remains
part of the [backend plan](rusthammer-backends.md), with left recursion in its
intended production implementation from the outset.

## Proposed construction and direct execution

The desired fixed-point combinator has the conceptual construction shape:

```text
recursive(|self_ref| body_built_with_existing_combinators(self_ref))
```

This is an API candidate, not an implemented function or settled Rust signature.
The body remains an ordinary combinator expression. A "rule" here means a parser
with an identity that other parsers, including its own body, can reference; it
does not mean a separate BNF language. C Hammer supplies the corresponding
two-step construction with
[`h_indirect` and `h_bind_indirect`](../src/hammer.h). A recursive combinator could
hide that binding operation. Mutual recursion is the corresponding construction
of several bodies from references to each other.

If this work is resumed, the construction and execution design must:

1. Find a finite, typed representation of the recursive reference and body that
   preserves structured grammar construction. Resolve output-family inference,
   ownership, configuration identity, and when the construction callback runs.
   Keep source grammar identity independent of packrat compilation. Do not assume
   a declaration DSL, trait objects, or an allocating self-referential graph is
   required; validate the chosen Rust mechanism with the pinned tools.
2. Exercise actual combinator bodies through direct evaluation: a nested consuming
   grammar, mutual recursion, independently borrowed input/configuration outputs,
   and non-`Clone` outputs. Check native behavior, promoted and optimized MIR,
   generated Lean, and an ordinary Cargo consumer. The earlier ordinary-function
   [probe](../rusthammer/probes/backend_memo.rs) passes, but the recursive
   [trait-dictionary diagnostic](../rusthammer/probes/backend_recursive_trait.rs)
   fails; neither result settles the new combinator's representation.
3. Specify the supported direct recursion and its termination conditions,
   including nullable paths, partial input, errors, and call-stack behavior.
   Determine how unsupported same-position cycles are excluded or diagnosed;
   do not turn them into ordinary mismatch or claim bounded physical stack use
   from extraction alone. Direct execution initially targets consuming recursion.
4. Check that the construction can later expose a separate lowering capability
   for packrat. Do not require direct outputs to satisfy memo replay bounds or
   make direct execution depend on compiled instructions and memo workspaces.

The deliverable is an extractable API/representation candidate, its supported
cases and limitations, and the direct correctness/termination proof plan. Keep
these checks in `probes/`. Implement and prove a production combinator only after
settling that durable design. Direct recursive execution will remain useful
alongside packrat; it is not a temporary recursion-rejecting packrat algorithm.
General packrat storage and left-recursion growth are subsequent work, not
prerequisites for this investigation.

## Investigation result and remaining decision

The [direct-recursion checks](../rusthammer/probes/direct_recursion/README.md)
now pass ten native tests and six positive roots at promoted MIR, optimized MIR,
and through a Cargo consumer. The positive representation uses ordinary self-
and mutually recursive functions behind existing `Grammar`/`Eval<Direct>`
wrappers. It preserves configuration/input lifetimes, non-`Clone` results,
partial input, and composition with actual outer combinators and spans.

That passing form expresses the control flow around recursive calls in Rust,
not as one inspectable combinator body. It neither establishes a general
`recursive` constructor nor supplies automatic packrat lowering. Do not export
it as a stand-in for the requested structured construction capability.

Four native-valid alternatives put recursion under actual combinators: a named
parser body, a closure adapter, a function-item adapter, and a function-pointer
adapter. All fail with reproducible Aeneas diagnostics at both MIR stages.
Charon's monomorphization option also reaches an Aeneas prepass failure on the
named candidate at both stages. The runner checks these ten negative translations
separately; they are not verified code or proof that every possible API must fail.

The [extraction follow-up](../rusthammer/probes/recursive_extraction/README.md)
identifies the cause: Charon suppresses the method's real dependency on its own
implementation record; retaining it exposes a function/implementation cycle
unsupported by Aeneas. Indirect entry points can make Aeneas emit Lean, but that
Lean still fails on an unknown implementation constant. Both MIR stages agree.
The isolated Charon patch diagnoses the cycle without fixing extraction; no
production tool pin changes.

A small handwritten Lean model establishes a possible function-fixed-point
definition and its unfolding equation with an explicit monotonicity proof. This
does not establish preservation of Rust behavior or soundness of a general
translation. The proposed tool direction and its obligations are recorded below;
neither it nor source generation has been selected for production.

The direct probe records a correctness/termination proof plan based on input
progress and a finite function-phase rank. It supplies neither those proofs nor
a physical stack bound. The production combinator gate remains open until the
construction/evaluation representation and its admissibility/resource contract
are settled. The prior packrat evidence remains useful independently.

## Proposed extraction direction and soundness requirements

Aeneas represents trait implementations as records of methods. In the failing
case, the implementation record contains the evaluator, and that evaluator
passes the record to a generic combinator. One possible translation would put
the recursion into functions and construct method records from those functions:

```text
eval(args) = body({ eval := eval }, args)   // recursive function
rule       = { eval := eval }              // record built from that function
```

This is a proposed change to the extracted Lean representation. It does not call
for adding runtime dictionaries to RustHammer. The
[handwritten experiment](../rusthammer/probes/recursive_extraction/DictionaryFixedPoint.lean)
uses Lean's `partial_fixpoint`, proves monotonicity in the computation order, and
proves the resulting body-unfolding equation. Its theorem's only axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

The experiment establishes a valid target definition. It supplies no theorem
relating that definition to the Rust or LLBC source semantics. An unfolding
equation alone would not suffice: `f(x) = f(x)` admits constant-returning
solutions, while an immediately self-calling source function has no successful
return. A sound translation must relate the chosen least fixed point to source
execution, including nontermination and errors.

Before implementing a general transformation, define its supported class and
develop a semantic-preservation argument. A useful initial class could have pure
method records with independently resolved associated types and constants.
Rebuilding such records must neither execute source computations nor duplicate
or discard parser configuration, captured values, or state. Establish that:

- Every dispatch reaches the same implementation with the same generic
  substitutions, arguments, associated types, and parent-trait dictionaries.
- Each translated body preserves evaluation order, state updates, borrow
  handling, return values, and modeled errors under corresponding child methods.
- The recursive equations and monotonicity proofs yield the source behavior;
  mutual recursion requires the corresponding joint fixed-point argument.
- Dependencies outside the supported class are diagnosed explicitly. Recognizing
  a mixed recursive group does not make every such group suitable for this rewrite.

The Charon dependency fix and the Aeneas transformation are separate work. The
isolated Charon patch only exposes the cycle; changing declaration order or
obtaining a successful Aeneas exit status does not solve it. Tool integration
would need a reviewed, validated revision, both MIR stages, generated Lean
checking, the real combinators, and ordinary downstream consumers. Extraction
tests supplement the semantic argument rather than replacing it.

An alternative is generating ordinary recursive Rust functions from structured
grammar bodies. The passing direct probe motivates that route but currently
expresses the body by hand. General generation would need its own typed
construction, lowering, and refinement argument while preserving a grammar
description usable by other interpreters. Neither approach is being implemented
as part of the first version.

## Shared grammar API and backend capabilities

Retain `Grammar<'input>::Output`, existing concrete combinators and construction
functions, and the separation between construction and interpretation. The
previous `grammar { rule ... }` sketch was one possible generated frontend, not
a requirement. On resumption, investigate the recursive combinator first. Any
generated type or storage machinery needed by the compiled backend must preserve
that construction interface; the private packrat model is not evidence for a
mandatory grammar DSL.

A recursive reference must have a finite Rust type and a known output family.
For example, a numeric parser's `Grammar<'input>::Output` is `usize`, and a span
parser's is `BitSpan<'input>`. A configured-pattern output can retain its separate
configuration lifetime. Do not tie those output lifetimes to the short borrow of
a parser reference or execution workspace. The exact reference type and ownership
mechanism are subjects of the investigation above.

References must resolve to the correct grammar instance. A shared Rust lifetime
alone does not establish instance identity. Internally, separate configured
parsers must not be merged merely because their Rust type or body shape is the
same, and copies of one reference must preserve its identity. Source references
need not be compiled-grammar handles. A typed packrat root, when introduced,
must be bound to its immutable compiled instance. A fresh packrat session fixes
the input, grammar, and configuration; its cache cannot be reused with another
snapshot or grammar.

Construction requires `Grammar`, not `Eval<Direct>`. A recursive reference need
not implement `Parser` merely to appear in a body. Execution capabilities are
separate: direct evaluation for supported terminating recursion, and packrat
compilation/execution for its admitted grammar class, including left recursion.
Supporting construction of a cycle does not establish that either evaluator
can execute it.

The proposed packrat architecture retains a separate lowering capability and a
machine with explicit control frames. Its calls refer to finite identities rather
than recursively instantiating interpreter dictionaries. The private
[experiment](../rusthammer/probes/recursive_rules/lib.rs) exercises the complete
seed/growth protocol, including mutually recursive rules. It is an executable
model, not a correctness proof or production implementation. For packrat,
compile an immutable grammar, reject unsupported operations or invalid
declarations, and execute a typed root on one input snapshot with a workspace
and explicit limits. Its typed value schema remains a separate design gate.

## Lowering and stored values

Use a separate lowering capability for the admitted grammar class. The proposed
compiled program contains owned instruction metadata, rule definitions, and
source/configuration identities. Immutable configuration is supplied separately.
The control stack contains instruction IDs, cursors, contexts, and value-slot
IDs. It should not carry an arbitrary sum of borrowed Rust values.

The private `lowered` entry point builds a recursive body using the actual
`seq`, `choice`, `Ignore`, `Literal`, and `Recognize` structures. Its private
`LowerRecognition` implementations emit instructions without evaluating the
body. The interpreter then executes the recursive calls. This establishes a
working construction/lowering/execution path for a pure recognition subset.
It does not establish a general compiler for every existing combinator.

Do not treat recognizing a grammar as permission to discard arbitrary actions:
`Verify`, `TryMap`, and `Bind` can affect acceptance. The recognition probe has no
blanket lowering implementations for these operations or `Map`. Production
lowering must either preserve the relevant computation or reject that source
capability. Arbitrary input-dependent grammar creation is outside the initial
closed-grammar compiler; `Direct` retains its existing `Bind` support.

Choose value-preserving replay at memoized rule boundaries as a permanent
capability requirement. `Clone` is the default Rust mechanism for owned results;
it is not a bound on every grammar output or intermediate computation. A final
mapping outside memoized boundaries may construct a non-`Clone` object, as the
private `owned` fixture demonstrates. Purity, termination, and value preservation
remain proof obligations; neither `Fn` nor `Clone` establishes them by itself.

Use a generated, statically typed value-storage schema. This can be a product of
typed stores with a finite owned tag/handle type for control flow. The model
instantiates a small schema for numbers, input spans, and configured patterns.
Its private tagged values are checked against the instruction/rule kinds; they
are not a uniform public AST or `Any` downcasts. A production schema generator
must establish the analogous type invariant for each supported value family.

Built-in borrowed views have a useful storage encoding:

- An input span stores its two cursors and enclosing bit direction. Materializing
  the output calls the existing checked `BitSpan::new`; an aligned byte view uses
  `as_bytes` and retains the original input lifetime.
- A configured pattern refers to immutable configuration, with checked bounds;
  replay returns the configured slice, independently of the input lifetime.

These coordinates remain valid because a session fixes their sources. They are
not sufficient to represent arbitrary callback-produced references. Such outputs
need typed reference storage or an explicit, verified encoding with provenance.
The earlier [typed-cache probe](../rusthammer/probes/backend_memo.rs) supplies
separate evidence for simple typed borrowed-result tables. Combining general
value stores, callbacks, and the new control machine still needs an exact
extraction check before that production capability is implemented.

Shared tree/arena handles can satisfy replay when their ownership contract is
explicit. They are not an assumed later replacement for a temporary deep-cloning
engine. The proposal does not promise constant-cost cloning of arbitrary outputs,
or claim that `Rc` and a general arena API have been validated with Aeneas.

## Rule invocation and left-recursion growth

Use the rule-invocation protocol implemented by
[C Hammer](../src/backends/packrat.c) as the starting point, with explicit
provisional answers, recursion heads, involved-rule sets, and per-round
reevaluation sets. The algorithmic reference is
[Warth, Douglass, and Millstein](https://www.cs.ucla.edu/~todd/research/pepm08.pdf).
The Rust representation must make the lifetime of these states explicit.

On a new rule invocation, install an internal failure seed and record the active
invocation. A recursive encounter identifies the head and involved rules. After
the first successful answer, repeatedly evaluate the head body, permitting each
involved rule to be reevaluated during that round. Keep an improved answer only
when its end cursor advances lexicographically. Keep the earlier answer on an
equal-length result. This gives nullable seeds a defined role without allowing
unbounded same-length growth. A cycle with no successful seed rejects; it is a
supported empty-language case, not an unsupported-recursion diagnostic.

The machine uses explicit frames for ordinary sequencing, alternatives, rule
completion, reevaluation, and growth. It has no Rust call-stack recursion.
Structural instruction edges are acyclic; rule calls are the only cyclic edges.
The same driver handles consuming, direct-left, and mutually left-recursive
fixtures. There is no interim driver that turns every recursive encounter into
a fatal error.

`NeedMore` and fatal errors abort the invocation, including during growth. Do not
return a shorter provisional success when the next growth round is incomplete.
Discard the session's speculative memo state; a retry starts against the new
snapshot. Recoverable rejection ends unsuccessful growth and retains the best
previous success. This preserves the existing distinctions between rejection,
incompleteness, and fatal execution failure.

For the finite ordering/finality context, treat `(rule identity, context)` as an
**effective rule symbol** and the cursor as its position. Memo keys include both.
Growth heads are indexed by position and their involved sets contain effective
symbols. This is the explicit product-grammar interpretation of context; indexing
heads by `(cursor, context)` as well would split a mutual cycle that changes
context. Additional semantic parameters require equivalent specialization or a
separately justified key scheme.

The proposal retains RustHammer's byte-boundary restriction for bit-direction
changes. Scopes delegate entry validation to the actual library and check
successful exit alignment. The model accepts only valid entry cursors; any
refinement theorem must state this domain, since `Direct`'s `Epsilon` also accepts
raw invalid cursors. The production entry contract must retain that distinction.

## Storage, sessions, and resources

Recommend dense indexed tables for the first fixed-grammar capability, with
checked workspace-size arithmetic, and explicit stacks and set storage. Cache
lookups do not linearly search previous entries. The model uses packed `u64`
rule sets and checks the layout before entering the machine. Production schema
generation must account for the contexts and value stores admitted by the compiled
grammar; the probe reserves all eight ordering/finality contexts.

The production execution entry should accept caller-provided workspace of a
validated size. Check the required layout before execution and perform no
implicit workspace growth while parsing. This provides a permanent bounded-memory
option and avoids promising recoverable allocator failure from ordinary `Vec`
allocation. An owned allocating convenience, if added, needs a fallible allocation
contract and its own extraction/model evidence before implementation.

Separate workspace capacity, control-stack capacity, and execution-step limits.
Exhaustion is a fatal execution outcome, never a branch mismatch or an internal
failure seed. Extend the production fatal error vocabulary when introducing this
backend so existing combinators propagate it. Compile-time validation errors
remain separate from parse outcomes. The private `Answer::Fatal(Fault)` enum is
a diagnostic model, not a proposed replacement for `ParseOutcome`.

The model pre-sizes its vectors, checks workspace capacity before execution,
clears memo/head metadata on reuse, and bounds every stack push and transition count.
Its allocation helper uses ordinary `Vec` allocation; its cell ceiling is not a
proof of a total byte budget or recoverable OOM. It demonstrates the execution
protocol after allocation, not the final workspace constructor. Step limits
count machine transitions, not the cost of a primitive, callback, clone, or drop.

No unconditional linear-time claim follows from named-rule memoization. Compiler
normalization, repeated suffix work, actions, replay costs, and left-recursion
growth all enter the cost argument. Dense storage is also potentially expensive
for sparse use of bit positions and contexts; expose the checked workspace
requirements rather than hiding that cost.

## Compatibility evidence and a C discrepancy

The pinned-tool runner is
[`check_recursive_rules.py`](../rusthammer/tools/check_recursive_rules.py).
It checks twelve native tests, six roots at promoted and optimized MIR, and those
six roots through a normal Cargo dependency,
then type-checks the generated Lean with warnings as errors and no admitted or
opaque project declarations. The generated files stay under ignored `target/`.

Fixtures exercise consuming and nested recursion, direct and mutual left
recursion, nullable/equal-length/seedless cases, numeric and borrowed-view rules
in one cycle, distinct configured identities, checked left-associative subtraction,
partial-input retries, ordering contexts, bit cursors, escaping partial spans,
independent input/pattern lifetimes, non-`Clone` final construction, and fatal
resource limits. The source-node lowering fixture exercises an actual structured
recursive description. These are native semantic tests and extraction evidence;
there is no engine-correctness, lowering-correctness, or complexity theorem yet.

A minimized [borrowed-sum diagnostic](../rusthammer/probes/recursive_rules/borrowed_sum.rs)
compiles in Rust but fails Aeneas at both MIR stages with `Unreachable` in
`InterpBorrowsCore.ml`. It replays a sum carrying independently borrowed input
and pattern slices. The positive machine avoids that representation. This is
separate from the old recursive-trait dictionary cycle and the deferred mapping
callback problem. The runner checks this expected negative case separately; it
must never count its failed translation as verified code.

[`check_recursive_rules_c.py`](../rusthammer/tools/check_recursive_rules_c.py)
compares 1,016 cases over eight fixtures against the checked-out C packrat engine.
It records 985 acceptance/consumption agreements and 31 discrepancies in one
context-changing mutual-recursion fixture:

```text
A = choice(seq(with_little_bytes(B), 'a'), 'a')
B = with_big_bytes(A)
```

On final `aa`, Rust's proposed product-context semantics consumes two bytes; C
consumes one. The terminals are whole-byte `a` literals, whose values are unchanged
by byte order. Removing the scopes gives the ordinary mutual-recursion fixture,
which agrees with C. All 31 differences have an initial run of at least two `a`s;
C returns the one-byte seed. The runner records these separately in
`target/recursive-rules/c-differences.json` and rejects unexpected differences.
Adding an end-of-input check also makes C reject scoped `aa`, while the unscoped
mutual grammar accepts it; this is not just a difference in reported match length.

C indexes its growth heads by the full `HInputStream`, including ordering state;
this is consistent with splitting the cycle across contexts. That explanation is
an inference from the implementation and reproducer, not a proved diagnosis of
C. Recommend the explicit product-context interpretation for RustHammer, with
this discrepancy recorded as an intentional proposed compatibility difference.
Do not claim full C equivalence or silently restrict all recursive rules to one
context. No C implementation has been changed as part of this investigation.

## Conditions for resuming implementation and proof work

This work is deferred, not complete. On resumption, first reproduce the retained
failures with the chosen tools and establish a scoped soundness argument for the
selected translation or generation approach. Validate the resulting structured
body representation with actual combinators before adding a production
`recursive` API. Establish reference resolution and body-unfolding contracts,
preservation of typed outputs and source lifetimes, context/error propagation,
and a well-founded recursion argument for the supported grammars. Existing
combinator contracts should supply the body semantics. Extraction and native
tests alone do not prove these obligations or a physical stack bound.

The completed packrat design increment supplies a separate API/execution proposal
and a checked private model. Before adding a production packrat API:

1. Validate lowering and the generated value schema for recursive combinator
   bodies with representative heterogeneous outputs and callbacks. Preserve the
   successful separation of instruction/control data from stored values and
   configuration. The tested recognition lowerer is not a general action compiler.
2. Extend the checked layout/session operations to the generated typed value
   stores and the intended caller-workspace API. The model validates dense
   indexing, packed sets, capacity errors, and fresh sessions; it does not yet
   generate layouts for arbitrary output schemas or provide a fallible allocator.
3. Fix the admitted grammar class and the proposed context-cycle compatibility
   difference in the production contract. Explicitly describe unsupported
   dynamic rule families and operations.

Then implement retained components of that design. Proof obligations include
instruction typing and lowering refinement; frame and table bounds; value replay
and source provenance; active-stack/head membership; provisional versus settled
entries; strict growth and equal-length tie behavior; propagation of `NeedMore`
and fatal errors; and session separation. Prove non-left-recursive refinement and
left-recursion semantics for that same implementation in separate milestones.
Existing combinator proofs supply source semantics; a compiled machine still
needs its own refinement proof. No placeholder production backend is needed to
make progress on these obligations.
