# Direct recursive parser compatibility investigation

Status: initial investigation complete; further work deferred at the user's
request, 2026-10-06. The first version targets nonrecursive grammars. This private
package is retained as evidence for the
[deferred recursion writeup](../../../plans/rusthammer-recursive-rules.md) and adds
no production API.

**Ordinary recursive functions behind typed parser wrappers pass. The tested
ways of putting recursive calls inside ordinary combinator bodies fail
extraction with the pinned tools.** A general `recursive(|self_ref| body)`
constructor has not been established. Changing its surface spelling to a named
parser or a closure adapter does not by itself remove the extraction obstacle.

## Reproduction and evidence

Run from `rusthammer/`:

```sh
LEAN_NUM_THREADS=3 python3 tools/check_direct_recursion.py
```

The runner accepts `--aeneas-dir` and
`--stage promoted|optimized|consumer|negative|all`. The default tool checkout is
`target/extraction-tools/aeneas`. It verifies both checkout and binary revisions
against `tools/verify.py`; Rust and Lean use the repository's pinned toolchains.
Generated artifacts and separate negative diagnostics stay under
`target/direct-recursion/`. This runner uses unmodified pinned tools; no generated
Lean is hand-edited and no extraction check is disabled. The separately documented
[follow-up](../recursive_extraction/README.md) tests an isolated diagnostic patch.

Ten native tests pass. They cover the four native-valid negative candidates as
well as nested/mutual recursion, every bit/byte/finality context, incomplete input,
malformed delimiters, backtracking after consumption, nullable terminals, escaping
independent borrows, distinct configurations, non-`Clone` results, unaligned spans,
and fatal error propagation through actual outer combinators.

Six positive roots pass Charon/Aeneas and Lean checking at promoted MIR,
optimized MIR, and through a normal Cargo dependency:

| Root | What it checks |
| --- | --- |
| `configured` | Mutual recursion with different result types; output borrows configuration independently of the input. |
| `spanned` | Actual `WithSpan` returns the non-`Clone` decoded value and an independently borrowed input span. |
| `recognized` | Actual `Recognize` discards the decoded value; the span outlives local configuration. |
| `complete` | Actual `Seq` and `End` compose with the recursive parser. |
| `twice` | Actual `Seq` moves two non-`Clone` outputs from a reused configuration. |
| `count` | Ordinary consuming self recursion, including `NeedMore` and checked count arithmetic. |

The runner checks every expected root and rejects admitted/opaque project
declarations. These are semantic tests and extraction/type-checking evidence,
not correctness or termination proofs.

## Passing boundary

The `Pairs` wrapper implements the existing `Grammar` and `Eval<Direct>` traits.
Its evaluator calls ordinary mutually recursive Rust functions for:

```text
A = '(' B ')' / configured_pattern
B = '[' A ']'
```

`A` returns a configured-pattern borrow and nesting depth in a non-`Clone`
`Parsed` value; `B` returns a distinct `Inner` type. Every recursive cycle
consumes input before returning to its original function. The primitive reads
use the real library. The recursion uses the Rust call stack and does not
allocate, cache, replay values, or require a memo workspace.

The recursive functions express sequence/choice around their recursive calls
with ordinary Rust control flow. The existing combinators work **outside** this
recursive implementation. There is no cycle in their evaluator dictionaries,
because the functions do not invoke `Pairs::eval` to recurse.

This is evidence that ordinary direct recursion fits the existing API, not an
implementation of a reusable recursion-construction combinator. The handwritten
body is not inspectable combinator data, and there is no automatic packrat
lowering for it. Its `Eval` implementation alone cannot supply that capability.
The investigation does not select this loss of structure as the public design.

## Failing candidates

[`candidates.rs`](candidates.rs) contains four small, native-valid ways to place
a recursive call under the actual `Seq`/`Choice`/`Ignore` nodes. They all implement
the same consuming parser for a run of `a`s. Failures therefore do not require
left recursion, borrowed results, or memo storage.

| Candidate | Pinned extraction result at both MIR stages |
| --- | --- |
| `named` | A named parser evaluates a combinator body containing itself. Aeneas reports `Could not find: trait_impl_id`. |
| `closure` | An ordinary function supplies a closure-based parser adapter that calls the function again. Aeneas rejects a mixed recursive group of functions and closure trait implementations. |
| `function_item` | The same adapter receives the function item directly. Aeneas rejects the corresponding mixed recursive group. |
| `pointer` | An adapter stores an explicit Rust function pointer. Aeneas reports `Arrow types are not supported yet`. |

The runner also tries the named candidate with Charon's `--monomorphize` at both
MIR stages. Charon succeeds, but Aeneas fails in its array-`Default` prepass
(`PrePasses.update_array_default`). This demonstrates that monomorphization is
not a drop-in remedy for this source and tool configuration; it does not prove
that specialization could never work with improved tool support.

All ten negative translations are checked separately. Unexpected success or a
changed diagnostic fails the runner and calls for investigation. Failed Lean
output is never included among the passing checks. These reproductions narrow
the problem; they are not an impossibility proof for every Rust API shape.

## Direct semantics and proof plan

For the passing fixtures, an independent specification should describe ordered
choice, the delimiters, configured-pattern matching, and the computed depth.
It must preserve the existing distinction between recoverable rejection,
`NeedMore`, and fatal errors. In particular, incompleteness in the first branch
must prevent fallback even if the configured pattern could already match.

Prove the mutual equations using remaining input bits as a mathematical measure,
with a finite function-phase rank for calls that stay at the same cursor.
Successful reads before cyclic calls strictly decrease the input component.
Treat invalid cursors separately using the primitive contracts. A nullable
terminal is compatible with this argument: the recursive cycle still consumes
the delimiters. Neither the native tests nor Lean type-checking establishes that
proof yet.

Further obligations include cursor validity/progress, configured-pattern and
input-span provenance, preserved context, count bounds, exact rollback, and
moving/dropping non-`Clone` outputs. The existing primitive and outer-combinator
proofs provide reusable contracts for these obligations.

Logical termination does not bound the physical Rust stack. This experiment
provides no recoverable stack-exhaustion error or general recursion-admissibility
checker. It does not accept arbitrary left-recursive/zero-progress descriptions
and then silently convert their cycles to mismatch: the passing functions have
fixed consuming definitions. A reusable production API still needs its own
admissibility and resource contract.

## Conditions for resuming

These are conditions for resuming the deferred feature, not current first-version
tasks. No additional tool or recursion implementation is planned for now.

Keep the desired grammar-construction interface independent of packrat. Do not
export a nominal `recursive` wrapper around the handwritten fallback and call
the structured-body requirement solved.

The [extraction follow-up](../recursive_extraction/README.md) traces the named
failure to a missing Charon dependency. An isolated dependency patch exposes an
unsupported mixed recursive group in Aeneas. Calling the same parser through
`Parser::parse_with` instead makes Aeneas emit Lean with an unknown implementation
constant, so it is not a workaround. These results agree at both MIR stages.
The follow-up retains a checked, handwritten Lean fixed-point model as a possible
target representation; automatic lowering and its proof obligations remain open.
Its valid Lean definition and unfolding theorem do not establish preservation of
Rust semantics; a scoped soundness argument is required before generalizing the
transformation.
The pinned tools and production library are unchanged.

Another possible route is generation of ordinary recursive functions specialized
to a structured body. That needs its own construction/lowering design and
refinement proof, and is more than a spelling change to the API. It has not been
implemented or selected here. General `recursive` implementation remains gated
on a successful representation choice; the earlier packrat experiment and its
remaining typed-storage gates are unchanged.
