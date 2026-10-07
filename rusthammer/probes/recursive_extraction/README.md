# Recursive evaluator dictionary extraction

Investigation retained; further work deferred at the user's request, 2026-10-06.
The first version of RustHammer targets nonrecursive grammars. This records a
tool limitation; it does not implement a recursion API or change the production
toolchain. See the [deferred design writeup](../../../plans/rusthammer-recursive-rules.md).

**There are two layers to the named-parser failure.** Charon loses a real
dependency on the method's own trait implementation. Retaining that dependency
exposes a function/implementation cycle that the pinned Aeneas does not support.
Changing the entry point can conceal the missing-name error without producing
valid Lean.

## Root cause

The minimal [Rust reproducer](../backend_recursive_trait.rs) implements
`Eval<Direct>` for `Rule`. Its method calls a generic `body<B>` with a
`Rule: Eval<B>` bound; that body calls `Rule.eval` after decreasing a counter.
There are no parser lifetimes, associated output types, closures, allocation,
memo tables, or left recursion in this reproducer.

In the extracted representation, a trait becomes a record of methods. A generic
call receives that record as an explicit argument. The dependencies are:

```text
Rule's implementation record → its eval function
its eval function → body(Rule's implementation record, ...)
```

Rust accepts this static-dispatch recursion. The proof translation must express
the corresponding recursive functions rather than emit the two definitions as
ordinary, independent declarations.

At Charon `c8f15d7d658c86a95658f71ad99cddd4be002e04`,
`charon/src/transform/add_missing_info/reorder_decls.rs` suppresses references to
a method's parent implementation in `DepsForItem::enter_trait_impl_id`. The
surrounding comment explains that this avoids artificial cycles from associated
types in signatures. The suppression also covers a real implementation argument
passed to a generic function. Consequently, the implementation exists in
`trait_impls` but is absent from `ordered_decls` when nothing else reaches it.

Aeneas `557eff83ecef5083b98a52a94ca7fae63d6c1dab` selects declarations from that
ordering in `src/interp/Interp.ml`. It therefore neither translates nor registers
the implementation. The error eventually appears during name lookup in
`src/extract/ExtractBase.ml`: `Could not find: trait_impl_id`.

The [isolated diagnostic patch](charon-dependencies.patch) retains implementation
dependencies inside function references, while leaving the existing signature
handling in place. Charon then includes both the method and its implementation
in one mixed recursive group. Aeneas rejects that group explicitly in
`src/interp/Interp.ml`, before symbolic translation. This patch exposes the
underlying limitation; **it is not a fix for recursive extraction**.

## Controls and results

The [runner](../../tools/check_recursive_extraction.py) checks each case separately
at promoted and optimized MIR. It inspects the LLBC dependency groups as well as
the tool exit statuses and generated Lean. The results are identical at both
stages:

| Entry | Pinned tools | Diagnostic Charon patch + pinned Aeneas |
| --- | --- | --- |
| Minimal `plain` | Extraction and Lean checking pass. | Extraction and Lean checking pass. |
| Minimal `run` | Missing implementation name. | Mixed recursive group rejected. |
| Minimal `indirect` | Aeneas succeeds; Lean rejects an unknown implementation constant. | Mixed recursive group rejected. |
| Actual combinators, `named` | Missing implementation name. | Mixed recursive group rejected. |
| Actual combinators, `named_parser` | Aeneas succeeds; Lean rejects an unknown implementation constant. | Mixed recursive group rejected. |

`indirect` calls the generic body from outside the implementation.
[`named_parser`](../direct_recursion/candidates.rs) uses the actual blanket
`Parser::parse_with` entry point. Each makes the implementation reachable from
another declaration, but Charon still omits the method-to-implementation edge.
The emitted method therefore references an implementation constant declared
later; swapping their order would merely reverse the unresolved dependency.
An Aeneas exit status of zero is insufficient evidence of successful extraction.

All 256 native counter inputs pass for the minimal fixture. The ten existing
direct-recursion native tests also pass, with the candidate test extended to
cover `named_parser`. The original ten negative controls remain in
`check_direct_recursion.py`; the follow-up checks here do not replace them.

The prior closure/function-item failure already reports a mixed recursive group.
The present result links the named case to that same unsupported class of
dependencies. Explicit function pointers and the array-`Default` failure under
monomorphization remain separate limitations.

## A possible target representation

The handwritten [Lean model](DictionaryFixedPoint.lean) checks a possible shape:

```text
eval(args) = body({ eval := eval }, args)       -- function fixed point
rule       = { eval := eval }                  -- ordinary record afterwards
```

The function uses Lean's `partial_fixpoint`, with a checked monotonicity proof.
Its `rule_unfold` theorem establishes the body-unfolding equation; its only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Simply adding
`partial_fixpoint` did not make Lean's default monotonicity tactic discharge the
call through the generic body in this experiment.

This file is independently written Lean, **not generated output**, a Rust
extraction success, or a refinement/termination proof. No failed generated file
was edited. It demonstrates that this small cycle can be represented in the
target logic. Automatically producing such definitions and proofs for the real
combinators remains tool work.

Aeneas's existing `impl_def` support is for a different case: eliminating
self-references in default methods by unfolding them and substituting already
resolved fields. See its `backends/lean/Aeneas/Tactic/Elab/TraitDefault/Init.lean`.
It requires those record self-references to disappear and does not implement
arbitrary recursive methods.

## Reproducing the investigation

From `rusthammer/`, with the pinned tools and Lean dependencies:

```sh
LEAN_NUM_THREADS=3 python3 tools/check_recursive_extraction.py
```

To repeat the isolated Charon experiment, clone the pinned checkout into an
unused directory under `target/`, apply `charon-dependencies.patch` there, and
build with the same Rust toolchain. For example, from `rusthammer/`:

```sh
git clone --shared target/extraction-tools/aeneas/charon target/recursive-extraction-charon
git -C target/recursive-extraction-charon apply ../../probes/recursive_extraction/charon-dependencies.patch
RUSTUP_TOOLCHAIN=nightly-2026-09-17 cargo build --locked --release \
  --manifest-path target/recursive-extraction-charon/charon/Cargo.toml \
  --bin charon --bin charon-driver
LEAN_NUM_THREADS=3 python3 tools/check_recursive_extraction.py \
  --candidate-charon target/recursive-extraction-charon/charon/target/release/charon
```

The runner validates the pinned baseline checkouts and binary revisions, rejects
unexpected successes or diagnostics, rejects admissions in generated output,
checks the handwritten model separately, and writes logs/dependency summaries to
`target/recursive-extraction/`. With the optional candidate it records twenty
extraction cases: four ordinary-recursion successes and sixteen expected failures
across the two tool variants and MIR stages. It does not install the candidate.

The isolated patch also passed Charon's full `make test` and `make clippy`.
The Rust UI run had 480 passes and four ignored cases, including two added copies
of the minimal reproducer for the MIR stages; the OCaml tests passed as well.
One existing snapshot changed: `issue-70-override-provided-method.2.nodup.out`.
Review of its LLBC confirms newly recognized mixed cycles between the default
method implementations and their functions, consistent with the dependency fix.
The optional OCaml formatting step reported an unavailable `ocamlformat` and was
ignored by the upstream Makefile; no OCaml source was edited. Rust formatting
checks passed. These checks validate the diagnostic patch's behavior, not support
for the resulting groups in Aeneas.

## Implication for RustHammer

This investigation is set aside for the first version. The proposed tool work
below is a direction to revisit when recursion is reprioritized.

Do not change associated types, constructor return types, or the backend split
on the strength of this failure. None causes the minimal example's cycle.
Renaming the recursive wrapper or routing it through `Parser` does not solve it.

On resumption, first specify a supported class and develop a semantic-preservation
argument for a lowering that replaces cyclic method dictionaries with recursive
functions and reconstructs their records. A monotonicity proof makes the Lean
fixed point well-defined but does not establish that it models the Rust program.
The transformation must preserve dispatch, evaluation order, state and borrow
handling, errors, nontermination, associated types, parent traits, and generic
substitutions. Mutual recursion needs the corresponding joint argument. The real
combinator and downstream-consumer checks are also required; the small Lean model
is a starting point, not validation of the general transformation.

Generating ordinary recursive Rust functions from structured grammar bodies is
another possible direction, with separate construction and refinement work.
Neither route has been selected as a production implementation. The requested
`recursive(|self_ref| body)` API and its admissibility/resource contract remain
open, and the existing handwritten-parser fallback is not promoted to that API.
