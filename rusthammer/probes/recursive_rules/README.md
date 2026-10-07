# Recursive rule and left-recursion design checks

This is a private experiment retained for the
[deferred recursion writeup](../../../plans/rusthammer-recursive-rules.md). The
first version targets nonrecursive grammars; this model and the related recursion
investigation are outside its implementation requirements. Nothing here is
exported by RustHammer or selected by a production Cargo feature.

Run from `rusthammer/` with the pinned tool checkout:

```sh
LEAN_NUM_THREADS=3 python3 tools/check_recursive_rules.py
python3 tools/check_recursive_rules_c.py
```

The first command accepts `--aeneas-dir` and
`--stage promoted|optimized|consumer|all`. Its default checkout is
`target/extraction-tools/aeneas`; it checks both source and binary revisions.
Generated Lean, compiler outputs, and logs go under `target/recursive-rules/`.
The C comparison uses GCC to build the core directly; it does not require the
GLib test suite or modify C Hammer.

## Positive checks

The immutable instruction graph has separate configured rule identities, a
finite value schema, and a stack machine implementing seed growth and mutual
recursion. Growth bookkeeping uses effective `(rule, context)` symbols. There
is no Rust call-stack recursion, recursive interpreter dictionary, linear memo
lookup, or active-entry error standing in for left-recursion support.

Instruction metadata and frames own their data. Input spans retain cursors and
bit direction; configured views refer to the immutable pattern source. The root
materializes slices or actual `BitSpan` values with the original source lifetime.
The six extraction roots are:

| Root | Evidence |
| --- | --- |
| `parse` / downstream `recursive` | Full rule driver, scalar values, growth, contexts, and bounded execution. |
| `borrowed` | A slice escapes the local program and workspace after mutual left recursion. |
| `pattern` | Output borrows configuration independently of the input. |
| `owned` | Final application construction has no `Clone` or `Copy` bound. |
| `lowered` | Actual library constructor/combinator nodes describe a recursive body, then lower to the instruction graph without executing it. |
| `bit_span` | A partial-byte span escapes left-recursive parsing and retains its input and direction. |

Twelve native tests cover direct/mutual/heterogeneous and consuming recursion,
nullable/equal-length/seedless cases, nested structure, checked left-associative
subtraction, incomplete growth, fresh sessions when reusing workspace,
configuration identity, both bit/byte orders, partial/final input, bit positions,
escaping borrows, malformed descriptions, and fatal workspace/stack/step limits. All six roots are
checked at both MIR stages and through a separate Cargo consumer, followed by
Lean type-checking without admitted/opaque project declarations.

The workspace uses dense entries and packed `u64` rule sets. It checks layout
before execution and clears memo/head metadata at each new session. Its storage
is allocated before interpretation; the machine never grows a vector. The
private allocation helper still uses ordinary `Vec` behavior. Neither its cell
ceiling nor successful extraction proves recoverable OOM, a physical byte budget,
or an engine correctness/complexity theorem.

The source lowerer admits only a pure structural recognition subset; it has no
blanket implementation for actions, predicates, or `Bind`. Private construction
tokens are unbranded indices and are confined to these fixtures. They are not a
proposal for exposing raw IDs or a generally typed runtime grammar builder.

## Negative extraction check

`borrowed_sum.rs` is a minimized source shape from the first representation. It
is valid Rust, but the pinned Aeneas fails to replay a sum of independently
borrowed input/pattern slices, reporting `Unreachable` in `InterpBorrowsCore.ml`.
The default runner checks the expected diagnostic at promoted and optimized MIR
and writes separate logs. A changed diagnostic or an unexpected success requires
investigation; the negative files are never imported as checked Lean code.

The passing representation keeps these references out of the control/value sum
and materializes borrowed views at typed boundaries. This does not establish that
all borrowed outputs fail extraction or that arbitrary callback-produced views
can be encoded as input-relative spans. Generic typed replay/callback storage
remains a production design gate.

Two source-shape adjustments also matter with the pinned tools: keep the main
loop's exit test inside `loop`, and separate consecutive validation loops that
return early. Primitive validation and parsing use the actual library; generated
Lean is never hand-edited and no translation check is disabled.

## C comparison

The corpus contains 1,016 cases: eight recursive fixture grammars over every
string of `a` and `x` through length six. There are 985 agreements on acceptance
and consumption, and 31 documented differences in the context-changing mutual
cycle. Rust decoded-count checks are separate; C ASTs are not compared.

For `A = (little(B) 'a') / 'a'; B = big(A)`, final `aa` consumes two bytes in the
proposed product-context interpretation and one in C Hammer. The C wrapper uses
only byte literals, so the byte-order scopes do not change primitive values.
An additional end-of-input check confirms that C rejects scoped `aa` and accepts
the unscoped mutual grammar on the same input.
The runner checks the exact known discrepancy class, emits
`target/recursive-rules/c-differences.json`, and rejects any additional difference.
These cases are not counted as agreements. See the proposal for the inference
about C's head keys and the recommended Rust semantics.
