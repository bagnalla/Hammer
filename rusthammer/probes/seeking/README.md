# Seeking compatibility probe

This private Cargo package retains the investigation of a permanent seeking primitive using
RustHammer's real `Grammar` and `Eval` traits. It is not exported by RustHammer.
See the [design, composition audit, and proof contract](../../../plans/rusthammer-seeking.md).

Production `rusthammer::Seek` is now implemented and proved separately. Its
arithmetic/composition tests and downstream examples run in `tools/verify.py`;
the shared offset application has a Lean correctness proof. This package keeps
the earlier candidate, C characterization, and negative callback regression for
reproducing the investigation. Its extraction checks are not production proofs.

The candidate has checked absolute `Cursor` targets, signed relative bit
offsets, and signed end-relative offsets. Every successful seek returns its
destination cursor as both continuation and output. The independent native
oracle uses `i128` positions on the tested 64-bit host, while the candidate uses
checked byte/bit arithmetic. Tests cover `isize::MIN` and virtual lengths through
`usize::MAX` without allocating large inputs.

Run from `rusthammer/`:

```sh
python3 tools/check_seeking.py
python3 tools/check_seeking.py --c
python3 tools/check_seeking.py --native-only
```

The runner uses the revisions from `tools/verify.py`, defaulting to the checkout
at `target/extraction-tools/aeneas`; pass `--aeneas-dir` to select another checkout
at those same revisions. It checks binary revision IDs as well as Git heads.

The checks cover:

- Nine native tests for exhaustive small positions/offsets, machine-limit
  arithmetic, malformed configuration/cursors, partial input, ordering scopes,
  backtracking, lookahead, spans, repetition, match comparisons, and permutation.
- Two native consumer tests, with borrowed payloads, saved positions, and a
  stateful backend.
- Two probe roots and nine consumer roots at both promoted and optimized MIR.
  Each generated module is checked with Lean's `autoImplicit` disabled and
  warnings treated as errors; generated axioms, opaque declarations, and admits
  are rejected. Consumer roots also exercise `Bind`, `TryMap`, span outputs,
  bounded folding, and backward match comparisons.
- A separate native-valid function-item callback root that reproduces Aeneas's
  `Arrow types are not supported yet` failure at both MIR stages. The supported
  consumer uses the equivalent closure. It also uses a lossless `u8 as isize`
  cast because `isize::from(u8)` initially emitted an unproved external axiom.
- With `--c`, 145,233 C cases compared against an independent mathematical
  destination/bounds contract. There are 145,044 agreements and 189 reproduced
  cases where C's same-byte shortcut accepts positions just past EOF. A separate
  check observes wrapped unsigned `bit_length` on a backward seek child.

All native tests and four supported extraction runs pass on the pinned tools;
two negative runs reproduce the function-item limitation. The runner succeeds
only when all those expectations hold. These are extraction and behavior
checks; no generic Lean correctness proof for seeking is claimed.
The C characterization deliberately records discrepancies instead of adopting
them as the Rust contract. It builds C from the repository and leaves it unchanged.
The [C implementation issue log](../../../docs/c-implementation-issues.md)
contains standalone C reproducers and follow-up work for those discrepancies.

Generated LLBC, Lean, logs, and JSON results live under ignored
`target/seeking/`. No generated probe modules or tool patches are checked in.
