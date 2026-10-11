# Permutation compatibility cases

Historical investigation: permutation, its comparison runner, and its proof
generator are preserved at `c5c2643`. Run the commands below in that checkout;
see the [reproduction instructions](../README.md#historical-probes-and-reproduction).

At that baseline, the production implementation lived in
`src/grammar/permutation.rs`. This package ran it as an ordinary dependency to
generate the complete-input corpus for `tools/check_permutation_c.py`:

```sh
# From rusthammer/
python3 tools/check_permutation_c.py
```

The runner compiles the repository's C core with GCC; SCons and GLib are not
required. It compares 217,728 cases: three patterns chosen independently from
`""`, `"a"`, `"b"`, `"aa"`, `"ab"`, `"ba"`; all eight optional-entry masks;
every binary `a`/`b` input of zero through five bytes; and bit offsets zero and
three. It checks acceptance, consumed bits, and optional presence. Both adapters
also check each returned value against its declared pattern and tuple position.
All cases agree. The C adapter frees its parse results and parser graphs.

Partial input, fatal errors, backend effects, ownership, and all tuple arities
were covered by `tests/permutation.rs` at `c5c2643`. This corpus is
compatibility evidence, not a proof of general equivalence with C Hammer.

## Extraction evidence

The initial private candidate passed promoted and optimized MIR extraction and
generated Lean checking with the pinned tools, including independent input and
configuration borrows and owned outputs without `Clone` or `Copy`. The candidate
has been replaced by the production implementation; there is no duplicate search
algorithm in this directory. At `c5c2643`, extraction checks belonged to the
normal `tools/verify.py` runner and cross-crate fixture. The v1 verifier has no
permutation roots.

The repetitive tuple storage proof source was maintained by
`tools/generate_permutation_tuple_proofs.py` at `c5c2643`.
It reads only the generated declaration names and emits explicit storage/output
specifications with proofs checked by Lean. The baseline verifier rejected stale
proof source. The generator and permutation proofs have been removed from v1.

Two source-shape changes were needed. A loop containing early returns failed
translation; a loop calling the recursive search then failed the generated Lean
monotonicity check. Explicit recursion over the remaining entries and candidate
index passed both stages. Separately, unpacking several optional tuple outputs
in one match encountered the known optimized-MIR partial-move failure. Moving
one slot through the `slot_value` helper at a time passed. Neither adjustment
changes permutation semantics or requires a tool patch, additional ownership
bounds, or admitted declarations. These findings do not resolve the deferred
recursive-grammar dictionary or borrowed-callback issues.
