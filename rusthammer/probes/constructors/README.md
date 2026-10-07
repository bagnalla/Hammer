# Constructor API extraction probe

This private Cargo package tests a possible construction API without adding
public RustHammer functions. The helpers return existing concrete nodes and use
`Grammar` bounds, so construction does not require `Eval<Direct>`.

## Results

Checked on 2026-10-06 with Rust `nightly-2026-09-17`, Charon
`c8f15d7d658c86a95658f71ad99cddd4be002e04`, Aeneas
`557eff83ecef5083b98a52a94ca7fae63d6c1dab`, and Lean `v4.31.0`.
All six native tests pass. All 26 cases pass Charon extraction; 16 also pass
Aeneas translation, the declaration audit, and Lean type-checking. The other
10 fail during Aeneas translation as described below. Each row has the same
result with promoted and optimized MIR for the current crate; dependency
bodies use optimized MIR in both modes.

| Case | Result at both MIR stages |
| --- | --- |
| `baseline` | Pass |
| `constructors` | Pass |
| `borrowed_sources` | Pass |
| `backend` | Pass |
| `opaque_output` | Pass |
| `opaque_borrow` | Pass |
| `opaque_callback` | Pass |
| `consumer` | Pass |
| `borrowed_callback` | Aeneas: non-endable abstraction |
| `direct_borrowed_callback` | Aeneas: non-endable abstraction |
| `consumer_callback` | Aeneas: non-endable abstraction |
| `named_borrowed_callback` | Aeneas: higher-ranked/free lifetime constraint |
| `consumer_named_callback` | Aeneas: higher-ranked/free lifetime constraint |

The evidence supports adding constructor helpers that return concrete nodes.
The generic helpers themselves are extraction roots, so this checks more than
their concrete uses. The `CountByte` fixture has no `Eval<Direct>` implementation:
its successful construction and interpretation show that the helper bounds
preserve backend independence.

The tested `impl Trait` returns also preserve a concrete representation during
extraction. For example, `opaque_payload` becomes a Lean definition returning
`rusthammer.TakeAligned`, and `opaque_header` returns a concrete `Map` over a
`Seq`. The partially opaque `Map<..., impl Fn(...) -> ...>` remains usable by a
generic backend, including across the dependency boundary. The callback is
constructed in a nongeneric helper, respecting the separately documented
[backend-closure limitation](../README.md#closures-inside-lifetime-generic-evaluators).

The failing closure is just `|bytes| bytes`, mapping a parsed input slice to
itself. Constructing `Map` directly reproduces the same error without the new
helper. This matches the diagnostic seen in earlier
[borrowed callback probes](../README.md#capturing-callback-with-a-borrowed-record-output);
it does not establish a common internal cause or a failure of all borrowed
outputs. Replacing this closure with the ordinary `identity_bytes` function is
not a workaround: Aeneas rejects a constraint relating a higher-ranked lifetime
to a free lifetime. Both spellings remain as isolated negative probes, including
their downstream uses. They impose no new restriction on RustHammer's Rust API.

## Coverage and reproduction

The cases cover:

- A direct `Byte` baseline with no new construction helper.
- Generic `seq`, `map`, `try_map`, `verify`, `choice`, `bind`, and `optional`
  helpers, captured callbacks, recoverable rejection, and partial input.
- Separate input/configuration borrows, and negative controls for mapping
  callbacks returning a borrowed input slice.
- A child supporting only a custom backend, including a shared child reference
  and borrowed output surviving local backend state.
- `impl for<'input> Parser<'input, Output = u32> + Copy` returns.
- `impl for<'input> Parser<'input, Output = &'input [u8]>` returns.
- A concrete `Map<...>` with an opaque callback, used by a generic backend.
- A downstream Cargo consumer exercising dependency bodies, owned non-`Clone`
  outputs, and borrowed outputs.

From `rusthammer/`, run:

```sh
python3 tools/check_constructor_api.py --native-only
python3 tools/check_constructor_api.py --aeneas-dir /path/to/pinned/aeneas
```

The runner checks the Aeneas and Charon revisions pinned by `tools/verify.py`.
It runs both Cargo packages' native tests, then extracts each case at promoted
and optimized MIR stages, translates to Lean, checks that every requested entry
point was generated, rejects admitted/opaque project declarations, and invokes
Lean with warnings treated as errors. The existing `lean/` project's pinned
dependencies must be built before running the Lean checks.

Use `--case NAME` to select one case, or repeat that option to select several.
Logs, generated modules, and `results.json` are written under
`target/constructor-api/`. The runner continues after an extraction failure to
report the remaining cases and exits unsuccessfully if any selected case fails.
The default run deliberately includes the five negative probes above, so its
current expected exit status is 1, with 16/26 checks passing. For example, use
`--case constructors --case opaque_output --case opaque_borrow --case opaque_callback`
to check just those passing API shapes.

These checks establish extraction and Lean type-checking compatibility, not
correctness theorems for the experimental construction API. They also do not
change which capabilities Rust exposes through an opaque return: `impl Parser`
still hides other backends unless its bounds explicitly expose them.
