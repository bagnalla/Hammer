# Floating-point extraction investigation

Status: investigated with the pinned tools on 2026-10-07. Native Rust decoding
works, but native floating-point outputs and range checks do not yet meet
RustHammer's extraction and proof requirements. This is a private compatibility
probe, not a production API, a tool patch, or a decision to change tool versions.
Following the investigation, the user deferred native float readers/ranges and
the required Aeneas work beyond the first release. Retain this report and its
reproductions for later work.

## Reproduce

From `rusthammer/`, with the existing Lean dependencies built:

```sh
python3 tools/check_floating_point.py
python3 tools/check_floating_point.py --native-only
```

The runner defaults to `target/extraction-tools/aeneas/` and checks the same
revisions as `tools/verify.py`:

- Rust: `nightly-2026-09-17`.
- Charon: `c8f15d7d658c86a95658f71ad99cddd4be002e04`.
- Aeneas: `557eff83ecef5083b98a52a94ca7fae63d6c1dab`.
- Lean: `v4.31.0`.

Use `--case NAME` to select individual cases. Logs, LLBC, generated Lean, and a
JSON result summary are written under `target/floating-point/`. A successful
runner exit means the integer controls passed and the particular documented
float failures were reproduced. It does **not** mean float extraction passed.

## Results

The [probe](lib.rs) uses ordinary `no_std` Rust and the actual RustHammer
`BeU32`, `Map`, cursor, and parsing entry points. The
[separate Cargo consumer](consumer/lib.rs) exercises dependency extraction.
Each case is checked at both promoted and optimized MIR. The runner rejects
generated axioms, opaque declarations, admitted proofs, and undefined names
that Lean could otherwise turn into implicit parameters.

| Operation | Result at both MIR stages |
| --- | --- |
| Integer field through `BeU32` | Extraction and strict Lean type-checking pass. |
| Binary32 NaN classification using integer masks | Extraction and strict Lean type-checking pass. |
| Binary16-to-binary32 **encoding** conversion using integer operations | Extraction and strict Lean type-checking pass, including through a Cargo consumer. |
| Identity functions on `f32` / `f64` | Aeneas emits undefined `F32` / `F64`; strict Lean checking rejects them. |
| `f32` equality | Strict Lean checking rejects undefined `F32`; no IEEE equality model is supplied. |
| `f32::from_bits`, `f64::from_bits`, and `to_bits` | Aeneas emits external axioms, rejected by the declaration audit. |
| Including the bodies of those conversion methods explicitly | Aeneas rejects their `transmute` operation. |
| Native `is_nan` | Aeneas emits an external axiom, rejected by the declaration audit. |
| Inclusive ranges over `f32` or `f64` | Aeneas rejects the ordered comparisons: `Invalid inputs for binop`. |
| Binary32 values with binary64 range bounds | Aeneas rejects the ordered comparisons. |
| `f32 as f64` alone | Aeneas reaches an unsupported scalar-cast extraction branch (`extract/Extract.ml`, line 487). |
| A float literal (`1.0f32`) | Aeneas rejects it as `Improperly typed constant value`. |
| Native float field, directly or through `Map` | The integer parsing path works, but the `from_bits` axiom fails the audit. The Cargo consumer reproduces that boundary. |
| Binary16 decoding returning `f32` | Integer encoding conversion works; the final `from_bits` call fails the audit. |

The full matrix has 25 cases at two MIR stages: eight supported integer-only
translations and 42 expected unsupported translations. Charon succeeds in all
50 cases; the limitations occur in Aeneas translation, the declaration audit,
or strict Lean checking. The successful controls are type-checking evidence;
this probe does not prove general IEEE decoding or range theorems.

### Why the identity test can misleadingly appear to pass

Aeneas generates the following shape for the identity case:

```lean
def identity32 (value : F32) : Result F32 := do
  ok value
```

Its imported support library does not define `F32`. With Lean's default
`autoImplicit` setting, this declaration nevertheless type-checks: `F32`
becomes an implicit type parameter. The result is a polymorphic identity
function, not evidence of an implemented float model. `F64` behaves similarly.
The runner uses `-DautoImplicit=false` as well as `-DwarningAsError=true`.
Lean's kernel is accepting a well-typed polymorphic definition here; this is not
a demonstration of kernel unsoundness.

### Why including the standard-library bodies does not fix conversion

With the default extraction policy, the conversion methods are opaque, so
Aeneas generates declarations such as:

```lean
axiom core.f32.F32.from_bits : Std.U32 → Result F32
```

That gives the operation no decoding specification and violates the production
declaration audit. The `*_body` cases explicitly include each Rust method body.
The pinned Rust implementation uses `mem::transmute`; Aeneas then reports
`Invalid input for unop: transmute<...>`. The limitation is not just a missing
include flag. The runner uses `core::f32::_` / `core::f64::_` module patterns:
the Charon CLI's primitive-type impl patterns did not make these bodies
transparent, so their LLBC bodies were checked when diagnosing this case.

Relevant locations in the pinned Aeneas checkout:

- `src/extract/ExtractBase.ml`, `float_name`: emits `F32` / `F64` names.
- `src/interp/InterpExpressions.ml`, `literal_to_tvalue`: rejects float
  constants; `eval_binary_op_symbolic` rejects float ordering, and
  `eval_unary_op_symbolic` rejects the conversion methods' transmutations.
- `src/extract/Extract.ml`: does not support the float-to-float scalar cast.
- `src/symbolic/SymbolicToPureExpressions.ml` also rejects `CastTransmute`
  downstream of symbolic interpretation.
- `backends/lean/Aeneas`: contains no `F32` / `F64` definitions or models for
  these float operations at the pinned revision.

## Native behavior and C Hammer comparison

Eight native probe tests and two Cargo-consumer tests pass. They cover signed
zeros, subnormals, finite extremes, infinities, NaN payloads, inclusive ranges,
reversed/NaN bounds, widening, unaligned parsing, truncation, and invalid cursors.
The binary16 test exhausts all 65,536 encodings and checks finite values against
an independent numerical specification, plus special-value classification and
NaN payload placement. These are native tests, not Lean proofs.

The C behavior below was checked against the local source and tests; this
investigation did not run a new C differential corpus.

- [`h_float32` / `h_float64`](../../../src/parsers/float.c) read the configured
  number of bits with the active input order and reinterpret the resulting
  encoding as IEEE binary32/binary64. Their constructors check that the host
  supports the required formats.
- `h_float16` returns C `float`: every finite binary16 value widens exactly to
  binary32, including subnormals. Its conversion preserves signed zero and
  places the NaN sign and payload in the corresponding binary32 encoding bits.
- [`h_float_range`](../../../src/parsers/float_range.c) compares inclusively,
  using `lower <= value && value <= upper`. It rejects NaN values and NaN
  bounds, treats the two zeros as numerically equal, and admits infinities when
  the bounds permit them. Reversed bounds describe an empty range; they are not
  rejected by C's constructor.
- C stores **double-precision bounds**, even for a child returning `float`, and
  widens the parsed value before comparison. Its
  [precision regression](../../../tests/parsers/test_float.c) rejects a binary32
  value of `1.0` against the lower bound `1.00000001`. Rounding the bounds to
  binary32 would change that behavior. The probe tests this distinction.

## Production implications

Reading the wire bits is already supported. The missing component is a model
and translation path for **native Rust float values and operations**. Rewriting
the parser combinators or removing partial-input support would not address it.

A possible tooling follow-up can target the operations needed by parsing,
without implementing all floating-point arithmetic at once. It would need:

1. Explicit bit-pattern models for binary32/binary64, preserving signed zeros
   and distinct NaN encodings where the Rust operation preserves them.
2. Justified models and translation rules for `from_bits`, `to_bits`, constants,
   classification, and the required comparisons. Numeric equality must handle
   NaNs and signed zero correctly; equality of encodings is a different relation.
3. A model for binary32-to-binary64 conversion if C-compatible double-precision
   range bounds are retained, including a deliberate NaN contract.
4. Parser and range theorems against independent IEEE specifications, with
   explicit assumptions connecting modeled primitives to the Rust operations.
   Adding arbitrary axioms or aliasing `F32` to a Lean float type would not by
   itself discharge those obligations.

Before choosing a public API, also settle whether float readers follow active
byte order or use named fixed-order variants, the binary16 output type, range
bound precision, and whether invalid configured ranges are constructor errors.
The probe's `BeU32`-based field and both range signatures are experiments, not
decisions about these interfaces.

Native applications can already decode integers with RustHammer and call Rust's
`from_bits` themselves. That conversion lies outside the currently verified
path. An encoded-float wrapper would be a different API and should only be
added if wanted as a permanent representation, not as a placeholder for native
float support. No such wrapper or production float parser is added here.

The current pins therefore do not support verified native float readers/ranges
without further tool/model work. Native float support and that tooling work are
excluded from the first release at the user's request. Revisit them when the
required Aeneas models and translation support are available or a dedicated
tooling effort is explicitly reprioritized. They are not first-release
completion requirements.
