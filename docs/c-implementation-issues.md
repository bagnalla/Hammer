# C Hammer implementation issues

This log records reproducible issues and unresolved semantics in the C
implementation. It includes findings from RustHammer compatibility work so that
they remain available independently of the Rust design plans. No fixes for the
entries below have been applied as part of that work.

Last checked: 2026-10-07, C sources at `887a64b`, on 64-bit Linux.

| ID | Issue | Status |
| --- | --- | --- |
| C-001 | [Absolute bit-position limits depend on assertions](#c-001-absolute-bit-position-limits) | Open; helper-level reproducer. |
| C-002 | [Seeking just past EOF can succeed](#c-002-seeking-just-past-eof-can-succeed) | Open; reproduced through the public parser API. |
| C-003 | [Backward seeks produce wrapped child lengths](#c-003-backward-seeks-produce-wrapped-child-lengths) | Open; reproduced through the public parser API; intended length semantics need a decision. |

## C-001: Absolute bit-position limits

First recorded on 2026-10-04 in checkout `a8dc507`; rechecked on 2026-10-07.

[`h_input_stream_pos`](../src/internal.h) converts a byte position to an
absolute bit count using `size_t` arithmetic:

```c
(state->pos + state->index) * 8 + state->bit_offset + state->margin
```

For valid stream states, ordinary `assert` checks protect the addition and
multiplication. With assertions enabled, an oversized position aborts the
process. With `NDEBUG`, those checks disappear and unsigned arithmetic can
wrap. Optimization alone does not disable assertions: the current
[SCons `opt` variant](../SConstruct) adds `-O3` without defining `NDEBUG`.

Multiplication first overflows at byte position `SIZE_MAX / 8 + 1`: 512 MiB with
32-bit `size_t`, or 2 EiB with 64-bit `size_t`. The current assertion is stricter:
it requires `pos + index < SIZE_MAX / 8`, also rejecting the preceding byte
position. [`h_tell`](../src/parsers/seek.c) stores the result in a `uint64_t`
token, but widening after the `size_t` calculation cannot recover lost bits.

Save this helper-level reproducer as `/tmp/hammer-position-limit.c`:

```c
#include <sys/types.h>
#include "internal.h"
#include <stdio.h>

int main(void) {
    HInputStream stream = {.pos = SIZE_MAX / 8 + 1};
    printf("%zu\n", h_input_stream_pos(&stream));
    return 0;
}
```

Compile and run from the repository root:

```sh
cc -std=gnu99 -O2 -DNDEBUG -Isrc /tmp/hammer-position-limit.c -o /tmp/hammer-position-limit-ndebug
/tmp/hammer-position-limit-ndebug
cc -std=gnu99 -O2 -Isrc /tmp/hammer-position-limit.c -o /tmp/hammer-position-limit-assert
/tmp/hammer-position-limit-assert
```

The first executable prints `0`; the second aborts at the assertion in
`h_input_stream_pos`. This is a synthetic stream state: the reproducer does not
allocate or parse a 2 EiB input.

Follow-up: provide checked position/length arithmetic with a defined failure
path, and test boundaries with and without assertions. Related paths to audit
include `h_input_stream_length` in the same header, the base-position conversions
in [`h_seek`](../src/parsers/seek.c), result lengths in
[`packrat.c`](../src/backends/packrat.c), and the separate
`s->pos * 8 + s->bit_offset` calculation in [`h_parse_finish`](../src/hammer.c).
This reproducer is not a full audit of those paths. C-003 below concerns
subtraction at small, representable positions and occurs with assertions enabled.

## C-002: Seeking just past EOF can succeed

Observed on 2026-10-07 with the default packrat backend and assertions enabled.

The public [`h_seek` contract](../src/hammer.h) says that a destination before
the start or past the end of input fails. However, when the current cursor is
already at EOF, seeking one through seven bits past EOF succeeds. The smallest
case is `h_seek(1, SEEK_SET)` on an empty final input: it returns a successful
`TT_UINT` token containing `1`. The expected result is parse failure (`NULL`).

The cause is the order of checks in [`h_seek_bits`](../src/bitreader.c). It first
handles `pos_index == stream->index` by assigning `bit_offset` and returning.
At EOF, that byte index also equals `stream->length`, so a nonzero target bit
offset bypasses the later bounds check. This does not occur for every seek past
EOF: targets in a different byte reach the bounds check normally.

The [seeking reproducer below](#seeking-reproducer) exercises the public API.
The retained [C characterization](../rusthammer/tools/check_seeking.py) also
checks lengths zero through eight bytes, every valid starting bit position,
all three origins, offsets from -80 through 80, and both signed extremes.
Of 145,233 cases, 145,044 agree with the mathematical target/bounds contract;
the other 189 are precisely these EOF successes. These cases use complete input
and default ordering. They do not establish behavior for arbitrary mixed bit
directions or streaming buffer management.

Follow-up: validate the destination before the same-byte shortcut. Add regression
coverage for offsets one through seven past EOF, empty inputs, all three seek
origins, and starting both inside the input and exactly at EOF. Preserve valid
same-byte seeks and an exact-EOF destination.

## C-003: Backward seeks produce wrapped child lengths

Observed on 2026-10-07 with the default packrat backend and assertions enabled.

[`perform_lowlevel_parse`](../src/backends/packrat.c) computes a successful
parser's length by subtracting its starting position from its ending position
using `size_t` arithmetic. A seek from bit 8 back to bit 0 therefore receives
`SIZE_MAX - 7` as its child `HParseResult.bit_length`:

```text
0 - 8 modulo 2^64 = 18446744073709551608
```

An ordinary `h_action` around the seek can observe that value. The
[reproducer below](#seeking-reproducer) captures it before the enclosing
`h_right(h_skip(8), ...)` creates its own result. That outer parse starts and
ends at bit 0 and reports length zero. Inspecting only the outermost result
would therefore miss the wrapped child length.

This happens on a one-byte input, independently of C-001's large-position
limit. The subtraction is defined unsigned wraparound in C, but the resulting
value is not a meaningful nonnegative amount of input consumed by the seek.
[`h_butnot`](../src/parsers/butnot.c) and
[`h_difference`](../src/parsers/difference.c) compare this field through
[`token_length`](../src/parsers/parser_internal.h), so their treatment of
backward-seeking children also needs an explicit contract.

Follow-up: decide what result length means for grammars that can revisit input.
Possible quantities such as signed net displacement, an endpoint interval, and
the amount of input inspected are different. Choose a representation and
combinator rules before changing the subtraction. Add tests for backward
children, seek-and-return grammars, callbacks observing child results, and match
comparisons involving forward, empty, and backward results. Merely clamping a
negative displacement to zero would also choose semantics and needs review.

## Seeking reproducer

Save this program as `/tmp/hammer-seek-quirks.c`. It uses the public C API and
the default packrat backend; no Rust or extraction tools are required.

```c
#include <sys/types.h>
#include "hammer.h"
#include <inttypes.h>
#include <stdio.h>

static HParsedToken *record_length(const HParseResult *result, void *context) {
    *(size_t *)context = result->bit_length;
    return (HParsedToken *)result->ast;
}

int main(void) {
    size_t child_bits = 0;
    HParserGraph *graph = h_parser_graph_begin();
    HParser *past_end = h_seek(1, SEEK_SET);
    HParser *backward = h_right(
        h_skip(8), h_action(h_seek(0, SEEK_SET), record_length, &child_bits));
    h_parser_graph_end(graph);

    HParseResult *result = h_parse(past_end, (const uint8_t *)"", 0);
    printf("EOF seek: success=%d", result != NULL);
    if (result) {
        printf(" position=%" PRIu64, result->ast->token_data.uint);
        h_parse_result_free(result);
    }
    putchar('\n');

    result = h_parse(backward, (const uint8_t *)"a", 1);
    printf("Backward seek: success=%d child_bits=%zu", result != NULL, child_bits);
    if (result) {
        printf(" outer_bits=%zu", result->bit_length);
        h_parse_result_free(result);
    }
    putchar('\n');
    h_parser_graph_free(graph);
    return 0;
}
```

With the standard Linux build, run from the repository root:

```sh
scons --no-tests
cc -std=gnu99 -O2 -Isrc /tmp/hammer-seek-quirks.c build/opt/src/libhammer.a -pthread -lm -lrt -o /tmp/hammer-seek-quirks
/tmp/hammer-seek-quirks
```

Observed output with 64-bit `size_t`:

```text
EOF seek: success=1 position=1
Backward seek: success=1 child_bits=18446744073709551608 outer_bits=0
```

The broader characterization is retained in the
[seeking probe](../rusthammer/probes/seeking/README.md), with its C adapter in
[`reference.c`](../rusthammer/probes/seeking/reference.c). To run that corpus
alongside its native Rust checks, without Aeneas or Lean:

```sh
cd rusthammer
python3 tools/check_seeking.py --native-only --c
```

The [RustHammer seeking proposal](../plans/rusthammer-seeking.md) describes its
chosen behavior separately. Its endpoint-based contracts do not settle the C
API's backward-length semantics.
