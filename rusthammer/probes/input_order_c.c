/* Adapter for the optional, direct-backend C comparison. */
#include <sys/types.h>
#include "hammer.h"
#include "internal.h"

void order_read(const uint8_t *input, size_t length, size_t byte,
                uint8_t high, uint8_t low, uint8_t flags, size_t width,
                int skip, uint64_t out[5]) {
    HInputStream stream = {
        .input = input, .length = length, .index = byte,
        .bit_offset = (flags & BIT_BIG_ENDIAN) ? high : low,
        .margin = (flags & BIT_BIG_ENDIAN) ? low : high,
        .endianness = (char)flags, .last_chunk = true
    };
    uint64_t value = 0;
    if (skip)
        h_skip_bits(&stream, width);
    else
        value = (uint64_t)h_read_bits(&stream, width, false);
    out[0] = !stream.overrun;
    out[1] = stream.index;
    out[2] = (flags & BIT_BIG_ENDIAN) ? stream.bit_offset : stream.margin;
    out[3] = (flags & BIT_BIG_ENDIAN) ? stream.margin : stream.bit_offset;
    out[4] = value;
}

void order_nested(const uint8_t *input, size_t length, uint8_t base,
                  uint8_t outer, uint8_t inner, const uint8_t widths[5],
                  uint64_t out[7]) {
    HParser *p[11];
    for (size_t i = 0; i < 5; ++i)
        p[i] = h_bits(widths[i], false);
    p[5] = h_with_endianness((char)inner, p[2]);
    p[6] = h_sequence(p[1], p[5], p[3], NULL);
    p[7] = h_with_endianness((char)outer, p[6]);
    p[8] = h_tell();
    p[9] = h_sequence(p[0], p[7], p[4], p[8], NULL);
    p[10] = h_with_endianness((char)base, p[9]);
    HParseResult *result = h_parse(p[10], input, length);
    out[0] = result != NULL;
    if (result != NULL) {
        HParsedToken **seq = result->ast->token_data.seq->elements;
        HParsedToken **middle = seq[1]->token_data.seq->elements;
        out[1] = seq[3]->token_data.uint;
        out[2] = seq[0]->token_data.uint;
        out[3] = middle[0]->token_data.uint;
        out[4] = middle[1]->token_data.uint;
        out[5] = middle[2]->token_data.uint;
        out[6] = seq[2]->token_data.uint;
        h_parse_result_free(result);
    }
    for (size_t i = 11; i > 0; --i)
        h_parser_free(p[i - 1]);
}
