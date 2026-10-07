/* C Hammer complete-input oracle, including values in declaration order. */
#include "hammer.h"
#include <assert.h>
#include <string.h>

int permutation_probe(unsigned a, unsigned b, unsigned c, unsigned optional,
                      unsigned offset, const uint8_t *input, size_t size,
                      size_t *bits, unsigned *present) {
    static const char *patterns[] = {"", "a", "b", "aa", "ab", "ba"};
    unsigned indices[] = {a, b, c};
    HParserGraph *graph = h_parser_graph_begin();
    HParser *items[3];
    for (unsigned i = 0; i < 3; ++i) {
        assert(indices[i] < 6);
        const char *pattern = patterns[indices[i]];
        items[i] = h_token((const uint8_t *)pattern, strlen(pattern));
        if (optional & (1u << i))
            items[i] = h_optional(items[i]);
    }
    HParser *parser = h_right(h_skip(offset), h_permutation(items[0], items[1], items[2], NULL));
    h_parser_graph_end(graph);
    HParseResult *result = h_parse(parser, input, size);
    int success = result != NULL;
    *bits = 0;
    *present = 0;
    if (result) {
        *bits = result->bit_length;
        assert(result->ast && result->ast->token_type == TT_SEQUENCE);
        HCountedArray *values = result->ast->token_data.seq;
        assert(values->used == 3);
        for (unsigned i = 0; i < 3; ++i) {
            HParsedToken *value = values->elements[i];
            assert(value);
            if (value->token_type == TT_NONE) {
                assert(optional & (1u << i));
            } else {
                const char *expected = patterns[indices[i]];
                assert(value->token_type == TT_BYTES);
                assert(value->token_data.bytes.len == strlen(expected));
                assert(memcmp(value->token_data.bytes.token, expected, strlen(expected)) == 0);
                *present |= 1u << i;
            }
        }
        h_parse_result_free(result);
    }
    h_parser_graph_free(graph);
    return success;
}
