/* Optional direct-backend comparison adapter; no Rust FFI in the library. */
#include <sys/types.h>
#include "hammer.h"
#include <assert.h>

typedef struct {
    unsigned kind, width;
    uint64_t expected;
} Atom;

typedef struct {
    HParser *nodes[32];
    size_t count;
} Grammar;

static HParser *keep(Grammar *g, HParser *parser) {
    assert(parser != NULL && g->count < 32);
    g->nodes[g->count++] = parser;
    return parser;
}

static bool literal(HParseResult *result, void *expected) {
    assert(result->ast != NULL && result->ast->token_type == TT_UINT);
    return result->ast->token_data.uint == *(uint64_t *)expected;
}

static HParser *atom(Grammar *g, Atom *config) {
    if (config->kind == 1) return keep(g, h_skip(config->width));
    if (config->kind == 5) return keep(g, h_epsilon_p());
    if (config->kind == 6) return keep(g, h_nothing_p());
    HParser *bits = keep(g, h_bits(config->width, false));
    HParser *value = keep(g, h_attr_bool(bits, literal, &config->expected));
    if (config->kind == 2) return keep(g, h_and(value));
    if (config->kind == 3) {
        HParser *skip = keep(g, h_skip(3));
        return keep(g, h_right(skip, value));
    }
    if (config->kind == 4) {
        HParser *skip = keep(g, h_skip(3));
        return keep(g, h_left(value, skip));
    }
    assert(config->kind == 0);
    return value;
}

int compare_matches(unsigned operation,
                    unsigned first_kind, unsigned first_width, uint64_t first_expected,
                    unsigned second_kind, unsigned second_width, uint64_t second_expected,
                    const uint8_t *input, size_t input_len, unsigned offset,
                    size_t *position, uint64_t *value) {
    Grammar g = { .count = 0 };
    Atom first = { first_kind, first_width, first_expected };
    Atom second = { second_kind, second_width, second_expected };
    HParser *p = atom(&g, &first), *q = atom(&g, &second);
    HParser *parser = keep(&g, operation == 0 ? h_butnot(p, q)
                             : operation == 1 ? h_difference(p, q) : h_xor(p, q));
    if (offset) {
        HParser *leading = keep(&g, h_skip(offset));
        parser = keep(&g, h_right(leading, parser));
    }
    HParseResult *result = h_parse(parser, input, input_len);
    int accepted = result != NULL;
    if (accepted) {
        *position = result->bit_length;
        if (result->ast) {
            assert(result->ast->token_type == TT_UINT);
            *value = result->ast->token_data.uint;
        } else {
            *value = 0;
        }
        h_parse_result_free(result);
    }
    while (g.count) h_parser_free(g.nodes[--g.count]);
    return accepted;
}
