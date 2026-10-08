/* Exercise the public C parser, including the packrat result-length machinery. */
#include "hammer.h"
#include <assert.h>
#include <stdio.h>

static HParsedToken *record_length(const HParseResult *result, void *environment) {
    *(size_t *)environment = result->bit_length;
    return (HParsedToken *)result->ast;
}

int seek_probe(unsigned origin, ssize_t offset, size_t start,
               const uint8_t *input, size_t size, size_t *position, size_t *length) {
    assert(origin < 3);
    int origins[] = {SEEK_SET, SEEK_CUR, SEEK_END};
    HParserGraph *graph = h_parser_graph_begin();
    HParser *parser = h_right(h_skip(start),
                             h_action(h_seek(offset, origins[origin]), record_length, length));
    h_parser_graph_end(graph);
    *position = *length = 0;
    HParseResult *result = h_parse(parser, input, size);
    int success = result != NULL;
    if (result) {
        assert(result->ast && result->ast->token_type == TT_UINT);
        *position = result->ast->token_data.uint;
        h_parse_result_free(result);
    }
    h_parser_graph_free(graph);
    return success;
}
