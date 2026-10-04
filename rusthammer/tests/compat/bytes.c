/* Optional direct-backend comparison adapter; no Rust FFI in the library. */
#include <sys/types.h>
#include "hammer.h"
#include <assert.h>
#include <string.h>

int compare_bytes(unsigned byte_reader, const uint8_t *pattern, size_t pattern_len,
                  const uint8_t *input, size_t input_len, unsigned offset,
                  size_t *position, unsigned *value) {
    HParser *atom = byte_reader ? h_uint8() : h_token(pattern, pattern_len);
    HParser *skip = offset ? h_bits(offset, false) : NULL;
    HParser *parser = skip ? h_right(skip, atom) : atom;
    HParseResult *result = h_parse(parser, input, input_len);
    int accepted = result != NULL;
    if (accepted) {
        assert(result->ast != NULL);
        *position = result->bit_length;
        if (byte_reader) {
            assert(result->ast->token_type == TT_UINT);
            *value = (unsigned)result->ast->token_data.uint;
        } else {
            assert(result->ast->token_type == TT_BYTES);
            assert(result->ast->token_data.bytes.len == pattern_len);
            assert(memcmp(result->ast->token_data.bytes.token, pattern, pattern_len) == 0);
            *value = 0;
        }
        h_parse_result_free(result);
    }
    if (skip) {
        h_parser_free(parser);
        h_parser_free(skip);
    }
    h_parser_free(atom);
    return accepted;
}
