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

int compare_signed(unsigned width, const uint8_t *input, size_t input_len,
                   unsigned offset, size_t *position, int64_t *value) {
    HParser *atom = h_bits(width, true);
    assert(atom != NULL);
    HParser *skip = offset ? h_bits(offset, false) : NULL;
    HParser *parser = skip ? h_right(skip, atom) : atom;
    HParseResult *result = h_parse(parser, input, input_len);
    int accepted = result != NULL;
    if (accepted) {
        assert(result->ast != NULL);
        assert(result->ast->token_type == TT_SINT);
        *position = result->bit_length;
        *value = result->ast->token_data.sint;
        h_parse_result_free(result);
    }
    if (skip) {
        h_parser_free(parser);
        h_parser_free(skip);
    }
    h_parser_free(atom);
    return accepted;
}

int compare_integer(unsigned width, unsigned signedp,
                    const uint8_t *input, size_t input_len, unsigned offset,
                    size_t *position, uint64_t *unsigned_value, int64_t *signed_value) {
    HParser *atom = NULL;
    switch (width) {
    case 8: atom = signedp ? h_int8() : h_uint8(); break;
    case 16: atom = signedp ? h_int16() : h_uint16(); break;
    case 32: atom = signedp ? h_int32() : h_uint32(); break;
    case 64: atom = signedp ? h_int64() : h_uint64(); break;
    default: assert(0 && "unsupported integer width");
    }
    assert(atom != NULL);
    HParser *skip = offset ? h_bits(offset, false) : NULL;
    HParser *parser = skip ? h_right(skip, atom) : atom;
    HParseResult *result = h_parse(parser, input, input_len);
    int accepted = result != NULL;
    if (accepted) {
        assert(result->ast != NULL);
        *position = result->bit_length;
        if (signedp) {
            assert(result->ast->token_type == TT_SINT);
            *signed_value = result->ast->token_data.sint;
        } else {
            assert(result->ast->token_type == TT_UINT);
            *unsigned_value = result->ast->token_data.uint;
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
