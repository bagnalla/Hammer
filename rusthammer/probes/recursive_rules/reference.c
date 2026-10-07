/* C Hammer oracle for the private recursive-rule fixtures. */
#include "hammer.h"

int recursive_probe(unsigned mode, const uint8_t *input, size_t size, size_t *bits) {
    unsigned complete = mode / 16;
    mode %= 16;
    HParser *a = h_indirect();
    HParser *token = h_ch('a');
    HParser *empty = h_epsilon_p();
    HParser *recursive = a;
    if (mode == 1 || mode == 6 || mode == 7) {
        HParser *b = h_indirect();
        h_bind_indirect(b, mode == 7 ? h_with_endianness(BYTE_BIG_ENDIAN | BIT_BIG_ENDIAN, a) : a);
        recursive = mode == 7 ? h_with_endianness(BYTE_LITTLE_ENDIAN | BIT_BIG_ENDIAN, b) : b;
    }
    HParser *body;
    if (mode == 2)
        body = h_choice(h_sequence(token, a, NULL), empty, NULL);
    else if (mode == 4)
        body = a;
    else if (mode == 5)
        body = h_choice(a, empty, NULL);
    else
        body = h_choice(h_sequence(recursive, token, NULL), mode == 3 ? empty : token, NULL);
    h_bind_indirect(a, body);
    HParser *root = complete ? h_left(a, h_end_p()) : a;
    HParseResult *result = h_parse(root, input, size);
    int success = result != NULL;
    *bits = success ? result->bit_length : 0;
    if (result) h_parse_result_free(result);
    /* All allocations in these tiny fixtures are process-local. The oracle
       process exits after its corpus; unused alternatives are not roots. */
    return success;
}
