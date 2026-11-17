#include "common.h"
#include "buffer.h"
#include <stddef.h>
_Static_assert(CHAR_BIT == 8 && sizeof(int64_t) == 8 && _Alignof(int64_t) == 8, "i64 layout");
_Static_assert(sizeof(size_t) == 8 && sizeof(ptrdiff_t) == 8, "64-bit allocation profile");
Buffer buffer_open(int64_t length, int64_t initial) {
    if (length < 0) trap("invalid_length");
    if ((uint64_t)length > SIZE_MAX / sizeof(int64_t) ||
        (uint64_t)length > PTRDIFF_MAX / sizeof(int64_t)) {
        (void)fputs("comparison: unrepresentable allocation\n", stderr);
        exit(4);
    }
    Buffer buffer = {NULL, length};
    if (length) {
        buffer.data = malloc((size_t)length * sizeof(int64_t));
        if (!buffer.data) {
            (void)fputs("comparison: allocation failure\n", stderr);
            exit(4);
        }
        for (int64_t i = 0; i < length; ++i) buffer.data[i] = initial;
    }
    return buffer;
}
int64_t *buffer_index(Buffer *buffer, int64_t index) {
    if (index < 0 || index >= buffer->length) trap("index_out_of_bounds");
    return &buffer->data[(size_t)index];
}
int64_t buffer_read(Buffer *buffer, int64_t index) { return *buffer_index(buffer, index); }
void buffer_close(Buffer *buffer) {
    free(buffer->data);
    buffer->data = NULL;
    buffer->length = 0;
}
