#ifndef COMPARISON_BUFFER_H
#define COMPARISON_BUFFER_H
#include <stdint.h>
typedef struct { int64_t *data; int64_t length; } Buffer;
Buffer buffer_open(int64_t length, int64_t initial);
int64_t *buffer_index(Buffer *buffer, int64_t index);
int64_t buffer_read(Buffer *buffer, int64_t index);
void buffer_close(Buffer *buffer);
#endif
