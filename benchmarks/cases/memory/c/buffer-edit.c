#include "common.h"
#include "buffer.h"
static void edit_all(Buffer *b, int64_t rounds) {
    int64_t r = 0;
    while (r < rounds) {
        int64_t i = 0;
        while (i < b->length) {
            int64_t *target = buffer_index(b, i);
            int64_t value = add(add(buffer_read(b, i), i), 1);
            *target = value;
            i = add(i, 1);
        }
        r = add(r, 1);
    }
}
static int64_t scan(Buffer *b) {
    int64_t total = 0, i = 0;
    while (i < b->length) {
        total = add(total, buffer_read(b, i));
        i = add(i, 1);
    }
    return total;
}
int main(void) {
    Buffer b = buffer_open(4096, 3);
    edit_all(&b, 64);
    int64_t result = scan(&b);
    buffer_close(&b);
    return output(result);
}
