#include "common.h"
#include "buffer.h"
static int64_t scan(Buffer *b, int64_t rounds) {
    int64_t total = 0, r = 0;
    while (r < rounds) {
        int64_t i = 0;
        while (i < b->length) {
            total = add(total, buffer_read(b, i));
            i = add(i, 1);
        }
        r = add(r, 1);
    }
    return total;
}
int main(void) {
    Buffer b = buffer_open(16384, 7);
    int64_t result = scan(&b, 64);
    buffer_close(&b);
    return output(result);
}
