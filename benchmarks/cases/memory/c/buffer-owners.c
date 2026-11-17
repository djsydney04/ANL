#include "common.h"
#include "buffer.h"
static int64_t one(int64_t seed) {
    Buffer b = buffer_open(16, seed);
    int64_t first = buffer_read(&b, 0);
    int64_t last = buffer_read(&b, 15);
    int64_t result = add(add(first, last), b.length);
    buffer_close(&b);
    return result;
}
int main(void) {
    int64_t total = 0, i = 0;
    while (i < 16384) {
        total = add(total, one(rem(i, 97)));
        i = add(i, 1);
    }
    return output(total);
}
