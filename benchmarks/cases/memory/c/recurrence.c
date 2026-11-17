#include "common.h"
static int64_t park_miller(int64_t steps) {
    int64_t x = 1, i = 0;
    while (i < steps) {
        x = rem(mul(x, 48271), 2147483647);
        i = add(i, 1);
    }
    return x;
}
int main(void) { return output(park_miller(1000000)); }
