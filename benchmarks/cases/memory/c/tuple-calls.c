#include "common.h"
typedef struct { int64_t first, second; } Pair;
static Pair advance(Pair p) { return (Pair){add(p.first, 1), add(p.second, 2)}; }
static Pair identity(Pair p) { return p; }
int main(void) {
    Pair p = {0, 1};
    int64_t i = 0, checksum = 0;
    while (i < 200000) {
        Pair old = p;
        Pair mirror = identity(old);
        p = advance(p);
        if (mirror.first == old.first && mirror.second == old.second && add(old.first, 1) == p.first)
            checksum = add(checksum, old.first);
        else checksum = -1000000000000;
        i = add(i, 1);
    }
    return output(add(add(p.first, p.second), checksum));
}
