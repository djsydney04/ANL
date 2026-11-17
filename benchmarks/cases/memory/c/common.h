#ifndef COMPARISON_COMMON_H
#define COMPARISON_COMMON_H
#include <inttypes.h>
#include <limits.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
static _Noreturn void trap(const char *tag) {
    (void)fprintf(stderr, "trap: %s\n", tag);
    exit(2);
}
static inline int64_t add(int64_t a, int64_t b) {
    int64_t value;
    if (__builtin_add_overflow(a, b, &value)) trap("arithmetic_overflow");
    return value;
}
static inline int64_t mul(int64_t a, int64_t b) {
    int64_t value;
    if (__builtin_mul_overflow(a, b, &value)) trap("arithmetic_overflow");
    return value;
}
static inline int64_t rem(int64_t a, int64_t b) {
    if (!b) trap("division_by_zero");
    if (a == INT64_MIN && b == -1) trap("arithmetic_overflow");
    return a % b;
}
static inline int output(int64_t value) {
#ifdef SIGPIPE
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) return 4;
#endif
    if (printf("%" PRId64 "\n", value) < 0 || fflush(stdout) == EOF) {
        (void)fputs("comparison: cannot write stdout\n", stderr);
        return 4;
    }
    return 0;
}
#endif
