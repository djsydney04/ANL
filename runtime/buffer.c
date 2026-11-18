#include "runtime.h"
#include <stdlib.h>
#ifdef ANL_MEMORY_EVIDENCE
#include <stdio.h>
#include <inttypes.h>
#include <string.h>
typedef struct { unsigned kind; uint64_t ordinal, function, site, length; unsigned success; } anl_event;
#include "evidence.h"
typedef struct { int64_t *base; anl_event event; } anl_owner;
static FILE *anl_trace;
static size_t anl_bytes, anl_events, anl_owners;
static uint64_t anl_requests, anl_empties;
static anl_owner anl_live[65536];
static _Noreturn void anl_evidence_fail(const char *reason);
static void anl_write(const char *text) {
    size_t n = strlen(text);
    if (!anl_trace || n > 8388608U - anl_bytes || fwrite(text, 1, n, anl_trace) != n) {
        (void)fputs("anl: evidence recording failed\n", stderr);
        exit(4);
    }
    anl_bytes += n;
}
static _Noreturn void anl_evidence_fail(const char *reason) {
    if (anl_trace) {
        anl_write("],\"completion\":{\"kind\":\"infrastructure\",\"reason\":\"");
        /* Reasons are fixed ASCII literals, never source or path text. */
        anl_write(reason);
        anl_write("\"}}\n");
        (void)fclose(anl_trace);
        anl_trace = NULL;
    }
    (void)fprintf(stderr, "anl: evidence failure: %s\n", reason);
    exit(4);
}
static void anl_room(void) {
    if (!anl_trace || anl_events >= 65536U) anl_evidence_fail("trace event bound exceeded");
}
static int anl_equal(anl_event a, anl_event b) {
    return a.kind == b.kind && a.ordinal == b.ordinal && a.function == b.function && a.site == b.site && a.length == b.length && a.success == b.success;
}
static void anl_event_record(anl_event e) {
    char text[256]; int n;
    anl_room();
    if (anl_replay && (anl_events >= anl_expected_count || !anl_equal(e, anl_expected[anl_events]))) anl_evidence_fail("invalid replay event");
    if (e.kind == 1) {
        n = snprintf(text, sizeof(text), "{\"kind\":\"request\",\"request\":\"%" PRIu64 "\",\"site\":{\"function\":%" PRIu64 ",\"heap\":%" PRIu64 "},\"length\":\"%" PRIu64 "\",\"response\":\"%s\"}", e.ordinal, e.function, e.site, e.length, e.success ? "success" : "refused");
    } else {
        const char *kind = e.kind == 2 ? "release" : (e.kind == 3 ? "empty_open" : "empty_close");
        const char *id = e.kind == 2 ? "request" : "empty";
        n = snprintf(text, sizeof(text), "{\"kind\":\"%s\",\"%s\":\"%" PRIu64 "\",\"site\":{\"function\":%" PRIu64 ",\"heap\":%" PRIu64 "}}", kind, id, e.ordinal, e.function, e.site);
    }
    if (n < 0 || (size_t)n >= sizeof(text)) anl_evidence_fail("event formatting failed");
    if (anl_events) anl_write(",");
    anl_write(text); anl_events++;
}
void anl_memory_begin(void) {
    anl_trace = fopen((const char *)anl_destination, "wbx");
    if (!anl_trace) anl_evidence_fail("cannot exclusively create trace");
    anl_write(anl_prefix);
}
static void anl_end(const char *completion, unsigned kind, int64_t value, unsigned trap) {
    if (anl_replay && (anl_events != anl_expected_count || anl_completion_kind != kind || (kind == 1 && anl_completion_value != value) || (kind == 2 && anl_completion_trap != trap))) anl_evidence_fail("invalid replay completion");
    anl_write("],\"completion\":"); anl_write(completion); anl_write("}\n");
    if (fclose(anl_trace) != 0) { anl_trace = NULL; anl_evidence_fail("cannot finalize trace"); }
    anl_trace = NULL;
}
void anl_memory_value(int64_t value) {
    char text[128];
    int n = snprintf(text, sizeof(text), "{\"kind\":\"value\",\"type\":\"i64\",\"value\":\"%" PRId64 "\"}", value);
    if (n < 0 || (size_t)n >= sizeof(text) || anl_owners != 0) anl_evidence_fail("invalid normal completion");
    anl_end(text, 1, value, 0);
}
void anl_memory_trap(const char *tag) {
    unsigned trap = !strcmp(tag, "arithmetic_overflow") ? 1U : !strcmp(tag, "division_by_zero") ? 2U : !strcmp(tag, "invalid_length") ? 3U : !strcmp(tag, "index_out_of_bounds") ? 4U : 0U;
#ifdef ANL_WORDS_EVIDENCE
    if (!strcmp(tag, "invalid_shift")) trap = 5U;
#endif
    char text[128];
    int n = snprintf(text, sizeof(text), "{\"kind\":\"trap\",\"trap\":\"%s\"}", tag);
    if (trap == 0 || n < 0 || (size_t)n >= sizeof(text)) anl_evidence_fail("invalid trap completion");
    anl_end(text, 2, 0, trap);
}
void anl_memory_empty_open(uint64_t function, uint64_t site) {
    anl_event e = {3, anl_empties, function, site, 0, 0};
    anl_room(); if (anl_owners >= 65536U) anl_evidence_fail("owner metadata bound exceeded");
    anl_event_record(e); anl_empties++;
    anl_live[anl_owners++] = (anl_owner){NULL, e};
}
void anl_memory_empty_close(uint64_t function, uint64_t site) {
    if (anl_owners == 0) anl_evidence_fail("missing empty owner");
    anl_event e = anl_live[anl_owners-1].event;
    if (e.kind != 3 || e.function != function || e.site != site) anl_evidence_fail("empty owner mismatch");
    e.kind = 4; anl_event_record(e); anl_owners--;
}
#endif
int64_t *anl_memory_request(int64_t cells, uint64_t function, uint64_t site) {
    if (cells <= 0 || (uint64_t)cells > ANL_MAX_CELLS || (uint64_t)cells > SIZE_MAX / sizeof(int64_t) || (uint64_t)cells > PTRDIFF_MAX / sizeof(int64_t)) exit(4);
    int64_t *base = NULL;
#ifdef ANL_MEMORY_EVIDENCE
    anl_event e = {1, anl_requests, function, site, (uint64_t)cells, 0};
    int response = -1;
    anl_room(); if (anl_owners >= 65536U) anl_evidence_fail("owner metadata bound exceeded");
    if (anl_replay) {
        if (anl_events >= anl_expected_count) anl_evidence_fail("missing replay request");
        anl_event expected = anl_expected[anl_events];
        if (expected.kind != 1 || expected.ordinal != e.ordinal || expected.function != function || expected.site != site || expected.length != (uint64_t)cells) anl_evidence_fail("invalid replay request");
        response = (int)expected.success;
    }
    if (response != 0)
#endif
    base = malloc((size_t)cells * sizeof(int64_t));
#ifdef ANL_MEMORY_EVIDENCE
    if (response == 1 && !base) anl_evidence_fail("forced allocation success unavailable");
    e.success = base != NULL; anl_event_record(e); anl_requests++;
    if (base) anl_live[anl_owners++] = (anl_owner){base, e};
#else
    (void)function; (void)site;
#endif
    return base;
}
void anl_memory_release(int64_t *base, uint64_t function, uint64_t site) {
#ifdef ANL_MEMORY_EVIDENCE
    if (anl_owners == 0) anl_evidence_fail("missing positive owner");
    anl_owner owner = anl_live[anl_owners-1];
    if (owner.base != base || owner.event.kind != 1 || owner.event.function != function || owner.event.site != site) anl_evidence_fail("positive owner mismatch");
    owner.event.kind = 2; owner.event.length = 0; owner.event.success = 0;
    anl_event_record(owner.event); anl_owners--;
#else
    (void)function; (void)site;
#endif
    free(base);
}
