/* erdos982_lrat_trim_bin: trim a BINARY LRAT proof (as CaDiCaL writes with --binary=true: 'a' id lits 0 hints 0,
 * 'd' ids 0, every number a 7-bit varint of 2|x| + sign) to the addition steps reachable backwards from the first
 * empty clause, and write it as TEXT LRAT. Same output conventions as erdos982_lrat_trim.c (the text-input trimmer):
 * kept lemmas are renumbered consecutively from m + 1 (m = number of input clauses; Lean's checker appends each added
 * clause and ignores the given id, so ids must be dense), original deletions are dropped, and a kept lemma is
 * deleted right after the last kept step that uses it as a hint. The input is memory-mapped; per step it keeps only
 * an offset, the id and a few 32-bit indices, so memory stays small for multi-GB proofs.
 * Usage: erdos982_lrat_trim_bin in.lratb out.lrat m
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>

static const unsigned char *B; static size_t N;

static inline uint64_t rd(size_t *q) {
    uint64_t x = 0; int sh = 0;
    for (;;) {
        if (*q >= N) { fprintf(stderr, "truncated varint at %zu\n", *q); exit(2); }
        unsigned char c = B[(*q)++];
        x |= (uint64_t)(c & 0x7f) << sh;
        if (!(c & 0x80)) return x;
        sh += 7; if (sh > 63) { fprintf(stderr, "varint too long\n"); exit(2); }
    }
}
static inline int64_t dec(uint64_t x) { return (x & 1) ? -(int64_t)(x >> 1) : (int64_t)(x >> 1); }

int main(int argc, char **argv) {
    if (argc != 4) { fprintf(stderr, "usage: %s in.lratb out.lrat m\n", argv[0]); return 2; }
    int64_t m = strtoll(argv[3], NULL, 10);
    int fd = open(argv[1], O_RDONLY); if (fd < 0) { perror("in"); return 2; }
    struct stat sb; fstat(fd, &sb); N = sb.st_size;
    B = mmap(NULL, N, PROT_READ, MAP_PRIVATE, fd, 0); if (B == MAP_FAILED) { perror("mmap"); return 2; }
    /* pass 1: offsets of addition steps (offset of the first literal), their ids */
    size_t cs = 1 << 22, ns = 0;
    uint64_t *off = malloc(cs * sizeof(uint64_t)); int64_t *ids = malloc(cs * sizeof(int64_t));
    int64_t maxid = 0, prev = m; int64_t last = -1; size_t q = 0; size_t ndel = 0;
    while (q < N) {
        unsigned char t = B[q++];
        if (t == 'a') {
            int64_t id = dec(rd(&q));
            if (id <= prev) { fprintf(stderr, "ids not increasing at %lld\n", (long long)id); return 2; }
            prev = id;
            if (ns == cs) { cs *= 2; off = realloc(off, cs * sizeof(uint64_t)); ids = realloc(ids, cs * sizeof(int64_t)); if (!off || !ids) { fprintf(stderr, "oom\n"); return 2; } }
            off[ns] = q; ids[ns] = id;
            size_t nl = 0; while (rd(&q) != 0) nl++;
            uint64_t h; while ((h = rd(&q)) != 0) { if (h & 1) { fprintf(stderr, "RAT hint not supported\n"); return 2; } }
            if (nl == 0 && last < 0) last = ns;
            if (id > maxid) maxid = id;
            ns++;
            if (last >= 0) break;            /* nothing after the first empty clause is needed */
        } else if (t == 'd') {
            while (rd(&q) != 0) ; ndel++;
        } else { fprintf(stderr, "bad step byte %d at %zu\n", t, q - 1); return 2; }
    }
    if (last < 0) { fprintf(stderr, "no empty clause (steps %zu)\n", ns); return 1; }
    fprintf(stderr, "pass 1: %zu addition steps up to the empty clause, %zu deletion lines, max id %lld\n", ns, ndel, (long long)maxid);
    int32_t *pos = malloc((size_t)(maxid - m + 1) * sizeof(int32_t));   /* index of the step with id m + k */
    for (int64_t i = 0; i <= maxid - m; i++) pos[i] = -1;
    for (size_t i = 0; i < ns; i++) pos[ids[i] - m] = (int32_t)i;
    int64_t lastid = ids[last];
    free(ids);
    /* pass 2: backward marking */
    char *mark = calloc(ns, 1);
    int32_t *lastuse = malloc(ns * sizeof(int32_t));
    for (size_t i = 0; i < ns; i++) lastuse[i] = -1;
    mark[last] = 1;
    for (int64_t i = last; i >= 0; i--) {
        if (!mark[i]) continue;
        size_t r = off[i]; while (rd(&r) != 0) ;
        uint64_t h;
        while ((h = rd(&r)) != 0) {
            int64_t hid = dec(h);
            if (hid > m) {
                if (hid > maxid || pos[hid - m] < 0) { fprintf(stderr, "hint %lld to a missing step\n", (long long)hid); return 3; }
                int32_t j = pos[hid - m];
                if (j >= i) { fprintf(stderr, "hint %lld not earlier\n", (long long)hid); return 3; }
                mark[j] = 1; if (lastuse[j] < i) lastuse[j] = (int32_t)i;
            } else if (hid < 1) { fprintf(stderr, "bad hint %lld\n", (long long)hid); return 3; }
        }
    }
    int32_t *dhead = malloc(ns * sizeof(int32_t)), *dnext = malloc(ns * sizeof(int32_t));
    for (size_t i = 0; i < ns; i++) dhead[i] = -1;
    for (size_t j = 0; j < ns; j++) if (mark[j] && lastuse[j] >= 0) { dnext[j] = dhead[lastuse[j]]; dhead[lastuse[j]] = (int32_t)j; }
    free(lastuse);
    int64_t *nid = malloc(ns * sizeof(int64_t));
    int64_t next = m;
    for (int64_t i = 0; i <= last; i++) nid[i] = mark[i] ? ++next : -1;
    /* pass 3: write text */
    FILE *o = fopen(argv[2], "w"); if (!o) { perror("out"); return 2; }
    static char obuf[1 << 22]; setvbuf(o, obuf, _IOFBF, sizeof obuf);
    size_t kept = 0, nlits = 0, nh = 0;
    for (int64_t i = 0; i <= last; i++) {
        if (!mark[i]) continue;
        kept++;
        fprintf(o, "%lld", (long long)nid[i]);
        size_t r = off[i]; uint64_t x;
        while ((x = rd(&r)) != 0) { fprintf(o, " %lld", (long long)dec(x)); nlits++; }
        fputs(" 0", o);
        while ((x = rd(&r)) != 0) {
            int64_t h = dec(x);
            int64_t hn = (h > m) ? nid[pos[h - m]] : h;
            if (hn < 0) { fprintf(stderr, "internal: hint to dropped step\n"); return 3; }
            fprintf(o, " %lld", (long long)hn); nh++;
        }
        fputs(" 0\n", o);
        if (i != last && dhead[i] >= 0) {
            fprintf(o, "%lld d", (long long)nid[i]);
            for (int32_t j = dhead[i]; j >= 0; j = dnext[j]) fprintf(o, " %lld", (long long)nid[j]);
            fputs(" 0\n", o);
        }
    }
    fclose(o);
    fprintf(stderr, "steps %zu, kept %zu (empty clause id %lld -> %lld), literals %zu, hints %zu\n", ns, kept,
            (long long)lastid, (long long)nid[last], nlits, nh);
    return 0;
}
