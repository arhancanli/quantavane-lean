/* erdos982_lrat_trim: trim a text LRAT proof (RUP steps only, as CaDiCaL writes) to the steps reachable backwards
 * from the empty clause, keeping original clause ids (still increasing), and re-insert deletions: a kept lemma is
 * deleted right after the last kept step that uses it as a hint. Kept lemmas are renumbered consecutively from
 * m + 1 (m = number of input clauses): Lean's checker appends each added clause and ignores the given id, so ids
 * must be dense.
 * Usage: erdos982_lrat_trim in.lrat out.lrat m
 * Input lines:  "<id> <lits...> 0 <hints...> 0"   or   "<id> d <ids...> 0".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { int64_t id; int64_t lit_off, nlits, hint_off, nhints; } Step;

static int64_t *buf; static size_t blen = 0, bcap = 0;
static void push(int64_t x) { if (blen == bcap) { bcap = bcap ? 2 * bcap : (1 << 24); buf = realloc(buf, bcap * sizeof(int64_t)); if (!buf) { fprintf(stderr, "oom\n"); exit(2); } } buf[blen++] = x; }

int main(int argc, char **argv) {
    if (argc != 4) { fprintf(stderr, "usage: %s in.lrat out.lrat m\n", argv[0]); return 2; }
    int64_t m = strtoll(argv[3], NULL, 10);
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("in"); return 2; }
    Step *st = NULL; size_t ns = 0, cs = 0;
    char *line = NULL; size_t lcap = 0; ssize_t len;
    int64_t maxid = 0;
    while ((len = getline(&line, &lcap, f)) > 0) {
        char *p = line, *e;
        int64_t id = strtoll(p, &e, 10); if (e == p) continue; p = e;
        while (*p == ' ') p++;
        if (*p == 'd') continue;                       /* original deletions are dropped */
        Step s; s.id = id; s.lit_off = blen; s.nlits = 0;
        for (;;) { int64_t x = strtoll(p, &e, 10); if (e == p) { fprintf(stderr, "parse error\n"); return 2; } p = e; if (x == 0) break; push(x); s.nlits++; }
        s.hint_off = blen; s.nhints = 0;
        for (;;) { int64_t x = strtoll(p, &e, 10); if (e == p) { fprintf(stderr, "parse error (hints)\n"); return 2; } p = e; if (x == 0) break; if (x < 0) { fprintf(stderr, "RAT hint not supported\n"); return 2; } push(x); s.nhints++; }
        if (ns == cs) { cs = cs ? 2 * cs : 1 << 20; st = realloc(st, cs * sizeof(Step)); }
        st[ns++] = s; if (id > maxid) maxid = id;
    }
    fclose(f);
    /* index of the step with a given id */
    int64_t *pos = malloc((maxid + 1) * sizeof(int64_t));
    for (int64_t i = 0; i <= maxid; i++) pos[i] = -1;
    for (size_t i = 0; i < ns; i++) pos[st[i].id] = i;
    /* the first empty clause */
    int64_t last = -1;
    for (size_t i = 0; i < ns; i++) if (st[i].nlits == 0) { last = i; break; }
    if (last < 0) { fprintf(stderr, "no empty clause\n"); return 1; }
    char *mark = calloc(ns, 1);
    int64_t *lastuse = malloc(ns * sizeof(int64_t));
    for (size_t i = 0; i < ns; i++) lastuse[i] = -1;
    mark[last] = 1;
    for (int64_t i = last; i >= 0; i--) {
        if (!mark[i]) continue;
        for (int64_t h = 0; h < st[i].nhints; h++) {
            int64_t hid = buf[st[i].hint_off + h];
            if (hid <= maxid && pos[hid] >= 0) { int64_t j = pos[hid]; mark[j] = 1; if (lastuse[j] < i) lastuse[j] = i; }
        }
    }
    /* deletion lists: lemmas whose last use is step i */
    int64_t *dhead = malloc(ns * sizeof(int64_t)), *dnext = malloc(ns * sizeof(int64_t));
    for (size_t i = 0; i < ns; i++) dhead[i] = -1;
    for (size_t j = 0; j < ns; j++) if (mark[j] && lastuse[j] >= 0) { dnext[j] = dhead[lastuse[j]]; dhead[lastuse[j]] = j; }
    /* new ids: original clauses keep 1..m, kept lemmas get m+1, m+2, ... in order */
    if (st[0].id != m + 1) fprintf(stderr, "warning: first lemma id %lld, expected m+1 = %lld\n", (long long)st[0].id, (long long)(m + 1));
    int64_t *nid = malloc(ns * sizeof(int64_t));
    int64_t next = m;
    for (int64_t i = 0; i <= last; i++) nid[i] = mark[i] ? ++next : -1;
    FILE *o = fopen(argv[2], "w"); if (!o) { perror("out"); return 2; }
    size_t kept = 0;
    for (int64_t i = 0; i <= last; i++) {
        if (!mark[i]) continue;
        kept++;
        fprintf(o, "%lld", (long long)nid[i]);
        for (int64_t k = 0; k < st[i].nlits; k++) fprintf(o, " %lld", (long long)buf[st[i].lit_off + k]);
        fprintf(o, " 0");
        for (int64_t k = 0; k < st[i].nhints; k++) {
            int64_t h = buf[st[i].hint_off + k];
            int64_t hn = (h > m) ? nid[pos[h]] : h;
            if (hn < 0) { fprintf(stderr, "internal: hint to dropped step\n"); return 3; }
            fprintf(o, " %lld", (long long)hn);
        }
        fprintf(o, " 0\n");
        if (i != last && dhead[i] >= 0) {
            fprintf(o, "%lld d", (long long)nid[i]);
            for (int64_t j = dhead[i]; j >= 0; j = dnext[j]) fprintf(o, " %lld", (long long)nid[j]);
            fprintf(o, " 0\n");
        }
    }
    fclose(o);
    fprintf(stderr, "steps %zu, kept %zu (empty clause id %lld)\n", ns, kept, (long long)st[last].id);
    return 0;
}
