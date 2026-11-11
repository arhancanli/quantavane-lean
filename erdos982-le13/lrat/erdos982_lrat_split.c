/* erdos982_lrat_split: trim a BINARY LRAT refutation of a CNF F (m clauses; CaDiCaL --binary=true output) to the
 * steps reachable from the first empty clause, and cut it into k chunks, each a TEXT LRAT refutation that Lean's
 * checker can take on its own (E982C/Split.lean, `chunkCNF`):
 *
 *   chunk j (1 <= j < k) refutes  F ++ S_{j-1} ++ negCls b S_j      chunk k refutes  F ++ S_{k-1}
 *
 * where S_j (S_0 = []) lists the kept lemmas derived in chunks 1..j that a later chunk uses, in derivation order,
 * and negCls b S = [s_0 ∨ s_1 ∨ ...] ++ [¬s_i ∨ ¬l | i, l ∈ S_i] with selector variable s_i = atom b + i
 * (DIMACS b + i + 1). So chunk j shows F ∧ S_{j-1} ⊨ S_j, and chunk k shows F ∧ S_{k-1} is unsatisfiable.
 * In each chunk: original clauses keep ids 1..m, S_{j-1} gets m+1.., the negCls clauses follow, and the kept
 * lemmas are renumbered densely after them (Lean's checker appends added clauses in order). A clause is deleted
 * right after the last step of its chunk that uses it, unless it belongs to S_j. A non-final chunk ends with the
 * units ¬s_i (hints: the clauses ¬s_i ∨ ¬l, then S_i) and the empty clause (hints: those units, then s_0 ∨ ...).
 *
 * Usage: erdos982_lrat_split in.lratb m b k outdir F.cnf
 * Writes outdir/s<j>.cls (clauses of S_j, DIMACS lines, j = 1..k-1), outdir/p<j>.lrat, and outdir/c<j>.cnf (the
 * chunk CNF in DIMACS, for external checkers). Chunks are balanced by estimated text size.
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
        if (*q >= N) { fprintf(stderr, "truncated varint\n"); exit(2); }
        unsigned char c = B[(*q)++];
        x |= (uint64_t)(c & 0x7f) << sh;
        if (!(c & 0x80)) return x;
        sh += 7; if (sh > 63) { fprintf(stderr, "varint too long\n"); exit(2); }
    }
}
static inline int64_t dec(uint64_t x) { return (x & 1) ? -(int64_t)(x >> 1) : (int64_t)(x >> 1); }
static int ndig(int64_t x) { int d = x < 0 ? 2 : 1; if (x < 0) x = -x; while (x >= 10) { x /= 10; d++; } return d; }

int main(int argc, char **argv) {
    if (argc != 7) { fprintf(stderr, "usage: %s in.lratb m b k outdir F.cnf\n", argv[0]); return 2; }
    int64_t m = strtoll(argv[2], NULL, 10), b = strtoll(argv[3], NULL, 10);
    int k = atoi(argv[4]); const char *od = argv[5];
    int fd = open(argv[1], O_RDONLY); if (fd < 0) { perror("in"); return 2; }
    struct stat sb; fstat(fd, &sb); N = sb.st_size;
    B = mmap(NULL, N, PROT_READ, MAP_PRIVATE, fd, 0); if (B == MAP_FAILED) { perror("mmap"); return 2; }
    size_t cs = 1 << 22, ns = 0;
    uint64_t *off = malloc(cs * sizeof(uint64_t)); int64_t *ids = malloc(cs * sizeof(int64_t));
    int64_t maxid = m, prev = m, last = -1; size_t q = 0;
    while (q < N) {
        unsigned char t = B[q++];
        if (t == 'a') {
            int64_t id = dec(rd(&q));
            if (id <= prev) { fprintf(stderr, "ids not increasing\n"); return 2; }
            prev = id;
            if (ns == cs) { cs *= 2; off = realloc(off, cs * 8); ids = realloc(ids, cs * 8); if (!off || !ids) return 2; }
            off[ns] = q; ids[ns] = id;
            size_t nl = 0; while (rd(&q) != 0) nl++;
            uint64_t h; while ((h = rd(&q)) != 0) if (h & 1) { fprintf(stderr, "RAT hint\n"); return 2; }
            maxid = id;
            if (nl == 0) { last = ns; ns++; break; }
            ns++;
        } else if (t == 'd') { while (rd(&q) != 0) {} }
        else { fprintf(stderr, "bad step byte\n"); return 2; }
    }
    if (last < 0) { fprintf(stderr, "no empty clause\n"); return 1; }
    int32_t *pos = malloc((size_t)(maxid - m + 1) * sizeof(int32_t));
    for (int64_t i = 0; i <= maxid - m; i++) pos[i] = -1;
    for (size_t i = 0; i < ns; i++) pos[ids[i] - m] = (int32_t)i;
    free(ids);
    /* backward marking; lastuse = largest step index using the step as a hint */
    char *mark = calloc(ns, 1); int32_t *lu = malloc(ns * 4);
    for (size_t i = 0; i < ns; i++) lu[i] = -1;
    mark[last] = 1;
    for (int64_t i = last; i >= 0; i--) {
        if (!mark[i]) continue;
        size_t r = off[i]; while (rd(&r) != 0) {}
        uint64_t h;
        while ((h = rd(&r)) != 0) {
            int64_t hid = dec(h);
            if (hid > m) {
                if (hid > maxid || pos[hid - m] < 0) { fprintf(stderr, "hint to missing step\n"); return 3; }
                int32_t j = pos[hid - m]; if (j >= i) { fprintf(stderr, "hint not earlier\n"); return 3; }
                mark[j] = 1; if (lu[j] < i) lu[j] = (int32_t)i;
            } else if (hid < 1) { fprintf(stderr, "bad hint\n"); return 3; }
        }
    }
    /* kept steps in order: rank -> step index; lastuse in ranks */
    size_t K = 0; for (size_t i = 0; i < ns; i++) K += mark[i];
    int32_t *st = malloc(K * 4), *rk = malloc(ns * 4); size_t r0 = 0;
    for (size_t i = 0; i < ns; i++) { rk[i] = -1; if (mark[i]) { rk[i] = (int32_t)r0; st[r0++] = (int32_t)i; } }
    int32_t *lur = malloc(K * 4);  /* last use rank, -1 if unused */
    uint64_t *sz = malloc(K * 8); uint64_t tot = 0;
    for (size_t r = 0; r < K; r++) {
        int32_t i = st[r]; lur[r] = lu[i] >= 0 ? rk[lu[i]] : -1;
        size_t p = off[i]; uint64_t x, s = 12;
        while ((x = rd(&p)) != 0) s += ndig(dec(x)) + 1;
        while ((x = rd(&p)) != 0) s += ndig(dec(x)) + 1;
        sz[r] = s; tot += s;
    }
    free(lu); free(mark);
    /* chunk boundaries: bnd[j] = last rank of chunk j (j = 1..k), bnd[0] = -1 */
    int64_t *bnd = malloc((k + 1) * 8); bnd[0] = -1; bnd[k] = (int64_t)K - 1;
    { uint64_t acc = 0; int j = 1;
      for (size_t r = 0; r < K && j < k; r++) { acc += sz[r]; if (acc >= tot * j / k) bnd[j++] = r; }
      if (j < k) { fprintf(stderr, "too many chunks\n"); return 2; } }
    fprintf(stderr, "kept %zu of %zu steps, est. text %.1f MB, %d chunks\n", K, ns, tot / 1e6, k);
    /* interface sets: S_j = ranks r <= bnd[j] with lur[r] > bnd[j], in order */
    int32_t **S = calloc(k + 1, sizeof(int32_t *)); size_t *Sn = calloc(k + 1, sizeof(size_t));
    for (int j = 1; j < k; j++) {
        size_t c = 0; for (int64_t r = 0; r <= bnd[j]; r++) if (lur[r] > bnd[j]) c++;
        S[j] = malloc((c + 1) * 4); Sn[j] = c; c = 0;
        for (int64_t r = 0; r <= bnd[j]; r++) if (lur[r] > bnd[j]) S[j][c++] = (int32_t)r;
    }
    int64_t *nid = malloc(K * 8);           /* id of a kept lemma in the current chunk */
    int32_t *dhead = malloc(K * 4), *dnext = malloc(K * 4);
    char path[4096]; static char obuf[1 << 22];
    /* the base CNF body, for the chunk DIMACS files */
    FILE *fc = fopen(argv[6], "r"); if (!fc) { perror("F.cnf"); return 2; }
    fseek(fc, 0, SEEK_END); long fl = ftell(fc); fseek(fc, 0, SEEK_SET);
    char *fbuf = malloc(fl + 1); if (fread(fbuf, 1, fl, fc) != (size_t)fl) return 2; fbuf[fl] = 0; fclose(fc);
    char *body = fbuf; while (*body == 'c' || *body == 'p') { body = strchr(body, '\n'); if (!body) return 2; body++; }
    int64_t fvars = 0; { char *pl = strstr(fbuf, "p cnf "); if (pl) fvars = strtoll(pl + 6, NULL, 10); }
    for (int j = 1; j <= k; j++) {
        int fin = (j == k);
        int64_t lo = bnd[j - 1] + 1, hi = bnd[j];
        size_t np = fin ? 0 : Sn[j];
        /* S_j clause file */
        if (!fin) {
            snprintf(path, sizeof path, "%s/s%d.cls", od, j);
            FILE *o = fopen(path, "w"); if (!o) { perror(path); return 2; }
            for (size_t t = 0; t < Sn[j]; t++) {
                size_t p = off[st[S[j][t]]]; uint64_t x;
                while ((x = rd(&p)) != 0) fprintf(o, "%lld ", (long long)dec(x));
                fputs("0\n", o);
            }
            fclose(o);
        }
        /* ids */
        int64_t sp = (j > 1) ? (int64_t)Sn[j - 1] : 0;
        int64_t negc = 0, *litoff = NULL;      /* id offset of the first ¬s_i ∨ ¬l clause of S_j[i] */
        if (!fin) {
            litoff = malloc((np + 1) * 8);
            int64_t c = m + sp + 2;
            for (size_t t = 0; t < np; t++) {
                litoff[t] = c; size_t p = off[st[S[j][t]]]; while (rd(&p) != 0) c++;
            }
            negc = c - (m + sp + 1);
        }
        int64_t base = m + sp + negc;
        for (int64_t r = 0; r < (int64_t)K; r++) nid[r] = -1;
        if (j > 1) for (size_t t = 0; t < Sn[j - 1]; t++) nid[S[j - 1][t]] = m + 1 + (int64_t)t;
        int64_t next = base;
        for (int64_t r = lo; r <= hi; r++) nid[r] = ++next;
        /* deletions within the chunk: clauses (S_{j-1} or chunk lemmas) with last use r in [lo, hi], not in S_j */
        for (int64_t r = lo; r <= hi; r++) dhead[r] = -1;
        if (j > 1) for (size_t t = 0; t < Sn[j - 1]; t++) { int32_t r = S[j - 1][t]; if (lur[r] >= lo && lur[r] <= hi) { dnext[r] = dhead[lur[r]]; dhead[lur[r]] = r; } }
        for (int64_t r = lo; r <= hi; r++) if (lur[r] >= lo && lur[r] <= hi) { dnext[r] = dhead[lur[r]]; dhead[lur[r]] = (int32_t)r; }
        snprintf(path, sizeof path, "%s/p%d.lrat", od, j);
        FILE *o = fopen(path, "w"); if (!o) { perror(path); return 2; }
        setvbuf(o, obuf, _IOFBF, sizeof obuf);
        for (int64_t r = lo; r <= hi; r++) {
            int32_t i = st[r];
            fprintf(o, "%lld", (long long)nid[r]);
            size_t p = off[i]; uint64_t x;
            while ((x = rd(&p)) != 0) fprintf(o, " %lld", (long long)dec(x));
            fputs(" 0", o);
            while ((x = rd(&p)) != 0) {
                int64_t h = dec(x), hn;
                if (h <= m) hn = h; else { int32_t rr = rk[pos[h - m]]; hn = nid[rr]; }
                if (hn < 0) { fprintf(stderr, "internal: hint not available in chunk %d\n", j); return 3; }
                fprintf(o, " %lld", (long long)hn);
            }
            fputs(" 0\n", o);
            if (r != (int64_t)K - 1 && dhead[r] >= 0) {
                fprintf(o, "%lld d", (long long)nid[r]);
                for (int32_t t = dhead[r]; t >= 0; t = dnext[t]) fprintf(o, " %lld", (long long)nid[t]);
                fputs(" 0\n", o);
            }
        }
        if (!fin) {
            int64_t u0 = next + 1;
            for (size_t t = 0; t < np; t++) {
                fprintf(o, "%lld %lld 0", (long long)(++next), -(long long)(b + (int64_t)t + 1));
                size_t p = off[st[S[j][t]]]; int64_t c = litoff[t];
                while (rd(&p) != 0) fprintf(o, " %lld", (long long)(c++));
                if (nid[S[j][t]] < 0) { fprintf(stderr, "internal: S clause without id\n"); return 3; }
                fprintf(o, " %lld 0\n", (long long)nid[S[j][t]]);
            }
            fprintf(o, "%lld 0", (long long)(++next));
            for (size_t t = 0; t < np; t++) fprintf(o, " %lld", (long long)(u0 + (int64_t)t));
            fprintf(o, " %lld 0\n", (long long)(m + sp + 1));
        }
        fclose(o);
        /* chunk CNF in DIMACS: F, S_{j-1}, negCls b S_j */
        snprintf(path, sizeof path, "%s/c%d.cnf", od, j);
        o = fopen(path, "w"); if (!o) { perror(path); return 2; }
        int64_t nv = fin ? fvars : (b + (int64_t)np > fvars ? b + (int64_t)np : fvars);
        fprintf(o, "p cnf %lld %lld\n", (long long)nv, (long long)(base));
        fputs(body, o);
        if (j > 1) for (size_t t = 0; t < Sn[j - 1]; t++) {
            size_t p = off[st[S[j - 1][t]]]; uint64_t x;
            while ((x = rd(&p)) != 0) fprintf(o, "%lld ", (long long)dec(x));
            fputs("0\n", o);
        }
        if (!fin) {
            for (size_t t = 0; t < np; t++) fprintf(o, "%lld ", (long long)(b + (int64_t)t + 1));
            fputs("0\n", o);
            for (size_t t = 0; t < np; t++) {
                size_t p = off[st[S[j][t]]]; uint64_t x;
                while ((x = rd(&p)) != 0) fprintf(o, "%lld %lld 0\n", -(long long)(b + (int64_t)t + 1), -(long long)dec(x));
            }
        }
        fclose(o);
        { uint64_t cz = 0; for (int64_t r = lo; r <= hi; r++) cz += sz[r];
          fprintf(stderr, "chunk %d: lemmas %lld..%lld (%lld), |S_prev| %lld, |S| %zu, neg clauses %lld, est %.1f MB\n", j,
                  (long long)lo, (long long)hi, (long long)(hi - lo + 1), (long long)sp, np, (long long)negc, cz / 1e6); }
        free(litoff);
    }
    return 0;
}
