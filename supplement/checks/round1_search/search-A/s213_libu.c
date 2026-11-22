/* s213_libu.c -- search-A: every closed non-traceable graph with a universal vertex on N <= 16 vertices,
 * from the star K_{1,N-1} by "add an edge, take the (n-1)-closure", keeping non-traceable graphs.
 * Reaches every edge-maximal non-traceable graph with a universal vertex; by Lemma M the largest slack
 * over all non-traceable graphs with a universal vertex is attained there.
 * Canonical form: tools/lib/smallgraph.h (128-bit).  Traceability: subset DP (inv2.h) with the
 * one-edge extension test.  gamma_2, lower median: inv1.h.
 * Usage: s213_libu N PREFIX      writes PREFIX_libumax_N.txt */
#include "smallgraph.h"
#include "inv1.h"
#include "inv2.h"
#include <time.h>
static unsigned *E;
static void close_u(int n, unsigned *a) {
    for (int ch = 1; ch;) {
        ch = 0;
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
            if (!((a[u] >> v) & 1) && SG_POP(a[u]) + SG_POP(a[v]) >= n - 1) { a[u] |= 1u << v; a[v] |= 1u << u; ch = 1; }
    }
}
int main(int argc, char **argv) {
    int n = atoi(argv[1]); const char *prefix = argc > 2 ? argv[2] : "libu";
    E = malloc(sizeof(unsigned) << n);
    time_t t0 = time(NULL);
    sg_set seen; sg_set_init(&seen, 1 << 16);
    size_t qn = 0, qc = 1 << 16; sg_code *Q = malloc(qc * sizeof(sg_code));
    { unsigned a[16] = {0}; for (int v = 0; v < n - 1; v++) { a[v] = 1u << (n - 1); a[n - 1] |= 1u << v; }
      close_u(n, a); if (!ham2(n, a, E)) { sg_code c = sg_canon(n, a); sg_set_insert(&seen, c); Q[qn++] = c; } }
    char fn[512]; sprintf(fn, "%s_libumax_%d.txt", prefix, n); FILE *f = fopen(fn, "w");
    long long tot = 0, nmax = 0, cex = 0, hist[40] = {0}, mh[40] = {0}; int best = -99;
    while (qn) {
        sg_code code = Q[--qn]; unsigned a[16], h[16]; sg_decode(n, code, a);
        tot++;
        complement1(n, a, h);
        int g2 = gamma2_1(n, h), lm = lowmed1(n, h), sl = g2 - lm - 2;
        hist[sl + 20]++; if (sl > best) best = sl;
        char g6[40]; graph6_1(n, a, g6);
        if (sl >= 0) { cex++; char e[1024]; edges1(n, a, e); printf("COUNTEREXAMPLE n=%d %s %s\n", n, g6, e); fflush(stdout); }
        ends2(n, a, E);
        if (E[(1u << n) - 1]) { fprintf(stderr, "BUG traceable\n"); return 2; }
        int kids = 0;
        for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) {
            if ((a[x] >> y) & 1) continue;
            if (ham2_plus(n, E, x, y)) continue;
            kids++;
            unsigned b[16]; memcpy(b, a, sizeof b); b[x] |= 1u << y; b[y] |= 1u << x;
            close_u(n, b);
            sg_code c = sg_canon(n, b);
            if (sg_set_insert(&seen, c)) { if (qn == qc) Q = realloc(Q, (qc *= 2) * sizeof(sg_code)); Q[qn++] = c; }
        }
        if (!kids) { nmax++; mh[sl + 20]++; fprintf(f, "%s %d %d %d\n", g6, sl, g2, lm); }
        if (tot % 100000 == 0) { fprintf(stderr, "  processed %lld, queue %zu, t=%lds\n", tot, qn, (long)(time(NULL) - t0)); }
    }
    fclose(f);
    printf("n=%d closed_non_traceable_with_universal_vertex=%lld maximal=%lld counterexamples=%lld best_slack=%d time=%lds\n   slack histogram (closed):",
           n, tot, nmax, cex, best, (long)(time(NULL) - t0));
    for (int s = 0; s < 40; s++) if (hist[s]) printf(" %d:%lld", s - 20, hist[s]);
    printf("\n   slack histogram (maximal):");
    for (int s = 0; s < 40; s++) if (mh[s]) printf(" %d:%lld", s - 20, mh[s]);
    printf("\n");
    return 0;
}
