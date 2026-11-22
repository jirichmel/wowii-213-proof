/* own_u128.c -- search-A, second implementation of the universal-vertex search (see s213_libu.c):
 * own canonical form (mycanon128.h), invariants inv2.h only; shares no code with smallgraph.h / inv1.h.
 * Usage: own_u128 N PREFIX     (N <= 16) writes PREFIX_u128max_N.txt */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "mycanon128.h"
#include "inv2.h"
static unsigned *E;
static void cl(int n, unsigned *a) {
    for (int ch = 1; ch;) { ch = 0;
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
            if (!((a[u] >> v) & 1) && __builtin_popcount(a[u]) + __builtin_popcount(a[v]) >= n - 1) { a[u] |= 1u << v; a[v] |= 1u << u; ch = 1; } }
}
static void g6(int n, const unsigned *adj, char *s) {
    int nb = n * (n - 1) / 2, len = (nb + 5) / 6; s[0] = (char)(n + 63);
    for (int i = 0; i < len; i++) s[1 + i] = 0;
    int b = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, b++) if ((adj[i] >> j) & 1) s[1 + b / 6] |= (char)(1 << (5 - b % 6));
    for (int i = 0; i < len; i++) s[1 + i] += 63; s[1 + len] = 0;
}
int main(int argc, char **argv) {
    int n = atoi(argv[1]); const char *prefix = argc > 2 ? argv[2] : "u128";
    E = malloc(sizeof(unsigned) << n); time_t t0 = time(NULL);
    mset seen; ms_init(&seen, 1 << 16);
    size_t qn = 0, qc = 1 << 16; u128 *Q = malloc(qc * 16);
    { unsigned a[16] = {0}; for (int v = 0; v < n - 1; v++) { a[v] = 1u << (n - 1); a[n - 1] |= 1u << v; }
      cl(n, a); if (!ham2(n, a, E)) { u128 c = mycanon(n, a); ms_add(&seen, c); Q[qn++] = c; } }
    char fn[512]; sprintf(fn, "%s_u128max_%d.txt", prefix, n); FILE *f = fopen(fn, "w");
    long long tot = 0, nmax = 0, cex = 0, mh[64] = {0}; int best = -99;
    while (qn) {
        u128 code = Q[--qn]; unsigned a[16], h[16]; mydecode(n, code, a); tot++;
        for (int v = 0; v < n; v++) { h[v] = 0; for (int w = 0; w < n; w++) if (w != v && !((a[v] >> w) & 1)) h[v] |= 1u << w; }
        int g2 = gamma2_2(n, h), lm = lowmed2(n, h), sl = g2 - lm - 2; if (sl > best) best = sl;
        char s[40]; g6(n, a, s);
        if (sl >= 0) { cex++; printf("COUNTEREXAMPLE %s\n", s); fflush(stdout); }
        ends2(n, a, E);
        int kids = 0;
        for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) {
            if ((a[x] >> y) & 1) continue;
            if (ham2_plus(n, E, x, y)) continue;
            kids++;
            unsigned b[16]; memcpy(b, a, sizeof b); b[x] |= 1u << y; b[y] |= 1u << x; cl(n, b);
            u128 c = mycanon(n, b);
            if (ms_add(&seen, c)) { if (qn == qc) Q = realloc(Q, (qc *= 2) * 16); Q[qn++] = c; }
        }
        if (!kids) { nmax++; mh[sl + 32]++; fprintf(f, "%s %d %d %d\n", s, sl, g2, lm); }
    }
    fclose(f);
    printf("n=%d closed_non_traceable_with_universal_vertex=%lld maximal=%lld counterexamples=%lld best_slack=%d time=%lds\n   maximal:", n, tot, nmax, cex, best, (long)(time(NULL) - t0));
    for (int s = 0; s < 64; s++) if (mh[s]) printf(" %d:%lld", s - 32, mh[s]);
    printf("\n"); return 0;
}
