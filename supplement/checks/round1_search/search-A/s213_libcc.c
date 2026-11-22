/* s213_libcc.c -- search-A, second implementation of the CLOSED-graph search (Claim C; no traceability filter) (shares no code with
 * s213_own.c / mycanon.h / inv2.h): canonical form and tree generation from tools/lib/smallgraph.h,
 * invariants from inv1.h (DFS Ham path), closure rewritten here.
 * Usage: s213_libcl N PREFIX    writes PREFIX_libclmax_N.txt (edge-maximal non-traceable connected).
 */
#include "smallgraph.h"
#include "inv1.h"
#include <time.h>

static int N; static sg_code *trees; static size_t ntr, captr;
static int acc_tree(int n, const unsigned *adj, void *c) {
    (void)c; int e = 0; for (int v = 0; v < n; v++) e += SG_POP(adj[v]);
    return e == 2 * (n - 1) && sg_connected(adj, (1u << n) - 1);
}
static void vis_tree(int n, const unsigned *adj, void *c) {
    (void)c; if (n != N) return;
    if (ntr == captr) trees = realloc(trees, (captr = captr ? 2 * captr : 64) * sizeof(sg_code));
    trees[ntr++] = sg_canon(n, adj);
}
static int is_complete(int n, const unsigned *a) { for (int v = 0; v < n; v++) if (SG_POP(a[v]) != n - 1) return 0; return 1; }
static void close_l(int n, unsigned *a) {           /* repeat until stable: join pairs with degree sum >= n-1 */
    int again = 1;
    while (again) {
        again = 0;
        int d[16]; for (int v = 0; v < n; v++) d[v] = SG_POP(a[v]);
        for (int u = 0; u < n && !again; u++) for (int v = 0; v < n && !again; v++)
            if (u != v && !((a[u] >> v) & 1) && d[u] + d[v] >= n - 1) { a[u] |= 1u << v; a[v] |= 1u << u; again = 1; }
    }
}
int main(int argc, char **argv) {
    N = atoi(argv[1]); const char *prefix = argc > 2 ? argv[2] : "libcl";
    time_t t0 = time(NULL);
    unsigned one[1] = {0};
    sg_hereditary(1, one, N, acc_tree, vis_tree, NULL);
    sg_set seen; sg_set_init(&seen, 1 << 16);
    size_t qn = 0, qc = 1024; sg_code *Q = malloc(qc * sizeof(sg_code));
    for (size_t i = 0; i < ntr; i++) {
        unsigned a[16]; sg_decode(N, trees[i], a);
        close_l(N, a);
        if (is_complete(N, a)) continue;
        sg_code c = sg_canon(N, a);
        if (sg_set_insert(&seen, c)) { if (qn == qc) Q = realloc(Q, (qc *= 2) * sizeof(sg_code)); Q[qn++] = c; }
    }
    char fn[512]; sprintf(fn, "%s_libccmax_%d.txt", prefix, N); FILE *f = fopen(fn, "w");
    long long tot = 0, nmax = 0, cex = 0, mh[40] = {0}; int best = -99;
    while (qn) {
        sg_code c = Q[--qn]; unsigned a[16], h[16]; sg_decode(N, c, a);
        tot++;
        complement1(N, a, h);
        int g2 = gamma2_1(N, h), lm = lowmed1(N, h), sl = g2 - lm - 2;
        if (sl > best) best = sl;
        if (sl >= 0) { char g6[32]; graph6_1(N, a, g6); cex++; printf("HYPOTHESIS_CLOSED_NONCOMPLETE %s\n", g6); }
        int kids = 0;
        for (int u = 0; u < N; u++) for (int v = u + 1; v < N; v++) {
            if ((a[u] >> v) & 1) continue;
            unsigned b[16]; memcpy(b, a, sizeof b); b[u] |= 1u << v; b[v] |= 1u << u;
            close_l(N, b);
            if (is_complete(N, b)) continue;
            kids++;
            sg_code cc = sg_canon(N, b);
            if (sg_set_insert(&seen, cc)) { if (qn == qc) Q = realloc(Q, (qc *= 2) * sizeof(sg_code)); Q[qn++] = cc; }
        }
        if (!kids) { nmax++; mh[sl + 20]++; char g6[32]; graph6_1(N, a, g6); fprintf(f, "%s %d %d %d\n", g6, sl, g2, lm); }
    }
    fclose(f);
    printf("n=%d trees=%zu closed_connected_noncomplete=%lld maximal_closed=%lld satisfying_hypothesis=%lld best_slack=%d time=%lds\n   maximal slack histogram:",
           N, ntr, tot, nmax, cex, best, (long)(time(NULL) - t0));
    for (int s = 0; s < 40; s++) if (mh[s]) printf(" %d:%lld", s - 20, mh[s]);
    printf("\n");
    return 0;
}
