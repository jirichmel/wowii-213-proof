/* certtest_A.c -- search-A's own test of the pair/triple certificate proposed on the board
 * (constructions 0527): for G closed, connected, non-complete,
 *    min( min_{u!=w} |N[u] u N[w]| , min_{|T|=3} |T u {x : x has >= 2 G-neighbours in T}| ) <= lm(H) + 1.
 * Both sets 2-dominate H.  The left side can only grow and lm(H) only drop when edges are added to G,
 * so the inequality for a graph implies it for all its spanning subgraphs; every closed non-complete
 * graph lies below a maximal closed non-complete one, so testing the maximal ones (out/own_ccmax_N.txt)
 * tests all closed connected non-complete graphs on N vertices.
 * Usage: certtest_A < LIST     (lines "graph6 slack ...") */
#include <stdio.h>
int main(void) {
    char line[256], g[64]; int sl; long tot = 0, fail = 0, needT = 0, pairtight = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (sscanf(line, "%63s %d", g, &sl) != 2) continue;
        int n = g[0] - 63; unsigned a[16] = {0}; int b = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, b++)
            if (((g[1 + b / 6] - 63) >> (5 - b % 6)) & 1) { a[i] |= 1u << j; a[j] |= 1u << i; }
        int hd[16], cnt[32] = {0};
        for (int v = 0; v < n; v++) { hd[v] = n - 1 - __builtin_popcount(a[v]); cnt[hd[v]]++; }
        int p = (n + 1) / 2, acc = 0, lm = 0;
        for (int d = 0; d < 32; d++) { acc += cnt[d]; if (acc >= p) { lm = d; break; } }
        int bp = 99, bt = 99;
        for (int u = 0; u < n; u++) for (int w = u + 1; w < n; w++) {
            int s = __builtin_popcount(a[u] | a[w] | (1u << u) | (1u << w)); if (s < bp) bp = s;
            for (int z = w + 1; z < n; z++) {
                unsigned T = (1u << u) | (1u << w) | (1u << z), D = T;
                for (int x = 0; x < n; x++) if (!((T >> x) & 1) && __builtin_popcount(a[x] & T) >= 2) D |= 1u << x;
                int s3 = __builtin_popcount(D); if (s3 < bt) bt = s3;
            }
        }
        tot++;
        int best = bp < bt ? bp : bt;
        if (best > lm + 1) { fail++; printf("FAIL %s pair=%d triple=%d lm=%d\n", g, bp, bt, lm); }
        else if (bp > lm + 1) needT++;
        if (bp == lm + 1) pairtight++;
    }
    printf("graphs=%ld certificate_failures=%ld need_triple=%ld\n", tot, fail, needT);
    return 0;
}
