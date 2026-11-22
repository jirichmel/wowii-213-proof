/* t_inv.c -- cross-check invariant sets I and II on random graphs, and test two lemmas:
 *  L1 (slack monotone): slack(G+e) >= slack(G) for every non-edge e, where
 *     slack(G) = gamma2(comp G) - lowmed(comp G) - 2.
 *  L2 (path closure, Bondy-Chvatal): if uv is a non-edge with d(u)+d(v) >= n-1, then
 *     G traceable <=> G+uv traceable.
 * Also prints random graphs with invariants for the Python brute-force check (t_brute.py).
 */
#include <stdio.h>
#include <stdlib.h>
#include "inv1.h"
#include "inv2.h"
static unsigned E[1 << 12];
static unsigned long long rs = 88172645463325252ULL;
static unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static int slack1(int n, const unsigned *a) { unsigned h[16]; complement1(n, a, h); return gamma2_1(n, h) - lowmed1(n, h) - 2; }
int main(int argc, char **argv) {
    long iters = argc > 1 ? atol(argv[1]) : 200000; int dump = argc > 2 ? atoi(argv[2]) : 0;
    long bad = 0, l1 = 0, l2 = 0, l2tests = 0;
    for (long it = 0; it < iters; it++) {
        int n = 2 + rnd() % 10; unsigned a[16] = {0};
        int p = rnd() % 100;
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if ((int)(rnd() % 100) < p) { a[i] |= 1u << j; a[j] |= 1u << i; }
        int h1 = ham1(n, a), h2 = ham2(n, a, E);
        int g1 = gamma2_1(n, a), g2 = gamma2_2(n, a), m1 = lowmed1(n, a), m2 = lowmed2(n, a);
        if (h1 != h2 || g1 != g2 || m1 != m2) { bad++; if (bad < 5) printf("MISMATCH n=%d\n", n); }
        if (dump && it < dump) { char e[1024]; edges1(n, a, e); printf("G %d %d %d %d | %s\n", n, h1, g1, m1, e); }
        int s = slack1(n, a);
        for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++) if (!((a[u] >> v) & 1)) {
            unsigned b[16]; for (int i = 0; i < n; i++) b[i] = a[i];
            b[u] |= 1u << v; b[v] |= 1u << u;
            if (slack1(n, b) < s) l1++;
            if (__builtin_popcount(a[u]) + __builtin_popcount(a[v]) >= n - 1) { l2tests++; if (ham1(n, b) != h1) l2++; }
        }
    }
    if (!dump) printf("iters=%ld mismatches=%ld L1_violations=%ld L2_tests=%ld L2_violations=%ld\n", iters, bad, l1, l2tests, l2);
    return 0;
}
