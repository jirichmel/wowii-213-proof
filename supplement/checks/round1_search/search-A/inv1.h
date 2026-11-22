/* inv1.h -- invariant set I for Conjecture 213 (search-A).  Written independently of
 * tools/lib/smallgraph.h's invariants.  Graph: adj[v] bitmask, n <= 16.
 *   ham1(n,adj)      Hamiltonian path by depth-first search with a connectivity prune
 *   gamma2_1(n,adj)  2-domination number by enumerating subsets in order of size
 *   lowmed1(n,adj)   lower median of the degree sequence (d_{n/2} n even, d_{(n+1)/2} n odd)
 */
#ifndef INV1_H
#define INV1_H
static int i1_reach(const unsigned *adj, int v, unsigned R) {   /* is R u {v} connected via R? */
    unsigned seen = 1u << v, fr = seen;
    while (fr) {
        unsigned nf = 0;
        for (unsigned t = fr; t; t &= t - 1) nf |= adj[__builtin_ctz(t)] & R;
        nf &= ~seen; seen |= nf; fr = nf;
    }
    return (seen & R) == R;
}
static int i1_dfs(const unsigned *adj, int v, unsigned R) {     /* path from v covering R (v not in R) */
    if (!R) return 1;
    if (!i1_reach(adj, v, R)) return 0;
    for (unsigned t = adj[v] & R; t; t &= t - 1) {
        int w = __builtin_ctz(t);
        if (i1_dfs(adj, w, R & ~(1u << w))) return 1;
    }
    return 0;
}
static int ham1(int n, const unsigned *adj) {
    unsigned full = (n == 32) ? ~0u : ((1u << n) - 1);
    if (n <= 1) return 1;
    int leaves = 0;
    for (int v = 0; v < n; v++) { int d = __builtin_popcount(adj[v]); if (d == 0) return 0; if (d == 1) leaves++; }
    if (leaves > 2) return 0;
    for (int v = 0; v < n; v++) if (i1_dfs(adj, v, full & ~(1u << v))) return 1;
    return 0;
}
static int is2dom1(int n, const unsigned *adj, unsigned D) {
    for (int v = 0; v < n; v++) {
        if ((D >> v) & 1) continue;
        unsigned x = adj[v] & D;
        if (!x || !(x & (x - 1))) return 0;     /* fewer than two neighbours in D */
    }
    return 1;
}
/* smallest size of a 2-dominating set; subsets of size k enumerated with Gosper's hack */
static int gamma2_1(int n, const unsigned *adj) {
    for (int k = 0; k <= n; k++) {
        if (k == 0) { if (n == 0) return 0; continue; }
        unsigned S = (1u << k) - 1, lim = 1u << n;
        while (S < lim) {
            if (is2dom1(n, adj, S)) return k;
            unsigned c = S & -S, r = S + c;
            S = (((r ^ S) >> 2) / c) | r;
        }
    }
    return n;
}
static int lowmed1(int n, const unsigned *adj) {
    int d[32];
    for (int v = 0; v < n; v++) d[v] = __builtin_popcount(adj[v]);
    for (int i = 1; i < n; i++) { int x = d[i], j = i - 1; while (j >= 0 && d[j] > x) { d[j + 1] = d[j]; j--; } d[j + 1] = x; }
    return d[(n - 1) / 2];          /* 1-indexed n/2 for n even, (n+1)/2 for n odd */
}
static void complement1(int n, const unsigned *adj, unsigned *h) {
    unsigned full = (1u << n) - 1;
    for (int v = 0; v < n; v++) h[v] = full & ~adj[v] & ~(1u << v);
}
static void graph6_1(int n, const unsigned *adj, char *out) {    /* n <= 62 */
    int k = 0, bits = 0, acc = 0;
    out[k++] = (char)(63 + n);
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        acc = (acc << 1) | ((adj[i] >> j) & 1); bits++;
        if (bits == 6) { out[k++] = (char)(63 + acc); acc = 0; bits = 0; }
    }
    if (bits) { acc <<= (6 - bits); out[k++] = (char)(63 + acc); }
    out[k] = 0;
}
static void edges1(int n, const unsigned *adj, char *out) {
    int k = 0; out[0] = 0;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if ((adj[i] >> j) & 1)
        k += sprintf(out + k, "%s%d-%d", k ? " " : "", i, j);
}
#endif
