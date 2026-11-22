/* inv2.h -- invariant set II for Conjecture 213 (search-A); shares no code with inv1.h.
 *   ends2(n,adj,e)   e[S] = set of v such that some path with vertex set exactly S ends at v
 *   ham2             Hamiltonian path from that table
 *   gamma2_2         n - (largest U with every u in U having >= 2 neighbours outside U), all subsets
 *   lowmed2          lower median via a degree histogram: the ((n+1) div 2)-th smallest degree
 */
#ifndef INV2_H
#define INV2_H
static void ends2(int n, const unsigned *adj, unsigned *e) {
    unsigned N = 1u << n;
    e[0] = 0;
    for (unsigned S = 1; S < N; S++) {
        if (!(S & (S - 1))) { e[S] = S; continue; }
        unsigned r = 0;
        for (int v = 0; v < n; v++) if ((S >> v) & 1) {
            unsigned P = S ^ (1u << v);
            if (e[P] & adj[v]) r |= 1u << v;
        }
        e[S] = r;
    }
}
static int ham2(int n, const unsigned *adj, unsigned *e) { ends2(n, adj, e); return e[(1u << n) - 1] != 0; }
/* after ends2 on a non-traceable G: is G + ij traceable?  Needs S with i in e[S], j in e[V\S]. */
static int ham2_plus(int n, unsigned *e, int i, int j) {
    unsigned full = (1u << n) - 1;
    for (unsigned S = 0; S <= full; S++) {
        if (!((S >> i) & 1) || ((S >> j) & 1)) continue;
        if (((e[S] >> i) & 1) && ((e[full ^ S] >> j) & 1)) return 1;
    }
    return 0;
}
static int gamma2_2(int n, const unsigned *adj) {
    unsigned full = (1u << n) - 1; int best = 0;
    for (unsigned U = 0; U <= full; U++) {
        int k = __builtin_popcount(U); if (k <= best) continue;
        int ok = 1;
        for (unsigned t = U; t && ok; t &= t - 1) { int u = __builtin_ctz(t); if (__builtin_popcount(adj[u] & ~U & full) < 2) ok = 0; }
        if (ok) best = k;
    }
    return n - best;
}
static int lowmed2(int n, const unsigned *adj) {
    int h[32] = {0};
    for (int v = 0; v < n; v++) h[__builtin_popcount(adj[v])]++;
    int p = (n + 1) / 2, acc = 0;
    for (int d = 0; d < 32; d++) { acc += h[d]; if (acc >= p) return d; }
    return -1;
}
#endif
