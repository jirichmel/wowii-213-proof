/* mycanon.h -- search-A's own canonical form (n <= 11), independent of tools/lib/smallgraph.h.
 * Individualisation-refinement: colour refinement to a stable ordered partition (cells ordered by
 * (old cell, neighbour counts per cell)), individualise each vertex of the first non-singleton
 * cell (one vertex per class of twins: swapping twins is an automorphism fixing everything
 * individualised so far, so their subtrees give the same codes), take the largest adjacency code
 * over the discrete leaves.  Code: for j = 1..n-1, i = 0..j-1, bit (i,j), first bit most significant.
 */
#ifndef MYCANON_H
#define MYCANON_H
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static int mc_n; static const unsigned *mc_adj; static uint64_t mc_best;

static int mc_compress(int n, uint64_t *key, int *col) {      /* colours := rank of key; returns #colours */
    int idx[16];
    for (int i = 0; i < n; i++) idx[i] = i;
    for (int i = 1; i < n; i++) { int x = idx[i], j = i - 1; while (j >= 0 && key[idx[j]] > key[x]) { idx[j + 1] = idx[j]; j--; } idx[j + 1] = x; }
    int c = 0;
    for (int i = 0; i < n; i++) { if (i > 0 && key[idx[i]] != key[idx[i - 1]]) c++; col[idx[i]] = c; }
    return c + 1;
}
static int mc_refine(int n, const unsigned *adj, int *col, int k) {
    for (;;) {
        uint64_t key[16];
        unsigned cls[16]; memset(cls, 0, sizeof cls);
        for (int v = 0; v < n; v++) cls[col[v]] |= 1u << v;
        for (int v = 0; v < n; v++) {
            uint64_t kk = (uint64_t)col[v] << 44;
            for (int c = 0; c < k; c++) kk |= (uint64_t)__builtin_popcount(adj[v] & cls[c]) << (4 * (10 - c));
            key[v] = kk;
        }
        int k2 = mc_compress(n, key, col);
        if (k2 == k) return k;
        k = k2;
    }
}
static void mc_search(int *col, int k) {
    int n = mc_n;
    if (k == n) {
        int inv[16]; for (int v = 0; v < n; v++) inv[col[v]] = v;
        uint64_t code = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) code = (code << 1) | ((mc_adj[inv[i]] >> inv[j]) & 1);
        if (code > mc_best) mc_best = code;
        return;
    }
    int sz[16] = {0};
    for (int v = 0; v < n; v++) sz[col[v]]++;
    int tc = 0; while (sz[tc] == 1) tc++;
    int tried[16], nt = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] != tc) continue;
        int tw = 0;
        for (int i = 0; i < nt && !tw; i++) { int u = tried[i]; if ((mc_adj[v] & ~(1u << u)) == (mc_adj[u] & ~(1u << v))) tw = 1; }
        if (tw) continue;
        tried[nt++] = v;
        uint64_t key[16]; int c2[16];
        for (int u = 0; u < n; u++) key[u] = 2 * (uint64_t)col[u] + (col[u] == tc && u != v);
        int k2 = mc_compress(n, key, c2);
        k2 = mc_refine(n, mc_adj, c2, k2);
        mc_search(c2, k2);
    }
}
static uint64_t mycanon(int n, const unsigned *adj) {
    mc_n = n; mc_adj = adj; mc_best = 0;
    int col[16]; for (int v = 0; v < n; v++) col[v] = 0;
    int k = mc_refine(n, adj, col, 1);
    mc_search(col, k);
    return mc_best;
}
static void mydecode(int n, uint64_t code, unsigned *adj) {
    int tot = n * (n - 1) / 2, b = tot - 1;
    for (int v = 0; v < n; v++) adj[v] = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, b--)
        if ((code >> b) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
}

/* open-addressing set of nonzero-or-zero 64-bit codes (stored +1) */
typedef struct { uint64_t *s; size_t cap, cnt; } mset;
static void ms_init(mset *m, size_t cap) { m->cap = cap; m->cnt = 0; m->s = calloc(cap, 8); if (!m->s) { fprintf(stderr, "oom\n"); exit(1); } }
static uint64_t ms_h(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static int ms_add(mset *m, uint64_t key) {
    uint64_t k = key + 1; size_t i = ms_h(k) & (m->cap - 1);
    while (m->s[i]) { if (m->s[i] == k) return 0; i = (i + 1) & (m->cap - 1); }
    m->s[i] = k; m->cnt++;
    if (m->cnt * 2 > m->cap) {
        mset b; ms_init(&b, m->cap * 2);
        for (size_t j = 0; j < m->cap; j++) if (m->s[j]) { size_t h = ms_h(m->s[j]) & (b.cap - 1); while (b.s[h]) h = (h + 1) & (b.cap - 1); b.s[h] = m->s[j]; b.cnt++; }
        free(m->s); *m = b;
    }
    return 1;
}
static uint64_t *ms_list(mset *m, size_t *cnt) {
    uint64_t *o = malloc((m->cnt + 1) * 8); size_t k = 0;
    for (size_t j = 0; j < m->cap; j++) if (m->s[j]) o[k++] = m->s[j] - 1;
    *cnt = k; return o;
}
#endif
