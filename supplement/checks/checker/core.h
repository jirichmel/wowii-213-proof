/* checker213 core: written from scratch for the adversarial check of the Claim C proof.
   Graphs on n <= 64 vertices, adjacency rows as uint64 bitmasks (G), complement computed on demand.
   Nothing here is taken from the prover's or the session agent's programs. */
#ifndef CORE213_H
#define CORE213_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
#define PC(x) __builtin_popcountll(x)
#define CTZ(x) __builtin_ctzll(x)
#define FULL(n) ((n) == 64 ? ~0ULL : ((1ULL << (n)) - 1))

static long long g_fail = 0;
#define FAIL(...) do { g_fail++; if (g_fail <= 50) { printf("FAIL: "); printf(__VA_ARGS__); printf("\n"); fflush(stdout);} } while (0)

/* ---------- basic ---------- */
static int is_connected(int n, const u64 *a) {
    u64 seen = 1, front = 1, all = FULL(n);
    while (front) {
        u64 nf = 0;
        for (u64 f = front; f; f &= f - 1) nf |= a[CTZ(f)];
        nf &= ~seen; seen |= nf; front = nf;
    }
    return seen == all;
}
static int is_complete(int n, const u64 *a) {
    for (int v = 0; v < n; v++) if (PC(a[v]) != n - 1) return 0;
    return 1;
}
/* closed: d(a)+d(b) <= n-2 for all non-adjacent a != b */
static int is_closed(int n, const u64 *a) {
    int d[64];
    for (int v = 0; v < n; v++) d[v] = PC(a[v]);
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++)
        if (!((a[x] >> y) & 1) && d[x] + d[y] > n - 2) return 0;
    return 1;
}
static void complement(int n, const u64 *a, u64 *h) {
    for (int v = 0; v < n; v++) h[v] = FULL(n) & ~a[v] & ~(1ULL << v);
}
static int cmpint(const void *x, const void *y) { return *(const int *)x - *(const int *)y; }
/* lower median of the degree sequence of H: k-th smallest, k = ceil(n/2) (1-based) */
static int lm_of(int n, const u64 *h) {
    int d[64];
    for (int v = 0; v < n; v++) d[v] = PC(h[v]);
    qsort(d, n, sizeof(int), cmpint);
    return d[(n + 1) / 2 - 1];
}
/* D 2-dominating in graph h: every v not in D has >= 2 h-neighbours in D */
static int is_2dom(int n, const u64 *h, u64 D) {
    for (int v = 0; v < n; v++) if (!((D >> v) & 1) && PC(h[v] & D) < 2) return 0;
    return 1;
}
/* exact gamma_2 by subset enumeration in order of size (Gosper); for n <= ~24 */
static int g2_exact_enum(int n, const u64 *h, int cap) {
    for (int k = 0; k <= n && k <= cap; k++) {
        if (k == 0) { if (n == 0) return 0; continue; }
        if (k > n) break;
        u64 s = (1ULL << k) - 1, lim = 1ULL << n;
        while (s < lim) {
            if (is_2dom(n, h, s)) return k;
            u64 c = s & -s, r = s + c; s = (((r ^ s) >> 2) / c) | r;
        }
    }
    return cap + 1; /* > cap */
}

/* ---------- branch and bound for gamma_2 <= k  (second implementation) ---------- */
static long long bb_nodes;
static int bb_rec(int n, const u64 *h, u64 D, u64 excl, int k) {
    bb_nodes++;
    /* find an unsatisfied vertex with fewest options */
    int best = -1, bestopt = 1000, need_b = 0; u64 bestc = 0;
    int totneed = 0;
    for (int v = 0; v < n; v++) {
        if ((D >> v) & 1) continue;
        int have = PC(h[v] & D);
        if (have >= 2) continue;
        int need = 2 - have;
        u64 cand = h[v] & ~D & ~excl;
        int opt = PC(cand) + (((excl >> v) & 1) ? 0 : 1);
        if (((excl >> v) & 1) && PC(cand) < need) return 0;
        if (opt == 0) return 0;
        totneed++;
        if (opt < bestopt) { bestopt = opt; best = v; bestc = cand; need_b = need; }
    }
    if (best < 0) return 1;
    if (k == 0) return 0;
    /* crude bound: each added vertex satisfies itself plus helps at most maxdeg others by 1 */
    (void)need_b; (void)totneed;
    int v = best;
    u64 ex = excl;
    if (!((excl >> v) & 1)) {
        if (bb_rec(n, h, D | (1ULL << v), ex, k - 1)) return 1;
        ex |= 1ULL << v;
    }
    for (u64 c = bestc; c; c &= c - 1) {
        int w = CTZ(c);
        if (bb_rec(n, h, D | (1ULL << w), ex, k - 1)) return 1;
        ex |= 1ULL << w;
    }
    return 0;
}
/* returns gamma_2 if <= cap, else cap+1 */
static int g2_bb(int n, const u64 *h, int cap) {
    for (int k = 1; k <= cap; k++) if (bb_rec(n, h, 0, 0, k)) return k;
    return cap + 1;
}

/* ---------- Hamiltonian path: DFS and bitmask DP (two implementations) ---------- */
static int hp_dfs_rec(int n, const u64 *a, int v, u64 vis) {
    if (vis == FULL(n)) return 1;
    for (u64 c = a[v] & ~vis; c; c &= c - 1) {
        int w = CTZ(c);
        if (hp_dfs_rec(n, a, w, vis | (1ULL << w))) return 1;
    }
    return 0;
}
static int hp_dfs(int n, const u64 *a) {
    if (n == 1) return 1;
    for (int v = 0; v < n; v++) if (hp_dfs_rec(n, a, v, 1ULL << v)) return 1;
    return 0;
}
static int hp_dp(int n, const u64 *a) { /* n <= 20 */
    static uint32_t ends[1 << 20];
    uint32_t N = 1u << n;
    for (uint32_t s = 0; s < N; s++) ends[s] = 0;
    for (int v = 0; v < n; v++) ends[1u << v] = 1u << v;
    for (uint32_t s = 1; s < N; s++) {
        uint32_t e = ends[s];
        if (!e) continue;
        uint32_t ext = 0;
        for (uint32_t t = e; t; t &= t - 1) ext |= (uint32_t)a[__builtin_ctz(t)];
        ext &= ~s;
        for (uint32_t t = ext; t; t &= t - 1) {
            int w = __builtin_ctz(t);
            ends[s | (1u << w)] |= 1u << w;
        }
    }
    return ends[N - 1] != 0;
}

/* ---------- the construction of the proof, with every choice explored ---------- */
/* Statistics of one graph's construction. */
typedef struct {
    int caseid;        /* 1 = 2m>=n (Lemma J), 2 = Case 2a, 3 = Case 2b */
    long long terminals; /* number of terminal (B,R) states / sets checked */
    int maxrounds;     /* max |B| at a terminal (Case 2a) */
    long long nodes;
    int capped;        /* exploration hit the node cap */
} cstat;

/* visited set for (B,R) states */
#define VHBITS 20
static u64 vh_b[1 << VHBITS], vh_r[1 << VHBITS];
static int vh_used[1 << VHBITS];
static int vh_stamp = 1;
static long long vh_count;
static int vh_insert(u64 B, u64 R) { /* 1 if new */
    u64 x = B * 0x9E3779B97F4A7C15ULL ^ (R + 0x632BE59BD9B4E019ULL) * 0xBF58476D1CE4E5B9ULL;
    unsigned i = (unsigned)(x >> (64 - VHBITS));
    while (vh_used[i] == vh_stamp) {
        if (vh_b[i] == B && vh_r[i] == R) return 0;
        i = (i + 1) & ((1 << VHBITS) - 1);
    }
    if (vh_count > (1 << VHBITS) * 0.7) return 1; /* table full: treat as new (no memo) */
    vh_used[i] = vh_stamp; vh_b[i] = B; vh_r[i] = R; vh_count++;
    return 1;
}
static void vh_reset(void) { vh_stamp++; vh_count = 0; if (vh_stamp == 0x7fffffff) { memset(vh_used, 0, sizeof vh_used); vh_stamp = 1; } }

typedef struct {
    int n, m, u, r;
    const u64 *a, *h;
    u64 U, P, Y, Q;
    long long nodecap;
    cstat *st;
    const char *tag;
} cctx;

static void check_terminal(cctx *c, u64 B, u64 R) {
    u64 D = c->U | B | R;
    c->st->terminals++;
    if (PC(B) > c->st->maxrounds) c->st->maxrounds = PC(B);
    if (PC(D) != c->m + 1) FAIL("%s: |D|=%d != m+1=%d", c->tag, PC(D), c->m + 1);
    if (!is_2dom(c->n, c->h, D)) FAIL("%s: D not 2-dominating (B=%llx R=%llx)", c->tag, (unsigned long long)B, (unsigned long long)R);
    /* check the conclusion of Lemma 4 directly */
    for (u64 p = c->P & ~B; p; p &= p - 1) {
        int q = CTZ(p);
        if (PC(c->a[q] & R) > PC(R) - 2) FAIL("%s: Lemma 4 conclusion fails at q=%d", c->tag, q);
    }
}
static void explore(cctx *c, u64 B, u64 R, int depth) {
    if (c->st->nodes >= c->nodecap) { c->st->capped = 1; return; }
    c->st->nodes++;
    if (!vh_insert(B, R)) return;
    /* invariants */
    if (PC(B) + PC(R) != c->r) FAIL("%s: |B|+|R| != r", c->tag);
    if (PC(R) < 2) FAIL("%s: |R| < 2", c->tag);
    if (depth > c->r - 2) FAIL("%s: more than r-2 rounds", c->tag);
    for (u64 t = R; t; t &= t - 1) { int y = CTZ(t); if ((B & c->a[y]) != B) FAIL("%s: B not inside A_y", c->tag); }
    int k = PC(R), any = 0;
    for (u64 p = c->P & ~B; p; p &= p - 1) {
        int q = CTZ(p);
        u64 S = c->a[q] & R; /* y in R with q in A_y */
        if (PC(S) >= k - 1) {
            any = 1;
            /* all (k-1)-subsets of S */
            if (PC(S) == k - 1) explore(c, B | (1ULL << q), S, depth + 1);
            else for (u64 t = S; t; t &= t - 1) explore(c, B | (1ULL << q), S & ~(t & -t), depth + 1);
        }
    }
    if (!any) check_terminal(c, B, R);
}

/* Run the whole proof of Theorem 1 on G (closed, connected, non-complete assumed and checked by caller).
   rootcap: max number of starting sets R0 tried (all if their number <= rootcap, else random + greedy ones). */
static u64 rng_s = 0x1234567ULL;
static inline u64 rng(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

static double binom(int a, int b) { double r = 1; if (b < 0 || b > a) return 0; for (int i = 0; i < b; i++) r = r * (a - i) / (i + 1); return r; }

static void run_proof(int n, const u64 *a, long long rootcap, long long nodecap, cstat *st, const char *tag) {
    u64 h[64];
    complement(n, a, h);
    int m = lm_of(n, h);
    memset(st, 0, sizeof *st);
    if (2 * m >= n) {
        /* Lemma J: W = {d_H >= m}, A subset of W of size n-m-1, D = V \ A. All choices of A (capped). */
        st->caseid = 1;
        u64 W = 0;
        for (int v = 0; v < n; v++) if (PC(h[v]) >= m) W |= 1ULL << v;
        int asz = n - m - 1, w = PC(W);
        if (w < n / 2 + 1) FAIL("%s: |W| < floor(n/2)+1", tag);
        if (asz < 0 || asz > w) { FAIL("%s: a out of range", tag); return; }
        int wl[64], nw = 0;
        for (u64 t = W; t; t &= t - 1) wl[nw++] = CTZ(t);
        double tot = binom(nw, asz);
        long long tries = tot <= rootcap ? (long long)tot : rootcap;
        int idx[64];
        for (int i = 0; i < asz; i++) idx[i] = i;
        for (long long t = 0; t < tries; t++) {
            u64 A = 0;
            if (tot <= rootcap) { for (int i = 0; i < asz; i++) A |= 1ULL << wl[idx[i]]; }
            else { while (PC(A) < asz) A |= 1ULL << wl[rng() % nw]; }
            u64 D = FULL(n) & ~A;
            st->terminals++;
            if (PC(D) != m + 1 || !is_2dom(n, h, D)) FAIL("%s: Lemma J set fails", tag);
            if (tot <= rootcap) { /* next combination */
                int i = asz - 1;
                while (i >= 0 && idx[i] == nw - asz + i) i--;
                if (i < 0) break;
                idx[i]++;
                for (int j = i + 1; j < asz; j++) idx[j] = idx[j - 1] + 1;
            }
        }
        return;
    }
    /* Setting S */
    u64 U = 0, Q = 0, Y = 0;
    for (int v = 0; v < n; v++) {
        int d = PC(a[v]);
        if (d == n - 1) U |= 1ULL << v;
        if (d >= m) Q |= 1ULL << v; else Y |= 1ULL << v;
    }
    u64 P = Q & ~U;
    int u = PC(U), r = m - u + 1;
    /* Lemma G checks */
    for (u64 t = Q; t; t &= t - 1) { int q = CTZ(t); if ((a[q] | (1ULL << q)) & Q & ~(a[q] | (1ULL << q))) {} if ((Q & ~a[q] & ~(1ULL << q))) FAIL("%s: Q not a clique", tag); }
    if (!Y) FAIL("%s: Y empty", tag);
    if (u > m - 1) FAIL("%s: u > m-1", tag);
    for (u64 t = P; t; t &= t - 1) { int q = CTZ(t); if (PC(h[q]) < 2) FAIL("%s: P vertex with < 2 non-nbrs", tag); if (h[q] & ~Y) FAIL("%s: non-nbr outside Y", tag); }
    for (u64 t = Y; t; t &= t - 1) { int y = CTZ(t); if ((a[y] & U) != U) FAIL("%s: y misses U", tag); if (PC(a[y] & P) > r - 2) FAIL("%s: |A_y| > r-2", tag); }
    {   /* Fact A / T inside Q */
        int cntT = 0; for (int v = 0; v < n; v++) if (PC(a[v]) >= n - 1 - m) { cntT++; if (!((Q >> v) & 1)) FAIL("%s: T not in Q", tag); }
        if (cntT < (n + 1) / 2) FAIL("%s: |T| < ceil(n/2)", tag);
    }
    int ny = PC(Y);
    if (ny >= r) {
        st->caseid = 2;
        cctx c = { n, m, u, r, a, h, U, P, Y, Q, nodecap, st, tag };
        int yl[64]; int k = 0;
        for (u64 t = Y; t; t &= t - 1) yl[k++] = CTZ(t);
        double tot = binom(ny, r);
        vh_reset();
        if (tot <= rootcap) {
            int idx[64];
            for (int i = 0; i < r; i++) idx[i] = i;
            for (;;) {
                u64 R0 = 0;
                for (int i = 0; i < r; i++) R0 |= 1ULL << yl[idx[i]];
                explore(&c, 0, R0, 0);
                int i = r - 1;
                while (i >= 0 && idx[i] == ny - r + i) i--;
                if (i < 0) break;
                idx[i]++;
                for (int j = i + 1; j < r; j++) idx[j] = idx[j - 1] + 1;
            }
        } else {
            /* adversarial roots: (i) R0 = the r vertices of Y with most neighbours in P (greedy, ties random),
               (ii) R0 built to maximise the number of heavy q (greedy around each q in P), (iii) random. */
            long long tries = 0;
            /* (ii) for each q in P: take Y-neighbours of q first, then fill */
            for (u64 t = P; t && tries < rootcap; t &= t - 1, tries++) {
                int q = CTZ(t);
                u64 R0 = 0;
                u64 cand = a[q] & Y;
                while (cand && PC(R0) < r) { int pick; do pick = yl[rng() % ny]; while (!((cand >> pick) & 1)); R0 |= 1ULL << pick; cand &= ~(1ULL << pick); }
                while (PC(R0) < r) R0 |= 1ULL << yl[rng() % ny];
                explore(&c, 0, R0, 0);
            }
            /* (i) */
            for (int rep = 0; rep < 8 && tries < rootcap; rep++, tries++) {
                int sc[64]; for (int i = 0; i < ny; i++) sc[i] = PC(a[yl[i]] & P) * 64 + (int)(rng() % 64);
                u64 R0 = 0;
                for (int s = 0; s < r; s++) { int bi = -1; for (int i = 0; i < ny; i++) if (!((R0 >> yl[i]) & 1) && (bi < 0 || sc[i] > sc[bi])) bi = i; R0 |= 1ULL << yl[bi]; }
                explore(&c, 0, R0, 0);
            }
            while (tries < rootcap) {
                u64 R0 = 0; while (PC(R0) < r) R0 |= 1ULL << yl[rng() % ny];
                explore(&c, 0, R0, 0); tries++;
            }
        }
    } else {
        st->caseid = 3;
        int cc = m + 1 - u - ny;
        if (cc < 1) FAIL("%s: c < 1 in case 2b", tag);
        if (PC(P) < cc) { FAIL("%s: |P| < c", tag); return; }
        int pl[64], np = 0;
        for (u64 t = P; t; t &= t - 1) pl[np++] = CTZ(t);
        double tot = binom(np, cc);
        long long tries = tot <= rootcap ? (long long)tot : rootcap;
        int idx[64];
        for (int i = 0; i < cc; i++) idx[i] = i;
        for (long long t = 0; t < tries; t++) {
            u64 B0 = 0;
            if (tot <= rootcap) { for (int i = 0; i < cc; i++) B0 |= 1ULL << pl[idx[i]]; }
            else { while (PC(B0) < cc) B0 |= 1ULL << pl[rng() % np]; }
            u64 D = U | Y | B0;
            st->terminals++;
            if (PC(D) != m + 1 || !is_2dom(n, h, D)) FAIL("%s: Case 2b set fails", tag);
            if (tot <= rootcap) {
                int i = cc - 1;
                while (i >= 0 && idx[i] == np - cc + i) i--;
                if (i < 0) break;
                idx[i]++;
                for (int j = i + 1; j < cc; j++) idx[j] = idx[j - 1] + 1;
            }
        }
    }
}
#endif
