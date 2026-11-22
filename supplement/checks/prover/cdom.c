/* cdom.c -- test of the proof of Claim C (prover-claimC, 21 November 2026).
 *
 * Claim tested: for every closed, connected, non-complete graph G on n vertices, with
 * H its complement and m = lm(H), the set D built in proof.md has |D| <= m+1 and
 * 2-dominates H.  Hence gamma_2(H) <= lm(H)+1 and Hyp fails.
 *
 * Construction (proof.md):
 *   case J  (2m >= n):  D = V \ A, A = any n-m-1 vertices with d_H >= m.
 *   case B  (2m <= n-1, |Y| < r): then u = 0, |Y| = m, D = Y + one vertex of Q.
 *   case A  (2m <= n-1, |Y| >= r): R = any r vertices of Y, B = {}; while some q in P\B
 *           has >= |R|-1 neighbours in R: B += q, R = any |R|-1 vertices of N(q) n R.
 *           D = U u B u R.
 * "any" is tested with the first choice and with K random choices per graph.
 * Steps of the proof that are asserted on the way: Q is a clique, Y nonempty, u <= m-1,
 * |Y| >= m, the invariants of the loop, |B| <= r-2 at the end, |D| = m+1.
 *
 * Modes:
 *   cdom lab N K           all labelled graphs on N <= 8 vertices
 *   cdom iso NMAX K        all graphs up to isomorphism, NMAX <= 10 (uses tools/lib/smallgraph.h)
 *   cdom rnd N S K SEED    S samples of a Markov chain on closed connected non-complete graphs
 *   cdom shape N S K SEED  S samples: Theorem-G-shaped random graph, then its (n-1)-closure
 *   cdom anneal N S K SEED S steps of a walk on closed graphs favouring long runs of the loop
 *   cdom hub N S K SEED    S samples of a hub family built so that the loop must run
 * Build: cc -O2 -I. -o cdom cdom.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "smallgraph.h"

typedef uint64_t u64;
#define MAXN 64
#define POP(x) __builtin_popcountll(x)
#define BIT(i) (1ULL << (i))

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27; return rs * 2685821657736338717ULL; }
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static u64 allmask(int n) { return n == 64 ? ~0ULL : (BIT(n) - 1); }

/* choose a random subset of size k of mask (k <= POP(mask)); first k bits if !randomize */
static u64 pick(u64 mask, int k, int randomize) {
    int c = POP(mask), idx[MAXN], t = 0;
    for (u64 x = mask; x; x &= x - 1) idx[t++] = __builtin_ctzll(x);
    if (randomize) for (int i = c - 1; i > 0; i--) { int j = rndint(i + 1); int s = idx[i]; idx[i] = idx[j]; idx[j] = s; }
    u64 r = 0; for (int i = 0; i < k; i++) r |= BIT(idx[i]);
    return r;
}

static int connected(int n, const u64 *adj) {
    u64 seen = 1, frontier = 1;
    while (frontier) { u64 nf = 0; for (u64 x = frontier; x; x &= x - 1) nf |= adj[__builtin_ctzll(x)]; frontier = nf & ~seen; seen |= nf; }
    return seen == allmask(n);
}
static int closed(int n, const u64 *adj) {
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
        if (!((adj[a] >> b) & 1) && POP(adj[a]) + POP(adj[b]) > n - 2) return 0;
    return 1;
}
static int complete(int n, const u64 *adj) { for (int v = 0; v < n; v++) if (POP(adj[v]) != n - 1) return 0; return 1; }
static int cmpint(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }
static int lmH(int n, const u64 *adj) {
    int h[MAXN]; for (int v = 0; v < n; v++) h[v] = n - 1 - POP(adj[v]);
    qsort(h, n, sizeof(int), cmpint);
    return h[(n + 1) / 2 - 1];          /* ceil(n/2)-th smallest */
}
static int twodom(int n, const u64 *adj, u64 D) {
    for (int v = 0; v < n; v++) {
        if ((D >> v) & 1) continue;
        u64 hn = allmask(n) & ~adj[v] & ~BIT(v);
        if (POP(hn & D) < 2) return 0;
    }
    return 1;
}
static void printgraph(int n, const u64 *adj) {
    printf("n=%d edges:", n);
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if ((adj[a] >> b) & 1) printf(" %d-%d", a, b);
    printf("\n");
}

/* statistics */
static long long st_graphs, st_caseJ, st_caseA, st_caseB, st_runs, st_fail, st_assert;
static long long st_steps[MAXN + 1];      /* histogram of loop steps (|B| at the end), case A */
static long long st_hyprange;
static int last_B = -1, last_case = 0, last_hyp = 0;   /* outcome of the last run (anneal mode) */             /* case A graphs with |Y| >= m+2 (the range left open by Lemma K) */

static void fail(const char *what, int n, const u64 *adj, u64 D) {
    st_fail++;
    if (st_fail <= 10) { printf("FAIL (%s) D=%llx ", what, (unsigned long long)D); printgraph(n, adj); }
}

/* one run of the construction; returns 1 if everything holds */
static int run(int n, const u64 *adj, int randomize, int count_case) {
    int m = lmH(n, adj), d[MAXN];
    for (int v = 0; v < n; v++) d[v] = POP(adj[v]);
    u64 all = allmask(n), D = 0;
    if (2 * m >= n) {
        if (count_case) st_caseJ++;
        u64 cand = 0; for (int v = 0; v < n; v++) if (n - 1 - d[v] >= m) cand |= BIT(v);
        int need = n - m - 1;
        if (need < 0 || POP(cand) < need) { st_assert++; fail("J: too few candidates", n, adj, 0); return 0; }
        D = all & ~pick(cand, need, randomize);
    } else {
        u64 Q = 0, U = 0;
        for (int v = 0; v < n; v++) { if (d[v] >= m) Q |= BIT(v); if (d[v] == n - 1) U |= BIT(v); }
        u64 Y = all & ~Q, P = Q & ~U;
        for (u64 x = Q; x; x &= x - 1) { int q = __builtin_ctzll(x); if (((adj[q] | BIT(q)) & Q) != Q) { st_assert++; fail("Q not a clique", n, adj, 0); return 0; } }
        if (!Y) { st_assert++; fail("Y empty", n, adj, 0); return 0; }
        int u = POP(U), r = m - u + 1;
        if (u > m - 1) { st_assert++; fail("u > m-1", n, adj, 0); return 0; }
        if (POP(Y) < m) { st_assert++; fail("|Y| < m", n, adj, 0); return 0; }
        if (POP(Y) < r) {
            if (count_case) st_caseB++;
            if (!(u == 0 && POP(Y) == m)) { st_assert++; fail("case B shape", n, adj, 0); return 0; }
            D = Y | pick(Q, 1, randomize);
        } else {
            if (count_case) { st_caseA++; if (POP(Y) >= m + 2) st_hyprange++; }
            u64 R = pick(Y, r, randomize), B = 0;
            for (;;) {
                /* invariants: |R| = r - |B|, every y in R adjacent to all of B, |B| <= r-2 */
                if (POP(R) != r - POP(B)) { st_assert++; fail("inv |R|", n, adj, 0); return 0; }
                for (u64 x = R; x; x &= x - 1) { int y = __builtin_ctzll(x); if ((adj[y] & B) != B) { st_assert++; fail("inv R in common nbhd", n, adj, 0); return 0; } }
                if (POP(B) > r - 2) { st_assert++; fail("inv |B| <= r-2", n, adj, 0); return 0; }
                u64 cand = 0;
                for (u64 x = P & ~B; x; x &= x - 1) { int q = __builtin_ctzll(x); if (POP(adj[q] & R) >= POP(R) - 1) cand |= BIT(q); }
                if (!cand) break;
                int q = __builtin_ctzll(pick(cand, 1, randomize));
                B |= BIT(q);
                R = pick(adj[q] & R, POP(R) - 1, randomize);
            }
            if (count_case) st_steps[POP(B)]++;
            last_B = POP(B); last_case = 'A'; last_hyp = POP(Y) >= m + 2;
            D = U | B | R;
            if (POP(D) != m + 1) { st_assert++; fail("|D| != m+1", n, adj, D); return 0; }
        }
    }
    st_runs++;
    if (POP(D) > m + 1) { fail("|D| > m+1", n, adj, D); return 0; }
    if (!twodom(n, adj, D)) { fail("D not 2-dominating in H", n, adj, D); return 0; }
    return 1;
}

static int K = 1;
static void test_graph(int n, const u64 *adj) {
    for (int a = 0; a < n; a++) { if ((adj[a] >> a) & 1) { printf("loop at %d\n", a); exit(3); } if (adj[a] & ~allmask(n)) { printf("bit beyond n\n"); exit(3); }
        for (int b = 0; b < n; b++) if (((adj[a] >> b) & 1) != ((adj[b] >> a) & 1)) { printf("asymmetric adjacency %d %d\n", a, b); exit(3); } }
    st_graphs++;
    run(n, adj, 0, 1);
    for (int k = 0; k < K; k++) run(n, adj, 1, 0);
}

static void report(const char *tag) {
    printf("%s: graphs %lld (case J %lld, case A %lld [|Y|>=m+2: %lld], case B %lld), runs %lld, failures %lld (assertion failures %lld)\n",
           tag, st_graphs, st_caseJ, st_caseA, st_hyprange, st_caseB, st_runs, st_fail, st_assert);
    printf("  case A, |B| at the end (first-choice run):");
    for (int i = 0; i <= MAXN; i++) if (st_steps[i]) printf(" %d:%lld", i, st_steps[i]);
    printf("\n");
    fflush(stdout);
}
static void reset(void) { st_graphs = st_caseJ = st_caseA = st_caseB = st_runs = st_fail = st_assert = st_hyprange = 0; memset(st_steps, 0, sizeof st_steps); }

/* ---- mode lab: all labelled graphs, Gray code over the edge set */
static void mode_lab(int n) {
    int E = n * (n - 1) / 2, ea[64], eb[64], t = 0;
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) { ea[t] = a; eb[t] = b; t++; }
    u64 adj[MAXN]; memset(adj, 0, sizeof adj);
    long long cnt = 0;
    for (u64 i = 0; i < (1ULL << E); i++) {
        if (i) { int e = __builtin_ctzll(i); adj[ea[e]] ^= BIT(eb[e]); adj[eb[e]] ^= BIT(ea[e]); }
        if (!closed(n, adj) || complete(n, adj) || !connected(n, adj)) continue;
        cnt++; test_graph(n, adj);
    }
    char tag[64]; sprintf(tag, "lab n=%d (labelled closed connected non-complete: %lld)", n, cnt);
    report(tag);
}

/* ---- mode iso: all graphs up to isomorphism via smallgraph.h */
static long long iso_cnt[SG_MAXN + 1];
static void visit_iso(int n, const unsigned *a, void *ctx) {
    (void)ctx; if (n < 2) return;
    u64 adj[MAXN]; for (int v = 0; v < n; v++) adj[v] = a[v];
    if (!closed(n, adj) || complete(n, adj) || !connected(n, adj)) return;
    iso_cnt[n]++; test_graph(n, adj);
}
static void mode_iso(int nmax) {
    sg_all_graphs(nmax, visit_iso, NULL);
    printf("iso: closed connected non-complete graphs up to isomorphism:");
    for (int n = 2; n <= nmax; n++) printf(" n=%d:%lld", n, iso_cnt[n]);
    printf("\n");
    report("iso");
}

/* ---- mode rnd: Markov chain on closed connected non-complete graphs, start = star */
static void mode_rnd(int n, long long S) {
    u64 adj[MAXN]; memset(adj, 0, sizeof adj);
    for (int v = 1; v < n; v++) { adj[0] |= BIT(v); adj[v] |= BIT(0); }
    for (long long s = 0; s < S; s++) {
        double p = (double)(rnd64() % 1000) / 1000.0;     /* target: add with prob p */
        int steps = 20 + rndint(4 * n);
        for (int it = 0; it < steps; it++) {
            int a = rndint(n), b = rndint(n); if (a == b) continue;
            int isedge = (adj[a] >> b) & 1;
            double coin = (double)(rnd64() % 1000) / 1000.0;
            if (isedge && coin < p) continue;           /* keep edges with prob p */
            if (!isedge && coin >= p) continue;
            adj[a] ^= BIT(b); adj[b] ^= BIT(a);
            if (!closed(n, adj) || complete(n, adj) || !connected(n, adj)) { adj[a] ^= BIT(b); adj[b] ^= BIT(a); }
        }
        test_graph(n, adj);
    }
    char tag[64]; sprintf(tag, "rnd n=%d", n); report(tag);
}

/* ---- mode shape: random graph of Theorem G shape, then the (n-1)-closure */
static void closure(int n, u64 *adj) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
            if (!((adj[a] >> b) & 1) && POP(adj[a]) + POP(adj[b]) >= n - 1) { adj[a] |= BIT(b); adj[b] |= BIT(a); changed = 1; }
    }
}
static void mode_shape(int n, long long S) {
    long long kept = 0;
    for (long long s = 0; s < S; s++) {
        u64 adj[MAXN]; memset(adj, 0, sizeof adj);
        int k = (n + 1) / 2 + rndint(n - (n + 1) / 2 - 1);  /* |Q| in [ceil(n/2), n-2] */
        int u = rndint(k / 2 + 1);                         /* universal part of Q */
        int maxextra = 1 + rndint(n / 3 + 1);
        int conc = 1 + rndint(k - u > 0 ? k - u : 1);      /* concentration: P-neighbours drawn from a pool */
        int pool[MAXN], np = 0;
        for (int q = u; q < k; q++) pool[np++] = q;
        for (int i = np - 1; i > 0; i--) { int j = rndint(i + 1); int t = pool[i]; pool[i] = pool[j]; pool[j] = t; }
        if (conc > np) conc = np;
        for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) { adj[a] |= BIT(b); adj[b] |= BIT(a); }
        for (int y = k; y < n; y++) for (int a = 0; a < u; a++) { adj[a] |= BIT(y); adj[y] |= BIT(a); }
        double pY = (double)(rnd64() % 1000) / 1000.0;
        for (int y = k; y < n; y++) {
            int t = rndint(maxextra + 1);
            for (int i = 0; i < t; i++) {
                int w;
                if ((double)(rnd64() % 1000) / 1000.0 < pY || conc == 0) w = k + rndint(n - k); else w = pool[rndint(conc)];
                if (w != y) { adj[y] |= BIT(w); adj[w] |= BIT(y); }
            }
        }
        if (u == 0) { /* make it connected: attach isolated Y vertices to a random Q vertex */
            for (int y = k; y < n; y++) if (!adj[y]) { int q = rndint(k); adj[y] |= BIT(q); adj[q] |= BIT(y); }
        }
        closure(n, adj);
        if (complete(n, adj) || !connected(n, adj)) continue;
        if (!closed(n, adj)) { st_assert++; printf("closure not closed?\n"); continue; }
        kept++; test_graph(n, adj);
    }
    char tag[96]; sprintf(tag, "shape n=%d (kept %lld of %lld)", n, kept, S); report(tag);
}


/* ---- mode anneal: walk on closed connected non-complete graphs that favours long runs of the loop */
static double score(int n, const u64 *adj) {
    double s = 0;
    for (int k = 0; k < 4; k++) { last_B = -1; last_case = 0; last_hyp = 0; run(n, adj, 1, 0); if (last_case == 'A') s += 1 + last_B + 0.5 * last_hyp; }
    return s;
}
static void mode_anneal(int n, long long S) {
    u64 adj[MAXN]; memset(adj, 0, sizeof adj);
    /* start: tie-break-like graph: U = {0..u-1}, Q = {0..k-1} clique, Y = rest, y adjacent to U and one P vertex */
    int k = (n + 1) / 2, u = 2 + rndint(3); if (u > k - 1) u = k - 1;
    for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) { adj[a] |= BIT(b); adj[b] |= BIT(a); }
    for (int y = k; y < n; y++) { for (int a = 0; a < u; a++) { adj[a] |= BIT(y); adj[y] |= BIT(a); } int q = u + (y - k) % (k - u); adj[q] |= BIT(y); adj[y] |= BIT(q); }
    for (int a = 0; a < u; a++) for (int b = 0; b < n; b++) if (a != b) { adj[a] |= BIT(b); adj[b] |= BIT(a); }
    if (!closed(n, adj) || complete(n, adj) || !connected(n, adj)) { printf("anneal: start graph not closed, restart from star\n"); memset(adj, 0, sizeof adj); for (int v = 1; v < n; v++) { adj[0] |= BIT(v); adj[v] |= BIT(0); } }
    double cur = score(n, adj), best = cur; long long hist[MAXN + 1]; memset(hist, 0, sizeof hist);
    for (long long s = 0; s < S; s++) {
        int a = rndint(n), b = rndint(n); if (a == b) continue;
        adj[a] ^= BIT(b); adj[b] ^= BIT(a);
        if (!closed(n, adj) || complete(n, adj) || !connected(n, adj)) { adj[a] ^= BIT(b); adj[b] ^= BIT(a); continue; }
        test_graph(n, adj);
        double nw = score(n, adj); { int mm = lmH(n, adj); if (2 * mm >= n) nw -= 0.5 * (2 * mm - n + 1); }
        if (nw >= cur || (double)(rnd64() % 100000) / 100000.0 < __builtin_exp((nw - cur) / 0.7)) { cur = nw; if (cur > best) best = cur; }
        else { adj[a] ^= BIT(b); adj[b] ^= BIT(a); }
    }
    char tag[96]; sprintf(tag, "anneal n=%d steps=%lld best score %.1f", n, S, best); report(tag);
}

/* ---- mode hub: U universal, hubs S adjacent to all of W, Z adjacent to U only (+ few),
 * P' with a few W-neighbours, sparse edges in Y; random relabelling; keep if closed.
 * Built so that the loop of case A must take |S| steps when R falls in W. */
static void mode_hub(int n, long long S) {
    long long kept = 0;
    for (long long s = 0; s < S; s++) {
        int u = rndint(4), h = 1 + rndint(5), z = u + 1 + rndint(3);
        int rest = n - u - h - z; if (rest < 4) continue;
        int w = 2 + rndint(rest - 2 + 1 > 1 ? rest - 2 : 1); int pp = n - u - h - z - w; if (pp < 0) continue;
        /* index layout before relabelling: U [0,u), S [u,u+h), P' [u+h, u+h+pp), Z, W */
        int oU = 0, oS = u, oP = u + h, oZ = u + h + pp, oW = oZ + z; (void)oU;
        u64 adj[MAXN]; memset(adj, 0, sizeof adj);
#define ED(a,b) do { int _a = (a), _b = (b); if (_a != _b) { adj[_a] |= BIT(_b); adj[_b] |= BIT(_a); } } while (0)
        for (int a = 0; a < oZ; a++) for (int b = a + 1; b < oZ; b++) ED(a, b);      /* Q clique */
        for (int a = 0; a < u; a++) for (int b = 0; b < n; b++) ED(a, b);               /* U universal */
        for (int a = oS; a < oP; a++) for (int b = oW; b < n; b++) ED(a, b);            /* hubs see W */
        int pw = rndint(4);                                                              /* P'-W degree */
        for (int a = oP; a < oZ; a++) for (int i = 0; i < pw; i++) ED(a, oW + rndint(w));
        int zp = rndint(2);                                                              /* Z extra nbrs */
        for (int a = oZ; a < oW; a++) for (int i = 0; i < zp; i++) if (pp) ED(a, oP + rndint(pp));
        int yy = rndint(3);                                                              /* Y-Y edges */
        for (int i = 0; i < yy; i++) ED(oZ + rndint(n - oZ), oZ + rndint(n - oZ));
#undef ED
        if (u == 0) for (int a = oZ; a < n; a++) if (!adj[a]) { int q = rndint(oZ); adj[a] |= BIT(q); adj[q] |= BIT(a); }
        if (!closed(n, adj) || complete(n, adj) || !connected(n, adj)) continue;
        /* random relabelling */
        int perm[MAXN]; for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) { int j = rndint(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        u64 b2[MAXN]; memset(b2, 0, sizeof b2);
        for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if ((adj[a] >> b) & 1) b2[perm[a]] |= BIT(perm[b]);
        kept++; test_graph(n, b2);
    }
    char tag[96]; sprintf(tag, "hub n=%d (kept %lld of %lld)", n, kept, S); report(tag);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 1; }
    const char *mode = argv[1];
    if (!strcmp(mode, "lab")) { int n = atoi(argv[2]); K = argc > 3 ? atoi(argv[3]) : 1; if (n > 8) return 1; mode_lab(n); }
    else if (!strcmp(mode, "iso")) { int n = atoi(argv[2]); K = argc > 3 ? atoi(argv[3]) : 1; if (n > 10) return 1; mode_iso(n); }
    else if (!strcmp(mode, "rnd") || !strcmp(mode, "shape") || !strcmp(mode, "anneal") || !strcmp(mode, "hub")) {
        int n = atoi(argv[2]); long long S = atoll(argv[3]); K = atoi(argv[4]); rs ^= (u64)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
        if (n < 4 || n > 64) return 1;
        if (!strcmp(mode, "rnd")) mode_rnd(n, S); else if (!strcmp(mode, "shape")) mode_shape(n, S); else if (!strcmp(mode, "hub")) mode_hub(n, S); else mode_anneal(n, S);
    }
    return st_fail ? 2 : 0;
}
