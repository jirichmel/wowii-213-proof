/* rnd.c: random, structured and annealed closed connected non-complete graphs, n <= 40 (up to 64 works).
   For each graph: the whole proof (Lemma J / Case 2a with adversarial exploration of Lemma 4 / Case 2b),
   every final set checked against the definition; greedy deep dives that try to make the loop of
   Lemma 4 run as many rounds as possible; for n <= NEX an exact gamma_2 (two methods for n <= 16).
   modes:
     closure  n trials seed      : random sparse connected graph, then Bondy-Chvatal (n-1)-closure
     hub      n trials seed      : designed hub family (Remark 5 shape, randomised), closure applied if needed
     anneal   n steps seed       : simulated annealing on closed graphs maximising the rounds of Lemma 4
     hyp      n trials seed      : random dense connected graphs with Hyp, Hamiltonian path checked (n <= 20)
   build: cc -O2 -o rnd rnd.c */
#include "core.h"
#include <math.h>

static int NEX = 18;          /* exact gamma_2 up to this n */
static long long ROOTCAP = 400, NODECAP = 200000;

static double urand(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }

static void add_edge(u64 *a, int x, int y) { if (x != y) { a[x] |= 1ULL << y; a[y] |= 1ULL << x; } }
static void del_edge(u64 *a, int x, int y) { a[x] &= ~(1ULL << y); a[y] &= ~(1ULL << x); }

/* (n-1)-closure: add ab while non-adjacent with d(a)+d(b) >= n-1 */
static void closure(int n, u64 *a) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++)
            if (!((a[x] >> y) & 1) && PC(a[x]) + PC(a[y]) >= n - 1) { add_edge(a, x, y); changed = 1; }
    }
}

/* greedy deep dives in Lemma 4: at every state pick the (q, R') that leaves the most heavy vertices */
static int dive_maxrounds;
static void greedy_dive(int n, const u64 *a, const u64 *h, int m, u64 U, u64 P, u64 R, int r, const char *tag) {
    u64 B = 0;
    for (;;) {
        int k = PC(R);
        int bestscore = -1; u64 bq = 0, bR = 0; int nties = 0;
        for (u64 p = P & ~B; p; p &= p - 1) {
            int q = CTZ(p);
            u64 S = a[q] & R;
            if (PC(S) < k - 1) continue;
            /* candidate R' */
            u64 cands[64]; int nc = 0;
            if (PC(S) == k - 1) cands[nc++] = S; else for (u64 t = S; t; t &= t - 1) cands[nc++] = S & ~(t & -t);
            for (int i = 0; i < nc; i++) {
                u64 B2 = B | (1ULL << q), R2 = cands[i];
                int sc = 0;
                for (u64 p2 = P & ~B2; p2; p2 &= p2 - 1) if (PC(a[CTZ(p2)] & R2) >= PC(R2) - 1) sc++;
                if (sc > bestscore) { bestscore = sc; bq = 1ULL << q; bR = R2; nties = 1; }
                else if (sc == bestscore && (rng() % (++nties)) == 0) { bq = 1ULL << q; bR = R2; }
            }
        }
        if (bestscore < 0) break;
        B |= bq; R = bR;
        if (PC(B) > r - 2) { FAIL("%s: dive exceeded r-2 rounds", tag); break; }
    }
    u64 D = U | B | R;
    if (PC(D) != m + 1 || !is_2dom(n, h, D)) FAIL("%s: dive set fails", tag);
    if (PC(B) > dive_maxrounds) dive_maxrounds = PC(B);
}

typedef struct { long long graphs, cases[4], terms, exact, slack[64], capped, allroots; int maxrounds, maxdive; } tot_t;
static tot_t T;

/* full treatment of one closed connected non-complete graph; returns max rounds seen */
static int treat(int n, u64 *a, const char *tag, int dives) {
    u64 h[64]; complement(n, a, h);
    if (!is_closed(n, a) || !is_connected(n, a) || is_complete(n, a)) { FAIL("%s: treat precondition", tag); return 0; }
    int m = lm_of(n, h);
    cstat st;
    run_proof(n, a, ROOTCAP, NODECAP, &st, tag);
    T.graphs++; T.cases[st.caseid]++; T.terms += st.terminals; if (st.capped) T.capped++;
    if (st.caseid == 2 && !st.capped) { /* were all roots enumerated? */
        int ny = 0, u = 0; for (int v = 0; v < n; v++) { if (PC(a[v]) < m) ny++; if (PC(a[v]) == n - 1) u++; }
        if (binom(ny, m - u + 1) <= ROOTCAP) T.allroots++;
    }
    int mr = st.maxrounds;
    if (st.caseid == 2 && dives > 0) {
        u64 U = 0, Q = 0, Y = 0;
        for (int v = 0; v < n; v++) { int d = PC(a[v]); if (d == n - 1) U |= 1ULL << v; if (d >= m) Q |= 1ULL << v; else Y |= 1ULL << v; }
        u64 P = Q & ~U; int r = m - PC(U) + 1;
        int yl[64], ny = 0; for (u64 t = Y; t; t &= t - 1) yl[ny++] = CTZ(t);
        dive_maxrounds = 0;
        for (int d = 0; d < dives; d++) {
            u64 R0 = 0;
            if (d % 2 == 0 && P) { /* start near a random q in P */
                int pl[64], np = 0; for (u64 t = P; t; t &= t - 1) pl[np++] = CTZ(t);
                int q = pl[rng() % np]; u64 cand = a[q] & Y;
                while (cand && PC(R0) < r) { int pk = yl[rng() % ny]; if ((cand >> pk) & 1) { R0 |= 1ULL << pk; cand &= ~(1ULL << pk); } }
            }
            while (PC(R0) < r) R0 |= 1ULL << yl[rng() % ny];
            greedy_dive(n, a, h, m, U, P, R0, r, tag);
        }
        if (dive_maxrounds > mr) mr = dive_maxrounds;
        if (dive_maxrounds > T.maxdive) T.maxdive = dive_maxrounds;
    }
    if (mr > T.maxrounds) T.maxrounds = mr;
    if (n <= NEX) {
        int g = g2_bb(n, h, m + 1);
        if (n <= 16) { int g2 = g2_exact_enum(n, h, m + 1); if (g != g2) FAIL("%s: gamma2 methods disagree %d %d", tag, g, g2); }
        if (g >= m + 2) FAIL("%s: exact gamma_2 >= lm+2 on a closed graph", tag);
        T.exact++; T.slack[g - m + 32]++;
    }
    if (st.caseid != 2) return -1;
    {   /* secondary score: number of P vertices that could be heavy for some root, and their excess */
        u64 Q = 0, Y = 0, U = 0;
        for (int v = 0; v < n; v++) { int d = PC(a[v]); if (d == n - 1) U |= 1ULL << v; if (d >= m) Q |= 1ULL << v; else Y |= 1ULL << v; }
        int r = m - PC(U) + 1, sec = 0, best = -100;
        for (u64 t = Q & ~U; t; t &= t - 1) { int x = PC(a[CTZ(t)] & Y) - (r - 1); if (x >= 0) sec += 10; if (x > best) best = x; }
        if (best < -50) best = -50;
        mr = 1000 * mr + sec + best;
    }
    return mr;
}

static int random_connected_sparse(int n, u64 *a, double p) {
    memset(a, 0, 64 * sizeof(u64));
    /* random spanning tree + extra edges */
    int perm[64]; for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rng() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 1; i < n; i++) add_edge(a, perm[i], perm[rng() % i]);
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (urand() < p) add_edge(a, x, y);
    return 1;
}

/* designed family: U universal, Q = U+P clique, hubs in P adjacent to all of W, other P see few of W,
   Z adjacent only to U (and maybe a few W), random sparse edges inside Y */
static void hub_graph(int n, u64 *a) {
    memset(a, 0, 64 * sizeof(u64));
    int u = rng() % 4, np = 2 + rng() % (n / 3), nhub = 1 + rng() % (np < 6 ? np : 6);
    if (u + np >= n - 2) np = n - 2 - u;
    if (nhub > np) nhub = np;
    int ny = n - u - np; int nw = 1 + rng() % ny;
    int Ul = 0, Pl = u, Yl = u + np, Wend = Yl + nw;
    for (int i = Ul; i < u; i++) for (int v = 0; v < n; v++) add_edge(a, i, v);
    for (int i = Pl; i < Yl; i++) for (int j = i + 1; j < Yl; j++) add_edge(a, i, j);
    for (int i = Pl; i < Pl + nhub; i++) for (int y = Yl; y < Wend; y++) if (urand() < 0.9) add_edge(a, i, y);
    int k = 1 + rng() % 3;
    for (int i = Pl + nhub; i < Yl; i++) for (int t = 0; t < k; t++) add_edge(a, i, Yl + rng() % nw);
    double py = urand() * 0.15;
    for (int x = Yl; x < n; x++) for (int y = x + 1; y < n; y++) if (urand() < py) add_edge(a, x, y);
    /* make sure Z vertices are attached */
    for (int z = Wend; z < n; z++) if (!a[z]) add_edge(a, z, u > 0 ? 0 : Pl + rng() % np);
    /* random relabelling */
    int perm[64]; for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rng() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    u64 b[64] = {0};
    for (int x = 0; x < n; x++) for (u64 t = a[x]; t; t &= t - 1) b[perm[x]] |= 1ULL << perm[CTZ(t)];
    memcpy(a, b, n * sizeof(u64));
}


/* Case-2a family: Q = U + P a clique of size >= ceil(n/2), Y the rest; P vertices see Y with
   per-vertex probabilities (a few hubs see most of Y); sparse edges in Y; then a down-repair that
   deletes Y-edges at violating pairs until the graph is closed. */
static int gen2a(int n, u64 *a) {
    memset(a, 0, 64 * sizeof(u64));
    int q = (n + 1) / 2 + rng() % (n / 2 - 1 > 0 ? n / 2 - 1 : 1);
    if (q > n - 2) q = n - 2;
    int u = rng() % 4; if (u > q - 2) u = 0;
    for (int i = 0; i < u; i++) for (int v = 0; v < n; v++) add_edge(a, i, v);
    for (int i = 0; i < q; i++) for (int j = i + 1; j < q; j++) add_edge(a, i, j);
    int nhub = rng() % 5;
    double plow = urand() * 0.3;
    for (int i = u; i < q; i++) {
        double p = (i < u + nhub) ? 0.5 + 0.5 * urand() : plow * urand();
        for (int y = q; y < n; y++) if (urand() < p) add_edge(a, i, y);
    }
    double py = urand() * 0.2;
    for (int x = q; x < n; x++) for (int y = x + 1; y < n; y++) if (urand() < py) add_edge(a, x, y);
    for (int y = q; y < n; y++) if (!a[y]) add_edge(a, y, rng() % q);
    for (int it = 0; it < 4 * n * n; it++) {
        int bx = -1, by = -1;
        for (int x = 0; x < n && bx < 0; x++) for (int y = x + 1; y < n; y++)
            if (!((a[x] >> y) & 1) && PC(a[x]) + PC(a[y]) >= n - 1) { bx = x; by = y; break; }
        if (bx < 0) break;
        /* delete an edge at the endpoint of lower degree, not to a vertex of index < u */
        int z = PC(a[bx]) <= PC(a[by]) ? bx : by;
        if (z < q) z = (z == bx) ? by : bx;
        u64 cand = a[z] & ~((1ULL << u) - 1);
        if (z < q) cand &= ~FULL(q);
        if (!cand) { int w = z == bx ? by : bx; cand = a[w] & ~((1ULL << u) - 1) & ~FULL(q); z = w; if (w < q && !cand) return 0; if (!cand) return 0; }
        int k = PC(cand), pick = rng() % k; u64 t = cand; while (pick--) t &= t - 1;
        del_edge(a, z, CTZ(t));
    }
    int perm[64]; for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rng() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    u64 b[64] = {0};
    for (int x = 0; x < n; x++) for (u64 t = a[x]; t; t &= t - 1) b[perm[x]] |= 1ULL << perm[CTZ(t)];
    memcpy(a, b, n * sizeof(u64));
    return is_closed(n, a) && is_connected(n, a) && !is_complete(n, a);
}


/* hub-chain family generalising Remark 5: U (u), k hubs adjacent to all of W, p further P vertices
   each adjacent to e random W vertices, Z adjacent only to U (or to one P vertex if u = 0).
   Sizes are random with total n. Returns 1 if closed, connected, non-complete. */
static int genhubk(int n, u64 *a) {
    memset(a, 0, 64 * sizeof(u64));
    int u = rng() % 4, k = 1 + rng() % (n / 3), w = 3 + rng() % (n / 2), z = rng() % (n / 4 + 1);
    int p = n - u - k - w - z;
    if (p < 0) return 0;
    int e = rng() % 4;
    int H0 = u, P0 = u + k, W0 = u + k + p, Z0 = W0 + w;
    for (int i = 0; i < u; i++) for (int v = 0; v < n; v++) add_edge(a, i, v);
    for (int i = 0; i < W0; i++) for (int j = i + 1; j < W0; j++) add_edge(a, i, j);
    for (int i = H0; i < P0; i++) for (int y = W0; y < Z0; y++) add_edge(a, i, y);
    for (int i = P0; i < W0; i++) for (int t = 0; t < e; t++) add_edge(a, i, W0 + rng() % w);
    for (int y = Z0; y < n; y++) if (u == 0) add_edge(a, y, (p > 0 ? P0 + rng() % p : H0));
    if (rng() % 2) { double py = urand() * 0.1; for (int x = W0; x < n; x++) for (int y = x + 1; y < n; y++) if (urand() < py) add_edge(a, x, y); }
    int perm[64]; for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rng() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    u64 b[64] = {0};
    for (int x = 0; x < n; x++) for (u64 t = a[x]; t; t &= t - 1) b[perm[x]] |= 1ULL << perm[CTZ(t)];
    memcpy(a, b, n * sizeof(u64));
    return is_closed(n, a) && is_connected(n, a) && !is_complete(n, a);
}

static void report(const char *mode, int n) {
    printf("%s n=%d: graphs=%lld cases J=%lld 2a=%lld 2b=%lld terminal_sets=%lld max_rounds=%d (dives %d) exact=%lld slack:",
           mode, n, T.graphs, T.cases[1], T.cases[2], T.cases[3], T.terms, T.maxrounds, T.maxdive, T.exact);
    for (int s = 0; s < 64; s++) if (T.slack[s]) printf(" [%d]=%lld", s - 32, T.slack[s]);
    printf(" case2a_capped=%lld case2a_fully_explored=%lld failures=%lld\n", T.capped, T.allroots, g_fail);
    fflush(stdout);
}

int main(int argc, char **argv) {
    const char *mode = argv[1];
    int n = atoi(argv[2]); long long trials = atoll(argv[3]);
    rng_s = 0x9E3779B97F4A7C15ULL ^ (u64)atoll(argv[4]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rng();
    if (argc > 5) NEX = atoi(argv[5]);
    char tag[96];
    if (!strcmp(mode, "closure") || !strcmp(mode, "hub") || !strcmp(mode, "c2a") || !strcmp(mode, "hubk")) {
        long long tried = 0;
        while (T.graphs < trials && tried < trials * 200) {
            tried++;
            u64 a[64];
            if (!strcmp(mode, "closure")) random_connected_sparse(n, a, urand() * 3.0 / n);
            else if (!strcmp(mode, "hub")) hub_graph(n, a);
            else if (!strcmp(mode, "hubk")) { if (!genhubk(n, a)) continue; }
            else if (!gen2a(n, a)) continue;
            if (!is_connected(n, a)) continue;
            if (!is_closed(n, a)) closure(n, a);
            if (is_complete(n, a)) continue;
            snprintf(tag, sizeof tag, "%s n=%d #%lld", mode, n, tried);
            treat(n, a, tag, 20);
        }
        report(mode, n);
    } else if (!strcmp(mode, "anneal")) {
        /* start from a hub graph that is closed */
        u64 a[64];
        { int ok = 0; u64 h0[64];
          for (int tries = 0; tries < 1000000 && !ok; tries++) { if (!(tries % 2 ? gen2a(n, a) : genhubk(n, a))) continue; complement(n, a, h0); ok = (2 * lm_of(n, h0) <= n - 1); }
          if (!ok) { printf("anneal: no Case-2 start found\n"); return 1; }
          /* best of 300 hub-chain starts by score */
          int bestsc = -1000000; u64 bb[64]; memcpy(bb, a, sizeof bb);
          for (int t = 0, got = 0; t < 200000 && got < 300; t++) {
              u64 c[64]; if (!genhubk(n, c)) continue; complement(n, c, h0); if (2 * lm_of(n, h0) > n - 1) continue;
              got++; ROOTCAP = 30; NODECAP = 5000; int sc = treat(n, c, "anneal-start", 10);
              if (sc > bestsc) { bestsc = sc; memcpy(bb, c, sizeof bb); }
          }
          memcpy(a, bb, sizeof bb); printf("  anneal start score %d\n", bestsc); }
        ROOTCAP = 60; NODECAP = 20000;
        snprintf(tag, sizeof tag, "anneal n=%d start", n);
        int cur = treat(n, a, tag, 30), best = cur;
        double temp = 1.0;
        for (long long s = 0; s < trials; s++) {
            u64 b[64]; memcpy(b, a, sizeof b);
            int nt = 1 + rng() % 3;
            u64 hb[64]; complement(n, b, hb); int mb = lm_of(n, hb); u64 Yb = 0;
            for (int v = 0; v < n; v++) if (PC(b[v]) < mb) Yb |= 1ULL << v;
            for (int t = 0; t < nt; t++) {
                int x = rng() % n, y = rng() % n;
                if (Yb && rng() % 10 < 8) { int k = PC(Yb), pk = rng() % k; u64 tt = Yb; while (pk--) tt &= tt - 1; y = CTZ(tt); }
                if (x == y) continue; if ((b[x] >> y) & 1) del_edge(b, x, y); else add_edge(b, x, y); }
            if (!is_connected(n, b)) continue;
            if (!is_closed(n, b)) { if (rng() % 2) closure(n, b); else continue; }
            if (is_complete(n, b) || !is_closed(n, b)) continue;
            snprintf(tag, sizeof tag, "anneal n=%d step %lld", n, s);
            int val = treat(n, b, tag, 30);
            if (val >= cur || urand() < exp((val - cur) / (20.0 * temp))) { memcpy(a, b, sizeof b); cur = val; }
            if (val / 1000 > best / 1000) { printf("  step %lld: new max rounds %d (score %d)\n", s, val / 1000, val); fflush(stdout); }
            if (val > best) best = val;
            temp = 1.0 * (1 - (double)s / trials) + 0.05;
        }
        report(mode, n);
    } else if (!strcmp(mode, "named")) {
        /* Remark 5 graph (n = 26) with my own choice of the two W-neighbours of each P' vertex, and the
           Remark 4 tie-break graph (n = 16). Every root R0 and every choice explored (no cap). */
        ROOTCAP = 1LL << 40; NODECAP = 1LL << 40;
        for (int variant = 0; variant < (int)trials; variant++) {
            u64 a[64] = {0}; int nn = 26;
            for (int i = 0; i < 2; i++) for (int v = 0; v < nn; v++) add_edge(a, i, v);
            for (int i = 0; i <= 12; i++) for (int j = i + 1; j <= 12; j++) add_edge(a, i, j);
            for (int hb = 2; hb <= 4; hb++) for (int w = 16; w <= 25; w++) add_edge(a, hb, w);
            for (int p = 5; p <= 12; p++) {
                int w1, w2;
                if (variant == 0) { w1 = 16 + (2 * (p - 5)) % 10; w2 = 16 + (2 * (p - 5) + 1) % 10; }
                else { w1 = 16 + rng() % 10; do w2 = 16 + rng() % 10; while (w2 == w1); }
                add_edge(a, p, w1); add_edge(a, p, w2);
            }
            u64 h[64]; complement(nn, a, h);
            printf("named26 variant %d: closed=%d connected=%d m=%d\n", variant, is_closed(nn, a), is_connected(nn, a), lm_of(nn, h));
            if (!is_closed(nn, a)) continue;
            snprintf(tag, sizeof tag, "named26 v%d", variant);
            int mr = treat(nn, a, tag, 200);
            printf("  max rounds over all roots and choices = %d\n", mr);
        }
        {
            u64 a[64] = {0}; int nn = 16;
            for (int i = 0; i < 4; i++) for (int v = 0; v < nn; v++) add_edge(a, i, v);
            for (int i = 0; i <= 7; i++) for (int j = i + 1; j <= 7; j++) add_edge(a, i, j);
            for (int i = 0; i < 4; i++) { add_edge(a, 8 + 2 * i, 4 + i); add_edge(a, 9 + 2 * i, 4 + i); }
            u64 h[64]; complement(nn, a, h);
            printf("tiebreak16: closed=%d connected=%d m=%d\n", is_closed(nn, a), is_connected(nn, a), lm_of(nn, h));
            int mr = treat(nn, a, "tiebreak16", 200);
            printf("  max rounds = %d\n", mr);
        }
        report(mode, 0);
    } else if (!strcmp(mode, "hyp")) {
        long long hyp = 0, tested = 0;
        for (long long t = 0; t < trials; t++) {
            u64 a[64] = {0};
            double p = 0.5 + 0.5 * urand();
            for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (urand() < p) add_edge(a, x, y);
            if (!is_connected(n, a)) continue;
            tested++;
            u64 h[64]; complement(n, a, h);
            int m = lm_of(n, h);
            if (g2_bb(n, h, m + 1) < m + 2) continue;
            hyp++;
            int hp = hp_dp(n, a);
            if (hp != hp_dfs(n, a)) FAIL("hyp: HP methods disagree");
            if (!hp) FAIL("COUNTEREXAMPLE to 213 (random) n=%d", n);
        }
        printf("hyp n=%d: connected tested=%lld with Hyp=%lld (all had a Hamiltonian path unless FAIL above) failures=%lld\n", n, tested, hyp, g_fail);
    }
    return g_fail ? 1 : 0;
}
