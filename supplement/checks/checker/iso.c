/* iso.c: all connected graphs on n <= 10 vertices up to isomorphism, by my own generator
   (vertex addition: the new vertex is a non-cut vertex of minimum degree among non-cut vertices;
   duplicates removed by a canonical form = minimum adjacency code over an individualisation-refinement
   tree, pruned only by twin transpositions, which are automorphisms fixing the current partition).
   Work at the last level is split across processes by an isomorphism invariant (degree data), so
   each isomorphism class is handled by exactly one process.
   Per graph: Hyp (gamma_2(H) >= lm(H)+2) and Hamiltonian path (DFS, and DP as second method);
   for closed non-complete graphs: exact gamma_2 by two methods and the proof's construction with
   every choice explored.
   usage: iso NMAX [part nparts]   build: cc -O2 -o iso iso.c */
#include "core.h"

static int N_;
/* ---------- canonical form ---------- */
static u64 best_code; static int have_best;
static void refine(int n, const u64 *a, int *lab, int *cst, int *nc) {
restart:
    for (int s = 0; s < *nc; s++) {
        u64 mask = 0;
        int s0 = cst[s], s1 = (s + 1 < *nc) ? cst[s + 1] : n;
        for (int i = s0; i < s1; i++) mask |= 1ULL << lab[i];
        for (int c = 0; c < *nc; c++) {
            int c0 = cst[c], c1 = (c + 1 < *nc) ? cst[c + 1] : n;
            if (c1 - c0 < 2) continue;
            int key[64], diff = 0;
            for (int i = c0; i < c1; i++) { key[i] = PC(a[lab[i]] & mask); if (key[i] != key[c0]) diff = 1; }
            if (!diff) continue;
            for (int i = c0 + 1; i < c1; i++) { /* insertion sort by key */
                int kv = key[i], lv = lab[i], j = i - 1;
                while (j >= c0 && key[j] > kv) { key[j + 1] = key[j]; lab[j + 1] = lab[j]; j--; }
                key[j + 1] = kv; lab[j + 1] = lv;
            }
            /* split: new cell starts where key changes */
            int newst[64], nn = 0;
            for (int i = c0 + 1; i < c1; i++) if (key[i] != key[i - 1]) newst[nn++] = i;
            /* insert newst after cell c */
            for (int t = *nc - 1; t > c; t--) cst[t + nn] = cst[t];
            for (int t = 0; t < nn; t++) cst[c + 1 + t] = newst[t];
            *nc += nn;
            goto restart;
        }
    }
}
static void canon_rec(int n, const u64 *a, int *lab0, int *cst0, int nc0) {
    int lab[64], cst[64], nc = nc0;
    memcpy(lab, lab0, n * sizeof(int)); memcpy(cst, cst0, nc0 * sizeof(int));
    refine(n, a, lab, cst, &nc);
    if (nc == n) {
        u64 code = 0;
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) code = (code << 1) | ((a[lab[i]] >> lab[j]) & 1);
        if (!have_best || code < best_code) { best_code = code; have_best = 1; }
        return;
    }
    int c = 0;
    while (((c + 1 < nc) ? cst[c + 1] : n) - cst[c] < 2) c++;
    int c0 = cst[c], c1 = (c + 1 < nc) ? cst[c + 1] : n;
    int tried[64], nt = 0;
    for (int i = c0; i < c1; i++) {
        int v = lab[i], skip = 0;
        for (int t = 0; t < nt; t++) { int w = tried[t]; if ((a[v] & ~(1ULL << w)) == (a[w] & ~(1ULL << v))) { skip = 1; break; } }
        if (skip) continue;
        tried[nt++] = v;
        int lab2[64], cst2[64];
        memcpy(lab2, lab, n * sizeof(int));
        /* move v to position c0 */
        for (int j = i; j > c0; j--) lab2[j] = lab2[j - 1];
        lab2[c0] = v;
        for (int t = 0; t <= c; t++) cst2[t] = cst[t];
        cst2[c + 1] = c0 + 1;
        for (int t = c + 1; t < nc; t++) cst2[t + 1] = cst[t];
        canon_rec(n, a, lab2, cst2, nc + 1);
    }
}
static u64 canon(int n, const u64 *a) {
    int lab[64], cst[1] = {0};
    for (int i = 0; i < n; i++) lab[i] = i;
    have_best = 0;
    canon_rec(n, a, lab, cst, 1);
    return best_code;
}
static void decode(int n, u64 code, u64 *a) {
    int E = n * (n - 1) / 2, b = E - 1;
    for (int i = 0; i < n; i++) a[i] = 0;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++, b--) if ((code >> b) & 1) { a[i] |= 1ULL << j; a[j] |= 1ULL << i; }
}
/* ---------- hash set ---------- */
#define HB 25
static u64 *hs; static long long hcount;
static int hs_insert(u64 key) {
    key += 1;
    u64 x = key * 0x9E3779B97F4A7C15ULL;
    size_t i = x >> (64 - HB);
    while (hs[i]) { if (hs[i] == key) return 0; i = (i + 1) & ((1ULL << HB) - 1); }
    hs[i] = key; hcount++;
    return 1;
}
/* ---------- invariant for splitting ---------- */
static unsigned inv_hash(int n, const u64 *a) {
    int d[64], s[64];
    for (int v = 0; v < n; v++) d[v] = PC(a[v]);
    for (int v = 0; v < n; v++) { int t = 0; for (u64 c = a[v]; c; c &= c - 1) t += d[CTZ(c)]; s[v] = d[v] * 1000 + t; }
    qsort(s, n, sizeof(int), cmpint);
    unsigned hsh = 2166136261u;
    for (int v = 0; v < n; v++) { hsh ^= (unsigned)s[v]; hsh *= 16777619u; }
    hsh ^= hsh >> 15; hsh *= 0x2c1b3c6dU; hsh ^= hsh >> 12; hsh *= 0x297a2d39U; hsh ^= hsh >> 15; /* mix low bits */
    return hsh;
}
/* ---------- statistics ---------- */
static long long cnt[16], nclosed[16], nhyp[16], nnohp[16], slack[16][64], cases[16][4], terms[16];
static int maxr[16];
static long long nmnt[16], nmnt_closed[16];
static void process(int n, const u64 *a, u64 code) {
    cnt[n]++;
    u64 h[64]; complement(n, a, h);
    int m = lm_of(n, h);
    int hp = hp_dfs(n, a);
    int checkdp = (n <= 9);
    int g = g2_exact_enum(n, h, m + 1);
    int hyp = (g >= m + 2);
    if (hyp) {
        nhyp[n]++;
        if (g2_bb(n, h, m + 1) != g) FAIL("gamma2 disagree on Hyp graph n=%d code=%llx", n, (unsigned long long)code);
        checkdp = 1;
    }
    if (!hp) {
        nnohp[n]++; checkdp = 1;
        /* Lemma C check: maximal non-traceable (every added edge gives a Hamiltonian path) => closed */
        int mnt = 1;
        for (int x = 0; x < n && mnt; x++) for (int y = x + 1; y < n && mnt; y++) if (!((a[x] >> y) & 1)) {
            u64 b[64]; memcpy(b, a, n * sizeof(u64)); b[x] |= 1ULL << y; b[y] |= 1ULL << x;
            if (!hp_dfs(n, b)) mnt = 0;
        }
        if (mnt) { nmnt[n]++; if (is_closed(n, a)) nmnt_closed[n]++; else FAIL("Lemma C fails: MNT not closed n=%d code=%llx", n, (unsigned long long)code); }
    }
    if (checkdp && hp_dp(n, a) != hp) FAIL("HP methods disagree n=%d code=%llx", n, (unsigned long long)code);
    if (hyp && !hp) FAIL("COUNTEREXAMPLE to Conjecture 213: n=%d code=%llx", n, (unsigned long long)code);
    if (n >= 2 && is_closed(n, a) && !is_complete(n, a)) {
        nclosed[n]++;
        int g1 = g2_exact_enum(n, h, n), g2 = g2_bb(n, h, n);
        if (g1 != g2) FAIL("gamma2 methods disagree n=%d code=%llx", n, (unsigned long long)code);
        slack[n][g1 - m + 32]++;
        if (g1 >= m + 2) FAIL("closed connected non-complete graph with Hyp n=%d code=%llx", n, (unsigned long long)code);
        cstat st; char tag[80]; snprintf(tag, sizeof tag, "n=%d code=%llx", n, (unsigned long long)code);
        run_proof(n, a, 1LL << 40, 1LL << 40, &st, tag);
        if (st.capped) FAIL("capped %s", tag);
        cases[n][st.caseid]++; terms[n] += st.terminals; if (st.maxrounds > maxr[n]) maxr[n] = st.maxrounds;
    }
}
static int noncut(int n, const u64 *a, int w) {
    u64 all = FULL(n) & ~(1ULL << w);
    int s = (w == 0) ? 1 : 0;
    u64 seen = 1ULL << s, fr = seen;
    while (fr) { u64 nf = 0; for (u64 f = fr; f; f &= f - 1) nf |= a[CTZ(f)]; nf &= all & ~seen; seen |= nf; fr = nf; }
    return seen == all;
}
int main(int argc, char **argv) {
    int NMAX = atoi(argv[1]);
    int part = argc > 3 ? atoi(argv[2]) : 0, nparts = argc > 3 ? atoi(argv[3]) : 1;
    hs = calloc(1ULL << HB, sizeof(u64));
    u64 *par = malloc(sizeof(u64)); long long npar = 1; par[0] = 0; /* K1 */
    { u64 a[1] = {0}; process(1, a, 0); }
    for (int n = 2; n <= NMAX; n++) {
        N_ = n;
        memset(hs, 0, (1ULL << HB) * sizeof(u64)); hcount = 0;
        u64 *nxt = NULL; long long nn = 0, cap = 0;
        int last = (n == NMAX);
        for (long long p = 0; p < npar; p++) {
            u64 b[64]; decode(n - 1, par[p], b);
            for (u64 S = 1; S < (1ULL << (n - 1)); S++) {
                u64 a[64];
                for (int v = 0; v < n - 1; v++) a[v] = b[v] | (((S >> v) & 1) ? (1ULL << (n - 1)) : 0);
                a[n - 1] = S;
                int k = PC(S), ok = 1;
                for (int w = 0; w < n - 1 && ok; w++) if (PC(a[w]) < k && noncut(n, a, w)) ok = 0;
                if (!ok) continue;
                if (last && nparts > 1 && (int)(inv_hash(n, a) % nparts) != part) continue;
                u64 c = canon(n, a);
                if (!hs_insert(c)) continue;
                u64 a2[64]; decode(n, c, a2);
                if (!is_connected(n, a2)) FAIL("decode error");
                process(n, a2, c);
                if (!last) { if (nn == cap) { cap = cap ? 2 * cap : 1024; nxt = realloc(nxt, cap * sizeof(u64)); } nxt[nn++] = c; }
            }
        }
        if (!last) { free(par); par = nxt; npar = nn; }
        printf("n=%d part %d/%d: connected=%lld Hyp=%lld nonHP=%lld closed_noncomplete=%lld | cases J=%lld 2a=%lld 2b=%lld terminals=%lld maxrounds=%d | slack:",
               n, last ? part : 0, last ? nparts : 1, cnt[n], nhyp[n], nnohp[n], nclosed[n], cases[n][1], cases[n][2], cases[n][3], terms[n], maxr[n]);
        for (int s = 0; s < 64; s++) if (slack[n][s]) printf(" [%d]=%lld", s - 32, slack[n][s]);
        printf(" | MNT=%lld MNT_closed=%lld | failures so far=%lld\n", nmnt[n], nmnt_closed[n], g_fail);
        fflush(stdout);
    }
    return g_fail ? 1 : 0;
}
