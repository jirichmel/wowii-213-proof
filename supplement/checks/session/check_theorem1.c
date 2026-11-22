/* check_theorem1.c -- the session agent's own check (21 November 2026) of prover-claimC's Theorem 1:
   every closed, connected, non-complete graph G has gamma_2(H) <= lm(H) + 1 (H = complement of G).
   Written from the proof text only; shares no code with cdom.c or pdom.py.
   For every graph tested it (a) runs the proof's construction of D (Lemma J if 2m >= n; otherwise
   Lemma 4's loop with RANDOM choices, or case 2b) and verifies |D| <= m+1 and that D 2-dominates H
   against the definition; (b) asserts Lemma G(b) (Q is a clique) and G(f) (each y in Y has at most
   r-2 neighbours in P); (c) for n <= 8 also searches all sets for a 2-dominating set of size <= m+1,
   independently of the construction.
   usage: check_theorem1 ex NMAX K                  all labelled graphs on 2..NMAX vertices (NMAX <= 8)
          check_theorem1 rnd NMIN NMAX COUNT K SEED random graphs made closed by the (n-1)-closure
          check_theorem1 hub NMIN NMAX COUNT K SEED clique U u P, random P-Y and Y-Y edges, then closure
   build: cc -O2 -o check_theorem1 check_theorem1.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
static int n; static u64 adj[64]; static int deg[64];
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static u64 ALL(void) { return n == 64 ? ~0ULL : ((1ULL << n) - 1); }
static int pc(u64 x) { return __builtin_popcountll(x); }
static void degs(void) { for (int v = 0; v < n; v++) deg[v] = pc(adj[v]); }
static int connected(void) { u64 seen = 1, fr = 1; while (fr) { u64 nf = 0; for (int v = 0; v < n; v++) if (fr >> v & 1) nf |= adj[v]; nf &= ~seen; seen |= nf; fr = nf; } return seen == ALL(); }
static int closed(void) { for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (!(adj[a] >> b & 1) && deg[a] + deg[b] > n - 2) return 0; return 1; }
static int complete(void) { for (int v = 0; v < n; v++) if (deg[v] != n - 1) return 0; return 1; }
static int lmH(void) { int h[64]; for (int v = 0; v < n; v++) h[v] = n - 1 - deg[v];
  for (int i = 1; i < n; i++) { int x = h[i], j = i - 1; while (j >= 0 && h[j] > x) { h[j + 1] = h[j]; j--; } h[j + 1] = x; }
  return h[(n + 1) / 2 - 1]; }
/* D 2-dominates H: every v outside D has at least two vertices of D, other than v, that are non-adjacent to v in G */
static int twodom(u64 D) { for (int v = 0; v < n; v++) { if (D >> v & 1) continue; if (pc(D & ~adj[v] & ~(1ULL << v)) < 2) return 0; } return 1; }
static long graphs, cons, fails, asserts, looped, exactfail, exactdone;
static u64 pick(u64 S, int k) { int idx[64], t = 0; for (int v = 0; v < n; v++) if (S >> v & 1) idx[t++] = v;
  if (k > t) { asserts++; k = t; } u64 R = 0;
  for (int i = 0; i < k; i++) { int j = i + (int)(rnd() % (u64)(t - i)); int tmp = idx[i]; idx[i] = idx[j]; idx[j] = tmp; R |= 1ULL << idx[i]; }
  return R; }
static u64 construct(int m) {
  if (2 * m >= n) { u64 W = 0; for (int v = 0; v < n; v++) if (n - 1 - deg[v] >= m) W |= 1ULL << v;
    return ALL() & ~pick(W, n - m - 1); }                                   /* Lemma J */
  u64 U = 0, Q = 0, Y = 0;
  for (int v = 0; v < n; v++) { if (deg[v] == n - 1) U |= 1ULL << v; if (deg[v] >= m) Q |= 1ULL << v; else Y |= 1ULL << v; }
  u64 P = Q & ~U; int u = pc(U), r = m - u + 1;
  for (int a = 0; a < n; a++) if ((Q >> a & 1) && (Q & ~adj[a] & ~(1ULL << a))) asserts++;   /* G(b) */
  for (int y = 0; y < n; y++) if ((Y >> y & 1) && pc(adj[y] & P) > r - 2) asserts++;        /* G(f) */
  if (pc(Y) >= r) {                                                         /* case 2a, Lemma 4 loop */
    u64 R = pick(Y, r), B = 0;
    for (;;) { int f = -1;
      for (int q = 0; q < n && f < 0; q++) if (((P & ~B) >> q & 1) && pc(adj[q] & R) >= pc(R) - 1) f = q;
      if (f < 0) break;
      B |= 1ULL << f; looped++; R = pick(adj[f] & R, pc(R) - 1); }
    return U | B | R; }
  return U | Y | pick(P, m + 1 - u - pc(Y));                                /* case 2b */
}
static void test(int K) {
  degs(); if (!connected() || complete() || !closed()) return;
  int m = lmH(); graphs++;
  for (int k = 0; k < K; k++) { u64 D = construct(m); cons++;
    if (pc(D) > m + 1 || !twodom(D)) { if (++fails <= 5) { printf("FAIL n=%d m=%d:", n, m);
      for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (adj[a] >> b & 1) printf(" %d-%d", a, b); printf("\n"); } } }
  if (n <= 8) { int ok = 0; exactdone++;
    for (u64 D = 0; D < (1ULL << n) && !ok; D++) if (pc(D) <= m + 1 && twodom(D)) ok = 1;
    if (!ok) exactfail++; }
}
static void closure(void) { int ch = 1; degs();
  while (ch) { ch = 0; for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++)
    if (!(adj[a] >> b & 1) && deg[a] + deg[b] >= n - 1) { adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; deg[a]++; deg[b]++; ch = 1; } } }
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: see header\n"); return 1; }
  if (argv[1][0] == 'e') { int N = atoi(argv[2]), K = atoi(argv[3]);
    for (n = 2; n <= N; n++) { int ea[64], eb[64], E = 0; long g0 = graphs;
      for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) { ea[E] = a; eb[E] = b; E++; }
      for (u64 mask = 0; mask < (1ULL << E); mask++) { for (int v = 0; v < n; v++) adj[v] = 0;
        for (int e = 0; e < E; e++) if (mask >> e & 1) { adj[ea[e]] |= 1ULL << eb[e]; adj[eb[e]] |= 1ULL << ea[e]; }
        test(K); }
      printf("n=%d: %ld labelled closed connected non-complete graphs\n", n, graphs - g0); fflush(stdout); } }
  else { int NMIN = atoi(argv[2]), NMAX = atoi(argv[3]); long C = atol(argv[4]); int K = atoi(argv[5]); rs ^= (u64)atol(argv[6]) * 0x9E3779B97F4A7C15ULL;
    int hub = argv[1][0] == 'h', wmode = argv[1][0] == 'w';
    for (long c = 0; c < C; c++) { n = NMIN + (int)(rnd() % (u64)(NMAX - NMIN + 1)); for (int v = 0; v < n; v++) adj[v] = 0;
      if (wmode) { /* forces Lemma 4's loop: U, hubs adjacent to all of W, other P with few W-neighbours,
                      Z adjacent only to U; Q = U u hubs u other P is a clique; no closure, closedness filtered */
        int u = 1 + (int)(rnd() % 4), h = 1 + (int)(rnd() % 5), w = 4 + (int)(rnd() % 14), o = (int)(rnd() % 10), z = (int)(rnd() % 6);
        if (u + h + w + o + z > 63) continue; n = u + h + w + o + z; int q = u + h + o;  /* vertices 0..q-1 form Q */
        for (int a = 0; a < q; a++) for (int b = a + 1; b < q; b++) { adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; }
        for (int a = 0; a < u; a++) for (int b = q; b < n; b++) { adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; }
        for (int a = u; a < u + h; a++) for (int b = q; b < q + w; b++) { adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; }
        for (int a = u + h; a < q; a++) { int k = (int)(rnd() % 4); for (int i = 0; i < k; i++) { int b = q + (int)(rnd() % (u64)w); adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; } }
        for (int a = q; a < n; a++) for (int b = a + 1; b < n; b++) if (rnd() % 100 < 4) { adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; }
        test(K); continue; }
      if (!hub) { double p = 0.03 + 0.5 * (double)(rnd() % 1000) / 1000.0;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if ((double)(rnd() % 100000) / 100000.0 < p) { adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; } }
      else { int u = (int)(rnd() % 6), q = 1 + (int)(rnd() % (u64)(n / 2)); if (u + q >= n) q = n - u - 1; if (q < 0) q = 0;
        double p1 = (double)(rnd() % 1000) / 1000.0 * 0.6, p2 = (double)(rnd() % 1000) / 1000.0 * 0.3;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) { int ina = a < u + q, inb = b < u + q, uni = a < u;
          int e = (ina && inb) || uni || (ina && !inb && (double)(rnd() % 1000) / 1000.0 < p1) || (!ina && !inb && (double)(rnd() % 1000) / 1000.0 < p2);
          if (e) { adj[a] |= 1ULL << b; adj[b] |= 1ULL << a; } } }
      closure(); test(K); } }
  printf("graphs %ld, constructions %ld, construction failures %ld, Lemma G assertion failures %ld, Lemma 4 rounds %ld", graphs, cons, fails, asserts, looped);
  if (exactdone) printf(", exact search (n <= 8): %ld graphs, %ld without a 2-dominating set of size <= lm+1", exactdone, exactfail);
  printf("\n"); return 0;
}
