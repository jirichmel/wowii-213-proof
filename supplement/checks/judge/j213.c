/* j213.c -- judge213's own checker for the Conjecture 213 proof (prover-claimC, 21 Nov 2026).
   Written from the statement and proof.md only; shares no code with cdom.c, pdom.py, lem4.c,
   check_theorem1.c, ref213.c or the checker213 programs.
   Build: cc -O2 -o j213 j213.c
   Modes:
     ./j213 thm N        all labelled graphs on N <= 8 vertices: for the closed connected non-complete
                         ones, exact gamma_2(H) vs lm(H)+1, plus the proof's construction (first choices
                         and 8 random-choice runs) with the final set checked against the definition.
     ./j213 conj N       all labelled connected graphs on N <= 7 vertices: Hyp => Hamiltonian path;
                         also every edge-maximal non-traceable graph (connected or not) is closed.
     ./j213 lem4 r K s   abstract Lemma 4 by direct existence search (not by the proof's procedure):
                         every multiset of s subsets of {0..K-1}, each of size <= r-2.
     ./j213 hub n0 n1 T seed   hub family where the Lemma 4 loop must run; 50 runs per graph.
     ./j213 rnd n0 n1 T seed [gen]   random (gen 0 or 1: two parameter settings) hub-type closed connected graphs, n0..n1 vertices, T tries each;
                         construction with random choices, set checked; exact gamma_2 when n <= 22.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint32_t msk;
#define MAXN 32
static int n;
static msk adj[MAXN], FULL;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k){ return (int)(rnd64() % (uint64_t)k); }

static int pc(msk x){ return __builtin_popcount(x); }
static int deg(int v){ return pc(adj[v]); }
static msk hadj(int v){ return FULL & ~adj[v] & ~((msk)1 << v); }

static int connected(void){
  msk seen = 1, fr = 1;
  while (fr){ msk nf = 0; for (int v = 0; v < n; v++) if (fr >> v & 1) nf |= adj[v]; fr = nf & ~seen; seen |= nf; }
  return seen == FULL;
}
static int closed_(void){
  for (int a = 0; a < n; a++) for (int b = a+1; b < n; b++)
    if (!(adj[a] >> b & 1) && deg(a) + deg(b) > n - 2) return 0;
  return 1;
}
static int complete_(void){ for (int v = 0; v < n; v++) if (deg(v) != n-1) return 0; return 1; }
/* lower median of H-degrees: k-th smallest with k = ceil(n/2) */
static int lmH(void){
  int h[MAXN]; for (int v = 0; v < n; v++) h[v] = n - 1 - deg(v);
  for (int i = 1; i < n; i++){ int x = h[i], j = i-1; while (j >= 0 && h[j] > x){ h[j+1] = h[j]; j--; } h[j+1] = x; }
  return h[(n+1)/2 - 1];
}
static int twodom(msk D){
  for (int v = 0; v < n; v++) if (!(D >> v & 1) && pc(hadj(v) & D) < 2) return 0;
  return 1;
}
/* exact gamma_2(H): smallest 2-dominating set (supersets of 2-dominating sets are 2-dominating) */
static msk *bysize[MAXN+1]; static int nbys[MAXN+1]; static int bys_n = -1;
static void prep_subsets(void){
  if (bys_n == n) return; bys_n = n;
  long cnt[MAXN+1] = {0};
  for (msk s = 0; s < ((msk)1 << n); s++) cnt[pc(s)]++;
  for (int k = 0; k <= n; k++){ free(bysize[k]); bysize[k] = malloc(sizeof(msk) * (cnt[k] + 1)); nbys[k] = 0; }
  for (msk s = 0; s < ((msk)1 << n); s++){ int k = pc(s); bysize[k][nbys[k]++] = s; }
}
static int exists2dom(int k){ for (int i = 0; i < nbys[k]; i++) if (twodom(bysize[k][i])) return 1; return 0; }
static int gamma2(void){ for (int k = 0; k <= n; k++) if (exists2dom(k)) return k; return n; }
/* Hamiltonian path by subset DP: end[S] = set of possible end vertices of a path covering S */
static msk *endv; static int endv_n = -1;
static int hampath(void){
  if (endv_n != n){ free(endv); endv = malloc(sizeof(msk) * (1u << n)); endv_n = n; }
  for (msk S = 1; S < ((msk)1 << n); S++){
    if (pc(S) == 1){ endv[S] = S; continue; }
    msk e = 0;
    for (int v = 0; v < n; v++) if (S >> v & 1){ msk T = S & ~((msk)1 << v); if (endv[T] & adj[v]) e |= (msk)1 << v; }
    endv[S] = e;
  }
  return endv[FULL] != 0;
}

/* ---------- the proof's construction ---------- */
static long st_case[3], st_rounds[40], fails;
static int maxrounds;
static msk rand_subset(msk from, int k, int randomize){ /* k-subset of 'from' */
  int el[MAXN], c = 0; for (int v = 0; v < n; v++) if (from >> v & 1) el[c++] = v;
  if (randomize) for (int i = c-1; i > 0; i--){ int j = rndi(i+1); int t = el[i]; el[i] = el[j]; el[j] = t; }
  msk s = 0; for (int i = 0; i < k && i < c; i++) s |= (msk)1 << el[i];
  return s;
}
#define FAIL(...) do{ fails++; if (fails < 20){ fprintf(stderr, "FAIL n=%d: ", n); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } return 0; }while(0)
/* returns the final D (0 on failure); checks every lemma assertion on the way */
static msk construct(int randomize){
  for (int a = 0; a < n; a++){ if (adj[a] >> a & 1) FAIL("loop"); for (int b = 0; b < n; b++) if ((adj[a] >> b & 1) != (adj[b] >> a & 1)) FAIL("adjacency not symmetric"); }
  int m = lmH();
  msk D;
  if (2*m >= n){
    msk W = 0; for (int v = 0; v < n; v++) if (n-1-deg(v) >= m) W |= (msk)1 << v;
    int a = n - m - 1;
    if (pc(W) < a) FAIL("|W| < a");
    msk A = rand_subset(W, a, randomize);
    D = FULL & ~A; st_case[0]++;
  } else {
    msk Q = 0, U = 0, Y, P;
    for (int v = 0; v < n; v++){ if (deg(v) >= m) Q |= (msk)1 << v; if (deg(v) == n-1) U |= (msk)1 << v; }
    Y = FULL & ~Q; P = Q & ~U;
    int u = pc(U), r = m - u + 1;
    for (int v = 0; v < n; v++) if (Q >> v & 1) if ((Q & ~adj[v] & ~((msk)1 << v)) != 0) FAIL("G(b) Q not clique");
    if (!Y) FAIL("G(c) Y empty");
    if (r < 2) FAIL("G(c) r<2");
    for (int v = 0; v < n; v++) if (P >> v & 1){
      msk non = FULL & ~adj[v] & ~((msk)1 << v);
      if (non & ~Y) FAIL("G(d)"); if (pc(non) < 2) FAIL("G(e)");
    }
    for (int y = 0; y < n; y++) if (Y >> y & 1){ if ((U & ~adj[y])) FAIL("G(c) U not in N(y)"); if (pc(adj[y] & P) > r-2) FAIL("G(f)"); }
    if (pc(Y) >= r){
      msk R = rand_subset(Y, r, randomize), B = 0; int rounds = 0;
      for (;;){
        /* heavy vertices: q in P\B adjacent to >= |R|-1 vertices of R */
        msk heavy = 0;
        for (int q = 0; q < n; q++) if ((P & ~B) >> q & 1) if (pc(adj[q] & R) >= pc(R) - 1) heavy |= (msk)1 << q;
        if (!heavy) break;
        int q = __builtin_ctz(rand_subset(heavy, 1, randomize));
        msk Rn = rand_subset(adj[q] & R, pc(R) - 1, randomize);
        if (pc(Rn) != pc(R) - 1) FAIL("Lemma4: not enough neighbours");
        B |= (msk)1 << q; R = Rn; rounds++;
        if (pc(B) + pc(R) != r) FAIL("inv |B|+|R|");
        if (pc(R) < 2) FAIL("inv |R|>=2");
        for (int y = 0; y < n; y++) if (R >> y & 1) if (B & ~adj[y]) FAIL("inv B in A_y");
        if (rounds > r - 2) FAIL("too many rounds");
      }
      if (rounds > maxrounds) maxrounds = rounds;
      st_rounds[rounds]++;
      D = U | B | R; st_case[1]++;
    } else {
      int c = m + 1 - u - pc(Y);
      if (c < 1 || pc(P) < c) FAIL("2b counts");
      D = U | Y | rand_subset(P, c, randomize); st_case[2]++;
    }
  }
  if (pc(D) != m + 1) FAIL("|D| = %d, m+1 = %d", pc(D), m+1);
  if (!twodom(D)) FAIL("D not 2-dominating");
  return D;
}

static void setgraph(int N, uint64_t code){
  n = N; FULL = (N == 32) ? ~(msk)0 : (((msk)1 << N) - 1);
  memset(adj, 0, sizeof adj); int b = 0;
  for (int i = 0; i < N; i++) for (int j = i+1; j < N; j++, b++) if (code >> b & 1){ adj[i] |= (msk)1 << j; adj[j] |= (msk)1 << i; }
}

static void mode_thm(int N){
  int E = N*(N-1)/2; long cnt = 0, hist[8] = {0}, bad = 0;
  n = N; prep_subsets();
  for (uint64_t c = 0; c < ((uint64_t)1 << E); c++){
    setgraph(N, c); prep_subsets();
    if (!connected() || complete_() || !closed_()) continue;
    cnt++;
    int m = lmH(), g = gamma2();
    int s = g - m; if (s >= -3 && s <= 4) hist[s+3]++;
    if (g > m + 1) bad++;
    construct(0); for (int k = 0; k < 8; k++) construct(1);
  }
  printf("thm n=%d closed connected non-complete labelled: %ld; gamma2>lm+1: %ld; construction fails: %ld\n", N, cnt, bad, fails);
  printf("  histogram of gamma2-lm:"); for (int s = -3; s <= 4; s++) if (hist[s+3]) printf(" [%d]=%ld", s, hist[s+3]); printf("\n");
  printf("  cases (runs): 2m>=n %ld, 2a %ld, 2b %ld; max Lemma-4 rounds %d\n", st_case[0], st_case[1], st_case[2], maxrounds);
}

static void mode_conj(int N){
  int E = N*(N-1)/2; long conn = 0, hyp = 0, hypnoham = 0, mnt = 0, mntnotclosed = 0, nonham = 0;
  for (uint64_t c = 0; c < ((uint64_t)1 << E); c++){
    setgraph(N, c); prep_subsets();
    int ham = hampath();
    if (!ham){
      /* edge-maximal non-traceable? */
      int maximal = 1;
      for (int a = 0; a < N && maximal; a++) for (int b = a+1; b < N && maximal; b++) if (!(adj[a] >> b & 1)){
        adj[a] |= (msk)1 << b; adj[b] |= (msk)1 << a;
        if (!hampath()) maximal = 0;
        adj[a] &= ~((msk)1 << b); adj[b] &= ~((msk)1 << a);
      }
      if (maximal){ mnt++; if (!closed_()) mntnotclosed++; }
    }
    if (!connected()) continue;
    conn++;
    int m = lmH();
    int isHyp = !exists2dom(m + 1);  /* gamma2 >= m+2 iff no 2-dom set of size m+1 (m+1 <= n always) */
    if (isHyp){ hyp++; if (!ham) hypnoham++; }
    if (!ham) nonham++;
  }
  printf("conj n=%d labelled connected: %ld; Hyp: %ld; Hyp without Ham path: %ld; connected non-traceable: %ld; MNT (all graphs): %ld, MNT not closed: %ld\n",
         N, conn, hyp, hypnoham, nonham, mnt, mntnotclosed);
}

/* abstract Lemma 4, by direct existence search over (B,R); s sets A_0..A_{s-1} of {0..K-1}, |A_i| <= r-2 */
static int L4r, L4K, L4s; static msk L4sets[1 << 10]; static int L4ns; static long L4fam, L4fail;
static int lem4_exists(const msk *A){
  for (msk R = 0; R < ((msk)1 << L4s); R++){
    int rr = pc(R); if (rr > L4r) continue;
    msk heavy = 0;
    for (int q = 0; q < L4K; q++){ int c = 0; for (int i = 0; i < L4s; i++) if (R >> i & 1) if (A[i] >> q & 1) c++; if (c > rr - 2) heavy |= (msk)1 << q; }
    int need = L4r - rr; /* |B| = need, B must contain heavy, B inside {0..K-1} */
    if (pc(heavy) <= need && need <= L4K) return 1;
  }
  return 0;
}
static void lem4_rec(int i, int from, msk *A){
  if (i == L4s){ L4fam++; if (!lem4_exists(A)){ L4fail++; if (L4fail < 5){ fprintf(stderr, "Lemma4 FAIL:"); for (int j = 0; j < L4s; j++) fprintf(stderr, " %x", A[j]); fprintf(stderr, "\n"); } } return; }
  for (int t = from; t < L4ns; t++){ A[i] = L4sets[t]; lem4_rec(i+1, t, A); }
}
static void mode_lem4(int r, int K, int s){
  L4r = r; L4K = K; L4s = s; L4ns = 0;
  for (msk x = 0; x < ((msk)1 << K); x++) if (pc(x) <= r - 2) L4sets[L4ns++] = x;
  msk A[32]; lem4_rec(0, 0, A);
  printf("lem4 r=%d |P|=%d |Y'|=%d: families (multisets) %ld, failures %ld\n", r, K, s, L4fam, L4fail);
}

/* random hub-type graphs: U universal clique, P with hubs, Q = U u P clique, Y low;
   then edges are deleted until closed (deleting only edges not inside Q); keep if connected, non-complete */
static int gen = 0;
static void mode_rnd(int n0, int n1, long T){
  long kept = 0, gtests = 0, gbad = 0, case2a = 0;
  for (int N = n0; N <= n1; N++) for (long t = 0; t < T; t++){
    n = N; FULL = (N == 32) ? ~(msk)0 : (((msk)1 << N) - 1); memset(adj, 0, sizeof adj);
    int u = rndi(N/4 + 1), p, y;
    if (gen == 0) p = 1 + rndi(N/3); else { p = N/2 - u + rndi(N/6 + 1); if (p < 1) p = 1; }
    y = N - u - p; if (y < 2) continue;
    int hubs = 1 + rndi(p < 4 ? p : 4);
    msk Q = ((msk)1 << (u + p)) - 1;
    for (int a = 0; a < N; a++) for (int b = a+1; b < N; b++){
      int e;
      if (b < u + p) e = 1;
      else if (a < u) e = 1;
      else if (a < u + hubs) e = rndi(100) < (gen ? 90 : 75);
      else if (a < u + p) e = rndi(100) < (gen ? 5 : 15);
      else e = rndi(100) < (gen ? 3 : 10);
      if (e){ adj[a] |= (msk)1 << b; adj[b] |= (msk)1 << a; }
    }
    for (;;){ /* repair */
      int va = -1, vb = -1;
      for (int a = 0; a < N && va < 0; a++) for (int b = a+1; b < N; b++)
        if (!(adj[a] >> b & 1) && deg(a) + deg(b) > N - 2){ va = a; vb = b; break; }
      if (va < 0) break;
      int ends[2] = {va, vb}; msk cand[2]; int tot = 0;
      for (int k = 0; k < 2; k++){ int x = ends[k]; cand[k] = adj[x]; if (Q >> x & 1) cand[k] &= ~Q; tot += pc(cand[k]); }
      if (!tot) break;
      int pick = rndi(tot), k = 0; if (pick >= pc(cand[0])){ pick -= pc(cand[0]); k = 1; }
      msk c = cand[k]; for (int i = 0; i < pick; i++) c &= c - 1; int w = __builtin_ctz(c), x = ends[k];
      adj[x] &= ~((msk)1 << w); adj[w] &= ~((msk)1 << x);
    }
    if (!closed_() || !connected() || complete_()) continue;
    kept++;
    long before = st_case[1];
    for (int k = 0; k < 20; k++) construct(k > 0);
    if (st_case[1] > before) case2a++;
    if (N <= 22){
      prep_subsets(); int m = lmH(); gtests++;
      if (m + 2 <= N && !exists2dom(m + 1)) gbad++;  /* gamma2 >= m+2 would refute Theorem 1 */
    }
  }
  printf("rnd n=%d..%d: graphs kept %ld (in Case 2a %ld); construction runs: 2m>=n %ld, 2a %ld, 2b %ld; fails %ld; max rounds %d\n",
         n0, n1, kept, case2a, st_case[0], st_case[1], st_case[2], fails, maxrounds);
  printf("  rounds histogram (2a runs):"); for (int i = 0; i < 40; i++) if (st_rounds[i]) printf(" [%d]=%ld", i, st_rounds[i]); printf("\n");
  printf("  exact test (n<=22): %ld graphs, gamma2 >= lm+2 in %ld\n", gtests, gbad);
}

/* hub family (built to make the Lemma 4 loop run): U universal, hubs Hb adjacent to all of W,
   P' each adjacent to k random vertices of W, Z adjacent only to U, Q = U u Hb u P' a clique,
   W and Z independent. Kept only if closed, connected, non-complete (no repair). */
static void mode_hub(int n0, int n1, long T){
  long tried = 0, kept = 0, case2a = 0, gtests = 0, gbad = 0;
  for (int N = n0; N <= n1; N++) for (long t = 0; t < T; t++){
    n = N; FULL = (N == 32) ? ~(msk)0 : (((msk)1 << N) - 1); memset(adj, 0, sizeof adj);
    int u = rndi(4), h = 1 + rndi(5), z = rndi(N/5 + 1), w = 2 + rndi(N/2), pp = N - u - h - z - w;
    if (pp < 0) continue;
    int k = 1 + rndi(3); tried++;
    int q = u + h + pp; /* Q = 0..q-1: U = 0..u-1, Hb = u..u+h-1, P' = u+h..q-1; W = q..q+w-1; Z = rest */
#define E_(a,b) do{ adj[a] |= (msk)1 << (b); adj[b] |= (msk)1 << (a); }while(0)
    for (int a = 0; a < q; a++) for (int b = a+1; b < q; b++) E_(a,b);
    for (int a = 0; a < u; a++) for (int b = q; b < N; b++) E_(a,b);
    for (int a = u; a < u+h; a++) for (int b = q; b < q+w; b++) E_(a,b);
    for (int a = u+h; a < q; a++) for (int i = 0; i < k; i++){ int b = q + rndi(w); E_(a, b); } /* b computed once: E_ uses its arguments twice */
    if (!closed_() || !connected() || complete_()) continue;
    kept++;
    long before = st_case[1];
    for (int i = 0; i < 50; i++) construct(i > 0);
    if (st_case[1] > before) case2a++;
    if (N <= 20){ prep_subsets(); int m = lmH(); gtests++; if (!exists2dom(m + 1)) gbad++; }
  }
  printf("hub n=%d..%d: tried %ld, kept %ld (Case 2a %ld); runs 2m>=n %ld, 2a %ld, 2b %ld; fails %ld; max rounds %d\n",
         n0, n1, tried, kept, case2a, st_case[0], st_case[1], st_case[2], fails, maxrounds);
  printf("  rounds histogram (2a runs):"); for (int i = 0; i < 40; i++) if (st_rounds[i]) printf(" [%d]=%ld", i, st_rounds[i]); printf("\n");
  printf("  exact test (n<=20): %ld graphs, gamma2 >= lm+2 in %ld\n", gtests, gbad);
}

int main(int argc, char **argv){
  if (argc < 2){ fprintf(stderr, "usage: see header\n"); return 1; }
  if (!strcmp(argv[1], "thm")) mode_thm(atoi(argv[2]));
  else if (!strcmp(argv[1], "conj")) mode_conj(atoi(argv[2]));
  else if (!strcmp(argv[1], "lem4")) mode_lem4(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
  else if (!strcmp(argv[1], "hub")){ rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; mode_hub(atoi(argv[2]), atoi(argv[3]), atol(argv[4])); }
  else if (!strcmp(argv[1], "rnd")){ rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; if (argc > 6) gen = atoi(argv[6]); mode_rnd(atoi(argv[2]), atoi(argv[3]), atol(argv[4])); }
  return fails ? 2 : 0;
}
