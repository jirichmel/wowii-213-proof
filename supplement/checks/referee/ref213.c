/* referee213: independent checker for the Claim C proof of WOWII Conjecture 213.
   Written from scratch by the referee; shares no code with cdom.c, pdom.py, lem4.c,
   check_theorem1.c or tools/lib.
   Build: cc -O2 -o ref213 ref213.c
   Modes:
     ref213 lab N K        all labelled graphs on N <= 8 vertices; for closed connected
                           non-complete ones: exact gamma2(H) vs lm(H)+1, construction of
                           Theorem 1 with first choices and K random runs, Lemma G asserts.
                           If N <= 7 also: Conjecture 213 directly on every connected graph,
                           and Lemma C / BC (HP(G+ab) -> HP(G) when d(a)+d(b) >= n-1),
                           and Lemma M (sigma(G+e) >= sigma(G)) on every graph and non-edge.
     ref213 mnt N COUNT SEED   random maximal non-traceable graphs on N <= 20 vertices.
     ref213 struct N COUNT SEED  structured closed graphs (clique Q + low vertices), N <= 60;
                           exact gamma2 only if N <= 22.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
static int n;
static u64 adj[64];
static u64 FULL;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k){ return (int)(rnd() % (u64)k); }

static int pc(u64 x){ return __builtin_popcountll(x); }
static u64 nonadj(int v){ return FULL & ~adj[v] & ~(1ULL<<v); }
static int deg(int v){ return pc(adj[v]); }

static int connected(void){
  u64 seen = 1, fr = 1;
  while(fr){ u64 nf = 0; for(int v=0; v<n; v++) if(fr>>v&1) nf |= adj[v]; fr = nf & ~seen; seen |= fr; }
  return seen == FULL;
}
static int closedG(void){
  for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(!(adj[a]>>b&1)) if(deg(a)+deg(b) > n-2) return 0;
  return 1;
}
static int complete(void){ for(int v=0;v<n;v++) if(deg(v)!=n-1) return 0; return 1; }

/* lm(H): sorted H-degrees, entry number ceil(n/2) (1-based). Counting sort, own code. */
static int lmH(void){
  int cnt[65]; memset(cnt,0,sizeof cnt);
  for(int v=0;v<n;v++) cnt[n-1-deg(v)]++;
  int k = (n+1)/2, s = 0;
  for(int h=0; h<=n; h++){ s += cnt[h]; if(s >= k) return h; }
  return -1;
}
/* D 2-dominating in H: every v not in D has >= 2 G-non-neighbours in D */
static int is2dom(u64 D){
  for(int v=0; v<n; v++) if(!(D>>v&1)) if(pc(nonadj(v) & D) < 2) return 0;
  return 1;
}
/* exact gamma2(H): sizes k = 0,1,... combinations by Gosper's hack */
static int gamma2(void){
  for(int k=0;k<=n;k++){
    if(k==0){ if(is2dom(0)) return 0; continue; }
    u64 c = (1ULL<<k)-1;
    while(c < (1ULL<<n)){
      if(is2dom(c)) return k;
      u64 a = c & -c, b = c + a; c = (((c ^ b) >> 2) / a) | b;
    }
  }
  return n;
}
/* Hamiltonian path by DP over subsets, n <= 20 */
static uint32_t *dp = NULL;
static int hampath(void){
  if(n==1) return 1;
  u64 S = 1ULL<<n;
  for(u64 m=0;m<S;m++) dp[m]=0;
  for(int v=0;v<n;v++) dp[1ULL<<v] = 1u<<v;
  for(u64 m=1;m<S;m++){
    uint32_t e = dp[m]; if(!e) continue;
    u64 ext = 0;
    for(int v=0; v<n; v++) if(e>>v&1) ext |= adj[v];
    ext &= ~m & FULL;
    for(int w=0; w<n; w++) if(ext>>w&1) dp[m|(1ULL<<w)] |= 1u<<w;
  }
  return dp[S-1] != 0;
}

static long fails = 0;
#define CHECK(c, msg) do{ if(!(c)){ fails++; if(fails<20){ printf("FAIL %s\n", msg); dumpg(); } } }while(0)
static void dumpg(void){
  printf("  n=%d edges:", n);
  for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(adj[a]>>b&1) printf(" %d-%d",a,b);
  printf("\n");
}

/* pick a random subset of size k of mask (random if rflag else lowest k) */
static u64 pick(u64 mask, int k, int rflag){
  int idx[64], c=0; for(int v=0; v<n; v++) if(mask>>v&1) idx[c++]=v;
  if(k > c) return ~0ULL;
  if(rflag) for(int i=c-1;i>0;i--){ int j=rndint(i+1); int t=idx[i]; idx[i]=idx[j]; idx[j]=t; }
  u64 r=0; for(int i=0;i<k;i++) r |= 1ULL<<idx[i];
  return r;
}

/* statistics */
static long st_case1=0, st_case2a=0, st_case2b=0, st_rounds[64], st_runs=0;
static long st_ylt_m = 0; /* |Y| < m in setting S */

/* Theorem 1 construction; returns D; checks Lemma G on the way */
static u64 construct(int rflag){
  int m = lmH();
  st_runs++;
  if(2*m >= n){
    if(rflag==0) st_case1++;
    u64 W=0; for(int v=0;v<n;v++) if(n-1-deg(v) >= m) W |= 1ULL<<v;
    CHECK(pc(W) >= n/2+1, "FactA(ii)");
    int a = n-m-1;
    CHECK(a >= 0 && a <= pc(W), "LemmaJ a<=|W|");
    u64 A = pick(W, a, rflag);
    u64 D = FULL & ~A;
    CHECK(pc(D) == m+1, "LemmaJ |D|");
    return D;
  }
  u64 T=0,Q=0,U=0;
  for(int v=0;v<n;v++){ int d=deg(v);
    if(d >= n-1-m) T |= 1ULL<<v;
    if(d >= m) Q |= 1ULL<<v;
    if(d == n-1) U |= 1ULL<<v; }
  u64 Y = FULL & ~Q, P = Q & ~U;
  int u = pc(U), r = m-u+1;
  CHECK(pc(T) >= (n+1)/2, "G(a) |T|");
  CHECK((T & ~Q)==0, "G(a) T in Q");
  for(int v=0;v<n;v++) if(Q>>v&1) CHECK(((Q & ~(1ULL<<v)) & ~adj[v])==0, "G(b) Q clique");
  CHECK(Y != 0, "G(c) Y nonempty");
  CHECK((U & ~Q)==0, "G(c) U in Q");
  for(int y=0;y<n;y++) if(Y>>y&1){ CHECK((U & ~adj[y])==0, "G(c) U in N(y)"); CHECK(deg(y)>=u && deg(y)<=m-1, "G(c) deg y"); }
  CHECK(u <= m-1 && r >= 2, "G(c) r>=2");
  for(int q=0;q<n;q++) if(P>>q&1){ CHECK((nonadj(q) & ~Y)==0, "G(d) nonnbrs in Y"); CHECK(pc(nonadj(q))>=2, "G(e) >=2 nonnbrs"); }
  for(int y=0;y<n;y++) if(Y>>y&1) CHECK(pc(adj[y] & P) <= r-2, "G(f)");
  CHECK((U|P|Y)==FULL && !(U&P) && !(U&Y) && !(P&Y), "G(g) partition");
  if(pc(Y) < m) st_ylt_m++;
  if(pc(Y) >= r){
    if(rflag==0) st_case2a++;
    u64 R = pick(Y, r, rflag), B = 0; int rounds = 0;
    for(;;){
      /* candidates: q in P\B adjacent to >= |R|-1 vertices of R */
      u64 cand = 0;
      for(int q=0;q<n;q++) if((P & ~B)>>q&1) if(pc(adj[q] & R) >= pc(R)-1) cand |= 1ULL<<q;
      if(!cand) break;
      u64 qq = pick(cand, 1, rflag); int q = __builtin_ctzll(qq);
      B |= qq;
      R = pick(R & adj[q], pc(R)-1, rflag);
      CHECK(R != ~0ULL, "Lemma4 R & N(q) too small");
      rounds++;
      CHECK(pc(B)+pc(R) == r, "Lemma4 invariant |B|+|R|=r");
      for(int y=0;y<n;y++) if(R>>y&1) CHECK((B & ~adj[y])==0, "Lemma4 invariant B in A_y");
      CHECK(pc(R) >= 2, "Lemma4 |R|>=2");
    }
    CHECK(rounds <= r-2, "Lemma4 rounds<=r-2");
    st_rounds[rounds]++;
    return U|B|R;
  } else {
    if(rflag==0) st_case2b++;
    int c = m+1-u-pc(Y);
    CHECK(c >= 1 && pc(P) >= c, "case2b sizes");
    return U|Y|pick(P, c, rflag);
  }
}

static void verifyD(u64 D){
  int m = lmH();
  CHECK(D != ~0ULL, "D undefined");
  CHECK(pc(D) <= m+1, "|D| <= m+1");
  CHECK(is2dom(D), "D 2-dominating");
}

static long slack_hist[130]; /* gamma2 - lm - 2 + 64 */

static void test_closed(int K, int exact){
  verifyD(construct(0));
  for(int k=0;k<K;k++) verifyD(construct(1));
  if(exact){
    int g = gamma2(), m = lmH();
    slack_hist[g-m-2+64]++;
    CHECK(g <= m+1, "Theorem1 exact gamma2 <= lm+1");
  }
}

static void setfull(void){ FULL = (n==64)? ~0ULL : (1ULL<<n)-1; }

static void mode_lab(int N, int K){
  n = N; setfull();
  int E = n*(n-1)/2, ea[64], eb[64], c=0;
  for(int a=0;a<n;a++) for(int b=a+1;b<n;b++){ ea[c]=a; eb[c]=b; c++; }
  long total = 1L<<E, ccn=0, cntConn=0, hypCount=0, hypNoHP=0, lcPairs=0, lmPairs=0;
  int small = (N <= 7);
  signed char *TG=NULL,*TL=NULL,*TH=NULL;
  if(small){
    TG=malloc(total); TL=malloc(total); TH=malloc(total);
    for(long g=0; g<total; g++){
      for(int v=0;v<n;v++) adj[v]=0;
      for(int e=0;e<E;e++) if(g>>e&1){ adj[ea[e]] |= 1ULL<<eb[e]; adj[eb[e]] |= 1ULL<<ea[e]; }
      TG[g]=gamma2(); TL[g]=lmH(); TH[g]=hampath();
    }
  }
  for(long g=0; g<total; g++){
    for(int v=0;v<n;v++) adj[v]=0;
    for(int e=0;e<E;e++) if(g>>e&1){ adj[ea[e]] |= 1ULL<<eb[e]; adj[eb[e]] |= 1ULL<<ea[e]; }
    int con = connected();
    if(small){
      int gm = TG[g], m = TL[g], hp = TH[g];
      if(con){ cntConn++;
        if(gm >= m+2){ hypCount++; if(!hp){ hypNoHP++; CHECK(0,"Conjecture 213 counterexample"); } } }
      for(int e=0;e<E;e++) if(!(g>>e&1)){
        int a=ea[e], b=eb[e];
        long g2 = g | (1L<<e);
        lmPairs++;
        CHECK(TG[g2]-TL[g2] >= gm-m, "Lemma M");
        if(deg(a)+deg(b) >= n-1){ lcPairs++; CHECK(!TH[g2] || hp, "Lemma C/BC"); }
      }
    }
    if(!con || complete() || !closedG()) continue;
    ccn++;
    test_closed(K, 1);
  }
  printf("lab n=%d: closed connected non-complete labelled graphs = %ld\n", n, ccn);
  printf("  construction runs %ld; case1 %ld, case2a %ld, case2b %ld; |Y|<m in setting S: %ld runs\n",
         st_runs, st_case1, st_case2a, st_case2b, st_ylt_m);
  printf("  Lemma-4 rounds histogram:"); for(int i=0;i<64;i++) if(st_rounds[i]) printf(" %d:%ld", i, st_rounds[i]); printf("\n");
  printf("  slack gamma2-lm-2 histogram (closed):"); for(int i=0;i<130;i++) if(slack_hist[i]) printf(" %d:%ld", i-64, slack_hist[i]); printf("\n");
  if(small) printf("  connected graphs %ld, with Hyp %ld, Hyp and no HP %ld; Lemma M pairs %ld; Lemma C pairs %ld\n",
                   cntConn, hypCount, hypNoHP, lmPairs, lcPairs);
  printf("  FAILURES %ld\n", fails);
}

/* random maximal non-traceable graphs */
static void mode_mnt(int N, long COUNT){
  n = N; setfull();
  long got=0, notclosed=0, ccn=0;
  for(long it=0; got<COUNT; it++){
    /* start: random sparse graph with no HP: take random graph with a pendant structure */
    for(int v=0;v<n;v++) adj[v]=0;
    double p = 0.1 + 0.4*(rnd()%1000)/1000.0;
    for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if((rnd()%1000) < p*1000){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    if(hampath()) {
      /* force non-traceable: isolate three random vertices to leaves of one vertex */
      int c0 = rndint(n);
      int k = 3 + rndint(n/3);
      for(int i=0;i<k;i++){ int x = rndint(n); if(x==c0) continue;
        for(int w=0;w<n;w++){ adj[w] &= ~(1ULL<<x); } adj[x]=0;
        adj[x] |= 1ULL<<c0; adj[c0] |= 1ULL<<x; }
      if(hampath()) continue;
    }
    /* add random non-edges while non-traceable, until maximal */
    int E=0, ea[400], eb[400];
    for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(!(adj[a]>>b&1)){ ea[E]=a; eb[E]=b; E++; }
    for(int i=E-1;i>0;i--){ int j=rndint(i+1); int t=ea[i]; ea[i]=ea[j]; ea[j]=t; t=eb[i]; eb[i]=eb[j]; eb[j]=t; }
    for(int e=0;e<E;e++){ int a=ea[e], b=eb[e];
      adj[a]|=1ULL<<b; adj[b]|=1ULL<<a;
      if(hampath()){ adj[a]&=~(1ULL<<b); adj[b]&=~(1ULL<<a); } }
    got++;
    /* Lemma C: MNT graph must be closed */
    if(!closedG()){ notclosed++; CHECK(0, "Lemma C: MNT graph not closed"); continue; }
    if(!connected() || complete()) continue;
    ccn++;
    test_closed(5, 1);
  }
  printf("mnt n=%d: MNT graphs %ld (not closed: %ld), connected ones tested %ld\n", n, got, notclosed, ccn);
  printf("  runs %ld; case1 %ld case2a %ld case2b %ld; |Y|<m runs %ld\n", st_runs, st_case1, st_case2a, st_case2b, st_ylt_m);
  printf("  rounds:"); for(int i=0;i<64;i++) if(st_rounds[i]) printf(" %d:%ld", i, st_rounds[i]); printf("\n");
  printf("  slack:"); for(int i=0;i<130;i++) if(slack_hist[i]) printf(" %d:%ld", i-64, slack_hist[i]); printf("\n");
  printf("  FAILURES %ld\n", fails);
}

/* structured: clique Q of size s containing U (size u); each low vertex y adjacent to U,
   to a random set of hubs in P, and to random other low vertices; reject unless closed. */
static void mode_struct(int N, long COUNT){
  n = N; setfull();
  long got=0, tries=0;
  int exact = (N <= 22);
  while(got < COUNT){
    tries++;
    for(int v=0;v<n;v++) adj[v]=0;
    int s = 1 + rndint(n-1);           /* |Q| */
    int u = rndint(s+1 < 6 ? s+1 : 6);  /* |U| target */
    for(int a=0;a<s;a++) for(int b=a+1;b<s;b++){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    for(int a=0;a<u;a++) for(int b=s;b<n;b++){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    /* hubs: a few vertices of P adjacent to many low vertices */
    int nh = rndint(4);
    for(int h=0; h<nh && u+h<s; h++){
      int frac = rndint(100);
      for(int y=s;y<n;y++) if(rndint(100) < frac){ adj[u+h]|=1ULL<<y; adj[y]|=1ULL<<(u+h); }
    }
    int pe = rndint(30);
    for(int q=u+nh;q<s;q++) for(int y=s;y<n;y++) if(rndint(100) < pe/3){ adj[q]|=1ULL<<y; adj[y]|=1ULL<<q; }
    int py = rndint(20);
    for(int a=s;a<n;a++) for(int b=a+1;b<n;b++) if(rndint(100) < py){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    if(!connected() || complete() || !closedG()) continue;
    got++;
    test_closed(20, exact);
  }
  printf("struct n=%d: closed connected non-complete graphs %ld (tries %ld)\n", n, got, tries);
  printf("  runs %ld; case1 %ld case2a %ld case2b %ld; |Y|<m runs %ld\n", st_runs, st_case1, st_case2a, st_case2b, st_ylt_m);
  printf("  rounds:"); for(int i=0;i<64;i++) if(st_rounds[i]) printf(" %d:%ld", i, st_rounds[i]); printf("\n");
  if(exact){ printf("  slack:"); for(int i=0;i<130;i++) if(slack_hist[i]) printf(" %d:%ld", i-64, slack_hist[i]); printf("\n"); }
  printf("  FAILURES %ld\n", fails);
}

/* hub family: U (size u) universal; H hubs adjacent to all of W; P' vertices each adjacent to
   kk random vertices of W; Z adjacent only to U (plus optional random edges inside W u Z);
   Q = U u H u P' a clique. Rejected unless closed, connected, non-complete. */
static void mode_hub(int N, long COUNT){
  n = N; setfull();
  long got=0, tries=0; int exact = (N <= 22);
  while(got < COUNT){
    tries++;
    for(int v=0;v<n;v++) adj[v]=0;
    int u = rndint(4), h = 1 + rndint(5);
    int rest = n - u - h; if(rest < 4) continue;
    int w = 2 + rndint(rest-2), z = rndint(rest - w + 1), pp = rest - w - z;
    int s = u+h+pp;           /* clique part: 0..s-1 ; W: s..s+w-1 ; Z: s+w..n-1 */
    for(int a=0;a<s;a++) for(int b=a+1;b<s;b++){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    for(int a=0;a<u;a++) for(int b=s;b<n;b++){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    for(int a=u;a<u+h;a++) for(int b=s;b<s+w;b++){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    int kk = rndint(4);
    for(int a=u+h;a<s;a++) for(int t=0;t<kk;t++){ int b = s + rndint(w); adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    int py = rndint(3) ? 0 : rndint(15);
    for(int a=s;a<n;a++) for(int b=a+1;b<n;b++) if(rndint(100) < py){ adj[a]|=1ULL<<b; adj[b]|=1ULL<<a; }
    if(!connected() || complete() || !closedG()) continue;
    got++;
    test_closed(30, exact);
  }
  printf("hub n=%d: closed connected non-complete graphs %ld (tries %ld)\n", n, got, tries);
  printf("  runs %ld; case1 %ld case2a %ld case2b %ld; |Y|<m runs %ld\n", st_runs, st_case1, st_case2a, st_case2b, st_ylt_m);
  printf("  rounds:"); for(int i=0;i<64;i++) if(st_rounds[i]) printf(" %d:%ld", i, st_rounds[i]); printf("\n");
  if(exact){ printf("  slack:"); for(int i=0;i<130;i++) if(slack_hist[i]) printf(" %d:%ld", i-64, slack_hist[i]); printf("\n"); }
  printf("  FAILURES %ld\n", fails);
}

int main(int argc, char **argv){
  if(argc < 3){ fprintf(stderr,"usage: see header\n"); return 1; }
  int N = atoi(argv[2]);
  if(N <= 20){ dp = malloc(sizeof(uint32_t) << N); }
  if(!strcmp(argv[1],"lab")){ mode_lab(N, argc>3? atoi(argv[3]) : 2); }
  else if(!strcmp(argv[1],"mnt")){ rs ^= (u64)atol(argv[4])*0x9E3779B97F4A7C15ULL; mode_mnt(N, atol(argv[3])); }
  else if(!strcmp(argv[1],"hub")){ rs ^= (u64)atol(argv[4])*0x9E3779B97F4A7C15ULL; mode_hub(N, atol(argv[3])); }
  else if(!strcmp(argv[1],"struct")){ rs ^= (u64)atol(argv[4])*0x9E3779B97F4A7C15ULL; mode_struct(N, atol(argv[3])); }
  return fails ? 2 : 0;
}
