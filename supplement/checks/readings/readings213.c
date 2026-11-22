/* readings213.c -- status213 reviewer, 21 Nov 2026.
   Written from scratch; shares no code with tools/wowii213 or the prover's programs.
   For every labelled graph G on n vertices (2 <= n <= NMAX), connected, H = complement:
   tests Conjecture 213 ("hyp => G traceable") under several readings of the definitions:
     median: LM  = lower median (d_{n/2} even n, d_{(n+1)/2} odd n)        [catalogue def 68]
             LIT = odd n read literally as d_{(n+1)/2+1} (the printed '+1'), even n as LM
             UM  = upper median (d_{n/2+1} even n, d_{(n+1)/2} odd n)
     gamma2: GE  = every vertex outside D has >= 2 neighbours in D           [standard]
             EQ  = every vertex outside D has exactly 2 neighbours in D      [literal alternative]
   hyp: 2 + median(H) <= gamma2(H).  Counts counterexamples (hyp and not traceable)
   and the number of graphs with hyp and slack equality.  Labelled count (no isomorphism
   reduction), so counts are of labelled graphs.
   Build: cc -O2 -o readings213 readings213.c ;  run: ./readings213 [NMAX]  (default 7) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n;
static unsigned adj[16];   /* adjacency of G as bitmasks */
static unsigned hadj[16];  /* adjacency of H */

static int popc(unsigned x){ int c=0; while(x){ x&=x-1; c++; } return c; }

static int connected(void){
  unsigned seen=1, frontier=1;
  while(frontier){ unsigned nf=0; for(int v=0;v<n;v++) if(frontier>>v&1) nf|=adj[v]; nf&=~seen; seen|=nf; frontier=nf; }
  return seen==(1u<<n)-1;
}

/* Hamiltonian path in G by DP over (subset, end vertex) */
static unsigned char dp[1<<10][10];
static int traceable(void){
  unsigned full=(1u<<n)-1;
  for(unsigned s=0;s<=full;s++) for(int v=0;v<n;v++) dp[s][v]=0;
  for(int v=0;v<n;v++) dp[1u<<v][v]=1;
  for(unsigned s=1;s<=full;s++) for(int v=0;v<n;v++) if(dp[s][v]){
    if(s==full) return 1;
    unsigned nb=adj[v]&~s;
    for(int w=0;w<n;w++) if(nb>>w&1) dp[s|1u<<w][w]=1;
  }
  return 0;
}

/* gamma_2 of H: smallest D with every v not in D having >=2 (mode 0) or ==2 (mode 1) H-nbrs in D */
static int gamma2(int exact){
  unsigned full=(1u<<n)-1; int best=n;
  for(unsigned D=0; D<=full; D++){
    int k=popc(D); if(k>=best) continue;
    int ok=1;
    for(int v=0; v<n && ok; v++) if(!(D>>v&1)){
      int c=popc(hadj[v]&D);
      if(exact ? (c!=2) : (c<2)) ok=0;
    }
    if(ok) best=k;
  }
  return best;
}

static int cmpint(const void*a,const void*b){ return *(const int*)a-*(const int*)b; }

int main(int argc,char**argv){
  int NMAX = argc>1 ? atoi(argv[1]) : 7;
  if(NMAX>9) NMAX=9;
  printf("n | connected | nontraceable | CE[LM,GE] CE[LIT,GE] CE[UM,GE] CE[LM,EQ] CE[LIT,EQ] CE[UM,EQ] | hyp[LM,GE] tight[LM,GE]\n");
  for(n=2;n<=NMAX;n++){
    int E=n*(n-1)/2; int eu[64],ev[64],k=0;
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ eu[k]=i; ev[k]=j; k++; }
    long long conn=0, nontr=0, ce[3][2]={{0}}, hyp0=0, tight0=0;
    long long firstce_mask[3][2]; for(int a=0;a<3;a++) for(int b=0;b<2;b++) firstce_mask[a][b]=-1;
    for(long long m=0; m < (1LL<<E); m++){
      memset(adj,0,sizeof adj);
      for(int e=0;e<E;e++) if(m>>e&1){ adj[eu[e]]|=1u<<ev[e]; adj[ev[e]]|=1u<<eu[e]; }
      if(!connected()) continue;
      conn++;
      unsigned full=(1u<<n)-1;
      int dH[16];
      for(int v=0;v<n;v++){ hadj[v]=full & ~adj[v] & ~(1u<<v); dH[v]=popc(hadj[v]); }
      qsort(dH,n,sizeof(int),cmpint);       /* dH[0] <= ... <= dH[n-1]; d_i = dH[i-1] */
      int med[3];
      if(n%2==0){ med[0]=dH[n/2-1]; med[1]=dH[n/2-1]; med[2]=dH[n/2]; }
      else      { med[0]=dH[(n+1)/2-1]; med[1]=dH[(n+1)/2]; med[2]=dH[(n+1)/2-1]; }
      int g[2]; g[0]=gamma2(0); g[1]=gamma2(1);
      int anyhyp=0;
      for(int a=0;a<3;a++) for(int b=0;b<2;b++) if(2+med[a]<=g[b]) anyhyp=1;
      if(2+med[0]<=g[0]){ hyp0++; if(2+med[0]==g[0]) tight0++; }
      int tr = anyhyp ? traceable() : 1;
      if(!anyhyp){ /* still count non-traceable for the record */ if(!traceable()) nontr++; continue; }
      if(!tr) nontr++;
      for(int a=0;a<3;a++) for(int b=0;b<2;b++) if(2+med[a]<=g[b] && !tr){ ce[a][b]++; if(firstce_mask[a][b]<0) firstce_mask[a][b]=m; }
    }
    printf("%d | %lld | %lld | %lld %lld %lld %lld %lld %lld | %lld %lld\n", n, conn, nontr,
      ce[0][0],ce[1][0],ce[2][0],ce[0][1],ce[1][1],ce[2][1], hyp0, tight0);
    const char*mn[3]={"LM","LIT","UM"}; const char*gn[2]={"GE","EQ"};
    for(int a=0;a<3;a++) for(int b=0;b<2;b++) if(firstce_mask[a][b]>=0){
      printf("   first CE [%s,%s] edges:", mn[a], gn[b]);
      for(int e=0;e<E;e++) if(firstce_mask[a][b]>>e&1) printf(" %d-%d",eu[e],ev[e]);
      printf("\n");
    }
    fflush(stdout);
  }
  return 0;
}
