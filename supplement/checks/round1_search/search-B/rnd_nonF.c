/* search-B heuristic: random edge-maximal non-traceable connected graphs on n vertices (n<=18),
 * slack = gamma_2(H) - lm(H) - 2 for H = complement.  By Lemma M a counterexample exists iff some
 * edge-maximal non-traceable connected graph has slack >= 0.
 * Sampling: random labelled tree (Pruefer) that is not a path, then a random order of the non-edges,
 * each added when the graph stays non-traceable (one pass gives an edge-maximal graph, since
 * traceability is monotone). Optionally (mode 1) start from a random tree whose max degree >= 3 chosen
 * among several, or (mode 2) start from a "spider" (K_{1,3} subdivided) to diversify.
 * Usage: rnd N SAMPLES SEED   -> prints slack histogram and every sample with slack >= -1 whose
 *        structure is not K_s v ((s+1)K_1 u K_t) (checked by: some S, |S|=s, G-S has >= s+1 isolated
 *        vertices and n-2s-1>=1, which for a maximal graph identifies F(n,s)).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint32_t set;
static int n;
static set adj[32];
static set *endm;
static uint64_t rs;
static uint64_t rnd64(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static int rndint(int k){ return (int)(rnd64()%k); }
static inline int pc(set x){ return __builtin_popcount(x); }

/* returns 1 if traceable; else fills reach[a] = {b : G+ab traceable} */
static int dp(set *reach){
  uint32_t full=(1u<<n)-1;
  endm[0]=0;
  for(uint32_t M=1; M<=full; M++){
    set e=0;
    if((M&(M-1))==0) e=M;
    else { set m=M; while(m){ int v=__builtin_ctz(m); m&=m-1; if(endm[M^(1u<<v)] & adj[v]) e|=1u<<v; } }
    endm[M]=e;
  }
  if(endm[full]) return 1;
  for(int a=0;a<n;a++) reach[a]=0;
  for(uint32_t M=1; M<full; M++){
    set e=endm[M]; if(!e) continue; set f=endm[full^M]; if(!f) continue;
    while(e){ int a=__builtin_ctz(e); e&=e-1; reach[a]|=f; }
  }
  return 0;
}
static int is2dom(const set *h, set D){
  set one=0,two=0,d=D; while(d){ int u=__builtin_ctz(d); d&=d-1; two|=one&h[u]; one|=h[u]; }
  set all=(n==32)?0xffffffffu:((1u<<n)-1); return ((all&~D)&~two)==0;
}
static int g2rec(const set *h, set D, int start, int left){
  if(left==0) return is2dom(h,D);
  for(int v=start; v<=n-left; v++) if(g2rec(h,D|(1u<<v),v+1,left-1)) return 1;
  return 0;
}
static int gamma2(const set *h){
  set forced=0; for(int v=0;v<n;v++) if(pc(h[v])<=1) forced|=1u<<v;
  /* enumerate supersets of forced */
  int fv[32], m=0; for(int v=0;v<n;v++) if(!(forced>>v&1)) fv[m++]=v;
  set hh[32]; memcpy(hh,h,sizeof hh);
  for(int k=0;k<=m;k++){
    /* combinations of k among fv */
    int idx[32]; for(int i=0;i<k;i++) idx[i]=i;
    while(1){
      set D=forced; for(int i=0;i<k;i++) D|=1u<<fv[idx[i]];
      if(is2dom(hh,D)) return pc(forced)+k;
      int i=k-1; while(i>=0 && idx[i]==m-k+i) i--; if(i<0) break;
      idx[i]++; for(int j=i+1;j<k;j++) idx[j]=idx[j-1]+1;
    }
  }
  return n;
}
static int lowmed(const set *h){
  int d[32]; for(int v=0;v<n;v++) d[v]=pc(h[v]);
  for(int i=1;i<n;i++){ int x=d[i],j=i-1; while(j>=0&&d[j]>x){d[j+1]=d[j];j--;} d[j+1]=x; }
  return d[(n-1)/2];
}
static int isF(void){
  /* exists s>=1, n-2s-1>=1, S of size s: G-S has >= s+1 isolated vertices. Check via: a vertex v is
     isolated in G-S iff N(v) subset of S. Try S = N(v) for each v with deg s. */
  for(int v=0;v<n;v++){
    set S=adj[v]; int s=pc(S); if(s<1 || n-2*s-1<1) continue;
    int iso=0; for(int w=0;w<n;w++) if(!(S>>w&1) && (adj[w]&~S)==0) iso++;
    if(iso>=s+1) return s;
  }
  return 0;
}
static void maximise(void){
  int ea[600], eb[600], ne=0;
  for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(!(adj[a]>>b&1)){ ea[ne]=a; eb[ne]=b; ne++; }
  for(int i=ne-1;i>0;i--){ int j=rndint(i+1); int t=ea[i]; ea[i]=ea[j]; ea[j]=t; t=eb[i]; eb[i]=eb[j]; eb[j]=t; }
  set reach[32];
  if(dp(reach)){ fprintf(stderr,"bug: traceable\n"); exit(2); }
  for(int i=0;i<ne;i++){ int a=ea[i], b=eb[i]; if(reach[a]>>b&1) continue;
    adj[a]|=1u<<b; adj[b]|=1u<<a; if(dp(reach)){ fprintf(stderr,"bug\n"); exit(3);} }
}
static int connected(void){ set seen=1, fr=1; while(fr){ set nf=0; for(int v=0;v<n;v++) if(fr>>v&1) nf|=adj[v]; nf&=~seen; seen|=nf; fr=nf; } return seen==(set)((1u<<n)-1); }
static int slackof(void){ set h[32]; set all=(1u<<n)-1; for(int v=0;v<n;v++) h[v]=all&~adj[v]&~(1u<<v); return gamma2(h)-lowmed(h)-2; }
static void printg(const char *tag, int sl){ printf("%s n=%d slack=%d:",tag,n,sl); for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(adj[a]>>b&1) printf(" %d-%d",a,b); printf("\n"); fflush(stdout); }
/* local search: rnd N ITERS SEED ls  */
static int localsearch(long iters){
  set best[32]; int bestsc=-999; long seenNF=0;
  set cur[32]; int cursc=-999;
  for(long it=0; it<iters; it++){
    if(it%3000==0){ /* restart from random tree */
      for(int v=0;v<n;v++) adj[v]=0;
      /* random tree: attach each vertex to a random earlier vertex, relabel not needed */
      do { for(int v=0;v<n;v++) adj[v]=0; for(int v=1;v<n;v++){ int p=rndint(v); adj[v]|=1u<<p; adj[p]|=1u<<v; } set r[32]; if(!dp(r)) break; } while(1);
      maximise(); memcpy(cur,adj,sizeof cur); cursc=-999;
    } else {
      memcpy(adj,cur,sizeof cur);
      int r=1+rndint(2*n);
      for(int k=0;k<r;k++){ int a=rndint(n); if(!adj[a]) continue; int d=pc(adj[a]); int j=rndint(d); set x=adj[a];
        while(j--) x&=x-1; int b=__builtin_ctz(x); adj[a]&=~(1u<<b); adj[b]&=~(1u<<a); }
      if(!connected()) continue;
      maximise();
    }
    int sl=slackof(); int f=isF();
    int sc = sl*4 - (f?9:0);
    if(sl>=0) printg("COUNTEREXAMPLE",sl);
    if(!f && sl>=-1){ seenNF++; if(seenNF<=20) printg("nonF-near-miss",sl); }
    if(sc>=cursc || rndint(20)==0){ memcpy(cur,adj,sizeof cur); cursc=sc; }
    if(sc>bestsc){ bestsc=sc; memcpy(best,adj,sizeof best); }
  }
  memcpy(adj,best,sizeof best);
  printf("localsearch n=%d iters=%ld bestscore=%d nonF_slack>=-1_hits=%ld\n",n,iters,bestsc,seenNF);
  printg("best",slackof());
  return 0;
}
int main(int argc,char**argv){
  n=atoi(argv[1]); long samples=atol(argv[2]); rs=strtoull(argv[3],0,10)*0x9E3779B97F4A7C15ULL+1;
  endm=malloc(sizeof(set)<<n);
  if(argc>4 && !strcmp(argv[4],"ls")) return localsearch(samples);
  long hist[64]={0}; int best=-99; long nF=0;
  for(long it=0; it<samples; it++){
    /* random non-path tree via Pruefer */
    for(int v=0;v<n;v++) adj[v]=0;
    int pr[32], deg[32];
    do{
      for(int i=0;i<n-2;i++) pr[i]=rndint(n);
      for(int v=0;v<n;v++) deg[v]=1; for(int i=0;i<n-2;i++) deg[pr[i]]++;
      int mx=0; for(int v=0;v<n;v++) if(deg[v]>mx) mx=deg[v];
      if(mx>=3) break;
    } while(1);
    for(int v=0;v<n;v++) adj[v]=0;
    int dg[32]; memcpy(dg,deg,sizeof deg);
    for(int i=0;i<n-2;i++){ int leaf=-1; for(int v=0;v<n;v++) if(dg[v]==1){ leaf=v; break; }
      int p=pr[i]; adj[leaf]|=1u<<p; adj[p]|=1u<<leaf; dg[leaf]--; dg[p]--; }
    { int a=-1,b=-1; for(int v=0;v<n;v++) if(dg[v]==1){ if(a<0) a=v; else b=v; } adj[a]|=1u<<b; adj[b]|=1u<<a; }
    /* random order of non-edges */
    int ea[600], eb[600], ne=0;
    for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(!(adj[a]>>b&1)){ ea[ne]=a; eb[ne]=b; ne++; }
    for(int i=ne-1;i>0;i--){ int j=rndint(i+1); int t=ea[i]; ea[i]=ea[j]; ea[j]=t; t=eb[i]; eb[i]=eb[j]; eb[j]=t; }
    set reach[32];
    if(dp(reach)){ fprintf(stderr,"bug: tree traceable\n"); return 2; }
    for(int i=0;i<ne;i++){
      int a=ea[i], b=eb[i]; if(adj[a]>>b&1) continue;
      if(reach[a]>>b&1) continue;
      adj[a]|=1u<<b; adj[b]|=1u<<a;
      if(dp(reach)){ fprintf(stderr,"bug\n"); return 3; }
    }
    set h[32]; set all=(1u<<n)-1; for(int v=0;v<n;v++) h[v]=all&~adj[v]&~(1u<<v);
    int sl=gamma2(h)-lowmed(h)-2;
    hist[sl+32]++; if(sl>best) best=sl;
    int f=isF(); if(f) nF++;
    if(sl>=-1 && !f){
      printf("n=%d slack=%d nonF:",n,sl);
      for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(adj[a]>>b&1) printf(" %d-%d",a,b);
      printf("\n");
    }
    if(sl>=0){ printf("COUNTEREXAMPLE?\n"); }
  }
  printf("n=%d samples=%ld best=%d F-type=%ld hist:",n,samples,best,nF);
  for(int i=0;i<64;i++) if(hist[i]) printf(" %d:%ld",i-32,hist[i]);
  printf("\n");
  return 0;
}
