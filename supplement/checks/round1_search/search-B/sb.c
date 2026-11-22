/* search-B: independent exhaustive search for WoWII Conjecture 213.
 * Own generator (vertex addition + own canonical form + hash dedup),
 * own invariants (Hamiltonian path by DFS, gamma_2 by subset search, lower median).
 *
 * Usage:
 *   sb full NMAX OUTDIR      : all connected graphs n=2..NMAX, stats + list of non-traceable
 *   sb nt NTARGET OUTDIR     : connected non-traceable graphs on NTARGET vertices only,
 *                              by edge addition from non-path trees (down-closed family)
 * Graph key: bits of the upper triangle in order (0,1),(0,2),...,(0,n-1),(1,2),... read MSB first.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 12
typedef uint16_t set;
static int N;

/* ---------------- canonical form ---------------- */
typedef struct { int nc; set c[MAXN]; } part_t;

static inline int pc(unsigned x){ return __builtin_popcount(x); }

static void refine(const set *adj, part_t *p){
  int changed = 1;
  while(changed){
    changed = 0;
    for(int s=0; s<p->nc && !changed; s++){
      set S = p->c[s];
      for(int x=0; x<p->nc; x++){
        set X = p->c[x];
        if(pc(X)==1) continue;
        int cnt[MAXN]; int lo=99, hi=-1;
        for(int v=0; v<N; v++) if(X>>v&1){ cnt[v]=pc(adj[v]&S); if(cnt[v]<lo)lo=cnt[v]; if(cnt[v]>hi)hi=cnt[v]; }
        if(lo==hi) continue;
        /* split X into fragments by count ascending */
        set frag[MAXN+1]; int nf=0;
        for(int k=lo;k<=hi;k++){ set F=0; for(int v=0;v<N;v++) if((X>>v&1)&&cnt[v]==k) F|=1u<<v; if(F) frag[nf++]=F; }
        /* shift */
        for(int j=p->nc-1;j>x;j--) p->c[j+nf-1]=p->c[j];
        for(int j=0;j<nf;j++) p->c[x+j]=frag[j];
        p->nc += nf-1;
        changed = 1; break;
      }
    }
  }
}

static uint64_t bestkey, firstkey; static int haveleaf;
static int firstperm[MAXN], bestperm[MAXN];
#define MAXGEN 64
static int gens[MAXGEN][MAXN]; static int ngens;
static const set *G_adj;

static uint64_t leafkey(const part_t *p, int *perm){
  for(int i=0;i<N;i++) perm[i]=__builtin_ctz(p->c[i]);
  uint64_t k=0;
  for(int i=0;i<N;i++) for(int j=i+1;j<N;j++) k = (k<<1) | ((G_adj[perm[i]]>>perm[j])&1);
  return k;
}

static void addgen(const int *from, const int *to){
  if(ngens>=MAXGEN) return;
  int g[MAXN]; int id=1;
  for(int i=0;i<N;i++){ g[from[i]]=to[i]; if(from[i]!=to[i]) id=0; }
  if(id) return;
  memcpy(gens[ngens++], g, sizeof(int)*N);
}

static int ufind(int *u,int x){ while(u[x]!=x){ u[x]=u[u[x]]; x=u[x]; } return x; }

static void search(part_t *p, set fixed){
  refine(G_adj, p);
  int t=-1;
  for(int i=0;i<p->nc;i++) if(pc(p->c[i])>1){ t=i; break; }
  if(t<0){
    int perm[MAXN]; uint64_t k=leafkey(p,perm);
    if(!haveleaf){ haveleaf=1; firstkey=bestkey=k; memcpy(firstperm,perm,sizeof perm); memcpy(bestperm,perm,sizeof perm); return; }
    if(k==firstkey) addgen(firstperm,perm);
    else if(k==bestkey) addgen(bestperm,perm);
    else if(k>bestkey){ bestkey=k; memcpy(bestperm,perm,sizeof perm); }
    return;
  }
  set T=p->c[t]; set explored=0;
  for(int v=0; v<N; v++) if(T>>v&1){
    if(explored){
      /* orbits under generators fixing 'fixed' pointwise */
      int u[MAXN]; for(int i=0;i<N;i++) u[i]=i;
      for(int g=0; g<ngens; g++){
        int ok=1; for(int w=0;w<N;w++) if((fixed>>w&1) && gens[g][w]!=w){ ok=0; break; }
        if(!ok) continue;
        for(int w=0;w<N;w++){ int a=ufind(u,w), b=ufind(u,gens[g][w]); if(a!=b) u[a]=b; }
      }
      int skip=0; int rv=ufind(u,v);
      for(int w=0;w<N;w++) if((explored>>w&1) && ufind(u,w)==rv){ skip=1; break; }
      if(skip) continue;
    }
    part_t q; q.nc=p->nc+1;
    for(int i=0;i<t;i++) q.c[i]=p->c[i];
    q.c[t]=1u<<v; q.c[t+1]=T&~(1u<<v);
    for(int i=t+1;i<p->nc;i++) q.c[i+1]=p->c[i];
    search(&q, fixed|(1u<<v));
    explored |= 1u<<v;
  }
}

static uint64_t canon(const set *adj){
  G_adj=adj; haveleaf=0; ngens=0;
  part_t p; p.nc=1; p.c[0]=(set)((1u<<N)-1);
  search(&p,0);
  return bestkey;
}

static void decode(uint64_t k, int n, set *adj){
  int b=n*(n-1)/2-1;
  for(int i=0;i<n;i++) adj[i]=0;
  for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ if((k>>b)&1){ adj[i]|=1u<<j; adj[j]|=1u<<i; } b--; }
}

/* ---------------- hash set ---------------- */
typedef struct { uint64_t *t; uint64_t mask; uint64_t cnt; } hset;
static void hinit(hset *h, int lg){ h->t=calloc(1ULL<<lg, 8); h->mask=(1ULL<<lg)-1; h->cnt=0; if(!h->t){fprintf(stderr,"oom\n");exit(1);} }
static int hins(hset *h, uint64_t k){ /* returns 1 if new */
  uint64_t key = k | (1ULL<<63);
  uint64_t i = (k*0x9E3779B97F4A7C15ULL) >> 20; i&=h->mask;
  while(h->t[i]){ if(h->t[i]==key) return 0; i=(i+1)&h->mask; }
  h->t[i]=key; h->cnt++; return 1;
}

/* ---------------- invariants ---------------- */
static int conn(const set *adj, int n){
  set seen=1, fr=1, all=(set)((1u<<n)-1);
  while(fr){ set nf=0; for(int v=0;v<n;v++) if(fr>>v&1) nf|=adj[v]; nf&=~seen; seen|=nf; fr=nf; }
  return seen==all;
}
static set ALL;
static int dfs(const set *adj, int v, set vis){
  if(vis==ALL) return 1;
  set c = adj[v] & ~vis;
  while(c){ int w=__builtin_ctz(c); c&=c-1; if(dfs(adj,w,vis|(1u<<w))) return 1; }
  return 0;
}
static int traceable(const set *adj, int n){
  ALL=(set)((1u<<n)-1);
  if(n==1) return 1;
  /* quick reject: >2 vertices of degree 1 or a degree 0 vertex */
  int d1=0; for(int v=0;v<n;v++){ int d=pc(adj[v]); if(d==0) return 0; if(d==1) d1++; }
  if(d1>2) return 0;
  /* start from degree-1 vertex if any, else all */
  for(int v=0;v<n;v++) if(pc(adj[v])==1) return dfs(adj,v,1u<<v);
  for(int v=0;v<n;v++) if(dfs(adj,v,1u<<v)) return 1;
  return 0;
}
static int is2dom(const set *h, int n, set D){
  set one=0,two=0; set d=D;
  while(d){ int u=__builtin_ctz(d); d&=d-1; two|=one&h[u]; one|=h[u]; }
  set all=(set)((1u<<n)-1);
  return ((all&~D)&~two)==0;
}
/* smallest k>=? such that a 2-dominating set of size k exists; if stopk>0, stop after size stopk
   and return stopk+1 to mean "> stopk" */
static int gamma2(const set *h, int n, int stopk){
  set forced=0; for(int v=0;v<n;v++) if(pc(h[v])<=1) forced|=1u<<v;
  set free_= (set)(((1u<<n)-1)&~forced);
  int f=pc(forced); int nfree=pc(free_);
  int fv[MAXN]; int m=0; for(int v=0;v<n;v++) if(free_>>v&1) fv[m++]=v;
  for(int k=f;k<=n;k++){
    if(stopk>0 && k>stopk) return stopk+1;
    int r=k-f; if(r>nfree) break;
    if(r==0){ if(is2dom(h,n,forced)) return k; continue; }
    unsigned s=(1u<<r)-1, lim=1u<<nfree;
    while(s<lim){
      set D=forced; unsigned t=s; while(t){ int i=__builtin_ctz(t); t&=t-1; D|=1u<<fv[i]; }
      if(is2dom(h,n,D)) return k;
      unsigned c=s&-s, rr=s+c; s=(((rr^s)>>2)/c)|rr;
    }
  }
  return n; /* not reached */
}
static int lowmed(const set *h, int n){
  int d[MAXN]; for(int v=0;v<n;v++) d[v]=pc(h[v]);
  for(int i=1;i<n;i++){ int x=d[i],j=i-1; while(j>=0&&d[j]>x){d[j+1]=d[j];j--;} d[j+1]=x; }
  return d[(n-1)/2];
}

/* For a non-traceable G: reach[a] = set of b such that G+ab is traceable.
   end[M] = vertices that are an end of a path covering exactly M (subset DP).
   G+ab traceable (G not) iff some M has a in end[M] and b in end[V\M]. */
static set endm[1<<MAXN];
static int ext_reach(const set *adj, int n, set *reach){
  int full=(1<<n)-1;
  endm[0]=0;
  for(int M=1; M<=full; M++){
    set e=0;
    if((M&(M-1))==0) e=(set)M;
    else for(int v=0; v<n; v++) if(M>>v&1){ if(endm[M^(1<<v)] & adj[v]) e|=1u<<v; }
    endm[M]=e;
  }
  if(endm[full]) return 1; /* traceable */
  for(int a=0;a<n;a++) reach[a]=0;
  for(int M=1; M<full; M++){
    set e=endm[M]; if(!e) continue; set f=endm[full^M]; if(!f) continue;
    while(e){ int a=__builtin_ctz(e); e&=e-1; reach[a]|=f; }
  }
  return 0;
}

typedef struct { long conn, hyp, nt, cex; int best; long hist[64]; } stats_t;

static void edges_str(const set *adj, int n, char *buf){
  buf[0]=0; int first=1;
  for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i]>>j&1){ buf+=sprintf(buf,"%s%d-%d",first?"":" ",i,j); first=0; }
}

static void analyse_k(uint64_t k, int n, stats_t *st, FILE *ntf, int trk){
  set g[MAXN], h[MAXN]; decode(k,n,g);
  set all=(set)((1u<<n)-1);
  for(int v=0;v<n;v++) h[v]=all&~g[v]&~(1u<<v);
  st->conn++;
  int lm=lowmed(h,n);
  int tr= trk>=0 ? trk : traceable(g,n);
  int need = lm+2; /* hypothesis: gamma2 >= need */
  int g2;
  if(!tr){ g2=gamma2(h,n,0); }
  else {
    if(need>n){ g2=-1; }
    else { g2=gamma2(h,n,need-1); if(g2>=need) g2=gamma2(h,n,0); }
  }
  int hyp = (g2>=0 && g2>=need);
  if(hyp) st->hyp++;
  if(!tr){
    st->nt++;
    int slack=g2-lm-2;
    if(slack>st->best) st->best=slack;
    st->hist[slack+32]++;
    if(slack>=0) st->cex++;
    if(ntf){ char buf[1024]; edges_str(g,n,buf); int m=0; for(int v=0;v<n;v++) m+=pc(g[v]); m/=2;
      fprintf(ntf,"%d\t%d\t%d\t%d\t%d\t%016llx\t%s\n", n, slack, g2, lm, m, (unsigned long long)k, buf); }
  }
}

static void analyse(uint64_t k, int n, stats_t *st, FILE *ntf){ analyse_k(k,n,st,ntf,-1); }

static void report(int n, stats_t *st, FILE *out){
  fprintf(out,"n=%d connected=%ld hypothesis=%ld non_traceable=%ld counterexamples=%ld best_slack_nt=%d  slack-hist:",
    n, st->conn, st->hyp, st->nt, st->cex, st->nt?st->best:-99);
  for(int i=0;i<64;i++) if(st->hist[i]) fprintf(out," %d:%ld", i-32, st->hist[i]);
  fprintf(out,"\n"); fflush(out);
}

int main(int argc, char **argv){
  if(argc<4){ fprintf(stderr,"usage\n"); return 1; }
  int nmax=atoi(argv[2]); const char *od=argv[3];
  char fn[512];
  if(!strcmp(argv[1],"full")){
    /* level 1: single vertex */
    uint64_t *cur=malloc(8); cur[0]=0; long ncur=1;
    for(int n=2;n<=nmax;n++){
      N=n;
      int lg = n<=7?16: n==8?18: n==9?21: 25;
      hset hs; hinit(&hs,lg);
      long cap=1024; uint64_t *nxt=malloc(cap*8); long nn=0;
      for(long i=0;i<ncur;i++){
        set p[MAXN]; decode(cur[i],n-1,p);
        for(unsigned S=1; S<(1u<<(n-1)); S++){
          set c[MAXN]; for(int v=0;v<n-1;v++) c[v]=p[v] | ((S>>v&1)?(1u<<(n-1)):0);
          c[n-1]=(set)S;
          uint64_t k=canon(c);
          if(hins(&hs,k)){ if(nn==cap){cap*=2; nxt=realloc(nxt,cap*8);} nxt[nn++]=k; }
        }
      }
      free(hs.t); free(cur); cur=nxt; ncur=nn;
      stats_t st; memset(&st,0,sizeof st); st.best=-99;
      snprintf(fn,sizeof fn,"%s/nt_n%d.tsv",od,n); FILE *ntf=fopen(fn,"w");
      for(long i=0;i<ncur;i++) analyse(cur[i],n,&st,ntf);
      fclose(ntf);
      report(n,&st,stdout);
      if(n<=9){ snprintf(fn,sizeof fn,"%s/conn_n%d.keys",od,n); FILE *f=fopen(fn,"w");
        for(long i=0;i<ncur;i++) fprintf(f,"%016llx\n",(unsigned long long)cur[i]); fclose(f); }
    }
  } else if(!strcmp(argv[1],"chv")){
    /* sb chv N KEYFILE : test "Chvatal path-condition violated => slack <= -1" on all graphs listed */
    int n=nmax; N=n; FILE *f=fopen(od,"r"); char line[64];
    long tot=0, bad=0, viol=0, violtr=0; long hs[64]={0};
    while(fgets(line,sizeof line,f)){
      uint64_t k=strtoull(line,0,16); set g[MAXN],h[MAXN]; decode(k,n,g);
      set all=(set)((1u<<n)-1); for(int v=0;v<n;v++) h[v]=all&~g[v]&~(1u<<v);
      int d[MAXN]; for(int v=0;v<n;v++) d[v]=pc(g[v]);
      for(int i=1;i<n;i++){ int x=d[i],j=i-1; while(j>=0&&d[j]>x){d[j+1]=d[j];j--;} d[j+1]=x; }
      int cv=0; for(int i=1; 2*i<n+1; i++) if(d[i-1]<=i-1 && d[n-i]<=n-i-1) cv=1;
      tot++;
      if(!cv) continue;
      viol++; if(traceable(g,n)) violtr++;
      int lm=lowmed(h,n); int g2=gamma2(h,n,0); int sl=g2-lm-2; hs[sl+32]++;
      if(sl>=0){ bad++; if(bad<=5){ char b[1024]; edges_str(g,n,b); printf("  violates&slack%d: %s\n",sl,b);} }
    }
    printf("n=%d graphs=%ld chvatal_violators=%ld (traceable among them %ld) violators_with_slack>=0=%ld hist:",n,tot,viol,violtr,bad);
    for(int i=0;i<64;i++) if(hs[i]) printf(" %d:%ld",i-32,hs[i]); printf("\n");
  } else if(!strcmp(argv[1],"nt")){
    int n=nmax;
    /* trees on n vertices by leaf addition */
    uint64_t *cur=malloc(8); cur[0]=0; long ncur=1;
    for(int t=2;t<=n;t++){
      N=t; hset hs; hinit(&hs,16); long cap=1024; uint64_t *nxt=malloc(cap*8); long nn=0;
      for(long i=0;i<ncur;i++){ set p[MAXN]; decode(cur[i],t-1,p);
        for(int u=0;u<t-1;u++){ set c[MAXN]; for(int v=0;v<t-1;v++) c[v]=p[v]; c[u]|=1u<<(t-1); c[t-1]=1u<<u;
          uint64_t k=canon(c); if(hins(&hs,k)){ if(nn==cap){cap*=2;nxt=realloc(nxt,cap*8);} nxt[nn++]=k; } } }
      free(hs.t); free(cur); cur=nxt; ncur=nn;
    }
    N=n;
    /* keep non-traceable trees (non-paths) */
    long m0=0; for(long i=0;i<ncur;i++){ set g[MAXN]; decode(cur[i],n,g); if(!traceable(g,n)) cur[m0++]=cur[i]; }
    ncur=m0;
    fprintf(stderr,"n=%d nonpath trees=%ld\n",n,ncur);
    stats_t st; memset(&st,0,sizeof st); st.best=-99;
    snprintf(fn,sizeof fn,"%s/ntonly_n%d.tsv",od,n); FILE *ntf=fopen(fn,"w");
    long maximal=0;
    snprintf(fn,sizeof fn,"%s/ntmax_n%d.tsv",od,n); FILE *mxf=fopen(fn,"w");
    int m=n-1;
    while(ncur>0){
      /* analyse level */
      int lg=16; while((1L<<lg) < 4*ncur+1024 && lg<28) lg++;
      hset hs; hinit(&hs,lg+1); long cap=1024; uint64_t *nxt=malloc(cap*8); long nn=0;
      for(long i=0;i<ncur;i++){
        set g[MAXN]; decode(cur[i],n,g);
        int ismax=1; set reach[MAXN];
        if(ext_reach(g,n,reach)){ fprintf(stderr,"BUG: traceable graph in nt level\n"); exit(2); }
        for(int a=0;a<n;a++) for(int b=a+1;b<n;b++) if(!(g[a]>>b&1)){
          int trd = (reach[a]>>b)&1;
          g[a]|=1u<<b; g[b]|=1u<<a;
#ifdef CHECKDP
          if(trd != traceable(g,n)){ fprintf(stderr,"DP mismatch\n"); exit(3); }
#endif
          if(!trd){ ismax=0; uint64_t k=canon(g); if(hins(&hs,k)){ if(nn==cap){cap*=2;nxt=realloc(nxt,cap*8);} nxt[nn++]=k; } }
          g[a]&=~(1u<<b); g[b]&=~(1u<<a);
        }
        stats_t dummy; memset(&dummy,0,sizeof dummy);
        analyse_k(cur[i],n,&st,ntf,0);
        if(ismax){ maximal++; analyse_k(cur[i],n,&dummy,mxf,0); }
      }
      fprintf(stderr,"m=%d level=%ld next=%ld\n",m,ncur,nn);
      free(hs.t); free(cur); cur=nxt; ncur=nn; m++;
    }
    fclose(ntf); fclose(mxf);
    report(n,&st,stdout);
    printf("maximal non-traceable connected graphs: %ld\n",maximal);
  }
  return 0;
}
