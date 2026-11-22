/* lab.c: all labelled graphs on n vertices (n <= 8).
   For closed connected non-complete graphs: count, exact gamma_2(H) (two methods), slack histogram,
   and the proof's construction with EVERY choice explored (all R0, all q, all (|R|-1)-subsets).
   For every connected graph with no Hamiltonian path: check that Hyp fails (end-to-end).
   usage: lab n [part nparts]   build: cc -O2 -o lab lab.c */
#include "core.h"

int main(int argc, char **argv) {
    int n = atoi(argv[1]);
    int part = argc > 3 ? atoi(argv[2]) : 0, nparts = argc > 3 ? atoi(argv[3]) : 1;
    int E = n * (n - 1) / 2, ei[64], ej[64], k = 0;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) { ei[k] = i; ej[k] = j; k++; }
    u64 tot = 1ULL << E;
    long long nconn = 0, nclosed = 0, nnohp = 0, nhyp_nohp = 0, slack[64] = {0}, cases[4] = {0};
    long long terms = 0; int maxrounds = 0; long long hypcount = 0;
    for (u64 code = part; code < tot; code += nparts) {
        u64 a[64] = {0};
        for (int e = 0; e < E; e++) if ((code >> e) & 1) { a[ei[e]] |= 1ULL << ej[e]; a[ej[e]] |= 1ULL << ei[e]; }
        if (!is_connected(n, a)) continue;
        nconn++;
        u64 h[64]; complement(n, a, h);
        int hp = hp_dfs(n, a);
        if (!hp) {
            nnohp++;
            if (n <= 20 && hp_dp(n, a)) FAIL("HP methods disagree code=%llx", (unsigned long long)code);
            int m = lm_of(n, h);
            int g = g2_exact_enum(n, h, m + 1);
            if (g >= m + 2) { nhyp_nohp++; FAIL("COUNTEREXAMPLE to 213: n=%d code=%llx", n, (unsigned long long)code); }
        }
        if (!is_closed(n, a) || is_complete(n, a)) continue;
        nclosed++;
        int m = lm_of(n, h);
        int g1 = g2_exact_enum(n, h, n), g2 = g2_bb(n, h, n);
        if (g1 != g2) FAIL("gamma_2 methods disagree code=%llx %d %d", (unsigned long long)code, g1, g2);
        slack[g1 - m + 32]++;
        if (g1 >= m + 2) { hypcount++; FAIL("closed graph with Hyp: code=%llx", (unsigned long long)code); }
        cstat st; char tag[64]; snprintf(tag, sizeof tag, "n=%d code=%llx", n, (unsigned long long)code);
        run_proof(n, a, 1LL << 40, 1LL << 40, &st, tag);
        if (st.capped) FAIL("capped %s", tag);
        cases[st.caseid]++; terms += st.terminals; if (st.maxrounds > maxrounds) maxrounds = st.maxrounds;
    }
    printf("n=%d part %d/%d: connected=%lld closed_conn_noncomplete=%lld nonHP_connected=%lld nonHP_with_Hyp=%lld\n",
           n, part, nparts, nconn, nclosed, nnohp, nhyp_nohp);
    printf("  cases: J=%lld 2a=%lld 2b=%lld; terminal sets checked=%lld; max rounds=%d; closed with Hyp=%lld\n",
           cases[1], cases[2], cases[3], terms, maxrounds, hypcount);
    printf("  slack gamma2-lm histogram:");
    for (int s = 0; s < 64; s++) if (slack[s]) printf(" [%d]=%lld", s - 32, slack[s]);
    printf("\n  failures=%lld\n", g_fail);
    return g_fail ? 1 : 0;
}
