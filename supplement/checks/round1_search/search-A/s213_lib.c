/* s213_lib.c -- search-A, program 1 for Conjecture 213 (WoWII).
 * Generation: tools/lib/smallgraph.h (sg_hereditary, keeping connected graphs: every connected
 * graph arises from a connected graph by adding a vertex, delete a non-cut vertex).
 * Invariants: inv1.h (own code).
 * Usage: s213_lib NMAX OUTPREFIX     writes OUTPREFIX_nt_N.txt (all non-traceable connected
 * graphs on N vertices with slack, graph6) and prints per-n counts.
 */
#include "smallgraph.h"
#include "inv1.h"
#include <time.h>

static long long cnt_conn[17], cnt_hyp[17], cnt_nt[17], cnt_cex[17], hist[17][40];
static int best[17];
static FILE *ntf[17];
static const char *prefix;

static int acc_conn(int n, const unsigned *adj, void *ctx) { (void)ctx; return sg_connected(adj, (1u << n) - 1); }

static void visit(int n, const unsigned *adj, void *ctx) {
    (void)ctx;
    if (n < 2) return;
    if (!sg_connected(adj, (1u << n) - 1)) return;
    cnt_conn[n]++;
    unsigned h[16]; complement1(n, adj, h);
    int g2 = gamma2_1(n, h), lm = lowmed1(n, h);
    int slack = g2 - lm - 2;
    int hyp = slack >= 0;
    if (hyp) cnt_hyp[n]++;
    int tr = ham1(n, adj);
    if (!tr) {
        cnt_nt[n]++;
        hist[n][slack + 20]++;
        if (slack > best[n]) best[n] = slack;
        char g6[32]; graph6_1(n, adj, g6);
        if (!ntf[n]) { char fn[512]; sprintf(fn, "%s_nt_%d.txt", prefix, n); ntf[n] = fopen(fn, "w"); }
        fprintf(ntf[n], "%s %d %d %d\n", g6, slack, g2, lm);
        if (hyp) {
            cnt_cex[n]++;
            char e[512]; edges1(n, adj, e);
            printf("COUNTEREXAMPLE n=%d g6=%s gamma2(H)=%d lm(H)=%d edges: %s\n", n, g6, g2, lm, e);
            fflush(stdout);
        }
    }
}

int main(int argc, char **argv) {
    int nmax = argc > 1 ? atoi(argv[1]) : 9;
    prefix = argc > 2 ? argv[2] : "s213lib";
    for (int i = 0; i < 17; i++) best[i] = -99;
    unsigned one[1] = {0};
    time_t t0 = time(NULL);
    sg_hereditary(1, one, nmax, acc_conn, visit, NULL);
    for (int n = 2; n <= nmax; n++) {
        printf("n=%d connected=%lld hypothesis=%lld non_traceable=%lld counterexamples=%lld best_slack_nt=%d\n",
               n, cnt_conn[n], cnt_hyp[n], cnt_nt[n], cnt_cex[n], best[n]);
        printf("   slack histogram (non-traceable):");
        for (int s = 0; s < 40; s++) if (hist[n][s]) printf(" %d:%lld", s - 20, hist[n][s]);
        printf("\n");
        if (ntf[n]) fclose(ntf[n]);
    }
    printf("time %ld s\n", (long)(time(NULL) - t0));
    return 0;
}
