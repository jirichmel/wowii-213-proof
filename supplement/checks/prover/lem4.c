/* lem4.c -- brute-force check of Lemma 4 of proof.md (prover-claimC), independent of pdom.py.
 * Lemma 4: r >= 2, a family (multiset) of r subsets of [N], each of size <= r-2 (or == r-2 with
 * flag 'exact'); then some subfamily I (|I| = k) has k + #{q : q lies in >= k-1 members of I} <= r.
 * Usage: lem4 R N [exact]      prints the number of families and of failures.
 * Build: cc -O2 -o lem4 lem4.c
 */
#include <stdio.h>
#include <stdlib.h>
static int R, N, exact, nsub, sub[1 << 12], fam[16];
static long long families, failures;
static int check(void) {
    for (int I = 0; I < (1 << R); I++) {
        int k = __builtin_popcount(I), heavy = 0;
        for (int q = 0; q < N; q++) {
            int c = 0;
            for (int i = 0; i < R; i++) if (((I >> i) & 1) && ((sub[fam[i]] >> q) & 1)) c++;
            if (c >= k - 1) heavy++;
        }
        if (k + heavy <= R) return 1;
    }
    return 0;
}
static void rec(int pos, int from) {
    if (pos == R) {
        families++;
        if (!check()) { failures++; if (failures <= 5) { printf("FAIL:"); for (int i = 0; i < R; i++) printf(" %x", sub[fam[i]]); printf("\n"); } }
        return;
    }
    for (int s = from; s < nsub; s++) { fam[pos] = s; rec(pos + 1, s); }
}
int main(int argc, char **argv) {
    R = atoi(argv[1]); N = atoi(argv[2]); exact = argc > 3;
    for (int m = 0; m < (1 << N); m++) {
        int p = __builtin_popcount(m);
        if (exact ? p == R - 2 : p <= R - 2) sub[nsub++] = m;
    }
    rec(0, 0);
    printf("lem4 r=%d N=%d %s: families %lld, failures %lld\n", R, N, exact ? "(sets of size exactly r-2)" : "(sets of size <= r-2)", families, failures);
    return failures ? 2 : 0;
}
