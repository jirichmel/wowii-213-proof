/* scat.c -- read lines "graph6 slack ..." and split by scattering: exists S (|S|>=1) with
 * c(G-S) >= |S|+2.  Prints counts and slack histograms of both parts.  Usage: scat < FILE */
#include <stdio.h>
#include <string.h>
static int ncomp(int n, const unsigned *a, unsigned R) {
    int c = 0;
    while (R) { unsigned s = R & -R, f = s; R &= ~s;
        while (f) { int v = __builtin_ctz(f); f &= f - 1; unsigned nw = a[v] & R; R &= ~nw; f |= nw; }
        c++; }
    return c;
}
int main(void) {
    char g[64]; int sl; long long hs[64] = {0}, hn[64] = {0}; char line[256];
    while (fgets(line, sizeof line, stdin)) {
        if (sscanf(line, "%63s %d", g, &sl) != 2) continue;
        int n = g[0] - 63; unsigned a[16] = {0}; int b = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, b++)
            if (((g[1 + b / 6] - 63) >> (5 - b % 6)) & 1) { a[i] |= 1u << j; a[j] |= 1u << i; }
        unsigned full = (1u << n) - 1; int sc = 0;
        for (unsigned S = 1; S < full && !sc; S++) if (ncomp(n, a, full & ~S) >= __builtin_popcount(S) + 2) sc = 1;
        if (sc) hs[sl + 32]++; else hn[sl + 32]++;
    }
    printf("scattering:"); for (int s = 0; s < 64; s++) if (hs[s]) printf(" %d:%lld", s - 32, hs[s]);
    printf("\nnon-scattering:"); for (int s = 0; s < 64; s++) if (hn[s]) printf(" %d:%lld", s - 32, hn[s]);
    printf("\n");
    return 0;
}
