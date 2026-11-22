/* canonlist.c -- read "graph6 slack ..." lines, print "<canonical code (smallgraph sg_canon)> <slack>"
 * so that two lists produced by different programs can be compared as sets. */
#include "smallgraph.h"
int main(void) {
    char line[256], g[64]; int sl;
    while (fgets(line, sizeof line, stdin)) {
        if (sscanf(line, "%63s %d", g, &sl) != 2) continue;
        int n = g[0] - 63; unsigned a[16] = {0}; int b = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, b++)
            if (((g[1 + b / 6] - 63) >> (5 - b % 6)) & 1) { a[i] |= 1u << j; a[j] |= 1u << i; }
        sg_code c = sg_canon(n, a);
        printf("%016llx%016llx %d\n", (unsigned long long)(c >> 64), (unsigned long long)c, sl);
    }
    return 0;
}
