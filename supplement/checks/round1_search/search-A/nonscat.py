# nonscat.py -- for each maximal non-traceable list, split into scattering (some S, c(G-S) >= |S|+2)
# and non-scattering graphs; report best slack in each part.  Usage: python3 -I nonscat.py FILES...
import sys, itertools
sys.path.insert(0, ".")
from analyze import g6dec, comps
for fn in sys.argv[1:]:
    best = {True: -99, False: -99}; cnt = {True: 0, False: 0}; ex = []
    for line in open(fn):
        p = line.split(); sl = int(p[1]); n, adj = g6dec(p[0])
        sc = any(len(comps(n, adj, set(S))) >= k + 2 for k in range(1, n - 1) for S in itertools.combinations(range(n), k))
        cnt[sc] += 1; best[sc] = max(best[sc], sl)
        if not sc and sl >= -2: ex.append((sl, p[0]))
    print(fn, "scattering: %d (best slack %d)  non-scattering: %d (best slack %d)" % (cnt[True], best[True], cnt[False], best[False]))
    for e in sorted(ex, reverse=True): print("   non-scattering near miss", e)
