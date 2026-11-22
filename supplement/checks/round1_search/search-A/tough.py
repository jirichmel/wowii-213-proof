# tough.py -- for each graph in a list "graph6 slack ...": scattering? 1-tough? property P16
# (c(G-S) <= |S| for every S with |S| >= 2, and c(G-v) <= 2 for every v) and the one-leaf shape.
# Usage: python3 -I tough.py FILES...
import sys, itertools
sys.path.insert(0, ".")
from analyze import g6dec, comps
for fn in sys.argv[1:]:
    tot = 0; res = {}
    for line in open(fn):
        p = line.split(); sl = int(p[1]); n, adj = g6dec(p[0]); tot += 1
        worst = {}  # max c(G-S) - |S| by |S|
        for k in range(1, n - 1):
            worst[k] = max(len(comps(n, adj, set(S))) - k for S in itertools.combinations(range(n), k))
        scat = any(worst[k] >= 2 for k in worst)
        tough1 = all(worst[k] <= 0 for k in worst)
        p16 = (not scat) and all(worst[k] <= 0 for k in worst if k >= 2)
        key = ("scattering" if scat else "1-tough" if tough1 else "P16(leaf-type)" if p16 else "other non-scattering")
        r = res.setdefault(key, [0, -99]); r[0] += 1; r[1] = max(r[1], sl)
        if key in ("1-tough", "P16(leaf-type)"): print("   ", key, p[0], "slack", sl)
    print(fn, tot, "graphs:", {k: "count %d, best slack %d" % tuple(v) for k, v in res.items()})
