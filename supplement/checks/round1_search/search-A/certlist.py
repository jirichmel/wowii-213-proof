# certlist.py -- list graphs where the pair bound min|N[u] u N[w]| exceeds lm(H)+1 (a triple is needed)
import sys, itertools
sys.path.insert(0, ".")
from analyze import g6dec, describe
for line in open(sys.argv[1]):
    p = line.split(); n, adj = g6dec(p[0])
    hd = sorted(n - 1 - len(a) for a in adj); lm = hd[(n + 1) // 2 - 1]
    bp = min(len(adj[u] | adj[w] | {u, w}) for u in range(n) for w in range(u + 1, n))
    if bp > lm + 1:
        d = describe(n, adj)
        print(p[0], "slack", p[1], "lmH", lm, "pair", bp, "univ", d["univ"], "G-univ:", d["after_univ"], "deg", d["deg"])
