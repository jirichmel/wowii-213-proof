"""Analyse near misses from sb.c TSV output (n slack g2 lm m key edges).
For each graph with slack >= THRESH: is it a spanning subgraph of F(n,s)=K_s v ((s+1)K_1 u K_t), t>=1,
i.e. is there S with |S|=s such that G-S has >= s+1 isolated vertices and n-2s-1>=1?
Also: smallest s with c(G-S) >= |S|+2 (a scattering witness), if any with s<=4.
Usage: nearmiss.py FILE THRESH [TOP]
"""
import sys, itertools

def parse(line):
    f = line.rstrip('\n').split('\t')
    n, sl, g2, lm, m = map(int, f[:5])
    edges = [tuple(map(int, e.split('-'))) for e in f[6].split()] if len(f) > 6 and f[6] else []
    G = [set() for _ in range(n)]
    for a, b in edges: G[a].add(b); G[b].add(a)
    return n, sl, g2, lm, m, G, f[6] if len(f) > 6 else ''

def comps(n, G, rem):
    seen = set(rem); c = 0; iso = 0
    for v in range(n):
        if v in seen: continue
        c += 1; st = [v]; seen.add(v); size = 0
        while st:
            x = st.pop(); size += 1
            for u in G[x]:
                if u not in seen: seen.add(u); st.append(u)
        if size == 1: iso += 1
    return c, iso

def analyse(n, G):
    inF = None; scat = None
    for s in range(0, 5):
        for S in itertools.combinations(range(n), s):
            c, iso = comps(n, G, set(S))
            if scat is None and c >= s + 2: scat = s
            if inF is None and s >= 1 and n - 2 * s - 1 >= 1 and iso >= s + 1: inF = s
        if scat is not None and inF is not None: break
    return inF, scat

fn, th = sys.argv[1], int(sys.argv[2])
top = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
rows = [parse(l) for l in open(fn)]
rows = [r for r in rows if r[1] >= th]
rows.sort(key=lambda r: (-r[1], -r[4]))
tot = 0; nf = 0; nscat = 0
from collections import Counter
cnt = Counter()
for r in rows:
    n, sl, g2, lm, m, G, es = r
    inF, scat = analyse(n, G)
    tot += 1; nf += inF is not None; nscat += scat is not None
    cnt[(sl, g2, lm, inF, scat)] += 1
print(f"{fn}: rows with slack>={th}: {tot}; spanning subgraph of some F(n,s): {nf}; has scattering witness (s<=4): {nscat}")
for k, v in sorted(cnt.items(), key=lambda kv: (-kv[0][0], kv[0][1:].__repr__())):
    print("  slack=%d g2=%d lm=%d inF_s=%s scatter_s=%s : %d" % (k + (v,)))
for r in rows[:top] if top < 10**9 else []:
    n, sl, g2, lm, m, G, es = r
    print(n, sl, g2, lm, m, analyse(n, G), es)
