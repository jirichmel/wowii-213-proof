# analyze.py -- describe graphs from a list "graph6 slack gamma2 lm ...": structure of near misses.
# Usage: python3 -I analyze.py FILE [minslack]
import sys, itertools

def g6dec(s):
    n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        x = ord(ch) - 63; bits += [(x >> (5 - i)) & 1 for i in range(6)]
    adj = [set() for _ in range(n)]; b = 0
    for j in range(1, n):
        for i in range(j):
            if bits[b]: adj[i].add(j); adj[j].add(i)
            b += 1
    return n, adj

def comps(n, adj, rem):
    left = set(range(n)) - rem; out = []
    while left:
        v = left.pop(); st = [v]; c = {v}
        while st:
            x = st.pop()
            for y in adj[x]:
                if y in left: left.discard(y); c.add(y); st.append(y)
        out.append(c)
    return out

def describe(n, adj):
    deg = [len(a) for a in adj]
    univ = {v for v in range(n) if deg[v] == n - 1}
    # best scattering: max c(G-S) - |S| over S nonempty
    best = None
    for k in range(0, n - 1):
        for S in itertools.combinations(range(n), k):
            c = len(comps(n, adj, set(S)))
            val = c - k
            if best is None or val > best[0]: best = (val, S, c)
    cs = comps(n, adj, univ)
    def iso_name(c):
        m = len(c); e = sum(len(adj[v] & c) for v in c) // 2
        if e == m * (m - 1) // 2: return "K%d" % m
        return "[%dv,%de]" % (m, e)
    rest = " u ".join(sorted(iso_name(c) for c in cs))
    nedges = sum(deg) // 2
    return {"deg": sorted(deg), "edges": nedges, "univ": len(univ), "after_univ": rest,
            "scatter": best[0], "S": best[1], "cGS": best[2],
            "edgelist": " ".join("%d-%d" % (i, j) for i in range(n) for j in sorted(adj[i]) if j > i)}

if __name__ == "__main__":
    fn = sys.argv[1]; mn = int(sys.argv[2]) if len(sys.argv) > 2 else -99
    for line in open(fn):
        p = line.split(); sl = int(p[1])
        if sl < mn: continue
        n, adj = g6dec(p[0]); d = describe(n, adj)
        print("%s slack=%d g2H=%s lmH=%s m=%d univ=%d G-univ: %s | max c(G-S)-|S| = %d (S=%s) deg=%s\n    edges: %s" %
              (p[0], sl, p[2], p[3], d["edges"], d["univ"], d["after_univ"], d["scatter"], d["S"], d["deg"], d["edgelist"]))
