"""search-B second implementation (shares no code with sb.c).
Mode 'gen NMAX': generates connected graphs up to NMAX by its own method
  (vertex addition, canonical form = lexicographically smallest edge list over
  all orderings compatible with a colour refinement, brute force inside classes),
  and computes, with different algorithms from sb.c:
  traceability by subset DP, gamma_2 by itertools.combinations, lower median.
Mode 'keys FILE N': recompute invariants on the graphs listed (hex keys from sb.c).
"""
import sys, itertools
from collections import Counter

def colour_classes(n, adj):
    col = [0]*n
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in adj[v]))) for v in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    classes = {}
    for v in range(n):
        classes.setdefault(col[v], []).append(v)
    return [classes[c] for c in sorted(classes)]

def canon(n, adj):
    classes = colour_classes(n, adj)
    best = None
    for combo in itertools.product(*[itertools.permutations(c) for c in classes]):
        order = [v for part in combo for v in part]
        pos = {v: i for i, v in enumerate(order)}
        e = tuple(sorted((min(pos[a], pos[b]), max(pos[a], pos[b])) for a in range(n) for b in adj[a] if a < b))
        if best is None or e < best:
            best = e
    return best

def adj_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    return adj

def connected(n, adj):
    seen = {0}; st = [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u); st.append(u)
    return len(seen) == n

def traceable_dp(n, adj):
    if n == 1:
        return True
    # ends[mask] = set of vertices v such that a path covering exactly mask ends at v
    ends = {}
    for v in range(n):
        ends[1 << v] = {v}
    for mask in range(1, 1 << n):
        if mask not in ends:
            continue
        for v in ends[mask]:
            for u in adj[v]:
                if not mask >> u & 1:
                    ends.setdefault(mask | 1 << u, set()).add(u)
    return (1 << n) - 1 in ends

def gamma2(n, hadj):
    V = range(n)
    for k in range(0, n + 1):
        for D in itertools.combinations(V, k):
            Ds = set(D)
            if all(len(hadj[v] & Ds) >= 2 for v in V if v not in Ds):
                return k
    return n

def lower_median(degs):
    d = sorted(degs); n = len(d)
    return d[n // 2 - 1] if n % 2 == 0 else d[(n + 1) // 2 - 1]

def invariants(n, adj):
    hadj = [set(range(n)) - adj[v] - {v} for v in range(n)]
    lm = lower_median([len(hadj[v]) for v in range(n)])
    g2 = gamma2(n, hadj)
    tr = traceable_dp(n, adj)
    return tr, g2, lm

def summarise(n, graphs):
    conn = hyp = nt = cex = 0; hist = Counter()
    for adj in graphs:
        tr, g2, lm = invariants(n, adj)
        conn += 1
        if g2 >= lm + 2: hyp += 1
        if not tr:
            nt += 1; s = g2 - lm - 2; hist[s] += 1
            if s >= 0: cex += 1
    best = max(hist) if hist else None
    print(f"n={n} connected={conn} hypothesis={hyp} non_traceable={nt} counterexamples={cex} best={best} hist={sorted(hist.items())}", flush=True)

def main():
    if sys.argv[1] == 'gen':
        nmax = int(sys.argv[2])
        level = [()]  # n=1 : no edges
        for n in range(2, nmax + 1):
            seen = set()
            for edges in level:
                for r in range(1, n):
                    for S in itertools.combinations(range(n - 1), r):
                        e = list(edges) + [(s, n - 1) for s in S]
                        c = canon(n, adj_from_edges(n, e))
                        seen.add(c)
            level = sorted(seen)
            summarise(n, [adj_from_edges(n, e) for e in level])
    else:
        fn, n = sys.argv[2], int(sys.argv[3])
        graphs = []
        m = n * (n - 1) // 2
        for line in open(fn):
            k = int(line.strip(), 16)
            b = m - 1; edges = []
            for i in range(n):
                for j in range(i + 1, n):
                    if k >> b & 1: edges.append((i, j))
                    b -= 1
            adj = adj_from_edges(n, edges)
            assert connected(n, adj)
            graphs.append(adj)
        summarise(n, graphs)

if __name__=='__main__': main()
