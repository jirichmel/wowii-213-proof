"""Test two statements on small graphs (Python, independent of sb.c's invariant code).
L1 (monotonicity): for every graph G on n vertices and every non-edge e,
    gamma_2(comp(G+e)) >= gamma_2(comp(G)) and lm(comp(G+e)) <= lm(comp(G)),
    so slack(G+e) >= slack(G).  Tested on all labelled graphs n<=6 (all non-edges).
L2 (tight family): F(n,s) = K_s v ((s+1)K_1 u K_t), t=n-2s-1>=1, s>=1, is connected,
    non-traceable, and has slack exactly -1.  Tested for n<=12.
"""
import itertools, sys
sys.setrecursionlimit(10000)

def gamma2(n, H):
    for k in range(n + 1):
        for D in itertools.combinations(range(n), k):
            Ds = set(D)
            if all(len(H[v] & Ds) >= 2 for v in range(n) if v not in Ds):
                return k

def lm(n, H):
    d = sorted(len(H[v]) for v in range(n))
    return d[n // 2 - 1] if n % 2 == 0 else d[(n + 1) // 2 - 1]

def comp(n, G):
    return [set(range(n)) - G[v] - {v} for v in range(n)]

def traceable(n, G):
    ends = {1 << v: {v} for v in range(n)}
    for mask in range(1, 1 << n):
        for v in ends.get(mask, ()):
            for u in G[v]:
                if not mask >> u & 1:
                    ends.setdefault(mask | 1 << u, set()).add(u)
    return (1 << n) - 1 in ends

def L1(nmax):
    for n in range(2, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        bad = 0; tested = 0
        cache = {}
        def inv(mask):
            if mask in cache: return cache[mask]
            G = [set() for _ in range(n)]
            for i, (a, b) in enumerate(pairs):
                if mask >> i & 1: G[a].add(b); G[b].add(a)
            H = comp(n, G)
            r = (gamma2(n, H), lm(n, H)); cache[mask] = r; return r
        for mask in range(1 << len(pairs)):
            g, l = inv(mask)
            for i in range(len(pairs)):
                if not mask >> i & 1:
                    g2, l2 = inv(mask | 1 << i); tested += 1
                    if g2 < g or l2 > l: bad += 1
        print(f"L1 n={n}: pairs tested={tested} violations={bad}", flush=True)

def L2(nmax):
    for n in range(4, nmax + 1):
        for s in range(1, n):
            t = n - 2 * s - 1
            if t < 1: break
            G = [set() for _ in range(n)]
            S = range(s); I = range(s, 2 * s + 1); T = range(2 * s + 1, n)
            def e(a, b): G[a].add(b); G[b].add(a)
            for a, b in itertools.combinations(range(n), 2):
                if a in S or b in S: e(a, b)
                elif a in T and b in T: e(a, b)
            H = comp(n, G)
            sl = gamma2(n, H) - lm(n, H) - 2
            print(f"L2 n={n} s={s} t={t}: traceable={traceable(n, G)} slack={sl}", flush=True)

L1(int(sys.argv[1])); L2(int(sys.argv[2]))
