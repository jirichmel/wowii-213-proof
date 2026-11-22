"""referee213 probe: Theorem 1 without connectivity. All labelled closed non-complete graphs
(connected or not) on n <= 7 vertices: is gamma2(H) <= lm(H)+1? Own code. python3 discon.py"""
import itertools
for n in range(2, 8):
    pairs = list(itertools.combinations(range(n), 2))
    bad = 0; tot = 0; ex = None; totc = 0; badc = 0; badiso = 0
    for g in range(1 << len(pairs)):
        adj = [0]*n
        for i, (a, b) in enumerate(pairs):
            if g >> i & 1: adj[a] |= 1 << b; adj[b] |= 1 << a
        deg = [bin(x).count('1') for x in adj]
        if all(d == n-1 for d in deg): continue
        if any(not (adj[a] >> b & 1) and deg[a]+deg[b] > n-2 for a, b in pairs): continue
        tot += 1
        seen = 1; fr = 1
        while fr:
            nf = 0
            for v in range(n):
                if fr >> v & 1: nf |= adj[v]
            fr = nf & ~seen; seen |= fr
        con = (seen == (1 << n) - 1); totc += con
        full = (1 << n) - 1
        non = [full & ~adj[v] & ~(1 << v) for v in range(n)]
        h = sorted(n-1-d for d in deg); m = h[(n+1)//2 - 1]
        g2 = min(bin(D).count('1') for D in range(1 << n)
                 if all(D >> v & 1 or bin(non[v] & D).count('1') >= 2 for v in range(n)))
        if g2 > m+1:
            bad += 1; badc += con
            badiso += (sorted(deg) == [0] + [n-2]*(n-1))
            if ex is None: ex = [p for i, p in enumerate(pairs) if g >> i & 1]
    print(f"n={n}: closed non-complete {tot} (connected {totc}); gamma2 > lm+1: {bad} (connected {badc}; of form K_(n-1)+K_1: {badiso}); example {ex}")
