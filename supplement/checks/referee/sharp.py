"""referee213: Remark 3 sharpness family F(n,s) = K_s join ((s+1)K_1 u K_(n-2s-1)).
Checks closed, connected, and gamma2(H) - lm(H) by exact search. Own code. python3 sharp.py"""
import itertools
def test(n, s):
    adj = [0]*n
    def e(a, b): adj[a] |= 1 << b; adj[b] |= 1 << a
    K = range(s); I = range(s, 2*s+1); C = range(2*s+1, n)
    for a, b in itertools.combinations(K, 2): e(a, b)
    for a in K:
        for b in range(s, n): e(a, b)
    for a, b in itertools.combinations(C, 2): e(a, b)
    deg = [bin(x).count('1') for x in adj]
    closed = all(adj[a] >> b & 1 or deg[a]+deg[b] <= n-2 for a, b in itertools.combinations(range(n), 2))
    full = (1 << n) - 1; non = [full & ~adj[v] & ~(1 << v) for v in range(n)]
    m = sorted(n-1-d for d in deg)[(n+1)//2 - 1]
    for k in range(n+1):
        if any(all(D >> v & 1 or bin(non[v] & D).count('1') >= 2 for v in range(n))
               for D in (sum(1 << i for i in c) for c in itertools.combinations(range(n), k))):
            return closed, m, k
for n in range(6, 15):
    for s in range(1, (n-1)//2 + 1):
        if n-2*s-1 >= 1:
            cl, m, g = test(n, s)
            print(f"n={n} s={s}: closed={cl} lm={m} gamma2={g} slack={g-m-2}")
