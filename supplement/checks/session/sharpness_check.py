# Session agent's own quick check of the small claims added in the write-up (one implementation).
import itertools, math
def comp(n, E):
    S = {frozenset(e) for e in E}
    return [(a, b) for a in range(n) for b in range(a+1, n) if frozenset((a, b)) not in S]
def adjsets(n, E):
    A = [set() for _ in range(n)]
    for a, b in E: A[a].add(b); A[b].add(a)
    return A
def lm(n, A):
    d = sorted(len(A[v]) for v in range(n)); return d[math.ceil(n/2)-1]
def gamma2(n, A, exact=False):
    for k in range(n+1):
        for D in itertools.combinations(range(n), k):
            Ds = set(D)
            ok = all((len(A[v] & Ds) == 2) if exact else (len(A[v] & Ds) >= 2) for v in range(n) if v not in Ds)
            if ok: return k
    return None
def traceable(n, A):
    full = (1 << n) - 1
    reach = {(1 << v, v) for v in range(n)}
    frontier = list(reach)
    while frontier:
        nf = []
        for m, v in frontier:
            if m == full: return True
            for w in A[v]:
                if not m >> w & 1:
                    s = (m | 1 << w, w)
                    if s not in reach: reach.add(s); nf.append(s)
        frontier = nf
    return n == 1
def closed(n, A):
    return all(len(A[a]) + len(A[b]) <= n-2 for a in range(n) for b in range(a+1, n) if b not in A[a])
def connected(n, A):
    seen = {0}; st = [0]
    while st:
        v = st.pop()
        for w in A[v]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == n
# 1. the exactly-two example, n = 6
E = [(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(2,3)]
n = 6; A = adjsets(n, E); H = adjsets(n, comp(n, E))
print("n=6 example: connected", connected(n, A), "traceable", traceable(n, A), "lm(H)", lm(n, H),
      "gamma2 at-least", gamma2(n, H), "gamma2 exactly", gamma2(n, H, exact=True))
# 1b. the 7-vertex example of Section 2 (all three median readings equal 4)
import itertools as _it
E = [(0,6),(1,6),(2,5),(2,6),(3,4),(3,5),(4,5),(4,6),(5,6)]
n = 7; A = adjsets(n, E); H = adjsets(n, comp(n, E))
dH = sorted(len(H[v]) for v in range(n))
print("n=7 example: connected", connected(n, A), "traceable", traceable(n, A), "H-degrees", dH,
      "lower", dH[math.ceil(n/2)-1], "upper", dH[n//2], "h5", dH[4],
      "gamma2 at-least", gamma2(n, H), "least exactly-two set", gamma2(n, H, exact=True))
# 2. F(n,s) = K_s v ((s+1)K_1 u K_{n-2s-1})
for s in range(1, 4):
    for n in range(2*s+2, 2*s+8):
        K = list(range(s)); I = list(range(s, 2*s+1)); C = list(range(2*s+1, n))
        E = [(a, b) for a in K for b in range(n) if b > a] + [(a, b) for a in C for b in C if a < b]
        E = list({tuple(sorted(e)) for e in E})
        A = adjsets(n, E); H = adjsets(n, comp(n, E))
        g, m = gamma2(n, H), lm(n, H)
        print(f"F({n},{s}): closed {closed(n,A)} connected {connected(n,A)} traceable {traceable(n,A)} lm {m} gamma2 {g} gamma2-lm {g-m}")
# 3. K_{n-1} + K_1 (disconnected): closed, gamma2 - lm = n - 2
for n in range(4, 9):
    E = [(a, b) for a in range(n-1) for b in range(a+1, n-1)]
    A = adjsets(n, E); H = adjsets(n, comp(n, E))
    print(f"K_{n-1}+K_1: closed {closed(n,A)} connected {connected(n,A)} lm {lm(n,H)} gamma2 {gamma2(n,H)}")
