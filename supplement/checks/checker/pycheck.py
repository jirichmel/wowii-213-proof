"""pycheck.py: second implementation (Python, shares no code with core.h / lab.c / iso.c / rnd.c).

modes
  lab N        all labelled graphs on N vertices (N <= 7): closed connected non-complete count, exact
               gamma_2(H) slack histogram, the proof's construction in the RECURSIVE form of Lemma 4 with
               every choice taken, and for every connected graph without a Hamiltonian path: Hyp fails.
  lemma R K    abstract Lemma 4: every family of R index sets |Y'| = R..R+1 (all multisets) of subsets of
               {0..K-1} of size <= R-2; every choice sequence of the procedure; conclusion checked.
"""
import sys
from itertools import combinations, combinations_with_replacement


def pc(x):
    return bin(x).count("1")


def lm(degs):
    s = sorted(degs)
    n = len(s)
    return s[(n + 1) // 2 - 1]


def two_dom(nb, D, n):
    for v in range(n):
        if not (D >> v) & 1 and pc(nb[v] & D) < 2:
            return False
    return True


def gamma2(nb, n):
    for k in range(1, n + 1):
        for c in combinations(range(n), k):
            D = 0
            for v in c:
                D |= 1 << v
            if two_dom(nb, D, n):
                return k
    return n


def connected(adj, n):
    seen, stack = 1, [0]
    while stack:
        v = stack.pop()
        new = adj[v] & ~seen
        seen |= new
        for w in range(n):
            if (new >> w) & 1:
                stack.append(w)
    return seen == (1 << n) - 1


def has_hp(adj, n):
    # DP over (set, end)
    reach = [0] * (1 << n)
    for v in range(n):
        reach[1 << v] = 1 << v
    for s in range(1, 1 << n):
        e = reach[s]
        if not e:
            continue
        for v in range(n):
            if (e >> v) & 1:
                out = adj[v] & ~s
                for w in range(n):
                    if (out >> w) & 1:
                        reach[s | (1 << w)] |= 1 << w
    return reach[(1 << n) - 1] != 0


def lemma4_all(r, P, Yp, A):
    """All (B, R) the recursive proof of Lemma 4 can return, over every choice.
    P: frozenset, Yp: tuple of indices, A: dict index -> frozenset subset of P."""
    out = set()
    if r == 2:
        for R in combinations(Yp, 2):
            out.add((frozenset(), frozenset(R)))
        return out
    for R0 in combinations(Yp, r):
        heavy = [x for x in P if sum(1 for y in R0 if x in A[y]) >= r - 1]
        if not heavy:
            out.add((frozenset(), frozenset(R0)))
            continue
        for x in heavy:
            Ypp = tuple(y for y in R0 if x in A[y])
            A2 = {y: A[y] - {x} for y in Ypp}
            for (B2, R2) in lemma4_all(r - 1, P - {x}, Ypp, A2):
                out.add((B2 | {x}, R2))
    return out


def lemma4_ok(r, P, A, B, R):
    if len(B) + len(R) != r:
        return False
    for q in P - B:
        if sum(1 for y in R if q in A[y]) > len(R) - 2:
            return False
    return True


def proof_sets(adj, n):
    """All final sets D the proof of Theorem 1 can produce (all choices)."""
    nb = [((1 << n) - 1) & ~adj[v] & ~(1 << v) for v in range(n)]
    d = [pc(adj[v]) for v in range(n)]
    m = lm([n - 1 - x for x in d])
    sets = []
    if 2 * m >= n:
        W = [v for v in range(n) if n - 1 - d[v] >= m]
        a = n - m - 1
        for Acomb in combinations(W, a):
            sets.append(((1 << n) - 1) & ~sum(1 << v for v in Acomb))
        return m, sets, "J", 0
    U = [v for v in range(n) if d[v] == n - 1]
    Q = [v for v in range(n) if d[v] >= m]
    Y = [v for v in range(n) if d[v] < m]
    P = frozenset(v for v in Q if v not in U)
    u = len(U)
    r = m - u + 1
    Um = sum(1 << v for v in U)
    if len(Y) >= r:
        A = {y: frozenset(q for q in P if (adj[y] >> q) & 1) for y in Y}
        assert all(len(A[y]) <= r - 2 for y in Y)
        res = lemma4_all(r, P, tuple(Y), A)
        mr = 0
        for (B, R) in res:
            assert lemma4_ok(r, P, A, B, R)
            mr = max(mr, len(B))
            sets.append(Um | sum(1 << v for v in B) | sum(1 << v for v in R))
        return m, sets, "2a", mr
    c = m + 1 - u - len(Y)
    Ym = sum(1 << v for v in Y)
    for B0 in combinations(sorted(P), c):
        sets.append(Um | Ym | sum(1 << v for v in B0))
    return m, sets, "2b", 0


def mode_lab(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    E = len(pairs)
    full = (1 << n) - 1
    nconn = nclosed = nnohp = bad = 0
    hist = {}
    cases = {"J": 0, "2a": 0, "2b": 0}
    nsets = 0
    maxr = 0
    for code in range(1 << E):
        adj = [0] * n
        for e in range(E):
            if (code >> e) & 1:
                i, j = pairs[e]
                adj[i] |= 1 << j
                adj[j] |= 1 << i
        if not connected(adj, n):
            continue
        nconn += 1
        d = [pc(adj[v]) for v in range(n)]
        nb = None
        closed = all(d[i] + d[j] <= n - 2 for (i, j) in pairs if not (adj[i] >> j) & 1)
        complete = all(x == n - 1 for x in d)
        need_nohp_check = True
        if closed and not complete:
            nclosed += 1
            nb = [full & ~adj[v] & ~(1 << v) for v in range(n)]
            m = lm([n - 1 - x for x in d])
            g = gamma2(nb, n)
            hist[g - m] = hist.get(g - m, 0) + 1
            if g >= m + 2:
                print("FAIL closed graph with Hyp", code)
                bad += 1
            m2, sets, case, mr = proof_sets(adj, n)
            cases[case] += 1
            maxr = max(maxr, mr)
            for D in sets:
                nsets += 1
                if pc(D) != m + 1 or not two_dom(nb, D, n):
                    print("FAIL construction", code, case, bin(D))
                    bad += 1
        if not has_hp(adj, n):
            nnohp += 1
            if nb is None:
                nb = [full & ~adj[v] & ~(1 << v) for v in range(n)]
            m = lm([n - 1 - x for x in d])
            # Hyp means no 2-dominating set of size m+1
            hyp = not any(two_dom(nb, sum(1 << v for v in c), n) for c in combinations(range(n), min(m + 1, n)))
            if hyp:
                print("FAIL counterexample to 213", code)
                bad += 1
    print(f"py lab n={n}: connected={nconn} closed_conn_noncomplete={nclosed} nonHP={nnohp} cases={cases} "
          f"sets_checked={nsets} max_rounds={maxr} slack={dict(sorted(hist.items()))} failures={bad}")


def mode_lemma(r, K):
    P = frozenset(range(K))
    subsets = [frozenset(c) for s in range(0, r - 1) for c in combinations(range(K), s)]
    fam = 0
    bad = 0
    maxr = 0
    for ny in (r, r + 1):
        for F in combinations_with_replacement(range(len(subsets)), ny):
            A = {i: subsets[F[i]] for i in range(ny)}
            fam += 1
            for (B, R) in lemma4_all(r, P, tuple(range(ny)), A):
                maxr = max(maxr, len(B))
                if not lemma4_ok(r, P, A, B, R):
                    bad += 1
                    print("FAIL lemma4", r, K, F, B, R)
    print(f"py lemma r={r} K={K}: families={fam} max_rounds={maxr} failures={bad}")


if __name__ == "__main__":
    if sys.argv[1] == "lab":
        mode_lab(int(sys.argv[2]))
    elif sys.argv[1] == "lemma":
        mode_lemma(int(sys.argv[2]), int(sys.argv[3]))
