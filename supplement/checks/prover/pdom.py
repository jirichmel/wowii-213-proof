#!/usr/bin/env python3
"""pdom.py -- second, independent test of the proof of Claim C (prover-claimC, 21 Nov 2026).

Shares no code with cdom.c.  Graphs are dicts of Python sets.  The construction of D is
written in the recursive form of Lemma 4 of proof.md (abstract double-miss lemma on the
family A(y) = N(y) n P), not as the loop used in cdom.c.

Modes
  lab N            all labelled graphs on N <= 7 vertices; construction + exact gamma_2(H)
  rnd N S SEED     S random closed connected non-complete graphs (own generator: random
                   two-level graph + perturbation, then (n-1)-closure); construction; exact
                   gamma_2(H) as well when N <= 13
  hub N S SEED     S random graphs of the hub family (loop of case A must run)
  named            the tie-break graph of round 1 and the n = 26 example of proof.md
  lemma RMAX NMAX  exhaustive check of the abstract Lemma 4 for r <= RMAX and ground sets of
                   size <= NMAX, by brute force over all (B, I) (no use of the recursion)
"""
import sys, random, itertools

def is_closed(n, adj):
    for a in range(n):
        for b in range(a + 1, n):
            if b not in adj[a] and len(adj[a]) + len(adj[b]) >= n - 1:
                return False
    return True

def is_connected(n, adj):
    seen = {0}; stack = [0]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w); stack.append(w)
    return len(seen) == n

def lower_median_H(n, adj):
    hs = sorted(n - 1 - len(adj[v]) for v in range(n))
    k = (n + 1) // 2            # ceil(n/2)
    return hs[k - 1]

def two_dominates_H(n, adj, D):
    for v in range(n):
        if v in D:
            continue
        miss = sum(1 for w in D if w != v and w not in adj[v])
        if miss < 2:
            return False
    return True

def gamma2_H(n, adj, upto):
    """smallest size of a 2-dominating set of H, searched up to size 'upto'; None if larger"""
    for k in range(0, upto + 1):
        for D in itertools.combinations(range(n), k):
            if two_dominates_H(n, adj, set(D)):
                return k
    return None

def lemma4(family, r, ground, rng):
    """family: list of (label, frozenset), each set of size <= r-2, len >= r, r >= 2.
    Returns (B, I): |B| + |I| = r, every q in ground minus B lies in <= |I|-2 sets of I."""
    assert r >= 2 and len(family) >= r
    for lab, s in family:
        assert len(s) <= r - 2
    F = rng.sample(family, r)
    xs = list(ground); rng.shuffle(xs)
    for x in xs:
        if sum(1 for _, s in F if x in s) >= r - 1:
            Fx = [(lab, s - {x}) for lab, s in F if x in s]
            B, I = lemma4(Fx, r - 1, ground - {x}, rng)
            return B | {x}, I
    return set(), [lab for lab, _ in F]

class Stats:
    def __init__(self):
        self.graphs = 0; self.cases = {'J': 0, 'A': 0, 'B': 0}; self.fail = 0
        self.maxslack = None; self.g2checked = 0; self.Bsizes = {}

def construct(n, adj, rng, st=None):
    m = lower_median_H(n, adj)
    V = set(range(n))
    if 2 * m >= n:
        case = 'J'
        cand = [v for v in V if n - 1 - len(adj[v]) >= m]
        need = n - m - 1
        assert need >= 0 and len(cand) >= need, "Lemma J: too few candidates"
        A = set(rng.sample(cand, need))
        D = V - A
    else:
        Q = {v for v in V if len(adj[v]) >= m}
        Y = V - Q
        U = {v for v in V if len(adj[v]) == n - 1}
        P = Q - U
        for a in Q:
            assert Q - {a} <= adj[a], "Q is not a clique"
        assert Y, "Y empty"
        u = len(U); r = m - u + 1
        assert u <= m - 1 and len(Y) >= m
        if len(Y) < r:
            case = 'B'
            assert u == 0 and len(Y) == m
            D = set(Y) | {rng.choice(sorted(Q))}
        else:
            case = 'A'
            family = [(y, frozenset(adj[y] & P)) for y in sorted(Y)]
            B, I = lemma4(family, r, frozenset(P), rng)
            D = U | set(B) | set(I)
            assert len(D) == m + 1
            if st is not None:
                st.Bsizes[len(B)] = st.Bsizes.get(len(B), 0) + 1
    ok = len(D) <= m + 1 and two_dominates_H(n, adj, D)
    return ok, case, m, D

def test_graph(n, adj, rng, st, reps, exact):
    st.graphs += 1
    for rep in range(reps):
        ok, case, m, D = construct(n, adj, rng, st if rep == 0 else None)
        if rep == 0:
            st.cases[case] += 1
        if not ok:
            st.fail += 1
            if st.fail <= 10:
                print("FAIL", case, n, sorted((a, b) for a in range(n) for b in adj[a] if a < b), sorted(D))
    if exact:
        m = lower_median_H(n, adj)
        g = gamma2_H(n, adj, m + 1)
        st.g2checked += 1
        slack = (g if g is not None else m + 2) - m - 2
        if st.maxslack is None or slack > st.maxslack:
            st.maxslack = slack
        if g is None:
            st.fail += 1
            print("gamma_2 > m+1 !", n, sorted((a, b) for a in range(n) for b in adj[a] if a < b))

def report(tag, st):
    print(f"{tag}: graphs {st.graphs}, cases {st.cases}, |B| histogram (case A) {dict(sorted(st.Bsizes.items()))}, "
          f"exact gamma_2 checked {st.g2checked}, max slack {st.maxslack}, failures {st.fail}")
    sys.stdout.flush()

def mode_lab(n, reps):
    rng = random.Random(12345 + n)
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    st = Stats(); count = 0
    for mask in range(1 << len(pairs)):
        adj = [set() for _ in range(n)]
        for i, (a, b) in enumerate(pairs):
            if (mask >> i) & 1:
                adj[a].add(b); adj[b].add(a)
        if all(len(adj[v]) == n - 1 for v in range(n)):
            continue
        if not is_closed(n, adj) or not is_connected(n, adj):
            continue
        count += 1
        test_graph(n, adj, rng, st, reps, exact=True)
    report(f"lab n={n} (labelled closed connected non-complete: {count})", st)

def closure(n, adj):
    changed = True
    while changed:
        changed = False
        for a in range(n):
            for b in range(a + 1, n):
                if b not in adj[a] and len(adj[a]) + len(adj[b]) >= n - 1:
                    adj[a].add(b); adj[b].add(a); changed = True

def random_closed(n, rng):
    """random two-level graph: a dense part of size k with density pd, a sparse part with
    density ps, cross density pc concentrated on a few dense vertices, then the closure."""
    while True:
        k = rng.randint((n + 1) // 2, n - 2)
        pd = rng.choice([1.0, 1.0, 0.95, 0.8])
        ps = rng.random() * 0.3
        pc = rng.random() * 0.35
        hubs = rng.sample(range(k), rng.randint(1, k))
        nuniv = rng.randint(0, max(0, k // 2))
        adj = [set() for _ in range(n)]
        def add(a, b):
            if a != b:
                adj[a].add(b); adj[b].add(a)
        for a in range(k):
            for b in range(a + 1, k):
                if rng.random() < pd:
                    add(a, b)
        for a in range(k, n):
            for b in range(a + 1, n):
                if rng.random() < ps:
                    add(a, b)
        for y in range(k, n):
            for q in hubs:
                if rng.random() < pc:
                    add(y, q)
        for x in range(nuniv):
            for v in range(n):
                add(x, v)
        for y in range(k, n):
            if not adj[y]:
                add(y, rng.randrange(k))
        closure(n, adj)
        if all(len(adj[v]) == n - 1 for v in range(n)) or not is_connected(n, adj):
            continue
        assert is_closed(n, adj)
        # random relabelling
        perm = list(range(n)); rng.shuffle(perm)
        return [set(perm[w] for w in adj[perm.index(v)]) for v in range(n)]

def mode_rnd(n, S, seed, reps):
    rng = random.Random(seed)
    st = Stats()
    for _ in range(S):
        adj = random_closed(n, rng)
        test_graph(n, adj, rng, st, reps, exact=(n <= 13))
    report(f"rnd n={n} S={S} seed={seed}", st)

def mode_lemma(rmax, nmax):
    """Lemma 4: r >= 2, family of r subsets (multiset) of [N], each of size <= r-2 ->
    exists I (subfamily, |I| = k) with k + #{q : q in >= k-1 members of I} <= r.
    (k <= 1 makes every ground element heavy.)  Families of exactly r sets suffice
    (a solution inside a subfamily works for the whole family)."""
    total = 0; bad = 0
    for r in range(2, rmax + 1):
        for N in range(0, nmax + 1):
            subsets = [frozenset(c) for s in range(0, min(r - 2, N) + 1) for c in itertools.combinations(range(N), s)]
            cnt = 0
            for fam in itertools.combinations_with_replacement(range(len(subsets)), r):
                sets = [subsets[i] for i in fam]
                cnt += 1
                found = False
                for k in range(0, r + 1):
                    for I in itertools.combinations(range(r), k):
                        heavy = sum(1 for q in range(N) if sum(1 for i in I if q in sets[i]) >= k - 1)
                        if k + heavy <= r:
                            found = True; break
                    if found:
                        break
                if not found:
                    bad += 1
                    if bad <= 5:
                        print("Lemma 4 FAILS:", r, N, [sorted(s) for s in sets])
            total += cnt
            print(f"lemma r={r} N={N}: families {cnt}, failures so far {bad}")
            sys.stdout.flush()
    print(f"lemma: total families {total}, failures {bad}")

def hub_graph(n, rng):
    """universal U, hubs S seeing every vertex of W, Z seeing U (and maybe one more),
    P' with a few W-neighbours, a few edges inside Y; returned relabelled, or None if not closed"""
    u = rng.randint(0, 3); h = rng.randint(1, 6); z = u + rng.randint(1, 3)
    rest = n - u - h - z
    if rest < 4:
        return None
    w = rng.randint(2, rest)
    pp = rest - w
    U = list(range(u)); S = list(range(u, u + h)); Pp = list(range(u + h, u + h + pp))
    Z = list(range(u + h + pp, u + h + pp + z)); W = list(range(u + h + pp + z, n))
    adj = [set() for _ in range(n)]
    def add(a, b):
        if a != b:
            adj[a].add(b); adj[b].add(a)
    Qs = U + S + Pp
    for i in range(len(Qs)):
        for j in range(i + 1, len(Qs)):
            add(Qs[i], Qs[j])
    for a in U:
        for b in range(n):
            add(a, b)
    for a in S:
        for b in W:
            add(a, b)
    k = rng.randint(0, 3)
    for a in Pp:
        for b in rng.sample(W, min(k, len(W))):
            add(a, b)
    if Pp and rng.random() < 0.5:
        for a in Z:
            add(a, rng.choice(Pp))
    Yall = Z + W
    for _ in range(rng.randint(0, 2)):
        add(rng.choice(Yall), rng.choice(Yall))
    if u == 0:
        for a in Yall:
            if not adj[a]:
                add(a, rng.choice(Qs))
    if all(len(adj[v]) == n - 1 for v in range(n)) or not is_connected(n, adj) or not is_closed(n, adj):
        return None
    perm = list(range(n)); rng.shuffle(perm)
    new = [set() for _ in range(n)]
    for a in range(n):
        for b in adj[a]:
            new[perm[a]].add(perm[b])
    return new

def mode_hub(n, S, seed, reps):
    rng = random.Random(seed)
    st = Stats(); tried = 0
    while st.graphs < S:
        tried += 1
        adj = hub_graph(n, rng)
        if adj is None:
            continue
        test_graph(n, adj, rng, st, reps, exact=(n <= 13))
    report(f"hub n={n} S={S} seed={seed} (tried {tried})", st)

def mode_named():
    """the tie-break graph of round 1 and the n = 26 hub example of proof.md"""
    rng = random.Random(7)
    st = Stats()
    n = 16; adj = [set() for _ in range(n)]
    def add(a, b):
        adj[a].add(b); adj[b].add(a)
    for a in range(8):
        for b in range(a + 1, 8):
            add(a, b)
    for a in range(4):
        for b in range(8, 16):
            add(a, b)
    for i in range(4):
        add(8 + 2 * i, 4 + i); add(9 + 2 * i, 4 + i)
    assert is_closed(n, adj) and is_connected(n, adj)
    print("tie-break graph: m =", lower_median_H(n, adj))
    test_graph(n, adj, rng, st, 200, exact=False)
    # n = 26 example: U = {0,1}, hubs {2,3,4}, P' = {5..12}, Z = {13,14,15}, W = {16..25}
    n = 26; adj = [set() for _ in range(n)]
    for a in range(13):
        for b in range(a + 1, 13):
            add(a, b)
    for a in range(2):
        for b in range(13, 26):
            add(a, b)
    for a in range(2, 5):
        for b in range(16, 26):
            add(a, b)
    for i, a in enumerate(range(5, 13)):     # each P' vertex sees two W vertices
        add(a, 16 + (2 * i) % 10); add(a, 16 + (2 * i + 1) % 10)
    assert is_closed(n, adj) and is_connected(n, adj)
    m = lower_median_H(n, adj)
    Y = [v for v in range(n) if len(adj[v]) <= m - 1]
    print("n=26 hub example: m =", m, "|Y| =", len(Y), "u = 2, r =", m - 2 + 1)
    test_graph(n, adj, rng, st, 200, exact=False)
    report("named", st)

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "lab":
        mode_lab(int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 3)
    elif mode == "rnd":
        mode_rnd(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]) if len(sys.argv) > 5 else 3)
    elif mode == "hub":
        mode_hub(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]) if len(sys.argv) > 5 else 3)
    elif mode == "named":
        mode_named()
    elif mode == "lemma":
        mode_lemma(int(sys.argv[2]), int(sys.argv[3]))
