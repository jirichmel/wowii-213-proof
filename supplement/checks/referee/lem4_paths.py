"""referee213: Lemma 4 (selection lemma) in the abstract, every choice path.

For r, N (|P| = N) and s = |Y'| >= r, every multiset of s subsets of P = {0..N-1} of size <= r-2.
For each family, every run of the unrolled procedure is explored: every start R0 (r-subset of
the index set), every heavy q chosen, every choice of |R|-1 indices among those y in R with q in
A_y. At every stop the conclusion of Lemma 4 is checked from the definition:
B subset of P, R subset of Y', |B|+|R| = r, every q in P\\B lies in at most |R|-2 of the A_y (y in R).
Also checked: number of rounds <= r-2 and |R| >= 2 at the stop.
Own code; shares nothing with pdom.py / lem4.c.
Run: python3 lem4_paths.py
"""
import itertools, sys
from functools import lru_cache

def check(r, N, s):
    P = range(N)
    sets = [frozenset(c) for k in range(0, r - 1) for c in itertools.combinations(P, k)]
    fam_count = 0; stops = 0; fails = 0; maxrounds = 0
    for fam in itertools.combinations_with_replacement(range(len(sets)), s):
        A = [sets[i] for i in fam]
        fam_count += 1
        seen = set()
        stack = [(frozenset(), frozenset(R0), 0) for R0 in itertools.combinations(range(s), r)]
        while stack:
            B, R, rounds = stack.pop()
            if (B, R) in seen:
                continue
            seen.add((B, R))
            heavy = [q for q in P if q not in B and sum(1 for y in R if q in A[y]) >= len(R) - 1]
            if not heavy:
                stops += 1
                ok = (len(B) + len(R) == r and len(R) >= 2 and rounds <= r - 2 and
                      all(sum(1 for y in R if q in A[y]) <= len(R) - 2 for q in P if q not in B))
                if not ok:
                    fails += 1
                    if fails < 5:
                        print("FAIL", r, N, s, A, B, R)
                continue
            for q in heavy:
                Yq = [y for y in R if q in A[y]]
                for R2 in itertools.combinations(Yq, len(R) - 1):
                    stack.append((B | {q}, frozenset(R2), rounds + 1))
                    maxrounds = max(maxrounds, rounds + 1)
    print(f"r={r} N={N} |Y'|={s}: families {fam_count}, stop states {stops}, "
          f"max rounds {maxrounds}, failures {fails}", flush=True)
    return fails

tot = 0
for (r, N, s) in [(2, 3, 2), (2, 3, 4), (3, 4, 3), (3, 5, 3), (3, 5, 4), (3, 6, 5),
                  (4, 5, 4), (4, 6, 4), (4, 5, 5), (4, 6, 5), (5, 6, 5), (5, 5, 6), (6, 7, 6)]:
    if len(sys.argv) > 1 and (r, N, s) == (6, 7, 6):
        continue
    tot += check(r, N, s)
print("TOTAL FAILURES", tot)
