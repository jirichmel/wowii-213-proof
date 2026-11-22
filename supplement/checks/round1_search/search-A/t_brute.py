# t_brute.py -- third, plain brute force: reads "G n ham gamma2 lowmed | edges" lines from t_inv
# and recomputes Hamiltonian path (permutations), gamma_2 (all subsets), lower median (sorted list).
import sys, itertools
bad = tot = 0
for line in sys.stdin:
    if not line.startswith("G "): continue
    head, edges = line.split("|")
    _, n, h, g, m = head.split(); n, h, g, m = int(n), int(h), int(g), int(m)
    if n > 8: continue
    E = set()
    for e in edges.split():
        u, v = map(int, e.split("-")); E.add((u, v)); E.add((v, u))
    ham = any(all((p[i], p[i+1]) in E for i in range(n-1)) for p in itertools.permutations(range(n)))
    nb = {v: {w for w in range(n) if (v, w) in E} for v in range(n)}
    gam = min(len(D) for k in range(n+1) for D in itertools.combinations(range(n), k)
              if all(len(nb[v] & set(D)) >= 2 for v in range(n) if v not in D))
    deg = sorted(len(nb[v]) for v in range(n))
    lm = deg[n//2 - 1] if n % 2 == 0 else deg[(n+1)//2 - 1]
    tot += 1
    if (int(ham), gam, lm) != (h, g, m): bad += 1; print("MISMATCH", line.strip())
print("checked", tot, "graphs, mismatches", bad)
