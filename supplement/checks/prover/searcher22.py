# searcher22.py -- the n = 22 graph from the searcher's NOTES.md (lowest-degree R fails without ties):
# U = {0..4}, P = {5..10}, Q = U u P clique, Y = {11..21} independent, Y sees all of U, plus P-Y edges.
import random, sys
sys.path.insert(0, '.')
import pdom
n = 22
adj = [set() for _ in range(n)]
def add(a, b):
    adj[a].add(b); adj[b].add(a)
for a in range(11):
    for b in range(a + 1, 11): add(a, b)
for a in range(5):
    for b in range(11, 22): add(a, b)
NY = {5: [16, 17, 19], 6: [12, 18, 21], 7: [19, 20, 21], 8: [12, 13, 16], 9: [17, 18, 20], 10: [11, 14, 15]}
for q, ys in NY.items():
    for y in ys: add(q, y)
print("closed", pdom.is_closed(n, adj), "connected", pdom.is_connected(n, adj), "m", pdom.lower_median_H(n, adj))
rng = random.Random(1); st = pdom.Stats()
pdom.test_graph(n, adj, rng, st, 500, exact=False)
pdom.report("searcher n=22 graph, 500 random runs", st)
