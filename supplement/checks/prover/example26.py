# example26.py -- Remark 5 of proof.md: the unrolled procedure of Lemma 4 started from R = W
# on the n = 26 example; prints every round and checks the final D (independent small script).
n = 26
adj = [set() for _ in range(n)]
def add(a, b):
    adj[a].add(b); adj[b].add(a)
for a in range(13):
    for b in range(a + 1, 13): add(a, b)
for a in range(2):
    for b in range(13, 26): add(a, b)
for a in range(2, 5):
    for b in range(16, 26): add(a, b)
for i, a in enumerate(range(5, 13)):
    add(a, 16 + (2 * i) % 10); add(a, 16 + (2 * i + 1) % 10)
deg = [len(adj[v]) for v in range(n)]
closed = all(deg[a] + deg[b] <= n - 2 for a in range(n) for b in range(a + 1, n) if b not in adj[a])
hs = sorted(n - 1 - d for d in deg); m = hs[(n + 1) // 2 - 1]
U = {v for v in range(n) if deg[v] == n - 1}; Q = {v for v in range(n) if deg[v] >= m}
Y = set(range(n)) - Q; P = Q - U; r = m - len(U) + 1
print("closed", closed, "m", m, "u", len(U), "r", r, "|Y|", len(Y), "Q", sorted(Q))
R = list(range(16, 26)); B = []
while True:
    cand = [q for q in sorted(P - set(B)) if len(adj[q] & set(R)) >= len(R) - 1]
    if not cand: break
    q = cand[0]; B.append(q); R = [y for y in R if y in adj[q]][:len(R) - 1]
    print("round: add", q, "to B; R =", R)
D = U | set(B) | set(R)
ok = all(sum(1 for w in D if w != v and w not in adj[v]) >= 2 for v in range(n) if v not in D)
print("B =", B, "|D| =", len(D), "= m+1:", len(D) == m + 1, "2-dominating in H:", ok)
