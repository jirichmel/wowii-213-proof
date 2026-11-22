"""Recompute (with check.py's independent invariant code) traceability, gamma_2(H), lm(H) on rows of sb.c TSV.
Usage: python3 check_tsv.py FILE MINSLACK [EVERY]: all rows with slack>=MINSLACK plus every EVERY-th row."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check import adj_from_edges, invariants, connected
fn, ms = sys.argv[1], int(sys.argv[2]); every = int(sys.argv[3]) if len(sys.argv) > 3 else 0
ok = bad = 0
for i, line in enumerate(open(fn)):
    f = line.rstrip('\n').split('\t'); n, sl, g2, lm = map(int, f[:4])
    if not (sl >= ms or (every and i % every == 0)): continue
    edges = [tuple(map(int, e.split('-'))) for e in f[6].split()]
    adj = adj_from_edges(n, edges)
    tr, pg2, plm = invariants(n, adj)
    if (not tr) and connected(n, adj) and pg2 == g2 and plm == lm and pg2 - plm - 2 == sl: ok += 1
    else: bad += 1; print("MISMATCH", line.strip())
print(f"{fn}: checked {ok+bad}, agree {ok}, disagree {bad}")
