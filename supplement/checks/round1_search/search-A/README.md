# search-A: exhaustive search for Conjecture 213 (WoWII)

Conjecture: G connected, n > 1, gamma_2(H) >= lm(H) + 2 for H = complement  =>  G traceable.
slack(G) = gamma_2(H) - lm(H) - 2; a counterexample is a non-traceable connected G with slack >= 0.

## Programs (all `cc -O2 -o NAME NAME.c`)
- `inv1.h`  invariants I: Ham path by DFS with connectivity prune; gamma_2 by subsets in order of
  size (Gosper); lower median by insertion sort; graph6/edge-list writers.
- `inv2.h`  invariants II (no shared code): Ham path by subset DP (path end-sets), test of G+uv from
  the table of G; gamma_2 = n - max{|U| : every u in U has >= 2 neighbours outside U}; lower median by histogram.
- `mycanon.h` own canonical form (colour refinement + individualisation, twin pruning), n <= 11.
- `s213_lib.c NMAX PREFIX`  generation by tools/lib/smallgraph.h (connected graphs by vertex
  addition) + inv1.h.  Counts per n, writes every non-traceable graph with slack.
- `s213_own.c` own generation + inv2.h:
  - `nt N PREFIX`  all connected non-traceable graphs on N vertices (edge addition from non-path trees),
    plus the edge-maximal ones (`PREFIX_ntmax_N.txt`).
  - `cl N PREFIX`  only CLOSED non-traceable graphs (no non-adjacent pair with degree sum >= n-1),
    "add an edge, take the closure"; reaches every edge-maximal non-traceable connected graph
    (`PREFIX_clmax_N.txt`).
  - `all NMAX`     all connected graphs by vertex addition with own canonical form: hypothesis counts.
- `t_inv.c`, `t_brute.py`  cross-checks of the two invariant sets (random graphs) against each other
  and a Python brute force; tests of Lemma M and Lemma C below.
- `analyze.py`, `nonscat.py`  structure of near misses; split into scattering / non-scattering.

## Lemmas used (proved by hand, tested by t_inv.c)
- Lemma M (slack monotone): slack(G+e) >= slack(G).  H loses an edge; 2-dominating sets of H-e
  2-dominate H, and each order statistic of the degree sequence can only drop.  Hence a counterexample
  on n vertices exists iff an edge-maximal non-traceable connected graph on n vertices has slack >= 0.
- Lemma C (path closure; Bondy-Chvatal applied to G v K1): non-adjacent u,v with d(u)+d(v) >= n-1:
  G traceable <=> G+uv traceable.  So edge-maximal non-traceable graphs are closed.
Outputs in `out/`.

## Results (logs in out/)
| n | connected | hypothesis | non-traceable | MNT | closed non-traceable | max slack (non-tr.) |
|---|---|---|---|---|---|---|
| 2..9 | 1,2,6,21,112,853,11117,261080 | 1,2,5,11,57,261,2248,27724 | 0,0,1,3,21,119,1087,12653 | -,-,1,1,4,6,13,23 | -,-,1,2,9,31,231,2275 | -1 (n>=4) |
| 10 | 11716571 | 874505 | 233999 | 52 | 37302 | -1 |
| 11 | (not enumerated) | (not computed) | (not computed) | 109 | 896253 | -1 (via Lemma M) |
Counterexamples: none for n <= 11.  Basis: program only, two implementations agree for every entry except
the n=10 hypothesis count (one of mine; agrees with the classes agent's independent generator) .
Closed connected non-complete graphs (Claim C): 1,2,11,49,514,7333,209149 for n=4..10, none satisfies the
hypothesis; maximal closed ones 1,1,5,11,40,246,1757 (two implementations agree, n<=10).
Pair/triple certificate (certtest_A.c) holds for every closed connected non-complete graph n<=10.
n=11 MNT lists from own-canon (s213_own cl) and smallgraph-canon (s213_libcl) are identical as sets (109 graphs).
Universal-vertex class (s213_libu.c, own_u128.c with mycanon128.h; agree as sets at n=12): closed non-traceable
graphs with a universal vertex n=5..12: 2,6,14,47,170,1005,8355,125042; maximal 1,3,4,8,12,24,41,87; best slack -1;
no counterexample with a universal vertex on <= 12 vertices.  n=13: partial (see out/libu13.log).
Claim C at n=11 (s213_cc cc 11): stopped at the time limit, incomplete (out/own_cc11.log).
Programs added: s213_cc.c (modes cc, clp, u), s213_libcc.c, s213_libu.c, own_u128.c, mycanon128.h, canonlist.c,
scat.c, tough.py, certtest_A.c, certlist.py.
