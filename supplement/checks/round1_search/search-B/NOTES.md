# search-B results, Conjecture 213 (WoWII)

Reading of the definitions: H = complement of G; gamma_2(H) by definition (vertices of H-degree <= 1
are forced); lm(H) = sorted H-degrees d_1<=...<=d_n, d_{n/2} (n even), d_{(n+1)/2} (n odd).
slack(G) = gamma_2(H) - lm(H) - 2; hypothesis <=> slack >= 0; counterexample = connected,
non-traceable, slack >= 0.

## Exhaustive results (sb.c full; second implementation where stated)

| n | connected | hypothesis | non-traceable | cex | max slack (NT) | slack histogram of NT |
|---|---|---|---|---|---|---|
| 2 | 1 | 1 | 0 | 0 | - | |
| 3 | 2 | 2 | 0 | 0 | - | |
| 4 | 6 | 5 | 1 | 0 | -1 | -1:1 |
| 5 | 21 | 11 | 3 | 0 | -1 | -2:2 -1:1 |
| 6 | 112 | 57 | 21 | 0 | -1 | -3:3 -2:11 -1:7 |
| 7 | 853 | 261 | 119 | 0 | -1 | -4:11 -3:70 -2:32 -1:6 |
| 8 | 11117 | 2248 | 1087 | 0 | -1 | -5:15 -4:393 -3:444 -2:207 -1:28 |
| 9 | 261080 | 27724 | 12653 | 0 | -1 | -6:92 -5:3894 -4:5670 -3:2593 -2:378 -1:26 |
| 10 | 11716571 | 874505 | 233999 | 0 | -1 | -7:140 -6:21035 -5:107524 -4:76536 -3:25971 -2:2672 -1:121 |

Basis:
- n<=8: two implementations sharing no code (sb.c; check.py with its own generator, canonical form,
  subset-DP traceability, combinations gamma_2) agree on every number in the row, histogram included.
- n=9: generation by sb.c only (connected count = 261080 = OEIS A001349); invariants recomputed on all
  261080 graphs by check.py: all numbers agree. Hypothesis count agrees with the project's 27724.
- n=10: sb.c full run. Connected count 11716571 = OEIS A001349 (so, since keys are labelled copies
  of the input graphs, exactly one representative per class). Non-traceable count and histogram are
  reproduced by a second generation route in sb.c (edge addition from non-path trees, DP traceability;
  shares the canonical-form code) and agree with search-A's board post (identical histogram).
  check.py recomputed invariants on all 2793 NT graphs with slack >= -2 and every 50th NT graph
  (7417 graphs): all agree. Hypothesis count 874505: sb.c only (search-A reports the same number from
  one of its implementations).

## n = 11, non-traceable graphs only (sb.c nt 11; 41 min wall, 812 s CPU)
All connected non-traceable graphs on 11 vertices, by edge addition from the 234 non-path trees
(complete: every connected non-traceable graph that is not a tree has a non-bridge edge, whose deletion
leaves a connected non-traceable graph; traceability of G+e for all e at once by a subset DP that was
checked against the DFS on every edge addition for n<=9, and reproduced the full-run n=10 numbers).
Result: 6,469,055 connected non-traceable graphs; no counterexample; max slack -1;
histogram -8:1305 -7:376545 -6:2765309 -5:2340959 -4:882206 -3:97940 -2:4670 -1:121.
Edge-maximal: 109 (search-A, different route via closures: 109). check.py re-verified the 109
maximal graphs and the 121 slack -1 graphs. Program only (one implementation for the 6,469,055).

## Lemma M (proof by hand; tested)
Adding an edge to G never decreases slack: H loses an edge, so every 2-dominating set of H-e is
2-dominating in H (gamma_2 can only grow) and every H-degree drops or stays (lm can only drop).
Non-traceability is closed under deleting edges. Hence a counterexample on n vertices exists iff some
edge-maximal non-traceable connected graph (MNT) on n vertices has slack >= 0.
Test: lemma_test.py, all labelled graphs n<=6 and every added edge (245760 pairs at n=6): 0 violations.

## Edge-maximal non-traceable connected graphs (sb.c nt mode)
Counts n=5..10: 1, 4, 6, 13, 23, 52 (search-A independently: same, n=4..10). n=11: see below.
Slack -1 MNT: n=6: 3, 7: 2, 8: 4, 9: 3, 10: 4.
For n = 7, 9, 10 the slack -1 MNT graphs are exactly F(n,s) = K_s v ((s+1)K_1 u K_{n-2s-1}),
1 <= s <= (n-2)/2. At n=8 there is one more: K_1 v (K_1 u net). At n=6 one more: the net.

## Tight family (proof by hand, tested n<=12 in lemma_test.py)
F(n,s), t = n-2s-1 >= 1: H = sK_1 u (K_{s+1} v tK_1); gamma_2(H) = s+2 (isolated vertices forced plus two
vertices of K_{s+1}); H-degrees: s zeros, t of value s+1, s+1 of value s+t, so lm(H) = s+1 and slack = -1.

## Near misses
All NT graphs with slack -1 at n=9 (26) and n=10 (121) are spanning subgraphs of some F(n,s)
(nearmiss.py). The only slack -1 NT graphs at n<=10 that are not: the net (n=6) and
K_1 v (K_1 u net) with the one-edge-deleted copy (n=8); none of these has a scattering set
(S with c(G-S) >= |S|+2).

## Degree-sequence route fails narrowly (program only, n<=9)
Non-traceable G violates Chvatal's condition for G v K_1: some i < (n+1)/2 has d_i <= i-1 and
d_{n+1-i} <= n-1-i. Test of "Chvatal-violating => slack <= -1" over all connected graphs:
violators n=6..9: 40, 299, 4800, 102060; with slack 0: 1, 1, 5, 7 (all traceable). So the degree
sequence alone cannot give the conjecture; out/chvatal_test.txt lists examples.

## Heuristic search n = 12..16 (rnd.c; basis: heuristic, proves nothing)
By Lemma M only edge-maximal non-traceable connected graphs matter. rnd.c samples them: random
non-path Pruefer tree, then one pass over a random order of the non-edges, adding an edge whenever the
graph stays non-traceable (subset DP on 2^n masks). Uniform over nothing in particular.
- Plain sampling: n=12,13,14: 20000 samples each; n=15,16: 4000 each. Max slack -1 every time; every
  sample with slack -1 was F(n,s) (counts equal: 4707, 6673, 3601, 1055, 579).
- Local search (perturb: delete up to 2n random edges, re-maximise; restart every 3000 steps):
  rnd2 (score favours slack) n=9..16, 20000 steps each: best slack -1, always F(n,s).
  rnd3 (F(n,s) penalised so the search explores other graphs) n=12..16, 30000 steps each: best slack
  among non-F maximal graphs = -2 (n=12..16). On n=6 and n=8 the same
  search finds the known non-F slack -1 graphs (net; K_1 v (K_1 u net)), and at n=10, 11 it finds -2,
  as the exhaustive lists say.
