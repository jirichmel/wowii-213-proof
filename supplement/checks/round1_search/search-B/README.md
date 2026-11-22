# search-B (Conjecture 213, WoWII)

Programs (no code shared with the project library tools/):

- `sb.c` — `cc -O2 -o sb sb.c`
  - `./sb full NMAX OUTDIR`: all connected graphs n=2..NMAX by vertex addition + own canonical
    form (equitable refinement, individualisation, automorphism pruning) + hash dedup.
    Per n: connected, hypothesis count, non-traceable count, counterexamples, slack histogram.
    Writes `OUTDIR/nt_n{n}.tsv` (n, slack, gamma2(H), lm(H), edges of G, key, edge list) for every
    non-traceable connected graph, and `conn_n{n}.keys` for n<=9.
  - `./sb nt N OUTDIR`: connected non-traceable graphs on N vertices only, by edge addition
    starting from the non-path trees (the family is closed under deleting non-bridge edges, so every
    member is reached). Writes `ntonly_nN.tsv` (all) and `ntmax_nN.tsv` (edge-maximal ones).
- `check.py` — second implementation (Python): own generator (colour refinement + brute force),
  traceability by subset DP, gamma_2 by combinations. `python3 -I check.py gen 8`;
  `python3 -I check.py keys out/conn_n9.keys 9` recomputes invariants on sb.c's n=9 list.
- `lemma_test.py` — tests Lemma M (monotonicity) on all labelled graphs n<=6 and the tight family.
- `nearmiss.py FILE THRESH [TOP]` — classifies near misses (in F(n,s)? scattering set?).

Outputs: `out/` (n<=9), `out10/` (n=10), `outnt/` (nt mode n=5..9), `outnt11/` (n=11).
- `rnd.c` — heuristic sampler/local search over edge-maximal non-traceable graphs, n<=18.
  `./rnd N SAMPLES SEED` (sampling), `./rnd N ITERS SEED ls` (local search; rnd_nonF.c is the same with
  the tight family F(n,s) penalised). Outputs in `outrnd/`.
- `check_tsv.py FILE MINSLACK [EVERY]` — recompute invariants (check.py code) on rows of sb.c output.
- `sb chv N KEYFILE` — tests "Chvatal path-condition violated => slack <= -1" (false; out/chvatal_test.txt).
