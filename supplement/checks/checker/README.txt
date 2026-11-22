checker213: adversarial computational check of the Claim C proof of WOWII Conjecture 213 (21 Nov 2026).
All programs written from scratch here; none of cdom.c, pdom.py, lem4.c, check_theorem1.c was used or read.

core.h     shared C core: closedness, lm, 2-domination, gamma_2 (subset enumeration AND branch-and-bound),
           Hamiltonian path (DFS AND bitmask DP), the proof of Theorem 1 with every choice of Lemma 4 explored
           (all R0, all heavy q, all (|R|-1)-subsets; memo on (B,R)); every final set checked by definition.
lab.c      all labelled graphs n <= 8.            cc -O2 -o lab lab.c;  ./lab N [part nparts]
iso.c      own generator of connected graphs up to isomorphism, n <= 10 (counts = OEIS A001349);
           Hyp + Hamiltonian path on every graph; Lemma C (MNT => closed) check.
                                                   cc -O2 -o iso iso.c;  ./iso NMAX [part nparts]
rnd.c      random / structured / annealed closed graphs up to n = 40, adversarial Lemma 4 roots,
           greedy deep dives maximising the rounds, exact gamma_2 for n <= NEX; random Hyp graphs n <= 20.
                                                   cc -O2 -o rnd rnd.c -lm; ./rnd MODE n trials seed [NEX]; runs.sh
pycheck.py second implementation in Python (no shared code): labelled n <= 7, recursive Lemma 4 with all
           choices; abstract Lemma 4 brute force.  python3 -I pycheck.py lab N | lemma R K
logs/      all outputs.
