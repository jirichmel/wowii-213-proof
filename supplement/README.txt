Supplement to "A proof of Conjecture 213 of Written on the Wall II" (version of 21 November 2026)
=================================================================================================

The proofs in the paper use no computation. This folder holds the formal proof in Lean and the
programs that checked the finite consequences. Every C program builds with "cc -O2 -I. -o NAME
NAME.c -lm" inside its own folder and has no other dependency; the Python scripts need only the
standard library ("python3 -I SCRIPT ...").

lean/  The formal proof (Section 10 and Appendix A of the paper); see lean/README.txt
-----
  LeanWowii/W213/  Defs, Selection, Structure, CaseJ, Monotone, Closure, Theorem1, Main (1642
                   lines) and Audit (160 lines, checks of the definitions on small graphs).
  LeanWowii.lean   root file of the library (imports LeanWowii.W213.Main).
  lakefile.toml, lean-toolchain, lake-manifest.json   Lean 4.37.0-rc1, Mathlib revision
                   31ce06eaadf4a200c0e1407c5f10953cf606b8f8.
  Build:   lake exe cache get
           lake build
           lake env lean LeanWowii/W213/Audit.lean    (prints the axioms and the definitions)
  BUILD_LOG.txt    output of a build on 21 November 2026: the main theorem
                   W213.conjecture213Statement depends only on propext, Classical.choice and
                   Quot.sound.

checks/  Programs and their outputs. Programs said to share no code were written independently
-------  of each other, from the mathematical statements, without reusing each other's code.
  session/      check_theorem1.c: runs the construction of Theorem 2 with random choices and checks
                the set; exact gamma_2 for small n. Logs check_theorem1.txt (labelled n <= 7, random
                and hub-type graphs up to n = 63) and check_theorem1_n8.txt (all 9007520 labelled
                closed connected non-complete graphs with n = 8).
                sharpness_check.py: the n = 7 example of Section 2 (and an n = 6 one), F(n,s) for
                s <= 3 (Proposition 11) and K_{n-1} u K_1 (Remark 12); output sharpness_check.txt.
  prover/       cdom.c (with smallgraph.h), pdom.py, lem4.c, example26.py: the first checks of the
                proof. logs/c_lab8.txt (n = 8 labelled), c_iso10.txt (n <= 10 up to isomorphism),
                c_lem4.txt and py_lemma.txt (Lemma 6), c_hub.txt and py_hub.txt (the loop of Remark
                7 on hub-type graphs up to n = 64), py_lab7.txt (exact gamma_2, n <= 7).
  referee/      ref213.c and Python scripts of the referee. logs/lab7.txt (Theorem 2 and Conjecture
                213, labelled n = 7), lab8.txt (Theorem 2, labelled n = 8), sharp.txt (F(n,s)),
                discon.txt (connectivity is needed), mnt.txt (Lemma 10), hub_*.txt, struct_*.txt.
  checker/      core.h, lab.c, iso.c, rnd.c, pycheck.py (see its README.txt). It explores every
                choice that the proof of Theorem 2 allows. logs/lab8_part*.txt (labelled n = 8:
                Theorem 2, and Conjecture 213 with nonHP_with_Hyp=0), iso9.txt and iso10_part*.txt
                (up to isomorphism, n <= 10: Theorem 2, Conjecture 213, and Lemma 10 on all
                edge-maximal non-traceable graphs), py_lemma*.txt, rnd_*.txt.
  judge/        j213.c. logs/thm_n2-7.txt, thm_n8.txt (Theorem 2, labelled, exact gamma_2),
                conj_n2-7.txt (Conjecture 213, labelled n <= 7), lem4.txt (Lemma 6), hub.txt,
                rnd*.txt.
  readings/     readings213.c: Conjecture 213 under the readings of Section 2 (at least / exactly
                two; lower, upper and literal median), labelled n <= 7; output readings213_n7.txt.
  round1_search/ The two exhaustive searches of the first round of work, sharing no code:
                search-A (s213_*.c with smallgraph.h; its README.md has the table of counts) and
                search-B (sb.c and check.py; out10/log.txt has the counts for n <= 10).
                Their READMEs also name some large outputs that were not kept (search-A:
                out/libu13.log, out/own_cc11.log; search-B: out/conn_n9.keys, nt_n*.tsv, ntonly_*,
                ntmax_*, outnt/); they are not part of this supplement.

Comments in some programs refer to paths of the project in which they were written (tools/...,
conjectures/...); those paths are not part of this supplement. Comments also name the AI agents that
wrote or checked the programs (prover, referee, checker, judge, session, status reviewer); see Section
1.1 of the paper.

Where each number of Section 10 comes from
------------------------------------------
  Closed connected non-complete graphs, labelled, n = 4..8: 4, 35, 1401, 87258, 9007520
      session/check_theorem1*.txt, judge/logs/thm_*.txt, checker/logs/lab8_part*.txt,
      referee/logs/lab7.txt and lab8.txt, prover/logs/c_lab8.txt.
  The same up to isomorphism, n = 4..10: 1, 2, 11, 49, 514, 7333, 209149
      prover/logs/c_iso10.txt, checker/logs/iso9.txt and iso10_part*.txt.
  Hypothesis graphs up to isomorphism, n = 2..10: 1, 2, 5, 11, 57, 261, 2248, 27724, 874505,
  none of them non-traceable; 11716571 connected graphs at n = 10
      round1_search/search-B/out10/log.txt, checker/logs/iso9.txt and iso10_part*.txt
      (round1_search/search-A/README.md gives the same table for search-A).
  Hypothesis graphs, labelled, n = 2..7: 1, 4, 34, 306, 13438, 483928
      judge/logs/conj_n2-7.txt, readings/readings213_n7.txt, referee/logs/lab7.txt (n = 7).
  Lemma 6: 61474519 set systems with r = |P| = |Y'| = 6
      prover/logs/c_lem4.txt, judge/logs/lem4.txt. The other ranges are listed in these logs and
      in prover/logs/py_lemma.txt and checker/logs/py_lemma*.txt.
  The loop of Remark 7: on the small graphs above it runs at most one round, only at n = 10
      (checker/logs/iso10_part7.txt, maxrounds=1; prover/logs/c_iso10.txt, |B| = 1 once).
      On random closed graphs generated with a structure meant to make it run (in most of them
      it still makes no round), up to 13 rounds; these random tests come from single programs
      (checker/logs/rnd_hubk.txt, max_rounds=13 at n = 40; also rnd_anneal.txt), and in
      session/check_theorem1.txt, judge/logs/hub.txt, prover/logs/c_hub.txt and py_hub.txt.

Two programs once produced non-symmetric adjacency matrices through a macro that evaluated a
random index twice (prover/cdom.c and judge/j213.c, hub generators); the failures they reported
were on these non-graphs. Both were fixed, a symmetry guard was added, and the reruns found no
failure. judge/logs/hub.txt records this at its top.
