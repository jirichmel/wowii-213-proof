The formal proof of Conjecture 213 (Lean 4.37.0-rc1, Mathlib 31ce06eaadf4a200c0e1407c5f10953cf606b8f8)

Build:  lake exe cache get      (downloads Mathlib's compiled files)
        lake build              (builds LeanWowii, which imports LeanWowii.W213.Main)
        lake env lean LeanWowii/W213/Audit.lean

Main result: W213.conjecture213Statement (LeanWowii/W213/Main.lean). Its statement and the
definitions it uses are printed in Appendix A of the paper and by Audit.lean.

The comments in the Lean files use the numbering of the working text from which the formal proof
was made. It corresponds to the paper as follows.

  Lean comments                    paper
  Fact A                           Lemma 3
  Lemma J                          Lemma 4
  Lemma G (a)-(g)                  Lemma 5 (a)-(g)
  Lemma 3                          Lemma 5 (h)
  Lemma 4 (selection lemma)        Lemma 6
  Theorem 1                        Theorem 2
  Corollary 2                      Theorem 2 restated: no closed, connected, non-complete graph
                                   satisfies lm + 2 <= gamma_2 of the complement
  Lemma M                          Lemma 8
  Lemma C (closure)                Lemmas 9 and 10 (proved directly on Hamiltonian paths)
  Corollary 3                      Theorem 1 (Conjecture 213)

Only comment lines differ from the files of the original project; the line counts are unchanged.
