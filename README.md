# A proof of Conjecture 213 of Written on the Wall II

Jiří Chmel. Preprint, version 1, 22 November 2026.

> **Status: preprint, not yet fully reviewed by the author.** The author's own review of the proofs is planned for
> 22 November 2026, and a reviewed version will replace this one. Until then, read it as unreviewed work.

**The paper:** [`WOWII213_proof.pdf`](WOWII213_proof.pdf), 10 pages.

## Abstract

Conjecture 213 of Written on the Wall II, a list of conjectures made by the program Graffiti.pc, states that a
connected graph G on n ≥ 2 vertices has a Hamiltonian path if the 2-domination number of its complement exceeds the
lower median of the degree sequence of the complement by at least two. We prove it.

The core of the proof is the inequality γ₂(Gᶜ) ≤ lm(Gᶜ) + 1, where Gᶜ is the complement of G. It holds for every
connected, non-complete graph G that is closed in the sense of Bondy and Chvátal, that is, d(u) + d(v) ≤ n − 2 for
all non-adjacent vertices u and v. The conjecture follows because adding an edge to G cannot decrease
γ₂(Gᶜ) − lm(Gᶜ), and an edge-maximal graph without a Hamiltonian path is closed. The inequality is proved by an
explicit polynomial-time construction based on a selection lemma for set systems. It is best possible, and so is
the constant 2 in the conjecture.

The proof has been formalised in Lean 4 with Mathlib and checked by the Lean kernel.

## Use of generative AI

The proof was found, and the paper, the programs and the formalisation were written, by Claude Opus 5.5, a generative
AI system made by Anthropic. Claude was used through Claude Code, in sessions directed by the author. Section 1.1 of
the paper describes this. Claude is not an author. None of the checking described in the paper is external peer
review.

## Contents

| Path | Contents |
|---|---|
| `WOWII213_proof.pdf` | The paper (preprint, version 1). |
| `source/paper.tex`, `source/build.sh` | Its LaTeX source and build script. |
| `supplement/README.txt` | What the supplement contains, and which program and log gives each number in the paper. |
| `supplement/lean/` | The formal proof in Lean 4 (version 4.37.0-rc1) with Mathlib (revision 31ce06eaadf4a200c0e1407c5f10953cf606b8f8), with its build log. |
| `supplement/checks/` | The checking programs (C and Python, no dependencies) and their outputs. |
| `SHA256SUMS` | The SHA-256 hash of every other file in this repository, as published in version 1. |
| `WOWII213_proof.pdf.ots`, `SHA256SUMS.ots` | OpenTimestamps proofs that these two files existed at the time recorded in the Bitcoin blockchain. |

## Timestamps

`WOWII213_proof.pdf` and `SHA256SUMS` are timestamped in the Bitcoin blockchain with
[OpenTimestamps](https://opentimestamps.org). `SHA256SUMS` lists the hash of every other file, so its timestamp
covers the whole repository as published.

A fresh proof is complete only after the calendar servers' Bitcoin transaction has been confirmed, usually within a
few hours. The completed (upgraded) `.ots` files will be committed then.

To check:

    shasum -a 256 -c SHA256SUMS                  # every file matches the list
    pip install opentimestamps-client
    ots verify WOWII213_proof.pdf.ots            # needs a Bitcoin node, or:
    # drop the .ots file and the PDF on https://opentimestamps.org

## Licence

All files are licensed under the Creative Commons Attribution 4.0 International licence (CC BY 4.0); see `LICENSE.md`.

## How to cite

Jiří Chmel, *A proof of Conjecture 213 of Written on the Wall II*, preprint, version 1 (22 November 2026), GitHub.
