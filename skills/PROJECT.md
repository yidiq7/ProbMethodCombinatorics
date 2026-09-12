# ProbMethodCombinatorics

Formalizing Yufei Zhao's *Probabilistic Methods in Combinatorics* (MIT 18.226, Fall 2022)
in Lean 4 with Mathlib.

The source PDF is in the repository at `sources/mit18_226_f22_lec_full.pdf` and every task
cites it by theorem number.  **Its PDF page numbers run six ahead of the printed page
numbers** — Theorem 1.1.2 is on printed page 3, PDF page 9.

The plan is `roadmap/README.md`, with the mathematics of each group in
`roadmap/introduction.md` and `roadmap/expectation.md`.  Read your task's group file: it
says what the node claims, where it sits, and usually what route the book takes.

## Pinned dependencies

- Lean `leanprover/lean4:v4.33.0`
- Mathlib `v4.33.0` (tag, not master)

Both are fixed for the life of the project.  Do not edit `lean-toolchain`,
`lakefile.toml`, or `lake-manifest.json` — a PR touching them is refused outright.
