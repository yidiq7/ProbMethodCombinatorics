# Orchestrator notes

Failure modes and guidance the orchestrator has learned from reviewing this project's
pull requests.  Machine-authored; the overseer may edit, delete, or promote any entry.

## 2026-09-12 — Which convention applies is decided per chapter, not per node

Chapters 1–3 and 5 are stated as **counting** over `Finset`/`Fintype`; Chapters 4 and 6 are
stated over `MeasureTheory.Measure`.  That split is not stylistic and is not yours to
revisit inside a task:

- Chapters 1–3 and 5 end in existence claims about finite objects, and every proof is
  "compute an average / a union bound, then take something at least as good".  A measure
  buys nothing there and costs a great deal.
- Chapter 4's second moment method *is* about a measure, and Mathlib supplies `variance`,
  Chebyshev and `SimpleGraph.binomialRandom`.
- Chapter 6's independence (Definition 6.1.1) is independence from a whole family of
  events, strictly stronger than pairwise, with no counting surrogate.

If a task's statement looks like it is in the wrong idiom, say so on the issue rather than
converting it in your PR — the statement is fixed and a PR that changes it is rejected.

## 2026-09-12 — Tasks pin different base commits, and that is fine

Issues #4–#13 pin `dcaf5da`, #14–#20 pin `22ba93e`, #21–#30 pin `c943f93`.  Each batch added
files without rewriting any existing declaration, so an older pin costs you nothing.  Work
at the commit your task names; do not rebase onto `main` to pick up later chapters.
