# Group: `later-chapters` — Chapters 3–11

Planned, not yet stated.  Nothing here has a declaration in the repository, so nothing
here is publishable; this file records the route so a restarted orchestrator does not
re-derive it.

## `alterations` — Chapter 3

Random construction followed by repair.  Theorem 3.1.1 (a dominating set of size
`≤ n(1 + log(δ+1))/(δ+1)`), Theorem 3.2.3 (Heilbronn: `n` points in the unit square with
every triangle of area `≳ n⁻²`), Markov's inequality, Theorem 3.4.1 (Erdős 1959: graphs of
arbitrarily high girth and chromatic number) and Theorem 3.5.1 (Radhakrishnan–Srinivasan
`m(k) ≳ 2^k √(k / log k)` by random greedy colouring).

This is the first group needing real analysis — logs and exponentials throughout — and
Theorem 3.2.3 needs plane geometry and areas, which is a much larger dependency than
anything in Chapters 1–2.  Expect to state §3.1, §3.3 and §3.4 first and leave §3.2 late.

## `second-moment` — Chapter 4

Thresholds for fixed subgraphs, clique number of `G(n, p)`, Hardy–Ramanujan, distinct
sums, Weierstrass approximation.  The first group that genuinely needs a probability
space rather than finite averaging: variance arguments over `G(n, p)` do not reduce to
counting as cleanly as Chapters 1–3 do.  Mathlib's `ProbabilityTheory.variance` and
`ProbabilityTheory.IndepFun` are the obvious dependencies.

## `chernoff` — Chapter 5

The Chernoff bound and three applications (discrepancy, nearly equiangular vectors, the
Hajós conjecture counterexample).  Mathlib has sub-Gaussian machinery
(`ProbabilityTheory.HasSubgaussianMGF`) that may cover the bound itself.

## `local-lemma` — Chapter 6

The Lovász local lemma, its lopsided and algorithmic forms, and applications to hypergraph
colouring, independent transversals and directed cycles.  Theorem 1.1.9 (Spencer's Ramsey
lower bound via the local lemma) belongs here rather than in `introduction`, since it is
the local lemma that does the work.

## `correlation`, `janson`, `concentration`, `entropy`, `containers` — Chapters 7–11

Harris–FKG and applications; Janson's inequalities and the chromatic number of a random
graph; bounded differences, martingale concentration, isoperimetry, Talagrand, the
Euclidean TSP; entropy, Shearer's lemma, Sidorenko; hypergraph containers.

Chapters 9–11 are research-level and are the right place to expect reductions rather than
single-PR proofs.
