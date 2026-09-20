# ProbMethodCombinatorics

A [Choir](https://github.com/Weber-GeoML/Choir)-managed formalization, in Lean 4 with
Mathlib, of Yufei Zhao's lecture notes *Probabilistic Methods in Combinatorics*
(MIT 18.226, Fall 2022).

The source is in [`sources/`](sources/README.md); the plan and a per-chapter log are in
[`roadmap/`](roadmap/README.md); project conventions contributors should follow are in
[`skills/`](skills/conventions.md).

## Status

**285 theorems across all eleven chapters, with one `sorry`.**  `lake build` is green.

Every result the source *proves* is formalized.  The single remaining `sorry` is
`Containers.lean`'s `exists_containers_fingerprint_three_uniform` — the §11.3 corner, which
is an **open mathematical problem**, not unfinished formalization
([`roadmap/containers.md`](roadmap/containers.md) records what is known about it and what has
been ruled out).

Four stated theorems are proved *from* that obligation and so inherit `sorryAx`.  Their proofs
are complete; they are conditional on the corner, and an axiom check reports them as such:

| | |
|---|---|
| `exists_containers_three_uniform` | Theorem 11.3.1 |
| `exists_shrunken_containers_of_many_triangles` | |
| `exists_containers_triangleFree` | |
| `card_triangleFreeGraphs_le` | §11.1, Erdős–Kleitman–Rothschild |

Everything else in the corpus is unconditional.  Theorem 11.1.5 would inherit `sorryAx` too and
so is not stated at all.

Three sections stop short, and in each case the obstacle is a theorem the source **quotes
rather than proves**:

| Section | Rests on | In Mathlib? |
|---|---|---|
| §2.6 crossing number | Euler's formula, Kuratowski/Wagner, a topological crossing number | no |
| §9.4 isoperimetry | Brunn–Minkowski, Harper, Johnson–Lindenstrauss | no |
| §9.5–9.6 | Talagrand's inequality — the source says outright "we omit the proof" | no |

For §9.4 the groundwork *is* here: `HammingCube.lean` proves the slice decomposition and both
down-compression lemmas, including `card_cubeNbhd_cubeCompress_le`, which Mathlib does not
provide — its `UV` and `Down` results bound the *shadow* of a `k`-uniform family, not the
neighbourhood of an arbitrary subset.  What remains for Harper is one identified step (a set
fixed by every compression need not be an initial segment of the simplicial order); the plan
is in [`roadmap/concentration.md`](roadmap/concentration.md).

Never targets, because they are open problems: Question 2.4.1, Conjecture 4.6.2 (Erdős),
Conjectures 6.5.8 and 6.5.9 (Ryser, Ryser–Brualdi–Stein), Conjecture 11.1.4, Question 1.4.1.

### Deviations from the source

Five unstated hypotheses and one typo were found by computing small cases, and are documented
at the statements concerned: §2.4.4 needs `5 ≤ n`, §9.3.1 needs `2 ≤ n`, §2.5.2 needs
`0 < n`, §6.3 needs a strict inequality, and §6.5.6's `ℙ(Aᵢ) = 1 - 1/n` should read `1/n`.
§6.4's hypothesis is *strengthened* to `k (1 + log((1+d)(1+D))) ≤ d`: the source's
`k (1 + log(1 + dD)) ≤ d` is too weak for the dependency degree the argument establishes, and
fails at `k = 5, d = 21, D = 1`.

## Contributing

Work is published as issues labelled `choir/available`.  Claim one and submit a pull
request from a fork; every submission is verified by the gate before a human reviews it.
Ask the project's overseer for the joining prompt, which points your agent at the
contributor playbook.

## Layout

| Path | Contents |
|---|---|
| `Intro.lean` | §1.0 — large bipartite subgraph |
| `Ramsey.lean` | §1.1 — lower bounds to Ramsey numbers |
| `SetSystems.lean` | §1.2 — Bollobás' two families theorem |
| `PropertyB.lean` | §1.3 — 2-colourable hypergraphs |
| `ListColouring.lean` | §1.4 — list chromatic number of `K n n` |
| `Expectation.lean` | Ch. 2 — Szele, sum-free sets, Caro–Wei, Turán, sampling, unbalancing lights |
| `PolyLowerBound.lean` | §2.5 — the uniform lower bound on normalised polynomials |
| `ColourDiscrepancy.lean` | §2.5 — red/blue discrepancy in a `k`-partite colouring |
| `Alterations.lean` | Ch. 3 — Markov, dominating sets, Heilbronn, girth vs. chromatic number |
| `SecondMoment.lean` | Ch. 4 — the second-moment engine, thresholds, distinct sums |
| `Chernoff.lean` | Ch. 5 — the Chernoff bound, discrepancy, equiangular vectors, `K t`-subdivisions |
| `Subdivision.lean` | §5.3 — Hajós: no large clique subdivision in `G(n, 1/2)` |
| `LocalLemma.lean` | Ch. 6 — the local lemma, colourings, independent transversals, compactness |
| `Coloring.lean` | §6.2 — multicoloured translates (Erdős–Lovász) |
| `ArithProgressions.lean` | §6.2.11 — Beck: no long monochromatic arithmetic progression |
| `DirectedCycles.lean` | §6.4 — Alon–Linial: directed cycles of length divisible by `k` |
| `Lopsided.lean` | §6.5 — the lopsided local lemma |
| `Derangements.lean` | §6.5 — the derangement bound |
| `LatinTransversal.lean` | §6.5 — Erdős–Spencer: Latin transversals |
| `Sat.lean` | §6.6 — satisfiability of sparse `k`-CNF formulas |
| `Correlation.lean` | Ch. 7 — Harris–FKG |
| `MaxDegree.lean` | §7.2 — Harris applied to the degrees of `G(n, p)` |
| `Janson.lean` | Ch. 8 — Janson's inequalities |
| `Concentration.lean` | Ch. 9 — bounded differences, Azuma, Shamir–Spencer |
| `ChromaticConcentration.lean` | §9.3.4 — four-value concentration of the chromatic number |
| `HammingCube.lean` | §9.4 — neighbourhoods and compression in the Hamming cube (groundwork) |
| `Entropy.lean` | Ch. 10 — entropy, Brégman–Minc, Kahn–Zhao, Shearer |
| `Containers.lean` | Ch. 11 — graph and hypergraph containers |
