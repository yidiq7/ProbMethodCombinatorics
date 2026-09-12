# Group: `expectation` — Chapter 2

What the chapter establishes: linearity of expectation as a tool — compute the average of
a statistic over a family of objects, then take an object at least as good as the average.
No independence is needed anywhere in it, which is exactly why the finite-averaging
formalization works.

Two of the chapter's six sections are stated so far.  §2.2 (large sum-free subsets),
§2.4 (sampling bounds for the hypergraph Turán problem), §2.5 (unbalancing lights) and
§2.6 (the crossing number inequality) are planned but unstated; §2.5 and §2.6 need
analytic input (a central limit estimate, Euler's formula) that the project does not yet
have.

## `hamilton_paths` — `ProbMethodCombinatorics.hamiltonPaths`

The Hamilton paths of a tournament `T : Fin n → Fin n → Bool`, as the orderings
`σ 0, σ 1, …, σ (n-1)` of the vertices in which each vertex beats its successor —
`univ.filter fun σ => ((List.finRange n).map σ).IsChain fun a b => T a b = true`.

Mathlib has no tournaments.  Representing one as a `Bool`-valued relation, and a Hamilton
path as a permutation rather than a `SimpleGraph.Walk`, keeps the count a plain
`Finset.card` and its decidability automatic (`List.IsChain` has a `Decidable` instance).

## `szele` — `exists_tournament_card_hamiltonPaths`

Theorem 2.1.2 (Szele 1943), the first use of the probabilistic method: some `n`-vertex
tournament has at least `n! / 2 ^ (n - 1)` Hamilton paths.

Orient each edge independently; each of the `n!` orderings is a Hamilton path with
probability `2 ^ -(n-1)`, so the expected count is `n! / 2 ^ (n-1)`.  Formalized, this is
an average over the `2 ^ (n.choose 2)` tournaments, so the work is a double count of
pairs `(T, σ)` with `σ` a Hamilton path of `T`.

## `caro_wei` — `exists_isIndepSet_caro_wei`

Theorem 2.3.2 (Caro 1979, Wei 1981).  Every graph has an independent set of size at least
`∑ v, 1 / (d v + 1)`.

The book takes a uniform random vertex ordering and keeps each vertex that precedes all of
its neighbours; `v` survives with probability `1 / (d v + 1)`.  Formalized: average the
size of that set over all `n!` orderings.  Mathlib supplies `SimpleGraph.IsIndepSet` and
`SimpleGraph.degree`, but nothing resembling the bound itself.

Remark 2.3.4's greedy derandomization — repeatedly remove a minimum-degree vertex and its
neighbourhood — is an alternative route that avoids averaging entirely, and may well be
the shorter formalization.

## `turan_edge_bound` — `card_edgeFinset_le_of_cliqueFree`

Theorem 2.3.6 (Turán 1941), edge-count form: an `n`-vertex `K (r+1)`-free graph has at
most `(1 - 1/r) · n² / 2` edges.

The book's route is Corollary 2.3.5 — Caro–Wei applied to the complement — plus convexity
of `x ↦ 1/(n - x)`.  Mathlib's `SimpleGraph.IsTuranMaximal` development proves the
stronger structural theorem (the extremal graph is the Turán graph) but never states this
bound, so either route is open: derive it from `caro_wei` as the book does, or count the
edges of `turanGraph n r` and quote Mathlib's extremal result.
