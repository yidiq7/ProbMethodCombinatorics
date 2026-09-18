# Group: `expectation` — Chapter 2

What the chapter establishes: linearity of expectation as a tool — compute the average of
a statistic over a family of objects, then take an object at least as good as the average.
No independence is needed anywhere in it, which is exactly why the finite-averaging
formalization works.

Five of the chapter's six sections are stated as of 2026-09-17; only §2.6 remains, and it has a
**named blocker** rather than merely being pending.  The per-section notes below record how each
blocker was assessed — several turned out to be wrong on inspection, which is why they are kept.

- **§2.2 (large sum-free subsets)** — blocked twice over.  Mathlib has no `IsSumFree`
  (`ThreeAPFree` is a different notion — three-term progressions, not sums), so the predicate
  would have to be authored here; and Erdős's proof needs a prime `p ≡ 2 (mod 3)` above the
  largest element, which needs primes in an arithmetic progression.  `PrimesCongruentOne.lean`
  covers only `≡ 1 mod k`, and Mathlib has no Dirichlet theorem.
- **§2.4 (sampling bounds for the hypergraph Turán problem)** — **assessed and stated
  2026-09-15** as `card_le_of_tetrahedronFree` (Proposition 2.4.2).  Fully tractable: finite,
  entirely in `ℕ`, a self-contained double count, no missing Mathlib input.  Tight at `n = 4`.
  Lemma 2.4.3 and the five-vertex refinement are **both proved 2026-09-17** —
  `card_le_seven_of_tetrahedronFree` (#196) and `card_le_of_tetrahedronFree_sample_five` (#202),
  the latter published only once the former had landed rather than against a `sorry`.  **§2.4 is
  complete.**  Question 2.4.1
  itself is a **notorious open problem** and must never be stated.
- **§2.5 (unbalancing lights)** — **stated 2026-09-15** as `exists_signs_sum_ge`.  My earlier
  note here ("needs a central limit estimate") was wrong twice over: Mathlib *does* have a CLT
  (`Probability/CentralLimitTheorem.lean`), and the book itself gives an **exact** binomial
  identity for `𝔼|Sₙ|` that avoids the CLT entirely.  Stated exactly, therefore, with no `o(1)`
  — strictly stronger than the book's `(√(2/π) + o(1)) n^{3/2}`.  Theorem 2.5.2 remains
  unstated and is harder (a compactness argument for the parameters).
- **§2.6 (the crossing number inequality)** — needs Euler's formula for planar graphs.

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


## §2.4 Bounding by sampling

`sampling_bound` (Proposition 2.4.2) is stated: `4 |H| ≤ 3 binom(n,3)` for a tetrahedron-free
3-graph on `n ≥ 4` vertices.  Kept entirely in `ℕ` rather than carrying the `3/4`.

Done as a **double count** rather than as expectation over a sampled 4-set, which is the same
argument and avoids introducing a probability space for a finite average — Chapter 2's standing
convention.  The identity that closes it is `4 binom(n,4) = binom(n,3) (n-3)`.

Verified tight at `n = 4`, and brute force at `n = 5` reproduces Zhao's Lemma 2.4.3 (maximum 7)
exactly — a useful cross-check that the encoding of "tetrahedron-free" is the intended one.

**Proposition 2.4.4 needs `5 ≤ n`; the source prints `n ≥ 4`, and at `n = 4` it is false.**
The 3-graph on four vertices missing exactly one triple is tetrahedron-free — the only 4-set is
`univ`, and it is not covered — and has `3` edges, while `(7/10) binom(4,3) = 2.8`.  An argument
that samples five vertices cannot say anything about four, so the printed hypothesis is simply
one too weak.  Exhaustive search over all 3-graphs on `n ≤ 6` vertices gives true maxima
`3, 7, 14` at `n = 4, 5, 6`, against `(7/10) binom(n,3) = 2.8, 7, 14`: false at `4`, and tight at
both `5` and `6`.  `card_le_of_tetrahedronFree_sample_five` is stated with `5 ≤ n` accordingly.

This is the second source erratum this project has had to repair, after the `≤`/`<` in §6.3.
Both were found the same way — **compute the small cases before stating the theorem** — and
neither would have been caught by reading the proof, because in both the proof is correct and
only the quantifier range is wrong.


## §2.5 Unbalancing lights

`unbalancing_lights` is stated **exactly**: `∑ᵢⱼ aᵢⱼ xᵢ yⱼ ≥ n² binom(n-1,⌊(n-1)/2⌋) / 2^{n-1}`.

The section had been recorded as blocked on a central limit estimate.  That was wrong on both
counts — Mathlib has a CLT, and the book notes an exact closed form for `𝔼|Sₙ|` which makes the
CLT unnecessary.  **An exact statement is better than an asymptotic one whenever the source
offers the identity**: it needs no `ε`–`N` idiom, it is strictly stronger, and it can be checked
numerically.

Verified before publication: the identity against the direct sum for `n ≤ 14`, and the claim by
brute force over *all* `±1` matrices for `n ≤ 3`.  **Tight at `n = 1, 2`**, so no
constant-losing proof will do.

The interesting feature for a reader is that the `Rᵢ = ∑ⱼ aᵢⱼ yⱼ` are **not independent** of one
another and the proof does not need them to be — only each marginal matters.  The task prose says
so explicitly, because it is the natural thing to go looking for and it is false.
