# Group: `correlation` — Chapter 7

What the chapter establishes: **increasing events of independent variables are positively
correlated.** The slogan does the work in Chapter 8, where the matching upper bounds come from
Janson's inequality.

## Already upstream, not tasks

- **`IsUpperSet.le_card_inter_finset`** (`Mathlib/Combinatorics/SetFamily/HarrisKleitman.lean`)
  — Harris–Kleitman: for up-sets `𝒜, ℬ` of `Finset α`,
  `#𝒜 * #ℬ ≤ 2 ^ |α| * #(𝒜 ∩ ℬ)`. This is Theorem 7.1.1 for the **uniform** measure, in
  counting form, together with the mixed and lower-set variants.
- **`fkg`** (`Mathlib/Combinatorics/SetFamily/FourFunctions.lean`) — the
  Fortuin–Kasteleyn–Ginibre inequality for a log-supermodular measure on a distributive
  lattice, with `holley` and the four functions theorem beside it.

So the *uniform* case of this chapter is done. What is missing is the case the applications
need: an arbitrary edge probability.

## `harris_binomial` — `binomialRandom_mul_le_inter`

Theorem 7.1.1 for `G(V, p)`: two increasing graph properties are positively correlated.
`SimpleGraph V` is a `CompleteAtomicBooleanAlgebra`, so `IsUpperSet` applies directly, and
`SimpleGraph.binomialRandom` is Mathlib's `G(V, p)`.

**Proved (PR #80) by reduction to `fkg`.** The step that makes it work: `G(V, p)` is not
merely log-*super*modular but log-**modular**. `binomialRandom_singleton` gives each graph mass
`p^|E(G)| · σp^(C(n,2) - |E(G)|)`, and `|E(a ⊓ b)| + |E(a ⊔ b)| = |E(a)| + |E(b)|` by
inclusion–exclusion on edge sets, so `fkg`'s hypothesis holds with equality.

The PR also settles a question left open when the task was written: **every set of graphs is
measurable for a `Fintype V`.** `MeasurableSingletonClass (SimpleGraph V)` follows from
`measurable_adj`, so the `MeasurableSet` hypotheses on this statement are redundant — callers
can discharge them with `measurableSet_discrete` or similar. They are left in place rather than
churned, but a future golf could drop them.

The content beyond upstream is precisely that `p` is arbitrary — Harris–Kleitman is the
`p = 1/2` case. The natural route is to transport the four functions theorem along
`SimpleGraph.edgeSet`, whose measurable-embedding property Mathlib already provides
(`measurableEmbedding_edgeSet`), turning the statement into one about a product of Bernoulli
measures on edge indicators.

## `harris_lower_family` — `prod_le_binomialRandom_iInter`

Corollary 7.1.6 in the form the applications use: finitely many *decreasing* properties, all
holding, with probability at least the product. Follows from the pairwise increasing case by
complementation and induction on the family — the induction is the real work, since each step
must re-establish that a finite intersection of lower sets is a lower set.

## `triangle_free_lower` — `le_binomialRandom_cliqueFree_three`

Theorem 7.2.2: `ℙ(G(n,p) triangle-free) ≥ (1 - p³)^{n choose 3}`.

For each triple, "does not span a triangle" is decreasing with probability exactly `1 - p³`;
the triples overlap, so independence fails, but `harris_lower_family` bounds the intersection
below by the product.

Remark 7.2.3 is worth knowing when judging this bound: it is the better of the two easy lower
bounds only when `p ≪ n^{-1/2}`; for larger `p` the bound
`ℙ(triangle-free) ≥ ℙ(empty) = (1-p)^{n choose 2}` wins. **Chapter 8 supplies the matching
upper bounds**, which is the point of the pairing.

## Not stated

**Theorem 7.1.5**, the monotone-*function* form `𝔼[fg] ≥ 𝔼[f]𝔼[g]`, which implies the event
form by taking indicators. Stating it needs a product measure over arbitrary linearly ordered
factors and integrability side conditions; the event form covers every application in the
book, so this waits until something needs it.

**Theorem 7.2.5** (Riordan–Selby, `ℙ(maxdeg G(n,1/2) ≤ n/2) = (0.6102… + o(1))ⁿ`) and
**Proposition 7.2.6** are not stated: the first is quoted without proof in the source, and the
second needs Gaussian random variables and a Laplace-method estimate.
