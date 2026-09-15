# Group: `second-moment` — Chapter 4

What the chapter establishes: the second moment method — a random variable whose variance
is small relative to the square of its mean is concentrated, hence positive.

**Only the chapter's engine is stated.** Its headline results are asymptotic — thresholds
for `G(n,p)`, the clique number, Hardy–Ramanujan — and every one of them is a statement
about a *sequence* of random graphs with `o(1)` error. Stating those well needs both a
worked `G(n,p)` API and a settled convention for "whp"; stating them badly would publish
tasks nobody can close. So the two finite inequalities everything runs on are stated now,
and the asymptotic nodes stay `planned` until the engine exists.

**Already upstream, not tasks:**
- Chebyshev's inequality (Theorem 4.1.5) — `ProbabilityTheory.meas_ge_le_variance_div_sq`.
- Variance and covariance (Definition 4.1.3) — `ProbabilityTheory.variance`,
  `ProbabilityTheory.covariance`, with `Var[X; μ]` notation.
- The Weierstrass approximation theorem (§4.7) — `polynomialFunctions_closure_eq_top`.
- The binomial random graph `G(V, p)` itself — `SimpleGraph.binomialRandom`, with
  `G(V, p)` notation and an `IsProbabilityMeasure` instance, in
  `Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`. Note this is a
  recent and **very thin** file: essentially the definition, the two degenerate cases
  `p = 0` and `p = 1`, and the singleton probability. Anything else about `G(n,p)` this
  project needs, it must build.

## `prob_zero_bound` — `prob_eq_zero_le_variance_div_sq`

Corollary 4.1.7: `ℙ(X = 0) ≤ Var X / (𝔼 X)²`.

The form in which the method is always applied. Follows from Chebyshev with `c = |𝔼 X|`,
since `X = 0` implies `|X - 𝔼X| ≥ |𝔼X|`. Short, given Mathlib's Chebyshev — this is the
group's entry point.

## `variance_indicator_bound` — `variance_sum_indicator_le`

Setup 4.2.2 and the display before Lemma 4.2.4: if `X` counts how many of the events `A i`
occur and `D` lists the dependent ordered pairs, then

    Var X ≤ 𝔼 X + ∑ (i,j) ∈ D, ℙ(A i ∩ A j).

The dependency set `D` is a parameter rather than something derived from `A`, because
independence is not decidable and the project may not introduce `Classical` helpers; every
application knows its own dependency structure anyway.

This is what turns a covariance computation into a usable bound, and it is the step every
threshold argument in §4.2 reuses. Proof: expand `Var X = ∑_{i,j} Cov[X i, X j]`, kill the
independent off-diagonal terms with `IndepSet`, bound the diagonal by `𝔼 X` (indicators are
idempotent, so `Var X i ≤ 𝔼 X i`), and bound each remaining term by `ℙ(A i ∩ A j)`.
`ProbabilityTheory.covariance` and the bilinearity lemmas around it are the relevant API.

## Planned, not stated

- **`triangle_threshold`** — Proposition 4.1.2 and Theorem 4.1.11: `1/n` is the threshold
  for `G(n,p)` to contain a triangle. Needs a triangle-count random variable over
  `G(Fin n, p)` and its first two moments; that count and its expectation are the natural
  next nodes once `variance_indicator_bound` lands.
- **`subgraph_threshold`** — Theorem 4.2.10 (Bollobás 1981): `n^{-1/m(H)}` is the
  threshold for containing a fixed `H`, where `m(H)` is the maximum edge-vertex ratio over
  subgraphs. Needs Definition 4.2.7 (`ρ`, `m`) as shared definitions first.
- **`clique_number`** — §4.4, the clique number of a random graph.
- **`hardy_ramanujan`** — §4.5. Mathlib has `ArithmeticFunction.cardDistinctFactors` (`ω`),
  so the statement is expressible; Turán's second-moment proof is the route. This is the
  one section of the chapter that needs no random graphs at all and may well be stated
  before the others.
- ~~**`distinct_sums`**~~ — **stated 2026-09-15** as `le_card_of_distinctSubsetSums`, task #151.
  See §4.6 below.


## §4.6 Distinct sums

`distinct_sums` (Theorem 4.6.3) is stated: `3 · 2^k ≤ 8 √k · n` whenever a `k`-element subset of
`[n]` has all `2^k` subset sums distinct. It was the first of the chapter's applications to be
stated because it is the only one needing **no random graphs at all** — the randomness is a
uniform sign vector — and because it comes with an explicit constant, so no `o(1)` idiom is
required.

It is also the chapter's best advertisement for its own method: the pigeonhole bound
`n ≥ 2^k/k` has to account for every subset sum, while the second moment lets you discard the
outliers Chebyshev says are rare, buying a factor of `√k`.

Verified against the known minimal witnesses for `k ≤ 8` — the Conway–Guy sequence
`1, 2, 4, 7, 13, 24, 44, 84` — before publication. The bound is comfortably slack at small `k`
(at `k = 3` it forces only `n ≥ 2` where the truth is `4`).

`hk : 0 < k` is load-bearing: at `k = 0` the claim reads `3 ≤ 0`.

**Deliberately not stated.** Conjecture 4.6.2 (`n ≳ 2^k`, Erdős's \$300 problem) is **open
mathematics**. Theorem 4.6.6 (Dubroff–Fox–Xu) improves the constant via Harper's
vertex-isoperimetric inequality and is a separate, harder node.
