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

- ~~**`triangle_threshold`**~~ — **stated 2026-09-17**, in both halves:
  `prob_no_triangle_of_mul_le` (proved, #183) and `prob_triangle_of_le_mul` (#189), on the back of
  `triangleCount` and its two moments.  The note below is kept because its diagnosis was right —
  what §4.1 needed was a triangle count and a settled `whp` idiom, and both now exist.

- **Proposition 4.1.2 and Theorem 4.1.11 as originally scoped**: `1/n` is the threshold
  for `G(n,p)` to contain a triangle.  **Assessed 2026-09-15: §4.1's non-asymptotic content is
  already complete.**  Corollary 4.1.7 *is* the proved `prob_eq_zero_le_variance_div_sq`,
  Chebyshev (4.1.5) is upstream as `meas_ge_le_variance_div_sq`, and Definition 4.1.3 is
  Mathlib's `variance`.  Everything that remains in the section — 4.1.2, 4.1.8, 4.1.11 — is
  **asymptotic**, and needs two things the project does not have: a triangle-count random
  variable over `binomialRandom` (an orchestrator-authored definition) and a settled `whp`
  idiom.  The natural first nodes are then the two finite moment computations,
  `𝔼X = binom(n,3) p³` and the variance bound; those are publishable the moment the count
  exists.  **Both are stated and published as of 2026-09-17** — `integral_triangleCount` (#181)
  and `variance_triangleCount_le` (#182) — on the back of `triangleCount`, authored centrally.

  **`triangleCount` is written with `Set.indicator`, not a clique filter**, and that is forced:
  the measure ranges over *all* graphs on `Fin n`, where no `DecidableRel G.Adj` is available,
  and this project declares no `Decidable` instances.  The same expression is therefore both the
  random variable and, integrated, the expected count.  Sanity-checked before publishing — the
  empty graph on three vertices has count `0`.

  What remains for the threshold itself is the **`whp` idiom**, which is still unsettled and is
  the last blocker on §4.1, §4.2 and Theorem 11.1.5 alike.
- **`subgraph_threshold`** — Theorem 4.2.10 (Bollobás 1981): `n^{-1/m(H)}` is the
  threshold for containing a fixed `H`, where `m(H)` is the maximum edge-vertex ratio over
  subgraphs. Needs Definition 4.2.7 (`ρ`, `m`) as shared definitions first.
- **`clique_number`** — §4.4, the clique number of a random graph.
- **`hardy_ramanujan`** — §4.5. **Blocked on Mertens' theorem, which Mathlib does not have.**
  The earlier note here said the statement is expressible — `ArithmeticFunction.cardDistinctFactors`
  (`ω`) exists — and inferred that this section would therefore be the easiest of the chapter.
  That inference was wrong, and it is the trap worth naming: **expressible is not tractable.**
  Turán's second-moment proof needs `∑_{p ≤ n} 1/p = log log n + O(1)` to compute `𝔼X`, and a
  search of `Mathlib/NumberTheory/` finds no Mertens estimate in any form — no sum of prime
  reciprocals, no `log log` asymptotic. Supplying it is an analytic-number-theory project, not a
  task, so §4.5 stays unstated until Mathlib grows one. Theorem 4.5.3 (Erdős–Kac) is further out
  still, needing the method of moments on top.
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


## §4.3 Thresholds

`multiple_round_exposure` (Lemma 4.3.7) is **stated**, as
`prob_notMem_le_pow_of_isUpperSet`, task #152 — but it lives in `Correlation.lean`, not here.
It is a statement about `setBernoulli` and upper sets, which is that file's subject, and this
file has no random-subset machinery at all. Chapter boundaries in the roadmap do not have to
match file boundaries, and forcing them to would mean duplicating the Chapter 7 layer.

Stated with the general hypothesis `1 - (1-q)^m ≤ p` rather than the book's `q = p/m`: that is
what the argument needs (it says the union of `m` copies of `Ω_q` is dominated by `Ω_p`), it
avoids producing `p/m` as an element of `unitInterval`, and `q = p/m` is the special case by
Bernoulli. The direction was checked numerically for `m ≤ 10` because it inverts easily —
the union's density is **at most** `p`, not at least.

Theorem 4.3.5 (monotonicity of `p ↦ ℙ(Ω_p ∈ F)`) is **also stated**, as
`prob_mem_mono_of_isUpperSet`, task #153 — requested by #152's contributor exactly as that
task's prose invited, rather than buried as a private `have`. It is stated **non-strictly**: the
book says strictly increasing, which needs `F` non-trivial, but strictness is used nowhere
downstream and dropping non-triviality makes it applicable with no side conditions. A strict
version, if ever wanted, belongs in its own node.

**Still unstated in §4.3:** Theorem 4.3.6 (Bollobás–Thomason) itself, which is asymptotic and
needs the `ε`–`N` idiom, plus Examples 4.3.8/4.3.9 which are asymptotic statements about
`G(n,p)`.
