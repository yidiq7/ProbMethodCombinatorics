# Group: `janson` — Chapter 8

What the chapter establishes: exponential bounds on the probability that a random subset
contains **none** of a prescribed family of sets, and on the lower tail of the count. Where the
second moment method (Chapter 4) gives polynomial decay, these give exponential decay — which
is what makes the chromatic-number application of §8.3 possible.

**Nothing in this chapter is in Mathlib.**

## Setup

Setup 8.1.1 throughout: `R` is a random subset of `ι`, each element kept independently with
probability `p`. That is Mathlib's `setBernoulli`, which already carries an
`IsProbabilityMeasure` instance and is the same primitive `SimpleGraph.binomialRandom` is built
from — so Chapters 7 and 8 sit on a common foundation.

Three definitions are authored here rather than inlined, because all three theorems share them
and a task's statement mentioning them makes them interface:

- `jansonMu p S` — `μ = ∑ ℙ(S i ⊆ R)`;
- `jansonDelta p S D` — `Δ = ∑_{(i,j) ∈ D} ℙ(S i ∪ S j ⊆ R)`;
- `jansonCount S R` — the random variable `X`, as `Set.ncard {i | S i ⊆ R}`. Not a
  `Finset.filter`: set inclusion on `Set ι` is undecidable and the project does not add
  `Decidable` instances.

**`D` is a parameter, not derived from `S`** — the same decision as `variance_sum_indicator_le`
in Chapter 4, and for the same reason. The hypothesis constrains only pairs *outside* `D`
(they must be disjoint, hence independent), so any `D` containing every dependent ordered pair
is admissible and a larger `D` merely weakens the bound. Note the book counts `(i,j)` and
`(j,i)` separately in `Δ`.

## `janson_one` — `janson_prob_none_le`

Theorem 8.1.2: `ℙ(X = 0) ≤ exp(-μ + Δ/2)`.

Useful when `Δ = o(μ)`. Remark 8.1.3 is the reason this chapter is paired with Chapter 7:
Harris' inequality gives the matching *lower* bound `exp(-(1+o(1))μ)` in the same regime, so
the two together determine the probability rather than merely bounding it.

The proof conditions the events one at a time and bounds each conditional probability below by
`ℙ(A i) - ∑_{j < i, j ~ i} ℙ(A i A j)`; that step is itself an application of Harris'
inequality (Corollary 7.1.6), so **`janson_one` genuinely depends on Chapter 7**.

## `janson_two` — `janson_prob_none_le_of_mu_le`

Theorem 8.1.8: when `Δ ≥ μ`, `ℙ(X = 0) ≤ exp(-μ²/(2Δ))`.

Covers the regime where the first inequality says nothing. Proved *from* the first by applying
it to a random subsample of the events — include each index with probability `q`, note
`𝔼μ_T = qμ` and `𝔼Δ_T = q²Δ`, and optimise at `q = μ/Δ ∈ [0,1]`.

## `janson_three` — `janson_lower_tail`

Theorem 8.2.2: for `0 ≤ t ≤ μ`, `ℙ(X ≤ μ - t) ≤ exp(-t²/(2(μ+Δ)))`.

The strongest of the three — taking `t = μ` recovers the other two up to a constant in the
exponent. The proof is a moment-generating-function argument in the style of the Chernoff
bound, using the first inequality on an auxiliary family.

**There is deliberately no upper-tail companion.** Example 8.2.4 shows the analogous bound is
*false*: planting a clique of size `Θ(np)` forces an excess of triangles with probability
`p^{Θ(n²p²)}`, far above `exp(-Θ(n²p))`. Anyone tempted to state the symmetric version should
read that example first.

## Not stated

The asymptotic consequences — Theorem 8.1.6, Corollary 8.1.7, Theorem 8.1.10 (the two-regime
triangle-free estimate), Theorem 8.2.5 (Harel–Mousset–Samotij) and §8.3's chromatic number of
`G(n,1/2)` (Theorem 8.3.2, Bollobás) — are planned rather than stated, for the same reason as
Chapter 4's: they are statements about sequences with `o(1)` error, and they need a settled
`whp` convention plus a worked `G(n,p)` API. Theorem 8.3.2 additionally needs Lemma 8.3.3 and
the iterated-extraction colouring argument, which is a substantial development of its own.
