# Group: `chernoff` — Chapter 5

What the chapter establishes: exponential tail bounds for sums of independent bounded
random variables, and two constructions that need them. Chebyshev (Chapter 4) gives
`ℙ(S ≥ λ√n) ≤ λ⁻²`; Chernoff gives `e^{-λ²/2}`, at the cost of full independence rather
than pairwise.

**Stated as counting, not as measure.** A uniform `±1` sequence is a function
`Fin n → Bool` read through `toSign`, and the bound is a count over the `2 ⁿ` sequences.
That is not a retreat from Chapter 4's convention but a fit to how the chapter is used:
§5.1 and §5.2 both end in existence statements about finite objects, and both proofs are
"Chernoff, then union bound over `m` sets", which is a count. A contributor who would
rather route through Mathlib's `ProbabilityTheory.HasSubgaussianMGF` may — the transfer
to the counting form is then part of the task.

## `to_sign` — `toSign`

`toSign b = if b then 1 else -1`. The `±1` reading of a Boolean, so that a sign sequence is
just a `Fin n → Bool` and `Finset.univ` over it has `2 ⁿ` elements.

## `chernoff` — `card_filter_le_exp_mul`

> **Corrected 2026-09-13: both Chernoff statements were false at `n = 0` and now carry
> `0 < n`.** At `n = 0` the empty sum is `0` and the threshold `λ √0` is `0`, so the single
> sign sequence meets the condition while the bound `exp(-λ²/2) · 2⁰` is strictly below `1`.
> Verified with a machine-checked counterexample before the statements were touched.  The
> proof needs the hypothesis anyway — it optimises at `t = λ / √n`.  Two workers claimed and
> released #21 without submitting, which is what prompted looking.

Theorem 5.0.1: `ℙ(S ≥ λ√n) ≤ exp(-λ²/2)` for `S` a sum of `n` uniform iid `±1`.

The chapter's engine, and its proof is the reason the chapter exists: bound the moment
generating function `𝔼[e^{tS}] = ((e^{-t} + e^{t})/2)ⁿ ≤ e^{t²n/2}` by comparing Taylor
series, apply Markov to `e^{tS}`, and optimize `t = λ/√n`. The Taylor comparison
`(e^{-x} + e^{x})/2 = ∑ x^{2k}/(2k)! ≤ ∑ x^{2k}/(k! 2^k) = e^{x²/2}` is the one genuinely
analytic step; `Real.cosh` and `Real.cosh_le_exp_half_sq`-shaped lemmas are worth searching
for before proving it by hand.

## `chernoff_abs` — `card_filter_abs_le_exp_mul`

Corollary 5.0.3, the two-sided bound `ℙ(|S| ≥ λ√n) ≤ 2 exp(-λ²/2)`. Immediate from the
one-sided bound and the sign-flipping involution `x ↦ !x` on `Fin n → Bool`, which is where
the counting formulation pays: the symmetry is a bijection of a `Finset`, not an argument
about distributions.

## `discrepancy` — `exists_toSign_abs_sum_le`

Theorem 5.1.1: any `m` subsets of `[n]` admit a `±1` colouring whose sum on every set is at
most `2√(n log m)` in absolute value.

Chernoff on each set (each is a sum of at most `n` signs) gives failure probability
`< 2/m²` per set; a union bound over `m` sets leaves a colouring that works. `hF : 2 ≤ F.card`
is needed both for `log` to be positive and for `1 - 2/m ≥ 0`.

Spencer's *six standard deviations suffice* (Theorem 5.1.3) removes the logarithm and is
**not** stated: its proof is a semirandom iterative construction with no Mathlib
counterpart, and it is not needed by anything downstream.

## `nearly_equiangular` — `exists_nearly_equiangular`

> **Corrected 2026-09-13: the statement now quantifies `∀ n ≥ n₀`.**  As first written it
> claimed the bound for *every* `n` and was false at the bottom.  At `n = 0` there is no unit
> vector in `EuclideanSpace ℝ (Fin 0)` while `2 ^ (c * 0) = 1` demands a non-empty `S`
> (machine-checked counterexample); at `n = 1` the only unit vectors are `±1` with inner
> product `-1`, so for small `ε` at most one qualifies while `2 ^ c > 1` demands two.  The
> book says "for every `n`", which is loose for an asymptotic statement.  This is the second
> statement in the project to be false at degenerate `n` — see the Chernoff bounds.

Theorem 5.2.1: for every `α ∈ (0,1)` and `ε > 0` there is `c > 0` with at least `2^{cn}` unit
vectors in `ℝⁿ` whose pairwise inner products lie in `[α - ε, α + ε]`.

Striking because the exactly-equiangular version allows at most `n + 1` vectors (a Gram
matrix rank argument, given in the same section) — relaxing equality to an `ε`-window buys
exponentially many. Proof: take `m = ⌈2^{cn}⌉` random vectors in `{-1,1}ⁿ` with `+1` biased
to probability `p = (1 + √α)/2`, so `𝔼[vᵢ · vⱼ] = (2p-1)² = α`; Chernoff plus a union bound
over the `m²` pairs. Normalize by `√n` at the end.

### `exists_large_sign_family` — many sign vectors with small pairwise correlation

Contributed with `nearly_equiangular` (PR #68): for `0 < β ≤ 1` there are at least
`exp(β² m / 2) / 4` vectors in `{±1}^m` whose pairwise correlations are all at most `β m` in
absolute value.  A greedy sphere-packing bound, from the two-sided Chernoff estimate.

**`β ≤ 1` is load-bearing, and the contributor flagged it rather than relying on it
silently.**  For `β > √(2 log 2) ≈ 1.177` the correlation condition holds for *every* pair —
the sum is at most `m` — so the family could be all `2^m` vectors, while `exp(β² m / 2)/4`
exceeds `2^m`.  The statement would be false there.

### Why the equiangular proof departs from the book

Zhao biases the random vectors (`+1` with probability `(1 + √α)/2`) so that
`𝔼[vᵢ · vⱼ] = α`, which needs a **biased** Chernoff bound; this project has only the uniform
one.  PR #68 instead freezes `k = ⌊α n⌋` coordinates at `+1` and lets the sign family choose
the remaining `m = n - k`: the frozen block supplies the mean `k/n ≈ α`, the free block stays
within `β`, and the uniform bound suffices.  Worth remembering — when the source's route needs
machinery the corpus lacks, moving the source of the bias is often cheaper than building it.

## Not stated

**§5.3, the Hajós conjecture counterexample** (Theorem 5.3.2: whp `G(n, 1/2)` has no
`K_t`-subdivision for `t = ⌈10√n⌉`). Two obstacles, either of which is larger than the
theorem: it is asymptotic in the same way Chapter 4's headline results are, and graph
*subdivisions* are not in Mathlib, so the statement needs a definition this project would
have to author and defend.

**Re-derived 2026-09-17: the first obstacle is gone, the second stands.**  Chapter 4's asymptotic
nodes *are* stated now and the `whp` idiom is settled, so "asymptotic in the same way" is no
longer a blocker.  But a fresh search of `Mathlib/Combinatorics/` finds **no graph subdivision
and no topological minor** — the only `IsMinor` is for matroids — so the definitional obstacle is
real.  Authoring `IsSubdivision` is possible but it is significant new vocabulary for one
theorem, and the `boxProd`-versus-tensor episode in §10.2 is the cautionary case: a plausible
wrong definition makes every downstream theorem true and useless.  Left unstated deliberately,
not for lack of checking.
