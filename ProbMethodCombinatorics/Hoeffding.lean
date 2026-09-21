import Mathlib.Probability.Moments.SubGaussian

/-!
# Section 5.0: Chernoff's bound for bounded independent summands

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 5.0.5.

`Chernoff.lean` proves the uniform sign case — `∑ εᵢ` with `εᵢ` uniform on `{-1, 1}` — by a
direct moment-generating-function argument over `Finset`s, and Chapter 5's applications run on
it.  Theorem 5.0.5 is the general statement: the summands need only be independent, bounded in
`[-1, 1]` and centred, and the conclusion is the same `exp (-λ² / 2)` with the same constant.

Mathlib's sub-Gaussian API supplies both halves.  A variable a.s. in `[a, b]` with mean zero has
`HasSubgaussianMGF` with parameter `(‖b - a‖₊ / 2) ^ 2`, which at `[-1, 1]` is `1`; Hoeffding's
inequality for a sum of independent sub-Gaussian variables then gives
`exp (-ε ^ 2 / (2 * ∑ cᵢ))`, and at `ε = λ √#s` with every `cᵢ = 1` the exponent is exactly
`-λ² / 2`.  No slack is lost, so this is the source's constant and not a weakening of it.

This statement is measure-theoretic where the rest of Chapter 5 is finite averaging.  That is
deliberate: the general form is about independence, which is a statement about a measure, and
re-deriving Mathlib's sub-Gaussian machinery over `Finset`s would be strictly worse.  It lives
in its own file for that reason.
-/

namespace ProbMethodCombinatorics

open MeasureTheory ProbabilityTheory

/-- **Theorem 5.0.5.**  For independent `Xᵢ`, each almost surely in `[-1, 1]` with mean zero,
`ℙ(∑ Xᵢ ≥ λ √n) ≤ exp (-λ² / 2)`, where `n` is the number of summands.

`s.Nonempty` is load-bearing rather than cosmetic: over an empty index set the sum is `0`, the
threshold `λ √0` is `0`, and the left side is `1` while the right side is `exp (-λ² / 2) < 1`
for every `λ > 0`. -/
theorem measure_sum_ge_le_of_mem_Icc {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty)
    (hindep : iIndepFun X μ) (hmeas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hbdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    μ.real {ω | lam * Real.sqrt s.card ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-lam ^ 2 / 2) := by
  sorry

end ProbMethodCombinatorics
