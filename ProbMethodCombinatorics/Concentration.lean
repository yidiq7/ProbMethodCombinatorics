import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Chapter 9: Concentration of Measure

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 9.

The chapter's slogan: **a Lipschitz function of many independent random variables is
concentrated.**  Chapter 5's Chernoff bound is the special case where the function is a sum.

Mathlib already has the analytic engine — `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
is Hoeffding's lemma (Lemma 9.2.12), and `measure_sum_ge_le_of_iIndepFun` is Hoeffding's
inequality for sums of independent sub-Gaussian variables.  What it does not have is Azuma's
inequality or the bounded differences inequality, and the latter is what the applications use.

Only the bounded differences inequality is stated here; the rest of the chapter is planned.
-/

namespace ProbMethodCombinatorics

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The bounded differences inequality** (Zhao, Theorem 9.1.3; also McDiarmid's inequality and
the Azuma–Hoeffding inequality).  If changing the `i`-th coordinate alone moves `f` by at most
`c i`, then `f` of independent coordinates is concentrated about its mean:

    ℙ(f - 𝔼f ≥ λ) ≤ exp(-2λ² / ∑ᵢ cᵢ²).

Taking `f` to be a sum recovers the Chernoff bound of Chapter 5, so this is a genuine
generalisation: the window of fluctuation has length `O(√n)` for any `1`-Lipschitz `f`, whether
or not it is a sum.

The source proves it from Azuma's inequality applied to the Doob martingale of `f`
(Theorems 9.2.8 and 9.2.9), whose engine is Hoeffding's lemma — already in Mathlib as
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`.

`f` is assumed measurable, and the assumption is not cosmetic: the bounded differences
condition alone does not give it, a Mathlib measure of a non-measurable set is its *outer*
measure, and `∫` of a non-integrable function is junk `0`.  Without `hf` a non-measurable `f`
with range of diameter `c₀` makes the left-hand side `1` and the statement false.  Measurable
and bounded-differences together do give integrability, so no separate hypothesis is needed for
the `∫`. -/
theorem measure_sub_integral_ge_le {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hf : Measurable f)
    (hc : ∀ i (x y : ∀ i, Ω i), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i)
    (hsum : 0 < ∑ i, c i ^ 2) {lam : ℝ} (hlam : 0 ≤ lam) :
    (Measure.pi μ {x | lam ≤ f x - ∫ y, f y ∂(Measure.pi μ)}).toReal
      ≤ Real.exp (-2 * lam ^ 2 / ∑ i, c i ^ 2) := by
  sorry

end ProbMethodCombinatorics
