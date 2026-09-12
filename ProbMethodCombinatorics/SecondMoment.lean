import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

/-!
# Chapter 4: Second Moment

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 4.

The chapter's headline results are asymptotic statements about `G(n, p)` — thresholds, the
clique number, Hardy–Ramanujan.  Stated here is the chapter's *engine*: the two finite
inequalities every one of those arguments runs on.  Chebyshev's inequality itself is
Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq`, and the Weierstrass approximation
theorem of §4.7 is Mathlib's `polynomialFunctions_closure_eq_top`; neither is restated.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Chebyshev bound on the probability of non-existence** (Zhao, Corollary 4.1.7): for any
random variable `X`, `ℙ(X = 0) ≤ Var X / (𝔼 X) ^ 2`.

This is the form in which the second moment method is always applied: a random variable whose
variance is small compared to the square of its mean is positive with high probability. -/
theorem prob_eq_zero_le_variance_div_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (hmean : μ[X] ≠ 0) :
    (μ {ω | X ω = 0}).toReal ≤ Var[X; μ] / μ[X] ^ 2 := by
  sorry

/-- **The second moment variance bound for sums of indicators** (Zhao, Setup 4.2.2 and the
display preceding Lemma 4.2.4): if `X` counts how many of the events `A i` occur, and `D`
contains every ordered pair of distinct indices whose events are dependent, then

    Var X ≤ 𝔼 X + ∑ (i, j) ∈ D, ℙ(A i ∩ A j).

The dependency set `D` is a parameter rather than something computed from `A`, because
independence is not decidable; a caller supplies whichever `D` its application makes convenient. -/
theorem variance_sum_indicator_le [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (D : Finset (ι × ι))
    (hD : ∀ i j, i ≠ j → (i, j) ∉ D → IndepSet (A i) (A j) μ) :
    Var[fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω; μ]
      ≤ (∑ i, (μ (A i)).toReal) + ∑ q ∈ D, (μ (A q.1 ∩ A q.2)).toReal := by
  sorry

end ProbMethodCombinatorics
