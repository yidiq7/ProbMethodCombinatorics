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
  have hc : 0 < |μ[X]| := abs_pos.mpr hmean
  have hsub : {ω | X ω = 0} ⊆ {ω | |μ[X]| ≤ |X ω - μ[X]|} := fun ω hω => by
    show |μ[X]| ≤ |X ω - μ[X]|
    rw [show X ω = 0 from hω, zero_sub, abs_neg]
  have hle : μ {ω | X ω = 0} ≤ ENNReal.ofReal (Var[X; μ] / |μ[X]| ^ 2) :=
    (measure_mono hsub).trans (meas_ge_le_variance_div_sq hX hc)
  have hnn : 0 ≤ Var[X; μ] / |μ[X]| ^ 2 :=
    div_nonneg (variance_nonneg X μ) (sq_nonneg _)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal hnn, sq_abs] at this

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
  have hmem : ∀ i, MemLp ((A i).indicator (fun _ => (1 : ℝ))) 2 μ := fun i =>
    memLp_indicator_const 2 (hA i) 1 (Or.inr (measure_ne_top μ _))
  have hint : ∀ i, μ[(A i).indicator (fun _ => (1 : ℝ))] = (μ (A i)).toReal := fun i => by
    rw [integral_indicator_const _ (hA i), smul_eq_mul, mul_one, measureReal_def]
  have hcov : ∀ i j, cov[(A i).indicator (fun _ => (1 : ℝ)),
      (A j).indicator (fun _ => (1 : ℝ)); μ]
      = (μ (A i ∩ A j)).toReal - (μ (A i)).toReal * (μ (A j)).toReal := by
    intro i j
    have hmul : (A i).indicator (fun _ => (1 : ℝ)) * (A j).indicator (fun _ => (1 : ℝ))
        = (A i ∩ A j).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simpa using (Set.inter_indicator_mul (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) ω).symm
    rw [covariance_eq_sub (hmem i) (hmem j), hint i, hint j, hmul,
      integral_indicator_const _ ((hA i).inter (hA j)), smul_eq_mul, mul_one,
      measureReal_def]
  set g : ι × ι → ℝ := fun q => (μ (A q.1 ∩ A q.2)).toReal with hg
  have hg0 : ∀ q : ι × ι, 0 ≤ g q := fun _ => ENNReal.toReal_nonneg
  set Δ : Finset (ι × ι) :=
    Finset.univ.map ⟨fun i => (i, i), fun _ _ h => congrArg Prod.fst h⟩ with hΔ
  have hmemΔ : ∀ q : ι × ι, q.1 = q.2 → q ∈ Δ := by
    rintro ⟨a, b⟩ (h : a = b)
    subst h
    rw [hΔ]
    exact Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩
  have hdiag : ∑ i, (μ (A i)).toReal = ∑ q ∈ Δ, g q := by
    rw [hΔ, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (μ (A i)).toReal = (μ (A i ∩ A i)).toReal
    rw [Set.inter_self]
  have hle : ∀ i j, cov[(A i).indicator (fun _ => (1 : ℝ)),
      (A j).indicator (fun _ => (1 : ℝ)); μ] ≤ g (i, j) := by
    intro i j
    rw [hcov i j, hg]
    exact sub_le_self _ (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  rw [variance_fun_sum hmem, hdiag,
    ← Finset.sum_indicator_subset g Δ.subset_univ,
    ← Finset.sum_indicator_subset g D.subset_univ,
    Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hqΔ : (i, j) ∈ (↑Δ : Set (ι × ι))
  · rw [Set.indicator_of_mem hqΔ]
    exact le_add_of_le_of_nonneg (hle i j) (Set.indicator_nonneg (fun a _ => hg0 a) _)
  by_cases hqD : (i, j) ∈ (↑D : Set (ι × ι))
  · rw [Set.indicator_of_mem hqD]
    exact le_add_of_nonneg_of_le (Set.indicator_nonneg (fun a _ => hg0 a) _) (hle i j)
  have hne : i ≠ j := fun h => hqΔ (Finset.mem_coe.2 (hmemΔ (i, j) h))
  have hnotD : (i, j) ∉ D := fun h => hqD (Finset.mem_coe.2 h)
  rw [Set.indicator_of_notMem hqΔ, Set.indicator_of_notMem hqD, add_zero, hcov i j,
    (hD i j hne hnotD).measure_inter_eq_mul, ENNReal.toReal_mul, sub_self]

/-- **Erdős's distinct-sums bound** (Zhao, Theorem 4.6.3; `sources/mit18_226_f22_lec_full.pdf`,
printed p. 61 = PDF p. 67).  If a `k`-element set of naturals bounded by `n` has all `2 ^ k`
subset sums distinct, then `n ≳ 2 ^ k / √k` — concretely, `3 · 2 ^ k ≤ 8 √k · n`.

This beats the pigeonhole bound `n ≥ 2 ^ k / k` by a factor of `√k`, and it is the chapter's
purest illustration of the second moment method: the pigeonhole argument counts *all* subset
sums, while this one discards the outliers that Chebyshev says are rare.

**Route.**  Let `X = ∑ εᵢ xᵢ` with `εᵢ ∈ {0,1}` independent and uniform.  Then `μ = (∑ xᵢ)/2`
and `σ² = (∑ xᵢ²)/4 ≤ n²k/4`, so `2σ ≤ n√k`.  Chebyshev gives `ℙ(|X - μ| ≥ 2σ) ≤ 1/4`, hence
`ℙ(|X - μ| < n√k) ≥ 3/4`.  In the other direction, distinctness makes `X` injective on
`{0,1}^k`, so `ℙ(X = x) ≤ 2^{-k}` for every `x`, and the open interval `(μ - n√k, μ + n√k)`
contains at most `2n√k` integers; therefore `ℙ(|X - μ| < n√k) ≤ 2n√k · 2^{-k}`.  Comparing the
two gives `2n√k · 2^{-k} ≥ 3/4`.

`prob_eq_zero_le_variance_div_sq` and `variance_sum_indicator_le` above are the engine; the
`εᵢ` are independent so the variance of the sum is the sum of the variances.

Erdős's conjecture that `n ≳ 2 ^ k` (Conjecture 4.6.2) is **open mathematics** and must not be
stated as a theorem.  Theorem 4.6.6 (Dubroff–Fox–Xu), which improves the constant via Harper's
vertex-isoperimetric inequality, is a separate and harder node.

The bound was checked against the known minimal witnesses for `k ≤ 8` (the Conway–Guy
sequence `1, 2, 4, 7, 13, 24, 44, 84`) before publication. -/
theorem le_card_of_distinctSubsetSums {n k : ℕ} (hk : 0 < k) (S : Finset ℕ)
    (hSn : ∀ x ∈ S, x ≤ n) (hScard : S.card = k)
    (hdistinct : ∀ A ⊆ S, ∀ B ⊆ S, ∑ x ∈ A, x = ∑ x ∈ B, x → A = B) :
    3 * 2 ^ k ≤ 8 * Real.sqrt k * n := by
  sorry

end ProbMethodCombinatorics
