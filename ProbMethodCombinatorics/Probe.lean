import ProbMethodCombinatorics.Chernoff
open Finset ProbMethodCombinatorics

/-- At `n = 0` the statement of `card_filter_le_exp_mul` is false for `lam = 1`. -/
example : ¬ ((((univ : Finset (Fin 0 → Bool)).filter
      fun x => (1:ℝ) * Real.sqrt ((0:ℕ):ℝ) ≤ ∑ i, toSign (x i)).card : ℝ)
    ≤ Real.exp (-(1:ℝ) ^ 2 / 2) * 2 ^ (0:ℕ)) := by
  have hfilter : ((univ : Finset (Fin 0 → Bool)).filter
      fun x => (1:ℝ) * Real.sqrt ((0:ℕ):ℝ) ≤ ∑ i, toSign (x i)) = univ := by
    apply Finset.filter_true_of_mem
    intro x _
    simp
  have hcard : ((univ : Finset (Fin 0 → Bool)).card : ℝ) = 1 := by
    simp [Finset.card_univ]
  rw [hfilter, hcard]
  have h1 : Real.exp (-(1:ℝ) ^ 2 / 2) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  simp only [pow_zero, mul_one]
  linarith

/-- The published theorem itself, instantiated, is therefore unprovable. -/
#check @card_filter_le_exp_mul
