import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fintype.Pi

/-!
# Chapter 5: Chernoff Bound

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 5.

A uniform `±1` sequence is a function `Fin n → Bool`, read through `toSign`, and the Chernoff
bound is stated as a count over the `2 ^ n` such sequences.  This keeps the chapter's two
applications — discrepancy and nearly equiangular vectors — in the same finite-averaging
idiom as Chapters 1–3, and matches how the book uses the bound.
-/

namespace ProbMethodCombinatorics

open Finset

/-- The `±1` value of a Boolean: `true ↦ 1`, `false ↦ -1`. -/
def toSign (b : Bool) : ℝ := if b then 1 else -1

/-- **Chernoff bound** (Zhao, Theorem 5.0.1): for `S = X₁ + ⋯ + Xₙ` with the `Xᵢ` uniform iid
`±1`, `ℙ(S ≥ λ√n) ≤ exp (-λ² / 2)`, stated as a count over the `2 ^ n` sign sequences. -/
theorem card_filter_le_exp_mul (n : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    (((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt n ≤ ∑ i, toSign (x i)).card : ℝ)
      ≤ Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
  sorry

/-- **Two-sided Chernoff bound** (Zhao, Corollary 5.0.3): `ℙ(|S| ≥ λ√n) ≤ 2 exp (-λ² / 2)`. -/
theorem card_filter_abs_le_exp_mul (n : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    (((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|).card : ℝ)
      ≤ 2 * Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
  sorry

/-- **Discrepancy of a set system** (Zhao, Theorem 5.1.1): any `m` subsets of `[n]` admit a
`±1` assignment whose sum on every set is `O(√(n log m))` — here, at most `2 √(n log m)`. -/
theorem exists_toSign_abs_sum_le {n : ℕ} (F : Finset (Finset (Fin n))) (hF : 2 ≤ F.card) :
    ∃ x : Fin n → Bool, ∀ S ∈ F,
      |∑ i ∈ S, toSign (x i)| ≤ 2 * Real.sqrt (n * Real.log F.card) := by
  sorry

/-- **Exponentially many nearly equiangular vectors** (Zhao, Theorem 5.2.1): for every
`α ∈ (0, 1)` and `ε > 0` there is `c > 0` such that every `ℝⁿ` contains at least `2 ^ (c n)`
unit vectors whose pairwise inner products all lie in `[α - ε, α + ε]`.

Contrast the exactly-equiangular case, where at most `n + 1` vectors are possible. -/
theorem exists_nearly_equiangular {α ε : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
      (2 : ℝ) ^ (c * n) ≤ S.card ∧ (∀ v ∈ S, ‖v‖ = 1) ∧
        ∀ v ∈ S, ∀ w ∈ S, v ≠ w → inner ℝ v w ∈ Set.Icc (α - ε) (α + ε) := by
  sorry

end ProbMethodCombinatorics
