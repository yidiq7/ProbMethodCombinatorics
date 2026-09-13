import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fintype.Pi
import ProbMethodCombinatorics.Alterations

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

/-- Negating a Boolean negates its `±1` value. -/
theorem toSign_not (b : Bool) : toSign (!b) = -toSign b := by
  cases b <;> norm_num [toSign]

/-- **Chernoff bound** (Zhao, Theorem 5.0.1): for `S = X₁ + ⋯ + Xₙ` with the `Xᵢ` uniform iid
`±1`, `ℙ(S ≥ λ√n) ≤ exp (-λ² / 2)`, stated as a count over the `2 ^ n` sign sequences.

`0 < n` is necessary, not bookkeeping: at `n = 0` the empty sum is `0` and the threshold
`λ √0` is `0`, so every sign sequence — there is one — meets the condition, while the bound
`exp (-λ²/2) · 2 ^ 0` is strictly below `1`.  The optimisation `t = λ / √n` in the proof needs
it too. -/
theorem card_filter_le_exp_mul (n : ℕ) (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    (((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt n ≤ ∑ i, toSign (x i)).card : ℝ)
      ≤ Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := Real.sqrt n
  have hs : 0 < s := Real.sqrt_pos.mpr hn'
  have hss : s * s = (n : ℝ) := Real.mul_self_sqrt hn'.le
  set t : ℝ := lam / s with ht_def
  have ht : 0 < t := div_pos hlam hs
  -- Transfer the threshold through the strictly monotone `x ↦ exp (t * x)`.
  have hsub : ((univ : Finset (Fin n → Bool)).filter
        fun x => lam * s ≤ ∑ i, toSign (x i))
      ⊆ (univ : Finset (Fin n → Bool)).filter
        fun x => Real.exp (t * (lam * s)) ≤ Real.exp (t * ∑ i, toSign (x i)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, Real.exp_le_exp] at hx ⊢
    exact mul_le_mul_of_nonneg_left hx ht.le
  -- The moment generating function factorises over the coordinates.
  have hmgf : ∑ x : Fin n → Bool, Real.exp (t * ∑ i, toSign (x i))
      = (Real.exp t + Real.exp (-t)) ^ n := by
    have hx : ∀ x : Fin n → Bool, Real.exp (t * ∑ i, toSign (x i))
        = ∏ i, Real.exp (t * toSign (x i)) := by
      intro x
      rw [Finset.mul_sum, Real.exp_sum]
    have hpow : (∑ b : Bool, Real.exp (t * toSign b)) ^ n
        = ∑ p : Fin n → Bool, ∏ i, Real.exp (t * toSign (p i)) :=
      Fintype.sum_pow (fun b : Bool => Real.exp (t * toSign b)) n
    simp only [hx]
    rw [← hpow]
    congr 1
    simp [toSign]
  have hexpn : (n : ℝ) * (t ^ 2 / 2) = lam ^ 2 / 2 := by
    rw [← hss, ht_def]
    field_simp
  have hthr : t * (lam * s) = lam ^ 2 := by
    rw [ht_def]
    field_simp
  calc (((univ : Finset (Fin n → Bool)).filter
          fun x => lam * s ≤ ∑ i, toSign (x i)).card : ℝ)
      ≤ (((univ : Finset (Fin n → Bool)).filter
          fun x => Real.exp (t * (lam * s)) ≤ Real.exp (t * ∑ i, toSign (x i))).card : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ (∑ x : Fin n → Bool, Real.exp (t * ∑ i, toSign (x i)))
          / Real.exp (t * (lam * s)) :=
        card_filter_le_sum_div _ _ (fun x _ => (Real.exp_pos _).le) (Real.exp_pos _)
    _ = (Real.exp t + Real.exp (-t)) ^ n / Real.exp (lam ^ 2) := by rw [hmgf, hthr]
    _ ≤ (2 * Real.exp (t ^ 2 / 2)) ^ n / Real.exp (lam ^ 2) := by
        have hcosh : Real.exp t + Real.exp (-t) = 2 * Real.cosh t := by
          rw [Real.cosh_eq]; ring
        have h2 : Real.exp t + Real.exp (-t) ≤ 2 * Real.exp (t ^ 2 / 2) := by
          rw [hcosh]
          have := Real.cosh_le_exp_half_sq t
          linarith
        have hnn : (0 : ℝ) ≤ Real.exp t + Real.exp (-t) := by positivity
        gcongr

    _ = 2 ^ n * Real.exp (lam ^ 2 / 2) / Real.exp (lam ^ 2) := by
        rw [mul_pow, ← Real.exp_nat_mul, hexpn]
    _ = Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
        rw [mul_comm (Real.exp (-lam ^ 2 / 2)), mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring

/-- **Two-sided Chernoff bound** (Zhao, Corollary 5.0.3): `ℙ(|S| ≥ λ√n) ≤ 2 exp (-λ² / 2)`.

`0 < n` is necessary for the same reason as in `card_filter_le_exp_mul`. -/
theorem card_filter_abs_le_exp_mul (n : ℕ) (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    (((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|).card : ℝ)
      ≤ 2 * Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
  have hsum : ∀ x : Fin n → Bool, ∑ i, toSign (!x i) = -∑ i, toSign (x i) := by
    intro x
    simp [toSign_not]
  set A := (univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ ∑ i, toSign (x i)) with hA
  set B := (univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ -∑ i, toSign (x i)) with hB
  have hsub : (univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|) ⊆ A ∪ B := by
    intro x hx
    simp only [hA, hB, mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    rcases abs_cases (∑ i, toSign (x i)) with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  have hBA : B.card = A.card := by
    refine Finset.card_nbij' (fun x i => !x i) (fun x i => !x i) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [hA, hB, mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      rw [hsum]
      exact hx
    · intro x hx
      simp only [hA, hB, mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      rw [hsum, neg_neg]
      exact hx
    · intro x _
      funext i
      simp
    · intro x _
      funext i
      simp
  have hAle : (A.card : ℝ) ≤ Real.exp (-lam ^ 2 / 2) * 2 ^ n :=
    card_filter_le_exp_mul n hn hlam
  have h1 : ((univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|)).card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
  rw [hBA] at h1
  have h2 : (((univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|)).card : ℝ)
      ≤ (A.card : ℝ) + (A.card : ℝ) := by exact_mod_cast h1
  have h3 : (2 : ℝ) * Real.exp (-lam ^ 2 / 2) * 2 ^ n
      = 2 * (Real.exp (-lam ^ 2 / 2) * 2 ^ n) := by ring
  rw [h3]
  linarith

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
