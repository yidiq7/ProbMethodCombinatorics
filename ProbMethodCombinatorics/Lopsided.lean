import ProbMethodCombinatorics.LocalLemma

/-!
# Section 6.5: the lopsided local lemma

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.5.1 and Corollary 6.5.2.

The independence hypothesis of the local lemma is used in exactly one place — equation (6.3),
where `ℙ(A i ∩ ⋂_{j ∈ S} (A j)ᶜ)` is rewritten as `ℙ(A i) · ℙ(⋂_{j ∈ S} (A j)ᶜ)`.  Turning that
`=` into a `≤` costs nothing in the proof and weakens the hypothesis to a *negative* dependency
condition: avoiding some bad events only makes it easier to avoid others.

Note how much weaker this is than `IndepFrom`.  `IndepFrom` quantifies over every pattern
`f : ι → Bool`, positive and negative; `IsNegativeDependencyGraph` asks only about the
all-negative pattern, and only for an inequality in one direction.  That gap is the content of
Remark 6.5.3's warning that a negative dependency graph is still not obtained by checking pairs.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Negative dependency graph** (Zhao, Theorem 6.5.1, hypothesis (6.1)): conditioning on
avoiding any set of events away from `i` and its neighbours does not make `A i` more likely. -/
def IsNegativeDependencyGraph (μ : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, ∀ s : Finset ι, (∀ j ∈ s, j ≠ i ∧ j ∉ N i) →
    μ (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ μ (A i) * μ (⋂ j ∈ s, (A j)ᶜ)

/-- An ordinary dependency graph is a negative dependency graph: independence gives equality,
and the all-negative pattern is one of the patterns `IndepFrom` covers. -/
theorem IsDependencyGraph.isNegativeDependencyGraph {A : ι → Set Ω} {N : ι → Finset ι}
    (h : IsDependencyGraph μ A N) : IsNegativeDependencyGraph μ A N := by
  intro i s hs
  have key := h i s hs (fun _ => false)
  simp only [pattern] at key
  exact le_of_eq key

variable [Fintype ι]

/-- **The lopsided local lemma** (Zhao, Theorem 6.5.1).  Identical to `lovasz_local_lemma`
except that `IsDependencyGraph` is replaced by `IsNegativeDependencyGraph`. -/
theorem lopsided_local_lemma [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsNegativeDependencyGraph μ A N)
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hbound : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ (μ (⋂ i, (A i)ᶜ)).toReal := by
  sorry

/-- **The lopsided local lemma, symmetric form** (Zhao, Corollary 6.5.2), at the usual weight
`x i = 1 / (d + 1)`. -/
theorem lopsided_local_lemma_symmetric [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsNegativeDependencyGraph μ A N)
    {p : ℝ} {d : ℕ} (hp : ∀ i, (μ (A i)).toReal ≤ p)
    (hd : ∀ i, (N i).card ≤ d)
    (h : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < (μ (⋂ i, (A i)ᶜ)).toReal := by
  -- Take every weight to be `1 / (d + 2)`.  The hypothesis of Theorem 6.5.1 then amounts to
  -- `(1 + 1 / (d + 1)) ^ (d + 1) ≤ e`, which `1 + x ≤ exp x` supplies; unlike `1 / (d + 1)` this
  -- weight is admissible at `d = 0` as well.
  have hm : (0:ℝ) < (d:ℝ) + 1 := by positivity
  have hkey : ((d:ℝ) + 2) ^ (d + 1) ≤ Real.exp 1 * ((d:ℝ) + 1) ^ (d + 1) := by
    have h2 := Real.add_one_le_exp (1 / ((d:ℝ) + 1))
    have h3 : ((d:ℝ) + 1) * (1 / ((d:ℝ) + 1) + 1) ≤ ((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h2 hm.le
    have h4 : ((d:ℝ) + 1) * (1 / ((d:ℝ) + 1) + 1) = (d:ℝ) + 2 := by
      field_simp
      ring
    have h1 : (d:ℝ) + 2 ≤ ((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1)) := by linarith
    have h5 : ((d:ℝ) + 2) ^ (d + 1) ≤ (((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1))) ^ (d + 1) :=
      pow_le_pow_left₀ (by positivity) h1 _
    have h6 : (((d:ℝ) + 1) * Real.exp (1 / ((d:ℝ) + 1))) ^ (d + 1)
        = ((d:ℝ) + 1) ^ (d + 1) * Real.exp 1 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp
    linarith
  have ht₀ : (0:ℝ) ≤ 1 / ((d:ℝ) + 2) := by positivity
  have ht₁ : 1 / ((d:ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have h1t : 1 - 1 / ((d:ℝ) + 2) = ((d:ℝ) + 1) / ((d:ℝ) + 2) := by field_simp; ring
  -- `hd` only bounds `(N i).card` from above, so the product over `N i` is compared with the
  -- `d`-fold power by monotonicity of `y ↦ y ^ n` on `[0, 1]`.
  have hbound : ∀ i, (μ (A i)).toReal
      ≤ 1 / ((d:ℝ) + 2) * ∏ _j ∈ N i, (1 - 1 / ((d:ℝ) + 2)) := by
    intro i
    rw [Finset.prod_const]
    have hp0 : 0 ≤ p := le_trans ENNReal.toReal_nonneg (hp i)
    refine (hp i).trans (le_trans ?_ (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by rw [h1t]; positivity) (by rw [h1t]; linarith) (hd i)) ht₀))
    have heq : 1 / ((d:ℝ) + 2) * (1 - 1 / ((d:ℝ) + 2)) ^ d
        = ((d:ℝ) + 1) ^ d / ((d:ℝ) + 2) ^ (d + 1) := by
      rw [h1t, div_pow, pow_succ]
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    calc p * ((d:ℝ) + 2) ^ (d + 1) ≤ p * (Real.exp 1 * ((d:ℝ) + 1) ^ (d + 1)) :=
          mul_le_mul_of_nonneg_left hkey hp0
      _ = ((d:ℝ) + 1) ^ d * (Real.exp 1 * p * ((d:ℝ) + 1)) := by rw [pow_succ]; ring
      _ ≤ ((d:ℝ) + 1) ^ d * 1 := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((d:ℝ) + 1) ^ d := mul_one _
  have hmain := lopsided_local_lemma A hA N hN (fun _ => 1 / ((d:ℝ) + 2))
    (fun _ => ht₀) (fun _ => ht₁) hbound
  have hpos : (0:ℝ) < ∏ _i : ι, (1 - 1 / ((d:ℝ) + 2)) :=
    Finset.prod_pos fun i _ => by rw [h1t]; positivity
  linarith

end ProbMethodCombinatorics
