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
  sorry

end ProbMethodCombinatorics
