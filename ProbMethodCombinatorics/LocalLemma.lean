import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import ProbMethodCombinatorics.PropertyB
import ProbMethodCombinatorics.Ramsey

/-!
# Chapter 6: Lovász Local Lemma

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 6.

The local lemma interpolates between the two easy regimes for avoiding a family of bad
events: full independence, and a union bound.  It needs a genuine probability space — the
notion of independence involved is not pairwise independence and does not reduce to
counting — so this chapter, like Chapter 4, is stated over `MeasureTheory.Measure`.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The event that each `B j` with `j ∈ s` occurs or fails according to `f`. -/
def pattern (B : ι → Set Ω) (s : Finset ι) (f : ι → Bool) : Set Ω :=
  ⋂ j ∈ s, if f j then B j else (B j)ᶜ

/-- **Independence from a set of events** (Zhao, Definition 6.1.1): `A` is independent of every
event built by intersecting the `B j`, `j ∈ s`, each taken either positively or negatively.

This is strictly stronger than pairwise independence of `A` with each `B j`, which is exactly
why the dependency graph of Definition 6.1.2 is not obtained by joining non-independent pairs. -/
def IndepFrom (μ : Measure Ω) (A : Set Ω) (B : ι → Set Ω) (s : Finset ι) : Prop :=
  ∀ f : ι → Bool, μ (A ∩ pattern B s f) = μ A * μ (pattern B s f)

/-- **Dependency graph** (Zhao, Definition 6.1.2): `N i` lists the neighbours of `i`, and each
`A i` must be independent from every set of events avoiding `i` and its neighbours. -/
def IsDependencyGraph (μ : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, ∀ s : Finset ι, (∀ j ∈ s, j ≠ i ∧ j ∉ N i) → IndepFrom μ (A i) A s

variable [Fintype ι]

/-- **Lovász local lemma, general form** (Zhao, Theorem 6.1.9; Erdős–Lovász 1975).  If weights
`x i ∈ [0, 1)` satisfy `ℙ(A i) ≤ x i * ∏_{j ∈ N i} (1 - x j)`, then the probability that no
`A i` occurs is at least `∏ i, (1 - x i)`. -/
theorem lovasz_local_lemma [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hbound : ∀ i, (μ (A i)).toReal ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ (μ (⋂ i, (A i)ᶜ)).toReal := by
  sorry

/-- **Lovász local lemma, symmetric form** (Zhao, Theorem 6.1.7): if every `A i` has probability
at most `p` and depends on at most `d` others, and `e * p * (d + 1) ≤ 1`, then with positive
probability none of the `A i` occur.  The constant `e` is best possible (Shearer 1985). -/
theorem lovasz_local_lemma_symmetric [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
    {p : ℝ} {d : ℕ} (hp : ∀ i, (μ (A i)).toReal ≤ p)
    (hd : ∀ i, (N i).card ≤ d)
    (h : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < (μ (⋂ i, (A i)ᶜ)).toReal := by
  sorry

/-- **Lovász local lemma, small-neighbourhood form** (Zhao, Corollary 6.1.10): if every `A i` has
probability less than `1 / 2` and the probabilities in each neighbourhood sum to at most `1 / 4`,
then with positive probability none of the `A i` occur. -/
theorem lovasz_local_lemma_of_sum_le [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (N : ι → Finset ι) (hN : IsDependencyGraph μ A N)
    (hhalf : ∀ i, (μ (A i)).toReal < 1 / 2)
    (hsum : ∀ i, ∑ j ∈ N i, (μ (A j)).toReal ≤ 1 / 4) :
    0 < (μ (⋂ i, (A i)ᶜ)).toReal := by
  sorry

section Applications

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Local condition for 2-colourability** (Zhao, Theorem 6.2.1): a `k`-uniform hypergraph in
which every edge meets at most `d` other edges is 2-colourable as soon as
`e * (d + 1) ≤ 2 ^ (k - 1)`.

Unlike `twoColorable_of_card_lt` (Theorem 1.3.1) this bounds no global quantity: a hypergraph
with arbitrarily many edges qualifies, provided they are spread out. -/
theorem twoColorable_of_inter_card_le {k : ℕ} (hk : 2 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k) {d : ℕ}
    (hd : ∀ e ∈ H, ((H.erase e).filter fun f => (e ∩ f).Nonempty).card ≤ d)
    (h : Real.exp 1 * (d + 1) ≤ 2 ^ (k - 1)) :
    TwoColorable H := by
  sorry

/-- **Zhao, Corollary 6.2.2**: for `k ≥ 9` every `k`-uniform `k`-regular hypergraph is
2-colourable, where `k`-regular means every vertex lies in exactly `k` edges.  (The statement
fails for `k = 2` and `k = 3` but holds for all `k ≥ 4`, by Thomassen 1992.) -/
theorem twoColorable_of_regular {k : ℕ} (hk : 9 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k)
    (hreg : ∀ v ∈ H.biUnion id, (H.filter fun e => v ∈ e).card = k) :
    TwoColorable H := by
  sorry

/-- **Spencer 1977** (Zhao, Theorem 1.1.9): the local lemma improves the Ramsey lower bound of
Theorem 1.1.2 by a further constant factor, giving the best bound on `R(k, k)` known to date.

The hypothesis is the book's `((k choose 2)(n choose (k-2)) + 1) 2 ^ (1 - (k choose 2)) < 1/e`
with denominators cleared. -/
theorem lt_ramseyNumber_of_local_lemma (n k : ℕ) (hk : 2 ≤ k)
    (h : Real.exp 1 * (2 * ((k.choose 2 * n.choose (k - 2) : ℕ) : ℝ) + 2)
      ≤ 2 ^ (k.choose 2)) :
    n < ramseyNumber k := by
  sorry

end Applications

end ProbMethodCombinatorics
