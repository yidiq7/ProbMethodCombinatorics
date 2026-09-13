import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import ProbMethodCombinatorics.PropertyB

/-!
# Chapter 3: Alterations

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 3.

The method: make a random construction, then repair its blemishes.
-/

namespace ProbMethodCombinatorics

open Finset

/-- **Markov's inequality**, in the finite-averaging form this project uses: for a nonnegative
`f` on `s`, the number of points of `s` where `f` reaches `a` is at most `(∑ i ∈ s, f i) / a`.

Mathlib's `MeasureTheory.mul_meas_ge_le_lintegral₀` is the measure-theoretic statement; this is
the counting one (Zhao, Theorem 3.3.1). -/
theorem card_filter_le_sum_div {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {a : ℝ} (ha : 0 < a) :
    ((s.filter fun i => a ≤ f i).card : ℝ) ≤ (∑ i ∈ s, f i) / a := by
  rw [le_div_iff₀ ha]
  have hsum : ∑ i ∈ s.filter fun i => a ≤ f i, f i ≤ ∑ i ∈ s, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i hi _ => hf i hi
  have hcard : ((s.filter fun i => a ≤ f i).card : ℝ) * a
      ≤ ∑ i ∈ s.filter fun i => a ≤ f i, f i := by
    have := Finset.card_nsmul_le_sum (s.filter fun i => a ≤ f i) f a
      fun i hi => (Finset.mem_filter.mp hi).2
    simpa [nsmul_eq_mul, mul_comm] using this
  exact hcard.trans hsum

section Dominating

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `U` is a *dominating set* of `G` if every vertex is in `U` or has a neighbour in `U`. -/
def IsDominating (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ v : V, v ∈ U ∨ ∃ u ∈ U, G.Adj u v

/-- **Zhao, Theorem 3.1.1**: a graph on `n` vertices with minimum degree `δ > 1` has a dominating
set of size at most `((log (δ + 1) + 1) / (δ + 1)) * n`. -/
theorem exists_isDominating_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {δ : ℕ} (hδ : 1 < δ) (hdeg : ∀ v : V, δ ≤ G.degree v) :
    ∃ U : Finset V, IsDominating G U ∧
      (U.card : ℝ) ≤ (Real.log (δ + 1) + 1) / (δ + 1) * Fintype.card V := by
  sorry

end Dominating

section Heilbronn

/-- Twice the (unsigned) area of the triangle spanned by `p`, `q`, `r` in the plane. -/
def twiceArea (p q r : ℝ × ℝ) : ℝ :=
  |(q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)|

/-- **Heilbronn triangle problem** (Zhao, Theorem 3.2.3): for some absolute constant `c > 0` and
every `n`, there are `n` points in the unit square with every triple spanning a triangle of area
at least `c / n ^ 2`. -/
theorem exists_heilbronn_configuration :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ S : Finset (ℝ × ℝ), S.card = n ∧
      (∀ p ∈ S, p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
        c / (n : ℝ) ^ 2 ≤ twiceArea p q r := by
  sorry

end Heilbronn

/-- **Erdős 1959** (Zhao, Theorem 3.4.1): there are graphs of arbitrarily large girth and
arbitrarily large chromatic number — high chromatic number cannot be certified locally. -/
theorem exists_girth_gt_and_chromaticNumber_gt (k l : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (l : ℕ∞) < G.girth ∧ (k : ℕ∞) < G.chromaticNumber := by
  sorry

/-- **Radhakrishnan–Srinivasan 2000** (Zhao, Theorem 3.5.1): for some absolute constant `c > 0`,
every `k`-uniform hypergraph with at most `c * √(k / log k) * 2 ^ k` edges is 2-colourable.  This
is the best known lower bound on `m k`, and strengthens `twoColorable_of_card_lt`. -/
theorem exists_twoColorable_of_card_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (k : ℕ), 2 ≤ k →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e.card = k) →
        (H.card : ℝ) ≤ c * Real.sqrt (k / Real.log k) * 2 ^ k → TwoColorable H := by
  sorry

end ProbMethodCombinatorics
