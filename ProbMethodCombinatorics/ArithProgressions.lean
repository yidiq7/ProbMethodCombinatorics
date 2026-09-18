import ProbMethodCombinatorics.LocalLemma

/-!
# Section 6.2.11: colouring the integers with no long monochromatic progression

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.2.11 (Beck 1980): for
every `ε > 0` there is a `k₀` and a 2-colouring of `ℤ` with no monochromatic `k`-term
arithmetic progression of common difference below `2 ^ ((1 - ε) k)`, for any `k ≥ k₀`.

The route is the asymmetric local lemma (`lovasz_local_lemma`) on finite subfamilies followed
by `exists_forall_notMem_of_forall_finset`.  A `k`-AP is monochromatic with probability
`2 ^ (1 - k)`, which depends on `k`, so the symmetric form cannot see it; the source takes
weights `x = 2 ^ (-(1 - ε/2) k)`.  Two inputs to that estimate are isolated here: how many
progressions can meet a fixed one, and the convergence of the resulting tail.
-/

namespace ProbMethodCombinatorics

open Finset

/-- The `k`-term arithmetic progression with first term `a` and common difference `d`. -/
def apSet (a d : ℤ) (k : ℕ) : Finset ℤ :=
  (Finset.range k).image fun i : ℕ => a + (i : ℤ) * d

/-- **Tails of `∑ n rⁿ` are eventually small.**  This is the convergence input to Beck's
estimate, where `r = 2 ^ (-ε/2)`: the source needs `∑_{ℓ ≥ k₀} ℓ 2 ^ (1 - εℓ/2) < ε/4`, which
is this bound with the constant absorbed. -/
theorem exists_tail_sum_coe_mul_geometric_lt {r c : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hc : 0 < c) :
    ∃ N : ℕ, ∑' m : ℕ, ((m + N : ℕ) : ℝ) * r ^ (m + N) < c := by
  sorry

/-- **How many progressions can meet a fixed one.**  An `ℓ`-AP of common difference at most `D`
meeting a fixed `k`-AP is determined by the element where they meet, the position of that
element in the `ℓ`-AP, and the common difference — so there are at most `k * ℓ * D` of them.

Stated for an arbitrary finite family of `(first term, common difference)` pairs rather than
for a Finset of progressions, because the progressions live in `ℤ` and there is no finite
ambient to filter. -/
theorem card_le_of_forall_apSet_inter_nonempty {k l : ℕ} {a d : ℤ} {D : ℕ}
    (T : Finset (ℤ × ℤ))
    (hT : ∀ p ∈ T, 0 < p.2 ∧ p.2 ≤ (D : ℤ) ∧ (apSet p.1 p.2 l ∩ apSet a d k).Nonempty) :
    T.card ≤ k * l * D := by
  sorry

end ProbMethodCombinatorics
