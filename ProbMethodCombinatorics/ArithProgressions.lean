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
  -- `∑ n rⁿ` converges for `‖r‖ < 1`, so its tails are the total minus the finite sums
  -- over `range N`, which tend to `0`; any `N` past the threshold for `c` works.
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr₀]
  have hsum : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have htail : ∀ N : ℕ, ∑' m : ℕ, ((m + N : ℕ) : ℝ) * r ^ (m + N)
      = (∑' n : ℕ, (n : ℝ) * r ^ n) - ∑ j ∈ Finset.range N, (j : ℝ) * r ^ j := by
    intro N
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum.sum_add_tsum_nat_add N
  have hconst : Filter.Tendsto (fun _ : ℕ => ∑' n : ℕ, (n : ℝ) * r ^ n) Filter.atTop
      (nhds (∑' n : ℕ, (n : ℝ) * r ^ n)) := tendsto_const_nhds
  have key : Filter.Tendsto (fun N : ℕ => ∑' m : ℕ, ((m + N : ℕ) : ℝ) * r ^ (m + N))
      Filter.atTop (nhds 0) := by
    simp only [htail]
    simpa using hconst.sub hsum.hasSum.tendsto_sum_nat
  exact (key.eventually_lt_const hc).exists

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
  classical
  -- For each `p = (b, e) ∈ T`, pick a meeting point `F p ∈ apSet a d k` together with its
  -- position `G p < l` inside the `l`-AP, so that `b + (G p) * e = F p`.
  have key : ∀ p ∈ T, ∃ (v : ℤ) (i : ℕ), v ∈ apSet a d k ∧ i < l ∧ p.1 + (i : ℤ) * p.2 = v := by
    intro p hp
    obtain ⟨-, -, v, hv⟩ := hT p hp
    rw [Finset.mem_inter] at hv
    obtain ⟨hv₁, hv₂⟩ := hv
    rw [apSet, Finset.mem_image] at hv₁
    obtain ⟨i, hi, hiv⟩ := hv₁
    exact ⟨v, i, hv₂, Finset.mem_range.mp hi, hiv⟩
  choose! F G hF hG hFG using key
  have hmaps : Set.MapsTo (fun p : ℤ × ℤ => (F p, G p, p.2)) (T : Set (ℤ × ℤ))
      ((apSet a d k ×ˢ Finset.range l ×ˢ Finset.Icc (1 : ℤ) (D : ℤ) : Finset (ℤ × ℕ × ℤ)) :
        Set (ℤ × ℕ × ℤ)) := by
    intro p hp
    have hp : p ∈ T := hp
    obtain ⟨h₁, h₂, -⟩ := hT p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨hF p hp, hG p hp, by omega, h₂⟩
  have hinj : Set.InjOn (fun p : ℤ × ℤ => (F p, G p, p.2)) (T : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    have hp : p ∈ T := hp
    have hq : q ∈ T := hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨hv, hi, he⟩ := hpq
    have e₁ := hFG p hp
    have e₂ := hFG q hq
    rw [← hv, ← hi, ← he] at e₂
    exact Prod.ext (add_right_cancel (e₁.trans e₂.symm)) he
  have hk : (apSet a d k).card ≤ k := by
    rw [apSet]
    exact Finset.card_image_le.trans_eq (Finset.card_range k)
  calc T.card
      ≤ (apSet a d k ×ˢ Finset.range l ×ˢ Finset.Icc (1 : ℤ) (D : ℤ)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (apSet a d k).card * (l * D) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Int.card_Icc]
        simp
    _ ≤ k * (l * D) := Nat.mul_le_mul_right _ hk
    _ = k * l * D := (mul_assoc _ _ _).symm

end ProbMethodCombinatorics
