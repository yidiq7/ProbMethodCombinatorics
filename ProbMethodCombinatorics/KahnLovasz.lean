import ProbMethodCombinatorics.Entropy

/-!
# Section 10.2: the Kahn–Lovász theorem

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Corollary 10.2.2.

Brégman's theorem bounds the permanent of a 0/1 matrix by `∏ (dᵢ!) ^ (1 / dᵢ)` over its row
sums; Kahn–Lovász is the graph statement it implies, bounding the number of perfect matchings
of a graph by `∏ (d_v !) ^ (1 / (2 d_v))` over its degrees.

The route is entirely assembly, and every piece is already proved here:
`perfectMatchingCount_sq_le_doubleCover` squares the count into the double cover,
`perfectMatchingCount_doubleCover` identifies that with the permutations respecting adjacency,
`permanent_eq_card_permSupport` reads those as the permanent of the adjacency matrix, and
`permanent_le_prod_factorial` is Brégman.  The square root at the end is what turns the `1 / d`
exponent into `1 / (2 d)`.

A vertex of degree zero needs no hypothesis: its factor is `(0!) ^ (0 : ℝ)⁻¹ = 1 ^ 0 = 1`, and
the graph has no perfect matching at all once `n` is positive, so the bound holds with room.
-/

namespace ProbMethodCombinatorics

open Finset

/-- **Corollary 10.2.2 (Kahn–Lovász).**  The number of perfect matchings of a finite simple
graph is at most `∏ (d_v !) ^ (1 / (2 d_v))` over its vertices.

Stated on `Fin n` because `perfectMatchingCount_doubleCover` is, and the two have to meet. -/
theorem perfectMatchingCount_le_prod_factorial {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (perfectMatchingCount G : ℝ)
      ≤ ∏ v, ((G.degree v).factorial : ℝ) ^ ((2 * G.degree v : ℝ))⁻¹ := by
  -- The adjacency matrix of `G`, as a `0/1` matrix whose row sums are the degrees.
  obtain ⟨A, hA1⟩ : ∃ A : Matrix (Fin n) (Fin n) ℝ,
      ∀ i j, A i j = if G.Adj i j then 1 else 0 :=
    ⟨Matrix.of fun i j => if G.Adj i j then 1 else 0, fun _ _ => rfl⟩
  have hA : ∀ i j, A i j = 0 ∨ A i j = 1 := by
    intro i j
    rw [hA1]
    by_cases h : G.Adj i j <;> simp [h]
  have hd : ∀ i, ∑ j, A i j = (G.degree i : ℝ) := by
    intro i
    simp_rw [hA1]
    rw [Finset.sum_boole, ← SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.card_neighborFinset_eq_degree]
  have hsupp : permSupport A = univ.filter fun σ : Equiv.Perm (Fin n) => ∀ i, G.Adj i (σ i) := by
    ext σ
    simp [permSupport, hA1]
  have hfacnn : ∀ i : Fin n,
      (0 : ℝ) ≤ (Nat.factorial (G.degree i) : ℝ) ^ ((G.degree i : ℝ))⁻¹ := fun i =>
    (Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos (G.degree i)) _).le
  -- Brégman–Minc for `A`, with its permanent read as the perfect-matching count of the cover.
  have hbreg := permanent_le_prod_factorial A hA (fun i => G.degree i) hd
  rw [permanent_eq_card_permSupport A hA, hsupp, ← perfectMatchingCount_doubleCover G] at hbreg
  have hsq : (perfectMatchingCount G : ℝ) ^ 2
      ≤ ∏ i, (Nat.factorial (G.degree i) : ℝ) ^ ((G.degree i : ℝ))⁻¹ := by
    refine le_trans ?_ hbreg
    exact_mod_cast perfectMatchingCount_sq_le_doubleCover G
  -- Taking square roots halves every exponent, turning `(dᵥ)⁻¹` into `(2 dᵥ)⁻¹`.
  have h0 : (0 : ℝ) ≤ (perfectMatchingCount G : ℝ) := Nat.cast_nonneg _
  have hroot := Real.rpow_le_rpow (by positivity) hsq (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  rw [← Real.rpow_natCast (perfectMatchingCount G : ℝ) 2, ← Real.rpow_mul h0,
    show ((2 : ℕ) : ℝ) * 2⁻¹ = 1 by norm_num, Real.rpow_one] at hroot
  refine hroot.trans_eq ?_
  rw [← Real.finsetProd_rpow univ _ (fun i _ => hfacnn i) (2⁻¹ : ℝ)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  rw [mul_inv]
  ring

end ProbMethodCombinatorics
