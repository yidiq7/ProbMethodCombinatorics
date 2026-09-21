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
  sorry

end ProbMethodCombinatorics
