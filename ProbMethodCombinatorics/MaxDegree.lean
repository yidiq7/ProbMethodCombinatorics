import ProbMethodCombinatorics.Correlation

/-!
# Section 7.2: Harris applied to the degrees of `G(n, p)`

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), §7.2.

Theorem 7.2.5 (Riordan–Selby) and Proposition 7.2.6 are both out of reach — the first is
quoted without proof, the second is given as a sketch and its constant `0.6102…` is a
Laplace-method integral with no closed form.  What *is* in reach is the observation the source
makes alongside them: the events "vertex `v` has small degree" are decreasing, so Harris
bounds the probability that *all* of them hold from below by the product.

The source makes that remark for the Gaussian surrogate of Proposition 7.2.6, where it needs
FKG for continuous product measures — which neither Mathlib nor this project has.  Stated here
for `binomialRandom`, the model Theorem 7.2.5 is actually about, it is a direct corollary of
`prod_le_binomialRandom_iInter` from §7.1.

Degrees are written as `(G.neighborSet v).ncard` rather than `G.degree v` because the measure
ranges over all graphs on `V`, where no `DecidableRel G.Adj` is available — the same reason
`copyCount` and `triangleCount` are written with `Set.indicator`.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory unitInterval SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Harris for degrees**: the events `deg v ≤ m` are decreasing, so `G(n, p)` keeps every
degree below `m` at least as often as the independent-events guess.

With `p = 1/2` and `m = ⌊(n-1)/2⌋` each factor is at least `1/2` by the symmetry of
`Binomial(n-1, 1/2)`, which is how the source gets its `2⁻ⁿ`. -/
theorem prod_le_binomialRandom_forall_ncard_neighborSet_le (p : I) (m : ℕ) :
    ∏ v : V, binomialRandom V p {G : SimpleGraph V | (G.neighborSet v).ncard ≤ m}
      ≤ binomialRandom V p {G : SimpleGraph V | ∀ v, (G.neighborSet v).ncard ≤ m} := by
  sorry

end ProbMethodCombinatorics
