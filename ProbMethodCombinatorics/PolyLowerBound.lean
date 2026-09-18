import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Topology.Algebra.Polynomial
import ProbMethodCombinatorics.Expectation

/-!
# Lemma 2.5.3: a uniform lower bound on normalised polynomials

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Lemma 2.5.3.

Let `P k` be the polynomials in `k` variables of total degree at most `k` whose coefficients
all have absolute value at most `1` and whose `p₁p₂⋯p_k` coefficient is exactly `1`.  Then some
`c k > 0` bounds `max_{[0,1]^k} |g|` from below, *uniformly over `g ∈ P k`*.

The uniformity is the whole point, and it is what makes the constant in Theorem 2.5.2
independent of the colouring.  The source's proof is a compactness argument: `P k` is a closed
bounded subset of the finite-dimensional space of coefficient vectors, `g ↦ max_{[0,1]^k} |g|`
is continuous and strictly positive on it (a polynomial with a nonzero coefficient cannot
vanish identically on `[0,1]^k`), so it attains a positive minimum.

This is the missing input to **Theorem 2.5.2**, whose own statement needs `k`-partite
`k`-uniform hypergraph vocabulary and is not attempted here.
-/

namespace ProbMethodCombinatorics

open MvPolynomial

/-- The all-ones exponent vector, whose coefficient in `g` is the `p₁p₂⋯p_k` coefficient. -/
noncomputable def allOnes (k : ℕ) : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

/-- **Lemma 2.5.3.**  A constant `c > 0` that no normalised polynomial can beat downwards on
the unit cube.

`0 < k` is needed: at `k = 0` the only exponent vector is empty, `allOnes 0` is `0`, and the
hypotheses force the constant polynomial `1`, for which the statement is true but degenerate —
the bound is kept nontrivial by excluding it. -/
theorem exists_pos_forall_exists_abs_eval_ge (k : ℕ) (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : MvPolynomial (Fin k) ℝ,
      g.totalDegree ≤ k →
      (∀ m : Fin k →₀ ℕ, |MvPolynomial.coeff m g| ≤ 1) →
      MvPolynomial.coeff (allOnes k) g = 1 →
      ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧
        c ≤ |MvPolynomial.eval p g| := by
  sorry

end ProbMethodCombinatorics
