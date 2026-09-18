import ProbMethodCombinatorics.PolyLowerBound

/-!
# Theorem 2.5.2: red/blue discrepancy in a `k`-partite colouring

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 2.5.2.

`V` is split into `k` parts of size `n`, the `k`-subsets of `V` are coloured red or blue, and
every *transversal* `k`-set — one vertex from each part — is blue.  Then some `S ⊆ V` has its
red and blue counts differing by more than `c k · nᵏ`, with `c k > 0` depending only on `k`.

The proof picks `S` by keeping each vertex of part `i` independently with probability `pᵢ`.
The expected red/blue difference is then a polynomial in `p₁, …, p_k` whose `p₁p₂⋯p_k`
coefficient is `nᵏ` (that is exactly the transversal hypothesis) and whose other coefficients
are bounded by `nᵏ` in absolute value.  Dividing through by `nᵏ` puts it in the family
`exists_pos_forall_exists_abs_eval_ge` handles, and the constant that lemma supplies is
uniform in the colouring — which is why `c k` does not depend on it.

The vertex set is modelled as `Fin k × Fin n`, so part `i` is the fibre over `i` and a
transversal edge is a `k`-set meeting every fibre exactly once.
-/

namespace ProbMethodCombinatorics

open Finset

variable {k n : ℕ}

/-- A `k`-set meeting every part exactly once. -/
def IsTransversalEdge (e : Finset (Fin k × Fin n)) : Prop :=
  ∀ i : Fin k, (e.filter fun v => v.1 = i).card = 1

/-- **Theorem 2.5.2.**  The constant is uniform in `n` and in the colouring; that uniformity
is inherited from `exists_pos_forall_exists_abs_eval_ge` and is the substance of the result. -/
theorem exists_subset_colour_discrepancy {k : ℕ} (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (col : Finset (Fin k × Fin n) → Bool),
      (∀ e : Finset (Fin k × Fin n), e.card = k → IsTransversalEdge e → col e = true) →
      ∃ S : Finset (Fin k × Fin n),
        c * (n : ℝ) ^ k <
          |(((S.powersetCard k).filter fun e => col e = true).card : ℝ)
            - (((S.powersetCard k).filter fun e => col e = false).card : ℝ)| := by
  sorry

end ProbMethodCombinatorics
