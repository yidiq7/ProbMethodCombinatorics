import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.UpperLower.Basic

/-!
# Chapter 7: Correlation Inequalities

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 7.

The chapter's slogan is that **increasing events of independent variables are positively
correlated**.  Two pieces of it are already in Mathlib and are recorded as upstream nodes:

* `IsUpperSet.le_card_inter_finset` — Harris–Kleitman, which is Theorem 7.1.1 for the
  *uniform* measure on subsets, in counting form;
* `fkg` — the Fortuin–Kasteleyn–Ginibre inequality for a log-supermodular measure on a
  distributive lattice.

What is not upstream is the case the applications need: a product of Bernoulli measures with
*arbitrary* edge probability, i.e. the binomial random graph `G(V, p)`.  That is stated here.
-/

namespace ProbMethodCombinatorics

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph

variable {V : Type*} [Fintype V]

/-- **Harris' inequality for the binomial random graph** (Zhao, Theorem 7.1.1).  Two increasing
graph properties are positively correlated under `G(V, p)`.

Mathlib's `IsUpperSet.le_card_inter_finset` is the `p = 1/2` case in counting form; the content
here is that the edge probability may be arbitrary. -/
theorem binomialRandom_mul_le_inter (p : I) (A B : Set (SimpleGraph V))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    binomialRandom V p A * binomialRandom V p B ≤ binomialRandom V p (A ∩ B) := by
  sorry

/-- **Decreasing events correlate too, and any number of them** (Zhao, Corollary 7.1.6): the
probability that every one of finitely many decreasing graph properties holds is at least the
product of their probabilities.

This is the form the applications use.  It follows from the pairwise increasing case by
complementation and induction on the family. -/
theorem prod_le_binomialRandom_iInter {ι : Type*} [Fintype ι] (p : I)
    (A : ι → Set (SimpleGraph V)) (hA : ∀ i, IsLowerSet (A i))
    (hAm : ∀ i, MeasurableSet (A i)) :
    ∏ i, binomialRandom V p (A i) ≤ binomialRandom V p (⋂ i, A i) := by
  sorry

/-- **Zhao, Theorem 7.2.2**: `ℙ(G(n, p) is triangle-free) ≥ (1 - p³) ^ (n choose 3)`.

For each triple of vertices, "this triple does not span a triangle" is a decreasing event of
probability `1 - p³`; the triples are not independent, but Harris' inequality bounds the
probability that all of them hold by the product.

Chapter 8 proves a matching upper bound via Janson's inequality. -/
theorem le_binomialRandom_cliqueFree_three {n : ℕ} (p : I) :
    ENNReal.ofReal ((1 - (p : ℝ) ^ 3) ^ (n.choose 3))
      ≤ binomialRandom (Fin n) p {G : SimpleGraph (Fin n) | G.CliqueFree 3} := by
  sorry

end ProbMethodCombinatorics
