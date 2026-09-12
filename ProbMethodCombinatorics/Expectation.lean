import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chapter 2: Linearity of expectations

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Sections 2.1 and 2.3.
-/

namespace ProbMethodCombinatorics

open Finset

section Tournament

variable {n : ℕ}

/-- The Hamilton paths of the tournament `T` on `Fin n`, viewed as the orderings
`σ 0, σ 1, …, σ (n - 1)` of the vertices in which every vertex beats its successor. -/
def hamiltonPaths (T : Fin n → Fin n → Bool) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun σ => ((List.finRange n).map σ).IsChain fun a b => T a b = true

/-- **Szele 1943** (Zhao, Theorem 2.1.2): some tournament on `n` vertices has at least
`n! / 2 ^ (n - 1)` Hamilton paths. -/
theorem exists_tournament_card_hamiltonPaths (n : ℕ) :
    ∃ T : Fin n → Fin n → Bool, (∀ a b, a ≠ b → T a b = !T b a) ∧
      (n.factorial : ℝ) / 2 ^ (n - 1) ≤ (hamiltonPaths T).card := by
  sorry

end Tournament

section IndependentSets

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Caro–Wei** (Zhao, Theorem 2.3.2): every graph has an independent set of size at least
`∑ v, 1 / (d v + 1)`. -/
theorem exists_isIndepSet_caro_wei (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
      ∑ v : V, ((G.degree v : ℝ) + 1)⁻¹ ≤ S.card := by
  sorry

/-- **Turán's theorem** (Zhao, Theorem 2.3.6) in its edge-count form: an `n`-vertex
`K (r + 1)`-free graph has at most `(1 - 1 / r) * n ^ 2 / 2` edges. -/
theorem card_edgeFinset_le_of_cliqueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hr : 1 ≤ r) (h : G.CliqueFree (r + 1)) :
    (G.edgeFinset.card : ℝ) ≤ (1 - 1 / r) * (Fintype.card V : ℝ) ^ 2 / 2 := by
  sorry

end IndependentSets

end ProbMethodCombinatorics
