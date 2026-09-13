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
  -- Greedy form: every vertex subset `A` contains an independent set of size at least
  -- `∑ v ∈ A, 1 / (d v + 1)`.  Taking `A = univ` gives the theorem.
  suffices h : ∀ A : Finset V, ∃ S ⊆ A, G.IsIndepSet (S : Set V) ∧
      ∑ v ∈ A, ((G.degree v : ℝ) + 1)⁻¹ ≤ S.card by
    obtain ⟨S, -, hind, hcard⟩ := h univ
    exact ⟨S, hind, hcard⟩
  intro A
  induction A using Finset.strongInduction with
  | _ A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hA
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    -- Remove a vertex `v` of minimum degree in the graph induced on `A`, along with its
    -- neighbours inside `A`.
    obtain ⟨v, hvA, hvmin⟩ := A.exists_min_image (fun u => (A.filter (G.Adj u)).card) hA
    have hvN : v ∉ A.filter (G.Adj v) := by simp
    have hBA : insert v (A.filter (G.Adj v)) ⊆ A :=
      Finset.insert_subset hvA (Finset.filter_subset _ _)
    obtain ⟨S, hSsub, hSind, hScard⟩ :=
      ih _ (Finset.sdiff_ssubset hBA ⟨v, Finset.mem_insert_self _ _⟩)
    have hSA : ∀ u ∈ S, u ∈ A ∧ u ∉ insert v (A.filter (G.Adj v)) :=
      fun u hu => Finset.mem_sdiff.1 (hSsub hu)
    have hvS : v ∉ S := fun hv => (hSA v hv).2 (Finset.mem_insert_self _ _)
    have hadj : ∀ u ∈ S, ¬G.Adj v u := fun u hu hvu =>
      (hSA u hu).2 (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨(hSA u hu).1, hvu⟩))
    -- Every vertex of `A` has degree at least the induced degree of `v`.
    have hdeg : ∀ u ∈ A, ((A.filter (G.Adj v)).card : ℝ) + 1 ≤ (G.degree u : ℝ) + 1 := by
      intro u hu
      have h2 : (A.filter (G.Adj u)).card ≤ G.degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_le_card fun x hx =>
          (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hx).2
      have : ((A.filter (G.Adj v)).card : ℝ) ≤ (G.degree u : ℝ) :=
        Nat.cast_le.2 ((hvmin u hu).trans h2)
      linarith
    -- The removed set carries total weight at most `1`.
    have hsumB : ∑ u ∈ insert v (A.filter (G.Adj v)), ((G.degree u : ℝ) + 1)⁻¹ ≤ 1 := by
      have hpos : (0 : ℝ) < ((A.filter (G.Adj v)).card : ℝ) + 1 := by positivity
      calc ∑ u ∈ insert v (A.filter (G.Adj v)), ((G.degree u : ℝ) + 1)⁻¹
          ≤ (insert v (A.filter (G.Adj v))).card •
              (((A.filter (G.Adj v)).card : ℝ) + 1)⁻¹ :=
            Finset.sum_le_card_nsmul _ _ _ fun u hu => inv_anti₀ hpos (hdeg u (hBA hu))
        _ = 1 := by
            rw [Finset.card_insert_of_notMem hvN, nsmul_eq_mul]
            push_cast
            field_simp
    refine ⟨insert v S, Finset.insert_subset hvA (hSsub.trans Finset.sdiff_subset), ?_, ?_⟩
    · rw [Finset.coe_insert]
      intro x hx y hy hxy
      simp only [Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact hadj y hy
      · rcases hy with rfl | hy
        · exact fun h => hadj x hx h.symm
        · exact hSind hx hy hxy
    · have hsplit := Finset.sum_sdiff (f := fun u => ((G.degree u : ℝ) + 1)⁻¹) hBA
      rw [Finset.card_insert_of_notMem hvS]
      push_cast
      linarith

/-- **Turán's theorem** (Zhao, Theorem 2.3.6) in its edge-count form: an `n`-vertex
`K (r + 1)`-free graph has at most `(1 - 1 / r) * n ^ 2 / 2` edges. -/
theorem card_edgeFinset_le_of_cliqueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hr : 1 ≤ r) (h : G.CliqueFree (r + 1)) :
    (G.edgeFinset.card : ℝ) ≤ (1 - 1 / r) * (Fintype.card V : ℝ) ^ 2 / 2 := by
  sorry

end IndependentSets

end ProbMethodCombinatorics
