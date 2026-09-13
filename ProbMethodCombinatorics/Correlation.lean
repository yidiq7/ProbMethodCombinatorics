import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SetFamily.FourFunctions
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
  classical
  -- `SimpleGraph V` carries the discrete σ-algebra, so every singleton is measurable.
  have : MeasurableSingletonClass (SimpleGraph V) :=
    ⟨fun G => by
      have h : ({G} : Set (SimpleGraph V)) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
        ext H; simp only [Set.mem_singleton_iff, Set.mem_preimage, SimpleGraph.adj_inj]
      rw [h]; exact measurable_adj (measurableSet_singleton _)⟩
  -- `μ G` is the `ℝ≥0`-valued mass that `G(V, p)` puts on the single graph `G`.
  obtain ⟨μ, hμ⟩ : ∃ μ : SimpleGraph V → NNReal,
      ∀ G, (μ G : ENNReal) = binomialRandom V p {G} :=
    ⟨fun G => (binomialRandom V p {G}).toNNReal,
      fun G => ENNReal.coe_toNNReal (measure_ne_top _ _)⟩
  -- Since there are finitely many graphs, `G(V, p) S` is the sum of `μ` over the members of `S`.
  have key : ∀ S : Set (SimpleGraph V),
      ((∑ G, μ G * (if G ∈ S then 1 else 0) : NNReal) : ENNReal) = binomialRandom V p S := by
    intro S
    rw [ENNReal.ofNNReal_finsetSum]
    simp only [hμ, apply_ite (ENNReal.ofNNReal), ENNReal.coe_zero, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, sum_measure_singleton]
    congr 1
    ext G
    simp
  -- The indicator of an upper set is monotone.
  have hmono : ∀ S : Set (SimpleGraph V), IsUpperSet S →
      Monotone (fun G : SimpleGraph V => if G ∈ S then (1 : NNReal) else 0) := by
    intro S hS a b hab
    dsimp only
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (hS hab h1) h2
    · exact zero_le
    · exact le_rfl
  -- `μ` is log-modular, because the edge count is a modular function of the graph.
  have hmod : ∀ a b : SimpleGraph V, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b) := by
    have hle : ∀ K : SimpleGraph V, K.edgeSet.ncard ≤ (Nat.card V).choose 2 := by
      intro K
      have hcard : (Nat.card V).choose 2 = (Sym2.diagSetᶜ : Set (Sym2 V)).ncard := by
        rw [Nat.card_eq_fintype_card, ← Sym2.card_diagSet_compl, Fintype.card_eq_nat_card,
          ← Nat.card_coe_set_eq]
      rw [hcard]
      exact Set.ncard_le_ncard K.edgeSet_subset_compl_diagSet (Set.toFinite _)
    intro a b
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_mul, hμ, hμ, hμ, hμ]
    have e1 : (a ⊓ b).edgeSet.ncard + (a ⊔ b).edgeSet.ncard
        = a.edgeSet.ncard + b.edgeSet.ncard := by
      rw [edgeSet_inf, edgeSet_sup,
        Set.ncard_inter_add_ncard_union _ _ (Set.toFinite _) (Set.toFinite _)]
    have e2 : ((Nat.card V).choose 2 - (a ⊓ b).edgeSet.ncard)
        + ((Nat.card V).choose 2 - (a ⊔ b).edgeSet.ncard)
        = ((Nat.card V).choose 2 - a.edgeSet.ncard)
          + ((Nat.card V).choose 2 - b.edgeSet.ncard) := by
      have := hle a; have := hle b; have := hle (a ⊓ b); have := hle (a ⊔ b); omega
    simp only [binomialRandom_singleton]
    rw [mul_mul_mul_comm, mul_mul_mul_comm ((toNNReal p : ENNReal) ^ (a ⊓ b).edgeSet.ncard),
      ← pow_add, ← pow_add, ← pow_add, ← pow_add, e1, e2]
  have hone : (∑ G, μ G) = 1 := by
    have h := key Set.univ
    simp only [Set.mem_univ, if_true, mul_one, measure_univ] at h
    exact_mod_cast h
  rw [← key A, ← key B, ← key (A ∩ B), ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hfkg := fkg (fun G : SimpleGraph V => if G ∈ A then (1 : NNReal) else 0)
    (fun G : SimpleGraph V => if G ∈ B then (1 : NNReal) else 0) μ
    (fun _ => zero_le) (fun _ => zero_le) (fun _ => zero_le)
    (hmono A hA) (hmono B hB) hmod
  rw [hone, one_mul] at hfkg
  refine hfkg.trans_eq (Finset.sum_congr rfl fun G _ => ?_)
  by_cases h1 : G ∈ A <;> by_cases h2 : G ∈ B <;> simp [h1, h2]

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
