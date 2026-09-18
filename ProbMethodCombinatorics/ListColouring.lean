import Mathlib.Combinatorics.SimpleGraph.Basic
import ProbMethodCombinatorics.PropertyB

/-!
# Section 1.4: the list chromatic number of `K n n`

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorems 1.4.2 and 1.4.3.

A graph is **`k`-choosable** when every assignment of size-`k` colour lists to its vertices
admits a proper colouring drawing each vertex's colour from its own list.  Mathlib has no
choosability predicate — a search for `choosable` and `listChromatic` across
`Mathlib/Combinatorics/` returns nothing — so the notion is authored here.

Both directions are in this file and they sandwich `ch(K n n)`:

* **1.4.2** `2n < 2 ^ k` forces `k`-choosability.  Mark each colour `L` or `R` uniformly;
  a left vertex discards its `R` colours and a right vertex its `L` colours, so a surviving
  choice can never collide across the bipartition.  A vertex is emptied with probability
  `2 ^ (-k)`, and the union bound over the `2n` vertices is `2n · 2 ^ (-k) < 1`.
* **1.4.3** a non-2-colourable `k`-uniform hypergraph with `n` edges obstructs
  `k`-choosability, by handing the `i`-th edge to the `i`-th vertex on *both* sides.

Question 1.4.1 asks for the asymptotics of `ch(K n n)` and is left open by the source; only the
two bounds are stated here.
-/

namespace ProbMethodCombinatorics

open Finset

/-- **`k`-choosability**: every assignment of size-`k` colour lists admits a proper colouring
choosing from the lists. -/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : V → Finset α), (∀ v, (L v).card = k) →
    ∃ c : V → α, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- **Theorem 1.4.2**: `K n n` is `k`-choosable once `2n < 2 ^ k`, i.e. once
`k ≥ log₂(2n) + 1`.

The `L`/`R` marking is what makes the two sides safe from each other: a left vertex only ever
keeps an `L` colour and a right vertex only an `R` colour, so adjacent vertices cannot clash
however the surviving colours are chosen. -/
theorem isKChoosable_completeBipartiteGraph {n k : ℕ} (h : 2 * n < 2 ^ k) :
    IsKChoosable (completeBipartiteGraph (Fin n) (Fin n)) k := by
  sorry

/-- **Theorem 1.4.3**: a non-2-colourable `k`-uniform hypergraph with `n` edges obstructs
`k`-choosability of `K n n`.

Give the `i`-th edge of `H` as the list of *both* the `i`-th left and the `i`-th right vertex.
A proper list colouring then 2-colours `V H`: call a vertex `L` when some left vertex chose it
and `R` otherwise.  Edge `e i` contains `c (left i)`, which is `L`; and it contains
`c (right i)`, which must be `R`, since a left vertex choosing it would be adjacent to
`right i` and forced to differ from it. -/
theorem not_isKChoosable_completeBipartiteGraph {α : Type} [Fintype α] [DecidableEq α]
    {n k : ℕ} (H : Finset (Finset α)) (huniform : ∀ e ∈ H, e.card = k) (hn : H.card = n)
    (hnot : ¬ TwoColorable H) :
    ¬ IsKChoosable (completeBipartiteGraph (Fin n) (Fin n)) k := by
  subst hn
  intro hchoose
  apply hnot
  obtain ⟨c, hc, hsep⟩ :=
    hchoose α (fun v => ((H.equivFin.symm (v.elim id id) : {e // e ∈ H}) : Finset α))
      (fun v => huniform _ (H.equivFin.symm (v.elim id id)).2)
  refine ⟨fun a => decide (∃ i, c (Sum.inl i) = a), fun e he => ?_⟩
  have hie : ((H.equivFin.symm (H.equivFin ⟨e, he⟩) : {e // e ∈ H}) : Finset α) = e := by
    rw [Equiv.symm_apply_apply]
  set i : Fin H.card := H.equivFin ⟨e, he⟩
  refine ⟨c (Sum.inl i), ?_, c (Sum.inr i), ?_, ?_⟩
  · simpa [hie] using hc (Sum.inl i)
  · simpa [hie] using hc (Sum.inr i)
  · have hleft : ∃ j, c (Sum.inl j) = c (Sum.inl i) := ⟨i, rfl⟩
    have hright : ¬ ∃ j, c (Sum.inl j) = c (Sum.inr i) := by
      rintro ⟨j, hj⟩
      exact hsep (Sum.inl j) (Sum.inr i) (Or.inl ⟨rfl, rfl⟩) hj
    simp [hleft, hright]

end ProbMethodCombinatorics
