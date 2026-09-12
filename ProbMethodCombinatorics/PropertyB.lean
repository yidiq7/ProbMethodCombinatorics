import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi

/-!
# Chapter 1.3: 2-colourable hypergraphs

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 1.3.1.

A hypergraph is a finite family of edges, each a `Finset` of vertices; it is `k`-uniform when every
edge has exactly `k` vertices.
-/

namespace ProbMethodCombinatorics

open Finset

/-- A hypergraph is *2-colourable* (has *property B*) if its vertices can be two-coloured with no
edge monochromatic. -/
def TwoColorable {α : Type*} (H : Finset (Finset α)) : Prop :=
  ∃ f : α → Bool, ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- **Erdős 1964** (Zhao, Theorem 1.3.1): every `k`-uniform hypergraph with fewer than `2 ^ (k - 1)`
edges is 2-colourable.  Equivalently `m k ≥ 2 ^ (k - 1)`, where `m k` is the least number of edges
in a non-2-colourable `k`-uniform hypergraph. -/
theorem twoColorable_of_card_lt {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : 2 ≤ k) {H : Finset (Finset α)}
    (huniform : ∀ e ∈ H, e.card = k) (hcard : H.card < 2 ^ (k - 1)) :
    TwoColorable H := by
  sorry

end ProbMethodCombinatorics
