import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Chapter 1: Introduction — a large bipartite subgraph

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 1.0.1.
-/

namespace ProbMethodCombinatorics

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G` separated by the two-colouring `f`, i.e. those with one endpoint of each
colour.  These are exactly the edges of the bipartite subgraph induced by `f`. -/
def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Bool) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => Sym2.map f e = s(true, false)

/-- **Large bipartite subgraph** (Zhao, Theorem 1.0.1): every graph with `m` edges has a bipartite
subgraph with at least `m / 2` edges. -/
theorem exists_cutEdges_two_mul_card_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ f : V → Bool, G.edgeFinset.card ≤ 2 * (cutEdges G f).card := by
  sorry

end ProbMethodCombinatorics
