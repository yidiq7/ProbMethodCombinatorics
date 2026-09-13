import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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
  -- `cut e` is the set of colourings that separate the two endpoints of `e`.
  let cut : Sym2 V → Finset (V → Bool) :=
    fun e => univ.filter fun f => Sym2.map f e = s(true, false)
  have hmem : ∀ (e : Sym2 V) (f : V → Bool),
      f ∈ cut e ↔ Sym2.map f e = s(true, false) := by
    intro e f
    simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Every edge is cut by at least half of the colourings: flipping the colour of one
  -- endpoint injects the colourings that fail to cut it into those that do.
  have key : ∀ e ∈ G.edgeFinset, (univ : Finset (V → Bool)).card ≤ (cut e).card + (cut e).card := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      have huv : u ≠ v := (G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)).ne
      have hP : ∀ f : V → Bool, (Sym2.map f s(u, v) = s(true, false)) ↔ f u ≠ f v := by
        intro f
        rw [Sym2.map_mk, Sym2.eq_iff]
        generalize f u = a
        generalize f v = b
        revert a b
        decide
      have hle : (univ.filter fun f : V → Bool =>
          ¬ (Sym2.map f s(u, v) = s(true, false))).card ≤ (cut s(u, v)).card := by
        apply Finset.card_le_card_of_injOn (fun f => Function.update f u (!(f u)))
        · intro f hf
          have hf' : ¬ (Sym2.map f s(u, v) = s(true, false)) := by
            have := Finset.mem_coe.mp hf
            rw [Finset.mem_filter] at this
            exact this.2
          rw [hP, not_ne_iff] at hf'
          refine Finset.mem_coe.mpr ?_
          show Function.update f u (!(f u)) ∈ cut s(u, v)
          rw [hmem, hP, Function.update_self, Function.update_of_ne (Ne.symm huv), hf']
          exact Bool.not_ne_self _
        · intro f₁ _ f₂ _ h
          funext w
          by_cases hw : w = u
          · subst hw
            have h' := congrFun h w
            simp only [Function.update_self] at h'
            exact Bool.not_inj h'
          · have h' := congrFun h w
            simpa only [Function.update_of_ne hw] using h'
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (V → Bool))) (fun f => Sym2.map f s(u, v) = s(true, false))
      have hA : (univ.filter fun f : V → Bool =>
          Sym2.map f s(u, v) = s(true, false)) = cut s(u, v) := rfl
      rw [hA] at hsplit
      omega
  -- Count the pairs `(f, e)` with `e` cut by `f` in both orders.
  have h1 : ∀ f : V → Bool, (cutEdges G f).card
      = ∑ e ∈ G.edgeFinset, if Sym2.map f e = s(true, false) then 1 else 0 := by
    intro f
    rw [cutEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
  have h2 : ∀ e : Sym2 V, (cut e).card
      = ∑ f : V → Bool, if Sym2.map f e = s(true, false) then 1 else 0 := by
    intro e
    show (univ.filter fun f : V → Bool => Sym2.map f e = s(true, false)).card = _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hdc : ∑ f : V → Bool, (cutEdges G f).card = ∑ e ∈ G.edgeFinset, (cut e).card := by
    rw [Finset.sum_congr rfl fun f _ => h1 f, Finset.sum_congr rfl fun e _ => h2 e]
    exact Finset.sum_comm
  -- Some colouring is at least as good as the average.
  refine (Finset.exists_le_of_sum_le ⟨fun _ => true, Finset.mem_univ _⟩ ?_).imp fun f hf => hf.2
  calc ∑ _f : V → Bool, G.edgeFinset.card
      = ∑ _e ∈ G.edgeFinset, (univ : Finset (V → Bool)).card := by
        simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ e ∈ G.edgeFinset, ((cut e).card + (cut e).card) := Finset.sum_le_sum key
    _ = (∑ e ∈ G.edgeFinset, (cut e).card) + ∑ e ∈ G.edgeFinset, (cut e).card :=
        Finset.sum_add_distrib
    _ = (∑ f : V → Bool, (cutEdges G f).card) + ∑ f : V → Bool, (cutEdges G f).card := by
        rw [hdc]
    _ = ∑ f : V → Bool, ((cutEdges G f).card + (cutEdges G f).card) :=
        Finset.sum_add_distrib.symm
    _ = ∑ f : V → Bool, 2 * (cutEdges G f).card :=
        Finset.sum_congr rfl fun f _ => (Nat.two_mul _).symm

end ProbMethodCombinatorics
