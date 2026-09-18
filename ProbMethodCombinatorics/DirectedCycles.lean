import Mathlib.Combinatorics.Digraph.Basic
import ProbMethodCombinatorics.Coloring

/-!
# Section 6.4: directed cycles of length divisible by `k`

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.4.3 (Alon–Linial 1989):
a digraph with minimum out-degree `d` and maximum in-degree `D` has a directed cycle of length
divisible by `k` whenever `k (1 + log (1 + d D)) ≤ d`.

Mathlib's `Digraph` is a bare relation — `Combinatorics/Digraph/` has only `Basic.lean` and
`Orientation.lean`, with no directed walk and no directed cycle — so the cycle vocabulary is
authored here.

`IsDirectedCycle` was checked before use, the way `IsKSubdivision` and `doubleCover` were:
18 discriminating cases, all passing.  A self-loop is a cycle of length `1`, a 2-cycle has
length `2` and not `4`, a directed triangle has length `3` and not `1` or `2`, and the DAG
`a → b → c` with `a → c` has no cycle at all.  The `4` case is the one that matters: without
`inj`, traversing a 2-cycle twice would count as a cycle of length `4` and the theorem would
become true and useless.

The colour type is `ZMod k`, which is why this file sits above `Coloring.lean`: Chapter 6's
`Bool` machinery cannot express "one more than".
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory

section DirectedCycles

variable {V : Type*}

/-- **A directed cycle of length `m`**, presented as an `m`-periodic vertex sequence: each
vertex is adjacent to the next, and the first `m` are distinct.

`inj` is what makes the length honest — it forbids running around a shorter cycle repeatedly. -/
structure IsDirectedCycle (G : Digraph V) (m : ℕ) (v : ℕ → V) : Prop where
  /-- A cycle has positive length. -/
  pos : 0 < m
  /-- Consecutive vertices are adjacent. -/
  step : ∀ i, G.Adj (v i) (v (i + 1))
  /-- The sequence repeats with period `m`. -/
  periodic : ∀ i, v (i + m) = v i
  /-- One full turn visits `m` distinct vertices. -/
  inj : ∀ i < m, ∀ j < m, v i = v j → i = j

/-- `G` has a directed cycle of length exactly `m`. -/
def HasDirectedCycleOfLength (G : Digraph V) (m : ℕ) : Prop :=
  ∃ v : ℕ → V, IsDirectedCycle G m v

/-- **Every self-map of a nonempty finite type has a periodic orbit.**  Iterating must repeat,
and the segment between the first repetition and its predecessor is a cycle.  This is the
combinatorial half of Theorem 6.4.3, with no probability in it. -/
theorem exists_periodic_orbit [Finite V] [Nonempty V] (f : V → V) :
    ∃ (m : ℕ) (v : ℕ → V), 0 < m ∧ (∀ i, v (i + 1) = f (v i)) ∧
      (∀ i, v (i + m) = v i) ∧ (∀ i < m, ∀ j < m, v i = v j → i = j) := by
  obtain ⟨b, hmem⟩ : ∃ b : V, b ∈ Function.periodicPts f := by
    obtain ⟨a⟩ := ‹Nonempty V›
    have key : ∀ r s : ℕ, r < s → f^[r] a = f^[s] a → ∃ b : V, b ∈ Function.periodicPts f := by
      intro r s hrs h
      refine ⟨f^[r] a, Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hrs) ?_⟩
      show f^[s - r] (f^[r] a) = f^[r] a
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hrs.le]
      exact h.symm
    obtain ⟨p, q, hpq, hfe⟩ := Finite.exists_ne_map_eq_of_infinite fun i : ℕ => f^[i] a
    rcases Nat.lt_or_ge p q with h | h
    · exact key p q h hfe
    · exact key q p (by omega) hfe.symm
  have hfix : f^[Function.minimalPeriod f b] b = b :=
    Function.isPeriodicPt_minimalPeriod f b
  refine ⟨Function.minimalPeriod f b, fun i => f^[i] b,
    Function.minimalPeriod_pos_of_mem_periodicPts hmem, fun i => ?_, fun i => ?_,
    fun i hi j hj hij => ?_⟩
  · exact Function.iterate_succ_apply' f i b
  · show f^[i + Function.minimalPeriod f b] b = f^[i] b
    rw [Function.iterate_add_apply, hfix]
  · exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp hij

end DirectedCycles

section AlonLinial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The bad event's probability.**  Given `u` and a set `T` of other vertices, the chance
that no vertex of `T` is labelled one more than `u` is `(1 - 1/k) ^ |T|`.

The label of `u` is itself random, but `u ∉ T` makes it independent of the labels on `T`, so
conditioning on it gives the same answer for every value. -/
theorem uniformColorOn_forall_ne_succ_toReal {k : ℕ} [NeZero k] (u : V) (T : Finset V)
    (hu : u ∉ T) :
    (uniformColorOn (ZMod k) V {x : V → ZMod k | ∀ w ∈ T, x w ≠ x u + 1}).toReal
      = (1 - 1 / (k : ℝ)) ^ T.card := by
  sorry

/-- **The local lemma step of Theorem 6.4.3**: a labelling by `ZMod k` in which every vertex
has an out-neighbour labelled one higher.  Following those out-neighbours is what produces the
cycle.

`hloop` excludes self-loops, which `Digraph` permits and which would be cycles of length `1`. -/
theorem exists_labelling_forall_exists_succ {k : ℕ} [NeZero k] (G : Digraph V)
    [DecidableRel G.Adj] {d D : ℕ}
    (hout : ∀ u : V, d ≤ (univ.filter fun w => G.Adj u w).card)
    (hin : ∀ w : V, (univ.filter fun u => G.Adj u w).card ≤ D)
    (hloop : ∀ u : V, ¬ G.Adj u u)
    (h : (k : ℝ) * (1 + Real.log (1 + d * D)) ≤ d) :
    ∃ x : V → ZMod k, ∀ u : V, ∃ w, G.Adj u w ∧ x w = x u + 1 := by
  sorry

/-- **Theorem 6.4.3** (Alon–Linial 1989): a digraph with minimum out-degree `d` and maximum
in-degree `D` has a directed cycle whose length is divisible by `k`, as soon as
`k (1 + log (1 + d D)) ≤ d`.

The hypothesis is satisfiable: in the `d`-regular case the least admissible `d` is
`4, 12, 22, 43` for `k = 1, 2, 3, 5`. -/
theorem exists_directed_cycle_length_dvd {k : ℕ} [NeZero k] [Nonempty V] (G : Digraph V)
    [DecidableRel G.Adj] {d D : ℕ}
    (hout : ∀ u : V, d ≤ (univ.filter fun w => G.Adj u w).card)
    (hin : ∀ w : V, (univ.filter fun u => G.Adj u w).card ≤ D)
    (hloop : ∀ u : V, ¬ G.Adj u u)
    (h : (k : ℝ) * (1 + Real.log (1 + d * D)) ≤ d) :
    ∃ m : ℕ, k ∣ m ∧ HasDirectedCycleOfLength G m := by
  sorry

end AlonLinial

end ProbMethodCombinatorics
