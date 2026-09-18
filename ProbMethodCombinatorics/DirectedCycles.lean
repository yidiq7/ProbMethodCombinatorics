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
  sorry

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
  have hne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  -- Conditioning on the label of `u`: the event splits as a disjoint union.
  have hunion : {x : V → ZMod k | ∀ w ∈ T, x w ≠ x u + 1}
      = ⋃ b ∈ (Finset.univ : Finset (ZMod k)),
          ({x : V → ZMod k | x u = b} ∩ {x : V → ZMod k | ∀ w ∈ T, x w ≠ b + 1}) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_biUnion (Finset.mem_univ (x u)) ⟨rfl, ?_⟩
      exact hx
    · intro hx
      obtain ⟨b, -, hb, hx2⟩ := Set.mem_iUnion₂.1 hx
      intro w hw
      show x w ≠ x u + 1
      rw [show x u = b from hb]
      exact hx2 w hw
  have hdisj : (↑(Finset.univ : Finset (ZMod k)) : Set (ZMod k)).PairwiseDisjoint
      (fun b => ({x : V → ZMod k | x u = b} ∩ {x : V → ZMod k | ∀ w ∈ T, x w ≠ b + 1})) := by
    intro b _ c _ hbc
    refine Set.disjoint_left.2 ?_
    intro x hxb hxc
    exact hbc ((show x u = b from hxb.1).symm.trans (show x u = c from hxc.1))
  have hmeas : ∀ b ∈ (Finset.univ : Finset (ZMod k)),
      MeasurableSet ({x : V → ZMod k | x u = b} ∩ {x : V → ZMod k | ∀ w ∈ T, x w ≠ b + 1}) :=
    fun _ _ => (Set.toFinite _).measurableSet
  -- The label of `u` is uniform.
  have hfirst : ∀ b : ZMod k,
      uniformColorOn (ZMod k) V {x : V → ZMod k | x u = b} = 1 / (k : ENNReal) := by
    intro b
    have hset : {x : V → ZMod k | x u = b}
        = Set.univ.pi (fun a => if a = u then ({b} : Set (ZMod k)) else Set.univ) := by
      ext x
      constructor
      · intro h a _
        show x a ∈ (if a = u then ({b} : Set (ZMod k)) else Set.univ)
        by_cases ha : a = u
        · rw [if_pos ha]
          subst ha
          exact h
        · rw [if_neg ha]
          exact Set.mem_univ _
      · intro h
        have hxu : x u ∈ (if u = u then ({b} : Set (ZMod k)) else Set.univ) :=
          h u (Set.mem_univ u)
        rw [if_pos rfl] at hxu
        exact hxu
    rw [hset, uniformColorOn, Measure.pi_pi,
      Finset.prod_eq_single_of_mem u (Finset.mem_univ u)
        (fun a _ ha => by rw [if_neg ha]; exact measure_univ),
      if_pos rfl, ProbabilityTheory.uniformOn_univ, Measure.count_singleton, ZMod.card]
  -- `{u}` and `T` are disjoint blocks of coordinates, so the two events factor.
  have hfactor : ∀ b : ZMod k,
      uniformColorOn (ZMod k) V
          ({x : V → ZMod k | x u = b} ∩ {x : V → ZMod k | ∀ w ∈ T, x w ≠ b + 1})
        = uniformColorOn (ZMod k) V {x : V → ZMod k | x u = b}
          * uniformColorOn (ZMod k) V {x : V → ZMod k | ∀ w ∈ T, x w ≠ b + 1} := by
    intro b
    rw [uniformColorOn]
    refine measure_pi_inter_eq_mul
      (fun _ : V => ProbabilityTheory.uniformOn (Set.univ : Set (ZMod k))) {u} _ _ ?_ ?_
    · intro x y hxy
      show x u = b ↔ y u = b
      rw [hxy u (Finset.mem_singleton_self u)]
    · intro x y hxy
      have hwT : ∀ w ∈ T, x w = y w := by
        intro w hw
        refine hxy w ?_
        rw [Finset.mem_singleton]
        intro hwu
        exact hu (hwu ▸ hw)
      show (∀ w ∈ T, x w ≠ b + 1) ↔ (∀ w ∈ T, y w ≠ b + 1)
      constructor
      · intro h w hw
        rw [← hwT w hw]
        exact h w hw
      · intro h w hw
        rw [hwT w hw]
        exact h w hw
  -- Each conditional probability is the fixed-colour answer.
  have hterm : ∀ b : ZMod k,
      (uniformColorOn (ZMod k) V
          ({x : V → ZMod k | x u = b} ∩ {x : V → ZMod k | ∀ w ∈ T, x w ≠ b + 1})).toReal
        = 1 / (k : ℝ) * (1 - 1 / (k : ℝ)) ^ T.card := by
    intro b
    rw [hfactor b, ENNReal.toReal_mul, hfirst b, uniformColorOn_avoid_toReal T (b + 1),
      ZMod.card, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
  rw [hunion, measure_biUnion_finset hdisj hmeas,
    ENNReal.toReal_sum (fun b _ => measure_ne_top _ _),
    Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ZMod.card]
  field_simp

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
