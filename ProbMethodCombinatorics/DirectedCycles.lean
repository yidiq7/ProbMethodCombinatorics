import Mathlib.Combinatorics.Digraph.Basic
import ProbMethodCombinatorics.Coloring

/-!
# Section 6.4: directed cycles of length divisible by `k`

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 6.4.3 (Alon–Linial 1989):
a digraph with minimum out-degree `d` and maximum in-degree `D` has a directed cycle of length
divisible by `k` whenever `k (1 + log ((1 + d)(1 + D))) ≤ d`.

**The constant differs from the source.**  Zhao states the hypothesis as
`k (1 + log (1 + d D)) ≤ d`, but the dependency degree that this argument actually
establishes is `(1 + d)(1 + D) - 1`, not `d D`: two bad events interact when their closed
out-neighbourhoods meet, which happens for the `d` out-neighbours of `v`, the at most `D`
in-neighbours of `v`, *and* the at most `d D` vertices sharing an out-neighbour with `v`.
With the source's constant the local lemma inequality genuinely fails — `k = 5, d = 21,
D = 1` is a counterexample, where `e (1 - 1/k)^d (1+d)(1+D) = 1.103 > 1`.  The corrected
hypothesis costs almost nothing: in the `d`-regular case the least admissible `d` moves from
`4, 12, 22, 43` to `5, 13, 22, 43` for `k = 1, 2, 3, 5`.

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

/-- **The dependency count.**  The closed out-neighbourhood `insert u (N u)` has at most `1 + d`
vertices, and a vertex `w` whose own closed out-neighbourhood meets it is, for one of those `z`,
either `z` itself or one of the at most `D` in-neighbours of `z`.  Discarding `u` itself leaves
at most `d + D + d * D = (1 + d) * (1 + D) - 1` dependents. -/
private theorem card_dependents_le (G : Digraph V) [DecidableRel G.Adj] {d D : ℕ}
    (hin : ∀ w : V, (univ.filter fun u => G.Adj u w).card ≤ D)
    {N : V → Finset V} (hNadj : ∀ u w, w ∈ N u → G.Adj u w)
    (u : V) (hNcard : (N u).card = d) (B : Finset V)
    (hB : ∀ w ∈ B, w ≠ u ∧ (insert u (N u) ∩ insert w (N w)).Nonempty) :
    B.card ≤ d + D + d * D := by
  have hBT : ∀ w ∈ B,
      w ∈ (insert u (N u)).biUnion fun z => insert z (univ.filter fun v => G.Adj v z) := by
    intro w hw
    obtain ⟨-, z, hz⟩ := hB w hw
    rw [Finset.mem_inter] at hz
    refine Finset.mem_biUnion.2 ⟨z, hz.1, ?_⟩
    rcases Finset.mem_insert.1 hz.2 with hzw | hzN
    · rw [hzw]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ w, hNadj w z hzN⟩)
  have hsub : insert u B
      ⊆ (insert u (N u)).biUnion fun z => insert z (univ.filter fun v => G.Adj v z) := by
    intro w hw
    rcases Finset.mem_insert.1 hw with hwu | hwB
    · rw [hwu]
      exact Finset.mem_biUnion.2
        ⟨u, Finset.mem_insert_self u (N u), Finset.mem_insert_self u _⟩
    · exact hBT w hwB
  have hTcard :
      ((insert u (N u)).biUnion fun z => insert z (univ.filter fun v => G.Adj v z)).card
        ≤ d + D + d * D + 1 := by
    have hstep : ∀ z ∈ insert u (N u),
        (insert z (univ.filter fun v => G.Adj v z)).card ≤ 1 + D := by
      intro z _
      have h1 := Finset.card_insert_le z (univ.filter fun v => G.Adj v z)
      have h2 := hin z
      omega
    have hcard : (insert u (N u)).card ≤ 1 + d := by
      have h1 := Finset.card_insert_le u (N u)
      rw [hNcard] at h1
      omega
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ (1 + D) hstep) ?_
    calc (insert u (N u)).card * (1 + D) ≤ (1 + d) * (1 + D) := Nat.mul_le_mul hcard le_rfl
      _ = d + D + d * D + 1 := by ring
  have huB : u ∉ B := fun hu => (hB u hu).1 rfl
  have hfinal : B.card + 1 ≤ d + D + d * D + 1 := by
    rw [← Finset.card_insert_of_notMem huB]
    exact le_trans (Finset.card_le_card hsub) hTcard
  exact Nat.le_of_add_le_add_right hfinal

/-- **The numerical condition of the symmetric local lemma**, from the hypothesis of
`exists_labelling_forall_exists_succ`.  For `k = 1` the bad events are null, because the
hypothesis forces `1 ≤ d`; for `k ≥ 2` it is the hypothesis after taking logarithms, using
`log (1 - 1/k) ≤ -1/k`. -/
private theorem exp_mul_pow_mul_le_one_of_log_le {k d D : ℕ} [NeZero k]
    (h : (k : ℝ) * (1 + Real.log ((1 + d) * (1 + D))) ≤ d) :
    Real.exp 1 * (1 - 1 / (k : ℝ)) ^ d * ((1 + d) * (1 + D)) ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (NeZero.ne k)
    exact_mod_cast hk
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hP1 : (1 : ℝ) ≤ (1 + (d : ℝ)) * (1 + (D : ℝ)) := by nlinarith [mul_nonneg hd0 hD0]
  have hPpos : (0 : ℝ) < (1 + (d : ℝ)) * (1 + (D : ℝ)) := by linarith
  have hlogP : (0 : ℝ) ≤ Real.log ((1 + (d : ℝ)) * (1 + (D : ℝ))) := Real.log_nonneg hP1
  -- The left-hand side of `h` is at least `1`, so `1 ≤ d`.
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ 1 + Real.log ((1 + (d : ℝ)) * (1 + (D : ℝ))))]
  rcases eq_or_lt_of_le hk1 with hk | hk
  · -- `k = 1`: the bad events are null, since `d ≠ 0`.
    have hz : 1 - 1 / (k : ℝ) = 0 := by rw [← hk]; norm_num
    have hdne : d ≠ 0 := by
      intro h0
      rw [h0] at hd1
      norm_num at hd1
    rw [hz, zero_pow hdne, mul_zero, zero_mul]
    norm_num
  · have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have ht0 : (0 : ℝ) < 1 - 1 / (k : ℝ) := by
      have h1 : 1 / (k : ℝ) < 1 := by
        rw [div_lt_one hkpos]
        exact hk
      linarith
    have hklog : (k : ℝ) * Real.log (1 - 1 / (k : ℝ)) ≤ -1 :=
      calc (k : ℝ) * Real.log (1 - 1 / (k : ℝ))
          ≤ (k : ℝ) * (1 - 1 / (k : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht0) hkpos.le
        _ = -1 := by
          field_simp
          ring
    have key : 1 + (d : ℝ) * Real.log (1 - 1 / (k : ℝ))
        + Real.log ((1 + (d : ℝ)) * (1 + (D : ℝ))) ≤ 0 := by
      have h1 : (d : ℝ) * ((k : ℝ) * Real.log (1 - 1 / (k : ℝ))) ≤ (d : ℝ) * (-1) :=
        mul_le_mul_of_nonneg_left hklog hd0
      have h2 : (k : ℝ) * (1 + (d : ℝ) * Real.log (1 - 1 / (k : ℝ))
            + Real.log ((1 + (d : ℝ)) * (1 + (D : ℝ)))) ≤ (k : ℝ) * 0 := by
        have hexpand : (k : ℝ) * (1 + (d : ℝ) * Real.log (1 - 1 / (k : ℝ))
              + Real.log ((1 + (d : ℝ)) * (1 + (D : ℝ))))
            = (k : ℝ) * (1 + Real.log ((1 + (d : ℝ)) * (1 + (D : ℝ))))
              + (d : ℝ) * ((k : ℝ) * Real.log (1 - 1 / (k : ℝ))) := by ring
        rw [hexpand, mul_zero]
        linarith
      exact le_of_mul_le_mul_left h2 hkpos
    have hexp : Real.exp (1 + (d : ℝ) * Real.log (1 - 1 / (k : ℝ))
          + Real.log ((1 + (d : ℝ)) * (1 + (D : ℝ))))
        = Real.exp 1 * (1 - 1 / (k : ℝ)) ^ d * ((1 + (d : ℝ)) * (1 + (D : ℝ))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hPpos, ← Real.log_pow,
        Real.exp_log (pow_pos ht0 d)]
    rw [← hexp]
    exact Real.exp_le_one_iff.2 key

/-- **The local lemma step of Theorem 6.4.3**: a labelling by `ZMod k` in which every vertex
has an out-neighbour labelled one higher.  Following those out-neighbours is what produces the
cycle.

`hloop` excludes self-loops, which `Digraph` permits and which would be cycles of length `1`. -/
theorem exists_labelling_forall_exists_succ {k : ℕ} [NeZero k] (G : Digraph V)
    [DecidableRel G.Adj] {d D : ℕ}
    (hout : ∀ u : V, d ≤ (univ.filter fun w => G.Adj u w).card)
    (hin : ∀ w : V, (univ.filter fun u => G.Adj u w).card ≤ D)
    (hloop : ∀ u : V, ¬ G.Adj u u)
    (h : (k : ℝ) * (1 + Real.log ((1 + d) * (1 + D))) ≤ d) :
    ∃ x : V → ZMod k, ∀ u : V, ∃ w, G.Adj u w ∧ x w = x u + 1 := by
  -- Trim to out-degree exactly `d`: only `d` out-neighbours of each vertex are used.
  obtain ⟨N, hNsub, hNcard⟩ : ∃ N : V → Finset V,
      (∀ u, N u ⊆ univ.filter fun w => G.Adj u w) ∧ ∀ u, (N u).card = d := by
    choose N hN1 hN2 using fun u : V => Finset.exists_subset_card_eq (hout u)
    exact ⟨N, hN1, hN2⟩
  have hNadj : ∀ u w, w ∈ N u → G.Adj u w := fun u w hw =>
    (Finset.mem_filter.1 (hNsub u hw)).2
  have hNu : ∀ u : V, u ∉ N u := fun u hu => hloop u (hNadj u u hu)
  -- The bad event at `u`: no chosen out-neighbour carries the next label.
  obtain ⟨A, hAdef⟩ : ∃ A : V → Set (V → ZMod k), ∀ u,
      A u = {x : V → ZMod k | ∀ w ∈ N u, x w ≠ x u + 1} := ⟨_, fun _ => rfl⟩
  have hAmem : ∀ (j : V) (x : V → ZMod k), x ∈ A j ↔ ∀ w ∈ N j, x w ≠ x j + 1 := by
    intro j x
    rw [hAdef]
    exact Iff.rfl
  have hAmeas : ∀ u, MeasurableSet (A u) := fun _ => (Set.toFinite _).measurableSet
  -- `A j` reads only the coordinates in the closed out-neighbourhood `insert j (N j)`.
  have hAinv : ∀ (j : V) (x y : V → ZMod k),
      (∀ a ∈ insert j (N j), x a = y a) → (x ∈ A j ↔ y ∈ A j) := by
    intro j x y hxy
    have hj : x j = y j := hxy j (Finset.mem_insert_self j (N j))
    have hw : ∀ w ∈ N j, x w = y w := fun w hw =>
      hxy w (Finset.mem_insert_of_mem hw)
    rw [hAmem, hAmem]
    constructor
    · intro hx w hwN
      rw [← hw w hwN, ← hj]
      exact hx w hwN
    · intro hy w hwN
      rw [hw w hwN, hj]
      exact hy w hwN
  -- Two bad events are joined when their closed out-neighbourhoods meet.
  obtain ⟨Nb, hNbdef⟩ : ∃ Nb : V → Finset V, ∀ u w,
      (w ∈ Nb u ↔ w ≠ u ∧ (insert u (N u) ∩ insert w (N w)).Nonempty) :=
    ⟨fun u => univ.filter fun w => w ≠ u ∧ (insert u (N u) ∩ insert w (N w)).Nonempty, by simp⟩
  have hNdep : IsDependencyGraph (uniformColorOn (ZMod k) V) A Nb := by
    intro i s hs g
    refine measure_pi_inter_eq_mul
      (fun _ : V => ProbabilityTheory.uniformOn (Set.univ : Set (ZMod k)))
      (insert i (N i)) (A i) (pattern A s g) (hAinv i) ?_
    intro x y hxy
    have hj : ∀ j ∈ s,
        (x ∈ (if g j then A j else (A j)ᶜ) ↔ y ∈ (if g j then A j else (A j)ᶜ)) := by
      intro j hjs
      obtain ⟨hjne, hjN⟩ := hs j hjs
      have hdisj : Disjoint (insert i (N i)) (insert j (N j)) := by
        by_contra hcon
        exact hjN ((hNbdef i j).2 ⟨hjne, Finset.not_disjoint_iff_nonempty_inter.1 hcon⟩)
      have hiff := hAinv j x y fun a ha =>
        hxy a fun hai => (Finset.disjoint_left.1 hdisj hai) ha
      by_cases hg : g j
      · rw [if_pos hg]; exact hiff
      · rw [if_neg hg]; exact not_congr hiff
    simp only [pattern, Set.mem_iInter]
    exact ⟨fun hh j hjs => (hj j hjs).1 (hh j hjs), fun hh j hjs => (hj j hjs).2 (hh j hjs)⟩
  -- Every bad event has probability exactly `(1 - 1/k) ^ d`.
  have hp : ∀ u, (uniformColorOn (ZMod k) V (A u)).toReal ≤ (1 - 1 / (k : ℝ)) ^ d := by
    intro u
    refine le_of_eq ?_
    rw [hAdef u, uniformColorOn_forall_ne_succ_toReal u (N u) (hNu u), hNcard u]
  have hdcard : ∀ u, (Nb u).card ≤ d + D + d * D := fun u =>
    card_dependents_le G hin hNadj u (hNcard u) (Nb u) fun w hw => (hNbdef u w).1 hw
  have hcond : Real.exp 1 * (1 - 1 / (k : ℝ)) ^ d * (((d + D + d * D : ℕ) : ℝ) + 1) ≤ 1 := by
    have hcast : ((d + D + d * D : ℕ) : ℝ) + 1 = (1 + (d : ℝ)) * (1 + (D : ℝ)) := by
      push_cast
      ring
    rw [hcast]
    exact exp_mul_pow_mul_le_one_of_log_le h
  have hposm := lovasz_local_lemma_symmetric (μ := uniformColorOn (ZMod k) V)
    A hAmeas Nb hNdep hp hdcard hcond
  -- A labelling of positive-measure support avoids every bad event.
  rcases Set.eq_empty_or_nonempty (⋂ u, (A u)ᶜ) with hempty | ⟨x, hx⟩
  · rw [hempty] at hposm
    simp at hposm
  refine ⟨x, fun u => ?_⟩
  simp only [Set.mem_iInter, Set.mem_compl_iff] at hx
  by_contra hcon
  exact hx u ((hAmem u x).2 fun w hw hxw => hcon ⟨w, hNadj u w hw, hxw⟩)

/-- **Theorem 6.4.3** (Alon–Linial 1989): a digraph with minimum out-degree `d` and maximum
in-degree `D` has a directed cycle whose length is divisible by `k`, as soon as
`k (1 + log (1 + d D)) ≤ d`.

The hypothesis is satisfiable: in the `d`-regular case the least admissible `d` is
`5, 13, 22, 43` for `k = 1, 2, 3, 5`. -/
theorem exists_directed_cycle_length_dvd {k : ℕ} [NeZero k] [Nonempty V] (G : Digraph V)
    [DecidableRel G.Adj] {d D : ℕ}
    (hout : ∀ u : V, d ≤ (univ.filter fun w => G.Adj u w).card)
    (hin : ∀ w : V, (univ.filter fun u => G.Adj u w).card ≤ D)
    (hloop : ∀ u : V, ¬ G.Adj u u)
    (h : (k : ℝ) * (1 + Real.log ((1 + d) * (1 + D))) ≤ d) :
    ∃ m : ℕ, k ∣ m ∧ HasDirectedCycleOfLength G m := by
  -- The local lemma supplies a labelling in which every vertex has a successor.
  obtain ⟨x, hx⟩ := exists_labelling_forall_exists_succ G hout hin hloop h
  choose f hadj hsucc using hx
  -- Iterating `f` on a finite vertex set must close up into a cycle.
  obtain ⟨m, v, hmpos, hstep, hper, hinj⟩ := exists_periodic_orbit f
  refine ⟨m, ?_, v, ⟨hmpos, fun i => ?_, hper, hinj⟩⟩
  · -- Each step raises the label by one, so after `i` steps it has risen by `i`.
    have key : ∀ i : ℕ, x (v i) = x (v 0) + (i : ZMod k) := by
      intro i
      induction i with
      | zero => simp
      | succ n ih =>
          rw [hstep n, hsucc, ih]
          push_cast
          ring
    have h0 : v m = v 0 := by simpa using hper 0
    have hkey := key m
    rw [h0] at hkey
    -- One full turn returns to the start, so the total rise `m` is zero in `ZMod k`.
    have hm : x (v 0) + (m : ZMod k) = x (v 0) + 0 := by rw [add_zero, ← hkey]
    exact (ZMod.natCast_eq_zero_iff m k).mp (add_left_cancel hm)
  · rw [hstep i]
    exact hadj (v i)

end AlonLinial

end ProbMethodCombinatorics
