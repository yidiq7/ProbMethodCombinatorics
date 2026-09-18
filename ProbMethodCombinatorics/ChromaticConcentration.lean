import ProbMethodCombinatorics.Concentration

/-!
# Section 9.3: four-value concentration of the chromatic number

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 9.3.4 (Shamir–Spencer
1987): for fixed `α > 5/6` and `p ≤ n ^ (-α)`, the chromatic number of `G(n, p)` is
concentrated on four values.

The vertex-exposure machinery this needs is already in `Concentration.lean` — the same
`measure_sub_integral_ge_le` that gave Theorem 9.3.1.  The random variable is different and
cleverer: `Y G` is the least size of a vertex set whose removal leaves `G` `u`-colourable, and
it changes by at most `1` when the edges at one vertex change, which the chromatic number
itself does not.

`α > 5/6` is not decoration.  It is exactly the convergence threshold of the union bound in
Lemma 9.3.5: the summand is `O(n ^ (5/4 - 3α/2)) ^ t`, whose exponent is `+0.05` at `α = 0.8`,
exactly `0` at `α = 5/6`, and negative beyond.  The source's strict inequality is necessary.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory unitInterval SimpleGraph

/-- Some colour of `Fin 3` is used by no neighbour of `x` inside `T.erase x`, as soon as `x` has
fewer than three neighbours there. -/
private theorem exists_color_unused_on_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x : V)
    (c : (SimpleGraph.induce ((T.erase x : Finset V) : Set V) G).Coloring (Fin 3))
    (hcard : ((T.erase x).filter fun y => G.Adj x y).card < 3) :
    ∃ b : Fin 3, ∀ (y : V) (hy : y ∈ T.erase x), G.Adj x y → c ⟨y, hy⟩ ≠ b := by
  have hlt : (((T.erase x).filter fun y => G.Adj x y).image
      fun y => if h : y ∈ T.erase x then c ⟨y, h⟩ else 0).card < Fintype.card (Fin 3) := by
    simpa using lt_of_le_of_lt Finset.card_image_le hcard
  obtain ⟨b, hb⟩ : ∃ b : Fin 3, b ∉ ((T.erase x).filter fun y => G.Adj x y).image
      fun y => if h : y ∈ T.erase x then c ⟨y, h⟩ else 0 := by
    by_contra hcon
    exact (Finset.card_lt_iff_ne_univ _).mp hlt
      (Finset.eq_univ_iff_forall.mpr fun b => not_not.mp fun h => hcon ⟨b, h⟩)
  refine ⟨b, fun y hy hadj hcy => hb (Finset.mem_image.mpr ⟨y, ?_, ?_⟩)⟩
  · exact Finset.mem_filter.mpr ⟨hy, hadj⟩
  · show (if h : y ∈ T.erase x then c ⟨y, h⟩ else 0) = b
    rw [dif_pos hy]
    exact hcy

/-- A 3-colouring of the subgraph induced on `T.erase x` extends to one of the subgraph induced
on `T` by giving `x` a colour that none of its neighbours uses. -/
private theorem colorable_three_of_color_unused {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x : V)
    (c : (SimpleGraph.induce ((T.erase x : Finset V) : Set V) G).Coloring (Fin 3)) (b : Fin 3)
    (hb : ∀ (y : V) (hy : y ∈ T.erase x), G.Adj x y → c ⟨y, hy⟩ ≠ b) :
    (SimpleGraph.induce (T : Set V) G).Colorable 3 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if hv : (v : V) = x then b else
    c ⟨(v : V), Finset.mem_erase.mpr ⟨hv, v.2⟩⟩) ?_⟩
  intro u v huv
  have hadj : G.Adj (u : V) (v : V) := huv
  by_cases hu : (u : V) = x
  · have hv : (v : V) ≠ x := fun h => hadj.ne (hu.trans h.symm)
    simp only [dif_pos hu, dif_neg hv]
    refine fun h => hb _ (Finset.mem_erase.mpr ⟨hv, v.2⟩) ?_ h.symm
    rw [← hu]
    exact hadj
  · by_cases hv : (v : V) = x
    · simp only [dif_neg hu, dif_pos hv]
      refine hb _ (Finset.mem_erase.mpr ⟨hu, u.2⟩) ?_
      rw [← hv]
      exact hadj.symm
    · simp only [dif_neg hu, dif_neg hv]
      exact c.valid hadj

/-- **A vertex-minimal non-3-colourable induced subgraph has minimum degree at least 3.**
If some vertex had at most two neighbours inside `T`, a 3-colouring of `T` without it would
extend by a colour avoiding those neighbours.

Pure graph theory — the combinatorial input to Lemma 9.3.5, with no probability in it. -/
theorem three_le_card_neighbors_of_minimal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (hT : ¬ (SimpleGraph.induce (T : Set V) G).Colorable 3)
    (hmin : ∀ x ∈ T, (SimpleGraph.induce ((T.erase x : Finset V) : Set V) G).Colorable 3) :
    ∀ x ∈ T, 3 ≤ ((T.erase x).filter fun y => G.Adj x y).card := by
  intro x hx
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨c⟩ := hmin x hx
  obtain ⟨b, hb⟩ := exists_color_unused_on_neighbors G T x c hlt
  exact hT (colorable_three_of_color_unused G T x c b hb)

/-- **Lemma 9.3.5**: for `p ≤ n ^ (-α)` with `α > 5/6`, with high probability every set of at
most `C √n` vertices of `G(n, p)` induces a 3-colourable subgraph.

A minimal non-3-colourable induced subgraph on `t` vertices has minimum degree `≥ 3` and hence
`≥ 3t/2` edges, and the union bound over such subgraphs converges precisely when `α > 5/6`. -/
theorem forall_small_induced_threeColorable {a C δ : ℝ} (ha : 5 / 6 < a) (hC : 0 < C)
    (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ p : I, (p : ℝ) ≤ (n : ℝ) ^ (-a) →
      1 - δ ≤ (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | ∀ T : Finset (Fin n), (T.card : ℝ) ≤ C * Real.sqrt n →
          (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3} := by
  sorry

/-- **Theorem 9.3.4** (Shamir–Spencer 1987): for `α > 5/6` and `p ≤ n ^ (-α)`, the chromatic
number of `G(n, p)` is concentrated on four consecutive values. -/
theorem exists_chromaticNumber_four_values {a δ : ℝ} (ha : 5 / 6 < a) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ p : I, (p : ℝ) ≤ (n : ℝ) ^ (-a) →
      ∃ u : ℕ, 1 - δ ≤ (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) |
          u ≤ G.chromaticNumber.toNat ∧ G.chromaticNumber.toNat ≤ u + 3} := by
  sorry

end ProbMethodCombinatorics
