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

/-- **A vertex-minimal non-3-colourable induced subgraph has minimum degree at least 3.**
If some vertex had at most two neighbours inside `T`, a 3-colouring of `T` without it would
extend by a colour avoiding those neighbours.

Pure graph theory — the combinatorial input to Lemma 9.3.5, with no probability in it. -/
theorem three_le_card_neighbors_of_minimal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (hT : ¬ (SimpleGraph.induce (T : Set V) G).Colorable 3)
    (hmin : ∀ x ∈ T, (SimpleGraph.induce ((T.erase x : Finset V) : Set V) G).Colorable 3) :
    ∀ x ∈ T, 3 ≤ ((T.erase x).filter fun y => G.Adj x y).card := by
  sorry

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

/-! ### The random variable

`measure_sub_integral_ge_le` bounds a function of independent coordinates, and
`binomialRandom_eq_map_graphOfExposure` presents `G(n, p)` as the vertex-exposure product.  The
chromatic number itself is a bad choice of function for what follows, because knowing it is
concentrated says nothing about *where*.  The Shamir–Spencer variable is

    `deletionNumber u G` = least `|S|` with `G - S` `u`-colourable,

which is `0` exactly when `G` is `u`-colourable, so a lower bound on `ℙ(χ ≤ u)` becomes an upper
bound on its mean, and the upper tail then pins the variable itself.
-/

/-- Restricting a colouring of an induced subgraph to a smaller vertex set, along an adjacency
that is allowed to change outside that set.

Both moves in one lemma: `B ⊆ A` shrinks the vertex set, and `hadj` lets the ambient graph be
rewired anywhere outside `B`. -/
private theorem colorable_induce_of_subset_of_adj {V : Type*} {G G' : SimpleGraph V}
    {A B : Set V} (hBA : B ⊆ A) (hadj : ∀ a ∈ B, ∀ b ∈ B, (G.Adj a b ↔ G'.Adj a b)) {u : ℕ}
    (h : (SimpleGraph.induce A G).Colorable u) : (SimpleGraph.induce B G').Colorable u := by
  obtain ⟨c⟩ := h
  exact ⟨SimpleGraph.Coloring.mk (fun x => c ⟨x.1, hBA x.2⟩) fun {a b} hab =>
    c.valid ((hadj a.1 a.2 b.1 b.2).mpr hab)⟩

/-- **Colouring a graph from a vertex set and its complement.**  A `u`-colouring of `G - S` and a
`k`-colouring of `G[S]` combine to a `(u + k)`-colouring of `G`, because the two palettes are
kept disjoint: the colours are taken in `Fin u ⊕ Fin k`, whose cardinality is `u + k`.

This is the last step of Theorem 9.3.4: `u` colours outside the deleted set, three inside. -/
private theorem colorable_add_of_induce {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {u k : ℕ} (h1 : (SimpleGraph.induce ((S : Set V)ᶜ) G).Colorable u)
    (h2 : (SimpleGraph.induce (S : Set V) G).Colorable k) : G.Colorable (u + k) := by
  obtain ⟨c1⟩ := h1
  obtain ⟨c2⟩ := h2
  have key : G.Coloring (Fin u ⊕ Fin k) := by
    refine SimpleGraph.Coloring.mk
      (fun v => if h : v ∈ S then Sum.inr (c2 ⟨v, by simpa using h⟩)
        else Sum.inl (c1 ⟨v, by simpa using h⟩)) ?_
    intro a b hab
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
      simp only [ha, hb, dif_pos, dif_neg, ne_eq, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq,
        not_false_eq_true]
    · exact c2.valid hab
    · exact c1.valid hab
  simpa using key.colorable

/-- `ℕ∞.toNat` is faithful on the chromatic numbers of graphs on `Fin n`, because `Fin n` is
finite and every such chromatic number is below `⊤`. -/
private theorem colorable_of_chromaticNumber_toNat_le {n u : ℕ} {G : SimpleGraph (Fin n)}
    (h : G.chromaticNumber.toNat ≤ u) : G.Colorable u := by
  have htop : G.chromaticNumber ≠ ⊤ :=
    SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨n, by simpa using G.colorable_of_fintype⟩
  refine SimpleGraph.chromaticNumber_le_iff_colorable.mp ?_
  rw [← ENat.natCast_toNat htop]
  exact_mod_cast h

/-- The converse direction of `colorable_of_chromaticNumber_toNat_le`, which needs no finiteness:
`ENat.toNat` is monotone against a natural number bound. -/
private theorem chromaticNumber_toNat_le_of_colorable {n u : ℕ} {G : SimpleGraph (Fin n)}
    (h : G.Colorable u) : G.chromaticNumber.toNat ≤ u :=
  ENat.toNat_le_of_le_natCast h.chromaticNumber_le

/-- **The Shamir–Spencer random variable.**  `deletionNumber u G` is the least size of a vertex
set whose removal leaves `G` `u`-colourable.

It is finite because deleting everything works, it vanishes exactly when `G` is `u`-colourable,
and — unlike the chromatic number — it moves by at most `1` when the edges at a single vertex are
rewired, since that one vertex can simply be added to the deleted set. -/
private noncomputable def deletionNumber (u : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ S : Finset (Fin n), S.card = k ∧
    (SimpleGraph.induce ((S : Set (Fin n))ᶜ) G).Colorable u}

/-- Deleting every vertex leaves the empty graph, which is `u`-colourable for every `u`; so the
set `deletionNumber` minimises over is nonempty and the infimum is attained. -/
private theorem nonempty_setOf_deletion (u : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    {k | ∃ S : Finset (Fin n), S.card = k ∧
      (SimpleGraph.induce ((S : Set (Fin n))ᶜ) G).Colorable u}.Nonempty := by
  refine ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, rfl, ?_⟩
  have : IsEmpty (((Finset.univ : Finset (Fin n)) : Set (Fin n))ᶜ : Set (Fin n)) := by
    refine ⟨fun x => ?_⟩
    have hx := x.2
    simp at hx
  exact SimpleGraph.Colorable.of_isEmpty u

/-- The minimum in `deletionNumber` is attained: there really is a deletion set of that size. -/
private theorem deletionNumber_spec (u : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), S.card = deletionNumber u G ∧
      (SimpleGraph.induce ((S : Set (Fin n))ᶜ) G).Colorable u :=
  Nat.sInf_mem (nonempty_setOf_deletion u G)

/-- Any successful deletion set bounds `deletionNumber` above. -/
private theorem deletionNumber_le (u : ℕ) {n : ℕ} {G : SimpleGraph (Fin n)} (S : Finset (Fin n))
    (hS : (SimpleGraph.induce ((S : Set (Fin n))ᶜ) G).Colorable u) :
    deletionNumber u G ≤ S.card :=
  Nat.sInf_le ⟨S, rfl, hS⟩

/-- **`deletionNumber u G = 0` exactly when `G` is `u`-colourable.**  This is the bridge between
the random variable and the event the theorem is about. -/
private theorem deletionNumber_eq_zero_iff (u : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) :
    deletionNumber u G = 0 ↔ G.Colorable u := by
  constructor
  · intro h
    obtain ⟨S, hS, hcol⟩ := deletionNumber_spec u G
    rw [h, Finset.card_eq_zero] at hS
    subst hS
    rw [show ((∅ : Finset (Fin n)) : Set (Fin n))ᶜ = Set.univ from by simp] at hcol
    obtain ⟨c⟩ := hcol
    exact ⟨SimpleGraph.Coloring.mk (fun v => c ⟨v, Set.mem_univ v⟩) fun {a b} hab => c.valid hab⟩
  · intro h
    refine Nat.le_zero.mp ?_
    have hz := deletionNumber_le u (G := G) ∅
      (colorable_induce_of_subset_of_adj (A := Set.univ) (fun x _ => Set.mem_univ x)
        (fun a _ b _ => Iff.rfl) (by
          obtain ⟨c⟩ := h
          exact ⟨SimpleGraph.Coloring.mk (fun x => c x.1) fun {a b} hab => c.valid hab⟩))
    simpa using hz

/-- **Rewiring one vertex moves the deletion number by at most one.**  Add `v` to an optimal
deletion set for `G`: outside the enlarged set the two graphs agree, so the old colouring still
works.

This is the bounded-differences input, and it is where `deletionNumber` beats the chromatic
number — the repair is available for *every* `u`, uniformly. -/
private theorem deletionNumber_le_succ_of_adj_off {u n : ℕ} (v : Fin n)
    (G G' : SimpleGraph (Fin n))
    (h : ∀ a b : Fin n, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)) :
    deletionNumber u G' ≤ deletionNumber u G + 1 := by
  classical
  obtain ⟨S, hS, hcol⟩ := deletionNumber_spec u G
  have hsub : ((insert v S : Finset (Fin n)) : Set (Fin n))ᶜ ⊆ ((S : Set (Fin n)))ᶜ := by
    intro x hx
    simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff] at hx ⊢
    exact fun hc => hx (Or.inr hc)
  have hadj : ∀ a ∈ ((insert v S : Finset (Fin n)) : Set (Fin n))ᶜ,
      ∀ b ∈ ((insert v S : Finset (Fin n)) : Set (Fin n))ᶜ, (G.Adj a b ↔ G'.Adj a b) := by
    intro a ha b hb
    simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or] at ha hb
    exact h a b ha.1 hb.1
  calc deletionNumber u G'
      ≤ (insert v S).card :=
        deletionNumber_le u (insert v S) (colorable_induce_of_subset_of_adj hsub hadj hcol)
    _ ≤ S.card + 1 := Finset.card_insert_le _ _
    _ = deletionNumber u G + 1 := by rw [hS]

/-- The two-sided form of `deletionNumber_le_succ_of_adj_off`, in the shape the bounded
differences inequality wants. -/
private theorem abs_sub_deletionNumber_le_one {u n : ℕ} (v : Fin n) (G G' : SimpleGraph (Fin n))
    (h : ∀ a b : Fin n, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)) :
    |(deletionNumber u G : ℝ) - (deletionNumber u G' : ℝ)| ≤ 1 := by
  have h₁ := deletionNumber_le_succ_of_adj_off (u := u) v G G' h
  have h₂ := deletionNumber_le_succ_of_adj_off (u := u) v G' G fun a b ha hb => (h a b ha hb).symm
  have h₁' : (deletionNumber u G' : ℝ) ≤ (deletionNumber u G : ℝ) + 1 := by exact_mod_cast h₁
  have h₂' : (deletionNumber u G : ℝ) ≤ (deletionNumber u G' : ℝ) + 1 := by exact_mod_cast h₂
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Three extra colours suffice.**  If some set of at most `C` vertices can be deleted to leave
`G` `u`-colourable, and every set of at most `C` vertices induces a 3-colourable subgraph, then
`G` is `(u + 3)`-colourable. -/
private theorem chromaticNumber_toNat_le_add_three {n u : ℕ} {G : SimpleGraph (Fin n)} {C : ℝ}
    (h1 : (deletionNumber u G : ℝ) ≤ C)
    (h2 : ∀ T : Finset (Fin n), (T.card : ℝ) ≤ C →
      (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3) :
    G.chromaticNumber.toNat ≤ u + 3 := by
  classical
  obtain ⟨S, hS, hcol⟩ := deletionNumber_spec u G
  exact chromaticNumber_toNat_le_of_colorable
    (colorable_add_of_induce hcol (h2 S (by rw [hS]; exact h1)))

/-! ### Concentration of the deletion number

The vertex-exposure product of `Concentration.lean`, run with `deletionNumber` in place of the
chromatic number.  Every step is the same as in `measure_abs_sub_integral_chromaticNumber_ge_le`;
only the Lipschitz lemma differs.
-/

/-- Adjacency in an assembled vertex-exposure sample, read off the block of the larger
endpoint. -/
private theorem adj_graphOfExposure_iff_lt {n : ℕ} (x : ∀ i, ExposureBlock n i) {a b : Fin n}
    (h : a < b) : (graphOfExposure x).Adj a b ↔ x b ⟨a, h⟩ := by
  simp only [graphOfExposure, SimpleGraph.fromRel_adj, ne_eq, dif_pos h, dif_neg (asymm h)]
  simp [h.ne]

/-- Assembling a graph from its vertex-exposure blocks is measurable: each adjacency is a single
coordinate of a single block. -/
private theorem measurable_graphOfExposure {n : ℕ} :
    Measurable (graphOfExposure : (∀ i, ExposureBlock n i) → SimpleGraph (Fin n)) := by
  rw [SimpleGraph.measurable_iff_adj]
  intro a b
  rcases lt_trichotomy a b with h | rfl | h
  · rw [show (fun x : ∀ i, ExposureBlock n i => (graphOfExposure x).Adj a b)
        = fun x => x b ⟨a, h⟩ from funext fun x => propext (adj_graphOfExposure_iff_lt x h)]
    exact (measurable_pi_apply _).comp (measurable_pi_apply b)
  · simp [graphOfExposure]
  · rw [show (fun x : ∀ i, ExposureBlock n i => (graphOfExposure x).Adj a b)
        = fun x => x a ⟨b, h⟩ from funext fun x =>
          propext ((SimpleGraph.adj_comm _ _ _).trans (adj_graphOfExposure_iff_lt x h))]
    exact (measurable_pi_apply _).comp (measurable_pi_apply a)

/-- Block `0` of the vertex-exposure product carries no information: its index type is empty. -/
private theorem eq_of_exposureBlock_zero {n : ℕ} {i : Fin n} (hi : (i : ℕ) = 0)
    (a b : ExposureBlock n i) : a = b := by
  have he : IsEmpty {j : Fin n // j < i} := by
    refine ⟨fun j => ?_⟩
    have hj := j.2
    rw [Fin.lt_def, hi] at hj
    omega
  exact funext fun j => he.elim j

/-- The vertex-exposure weights sum to `n - 1`: every block but the empty block `0` contributes
`1`.  This is the `∑ i, c i ^ 2` of the bounded differences inequality. -/
private theorem sum_sq_exposureWeight_aux (n : ℕ) (hn : 1 ≤ n) :
    ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 = (n : ℝ) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  simp

/-- **The one-sided bounded differences inequality for `G(n, p)`.**  Any graph parameter that
moves by at most `1` when the edges at one vertex are rewired satisfies

    ℙ(f - 𝔼f ≥ lam √(n-1)) ≤ exp (-2 lam²).

This is Theorem 9.3.1's proof with the chromatic number replaced by an arbitrary vertex-Lipschitz
`f`; measurability is automatic because `SimpleGraph (Fin n)` is discrete. -/
private theorem measure_sub_integral_graph_ge_le {n : ℕ} (hn : 2 ≤ n) (p : I)
    (f : SimpleGraph (Fin n) → ℝ)
    (hbd : ∀ (v : Fin n) (G G' : SimpleGraph (Fin n)),
      (∀ a b : Fin n, a ≠ v → b ≠ v → (G.Adj a b ↔ G'.Adj a b)) → |f G - f G'| ≤ 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | lam * Real.sqrt ((n : ℝ) - 1)
          ≤ f G - ∫ K, f K ∂(SimpleGraph.binomialRandom (Fin n) p)}
      ≤ Real.exp (-2 * lam ^ 2) := by
  classical
  have hb : IsProbabilityMeasure ((toNNReal p) • Measure.dirac True
      + (toNNReal (σ p)) • Measure.dirac False) := ⟨by simp⟩
  have hpr : ∀ i : Fin n, IsProbabilityMeasure (exposureMeasure n p i) := fun i =>
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {j : Fin n // j < i} =>
      (toNNReal p) • Measure.dirac True + (toNNReal (σ p)) • Measure.dirac False))
  have hfm : Measurable f := Measurable.of_discrete
  have hF : Measurable fun x : ∀ i : Fin n, ExposureBlock n i => f (graphOfExposure x) :=
    hfm.comp measurable_graphOfExposure
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcsum : ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 = (n : ℝ) - 1 :=
    sum_sq_exposureWeight_aux n (by omega)
  have hsum : 0 < ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 := hcsum ▸ hn1
  have hlam' : 0 ≤ lam * Real.sqrt ((n : ℝ) - 1) := mul_nonneg hlam (Real.sqrt_nonneg _)
  have hc : ∀ i : Fin n, ∀ x y : ∀ j, ExposureBlock n j, (∀ j, j ≠ i → x j = y j) →
      |f (graphOfExposure x) - f (graphOfExposure y)|
        ≤ if (i : ℕ) = 0 then (0 : ℝ) else 1 := by
    intro i x y h
    by_cases hi : (i : ℕ) = 0
    · have hxy : x = y := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · exact eq_of_exposureBlock_zero hi _ _
        · exact h j hj
      rw [hxy, if_pos hi]
      simp
    · rw [if_neg hi]
      refine hbd i _ _ fun a b ha hb => ?_
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [adj_graphOfExposure_iff_lt x hab, adj_graphOfExposure_iff_lt y hab, h b hb]
      · simp
      · rw [SimpleGraph.adj_comm (graphOfExposure x), SimpleGraph.adj_comm (graphOfExposure y),
          adj_graphOfExposure_iff_lt x hab, adj_graphOfExposure_iff_lt y hab, h a ha]
  have hstep : (SimpleGraph.binomialRandom (Fin n) p).real
      {G : SimpleGraph (Fin n) | lam * Real.sqrt ((n : ℝ) - 1)
        ≤ f G - ∫ K, f K ∂(SimpleGraph.binomialRandom (Fin n) p)}
      = (Measure.pi (exposureMeasure n p)).real
          {x | lam * Real.sqrt ((n : ℝ) - 1)
            ≤ f (graphOfExposure x)
                - ∫ y, f (graphOfExposure y) ∂(Measure.pi (exposureMeasure n p))} := by
    rw [binomialRandom_eq_map_graphOfExposure n p,
      integral_map measurable_graphOfExposure.aemeasurable hfm.aestronglyMeasurable,
      map_measureReal_apply measurable_graphOfExposure MeasurableSet.of_discrete,
      Set.preimage_ofPred_eq]
  rw [hstep]
  have hmain := measure_sub_integral_ge_le (exposureMeasure n p)
    (fun x => f (graphOfExposure x))
    (fun i : Fin n => if (i : ℕ) = 0 then (0 : ℝ) else 1) hF hc hsum hlam'
  have hexp : -2 * (lam * Real.sqrt ((n : ℝ) - 1)) ^ 2
      / ∑ i : Fin n, (if (i : ℕ) = 0 then (0 : ℝ) else 1) ^ 2 = -2 * lam ^ 2 := by
    rw [hcsum, mul_pow, Real.sq_sqrt hn1.le]
    field_simp
  rw [hexp] at hmain
  exact hmain

/-- The upper tail of the deletion number. -/
private theorem measure_deletionNumber_sub_mean_ge_le (u : ℕ) {n : ℕ} (hn : 2 ≤ n) (p : I)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | lam * Real.sqrt ((n : ℝ) - 1)
          ≤ (deletionNumber u G : ℝ)
            - ∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p)}
      ≤ Real.exp (-2 * lam ^ 2) :=
  measure_sub_integral_graph_ge_le hn p (fun G => (deletionNumber u G : ℝ))
    (fun v G G' h => abs_sub_deletionNumber_le_one v G G' h) hlam

/-- The lower tail of the deletion number: `-deletionNumber u` has the same bounded differences
and the negated mean. -/
private theorem measure_mean_sub_deletionNumber_ge_le (u : ℕ) {n : ℕ} (hn : 2 ≤ n) (p : I)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | lam * Real.sqrt ((n : ℝ) - 1)
          ≤ (∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
            - (deletionNumber u G : ℝ)}
      ≤ Real.exp (-2 * lam ^ 2) := by
  have h := measure_sub_integral_graph_ge_le hn p (fun G => -(deletionNumber u G : ℝ))
    (fun v G G' hgg => by
      have h1 := abs_sub_deletionNumber_le_one (u := u) v G' G
        fun x y hx hy => (hgg x y hx hy).symm
      rw [show -(deletionNumber u G : ℝ) - -(deletionNumber u G' : ℝ)
        = (deletionNumber u G' : ℝ) - (deletionNumber u G : ℝ) from by ring]
      exact h1) hlam
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq, integral_neg]
  constructor <;> intro hG <;> linarith

/-! ### Choosing the level `u`

`u` is the least level whose probability is not negligible.  Membership gives the lower bound
that forces the mean of the deletion number down; minimality gives `ℙ(χ < u) ≤ ε` directly, which
is the third of the three events.
-/

/-- Well-ordering of `ℕ`, in the form used to choose the level `u`. -/
private theorem exists_least_mem {T : Set ℕ} (hne : T.Nonempty) :
    ∃ u, u ∈ T ∧ ∀ k < u, k ∉ T :=
  ⟨sInf T, Nat.sInf_mem hne, fun _k hk hmem => absurd (Nat.sInf_le hmem) (not_le.mpr hk)⟩

/-- **The least non-negligible level.**  There is a `u` with `ℙ(χ ≤ u) > ε` and `ℙ(χ < u) ≤ ε`.

The set of admissible levels is nonempty because every graph on `Fin n` is `n`-colourable, so
`u = n` has probability `1 > ε`. -/
private theorem exists_chromaticNumber_level {n : ℕ} (p : I) {eps : ℝ} (heps0 : 0 ≤ eps)
    (heps1 : eps < 1) :
    ∃ u : ℕ, eps < (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat ≤ u}
      ∧ (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat < u} ≤ eps := by
  have hTne : {k : ℕ | eps < (SimpleGraph.binomialRandom (Fin n) p).real
      {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat ≤ k}}.Nonempty := by
    refine ⟨n, ?_⟩
    have huniv : {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat ≤ n} = Set.univ :=
      Set.eq_univ_of_forall fun G =>
        chromaticNumber_toNat_le_of_colorable (by simpa using G.colorable_of_fintype)
    show eps < _
    rw [huniv, probReal_univ]
    exact heps1
  obtain ⟨u, hmem, hmin⟩ := exists_least_mem hTne
  refine ⟨u, hmem, ?_⟩
  rcases Nat.eq_zero_or_pos u with rfl | hpos
  · rw [show {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat < 0} = ∅ from by ext G; simp]
    simpa using heps0
  · obtain ⟨m, rfl⟩ : ∃ m, u = m + 1 := ⟨u - 1, by omega⟩
    rw [show {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat < m + 1}
        = {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat ≤ m} from by ext G; simp]
    exact not_lt.mp (hmin m (by omega))

/-- **The mean deletion number is at most `lam √(n-1)`.**  The lower tail at radius `𝔼Y` gives

    ε < ℙ(χ ≤ u) = ℙ(Y = 0) ≤ exp (-2 (𝔼Y)² / (n-1)),

and `exp (-2 lam²) = ε` turns that into `𝔼Y < lam √(n-1)`.  This is the step that converts a
statement about *where* the chromatic number is into a bound on the size of the set that has to
be deleted. -/
private theorem integral_deletionNumber_lt (u : ℕ) {n : ℕ} (hn : 2 ≤ n) (p : I) {eps lam : ℝ}
    (hlam : 0 < lam) (hexp : Real.exp (-2 * lam ^ 2) = eps)
    (hcol : eps < (SimpleGraph.binomialRandom (Fin n) p).real
      {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat ≤ u}) :
    (∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
      < lam * Real.sqrt ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hm0 : 0 ≤ ∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p) :=
    integral_nonneg fun K => by positivity
  have htail := measure_mean_sub_deletionNumber_ge_le u hn p
    (lam := (∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
      / Real.sqrt ((n : ℝ) - 1)) (div_nonneg hm0 hspos.le)
  have hset : {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat ≤ u}
      ⊆ {G : SimpleGraph (Fin n) |
          ((∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
              / Real.sqrt ((n : ℝ) - 1)) * Real.sqrt ((n : ℝ) - 1)
            ≤ (∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
              - (deletionNumber u G : ℝ)} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    rw [div_mul_cancel₀ _ (ne_of_gt hspos),
      (deletionNumber_eq_zero_iff u G).mpr (colorable_of_chromaticNumber_toNat_le hG)]
    simp
  have hlt := lt_of_lt_of_le hcol (le_trans (measureReal_mono hset) htail)
  rw [← hexp] at hlt
  have hq := Real.exp_lt_exp.mp hlt
  have hq2 : ((∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
      / Real.sqrt ((n : ℝ) - 1)) ^ 2 < lam ^ 2 := by linarith
  have hdiv := lt_of_pow_lt_pow_left₀ 2 hlam.le hq2
  calc (∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
      = ((∫ K, (deletionNumber u K : ℝ) ∂(SimpleGraph.binomialRandom (Fin n) p))
          / Real.sqrt ((n : ℝ) - 1)) * Real.sqrt ((n : ℝ) - 1) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hspos)]
    _ < lam * Real.sqrt ((n : ℝ) - 1) := mul_lt_mul_of_pos_right hdiv hspos

/-- **The union bound over three failures.**  If three events each fail with probability at most
`ε` and their intersection is contained in `D`, then `D` has probability at least `1 - 3 ε`. -/
private theorem one_sub_three_le_measureReal {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {A B C D : Set α} {eps : ℝ} (hABC : A ∩ B ∩ C ⊆ D)
    (hA : μ.real Aᶜ ≤ eps) (hB : μ.real Bᶜ ≤ eps) (hC : μ.real Cᶜ ≤ eps) :
    1 - 3 * eps ≤ μ.real D := by
  have h1 : μ.real (A ∩ B ∩ C)ᶜ ≤ 3 * eps := by
    rw [show (A ∩ B ∩ C)ᶜ = Aᶜ ∪ Bᶜ ∪ Cᶜ from by simp [Set.compl_inter]]
    have hab := measureReal_union_le (μ := μ) Aᶜ Bᶜ
    have habc := measureReal_union_le (μ := μ) (Aᶜ ∪ Bᶜ) Cᶜ
    linarith
  have h2 : μ.real (A ∩ B ∩ C)ᶜ = 1 - μ.real (A ∩ B ∩ C) := by
    rw [measureReal_compl MeasurableSet.of_discrete, probReal_univ]
  have h3 : μ.real (A ∩ B ∩ C) ≤ μ.real D := measureReal_mono hABC
  linarith

/-- **Theorem 9.3.4** (Shamir–Spencer 1987): for `α > 5/6` and `p ≤ n ^ (-α)`, the chromatic
number of `G(n, p)` is concentrated on four consecutive values. -/
theorem exists_chromaticNumber_four_values {a δ : ℝ} (ha : 5 / 6 < a) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ p : I, (p : ℝ) ≤ (n : ℝ) ^ (-a) →
      ∃ u : ℕ, 1 - δ ≤ (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) |
          u ≤ G.chromaticNumber.toNat ∧ G.chromaticNumber.toNat ≤ u + 3} := by
  classical
  -- `δ ≥ 1` makes the claim vacuous: a measure is never negative.
  by_cases hδ1 : δ < 1
  swap
  · exact ⟨0, fun n _ p _ => ⟨0, le_trans (by linarith [not_lt.mp hδ1]) measureReal_nonneg⟩⟩
  -- Three events will each fail with probability at most `δ / 3`.
  have heps0 : 0 < δ / 3 := by linarith
  have heps1 : δ / 3 < 1 := by linarith
  have hlogneg : Real.log (δ / 3) < 0 := Real.log_neg heps0 heps1
  -- `lam` is chosen so that the Gaussian tail `exp (-2 lam²)` is exactly `δ / 3`.
  set lam : ℝ := Real.sqrt (-Real.log (δ / 3) / 2) with hlamdef
  have hlamsq : lam ^ 2 = -Real.log (δ / 3) / 2 := by
    rw [hlamdef]; exact Real.sq_sqrt (by linarith)
  have hlampos : 0 < lam := by
    rw [hlamdef]; exact Real.sqrt_pos.mpr (by linarith)
  have hexplam : Real.exp (-2 * lam ^ 2) = δ / 3 := by
    rw [hlamsq, show -2 * (-Real.log (δ / 3) / 2) = Real.log (δ / 3) from by ring,
      Real.exp_log heps0]
  -- Lemma 9.3.5 at radius `C = 2 lam`, which is the radius the upper tail will produce.
  obtain ⟨N₁, hN₁⟩ :=
    forall_small_induced_threeColorable ha (show (0 : ℝ) < 2 * lam by linarith) heps0
  refine ⟨max N₁ 2, fun n hn p hp => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right N₁ 2) hn
  have hnN1 : N₁ ≤ n := le_trans (le_max_left N₁ 2) hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hsle : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by linarith)
  -- `u` is the least level whose probability is not negligible.
  obtain ⟨u, hu, humin⟩ := exists_chromaticNumber_level (n := n) p heps0.le heps1
  refine ⟨u, ?_⟩
  have hmean := integral_deletionNumber_lt u hn2 p hlampos hexplam hu
  -- First event: a set of at most `2 lam √n` vertices can be deleted to leave `G`
  -- `u`-colourable.  The mean is below `lam √(n-1)`, so the upper tail at radius `lam √(n-1)`
  -- already reaches `2 lam √(n-1) ≤ 2 lam √n`.
  have hE1 : (SimpleGraph.binomialRandom (Fin n) p).real
      {G : SimpleGraph (Fin n) | (deletionNumber u G : ℝ) ≤ 2 * lam * Real.sqrt (n : ℝ)}ᶜ
        ≤ δ / 3 := by
    refine le_trans (le_trans (measureReal_mono ?_)
      (measure_deletionNumber_sub_mean_ge_le u hn2 p hlampos.le)) (le_of_eq hexplam)
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hG ⊢
    have h1 : 2 * lam * Real.sqrt ((n : ℝ) - 1) ≤ 2 * lam * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsle (by linarith)
    have h2 : 2 * lam * Real.sqrt ((n : ℝ) - 1)
        = lam * Real.sqrt ((n : ℝ) - 1) + lam * Real.sqrt ((n : ℝ) - 1) := by ring
    linarith
  -- Second event: every set of at most `2 lam √n` vertices induces a 3-colourable subgraph.
  have hE2 : (SimpleGraph.binomialRandom (Fin n) p).real
      {G : SimpleGraph (Fin n) | ∀ T : Finset (Fin n), (T.card : ℝ) ≤ 2 * lam * Real.sqrt n →
        (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3}ᶜ ≤ δ / 3 := by
    have h := hN₁ n hnN1 p hp
    rw [measureReal_compl MeasurableSet.of_discrete, probReal_univ]
    linarith
  -- Third event: the chromatic number is at least `u`, by minimality of `u`.
  have hE3 : (SimpleGraph.binomialRandom (Fin n) p).real
      {G : SimpleGraph (Fin n) | u ≤ G.chromaticNumber.toNat}ᶜ ≤ δ / 3 := by
    rw [show {G : SimpleGraph (Fin n) | u ≤ G.chromaticNumber.toNat}ᶜ
        = {G : SimpleGraph (Fin n) | G.chromaticNumber.toNat < u} from by
      ext G; simp [Set.mem_compl_iff]]
    exact humin
  -- On all three at once, `u ≤ χ(G) ≤ u + 3`.
  have hincl : {G : SimpleGraph (Fin n) | (deletionNumber u G : ℝ) ≤ 2 * lam * Real.sqrt (n : ℝ)}
      ∩ {G : SimpleGraph (Fin n) | ∀ T : Finset (Fin n),
          (T.card : ℝ) ≤ 2 * lam * Real.sqrt n →
          (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3}
      ∩ {G : SimpleGraph (Fin n) | u ≤ G.chromaticNumber.toNat}
      ⊆ {G : SimpleGraph (Fin n) |
          u ≤ G.chromaticNumber.toNat ∧ G.chromaticNumber.toNat ≤ u + 3} := by
    rintro G ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, chromaticNumber_toNat_le_add_three h1 h2⟩
  have hfin := one_sub_three_le_measureReal (SimpleGraph.binomialRandom (Fin n) p)
    hincl hE1 hE2 hE3
  linarith

end ProbMethodCombinatorics
