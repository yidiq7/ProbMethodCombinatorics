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

/-! ### The union bound of Lemma 9.3.5

The chain of estimates is:

* a vertex-minimal non-3-colourable induced subgraph on `t` vertices carries at least
  `⌈3t/2⌉` edges (`exists_edgeFinset_of_not_colorable`);
* hence the bad event is covered by `binom(n,t) * binom(binom(t,2), ⌈3t/2⌉)` cylinder events
  of probability `p ^ ⌈3t/2⌉` each (`prob_not_forall_small_colorable_le`);
* each such summand is at most `q ^ t` with `q = 3 √C n ^ (5/4 - 3α/2)`
  (`term_sq_le_base_pow`, stated for `q ^ 2` so that no square roots appear in the algebra);
* and `5/4 - 3α/2 < 0` exactly when `α > 5/6`, so `q → 0` and the geometric tail
  `∑_{t ≥ 4} q ^ t ≤ 2 q ^ 4` is eventually below `δ` (`sum_pow_Icc_four_le`).
-/

/-- `e < 3`, from `1 - x ≤ exp (-x)` at `x = 1/10` and `(10/9) ^ 10 < 3`. -/
private theorem exp_one_lt_three : Real.exp 1 < 3 := by
  have h : (9 : ℝ) / 10 ≤ (Real.exp (1 / 10))⁻¹ := by
    have := Real.add_one_le_exp (-(1 / 10) : ℝ)
    rw [Real.exp_neg] at this
    linarith
  have hpos : (0 : ℝ) < Real.exp (1 / 10) := Real.exp_pos _
  have h2 : Real.exp (1 / 10 : ℝ) ≤ 10 / 9 := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  have h3 : Real.exp (1 : ℝ) = Real.exp (1 / 10 : ℝ) ^ 10 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3]
  calc Real.exp (1 / 10 : ℝ) ^ 10 ≤ (10 / 9 : ℝ) ^ 10 := by
        exact pow_le_pow_left₀ hpos.le h2 10
    _ < 3 := by norm_num

/-- `k ^ k ≤ 3 ^ k k!`, the crude Stirling bound the two binomial estimates below need.
Induction on `k`, the step being `(1 + 1/k) ^ k ≤ exp 1 < 3`. -/
private theorem pow_self_le_three_pow_mul_factorial (k : ℕ) :
    (k : ℝ) ^ k ≤ 3 ^ k * (k.factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hstep : ((k : ℝ) + 1) ^ k ≤ 3 * (k : ℝ) ^ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num
      · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
        have h1 : (1 : ℝ) + 1 / k ≤ Real.exp (1 / k) := by
          have := Real.add_one_le_exp (1 / (k : ℝ)); linarith
        have h2 : ((1 : ℝ) + 1 / k) ^ k ≤ Real.exp (1 / (k : ℝ)) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
        have h3 : Real.exp (1 / (k : ℝ)) ^ k = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
        have h5 : ((k : ℝ) + 1) ^ k = (k : ℝ) ^ k * ((1 : ℝ) + 1 / k) ^ k := by
          rw [← mul_pow]
          congr 1
          field_simp
        rw [h3] at h2
        have h6 : ((1 : ℝ) + 1 / k) ^ k ≤ 3 := by
          linarith [exp_one_lt_three]
        rw [h5]
        calc (k : ℝ) ^ k * ((1 : ℝ) + 1 / k) ^ k ≤ (k : ℝ) ^ k * 3 :=
              mul_le_mul_of_nonneg_left h6 (pow_nonneg hk0.le k)
          _ = 3 * (k : ℝ) ^ k := by ring
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast, Nat.factorial_succ]
    push_cast
    have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    calc ((k : ℝ) + 1) ^ (k + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ k := by ring
      _ ≤ ((k : ℝ) + 1) * (3 * (k : ℝ) ^ k) := by
          exact mul_le_mul_of_nonneg_left hstep hk0
      _ ≤ ((k : ℝ) + 1) * (3 * (3 ^ k * (k.factorial : ℝ))) := by
          have : (0:ℝ) ≤ 3 := by norm_num
          nlinarith [ih, pow_nonneg (by norm_num : (0:ℝ) ≤ 3) k,
            Nat.cast_nonneg (α := ℝ) k.factorial]
      _ = 3 ^ (k + 1) * (((k : ℝ) + 1) * (k.factorial : ℝ)) := by ring

/-- `binom(N,k) ≤ (3N/k) ^ k`: `Nat.choose_le_pow_div` gives `N ^ k / k!`, and
`pow_self_le_three_pow_mul_factorial` turns `1/k!` into `(3/k) ^ k`. -/
private theorem choose_le_three_mul_div_pow (N k : ℕ) (hk : 0 < k) :
    (N.choose k : ℝ) ≤ (3 * N / k) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast k.factorial_pos
  calc (N.choose k : ℝ) ≤ (N : ℝ) ^ k / (k.factorial : ℝ) := Nat.choose_le_pow_div k N
    _ ≤ (3 * N / k) ^ k := by
        rw [div_pow, mul_pow, div_le_div_iff₀ hfac (by positivity)]
        have h := pow_self_le_three_pow_mul_factorial k
        have hN : (0 : ℝ) ≤ (N : ℝ) ^ k := by positivity
        nlinarith [h, hN]


/-- The geometric tail together with its remainder term, in the shape the induction needs. -/
private theorem sum_pow_Icc_four_le_aux {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (j : ℕ) :
    ∑ t ∈ Finset.Icc 4 (3 + j), q ^ t ≤ 2 * (q ^ 4 - q ^ (4 + j)) := by
  induction j with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ j ih =>
    have hsum : ∑ t ∈ Finset.Icc 4 (3 + (j + 1)), q ^ t
        = ∑ t ∈ Finset.Icc 4 (3 + j), q ^ t + q ^ (4 + j) := by
      rw [show 3 + (j + 1) = (3 + j) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
      congr 2
      omega
    rw [hsum]
    have h1 : q ^ (4 + (j + 1)) ≤ q ^ (4 + j) * (1 / 2) := by
      rw [show 4 + (j + 1) = (4 + j) + 1 by ring, pow_succ]
      exact mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0 _)
    linarith

/-- `∑_{t = 4}^{K} q ^ t ≤ 2 q ^ 4` for `0 ≤ q ≤ 1/2`, uniformly in `K`. -/
private theorem sum_pow_Icc_four_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (K : ℕ) :
    ∑ t ∈ Finset.Icc 4 K, q ^ t ≤ 2 * q ^ 4 := by
  rcases le_or_gt K 3 with h | h
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · obtain ⟨j, rfl⟩ : ∃ j, K = 3 + j := ⟨K - 3, by omega⟩
    have haux := sum_pow_Icc_four_le_aux hq0 hq1 j
    have : (0 : ℝ) ≤ q ^ (4 + j) := pow_nonneg hq0 _
    linarith


/-- **The combinatorial half of Lemma 9.3.5.**  If some set of at most `r` vertices induces a
non-3-colourable subgraph, then some such set `T` has at least four vertices and contains a set
of exactly `⌈3 #T / 2⌉` edges of `G`.

Take `T` of least cardinality among the offending sets.  Minimality feeds
`three_le_card_neighbors_of_minimal`, so each vertex of `T` has at least three neighbours in
`T`; the resulting `3 #T` ordered adjacent pairs map at most two-to-one onto `Sym2`, giving
`3 #T ≤ 2 #S₀` for the set `S₀` of induced edges. -/
private theorem exists_edgeFinset_of_not_colorable {n : ℕ} (G : SimpleGraph (Fin n))
    (r : ℝ) (T₀ : Finset (Fin n)) (hT₀ : (T₀.card : ℝ) ≤ r)
    (hnc : ¬ (SimpleGraph.induce (T₀ : Set (Fin n)) G).Colorable 3) :
    ∃ T : Finset (Fin n), (T.card : ℝ) ≤ r ∧ 4 ≤ T.card ∧
      ∃ S ⊆ offDiagPairs T, S.card = (3 * T.card + 1) / 2 ∧
        (↑S : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
  classical
  set 𝒯 : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => (T.card : ℝ) ≤ r ∧ ¬ (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3)
    with h𝒯
  have hne : 𝒯.Nonempty := ⟨T₀, by rw [h𝒯, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hT₀, hnc⟩⟩
  obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_min_image 𝒯 Finset.card hne
  rw [h𝒯, Finset.mem_filter] at hTmem
  obtain ⟨-, hTr, hTnc⟩ := hTmem
  have hmin : ∀ x ∈ T,
      (SimpleGraph.induce ((T.erase x : Finset (Fin n)) : Set (Fin n)) G).Colorable 3 := by
    intro x hx
    by_contra hcon
    have hcard : (T.erase x).card < T.card := Finset.card_erase_lt_of_mem hx
    have hle : (((T.erase x).card : ℕ) : ℝ) ≤ r :=
      le_trans (by exact_mod_cast hcard.le) hTr
    have hmem : T.erase x ∈ 𝒯 := by
      rw [h𝒯, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hle, hcon⟩
    have := hTmin _ hmem
    omega
  have hTne : T.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T with rfl | h
    · exact absurd (by rw [Finset.coe_empty]; exact SimpleGraph.Colorable.of_isEmpty 3) hTnc
    · exact h
  obtain ⟨x₀, hx₀⟩ := hTne
  have hdeg := three_le_card_neighbors_of_minimal G T hTnc hmin
  have hTpos : 0 < T.card := Finset.card_pos.2 ⟨x₀, hx₀⟩
  have h4 : 4 ≤ T.card := by
    have h3 := hdeg x₀ hx₀
    have hle : ((T.erase x₀).filter fun y => G.Adj x₀ y).card ≤ (T.erase x₀).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_erase_of_mem hx₀] at hle
    omega
  set P : Finset (Fin n × Fin n) :=
    T.biUnion (fun x => ((T.erase x).filter fun y => G.Adj x y).image (fun y => (x, y))) with hP
  have hinj : ∀ x : Fin n, Function.Injective (fun y : Fin n => (x, y)) := by
    intro x a b h; simpa using h
  have hPcard : 3 * T.card ≤ P.card := by
    have hdisj : (↑T : Set (Fin n)).PairwiseDisjoint
        (fun x => ((T.erase x).filter fun y => G.Adj x y).image (fun y => (x, y))) := by
      intro a _ b _ hab
      simp only [Finset.disjoint_left, Finset.mem_image]
      rintro q ⟨y, -, rfl⟩ ⟨z, -, hz⟩
      exact hab (congrArg Prod.fst hz).symm
    rw [hP, Finset.card_biUnion hdisj]
    have hterm : ∀ x ∈ T,
        3 ≤ (((T.erase x).filter fun y => G.Adj x y).image (fun y => (x, y))).card := by
      intro x hx
      rw [Finset.card_image_of_injective _ (hinj x)]
      exact hdeg x hx
    calc 3 * T.card = ∑ _x ∈ T, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hterm
  set S₀ : Finset (Sym2 (Fin n)) := P.image (fun q => s(q.1, q.2)) with hS₀
  have hfiber : ∀ e ∈ S₀, ({q ∈ P | s(q.1, q.2) = e}).card ≤ 2 := by
    intro e _
    induction e using Sym2.ind with
    | _ u v =>
      have hsub : {q ∈ P | s(q.1, q.2) = s(u, v)} ⊆ {(u, v), (v, u)} := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have h2 := hq.2
        rw [Sym2.eq_iff] at h2
        rcases h2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          simp [Finset.mem_insert, Prod.ext_iff, h1, h2]
      exact le_trans (Finset.card_le_card hsub)
        (le_trans (Finset.card_insert_le _ _) (by simp))
  have hS₀card : (3 * T.card + 1) / 2 ≤ S₀.card := by
    have := Finset.card_le_mul_card_image (f := fun q : Fin n × Fin n => s(q.1, q.2)) P 2 hfiber
    rw [← hS₀] at this
    omega
  have hmemP : ∀ q ∈ P, q.1 ∈ T ∧ q.2 ∈ T ∧ G.Adj q.1 q.2 := by
    intro q hq
    rw [hP, Finset.mem_biUnion] at hq
    obtain ⟨x, hx, hq2⟩ := hq
    rw [Finset.mem_image] at hq2
    obtain ⟨y, hy, rfl⟩ := hq2
    rw [Finset.mem_filter, Finset.mem_erase] at hy
    exact ⟨hx, hy.1.2, hy.2⟩
  have hS₀sub : S₀ ⊆ offDiagPairs T := by
    intro e he
    rw [hS₀, Finset.mem_image] at he
    obtain ⟨q, hq, rfl⟩ := he
    obtain ⟨h1, h2, h3⟩ := hmemP q hq
    exact mem_offDiagPairs.2 ⟨h1, h2, G.ne_of_adj h3⟩
  have hS₀edge : (↑S₀ : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
    intro e he
    rw [Finset.mem_coe, hS₀, Finset.mem_image] at he
    obtain ⟨q, hq, rfl⟩ := he
    exact (hmemP q hq).2.2
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hS₀card
  exact ⟨T, hTr, h4, S, hSsub.trans hS₀sub, hScard,
    fun e he => hS₀edge (by exact_mod_cast hSsub (by exact_mod_cast he))⟩


/-- **The union bound.**  The event that some set of at most `r` vertices induces a
non-3-colourable subgraph has probability at most
`∑_{t=4}^{K} binom(n,t) binom(binom(t,2), ⌈3t/2⌉) p ^ ⌈3t/2⌉`,
where `K` is any bound on the cardinalities in play.

One term per pair (vertex set of size `t`, edge set of size `⌈3t/2⌉` inside it); each event is
the cylinder of `binomialRandom_setOf_subset_edgeSet`. -/
private theorem prob_not_forall_small_colorable_le {n : ℕ} (p : I) (r : ℝ) (K : ℕ)
    (hKr : ∀ t : ℕ, (t : ℝ) ≤ r → t ≤ K) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | ∀ T : Finset (Fin n), (T.card : ℝ) ≤ r →
          (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3}ᶜ
      ≤ ∑ t ∈ Finset.Icc 4 K,
          ((n.choose t : ℝ) * ((t.choose 2).choose ((3 * t + 1) / 2) : ℝ)) *
            (p : ℝ) ^ ((3 * t + 1) / 2) := by
  classical
  set m : ℕ → ℕ := fun t => (3 * t + 1) / 2 with hm
  set Sfam : ℕ → Finset (Finset (Sym2 (Fin n))) := fun t =>
    ((Finset.univ : Finset (Fin n)).powersetCard t).biUnion
      (fun T => (offDiagPairs T).powersetCard (m t)) with hSfam
  have hsub : {G : SimpleGraph (Fin n) | ∀ T : Finset (Fin n), (T.card : ℝ) ≤ r →
        (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3}ᶜ
      ⊆ ⋃ t ∈ Finset.Icc 4 K, ⋃ S ∈ Sfam t,
          {G : SimpleGraph (Fin n) | (↑S : Set (Sym2 (Fin n))) ⊆ G.edgeSet} := by
    intro G hG
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hG
    push Not at hG
    obtain ⟨T₀, hT₀, hnc⟩ := hG
    obtain ⟨T, hTr, h4, S, hSsub, hScard, hSedge⟩ :=
      exists_edgeFinset_of_not_colorable G r T₀ hT₀ hnc
    refine Set.mem_iUnion₂.2 ⟨T.card, Finset.mem_Icc.2 ⟨h4, hKr _ hTr⟩, ?_⟩
    refine Set.mem_iUnion₂.2 ⟨S, ?_, hSedge⟩
    rw [hSfam, Finset.mem_biUnion]
    exact ⟨T, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩,
      Finset.mem_powersetCard.2 ⟨hSsub, hScard⟩⟩
  have hprob : ∀ t : ℕ, ∀ S ∈ Sfam t,
      (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | (↑S : Set (Sym2 (Fin n))) ⊆ G.edgeSet} = (p : ℝ) ^ m t := by
    intro t S hS
    rw [hSfam, Finset.mem_biUnion] at hS
    obtain ⟨T, -, hS2⟩ := hS
    rw [Finset.mem_powersetCard] at hS2
    rw [Measure.real, binomialRandom_setOf_subset_edgeSet p _
      (fun e he => not_isDiag_of_mem_offDiagPairs (hS2.1 he)), hS2.2,
      ENNReal.toReal_pow, ENNReal.coe_toReal, unitInterval.coe_toNNReal]
  have hoffcard : ∀ t : ℕ, ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
      (offDiagPairs T).card = t.choose 2 := by
    intro t T hT
    have hTc := (Finset.mem_powersetCard.1 hT).2
    have h := card_offDiagPairs_add T
    rw [hTc] at h
    have hpas : (t + 1).choose 2 = t + t.choose 2 := by
      have := Nat.choose_succ_succ t 1
      simpa [Nat.choose_one_right] using this
    omega
  have hcard : ∀ t : ℕ, (Sfam t).card ≤ n.choose t * ((t.choose 2).choose (m t)) := by
    intro t
    calc (Sfam t).card
        ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard t,
            ((offDiagPairs T).powersetCard (m t)).card := Finset.card_biUnion_le
      _ = ∑ _T ∈ (Finset.univ : Finset (Fin n)).powersetCard t, (t.choose 2).choose (m t) :=
          Finset.sum_congr rfl fun T hT => by
            rw [Finset.card_powersetCard, hoffcard t T hT]
      _ = n.choose t * ((t.choose 2).choose (m t)) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin]
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  calc (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) | ∀ T : Finset (Fin n), (T.card : ℝ) ≤ r →
          (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3}ᶜ
      ≤ (SimpleGraph.binomialRandom (Fin n) p).real
          (⋃ t ∈ Finset.Icc 4 K, ⋃ S ∈ Sfam t,
            {G : SimpleGraph (Fin n) | (↑S : Set (Sym2 (Fin n))) ⊆ G.edgeSet}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ t ∈ Finset.Icc 4 K, (SimpleGraph.binomialRandom (Fin n) p).real
          (⋃ S ∈ Sfam t, {G : SimpleGraph (Fin n) | (↑S : Set (Sym2 (Fin n))) ⊆ G.edgeSet}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ t ∈ Finset.Icc 4 K, ∑ S ∈ Sfam t, (SimpleGraph.binomialRandom (Fin n) p).real
          {G : SimpleGraph (Fin n) | (↑S : Set (Sym2 (Fin n))) ⊆ G.edgeSet} :=
        Finset.sum_le_sum fun t _ => measureReal_biUnion_finset_le _ _
    _ = ∑ t ∈ Finset.Icc 4 K, ((Sfam t).card : ℝ) * (p : ℝ) ^ m t := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_congr rfl (hprob t), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ Finset.Icc 4 K,
          ((n.choose t : ℝ) * ((t.choose 2).choose (m t) : ℝ)) * (p : ℝ) ^ m t := by
        refine Finset.sum_le_sum fun t _ => ?_
        have h1 : ((Sfam t).card : ℝ) ≤ (n.choose t : ℝ) * ((t.choose 2).choose (m t) : ℝ) := by
          exact_mod_cast hcard t
        exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hp0 _)


/-- `2 binom(t,2) = t (t-1)`. -/
private theorem two_mul_choose_two : ∀ t : ℕ, 2 * (t.choose 2) = t * (t - 1)
  | 0 => rfl
  | s + 1 => by
    have h := Nat.add_one_mul_choose_eq s 1
    simp only [Nat.choose_one_right, Nat.reduceAdd] at h
    rw [Nat.add_sub_cancel, h]
    ring

/-- `3 binom(t,2) ≤ t ⌈3t/2⌉`, i.e. `3 binom(t,2) / ⌈3t/2⌉ ≤ t`: the reason the inner
binomial coefficient is at most `t ^ ⌈3t/2⌉`. -/
private theorem three_mul_choose_two_le (t : ℕ) :
    3 * (t.choose 2) ≤ t * ((3 * t + 1) / 2) := by
  have h2c := two_mul_choose_two t
  have h1 : 3 * t ≤ 2 * ((3 * t + 1) / 2) := by omega
  have step : 2 * (3 * (t.choose 2)) = 3 * (t * (t - 1)) := by rw [← h2c]; ring
  have key : 2 * (3 * (t.choose 2)) ≤ 2 * (t * ((3 * t + 1) / 2)) :=
    calc 2 * (3 * (t.choose 2)) = 3 * (t * (t - 1)) := step
      _ ≤ 3 * (t * t) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left t (Nat.sub_le t 1))
      _ = t * (3 * t) := by ring
      _ ≤ t * (2 * ((3 * t + 1) / 2)) := Nat.mul_le_mul_left t h1
      _ = 2 * (t * ((3 * t + 1) / 2)) := by ring
  omega

/-- **The analytic heart.**  For `4 ≤ t ≤ C √n` and `p ≤ n ^ (-α)`, the square of the
`t`-th summand of the union bound is at most `(9 n² (C √n) n ^ (-3α)) ^ t`.

Indeed `binom(n,t) ≤ (3n/t) ^ t` and `binom(binom(t,2), m) ≤ t ^ m`, so the summand is at most
`(3n/t) ^ t β ^ m` with `β = t n ^ (-α) ≤ 1`; squaring and using `3t ≤ 2m` replaces `β ^ 2m` by
`β ^ 3t`, and `(3n/t) ² β ³ = 9 n² t n ^ (-3α)`.  Squaring keeps the exponent `⌈3t/2⌉` an
integer throughout. -/
private theorem term_sq_le_base_pow {n t : ℕ} {a C : ℝ} (p : I)
    (ht4 : 4 ≤ t) (htC : (t : ℝ) ≤ C * Real.sqrt n)
    (hp : (p : ℝ) ≤ (n : ℝ) ^ (-a))
    (hb : (t : ℝ) * (n : ℝ) ^ (-a) ≤ 1) :
    ((n.choose t : ℝ) * ((t.choose 2).choose ((3 * t + 1) / 2) : ℝ) *
        (p : ℝ) ^ ((3 * t + 1) / 2)) ^ 2
      ≤ (9 * (n : ℝ) ^ 2 * (C * Real.sqrt n) * ((n : ℝ) ^ (-a)) ^ 3) ^ t := by
  set m : ℕ := (3 * t + 1) / 2 with hmdef
  set P : ℝ := (n : ℝ) ^ (-a) with hPdef
  have hP0 : (0 : ℝ) ≤ P := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ht0 : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  -- the two binomial factors
  have hA : (n.choose t : ℝ) ≤ (3 * n / t) ^ t := choose_le_three_mul_div_pow n t ht0
  have hB : ((t.choose 2).choose m : ℝ) ≤ (t : ℝ) ^ m := by
    refine le_trans (choose_le_three_mul_div_pow (t.choose 2) m hm0) ?_
    refine pow_le_pow_left₀ (by positivity) ?_ m
    rw [div_le_iff₀ hmR]
    exact_mod_cast three_mul_choose_two_le t
  have hC' : (p : ℝ) ^ m ≤ P ^ m := pow_le_pow_left₀ p.2.1 hp m
  have hA0 : (0 : ℝ) ≤ (n.choose t : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ ((t.choose 2).choose m : ℝ) := by positivity
  have hp0 : (0 : ℝ) ≤ (p : ℝ) ^ m := pow_nonneg p.2.1 m
  have hterm0 : (0 : ℝ) ≤ (n.choose t : ℝ) * ((t.choose 2).choose m : ℝ) * (p : ℝ) ^ m := by
    positivity
  have hstep1 : (n.choose t : ℝ) * ((t.choose 2).choose m : ℝ) * (p : ℝ) ^ m
      ≤ (3 * n / t) ^ t * ((t : ℝ) * P) ^ m := by
    have h1 : (n.choose t : ℝ) * ((t.choose 2).choose m : ℝ) * (p : ℝ) ^ m
        ≤ (3 * n / t) ^ t * ((t : ℝ) ^ m * P ^ m) := by
      have hmul : (n.choose t : ℝ) * ((t.choose 2).choose m : ℝ) ≤ (3 * n / t) ^ t * (t : ℝ) ^ m :=
        mul_le_mul hA hB hB0 (by positivity)
      calc (n.choose t : ℝ) * ((t.choose 2).choose m : ℝ) * (p : ℝ) ^ m
          ≤ ((3 * n / t) ^ t * (t : ℝ) ^ m) * P ^ m :=
            mul_le_mul hmul hC' hp0 (by positivity)
        _ = (3 * n / t) ^ t * ((t : ℝ) ^ m * P ^ m) := by ring
    rwa [← mul_pow] at h1
  have hbase0 : (0 : ℝ) ≤ (3 * n / t) ^ t * ((t : ℝ) * P) ^ m := by positivity
  have hb0 : (0 : ℝ) ≤ (t : ℝ) * P := by positivity
  have hexp : t * 3 ≤ m * 2 := by omega
  calc ((n.choose t : ℝ) * ((t.choose 2).choose m : ℝ) * (p : ℝ) ^ m) ^ 2
      ≤ ((3 * n / t) ^ t * ((t : ℝ) * P) ^ m) ^ 2 := pow_le_pow_left₀ hterm0 hstep1 2
    _ = (3 * n / t) ^ (t * 2) * ((t : ℝ) * P) ^ (m * 2) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ (3 * n / t) ^ (t * 2) * ((t : ℝ) * P) ^ (t * 3) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb0 hb hexp) (by positivity)
    _ = ((3 * n / t) ^ 2 * ((t : ℝ) * P) ^ 3) ^ t := by
        rw [mul_pow ((3 * (n : ℝ) / t) ^ 2) (((t : ℝ) * P) ^ 3) t, ← pow_mul, ← pow_mul,
          Nat.mul_comm 2 t, Nat.mul_comm 3 t]
    _ ≤ (9 * (n : ℝ) ^ 2 * (C * Real.sqrt n) * P ^ 3) ^ t := by
        refine pow_le_pow_left₀ (by positivity) ?_ t
        have heq : (3 * (n : ℝ) / t) ^ 2 * ((t : ℝ) * P) ^ 3
            = 9 * (n : ℝ) ^ 2 * (t : ℝ) * P ^ 3 := by
          field_simp
          ring
        rw [heq]
        have h9 : (0 : ℝ) ≤ 9 * (n : ℝ) ^ 2 := by positivity
        have hP3 : (0 : ℝ) ≤ P ^ 3 := by positivity
        have hmul := mul_le_mul_of_nonneg_left htC (mul_nonneg h9 hP3)
        nlinarith [hmul]


/-- The base of the last estimate is `9 C n ^ (5/2 - 3α)`, whose exponent is negative exactly
when `α > 5/6`. -/
private theorem base_eq_rpow {n : ℕ} {a C : ℝ} (hn : (0 : ℝ) < n) :
    9 * (n : ℝ) ^ 2 * (C * Real.sqrt n) * ((n : ℝ) ^ (-a)) ^ 3
      = 9 * C * (n : ℝ) ^ (5 / 2 - 3 * a) := by
  have h1 : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have h2 : (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ ((2 : ℝ)) := by
    rw [← Real.rpow_natCast (n : ℝ) 2]; norm_num
  have h3 : ((n : ℝ) ^ (-a)) ^ (3 : ℕ) = (n : ℝ) ^ (-a * 3) := by
    rw [Real.rpow_mul hn.le, ← Real.rpow_natCast ((n : ℝ) ^ (-a)) 3]; norm_num
  rw [h1, h2, h3, show (5 : ℝ) / 2 - 3 * a = 2 + (1 / 2 + -a * 3) by ring,
    Real.rpow_add hn, Real.rpow_add hn]
  ring

/-- `√n · n ^ (-α) = n ^ (1/2 - α)`. -/
private theorem sqrt_mul_rpow_neg {n : ℕ} {a : ℝ} (hn : (0 : ℝ) < n) :
    Real.sqrt n * (n : ℝ) ^ (-a) = (n : ℝ) ^ (1 / 2 - a) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  ring_nf

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
  classical
  set d : ℝ := min (3 * a - 5 / 2) (a - 1 / 2) with hddef
  have hd : 0 < d := by rw [hddef]; exact lt_min (by linarith) (by linarith)
  set ε : ℝ := min (1 / 4) (δ ^ 2 / 4) with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact lt_min (by norm_num) (by positivity)
  have hMlim : Filter.Tendsto (fun k : ℕ => (9 * C + C) * (k : ℝ) ^ (-d)) Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using h.const_mul (9 * C + C)
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.1 (Filter.Tendsto.eventually_le_const hε hMlim)
  refine ⟨max N₀ 1, ?_⟩
  intro n hn p hp
  have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsmall : (9 * C + C) * (n : ℝ) ^ (-d) ≤ ε := hN₀ n (le_trans (le_max_left N₀ 1) hn)
  have hrpow0 : (0 : ℝ) ≤ (n : ℝ) ^ (-d) := Real.rpow_nonneg hn0.le _
  -- the base of the geometric bound
  set w : ℝ := 9 * (n : ℝ) ^ 2 * (C * Real.sqrt n) * ((n : ℝ) ^ (-a)) ^ 3 with hwdef
  have hw0 : 0 ≤ w := by rw [hwdef]; positivity
  have hwε : w ≤ ε := by
    rw [hwdef, base_eq_rpow hn0]
    have h1 : (n : ℝ) ^ (5 / 2 - 3 * a) ≤ (n : ℝ) ^ (-d) := by
      refine Real.rpow_le_rpow_of_exponent_le hnR ?_
      have := min_le_left (3 * a - 5 / 2) (a - 1 / 2)
      rw [← hddef] at this
      linarith
    calc 9 * C * (n : ℝ) ^ (5 / 2 - 3 * a) ≤ 9 * C * (n : ℝ) ^ (-d) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (9 * C + C) * (n : ℝ) ^ (-d) := mul_le_mul_of_nonneg_right (by linarith) hrpow0
      _ ≤ ε := hsmall
  set q : ℝ := Real.sqrt w with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqsq : q ^ 2 = w := Real.sq_sqrt hw0
  have hq2 : q ≤ 1 / 2 := by
    have hle : w ≤ 1 / 4 := le_trans hwε (by rw [hεdef]; exact min_le_left _ _)
    calc q = Real.sqrt w := hqdef
      _ ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hle
      _ = 1 / 2 := by
          rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hqδ : q ≤ δ / 2 := by
    have hle : w ≤ δ ^ 2 / 4 := le_trans hwε (by rw [hεdef]; exact min_le_right _ _)
    calc q = Real.sqrt w := hqdef
      _ ≤ Real.sqrt (δ ^ 2 / 4) := Real.sqrt_le_sqrt hle
      _ = δ / 2 := by
          rw [show δ ^ 2 / 4 = (δ / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  -- every candidate set is small enough that `t * n ^ (-a) ≤ 1`
  have hbeta : ∀ t : ℕ, (t : ℝ) ≤ C * Real.sqrt (n : ℝ) → (t : ℝ) * (n : ℝ) ^ (-a) ≤ 1 := by
    intro t ht
    have hPa : (0 : ℝ) ≤ (n : ℝ) ^ (-a) := Real.rpow_nonneg hn0.le _
    have h1 : (t : ℝ) * (n : ℝ) ^ (-a) ≤ C * (n : ℝ) ^ (1 / 2 - a) := by
      have := mul_le_mul_of_nonneg_right ht hPa
      rw [mul_assoc, sqrt_mul_rpow_neg hn0] at this
      exact this
    have h2 : (n : ℝ) ^ (1 / 2 - a) ≤ (n : ℝ) ^ (-d) := by
      refine Real.rpow_le_rpow_of_exponent_le hnR ?_
      have := min_le_right (3 * a - 5 / 2) (a - 1 / 2)
      rw [← hddef] at this
      linarith
    have h3 : C * (n : ℝ) ^ (-d) ≤ (9 * C + C) * (n : ℝ) ^ (-d) :=
      mul_le_mul_of_nonneg_right (by linarith) hrpow0
    have h4 : ε ≤ 1 / 4 := by rw [hεdef]; exact min_le_left _ _
    have h5 : C * (n : ℝ) ^ (1 / 2 - a) ≤ C * (n : ℝ) ^ (-d) :=
      mul_le_mul_of_nonneg_left h2 hC.le
    linarith
  have hr0 : (0 : ℝ) ≤ C * Real.sqrt n := by positivity
  set K : ℕ := ⌊C * Real.sqrt (n : ℝ)⌋₊ with hKdef
  have hKr : ∀ t : ℕ, (t : ℝ) ≤ C * Real.sqrt n → t ≤ K := fun t h => Nat.le_floor h
  have hKle : ∀ t : ℕ, t ≤ K → (t : ℝ) ≤ C * Real.sqrt n := by
    intro t ht
    calc (t : ℝ) ≤ (K : ℝ) := by exact_mod_cast ht
      _ ≤ C * Real.sqrt n := Nat.floor_le hr0
  have hbound := prob_not_forall_small_colorable_le (n := n) p (C * Real.sqrt n) K hKr
  have hsum : ∑ t ∈ Finset.Icc 4 K,
      ((n.choose t : ℝ) * ((t.choose 2).choose ((3 * t + 1) / 2) : ℝ)) *
        (p : ℝ) ^ ((3 * t + 1) / 2) ≤ ∑ t ∈ Finset.Icc 4 K, q ^ t := by
    refine Finset.sum_le_sum fun t ht => ?_
    rw [Finset.mem_Icc] at ht
    have htC : (t : ℝ) ≤ C * Real.sqrt n := hKle t ht.2
    have hsq := term_sq_le_base_pow (a := a) (C := C) p ht.1 htC hp (hbeta t htC)
    rw [← hwdef] at hsq
    refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (pow_nonneg hq0 t) ?_
    calc ((n.choose t : ℝ) * ((t.choose 2).choose ((3 * t + 1) / 2) : ℝ) *
            (p : ℝ) ^ ((3 * t + 1) / 2)) ^ 2 ≤ w ^ t := hsq
      _ = (q ^ t) ^ 2 := by rw [← hqsq, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hfinal : ∑ t ∈ Finset.Icc 4 K, q ^ t ≤ δ := by
    have h1 := sum_pow_Icc_four_le hq0 hq2 K
    have h2 : q ^ 4 ≤ q := by
      calc q ^ 4 ≤ q ^ 1 := pow_le_pow_of_le_one hq0 (by linarith) (by norm_num)
        _ = q := pow_one q
    linarith
  have hcompl := le_trans hbound (le_trans hsum hfinal)
  have hmeas : MeasurableSet {G : SimpleGraph (Fin n) |
      ∀ T : Finset (Fin n), (T.card : ℝ) ≤ C * Real.sqrt n →
      (SimpleGraph.induce (T : Set (Fin n)) G).Colorable 3} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  rw [measureReal_compl hmeas, probReal_univ] at hcompl
  linarith

/-- **Theorem 9.3.4** (Shamir–Spencer 1987): for `α > 5/6` and `p ≤ n ^ (-α)`, the chromatic
number of `G(n, p)` is concentrated on four consecutive values. -/
theorem exists_chromaticNumber_four_values {a δ : ℝ} (ha : 5 / 6 < a) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ p : I, (p : ℝ) ≤ (n : ℝ) ^ (-a) →
      ∃ u : ℕ, 1 - δ ≤ (SimpleGraph.binomialRandom (Fin n) p).real
        {G : SimpleGraph (Fin n) |
          u ≤ G.chromaticNumber.toNat ∧ G.chromaticNumber.toNat ≤ u + 3} := by
  sorry

end ProbMethodCombinatorics
