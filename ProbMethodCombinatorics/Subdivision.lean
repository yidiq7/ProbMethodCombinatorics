import ProbMethodCombinatorics.Chernoff
import ProbMethodCombinatorics.Concentration

/-!
# Section 5.3: no large clique subdivision in `G(n, 1/2)`

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Theorem 5.3.2 (Hajós): with high
probability `G(n, 1/2)` contains no subdivision of `K t` for `t = ⌈10 √n⌉`.

The vocabulary (`IsKSubdivision`, `HasKSubdivision`, `branchNonAdj`) lives in `Chernoff.lean`
with the rest of Chapter 5, but the argument needs the edge-exposure product space of Chapter 9,
so the probabilistic half is collected here, in the one file that imports both.

The argument is a counting one.  A `K t`-subdivision forces its `t` branch vertices to span at
least `C(t, 2) - (n - t)` edges, because every *non*-adjacent branch pair consumes a private
interior vertex and only `n - t` vertices are available.  For `t = ⌈10 √n⌉` that threshold sits
`Θ(n)` above the mean `C(t, 2) / 2`, while the union bound over the `C(n, t)` candidate branch
sets costs only `t log n = Θ(√n log n)`.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory unitInterval SimpleGraph

/-- The number of edges of `G` spanned by `S`.  The sum over `S.offDiag` visits each edge in
both orders, hence the `/ 2`; phrasing it with set indicators keeps it a function of `G` alone,
with no `DecidableRel G.Adj` to supply, since the measure ranges over all graphs on `Fin n`. -/
noncomputable def edgeCountWithin {n : ℕ} (S : Finset (Fin n)) (G : SimpleGraph (Fin n)) : ℝ :=
  (∑ q ∈ S.offDiag, ({K : SimpleGraph (Fin n) | K.Adj q.1 q.2}).indicator (fun _ => 1) G) / 2

/-- **The expected number of edges inside `S`** is `p · C(|S|, 2)`: each of the `|S|(|S| - 1)`
ordered pairs contributes `p`, and the `/ 2` turns that into the unordered count. -/
theorem integral_edgeCountWithin {n : ℕ} (S : Finset (Fin n)) (p : I) :
    ∫ G, edgeCountWithin S G ∂(SimpleGraph.binomialRandom (Fin n) p) = (p : ℝ) * S.card.choose 2 := by
  sorry

/-- **The edge slots inside `S` number `C(|S|, 2)`.**  This is the coordinate count that sets
the exponent in the bounded differences inequality below. -/
theorem card_edgeSlots_within {n : ℕ} (S : Finset (Fin n)) :
    (Finset.univ.filter fun e : EdgeSlot n => (e : Sym2 (Fin n)) ∈ S.sym2).card
      = S.card.choose 2 := by
  sorry

/-- **The edge count inside a fixed set concentrates.**  As a function of the `C(|S|, 2)` edge
slots inside `S` it changes by at most `1` when one slot is toggled and does not depend on the
other slots at all, so the bounded differences inequality applies with `∑ cᵢ² = C(|S|, 2)`. -/
theorem binomialRandom_edgeCountWithin_ge_le {n : ℕ} (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (p : I) {lam : ℝ} (hlam : 0 ≤ lam) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G | lam ≤ edgeCountWithin S G - (p : ℝ) * S.card.choose 2}
      ≤ Real.exp (-2 * lam ^ 2 / S.card.choose 2) := by
  sorry

/-- **Union bound over the candidate branch sets**: no `t`-set at all is that dense, at the cost
of a factor `C(n, t)`. -/
theorem binomialRandom_exists_edgeCountWithin_ge_le {n t : ℕ} (ht : 2 ≤ t) (p : I)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (SimpleGraph.binomialRandom (Fin n) p).real
        {G | ∃ S : Finset (Fin n), S.card = t ∧
          lam ≤ edgeCountWithin S G - (p : ℝ) * t.choose 2}
      ≤ n.choose t * Real.exp (-2 * lam ^ 2 / t.choose 2) := by
  sorry

/-- The ordered non-adjacent branch pairs number twice the `i < j` ones: swapping the two
coordinates matches the `i > j` half of the filtered off-diagonal with `branchNonAdj G br`. -/
private theorem card_offDiag_filter_not_adj_eq_two_mul {n t : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (br : Fin t → Fin n) :
    (((Finset.univ : Finset (Fin t)).offDiag).filter
        fun q => ¬ G.Adj (br q.1) (br q.2)).card = 2 * (branchNonAdj G br).card := by
  classical
  have hlt : (((Finset.univ : Finset (Fin t)).offDiag).filter
      fun q => ¬ G.Adj (br q.1) (br q.2)).filter (fun q => q.1 < q.2)
      = branchNonAdj G br := by
    ext q
    simp only [branchNonAdj, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact ⟨fun hq => ⟨hq.2, hq.1.2⟩, fun hq => ⟨⟨hq.1.ne, hq.2⟩, hq.1⟩⟩
  have hge : (((Finset.univ : Finset (Fin t)).offDiag).filter
      fun q => ¬ G.Adj (br q.1) (br q.2)).filter (fun q => ¬ q.1 < q.2)
      = (branchNonAdj G br).image Prod.swap := by
    ext q
    simp only [branchNonAdj, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_image, Prod.exists, Prod.swap_prod_mk]
    constructor
    · intro hq
      refine ⟨q.2, q.1, ⟨?_, ?_⟩, rfl⟩
      · omega
      · rw [G.adj_comm]; exact hq.1.2
    · intro hq
      obtain ⟨a, b, ⟨hab, hnadj⟩, heq⟩ := hq
      subst heq
      dsimp only
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · omega
      · rw [G.adj_comm]; exact hnadj
      · omega
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := (((Finset.univ : Finset (Fin t)).offDiag).filter
        fun q => ¬ G.Adj (br q.1) (br q.2))) (fun q => q.1 < q.2)
  rw [hlt, hge, Finset.card_image_of_injective _ Prod.swap_injective] at hsplit
  omega

/-- Reindexing the adjacent pairs of the branch set along `br`, which is injective, so
`(i, j) ↦ (br i, br j)` is a bijection from `Finset.univ.offDiag` onto the branch set's. -/
private theorem card_image_offDiag_filter_adj_eq {n t : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {br : Fin t → Fin n} (hbr : Function.Injective br) :
    (((Finset.univ.image br).offDiag).filter fun q => G.Adj q.1 q.2).card
      = (((Finset.univ : Finset (Fin t)).offDiag).filter
          fun q => G.Adj (br q.1) (br q.2)).card := by
  classical
  have hinj : Function.Injective (fun q : Fin t × Fin t => (br q.1, br q.2)) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (hbr hab.1) (hbr hab.2)
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · intro hq
    obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩, hne⟩, hadj⟩ := hq
    refine ⟨i, j, ⟨?_, ?_⟩, ?_⟩
    · intro hij
      exact hne (by rw [← hi, ← hj, hij])
    · rw [hi, hj]; exact hadj
    · rw [hi, hj]
  · intro hq
    obtain ⟨i, j, ⟨hne, hadj⟩, heq⟩ := hq
    subst heq
    dsimp only
    exact ⟨⟨⟨i, rfl⟩, ⟨j, rfl⟩, fun hc => hne (hbr hc)⟩, hadj⟩

/-- **A `K t`-subdivision exhibits a dense `t`-set**: its branch vertices span all but at most
`n - t` of the `C(t, 2)` pairs, by `card_branchNonAdj_add_le_of_isKSubdivision`. -/
theorem exists_card_eq_and_le_edgeCountWithin_of_hasKSubdivision {n t : ℕ}
    {G : SimpleGraph (Fin n)} (h : HasKSubdivision G t) :
    ∃ S : Finset (Fin n), S.card = t ∧
      (t.choose 2 : ℝ) - n + t ≤ edgeCountWithin S G := by
  classical
  obtain ⟨br, P, hsub⟩ := h
  refine ⟨Finset.univ.image br, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hsub.inj, Finset.card_univ, Fintype.card_fin]
  · have hcount : (branchNonAdj G br).card + t ≤ n := by
      have := card_branchNonAdj_add_le_of_isKSubdivision hsub
      rwa [Fintype.card_fin] at this
    have hsum : edgeCountWithin (Finset.univ.image br) G
        = ((((Finset.univ.image br).offDiag).filter fun q => G.Adj q.1 q.2).card : ℝ) / 2 := by
      unfold edgeCountWithin
      congr 1
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_boole]
    have hsplit := Finset.card_filter_add_card_filter_not
        (s := ((Finset.univ : Finset (Fin t)).offDiag)) (fun q => G.Adj (br q.1) (br q.2))
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
      card_offDiag_filter_not_adj_eq_two_mul G br,
      ← card_image_offDiag_filter_adj_eq G hsub.inj] at hsplit
    have hle : t ≤ t * t := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · simp [h0]
      · exact Nat.le_mul_of_pos_left t hpos
    have hreal : ((((Finset.univ.image br).offDiag).filter fun q => G.Adj q.1 q.2).card : ℝ)
        + 2 * ((branchNonAdj G br).card : ℝ) = (t : ℝ) * (t : ℝ) - (t : ℝ) := by
      calc ((((Finset.univ.image br).offDiag).filter fun q => G.Adj q.1 q.2).card : ℝ)
            + 2 * ((branchNonAdj G br).card : ℝ)
          = (((((Finset.univ.image br).offDiag).filter fun q => G.Adj q.1 q.2).card
              + 2 * (branchNonAdj G br).card : ℕ) : ℝ) := by push_cast; ring
        _ = ((t * t - t : ℕ) : ℝ) := by rw [hsplit]
        _ = (t : ℝ) * (t : ℝ) - (t : ℝ) := by rw [Nat.cast_sub hle]; push_cast; ring
    have hcountreal : ((branchNonAdj G br).card : ℝ) + (t : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hcount
    rw [hsum, Nat.cast_choose_two]
    linarith

/-- For `t = ⌈10 √n⌉` the counting threshold `C(t, 2) - n + t` sits at least `20 n` above the
mean `C(t, 2) / 2`, since `C(t, 2) ≥ 50n - 5√n`. -/
theorem half_choose_two_add_twenty_le {n : ℕ} :
    (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ) / 2 + 20 * n
      ≤ (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ) - n + ⌈10 * Real.sqrt n⌉₊ := by
  sorry

/-- The union bound over the `C(n, t)` candidate branch sets is beaten by the deviation `20 n`:
its logarithm is `O(√n log n)` while the exponent is `Ω(n)`. -/
theorem exists_forall_choose_mul_exp_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (n.choose ⌈10 * Real.sqrt n⌉₊ : ℝ)
          * Real.exp (-2 * (20 * n) ^ 2 / (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ)) < δ := by
  sorry

/-- **Theorem 5.3.2** (Hajós).  With high probability `G(n, 1/2)` has no `K t`-subdivision for
`t = ⌈10 √n⌉`, stated in the chapter's explicit `δ`–`N` form. -/
theorem binomialRandom_hasKSubdivision_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩).real
          {G | HasKSubdivision G ⌈10 * Real.sqrt n⌉₊} < δ := by
  sorry

end ProbMethodCombinatorics
