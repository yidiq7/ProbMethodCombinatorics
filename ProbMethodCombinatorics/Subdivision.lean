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

/-- **A `K t`-subdivision exhibits a dense `t`-set**: its branch vertices span all but at most
`n - t` of the `C(t, 2)` pairs, by `card_branchNonAdj_add_le_of_isKSubdivision`. -/
theorem exists_card_eq_and_le_edgeCountWithin_of_hasKSubdivision {n t : ℕ}
    {G : SimpleGraph (Fin n)} (h : HasKSubdivision G t) :
    ∃ S : Finset (Fin n), S.card = t ∧
      (t.choose 2 : ℝ) - n + t ≤ edgeCountWithin S G := by
  sorry

/-- For `t = ⌈10 √n⌉` the counting threshold `C(t, 2) - n + t` sits at least `20 n` above the
mean `C(t, 2) / 2`, since `C(t, 2) ≥ 50n - 5√n`. -/
theorem half_choose_two_add_twenty_le {n : ℕ} :
    (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ) / 2 + 20 * n
      ≤ (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ) - n + ⌈10 * Real.sqrt n⌉₊ := by
  sorry

private theorem two_le_ceil_ten_sqrt {n : ℕ} (hn : 1 ≤ n) : 2 ≤ ⌈10 * Real.sqrt n⌉₊ := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn'
  have h : ((1 : ℕ) : ℝ) < 10 * Real.sqrt n := by push_cast; linarith
  have := Nat.lt_ceil.mpr h
  omega

private theorem choose_two_ceil_ten_sqrt_pos {n : ℕ} (hn : 1 ≤ n) :
    (0 : ℝ) < (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ) := by
  have h : 0 < ⌈10 * Real.sqrt n⌉₊.choose 2 := Nat.choose_pos (two_le_ceil_ten_sqrt hn)
  exact_mod_cast h

private theorem choose_two_ceil_ten_sqrt_le {n : ℕ} (hn : 1 ≤ n) :
    (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ) ≤ 61 * n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs2 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn'
  have ht : (⌈10 * Real.sqrt n⌉₊ : ℝ) < 10 * Real.sqrt n + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have ht0 : (0 : ℝ) ≤ (⌈10 * Real.sqrt n⌉₊ : ℝ) := Nat.cast_nonneg _
  have hsq := mul_self_le_mul_self ht0 ht.le
  rw [Nat.cast_choose_two]
  nlinarith [hsq, hs1, hs2, ht0, hn']

private theorem choose_le_exp_card (n k : ℕ) : (n.choose k : ℝ) ≤ Real.exp n := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (n.choose k : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_le_two_pow n k
    _ = (2 : ℝ) ^ n := by push_cast; ring
    _ ≤ Real.exp 1 ^ n := by gcongr
    _ = Real.exp n := by rw [← Real.exp_nat_mul]; simp

/-- The union bound over the `C(n, t)` candidate branch sets is beaten by the deviation `20 n`:
its logarithm is `O(√n log n)` while the exponent is `Ω(n)`. -/
theorem exists_forall_choose_mul_exp_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (n.choose ⌈10 * Real.sqrt n⌉₊ : ℝ)
          * Real.exp (-2 * (20 * n) ^ 2 / (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ)) < δ := by
  refine ⟨max 1 (⌈1 / δ⌉₊ + 1), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hC0 := choose_two_ceil_ten_sqrt_pos hn1
  have hCle := choose_two_ceil_ten_sqrt_le hn1
  have hexp : -2 * (20 * (n : ℝ)) ^ 2 / (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ) ≤ -(13 * n) := by
    rw [div_le_iff₀ hC0]
    nlinarith [hCle, hnR, hC0]
  have hprod : (n.choose ⌈10 * Real.sqrt n⌉₊ : ℝ)
        * Real.exp (-2 * (20 * (n : ℝ)) ^ 2 / (⌈10 * Real.sqrt n⌉₊.choose 2 : ℝ))
      ≤ Real.exp n * Real.exp (-(13 * (n : ℝ))) :=
    mul_le_mul (choose_le_exp_card n _) (Real.exp_le_exp.mpr hexp)
      (Real.exp_pos _).le (Real.exp_pos _).le
  have heq : Real.exp (n : ℝ) * Real.exp (-(13 * (n : ℝ))) = Real.exp (-(12 * (n : ℝ))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlb : 1 / δ < (n : ℝ) := by
    have hk : (⌈1 / δ⌉₊ : ℕ) + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hkR : ((⌈1 / δ⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
    linarith [Nat.le_ceil (1 / δ : ℝ)]
  have hE : 1 / δ < Real.exp (12 * (n : ℝ)) := by
    linarith [Real.add_one_le_exp (12 * (n : ℝ))]
  have hlast : Real.exp (-(12 * (n : ℝ))) < δ := by
    have hEpos : (0 : ℝ) < Real.exp (12 * (n : ℝ)) := Real.exp_pos _
    have h3 : 1 < Real.exp (12 * (n : ℝ)) * δ := (div_lt_iff₀ hδ).mp hE
    rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ hEpos]
    linarith
  linarith [hprod, heq, hlast]

/-- **Theorem 5.3.2** (Hajós).  With high probability `G(n, 1/2)` has no `K t`-subdivision for
`t = ⌈10 √n⌉`, stated in the chapter's explicit `δ`–`N` form. -/
theorem binomialRandom_hasKSubdivision_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩).real
          {G | HasKSubdivision G ⌈10 * Real.sqrt n⌉₊} < δ := by
  sorry

end ProbMethodCombinatorics
