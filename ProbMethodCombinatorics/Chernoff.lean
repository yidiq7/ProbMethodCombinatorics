import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.SimpleGraph.Paths
import ProbMethodCombinatorics.Alterations

/-!
# Chapter 5: Chernoff Bound

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Chapter 5.

A uniform `±1` sequence is a function `Fin n → Bool`, read through `toSign`, and the Chernoff
bound is stated as a count over the `2 ^ n` such sequences.  This keeps the chapter's two
applications — discrepancy and nearly equiangular vectors — in the same finite-averaging
idiom as Chapters 1–3, and matches how the book uses the bound.
-/

namespace ProbMethodCombinatorics

open Finset

/-- The `±1` value of a Boolean: `true ↦ 1`, `false ↦ -1`. -/
def toSign (b : Bool) : ℝ := if b then 1 else -1

/-- Negating a Boolean negates its `±1` value. -/
theorem toSign_not (b : Bool) : toSign (!b) = -toSign b := by
  cases b <;> norm_num [toSign]

/-- **Chernoff bound** (Zhao, Theorem 5.0.1): for `S = X₁ + ⋯ + Xₙ` with the `Xᵢ` uniform iid
`±1`, `ℙ(S ≥ λ√n) ≤ exp (-λ² / 2)`, stated as a count over the `2 ^ n` sign sequences.

`0 < n` is necessary, not bookkeeping: at `n = 0` the empty sum is `0` and the threshold
`λ √0` is `0`, so every sign sequence — there is one — meets the condition, while the bound
`exp (-λ²/2) · 2 ^ 0` is strictly below `1`.  The optimisation `t = λ / √n` in the proof needs
it too. -/
theorem card_filter_le_exp_mul (n : ℕ) (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    (((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt n ≤ ∑ i, toSign (x i)).card : ℝ)
      ≤ Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := Real.sqrt n
  have hs : 0 < s := Real.sqrt_pos.mpr hn'
  have hss : s * s = (n : ℝ) := Real.mul_self_sqrt hn'.le
  set t : ℝ := lam / s with ht_def
  have ht : 0 < t := div_pos hlam hs
  -- Transfer the threshold through the strictly monotone `x ↦ exp (t * x)`.
  have hsub : ((univ : Finset (Fin n → Bool)).filter
        fun x => lam * s ≤ ∑ i, toSign (x i))
      ⊆ (univ : Finset (Fin n → Bool)).filter
        fun x => Real.exp (t * (lam * s)) ≤ Real.exp (t * ∑ i, toSign (x i)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, Real.exp_le_exp] at hx ⊢
    exact mul_le_mul_of_nonneg_left hx ht.le
  -- The moment generating function factorises over the coordinates.
  have hmgf : ∑ x : Fin n → Bool, Real.exp (t * ∑ i, toSign (x i))
      = (Real.exp t + Real.exp (-t)) ^ n := by
    have hx : ∀ x : Fin n → Bool, Real.exp (t * ∑ i, toSign (x i))
        = ∏ i, Real.exp (t * toSign (x i)) := by
      intro x
      rw [Finset.mul_sum, Real.exp_sum]
    have hpow : (∑ b : Bool, Real.exp (t * toSign b)) ^ n
        = ∑ p : Fin n → Bool, ∏ i, Real.exp (t * toSign (p i)) :=
      Fintype.sum_pow (fun b : Bool => Real.exp (t * toSign b)) n
    simp only [hx]
    rw [← hpow]
    congr 1
    simp [toSign]
  have hexpn : (n : ℝ) * (t ^ 2 / 2) = lam ^ 2 / 2 := by
    rw [← hss, ht_def]
    field_simp
  have hthr : t * (lam * s) = lam ^ 2 := by
    rw [ht_def]
    field_simp
  calc (((univ : Finset (Fin n → Bool)).filter
          fun x => lam * s ≤ ∑ i, toSign (x i)).card : ℝ)
      ≤ (((univ : Finset (Fin n → Bool)).filter
          fun x => Real.exp (t * (lam * s)) ≤ Real.exp (t * ∑ i, toSign (x i))).card : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ (∑ x : Fin n → Bool, Real.exp (t * ∑ i, toSign (x i)))
          / Real.exp (t * (lam * s)) :=
        card_filter_le_sum_div _ _ (fun x _ => (Real.exp_pos _).le) (Real.exp_pos _)
    _ = (Real.exp t + Real.exp (-t)) ^ n / Real.exp (lam ^ 2) := by rw [hmgf, hthr]
    _ ≤ (2 * Real.exp (t ^ 2 / 2)) ^ n / Real.exp (lam ^ 2) := by
        have hcosh : Real.exp t + Real.exp (-t) = 2 * Real.cosh t := by
          rw [Real.cosh_eq]; ring
        have h2 : Real.exp t + Real.exp (-t) ≤ 2 * Real.exp (t ^ 2 / 2) := by
          rw [hcosh]
          have := Real.cosh_le_exp_half_sq t
          linarith
        have hnn : (0 : ℝ) ≤ Real.exp t + Real.exp (-t) := by positivity
        gcongr

    _ = 2 ^ n * Real.exp (lam ^ 2 / 2) / Real.exp (lam ^ 2) := by
        rw [mul_pow, ← Real.exp_nat_mul, hexpn]
    _ = Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
        rw [mul_comm (Real.exp (-lam ^ 2 / 2)), mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring

/-- **Two-sided Chernoff bound** (Zhao, Corollary 5.0.3): `ℙ(|S| ≥ λ√n) ≤ 2 exp (-λ² / 2)`.

`0 < n` is necessary for the same reason as in `card_filter_le_exp_mul`. -/
theorem card_filter_abs_le_exp_mul (n : ℕ) (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam) :
    (((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|).card : ℝ)
      ≤ 2 * Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
  have hsum : ∀ x : Fin n → Bool, ∑ i, toSign (!x i) = -∑ i, toSign (x i) := by
    intro x
    simp [toSign_not]
  set A := (univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ ∑ i, toSign (x i)) with hA
  set B := (univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ -∑ i, toSign (x i)) with hB
  have hsub : (univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|) ⊆ A ∪ B := by
    intro x hx
    simp only [hA, hB, mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    rcases abs_cases (∑ i, toSign (x i)) with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl (h ▸ hx)
    · exact Or.inr (h ▸ hx)
  have hBA : B.card = A.card := by
    refine Finset.card_nbij' (fun x i => !x i) (fun x i => !x i) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [hA, hB, mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      rw [hsum]
      exact hx
    · intro x hx
      simp only [hA, hB, mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      rw [hsum, neg_neg]
      exact hx
    · intro x _
      funext i
      simp
    · intro x _
      funext i
      simp
  have hAle : (A.card : ℝ) ≤ Real.exp (-lam ^ 2 / 2) * 2 ^ n :=
    card_filter_le_exp_mul n hn hlam
  have h1 : ((univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|)).card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
  rw [hBA] at h1
  have h2 : (((univ : Finset (Fin n → Bool)).filter
      (fun x => lam * Real.sqrt n ≤ |∑ i, toSign (x i)|)).card : ℝ)
      ≤ (A.card : ℝ) + (A.card : ℝ) := by exact_mod_cast h1
  have h3 : (2 : ℝ) * Real.exp (-lam ^ 2 / 2) * 2 ^ n
      = 2 * (Real.exp (-lam ^ 2 / 2) * 2 ^ n) := by ring
  rw [h3]
  linarith

/-- The two-sided Chernoff bound `card_filter_abs_le_exp_mul` transported from `Fin S.card` to a
subset `S` of `Fin n`: the sign sequences are indexed by all of `Fin n`, but only the `S.card`
coordinates in `S` enter the sum, and the remaining coordinates contribute the same factor to
both sides.

`0 < S.card` is inherited from the hypothesis `0 < n` of the Chernoff bound. -/
theorem card_filter_abs_sum_subset_le {n : ℕ} (S : Finset (Fin n)) (hS : 0 < S.card)
    {lam : ℝ} (hlam : 0 < lam) :
    (((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt S.card ≤ |∑ i ∈ S, toSign (x i)|).card : ℝ)
      ≤ 2 * Real.exp (-lam ^ 2 / 2) * 2 ^ n := by
  let E : (Fin n → Bool) ≃ (Fin S.card → Bool) × ({i : Fin n // i ∉ S} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).trans
      (Equiv.prodCongr (Equiv.arrowCongr S.equivFin (Equiv.refl Bool)) (Equiv.refl _))
  have hEfst : ∀ (x : Fin n → Bool) (j : Fin S.card),
      (E x).1 j = x (S.equivFin.symm j) := fun _ _ => rfl
  have hsum : ∀ x : Fin n → Bool, ∑ j, toSign ((E x).1 j) = ∑ i ∈ S, toSign (x i) := by
    intro x
    simp only [hEfst]
    rw [Equiv.sum_comp S.equivFin.symm fun i : {i : Fin n // i ∈ S} => toSign (x i)]
    exact Finset.sum_coe_sort S fun i => toSign (x i)
  have hcard : ((univ : Finset (Fin n → Bool)).filter
        fun x => lam * Real.sqrt S.card ≤ |∑ i ∈ S, toSign (x i)|).card
      = ((univ : Finset (Fin S.card → Bool)).filter
          fun y => lam * Real.sqrt S.card ≤ |∑ j, toSign (y j)|).card
        * Fintype.card ({i : Fin n // i ∉ S} → Bool) := by
    rw [← Finset.card_univ (α := ({i : Fin n // i ∉ S} → Bool)), ← Finset.card_product]
    refine Finset.card_equiv E ?_
    intro x
    simp only [mem_filter, mem_univ, true_and, Finset.mem_product, and_true, hsum]
  have hprod : Fintype.card (Fin S.card → Bool) * Fintype.card ({i : Fin n // i ∉ S} → Bool)
      = 2 ^ n := by
    rw [← Fintype.card_prod, Fintype.card_congr E.symm]
    simp
  have hpow : (2 : ℝ) ^ S.card * (Fintype.card ({i : Fin n // i ∉ S} → Bool) : ℝ) = 2 ^ n := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hprod
    simpa using h
  have hnn : (0 : ℝ) ≤ (Fintype.card ({i : Fin n // i ∉ S} → Bool) : ℝ) := Nat.cast_nonneg _
  calc (((univ : Finset (Fin n → Bool)).filter
          fun x => lam * Real.sqrt S.card ≤ |∑ i ∈ S, toSign (x i)|).card : ℝ)
      = (((univ : Finset (Fin S.card → Bool)).filter
            fun y => lam * Real.sqrt S.card ≤ |∑ j, toSign (y j)|).card : ℝ)
          * (Fintype.card ({i : Fin n // i ∉ S} → Bool) : ℝ) := by
        rw [hcard]; push_cast; ring
    _ ≤ (2 * Real.exp (-lam ^ 2 / 2) * 2 ^ S.card)
          * (Fintype.card ({i : Fin n // i ∉ S} → Bool) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (card_filter_abs_le_exp_mul S.card hS hlam) hnn
    _ = 2 * Real.exp (-lam ^ 2 / 2)
          * ((2 : ℝ) ^ S.card * (Fintype.card ({i : Fin n // i ∉ S} → Bool) : ℝ)) := by ring
    _ = 2 * Real.exp (-lam ^ 2 / 2) * 2 ^ n := by rw [hpow]

/-- **Discrepancy of a set system** (Zhao, Theorem 5.1.1): any `m` subsets of `[n]` admit a
`±1` assignment whose sum on every set is `O(√(n log m))` — here, at most `2 √(n log m)`. -/
theorem exists_toSign_abs_sum_le {n : ℕ} (F : Finset (Finset (Fin n))) (hF : 2 ≤ F.card) :
    ∃ x : Fin n → Bool, ∀ S ∈ F,
      |∑ i ∈ S, toSign (x i)| ≤ 2 * Real.sqrt (n * Real.log F.card) := by
  have hm2 : (2 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hF
  have hmpos : (0 : ℝ) < (F.card : ℝ) := by linarith
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exfalso
      have hsub : F ⊆ {(∅ : Finset (Fin 0))} := by
        intro S _
        simp [Finset.eq_empty_of_isEmpty S]
      have h1 := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at h1
      omega
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set L : ℝ := Real.log F.card with hLdef
  have hLpos : 0 < L := Real.log_pos (by linarith)
  set T : ℝ := 2 * Real.sqrt ((n : ℝ) * L) with hTdef
  have hTpos : 0 < T := by
    have h := Real.sqrt_pos.mpr (mul_pos hnR hLpos)
    rw [hTdef]; linarith
  obtain ⟨bad, hbad⟩ : ∃ bad : Finset (Fin n) → Finset (Fin n → Bool),
      ∀ S, bad S = (univ : Finset (Fin n → Bool)).filter
        fun x => T < |∑ i ∈ S, toSign (x i)| := ⟨_, fun _ => rfl⟩
  have key : ∀ (S : Finset (Fin n)) (u : ℝ), 0 < u → (S.card : ℝ) * u ≤ (n : ℝ) * L →
      ((bad S).card : ℝ) ≤ 2 * Real.exp (-(2 * u)) * 2 ^ n := by
    intro S u hu hku
    rcases Nat.eq_zero_or_pos S.card with hk | hk
    · have hbe : bad S = ∅ := by
        rw [hbad S, Finset.card_eq_zero.mp hk]
        ext x
        simp only [mem_filter, mem_univ, true_and, Finset.sum_empty, abs_zero,
          Finset.notMem_empty, iff_false, not_lt]
        exact hTpos.le
      rw [hbe, Finset.card_empty, Nat.cast_zero]
      positivity
    · have hkR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hk
      have hsq : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.mpr hkR
      set lam : ℝ := T / Real.sqrt (S.card : ℝ) with hlamdef
      have hlampos : 0 < lam := div_pos hTpos hsq
      have hthr : lam * Real.sqrt (S.card : ℝ) = T := by
        rw [hlamdef]; field_simp
      have hsub : bad S ⊆ (univ : Finset (Fin n → Bool)).filter
          fun x => lam * Real.sqrt (S.card : ℝ) ≤ |∑ i ∈ S, toSign (x i)| := by
        intro x hx
        rw [hbad S] at hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        rw [hthr]
        exact hx.le
      have h1 : ((bad S).card : ℝ) ≤ 2 * Real.exp (-lam ^ 2 / 2) * 2 ^ n :=
        le_trans ((Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub))
          (card_filter_abs_sum_subset_le S hk hlampos)
      have hlamsq : lam ^ 2 = 4 * ((n : ℝ) * L / (S.card : ℝ)) := by
        rw [hlamdef, div_pow, Real.sq_sqrt hkR.le, hTdef, mul_pow,
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) * L)]
        ring
      have hu' : u ≤ (n : ℝ) * L / (S.card : ℝ) := by
        rw [le_div_iff₀ hkR]; linarith
      have hexp : -lam ^ 2 / 2 ≤ -(2 * u) := by rw [hlamsq]; linarith
      refine le_trans h1 ?_
      have he := Real.exp_le_exp.mpr hexp
      have hp : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith [he, hp]
  have hcard_le : ∀ S : Finset (Fin n), (S.card : ℝ) ≤ (n : ℝ) := by
    intro S
    have h : S.card ≤ n := by simpa using Finset.card_le_univ S
    exact_mod_cast h
  have hc1 : ∀ S ∈ F, ((bad S).card : ℝ) ≤ 2 * Real.exp (-(2 * L)) * 2 ^ n := fun S _ =>
    key S L hLpos (mul_le_mul_of_nonneg_right (hcard_le S) hLpos.le)
  have hc2 : ∃ S ∈ F, ((bad S).card : ℝ) < 2 * Real.exp (-(2 * L)) * 2 ^ n := by
    obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
    obtain ⟨S, hSF, hSne⟩ : ∃ S ∈ F, S ≠ (univ : Finset (Fin n)) := by
      by_cases h : A = univ
      · exact ⟨B, hB, fun hBu => hAB (h.trans hBu.symm)⟩
      · exact ⟨A, hA, h⟩
    have hSlt : S.card < n := by
      have hss : S ⊂ univ := lt_of_le_of_ne (Finset.subset_univ S) hSne
      simpa using Finset.card_lt_card hss
    refine ⟨S, hSF, ?_⟩
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    rcases Nat.eq_zero_or_pos S.card with hk | hk
    · have h1 := key S (2 * L) (by linarith) (by
        rw [hk]; push_cast; nlinarith [mul_pos hnR hLpos])
      have he : Real.exp (-(2 * (2 * L))) < Real.exp (-(2 * L)) :=
        Real.exp_lt_exp.mpr (by linarith)
      nlinarith [h1, he, hp]
    · have hkR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hk
      have hSltR : (S.card : ℝ) < (n : ℝ) := by exact_mod_cast hSlt
      have hu : 0 < (n : ℝ) * L / (S.card : ℝ) := by positivity
      have hku : (S.card : ℝ) * ((n : ℝ) * L / (S.card : ℝ)) ≤ (n : ℝ) * L :=
        le_of_eq (by field_simp)
      have h1 := key S ((n : ℝ) * L / (S.card : ℝ)) hu hku
      have hLu : L < (n : ℝ) * L / (S.card : ℝ) := by
        rw [lt_div_iff₀ hkR]; nlinarith [mul_pos hLpos (sub_pos.mpr hSltR)]
      have he : Real.exp (-(2 * ((n : ℝ) * L / (S.card : ℝ)))) < Real.exp (-(2 * L)) :=
        Real.exp_lt_exp.mpr (by linarith)
      nlinarith [h1, he, hp]
  by_contra hcon
  have hall : ∀ x : Fin n → Bool, ∃ S ∈ F, T < |∑ i ∈ S, toSign (x i)| := by
    intro x
    by_contra h
    exact hcon ⟨x, fun S hS => not_lt.mp fun hlt => h ⟨S, hS, hlt⟩⟩
  have hsubU : (univ : Finset (Fin n → Bool)) ⊆ F.biUnion bad := by
    intro x _
    obtain ⟨S, hSF, hlt⟩ := hall x
    refine Finset.mem_biUnion.mpr ⟨S, hSF, ?_⟩
    rw [hbad S]
    simp only [mem_filter, mem_univ, true_and]
    exact hlt
  have hbig : ((2 : ℝ) ^ n) ≤ ((F.biUnion bad).card : ℝ) := by
    have h := Finset.card_le_card hsubU
    have h2 : (univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
    rw [h2] at h
    exact_mod_cast h
  have hunion : ((F.biUnion bad).card : ℝ) ≤ ∑ S ∈ F, ((bad S).card : ℝ) := by
    have h := Finset.card_biUnion_le (s := F) (t := bad)
    calc ((F.biUnion bad).card : ℝ) ≤ ((∑ S ∈ F, (bad S).card : ℕ) : ℝ) := by exact_mod_cast h
      _ = ∑ S ∈ F, ((bad S).card : ℝ) := by push_cast; ring
  have hsum : ∑ S ∈ F, ((bad S).card : ℝ)
      < (F.card : ℝ) * (2 * Real.exp (-(2 * L)) * 2 ^ n) := by
    have h := Finset.sum_lt_sum (s := F) (f := fun S => ((bad S).card : ℝ))
      (g := fun _ => 2 * Real.exp (-(2 * L)) * 2 ^ n) hc1 hc2
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hfin : (F.card : ℝ) * (2 * Real.exp (-(2 * L)) * 2 ^ n) ≤ 2 ^ n := by
    have hv : Real.exp (-L) * (F.card : ℝ) = 1 := by
      rw [Real.exp_neg, hLdef, Real.exp_log hmpos]
      field_simp
    have hepos : (0 : ℝ) < Real.exp (-L) := Real.exp_pos _
    have h2 : Real.exp (-(2 * L)) = Real.exp (-L) * Real.exp (-L) := by
      rw [← Real.exp_add]; ring_nf
    have h2e : 2 * Real.exp (-L) ≤ 1 := by
      nlinarith [hv, mul_nonneg hepos.le (sub_nonneg.mpr hm2)]
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hcalc : (F.card : ℝ) * (2 * (Real.exp (-L) * Real.exp (-L)) * 2 ^ n)
        = 2 * Real.exp (-L) * 2 ^ n * (Real.exp (-L) * (F.card : ℝ)) := by ring
    rw [h2, hcalc, hv, mul_one]
    nlinarith [h2e, hp]
  linarith

section SignFamily

/-- **Exponentially many sign vectors with small pairwise correlations**, the counting core of
Zhao's Theorem 5.2.1.

For `0 < β ≤ 1` there are at least `exp (β ^ 2 * m / 2) / 4` sign sequences in `Fin m → Bool`
whose pairwise correlations `∑ j, toSign (z j) * toSign (w j)` are all at most `β * m` in
absolute value; divided by `m`, these are that many unit vectors in `ℝ ^ m` with pairwise inner
products in `[-β, β]`.

`β ≤ 1` is not bookkeeping: for `β > 1` the correlation bound holds for every pair, so no family
can beat `2 ^ m`, while `exp (β ^ 2 * m / 2) / 4` can exceed `2 ^ m`. -/
theorem exists_large_sign_family (m : ℕ) (hm : 0 < m) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ T : Finset (Fin m → Bool), Real.exp (β ^ 2 * m / 2) / 4 ≤ T.card ∧
      ∀ z ∈ T, ∀ w ∈ T, z ≠ w → |∑ j, toSign (z j) * toSign (w j)| ≤ β * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsmpos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hsm : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt hmR.le
  set lam : ℝ := β * Real.sqrt m with hlamdef
  have hlam : 0 < lam := mul_pos hβ hsmpos
  have hlm : lam * Real.sqrt m = β * m := by rw [hlamdef, mul_assoc, hsm]
  have hlam2 : lam ^ 2 = β ^ 2 * m := by rw [hlamdef, mul_pow, Real.sq_sqrt hmR.le]
  set Bad : Finset (Fin m → Bool) :=
    (univ : Finset (Fin m → Bool)).filter
      (fun u => lam * Real.sqrt m ≤ |∑ i, toSign (u i)|) with hBaddef
  have hBadcard : (Bad.card : ℝ) ≤ 2 * Real.exp (-(β ^ 2 * m) / 2) * 2 ^ m := by
    have h := card_filter_abs_le_exp_mul m hm hlam
    rw [← hBaddef, hlam2] at h
    exact h
  -- A sign sequence outside `Bad` has a small signed sum.
  have hnotBad : ∀ u : Fin m → Bool, u ∉ Bad → |∑ i, toSign (u i)| ≤ β * m := by
    intro u hu
    by_contra hcon
    exact hu (by rw [hBaddef, mem_filter]; exact ⟨mem_univ u, by rw [hlm]; linarith⟩)
  -- The zero difference is bad, so `Bad` is nonempty.
  have hzeroBad : (fun _ => false : Fin m → Bool) ∈ Bad := by
    rw [hBaddef, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hzsum : ∑ i : Fin m, toSign ((fun _ => false : Fin m → Bool) i) = -(m : ℝ) := by
      simp [toSign, Finset.sum_const, Finset.card_univ]
    rw [hlm, hzsum, abs_neg, abs_of_nonneg hmR.le]
    exact mul_le_of_le_one_left hmR.le hβ1
  have hBadpos : 1 ≤ Bad.card := Finset.card_pos.mpr ⟨_, hzeroBad⟩
  -- Correlations are read off from the difference sequence.
  have hmulsign : ∀ a b : Bool, toSign a * toSign b = -toSign (xor a b) := by
    intro a b; cases a <;> cases b <;> norm_num [toSign]
  have hcorr : ∀ z w : Fin m → Bool,
      |∑ j, toSign (z j) * toSign (w j)| = |∑ j, toSign (xor (z j) (w j))| := by
    intro z w
    have h : ∑ j, toSign (z j) * toSign (w j) = -∑ j, toSign (xor (z j) (w j)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => hmulsign (z j) (w j))
    rw [h, abs_neg]
  -- Greedy selection: keep adding a sequence whose difference from every chosen one is good.
  have greedy : ∀ t : ℕ, t * Bad.card ≤ 2 ^ m →
      ∃ T : Finset (Fin m → Bool), T.card = t ∧
        ∀ z ∈ T, ∀ w ∈ T, z ≠ w → (fun j => xor (z j) (w j)) ∉ Bad := by
    intro t
    induction t with
    | zero => intro _; exact ⟨∅, rfl, by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨T, hTc, hTg⟩ := ih (le_trans (Nat.mul_le_mul (Nat.le_succ t) (le_refl _)) ht)
      have hBlcard : (T.biUnion (fun x => Bad.image (fun u j => xor (x j) (u j)))).card
          ≤ t * Bad.card := by
        refine le_trans (Finset.card_biUnion_le_card_mul _ _ _ ?_) (le_of_eq (by rw [hTc]))
        exact fun x _ => Finset.card_image_le
      have hcard : (T.biUnion (fun x => Bad.image (fun u j => xor (x j) (u j)))).card
          < (univ : Finset (Fin m → Bool)).card := by
        have huniv : (univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
        have h1 : t * Bad.card + Bad.card ≤ 2 ^ m := by rw [← Nat.succ_mul]; exact ht
        omega
      obtain ⟨y, hy⟩ : ∃ y : Fin m → Bool,
          y ∉ T.biUnion (fun x => Bad.image (fun u j => xor (x j) (u j))) := by
        by_contra hcon
        have : (univ : Finset (Fin m → Bool)) ⊆
            T.biUnion (fun x => Bad.image (fun u j => xor (x j) (u j))) := by
          intro a _
          by_contra ha
          exact hcon ⟨a, ha⟩
        exact absurd (Finset.card_le_card this) (by omega)
      have hkey : ∀ x ∈ T, (fun j => xor (y j) (x j)) ∉ Bad := by
        intro x hx hmem
        refine hy (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr
          ⟨fun j => xor (y j) (x j), hmem, ?_⟩⟩)
        funext j
        cases hxj : x j <;> cases hyj : y j <;> simp [hxj, hyj]
      have hyT : y ∉ T := by
        intro hmem
        refine hy (Finset.mem_biUnion.mpr ⟨y, hmem, Finset.mem_image.mpr
          ⟨fun _ => false, hzeroBad, ?_⟩⟩)
        funext j
        simp
      refine ⟨insert y T, by rw [Finset.card_insert_of_notMem hyT, hTc], ?_⟩
      intro z hz w hw hzw
      rw [Finset.mem_insert] at hz hw
      rcases hz with rfl | hz
      · rcases hw with rfl | hw
        · exact absurd rfl hzw
        · exact hkey w hw
      · rcases hw with rfl | hw
        · intro hmem
          refine hkey z hz ?_
          have hfe : (fun j => xor (w j) (z j)) = (fun j => xor (z j) (w j)) := by
            funext j
            cases hzj : z j <;> cases hwj : w j <;> simp
          rw [hfe]
          exact hmem
        · exact hTg z hz w hw hzw
  set E : ℝ := Real.exp (β ^ 2 * m / 2) with hEdef
  have hE : 0 < E := Real.exp_pos _
  by_cases hsmall : E / 4 ≤ 1
  · refine ⟨{fun _ => true}, ?_, ?_⟩
    · rw [Finset.card_singleton]
      simpa using hsmall
    · intro z hz w hw hzw
      rw [Finset.mem_singleton] at hz hw
      exact absurd (hz.trans hw.symm) hzw
  · have hE4 : 4 < E := by
      by_contra hcon
      exact hsmall (by linarith)
    set t : ℕ := ⌈E / 4⌉₊ with htdef
    have htR : E / 4 ≤ (t : ℝ) := Nat.le_ceil _
    have htlt : (t : ℝ) < E / 2 := by
      have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ E / 4)
      rw [← htdef] at h
      linarith
    have hexp : Real.exp (-(β ^ 2 * m) / 2) = E⁻¹ := by
      rw [hEdef, ← Real.exp_neg]; congr 1; ring
    have hB2 : (Bad.card : ℝ) ≤ 2 * E⁻¹ * 2 ^ m := by rw [← hexp]; exact hBadcard
    have hstepR : (t : ℝ) * Bad.card ≤ 2 ^ m := by
      have h2 : (0 : ℝ) ≤ (Bad.card : ℝ) := Nat.cast_nonneg _
      have h3 : (t : ℝ) * Bad.card ≤ (E / 2) * (2 * E⁻¹ * 2 ^ m) :=
        mul_le_mul htlt.le hB2 h2 (by positivity)
      have h4 : (E / 2) * (2 * E⁻¹ * 2 ^ m) = (2 : ℝ) ^ m := by
        field_simp
      linarith
    have hstep : t * Bad.card ≤ 2 ^ m := by exact_mod_cast hstepR
    obtain ⟨T, hTc, hTg⟩ := greedy t hstep
    refine ⟨T, ?_, ?_⟩
    · rw [hTc]; exact htR
    · intro z hz w hw hzw
      rw [hcorr]
      exact hnotBad _ (hTg z hz w hw hzw)

end SignFamily

/-- **Exponentially many nearly equiangular vectors** (Zhao, Theorem 5.2.1): for every
`α ∈ (0, 1)` and `ε > 0` there is `c > 0` such that for all large `n`, `ℝⁿ` contains at least
`2 ^ (c n)` unit vectors whose pairwise inner products all lie in `[α - ε, α + ε]`.

Contrast the exactly-equiangular case, where at most `n + 1` vectors are possible.

The bound holds only for large `n`, and the `n₀` is not bookkeeping.  At `n = 0` there is no
unit vector at all while `2 ^ (c * 0) = 1` demands a non-empty `S`; at `n = 1` the only unit
vectors are `±1`, whose inner product is `-1`, so for small `ε` at most one of them qualifies
while `2 ^ c > 1` demands two.  The book states the theorem for every `n`, which is loose. -/
theorem exists_nearly_equiangular {α ε : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ ∀ n ≥ n₀, ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
      (2 : ℝ) ^ (c * n) ≤ S.card ∧ (∀ v ∈ S, ‖v‖ = 1) ∧
        ∀ v ∈ S, ∀ w ∈ S, v ≠ w → inner ℝ v w ∈ Set.Icc (α - ε) (α + ε) := by
  -- Freeze `k = ⌊α n⌋` coordinates at `+1` and let `exists_large_sign_family` choose the
  -- remaining `m = n - k`; the frozen block contributes `k / n ≈ α` to every inner product and
  -- the free block contributes at most `β = ε' / 2` in absolute value.
  obtain ⟨hα0, hα1⟩ := hα
  set ε' : ℝ := min ε 1
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set β : ℝ := ε' / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith only [hε'0]
  have hβ1 : β ≤ 1 := by rw [hβdef]; linarith only [hε'0, hε'1]
  set A : ℝ := β ^ 2 * (1 - α) / 2 with hAdef
  have h1α : 0 < 1 - α := by linarith only [hα1]
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A / (2 * Real.log 2), ⌈2 / ε'⌉₊ + ⌈2 * Real.log 4 / A⌉₊ + 1, by positivity, ?_⟩
  intro n hn
  -- `n₀` is a sum of ceilings, so every real threshold entering it is at most `n`.
  have hceil : ∀ x : ℝ, ⌈x⌉₊ ≤ n → x ≤ (n : ℝ) :=
    fun x h => (Nat.le_ceil x).trans (by exact_mod_cast h)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hcast1 : (2 : ℝ) / ε' ≤ n := hceil _ (by omega)
  have hcast2 : 2 * Real.log 4 / A ≤ n := hceil _ (by omega)
  have hεn : 2 ≤ ε' * (n : ℝ) := by rw [div_le_iff₀ hε'0] at hcast1; linarith only [hcast1]
  -- Split the coordinates into a block of `k ≈ α n` frozen ones and `m` free ones.
  set k : ℕ := ⌊α * n⌋₊
  have hkle : (k : ℝ) ≤ α * n := Nat.floor_le (by positivity)
  have hklt : α * n < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkn : k < n := by
    exact_mod_cast hkle.trans_lt ((mul_lt_mul_of_pos_right hα1 hnpos).trans_eq (one_mul _))
  set m : ℕ := n - k
  have hnkm : n = k + m := by omega
  have hm0 : 0 < m := by omega
  have hkm : (k : ℝ) + (m : ℝ) = (n : ℝ) := by exact_mod_cast hnkm.symm
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hmn : (m : ℝ) ≤ (n : ℝ) := by linarith only [hkm, hk0]
  have hmlow : (1 - α) * n ≤ (m : ℝ) := by linarith only [hkm, hkle]
  obtain ⟨e⟩ : Nonempty (Fin n ≃ (Fin k ⊕ Fin m)) :=
    ⟨(Equiv.cast (congrArg Fin hnkm)).trans finSumFinEquiv.symm⟩
  have hsplit : ∀ f : Fin n → ℝ,
      ∑ i, f i = (∑ a : Fin k, f (e.symm (Sum.inl a))) + ∑ b : Fin m, f (e.symm (Sum.inr b)) :=
    fun f => (Equiv.sum_comp e.symm f).symm.trans (Fintype.sum_sum_type _)
  obtain ⟨T, hTcard, hTgood⟩ := exists_large_sign_family m hm0 hβ0 hβ1
  -- The counting is done; only the real inequalities above carry into the geometry below.
  clear hn hkn hnkm hk0 hε'1 hceil hcast1 hlog2 hα0 hα1 h1α hβ1 hm0
  set sgn : (Fin m → Bool) → Fin n → ℝ :=
    fun z i => toSign (Sum.elim (fun _ => true) z (e i)) with hsgn
  set vec : (Fin m → Bool) → EuclideanSpace ℝ (Fin n) :=
    fun z => WithLp.toLp 2 (fun i => sgn z i / Real.sqrt n)
  have hsnpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hvecapp : ∀ z i, vec z i = sgn z i / Real.sqrt n := fun z i => rfl
  have hvl : ∀ z a, sgn z (e.symm (Sum.inl a)) = 1 := fun z a => by simp [hsgn, toSign]
  have hvr : ∀ z b, sgn z (e.symm (Sum.inr b)) = toSign (z b) := fun z b => by simp [hsgn]
  -- The inner product of two such vectors is the normalised correlation of the sign sequences.
  have hinner : ∀ z w, (inner ℝ (vec z) (vec w) : ℝ)
      = ((k : ℝ) + ∑ b : Fin m, toSign (z b) * toSign (w b)) / n := by
    intro z w
    have hterm : ∀ i : Fin n, (inner ℝ (vec z i) (vec w i) : ℝ) = sgn z i * sgn w i / n := by
      intro i
      rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, hvecapp, hvecapp,
        div_mul_div_comm, hsn, mul_comm (sgn w i)]
    rw [PiLp.inner_apply, Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div,
      hsplit (fun i => sgn z i * sgn w i)]
    congr 2
    · simp [hvl]
    · exact Finset.sum_congr rfl (fun b _ => by rw [hvr, hvr])
  -- Every `vec z` is a unit vector: its self-correlation is the full count `k + m = n`.
  have hnorm : ∀ z, ‖vec z‖ = 1 := by
    intro z
    have hone : ∀ b : Bool, toSign b * toSign b = 1 := by
      intro b; cases b <;> norm_num [toSign]
    have h2 : ‖vec z‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hinner, Finset.sum_congr rfl (fun b _ => hone (z b)),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hkm,
        div_self hnpos.ne']
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by rw [h2, one_pow])
  -- Distinct sign sequences give distinct vectors.
  have hvecinj : Function.Injective vec := by
    intro z w h
    funext b
    have h' : vec z (e.symm (Sum.inr b)) = vec w (e.symm (Sum.inr b)) := by rw [h]
    rw [hvecapp, hvecapp, div_left_inj' (ne_of_gt hsnpos), hvr, hvr] at h'
    rcases hz : z b <;> rcases hw : w b <;> simp [toSign, hz, hw] at h' ⊢ <;> norm_num at h'
  have hmem : ∀ u ∈ T.map ⟨vec, hvecinj⟩, ∃ z ∈ T, vec z = u :=
    fun _ hu => Finset.mem_map.1 hu
  refine ⟨T.map ⟨vec, hvecinj⟩, ?_, ?_, ?_⟩
  · -- `2 ^ (c n) = exp (A n / 2)`, and `n ≥ 2 log 4 / A` makes that at least `4`, so the
    -- factor `4` lost in `hTcard` is paid for by one of the two halves of
    -- `exp (A n) ≤ exp (β ^ 2 * m / 2)`.
    rw [Finset.card_map]
    have hpow : (2 : ℝ) ^ (A / (2 * Real.log 2) * n) = Real.exp (A * n / 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; congr 1; field_simp
    have h4 : (4 : ℝ) ≤ Real.exp (A * n / 2) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 4)).symm.trans_le
        (Real.exp_le_exp.mpr (by rw [div_le_iff₀ hA0] at hcast2; linarith only [hcast2]))
    have hAm : A * n / 2 + A * n / 2 ≤ β ^ 2 * m / 2 := by
      rw [hAdef]; linarith only [mul_le_mul_of_nonneg_left hmlow (sq_nonneg β)]
    have e1 : Real.exp (A * n / 2) * Real.exp (A * n / 2) ≤ Real.exp (β ^ 2 * m / 2) :=
      (Real.exp_add _ _).symm.trans_le (Real.exp_le_exp.mpr hAm)
    rw [hpow]
    refine le_trans ?_ hTcard
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith only [e1, mul_le_mul_of_nonneg_left h4 (Real.exp_pos (A * n / 2)).le]
  · intro u hu
    obtain ⟨z, -, rfl⟩ := hmem u hu
    exact hnorm z
  · intro u hu u' hu' huu'
    obtain ⟨z, hz, rfl⟩ := hmem u hu
    obtain ⟨z', hz', rfl⟩ := hmem u' hu'
    have hne : z ≠ z' := fun h => huu' (by rw [h])
    have hs := hTgood z hz z' hz' hne
    rw [abs_le] at hs
    -- The free block moves the correlation by at most `β m ≤ ε' n / 2`, and `ε' n ≥ 2`
    -- absorbs the rounding error `α n - k < 1`.
    have hbm : β * (m : ℝ) ≤ ε' * n / 2 :=
      (mul_le_mul_of_nonneg_left hmn hβ0.le).trans_eq (by rw [hβdef]; ring)
    have hen : ε' * (n : ℝ) ≤ ε * n := mul_le_mul_of_nonneg_right hε'ε hnpos.le
    rw [Set.mem_Icc, hinner, le_div_iff₀ hnpos, div_le_iff₀ hnpos]
    constructor <;> linarith only [hkle, hklt, hs.1, hs.2, hbm, hen, hεn]

/-! ### §5.3 Graph subdivisions

Mathlib has no notion of a graph subdivision or topological minor — re-checked 2026-09-17, the
only `IsMinor` is for matroids — so §5.3 needs one authored here.

**The definition is the risk, not the theorem.**  §10.2's `boxProd`-versus-tensor episode is the
cautionary case: a plausible wrong definition makes every downstream statement true and useless.
This one was checked against the standard notion on all graphs with at most six vertices before
being committed, on anchors (a `K t` subgraph forces a subdivision; fewer than `binom(t,2)` edges
forbids one) and on the cases that discriminate a too-permissive definition from a too-strict
one — `C₅` and two triangles sharing a vertex have no `K₄`-subdivision, while `K₄` with an edge
subdivided and `K₃₃` do.
-/

section Subdivision

open SimpleGraph

variable {V : Type*}

/-- **A `K t`-subdivision in `G`**: `t` distinct *branch* vertices joined pairwise by paths whose
interiors are disjoint from one another and from every branch vertex.

`interior_disjoint` concludes that a vertex shared by two of the paths is an endpoint of the
first.  Combined with `interior_avoids_branch` that forces it to be a *common* endpoint, so the
paths meet only where they are required to — which is what "internally disjoint" means and what a
weaker condition would silently fail to capture. -/
structure IsKSubdivision (G : SimpleGraph V) (t : ℕ)
    (br : Fin t → V) (P : ∀ i j : Fin t, i ≠ j → G.Walk (br i) (br j)) : Prop where
  /-- The branch vertices are distinct. -/
  inj : Function.Injective br
  /-- Each connecting walk is a path. -/
  isPath : ∀ i j (h : i ≠ j), (P i j h).IsPath
  /-- No interior vertex of a path is a branch vertex. -/
  interior_avoids_branch : ∀ i j (h : i ≠ j) (k : Fin t) (v : V),
    v ∈ (P i j h).support → v ≠ br i → v ≠ br j → v ≠ br k
  /-- Paths for different pairs meet only at shared branch endpoints. -/
  interior_disjoint : ∀ i j (h : i ≠ j) (i' j' : Fin t) (h' : i' ≠ j'),
    ({i, j} : Finset (Fin t)) ≠ {i', j'} → ∀ v : V,
      v ∈ (P i j h).support → v ∈ (P i' j' h').support →
      v = br i ∨ v = br j

/-- `G` contains a subdivision of `K t`. -/
def HasKSubdivision (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ (br : Fin t → V) (P : ∀ i j : Fin t, i ≠ j → G.Walk (br i) (br j)),
    IsKSubdivision G t br P

/-- The non-adjacent branch pairs of a `K t`-subdivision, as ordered pairs `i < j`. -/
def branchNonAdj {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} (br : Fin t → V) : Finset (Fin t × Fin t) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ ¬ G.Adj (br q.1) (br q.2)

/-- A non-adjacent pair of branch vertices is joined by a walk with an interior vertex: the
walk cannot be `nil`, and the second vertex of a `cons` is neither endpoint. -/
private theorem exists_mem_support_ne_branch_of_not_adj {V : Type*} {G : SimpleGraph V}
    {t : ℕ} {br : Fin t → V} {P : ∀ i j : Fin t, i ≠ j → G.Walk (br i) (br j)}
    (h : IsKSubdivision G t br P) (i j : Fin t) (hij : i ≠ j)
    (hnadj : ¬ G.Adj (br i) (br j)) :
    ∃ v : V, v ∈ (P i j hij).support ∧ v ≠ br i ∧ v ≠ br j := by
  have hne : br i ≠ br j := fun e => hij (h.inj e)
  obtain ⟨u, hadj, q, hq⟩ :=
    Walk.not_nil_iff.mp (Walk.not_nil_of_ne (p := P i j hij) hne)
  refine ⟨u, ?_, hadj.ne', ?_⟩
  · rw [hq, Walk.support_cons]
    exact List.mem_cons_of_mem _ (Walk.start_mem_support q)
  · rintro rfl
    exact hnadj hadj

/-- **The counting core of Theorem 5.3.2.**  Every non-adjacent pair of branch vertices is
joined by a path of length at least two, so it consumes an interior vertex, and interiors of
different paths are disjoint from each other and from all `t` branch vertices.  Hence the
non-adjacent pairs and the branch vertices together fit inside `V`. -/
theorem card_branchNonAdj_add_le_of_isKSubdivision {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {t : ℕ} {br : Fin t → V}
    {P : ∀ i j : Fin t, i ≠ j → G.Walk (br i) (br j)} (h : IsKSubdivision G t br P) :
    (branchNonAdj G br).card + t ≤ Fintype.card V := by
  have hmem : ∀ q : Fin t × Fin t, q ∈ branchNonAdj G br →
      q.1 < q.2 ∧ ¬ G.Adj (br q.1) (br q.2) := by
    intro q hq
    simpa [branchNonAdj] using hq
  -- Ordered pairs are determined by their unordered pair.
  have hpair : ∀ i j i' j' : Fin t, i < j → i' < j' → (i, j) ≠ (i', j') →
      ({i, j} : Finset (Fin t)) ≠ {i', j'} := by
    intro i j i' j' hlt hlt' hne hset
    have h1 : i ∈ ({i', j'} : Finset (Fin t)) := by rw [← hset]; simp
    have h2 : j ∈ ({i', j'} : Finset (Fin t)) := by rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) (ne_of_lt hlt)
    · exact hne (by rw [h1, h2])
    · rw [← h1, ← h2] at hlt'; exact absurd hlt (lt_asymm hlt')
    · exact absurd (h1.trans h2.symm) (ne_of_lt hlt)
  -- Choose an interior vertex for every non-adjacent pair.
  have hex : ∀ q : Fin t × Fin t, ∃ v : V, q ∈ branchNonAdj G br →
      (∀ hij : q.1 ≠ q.2, v ∈ (P q.1 q.2 hij).support) ∧ v ≠ br q.1 ∧ v ≠ br q.2 := by
    intro q
    by_cases hq : q ∈ branchNonAdj G br
    · obtain ⟨hlt, hnadj⟩ := hmem q hq
      obtain ⟨v, hv, hv1, hv2⟩ :=
        exists_mem_support_ne_branch_of_not_adj h q.1 q.2 (ne_of_lt hlt) hnadj
      exact ⟨v, fun _ => ⟨fun _ => hv, hv1, hv2⟩⟩
    · exact ⟨br q.1, fun hq' => absurd hq' hq⟩
  choose f hf using hex
  have hcard : (branchNonAdj G br).card ≤
      (Finset.univ \ Finset.image br Finset.univ).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro q hq
      rw [Finset.mem_coe] at hq
      obtain ⟨hsupp, hne1, hne2⟩ := hf q hq
      obtain ⟨hlt, -⟩ := hmem q hq
      rw [Finset.mem_coe, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_image]
      rintro ⟨k, -, hk⟩
      exact h.interior_avoids_branch q.1 q.2 (ne_of_lt hlt) k (f q)
        (hsupp (ne_of_lt hlt)) hne1 hne2 hk.symm
    · intro q hq q' hq' heq
      rw [Finset.mem_coe] at hq hq'
      obtain ⟨i, j⟩ := q
      obtain ⟨i', j'⟩ := q'
      obtain ⟨hsupp, hne1, hne2⟩ := hf (i, j) hq
      obtain ⟨hsupp', -, -⟩ := hf (i', j') hq'
      obtain ⟨hlt, -⟩ := hmem (i, j) hq
      obtain ⟨hlt', -⟩ := hmem (i', j') hq'
      by_contra hqq
      have hmem2 : f (i, j) ∈ (P i' j' (ne_of_lt hlt')).support := by
        rw [heq]; exact hsupp' (ne_of_lt hlt')
      rcases h.interior_disjoint i j (ne_of_lt hlt) i' j' (ne_of_lt hlt')
        (hpair i j i' j' hlt hlt' hqq) (f (i, j))
        (hsupp (ne_of_lt hlt)) hmem2 with e | e
      · exact hne1 e
      · exact hne2 e
  have himg : (Finset.image br Finset.univ).card = t := by
    rw [Finset.card_image_of_injective _ h.inj, Finset.card_univ, Fintype.card_fin]
  rw [Finset.card_univ_sdiff, himg] at hcard
  have ht : t ≤ Fintype.card V := by
    simpa using Fintype.card_le_of_injective br h.inj
  omega

end Subdivision

end ProbMethodCombinatorics
