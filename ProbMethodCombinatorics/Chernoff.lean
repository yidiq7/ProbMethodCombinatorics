import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fintype.Pi
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

/-- **Discrepancy of a set system** (Zhao, Theorem 5.1.1): any `m` subsets of `[n]` admit a
`±1` assignment whose sum on every set is `O(√(n log m))` — here, at most `2 √(n log m)`. -/
theorem exists_toSign_abs_sum_le {n : ℕ} (F : Finset (Finset (Fin n))) (hF : 2 ≤ F.card) :
    ∃ x : Fin n → Bool, ∀ S ∈ F,
      |∑ i ∈ S, toSign (x i)| ≤ 2 * Real.sqrt (n * Real.log F.card) := by
  sorry

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
  set ε' : ℝ := min ε 1 with hε'def
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set β : ℝ := ε' / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β ≤ 1 := by rw [hβdef]; linarith
  set A : ℝ := β ^ 2 * (1 - α) / 2 with hAdef
  have hA0 : 0 < A := by
    have h1α : 0 < 1 - α := by linarith
    rw [hAdef]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A / (2 * Real.log 2), ⌈2 / ε'⌉₊ + ⌈2 * Real.log 4 / A⌉₊ + 1, by positivity, ?_⟩
  intro n hn
  have hc1 : ⌈(2 : ℝ) / ε'⌉₊ ≤ n := by omega
  have hc2 : ⌈2 * Real.log 4 / A⌉₊ ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hcast1 : (2 : ℝ) / ε' ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hc1)
  have hcast2 : 2 * Real.log 4 / A ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hc2)
  have hεn : 2 ≤ ε' * (n : ℝ) := by
    rw [div_le_iff₀ hε'0] at hcast1; linarith
  -- Split the coordinates into a block of `k ≈ α n` frozen ones and `m` free ones.
  set k : ℕ := ⌊α * n⌋₊ with hkdef
  have hkle : (k : ℝ) ≤ α * n := Nat.floor_le (by positivity)
  have hklt : α * n < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkn : k < n := by
    have h : (k : ℝ) < n := by nlinarith only [hkle, hα1, hnpos]
    exact_mod_cast h
  set m : ℕ := n - k with hmdef
  have hnkm : n = k + m := by omega
  have hm0 : 0 < m := by omega
  have hkm : (k : ℝ) + (m : ℝ) = (n : ℝ) := by exact_mod_cast hnkm.symm
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hmn : (m : ℝ) ≤ (n : ℝ) := by linarith
  have hmlow : (1 - α) * n ≤ (m : ℝ) := by linarith only [hkm, hkle]
  obtain ⟨e⟩ : Nonempty (Fin n ≃ (Fin k ⊕ Fin m)) :=
    ⟨(Equiv.cast (congrArg Fin hnkm)).trans finSumFinEquiv.symm⟩
  have hsplit : ∀ f : Fin n → ℝ,
      ∑ i, f i = (∑ a : Fin k, f (e.symm (Sum.inl a))) + ∑ b : Fin m, f (e.symm (Sum.inr b)) :=
    fun f => (Equiv.sum_comp e.symm f).symm.trans (Fintype.sum_sum_type _)
  obtain ⟨T, hTcard, hTgood⟩ := exists_large_sign_family m hm0 hβ0 hβ1
  set sgn : (Fin m → Bool) → Fin n → ℝ :=
    fun z i => toSign (Sum.elim (fun _ => true) z (e i)) with hsgn
  set vec : (Fin m → Bool) → EuclideanSpace ℝ (Fin n) :=
    fun z => WithLp.toLp 2 (fun i => sgn z i / Real.sqrt n) with hvec
  have hsnpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
  have hvecapp : ∀ z i, vec z i = sgn z i / Real.sqrt n := fun z i => rfl
  have hvl : ∀ z, ∀ a : Fin k, sgn z (e.symm (Sum.inl a)) = 1 := by
    intro z a; simp [hsgn, toSign]
  have hvr : ∀ z, ∀ b : Fin m, sgn z (e.symm (Sum.inr b)) = toSign (z b) := by
    intro z b; simp [hsgn]
  have hsgnsq : ∀ z i, sgn z i ^ 2 = 1 := by
    intro z i
    rw [hsgn]
    rcases Sum.elim (fun _ => true) z (e i) with _ | _ <;> norm_num [toSign]
  -- Every `vec z` is a unit vector.
  have hnorm : ∀ z, ‖vec z‖ = 1 := by
    intro z
    have h2 : ‖vec z‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hterm : ∀ i : Fin n, (vec z i) ^ 2 = 1 / (n : ℝ) := by
        intro i
        rw [hvecapp, div_pow, hsgnsq, Real.sq_sqrt hnpos.le]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    nlinarith only [h2, norm_nonneg (vec z)]
  -- The inner product of two such vectors is the normalised correlation of the sign sequences.
  have hinner : ∀ z w, (inner ℝ (vec z) (vec w) : ℝ)
      = ((k : ℝ) + ∑ b : Fin m, toSign (z b) * toSign (w b)) / n := by
    intro z w
    rw [PiLp.inner_apply]
    have hterm : ∀ i : Fin n, (inner ℝ (vec z i) (vec w i) : ℝ)
        = (sgn z i * sgn w i) / n := by
      intro i
      rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, hvecapp, hvecapp,
        div_mul_div_comm, hsn]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div]
    congr 1
    rw [hsplit (fun i => sgn z i * sgn w i)]
    congr 1
    · simp [hvl]
    · exact Finset.sum_congr rfl (fun b _ => by rw [hvr, hvr])
  -- Distinct sign sequences give distinct vectors.
  have hvecinj : Function.Injective vec := by
    intro z w h
    funext b
    have h' : vec z (e.symm (Sum.inr b)) = vec w (e.symm (Sum.inr b)) := by rw [h]
    rw [hvecapp, hvecapp, div_left_inj' (ne_of_gt hsnpos), hvr, hvr] at h'
    rcases hz : z b <;> rcases hw : w b <;> simp [toSign, hz, hw] at h' ⊢ <;> norm_num at h'
  refine ⟨T.map ⟨vec, hvecinj⟩, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    have hpow : (2 : ℝ) ^ (A / (2 * Real.log 2) * n) = Real.exp (A * n / 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      field_simp
    rw [hpow]
    refine le_trans ?_ hTcard
    have hlog4 : Real.log 4 ≤ A * n / 2 := by
      rw [div_le_iff₀ hA0] at hcast2; linarith
    have h4 : (4 : ℝ) ≤ Real.exp (A * n / 2) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 4)).symm.trans_le (Real.exp_le_exp.mpr hlog4)
    have hAm : A * n ≤ β ^ 2 * m / 2 := by
      rw [hAdef]; nlinarith only [hmlow, sq_nonneg β]
    have e1 : Real.exp (A * n) ≤ Real.exp (β ^ 2 * m / 2) := Real.exp_le_exp.mpr hAm
    have e2 : Real.exp (A * n / 2) * Real.exp (A * n / 2) = Real.exp (A * n) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith only [h4, e1, e2, Real.exp_pos (A * n / 2)]
  · intro u hu
    rw [Finset.mem_map] at hu
    obtain ⟨z, _, hzu⟩ := hu
    have hzu' : vec z = u := hzu
    rw [← hzu']
    exact hnorm z
  · intro u hu u' hu' huu'
    rw [Finset.mem_map] at hu hu'
    obtain ⟨z, hz, hzu⟩ := hu
    obtain ⟨z', hz', hz'u⟩ := hu'
    have hzu' : vec z = u := hzu
    have hz'u' : vec z' = u' := hz'u
    subst hzu'
    subst hz'u'
    clear hzu hz'u
    have hne : z ≠ z' := fun h => huu' (by rw [h])
    have hs := hTgood z hz z' hz' hne
    rw [abs_le] at hs
    have hbm : β * (m : ℝ) ≤ β * n := mul_le_mul_of_nonneg_left hmn hβ0.le
    have hbn : β * (n : ℝ) = ε' * n / 2 := by rw [hβdef]; ring
    have hen : ε' * (n : ℝ) ≤ ε * n := mul_le_mul_of_nonneg_right hε'ε hnpos.le
    rw [Set.mem_Icc, hinner]
    constructor
    · rw [le_div_iff₀ hnpos]
      linarith only [hkle, hklt, hs.1, hs.2, hbm, hbn, hen, hεn]
    · rw [div_le_iff₀ hnpos]
      linarith only [hkle, hklt, hs.1, hs.2, hbm, hbn, hen, hεn]

end ProbMethodCombinatorics
