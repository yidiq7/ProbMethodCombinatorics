import ProbMethodCombinatorics.LocalLemma

/-!
# Section 6.2: multicoloured translates

Zhao, *Probabilistic Methods in Combinatorics* (MIT 18.226), Question 6.2.9 and Theorem 6.2.10
(Erdős–Lovász 1975): for every `k` there is an `m` such that for every `m`-element `S ⊆ ℝ` the
reals can be `k`-coloured so that every translate of `S` sees all `k` colours.

Chapter 6's `Applications` section colours with `Bool`, which `fairCoin` and `uniformColoring`
serve.  This section needs more than two colours, so it works with the uniform measure on
`κ → β` for a finite colour type `β`.  Mathlib's `uniformOn` supplies that, and `uniformOn_pi`
already identifies it with the product measure, so the independence lemmas of `LocalLemma`
apply unchanged.

The hypothesis is satisfiable for every `k`: the least admissible `m` is `9, 20, 33, 46` for
`k = 2, 3, 4, 5` and `123` for `k = 10`.
-/

namespace ProbMethodCombinatorics

open Finset MeasureTheory ProbabilityTheory

section UniformColor

variable {β : Type*} [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The uniform measure on colourings of `κ` by `β`: every coordinate independent and uniform.
By `uniformOn_pi` this is also `uniformOn (Set.univ : Set (κ → β))`. -/
noncomputable def uniformColorOn (β : Type*) [MeasurableSpace β] (κ : Type*) [Fintype κ] :
    Measure (κ → β) :=
  Measure.pi fun _ : κ => uniformOn (Set.univ : Set β)

instance : IsProbabilityMeasure (uniformColorOn β κ) := by
  rw [uniformColorOn]; infer_instance

/-- **A uniform colouring avoids a fixed colour on a fixed finite set** with probability
`(1 - 1/|β|) ^ |T|`: the coordinates in `T` are independent and each misses `b` with
probability `1 - 1/|β|`. -/
theorem uniformColorOn_avoid_toReal (T : Finset κ) (b : β) :
    (uniformColorOn β κ {x : κ → β | ∀ u ∈ T, x u ≠ b}).toReal
      = (1 - 1 / (Fintype.card β : ℝ)) ^ T.card := by
  have hset : {x : κ → β | ∀ u ∈ T, x u ≠ b}
      = Set.univ.pi (fun a => if a ∈ T then ({b}ᶜ : Set β) else Set.univ) := by
    ext x
    constructor
    · intro h a _
      show x a ∈ (if a ∈ T then ({b}ᶜ : Set β) else Set.univ)
      by_cases ha : a ∈ T
      · rw [if_pos ha]; exact h a ha
      · rw [if_neg ha]; exact Set.mem_univ _
    · intro h u hu
      have hxu : x u ∈ (if u ∈ T then ({b}ᶜ : Set β) else Set.univ) := h u (Set.mem_univ u)
      rw [if_pos hu] at hxu
      exact hxu
  have hsingle : uniformOn (Set.univ : Set β) {b} = 1 / (Fintype.card β : ENNReal) := by
    rw [uniformOn_univ, Measure.count_singleton]
  have hreal : (uniformOn (Set.univ : Set β) ({b}ᶜ)).toReal
      = 1 - 1 / (Fintype.card β : ℝ) := by
    have h2 := congrArg ENNReal.toReal
      (uniformOn_compl (s := (Set.univ : Set β)) {b} Set.finite_univ Set.univ_nonempty)
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsingle] at h2
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at h2
    linarith
  have hrew : ∀ a : κ,
      uniformOn (Set.univ : Set β) (if a ∈ T then ({b}ᶜ : Set β) else Set.univ)
        = if a ∈ T then uniformOn (Set.univ : Set β) ({b}ᶜ) else 1 := by
    intro a
    by_cases ha : a ∈ T
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha]; exact measure_univ
  rw [hset, uniformColorOn, Measure.pi_pi,
    Finset.prod_congr rfl (fun a _ => hrew a), Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const, ENNReal.toReal_pow, hreal]

/-- **A uniform colouring fails to use every colour on `T`** with probability at most
`|β| · (1 - 1/|β|) ^ |T|`, by a union bound over which colour is missing. -/
theorem uniformColorOn_not_multicolored_toReal_le (T : Finset κ) :
    (uniformColorOn β κ {x : κ → β | ∃ b : β, ∀ u ∈ T, x u ≠ b}).toReal
      ≤ Fintype.card β * (1 - 1 / (Fintype.card β : ℝ)) ^ T.card := by
  have hset : {x : κ → β | ∃ b : β, ∀ u ∈ T, x u ≠ b}
      = ⋃ b : β, {x : κ → β | ∀ u ∈ T, x u ≠ b} := by
    ext x
    simp
  have hfin : ∀ b : β, uniformColorOn β κ {x : κ → β | ∀ u ∈ T, x u ≠ b} ≠ ⊤ :=
    fun b => measure_ne_top _ _
  have hsum : (∑ b : β, uniformColorOn β κ {x : κ → β | ∀ u ∈ T, x u ≠ b}) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun b _ => hfin b
  rw [hset]
  refine (ENNReal.toReal_mono hsum (measure_iUnion_fintype_le _ _)).trans ?_
  rw [ENNReal.toReal_sum fun b _ => hfin b]
  simp only [uniformColorOn_avoid_toReal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    le_refl]

end UniformColor

section Translates

/-- **Theorem 6.2.10 for finitely many translates.**  The local lemma alone gets this far;
passing to all of `ℝ` is the compactness step below. -/
theorem exists_coloring_forall_mem_multicolored {k m : ℕ} [NeZero k]
    (h : Real.exp 1 * ((m * (m - 1) + 1 : ℕ) : ℝ) * k * (1 - 1 / (k : ℝ)) ^ m ≤ 1)
    {S : Finset ℝ} (hS : S.card = m) (X : Finset ℝ) :
    ∃ c : ℝ → Fin k, ∀ x ∈ X, ∀ i : Fin k, ∃ s ∈ S, c (x + s) = i := by
  classical
  -- Only the reals `x + s` with `x ∈ X` and `s ∈ S` are constrained, and there are finitely
  -- many of them.  The local lemma runs on colourings of that finite set.
  obtain ⟨V, hVmem⟩ : ∃ V : Finset ℝ, ∀ x ∈ X, ∀ s ∈ S, x + s ∈ V :=
    ⟨X.biUnion fun x => S.image fun s => x + s, fun x hx s hs =>
      Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨s, hs, rfl⟩⟩⟩
  -- `T x` is the translate `x + S`, read inside `V`.
  obtain ⟨T, hTdef⟩ : ∃ T : {x // x ∈ X} → Finset {r : ℝ // r ∈ V}, ∀ x u,
      (u ∈ T x ↔ (u : ℝ) - (x : ℝ) ∈ S) :=
    ⟨fun x => Finset.univ.filter fun u => (u : ℝ) - (x : ℝ) ∈ S, by simp⟩
  -- Translation is injective, so `T x` still has `m` elements.
  have hTcard : ∀ x, (T x).card = m := by
    intro x
    rw [← hS]
    refine Finset.card_bij (fun u _ => (u : ℝ) - (x : ℝ)) (fun u hu => (hTdef x u).1 hu) ?_ ?_
    · intro u _ v _ huv
      exact Subtype.ext (by linarith)
    · intro s hs
      refine ⟨⟨(x : ℝ) + s, hVmem _ x.2 _ hs⟩, (hTdef x _).2 ?_, ?_⟩
      · show (x : ℝ) + s - (x : ℝ) ∈ S
        simpa using hs
      · show (x : ℝ) + s - (x : ℝ) = s
        ring
  -- The bad event for `x`: some colour is missing from the translate `x + S`.
  obtain ⟨A, hAdef⟩ : ∃ A : {x // x ∈ X} → Set ({r : ℝ // r ∈ V} → Fin k), ∀ x,
      A x = {c | ∃ i : Fin k, ∀ u ∈ T x, c u ≠ i} := ⟨_, fun _ => rfl⟩
  have hAmeas : ∀ x, MeasurableSet (A x) := fun _ => (Set.toFinite _).measurableSet
  -- `A x` only looks at the coordinates in `T x`.
  have hAinv : ∀ (j : {x // x ∈ X}) (c c' : {r : ℝ // r ∈ V} → Fin k),
      (∀ a ∈ T j, c a = c' a) → (c ∈ A j ↔ c' ∈ A j) := by
    intro j c c' hcc'
    rw [hAdef]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, fun u hu => by rw [← hcc' u hu]; exact hi u hu⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, fun u hu => by rw [hcc' u hu]; exact hi u hu⟩
  -- Two translates are joined when they meet.
  obtain ⟨N, hNdef⟩ : ∃ N : {x // x ∈ X} → Finset {x // x ∈ X}, ∀ x y,
      (y ∈ N x ↔ y ≠ x ∧ (T x ∩ T y).Nonempty) :=
    ⟨fun x => Finset.univ.filter fun y => y ≠ x ∧ (T x ∩ T y).Nonempty, by simp⟩
  -- Events indexed outside `N x ∪ {x}` use coordinates disjoint from `T x`, so the product
  -- measure factorises.
  have hNdep : IsDependencyGraph (uniformColorOn (Fin k) {r : ℝ // r ∈ V}) A N := by
    intro i s hs g
    refine measure_pi_inter_eq_mul (fun _ => uniformOn (Set.univ : Set (Fin k)))
      (T i) (A i) (pattern A s g) (hAinv i) ?_
    intro c c' hcc'
    have hj : ∀ j ∈ s,
        (c ∈ (if g j then A j else (A j)ᶜ) ↔ c' ∈ (if g j then A j else (A j)ᶜ)) := by
      intro j hjs
      obtain ⟨hjne, hjN⟩ := hs j hjs
      have hdisj : Disjoint (T i) (T j) := by
        by_contra hcon
        exact hjN ((hNdef i j).2 ⟨hjne, Finset.not_disjoint_iff_nonempty_inter.1 hcon⟩)
      have hiff := hAinv j c c' fun a ha =>
        hcc' a fun hai => (Finset.disjoint_left.1 hdisj hai) ha
      by_cases hg : g j
      · rw [if_pos hg]; exact hiff
      · rw [if_neg hg]; exact not_congr hiff
    simp only [pattern, Set.mem_iInter]
    exact ⟨fun hh j hjs => (hj j hjs).1 (hh j hjs), fun hh j hjs => (hj j hjs).2 (hh j hjs)⟩
  -- A union bound over the missing colour gives the probability of a bad event.
  have hp : ∀ x, (uniformColorOn (Fin k) {r : ℝ // r ∈ V} (A x)).toReal
      ≤ (k : ℝ) * (1 - 1 / (k : ℝ)) ^ m := by
    intro x
    have hbd := uniformColorOn_not_multicolored_toReal_le (β := Fin k) (T x)
    rw [Fintype.card_fin, hTcard x] at hbd
    rw [hAdef x]
    exact hbd
  -- If `x + S` meets `x' + S` then `x' - x` is a difference of two distinct elements of `S`,
  -- and `x'` is determined by it.  There are at most `m * (m - 1)` such differences.
  have hdcard : ∀ x : {x // x ∈ X}, (N x).card ≤ m * (m - 1) := by
    intro x
    have hkey : ∀ y ∈ N x, ∃ p : ℝ × ℝ, p ∈ S.offDiag ∧ (y : ℝ) = (x : ℝ) + (p.1 - p.2) := by
      intro y hy
      obtain ⟨hyne, u, hu⟩ := (hNdef x y).1 hy
      rw [Finset.mem_inter] at hu
      refine ⟨((u : ℝ) - (x : ℝ), (u : ℝ) - (y : ℝ)),
        Finset.mem_offDiag.2 ⟨(hTdef x u).1 hu.1, (hTdef y u).1 hu.2, ?_⟩, by
          show (y : ℝ) = (x : ℝ) + ((u : ℝ) - (x : ℝ) - ((u : ℝ) - (y : ℝ)))
          ring⟩
      show (u : ℝ) - (x : ℝ) ≠ (u : ℝ) - (y : ℝ)
      intro hcon
      exact hyne (Subtype.ext (by linarith))
    choose! f hf1 hf2 using hkey
    refine le_trans (Finset.card_le_card_of_injOn (t := S.offDiag) f ?_ ?_) ?_
    · intro y hy
      exact Finset.mem_coe.2 (hf1 y (Finset.mem_coe.1 hy))
    · intro y hy z hz hyz
      have h1 := hf2 y (Finset.mem_coe.1 hy)
      have h2 := hf2 z (Finset.mem_coe.1 hz)
      exact Subtype.ext (by rw [h1, h2, hyz])
    · rw [Finset.offDiag_card, hS, Nat.mul_sub, Nat.mul_one]
  -- The hypothesis `h` is exactly the symmetric condition `e · p · (d + 1) ≤ 1`.
  have hcond : Real.exp 1 * ((k : ℝ) * (1 - 1 / (k : ℝ)) ^ m)
      * (((m * (m - 1) : ℕ) : ℝ) + 1) ≤ 1 := by
    have hrw : Real.exp 1 * ((k : ℝ) * (1 - 1 / (k : ℝ)) ^ m) * (((m * (m - 1) : ℕ) : ℝ) + 1)
        = Real.exp 1 * ((m * (m - 1) + 1 : ℕ) : ℝ) * k * (1 - 1 / (k : ℝ)) ^ m := by
      push_cast
      ring
    rw [hrw]
    exact h
  have hpos := lovasz_local_lemma_symmetric (μ := uniformColorOn (Fin k) {r : ℝ // r ∈ V})
    A hAmeas N hNdep hp hdcard hcond
  -- A set of positive measure is nonempty, so a good colouring of `V` exists.
  rcases Set.eq_empty_or_nonempty (⋂ x, (A x)ᶜ) with hempty | ⟨c₀, hc₀⟩
  · rw [hempty] at hpos
    simp at hpos
  obtain ⟨c, hc⟩ : ∃ c : ℝ → Fin k, ∀ u : {r : ℝ // r ∈ V}, c (u : ℝ) = c₀ u :=
    ⟨fun r => if hr : r ∈ V then c₀ ⟨r, hr⟩ else default, fun u => by simp [u.2]⟩
  refine ⟨c, fun x hx i => ?_⟩
  simp only [Set.mem_iInter, Set.mem_compl_iff] at hc₀
  have hnot := hc₀ ⟨x, hx⟩
  rw [hAdef] at hnot
  by_contra hcon
  refine hnot ⟨i, fun u hu hcu => hcon ⟨(u : ℝ) - x, (hTdef ⟨x, hx⟩ u).1 hu, ?_⟩⟩
  have hxu : x + ((u : ℝ) - x) = (u : ℝ) := by ring
  rw [hxu, hc u, hcu]

/-- **Theorem 6.2.10** (Erdős–Lovász 1975): every translate of `S` is multicoloured.
`exists_forall_notMem_of_forall_finset` upgrades the finite statement to all of `ℝ`. -/
theorem exists_coloring_forall_translate_multicolored {k m : ℕ} [NeZero k]
    (h : Real.exp 1 * ((m * (m - 1) + 1 : ℕ) : ℝ) * k * (1 - 1 / (k : ℝ)) ^ m ≤ 1)
    {S : Finset ℝ} (hS : S.card = m) :
    ∃ c : ℝ → Fin k, ∀ x : ℝ, ∀ i : Fin k, ∃ s ∈ S, c (x + s) = i := by
  sorry

end Translates

end ProbMethodCombinatorics
