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
  sorry

/-- **Theorem 6.2.10** (Erdős–Lovász 1975): every translate of `S` is multicoloured.
`exists_forall_notMem_of_forall_finset` upgrades the finite statement to all of `ℝ`. -/
theorem exists_coloring_forall_translate_multicolored {k m : ℕ} [NeZero k]
    (h : Real.exp 1 * ((m * (m - 1) + 1 : ℕ) : ℝ) * k * (1 - 1 / (k : ℝ)) ^ m ≤ 1)
    {S : Finset ℝ} (hS : S.card = m) :
    ∃ c : ℝ → Fin k, ∀ x : ℝ, ∀ i : Fin k, ∃ s ∈ S, c (x + s) = i := by
  sorry

end Translates

end ProbMethodCombinatorics
